
#!/usr/bin/env python3
"""
HEX REA - HTML Recon Terminal (Termux)
Usage:  hex rea start

Two local servers (127.0.0.1 only):
  8765  editor UI + modify UI + JSON API
  8766  preview mirror (the "Play" button loads the site through here,
        rewritten so everything runs from what was extracted)
"""
import os
import re
import sys
import json
import time
import ssl
import shutil
import socket
import hashlib
import zipfile
import mimetypes
import threading
import uuid
import getpass
import textwrap
import posixpath
import select
import subprocess
from pathlib import Path
from urllib.parse import urljoin, urlsplit, quote, unquote
from concurrent.futures import ThreadPoolExecutor
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

try:
    import requests
    from bs4 import BeautifulSoup, Comment
    from colorama import init, Fore, Style
except ImportError:
    print("Missing dependencies. Run:  pip install requests beautifulsoup4 colorama")
    sys.exit(1)

init(autoreset=True)

BASE_DIR = Path(__file__).resolve().parent
EDITOR = BASE_DIR / "editor.html"
MODIFIER_HTML = BASE_DIR / "modify.html"

HOST = "127.0.0.1"
PORT = 8765
PREVIEW_PORT = 8766
UA = ("Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36")
REQ_HEADERS = {"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"}

MAX_FILE = 80 * 1024 * 1024        # per downloaded file
MAX_TOTAL = 500 * 1024 * 1024      # per download job
MAX_PAGE = 15 * 1024 * 1024        # HTML / CSS we parse in memory

PROBE_PATHS = ["admin", "login", "robots.txt", "sitemap.xml", ".env", ".git/config"]
PROBE_CODES = {200, 301, 302, 401, 403}
PAGE_EXT = ("", ".html", ".htm", ".php", ".asp", ".aspx", ".jsp", ".xhtml")
IMG_EXT = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".ico", ".bmp", ".avif"}
FONT_EXT = {".woff", ".woff2", ".ttf", ".otf", ".eot"}
AUD_EXT = {".mp3", ".wav", ".ogg", ".m4a", ".aac", ".flac", ".opus"}
VID_EXT = {".mp4", ".webm", ".mov", ".m4v", ".mkv", ".ogv"}
SKIP_SCHEMES = ("data:", "javascript:", "mailto:", "tel:", "blob:", "about:", "sms:")
BAD_CRAWL = re.compile(r"logout|signout|sign-out|log-out|delete|remove|unsubscribe", re.I)

SESSIONS = {}
JOBS = {}
SAVED = BASE_DIR / "saved"
CONF_DIR = Path.home() / ".hexrea"
CONF_FILE = CONF_DIR / "config.json"

_wake_r, _wake_w = os.pipe()
_pending_modify = None
MOD_LOCK = threading.Lock()


# --------------------------------------------------------------------------
# Terminal UI
# --------------------------------------------------------------------------
def typewriter(text, color=Fore.RED, delay=0.004, end="\n"):
    for ch in text:
        sys.stdout.write(color + ch)
        sys.stdout.flush()
        if ch not in " \n":
            time.sleep(delay)
    sys.stdout.write(Style.RESET_ALL + end)


def banner():
    os.system("clear")
    art = r"""
   ██╗  ██╗███████╗██╗  ██╗    ██████╗ ███████╗ █████╗
   ██║  ██║██╔════╝╚██╗██╔╝    ██╔══██╗██╔════╝██╔══██╗
   ███████║█████╗   ╚███╔╝     ██████╔╝█████╗  ███████║
   ██╔══██║██╔══╝   ██╔██╗     ██╔══██╗██╔══╝  ██╔══██║
   ██║  ██║███████╗██╔╝ ██╗    ██║  ██║███████╗██║  ██║
   ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝    ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝
"""
    typewriter(art, Fore.RED, 0.001)
    typewriter("          H T M L   R E C O N   T E R M I N A L", Fore.RED, 0.012)
    print()


def menu():
    R, W, G = Fore.RED, Fore.WHITE + Style.BRIGHT, Fore.GREEN
    print(R + "┌──(" + W + "HEX" + R + "@" + W + "REA" + R + ")-[" + G + "main menu" + R + "]")
    print(R + "│")
    print(R + "├─ " + W + "[1]" + G + " Extract Deep Code & Analyze")
    print(R + "├─ " + W + "[2]" + G + " Exit")
    print(R + "├─ " + W + "[3]" + G + " REA Your Sites")
    print(R + "│")
    sys.stdout.write(R + "└─" + G + "❯ " + Style.RESET_ALL)
    sys.stdout.flush()
    try:
        rlist, _, _ = select.select([sys.stdin, _wake_r], [], [])
        if _wake_r in rlist:
            os.read(_wake_r, 64)
            print()
            return "__MODIFY__"
        line = sys.stdin.readline()
        if not line:
            raise EOFError
        return line.strip()
    except (OSError, ValueError):
        return input().strip()


# --------------------------------------------------------------------------
# Generic helpers
# --------------------------------------------------------------------------
def registrable_domain(host):
    host = (host or "").split(":")[0].lower()
    if re.fullmatch(r"[\d.]+", host):
        return host
    parts = host.split(".")
    if len(parts) <= 2:
        return host
    sld = {"co", "com", "org", "net", "gov", "ac", "edu", "or", "ne"}
    if len(parts[-1]) == 2 and parts[-2] in sld:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def is_ip(host):
    return bool(re.fullmatch(r"[\d.]+", host)) or ":" in host


def ext_of(url):
    return posixpath.splitext(urlsplit(url).path)[1].lower()


def kind_by_ext(url):
    e = ext_of(url)
    if e in IMG_EXT:
        return "image"
    if e in FONT_EXT:
        return "font"
    if e in AUD_EXT:
        return "audio"
    if e in VID_EXT:
        return "video"
    if e == ".css":
        return "style"
    if e in (".js", ".mjs"):
        return "script"
    return "other"


def fetch(url, limit=MAX_FILE, referer=None, client=None, timeout=20):
    """GET with a size cap. Returns (response, body_bytes)."""
    h = dict(REQ_HEADERS)
    if referer:
        h["Referer"] = referer
    r = (client or requests).get(url, headers=h, timeout=timeout, stream=True, allow_redirects=True)
    buf = bytearray()
    try:
        for chunk in r.iter_content(65536):
            buf += chunk
            if len(buf) > limit:
                raise ValueError("file too large")
    finally:
        r.close()
    return r, bytes(buf)


def decode_bytes(data, content_type=""):
    m = re.search(r"charset=([\w-]+)", content_type or "", re.I)
    if not m:
        m = re.search(rb"<meta[^>]+charset=[\"']?([\w-]+)", data[:3000], re.I)
        enc = m.group(1).decode("ascii", "ignore") if m else None
    else:
        enc = m.group(1)
    for e in ([enc] if enc else []) + ["utf-8"]:
        try:
            return data.decode(e)
        except (LookupError, UnicodeDecodeError):
            pass
    return data.decode("cp1252", errors="replace")


def is_text(ct):
    ct = (ct or "").lower()
    return any(x in ct for x in ("text/", "json", "xml", "javascript", "html", "css", "svg"))


# --------------------------------------------------------------------------
# HTML / CSS processing (shared by analysis, preview mirror and downloader)
# --------------------------------------------------------------------------
CSS_URL = re.compile(r"""url\(\s*(["']?)(.*?)\1\s*\)""", re.I)
CSS_IMPORT = re.compile(r"""@import\s+(["'])(.*?)\1""", re.I)
LINK_RELS = ("stylesheet", "icon", "apple-touch-icon", "preload", "prefetch",
             "manifest", "modulepreload", "mask-icon", "image_src")
LAZY_ATTRS = ("poster", "data-src", "data-original", "data-lazy-src", "data-bg", "data-background")
AS_KIND = {"font": "font", "image": "image", "style": "style", "script": "script",
           "audio": "audio", "video": "video"}


def process_css(css, base, mapper=None, collect=None):
    def one(v, q, whole):
        v = v.strip()
        if not v or v.startswith(("data:", "#")):
            return whole
        absu = urljoin(base, v)
        if not absu.lower().startswith(("http://", "https://")):
            return whole
        absu = absu.split("#")[0]
        k = kind_by_ext(absu)
        if collect:
            collect(absu, k)
        if mapper:
            n = mapper(absu, k)
            if n:
                return n
        return whole

    def rep_url(m):
        n = one(m.group(2), m.group(1), None)
        if n is None:
            return m.group(0)
        q = m.group(1)
        return f"url({q}{n}{q})"

    def rep_imp(m):
        n = one(m.group(2), m.group(1), None)
        if n is None:
            return m.group(0)
        return f"@import {m.group(1)}{n}{m.group(1)}"

    css = CSS_URL.sub(rep_url, css)
    return CSS_IMPORT.sub(rep_imp, css)


def process_html(html, page_url, mapper=None, collect=None, shim=None):
    """Walk every resource reference in the page."""
    soup = BeautifulSoup(html, "html.parser")
    base = page_url
    bt = soup.find("base", href=True)
    if bt:
        base = urljoin(page_url, bt["href"])

    def ref(v, kind):
        v = (v or "").strip() if isinstance(v, str) else ""
        if not v or v.startswith("#") or v.lower().startswith(SKIP_SCHEMES):
            return None
        absu = urljoin(base, v)
        if not absu.lower().startswith(("http://", "https://")):
            return None
        absu, _, frag = absu.partition("#")
        if collect:
            collect(absu, kind)
        if mapper:
            n = mapper(absu, kind)
            if n:
                return n + ("#" + frag if frag else "")
        return None

    def srcset(v, kind):
        parts, changed = [], False
        for cand in re.split(r",\s+|(?<=\d[wx]),", v):
            cand = cand.strip()
            if not cand:
                continue
            bits = cand.split(None, 1)
            n = ref(bits[0], kind)
            if n:
                bits[0], changed = n, True
            parts.append(" ".join(bits))
        return ", ".join(parts) if changed else None

    for tag in soup.find_all(True):
        name = tag.name
        if name in ("a", "area"):
            n = ref(tag.get("href"), "page")
            if n:
                tag["href"] = n
                tag.attrs.pop("target", None)
        elif name in ("iframe", "frame"):
            n = ref(tag.get("src"), "frame")
            if n:
                tag["src"] = n
        elif name == "link":
            rel = " ".join(tag.get("rel", [])).lower()
            if any(x in rel for x in LINK_RELS):
                kind = "style" if "stylesheet" in rel else ("image" if "icon" in rel else "other")
                kind = AS_KIND.get(tag.get("as", ""), kind)
                if "modulepreload" in rel:
                    kind = "script"
                n = ref(tag.get("href"), kind)
                if n:
                    tag["href"] = n
        elif name in ("img", "script", "audio", "video", "source", "track", "embed", "input"):
            if name == "input" and tag.get("type") != "image":
                pass
            else:
                kind = {"script": "script", "img": "image", "audio": "audio", "video": "video",
                        "track": "other", "embed": "frame", "input": "image"}.get(name)
                if name == "source":
                    pn = tag.parent.name if tag.parent else ""
                    kind = "audio" if pn == "audio" else "video" if pn == "video" else "image"
                n = ref(tag.get("src"), kind)
                if n:
                    tag["src"] = n
        for attr in ("srcset", "data-srcset"):
            if tag.get(attr):
                n = srcset(tag[attr], "image")
                if n:
                    tag[attr] = n
        for attr in LAZY_ATTRS:
            if tag.get(attr):
                n = ref(tag[attr], "image")
                if n:
                    tag[attr] = n
        st = tag.get("style")
        if st and "url(" in st:
            tag["style"] = process_css(st, base, mapper, collect)

    for s in soup.find_all("style"):
        if s.string:
            new = process_css(str(s.string), base, mapper, collect)
            if mapper:
                s.string.replace_with(s.string.__class__(new))

    if not mapper:
        return None

    for t in soup.find_all(["link", "script"]):
        for a in ("integrity", "crossorigin", "nonce"):
            t.attrs.pop(a, None)
    for m in soup.find_all("meta"):
        he = (m.get("http-equiv") or "").lower()
        if he in ("content-security-policy", "refresh", "content-type") or m.get("charset"):
            m.decompose()
    for b in soup.find_all("base"):
        b.decompose()

    head = soup.head
    if head is None:
        head = soup.new_tag("head")
        (soup.html or soup).insert(0, head)
    if shim:
        head.insert(0, BeautifulSoup("<script>" + shim + "</script>", "html.parser").script)
    head.insert(0, BeautifulSoup('<meta charset="utf-8">', "html.parser").meta)
    return str(soup)


SHIM = r"""(function(){
var SID="__SID__",H="__H__",SC="__SC__",P="/site/"+SID+"/"+H,O=location.origin;
function fix(u){
 if(typeof u!=="string")return u;
 if(u.indexOf("/site/"+SID+"/")===0||u.indexOf(O)===0)return u;
 if(u.indexOf("//")===0)u=SC+":"+u;
 var m=u.match(/^https?:\/\/([^\/?#]+)(.*)$/i);
 if(m)return "/site/"+SID+"/"+m[1]+(m[2]&&m[2].charAt(0)!=="/"?"/"+m[2]:(m[2]||"/"));
 if(u.charAt(0)==="/")return P+u;
 return u;
}
var f=window.fetch;
if(f)window.fetch=function(i,o){try{if(typeof i==="string")i=fix(i);else if(i&&i.url)i=new Request(fix(i.url),i)}catch(e){}return f.call(this,i,o)};
var xo=XMLHttpRequest.prototype.open;
XMLHttpRequest.prototype.open=function(m,u){var a=Array.prototype.slice.call(arguments);a[1]=fix(String(u));return xo.apply(this,a)};
function say(o){try{parent.postMessage(o,"*")}catch(e){}}
document.addEventListener("submit",function(e){e.preventDefault();say({hexrea:"toast",msg:"Form submit is disabled in preview"})},true);
document.addEventListener("click",function(e){var a=e.target.closest&&e.target.closest("a[href]");if(!a)return;var h=a.getAttribute("href")||"";if(/^(https?:)?\/\//i.test(h)&&h.indexOf(O)!==0){e.preventDefault();say({hexrea:"toast",msg:"External link blocked in preview"})}},true);
say({hexrea:"nav",path:location.pathname+location.search});
})();"""


def build_shim(sess, page_url):
    p = urlsplit(page_url)
    return (SHIM.replace("__SID__", sess["id"]).replace("__H__", p.netloc).replace("__SC__", p.scheme))


# --------------------------------------------------------------------------
# Sessions / preview mapping
# --------------------------------------------------------------------------
def host_allowed(sess, netloc):
    if netloc in sess["hosts"]:
        return True
    return registrable_domain(netloc) == sess["reg"]


def preview_path(sess, url):
    p = urlsplit(url)
    return f"/site/{sess['id']}/{p.netloc}{p.path or '/'}" + (f"?{p.query}" if p.query else "")


def preview_url(sess, url):
    return f"http://{HOST}:{PREVIEW_PORT}{preview_path(sess, url)}"


def preview_mapper(sess):
    def m(url, kind):
        p = urlsplit(url)
        if kind in ("page", "frame") and not host_allowed(sess, p.netloc):
            return None
        sess["hosts"].add(p.netloc)
        sess["schemes"][p.netloc] = p.scheme
        return preview_path(sess, url)
    return m


def new_session(final_url):
    p = urlsplit(final_url)
    sid = uuid.uuid4().hex[:10]
    if len(SESSIONS) >= 20:
        SESSIONS.pop(next(iter(SESSIONS)))
    SESSIONS[sid] = {
        "id": sid, "start": final_url, "origin": f"{p.scheme}://{p.netloc}",
        "netloc": p.netloc, "scheme": p.scheme, "reg": registrable_domain(p.netloc),
        "hosts": {p.netloc}, "schemes": {p.netloc: p.scheme}, "analysis": None,
    }
    return SESSIONS[sid]


# --------------------------------------------------------------------------
# Deep analysis
# --------------------------------------------------------------------------
SECURITY_HEADERS = [
    ("Content-Security-Policy", "Blocks injected scripts"),
    ("Strict-Transport-Security", "Forces HTTPS"),
    ("X-Frame-Options", "Clickjacking protection"),
    ("X-Content-Type-Options", "Stops MIME sniffing"),
    ("Referrer-Policy", "Controls referrer leaks"),
    ("Permissions-Policy", "Limits browser features"),
    ("Cross-Origin-Opener-Policy", "Window isolation"),
]
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
API_RE = re.compile(r"""["'`]((?:https?:)?//[^"'`\s]+/api/[^"'`\s]*|/(?:api|graphql|ajax|wp-json|rest|v\d)/[^"'`\s]*)["'`]""")
FETCH_RE = re.compile(r"""(?:fetch|axios(?:\.\w+)?|\$\.(?:get|post|ajax)|\.open)\(\s*(?:["'](?:GET|POST)["']\s*,\s*)?["'`]([^"'`\s]+)["'`]""")
SOCIAL = ("facebook.com", "twitter.com", "x.com", "instagram.com", "linkedin.com", "youtube.com",
          "github.com", "tiktok.com", "t.me", "wa.me", "discord.gg", "pinterest.com", "reddit.com")


def detect_tech(resp, html, cookies):
    h = {k.lower(): v for k, v in resp.headers.items()}
    low = html.lower()
    ck = " ".join(c.name for c in cookies).lower()
    out = []
    if h.get("server"):
        out.append(f"Server: {h['server']}")
    if h.get("x-powered-by"):
        out.append(f"Powered-By: {h['x-powered-by']}")
    m = re.search(r"<meta[^>]+name=[\"']generator[\"'][^>]+content=[\"']([^\"']+)", html, re.I)
    if m:
        out.append(f"Generator: {m.group(1)[:60]}")
    sigs = [
        ("WordPress", "wp-content" in low or "wp-includes" in low),
        ("Next.js", "_next/static" in low or "__next_data__" in low),
        ("Nuxt", "/_nuxt/" in low or "__nuxt" in low),
        ("Gatsby", "___gatsby" in low),
        ("React", any(s in low for s in ("react-dom", "data-reactroot", "react.production", "react.development", "__react"))),
        ("Vue.js", any(s in low for s in ("vue.js", "vue.min.js", "vue.global", "data-v-", "__vue"))),
        ("Angular", "ng-version" in low or "ng-app" in low),
        ("Svelte", "svelte-" in low),
        ("jQuery", "jquery" in low),
        ("Bootstrap", "bootstrap" in low),
        ("Tailwind CSS", "tailwind" in low),
        ("Font Awesome", "font-awesome" in low or "fontawesome" in low),
        ("Google Fonts", "fonts.googleapis.com" in low),
        ("Google Analytics", any(s in low for s in ("googletagmanager.com", "google-analytics.com", "gtag("))),
        ("reCAPTCHA", "recaptcha" in low),
        ("Stripe", "js.stripe.com" in low),
        ("Shopify", "cdn.shopify.com" in low),
        ("Wix", "wixstatic.com" in low),
        ("Squarespace", "squarespace" in low),
        ("Webflow", "webflow" in low),
        ("Drupal", "drupal" in low),
        ("Joomla", "joomla" in low),
        ("Laravel", "laravel_session" in ck),
        ("PHP", "phpsessid" in ck or "php" in h.get("x-powered-by", "").lower()),
        ("ASP.NET", "asp.net" in ck or "x-aspnet-version" in h),
        ("Django", "csrftoken" in ck),
        ("Cloudflare", "cf-ray" in h or "cloudflare" in h.get("server", "").lower()),
        ("Vercel", "x-vercel-id" in h),
        ("Netlify", "x-nf-request-id" in h or "netlify" in h.get("server", "").lower()),
        ("AWS CloudFront", "x-amz-cf-id" in h),
        ("Fastly", "x-served-by" in h),
    ]
    out += [n for n, ok in sigs if ok]
    return out


def tls_info(host, port):
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((host, port), timeout=5) as s:
            with ctx.wrap_socket(s, server_hostname=host) as t:
                c = t.getpeercert()
                subj = dict(x[0] for x in c.get("subject", ()))
                iss = dict(x[0] for x in c.get("issuer", ()))
                return {
                    "Protocol": t.version(), "Cipher": (t.cipher() or [""])[0],
                    "Subject": subj.get("commonName", ""),
                    "Issuer": iss.get("organizationName") or iss.get("commonName", ""),
                    "Valid from": c.get("notBefore", ""), "Valid until": c.get("notAfter", ""),
                    "SAN": [v for k, v in c.get("subjectAltName", ()) if k == "DNS"][:25],
                }
    except Exception as e:  # noqa: BLE001
        return {"Error": str(e)[:140]}


def dns_addrs(host):
    try:
        return sorted({a[4][0] for a in socket.getaddrinfo(host, None)})
    except OSError:
        return []


def probe_paths(origin):
    def one(path):
        url = f"{origin}/{path}"
        try:
            r = requests.get(url, headers=REQ_HEADERS, timeout=4, allow_redirects=False, stream=True)
            code, size, loc = r.status_code, r.headers.get("Content-Length"), r.headers.get("Location", "")
            r.close()
            if code in PROBE_CODES:
                return {"path": "/" + path, "url": url, "status": code, "location": loc,
                        "size": int(size) if size and size.isdigit() else None}
        except requests.RequestException:
            pass
        return None

    catch_all = False
    try:
        r = requests.get(f"{origin}/hexrea-{int(time.time())}-nope", headers=REQ_HEADERS,
                         timeout=4, allow_redirects=False, stream=True)
        catch_all = r.status_code == 200
        r.close()
    except requests.RequestException:
        pass

    with ThreadPoolExecutor(max_workers=6) as pool:
        results = [r for r in pool.map(one, PROBE_PATHS) if r]
    for r in results:
        r["unverified"] = catch_all and r["status"] == 200
        if r["status"] == 200 and not r["unverified"] and r["path"] in ("/robots.txt", "/sitemap.xml"):
            try:
                rr, data = fetch(r["url"], 300_000, timeout=6)
                body = decode_bytes(data, rr.headers.get("Content-Type", ""))
                r["body"] = body[:4000]
                if r["path"] == "/sitemap.xml":
                    r["sitemap_urls"] = re.findall(r"<loc>\s*(.*?)\s*</loc>", body)[:80]
            except Exception:  # noqa: BLE001
                pass
    return results


def rdap_lookup(host):
    if is_ip(host):
        return {}
    domain = registrable_domain(host)
    try:
        r = requests.get(f"https://rdap.org/domain/{domain}", timeout=10,
                         headers={"Accept": "application/rdap+json", "User-Agent": UA})
        if r.status_code != 200:
            return {}
        d = r.json()
    except (requests.RequestException, ValueError):
        return {}
    info = {"Domain": domain}
    registrar = None
    for ent in d.get("entities", []):
        if "registrar" in ent.get("roles", []):
            try:
                for item in ent["vcardArray"][1]:
                    if item[0] == "fn":
                        registrar = item[3]
                        break
            except (KeyError, IndexError, TypeError):
                pass
            if registrar:
                break
    info["Registrar"] = registrar or "Unknown"
    for ev in d.get("events", []):
        date = (ev.get("eventDate") or "")[:10]
        a = ev.get("eventAction")
        if a == "registration":
            info["Created"] = date
        elif a == "expiration":
            info["Expires"] = date
        elif a == "last changed":
            info["Updated"] = date
    info["Nameservers"] = [n.get("ldhName", "").lower() for n in d.get("nameservers", []) if n.get("ldhName")]
    return info


def analyze(url):
    if not url.startswith(("http://", "https://")):
        url = "https://" + url
    client = requests.Session()
    t0 = time.time()
    resp, data = fetch(url, MAX_PAGE, client=client, timeout=15)
    elapsed = int((time.time() - t0) * 1000)

    html = decode_bytes(data, resp.headers.get("Content-Type", ""))
    final = urlsplit(resp.url)
    host = final.hostname or ""
    origin = f"{final.scheme}://{final.netloc}"
    sess = new_session(resp.url)
    soup = BeautifulSoup(html, "html.parser")

    assets, seen, internal = [], set(), set()
    site_reg = sess["reg"]

    def coll(u, kind):
        if kind in ("page", "frame"):
            p = urlsplit(u)
            if p.netloc == final.netloc and ext_of(u) in PAGE_EXT:
                internal.add(u)
            if kind == "page":
                return
        if u not in seen and len(assets) < 2500:
            seen.add(u)
            h = urlsplit(u).netloc
            assets.append({"url": u, "kind": kind, "host": h,
                           "third_party": registrable_domain(h) != site_reg})

    process_html(html, resp.url, collect=coll)
    for a in soup.find_all("a", href=True):
        full = urljoin(resp.url, a["href"]).split("#")[0]
        p = urlsplit(full)
        if p.scheme in ("http", "https") and p.netloc == final.netloc and p.path not in ("", "/") \
                and ext_of(full) in PAGE_EXT:
            internal.add(full)
    internal.discard(resp.url)

    meta = {}
    for tag in soup.find_all("meta"):
        n = (tag.get("name") or tag.get("property") or "").strip()
        c = tag.get("content")
        if n and c and (n.lower() in ("description", "keywords", "author", "viewport", "robots", "theme-color")
                        or n.lower().startswith(("og:", "twitter:"))):
            meta[n] = c.strip()[:220]

    forms = []
    for f in soup.find_all("form"):
        fields = [{"name": i.get("name") or i.get("id") or "",
                   "type": i.get("type", "text") if i.name == "input" else i.name}
                  for i in f.find_all(["input", "textarea", "select"])]
        forms.append({"action": urljoin(resp.url, f.get("action") or resp.url),
                      "method": (f.get("method") or "GET").upper(), "inputs": fields})

    cookies = [{"name": c.name, "value": c.value, "domain": c.domain, "secure": bool(c.secure),
                "httponly": c.has_nonstandard_attr("HttpOnly") or c.has_nonstandard_attr("httponly")}
               for c in client.cookies]

    emails = sorted({e for e in EMAIL_RE.findall(html)
                     if not e.lower().rsplit(".", 1)[-1] in ("png", "jpg", "jpeg", "gif", "webp", "svg")})[:40]
    phones = sorted({a["href"][4:].strip() for a in soup.find_all("a", href=True)
                     if a["href"].lower().startswith("tel:")})[:20]
    social = sorted({urljoin(resp.url, a["href"]) for a in soup.find_all("a", href=True)
                     if any(s in urlsplit(urljoin(resp.url, a["href"])).netloc.lower() for s in SOCIAL)})[:30]
    comments = [str(c).strip()[:300] for c in soup.find_all(string=lambda t: isinstance(t, Comment))
                if str(c).strip()][:30]
    inline_js = "\n".join(s.get_text() for s in soup.find_all("script") if not s.get("src"))
    endpoints = sorted(set(API_RE.findall(html)) | set(FETCH_RE.findall(inline_js)))
    endpoints = [e for e in endpoints if len(e) < 200][:50]
    jsonld = [s.get_text().strip()[:1500] for s in soup.find_all("script", type="application/ld+json")][:5]
    headings = [{"tag": h.name, "text": h.get_text(" ", strip=True)[:90]}
                for h in soup.find_all(["h1", "h2", "h3"])][:40]
    canon = soup.find("link", rel="canonical")
    icon = next((urljoin(resp.url, l["href"]) for l in soup.find_all("link", href=True)
                 if "icon" in " ".join(l.get("rel", [])).lower()), "")
    lang = (soup.html.get("lang") if soup.html else "") or ""
    inline_count = len([s for s in soup.find_all("script") if not s.get("src")])
    title = soup.title.get_text(strip=True) if soup.title and soup.title.get_text(strip=True) else "No Title"
    for s in soup(["script", "style"]):
        s.extract()
    words = len(soup.get_text(" ", strip=True).split())

    sec = []
    low_h = {k.lower(): v for k, v in resp.headers.items()}
    for name, why in SECURITY_HEADERS:
        v = low_h.get(name.lower())
        sec.append({"name": name, "why": why, "present": bool(v), "value": (v or "")[:200]})

    port = final.port or (443 if final.scheme == "https" else 80)
    analysis = {
        "final_url": resp.url, "status": f"{resp.status_code} {resp.reason}",
        "status_code": resp.status_code, "size": f"{len(html):,} chars", "bytes": len(data),
        "elapsed_ms": elapsed, "title": title, "lang": lang,
        "canonical": canon.get("href", "") if canon else "", "favicon": icon, "words": words,
        "content_type": resp.headers.get("Content-Type", ""),
        "redirects": [{"status": r.status_code, "url": r.url} for r in resp.history],
        "tech": detect_tech(resp, html, client.cookies), "meta": meta,
        "headers": dict(resp.headers), "cookies": cookies, "security": sec,
        "assets": assets, "links": sorted(internal)[:300], "forms": forms,
        "emails": emails, "phones": phones, "social": social, "comments": comments,
        "endpoints": endpoints, "jsonld": jsonld, "headings": headings,
        "inline_scripts": inline_count,
        "dns": dns_addrs(host), "tls": tls_info(host, port) if final.scheme == "https" else {},
        "probes": probe_paths(origin), "rdap": rdap_lookup(host),
        "local_url": preview_url(sess, resp.url),
    }
    sess["analysis"] = analysis
    save_site(sess, html)
    return {"success": True, "sid": sess["id"], "netloc": sess["netloc"],
            "saved_id": sess.get("saved_id", ""), "html": html, "analysis": analysis}


def page_info(sess, target):
    target = (target or "").strip()
    if re.match(r"https?://", target, re.I):
        url = target
        if not host_allowed(sess, urlsplit(url).netloc):
            raise ValueError("That address is outside this site")
    else:
        url = urljoin(sess["origin"] + "/", target.lstrip("/") if not target.startswith("?") else target)
    r, data = fetch(url, MAX_PAGE, referer=sess["origin"] + "/", timeout=20)
    ct = r.headers.get("Content-Type", "")
    final = urlsplit(r.url)
    sess["hosts"].add(final.netloc)
    sess["schemes"][final.netloc] = final.scheme
    text_ok = is_text(ct)
    display = final.path + (f"?{final.query}" if final.query else "")
    if final.netloc != sess["netloc"]:
        display = final.netloc + display
    return {
        "success": True, "url": url, "final_url": r.url, "status": r.status_code,
        "reason": r.reason, "content_type": ct, "bytes": len(data), "is_text": text_ok,
        "source": decode_bytes(data, ct) if text_ok else "",
        "display_path": display or "/", "local_url": preview_url(sess, r.url),
    }


# --------------------------------------------------------------------------
# Full-site downloader
# --------------------------------------------------------------------------
def local_rel(url, ctype=""):
    p = urlsplit(url)
    path = unquote(p.path) or "/"
    if path.endswith("/"):
        path += "index"
    path = re.sub(r'[<>:"\\|?*\x00-\x1f]', "_", path)
    base, ext = posixpath.splitext(path)
    if p.query:
        base += "__" + hashlib.md5(p.query.encode()).hexdigest()[:8]
    ctype = (ctype or "").split(";")[0].strip().lower()
    if "html" in ctype and ext.lower() not in (".html", ".htm"):
        ext = ".html"
    elif not ext:
        ext = ".html" if not ctype else (mimetypes.guess_extension(ctype) or ".bin")
    rel = (p.netloc.replace(":", "_") + base + ext).lstrip("/")
    if len(rel) > 160:
        rel = rel[:100] + "_" + hashlib.md5(rel.encode()).hexdigest()[:10] + ext
    return rel


def offline_mapper(url2path, cur_rel):
    folder = posixpath.dirname(cur_rel) or "."

    def m(url, kind):
        rel = url2path.get(url)
        if not rel:
            return None
        return quote(posixpath.relpath(rel, folder), safe="/")
    return m


def storage_dir():
    for c in (Path.home() / "storage" / "downloads", Path("/storage/emulated/0/Download"), Path("/sdcard/Download")):
        try:
            if c.is_dir() and os.access(c, os.W_OK):
                d = c / "HexRea"
                d.mkdir(exist_ok=True)
                return d, True
        except OSError:
            pass
    d = BASE_DIR / "downloads"
    d.mkdir(exist_ok=True)
    return d, False


def run_download(job, sess, max_pages, third_party, dest_root=None, package=True):
    lock = threading.Lock()
    try:
        name = f"{sess['netloc'].replace(':', '_')}_{time.strftime('%Y%m%d_%H%M%S')}"
        work = BASE_DIR / "downloads"
        root = Path(dest_root) if dest_root else work / name
        root.mkdir(parents=True, exist_ok=True)
        url2path, used, files, errors = {}, set(), [], []
        html_files, css_files, pages, page_hashes = [], [], [], {}
        seen_assets, total = set(), [0]

        def log(msg):
            job["log"].append(msg)
            del job["log"][:-80]

        def unique(rel):
            with lock:
                base, ext = posixpath.splitext(rel)
                cand, n = rel, 1
                while cand.lower() in used:
                    cand = f"{base}_{n}{ext}"
                    n += 1
                used.add(cand.lower())
                return cand

        def write(rel, data):
            fp = root / rel
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_bytes(data)

        def fail(url, err):
            with lock:
                errors.append({"url": url, "error": str(err)[:140]})
                job["errors"] = len(errors)
                job["done"] += 1
            log(f"✗ {url[:70]}  ({str(err)[:40]})")

        def tick():
            job["pct"] = min(75, 4 + 71 * job["done"] / max(job["total"], 1))

        def dl_one(url, kind):
            if job["cancel"] or total[0] > MAX_TOTAL:
                return None
            try:
                r, data = fetch(url, MAX_FILE, referer=sess["origin"] + "/")
                if r.status_code >= 400:
                    raise ValueError(f"HTTP {r.status_code}")
                ct = r.headers.get("Content-Type", "")
                rel = unique(local_rel(url, ct))
                write(rel, data)
                refs = []
                with lock:
                    url2path[url] = rel
                    url2path[r.url.split("#")[0]] = rel
                    total[0] += len(data)
                    job["files"] += 1
                    job["bytes"] = total[0]
                    job["done"] += 1
                    files.append({"url": url, "path": rel, "type": ct.split(";")[0], "size": len(data), "kind": kind})
                    if "css" in ct.lower() or rel.endswith(".css"):
                        css_files.append((rel, r.url, ct))
                if "css" in ct.lower() or rel.endswith(".css"):
                    process_css(decode_bytes(data, ct), r.url, collect=lambda u, k: refs.append(u))
                job["current"] = url
                log(f"✓ {rel[:70]}  {len(data) // 1024} KB")
                tick()
                return refs
            except Exception as e:  # noqa: BLE001
                fail(url, e)
                return None

        def dl_many(urls):
            todo = []
            for u in urls:
                if u not in seen_assets:
                    seen_assets.add(u)
                    todo.append(u)
            while todo and not job["cancel"]:
                job["total"] += len(todo)
                with ThreadPoolExecutor(max_workers=8) as ex:
                    results = list(ex.map(lambda u: dl_one(u, "asset"), todo))
                todo = []
                for refs in results:
                    for u in refs or []:
                        if u not in seen_assets and len(seen_assets) < 4000 \
                                and (third_party or registrable_domain(urlsplit(u).netloc) == sess["reg"]):
                            seen_assets.add(u)
                            todo.append(u)

        job["phase"] = "Crawling pages and downloading assets"
        queue, queued = [sess["start"]], {sess["start"]}
        while queue and len(pages) < max_pages and not job["cancel"]:
            purl = queue.pop(0)
            job["current"] = purl
            try:
                r, data = fetch(purl, MAX_PAGE, referer=sess["origin"] + "/")
            except Exception as e:  # noqa: BLE001
                fail(purl, e)
                continue
            ct = r.headers.get("Content-Type", "")
            if r.status_code >= 400 or "html" not in ct.lower():
                if r.status_code < 400:
                    dl_many([purl])
                continue
            html = decode_bytes(data, ct)
            digest = hashlib.md5(data).hexdigest()
            if digest in page_hashes:
                url2path[purl] = page_hashes[digest]
                url2path[r.url.split("#")[0]] = page_hashes[digest]
                continue
            rel = unique(local_rel(purl, "text/html"))
            page_hashes[digest] = rel
            write(rel, data)
            write("_original_source/" + rel, data)
            with lock:
                url2path[purl] = rel
                url2path[r.url.split("#")[0]] = rel
                html_files.append((rel, r.url, ct))
                pages.append({"url": purl, "path": rel})
                total[0] += len(data)
                job["files"] += 1
                job["pages"] = len(pages)
                job["bytes"] = total[0]
            log(f"▶ page {len(pages)}: {rel[:60]}")
            assets, links = [], []
            process_html(html, r.url, collect=lambda u, k: (links if k in ("page", "frame") else assets).append(u))
            for u in links:
                u = u.split("#")[0]
                if urlsplit(u).netloc == sess["netloc"] and ext_of(u) in PAGE_EXT and not BAD_CRAWL.search(u) \
                        and u not in queued and len(queued) < 2000:
                    queued.add(u)
                    queue.append(u)
            assets = [u for u in dict.fromkeys(assets)
                      if third_party or registrable_domain(urlsplit(u).netloc) == sess["reg"]]
            dl_many(assets)

        if job["cancel"]:
            job.update(status="cancelled", phase="Cancelled")
            return

        job.update(phase="Rewriting links for offline use", pct=80)
        for rel, burl, ct in html_files:
            fp = root / rel
            out = process_html(decode_bytes(fp.read_bytes(), ct), burl, mapper=offline_mapper(url2path, rel))
            fp.write_text(out, encoding="utf-8")
        for rel, burl, ct in css_files:
            fp = root / rel
            fp.write_text(process_css(decode_bytes(fp.read_bytes(), ct), burl, mapper=offline_mapper(url2path, rel)),
                          encoding="utf-8")

        start_rel = url2path.get(sess["start"]) or (pages[0]["path"] if pages else "")
        if start_rel:
            (root / "index.html").write_text(
                '<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url='
                + quote(start_rel) + '"><a href="' + quote(start_rel) + '">Open saved site</a>', encoding="utf-8")
        (root / "manifest.json").write_text(json.dumps(
            {"target": sess["start"], "saved": time.strftime("%Y-%m-%d %H:%M:%S"), "pages": pages,
             "files": files, "errors": errors}, indent=2), encoding="utf-8")
        (root / "analysis.json").write_text(json.dumps(sess.get("analysis") or {}, indent=2), encoding="utf-8")

        if not package:
            job.update(status="done", phase="Done", pct=100)
            return

        job.update(phase="Creating ZIP", pct=88)
        zpath = work / f"{name}.zip"
        with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
            for fp in root.rglob("*"):
                if fp.is_file():
                    z.write(fp, Path(name) / fp.relative_to(root))
        job["zip"] = str(zpath)
        job["zip_name"] = zpath.name

        job.update(phase="Saving to file manager", pct=94)
        dest, shared = storage_dir()
        try:
            if dest != work:
                shutil.copy2(zpath, dest / zpath.name)
                shutil.copytree(root, dest / name)
            job["saved_to"] = str(dest / name)
            job["saved_zip"] = str(dest / zpath.name)
            job["shared"] = shared
        except OSError as e:
            job["saved_to"] = str(root)
            job["saved_zip"] = str(zpath)
            job["shared"] = False
            log(f"! could not copy to shared storage: {e}")
        job.update(status="done", phase="Done", pct=100)
    except Exception as e:  # noqa: BLE001
        job.update(status="error", phase="Failed", error=str(e))


# --------------------------------------------------------------------------
# Servers
# --------------------------------------------------------------------------
class BaseHandler(BaseHTTPRequestHandler):
    port = PORT

    def log_message(self, *a):
        pass

    def host_ok(self):
        return self.headers.get("Host", "") in (f"{HOST}:{self.port}", f"localhost:{self.port}")

    def send_body(self, body, ctype="application/json", status=200, extra=None):
        self.send_response(status)
        self.send_header("Content-Type", ctype if "charset" in ctype or not ctype.startswith("text") else ctype + "; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, status=200):
        self.send_body(json.dumps(obj).encode("utf-8"), "application/json", status)


class EditorHandler(BaseHandler):
    port = PORT

    def do_GET(self):
        if not self.host_ok():
            return self.send_body(b"Forbidden", "text/plain", 403)
        path = urlsplit(self.path).path
        if path in ("/", "/index.html"):
            if not EDITOR.exists():
                return self.send_body(b"editor.html is missing next to hex.py", "text/plain", 404)
            return self.send_body(EDITOR.read_bytes(), "text/html")
        if path in ("/modify", "/modify.html"):
            if not MODIFIER_HTML.exists():
                return self.send_body(b"modify.html is missing next to hex.py", "text/plain", 404)
            return self.send_body(MODIFIER_HTML.read_bytes(), "text/html")
        if path == "/api/mod/sites":
            cfg = load_cfg()
            slot = active_slot(cfg)
            has_groq = bool(get_key(cfg))
            return self.send_json({
                "success": True,
                "sites": list_saved(),
                "slot": cfg["slot"],
                "active": slot,
                "slots": [{"id": k, **v} for k, v in cfg["slots"].items()],
                "custom": cfg.get("custom"),
                "has_key": has_groq,
                "has_groq": has_groq,
            })
        if path.startswith("/dl/"):
            parts = path.split("/")
            if len(parts) == 4 and re.fullmatch(r"[\w.-]+", parts[2]) and re.fullmatch(r"[\w.-]+\.zip", parts[3]):
                fp = SAVED / parts[2] / parts[3]
                if fp.is_file():
                    return send_file_range(self, fp, {"Content-Disposition": f'attachment; filename="{parts[3]}"'})
            return self.send_body(b"Not found", "text/plain", 404)
        if path.startswith("/api/job/"):
            job = JOBS.get(path.rsplit("/", 1)[-1])
            if not job:
                return self.send_json({"success": False, "error": "Unknown job"}, 404)
            keys = ("status", "phase", "pct", "done", "total", "files", "bytes", "errors", "pages",
                    "current", "saved_to", "saved_zip", "shared", "zip_name", "error")
            out = {k: job.get(k) for k in keys}
            out["log"] = job["log"][-14:]
            out["id"] = job["id"]
            return self.send_json({"success": True, **out})
        if path.startswith("/download/") and path.endswith(".zip"):
            job = JOBS.get(path[len("/download/"):-4])
            if not job or not job.get("zip") or not os.path.exists(job["zip"]):
                return self.send_body(b"Not ready", "text/plain", 404)
            size = os.path.getsize(job["zip"])
            self.send_response(200)
            self.send_header("Content-Type", "application/zip")
            self.send_header("Content-Length", str(size))
            self.send_header("Content-Disposition", f'attachment; filename="{job["zip_name"]}"')
            self.end_headers()
            with open(job["zip"], "rb") as f:
                shutil.copyfileobj(f, self.wfile)
            return
        return self.send_body(b"Not found", "text/plain", 404)

    def do_POST(self):
        if not self.host_ok():
            return self.send_body(b"Forbidden", "text/plain", 403)
        origin = self.headers.get("Origin")
        if (origin and urlsplit(origin).netloc != self.headers.get("Host")) or self.headers.get("X-Hex") != "1":
            return self.send_json({"success": False, "error": "Request blocked"}, 403)
        try:
            n = min(int(self.headers.get("Content-Length", 0)), 262144)
            body = json.loads(self.rfile.read(n) or b"{}")
            route = urlsplit(self.path).path

            # ---- web modifier endpoints (modify.html) ----
            if route == "/api/mod/open":
                return self.send_json(web_mod_open(body.get("id", ""), int(body.get("pages", 1))))
            if route == "/api/mod/chat":
                return self.send_json(web_mod_chat(body.get("id", ""), body.get("message", ""), body.get("section", "")))
            if route == "/api/mod/file":
                return self.send_json(web_mod_file(body.get("id", ""), body.get("path", "")))
            if route == "/api/mod/model":
                return self.send_json(web_mod_model(body.get("slot", ""), body.get("custom")))
            if route == "/api/mod/key":
                return self.send_json(web_mod_key(body.get("key", "")))
            if route == "/api/mod/undo":
                return self.send_json(web_mod_undo(body.get("id", "")))
            if route == "/api/mod/reset":
                return self.send_json(web_mod_reset(body.get("id", "")))
            if route == "/api/mod/clear":
                return self.send_json(web_mod_clear(body.get("id", "")))
            if route == "/api/mod/download":
                return self.send_json(web_mod_download(body.get("id", "")))

            # ---- editor / recon endpoints (editor.html) ----
            if route == "/api/extract":
                url = (body.get("url") or "").strip()
                if not url:
                    return self.send_json({"success": False, "error": "No URL provided"}, 400)
                return self.send_json(analyze(url))
            sess = SESSIONS.get(body.get("sid", ""))
            if not sess:
                return self.send_json({"success": False, "error": "Session expired. Extract the site again."}, 400)
            if route == "/api/page":
                return self.send_json(page_info(sess, body.get("path", "")))
            if route == "/api/download":
                job = new_job()
                jid = job["id"]
                pages = max(1, min(int(body.get("max_pages", 1)), 200))
                threading.Thread(target=run_download, args=(job, sess, pages, bool(body.get("third_party", True))),
                                 daemon=True).start()
                return self.send_json({"success": True, "job": jid})
            if route == "/api/cancel":
                job = JOBS.get(body.get("job", ""))
                if job:
                    job["cancel"] = True
                return self.send_json({"success": True})
            if route == "/api/update_analysis":
                sess = SESSIONS.get(body.get("sid", ""))
                if not sess or not sess.get("analysis"):
                    return self.send_json({"success": False, "error": "Session expired. Extract again."}, 400)
                field = body.get("field", "")
                allowed = {"links", "emails", "phones", "social", "endpoints", "assets", "comments", "jsonld"}
                if field not in allowed or not isinstance(body.get("value"), list):
                    return self.send_json({"success": False, "error": "Bad field"}, 400)
                sess["analysis"][field] = body["value"]
                sid = sess.get("saved_id")
                if sid:
                    p = SAVED / sid / "analysis.json"
                    if p.is_file():
                        try:
                            p.write_text(json.dumps(sess["analysis"]), encoding="utf-8")
                        except OSError:
                            pass
                return self.send_json({"success": True})
            if route == "/api/modify":
                global _pending_modify
                sid = sess.get("saved_id")
                if not sid or not (SAVED / sid / "meta.json").is_file():
                    return self.send_json({"success": False, "error": "Saved site record not found. Extract again."}, 400)
                meta = json.loads((SAVED / sid / "meta.json").read_text(encoding="utf-8"))
                meta["has_work"] = (SAVED / sid / "work").is_dir() and bool(list_work_files(SAVED / sid / "work"))
                _pending_modify = meta
                try:
                    os.write(_wake_w, b"1")
                except OSError:
                    pass
                if shutil.which("termux-toast"):
                    try:
                        subprocess.Popen(["termux-toast", "Switch to Termux: REA Modifier ready!"],
                                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    except OSError:
                        pass
                return self.send_json({"success": True, "id": sid, "url": sess["start"], "netloc": sess["netloc"],
                                       "web_url": f"http://{HOST}:{PORT}/modify?id={quote(sid)}"})
            return self.send_json({"success": False, "error": "Unknown endpoint"}, 404)
        except AIError as e:
            return self.send_json({"success": False, "error": str(e)}, 400)
        except ValueError as e:
            return self.send_json({"success": False, "error": str(e)}, 400)
        except requests.exceptions.SSLError:
            return self.send_json({"success": False, "error": "TLS/SSL error connecting to target"}, 502)
        except requests.exceptions.ConnectionError:
            return self.send_json({"success": False, "error": "Could not connect to target host"}, 502)
        except requests.exceptions.Timeout:
            return self.send_json({"success": False, "error": "Target timed out"}, 504)
        except Exception as e:  # noqa: BLE001
            return self.send_json({"success": False, "error": str(e)}, 500)


class PreviewHandler(BaseHandler):
    """Serves the mirrored site. Only hosts that the extracted site itself references are reachable."""
    port = PREVIEW_PORT

    def do_POST(self):
        self.send_body(b"Form submission is disabled in preview", "text/plain", 405)

    def do_GET(self):
        if not self.host_ok():
            return self.send_body(b"Forbidden", "text/plain", 403)
        if self.path.startswith("/work/"):
            return serve_work(self)
        u = urlsplit(self.path)
        segs = u.path.split("/", 4)
        if len(segs) < 4 or segs[1] != "site":
            return self.send_body(b"Not found", "text/plain", 404)
        sess = SESSIONS.get(segs[2])
        netloc, rest = segs[3], (segs[4] if len(segs) > 4 else "")
        if not sess:
            return self.send_body(b"Session expired. Extract the site again.", "text/plain", 404)
        if not host_allowed(sess, netloc):
            return self.send_body(b"Host not part of this site", "text/plain", 403)
        scheme = sess["schemes"].get(netloc, sess["scheme"])
        upstream = f"{scheme}://{netloc}/{rest}" + (f"?{u.query}" if u.query else "")
        h = dict(REQ_HEADERS)
        h.update({"Referer": sess["origin"] + "/", "Accept-Encoding": "identity"})
        if self.headers.get("Accept"):
            h["Accept"] = self.headers["Accept"]
        if self.headers.get("Range"):
            h["Range"] = self.headers["Range"]
        cors = {"Access-Control-Allow-Origin": "*"}
        try:
            r = requests.get(upstream, headers=h, stream=True, timeout=20, allow_redirects=True)
        except requests.RequestException as e:
            return self.send_body(f"Upstream error: {e}".encode(), "text/plain", 502, cors)

        final = r.url.split("#")[0]
        if r.history:
            loc = preview_mapper(sess)(final, "asset")
            if loc != self.path:
                r.close()
                return self.send_body(b"", "text/plain", 302, {**cors, "Location": loc})

        ct = r.headers.get("Content-Type", "")
        low = ct.lower()
        if "html" in low or "text/css" in low:
            try:
                buf = bytearray()
                for chunk in r.iter_content(65536):
                    buf += chunk
                    if len(buf) > MAX_PAGE:
                        break
            finally:
                r.close()
            text = decode_bytes(bytes(buf), ct)
            mapper = preview_mapper(sess)
            if "html" in low:
                out = process_html(text, final, mapper, None, build_shim(sess, final))
                ctype = "text/html; charset=utf-8"
            else:
                out = process_css(text, final, mapper)
                ctype = "text/css; charset=utf-8"
            return self.send_body(out.encode("utf-8"), ctype, r.status_code, cors)

        self.send_response(r.status_code)
        for k in ("Content-Type", "Content-Range", "Accept-Ranges"):
            if r.headers.get(k):
                self.send_header(k, r.headers[k])
        if r.headers.get("Content-Length") and not r.headers.get("Content-Encoding"):
            self.send_header("Content-Length", r.headers["Content-Length"])
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        try:
            for chunk in r.iter_content(65536):
                self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass
        finally:
            r.close()


# --------------------------------------------------------------------------
# REA modifier: saved sites + 100% Groq LPU coding agent
# --------------------------------------------------------------------------
GROQ_URL = "https://api.groq.com/openai/v1"
GEMINI_URL = "https://generativelanguage.googleapis.com/v1beta/openai"
DEFAULT_CFG = {
    "groq_key": "",
    "gemini_key": "",
    "slot": "oss120",
    "custom": None,
    "slots": {
        "gflash": {"label": "Gemini Flash · fast + big context", "model": "gemini-3.8-flash",
                   "provider": "gemini", "ctx_chars": 400_000, "max_tokens": 32_000},
        "gpro": {"label": "Gemini Pro · smartest (may need paid)", "model": "gemini-3.8-pro",
                 "provider": "gemini", "ctx_chars": 400_000, "max_tokens": 32_000},
        "qwen": {"label": "Qwen 3.8 27B  · coding", "model": "qwen/qwen3.8-27b",
                 "ctx_chars": 60_000, "max_tokens": 16_000},
        "oss120": {"label": "GPT-OSS 120B  · 500 tok/s deep coder", "model": "openai/gpt-oss-120b",
                   "ctx_chars": 60_000, "max_tokens": 16_000, "reasoning_effort": "low"},
        "llama70": {"label": "Llama 3.3 70B · 280 tok/s versatile", "model": "llama-3.3-70b-versatile",
                    "ctx_chars": 60_000, "max_tokens": 16_000},
        "oss20": {"label": "GPT-OSS 20B   · 1000 tok/s instant", "model": "openai/gpt-oss-20b",
                  "ctx_chars": 60_000, "max_tokens": 16_000, "reasoning_effort": "low"},
        "llama8": {"label": "Llama 3.1 8B  · 560 tok/s light", "model": "llama-3.1-8b-instant",
                   "ctx_chars": 40_000, "max_tokens": 8_000},
    },
}
TEXT_EXT = {".html", ".htm", ".css", ".js", ".mjs", ".json", ".svg", ".txt", ".xml", ".md",
            ".php", ".webmanifest", ".csv"}
SKIP_DIRS = {".hexrea", "_original_source"}
SKIP_FILES = {"manifest.json", "analysis.json"}
MAX_ROUNDS = 8

SYSTEM_PROMPT = """You are HEX REA Coding Agent — a fast, surgical front-end engineer powered by Groq LPU.

YOU HAVE FULL ACCESS TO EVERYTHING
You have access to 100% of the extracted site:
- All workspace files (HTML, CSS, JS, JSON, SVG, etc.), the raw `[1]` `source.html`, and the full `[1]` recon `analysis.json`.
- If a huge file is summarized/excerpted to fit fast Groq latency, use `<<<GREP path text>>>` or `<<<READ path start_line end_line>>>` to inspect ANY exact line or section immediately. Never say you lack access.

CRITICAL RULE — NEVER REBUILD FROM SCRATCH
1. NEVER rewrite or rebuild an existing site or file from scratch. Strictly CHANGE and ADD only what the user requested, keeping all original layout, classes, styles, scripts, and assets intact.
2. You MUST use `<<<EDIT path>>>` with small surgical `SEARCH` / `REPLACE` blocks on existing files. (`<<<FILE path>>>` is ONLY for creating brand-new files that do not exist yet.)
3. GO STRAIGHT TO THE POINT: When the request is clear, output the `<<<EDIT>>>` block(s) + 1–2 crisp sentences explaining what you modified/added.
4. TARGET SECTION / EXTRACTED URL: If a target section, page, or extracted URL is specified, edit only that target.
5. CLARIFY ONLY IF UNCLEAR: If a request is genuinely ambiguous (missing placement, text, or which extracted page), list 2–3 exact sections/URLs you see and ask 1 short question.
6. ANALYSIS QUESTIONS: If asked about recon, security, tech stack, or extracted links, answer directly using exact values from ANALYSIS with zero edit blocks.
7. SELF-REPAIR: If an EDIT fails, check the returned lines (or `<<<GREP>>>`), fix your `SEARCH` snippet (keep `SEARCH` to a unique 60–250 char snippet on minified files), and resend ONLY the failed edit. Never wrap blocks in ``` markdown fences.

PROTOCOL (exact literal syntax)
Edit existing file:
<<<EDIT path/from/tree.html>>>
<<<<<<< SEARCH
exact existing lines
=======
updated or added lines
>>>>>>> REPLACE
<<<END>>>

Create brand-new file ONLY:
<<<FILE path/to/new_file.css>>>
new file contents
<<<END>>>

Delete file:  <<<DELETE path/to/file>>>
Read file / lines:  <<<READ path/to/file>>>  or  <<<READ path/to/file 1 300>>>
Search inside any file:  <<<GREP path/to/file search_text>>>"""


# ---- config ---------------------------------------------------------------
def load_cfg():
    cfg = json.loads(json.dumps(DEFAULT_CFG))
    try:
        user = json.loads(CONF_FILE.read_text(encoding="utf-8"))
        for k in ("groq_key", "gemini_key", "slot", "custom"):
            if k in user:
                cfg[k] = user[k]
    except (OSError, ValueError):
        pass
    if cfg["slot"] != "custom" and cfg["slot"] not in cfg["slots"]:
        cfg["slot"] = "oss120"
    return cfg


def save_cfg(cfg):
    CONF_DIR.mkdir(parents=True, exist_ok=True)
    out = {k: v for k, v in cfg.items() if k != "slots"}
    CONF_FILE.write_text(json.dumps(out, indent=2), encoding="utf-8")
    try:
        os.chmod(CONF_FILE, 0o600)
    except OSError:
        pass


def get_key(cfg, provider=None):
    """provider None -> any available key (groq first)."""
    groq = os.environ.get("GROQ_API_KEY") or cfg.get("groq_key") or ""
    gem = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY") or cfg.get("gemini_key") or ""
    if provider == "groq":
        return groq
    if provider == "gemini":
        return gem
    return groq or gem


def slot_provider(slot):
    p = slot.get("provider")
    if p:
        return p
    return "gemini" if str(slot.get("model", "")).startswith("gemini") else "groq"


def usable_slot(cfg):
    """Active slot, or the first slot of a provider that has a key if the active one has none."""
    slot = active_slot(cfg)
    if get_key(cfg, slot_provider(slot)):
        return slot
    other = "gemini" if slot_provider(slot) == "groq" else "groq"
    if get_key(cfg, other):
        for v in cfg["slots"].values():
            if slot_provider(v) == other:
                return v
    return slot


def ensure_key(cfg, force=False):
    if get_key(cfg) and not force:
        return True
    print(Fore.YELLOW + "\n  Groq API key needed (free at https://console.groq.com/keys, starts with gsk_).")
    print(Fore.YELLOW + f"  Saved only on this phone in {CONF_FILE} (or set GROQ_API_KEY).")
    try:
        key = getpass.getpass(Fore.GREEN + "  Paste Groq key (hidden, Enter to cancel): " + Style.RESET_ALL).strip()
    except (EOFError, KeyboardInterrupt):
        return False
    if not key:
        return False
    if not key.startswith("gsk_"):
        print(Fore.RED + "  [!] That does not look like a Groq key (expected gsk_...).")
        return False
    cfg["groq_key"] = key
    save_cfg(cfg)
    print(Fore.GREEN + "  [✓] Groq key saved.\n")
    return True


def active_slot(cfg):
    if cfg["slot"] == "custom" and cfg.get("custom"):
        c = {"label": "Custom Groq", "ctx_chars": 140_000, "max_tokens": 16_000}
        c.update(cfg["custom"])
        return c
    return cfg["slots"].get(cfg["slot"]) or cfg["slots"]["qwen"]


# ---- saved sites ------------------------------------------------------------
def new_job():
    job = {"id": uuid.uuid4().hex[:10], "status": "running", "phase": "Starting", "pct": 2, "done": 0,
           "total": 1, "files": 0, "bytes": 0, "errors": 0, "pages": 0, "current": "", "log": [],
           "cancel": False}
    JOBS[job["id"]] = job
    return job


def save_site(sess, html):
    """Remember every extraction so the REA modifier can load it later."""
    try:
        a = sess["analysis"]
        sid = f"{sess['netloc'].replace(':', '_')}_{hashlib.md5(sess['start'].encode()).hexdigest()[:6]}"
        d = SAVED / sid
        d.mkdir(parents=True, exist_ok=True)
        (d / "source.html").write_text(html, encoding="utf-8")
        (d / "analysis.json").write_text(json.dumps(a), encoding="utf-8")
        (d / "meta.json").write_text(json.dumps({
            "id": sid, "url": sess["start"], "netloc": sess["netloc"], "title": a["title"],
            "saved": time.strftime("%Y-%m-%d %H:%M")}), encoding="utf-8")
        sess["saved_id"] = sid
    except OSError:
        pass


def list_saved():
    out = []
    if SAVED.is_dir():
        for d in SAVED.iterdir():
            try:
                m = json.loads((d / "meta.json").read_text(encoding="utf-8"))
            except (OSError, ValueError):
                continue
            w = d / "work"
            m["has_work"] = w.is_dir() and bool(list_work_files(w))
            out.append(m)
    return sorted(out, key=lambda m: m["saved"], reverse=True)


def get_saved_site(site_id):
    if not site_id or not re.fullmatch(r"[\w.-]+", site_id):
        raise ValueError("Invalid site ID")
    d = SAVED / site_id
    if not (d / "meta.json").is_file():
        raise ValueError("Extracted site not found")
    m = json.loads((d / "meta.json").read_text(encoding="utf-8"))
    w = d / "work"
    m["has_work"] = w.is_dir() and bool(list_work_files(w))
    return m


# ---- workspace files --------------------------------------------------------
def list_work_files(work):
    out = []
    if not work.is_dir():
        return out
    for fp in sorted(work.rglob("*")):
        if not fp.is_file():
            continue
        rel = fp.relative_to(work).as_posix()
        if rel.split("/")[0] in SKIP_DIRS or rel in SKIP_FILES:
            continue
        out.append((rel, fp.stat().st_size))
    return out


def read_text(fp):
    try:
        return fp.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None


def entry_rel(work):
    try:
        m = json.loads((work / "manifest.json").read_text(encoding="utf-8"))
        if m.get("pages"):
            return m["pages"][0]["path"]
    except (OSError, ValueError, KeyError):
        pass
    htmls = [r for r, _ in list_work_files(work) if r.endswith(".html")]
    return htmls[0] if htmls else ""


def resolve_path(work, p, lenient=True, allow_site_dir=None):
    p = re.sub(r"^\./", "", (p or "").strip().strip("`'\"").replace("\\", "/"))
    if not p or p.startswith("/") or ".." in p.split("/"):
        return None
    if allow_site_dir and p in ("source.html", "analysis.json"):
        sfp = (allow_site_dir / p).resolve()
        if allow_site_dir.resolve() in sfp.parents and sfp.is_file():
            return sfp
    if p.split("/")[0] in SKIP_DIRS:
        if not (allow_site_dir and p.split("/")[0] == "_original_source"):
            return None
    root = work.resolve()
    fp = (root / p).resolve()
    if root != fp and root not in fp.parents:
        return None
    if fp.exists() or not lenient:
        return fp
    cands = [r for r, _ in list_work_files(root) if r == p or r.endswith("/" + p)]
    return (root / cands[0]) if len(cands) == 1 else None


def html_landmarks(text, max_items=24):
    hits = []
    rx = re.compile(r"<(header|nav|main|section|form|footer|h1|h2)\b[^>]*>", re.I)
    for idx, ln in enumerate(text.splitlines(), 1):
        m = rx.search(ln)
        if m:
            hits.append(f"L{idx}: {m.group(0)[:90]}")
            if len(hits) >= max_items:
                break
    return hits


def compact_analysis(a, cap=18_000):
    b = {k: v for k, v in a.items() if k != "local_url"}
    raw_assets = a.get("assets", [])
    kinds = {}
    for x in raw_assets:
        kinds[x["kind"]] = kinds.get(x["kind"], 0) + 1
    b["assets_summary"] = {"total": len(raw_assets), "by_kind": kinds,
                           "note": "Use <<<READ analysis.json>>> or <<<GREP analysis.json text>>> for all asset URLs."}
    b["assets"] = [f"{x['kind']} {x['url']}" for x in raw_assets[:40]]
    s = json.dumps(b, ensure_ascii=False, separators=(",", ":"))
    return s if len(s) <= cap else s[:cap] + "...[truncated; use <<<READ analysis.json>>> for full JSON]"


def build_context(meta, analysis, work, budget, focus_section="", site_dir=None, lean=False):
    files = list_work_files(work)
    entry = entry_rel(work)
    lines = [f"ORIGINAL URL: {meta['url']}", f"WORKSPACE ENTRY PAGE: {entry}",
             f"FILES: {len(files)}"]
    if site_dir and (site_dir / "source.html").is_file():
        lines.append(f"RAW [1] EXTRACTED FILES READABLE: source.html ({(site_dir / 'source.html').stat().st_size} bytes), analysis.json")
    if focus_section:
        lines.append(f"USER SELECTED SECTION / TARGET: {focus_section}")
    lines += ["", "FILE TREE (path · bytes):"]
    if lean:
        tf = [f for f in files if posixpath.splitext(f[0])[1].lower() in TEXT_EXT]
        lines += [f"  {r} · {s}" for r, s in tf[:70]]
        if len(tf) > 70:
            lines.append(f"  ... {len(tf) - 70} more text files (find them with <<<GREP path text>>>)")
        lines.append(f"  (+ {len(files) - len(tf)} images/fonts/binary files not shown)")
    else:
        lines += [f"  {r} · {s}" for r, s in files]
    head = "\n".join(lines)
    ana = compact_analysis(analysis, cap=(1_200 if lean else min(18_000, max(8_000, budget // 6))))
    lean_only = None
    if lean:
        lean_only = set()
        fs = (focus_section or "").strip().lower().strip("/")
        base_fs = posixpath.basename(fs)
        for r, _ in files:
            rl = r.lower()
            if fs and (rl == fs or rl.endswith("/" + fs) or (base_fs and posixpath.basename(rl) == base_fs and "." in base_fs)):
                lean_only.add(r)
        if not lean_only:
            lean_only.add(entry)
    used = len(head) + len(ana)

    def prio(item):
        r, _ = item
        e = posixpath.splitext(r)[1].lower()
        return (0 if r == entry else 1, {".html": 0, ".htm": 0, ".css": 1, ".js": 2, ".mjs": 2}.get(e, 3), r)

    included, partial, skipped = [], [], []
    for rel, size in sorted([f for f in files if posixpath.splitext(f[0])[1].lower() in TEXT_EXT], key=prio):
        text = read_text(work / rel)
        if text is None:
            skipped.append(f"  {rel} · not valid UTF-8")
            continue
        if lean:
            if rel not in lean_only:
                continue
            room = max(1_500, budget - used)
            if len(text) <= room:
                used += len(text)
                included.append(f"----- FILE: {rel} -----\n{text}\n----- END FILE -----")
            else:
                marks = html_landmarks(text) if rel.endswith((".html", ".htm")) else []
                mark_txt = ("LANDMARKS:\n  " + "\n  ".join(marks[:12]) + "\n") if marks else ""
                h = text[: int(room * 0.75)]
                used += len(h)
                partial.append(f"----- START OF {rel} ({len(text):,} chars, {text.count(chr(10)) + 1:,} lines) -----\n{mark_txt}{h}\n"
                               f"... [REST OMITTED — use <<<READ {rel} start_line end_line>>> or <<<GREP {rel} text>>>] ...\n----- END EXCERPT -----")
            continue
        if used + len(text) <= budget:
            used += len(text)
            included.append(f"----- FILE: {rel} -----\n{text}\n----- END FILE -----")
        elif budget - used >= 12_000:
            total_lines = text.count("\n") + 1
            h_sz = min(10_000, max(4_000, (budget - used) // 2))
            t_sz = min(6_000, max(2_500, (budget - used) // 3))
            head_chunk = text[:h_sz]
            tail_chunk = text[-t_sz:]
            marks = html_landmarks(text) if rel.endswith((".html", ".htm")) else []
            mark_txt = ("\nLANDMARKS:\n  " + "\n  ".join(marks) + "\n") if marks else ""
            used += len(head_chunk) + len(tail_chunk) + len(mark_txt)
            partial.append(
                f"----- EXCERPTED FILE: {rel} ({len(text):,} chars, {total_lines:,} lines) -----\n"
                f"{mark_txt}"
                f"[START OF FILE]\n{head_chunk}\n"
                f"... [MIDDLE OMITTED — use <<<GREP {rel} text>>> or <<<READ {rel} start_line end_line>>> to inspect exact lines] ...\n"
                f"[END OF FILE]\n{tail_chunk}\n----- END EXCERPT -----"
            )
        else:
            skipped.append(f"  {rel} · {size:,} bytes (use <<<GREP {rel} text>>> or <<<READ {rel}>>>)")
    binary = [] if lean else [f"  {r} · {s}" for r, s in files if posixpath.splitext(r)[1].lower() not in TEXT_EXT]
    if lean:
        out_lean_note = "LEAN MODE: only the target file is shown. Ask for any other file you need with <<<READ path>>> or <<<GREP path text>>> BEFORE editing it."
        skipped = [out_lean_note]
    out = ["=== HEX REA SITE CONTEXT ===", head, "",
           "=== RECON ANALYSIS (from HEX REA [1]) ===", ana, "",
           "=== FILE CONTENTS ===", "\n".join(included)]
    if partial:
        out += ["", "=== LARGE FILES (EXCERPTED FOR SPEED — INSPECT FULL FILE WITH GREP/READ) ===", "\n".join(partial)]
    if skipped:
        out += ["", "=== MORE FILES (INSPECT WITH <<<READ path>>> OR <<<GREP path text>>>) ===", "\n".join(skipped)]
    if binary:
        out += ["", "=== BINARY FILES (paths only) ===", "\n".join(binary[:300])]
    return "\n".join(out), len(included), len(files)


# ---- edit & inspection protocol ---------------------------------------------
RE_FILE = re.compile(r"<<<FILE\s+(.+?)>>>\r?\n(.*?)\r?\n?<<<END>>>", re.S)
RE_EDIT = re.compile(r"<<<EDIT\s+(.+?)>>>\r?\n(.*?)\r?\n?<<<END>>>", re.S)
RE_BLOCK = re.compile(r"<<<<<<< SEARCH\r?\n(.*?)\r?\n=======\r?\n(.*?)\r?\n?>>>>>>> REPLACE", re.S)
RE_READ = re.compile(r"<<<READ\s+([^\n>]+?)>>>")
RE_GREP = re.compile(r"<<<GREP\s+(\S+)\s+(.+?)>>>")
RE_DEL = re.compile(r"<<<DELETE\s+(.+?)>>>")


def strip_fences(body):
    ls = body.split("\n")
    if ls and ls[0].strip().startswith("```"):
        ls = ls[1:]
        if ls and ls[-1].strip() == "```":
            ls = ls[:-1]
    return "\n".join(ls)


def strip_blocks(text):
    for rx in (RE_EDIT, RE_FILE, RE_READ, RE_GREP, RE_DEL):
        text = rx.sub("", text)
    text = re.sub(r"(?m)^```[\w-]*\s*$\n?", "", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


def loose_replace(content, search, repl):
    """Match ignoring trailing whitespace/blank edge lines. Returns new content or None."""
    cl, sl = content.split("\n"), search.split("\n")
    while sl and not sl[0].strip():
        sl.pop(0)
    while sl and not sl[-1].strip():
        sl.pop()
    if not sl:
        return None
    ncl, nsl = [l.rstrip() for l in cl], [l.rstrip() for l in sl]
    hits = [i for i in range(len(ncl) - len(nsl) + 1) if ncl[i:i + len(nsl)] == nsl]
    if len(hits) != 1:
        return None
    i = hits[0]
    return "\n".join(cl[:i] + repl.split("\n") + cl[i + len(nsl):])


def apply_response(work, text, backup, ops_out=None):
    work = work.resolve()
    done, errs = [], []

    def keep(rel, fp):
        if rel not in backup:
            backup[rel] = fp.read_bytes() if fp.exists() else None

    for path, body in RE_EDIT.findall(text):
        fp = resolve_path(work, path)
        if not fp or not fp.is_file():
            msg = f"EDIT {path}: file is not in the file tree"
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "EDIT", "path": path, "ok": False, "error": msg, "blocks": []})
            continue
        rel = fp.relative_to(work).as_posix()
        raw_content = read_text(fp)
        if raw_content is None:
            msg = f"EDIT {rel}: not a UTF-8 text file"
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "EDIT", "path": rel, "ok": False, "error": msg, "blocks": []})
            continue
        content = raw_content.replace("\r\n", "\n")
        blocks = RE_BLOCK.findall(body)
        if not blocks:
            msg = f"EDIT {rel}: no valid SEARCH/REPLACE block"
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "EDIT", "path": rel, "ok": False, "error": msg, "blocks": []})
            continue
        ok, op_blocks = 0, []
        for raw_search, raw_repl in blocks:
            search = raw_search.replace("\r\n", "\n")
            repl = raw_repl.replace("\r\n", "\n")
            n = content.count(search)
            if n == 1:
                content, ok = content.replace(search, repl, 1), ok + 1
                op_blocks.append({"search": search, "replace": repl, "ok": True})
            elif n > 1:
                msg = f"EDIT {rel}: SEARCH text matches {n} places, add more surrounding lines"
                errs.append(msg)
                op_blocks.append({"search": search, "replace": repl, "ok": False, "error": msg})
            else:
                new = loose_replace(content, search, repl)
                if new is not None:
                    content, ok = new, ok + 1
                    op_blocks.append({"search": search, "replace": repl, "ok": True})
                else:
                    msg = f"EDIT {rel}: SEARCH text not found: {search.strip()[:70]!r}"
                    errs.append(msg)
                    op_blocks.append({"search": search, "replace": repl, "ok": False, "error": msg})
        if ok:
            keep(rel, fp)
            fp.write_text(content, encoding="utf-8")
            done.append(f"edited  {rel}  ({ok}/{len(blocks)} blocks)")
        if ops_out is not None:
            ops_out.append({"op": "EDIT", "path": rel, "ok": ok == len(blocks), "applied": ok,
                            "total": len(blocks), "blocks": op_blocks})

    for path, body in RE_FILE.findall(text):
        fp = resolve_path(work, path, lenient=False)
        if not fp:
            msg = f"FILE {path}: invalid path"
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "FILE", "path": path, "ok": False, "error": msg})
            continue
        rel = fp.relative_to(work).as_posix()
        if fp.exists() and fp.stat().st_size > 400:
            msg = f"FILE {rel}: rejected! Do NOT rebuild existing files from scratch — use <<<EDIT {rel}>>> SEARCH/REPLACE to change or add only what was asked."
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "FILE", "path": rel, "ok": False, "error": msg})
            continue
        existed = fp.exists()
        keep(rel, fp)
        fp.parent.mkdir(parents=True, exist_ok=True)
        clean = strip_fences(body)
        fp.write_text(clean + "\n", encoding="utf-8")
        done.append(("rewrote " if existed else "created ") + " " + rel)
        if ops_out is not None:
            ops_out.append({"op": "REWRITE" if existed else "CREATE", "path": rel, "ok": True,
                            "content": clean[:4000]})

    for path in RE_DEL.findall(text):
        fp = resolve_path(work, path)
        if not fp or not fp.is_file():
            msg = f"DELETE {path}: file is not in the file tree"
            errs.append(msg)
            if ops_out is not None:
                ops_out.append({"op": "DELETE", "path": path, "ok": False, "error": msg})
            continue
        rel = fp.relative_to(work).as_posix()
        keep(rel, fp)
        fp.unlink()
        done.append(f"deleted {rel}")
        if ops_out is not None:
            ops_out.append({"op": "DELETE", "path": rel, "ok": True})
    return done, errs


def read_files_msg(work, specs, site_dir=None, max_chars=9_000):
    out = []
    for raw in specs:
        parts = raw.strip().split()
        p = (parts[0] if parts else "").strip("`'\"")
        s_line = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else None
        e_line = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else None
        fp = resolve_path(work, p, allow_site_dir=site_dir)
        t = read_text(fp) if fp and fp.is_file() else None
        rel = p
        if fp and fp.exists():
            try:
                rel = fp.relative_to(work.resolve()).as_posix()
            except ValueError:
                rel = fp.name
        if not fp or not fp.exists():
            body = "(not found)"
        elif t is None:
            body = "(binary or non-UTF-8 file)"
        elif s_line is not None:
            lines = t.splitlines()
            a = max(1, s_line)
            b = min(len(lines), e_line or (a + 200))
            chunk = "\n".join(f"{i}: {lines[i - 1]}" for i in range(a, b + 1))
            body = f"[Lines {a}-{b} of {len(lines)}]\n" + chunk[:max_chars]
        else:
            body = t[:max_chars] + (f"\n... [TRUNCATED at {max_chars:,} chars of {len(t):,}; use <<<READ {rel} start_line end_line>>> or <<<GREP {rel} text>>>]" if len(t) > max_chars else "")
        out.append(f"----- FILE: {rel} -----\n{body}\n----- END FILE -----")
    return "\n".join(out)


def grep_files_msg(work, queries, site_dir=None):
    out = []
    for path, pattern in queries:
        path = path.strip("`'\"")
        fp = resolve_path(work, path, allow_site_dir=site_dir)
        t = read_text(fp) if fp and fp.is_file() else None
        if not fp or t is None:
            out.append(f"[GREP {path}: file not found or binary]")
            continue
        pat = pattern.strip().strip("`'\"")
        lines = t.splitlines()
        hits = []
        for idx, ln in enumerate(lines, 1):
            if pat.lower() in ln.lower():
                if len(ln) > 600:
                    pos = ln.lower().find(pat.lower())
                    start = max(0, pos - 300)
                    end = min(len(ln), pos + len(pat) + 300)
                    hits.append(f"Line {idx} (chars {start}-{end}):\n{ln[start:end]}")
                else:
                    lo = max(0, idx - 5)
                    hi = min(len(lines), idx + 5)
                    snippet = "\n".join(f"{j + 1}: {lines[j]}" for j in range(lo, hi))
                    hits.append(snippet)
                if len(hits) >= 15:
                    break
        if not hits:
            out.append(f"[GREP {path} for {pat!r}: 0 matches]")
        else:
            out.append(f"----- GREP {path} for {pat!r} ({len(hits)} match block(s)) -----\n" +
                       "\n---\n".join(hits) + "\n----- END GREP -----")
    return "\n".join(out)


def save_undo(work, backup):
    if not backup:
        return
    base = work / ".hexrea" / "undo"
    base.mkdir(parents=True, exist_ok=True)
    n = max([int(p.name) for p in base.iterdir() if p.name.isdigit()] or [0]) + 1
    d, meta = base / str(n), {}
    for rel, data in backup.items():
        if data is None:
            meta[rel] = "new"
        else:
            meta[rel] = "file"
            fp = d / "files" / rel
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_bytes(data)
    (d / "meta.json").write_text(json.dumps(meta), encoding="utf-8")


def undo_last(work):
    base = work / ".hexrea" / "undo"
    nums = sorted(int(p.name) for p in base.iterdir() if p.name.isdigit()) if base.is_dir() else []
    if not nums:
        return None
    d = base / str(nums[-1])
    meta = json.loads((d / "meta.json").read_text(encoding="utf-8"))
    for rel, kind in meta.items():
        tgt = work / rel
        if kind == "new":
            tgt.unlink(missing_ok=True)
        else:
            tgt.parent.mkdir(parents=True, exist_ok=True)
            tgt.write_bytes((d / "files" / rel).read_bytes())
    shutil.rmtree(d)
    return sorted(meta)


# ---- Groq Cloud LPU ---------------------------------------------------------
class AIError(Exception):
    pass


class PayloadTooLargeError(AIError):
    pass


class QuotaError(AIError):
    pass


class RateWait(AIError):
    def __init__(self, secs, msg):
        super().__init__(msg)
        self.secs = secs


def groq_chat(cfg, slot, messages, progress=None):
    """Chat call that politely waits out per-minute rate limits (up to ~75s total)."""
    waited = 0.0
    while True:
        try:
            return _chat_once(cfg, slot, messages, progress)
        except RateWait as e:
            if waited + e.secs > 75:
                if slot_provider(slot) == "gemini":
                    raise QuotaError(str(e))
                raise AIError(f"{e}  ·  Per-minute limit still full. Wait a minute or use Gemini Flash.")
            time.sleep(e.secs)
            waited += e.secs


GEMINI_FALLBACKS = ["gemini-2.5-flash", "gemini-2.5-flash-lite"]


def _chat_once(cfg, slot, messages, progress=None):
    provider = slot_provider(slot)
    key = get_key(cfg, provider)
    if not key:
        raise AIError(f"Missing {provider.title()} API key. Add it in Settings.")
    base_url = GEMINI_URL if provider == "gemini" else GROQ_URL
    max_tok = slot.get("max_tokens", 16_000)
    if provider == "groq":
        max_tok = min(max_tok, 2_500)   # Groq counts max_tokens toward the free 8k TPM limit
    body = {"model": slot["model"], "messages": messages, "stream": True,
            "temperature": 0.2, "max_tokens": max_tok}
    if slot.get("reasoning_effort") and provider == "groq":
        body["reasoning_effort"] = slot["reasoning_effort"]
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    try:
        r = requests.post(base_url + "/chat/completions", headers=headers, json=body, stream=True, timeout=(20, 180))
    except requests.RequestException as e:
        raise AIError(f"Network error: {e}")
    if r.status_code != 200:
        try:
            j = r.json()
            if isinstance(j, list):
                j = j[0] if j else {}
            err = j.get("error", {}) if isinstance(j, dict) else {}
            msg = (err.get("message") if isinstance(err, dict) else str(err)) or r.text[:300]
        except (ValueError, AttributeError):
            msg = r.text[:300]
        low = msg.lower()
        m_wait = re.search(r"try again in ([0-9.]+)\s*(ms|s|m)", low)
        if r.status_code == 429 and m_wait and "request too large" not in low:
            secs = float(m_wait.group(1)) * {"ms": 0.001, "s": 1, "m": 60}[m_wait.group(2)]
            raise RateWait(secs + 0.5, f"{provider} 429: {msg[:200]}")
        too_big = r.status_code == 413 or "request too large" in low or "exceeds the maximum number of tokens" in low
        if too_big:
            raise PayloadTooLargeError(f"{provider} {r.status_code}: {msg[:300]}")
        if provider == "gemini" and r.status_code in (429, 503, 404):
            raise QuotaError(f"Gemini {r.status_code}: {msg[:300]}")
        hint = {401: "Groq rejected the key. Use /key to enter a valid gsk_... key.",
                404: "Model not available on Groq. Switch with /model.",
                429: "Groq rate limit hit. Wait a few seconds or switch model with /model."}.get(r.status_code, "")
        raise AIError(f"{r.status_code}: {msg}" + (f"  ·  {hint}" if hint else ""))
    r.encoding = "utf-8"
    parts, finish = [], None
    for line in r.iter_lines(decode_unicode=True):
        if not line or line.startswith(":") or not line.startswith("data:"):
            continue
        data = line[5:].strip()
        if data == "[DONE]":
            break
        try:
            obj = json.loads(data)
        except ValueError:
            continue
        if obj.get("error"):
            raise AIError(str(obj["error"].get("message", "stream error")) if isinstance(obj["error"], dict) else str(obj["error"]))
        if isinstance(obj, list):
            obj = obj[0] if obj else {}
        ch = (obj.get("choices") or [{}])[0]
        delta = (ch.get("delta") or {}).get("content")
        if delta:
            parts.append(delta)
            if progress:
                progress(sum(len(p) for p in parts))
        finish = ch.get("finish_reason") or finish
    text = "".join(parts)
    if not text.strip():
        raise AIError(f"{provider.title()} returned an empty response. Try again or switch model.")
    return text, finish


GEMINI_RESOLVED = {}


def gemini_candidates(cfg, prefer="flash"):
    """Ask Google which Gemini models this key can use right now (ids change often)."""
    key = get_key(cfg, "gemini")
    try:
        r = requests.get(GEMINI_URL + "/models", headers={"Authorization": f"Bearer {key}"}, timeout=15)
        data = r.json()
        data = data.get("data", []) if isinstance(data, dict) else []
        ids = [str(m.get("id", "")).replace("models/", "") for m in data]
    except (requests.RequestException, ValueError, AttributeError):
        ids = []

    def pick(fam):
        found = []
        for i in ids:
            m = re.fullmatch(r"gemini-(\d+(?:\.\d+)?)-" + fam, i)
            if m:
                found.append((float(m.group(1)), i))
        return [i for _, i in sorted(found, reverse=True)]
    order = ["pro", "flash", "flash-lite"] if prefer == "pro" else ["flash", "flash-lite"]
    out = []
    for fam in order:
        out += pick(fam)
    return out or list(GEMINI_FALLBACKS)


def chat_with_fallback(cfg, slot, messages, progress=None):
    """Gemini: remember a working model; on 404/quota, discover and try current models."""
    if slot_provider(slot) == "gemini" and slot["model"] in GEMINI_RESOLVED:
        slot = dict(slot, model=GEMINI_RESOLVED[slot["model"]])
    try:
        return groq_chat(cfg, slot, messages, progress)
    except QuotaError as first:
        orig = slot["model"]
        tried = [orig]
        for m in gemini_candidates(cfg, "pro" if "pro" in orig else "flash"):
            if m in tried:
                continue
            tried.append(m)
            try:
                res = groq_chat(cfg, dict(slot, model=m, provider="gemini"), messages, progress)
                GEMINI_RESOLVED[orig] = m
                return res
            except QuotaError:
                continue
        raise AIError(f"{first}  ·  (also tried {', '.join(tried[1:]) or 'nothing else'}). "
                      "If this says quota/limit: wait a minute. If it says API key invalid: make a new key in Google AI Studio.")


# ---- terminal UI (Clean Loading Bar + Bold Code Box) ------------------------
_HX = ["██╗  ██╗", "██║  ██║", "███████║", "██╔══██║", "██║  ██║", "╚═╝  ╚═╝"]
_TX = ["████████╗", "╚══██╔══╝", "   ██║   ", "   ██║   ", "   ██║   ", "   ╚═╝   "]
_MX = ["███╗   ███╗", "████╗ ████║", "██╔████╔██║", "██║╚██╔╝██║", "██║ ╚═╝ ██║", "╚═╝     ╚═╝"]
_LX = ["██╗     ", "██║     ", "██║     ", "██║     ", "███████╗", "╚══════╝"]
HTML_ART = "\n".join("   " + h + t + m + l for h, t, m, l in zip(_HX, _TX, _MX, _LX))
HEX_ART = r"""
   ██╗  ██╗███████╗██╗  ██╗    ██████╗ ███████╗ █████╗
   ██║  ██║██╔════╝╚██╗██╔╝    ██╔══██╗██╔════╝██╔══██╗
   ███████║█████╗   ╚███╔╝     ██████╔╝█████╗  ███████║
   ██╔══██║██╔══╝   ██╔██╗     ██╔══██╗██╔══╝  ██╔══██║
   ██║  ██║███████╗██╔╝ ██╗    ██║  ██║███████╗██║  ██║
   ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝    ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝"""


def hexprompt(where):
    R, W, G = Fore.RED, Fore.WHITE + Style.BRIGHT, Fore.GREEN
    print(R + "┌──(" + W + "HEX" + R + "@" + W + "REA" + R + ")-[" + G + where + R + "]")
    return input(R + "└─" + G + "❯ " + Style.RESET_ALL).strip()


def print_code_box(ops, rnd, is_fix=False):
    if not ops:
        return
    cols = max(54, min(96, shutil.get_terminal_size((80, 20)).columns - 4))
    inner = cols - 4
    R = Fore.RED + Style.BRIGHT
    W = Fore.WHITE + Style.BRIGHT
    G = Fore.GREEN + Style.BRIGHT
    C = Fore.CYAN + Style.BRIGHT
    Y = Fore.YELLOW + Style.BRIGHT
    tag = f"SELF-FIX ROUND {rnd + 1}" if is_fix else f"HEX CODE ENGINE · ROUND {rnd + 1}"
    hdr = f"══[ {tag} ]"
    print("\n  " + R + "╔" + hdr + "═" * max(2, cols - 2 - len(hdr)) + "╗" + Style.RESET_ALL)
    for op in ops:
        status = (G + "✓ APPLIED") if op.get("ok") else (Y + "⚠ RETRYING")
        kind = op.get("op", "EDIT")
        print("  " + R + "║ " + C + f"[{kind}] " + W + f"{op.get('path', '')[:inner - 22]} " + status + Style.RESET_ALL)
        if op.get("op") == "EDIT":
            for idx, blk in enumerate(op.get("blocks", []), 1):
                print("  " + R + "║ " + Fore.LIGHTBLACK_EX + f"  ── block #{idx} " + ("─" * max(4, inner - 16)) + Style.RESET_ALL)
                for ln in blk.get("search", "").splitlines()[:10]:
                    print("  " + R + "║   " + Fore.RED + "- " + ln[:inner - 6] + Style.RESET_ALL)
                for ln in blk.get("replace", "").splitlines()[:14]:
                    print("  " + R + "║   " + Fore.GREEN + "+ " + ln[:inner - 6] + Style.RESET_ALL)
        elif op.get("content"):
            for ln in op["content"].splitlines()[:18]:
                print("  " + R + "║   " + Fore.WHITE + "+ " + ln[:inner - 6] + Style.RESET_ALL)
        if op.get("error"):
            print("  " + R + "║   " + Y + "! " + op["error"][:inner - 5] + Style.RESET_ALL)
    print("  " + R + "╚" + "═" * (cols - 2) + "╝\n" + Style.RESET_ALL)


def print_nano_reply(prose, model_name, self_fixed=False):
    cols = max(50, min(92, shutil.get_terminal_size((80, 20)).columns - 4))
    R, W, G, C = Fore.RED, Fore.WHITE + Style.BRIGHT, Fore.GREEN, Fore.CYAN
    badge = (Fore.YELLOW + " · SELF-HEALED" + R) if self_fixed else ""
    top = f"─[GROQ // {model_name}]"
    print("  " + R + "┌" + top + "─" * max(2, cols - 2 - len(top)) + badge + Style.RESET_ALL)
    width = cols - 6
    for para in (prose or "(code changes applied)").split("\n"):
        for ln in (textwrap.wrap(para, width, replace_whitespace=False) or [""]):
            print("  " + R + "│ " + W + ln + Style.RESET_ALL)
    print("  " + R + "└─[" + G + "DONE" + R + "]" + "─" * max(2, cols - 10) + "─" + C + "◈" + Style.RESET_ALL)


def modifier_banner(site, cfg, work):
    os.system("clear")
    print(Fore.RED + HEX_ART)
    print(Fore.WHITE + Style.BRIGHT + HTML_ART + Style.RESET_ALL)
    print(Fore.LIGHTBLACK_EX + "                 R E A   M O D I F I E R   [ G R O Q   L P U ]\n")
    slot = active_slot(cfg)
    files = list_work_files(work)
    R, W, G, C = Fore.RED, Fore.WHITE + Style.BRIGHT, Fore.GREEN, Fore.CYAN
    print(R + "  ├─ " + W + "Site   " + G + site["url"])
    print(R + "  ├─ " + W + "Groq   " + G + f"{slot['model']}")
    print(R + "  └─ " + W + "Files  " + G + f"{len(files)} in workspace\n")

    print(R + "  ╔══[ " + W + "COMMANDS (/help)" + R + " ]═════════════════════════════════════════════╗")
    print(R + "  ║ " + W + "p" + G + " preview    " + W + "d" + G + " download    " + W + "/web" + C + " open web UI      " + W + "/model" + G + " Groq model" + R + "║")
    print(R + "  ║ " + W + "/files" + G + " list  " + W + "/undo" + G + " revert   " + W + "/reset" + G + " orig site       " + W + "/clear" + G + " new chat " + R + " ║")
    print(R + "  ║ " + W + "/key" + G + " Groq key" + W + "/help" + G + " full guide                  " + W + "/exit" + G + " back      " + R + " ║")
    print(R + "  ╚══════════════════════════════════════════════════════════════════╝\n" + Style.RESET_ALL)

    print(W + "  What do you want to modify in this site?" + Style.RESET_ALL)
    print(Fore.LIGHTBLACK_EX + "  e.g. “add a pulsing red Buy Now button under the hero title”  ·  “explain the analysis”\n")


def options_line():
    print(Fore.RED + "  ──────────────────────────────────────────────────────────────────")
    print(Fore.WHITE + Style.BRIGHT + "   [p]" + Fore.GREEN + "review   " +
          Fore.WHITE + Style.BRIGHT + "[d]" + Fore.GREEN + "ownload   " +
          Fore.WHITE + Style.BRIGHT + "[/web]" + Fore.CYAN + " Web UI   " +
          Fore.LIGHTBLACK_EX + "or keep typing to edit\n")


def prepare_workspace(site, auto_pages=None):
    d = SAVED / site["id"]
    work, orig = d / "work", d / "orig"
    if work.is_dir() and list_work_files(work):
        return work
    shutil.rmtree(work, ignore_errors=True)
    try:
        analysis = json.loads((d / "analysis.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        if auto_pages is not None:
            raise ValueError("Saved analysis is missing. Extract the site again with [1].")
        print(Fore.RED + "  [!] Saved analysis is missing. Extract the site again with [1].")
        return None
    if auto_pages is None:
        print(Fore.YELLOW + "\n  First time in the modifier for this site: pulling every page and file into a workspace.")
        raw = input(Fore.GREEN + "  Pages to pull (1-200, Enter = 1): " + Style.RESET_ALL).strip()
        pages = max(1, min(int(raw), 200)) if raw.isdigit() else 1
    else:
        pages = max(1, min(int(auto_pages), 200))
    sess = new_session(site["url"])
    sess["analysis"] = analysis
    job = new_job()
    t = threading.Thread(target=run_download, args=(job, sess, pages, True),
                         kwargs={"dest_root": work, "package": False}, daemon=True)
    t.start()
    if auto_pages is None:
        try:
            while t.is_alive():
                bar = "█" * int(job["pct"] / 5) + "░" * (20 - int(job["pct"] / 5))
                sys.stdout.write(f"\r  {Fore.RED}{bar}{Fore.WHITE} {int(job['pct']):3d}%  {job['files']} files  "
                                 f"{job['bytes'] // 1024} KB  {job['phase'][:28]:<28}")
                sys.stdout.flush()
                time.sleep(0.25)
        except KeyboardInterrupt:
            job["cancel"] = True
            t.join()
            print(Fore.YELLOW + "\n  Cancelled.")
            shutil.rmtree(work, ignore_errors=True)
            return None
        print()
    else:
        t.join(timeout=120)

    if job["status"] != "done" or not list_work_files(work):
        src = d / "source.html"
        if src.is_file():
            work.mkdir(parents=True, exist_ok=True)
            rel = f"{site['netloc'].replace(':', '_')}/index.html"
            fp = work / rel
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
            (work / "index.html").write_text(
                '<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url='
                + quote(rel) + '"><a href="' + quote(rel) + '">Open saved site</a>', encoding="utf-8")
            (work / "manifest.json").write_text(json.dumps(
                {"target": site["url"], "saved": time.strftime("%Y-%m-%d %H:%M:%S"),
                 "pages": [{"url": site["url"], "path": rel}], "files": [], "errors": []}, indent=2), encoding="utf-8")
            (work / "analysis.json").write_text(json.dumps(analysis, indent=2), encoding="utf-8")
        else:
            if auto_pages is not None:
                raise ValueError(f"Could not build workspace: {job.get('error') or job['status']}")
            print(Fore.RED + f"  [!] Could not build the workspace: {job.get('error') or job['status']}")
            shutil.rmtree(work, ignore_errors=True)
            return None

    shutil.rmtree(orig, ignore_errors=True)
    shutil.copytree(work, orig)
    if auto_pages is None:
        print(Fore.GREEN + f"  [✓] Workspace ready: {len(list_work_files(work))} files.")
        time.sleep(0.3)
    return work


def preview_work(site):
    start_servers()
    url = f"http://{HOST}:{PREVIEW_PORT}/work/{site['id']}/index.html"
    print(Fore.GREEN + f"\n  [✓] Opening preview: {url}")
    open_browser(url)
    print(Fore.LIGHTBLACK_EX + "  This is your modified copy. Come back here to keep editing.\n")


def open_web_modifier(site):
    start_servers()
    url = f"http://{HOST}:{PORT}/modify?id={quote(site['id'])}"
    print(Fore.CYAN + f"\n  [✓] Opening Web Modifier UI: {url}")
    open_browser(url)
    print(Fore.LIGHTBLACK_EX + "  Your edits and chat stay synced between Terminal and Web UI.\n")


def build_modified_zip(site, work):
    d = SAVED / site["id"]
    name = f"{site['netloc'].replace(':', '_')}_modified_{time.strftime('%Y%m%d_%H%M%S')}"
    zpath = d / f"{name}.zip"
    with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
        for fp in work.rglob("*"):
            rel = fp.relative_to(work)
            if fp.is_file() and rel.parts[0] not in SKIP_DIRS:
                z.write(fp, Path(name) / rel)
    dest, shared = storage_dir()
    saved_to, saved_zip = str(work), str(zpath)
    try:
        if shared:
            shutil.copy2(zpath, dest / zpath.name)
            shutil.copytree(work, dest / name, ignore=shutil.ignore_patterns(*SKIP_DIRS))
            saved_to = str(dest / name)
            saved_zip = str(dest / zpath.name)
    except OSError:
        shared = False
    return zpath, saved_to, saved_zip, shared


def download_work(site, work):
    start_servers()
    zpath, saved_to, saved_zip, shared = build_modified_zip(site, work)
    if shared:
        print(Fore.GREEN + f"\n  [✓] Saved to your file manager: {saved_to}")
        print(Fore.GREEN + f"      ZIP: {saved_zip}")
    else:
        print(Fore.GREEN + f"\n  [✓] ZIP created: {zpath}")
        print(Fore.YELLOW + "  [!] Run `termux-setup-storage` once so files appear in your file manager.")
    url = f"http://{HOST}:{PORT}/dl/{site['id']}/{zpath.name}"
    print(Fore.GREEN + "  [✓] Opening the browser download page…\n")
    open_browser(url)


def pick_model(cfg):
    print(Fore.RED + "\n  Groq LPU Coding Models")
    names = list(cfg["slots"])
    for i, n in enumerate(names, 1):
        s = cfg["slots"][n]
        mark = Fore.GREEN + "  ◀ active" if cfg["slot"] == n else ""
        print(Fore.WHITE + f"  [{i}] {s['label']}  " + Fore.LIGHTBLACK_EX + f"{s['model']}" + mark)
    custom_num = len(names) + 1
    cm = cfg.get("custom")
    print(Fore.WHITE + f"  [{custom_num}] Custom Groq model id" + (Fore.LIGHTBLACK_EX + f"  {cm['model']}" if cm else "") +
          (Fore.GREEN + "  ◀ active" if cfg["slot"] == "custom" else ""))
    c = input(Fore.GREEN + "  Pick (Enter = keep): " + Style.RESET_ALL).strip()
    if c.isdigit() and 1 <= int(c) <= len(names):
        cfg["slot"] = names[int(c) - 1]
    elif c == str(custom_num):
        mid = input(Fore.GREEN + "  Groq model id (e.g. gemini-3.8-flash): " + Style.RESET_ALL).strip()
        if not mid:
            return
        cfg["custom"] = {"model": mid}
        cfg["slot"] = "custom"
    else:
        return
    save_cfg(cfg)
    s = active_slot(cfg)
    print(Fore.GREEN + f"  [✓] Using {s['model']}\n")


def run_ai_agent(cfg, site, work, history, user_text, focus_section="", progress_cb=None, round_cb=None):
    """AI coding agent (Groq/Gemini) with full-file access + auto-shrink on TPM/413 + self-healing edits."""
    slot = usable_slot(cfg)
    site_dir = SAVED / site["id"]
    analysis = json.loads((site_dir / "analysis.json").read_text(encoding="utf-8"))

    lean = slot_provider(slot) == "groq"
    read_cap = 5_000 if lean else 24_000
    if lean:
        budgets = [8_000, 5_000, 3_000]       # lean mode: fits Groq free tier (7-8k tokens/min)
    else:
        budgets = [slot.get("ctx_chars", 400_000), 120_000, 40_000]
    prompt_text = (f"[TARGET SECTION / EXTRACTED URL: {focus_section}]\n{user_text}" if focus_section else user_text)

    backup, applied_all, prose_all, ops_all, last_errs = {}, [], [], [], []
    self_fixed = False
    rounds_used = 0

    for b_idx, budget in enumerate(budgets):
        ctx, _, _ = build_context(site, analysis, work, budget, focus_section=focus_section, site_dir=site_dir, lean=lean)
        hist_slice = history[-10:] if budget >= 60_000 else history[-2:]
        base = [{"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": ctx},
                {"role": "assistant", "content": "Context & [1] analysis ready. Tell me what to change or add."}] + hist_slice
        convo = [{"role": "user", "content": prompt_text}]
        backup, applied_all, prose_all, ops_all, last_errs = {}, [], [], [], []
        self_fixed = False
        rounds_used = 0
        try:
            for rnd in range(MAX_ROUNDS):
                rounds_used = rnd + 1
                reply, finish = chat_with_fallback(cfg, slot, base + convo, progress_cb)
                convo.append({"role": "assistant", "content": reply})
                prose = strip_blocks(reply)
                if prose:
                    prose_all.append(prose)
                ops = []
                done, errs = apply_response(work, reply, backup, ops_out=ops)
                applied_all += done
                ops_all += ops
                if rnd > 0 and done:
                    self_fixed = True
                if round_cb:
                    round_cb(rnd, ops, prose, done, errs, finish)
                last_errs = errs
                feedback = []
                reads = RE_READ.findall(reply)
                if reads:
                    feedback.append("Requested files:\n" + read_files_msg(work, reads, site_dir=site_dir, max_chars=read_cap))
                greps = RE_GREP.findall(reply)
                if greps:
                    feedback.append("Search results:\n" + grep_files_msg(work, greps, site_dir=site_dir))
                if errs:
                    failed = sorted({e.split()[1].rstrip(":") for e in errs if e.split()[0] in ("EDIT", "FILE", "DELETE")})
                    feedback.append("These edits FAILED and were NOT applied:\n" + "\n".join(errs) +
                                    "\nCurrent file contents:\n" + read_files_msg(work, failed[:2], site_dir=site_dir, max_chars=read_cap) +
                                    "\nFix your SEARCH snippet or use <<<EDIT>>> instead of <<<FILE>>>, then resend ONLY the failed edit.")
                if not feedback:
                    last_errs = []
                    break
                convo.append({"role": "user", "content": "[HEX REA AUTO-CHECK] " + "\n\n".join(feedback)})
            break
        except PayloadTooLargeError as e:
            if b_idx == len(budgets) - 1:
                raise AIError(f"Request still too big for {slot['model']} even in compact mode: {e}. "
                              "Use a Gemini Flash model (bigger limits) or pick a smaller target section.")

    save_undo(work, backup)
    note = ("\n[HEX REA applied: " + "; ".join(applied_all) + "]") if applied_all else ""
    final_prose = prose_all[-1] if prose_all else ("Applied: " + "; ".join(applied_all) if applied_all else "(no changes)")
    new_history = (history + [{"role": "user", "content": prompt_text},
                              {"role": "assistant", "content": final_prose + note}])[-20:]
    (site_dir / "chat.json").write_text(json.dumps(new_history), encoding="utf-8")
    return {
        "prose": final_prose,
        "applied": applied_all,
        "ops": ops_all,
        "errors": last_errs,
        "rounds": rounds_used,
        "self_fixed": self_fixed,
        "history": new_history,
        "model": slot["model"],
    }


def ai_turn(state, user_text):
    cfg, work, site = state["cfg"], state["work"], state["site"]
    slot = active_slot(cfg)

    def draw_bar(pct, chars, label="coding"):
        fill = min(20, max(1, int(pct / 5)))
        bar = "█" * fill + "░" * (20 - fill)
        sys.stdout.write(f"\r  {Fore.RED}[{bar}]{Fore.WHITE} {pct:3d}%  {Fore.CYAN}{slot['model'].split('/')[-1]}"
                         f"{Fore.LIGHTBLACK_EX} · {label} ({chars:,} chars)   ")
        sys.stdout.flush()

    def progress(n):
        pct = min(96, 15 + int(81 * (1 - 1 / (1 + n / 900))))
        draw_bar(pct, n, "writing")

    def on_round(rnd, ops, prose, done, errs, finish):
        draw_bar(100, 0, "done")
        sys.stdout.write("\r" + " " * 82 + "\r")
        if ops:
            print_code_box(ops, rnd, is_fix=(rnd > 0))
        if finish == "length":
            print(Fore.YELLOW + "  ⚠ Reply hit output length limit; partial edit skipped.")
        if errs:
            print(Fore.YELLOW + "  ⚡ Auto-Fixer repairing edit mismatch…")

    draw_bar(8, 0, "connecting")
    res = run_ai_agent(cfg, site, work, state["history"], user_text, progress_cb=progress, round_cb=on_round)
    sys.stdout.write("\r" + " " * 82 + "\r")
    state["history"] = res["history"]
    print_nano_reply(res["prose"], res["model"], self_fixed=res["self_fixed"])
    if res["errors"]:
        print(Fore.YELLOW + "  ⚠ Some edits could not be auto-repaired. Try being a bit more specific.\n")


# ---- Web Modifier API helpers (for modify.html) -----------------------------
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}")
EMAIL_SKIP_DOMAINS = ("example.com", "example.org", "sentry.io", "w3.org", "schema.org")


def scan_email_leaks(work):
    """Find email addresses sitting in plain text across the extracted site (JS/HTML/JSON/etc)."""
    found, seen = [], set()
    for rel, _ in list_work_files(work):
        if posixpath.splitext(rel)[1].lower() not in TEXT_EXT:
            continue
        text = read_text(work / rel)
        if not text:
            continue
        for m in EMAIL_RE.finditer(text):
            addr = m.group(0).rstrip(".,;:'\")")
            dom = addr.split("@")[-1].lower()
            if dom in EMAIL_SKIP_DOMAINS or addr.lower().startswith(("example@", "test@", "you@", "name@")):
                continue
            key = addr.lower()
            if key in seen:
                continue
            seen.add(key)
            found.append({"email": addr, "file": rel})
            if len(found) >= 40:
                return found
    return found


def web_mod_open(site_id, pages=1):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = prepare_workspace(site, auto_pages=pages)
        cfg = load_cfg()
        try:
            history = json.loads((SAVED / site["id"] / "chat.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            history = []
        analysis = {}
        try:
            analysis = json.loads((SAVED / site["id"] / "analysis.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            pass
        files = [{"path": r, "bytes": s} for r, s in list_work_files(work)]
        has_groq = bool(get_key(cfg))
        email_leaks = scan_email_leaks(work)
        return {
            "email_leaks": email_leaks,
            "success": True,
            "site": site,
            "files": files,
            "history": history,
            "slot": cfg["slot"],
            "active": active_slot(cfg),
            "slots": [{"id": k, **v} for k, v in cfg["slots"].items()],
            "custom": cfg.get("custom"),
            "has_key": has_groq,
            "has_groq": has_groq,
            "preview_url": f"http://{HOST}:{PREVIEW_PORT}/work/{site['id']}/index.html",
            "sections": {
                "title": analysis.get("title", ""),
                "tech": analysis.get("tech", [])[:12],
                "links": analysis.get("links", [])[:100],
                "forms": [{"action": f.get("action", ""), "method": f.get("method", "GET")} for f in analysis.get("forms", [])[:20]],
                "endpoints": analysis.get("endpoints", [])[:30],
                "headings": analysis.get("headings", [])[:25],
            },
        }


def web_mod_chat(site_id, message, section=""):
    msg = (message or "").strip()
    if not msg:
        raise ValueError("Empty message")
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = prepare_workspace(site, auto_pages=1)
        cfg = load_cfg()
        if not get_key(cfg):
            raise AIError("No API key saved yet. Add your Groq (gsk_...) or Gemini key in Settings.")
        try:
            history = json.loads((SAVED / site["id"] / "chat.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            history = []
        res = run_ai_agent(cfg, site, work, history, msg, focus_section=(section or "").strip())
        files = [{"path": r, "bytes": s} for r, s in list_work_files(work)]
        return {
            "success": True,
            **res,
            "files": files,
            "preview_url": f"http://{HOST}:{PREVIEW_PORT}/work/{site['id']}/index.html",
        }


def web_mod_file(site_id, path):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = SAVED / site["id"] / "work"
        fp = resolve_path(work, path)
        if not fp or not fp.is_file():
            raise ValueError("File not found in workspace")
        txt = read_text(fp)
        return {"success": True, "path": fp.relative_to(work.resolve()).as_posix(),
                "is_text": txt is not None, "content": txt if txt is not None else "(binary file)"}


def web_mod_model(slot_name, custom=None):
    cfg = load_cfg()
    if slot_name == "custom":
        if not custom or not (custom.get("model") or "").strip():
            raise ValueError("Custom Groq model ID required")
        cfg["custom"] = {"model": custom["model"].strip()}
        cfg["slot"] = "custom"
    elif slot_name in cfg["slots"]:
        cfg["slot"] = slot_name
    else:
        raise ValueError("Unknown model slot")
    save_cfg(cfg)
    return {"success": True, "slot": cfg["slot"], "active": active_slot(cfg)}


def web_mod_key(key):
    key = (key or "").strip()
    if not key:
        raise ValueError("Key cannot be empty")
    if len(key) < 20 or any(c.isspace() for c in key):
        raise ValueError("That does not look like an API key")
    cfg = load_cfg()
    if key.startswith("gsk_"):
        cfg["groq_key"] = key
        provider = "groq"
    else:
        cfg["gemini_key"] = key
        provider = "gemini"
        if slot_provider(active_slot(cfg)) != "gemini" and not get_key(cfg, "groq"):
            cfg["slot"] = "gflash"
    save_cfg(cfg)
    return {"success": True, "provider": provider}


def web_mod_undo(site_id):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = SAVED / site["id"] / "work"
        res = undo_last(work)
        if not res:
            return {"success": True, "reverted": [], "message": "Nothing to undo"}
        try:
            history = json.loads((SAVED / site["id"] / "chat.json").read_text(encoding="utf-8"))
        except (OSError, ValueError):
            history = []
        history = (history + [{"role": "user", "content": "[HEX REA] User undid the last edit."},
                              {"role": "assistant", "content": "Understood, reverted: " + ", ".join(res)}])[-20:]
        (SAVED / site["id"] / "chat.json").write_text(json.dumps(history), encoding="utf-8")
        files = [{"path": r, "bytes": s} for r, s in list_work_files(work)]
        return {"success": True, "reverted": res, "files": files, "history": history}


def web_mod_reset(site_id):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = SAVED / site["id"] / "work"
        orig = SAVED / site["id"] / "orig"
        if orig.is_dir():
            shutil.rmtree(work, ignore_errors=True)
            shutil.copytree(orig, work)
        (SAVED / site["id"] / "chat.json").unlink(missing_ok=True)
        files = [{"path": r, "bytes": s} for r, s in list_work_files(work)] if work.is_dir() else []
        return {"success": True, "files": files, "history": []}


def web_mod_clear(site_id):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        (SAVED / site["id"] / "chat.json").unlink(missing_ok=True)
        return {"success": True, "history": []}


def web_mod_download(site_id):
    with MOD_LOCK:
        site = get_saved_site(site_id)
        work = SAVED / site["id"] / "work"
        if not work.is_dir():
            raise ValueError("Workspace not built yet")
        zpath, saved_to, saved_zip, shared = build_modified_zip(site, work)
        return {"success": True, "dl_url": f"/dl/{site['id']}/{zpath.name}",
                "saved_to": saved_to, "saved_zip": saved_zip, "shared": shared, "zip_name": zpath.name}


def modifier_help():
    print(Fore.WHITE + """
  Type what you want changed or added, pick a section/URL, or ask about the recon analysis.
    p        preview the modified site in your browser
    d        download it (saves to your file manager + opens the download page)
    /web     open the Web Modifier UI (modify.html) for this site
    /model   switch Groq model (Qwen 3.8 27B · GPT-OSS 120B · Llama 3.3 70B · GPT-OSS 20B · Llama 3.1 8B)
    /files   list all files in the workspace
    /undo    undo the AI's last change
    /reset   restore the original extracted site
    /clear   clear conversation memory (files stay as they are)
    /key     replace your Groq API key
    /exit    back to the sites list
  End a line with \\ to continue on the next line.
""")


def rea_modifier(site):
    cfg = load_cfg()
    if not ensure_key(cfg):
        print(Fore.YELLOW + "  No Groq key, cannot start the modifier.\n")
        return
    work = prepare_workspace(site)
    if not work:
        return
    start_servers()
    try:
        history = json.loads((SAVED / site["id"] / "chat.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        history = []
    state = {"cfg": cfg, "site": site, "work": work, "history": history}
    modifier_banner(site, cfg, work)
    where = f"rea · modifier · {site['netloc']}"
    while True:
        try:
            msg = hexprompt(where)
            while msg.endswith("\\"):
                msg = msg[:-1] + "\n" + input(Fore.GREEN + "   … " + Style.RESET_ALL)
        except (EOFError, KeyboardInterrupt):
            print()
            return
        low = msg.strip().lower()
        if not low:
            continue
        if low in ("p", "preview"):
            preview_work(site)
            continue
        if low in ("d", "download"):
            download_work(site, work)
            continue
        if low in ("/web", "w", "web"):
            open_web_modifier(site)
            continue
        if low.startswith("/"):
            cmd = low.split()[0]
            if cmd in ("/exit", "/back", "/quit"):
                return
            elif cmd == "/help":
                modifier_help()
            elif cmd == "/model":
                pick_model(cfg)
            elif cmd == "/key":
                ensure_key(cfg, force=True)
            elif cmd == "/files":
                for r, s in list_work_files(work)[:120]:
                    print(Fore.WHITE + f"  {r}" + Fore.LIGHTBLACK_EX + f"  {s:,} B")
                print()
            elif cmd == "/undo":
                res = undo_last(work)
                if res:
                    state["history"] += [{"role": "user", "content": "[HEX REA] The user undid your last change; the files were restored."},
                                         {"role": "assistant", "content": "Understood, the last change is reverted."}]
                    print(Fore.GREEN + f"  [✓] Reverted: {', '.join(res)}\n")
                else:
                    print(Fore.YELLOW + "  Nothing to undo.\n")
            elif cmd == "/reset":
                if input(Fore.YELLOW + "  Restore the original site and drop all edits? [y/n] " + Style.RESET_ALL).lower() == "y":
                    shutil.rmtree(work)
                    shutil.copytree(SAVED / site["id"] / "orig", work)
                    state["history"] = []
                    (SAVED / site["id"] / "chat.json").unlink(missing_ok=True)
                    print(Fore.GREEN + "  [✓] Original restored.\n")
            elif cmd == "/clear":
                state["history"] = []
                (SAVED / site["id"] / "chat.json").unlink(missing_ok=True)
                print(Fore.GREEN + "  [✓] Conversation memory cleared.\n")
            else:
                print(Fore.YELLOW + "  Unknown command. /help\n")
            continue
        try:
            ai_turn(state, msg)
            options_line()
        except AIError as e:
            sys.stdout.write("\r" + " " * 82 + "\r")
            print(Fore.RED + f"  [!] {e}\n")
        except KeyboardInterrupt:
            sys.stdout.write("\r" + " " * 82 + "\r")
            print(Fore.YELLOW + "  Cancelled. Nothing was changed by this request.\n")


def rea_sites():
    R, W, G, C = Fore.RED, Fore.WHITE + Style.BRIGHT, Fore.GREEN, Fore.CYAN
    while True:
        sites = list_saved()
        os.system("clear")
        print(Fore.RED + HEX_ART)
        print(Fore.LIGHTBLACK_EX + "                 R E A   Y O U R   S I T E S\n")
        if not sites:
            print(Fore.YELLOW + "  No extracted sites yet. Use [1] Extract first, then come back.\n")
            input(Fore.GREEN + "  Press Enter…" + Style.RESET_ALL)
            return
        for i, s in enumerate(sites, 1):
            tag = Fore.YELLOW + "  ✎ has workspace" if s["has_work"] else ""
            print(R + "├─ " + W + f"[{i}]" + G + f" {s['url']}" + tag)
            print(R + "│      " + Fore.LIGHTBLACK_EX + f"{s['title'][:50]} · {s['saved']}")
        print(R + "├─ " + W + "[0]" + G + " Back")
        c = hexprompt("rea · your sites")
        if c in ("0", "", "b", "back", "q"):
            return
        if not c.isdigit() or not 1 <= int(c) <= len(sites):
            print(Fore.YELLOW + "  Type a number from the list.")
            time.sleep(1)
            continue
        site = sites[int(c) - 1]
        print(Fore.WHITE + f"\n  You are about to enter the REA modifier for {Fore.GREEN}{site['url']}")
        ans = hexprompt("rea · confirm  [y]es / [n]o")
        if ans.lower() in ("y", "yes"):
            print(R + "  ├─ " + W + "[t]" + G + " Terminal Modifier  " + Fore.LIGHTBLACK_EX + "(Groq CLI + Loading Bar)")
            print(R + "  └─ " + W + "[w]" + C + " Web Modifier       " + Fore.LIGHTBLACK_EX + "(modify.html)")
            mode = hexprompt("rea · choose mode  [t/w, Enter = t]").lower()
            if mode in ("w", "web"):
                open_web_modifier(site)
                input(Fore.LIGHTBLACK_EX + "  Press Enter to return… " + Style.RESET_ALL)
            else:
                rea_modifier(site)


# ---- static file serving for modified workspaces -------------------------------
def send_file_range(handler, fp, extra=None):
    ctype = mimetypes.guess_type(fp.name)[0] or "application/octet-stream"
    if ctype.startswith("text/") or ctype in ("application/javascript", "application/json", "image/svg+xml"):
        ctype += "; charset=utf-8"
    size = fp.stat().st_size
    start, end, status = 0, size - 1, 200
    m = re.match(r"bytes=(\d*)-(\d*)", handler.headers.get("Range", "") or "")
    if m and (m.group(1) or m.group(2)):
        if m.group(1):
            start = int(m.group(1))
            end = int(m.group(2)) if m.group(2) else size - 1
        else:
            start = max(size - int(m.group(2)), 0)
        end = min(end, size - 1)
        if start > end:
            return handler.send_body(b"", "text/plain", 416)
        status = 206
    handler.send_response(status)
    handler.send_header("Content-Type", ctype)
    handler.send_header("Content-Length", str(end - start + 1))
    handler.send_header("Accept-Ranges", "bytes")
    handler.send_header("Cache-Control", "no-store")
    if status == 206:
        handler.send_header("Content-Range", f"bytes {start}-{end}/{size}")
    for k, v in (extra or {}).items():
        handler.send_header(k, v)
    handler.end_headers()
    try:
        with open(fp, "rb") as f:
            f.seek(start)
            left = end - start + 1
            while left > 0:
                chunk = f.read(min(65536, left))
                if not chunk:
                    break
                handler.wfile.write(chunk)
                left -= len(chunk)
    except (BrokenPipeError, ConnectionResetError):
        pass


def serve_work(handler):
    segs = unquote(urlsplit(handler.path).path).split("/", 3)
    sid = segs[2] if len(segs) > 2 else ""
    rest = segs[3] if len(segs) > 3 else "index.html"
    if not re.fullmatch(r"[\w.-]+", sid):
        return handler.send_body(b"Bad id", "text/plain", 400)
    root = (SAVED / sid / "work").resolve()
    fp = (root / (rest or "index.html")).resolve()
    if root not in fp.parents and fp != root:
        return handler.send_body(b"Forbidden", "text/plain", 403)
    if fp.is_dir():
        fp = fp / "index.html"
    if not fp.is_file() or fp.relative_to(root).parts[0] in SKIP_DIRS:
        return handler.send_body(b"Not found", "text/plain", 404)
    send_file_range(handler, fp)


_servers = []


def start_servers():
    if _servers:
        return True
    try:
        for port, handler in ((PORT, EditorHandler), (PREVIEW_PORT, PreviewHandler)):
            srv = ThreadingHTTPServer((HOST, port), handler)
            threading.Thread(target=srv.serve_forever, daemon=True).start()
            _servers.append(srv)
        return True
    except OSError as e:
        print(Fore.RED + f"  [!] Cannot bind {HOST}:{PORT}/{PREVIEW_PORT} - {e}")
        for s in _servers:
            s.shutdown()
        _servers.clear()
        return False


def open_browser(url):
    if shutil.which("termux-open-url"):
        try:
            subprocess.Popen(["termux-open-url", url], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except OSError:
            print(Fore.YELLOW + f"  [!] Could not launch browser. Open: {url}")
    else:
        print(Fore.YELLOW + f"  [!] termux-open-url not found. Open this in your browser: {url}")


def main():
    global _pending_modify
    if sys.argv[1:3] != ["rea", "start"]:
        print("Usage: hex rea start")
        return
    banner()
    url = f"http://{HOST}:{PORT}/"
    while True:
        try:
            choice = menu()
        except (EOFError, KeyboardInterrupt):
            print()
            break
        if choice == "1":
            if start_servers():
                print(Fore.GREEN + f"\n  [✓] Editor  {url}")
                print(Fore.GREEN + f"  [✓] Preview http://{HOST}:{PREVIEW_PORT}/")
                open_browser(url)
                dest, shared = storage_dir()
                if shared:
                    print(Fore.LIGHTBLACK_EX + f"  Downloads will be saved to: {dest}\n")
                else:
                    print(Fore.YELLOW + "  [!] Run `termux-setup-storage` once so downloads can be saved to your file manager.\n")
            time.sleep(0.5)
        elif choice == "2":
            break
        elif choice == "3":
            rea_sites()
            banner()
        elif choice == "__MODIFY__":
            site = _pending_modify
            _pending_modify = None
            if site:
                print(Fore.WHITE + f"\n  You are about to enter the REA modifier for {Fore.GREEN}{site['url']}")
                ans = hexprompt("rea · confirm  [y]es / [n]o")
                if ans.lower() in ("y", "yes"):
                    rea_modifier(site)
                banner()
        else:
            print(Fore.YELLOW + "  [!] Choose 1, 2 or 3.\n")
    for s in _servers:
        s.shutdown()
        s.server_close()
    print(Fore.RED + "  Session closed.")


if __name__ == "__main__":
    main()

