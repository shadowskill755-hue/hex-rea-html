# HEX REA — HTML Recon & Modifier Terminal

## Install on Termux
```bash
pkg update -y && pkg install -y git python
git clone https://github.com/shadowskill755-hue/hex-rea-html.git
cd hex-rea-html
bash install.sh
hex rea start
[1] Recon Editor & Deep Analyzer (editor.html)
[3] AI Site Modifier powered by Groq (modify.html + Termux CLI)
Get a free Groq API key (gsk_...) at https://console.groq.com/keys
check tze files first therr as been some upgrade so this migth no be needed
---

### Step 2: Clean GitHub History & Push ONLY Your Tool Files (Keeps `saved/` Safe on Your Phone)

Run these commands inside `~/hex-rea-html`:

```bash
cat > .gitignore << 'EOF'
saved/
downloads/
__pycache__/
*.pyc
*.zip
.env
.hexrea/
