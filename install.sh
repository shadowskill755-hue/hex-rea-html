#!/usr/bin/env bash
set -e
DIR="$(cd "$(dirname "$0")" && pwd)"

if command -v pkg >/dev/null 2>&1; then
  pkg update -y && pkg install -y python git termux-api
  termux-setup-storage || true
  BIN="$PREFIX/bin/hex"
else
  BIN="/usr/local/bin/hex"
fi

pip install requests beautifulsoup4 colorama

cat > "$BIN" << LAUNCHER
#!/usr/bin/env sh
exec python3 "$DIR/hex.py" "\$@"
LAUNCHER

chmod +x "$BIN" "$DIR/hex.py"
echo ""
echo "[✓] HEX REA installed! Start anytime with:  hex rea start"
