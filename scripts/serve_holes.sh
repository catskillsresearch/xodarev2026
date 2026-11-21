#!/usr/bin/env bash
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Serve the SignatureVolatility holes board (same pattern as lyasoff2016 / yaacov).
#
#   scripts/serve_holes.sh          # rebuild board, serve on PORT (default 8766)
#   PORT=8767 scripts/serve_holes.sh
#
# Then open http://127.0.0.1:${PORT}/holes.html
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
PORT="${PORT:-8766}"
BIND="${BIND:-127.0.0.1}"

python3 scripts/build_holes.py
echo "Serving $ROOT on http://${BIND}:${PORT}/holes.html"
exec python3 -m http.server "$PORT" --bind "$BIND"
