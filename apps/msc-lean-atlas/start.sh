#!/bin/sh
set -eu
atlas_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ ! -x "$atlas_root/.venv/bin/python" ]; then
  echo "Run python3.12 -m venv .venv and .venv/bin/pip install -r requirements-research.lock in $atlas_root first." >&2
  exit 1
fi
exec "$atlas_root/.venv/bin/python" "$atlas_root/server.py" "$@"
