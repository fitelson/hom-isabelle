#!/usr/bin/env bash
set -euo pipefail
APP_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CORE_DIR="$(cd "$APP_DIR/../.." && pwd)"
if [[ $# -ne 0 ]]; then
  echo "Usage: $0" >&2
  exit 2
fi
python3 "$CORE_DIR/tools/check_isabelle_trust.py" --root "$APP_DIR"
python3 "$APP_DIR/tools/check_package.py"
# This is a separate application session. All Isabelle work is serialized.
exec isabelle build -j 1 -d "$CORE_DIR" -D "$APP_DIR" \
  -o timeout=60 -o export_theory=true -o skip_proofs=false
