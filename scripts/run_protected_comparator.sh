#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "$(uname -s)" != Linux ]]; then
  echo "NOT RUN: the protected Comparator requires Linux and bwrap." >&2
  exit 2
fi
for required_command in bwrap lake lean python3; do
  command -v "$required_command" >/dev/null
done
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "Missing bundled verifier: $prefix/bin/$tool" >&2
    exit 2
  fi
done
python3 scripts/check_snapshot.py
# Register the independent kernels in a verifier-owned temporary copy, as in
# PalomarTemplate/scripts/verify-comparator.sh. The submitted config is unchanged.
config=$(mktemp "${TMPDIR:-/tmp}/density-protected-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys
source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
assert isinstance(config, dict)
assert 'external_kernels' not in config, 'Not a submitter config field'
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron'],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
lake exe cache get
lake comparator --config "$config"
