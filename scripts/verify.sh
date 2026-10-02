#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mkdir -p evidence
execution_config=$(mktemp "${TMPDIR:-/tmp}/bce-comparator.XXXXXX")
trap 'rm -f "$execution_config"' EXIT HUP INT TERM
python3 scripts/verification_config.py "$execution_config" > evidence/configuration.log 2>&1
python3 scripts/check_package.py
python3 scripts/verify_metadata.py > evidence/metadata-validation.log 2>&1
lake build Challenge > evidence/challenge-build.log 2>&1
lake build Solution > evidence/solution-build.log 2>&1
lake build > evidence/full-build.log 2>&1
lake env lean Audit.lean > evidence/final-axioms.log 2>&1
python3 scripts/check_challenge_axioms.py
lake env lean ContractAudit.lean > evidence/contract-binders.log 2>&1
lake env lean --src-deps Challenge.lean > evidence/challenge-source-deps.log 2>&1
python3 - <<'PY'
from pathlib import Path
for p in Path('evidence/challenge-source-deps.log').read_text().splitlines():
    assert '/src/lean/' in p or '/.lake/packages/mathlib/' in p, p
PY
python3 scripts/check_package.py
case "$(uname -s)" in
  Darwin) lake comparator --config "$execution_config" --inadvisably-no-sandbox > evidence/final-comparator.log 2>&1 ;;
  *) lake comparator --config "$execution_config" > evidence/final-comparator.log 2>&1 ;;
esac
python3 - <<'PY'
from pathlib import Path
log = Path('evidence/final-comparator.log').read_text()
assert 'Your solution is okay!' in log
for kernel in ('Lean default', 'nanoda', 'con-ron'):
    assert f'{kernel} kernel accepts the solution' in log, kernel
print(log)
PY
python3 - <<'PY'
from pathlib import Path
for path in Path('evidence').glob('*.log'):
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines()) + '\n')
PY
git diff --check
