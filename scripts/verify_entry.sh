#!/usr/bin/env bash
# Explicit, local verification only. Never submits, pushes, or registers.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
entry=${1:?Usage: bash scripts/verify_entry.sh P003}
if [[ ! "$entry" =~ ^P[0-9]{3}$ ]]; then
  echo 'error: expected a paper identifier such as P003' >&2
  exit 2
fi
source_config="entries/$entry/comparator.json"
if [[ ! -f "$source_config" ]]; then
  echo "error: $entry has no completed Comparator configuration" >&2
  exit 2
fi
for command in bwrap lake lean python3 timeout; do
  command -v "$command" >/dev/null || { echo "error: missing $command" >&2; exit 2; }
done
python3 scripts/verification_preflight.py
prefix=$(lean --print-prefix)
for command in lake leanexport leanchecker nanoda_bin con-ron; do
  [[ -x "$prefix/bin/$command" ]] || { echo "error: target toolchain lacks $command" >&2; exit 2; }
done
mkdir -p .local/verification
run_dir=$(mktemp -d ".local/verification/$entry.XXXXXXXX")
config="$run_dir/comparator.protected.json"
python3 - "$source_config" "$config" "$prefix" "$run_dir" <<'PY'
import hashlib, json, os, pathlib, subprocess, sys
source, destination, prefix, run = sys.argv[1:]
config=json.loads(pathlib.Path(source).read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels is not permitted in submitted configuration')
config.pop('enable_nanoda',None)
con_ron=[f'{prefix}/bin/con-ron']
con_ron_jobs=os.environ.get('CON_RON_JOBS')
if con_ron_jobs:
    if not con_ron_jobs.isdecimal() or int(con_ron_jobs) < 1:
        raise SystemExit('CON_RON_JOBS must be a positive decimal integer')
    con_ron.append(f'--jobs={con_ron_jobs}')
config['external_kernels']={'nanoda':[f'{prefix}/bin/nanoda_bin'],'con-ron':con_ron}
pathlib.Path(destination).write_text(json.dumps(config,indent=2)+'\n')
paths=[]
for directory, folders, files in os.walk('.'):
    folders[:]=[f for f in folders if f not in {'.git','.lake','.local','__pycache__'}]
    paths.extend(pathlib.Path(directory)/file for file in files)
snapshot={p.as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
pathlib.Path(run,'source-hashes.json').write_text(json.dumps(snapshot,indent=2)+'\n')
pathlib.Path(run,'toolchain.txt').write_text(subprocess.check_output(['lean','--version'],text=True))
PY
# This is an explicit verification command: cache retrieval and proof replay can
# be lengthy. No preparation script calls it automatically. Limits are per run.
set +e
timeout "${CACHE_TIMEOUT_SECONDS:-1800}" lake exe cache get 2>&1 | tee "$run_dir/cache.log"
result=${PIPESTATUS[0]}
stage=cache
if [[ "$result" -eq 0 ]]; then
  stage=comparator
  timeout "${VERIFY_TIMEOUT_SECONDS:-14400}" lake comparator --config "$config" 2>&1 | tee "$run_dir/comparator.log"
  result=${PIPESTATUS[0]}
fi
set -e
python3 - "$run_dir" "$entry" "$result" "$stage" <<'PY'
import datetime, hashlib, json, os, pathlib, sys
run,entry,code,stage=sys.argv[1:]
before=json.loads(pathlib.Path(run,'source-hashes.json').read_text())
after={}
for directory, folders, files in os.walk('.'):
    folders[:]=[f for f in folders if f not in {'.git','.lake','.local','__pycache__'}]
    for file in files:
        p=pathlib.Path(directory)/file
        after[p.as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
changed=sorted(p for p in before.keys() | after.keys() if before.get(p)!=after.get(p))
record={'entry':entry,'last_stage':stage,'last_stage_exit_code':int(code),
        'comparator_exit_code':int(code) if stage=='comparator' else None,
        'completed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_snapshot':'source-hashes.json',
        'changed_during_verification':changed,
        'mechanical_verification':('SOURCE_CHANGED' if changed else
                                   'PASS' if stage=='comparator' and code=='0' else 'FAIL_OR_RESOURCE_LIMIT'),
        'editorial_review':'NOT_RUN','submission':'NOT_PERFORMED'}
pathlib.Path(run,'result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
if changed:
    raise SystemExit('Source changed during verification; do not treat this run as a release receipt.')
PY
echo "Evidence directory: $run_dir"
exit "$result"
