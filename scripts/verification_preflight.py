"""Check the local Linux verifier environment without compiling research proofs."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def main():
    errors = []
    record = {'kind': 'ENVIRONMENT_ONLY_NOT_PROOF_VERIFICATION',
              'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'platform': platform.system(), 'errors': errors}
    expected = (ROOT / 'lean-toolchain').read_text().strip()
    record['expected_toolchain'] = expected
    record['manifest_sha256'] = hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest()
    if platform.system() != 'Linux':
        errors.append('Independent verification requires Linux; Windows statement checks are insufficient.')
    else:
        paths = {name: shutil.which(name) for name in ('lean', 'lake', 'bwrap', 'timeout', 'git', 'python3')}
        record['commands'] = paths
        errors.extend('Missing executable: ' + name for name, path in paths.items() if not path)
        if os.environ.get('COMPARATOR_BWRAP'):
            errors.append('Unset COMPARATOR_BWRAP so preflight and Comparator use the same bwrap executable.')
        try:
            if paths['lean']:
                version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True, timeout=30).strip()
                record['actual_lean_version'] = version
                match = re.search(r'Lean \(version ([^,\s]+)', version)
                if not match or 'leanprover/lean4:v' + match[1] != expected:
                    errors.append('Active Lean version does not match lean-toolchain.')
                prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True, timeout=30).strip())
                record['toolchain_prefix'] = str(prefix)
                kernels = {name: str(prefix / 'bin' / name) for name in
                           ('lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron')}
                record['bundled_tools'] = kernels
                errors.extend('Missing bundled executable: ' + path for path in kernels.values()
                              if not os.access(path, os.X_OK))
            if paths['bwrap']:
                # Mirror Check.lean/buildSandboxArgs baseline mounts and namespaces.
                command = [paths['bwrap'], '--ro-bind', '/', '/', '--tmpfs', '/home',
                           '--tmpfs', '/root', '--tmpfs', '/run/user', '--tmpfs', '/tmp',
                           '--dir', '/tmp/home', '--dev', '/dev', '--proc', '/proc',
                           '--clearenv', '--unshare-all', '--die-with-parent', '--new-session',
                           '--chdir', '/', '--', '/bin/true']
                result = subprocess.run(command, text=True, capture_output=True, timeout=20)
                record['sandbox_probe'] = {'command': command, 'exit_code': result.returncode,
                                           'stderr': result.stderr}
                if result.returncode:
                    errors.append('bwrap mount/namespace probe failed; do not start proof verification.')
        except (subprocess.SubprocessError, OSError) as error:
            errors.append(str(error))
    record['status'] = 'FAIL' if errors else 'PASS_ENVIRONMENT_ONLY'
    output = ROOT / '.local/verification/environment-preflight.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(record, indent=2))
    return 2 if errors else 0

if __name__ == '__main__':
    raise SystemExit(main())
