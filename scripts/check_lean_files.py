#!/usr/bin/env python3
"""Check each CKSD Lean file after building imports, with the package's implicit-variable settings."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = Path('/tmp/cksd-file-checks')


def check(path):
    result = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false',
                             '-DrelaxedAutoImplicit=false', str(path.relative_to(ROOT))],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = LOGS / (str(path.relative_to(ROOT)).replace('/', '_') + '.log')
    log.write_text(result.stdout)
    return path, result.returncode, log


def main():
    LOGS.mkdir(exist_ok=True)
    files = sorted((ROOT / 'CKSD').rglob('*.lean')) + [ROOT / 'CKSD.lean']
    files += sorted(ROOT.glob('Suggested*.lean'))
    failed = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        for path, code, log in pool.map(check, files):
            if code:
                failed.append(path)
                print(f'FAILED {path.relative_to(ROOT)}: {log}', flush=True)
    print(f'{len(files) - len(failed)}/{len(files)} individual Lean checks passed; logs: {LOGS}')
    return bool(failed)


if __name__ == '__main__':
    sys.exit(main())
