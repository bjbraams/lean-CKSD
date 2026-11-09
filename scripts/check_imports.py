#!/usr/bin/env python3
"""Check the import rule between the statistics sections (AGENTS.md).

A file in Sections 101-106 may import any module of Foundations (`CKSD.Inference`). From another
of Sections 102-106 it may import only `Basic` modules (`CKSD.<Section>....Basic`). Sections 107
and 108 are not checked. Exit status 1 if a violation is found.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FOUNDATIONS = 'Inference'
STATISTICS = ['Inference', 'Asymptotics', 'Nonparametric', 'Bayes', 'LinearModels', 'Processes']
IMPORT = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(CKSD\.\S+)', re.M)


def main():
    violations = []
    for section in STATISTICS:
        for path in sorted((ROOT / 'CKSD' / section).rglob('*.lean')):
            for module in IMPORT.findall(path.read_text()):
                target = module.split('.')[1]
                if target in (section, FOUNDATIONS) or target not in STATISTICS:
                    continue
                if module.split('.')[-1] != 'Basic':
                    violations.append(f'{path.relative_to(ROOT)}: imports {module}')
    for line in violations:
        print(line)
    print(f'{len(violations)} import-rule violations')
    return bool(violations)


if __name__ == '__main__':
    sys.exit(main())
