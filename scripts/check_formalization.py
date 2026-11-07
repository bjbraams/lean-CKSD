#!/usr/bin/env python3
"""Audit CKSD declarations and regenerate the gap-to-code index from source docstrings.

Run after `lake build > /tmp/cksd-build.log 2>&1`. With --write, update the root
FORMALIZATION.md and formalization.json. Otherwise require them to match.
This audits the compiled axiom dependencies, not just occurrences of `sorry`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r"(?m)^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|scoped|local) )*"
                  r"(def|abbrev|structure|inductive|theorem|lemma)\s+([^\s({:]+)")
DOC = re.compile(r"/--(.*?)\-/", re.S)
GAP = re.compile(r"GAPS (\d{3}\.\d+)")
ADMISSION = re.compile(r"(?m)^\s*sorry\b")
AREAS = {101: 'Inference', 102: 'Asymptotics', 103: 'Nonparametric', 104: 'Bayes',
         105: 'LinearModels', 106: 'Processes', 107: 'Learning', 108: 'Geometry'}


SCOPE = re.compile(r'(?m)^(namespace|section|end)\b[ \t]*([^\s-]*)')


def namespace_at(source, position):
    """Return the namespace in force at `position`, following namespace/section/end lines."""
    stack = []
    for scope in SCOPE.finditer(source[:position]):
        kind, label = scope[1], scope[2]
        if kind == 'end':
            if stack:
                stack.pop()
        else:
            stack.append((kind, label))
    return '.'.join(label for kind, label in stack if kind == 'namespace')


def read_declarations():
    result = []
    for path in sorted((ROOT / 'CKSD').rglob('*.lean')):
        source = path.read_text()
        matches, docs = list(DECL.finditer(source)), list(DOC.finditer(source))
        for i, match in enumerate(matches):
            earlier = [d for d in docs if d.end() <= match.start()]
            if not earlier:
                raise ValueError(f'Missing docstring: {path}:{match[2]}')
            doc = earlier[-1]
            between = re.sub(r'@\[[^\]]*\]', '', source[doc.end():match.start()]).strip()
            if between:
                raise ValueError(f'Docstring not adjacent: {path}:{match[2]}')
            body = source[match.end():matches[i + 1].start() if i + 1 < len(matches) else len(source)]
            kind, short = match[1], match[2]
            prefix = namespace_at(source, match.start())
            if not prefix.startswith('CKSD'):
                raise ValueError(f'Declaration outside CKSD: {path}:{short}')
            name = prefix + '.' + short
            if short.startswith('_root_.'):
                raise ValueError(f'Declaration escapes CKSD: {name}')
            is_theorem = kind in ('theorem', 'lemma')
            admitted = bool(ADMISSION.search(body))
            if admitted and not is_theorem:
                raise ValueError(f'Admitted definition: {name}')
            result.append(dict(name=name, kind=kind, file=str(path.relative_to(ROOT)),
                               line=source[:match.start()].count('\n') + 1,
                               doc=' '.join(doc[1].split()),
                               gaps=GAP.findall(doc[1]), admitted=admitted,
                               source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    names = [d['name'] for d in result]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate declaration names')
    return result


def audit_axioms(declarations):
    """Lean checks every expected declaration and audits its transitive axiom closure."""
    names = ',\n    '.join('`' + d['name'] for d in declarations)
    source = '''import CKSD
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : List Name := [NAMES]
  for name in names do
    unless env.contains name do throwError "Missing declaration: {name}"
    let axioms ← collectAxioms name
    logInfo m!"CKSD_AXIOMS {name}: {axioms.toList}"
'''.replace('NAMES', names)
    with tempfile.TemporaryDirectory(prefix='cksd-axioms-') as folder:
        path = Path(folder) / 'Audit.lean'
        path.write_text(source)
        run = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false',
                              '-DrelaxedAutoImplicit=false', str(path)], cwd=ROOT,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    Path('/tmp/cksd-formalization-axioms.log').write_text(run.stdout)
    if run.returncode:
        raise ValueError('Lean axiom audit failed; see /tmp/cksd-formalization-axioms.log')
    found = {}
    for name, axioms in re.findall(r'CKSD_AXIOMS ([^:]+): \[([^\]]*)\]', run.stdout):
        found[name] = [a.strip() for a in axioms.split(',') if a.strip()]
    allowed = {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}
    for d in declarations:
        if d['name'] not in found:
            raise ValueError(f"No axiom audit output: {d['name']}")
        axioms = found[d['name']]
        unexpected = set(axioms) - allowed
        if unexpected:
            raise ValueError(f"Unexpected axioms for {d['name']}: {unexpected}")
        if d['admitted'] and 'sorryAx' not in axioms:
            raise ValueError(f"Stale build: {d['name']}")
        if 'sorryAx' in axioms and d['kind'] not in ('theorem', 'lemma'):
            raise ValueError(f"Definition depends on an admission: {d['name']}")
        d['axioms'] = axioms
        if d['kind'] in ('theorem', 'lemma'):
            # `conditional`: the proof itself is complete but uses an admitted result.
            d['proof'] = ('admitted' if d['admitted'] else
                          'conditional' if 'sorryAx' in axioms else 'proved')
    return declarations


def make_inventory(declarations):
    gaps = re.findall(r'(?ms)^\* \*\*(\d{3}\.\d+)\. (.*?)\*\*', (ROOT / 'GAPS.md').read_text())
    easy = set(re.findall(r'(?m)^### (\d{3}\.\d+)\.', (ROOT / 'GAPS_EASY.md').read_text()))
    if len(gaps) != len(set(i for i, _ in gaps)):
        raise ValueError('Duplicate gap identifiers')
    ids = {i for i, _ in gaps}
    if any(g not in ids for d in declarations for g in d['gaps']):
        raise ValueError('A declaration cites a nonexistent selected gap')
    theorem_map = {g: [d['name'] for d in declarations if g in d['gaps'] and 'proof' in d] for g in ids}
    missing_easy = sorted(g for g in easy if not theorem_map[g])
    if missing_easy:
        raise ValueError(f'No scoped statement for easy entries: {missing_easy}')
    entries = [dict(id=g, title=' '.join(t.split()), easy=g in easy, theorems=theorem_map[g]) for g, t in gaps]
    stats = Counter(d.get('proof', 'definition') for d in declarations)
    stats.update(proved=0, admitted=0, conditional=0)
    stats.update(gaps=len(gaps), easy_entries=len(easy),
                 gaps_with_statements=sum(bool(e['theorems']) for e in entries),
                 gaps_without_statements=sum(not e['theorems'] for e in entries))
    return dict(schema_version=1, scope_rule='A tagged theorem represents only its stated hypotheses and '
                'conclusions. Presence of a statement does not assert full coverage of a catalogue family.',
                counts=dict(stats), declarations=declarations, gaps=entries)


def render(inventory):
    c = inventory['counts']
    byname = {d['name']: d for d in inventory['declarations']}
    lines = ['# CKSD formalization', '',
             'The public entry point is [CKSD.lean](CKSD.lean). Every project declaration is in',
             '`namespace CKSD` or one of its subnamespaces. The module names follow topics, while',
             'the stable identifiers of [GAPS.md](GAPS.md) connect code to the mathematical catalogue.', '',
             f"There are **{c['definition']} definitions, abbreviations, structures, and inductive types**",
             f"and **{c['proved'] + c['admitted'] + c['conditional']} theorem statements**: "
             f"**{c['proved']} proved**,",
             f"**{c['conditional']} conditional** (the proof is complete but uses an admitted result), and",
             f"**{c['admitted']} admitted**. Definitions contain no admissions. A compiled axiom audit",
             'checks that proved results do not depend on `sorryAx`; only the usual Lean classical',
             'axioms occur in their dependency closures.', '',
             f"The index contains all **{c['gaps']} selected gap families**. **{c['gaps_with_statements']}**",
             f"have at least one scoped theorem statement and **{c['gaps_without_statements']}** still need",
             f"a theorem formulation. All **{c['easy_entries']} entries** of [GAPS_EASY.md](GAPS_EASY.md)",
             'have at least one scoped statement. This does **not** mean that all their short-derivation',
             'scopes are formalized or proved. Finite-dimensional, finite-class, scalar, deterministic,',
             'or algebraic restrictions in a declaration must be retained when reading its status.', '',
             'A statement below is linked even when its proof is admitted. **No full-family coverage',
             'classification is inferred from these links.** The mathematical synopsis and the',
             'Mathlib/TauCeti/Statlib coverage counts retain their own meaning and source baseline.', '',
             '## Modules', '']
    for n, area in AREAS.items():
        lines.append(f'- Section {n}: [{area}](CKSD/{area}.lean); definitions and results in `CKSD/{area}/`.')
    lines += ['', 'The `Basic` modules provide common definitions. The other files contain thematic',
              'definitions and results; direct files under `CKSD/` assemble those modules.',
              '`Suggested101.lean`–`Suggested108.lean` are compatibility import modules.', '',
              '## Reuse and conventions', '',
              'Mathlib measures, kernels, conditional expectations, linear maps, projections, categories,',
              'and `Lp` spaces are reused. TauCeti supplies distribution and transport constructions;',
              'Statlib supplies the probability-measure contiguity interface. Some section drafts use',
              'real-moment or measure-valued statistical adapters; their docstrings specify integrability',
              'and normalization conventions. See [CREDITS.md](CREDITS.md) for provenance.', '',
              'Dependency revisions and the Lean toolchain are recorded in `lakefile.toml`,',
              '`lake-manifest.json`, and `lean-toolchain`. The build output is `.lake/build-CKSD`.', '',
              '## Validation', '',
              'Run from the project root:', '', '```sh',
              'lake build > /tmp/cksd-build.log 2>&1',
              'python3 scripts/check_formalization.py',
              'python3 scripts/check_lean_files.py', 'git diff --check', '```', '',
              'The inventory checker compiles an axiom audit, checks declaration names and source links,',
              'and compares this index and [formalization.json](formalization.json) with the source.',
              'Use `--write` to regenerate the two index files after changes. The individual-file checker',
              'checks every project Lean module with both implicit-variable options disabled.', '',
              '## Catalogue', '']
    for n in AREAS:
        lines += [f'### Section {n}', '']
        for e in inventory['gaps']:
            if not e['id'].startswith(str(n) + '.'):
                continue
            label = f"- **{e['id']} {e['title']}**"
            if not e['theorems']:
                lines.append(label + ' — theorem formulation pending.')
                continue
            lines.append(label)
            for name in e['theorems']:
                d = byname[name]
                lines += [f"  [{name}]({d['file']}#L{d['line']}) ({d['proof']}; scope in docstring)."]
        lines.append('')
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate the inventory files')
    args = parser.parse_args()
    inventory = make_inventory(audit_axioms(read_declarations()))
    outputs = {'formalization.json': json.dumps(inventory, ensure_ascii=False, indent=2) + '\n',
               'FORMALIZATION.md': render(inventory)}
    for name, expected in outputs.items():
        path = ROOT / name
        if args.write:
            path.write_text(expected)
        elif not path.exists() or path.read_text() != expected:
            raise ValueError(f'{name} is stale; regenerate with --write after building')
    print(json.dumps(inventory['counts'], sort_keys=True))


if __name__ == '__main__':
    main()
