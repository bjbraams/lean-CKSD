# Core knowledge in statistics and data science: Mathlib and TauCeti coverage

The eight files `STRUCTURE101.md`–`STRUCTURE108.md` describe relevant
definitions, structures, and proved results in Mathlib and TauCeti for the
material of the [mathematical synopses](SYNOPSIS.md) `SYNOPSIS101.md`–`SYNOPSIS108.md`.
Their topical order follows the synopses and the current
[bibliography](CKSD-bib.md), including the lettered subdivisions. They follow
the conventions of the coverage inventories of the sibling analysis project,
[CKMA STRUCTURE.md](../lean-CKMA/STRUCTURE.md), whose files are cited where
the probability, analysis, and geometry on which statistics builds are
already described there.

Each inventory distinguishes Mathlib from TauCeti within a mathematical topic.
It retains concrete source locations, declaration names, hypotheses, and scope
qualifications. Supporting constructions are identified as such: a library
definition of a divergence, a kernel, or a Gaussian law supports, but does not
itself prove, a statistical theorem that uses it. Definitions and unproved
statements, where retained for orientation, are explicitly labelled. Placement
under a synopsis heading does not claim that every numbered result under that
heading is formalized.

Each section corresponds to one `###` heading of the synopsis and ends with a
**Synopsis entries** line that sorts every numbered entry under that heading
into *covered* (the result as stated, with its hypotheses, is proved in
Mathlib or TauCeti, possibly in an equivalent formulation), *partly covered*
(with a note on what is present), or *not covered*. The line between the
last two is drawn uniformly. An entry is *partly covered* when a library
declaration proves one of the claims that the entry itself makes, or a
special case of the entry, either in an equivalent formulation or as a
direct instance of the declaration's hypotheses. An entry is *not covered*
when the libraries supply only ingredients from which the statement, or a
part of it, would follow by a further argument, however short, or only
supporting definitions; such entries carry the note *ingredients only*,
naming what is present. This is stricter than some classifications in the
sibling project, which count a result as partly covered when it follows
from library results. Each file ends with a
section **Missing from both libraries**, a brief review of the principal
results of the synopsis that neither library provides, with the existing
infrastructure from which they would be developed.

Across the 535 synopsis entries, the two libraries together cover 4, partly
cover 48, and do not cover 483. Section-by-section summaries for each
library are in [MathlibCoverage.md](MathlibCoverage.md) and
[TauCetiCoverage.md](TauCetiCoverage.md). The separate
[gap inventory](GAPS.md) selects 295 principal missing results, restates
them, and assesses what the libraries supply towards each. Of these,
[GAPS_EASY.md](GAPS_EASY.md) outlines short derivations from library
results for 107, some for part of the statement only.

## Source baseline and conventions

The coverage statements were checked on **2026-11-01** against local checkouts
of the following revisions, both of 2026-10-18:

- **Mathlib:** commit
  [`911003dd6dea5df215dff57f2717be762e11a6ca`](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca),
  using Lean `v4.36.0-rc1`. This is the Mathlib revision of the CKMA
  inventories.
- **TauCeti:** commit
  [`a049b4264d2cf4dbf4720796f844a3a3764914a5`](https://github.com/TauCetiProject/TauCeti/tree/a049b4264d2cf4dbf4720796f844a3a3764914a5).
  This is a later TauCeti revision than the one recorded in the CKMA
  inventories, so TauCeti statements in the CKMA files cited here may differ
  in detail.

The check was by source inspection: cited files and declarations were located
and their hypotheses compared with the synopsis statements. A TauCeti result
is recorded as proved only when the cited declaration does not rely on
`sorry`, `admit`, or an added axiom, as far as can be seen in its source. No
build or axiom-dependency check was run.

Mathlib paths such as `Probability/Decision/Risk/Basic.lean` are relative to
[`Mathlib/` at the recorded revision](https://github.com/leanprover-community/mathlib4/tree/911003dd6dea5df215dff57f2717be762e11a6ca/Mathlib).
`Mathlib/...` includes that prefix explicitly. A source file `Mathlib/A/B/C.lean`
is imported as `import Mathlib.A.B.C`; dotted source-area names can also denote
directory prefixes, so the individual `.lean` files cited in the entries are
the precise import entry points.

TauCeti source links are pinned to its recorded commit. A file
`TauCeti/A/B/C.lean` is imported as `import TauCeti.A.B.C` in the matching
dependency environment. Declaration names and namespaces provide search terms;
the full hypotheses of the cited declaration govern reuse. A human-readable
summary is not a replacement for checking those hypotheses in Lean.

## Topical inventories

- [101. Statistical inference: foundations, decision theory, estimation, and testing](STRUCTURE101.md)
- [102. Asymptotic, semiparametric, and robust statistics](STRUCTURE102.md) — 102A–B
- [103. Nonparametric and high-dimensional inference](STRUCTURE103.md) — 103A–B
- [104. Bayesian inference and stochastic computation](STRUCTURE104.md) — 104A–C
- [105. Linear models, multivariate analysis, experimental design, and causal inference](STRUCTURE105.md) — 105A–B
- [106. Dependent data and stochastic models](STRUCTURE106.md) — 106A–B
- [107. Statistical learning and machine learning](STRUCTURE107.md) — 107A–B
- [108. Geometry of data: manifolds, topology, optimal transport, and kernels](STRUCTURE108.md) — 108A–B
