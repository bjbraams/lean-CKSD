# Core knowledge in statistics and data science: Mathlib, TauCeti, and Statlib coverage

The eight files `STRUCTURE101.md`–`STRUCTURE108.md` describe relevant
definitions, structures, and proved results in Mathlib, TauCeti, and Statlib for the
material of the [mathematical synopses](SYNOPSIS.md) `SYNOPSIS101.md`–`SYNOPSIS108.md`.
Their topical order follows the synopses and the current
[bibliography](CKSD-bib.md), including the lettered subdivisions. They follow
the conventions of the coverage inventories of the sibling analysis project,
[CKMA STRUCTURE.md](../lean-CKMA/STRUCTURE.md), whose files are cited where
the probability, analysis, and geometry on which statistics builds are
already described there.

Each inventory distinguishes Mathlib, TauCeti, and Statlib within a mathematical topic.
TauCeti and Statlib are developed independently on top of Mathlib; a result of
either is recorded only where Mathlib lacks it, and a result proved in both is
recorded under both without preference.
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
one or more of the three libraries, possibly in an equivalent formulation), *partly covered*
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
section **Missing from all three libraries**, a brief review of the principal
results of the synopsis that none of the libraries provides, with the existing
infrastructure from which they would be developed.

Across the 537 synopsis entries, the three libraries together cover 5, partly
cover 55, and do not cover 477. Section-by-section summaries for each
library are in [MathlibCoverage.md](MathlibCoverage.md),
[TauCetiCoverage.md](TauCetiCoverage.md), and
[StatlibCoverage.md](StatlibCoverage.md). The separate
[gap inventory](GAPS.md) selects 296 principal missing results, restates
them, and assesses what the libraries supply towards each. Of these,
[GAPS_EASY.md](GAPS_EASY.md) outlines short derivations from library
results for 110, some for part of the statement only.

## Comparison with CKMA

The counts in this series measure direct declaration coverage under the
rule above. CKMA sometimes also classifies short derivations as partly
covered, its recorded Mathlib and TauCeti revisions are earlier, and it
does not consider Statlib. The two sets of
counts therefore cannot be compared as coverage percentages on a common
basis. The distinction is retained explicitly for the separate projects;
a future merger will need a common classification rule and source
baseline, followed by review of the affected verdicts. A short derivation
in GAPS_EASY.md remains a missing library statement under the present
rule, and a Scope paragraph may delimit only part of its entry.

## Source baseline and conventions

The coverage statements were checked on **2026-11-06** against local checkouts
of the following revisions, which are the dependency pins of this project:

- **Mathlib:** commit
  [`6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`](https://github.com/leanprover-community/mathlib4/tree/6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b)
  of 2026-11-05, using Lean `v4.36.0-rc2`. This is a later Mathlib revision
  than the one recorded in the CKMA inventories.
- **TauCeti:** commit
  [`afa08a3ed16fb167e35de371afb1eb03fbc5913a`](https://github.com/TauCetiProject/TauCeti/tree/afa08a3ed16fb167e35de371afb1eb03fbc5913a)
  of 2026-11-06. This is a later TauCeti revision than the one recorded in the
  CKMA inventories, so TauCeti statements in the CKMA files cited here may
  differ in detail.
- **Statlib:** commit
  [`eeaac0283690efaa60c31115400cf561836baeb9`](https://github.com/stat-lib/statlib/tree/eeaac0283690efaa60c31115400cf561836baeb9)
  of 2026-11-05, a Lean library for mathematical statistics built on Mathlib
  ([project page](https://stat-lib.github.io/)). Its own Mathlib pin is the
  Mathlib revision above.

The check was by source inspection: cited files and declarations were located
and their hypotheses compared with the synopsis statements. A TauCeti or
Statlib result is recorded as proved only when the cited declaration does not
rely on `sorry`, `admit`, or an added axiom, as far as can be seen in its
source; no such use occurs in the Statlib revision. The project and the full
Statlib library build against the pinned Mathlib with Lean `v4.36.0-rc2`. TauCeti's own Mathlib pin is [`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`](https://github.com/leanprover-community/mathlib4/tree/1b1ccf4b088b32fa3f23f2de1127433254a81e1e). Against the Mathlib pin of this project, 206 TauCeti modules fail to compile, mainly through deprecation and linter warnings, which TauCeti treats as errors, and in a few cases through proofs that no longer elaborate; modules importing them are not built. Of the 255 cited TauCeti files, 247 compile in this setting and 8 are not built because they import a failing module: `TauCeti/Probability/Distributions/Gaussian/Conditional/Basic.lean`, `TauCeti/Analysis/Matrix/CovariancePseudoInverse.lean`, `TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/FixedPoint.lean`, `TauCeti/Geometry/Manifold/Riemannian/Geodesic/Exponential.lean`, `TauCeti/Geometry/Manifold/Riemannian/Geodesic/HopfRinow.lean`, `TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/Sectional/Basic.lean`, `TauCeti/AlgebraicTopology/Singular/Cech/QuasiIso.lean`, `TauCeti/RepresentationTheory/Quiver/FiniteRepType/Gabriel.lean`. Their results are recorded from source in the same way as those of the other cited files. No axiom-dependency check was run.

Mathlib paths such as `Probability/Decision/Risk/Basic.lean` are relative to
[`Mathlib/` at the recorded revision](https://github.com/leanprover-community/mathlib4/tree/6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b/Mathlib).
`Mathlib/...` includes that prefix explicitly. A source file `Mathlib/A/B/C.lean`
is imported as `import Mathlib.A.B.C`; dotted source-area names can also denote
directory prefixes, so the individual `.lean` files cited in the entries are
the precise import entry points.

TauCeti and Statlib source links are pinned to their recorded commits. A file
`TauCeti/A/B/C.lean` is imported as `import TauCeti.A.B.C`, and a file
`Statlib/A/B/C.lean` as `import Statlib.A.B.C`, in the matching dependency
environment. Statlib's `sqHellinger` is half the squared Hellinger distance of
the synopses, and the `tvDist` of two probability laws used by Statlib and
TauCeti is twice the total-variation distance \(\|P-Q\|_{\mathrm{TV}}\) of the
synopses. Declaration names and namespaces provide search terms; the full
hypotheses of the cited declaration govern reuse. A human-readable summary is
not a replacement for checking those hypotheses in Lean.

## Topical inventories

- [101. Statistical inference: foundations, decision theory, estimation, and testing](STRUCTURE101.md)
- [102. Asymptotic, semiparametric, and robust statistics](STRUCTURE102.md) — 102A–B
- [103. Nonparametric and high-dimensional inference](STRUCTURE103.md) — 103A–B
- [104. Bayesian inference and stochastic computation](STRUCTURE104.md) — 104A–C
- [105. Linear models, multivariate analysis, experimental design, and causal inference](STRUCTURE105.md) — 105A–B
- [106. Dependent data and stochastic models](STRUCTURE106.md) — 106A–B
- [107. Statistical learning and machine learning](STRUCTURE107.md) — 107A–B
- [108. Geometry of data: manifolds, topology, optimal transport, and kernels](STRUCTURE108.md) — 108A–B
