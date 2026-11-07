# Core Knowledge of Statistics and Data Science

This project inventories core statistics and data science at the level of
graduate students and beginning researchers, and compares that mathematics
with the Lean libraries Mathlib, TauCeti, and Statlib. It follows the sibling
[Core Knowledge of Mathematical Analysis](../lean-CKMA/README.md) project.

The [bibliography](CKSD-bib.md) organizes Sections 101–109. The mathematical
synopses and library inventories cover Sections 101–108; Section 109, on
optimization and numerical algorithms, is outside this series.

## Main documents

- [SYNOPSIS.md](SYNOPSIS.md) indexes the mathematical synopses. Their
  numbered statements have stable identifiers.
- [STRUCTURE.md](STRUCTURE.md) indexes the coverage inventories and records
  their source revisions and classification rule. Each topic file names
  declarations, source locations, hypotheses, and missing results.
- [MathlibCoverage.md](MathlibCoverage.md),
  [TauCetiCoverage.md](TauCetiCoverage.md), and
  [StatlibCoverage.md](StatlibCoverage.md) summarize each library separately.
- [GAPS.md](GAPS.md) selects principal missing statements and assesses the
  work remaining.
- [GAPS_EASY.md](GAPS_EASY.md) gives short mathematical derivations for
  selected gaps. A Scope paragraph identifies when only part is addressed.

The local Lean library is in [CKSD/](CKSD/), with public entry point
[CKSD.lean](CKSD.lean). All project declarations use namespace `CKSD`.
[FORMALIZATION.md](FORMALIZATION.md) indexes every selected gap against the
available theorem formulations and records proofs, admissions, and work
still needing a statement. Definitions contain no admissions. The remaining
theorem proofs may use explicit `sorry`.

The coverage inventories describe the pinned external libraries; local
statements and proofs are tracked separately. Mathlib provides models and
randomized estimators as Markov kernels and the risk framework on which
Statlib builds binary testing. CKSD's direct-coverage rule is stricter than
some CKMA classifications, so their counts are not directly comparable; see
the [comparison conventions](STRUCTURE.md#comparison-with-ckma).

Build from the project root with `lake build > /tmp/cksd-build.log 2>&1`.
The dependency pins and the project-specific `.lake` symlink are authoritative.
See [formalization validation](FORMALIZATION.md#validation) and
[CREDITS.md](CREDITS.md) for checks and source provenance.

## Areas

- **101. Statistical inference:** foundations, decision theory, estimation,
  and testing — [synopsis](SYNOPSIS101.md), [coverage](STRUCTURE101.md).
- **102. Asymptotic, semiparametric, and robust statistics** —
  [synopsis](SYNOPSIS102.md), [coverage](STRUCTURE102.md).
- **103. Nonparametric and high-dimensional inference** —
  [synopsis](SYNOPSIS103.md), [coverage](STRUCTURE103.md).
- **104. Bayesian inference and stochastic computation** —
  [synopsis](SYNOPSIS104.md), [coverage](STRUCTURE104.md).
- **105. Linear models, multivariate analysis, experimental design, and
  causal inference**, including finite-population survey sampling —
  [synopsis](SYNOPSIS105.md), [coverage](STRUCTURE105.md).
- **106. Dependent data and stochastic models** —
  [synopsis](SYNOPSIS106.md), [coverage](STRUCTURE106.md).
- **107. Statistical learning and machine learning** —
  [synopsis](SYNOPSIS107.md), [coverage](STRUCTURE107.md).
- **108. Geometry of data:** manifolds, topology, optimal transport, and
  kernels — [synopsis](SYNOPSIS108.md), [coverage](STRUCTURE108.md).

Reference guides distinguish local full texts, previews, and other sources.
Most local copies are shared with CKMA in its `References` and
`ReferencesSuppl` directories. Mathematical corrections must be propagated
through every restatement, coverage assessment, and affected count, while
preserving existing result identifiers.
