# Core Knowledge of Statistics and Data Science

This project inventories core statistics and data science at the level of
graduate students and beginning researchers, and compares that mathematics
with the Lean libraries Mathlib and TauCeti. It follows the sibling
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
- [MathlibCoverage.md](MathlibCoverage.md) and
  [TauCetiCoverage.md](TauCetiCoverage.md) summarize each library separately.
- [GAPS.md](GAPS.md) selects principal missing statements and assesses the
  work remaining.
- [GAPS_EASY.md](GAPS_EASY.md) gives short mathematical derivations for
  selected gaps. A Scope paragraph identifies when only part is addressed.

Coverage and short derivations rest on source inspection. They have not
been implemented and compiled as Lean proofs. Mathlib already provides
models and randomized estimators as Markov kernels, with a decision-theory
risk framework; many dedicated statistical notions and theorems remain
absent. CKSD's direct-coverage rule is stricter than some CKMA
classifications, so their counts are not directly comparable; see the
[comparison conventions](STRUCTURE.md#comparison-with-ckma).

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
