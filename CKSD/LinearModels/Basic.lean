module

public import CKSD.Inference.Basic
public import TauCeti.Probability.Distributions.Wishart.Basic

/-!
# Linear models: common definitions

Definitions shared by the files on linear models, multivariate analysis, experimental design and
survey sampling (Section 105).

## Main definitions

* `CKSD.matrixQuadraticForm`: the quadratic form `x ↦ ⟪x, A x⟫` of a real square matrix.
* `CKSD.sampleMean`, `CKSD.scatterMatrix`: the mean and the centred scatter matrix
  `∑ᵢ (xᵢ - x̄)(xᵢ - x̄)ᵀ` of a finite Euclidean sample.
* `CKSD.gaussianNegLogLikelihood`: the negative Gaussian log-likelihood
  `(n/2) log det C + (1/2) ∑ᵢ (xᵢ - m)ᵀ C⁻¹ (xᵢ - m)` up to its constant term.
* `CKSD.simpleRandomSampleDesign`: the uniform law on the `n`-subsets of `{0, …, N-1}`,
  with the discrete measurable structure `CKSD.finiteSampleMeasurableSpace` on samples.
* `CKSD.populationMean`, `CKSD.populationVariance`: finite-population mean and variance with
  divisor `N - 1`.
* `CKSD.IsLatinSquare`, `CKSD.OrthogonalLatinSquares`: Latin squares of order `s` and their
  orthogonality.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- The discrete measurable structure on the samples (subsets) of a finite population. -/
scoped instance finiteSampleMeasurableSpace (N : ℕ) : MeasurableSpace (Finset (Fin N)) := ⊤

/-- Quadratic form of a real matrix on Euclidean space. -/
def matrixQuadraticForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x)

/-- Mean of a finite Euclidean sample. -/
def sampleMean {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- Centered scatter matrix of a finite Euclidean sample. -/
def scatterMatrix {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k ↦ ∑ i, (x i j - sampleMean x j) * (x i k - sampleMean x k)

/-- Negative Gaussian log-likelihood up to its constant term. -/
def gaussianNegLogLikelihood {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (n : ℝ) / 2 * Real.log C.det + (∑ i, matrixQuadraticForm C⁻¹ (x i - m)) / 2

/-- Simple random sampling without replacement: the uniform law on the subsets of size `n` of a
population of `N` units. It is a probability measure when `n ≤ N`. -/
def simpleRandomSampleDesign (N n : ℕ) : Measure (Finset (Fin N)) :=
  (Nat.choose N n : ℝ≥0∞)⁻¹ • Measure.count.restrict {s | s.card = n}

/-- Finite-population mean. -/
def populationMean {N : ℕ} (y : Fin N → ℝ) : ℝ := (∑ i, y i) / N

/-- Finite-population variance with divisor `N-1`. -/
def populationVariance {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i - populationMean y) ^ 2) / (N - 1 : ℕ)

/-- A Latin square of order `s`: every symbol occurs exactly once in each row and in each
column. -/
def IsLatinSquare {s : ℕ} (L : Fin s → Fin s → Fin s) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i ↦ L i j)

/-- Two Latin squares are orthogonal when superposing them gives every ordered pair of symbols
exactly once. -/
def OrthogonalLatinSquares {s : ℕ} (L M : Fin s → Fin s → Fin s) : Prop :=
  Function.Injective (fun z : Fin s × Fin s ↦ (L z.1 z.2, M z.1 z.2))


end CKSD
