module

public import CKSD.Inference.Basic
public import TauCeti.Probability.Distributions.Wishart.Basic

/-!
# LinearModels: definitions

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- Discrete measurable structure for finite samples. -/
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

/-- Uniform sampling of exactly `n` units from `N`. -/
def simpleRandomSampleDesign (N n : ℕ) : Measure (Finset (Fin N)) :=
  (Nat.choose N n : ℝ≥0∞)⁻¹ • Measure.count.restrict {s | s.card = n}

/-- Finite-population mean. -/
def populationMean {N : ℕ} (y : Fin N → ℝ) : ℝ := (∑ i, y i) / N

/-- Finite-population variance with divisor `N-1`. -/
def populationVariance {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i - populationMean y) ^ 2) / (N - 1 : ℕ)

/-- A Latin square on `Fin s`. -/
def IsLatinSquare {s : ℕ} (L : Fin s → Fin s → Fin s) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i ↦ L i j)

/-- Orthogonality of two Latin squares. -/
def OrthogonalLatinSquares {s : ℕ} (L M : Fin s → Fin s → Fin s) : Prop :=
  Function.Injective (fun z : Fin s × Fin s ↦ (L z.1 z.2, M z.1 z.2))


end CKSD
