module

public import CKSD.Asymptotics.Basic

/-!
# Nonparametric: definitions

Sources: `GAPS.md`, `SYNOPSIS103.md`, and `STRUCTURE103.md`.
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

/-- Discrete measurable structure for finite permutations. -/
scoped instance rankMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Total variation in the statistical convention. -/
def totalVariationDistance {X : Type*} [MeasurableSpace X] (P Q : Measure X) : ℝ :=
  sSup {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |P.real A - Q.real A|}

/-- Kolmogorov–Smirnov discrepancy, using a countable determining set. -/
def kolmogorovSmirnovStatistic {Ω : Type*} (X : ℕ → Ω → ℝ) (P : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sSup (range fun t : ℚ ↦ |empiricalCDF X n ω t - cdf P t|)

/-- Kernel density estimator in one dimension. -/
def kernelDensityEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, K ((t - X i ω) / h n)) / ((n : ℝ) * h n)

/-- Coordinatewise L1 norm restricted to a set of coordinates. -/
def restrictedL1Norm {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j ∈ S, |x j|

/-- Support size of a finite-dimensional vector. -/
def sparsity {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) : ℕ :=
  (Finset.univ.filter fun j ↦ x j ≠ 0).card

/-- The best `s`-term L1 approximation error. -/
def bestSparseL1Error {p : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⨅ y : {y : EuclideanSpace ℝ (Fin p) // sparsity y ≤ s}, restrictedL1Norm Finset.univ (x - y.val)

/-- A restricted-isometry bound, expressed without taking an infimum over constants. -/
def HasRestrictedIsometry {p n : ℕ} (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, sparsity x ≤ s →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- Benjamini–Hochberg rejection count, including the zero-rejection case. -/
def benjaminiHochbergCount {m : ℕ} (p : Fin m → ℝ) (α : ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ ↦
    k ≤ (Finset.univ.filter fun i ↦ p i ≤ (k : ℝ) * α / m).card).sup id


end CKSD
