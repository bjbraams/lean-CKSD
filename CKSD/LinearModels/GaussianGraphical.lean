module

public import CKSD.LinearModels.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Gaussian graphical concentration models

The conditioning map contains exactly the coordinates other than a specified pair.
Graphs reuse Mathlib's `SimpleGraph`; concentration constraints use the inverse covariance.
Source: GAPS 105.26, Gaussian precision-matrix part. General Hammersley–Clifford and the
intersection property for arbitrary positive densities are not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace CKSD

/-- All coordinates except two selected indices. -/
def otherCoordinates {p : ℕ} (i j : Fin p) (x : EuclideanSpace ℝ (Fin p)) :
    {k : Fin p // k ≠ i ∧ k ≠ j} → ℝ := fun k ↦ x k.val

/-- The coordinate conditioning map is measurable. -/
@[fun_prop] theorem measurable_otherCoordinates {p : ℕ} (i j : Fin p) :
    Measurable (otherCoordinates i j) := by
  unfold otherCoordinates
  fun_prop

/-- A nondegenerate Gaussian covariance belongs to a concentration graph if missing edges
correspond to zero entries of its precision matrix. -/
def IsGaussianConcentrationModel {p : ℕ} (G : SimpleGraph (Fin p))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Sigma.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → Sigma⁻¹ i j = 0

/-- Gaussian pairwise Markov property relative to an undirected graph. -/
def HasGaussianPairwiseMarkovProperty {p : ℕ} (G : SimpleGraph (Fin p))
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬ G.Adj i j →
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : Fin p // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_otherCoordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma)

/-- GAPS 105.26: a missing precision entry is equivalent to conditional independence of the
corresponding Gaussian coordinates given all remaining coordinates. -/
theorem gaussian_condIndepFun_iff_precision_eq_zero {p : ℕ}
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hSigma : Sigma.PosDef) (i j : Fin p) (hij : i ≠ j) :
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : Fin p // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_otherCoordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma) ↔ Sigma⁻¹ i j = 0 := by
  sorry

end CKSD
