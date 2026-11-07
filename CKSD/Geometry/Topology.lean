module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic

/-!
# Geometry: Topology

Sources: `GAPS.md`, `SYNOPSIS108.md`, and `STRUCTURE108.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 108.21, the Euclidean Čech/Rips inclusions, in the diameter-`2r` convention. -/
theorem cech_rips_inclusions {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (r : ℝ) (hr : 0 ≤ r) :
    ((∃ c, ∀ x ∈ S, dist x c ≤ r) → ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) ∧
      ((∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) →
        ∃ c, ∀ x ∈ S, dist x c ≤ Real.sqrt 2 * r) := by
  sorry

/-- GAPS 108.24: stability of distance to a measure. -/
theorem abs_distanceToMeasure_sub_le_wasserstein {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 2 P) (hQ : MemLp id 2 Q) (m : ℝ) (hm : m ∈ Ioc 0 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    |distanceToMeasure P m x - distanceToMeasure Q m x| ≤
      (TauCeti.wassersteinEDist 2 P Q).toReal / Real.sqrt m := by
  sorry


end CKSD
