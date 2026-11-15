module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reach and weak feature size

Feature sizes of subsets of `ℝ^D` defined through the distance function `x ↦ d(x, S)`. The reach
of a set is the supremum of the radii `r` such that every point at distance less than `r` has a
unique nearest point in the set. A critical point of the distance function to `K` is a point
outside `K` lying in the convex hull of its nearest points, and the weak feature size is the
infimum of the positive critical values.

## Main definitions

* `CKSD.reach`: the reach of a set.
* `CKSD.IsDistanceCriticalPoint`, `CKSD.weakFeatureSize`: critical points of the distance function
  and the weak feature size.
-/

public section

noncomputable section

open Set Metric
open scoped ENNReal NNReal

namespace CKSD

variable {D : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The reach of a set: the supremum of the radii `r` such that every point at distance less than
`r` from the set has a unique nearest point in it. -/
def reach (S : Set E) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : ∀ x, infDist x S < r → ∃! y, y ∈ S ∧ dist x y = infDist x S), (r : ℝ≥0∞)

/-- A point outside `K` is critical for the distance function to `K` when it lies in the convex
hull of its nearest points in `K`. -/
def IsDistanceCriticalPoint (K : Set E) (x : E) : Prop :=
  x ∉ K ∧ x ∈ convexHull ℝ {y | y ∈ K ∧ dist x y = infDist x K}

/-- The weak feature size: the infimum of the positive critical values of the distance function,
`∞` when there are none. -/
def weakFeatureSize (K : Set E) : ℝ≥0∞ :=
  ⨅ (x : E) (_ : IsDistanceCriticalPoint K x) (_ : 0 < infDist x K), ENNReal.ofReal (infDist x K)

end CKSD
