module

public import CKSD.Geometry.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Persistence modules, diagrams, and landscapes

Persistence modules reuse Mathlib's functors to `ModuleCat`. Diagram distances below treat finite
birth and death coordinates; essential bars are a separate component of a full diagram. Index
sets retain multiplicities: two indices may carry the same point. Unmatched points are matched
to the diagonal at half their lifetime. The landscape is indexed from zero.

## Main definitions

* `CKSD.PersistenceModule`, `CKSD.IsPointwiseFiniteDimensional`, `CKSD.IsQTame`.
* `CKSD.PersistenceInterleaving`, `CKSD.interleavingEDist`: interleavings and the interleaving
  distance.
* `CKSD.FiniteDeathDiagram`, `CKSD.DiagramMatching`, `CKSD.bottleneckEDist`.
* `CKSD.persistenceTent`, `CKSD.persistenceLandscape`.
* `CKSD.IsCechSimplex`, `CKSD.IsRipsSimplex`.

## Main results

* `CKSD.IsCechSimplex.isRipsSimplex`: the first Čech/Rips inclusion (GAPS 108.21).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter CategoryTheory
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A real-indexed persistence module over a field is a functor to vector spaces. -/
abbrev PersistenceModule (K : Type*) [Field K] := ℝ ⥤ ModuleCat K

/-- A persistence module is pointwise finite-dimensional when every vector space is finite-
dimensional. -/
def IsPointwiseFiniteDimensional {K : Type*} [Field K] (V : PersistenceModule K) : Prop :=
  ∀ t : ℝ, Module.Finite K (V.obj t)

/-- A persistence module is q-tame when its structure maps across strict intervals have finite
rank. -/
def IsQTame {K : Type*} [Field K] (V : PersistenceModule K) : Prop :=
  ∀ s t : ℝ, ∀ h : s < t, Module.Finite K (LinearMap.range (V.map (homOfLE h.le)).hom)

/-- An interleaving, including naturality and both composition identities. -/
structure PersistenceInterleaving {K : Type*} [Field K]
    (U V : PersistenceModule K) (ε : ℝ) where
  /-- Nonnegative shift. -/
  nonneg : 0 ≤ ε
  /-- Forward comparison maps. -/
  forward : ∀ t, U.obj t →ₗ[K] V.obj (t + ε)
  /-- Backward comparison maps. -/
  backward : ∀ t, V.obj t →ₗ[K] U.obj (t + ε)
  /-- Naturality of the forward maps. -/
  forward_natural : ∀ s t (h : s ≤ t),
    (V.map (homOfLE (show s + ε ≤ t + ε by linarith))).hom.comp (forward s) =
      (forward t).comp (U.map (homOfLE h)).hom
  /-- Naturality of the backward maps. -/
  backward_natural : ∀ s t (h : s ≤ t),
    (U.map (homOfLE (show s + ε ≤ t + ε by linarith))).hom.comp (backward s) =
      (backward t).comp (V.map (homOfLE h)).hom
  /-- The first composite is the structure map over two shifts. -/
  backward_forward : ∀ t, (backward (t + ε)).comp (forward t) =
    (U.map (homOfLE (show t ≤ (t + ε) + ε by linarith [nonneg]))).hom
  /-- The second composite is the structure map over two shifts. -/
  forward_backward : ∀ t, (forward (t + ε)).comp (backward t) =
    (V.map (homOfLE (show t ≤ (t + ε) + ε by linarith [nonneg]))).hom

/-- Extended interleaving distance, with value infinity when no interleaving exists. -/
def interleavingEDist {K : Type*} [Field K] (U V : PersistenceModule K) : ℝ≥0∞ :=
  ⨅ ε : {ε : ℝ // Nonempty (PersistenceInterleaving U V ε)}, ENNReal.ofReal ε.val

/-- A persistence diagram's finite-death component, with multiplicity recorded by its index set. -/
structure FiniteDeathDiagram (ι : Type*) where
  /-- Birth coordinate. -/
  birth : ι → ℝ
  /-- Death coordinate. -/
  death : ι → ℝ
  /-- Strictly positive lifetimes. -/
  birth_lt_death : ∀ i, birth i < death i

/-- A partial matching: every point is matched to at most one point on the other side. -/
structure DiagramMatching (ι κ : Type*) where
  /-- Matched pairs. -/
  relates : ι → κ → Prop
  /-- Single-valued on the left. -/
  left_unique : ∀ i j k, relates i j → relates i k → j = k
  /-- Single-valued on the right. -/
  right_unique : ∀ i j k, relates i k → relates j k → i = j

/-- Cost of a partial matching, including the distance of unmatched points to the diagonal. -/
def DiagramMatching.cost {ι κ : Type*} (M : DiagramMatching ι κ)
    (D : FiniteDeathDiagram ι) (E : FiniteDeathDiagram κ) : ℝ≥0∞ :=
  max (⨆ i, if h : ∃ j, M.relates i j then
    ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
    else ENNReal.ofReal ((D.death i - D.birth i) / 2))
    (⨆ j, if h : ∃ i, M.relates i j then
      ENNReal.ofReal (max |D.birth h.choose - E.birth j| |D.death h.choose - E.death j|)
      else ENNReal.ofReal ((E.death j - E.birth j) / 2))

/-- Bottleneck distance on finite-death diagrams, allowing unmatched points on the diagonal. -/
def bottleneckEDist {ι κ : Type*} (D : FiniteDeathDiagram ι) (E : FiniteDeathDiagram κ) : ℝ≥0∞ :=
  ⨅ M : DiagramMatching ι κ, M.cost D E

/-- Tent function associated to one finite persistence interval. -/
def persistenceTent (birth death t : ℝ) : ℝ := max 0 (min (t - birth) (death - t))

/-- Persistence landscape: level `k` is the `(k+1)`st largest tent height.
The supremum over finite subsets avoids choosing an ordering of diagram points. -/
def persistenceLandscape {ι : Type*} (D : FiniteDeathDiagram ι) (k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ S : {S : Finset ι // S.card = k + 1},
    ⨅ i : S.val, ENNReal.ofReal (persistenceTent (D.birth i.val) (D.death i.val) t)

/-- A Čech simplex in an ambient metric space, with closed balls of radius `r`. -/
def IsCechSimplex {X : Type*} [PseudoMetricSpace X] (r : ℝ) (S : Finset X) : Prop :=
  ∃ c : X, ∀ x ∈ S, dist x c ≤ r

/-- A Rips simplex in the diameter-`2r` parameter convention. -/
def IsRipsSimplex {X : Type*} [PseudoMetricSpace X] (r : ℝ) (S : Finset X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r

/-- GAPS 108.21, the first Čech/Rips inclusion in every pseudometric space: a Čech simplex of
radius `r` is a Rips simplex of parameter `r`, since points within `r` of a common center are
within `2r` of each other. -/
theorem IsCechSimplex.isRipsSimplex {X : Type*} [PseudoMetricSpace X]
    {r : ℝ} {S : Finset X} (h : IsCechSimplex r S) : IsRipsSimplex r S := by
  obtain ⟨c, hc⟩ := h
  intro x hx y hy
  calc
    dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (hc x hx) (by simpa [dist_comm] using hc y hy)
    _ = 2 * r := by ring

/-- Čech simplices are closed under taking faces. -/
theorem IsCechSimplex.mono {X : Type*} [PseudoMetricSpace X] {r : ℝ}
    {S T : Finset X} (h : IsCechSimplex r S) (hTS : T ⊆ S) : IsCechSimplex r T := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x hx ↦ hc x (hTS hx)⟩

/-- Rips simplices are closed under taking faces. -/
theorem IsRipsSimplex.mono {X : Type*} [PseudoMetricSpace X] {r : ℝ}
    {S T : Finset X} (h : IsRipsSimplex r S) (hTS : T ⊆ S) : IsRipsSimplex r T :=
  fun x hx y hy ↦ h x (hTS hx) y (hTS hy)

/-- Persistence tents are nonnegative. -/
theorem persistenceTent_nonneg (b d t : ℝ) : 0 ≤ persistenceTent b d t := le_max_left _ _

end CKSD
