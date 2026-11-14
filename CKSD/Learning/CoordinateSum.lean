module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.DependsOn

/-!
# Partial sums over coordinates of finite configurations

For finite types `V` and `S`, a configuration is a function `x : V → S`. Summing a function of
configurations over the coordinates in a finite set `D ⊆ V`, with the remaining coordinates
frozen at their values in `x`, is the finite analogue of Mathlib's marginal integral
`∫⋯∫⁻_D, f ∂μ` (`MeasureTheory.lmarginal`) for counting measures, with values in an arbitrary
additive commutative monoid. Dependence of a function of configurations on a set of coordinates
is expressed with Mathlib's `DependsOn`.

## Main definitions

* `CKSD.coordSum`: the sum of `f` over the configurations that agree with `x` off `D`.

## Main results

* `CKSD.coordSum_empty`, `CKSD.coordSum_singleton`: summing over no coordinates and over one
  coordinate.
* `CKSD.coordSum_union`: Fubini for disjoint coordinate sets.
* `CKSD.coordSum_mul_left`, `CKSD.coordSum_mul_right`: factors that do not depend on the summed
  coordinates come out of the sum.
* `CKSD.dependsOn_coordSum`: a partial sum over `D` does not depend on the coordinates in `D`.
* `CKSD.coordSum_biUnion_prod`: a product of factors on disjoint blocks of coordinates sums
  blockwise.
-/

@[expose] public section

noncomputable section

open Finset

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S M R : Type*} [Fintype V] [Fintype S]

section AddCommMonoid

variable [AddCommMonoid M]

/-- Sum of a function of configurations over the coordinates in `D`, the coordinates outside
`D` being frozen at their values in `x`. -/
def coordSum (D : Finset V) (f : (V → S) → M) (x : V → S) : M :=
  ∑ x' ∈ univ.filter (fun x' : V → S ↦ ∀ v ∉ D, x' v = x v), f x'

/-- Summing over no coordinates is evaluation. -/
@[simp]
theorem coordSum_empty (f : (V → S) → M) (x : V → S) : coordSum ∅ f x = f x := by
  unfold coordSum
  rw [Finset.sum_eq_single_of_mem x (by simp)]
  intro x' hx' hne
  exact absurd (funext fun v ↦ (Finset.mem_filter.mp hx').2 v (Finset.notMem_empty v)) hne

/-- `coordSum D f x` only sees values of `f` at configurations agreeing with `x` off `D`. -/
theorem coordSum_congr {D : Finset V} {f g : (V → S) → M} {x : V → S}
    (h : ∀ x', (∀ v ∉ D, x' v = x v) → f x' = g x') : coordSum D f x = coordSum D g x :=
  Finset.sum_congr rfl fun x' hx' ↦ h x' (Finset.mem_filter.mp hx').2

/-- Summing over disjoint coordinate sets in two stages (Fubini for finite sums). -/
theorem coordSum_union {D E : Finset V} (hDE : Disjoint D E) (f : (V → S) → M)
    (x : V → S) : coordSum (D ∪ E) f x = coordSum D (fun y ↦ coordSum E f y) x := by
  unfold coordSum
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij' (fun p _ ↦ p.2) (fun y _ ↦ ⟨fun v ↦ if v ∈ D then y v else x v, y⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x', x''⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [hp.2 v hv.2, hp.1 v hv.1]
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨fun v hv ↦ by simp [hv], fun v hv ↦ ?_⟩
    by_cases hvD : v ∈ D
    · simp [hvD]
    · rw [ite_eq_right hvD]
      exact hy v (by simp [hvD, hv])
  · rintro ⟨x', x''⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    funext v
    by_cases hvD : v ∈ D
    · rw [ite_eq_left hvD]
      exact hp.2 v (Finset.disjoint_left.mp hDE hvD)
    · rw [ite_eq_right hvD]
      exact (hp.1 v hvD).symm
  · intro y _
    rfl
  · intro p _
    rfl

/-- Summing over one coordinate. -/
theorem coordSum_singleton (i : V) (f : (V → S) → M) (x : V → S) :
    coordSum {i} f x = ∑ a : S, f (Function.update x i a) := by
  unfold coordSum
  refine Finset.sum_nbij' (fun z ↦ z i) (fun a ↦ Function.update x i a) ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_univ _
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    intro v hv
    exact Function.update_of_ne hv _ _
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hz
    funext v
    by_cases hv : v = i
    · subst hv; simp
    · rw [Function.update_of_ne hv]; exact (hz v hv).symm
  · intro a _; simp
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz
    congr 1
    funext v
    by_cases hv : v = i
    · subst hv; simp
    · rw [Function.update_of_ne hv]; exact hz v hv

/-- If `f` depends only on the coordinates in `s`, then its partial sum over `D` depends only on
the coordinates in `s \ D`. -/
theorem dependsOn_coordSum {D : Finset V} {s : Set V} {f : (V → S) → M} (hf : DependsOn f s) :
    DependsOn (coordSum D f) (s \ (D : Set V)) := by
  intro y y' hy
  unfold coordSum
  refine Finset.sum_nbij' (fun z ↦ fun v ↦ if v ∈ D then z v else y' v)
    (fun z ↦ fun v ↦ if v ∈ D then z v else y v) ?_ ?_ ?_ ?_ ?_
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro v hv; simp [hv]
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro v hv; simp [hv]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext v
    by_cases hv : v ∈ D
    · simp [hv]
    · rw [ite_eq_right hv]; exact (hz v hv).symm
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    funext v
    by_cases hv : v ∈ D
    · simp [hv]
    · rw [ite_eq_right hv]; exact (hz v hv).symm
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine hf fun v hvs ↦ ?_
    by_cases hv : v ∈ D
    · simp [hv]
    · rw [ite_eq_right hv, hz v hv]
      exact hy v ⟨hvs, hv⟩

end AddCommMonoid

section Semiring

variable [NonUnitalNonAssocSemiring R]

/-- A factor that does not depend on the coordinates in `D` comes out of `coordSum D` on the
left. -/
theorem coordSum_mul_left {D : Finset V} (g h : (V → S) → R) {x : V → S}
    (hg : ∀ x', (∀ v ∉ D, x' v = x v) → g x' = g x) :
    coordSum D (fun y ↦ g y * h y) x = g x * coordSum D h x := by
  unfold coordSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' hx' ↦ by
    show g x' * h x' = _
    rw [hg x' (Finset.mem_filter.mp hx').2]

/-- A factor that does not depend on the coordinates in `D` comes out of `coordSum D` on the
right. -/
theorem coordSum_mul_right {D : Finset V} (h g : (V → S) → R) {x : V → S}
    (hg : ∀ x', (∀ v ∉ D, x' v = x v) → g x' = g x) :
    coordSum D (fun y ↦ h y * g y) x = coordSum D h x * g x := by
  unfold coordSum
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x' hx' ↦ by
    show h x' * g x' = _
    rw [hg x' (Finset.mem_filter.mp hx').2]

end Semiring

/-- Summing a product of factors over a disjoint union of coordinate blocks, each factor not
depending on the blocks of the other factors, factorizes into the product of the blockwise
sums. -/
theorem coordSum_biUnion_prod [CommSemiring R] {ι : Type*} (K : Finset ι) (D : ι → Finset V)
    (f : ι → (V → S) → R) (hD : (K : Set ι).PairwiseDisjoint D)
    (hf : ∀ k ∈ K, DependsOn (f k) (↑((K.erase k).biUnion D))ᶜ) (x : V → S) :
    coordSum (K.biUnion D) (fun y ↦ ∏ k ∈ K, f k y) x = ∏ k ∈ K, coordSum (D k) (f k) x := by
  induction K using Finset.induction_on generalizing x with
  | empty => simp
  | @insert k K hk ih =>
    have hdisj : Disjoint (D k) (K.biUnion D) := by
      rw [Finset.disjoint_biUnion_right]
      intro l hl
      exact hD (by simp) (by simp [hl]) (fun h ↦ hk (h ▸ hl))
    have hD' : (K : Set ι).PairwiseDisjoint D := hD.subset (by simp)
    have hf' : ∀ l ∈ K, DependsOn (f l) (↑((K.erase l).biUnion D))ᶜ := fun l hl ↦
      (hf l (by simp [hl])).mono (Set.compl_subset_compl.mpr (Finset.coe_subset.mpr
        (Finset.biUnion_subset_biUnion_of_subset_left _
          (Finset.erase_subset_erase _ (Finset.subset_insert _ _)))))
    have hfk : DependsOn (f k) (↑(K.biUnion D))ᶜ := by
      have := hf k (by simp)
      rwa [Finset.erase_insert hk] at this
    rw [Finset.biUnion_insert, coordSum_union hdisj, Finset.prod_insert hk]
    simp_rw [Finset.prod_insert hk]
    rw [coordSum_congr (g := fun y ↦ f k y * ∏ l ∈ K, coordSum (D l) (f l) y) fun y _ ↦ by
      rw [coordSum_mul_left _ _ fun y' hy' ↦ hfk fun v hv ↦ hy' v hv, ih hD' hf' y]]
    rw [coordSum_mul_right _ _ fun y' hy' ↦ ?_]
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hlk : l ≠ k := fun h ↦ hk (h ▸ hl)
    have hign : DependsOn (f l) (↑(D k))ᶜ := (hf l (by simp [hl])).mono
      (Set.compl_subset_compl.mpr fun v hv ↦
        Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨k, by simp [hlk.symm], hv⟩))
    exact dependsOn_coordSum hign fun v hv ↦ hy' v hv.1

end CKSD
