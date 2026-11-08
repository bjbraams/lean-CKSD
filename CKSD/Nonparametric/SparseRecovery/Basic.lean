module

public import CKSD.Nonparametric.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Sparse vectors, the null space property, and restricted orthogonality

Coordinate `ℓ¹` norms on sets of coordinates, basis pursuit, and the null space property, with
the polarization estimate that turns the restricted isometry property into restricted
orthogonality of sparse vectors with disjoint supports.

## Main definitions

* `CKSD.HasNullspaceProperty A S`: every nonzero `δ` in the kernel of `A` has
  `‖δ_S‖₁ < ‖δ_{Sᶜ}‖₁`.
* `CKSD.IsBasisPursuitEstimator A y η β`: `β` minimizes `‖b‖₁` subject to `‖A b - y‖ ≤ η`.

## Main results

* `CKSD.hasNullspaceProperty_iff`: the null space property on `S` holds if and only if basis
  pursuit recovers every vector supported in `S` as the unique `ℓ¹` minimizer of its
  measurements.
* `CKSD.abs_inner_apply_le_of_hasRestrictedIsometry`: if `A` has the restricted isometry
  property of order `2 s` with constant `δ`, then `|⟪A x, A y⟫| ≤ δ ‖x‖ ‖y‖` for `s`-sparse `x`,
  `y` with disjoint supports.

Sources: GAPS 103.48 and 103.49.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The coordinatewise L1 norm splits over complementary coordinate sets. -/
theorem restrictedL1Norm_add_compl {p : ℕ} (S : Finset (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x + restrictedL1Norm Sᶜ x = restrictedL1Norm Finset.univ x := by
  exact S.sum_add_sum_compl (fun j ↦ |x j|)

/-- A restricted reverse triangle bound for coordinatewise L1 norms. -/
theorem restrictedL1Norm_le_add_sub {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x ≤ restrictedL1Norm S y + restrictedL1Norm S (y - x) := by
  unfold restrictedL1Norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  change |x j| ≤ |y j| + |y j - x j|
  calc
    |x j| = |y j + (x j - y j)| := by congr 1; ring
    _ ≤ |y j| + |x j - y j| := abs_add_le _ _
    _ = |y j| + |y j - x j| := by rw [abs_sub_comm]

/-- The null space property of `A` on the coordinate set `S`: every nonzero vector `δ` in the
kernel of `A` has `‖δ_S‖₁ < ‖δ_{Sᶜ}‖₁`. -/
def HasNullspaceProperty {n p : ℕ} (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) : Prop :=
  ∀ δ, A δ = 0 → δ ≠ 0 → restrictedL1Norm S δ < restrictedL1Norm Sᶜ δ

/-- `β` is a basis pursuit estimate with residual bound `η`: it minimizes `‖b‖₁` over all `b`
with `‖A b - y‖ ≤ η`. -/
def IsBasisPursuitEstimator {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (η : ℝ) (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ‖A β - y‖ ≤ η ∧ ∀ b, ‖A b - y‖ ≤ η →
    restrictedL1Norm Finset.univ β ≤ restrictedL1Norm Finset.univ b

/-- GAPS 103.48: the null space property on `S` holds if and only if every `β` supported in `S`
is the unique minimizer of `‖b‖₁` subject to `A b = A β`. -/
theorem hasNullspaceProperty_iff {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) :
    HasNullspaceProperty A S ↔
    ∀ β, (∀ j ∉ S, β j = 0) → ∀ b, A b = A β → b ≠ β →
      restrictedL1Norm Finset.univ β < restrictedL1Norm Finset.univ b := by
  constructor
  · intro hnsp β hβ b hab hne
    have hnull : A (b - β) = 0 := by rw [map_sub, hab, sub_self]
    have hstrict := hnsp (b - β) hnull (sub_ne_zero.mpr hne)
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hβ j (Finset.mem_compl.mp hj), abs_zero]
    have hcomp : restrictedL1Norm Sᶜ (b - β) = restrictedL1Norm Sᶜ b := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [PiLp.sub_apply, hβ j (Finset.mem_compl.mp hj), sub_zero]
    have htriangle := restrictedL1Norm_le_add_sub S β b
    have hsplitβ := restrictedL1Norm_add_compl S β
    have hsplitb := restrictedL1Norm_add_compl S b
    rw [hβc, add_zero] at hsplitβ
    rw [hcomp] at hstrict
    linarith
  · intro hunique δ hnull hne
    let β : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (fun j ↦ if j ∈ S then δ j else 0)
    let b := β - δ
    have hβ : ∀ j ∉ S, β j = 0 := by
      intro j hj
      simp [β, hj]
    have hab : A b = A β := by
      change A (β - δ) = A β
      rw [map_sub, hnull, sub_zero]
    have hbne : b ≠ β := by
      intro h
      change β - δ = β at h
      exact hne (sub_eq_self.mp h)
    have hlt := hunique β hβ b hab hbne
    have hβs : restrictedL1Norm S β = restrictedL1Norm S δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [β, hj]
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [β, Finset.mem_compl.mp hj]
    have hbs : restrictedL1Norm S b = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [b, β, PiLp.sub_apply, hj]
    have hbc : restrictedL1Norm Sᶜ b = restrictedL1Norm Sᶜ δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [b, β, PiLp.sub_apply, Finset.mem_compl.mp hj]
    rw [← restrictedL1Norm_add_compl S β, ← restrictedL1Norm_add_compl S b,
      hβs, hβc, hbs, hbc, add_zero, zero_add] at hlt
    exact hlt

/-- The support of `a • x + b • y` has at most `2 s` elements when `x` and `y` are
`s`-sparse. -/
theorem sparsity_smul_add_smul_le {p s : ℕ} (x y : EuclideanSpace ℝ (Fin p)) (a b : ℝ)
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) : sparsity (a • x + b • y) ≤ 2 * s := by
  classical
  unfold sparsity at *
  calc (Finset.univ.filter fun j ↦ (a • x + b • y) j ≠ 0).card
      ≤ ((Finset.univ.filter fun j ↦ x j ≠ 0) ∪ (Finset.univ.filter fun j ↦ y j ≠ 0)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
        by_contra h
        push Not at h
        apply hj
        simp [h.1, h.2]
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 * s := by omega

/-- Vectors with disjoint supports are orthogonal. -/
theorem inner_eq_zero_of_forall_eq_zero_or_eq_zero {p : ℕ} {x y : EuclideanSpace ℝ (Fin p)}
    (hxy : ∀ j, x j = 0 ∨ y j = 0) : ⟪x, y⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rcases hxy j with h | h <;> simp [h]

/-- Restricted orthogonality from the restricted isometry property: for `s`-sparse vectors
with disjoint supports, `|⟪A x, A y⟫| ≤ δ ‖x‖ ‖y‖` when `A` has the RIP of order `2 s`. -/
theorem abs_inner_apply_le_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (hrip : HasRestrictedIsometry A (2 * s) δ) (x y : EuclideanSpace ℝ (Fin p))
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) (hxy : ∀ j, x j = 0 ∨ y j = 0) :
    |⟪A x, A y⟫| ≤ δ * ‖x‖ * ‖y‖ := by
  have hinner : ⟪x, y⟫ = 0 := inner_eq_zero_of_forall_eq_zero_or_eq_zero hxy
  rcases (norm_nonneg x).eq_or_lt with hx0 | hx0
  · rw [eq_comm, norm_eq_zero] at hx0; simp [hx0]
  rcases (norm_nonneg y).eq_or_lt with hy0 | hy0
  · rw [eq_comm, norm_eq_zero] at hy0; simp [hy0]
  set α := Real.sqrt ‖x‖
  set β := Real.sqrt ‖y‖
  have hα : 0 < α := Real.sqrt_pos.mpr hx0
  have hβ : 0 < β := Real.sqrt_pos.mpr hy0
  have hα2 : α ^ 2 = ‖x‖ := Real.sq_sqrt hx0.le
  have hβ2 : β ^ 2 = ‖y‖ := Real.sq_sqrt hy0.le
  set a := β / α
  set b := α / β
  have hab : a * b = 1 := by
    simp only [a, b]; field_simp
  have h1 := (hrip (a • x + b • y) (sparsity_smul_add_smul_le x y a b hx hy)).2
  have h2 := (hrip (a • x + (-b) • y) (sparsity_smul_add_smul_le x y a (-b) hx hy)).1
  have h3 := (hrip (a • x + b • y) (sparsity_smul_add_smul_le x y a b hx hy)).1
  have h4 := (hrip (a • x + (-b) • y) (sparsity_smul_add_smul_le x y a (-b) hx hy)).2
  simp only [map_add, map_smul, norm_add_sq_real, inner_smul_left, inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hinner, RCLike.conj_to_real] at h1 h2 h3 h4
  have ha2 : a ^ 2 * ‖x‖ ^ 2 = ‖x‖ * ‖y‖ := by
    simp only [a]; rw [div_pow, hβ2, ← hα2]; field_simp
  have hb2 : b ^ 2 * ‖y‖ ^ 2 = ‖x‖ * ‖y‖ := by
    simp only [b]; rw [div_pow, hα2, ← hβ2]; field_simp
  have e : a * (b * ⟪A x, A y⟫) = ⟪A x, A y⟫ := by rw [← mul_assoc, hab, one_mul]
  have key : 4 * ⟪A x, A y⟫ ≤ 2 * δ * (a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2) := by
    nlinarith
  have key' : -(4 * ⟪A x, A y⟫) ≤ 2 * δ * (a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2) := by
    nlinarith
  rw [ha2, hb2] at key key'
  rw [abs_le]
  constructor <;> nlinarith

end CKSD
