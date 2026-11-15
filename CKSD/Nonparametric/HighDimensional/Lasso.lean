module

public import CKSD.Nonparametric.Models
import CKSD.Nonparametric.SparseRecovery.Basic

/-!
# Deterministic analysis of the lasso

For a lasso estimate (`CKSD.IsLassoEstimator`, with the `1/(2n)` squared-error normalization)
on the noise event `|⟪ε, A δ⟫| / n ≤ λ ‖δ‖₁ / 2`.

## Main results

* `CKSD.restrictedL1Norm_sub_smul_sub_le`: convexity of the coordinate `ℓ¹` norm along
  segments.
* `CKSD.IsLassoEstimator.norm_apply_sub_sq_div_le`: the basic inequality of the lasso, with the
  cone condition `CKSD.IsLassoEstimator.restrictedL1Norm_compl_sub_le`.
* `CKSD.IsLassoEstimator.norm_apply_sub_sq_div_le_of_hasCompatibility`,
  `CKSD.IsLassoEstimator.restrictedL1Norm_sub_le`: the prediction and `ℓ¹` error bounds under
  compatibility.

Source: GAPS 103.34.

## References

* S. van de Geer, *Estimation and Testing Under Sparsity*, Lecture Notes in Mathematics, Springer,
  2016.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
  Press, 2019, Theorem 7.13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The coordinate `ℓ¹` norm is convex along segments:
`‖x - h (x - y)‖₁ ≤ (1 - h) ‖x‖₁ + h ‖y‖₁` for `0 ≤ h ≤ 1`. -/
theorem restrictedL1Norm_sub_smul_sub_le {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    restrictedL1Norm S (x - h • (x - y)) ≤
      (1 - h) * restrictedL1Norm S x + h * restrictedL1Norm S y := by
  simp only [restrictedL1Norm_def]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have : (x - h • (x - y)) j = (1 - h) * x j + h * y j := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this]
  calc |(1 - h) * x j + h * y j| ≤ |(1 - h) * x j| + |h * y j| := abs_add_le _ _
    _ = (1 - h) * |x j| + h * |y j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]

/-- The basic inequality of the lasso. Let `y = A β + ε` with `β` supported in `S`, and let `b`
be a lasso estimate with penalty `λ > 0` on the noise event `|⟪ε, A δ⟫| / n ≤ λ ‖δ‖₁ / 2`.
Then `‖A (b - β)‖² / n ≤ (3λ/2) ‖(b - β)_S‖₁ - (λ/2) ‖(b - β)_{Sᶜ}‖₁`. -/
theorem IsLassoEstimator.norm_apply_sub_sq_div_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda)
    (S : Finset (Fin p)) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ) :
    ‖A (b - β)‖ ^ 2 / n ≤
      3 * lambda / 2 * restrictedL1Norm S (b - β) - lambda / 2 * restrictedL1Norm Sᶜ (b - β) := by
  have hmin : ∀ t, ‖A β + ε - A b‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b ≤
      ‖A β + ε - A t‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ t := fun t ↦ by
    simpa only [lassoObjective_def] using hb t
  set δ := b - β with hδ
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set u' := ‖A δ‖ ^ 2 with hu'
  set e := inner ℝ ε (A δ) with he
  -- first-order condition of the lasso along the segment towards `β`
  have hvar : ∀ h : ℝ, 0 < h → h ≤ 1 →
      u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
        restrictedL1Norm Finset.univ b) + h * u' / (2 * n) := by
    intro h h0 h1
    have hm := hmin (b - h • δ)
    have hr : A β + ε - A b = ε - A δ := by rw [hδ, map_sub]; abel
    have hr' : A β + ε - A (b - h • δ) = (ε - A δ) + h • A δ := by
      rw [map_sub, map_smul, hδ, map_sub]; abel
    rw [hr, hr', norm_add_sq_real, norm_smul, inner_smul_right, inner_sub_left,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos h0] at hm
    have hl1 := restrictedL1Norm_sub_smul_sub_le Finset.univ b β h h0.le h1
    rw [← hδ] at hl1
    have key : 0 ≤ h * ((e - u') / n + h * u' / (2 * n) +
        lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) := by
      have : h * ((e - u') / n + h * u' / (2 * n) +
          lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) =
          ((‖ε - A δ‖ ^ 2 + 2 * (h * (e - u')) + (h * ‖A δ‖) ^ 2) / (2 * n) +
            lambda * ((1 - h) * restrictedL1Norm Finset.univ b +
              h * restrictedL1Norm Finset.univ β)) -
          (‖ε - A δ‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b) := by
        rw [hu']; field_simp; ring
      rw [this, sub_nonneg]
      refine hm.trans ?_
      gcongr
    have := (mul_nonneg_iff_of_pos_left h0).mp key
    have h2 : (e - u') / n = e / n - u' / n := by ring
    linarith
  have hvar' : u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b) := by
    by_contra hcon
    rw [not_le] at hcon
    set gapv := u' / n - (e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b)) with hgap
    have hgpos : 0 < gapv := by linarith
    have hc : 0 ≤ u' / (2 * n) := by positivity
    set h := min 1 (gapv / (2 * (u' / (2 * n) + 1))) with hh
    have hpos : 0 < h := lt_min one_pos (by positivity)
    have hle : h ≤ 1 := min_le_left _ _
    have hle2 : h ≤ gapv / (2 * (u' / (2 * n) + 1)) := min_le_right _ _
    have := hvar h hpos hle
    have hmul : h * (u' / (2 * n)) ≤ gapv / 2 := by
      calc h * (u' / (2 * n)) ≤ gapv / (2 * (u' / (2 * n) + 1)) * (u' / (2 * n) + 1) := by
            apply mul_le_mul hle2 (by linarith) hc (by positivity)
        _ = gapv / 2 := by
            have hgen : ∀ g q : ℝ, q ≠ 0 → g / (2 * q) * q = g / 2 := by
              intro g q hq; field_simp
            exact hgen _ _ (by positivity)
    have : h * u' / (2 * n) = h * (u' / (2 * n)) := by ring
    linarith
  -- split the `L1` norms over `S` and its complement
  have hβc : restrictedL1Norm Sᶜ β = 0 := by
    simp only [restrictedL1Norm_def]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsupp j (Finset.mem_compl.mp hj), abs_zero]
  have hcomp : restrictedL1Norm Sᶜ δ = restrictedL1Norm Sᶜ b := by
    simp only [restrictedL1Norm_def]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hδ, PiLp.sub_apply, hsupp j (Finset.mem_compl.mp hj), sub_zero]
  have htri := restrictedL1Norm_le_add_sub S β b
  have hsβ := restrictedL1Norm_add_compl S β
  have hsb := restrictedL1Norm_add_compl S b
  have hsδ := restrictedL1Norm_add_compl S δ
  have hnz := hnoise δ
  have habs := neg_abs_le e
  have habs' := le_abs_self e
  set a := restrictedL1Norm S δ
  set c := restrictedL1Norm Sᶜ δ
  have ha0 : 0 ≤ a := restrictedL1Norm_nonneg _ _
  have hc0 : 0 ≤ c := restrictedL1Norm_nonneg _ _
  have he' : e / n ≤ |e| / n := div_le_div_of_nonneg_right habs' hN.le
  have hu0 : 0 ≤ u' / n := by positivity
  -- the main inequality `u ≤ (3λ/2) a - (λ/2) c`
  have hmain : u' / n ≤ 3 * lambda / 2 * a - lambda / 2 * c := by
    rw [← hsδ] at hnz
    nlinarith
  exact hmain

/-- GAPS 103.34: the cone condition for the lasso. Under the noise event
`|⟪ε, A δ⟫| / n ≤ λ ‖δ‖₁ / 2`, the error `δ = b - β` of a lasso estimate satisfies
`‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, where `S` contains the support of `β`. -/
theorem IsLassoEstimator.restrictedL1Norm_compl_sub_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda)
    (S : Finset (Fin p)) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ) :
    restrictedL1Norm Sᶜ (b - β) ≤ 3 * restrictedL1Norm S (b - β) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have hu0 : 0 ≤ ‖A (b - β)‖ ^ 2 / n := by positivity
  nlinarith

/-- Under the compatibility condition, the lasso error has `‖δ_S‖₁ ≤ 3 λ |S| / (2 κ²)`. -/
private theorem IsLassoEstimator.restrictedL1Norm_sub_le_aux {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    restrictedL1Norm S (b - β) ≤ 3 * lambda * S.card / (2 * κ ^ 2) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have hcone := hb.restrictedL1Norm_compl_sub_le hn hlambda S hsupp hnoise
  set a := restrictedL1Norm S (b - β)
  set c := restrictedL1Norm Sᶜ (b - β)
  set u := ‖A (b - β)‖ ^ 2 / n with hu
  have ha0 : 0 ≤ a := restrictedL1Norm_nonneg _ _
  have hc0 : 0 ≤ c := restrictedL1Norm_nonneg _ _
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hcomp : κ ^ 2 * a ^ 2 ≤ S.card * u := by
    calc κ ^ 2 * a ^ 2 ≤ (S.card : ℝ) * ‖A (b - β)‖ ^ 2 / n := hcompat (b - β) hcone
      _ = _ := by rw [hu]; ring
  have hka : κ ^ 2 * a ≤ 3 * lambda * S.card / 2 := by
    rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · have : κ ^ 2 * a ^ 2 ≤ S.card * (3 * lambda / 2 * a) := by
        calc κ ^ 2 * a ^ 2 ≤ S.card * u := hcomp
          _ ≤ S.card * (3 * lambda / 2 * a) := by
            apply mul_le_mul_of_nonneg_left _ hs.le; nlinarith
      nlinarith
  rw [le_div_iff₀ (by positivity)]; nlinarith

/-- GAPS 103.34: the lasso prediction bound under compatibility. Under the noise event and the
compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, a lasso estimate
satisfies `‖A (b - β)‖² / n ≤ 9 λ² |S| / (4 κ²)`. -/
theorem IsLassoEstimator.norm_apply_sub_sq_div_le_of_hasCompatibility {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    ‖A (b - β)‖ ^ 2 / n ≤ 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have ha := hb.restrictedL1Norm_sub_le_aux hn hlambda hκ S hne hsupp hnoise hcompat
  have hc0 : 0 ≤ restrictedL1Norm Sᶜ (b - β) := restrictedL1Norm_nonneg _ _
  calc ‖A (b - β)‖ ^ 2 / n ≤ 3 * lambda / 2 * restrictedL1Norm S (b - β) := by nlinarith
    _ ≤ 3 * lambda / 2 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
    _ = 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) := by field_simp; ring

/-- GAPS 103.34: the lasso `ℓ¹` error bound under compatibility. Under the noise event and the
compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, a lasso estimate
satisfies `‖b - β‖₁ ≤ 6 λ |S| / κ²`. -/
theorem IsLassoEstimator.restrictedL1Norm_sub_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    restrictedL1Norm Finset.univ (b - β) ≤ 6 * lambda * S.card / κ ^ 2 := by
  have hcone := hb.restrictedL1Norm_compl_sub_le hn hlambda S hsupp hnoise
  have ha := hb.restrictedL1Norm_sub_le_aux hn hlambda hκ S hne hsupp hnoise hcompat
  rw [← restrictedL1Norm_add_compl S (b - β)]
  calc restrictedL1Norm S (b - β) + restrictedL1Norm Sᶜ (b - β)
      ≤ 4 * restrictedL1Norm S (b - β) := by linarith
    _ ≤ 4 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
    _ = 6 * lambda * S.card / κ ^ 2 := by field_simp; ring

end CKSD
