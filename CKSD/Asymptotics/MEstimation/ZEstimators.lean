module

import CKSD.Asymptotics.LikelihoodSupport
public import CKSD.Inference.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.MEstimation.LipschitzChaining

/-!
# Lipschitz empirical processes and Z-estimator normality

For a scalar parameter family with a square-integrable Lipschitz envelope, the centred empirical
process evaluated at a consistent random parameter is stochastically equicontinuous. This yields
the asymptotically linear expansion and normal limit of a consistent approximate
estimating-equation root.

## Main results

* `CKSD.tendstoInMeasure_centredSum_sub_of_lipschitz`: stochastic equicontinuity at a consistent
  random parameter.
* `CKSD.zEstimator_asymptotic_linearization_and_normality`: GAPS 102.4.

Sources: GAPS 102.4 and van der Vaart, *Asymptotic Statistics*, Theorem 5.21. The stochastic
equicontinuity is the case `d = 1` of the maximal inequality
`CKSD.measureReal_exists_abs_empiricalProcess_sub_gt_le_four_mul` of
`CKSD.Asymptotics.MEstimation.LipschitzChaining`; the argument also uses the convergence adapters
in `CKSD.Asymptotics.Basic`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Square integrability of a parameter family with a square-integrable Lipschitz envelope, at
parameters within the Lipschitz radius. -/
theorem memLp_two_of_lipschitz_envelope {E : Type*} [MeasurableSpace E] (P : Measure E)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) :
    MemLp (fun x ↦ psi a x - psi b x) 2 P ∧ MemLp (psi a) 2 P ∧
      ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ (∫ x, M x ^ 2 ∂P) * (a - b) ^ 2 := by
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  have h0 : |theta₀ - theta₀| < r := by simpa using hr
  have hd : ∀ a b, |a - theta₀| < r → |b - theta₀| < r →
      MemLp (fun x ↦ psi a x - psi b x) 2 P := fun a b ha hb ↦ by
    refine (hM.const_mul |a - b|).of_le ((hmeas a).sub (hmeas b)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    have := hlip x a b ha hb
    have := le_abs_self (M x)
    nlinarith [abs_nonneg (a - b)]
  refine ⟨hd a b ha hb, ?_, ?_⟩
  · have := (hd a theta₀ ha h0).add hpsi
    convert this using 1
    ext x; simp
  · have hab := hd a b ha hb
    calc ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ ∫ x, M x ^ 2 * (a - b) ^ 2 ∂P := by
          refine integral_mono hab.integrable_sq (hM.integrable_sq.mul_const _) fun x ↦ ?_
          have h1 := hlip x a b ha hb
          have h2 : 0 ≤ |psi a x - psi b x| := abs_nonneg _
          have : (psi a x - psi b x) ^ 2 ≤ (M x * |a - b|) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ h2 h1 2
          simpa [mul_pow, sq_abs] using this
      _ = _ := integral_mul_const _ _

/-- Transport of a scalar Lipschitz family to `ℝ¹`. Let `ψ` be jointly measurable, integrable on
`|t - θ₀| < r`, and Lipschitz there with envelope `L ≥ 0` at every `x ∉ N`. For `δ < r`, the
family `θ ↦ 1_{Nᶜ} ψ_{θ 0}` on the cube `[θ₀ - δ, θ₀ + δ)` of `ℝ¹` consists of measurable
integrable functions, is Lipschitz with envelope `L`, and the cube contains the points within
`δ` of `θ₀`. -/
theorem lipschitz_indicator_comp_fin_one_halfOpenCube {E : Type*} [MeasurableSpace E]
    (P : Measure E) (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi))
    {theta₀ r δ : ℝ} (hδ : δ < r) (hint : ∀ t, |t - theta₀| < r → Integrable (psi t) P)
    {N : Set E} (hNm : MeasurableSet N) {L : E → ℝ} (hL0 : ∀ x, 0 ≤ L x)
    (hlip : ∀ x ∉ N, ∀ a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ L x * |a - b|) :
    (∀ t, |t - theta₀| < δ → (WithLp.toLp 2 fun _ : Fin 1 ↦ t) ∈
      halfOpenCube (WithLp.toLp 2 fun _ : Fin 1 ↦ theta₀ - δ) (2 * δ)) ∧
    (∀ θ ∈ halfOpenCube (WithLp.toLp 2 fun _ : Fin 1 ↦ theta₀ - δ) (2 * δ),
      Measurable (Nᶜ.indicator (psi (θ 0))) ∧ Integrable (Nᶜ.indicator (psi (θ 0))) P) ∧
    (∀ u ∈ halfOpenCube (WithLp.toLp 2 fun _ : Fin 1 ↦ theta₀ - δ) (2 * δ),
      ∀ v ∈ halfOpenCube (WithLp.toLp 2 fun _ : Fin 1 ↦ theta₀ - δ) (2 * δ), ∀ x,
        |Nᶜ.indicator (psi (u 0)) x - Nᶜ.indicator (psi (v 0)) x| ≤ L x * ‖u - v‖) := by
  have hcube : ∀ θ ∈ halfOpenCube (WithLp.toLp 2 fun _ : Fin 1 ↦ theta₀ - δ) (2 * δ),
      |θ 0 - theta₀| < r := fun θ hθ ↦ by
    obtain ⟨h1, h2⟩ := hθ 0
    rw [abs_lt]
    constructor <;> dsimp only at h1 h2 <;> linarith
  refine ⟨fun t ht i ↦ ?_, fun θ hθ ↦ ⟨?_, (hint _ (hcube θ hθ)).indicator hNm.compl⟩,
    fun u hu v hv x ↦ ?_⟩
  · rw [abs_lt] at ht
    dsimp only
    constructor <;> linarith
  · exact (hm.comp (measurable_const.prodMk measurable_id)).indicator hNm.compl
  · by_cases hx : x ∈ N
    · simp only [indicator_of_notMem (notMem_compl_iff.2 hx), sub_self, abs_zero]
      exact mul_nonneg (hL0 x) (norm_nonneg _)
    · simp only [indicator_of_mem (mem_compl hx)]
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
        Real.sqrt_sq_eq_abs, PiLp.sub_apply]
      exact hlip x hx _ _ (hcube u hu) (hcube v hv)

/-- Stochastic equicontinuity of the empirical process of a scalar parameter family with a
square-integrable Lipschitz envelope: evaluated at a consistent random parameter `Tₙ`, the
normalised centred partial-sum increment
`n ^ (-1/2) ∑ᵢ (ψ_{Tₙ} - ψ_{θ₀})(Xᵢ) - √n (P ψ_{Tₙ} - P ψ_{θ₀})`
tends to `0` in probability. The proof transports the family to `ℝ¹` and applies the maximal
inequality `measureReal_exists_abs_empiricalProcess_sub_gt_le_four_mul` on a small interval
around `θ₀`, after replacing `M` by a measurable envelope that agrees with it almost everywhere. -/
theorem tendstoInMeasure_centredSum_sub_of_lipschitz {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hcons : TendstoInMeasure μ T atTop (fun _ ↦ theta₀)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P)))
            atTop (fun _ ↦ 0) := by
  have hint : ∀ t, |t - theta₀| < r → Integrable (psi t) P := fun t ht ↦
    ((memLp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip t theta₀ ht
      (by simpa using hr)).2.1).integrable one_le_two
  obtain ⟨N, hNm, hN0, L, hLm, hL0, hL2, hLM⟩ := exists_measurable_nonneg_eq_of_memLp hM
    fun x ↦ nonneg_of_forall_abs_sub_le_mul_abs_sub (f := fun a ↦ psi a x) hr (hlip x)
  set f : EuclideanSpace ℝ (Fin 1) → E → ℝ := fun θ ↦ Nᶜ.indicator (psi (θ 0)) with hf
  set emb : ℝ → EuclideanSpace ℝ (Fin 1) := fun t ↦ WithLp.toLp 2 fun _ ↦ t with hemb
  rw [tendstoInMeasure_iff_measureReal_lt_dist] at hcons ⊢
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  -- Choice of the Bernstein level `A` and of the interval `[θ₀ - δ, θ₀ + δ)`.
  have hβ0 : 0 < ∫ x, L x ^ 2 ∂P + 1 := by
    have : 0 ≤ ∫ x, L x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    linarith
  obtain ⟨A, hA1, hφA⟩ := exists_one_le_exp_neg_bernsteinExponent_le hβ0
    (by norm_num : (0 : ℝ) ≤ 2 * 1 / 3) (by positivity : (0 : ℝ) < min (1 / 4) (η / 24))
  have hq : 2 ^ 1 * Real.exp (-bernsteinExponent (∫ x, L x ^ 2 ∂P + 1) (2 * 1 / 3) A) ≤
      1 / 2 := by
    have := min_le_left (1 / 4 : ℝ) (η / 24)
    linarith
  have hmax' : 4 * (2 ^ 1 * Real.exp (-bernsteinExponent (∫ x, L x ^ 2 ∂P + 1) (2 * 1 / 3) A))
      ≤ η / 3 := by
    have := min_le_right (1 / 4 : ℝ) (η / 24)
    linarith
  set δ : ℝ := min (r / 2) (ε / (4 * (2 * A + 1))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : 4 * δ * (2 * A + 1) ≤ ε := by
    have h := min_le_right (r / 2) (ε / (4 * (2 * A + 1)))
    rw [← hδ, le_div_iff₀ (by positivity)] at h
    linarith
  set a : EuclideanSpace ℝ (Fin 1) := emb (theta₀ - δ) with ha
  have hw0 : 0 < 2 * δ := by positivity
  obtain ⟨hmem, hfmi, hlipf⟩ := lipschitz_indicator_comp_fin_one_halfOpenCube P psi hm
    ((min_le_left _ _).trans_lt (half_lt_self hr)) hint hNm hL0
    fun x hx a b ha hb ↦ by rw [hLM x hx]; exact hlip x a b ha hb
  have hrem := tendstoInMeasure_lipschitzChainRemainder μ P X hiid L hLm hL0 hL2 one_pos
  rw [tendstoInMeasure_iff_measureReal_lt_dist] at hrem
  filter_upwards [eventually_ge_atTop 1,
    (hcons (δ / 2) (half_pos hδ0)).eventually (eventually_le_nhds (by positivity : 0 < η / 3)),
    (hrem 1 one_pos).eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η / 3))]
    with n hn1 hn2 hn3
  have hmax := measureReal_exists_abs_empiricalProcess_sub_gt_le_four_mul μ P X hiid f a hw0
    (fun θ hθ ↦ (hfmi θ hθ).1) (fun θ hθ ↦ (hfmi θ hθ).2) L hLm hL0 hL2 hlipf one_pos hn1
    (by linarith) hq
  have hsub : {ω | ε < dist ((Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P))) 0} ⊆
      (({ω | δ / 2 < dist (T n ω) theta₀} ∪
        {ω | ∃ θ ∈ halfOpenCube a (2 * δ),
          Real.sqrt ((1 : ℕ) : ℝ) * (2 * δ) * (2 * A + lipschitzChainRemainder P X L 1 n ω) <
            |empiricalProcess P X n (f θ) ω - empiricalProcess P X n (f a) ω|}) ∪
        {ω | 1 < dist (lipschitzChainRemainder P X L 1 n ω) 0}) ∪
        {ω | ¬ ∀ i, X i ω ∉ N} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_exists, not_and, not_not] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    rw [Real.dist_eq] at h1
    rw [Real.dist_eq, sub_zero] at h3
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    rw [Nat.cast_one, Real.sqrt_one, one_mul] at h2
    have hR : 2 * A + lipschitzChainRemainder P X L 1 n ω ≤ 2 * A + 1 := by
      linarith [le_abs_self (lipschitzChainRemainder P X L 1 n ω)]
    have hb : ∀ t, |t - theta₀| < δ → |empiricalProcess P X n (f (emb t)) ω -
        empiricalProcess P X n (f a) ω| ≤ 2 * δ * (2 * A + 1) := fun t ht ↦
      (h2 _ (hmem t ht)).trans (mul_le_mul_of_nonneg_left hR hw0.le)
    have hT := hb (T n ω) (by linarith)
    have h0 := hb theta₀ (by simpa using hδ0)
    have hG : ∀ t, empiricalProcess P X n (f (emb t)) ω =
        (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, psi t (X i ω) - n * ∫ x, psi t x ∂P) :=
      fun t ↦ empiricalProcess_indicator_compl_eq P X hN0 n (psi t) h4
    rw [mul_sub, ← hG, ← hG] at hω
    have htri := abs_sub_le (empiricalProcess P X n (f (emb (T n ω))) ω)
      (empiricalProcess P X n (f a) ω) (empiricalProcess P X n (f (emb theta₀)) ω)
    rw [abs_sub_comm (empiricalProcess P X n (f a) ω)] at htri
    nlinarith
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ η / 3 + η / 3 + η / 3 + 0 := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_
          (measureReal_setOf_not_forall_notMem_eq_zero μ P X hiid hNm hN0).le)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ hn3)
        exact (measureReal_union_le _ _).trans (add_le_add hn2 (hmax.trans hmax'))
    _ = η := by ring

/-- GAPS 102.4, the scalar Z-estimator theorem under a square-integrable Lipschitz envelope. -/
theorem zEstimator_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (psi : ℝ → E → ℝ)
    (hm : Measurable (Function.uncurry psi)) (theta₀ D : ℝ) (hD : D ≠ 0)
    (hpsi : MemLp (psi theta₀) 2 P) (h0 : (∫ x, psi theta₀ x ∂P) = 0)
    (hd : HasDerivAt (fun theta ↦ ∫ x, psi theta x ∂P) D theta₀)
    (r : ℝ) (hr : 0 < r) (M : E → ℝ) (hM : MemLp M 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInMeasure mu T atTop (fun _ ↦ theta₀))
    (hroot : TendstoInMeasure mu (fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, psi (T n w) (X i w)) atTop (fun _ ↦ 0)) :
    TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) atTop (fun _ ↦ 0) ∧
      TendstoInDistribution (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀)) atTop id (fun _ ↦ mu)
        (gaussianReal 0 (Real.toNNReal (Var[psi theta₀; P] / D ^ 2))) := by
  have hXm := hiid.1
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  set F : ℝ → ℝ := fun θ ↦ ∫ x, psi θ x ∂P with hF
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)
    with hZ
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ (hmeas theta₀).comp (hXm i)).const_mul _
  have hZlim : TendstoInDistribution Z atTop id (fun _ ↦ mu)
      (gaussianReal 0 (Real.toNNReal (∫ x, psi theta₀ x ^ 2 ∂P))) :=
    tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu P X hiid _ (hmeas theta₀) hpsi h0
  have hZb : IsBoundedInProbability mu Z :=
    isBoundedInProbability_of_tendstoInDistribution mu Z hZlim
  have hsn : ∀ n : ℕ, (Real.sqrt n)⁻¹ * n = Real.sqrt n := fun n ↦ by
    rw [inv_mul_eq_div, Real.div_sqrt]
  have hSE := tendstoInMeasure_centredSum_sub_of_lipschitz mu P X hiid psi hm theta₀ r hr
    M hM hpsi hlip T hcons
  -- `√n F(Tₙ) + Zₙ → 0`
  have hE1 : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * F (T n w) + Z n w)
      atTop (fun _ ↦ 0) := by
    have := tendstoInMeasure_add_zero mu _ _ hroot
      (tendstoInMeasure_const_mul_zero mu _ (-1) hSE)
    convert this using 3 with n w
    simp only [hZ, hF]
    rw [h0]
    first
      | linear_combination (∫ x, psi (T n w) x ∂P) * hsn n
      | linear_combination (-(∫ x, psi (T n w) x ∂P)) * hsn n
  set ρ : ℝ → ℝ := Function.update (fun t ↦ slope F theta₀ t - D) theta₀ 0 with hρ
  have hρc : ContinuousAt ρ theta₀ := by
    rw [hρ, continuousAt_update_same]
    have := (hasDerivAt_iff_tendsto_slope.1 hd).sub_const D
    simpa using this
  have hρ0 : ρ theta₀ = 0 := by simp [hρ]
  have hρT : TendstoInMeasure mu (fun (n : ℕ) w ↦ ρ (T n w)) atTop (fun _ ↦ 0) := by
    have := tendstoInMeasure_comp_of_continuousAt mu T theta₀ ρ hρc hcons
    rwa [hρ0] at this
  set W : ℕ → Ω → ℝ := fun n w ↦ Real.sqrt n * (T n w - theta₀) with hW
  have hF0 : F theta₀ = 0 := h0
  have hid : ∀ (n : ℕ) (w : Ω),
      Real.sqrt n * F (T n w) = D * W n w + W n w * ρ (T n w) := fun n w ↦ by
    by_cases h : T n w = theta₀
    · simp [hW, h, hF0]
    · have : ρ (T n w) = (T n w - theta₀)⁻¹ * (F (T n w) - F theta₀) - D := by
        rw [hρ, Function.update_of_ne h]
        simp [slope_def_field, div_eq_inv_mul]
      rw [this, hF0, sub_zero]
      have hne : T n w - theta₀ ≠ 0 := sub_ne_zero.2 h
      simp only [hW]
      field_simp
      ring
  set Ev : ℕ → Ω → ℝ := fun n w ↦ D * W n w + W n w * ρ (T n w) + Z n w with hEv
  have hE : TendstoInMeasure mu Ev atTop (fun _ ↦ 0) := by
    convert hE1 using 3 with n w
    simp only [hEv]
    rw [hid]
  have hWb : IsBoundedInProbability mu W :=
    isBoundedInProbability_of_tendstoInMeasure_const_mul_add_mul_add mu W Z
      (fun n w ↦ ρ (T n w)) D hD hZb hρT hE
  have hWρ := tendstoInMeasure_mul_zero_of_isBoundedInProbability mu W _ hWb hρT
  have hDWZ : TendstoInMeasure mu (fun (n : ℕ) w ↦ D * W n w + Z n w) atTop (fun _ ↦ 0) := by
    have := tendstoInMeasure_add_zero mu _ _ hE
      (tendstoInMeasure_const_mul_zero mu _ (-1) hWρ)
    convert this using 3 with n w
    simp only [hEv]; ring
  have hrem : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) atTop (fun _ ↦ 0) := by
    have := tendstoInMeasure_const_mul_zero mu _ D⁻¹ hDWZ
    convert this using 3 with n w
    simp only [hW, hZ]
    rw [mul_inv]
    field_simp
  refine ⟨hrem, ?_⟩
  have hvar : Var[psi theta₀; P] = ∫ x, psi theta₀ x ^ 2 ∂P := by
    rw [variance_eq_integral (hmeas theta₀).aemeasurable]
    simp only [h0, sub_zero]
  have hX' : TendstoInDistribution (fun (n : ℕ) w ↦ -D⁻¹ * Z n w) atTop id (fun _ ↦ mu)
      (gaussianReal 0 (Real.toNNReal (Var[psi theta₀; P] / D ^ 2))) := by
    refine tendstoInDistribution_of_map_eq (hZlim.continuous_comp (g := fun x ↦ -D⁻¹ * x)
      (continuous_const.mul continuous_id)) aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    have hI0 : 0 ≤ ∫ x, psi theta₀ x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    simp only [NNReal.coe_mul, NNReal.coe_mk, hvar, Real.coe_toNNReal _ hI0,
      Real.coe_toNNReal _ (div_nonneg hI0 (sq_nonneg D))]
    field_simp
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable mu _ _
    (fun n ↦ (hZm n).const_mul _) (fun n ↦ ((hT n).sub_const _).const_mul _) hX' ?_
  convert hrem using 3 with n w
  simp only [hZ]
  rw [mul_inv]
  ring

end CKSD
