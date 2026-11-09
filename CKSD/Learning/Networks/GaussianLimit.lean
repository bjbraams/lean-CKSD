module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Characteristic functions of wide random layers

For a layer of width `N` with independent standard normal parameters, the characteristic
function of a scalar output `a b + c ∑ₖ vₖ g(uₖ)` (bias `b`, output weights `vₖ`, hidden-unit
parameters `uₖ`) factors as the product of the Gaussian factor of the bias and the `N`-th power
of a Gaussian mixture integral over one hidden unit. The power converges as `N → ∞` when
`c² = C / N`, which gives the Gaussian-process limit of wide networks at initialization.

## Main results

* `CKSD.measurePreserving_uncurry_pi`: the product measure on `κ × U → α` is the image of the
  iterated product measure under uncurrying.
* `CKSD.integral_cexp_wideLayer`: the factorization of the characteristic function.
* `CKSD.tendsto_integral_exp_neg_div_pow`: `(𝔼 exp(-h/N))^N → exp(-𝔼 h)` for integrable `h ≥ 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Complex

namespace CKSD

/-- The product measure `μ^{κ × U}` is the image of the iterated product measure
`(μ^U)^κ` under uncurrying `z ↦ ((k, u) ↦ z k u)`. -/
theorem measurePreserving_uncurry_pi {κ U : Type*} [Fintype κ] [Fintype U] {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (fun z : κ → U → α ↦ fun p : κ × U ↦ z p.1 p.2)
      (Measure.pi fun _ : κ ↦ Measure.pi fun _ : U ↦ μ) (Measure.pi fun _ : κ × U ↦ μ) where
  measurable := by fun_prop
  map_eq := by
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have : (fun z : κ → U → α ↦ fun p : κ × U ↦ z p.1 p.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun k ↦ Set.univ.pi fun u ↦ s (k, u) := by
      ext z
      simp [Set.mem_pi, Prod.forall]
    rw [this, Measure.pi_pi]
    simp_rw [Measure.pi_pi, Fintype.prod_prod_type]

/-- Integral of `exp(i t v)` against the standard normal law: `exp(-t²/2)`. -/
private lemma integral_cexp_mul_gaussianReal (t : ℝ) :
    ∫ v, cexp (↑(t * v) * I) ∂gaussianReal 0 1 = ↑(Real.exp (-(t ^ 2 / 2))) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  simp only [ofReal_mul]
  rw [h, ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Characteristic function of a wide random layer.** Under independent standard normal
parameters indexed by `(Fin N × U) ⊕ (Fin N ⊕ Unit)` (hidden-unit parameters `uₖ ∈ ℝ^U`,
output weights `vₖ`, bias `b`), the scalar output `a b + c ∑ₖ vₖ g(uₖ)` has characteristic
function at `1` equal to `exp(-a²/2) · (𝔼 exp(-c² g(u)²/2))^N`. -/
theorem integral_cexp_wideLayer {U : Type*} [Fintype U] (N : ℕ) (g : (U → ℝ) → ℝ)
    (hg : Measurable g) (a c : ℝ) :
    ∫ θ, cexp (↑(a * θ (Sum.inr (Sum.inr ())) + c * ∑ k, θ (Sum.inr (Sum.inl k)) *
        g (fun i ↦ θ (Sum.inl (k, i)))) * I)
      ∂(Measure.pi fun _ : (Fin N × U) ⊕ (Fin N ⊕ Unit) ↦ gaussianReal 0 1) =
    ↑(Real.exp (-(a ^ 2 / 2))) *
      (↑(∫ u, Real.exp (-(c ^ 2 * g u ^ 2 / 2)) ∂(Measure.pi fun _ : U ↦ gaussianReal 0 1)) :
        ℂ) ^ N := by
  set μ : Measure ℝ := gaussianReal 0 1
  let F : ((Fin N × U) ⊕ (Fin N ⊕ Unit) → ℝ) → ℂ := fun θ ↦
    cexp (↑(a * θ (Sum.inr (Sum.inr ())) + c * ∑ k, θ (Sum.inr (Sum.inl k)) *
        g (fun i ↦ θ (Sum.inl (k, i)))) * I)
  have hFm : Measurable F := by fun_prop
  change ∫ θ, F θ ∂_ = _
  rw [← (measurePreserving_sumPiEquivProdPi_symm (fun _ ↦ μ)).integral_comp']
  have hint : Integrable (fun p ↦ F ((MeasurableEquiv.sumPiEquivProdPi _).symm p))
      ((Measure.pi fun _ : Fin N × U ↦ μ).prod (Measure.pi fun _ : Fin N ⊕ Unit ↦ μ)) := by
    refine Integrable.of_bound ((hFm.comp (MeasurableEquiv.measurable _)).aestronglyMeasurable)
      1 (Eventually.of_forall fun p ↦ ?_)
    simp only [F]
    rw [norm_exp_ofReal_mul_I]
  rw [integral_prod _ hint]
  -- inner integral over the output layer
  have hinner : ∀ z : Fin N × U → ℝ,
      ∫ w, F ((MeasurableEquiv.sumPiEquivProdPi _).symm (z, w))
        ∂(Measure.pi fun _ : Fin N ⊕ Unit ↦ μ) =
      ↑(Real.exp (-(a ^ 2 / 2))) *
        ∏ k, (↑(Real.exp (-(c ^ 2 * g (fun i ↦ z (k, i)) ^ 2 / 2))) : ℂ) := by
    intro z
    let f : (j : Fin N ⊕ Unit) → ℝ → ℂ := fun j v ↦ match j with
      | Sum.inl k => cexp (↑((c * g (fun i ↦ z (k, i))) * v) * I)
      | Sum.inr _ => cexp (↑(a * v) * I)
    have hF : ∀ w : Fin N ⊕ Unit → ℝ,
        F ((MeasurableEquiv.sumPiEquivProdPi _).symm (z, w)) = ∏ j, f j (w j) := by
      intro w
      simp only [F, f, Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton,
        MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
        Equiv.sumPiEquivProdPi_symm_apply]
      rw [← Complex.exp_sum, ← Complex.exp_add]
      congr 1
      push_cast
      rw [Finset.mul_sum, add_mul, Finset.sum_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp_rw [hF]
    rw [integral_fintype_prod_eq_prod, Fintype.prod_sum_type, mul_comm]
    simp only [f, μ, integral_cexp_mul_gaussianReal, Finset.univ_unique, Finset.prod_singleton,
      mul_pow]
  simp_rw [hinner]
  rw [integral_const_mul]
  congr 1
  rw [← (measurePreserving_uncurry_pi (κ := Fin N) (U := U) μ).map_eq,
    integral_map (measurePreserving_uncurry_pi μ).measurable.aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop)),
    integral_fintype_prod_eq_prod (f := fun (_ : Fin N) (u : U → ℝ) ↦
      (↑(Real.exp (-(c ^ 2 * g u ^ 2 / 2))) : ℂ)), integral_complex_ofReal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- For `y ≥ 0`, `n (exp(-y/n) - 1) → -y` as `n → ∞`. -/
private lemma tendsto_natCast_mul_exp_neg_div_sub_one (y : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (Real.exp (-(y / n)) - 1)) atTop (𝓝 (-y)) := by
  have hb : ∀ᶠ n : ℕ in atTop, |(n : ℝ) * (Real.exp (-(y / n)) - 1) - (-y)| ≤ y ^ 2 / n := by
    filter_upwards [eventually_ge_atTop (⌈|y|⌉₊ + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hyn : |y| ≤ n := by
      have := Nat.le_ceil |y|
      have : ((⌈|y|⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (show ⌈|y|⌉₊ ≤ n by omega)
      linarith
    have hx : |-(y / n)| ≤ 1 := by
      rw [abs_neg, abs_div, abs_of_pos hn0, div_le_one hn0]
      exact hyn
    have h := Real.abs_exp_sub_one_sub_id_le hx
    have : (n : ℝ) * (Real.exp (-(y / n)) - 1) - (-y) =
        n * (Real.exp (-(y / n)) - 1 - (-(y / n))) := by
      field_simp
    rw [this, abs_mul, abs_of_pos hn0]
    calc (n : ℝ) * |Real.exp (-(y / n)) - 1 - -(y / n)| ≤ n * (-(y / n)) ^ 2 :=
          mul_le_mul_of_nonneg_left h hn0.le
      _ = y ^ 2 / n := by field_simp
  have h0 : Tendsto (fun n : ℕ ↦ y ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ h0
  simpa only [Real.norm_eq_abs] using hb

/-- **Poisson-type limit of a mixture.** For an integrable `h ≥ 0` under a probability measure,
`(𝔼 exp(-h/N))^N → exp(-𝔼 h)` as `N → ∞`. -/
theorem tendsto_integral_exp_neg_div_pow {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) (h0 : 0 ≤ h) :
    Tendsto (fun N : ℕ ↦ (∫ ω, Real.exp (-(h ω / N)) ∂μ) ^ N) atTop
      (𝓝 (Real.exp (-∫ ω, h ω ∂μ))) := by
  have hexp : ∀ N : ℕ, Integrable (fun ω ↦ Real.exp (-(h ω / N))) μ := fun N ↦
    Integrable.of_bound ((by fun_prop : Continuous fun y : ℝ ↦ Real.exp (-(y / N))
      ).comp_aestronglyMeasurable hh.1) 1 (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
        exact div_nonneg (h0 ω) (Nat.cast_nonneg N))
  have key : ∀ N : ℕ, (N : ℝ) * ((∫ ω, Real.exp (-(h ω / N)) ∂μ) - 1) =
      ∫ ω, (N : ℝ) * (Real.exp (-(h ω / N)) - 1) ∂μ := by
    intro N
    rw [integral_const_mul, integral_sub (hexp N) (integrable_const 1), integral_const,
      probReal_univ, one_smul]
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) * ((∫ ω, Real.exp (-(h ω / N)) ∂μ) - 1)) atTop
      (𝓝 (-∫ ω, h ω ∂μ)) := by
    simp_rw [key, ← integral_neg]
    refine tendsto_integral_of_dominated_convergence h (fun N ↦ ?_) hh (fun N ↦ ?_)
      (Eventually.of_forall fun ω ↦ tendsto_natCast_mul_exp_neg_div_sub_one (h ω))
    · exact (by fun_prop : Continuous fun y : ℝ ↦ (N : ℝ) * (Real.exp (-(y / N)) - 1)
        ).comp_aestronglyMeasurable hh.1
    · refine Eventually.of_forall fun ω ↦ ?_
      have hy := h0 ω
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simpa using hy
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : Real.exp (-(h ω / N)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; exact div_nonneg hy hN'.le
      have h2 : -(h ω / N) + 1 ≤ Real.exp (-(h ω / N)) := Real.add_one_le_exp _
      rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hN'.le (by linarith))]
      have : (N : ℝ) * (h ω / N) = h ω := by field_simp
      nlinarith
  have := Real.tendsto_one_add_pow_exp_of_tendsto hlim
  simpa using this

end CKSD
