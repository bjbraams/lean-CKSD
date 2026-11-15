module

public import CKSD.Bayes.Basic
public import CKSD.Nonparametric.Basic
import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Bernstein–von Mises theorem in the normal location model

For i.i.d. observations from `N(θ₀, v)` and a prior probability density that is continuous and
positive at `θ₀`, the posterior `CKSD.normalPosterior` of `√n (θ - X̄ₙ)` converges to `N(0, v)`
in total variation, in probability.

## Main results

* `CKSD.tendstoInMeasure_totalVariationDistance_normalPosterior`: Bernstein–von Mises in
  the normal location model (GAPS 104.1).

The proof is an explicit `L¹` comparison of the posterior density with the Gaussian density
near the sample mean, combined with Mathlib's strong law of large numbers
(`ProbabilityTheory.strong_law_ae_real`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Shifted Gaussian integral `∫ exp(-b (θ - m)²) dθ = √(π / b)`. -/
private theorem integral_exp_neg_mul_sq_sub (b m : ℝ) :
    ∫ θ, Real.exp (-b * (θ - m) ^ 2) = Real.sqrt (Real.pi / b) :=
  (integral_sub_right_eq_self (fun θ ↦ Real.exp (-b * θ ^ 2)) m).trans (integral_gaussian b)

/-- The shifted Gaussian kernel `exp(-b (θ - m)²)` is integrable for `b > 0`. -/
private theorem integrable_exp_neg_mul_sq_sub {b : ℝ} (hb : 0 < b) (m : ℝ) :
    Integrable (fun θ ↦ Real.exp (-b * (θ - m) ^ 2)) :=
  (integrable_exp_neg_mul_sq hb).comp_sub_right m

/-- The difference of the masses of an event under two laws with densities, one of them
normalized by `c`, is at most the `L¹` distance of the normalized densities. -/
private theorem abs_measureReal_sub_le_integral {g q : ℝ → ℝ} (hg : Integrable g)
    (hg0 : ∀ θ, 0 ≤ g θ) (hq : Integrable q) (hq0 : ∀ θ, 0 ≤ q θ) {c : ℝ} (hc : 0 < c)
    {B : Set ℝ} (hB : MeasurableSet B) :
    |((ENNReal.ofReal c)⁻¹ • volume.withDensity (fun θ ↦ ENNReal.ofReal (g θ))).real B -
      (volume.withDensity (fun θ ↦ ENNReal.ofReal (q θ))).real B| ≤ ∫ θ, |g θ / c - q θ| := by
  have hP : ((ENNReal.ofReal c)⁻¹ • volume.withDensity (fun θ ↦ ENNReal.ofReal (g θ))).real B
      = ∫ θ in B, g θ / c := by
    rw [measureReal_def, smul_apply, withDensity_apply _ hB, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le,
      ← ofReal_integral_eq_lintegral_ofReal hg.integrableOn (ae_of_all _ fun θ ↦ hg0 θ),
      ENNReal.toReal_ofReal (setIntegral_nonneg hB fun θ _ ↦ hg0 θ), integral_div]
    ring
  have hQ : (volume.withDensity (fun θ ↦ ENNReal.ofReal (q θ))).real B = ∫ θ in B, q θ := by
    rw [measureReal_def, withDensity_apply _ hB,
      ← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (ae_of_all _ fun θ ↦ hq0 θ),
      ENNReal.toReal_ofReal (setIntegral_nonneg hB fun θ _ ↦ hq0 θ)]
  rw [hP, hQ, ← integral_sub (hg.div_const c).integrableOn hq.integrableOn]
  exact abs_integral_le_integral_abs.trans
    (setIntegral_le_integral ((hg.div_const c).sub hq).abs (ae_of_all _ fun θ ↦ abs_nonneg _))

/-- If `g` is `L¹`-close to `p₀ E`, relative to the mass `p₀ I` of `p₀ E`, then the normalized
densities `g / ∫ g` and `E / I` are `L¹`-close. -/
private theorem integral_abs_div_sub_le {g E : ℝ → ℝ} (hg : Integrable g) (hE : Integrable E)
    (hE0 : ∀ θ, 0 ≤ E θ) {p₀ I η : ℝ} (hp₀ : 0 < p₀) (hI : ∫ θ, E θ = I) (hIpos : 0 < I)
    (hη : η ≤ 1 / 2) (hD : ∫ θ, |g θ - p₀ * E θ| ≤ η * (p₀ * I)) :
    0 < ∫ θ, g θ ∧ ∫ θ, |g θ / (∫ θ, g θ) - E θ / I| ≤ 4 * η := by
  set c := ∫ θ, g θ with hc_def
  set D := ∫ θ, |g θ - p₀ * E θ| with hD_def
  have hdiff : |p₀ * I - c| ≤ D := by
    have h : p₀ * I - c = ∫ θ, (p₀ * E θ - g θ) := by
      rw [integral_sub (hE.const_mul p₀) hg, integral_const_mul, hI]
    rw [h]
    refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
    congr 1
    funext θ
    rw [abs_sub_comm]
  have hD0 : 0 ≤ D := integral_nonneg fun _ ↦ abs_nonneg _
  have hpI : 0 < p₀ * I := mul_pos hp₀ hIpos
  have hc : p₀ * I / 2 ≤ c := by
    have := (abs_le.mp hdiff).2
    nlinarith
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  refine ⟨hcpos, ?_⟩
  have hpt (θ : ℝ) : |g θ / c - E θ / I| ≤
      |g θ - p₀ * E θ| / c + |p₀ * I - c| / c * (E θ / I) := by
    have heq : g θ / c - E θ / I = (g θ - p₀ * E θ) / c + (p₀ * I - c) / c * (E θ / I) := by
      field_simp
      ring
    rw [heq]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hcpos, abs_mul, abs_div, abs_of_pos hcpos,
      abs_of_nonneg (div_nonneg (hE0 θ) hIpos.le)]
  have hint : Integrable (fun θ ↦ |g θ - p₀ * E θ| / c + |p₀ * I - c| / c * (E θ / I)) :=
    ((hg.sub (hE.const_mul p₀)).abs.div_const c).add ((hE.div_const I).const_mul _)
  calc ∫ θ, |g θ / c - E θ / I|
      ≤ ∫ θ, (|g θ - p₀ * E θ| / c + |p₀ * I - c| / c * (E θ / I)) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hint (ae_of_all _ hpt)
    _ = D / c + |p₀ * I - c| / c := by
        have h1 : Integrable (fun θ ↦ |g θ - p₀ * E θ| / c) :=
          (hg.sub (hE.const_mul p₀)).abs.div_const c
        have h2 : Integrable (fun θ ↦ |p₀ * I - c| / c * (E θ / I)) :=
          (hE.div_const I).const_mul _
        rw [integral_add h1 h2, integral_div, integral_const_mul, integral_div, hI,
          div_self hIpos.ne', mul_one]
    _ ≤ 2 * D / c := by
        rw [mul_div_assoc, two_mul]
        gcongr
    _ ≤ 2 * (η * (p₀ * I)) / (p₀ * I / 2) := by
        gcongr
        nlinarith
    _ = 4 * η := by
        field_simp
        ring


/-- `L¹` bound for the difference between the unnormalized posterior density
`prior θ · exp(-b (θ - m)²)` and its frozen version `p₀ · exp(-b (θ - m)²)`, splitting into a
neighbourhood of the true parameter and a Gaussian tail. -/
private theorem integral_abs_prior_mul_sub_le {prior : ℝ → ℝ} (hint : Integrable prior)
    (hpos : ∀ θ, 0 ≤ prior θ) (h1 : ∫ θ, prior θ = 1) {θ₀ p₀ η' δ b m : ℝ} (hp₀ : 0 ≤ p₀)
    (hδ : 0 < δ) (hb : 0 < b) (hcont : ∀ θ, |θ - θ₀| < 2 * δ → |prior θ - p₀| ≤ η')
    (hm : |m - θ₀| < δ) :
    ∫ θ, |prior θ * Real.exp (-b * (θ - m) ^ 2) - p₀ * Real.exp (-b * (θ - m) ^ 2)| ≤
      η' * Real.sqrt (Real.pi / b) +
        Real.exp (-(b / 2) * δ ^ 2) * (1 + p₀ * Real.sqrt (Real.pi / (b / 2))) := by
  have hη' : 0 ≤ η' := (abs_nonneg _).trans (hcont m (by linarith))
  have hb2 : 0 < b / 2 := half_pos hb
  set K := Real.exp (-(b / 2) * δ ^ 2)
  have hpt (θ : ℝ) :
      |prior θ * Real.exp (-b * (θ - m) ^ 2) - p₀ * Real.exp (-b * (θ - m) ^ 2)| ≤
        η' * Real.exp (-b * (θ - m) ^ 2) +
          K * (prior θ + p₀ * Real.exp (-(b / 2) * (θ - m) ^ 2)) := by
    have hE := Real.exp_pos (-b * (θ - m) ^ 2)
    rw [← sub_mul, abs_mul, abs_of_pos hE]
    have hK : 0 ≤ K * (prior θ + p₀ * Real.exp (-(b / 2) * (θ - m) ^ 2)) :=
      mul_nonneg (Real.exp_pos _).le (add_nonneg (hpos θ) (mul_nonneg hp₀ (Real.exp_pos _).le))
    rcases lt_or_ge |θ - m| δ with hlt | hge
    · have : |θ - θ₀| < 2 * δ := by
        calc |θ - θ₀| = |(θ - m) + (m - θ₀)| := by ring_nf
          _ ≤ |θ - m| + |m - θ₀| := abs_add_le _ _
          _ < 2 * δ := by linarith
      have := mul_le_mul_of_nonneg_right (hcont θ this) hE.le
      linarith
    · have hsq : δ ^ 2 ≤ (θ - m) ^ 2 := by
        rw [← sq_abs (θ - m)]
        exact pow_le_pow_left₀ hδ.le hge 2
      have hsplit : Real.exp (-b * (θ - m) ^ 2) =
          Real.exp (-(b / 2) * (θ - m) ^ 2) * Real.exp (-(b / 2) * (θ - m) ^ 2) := by
        rw [← Real.exp_add]; ring_nf
      have hE1 : Real.exp (-(b / 2) * (θ - m) ^ 2) ≤ K :=
        Real.exp_le_exp.2 (by nlinarith)
      have hE2 : Real.exp (-(b / 2) * (θ - m) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (θ - m)])
      have hpos2 := Real.exp_pos (-(b / 2) * (θ - m) ^ 2)
      have hEK : Real.exp (-b * (θ - m) ^ 2) ≤ K * Real.exp (-(b / 2) * (θ - m) ^ 2) := by
        rw [hsplit]; exact mul_le_mul_of_nonneg_right hE1 hpos2.le
      have hEK' : Real.exp (-b * (θ - m) ^ 2) ≤ K := by
        rw [hsplit]; nlinarith
      have habs : |prior θ - p₀| ≤ prior θ + p₀ := by
        rw [abs_le]; constructor <;> linarith [hpos θ]
      calc |prior θ - p₀| * Real.exp (-b * (θ - m) ^ 2)
          ≤ (prior θ + p₀) * Real.exp (-b * (θ - m) ^ 2) :=
            mul_le_mul_of_nonneg_right habs hE.le
        _ ≤ prior θ * K + p₀ * (K * Real.exp (-(b / 2) * (θ - m) ^ 2)) := by
            rw [add_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left hEK' (hpos θ))
              (mul_le_mul_of_nonneg_left hEK hp₀)
        _ ≤ _ := by nlinarith [mul_nonneg hη' hE.le]
  have hI1 := integrable_exp_neg_mul_sq_sub hb m
  have hI2 := integrable_exp_neg_mul_sq_sub hb2 m
  have hRint : Integrable (fun θ ↦ η' * Real.exp (-b * (θ - m) ^ 2) +
      K * (prior θ + p₀ * Real.exp (-(b / 2) * (θ - m) ^ 2))) :=
    (hI1.const_mul η').add ((hint.add (hI2.const_mul p₀)).const_mul K)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hRint
    (ae_of_all _ hpt)).trans (le_of_eq ?_)
  have hA : Integrable (fun θ ↦ η' * Real.exp (-b * (θ - m) ^ 2)) := hI1.const_mul η'
  have hB : Integrable (fun θ ↦ K * (prior θ + p₀ * Real.exp (-(b / 2) * (θ - m) ^ 2))) :=
    (hint.add (hI2.const_mul p₀)).const_mul K
  have hC : Integrable (fun θ ↦ p₀ * Real.exp (-(b / 2) * (θ - m) ^ 2)) := hI2.const_mul p₀
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_add hint hC,
    integral_const_mul, h1, integral_exp_neg_mul_sq_sub, integral_exp_neg_mul_sq_sub]

/-- Eventual smallness, as `b → ∞`, of the Gaussian tail term in the posterior `L¹` bound. -/
private theorem eventually_exp_tail_le {δ p₀ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ b in atTop, Real.exp (-(b / 2) * δ ^ 2) * (1 + p₀ * Real.sqrt (Real.pi / (b / 2))) ≤
      c * Real.sqrt (Real.pi / b) := by
  have hlim : Tendsto (fun b : ℝ ↦ b ^ (1 / 2 : ℝ) * Real.exp (-(δ ^ 2 / 2) * b) +
      p₀ * Real.sqrt (2 * Real.pi) * (b ^ (0 : ℝ) * Real.exp (-(δ ^ 2 / 2) * b))) atTop
      (𝓝 (0 + p₀ * Real.sqrt (2 * Real.pi) * 0)) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by positivity)).add
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by positivity)).const_mul _)
  simp only [mul_zero, add_zero] at hlim
  have hev := hlim.eventually (gt_mem_nhds (show 0 < c * Real.sqrt Real.pi by positivity))
  filter_upwards [hev, eventually_gt_atTop 0] with b hb hb0
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  rw [Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] at hb
  have h1 : Real.sqrt (Real.pi / b) = Real.sqrt Real.pi / Real.sqrt b :=
    Real.sqrt_div' _ hb0.le
  have h2 : Real.sqrt (Real.pi / (b / 2)) = Real.sqrt (2 * Real.pi) / Real.sqrt b := by
    rw [show Real.pi / (b / 2) = 2 * Real.pi / b by field_simp, Real.sqrt_div' _ hb0.le]
  have h3 : -(b / 2) * δ ^ 2 = -(δ ^ 2 / 2) * b := by ring
  rw [h1, h2, h3]
  rw [← sub_pos] at hb
  rw [← sub_nonneg]
  have : c * (Real.sqrt Real.pi / Real.sqrt b) -
      Real.exp (-(δ ^ 2 / 2) * b) * (1 + p₀ * (Real.sqrt (2 * Real.pi) / Real.sqrt b)) =
      (c * Real.sqrt Real.pi - (Real.sqrt b * Real.exp (-(δ ^ 2 / 2) * b) +
        p₀ * Real.sqrt (2 * Real.pi) * Real.exp (-(δ ^ 2 / 2) * b))) / Real.sqrt b := by
    field_simp
  rw [this]
  exact div_nonneg hb.le hsb.le


/-- Rescaling a Gaussian: if `n > 0`, then `N(0, v)` is the image of `N(m, v / n)` under
`θ ↦ √n (θ - m)`. -/
theorem gaussianReal_eq_map_sqrt_mul_sub (v : ℝ≥0) (m : ℝ) {n : ℕ} (hn0 : (0 : ℝ) < n) :
    gaussianReal 0 v = (gaussianReal m (v / n)).map fun θ ↦ Real.sqrt n * (θ - m) := by
  have h2 : (fun θ ↦ Real.sqrt n * (θ - m)) = (fun x ↦ Real.sqrt n * x) ∘ (fun x ↦ x - m) := rfl
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_natCast]
    rw [Real.sq_sqrt hn0.le]
    field_simp

/-- Deterministic core of the Bernstein–von Mises theorem in the normal location model: the total
variation bound holds uniformly over posterior centres `m` near the true parameter, for all large
`n`. -/
private theorem exists_tv_normalPosterior_le (prior : ℝ → ℝ) (hmeas : Measurable prior)
    (hpos : ∀ θ, 0 ≤ prior θ)
    (h1 : ∫ θ, prior θ = 1) (θ₀ : ℝ) (hc : ContinuousAt prior θ₀) (htrue : 0 < prior θ₀)
    (v : ℝ≥0) (hv : 0 < v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℝ, |m - θ₀| < δ →
      0 ≤ totalVariationDistance ((normalPosterior prior v n m).map
        (fun θ ↦ Real.sqrt n * (θ - m))) (gaussianReal 0 v) ∧
      totalVariationDistance ((normalPosterior prior v n m).map
        (fun θ ↦ Real.sqrt n * (θ - m))) (gaussianReal 0 v) ≤ ε := by
  have hint : Integrable prior := by
    by_contra h
    rw [integral_undef h] at h1
    norm_num at h1
  set p₀ := prior θ₀ with hp₀
  set η := min (1 / 2 : ℝ) (ε / 4) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  set η' := η * p₀ / 2 with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousAt_iff.1 hc η' hη'0
  set δ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := half_pos hδ₀
  have hcont : ∀ θ, |θ - θ₀| < 2 * δ → |prior θ - p₀| ≤ η' := fun θ hθ ↦ by
    have := hδ₀' (x := θ) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at this
    exact this.le
  have hv' : (0 : ℝ) < v := hv
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 * v)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hb.eventually (eventually_exp_tail_le (p₀ := p₀) hδ hη'0)).and (eventually_ge_atTop 1))
  refine ⟨δ, hδ, N, fun n hn m hm ↦ ?_⟩
  obtain ⟨htail, hn1⟩ := hN n hn
  set b := (n : ℝ) / (2 * v) with hbdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hb0 : 0 < b := by positivity
  set E : ℝ → ℝ := fun θ ↦ Real.exp (-b * (θ - m) ^ 2) with hE
  set g : ℝ → ℝ := fun θ ↦ prior θ * E θ with hg
  set I := Real.sqrt (Real.pi / b) with hI
  have hIpos : 0 < I := Real.sqrt_pos.2 (by positivity)
  have hEint : Integrable E := integrable_exp_neg_mul_sq_sub hb0 m
  have hE0 (θ : ℝ) : 0 ≤ E θ := (Real.exp_pos _).le
  have hgint : Integrable g :=
    hint.mono' (hmeas.mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos θ) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right (hpos θ)
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (θ - m)])))
  have hg0 (θ : ℝ) : 0 ≤ g θ := mul_nonneg (hpos θ) (hE0 θ)
  have hD : ∫ θ, |g θ - p₀ * E θ| ≤ η * (p₀ * I) := by
    have := integral_abs_prior_mul_sub_le hint hpos h1 htrue.le hδ hb0 hcont hm
    rw [← hI] at this
    have h2 : η' * I + η' * I = η * (p₀ * I) := by rw [hη']; ring
    exact this.trans (by linarith)
  obtain ⟨hcpos, hL1⟩ := integral_abs_div_sub_le hgint hEint hE0 htrue
    (integral_exp_neg_mul_sq_sub b m) hIpos (min_le_left _ _) hD
  set T : ℝ → ℝ := fun θ ↦ Real.sqrt n * (θ - m) with hT
  have hTm : Measurable T := by fun_prop
  have hP : normalPosterior prior v n m =
      (ENNReal.ofReal (∫ θ, g θ))⁻¹ • volume.withDensity (fun θ ↦ ENNReal.ofReal (g θ)) := by
    have hden (θ : ℝ) : prior θ * Real.exp (-(n : ℝ) * (θ - m) ^ 2 / (2 * v)) = g θ := by
      simp only [g, E, b]
      congr 2
      ring
    simp only [normalPosterior_def, hden]
  have hvn : v / (n : ℝ≥0) ≠ 0 := by
    have : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
    exact div_ne_zero hv.ne' this
  have hG : gaussianReal 0 v = (gaussianReal m (v / n)).map T :=
    gaussianReal_eq_map_sqrt_mul_sub v m hn0
  have hGd : gaussianReal m (v / n) =
      volume.withDensity (fun θ ↦ ENNReal.ofReal (E θ / I)) := by
    rw [gaussianReal_of_var_ne_zero _ hvn, gaussianPDF_def]
    congr 1
    funext θ
    congr 1
    rw [gaussianPDFReal_def]
    have hvar : 2 * Real.pi * ((v / (n : ℝ≥0) : ℝ≥0) : ℝ) = Real.pi / b := by
      simp only [NNReal.coe_div, NNReal.coe_natCast, b]
      field_simp
    simp only [E, I]
    rw [hvar, div_eq_inv_mul (Real.exp _)]
    congr 2
    simp only [NNReal.coe_div, NNReal.coe_natCast, b]
    field_simp
  have hbound : ∀ A : Set ℝ, MeasurableSet A →
      |((normalPosterior prior v n m).map T).real A - (gaussianReal 0 v).real A| ≤ ε := by
    intro A hA
    rw [map_measureReal_apply hTm hA, hG, map_measureReal_apply hTm hA, hP, hGd]
    refine (abs_measureReal_sub_le_integral hgint hg0 (hEint.div_const I)
      (fun θ ↦ div_nonneg (hE0 θ) hIpos.le) hcpos (hTm hA)).trans (hL1.trans ?_)
    have := min_le_right (1 / 2 : ℝ) (ε / 4)
    linarith
  have hne : {r : ℝ | ∃ A : Set ℝ, MeasurableSet A ∧ r =
      |((normalPosterior prior v n m).map T).real A - (gaussianReal 0 v).real A|}.Nonempty :=
    ⟨_, ∅, MeasurableSet.empty, rfl⟩
  have hle : ∀ r ∈ {r : ℝ | ∃ A : Set ℝ, MeasurableSet A ∧ r =
      |((normalPosterior prior v n m).map T).real A - (gaussianReal 0 v).real A|}, r ≤ ε := by
    rintro r ⟨A, hA, rfl⟩
    exact hbound A hA
  rw [totalVariationDistance_def]
  refine ⟨?_, csSup_le hne hle⟩
  refine (abs_nonneg _).trans (le_csSup ⟨ε, hle⟩ ⟨∅, MeasurableSet.empty, rfl⟩)

/-- GAPS 104.1: Bernstein–von Mises theorem for the normal location model `N(θ, v)`. For any
prior density that is continuous and positive at the true mean `θ₀`, the posterior of
`√n (θ - X̄ₙ)` converges to `N(0, v)` in total variation, in probability. The normalization
`∫ prior = 1` forces the prior density to be integrable. -/
theorem tendstoInMeasure_totalVariationDistance_normalPosterior {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (θ₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X (gaussianReal θ₀ v))
    (prior : ℝ → ℝ) (hm : Measurable prior)
    (hpos : ∀ θ, 0 ≤ prior θ) (h1 : (∫ θ, prior θ) = 1)
    (hc : ContinuousAt prior θ₀) (htrue : 0 < prior θ₀) :
    TendstoInMeasure μ (fun (n : ℕ) w ↦ totalVariationDistance
      ((normalPosterior prior v n (sampleAverage X n w)).map
        (fun θ ↦ Real.sqrt n * (θ - sampleAverage X n w)))
      (gaussianReal 0 v)) atTop (fun _ ↦ 0) := by
  have hid (i : ℕ) : IdentDistrib (X i) (X 0) μ μ :=
    ⟨(hiid.1 i).aemeasurable, (hiid.1 0).aemeasurable, by rw [hiid.2.2 i, hiid.2.2 0]⟩
  have hmap : IdentDistrib (X 0) id μ (gaussianReal θ₀ v) :=
    ⟨(hiid.1 0).aemeasurable, measurable_id.aemeasurable, by simp [hiid.2.2 0]⟩
  have hint0 : Integrable (X 0) μ :=
    hmap.integrable_iff.mpr ((memLp_id_gaussianReal 1).integrable le_rfl)
  have hmean : ∫ ω, X 0 ω ∂μ = θ₀ := by
    rw [hmap.integral_eq]
    exact integral_id_gaussianReal
  have hslln := strong_law_ae_real X hint0 (fun i j hij ↦ hiid.2.1.indepFun hij) hid
  have hXm := hiid.1
  have hS : TendstoInMeasure μ (fun n w ↦ sampleAverage X n w) atTop (fun _ ↦ θ₀) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
    · unfold sampleAverage
      have : Measurable (fun w ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i w) := by fun_prop
      exact this.aestronglyMeasurable
    · filter_upwards [hslln] with ω hω
      rw [hmean] at hω
      simpa [sampleAverage, div_eq_inv_mul] using hω
  rw [tendstoInMeasure_iff_dist] at hS ⊢
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := exists_tv_normalPosterior_le prior hm hpos h1 θ₀ hc htrue v hv
    (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hS δ hδ)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  push Not at hlt
  rw [Real.dist_eq] at hlt
  obtain ⟨h0, hle⟩ := hN n hn _ hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hω
  linarith

end CKSD
