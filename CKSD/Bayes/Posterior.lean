module

public import CKSD.Bayes.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.StrongLaw
public import TauCeti.Probability.Distributions.Gaussian.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric


/-!
# Posterior summaries, empirical Bayes, and asymptotic normality of posteriors

Results on posteriors in finite-dimensional models: the volume minimality of highest-density
regions, Tweedie's formula and its Poisson analogue with Robbins' empirical Bayes estimator, the
Bernstein–von Mises theorem in the normal location model, and the deterministic core of the
Laplace approximation of posterior normalizing constants.

## Main results

* `CKSD.volume_highest_density_region_le`: a highest-density region has least volume among sets of
  at least its probability (GAPS 104.10).
* `CKSD.integral_mul_gaussian_pdf_real_div_eq_add_mul_deriv_log`: Tweedie's formula
  `E[θ | x] = x + v (log m)'(x)` for normal observations (GAPS 104.14).
* `CKSD.integral_mul_poisson_mass_div_eq`: the Poisson identity
  `E[θ | x] = (x + 1) m(x + 1) / m(x)` (GAPS 104.14).
* `CKSD.ae_tendsto_robbins_estimator`: almost-sure consistency of Robbins' estimator
  (GAPS 104.14).
* `CKSD.tendsto_in_measure_total_variation_distance_normal_posterior`: Bernstein–von Mises in
  the normal location model (GAPS 104.1).
* `CKSD.integral_exp_neg_inner_to_euclidean_clm_div_two`: the Gaussian integral
  `∫ exp(-⟪y, H y⟫/2) dy = (2π)^{d/2} / √(det H)`.
* `CKSD.tendsto_laplace_approximation`: Laplace's method on a compact set
  `n^{d/2} ∫_K a e^{-n f} → a(m) (2π)^{d/2} / √(det ∇²f(m))` (GAPS 104.5).

The Bernstein–von Mises theorem is proved by an explicit `L¹` comparison of the posterior
density with the Gaussian density near the sample mean, combined with Mathlib's strong law of
large numbers (`ProbabilityTheory.strong_law_ae_real`). The Gaussian integral uses TauCeti's
normalization of the multivariate normal density
(`TauCeti.Probability.multivariateGaussian_eq_withDensity`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 104.10: volume minimality of a highest-density region. If `P` has density `f`, the set
`C` lies between `{f > k}` and `{f ≥ k}` with `k > 0`, and `P C ≤ P D`, then `vol C ≤ vol D`. -/
theorem volume_highest_density_region_le {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : HasDensity P volume f) (k : ℝ) (hk : 0 < k)
    (C D : Set (EuclideanSpace ℝ (Fin d))) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hlow : {x | k < f x} ⊆ C) (hhigh : C ⊆ {x | k ≤ f x})
    (hmass : P C ≤ P D) : volume C ≤ volume D := by
  obtain ⟨hfm, -, hP⟩ := hf
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  -- On `C \ D` the density is at least `k`, on `D \ C` at most `k`.
  have hlow' : ENNReal.ofReal k * volume (C \ D) ≤ P (C \ D) := by
    rw [hP, withDensity_apply _ (hC.diff hD), ← setLIntegral_const]
    exact setLIntegral_mono hfm.ennreal_ofReal fun x hx ↦ ENNReal.ofReal_le_ofReal (hhigh hx.1)
  have hhigh' : P (D \ C) ≤ ENNReal.ofReal k * volume (D \ C) := by
    rw [hP, withDensity_apply _ (hD.diff hC), ← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
    by_contra h
    exact hx.2 (hlow (lt_of_not_ge h))
  have hdiff : P (C \ D) ≤ P (D \ C) := by
    have h1 := measure_inter_add_sdiff (μ := P) C hD
    have h2 := measure_inter_add_sdiff (μ := P) D hC
    rw [inter_comm] at h2
    rw [← h1, ← h2] at hmass
    exact ENNReal.le_of_add_le_add_left (measure_ne_top P _) hmass
  have hvol : volume (C \ D) ≤ volume (D \ C) :=
    (ENNReal.mul_le_mul_iff_right hk0 ENNReal.ofReal_ne_top).1
      (hlow'.trans (hdiff.trans hhigh'))
  rw [← measure_inter_add_sdiff C hD, ← measure_inter_add_sdiff D hC, inter_comm D C]
  gcongr

/-- GAPS 104.14: Tweedie's formula. For `X | θ ~ N(θ, v)` and an arbitrary probability prior `π`
with marginal density `m(x) = ∫ φ_{θ,v}(x) dπ(θ)`, the posterior mean is `x + v (log m)'(x)`. -/
theorem integral_mul_gaussian_pdf_real_div_eq_add_mul_deriv_log (π : Measure ℝ)
    [IsProbabilityMeasure π] (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    let m := fun t ↦ ∫ θ, gaussianPDFReal θ v t ∂π;
    (∫ θ, θ * gaussianPDFReal θ v x ∂π) / m x =
      x + (v : ℝ) * deriv (fun t ↦ Real.log (m t)) x := by
  intro m
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hv0 : (v : ℝ) ≠ 0 := hvpos.ne'
  set c : ℝ := (√(2 * Real.pi * v))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set K : ℝ := max 1 (2 * (v : ℝ)) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK2 : 2 * (v : ℝ) ≤ K := le_max_right _ _
  have hφ (θ t : ℝ) : gaussianPDFReal θ v t = c * Real.exp (-(t - θ) ^ 2 / (2 * v)) := rfl
  -- The derivative of the Gaussian kernel is bounded uniformly in the mean and the argument.
  have hbound (t θ : ℝ) : ‖-(t - θ) / (v : ℝ) * gaussianPDFReal θ v t‖ ≤ K / v * c := by
    rw [hφ, Real.norm_eq_abs]
    set u := t - θ
    have hE := Real.exp_pos (-u ^ 2 / (2 * v))
    have hexp : Real.exp (-u ^ 2 / (2 * v)) * Real.exp (u ^ 2 / (2 * v)) = 1 := by
      rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    have hge := Real.add_one_le_exp (u ^ 2 / (2 * v))
    have hu : |u| ≤ K * (1 + u ^ 2 / (2 * v)) := by
      have h1 : |u| ≤ 1 + u ^ 2 := by
        have := sq_abs u
        nlinarith [sq_nonneg (|u| - 1)]
      have h2 : u ^ 2 ≤ K * (u ^ 2 / (2 * v)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg u]
      nlinarith
    have hmain : |u| * Real.exp (-u ^ 2 / (2 * v)) ≤ K := by
      calc |u| * Real.exp (-u ^ 2 / (2 * v))
          ≤ K * (1 + u ^ 2 / (2 * v)) * Real.exp (-u ^ 2 / (2 * v)) :=
            mul_le_mul_of_nonneg_right hu hE.le
        _ ≤ K * Real.exp (u ^ 2 / (2 * v)) * Real.exp (-u ^ 2 / (2 * v)) := by
            gcongr; linarith
        _ = K := by rw [mul_assoc, mul_comm (Real.exp _), hexp, mul_one]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hvpos, abs_mul, abs_of_nonneg hc0,
      abs_of_pos hE]
    calc |u| / v * (c * Real.exp (-u ^ 2 / (2 * v)))
        = (|u| * Real.exp (-u ^ 2 / (2 * v))) / v * c := by ring
      _ ≤ K / v * c := by gcongr
  have hcont (t : ℝ) : Continuous fun θ ↦ gaussianPDFReal θ v t := by
    simp_rw [hφ]; fun_prop
  have hφle (θ t : ℝ) : ‖gaussianPDFReal θ v t‖ ≤ c := by
    rw [hφ, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
    refine mul_le_of_le_one_right hc0 ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (t - θ)]) (by positivity)
  have hint (t : ℝ) : Integrable (fun θ ↦ gaussianPDFReal θ v t) π :=
    Integrable.of_bound (hcont t).aestronglyMeasurable c (ae_of_all _ fun θ ↦ hφle θ t)
  -- Differentiation under the integral sign.
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := π) (x₀ := x)
    (F := fun t θ ↦ gaussianPDFReal θ v t)
    (F' := fun t θ ↦ -(t - θ) / (v : ℝ) * gaussianPDFReal θ v t)
    (bound := fun _ ↦ K / v * c) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun t ↦ (hcont t).aestronglyMeasurable) (hint x)
    (by
      have : Continuous fun θ ↦ -(x - θ) / (v : ℝ) * gaussianPDFReal θ v x := by
        simp_rw [hφ]; fun_prop
      exact this.aestronglyMeasurable)
    (ae_of_all _ fun θ t _ ↦ hbound t θ) (integrable_const _)
    (ae_of_all _ fun θ t _ ↦ TauCeti.Probability.hasDerivAt_gaussianPDFReal θ v t)
  obtain ⟨hF'int, hm'⟩ := hdiff
  have hmpos : 0 < m x := by
    refine integral_pos_iff_support_of_nonneg (fun θ ↦ gaussianPDFReal_nonneg _ _ _)
      (hint x) |>.2 ?_
    have : Function.support (fun θ ↦ gaussianPDFReal θ v x) = univ := by
      ext θ; simp [(gaussianPDFReal_pos θ v x hv.ne').ne']
    rw [this, measure_univ]
    exact one_pos
  have hlog : HasDerivAt (fun t ↦ Real.log (m t))
      ((∫ θ, -(x - θ) / (v : ℝ) * gaussianPDFReal θ v x ∂π) / m x) x :=
    hm'.log hmpos.ne'
  rw [hlog.deriv]
  -- `θ φ = x φ + v · (-(x - θ)/v) φ`.
  have hsplit : (∫ θ, θ * gaussianPDFReal θ v x ∂π) =
      x * m x + v * ∫ θ, -(x - θ) / (v : ℝ) * gaussianPDFReal θ v x ∂π := by
    have hpt : (fun θ ↦ θ * gaussianPDFReal θ v x) = fun θ ↦
        x * gaussianPDFReal θ v x + v * (-(x - θ) / (v : ℝ) * gaussianPDFReal θ v x) := by
      funext θ; field_simp; ring
    rw [hpt, integral_add ((hint x).const_mul x) (hF'int.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsplit]
  field_simp

/-- GAPS 104.14: the Poisson mass-ratio identity `∫ θ p_θ(x) dπ / m(x) = (x + 1) m(x + 1) / m(x)`
with `m(j) = ∫ p_θ(j) dπ(θ)`. For a probability prior on nonnegative intensities with finite first
moment and `m(x) > 0`, the left side is the posterior mean; the identity itself holds for every
measure `π`. -/
theorem integral_mul_poisson_mass_div_eq (π : Measure ℝ)
    (x : ℕ) :
    let m := fun j ↦ ∫ θ, poissonMass θ j ∂π;
    (∫ θ, θ * poissonMass θ x ∂π) / m x = (x + 1 : ℕ) * m (x + 1) / m x := by
  have hpoint (θ : ℝ) : θ * poissonMass θ x =
      ((x + 1 : ℕ) : ℝ) * poissonMass θ (x + 1) := by
    have hx : (x.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero x)
    have hs : ((x + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [poissonMass, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp [hx, hs]
  dsimp only
  simp_rw [hpoint]
  rw [integral_const_mul]

/-- GAPS 104.14: almost-sure consistency of Robbins' estimator. For i.i.d. counts with law `P`
and `P{x} > 0`, the ratio `(x + 1) #{i < n | Xᵢ = x + 1} / #{i < n | Xᵢ = x}` converges almost
surely to `(x + 1) P{x + 1} / P{x}`. -/
theorem ae_tendsto_robbins_estimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Measure ℕ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hiid : IsIndependentIdenticallyDistributed μ X P) (x : ℕ) (hx : 0 < P {x}) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((x + 1 : ℕ) : ℝ) *
      ((Finset.range n).filter (fun i ↦ X i ω = x + 1)).card /
      ((Finset.range n).filter (fun i ↦ X i ω = x)).card) atTop
      (𝓝 (((x + 1 : ℕ) : ℝ) * P.real {x + 1} / P.real {x})) := by
  have hfreq (j : ℕ) : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦
        (((Finset.range n).filter (fun i ↦ X i ω = j)).card : ℝ) / n)
        atTop (𝓝 (P.real {j})) := by
    let f : ℕ → ℝ := ({j} : Set ℕ).indicator (fun _ ↦ 1)
    have hf : Measurable f := measurable_of_countable f
    have hid (i : ℕ) : IdentDistrib (X i) (X 0) μ μ :=
      ⟨(hiid.1 i).aemeasurable, (hiid.1 0).aemeasurable, by rw [hiid.2.2 i, hiid.2.2 0]⟩
    have hmap : IdentDistrib (X 0) id μ P :=
      ⟨(hiid.1 0).aemeasurable, measurable_id.aemeasurable, by simp [hiid.2.2 0]⟩
    have hint : Integrable (fun ω ↦ f (X 0 ω)) μ := by
      have hfp : Integrable f P :=
        (integrable_const (μ := P) (1 : ℝ)).indicator (measurableSet_singleton j)
      exact (hmap.comp hf).integrable_iff.mpr hfp
    have hmean : (∫ ω, f (X 0 ω) ∂μ) = P.real {j} := by
      calc
        _ = ∫ t, f t ∂P := (hmap.comp hf).integral_eq
        _ = P.real {j} := by
          change (∫ t, ({j} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) t ∂P) = _
          rw [integral_indicator (measurableSet_singleton j), setIntegral_const]
          simp
    have hlln := strong_law_ae_real (fun i ω ↦ f (X i ω)) hint
      (fun i k hik ↦ (hiid.2.1.indepFun hik).comp hf hf)
      (fun i ↦ (hid i).comp hf)
    rw [hmean] at hlln
    simpa only [f, Set.indicator, Set.mem_singleton_iff, Finset.sum_boole] using hlln
  have hden : P.real {x} ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt hx) (measure_ne_top P {x})).ne'
  filter_upwards [hfreq (x + 1), hfreq x] with ω hnum hdenom
  have hlim := (((tendsto_const_nhds (x := ((x + 1 : ℕ) : ℝ))).mul hnum).div hdenom hden)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [Pi.div_apply, ← mul_div_assoc, div_div_div_cancel_right₀ hn0]

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
private theorem abs_measure_real_sub_le_integral {g q : ℝ → ℝ} (hg : Integrable g)
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


/-- Deterministic core of the Bernstein–von Mises theorem in the normal location model: the total
variation bound holds uniformly over posterior centres `m` near the true parameter, for all large
`n`. -/
private theorem exists_tv_normal_posterior_le (prior : ℝ → ℝ) (hmeas : Measurable prior)
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
    simp only [normalPosterior, hden]
  have hvn : v / (n : ℝ≥0) ≠ 0 := by
    have : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn0.ne'
    exact div_ne_zero hv.ne' this
  have hG : gaussianReal 0 v = (gaussianReal m (v / n)).map T := by
    have h2 : T = (fun x ↦ Real.sqrt n * x) ∘ (fun x ↦ x - m) := rfl
    rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_natCast]
      rw [Real.sq_sqrt hn0.le]
      field_simp
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
    refine (abs_measure_real_sub_le_integral hgint hg0 (hEint.div_const I)
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
  refine ⟨?_, csSup_le hne hle⟩
  refine (abs_nonneg _).trans (le_csSup ⟨ε, hle⟩ ⟨∅, MeasurableSet.empty, rfl⟩)

/-- GAPS 104.1: Bernstein–von Mises theorem for the normal location model `N(θ, v)`. For any
prior density that is continuous and positive at the true mean `θ₀`, the posterior of
`√n (θ - X̄ₙ)` converges to `N(0, v)` in total variation, in probability. The normalization
`∫ prior = 1` forces the prior density to be integrable. -/
theorem tendsto_in_measure_total_variation_distance_normal_posterior {Ω : Type*}
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
  obtain ⟨δ, hδ, N, hN⟩ := exists_tv_normal_posterior_le prior hm hpos h1 θ₀ hc htrue v hv
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

/-- Gaussian integral for a positive definite matrix `H`:
`∫ exp(-⟪y, H y⟫/2) dy = (2π)^{d/2} / √(det H)`, from the normalization of TauCeti's
multivariate normal density with covariance `H⁻¹`. -/
theorem integral_exp_neg_inner_to_euclidean_clm_div_two {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) H y) / 2) =
      Real.rpow (2 * Real.pi) ((d : ℝ) / 2) / Real.sqrt H.det := by
  set S := H⁻¹ with hSdef
  have hS : S.PosDef := hH.inv
  have hdetH : 0 < H.det := hH.det_pos
  have hSinv : S⁻¹ = H := by
    rw [hSdef, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetH.ne')]
  have hdetS : S.det = H.det⁻¹ := by rw [hSdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hmass := TauCeti.Probability.multivariateGaussian_eq_withDensity hS
    (0 : EuclideanSpace ℝ (Fin d))
  have h1 : ∫ x, TauCeti.Probability.multivariateGaussianPDFReal 0 S x = 1 := by
    simp_rw [← TauCeti.Probability.toReal_multivariateGaussianPDF]
    rw [integral_toReal (by fun_prop) (ae_of_all _ fun _ ↦
      TauCeti.Probability.multivariateGaussianPDF_lt_top _ _ _)]
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hmass]
    simp
  simp only [TauCeti.Probability.multivariateGaussianPDFReal_def, sub_zero, hSinv,
    Fintype.card_fin] at h1
  rw [integral_const_mul] at h1
  have e : ∀ y : EuclideanSpace ℝ (Fin d),
      inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) H y) = inner ℝ y (Matrix.toEuclideanLin H y) :=
    fun y ↦ rfl
  simp_rw [e]
  have hc : (2 * Real.pi) ^ (-(d : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) ≠ 0 := by
    have : 0 < S.det := hS.det_pos
    positivity
  rw [eq_div_iff (Real.sqrt_pos.2 hdetH).ne']
  have h2 := h1
  rw [mul_comm] at h2
  have h3 : ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-inner ℝ y (Matrix.toEuclideanLin H y) / 2) =
      ((2 * Real.pi) ^ (-(d : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2))⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h1
  rw [h3, hdetS, Real.sqrt_eq_rpow, Real.inv_rpow hdetH.le, ← Real.rpow_neg hdetH.le,
    mul_inv, ← Real.rpow_neg (by positivity), ← Real.rpow_neg hdetH.le]
  rw [show -(-(d : ℝ) / 2) = (d : ℝ) / 2 by ring, mul_assoc, ← Real.rpow_add hdetH]
  norm_num


/-- Coercivity of a positive definite quadratic form: `c ‖v‖² ≤ ⟪v, H v⟫` for some `c > 0`. -/
theorem exists_pos_mul_norm_sq_le_inner_to_euclidean_clm {d : ℕ}
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    ∃ c > 0, ∀ v : EuclideanSpace ℝ (Fin d),
      c * ‖v‖ ^ 2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H v) := by
  set q : EuclideanSpace ℝ (Fin d) → ℝ := fun v ↦ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H v)
    with hq
  have hqc : Continuous q := by fun_prop
  have hqpos (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) : 0 < q v := by
    simp only [hq, Matrix.inner_toEuclideanCLM]
    have hx : (WithLp.ofLp v) ≠ 0 := by
      intro h; apply hv; rw [← WithLp.toLp_ofLp (p := 2) v, h]; rfl
    simpa using hH.dotProduct_mulVec_pos hx
  have hhom (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) : q (t • v) = t ^ 2 * q v := by
    simp only [hq, map_smul, inner_smul_left, inner_smul_right]; simp; ring
  by_cases hS : (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_isMinOn
      hS hqc.continuousOn
    have hu₀0 : u₀ ≠ 0 := by
      intro h; rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at hu₀; norm_num at hu₀
    refine ⟨q u₀, hqpos u₀ hu₀0, fun v ↦ ?_⟩
    by_cases hv : v = 0
    · simp [hv, hq]
    have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnv.ne']
    have h1 := hmin hu
    simp only [Set.mem_ofPred_eq] at h1
    have h2 : q v = ‖v‖ ^ 2 * q (‖v‖⁻¹ • v) := by
      rw [hhom, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hnv.ne', one_pow, one_mul]
    change q u₀ * ‖v‖ ^ 2 ≤ q v
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun v ↦ ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    exfalso; apply hS
    refine ⟨‖v‖⁻¹ • v, ?_⟩
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.2 hv).ne']

/-- Second-order Taylor estimate at a critical point: for `C²` `f` with `f m = 0` and
`Df(m) = 0`, `|f(m + h) - ½ D²f(m)(h, h)| ≤ ε ‖h‖²` for all small `h`. -/
theorem exists_abs_sub_half_fderiv_fderiv_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : E} (hm0 : f m = 0)
    (hd : fderiv ℝ f m = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      |f (m + h) - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) m h h| ≤ ε * ‖h‖ ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ f) m with hBdef
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hB : HasFDerivAt (fderiv ℝ f) B m :=
    ((hf1.differentiable (by norm_num)) m).hasFDerivAt
  have hsymm : ∀ u v, B u v = B v u :=
    ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := m)) (by simp)
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hB).bound hε
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hlo
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  set φ : E → ℝ := fun k ↦ f (m + k) - (1 / 2 : ℝ) * B k k with hφ
  have hderiv (k : E) : HasFDerivAt φ (fderiv ℝ f (m + k) - B k) k := by
    have h1 : HasFDerivAt (fun k ↦ f (m + k)) (fderiv ℝ f (m + k)) k := by
      have := (hdiff (m + k)).hasFDerivAt
      exact this.comp k ((hasFDerivAt_id k).const_add m)
    have h2 := B.hasFDerivAt_of_bilinear (hasFDerivAt_id k) (hasFDerivAt_id k)
    have h3 := h1.sub (h2.const_mul (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext v
    simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, hsymm v k]
    ring
  have hbound : ∀ k ∈ Metric.closedBall (0 : E) ‖h‖, ‖fderiv ℝ f (m + k) - B k‖ ≤ ε * ‖h‖ := by
    intro k hk
    rw [mem_closedBall_zero_iff] at hk
    have hkδ : dist k 0 < δ := by rw [dist_zero_right]; linarith
    have := hδb hkδ
    simp only [hd, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hk hε.le)
  have hmvt := (convex_closedBall (0 : E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun k _ ↦ (hderiv k).hasFDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg h))
    (mem_closedBall_zero_iff.2 le_rfl)
  simp only [hφ, add_zero, hm0, map_zero, mul_zero, sub_zero,
    Real.norm_eq_abs] at hmvt
  calc _ ≤ ε * ‖h‖ * ‖h‖ := hmvt
    _ = ε * ‖h‖ ^ 2 := by ring


/-- On a compact set where `f` is positive off `m`, a local quadratic lower bound at `m` extends to
a global one: `c ‖x - m‖² ≤ f x` on `K`. -/
theorem exists_pos_mul_norm_sub_sq_le_of_is_compact {E : Type*} [NormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) {m : E} {f : E → ℝ} (hfc : Continuous f)
    (huniq : ∀ x ∈ K, x ≠ m → 0 < f x) {δ c₁ : ℝ} (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (hloc : ∀ h : E, ‖h‖ < δ → c₁ * ‖h‖ ^ 2 ≤ f (m + h)) :
    ∃ c > 0, ∀ x ∈ K, c * ‖x - m‖ ^ 2 ≤ f x := by
  set A := K ∩ {x | δ ≤ ‖x - m‖} with hA
  have hAc : IsCompact A := hK.inter_right (isClosed_le continuous_const (by fun_prop))
  have hη : ∃ η > 0, ∀ x ∈ A, η ≤ f x := by
    by_cases hne : A.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hAc.exists_isMinOn hne hfc.continuousOn
      refine ⟨f x₀, huniq x₀ hx₀.1 ?_, fun x hx ↦ hmin hx⟩
      intro h; have := hx₀.2; simp only [Set.mem_ofPred_eq, h, sub_self, norm_zero] at this
      linarith
    · exact ⟨1, one_pos, fun x hx ↦ absurd ⟨x, hx⟩ hne⟩
  obtain ⟨η, hη0, hηA⟩ := hη
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ K, ‖x - m‖ ≤ R := by
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun x ↦ x - m) (by fun_prop)
    exact ⟨R, hR⟩
  set R' := max R δ with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le hδ (le_max_right _ _)
  refine ⟨min c₁ (η / R' ^ 2), lt_min hc₁ (by positivity), fun x hx ↦ ?_⟩
  by_cases hxm : ‖x - m‖ < δ
  · have := hloc (x - m) hxm
    rw [add_sub_cancel] at this
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans this
  · have hxA : x ∈ A := ⟨hx, not_lt.1 hxm⟩
    have h1 : ‖x - m‖ ^ 2 ≤ R' ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((hR x hx).trans (le_max_left _ _)) 2
    calc min c₁ (η / R' ^ 2) * ‖x - m‖ ^ 2 ≤ η / R' ^ 2 * R' ^ 2 :=
          mul_le_mul (min_le_right _ _) h1 (sq_nonneg _) (by positivity)
      _ = η := by field_simp
      _ ≤ f x := hηA x hxA


/-- GAPS 104.5: Laplace's method on a compact region `K`. If `f` is `C²` with `f(m) = 0` at an
interior point `m`, `f > 0` on `K \ {m}`, and `∇²f(m) = H` is positive definite, then for `a`
continuous on `K`, `n^{d/2} ∫_K a e^{-n f} → a(m) (2π)^{d/2} / √(det H)`. This is the
deterministic core of the approximation; the random-likelihood and BIC conclusions of the source
require additional probabilistic hypotheses. -/
theorem tendsto_laplace_approximation
    {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (m : EuclideanSpace ℝ (Fin d)) (hm : m ∈ interior K)
    (f a : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 2 f)
    (ha : ContinuousOn a K) (hmin : f m = 0)
    (huniq : ∀ x ∈ K, x ≠ m → 0 < f x)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosDef)
    (hhess : ∀ u v, fderiv ℝ (fderiv ℝ f) m u v =
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) H v)) :
    Tendsto (fun n : ℕ ↦ Real.rpow n ((d : ℝ) / 2) *
      ∫ x in K, a x * Real.exp (-(n : ℝ) * f x)) atTop
      (𝓝 (a m * Real.rpow (2 * Real.pi) ((d : ℝ) / 2) / Real.sqrt H.det)) := by
  set H' := Matrix.toEuclideanCLM (𝕜 := ℝ) H with hH'
  have hKm : K ∈ 𝓝 m := mem_interior_iff_mem_nhds.1 hm
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hfc : Continuous f := hf.continuous
  have hlmin : IsLocalMin f m := by
    filter_upwards [hKm] with x hx
    rcases eq_or_ne x m with rfl | hxm
    · exact le_rfl
    · rw [hmin]; exact (huniq x hx hxm).le
  have hd : fderiv ℝ f m = 0 := hlmin.fderiv_eq_zero
  obtain ⟨c₁, hc₁, hcoer⟩ := exists_pos_mul_norm_sq_le_inner_to_euclidean_clm hH
  obtain ⟨δ, hδ, hTay⟩ := exists_abs_sub_half_fderiv_fderiv_le hf hmin hd
    (ε := c₁ / 4) (by positivity)
  have hloc : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ < δ → c₁ / 4 * ‖h‖ ^ 2 ≤ f (m + h) := by
    intro h hh
    have h1 := hTay h hh
    have h2 := hcoer h
    rw [hhess] at h1
    have := (abs_le.1 h1).1
    nlinarith
  obtain ⟨c, hc, hquad⟩ := exists_pos_mul_norm_sub_sq_le_of_is_compact hK hfc huniq hδ
    (by positivity) hloc
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn ha
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA m (interior_subset hm))
  -- the rescaled integrands
  set s : ℕ → ℝ := fun n ↦ (Real.sqrt ((n : ℝ) + 1))⁻¹ with hs
  have hs0 (n : ℕ) : 0 < s n := by simp only [hs]; positivity
  have hs2 (n : ℕ) : ((n : ℝ) + 1) * s n ^ 2 = 1 := by
    simp only [hs, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    field_simp
  set g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x ↦ a x * Real.exp (-(n : ℝ) * f x) with hg
  set F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n y ↦ K.indicator (g (n + 1)) (m + s n • y)
    with hF
  have hgm (n : ℕ) : Measurable (K.indicator (g n)) := by
    rw [← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise (ha.mul (by fun_prop)) continuousOn_const hKmeas
  have hFeq (n : ℕ) : Real.rpow ((n + 1 : ℕ) : ℝ) ((d : ℝ) / 2) * ∫ x in K, g (n + 1) x =
      ∫ y, F n y := by
    simp only [hF]
    rw [Measure.integral_comp_smul volume (fun z ↦ K.indicator (g (n + 1)) (m + z)) (s n),
      integral_add_left_eq_self (fun z ↦ K.indicator (g (n + 1)) z) m (μ := volume),
      integral_indicator hKmeas, finrank_euclideanSpace_fin, smul_eq_mul]
    congr 1
    simp only [hs]
    rw [inv_pow, inv_inv, abs_of_pos (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    push_cast
    congr 1; ring
  -- domination
  have hbound (n : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
      ‖F n y‖ ≤ A * Real.exp (-c * ‖y‖ ^ 2) := by
    simp only [hF]
    by_cases hmem : m + s n • y ∈ K
    · rw [Set.indicator_of_mem hmem]
      simp only [hg, norm_mul, Real.norm_eq_abs, Real.abs_exp]
      refine mul_le_mul (hA _ hmem) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hA0
      have hq := hquad _ hmem
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 n), mul_pow] at hq
      push_cast
      have h3 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
      have h4 : ((n : ℝ) + 1) * (c * (s n ^ 2 * ‖y‖ ^ 2)) = c * ‖y‖ ^ 2 := by
        linear_combination (c * ‖y‖ ^ 2) * hs2 n
      linarith
    · rw [Set.indicator_of_notMem hmem, norm_zero]; positivity
  have hbint : Integrable (fun y : EuclideanSpace ℝ (Fin d) ↦ A * Real.exp (-c * ‖y‖ ^ 2)) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin d))
      (b := (c : ℂ)) (by simpa using hc) 0 0).norm
    refine (h.congr (ae_of_all _ fun y ↦ ?_)).const_mul A
    simp only [zero_mul, add_zero, Complex.norm_exp]
    norm_cast
  -- pointwise limit
  have hslim : Tendsto s atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h1)
  have hlim (y : EuclideanSpace ℝ (Fin d)) : Tendsto (fun n ↦ F n y) atTop
      (𝓝 (a m * Real.exp (-inner ℝ y (H' y) / 2))) := by
    have hx : Tendsto (fun n ↦ m + s n • y) atTop (𝓝 m) := by
      simpa using tendsto_const_nhds.add (hslim.smul_const y)
    have hsy : Tendsto (fun n ↦ s n • y) atTop (𝓝 0) := by simpa using hslim.smul_const y
    have hev : ∀ᶠ n in atTop, m + s n • y ∈ K := hx.eventually_mem hKm
    have ha' : Tendsto (fun n ↦ a (m + s n • y)) atTop (𝓝 (a m)) :=
      ((ha.continuousAt hKm).tendsto).comp hx
    have hf' : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * f (m + s n • y)) atTop
        (𝓝 (inner ℝ y (H' y) / 2)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ', hδ', hT'⟩ := exists_abs_sub_half_fderiv_fderiv_le hf hmin hd
        (ε := ε / (2 * (‖y‖ ^ 2 + 1))) (by positivity)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hsy δ' hδ'
      refine ⟨N, fun n hn ↦ ?_⟩
      have h1 := hN n hn
      rw [dist_zero_right] at h1
      have h2 := hT' _ h1
      rw [hhess, map_smul, inner_smul_left, inner_smul_right,
        norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 n), mul_pow] at h2
      simp only [conj_trivial] at h2
      rw [Real.dist_eq]
      have e : ((n : ℝ) + 1) * f (m + s n • y) - inner ℝ y (H' y) / 2 =
          ((n : ℝ) + 1) * (f (m + s n • y) - 1 / 2 * (s n * (s n * inner ℝ y (H' y)))) := by
        have := hs2 n
        linear_combination (inner ℝ y (H' y) / 2) * this
      rw [e, abs_mul, abs_of_pos (by positivity)]
      calc ((n : ℝ) + 1) * |f (m + s n • y) - 1 / 2 * (s n * (s n * inner ℝ y (H' y)))|
          ≤ ((n : ℝ) + 1) * (ε / (2 * (‖y‖ ^ 2 + 1)) * (s n ^ 2 * ‖y‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ε / (2 * (‖y‖ ^ 2 + 1)) * ‖y‖ ^ 2 := by
            have := hs2 n
            linear_combination (ε / (2 * (‖y‖ ^ 2 + 1)) * ‖y‖ ^ 2) * this
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [sq_nonneg ‖y‖]
    have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) + 1) * f (m + s n • y))) atTop
        (𝓝 (Real.exp (-inner ℝ y (H' y) / 2))) := by
      have := (Real.continuous_exp.tendsto _).comp hf'.neg
      refine this.congr' (Eventually.of_forall fun n ↦ ?_) |>.trans ?_
      · simp only [Function.comp_apply, neg_mul]
      · rw [neg_div]
    refine (ha'.mul hexp).congr' ?_
    filter_upwards [hev] with n hn
    simp only [hF, Set.indicator_of_mem hn, hg]
    push_cast; ring_nf
  -- dominated convergence
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    have haff : Measurable fun y : EuclideanSpace ℝ (Fin d) ↦ m + s n • y := by fun_prop
    have : Measurable (F n) := (hgm (n + 1)).comp haff
    exact this.aestronglyMeasurable
  have hDCT := tendsto_integral_of_dominated_convergence (F := F)
    (f := fun y ↦ a m * Real.exp (-inner ℝ y (H' y) / 2))
    (fun y ↦ A * Real.exp (-c * ‖y‖ ^ 2)) hFm hbint (fun n ↦ ae_of_all _ (hbound n))
    (ae_of_all _ hlim)
  have hval : ∫ y, a m * Real.exp (-inner ℝ y (H' y) / 2) =
      a m * Real.rpow (2 * Real.pi) ((d : ℝ) / 2) / Real.sqrt H.det := by
    rw [integral_const_mul, hH', integral_exp_neg_inner_to_euclidean_clm_div_two hH, mul_div_assoc]
  rw [hval] at hDCT
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hDCT.congr fun n ↦ ?_
  simp only [hg] at hFeq
  exact (hFeq n).symm


end CKSD
