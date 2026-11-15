module

public import CKSD.Bayes.Basic
import Mathlib.Probability.StrongLaw
import TauCeti.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Posterior summaries and empirical Bayes

Results on posteriors in finite-dimensional models: the volume minimality of highest-density
regions, and Tweedie's formula and its Poisson analogue with Robbins' empirical Bayes estimator.

## Main results

* `CKSD.volume_highest_density_region_le`: a highest-density region has least reference measure
  (for instance volume) among sets of at least its probability (GAPS 104.10).
* `CKSD.integral_mul_gaussianPDFReal_div_eq_add_mul_deriv_log`: Tweedie's formula
  `E[θ | x] = x + v (log m)'(x)` for normal observations (GAPS 104.14).
* `CKSD.integral_mul_poissonMass_div_eq`: the Poisson identity
  `E[θ | x] = (x + 1) m(x + 1) / m(x)` (GAPS 104.14).
* `CKSD.ae_tendsto_robbins_estimator`: almost-sure consistency of Robbins' estimator
  (GAPS 104.14).

The Bernstein–von Mises theorem is in `CKSD.Bayes.Posterior.BernsteinVonMises` and the Laplace
approximation in `CKSD.Bayes.Posterior.Laplace`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 104.10: volume minimality of a highest-density region. If the finite measure `P` has
density `f` with respect to a reference measure `ν` (for instance Lebesgue measure on `ℝᵈ`), the
set `C` lies between `{f > k}` and `{f ≥ k}` with `k > 0`, and `P C ≤ P D`, then
`ν C ≤ ν D`. -/
theorem volume_highest_density_region_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : HasDensity P ν f) (k : ℝ) (hk : 0 < k)
    (C D : Set Ω) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hlow : {x | k < f x} ⊆ C) (hhigh : C ⊆ {x | k ≤ f x})
    (hmass : P C ≤ P D) : ν C ≤ ν D := by
  obtain ⟨hfm, -, hP⟩ := hf
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  -- On `C \ D` the density is at least `k`, on `D \ C` at most `k`.
  have hlow' : ENNReal.ofReal k * ν (C \ D) ≤ P (C \ D) := by
    rw [hP, withDensity_apply _ (hC.diff hD), ← setLIntegral_const]
    exact setLIntegral_mono hfm.ennreal_ofReal fun x hx ↦ ENNReal.ofReal_le_ofReal (hhigh hx.1)
  have hhigh' : P (D \ C) ≤ ENNReal.ofReal k * ν (D \ C) := by
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
  have hvol : ν (C \ D) ≤ ν (D \ C) :=
    (ENNReal.mul_le_mul_iff_right hk0 ENNReal.ofReal_ne_top).1
      (hlow'.trans (hdiff.trans hhigh'))
  rw [← measure_inter_add_sdiff (μ := ν) C hD, ← measure_inter_add_sdiff (μ := ν) D hC,
    inter_comm D C]
  gcongr

/-- GAPS 104.14: Tweedie's formula. For `X | θ ~ N(θ, v)` and an arbitrary probability prior `π`
with marginal density `m(x) = ∫ φ_{θ, v}(x) dπ(θ)`, the posterior mean is `x + v (log m)'(x)`. -/
theorem integral_mul_gaussianPDFReal_div_eq_add_mul_deriv_log (π : Measure ℝ)
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
  -- `θ φ = x φ + v · (-(x - θ) / v) φ`.
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
theorem integral_mul_poissonMass_div_eq (π : Measure ℝ)
    (x : ℕ) :
    let m := fun j ↦ ∫ θ, poissonMass θ j ∂π;
    (∫ θ, θ * poissonMass θ x ∂π) / m x = (x + 1 : ℕ) * m (x + 1) / m x := by
  have hpoint (θ : ℝ) : θ * poissonMass θ x =
      ((x + 1 : ℕ) : ℝ) * poissonMass θ (x + 1) := by
    have hx : (x.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero x)
    have hs : ((x + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [poissonMass_def, Nat.factorial_succ, Nat.cast_mul, pow_succ]
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

end CKSD
