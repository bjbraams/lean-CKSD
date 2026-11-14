module

public import CKSD.Nonparametric.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Pinsker
public import TauCeti.Probability.Distributions.Tilted
public import Statlib.Divergence.KullbackLeibler.CondKL


/-!
# Divergences between Gaussian product laws

Kullback–Leibler divergence and total variation between product laws of independent Gaussian
observations with a common variance. These are the information bounds behind the Gaussian
lower-bound constructions: neighbouring hypotheses whose means differ by `δ ∈ ℝⁿ` are at total
variation at most `√(‖δ‖² / (4v))`. Total variation is in the statistical normalization
`sup_A |P(A) - Q(A)|` (`CKSD.totalVariationDistance`).

## Main results

* `CKSD.kl_div_gaussian_real_gaussian_real`: `KL(N(a, v), N(b, v)) = (b - a)² / (2v)`, computed
  by exponential tilting (TauCeti's `TauCeti.Probability.gaussianReal_tilted_mul`).
* `CKSD.kl_div_pi_gaussian_real`: the product formula, from Statlib's tensorization `klDiv_pi`.
* `CKSD.total_variation_distance_le_sqrt_to_real_kl_div`: Pinsker's inequality
  `TV(P, Q) ≤ √(KL(P, Q) / 2)`, from TauCeti's `TauCeti.two_mul_sq_measureReal_sub_le_klDiv`.
* `CKSD.total_variation_distance_pi_gaussian_real_le`: `TV ≤ √(∑ (bᵢ - aᵢ)² / (4v))` for
  Gaussian product laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set InformationTheory Real
open scoped NNReal ENNReal BigOperators

namespace CKSD

/-- Kullback–Leibler divergence between Gaussian laws of a common positive variance:
`KL(N(a, v), N(b, v)) = (b - a)² / (2v)`, computed by exponential tilting. -/
theorem kl_div_gaussian_real_gaussian_real (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((b - a) ^ 2 / (2 * v)) := by
  set t : ℝ := (b - a) / v with ht
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hb : gaussianReal b v = (gaussianReal a v).tilted (t * ·) := by
    rw [TauCeti.Probability.gaussianReal_tilted_mul]
    congr 1
    rw [ht]; field_simp; ring
  set μ := gaussianReal a v
  have hexp : Integrable (fun x ↦ exp (t * x)) μ := integrable_exp_mul_gaussianReal t
  have hac : μ ≪ μ.tilted (t * ·) := absolutelyContinuous_tilted hexp
  have hself : Integrable (llr μ μ) μ :=
    (integrable_congr (llr_self μ)).mpr (integrable_zero _ _ _)
  have hlin : Integrable (fun x ↦ t * x) μ :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).const_mul t
  have hint : Integrable (llr μ (μ.tilted (t * ·))) μ :=
    integrable_llr_tilted_right Measure.AbsolutelyContinuous.rfl hlin hself hexp
  have hval := integral_llr_tilted_right (Measure.AbsolutelyContinuous.rfl) hlin hexp hself
  have hZ : ∫ x, exp (t * x) ∂μ = exp (a * t + v * t ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := a) (v := v)) t
  rw [integral_congr_ae (llr_self μ), hZ, log_exp, integral_const_mul,
    integral_id_gaussianReal] at hval
  simp only [Pi.zero_apply, integral_zero] at hval
  have hone : (μ.tilted (t * ·)).real univ = 1 := by rw [← hb]; simp
  rw [hb, klDiv_of_ac_of_integrable hac hint, hval, hone, probReal_univ]
  congr 1
  rw [ht]; field_simp; ring

/-- Kullback–Leibler divergence between finite products of Gaussian laws of a common positive
variance, from the tensorization of Kullback–Leibler divergence. -/
theorem kl_div_pi_gaussian_real {ι : Type*} [Fintype ι] (a b : ι → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (Measure.pi fun i ↦ gaussianReal (a i) v) (Measure.pi fun i ↦ gaussianReal (b i) v) =
      ∑ i, ENNReal.ofReal ((b i - a i) ^ 2 / (2 * v)) := by
  rw [klDiv_pi]
  exact Finset.sum_congr rfl fun i _ ↦ kl_div_gaussian_real_gaussian_real _ _ hv

/-- Pinsker's inequality in the statistical normalization of total variation:
`TV(P, Q) ≤ √(KL(P, Q) / 2)` when the divergence is finite. -/
theorem total_variation_distance_le_sqrt_to_real_kl_div {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hfin : klDiv P Q ≠ ∞) :
    totalVariationDistance P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨A, hA, rfl⟩
    have hr := ENNReal.toReal_mono hfin (TauCeti.two_mul_sq_measureReal_sub_le_klDiv
      (μ := P) (ν := Q) hA)
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith

/-- Total variation between finite products of Gaussian laws with common variance `v`:
`TV ≤ √(∑ (bᵢ - aᵢ)² / (4v))`. -/
theorem total_variation_distance_pi_gaussian_real_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    totalVariationDistance (Measure.pi fun i ↦ gaussianReal (a i) v)
      (Measure.pi fun i ↦ gaussianReal (b i) v) ≤
      Real.sqrt ((∑ i, (b i - a i) ^ 2) / (4 * v)) := by
  have hk := kl_div_pi_gaussian_real a b hv
  have hfin : klDiv (Measure.pi fun i ↦ gaussianReal (a i) v)
      (Measure.pi fun i ↦ gaussianReal (b i) v) ≠ ∞ := by
    rw [hk]; exact ENNReal.sum_ne_top.mpr fun i _ ↦ ENNReal.ofReal_ne_top
  refine (total_variation_distance_le_sqrt_to_real_kl_div _ _ hfin).trans (le_of_eq ?_)
  congr 1
  rw [hk, ENNReal.toReal_sum (fun i _ ↦ ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl fun i _ ↦ ENNReal.toReal_ofReal
    (div_nonneg (sq_nonneg (b i - a i)) (by positivity)), ← Finset.sum_div, div_div]
  ring_nf

end CKSD
