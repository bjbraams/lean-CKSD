module

public import CKSD.Bayes.Diffusion
public import TauCeti.Probability.Concentration.PoincareLogSobolev
public import Mathlib.Probability.Moments.Variance


/-!
# Bounded perturbations of logarithmic Sobolev inequalities

The Holley–Stroock comparison uses the nonnegative integrand
`x log x - x log a - x + a`. Its integral is minimized when `a` is the mean, so domination
of probability measures implies the same domination of the entropy of a nonnegative function.
Comparing the two Dirichlet integrals then transfers a logarithmic Sobolev inequality.

For Gibbs laws, the partition integrals cancel between the upper and lower density bounds.
Adding a measurable potential with values in `[a, b]` therefore multiplies a logarithmic Sobolev
constant by at most `exp (b - a)`. This is the bounded-perturbation component of GAPS 104.44.

The proof uses Mathlib's Bochner integral, measure domination and Gibbs normalization, and
TauCeti's entropy and logarithmic Sobolev predicates.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology ContDiff
namespace CKSD

/-- The nonnegative integrand in the variational formula for entropy. -/
def entropyIntegrand (x a : ℝ) : ℝ :=
  x * Real.log x - x * Real.log a - x + a

/-- The entropy integrand is nonnegative for a nonnegative value and a positive reference. -/
theorem entropy_integrand_nonneg {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    0 ≤ entropyIntegrand x a := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa [entropyIntegrand] using ha.le
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha hx)) hx.le
  rw [Real.log_div ha.ne' hx.ne'] at h
  have hdiv : x * (a / x - 1) = a - x := by field_simp
  rw [hdiv] at h
  dsimp [entropyIntegrand]
  nlinarith

/-- Integrability of the entropy integrand follows from integrability of its two moments. -/
theorem integrable_entropy_integrand {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hfl : Integrable (fun x ↦ f x * Real.log (f x)) μ) (a : ℝ) :
    Integrable (fun x ↦ entropyIntegrand (f x) a) μ :=
  ((hfl.sub (hf.mul_const (Real.log a))).sub hf).add (integrable_const a)

/-- The integral of the entropy integrand differs from entropy by its value at the mean. -/
theorem integral_entropy_integrand {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hfl : Integrable (fun x ↦ f x * Real.log (f x)) μ) (a : ℝ) :
    (∫ x, entropyIntegrand (f x) a ∂μ) =
      μ.entropy f + entropyIntegrand (∫ x, f x ∂μ) a := by
  simp only [entropyIntegrand, Measure.entropy_def]
  have hsub : Integrable (fun x ↦ f x * Real.log (f x) - f x * Real.log a) μ :=
    hfl.sub (hf.mul_const _)
  have hsub' : Integrable (fun x ↦ f x * Real.log (f x) - f x * Real.log a - f x) μ :=
    hsub.sub hf
  rw [integral_add hsub' (integrable_const a), integral_sub hsub hf,
    integral_sub hfl (hf.mul_const _), integral_mul_const, integral_const]
  simp
  ring

/-- Every positive reference value gives an upper bound on entropy. -/
theorem entropy_le_integral_entropy_integrand {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hfl : Integrable (fun x ↦ f x * Real.log (f x)) μ) (hf0 : 0 ≤ᵐ[μ] f)
    {a : ℝ} (ha : 0 < a) :
    μ.entropy f ≤ ∫ x, entropyIntegrand (f x) a ∂μ := by
  rw [integral_entropy_integrand μ hf hfl]
  exact le_add_of_nonneg_right (entropy_integrand_nonneg (integral_nonneg_of_ae hf0) ha)

/-- Choosing the mean as reference recovers entropy exactly. -/
theorem integral_entropy_integrand_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hfl : Integrable (fun x ↦ f x * Real.log (f x)) μ) :
    (∫ x, entropyIntegrand (f x) (∫ y, f y ∂μ) ∂μ) = μ.entropy f := by
  rw [integral_entropy_integrand μ hf hfl]
  simp [entropyIntegrand]

/-- Entropy respects almost-everywhere equality. -/
theorem entropy_congr_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ} (h : f =ᵐ[μ] g) : μ.entropy f = μ.entropy g := by
  have hl : (fun x ↦ f x * Real.log (f x)) =ᵐ[μ] (fun x ↦ g x * Real.log (g x)) :=
    h.mono fun x hx ↦ by dsimp only; rw [hx]
  rw [Measure.entropy_def, Measure.entropy_def, integral_congr_ae h, integral_congr_ae hl]

/-- Domination of probability measures gives the same domination of nonnegative entropies. -/
theorem entropy_le_mul_of_measure_le_smul {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℝ} (hA : 0 ≤ A) (hν : ν ≤ ENNReal.ofReal A • μ)
    {f : X → ℝ} (hf : Integrable f μ)
    (hfl : Integrable (fun x ↦ f x * Real.log (f x)) μ) (hf0 : 0 ≤ᵐ[μ] f) :
    ν.entropy f ≤ A * μ.entropy f := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hfν := hf.of_measure_le_smul ENNReal.ofReal_ne_top hν
  have hflν := hfl.of_measure_le_smul ENNReal.ofReal_ne_top hν
  by_cases hz : (∫ x, f x ∂μ) = 0
  · have hzero : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hf0 hf).1 hz
    rw [entropy_congr_ae μ hzero, entropy_congr_ae ν (hac.ae_le hzero)]
    simp [Measure.entropy_def]
  have hm : 0 < ∫ x, f x ∂μ :=
    lt_of_le_of_ne (integral_nonneg_of_ae hf0) (Ne.symm hz)
  calc ν.entropy f ≤ ∫ x, entropyIntegrand (f x) (∫ y, f y ∂μ) ∂ν :=
        entropy_le_integral_entropy_integrand ν hfν hflν (hac.ae_le hf0) hm
    _ ≤ ∫ x, entropyIntegrand (f x) (∫ y, f y ∂μ) ∂(ENNReal.ofReal A • μ) :=
        integral_mono_measure hν (Measure.ae_smul_measure (hf0.mono fun x hx ↦ entropy_integrand_nonneg hx hm) _)
          ((integrable_entropy_integrand μ hf hfl _).smul_measure ENNReal.ofReal_ne_top)
    _ = A * μ.entropy f := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul,
          integral_entropy_integrand_mean μ hf hfl]

/-- A logarithmic Sobolev inequality transfers between probability measures whose densities
are bounded above and below. The constant is multiplied by the ratio of the bounds. -/
theorem log_sobolev_inequality_of_measure_le_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hν : ν ≤ ENNReal.ofReal A • μ) (hμ : μ ≤ ENNReal.ofReal B • ν)
    (hLS : μ.LogSobolevInequality C) : ν.LogSobolevInequality (A * B * C) := by
  rw [Measure.LogSobolevInequality_def]
  intro f hf hdf hf2 hf2log
  have hf2μ := hf2.of_measure_le_smul ENNReal.ofReal_ne_top hμ
  have hf2logμ := hf2log.of_measure_le_smul ENNReal.ofReal_ne_top hμ
  have hdfμ := hdf.of_measure_le_smul ENNReal.ofReal_ne_top hμ
  have hI := hdf.integrable_sq
  have henergy : (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) ≤
      B * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν := by
    calc (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) ≤
          ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(ENNReal.ofReal B • ν) :=
            integral_mono_measure hμ (ae_of_all _ fun x ↦ sq_nonneg _)
              (hI.smul_measure ENNReal.ofReal_ne_top)
      _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hB, smul_eq_mul]
  calc ν.entropy (fun x ↦ f x ^ 2) ≤ A * μ.entropy (fun x ↦ f x ^ 2) :=
        entropy_le_mul_of_measure_le_smul μ ν hA hν hf2μ hf2logμ
          (ae_of_all _ fun x ↦ sq_nonneg _)
    _ ≤ A * (2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left (hLS.apply f hf hdfμ hf2μ hf2logμ) hA
    _ ≤ A * (2 * C * (B * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left henergy (by positivity)) hA
    _ = _ := by ring

/-- A lower bound on a change of potential bounds the ratio of the corresponding Gibbs laws. -/
theorem gibbs_measure_le_smul_of_sub_le {d : ℕ}
    {V W : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Integrable (fun x ↦ Real.exp (-V x)))
    (hW : Integrable (fun x ↦ Real.exp (-W x)))
    {a : ℝ} (ha : ∀ x, a ≤ W x - V x) :
    gibbsMeasure W ≤ ENNReal.ofReal
      (Real.exp (-a) * (∫ x, Real.exp (-V x)) / (∫ x, Real.exp (-W x))) • gibbsMeasure V := by
  have hZV : 0 < ∫ x, Real.exp (-V x) := integral_exp_pos hV
  have hZW : 0 < ∫ x, Real.exp (-W x) := integral_exp_pos hW
  unfold gibbsMeasure
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply ae_of_all
  intro x
  change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-W x) ≤ Real.exp (-a) * Real.exp (-V x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [ha x])
  have hratio : (Real.exp (-a) * (∫ y, Real.exp (-V y)) / (∫ y, Real.exp (-W y))) *
      (Real.exp (-V x) / (∫ y, Real.exp (-V y))) =
        Real.exp (-a) * Real.exp (-V x) / (∫ y, Real.exp (-W y)) := by
    field_simp
  rw [hratio]
  exact div_le_div_of_nonneg_right he hZW.le

/-- Holley–Stroock bounded perturbation: adding a bounded measurable potential multiplies a
logarithmic Sobolev constant by at most the exponential of the potential's oscillation. -/
theorem log_sobolev_inequality_gibbs_measure_add {d : ℕ}
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Integrable (fun x ↦ Real.exp (-V x))) (hVm : Measurable V)
    (hψ : Measurable ψ) {a b C : ℝ} (hab : ∀ x, ψ x ∈ Icc a b)
    (hC : 0 ≤ C) (hLS : (gibbsMeasure V).LogSobolevInequality C) :
    (gibbsMeasure (V + ψ)).LogSobolevInequality (Real.exp (b - a) * C) := by
  have hW : Integrable (fun x ↦ Real.exp (-(V + ψ) x)) := by
    refine (hV.const_mul (Real.exp (-a))).mono'
      ((hVm.add hψ).neg.exp.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Pi.add_apply]
    exact Real.exp_le_exp.2 (by linarith [(hab x).1])
  have hZV : 0 < ∫ x, Real.exp (-V x) := integral_exp_pos hV
  have hZW : 0 < ∫ x, Real.exp (-(V + ψ) x) := integral_exp_pos hW
  have := is_probability_measure_gibbs_measure hV
  have := is_probability_measure_gibbs_measure hW
  have hν := gibbs_measure_le_smul_of_sub_le hV hW (a := a)
    (fun x ↦ by simpa using (hab x).1)
  have hμ := gibbs_measure_le_smul_of_sub_le hW hV (a := -b)
    (fun x ↦ by dsimp only [Pi.add_apply]; linarith [(hab x).2])
  simp only [neg_neg] at hμ
  have h := log_sobolev_inequality_of_measure_le_smul (gibbsMeasure V) (gibbsMeasure (V + ψ))
    (A := Real.exp (-a) * (∫ x, Real.exp (-V x)) / (∫ x, Real.exp (-(V + ψ) x)))
    (B := Real.exp b * (∫ x, Real.exp (-(V + ψ) x)) / (∫ x, Real.exp (-V x)))
    (by positivity) (by positivity) hC hν hμ hLS
  have heq : (Real.exp (-a) * (∫ x, Real.exp (-V x)) / (∫ x, Real.exp (-(V + ψ) x))) *
      (Real.exp b * (∫ x, Real.exp (-(V + ψ) x)) / (∫ x, Real.exp (-V x))) * C =
        Real.exp (b - a) * C := by
    calc _ = Real.exp (-a) * Real.exp b * C := by field_simp
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  rw [heq] at h
  exact h

end CKSD
