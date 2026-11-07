module

public import CKSD.Asymptotics.Statistics
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic

/-!
# Likelihood-ratio, Wald, and score tests

The three classical test statistics of a simple null hypothesis in a scalar smooth model,
with their common chi-squared limit under the null and their common noncentral chi-squared
limit under local alternatives. The limit laws are TauCeti's chi-squared and noncentral
chi-squared measures. The estimators are functions of the sample of size `n`, so that the
laws under the null and under local alternatives are product measures on `Fin n → E`.
Sources: GAPS 102.11, with the hypotheses of GAPS 102.3 and the DQM condition of GAPS 102.13.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Wald statistic of a scalar simple null `θ = θ₀`, with information evaluated at the estimate:
`n (T - θ₀)² I(T)`. -/
def scalarWaldStatistic (I : ℝ → ℝ) (n : ℕ) (estimate θ₀ : ℝ) : ℝ :=
  n * (estimate - θ₀) ^ 2 * I estimate

/-- Rao score statistic of a scalar simple null: `ℓₙ'(θ₀)² / (n I(θ₀))`, written with the
derivative of the sample log likelihood. -/
def scalarScoreStatistic {E : Type*} (f : ℝ → E → ℝ) (I : ℝ → ℝ) {n : ℕ} (x : Fin n → E)
    (θ₀ : ℝ) : ℝ :=
  deriv (sampleLogLikelihood f x) θ₀ ^ 2 / (n * I θ₀)

/-- GAPS 102.11, null part, for a scalar parameter and the simple null `Θ₀ = {θ₀}`
(so `q = k = 1`, `c(θ) = θ - θ₀`, and the restricted maximizer is `θ₀`). Under the
hypotheses of 102.3 at `θ₀` with Fisher information continuous at `θ₀`, and for consistent
global maximizers `T n` of the sample log likelihood, the likelihood-ratio, Wald, and score
statistics each converge in law to `χ²₁` under `P θ₀`, and the Wald and score statistics differ
from the likelihood-ratio statistic by `o_P(1)`. Composite nulls with `q < k` are outside
this scope. -/
theorem tendstoWeakly_likelihoodRatio_wald_score_chiSquared
    {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x)))
    (θ₀ : ℝ) (hIc : ContinuousAt (fisherInformation P f) θ₀)
    (hI : 0 < fisherInformation P f θ₀) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M (P θ₀))
    (henv : ∀ x θ, |θ - θ₀| < r →
      |deriv (deriv (deriv (fun t ↦ Real.log (f t x)))) θ| ≤ M x)
    (hscore : MemLp (likelihoodScore f θ₀) 2 (P θ₀))
    (hmean : (∫ x, likelihoodScore f θ₀ x ∂P θ₀) = 0)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ Real.log (f t x))) θ₀) (P θ₀))
    (hinfo : (∫ x, deriv (deriv (fun t ↦ Real.log (f t x))) θ₀ ∂P θ₀) =
      -fisherInformation P f θ₀)
    (T : ∀ n, (Fin n → E) → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
      (fun n x ↦ T n x - θ₀))
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀), ∀ θ,
      sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x (T n x)) :
    let I := fisherInformation P f;
    let LR := fun n (x : Fin n → E) ↦
      likelihoodRatioStatistic (sampleLogLikelihood f x (T n x)) (sampleLogLikelihood f x θ₀);
    let W := fun n (x : Fin n → E) ↦ scalarWaldStatistic I n (T n x) θ₀;
    let S := fun n (x : Fin n → E) ↦ scalarScoreStatistic f I x θ₀;
    TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (LR n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (W n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (S n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
        (fun n x ↦ LR n x - W n x) ∧
      TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
        (fun n x ↦ LR n x - S n x) := by
  sorry

/-- GAPS 102.11, local-alternative part, in the scalar simple-null scope of
`tendstoWeakly_likelihoodRatio_wald_score_chiSquared`. If in addition the model is DQM at `θ₀`
with the likelihood score, then under `P (θ₀ + h / √n)` each of the three statistics converges
in law to the noncentral `χ²₁` with noncentrality `h² I(θ₀)`. -/
theorem tendstoWeakly_likelihoodRatio_wald_score_noncentralChiSquared
    {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x)))
    (θ₀ : ℝ) (hIc : ContinuousAt (fisherInformation P f) θ₀)
    (hI : 0 < fisherInformation P f θ₀) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M (P θ₀))
    (henv : ∀ x θ, |θ - θ₀| < r →
      |deriv (deriv (deriv (fun t ↦ Real.log (f t x)))) θ| ≤ M x)
    (hscore : MemLp (likelihoodScore f θ₀) 2 (P θ₀))
    (hmean : (∫ x, likelihoodScore f θ₀ x ∂P θ₀) = 0)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ Real.log (f t x))) θ₀) (P θ₀))
    (hinfo : (∫ x, deriv (deriv (fun t ↦ Real.log (f t x))) θ₀ ∂P θ₀) =
      -fisherInformation P f θ₀)
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (θ₀ + h) x) - Real.sqrt (f θ₀ x) -
        h / 2 * likelihoodScore f θ₀ x * Real.sqrt (f θ₀ x)) ^ 2 ∂ν) (fun h : ℝ ↦ h ^ 2))
    (T : ∀ n, (Fin n → E) → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
      (fun n x ↦ T n x - θ₀))
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀), ∀ θ,
      sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x (T n x)) (h : ℝ) :
    let I := fisherInformation P f;
    let LR := fun n (x : Fin n → E) ↦
      likelihoodRatioStatistic (sampleLogLikelihood f x (T n x)) (sampleLogLikelihood f x θ₀);
    let W := fun n (x : Fin n → E) ↦ scalarWaldStatistic I n (T n x) θ₀;
    let S := fun n (x : Fin n → E) ↦ scalarScoreStatistic f I x θ₀;
    let Q := fun n : ℕ ↦ Measure.pi fun _ : Fin n ↦ P (θ₀ + h / Real.sqrt n);
    let L := TauCeti.Probability.noncentralChiSquaredMeasure 1 (Real.toNNReal (h ^ 2 * I θ₀));
    TendstoWeakly (fun n ↦ (Q n).map (LR n)) L ∧
      TendstoWeakly (fun n ↦ (Q n).map (W n)) L ∧
      TendstoWeakly (fun n ↦ (Q n).map (S n)) L := by
  sorry

/-- The Wald statistic vanishes at the null value. -/
@[simp] theorem scalarWaldStatistic_self (I : ℝ → ℝ) (n : ℕ) (θ₀ : ℝ) :
    scalarWaldStatistic I n θ₀ θ₀ = 0 := by
  simp [scalarWaldStatistic]

end CKSD
