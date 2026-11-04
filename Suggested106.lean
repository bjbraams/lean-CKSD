module

public import Suggested105

/-!
# Suggested statements for Section 106

Sources: `GAPS.md`, `SYNOPSIS106.md`, `STRUCTURE106.md`.
Every proof is admitted. Process limits that require Skorokhod-space choices
are represented only by the scalar marginal assertions explicitly identified.

Not represented: 106.6–7 (spectral-estimator and Kalman process interfaces),
106.11 (conditional moving-block resampling), 106.16–17 (Szegő prediction
and ARMA likelihoods), 106.21 (equivalence of Gaussian process laws),
106.24 (Matérn/Bessel functions and mean-square derivative fields), 106.30
and 106.34 (multiplicative intensities and counting-process integrals),
106.39 (a Brownian bridge functional limit), 106.41 (unbounded SPRT
exponential identities), 106.44 (Lorden delay and optimal stopping),
106.47 (generalized Pareto threshold limits), 106.49 (second-order regular variation and order-statistic conventions).
The partial statements for 106.18, 106.46, 106.48, and 106.50 do not give the
boundary/nonexistence, full classification, dependent-extremal-index, or
threshold-existence assertions of those entries.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section106

attribute [local instance] Classical.propDecidable

/-- Sample autocovariance using the sample mean and divisor `n`. -/
def acov {Ω : Type*} (X : ℕ → Ω → ℝ) (lag n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n - lag),
    (X (i + lag) ω - average X n ω) * (X i ω - average X n ω)) / n

/-- The risk-set cardinality at the `i`th observed time. -/
def riskSet {Ω : Type*} (T C : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter fun j ↦ min (T i ω) (C i ω) ≤ min (T j ω) (C j ω)).card

/-- Nelson–Aalen estimator, expressed as a sum over individual observed failures. -/
def nelsonAalen {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    (riskSet T C n i ω : ℝ)⁻¹ else 0

/-- Kaplan–Meier product, with one factor for each individual observed failure. -/
def kaplanMeier {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    1 - (riskSet T C n i ω : ℝ)⁻¹ else 1

/-- GAPS 106.1: triangular-array martingale central limit theorem. -/
theorem gap106_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ha : ∀ n j, Measurable[F n (j + 1)] (X n j))
    (h2 : ∀ n j, MemLp (X n j) 2 μ)
    (h0 : ∀ n j, μ[X n j | F n j] =ᵐ[μ] fun _ ↦ 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hvar : InProbability μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n), μ[(fun ω ↦ X n j ω ^ 2) | F n j] ω) v)
    (hlin : ∀ ε > 0, InProbability μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n),
        μ[(fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0) | F n j] ω) 0) :
    InLaw μ (fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω)
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.2, Wold decomposition of a stationary sequence in a real Hilbert space. -/
theorem gap106_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (X : ℤ → H)
    (hstat : ∀ s t, inner ℝ (X s) (X t) = inner ℝ (X (s - t)) (X 0)) :
    let past := fun t ↦ (Submodule.span ℝ {x | ∃ s : ℤ, s ≤ t ∧ x = X s}).topologicalClosure;
    ∀ (P : ℤ → H →L[ℝ] H),
    ∀ (hproj : ∀ t x, P t x ∈ past t ∧ ∀ y ∈ past t, inner ℝ (x - P t x) y = 0),
    let e := fun t ↦ X t - P (t - 1) (X t);
    ∀ (he : 0 < ‖e 0‖),
    ∃ (a : ℕ → ℝ) (V : ℤ → H), a 0 = 1 ∧ Summable (fun j ↦ a j ^ 2) ∧
      (∀ t s, V t ∈ past s) ∧ (∀ t s, inner ℝ (V t) (e s) = 0) ∧
      ∀ t, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j • e (t - j)) + V t) atTop (𝓝 (X t)) := by
  sorry

/-- GAPS 106.4, independent-observation special case of Bartlett's theorem. -/
theorem gap106_4 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (m : ℕ) :
    InLaw μ (fun n ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * acov X (i.val + 1) n ω / acov X 0 n ω))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry

/-- GAPS 106.12, long-run variance from summable autocovariances. -/
theorem gap106_12 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ)
    (h2 : ∀ t, MemLp (X t) 2 μ) (γ : ℤ → ℝ) (hγ : Summable (fun t ↦ |γ t|))
    (hcov : ∀ s t, covariance μ (X s) (X t) = γ (s - t)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * variance μ (average (fun j ↦ X j) n))
      atTop (𝓝 (∑' h : ℤ, γ h)) := by
  sorry

/-- GAPS 106.14, real Gaussian realization of a positive-definite stationary covariance. -/
theorem gap106_14 (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    ∃ P : Measure (ℤ → ℝ), IsProbabilityMeasure P ∧
      (∀ h : ℤ, P.map (fun x t ↦ x (t + h)) = P) ∧
      ∀ n : ℕ, ∀ t : Fin n → ℤ,
        P.map (fun x ↦ WithLp.toLp 2 (fun i : Fin n ↦ x (t i))) =
          multivariateGaussian 0 (fun i j ↦ γ (t i - t j)) := by
  sorry

/-- GAPS 106.18, finite-variance GARCH series when `alpha + beta < 1`. -/
theorem gap106_18 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1)
    (a₀ a b : ℝ) (ha₀ : 0 < a₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) :
    let V := fun t ω ↦ a₀ * ∑' n : ℕ,
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2);
    let X := fun t ω ↦ Real.sqrt (V t ω) * ε t ω;
    (∀ t, ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2))) ∧
      (∀ t, (∫ ω, V t ω ∂μ) = a₀ / (1 - a - b)) ∧
      (∀ t, ∀ᵐ ω ∂μ, V t ω = a₀ + a * X (t - 1) ω ^ 2 + b * V (t - 1) ω) ∧
      ∀ s t, covariance μ (X s) (X t) = if s = t then a₀ / (1 - a - b) else 0 := by
  sorry

/-- GAPS 106.28, fixed-time Nelson–Aalen CLT for absolutely continuous failure times. -/
theorem gap106_28 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω ↦ (T i ω, C i ω)) (F.prod C₀))
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (hF : F (Ici 0) = 1) (hC : C₀ (Ici 0) = 1)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let Λ := ∫ s in (0 : ℝ)..t, f s / (1 - cdf F s);
    let v := ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    InLaw μ (fun n ω ↦ Real.sqrt n * (nelsonAalen T C n ω t - Λ))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.29, fixed-time Kaplan–Meier CLT under independent censoring. -/
theorem gap106_29 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F C₀ : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure C₀]
    (T C : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω ↦ (T i ω, C i ω)) (F.prod C₀))
    (f : ℝ → ℝ) (hf : HasDensity F volume f)
    (hF : F (Ici 0) = 1) (hC : C₀ (Ici 0) = 1)
    (t : ℝ) (ht : 0 ≤ t) (hrisk : 0 < F (Ici t) * C₀ (Ici t)) :
    let S := 1 - cdf F t;
    let v := S ^ 2 * ∫ s in (0 : ℝ)..t, f s / ((1 - cdf F s) ^ 2 * C₀.real (Ici s));
    InLaw μ (fun n ω ↦ Real.sqrt n * (kaplanMeier T C n ω t - S))
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.37, Wald's stopped-sum identity under the past/future independence condition. -/
theorem gap106_37_wald {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (hX : Integrable id P)
    (N : Ω → ℕ) (hN : Measurable N) (hNi : Integrable (fun ω ↦ (N ω : ℝ)) μ)
    (hpast : ∀ i : ℕ, IndepFun (X i) (fun ω ↦ decide (i < N ω)) μ) :
    Integrable (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ ∧
      (∫ ω, ∑ i ∈ Finset.range (N ω), X i ω ∂μ) =
        (∫ ω, (N ω : ℝ) ∂μ) * ∫ x, x ∂P := by
  sorry

/-- GAPS 106.38: infinite-horizon Ville inequality, including a supremum not attained. -/
theorem gap106_38 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (M : ℕ → Ω → ℝ)
    (hsuper : Supermartingale M F μ) (hpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ M n ω)
    (hinit : M 0 ≤ᵐ[μ] fun _ ↦ 1) (α : ℝ) (hα : α ∈ Ioo 0 1) :
    μ {ω | ENNReal.ofReal (1 / α) ≤ ⨆ n : ℕ, ENNReal.ofReal (M n ω)} ≤ ENNReal.ofReal α := by
  sorry

/-- GAPS 106.42: Anscombe's theorem for an observation-dependent random sample size. -/
theorem gap106_42 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (N : ℕ → Ω → ℕ) (hN : ∀ n, Measurable (N n))
    (hpos : ∀ n ω, 0 < N n ω) (k : ℝ) (hk : 0 < k)
    (hratio : InProbability μ (fun n ω ↦ (N n ω : ℝ) / n) k) :
    InLaw μ (fun n ω ↦ Real.sqrt (N n ω) *
      (average X (N n ω) ω - ∫ x, x ∂P) / Real.sqrt (variance P id)) (gaussianReal 0 1) := by
  sorry

/-- GAPS 106.46, the regularly varying positive-tail sufficient condition for a Fréchet limit. -/
theorem gap106_46 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (γ : ℝ) (hγ : 0 < γ)
    (hpos : ∀ t : ℝ, cdf P t < 1)
    (hrv : ∀ x > 0, Tendsto (fun t ↦ (1 - cdf P (t * x)) / (1 - cdf P t))
      atTop (𝓝 (Real.rpow x (-1 / γ)))) :
    let a := fun n : ℕ ↦ sInf {t | 1 - (n : ℝ)⁻¹ ≤ cdf P t};
    ∀ x > 0, Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ a n * x}) atTop
      (𝓝 (Real.exp (-Real.rpow x (-1 / γ)))) := by
  sorry

/-- GAPS 106.50, finite-intensity exceedance limit; also the independent part of 106.48. -/
theorem gap106_50 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (u : ℕ → ℝ) (τ : ℝ≥0)
    (htail : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - cdf P (u n))) atTop (𝓝 (τ : ℝ))) :
    Tendsto (fun n ↦ μ.real {ω | ∀ i < n, X i ω ≤ u n}) atTop (𝓝 (Real.exp (-τ))) ∧
      InLaw μ (fun n ω ↦ ((Finset.range n).filter (fun i ↦ u n < X i ω)).card)
        (poissonMeasure τ) := by
  sorry

end CKSD.Section106
