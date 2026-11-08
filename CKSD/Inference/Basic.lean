module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.StrongLaw
public import Mathlib.Tactic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Statistical models and convergence interfaces

Basic vocabulary of the CKSD formalization: weak convergence of finite measures, convergence in
law and in probability, empirical measures and averages, i.i.d. sequences, real densities,
moments, sufficient and complete statistics, randomized tests, and randomized decision rules.

## Main definitions

* `CKSD.TendstoWeakly μ ν`: finite measures `μ n` converge weakly to a finite measure `ν`, i.e.
  `∫ f dμ n → ∫ f dν` for every bounded continuous real `f`. For finite measures this is
  convergence in Mathlib's `MeasureTheory.FiniteMeasure` topology
  (`MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`).
* `CKSD.TendstoInDistribution μ X ν`: the laws `μ.map (X n)` converge weakly to `ν`. Mathlib's
  `MeasureTheory.TendstoInDistribution` is the same notion for almost everywhere measurable
  random variables, phrased with `ProbabilityMeasure` and allowing different probability spaces.
* `CKSD.TendstoInProbabilityConst μ X c`: `μ {ε < dist (X n) c} → 0` for every `ε > 0`. For a
  finite measure it is Mathlib's `MeasureTheory.TendstoInMeasure` to the constant `c`
  (`CKSD.tendstoInProbabilityConst_iff_tendstoInMeasure`).
* `CKSD.cdf P t = P.real (Iic t)`; for a probability measure it is `ProbabilityTheory.cdf P t`.
* `CKSD.variance P f = ∫ (f - ∫ f dP) ^ 2 dP`, the measure-first form of
  `ProbabilityTheory.variance f P` (they agree for almost everywhere measurable `f`, see
  `CKSD.variance_eq_mathlib`); `CKSD.covariance P f g` is `ProbabilityTheory.covariance f g P`.
* `CKSD.IsStatisticalTest φ`: a measurable randomized test `φ : X → [0, 1]`;
  `CKSD.thresholdTest T c γ` is the one-sided test rejecting when `c < T`, with randomization
  `γ` on `T = c`.
* `CKSD.IsSufficientStatistic`, `CKSD.IsCompleteStatistic`, `CKSD.IsBoundedlyCompleteStatistic`,
  `CKSD.IsUnbiasedEstimator`, `CKSD.IsUniformlyMostPowerfulTest`, and `CKSD.risk` of a
  `CKSD.RandomizedDecisionRule` (a Markov kernel from observations to actions).

## Main results

* `CKSD.TendstoWeakly.isProbabilityMeasure`: a weak limit of probability measures is a
  probability measure.
* `CKSD.tendstoInProbabilityConst_iff_tendstoInMeasure`.
* `CKSD.IsStatisticalTest.integrable`, `CKSD.IsStatisticalTest.integral_mem_Icc`: a test is
  integrable for every finite measure, with mean in `[0, 1]` under a probability measure.

## Conventions

Real-valued integrals, risks, and moments are Bochner integrals; theorems using them carry the
integrability hypotheses that exclude the junk value `0` of a nonintegrable function.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Weak convergence of finite measures: `∫ f dμ n → ∫ f dν` for every bounded continuous real
function `f`. Finiteness of all measures is part of the predicate, so totalized Bochner integrals
cannot identify an infinite-mass law with the zero measure. For finite measures this is
convergence in Mathlib's `FiniteMeasure` topology. -/
structure TendstoWeakly {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop where
  /-- Each measure in the sequence is finite. -/
  finite : ∀ n, IsFiniteMeasure (μ n)
  /-- The limit measure is finite. -/
  finite_limit : IsFiniteMeasure ν
  /-- Integrals of bounded continuous real functions converge. -/
  integral_tendsto : ∀ f : BoundedContinuousFunction E ℝ,
    Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- A weak-convergence hypothesis can be applied to a bounded continuous test function. -/
instance {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {μ : ℕ → Measure E} {ν : Measure E} :
    CoeFun (TendstoWeakly μ ν) (fun _ ↦ ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))) where
  coe h := h.integral_tendsto

/-- For finite measures, convergence of the bounded continuous integrals gives weak convergence. -/
theorem TendstoWeakly.of_forall_integral_tendsto {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] {μ : ℕ → Measure E} {ν : Measure E}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (h : ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))) :
    TendstoWeakly μ ν :=
  ⟨fun _ ↦ inferInstance, inferInstance, h⟩

/-- On finite measures, weak convergence is equivalent to convergence of test integrals. -/
theorem TendstoWeakly.iff_forall_integral_tendsto {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] {μ : ℕ → Measure E} {ν : Measure E}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν] :
    TendstoWeakly μ ν ↔ ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) :=
  ⟨fun h ↦ h.integral_tendsto, TendstoWeakly.of_forall_integral_tendsto⟩

/-- Convergence in law of random variables `X n` on one probability space: the image laws
`μ.map (X n)` converge weakly to `ν`. This is the measure-level counterpart of Mathlib's
`MeasureTheory.TendstoInDistribution`, which uses `ProbabilityMeasure` values. -/
abbrev TendstoInDistribution {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (ν : Measure E) : Prop :=
  TendstoWeakly (fun n ↦ μ.map (X n)) ν

/-- Convergence in probability to a constant: `μ {ω | ε < dist (X n ω) x} → 0` for every
`ε > 0`. For a finite measure this is Mathlib's `TendstoInMeasure μ X atTop (fun _ ↦ x)`
(`tendstoInProbabilityConst_iff_tendstoInMeasure`). -/
def TendstoInProbabilityConst {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ μ.real {ω | ε < dist (X n ω) x}) atTop (𝓝 0)

/-- Boundedness in probability (uniform tightness) of a real sequence: for every `ε > 0` there is
`C > 0` with `μ {C < |X n|} ≤ ε` for all large `n`. -/
def IsBoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < |X n ω|} ≤ ε

/-- The empirical measure; the empty sample gives the zero measure. -/
def empiricalMeasure {E : Type*} [MeasurableSpace E] (n : ℕ) (x : Fin n → E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The empirical average of the first `n` observations of a sequence. -/
def sampleAverage {Ω E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- A measurable independent sequence with common law `P`. -/
def IsIndependentIdenticallyDistributed {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (P : Measure E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, μ.map (X i) = P

/-- The distribution function `t ↦ P (-∞, t]` of a finite measure on the line. For a probability
measure it is Mathlib's `ProbabilityTheory.cdf P` (`CKSD.cdf_eq_mathlib`). -/
def cdf (P : Measure ℝ) (t : ℝ) : ℝ := P.real (Iic t)

/-- `f` is a real density of `P` with respect to `μ`: `f` is measurable, `μ`-almost everywhere
nonnegative, and `P = μ.withDensity (ofReal ∘ f)`. -/
def HasDensity {X : Type*} [MeasurableSpace X]
    (P μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- The centred second moment `∫ (f - ∫ f dP) ^ 2 dP`, with the measure first. It is Mathlib's
`ProbabilityTheory.variance f P` for almost everywhere measurable `f` (`CKSD.variance_eq_mathlib`);
it is used with second-moment hypotheses. -/
def variance {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → ℝ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P

/-- Mathlib's `ProbabilityTheory.covariance f g P`, with the measure first. -/
abbrev covariance {X : Type*} [MeasurableSpace X]
    (P : Measure X) (f g : X → ℝ) : ℝ :=
  ProbabilityTheory.covariance f g P

/-- A randomized test: a measurable function `φ : X → [0, 1]`, the probability of rejection at
each observation. -/
def IsStatisticalTest {X : Type*} [MeasurableSpace X] (φ : X → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1

/-- The one-sided randomized test in a statistic `T`: reject when `c < T x`, reject with
probability `γ` when `T x = c`, and accept otherwise. -/
def thresholdTest {X α : Type*} [LinearOrder α] (T : X → α) (c : α) (γ : ℝ) (x : X) : ℝ :=
  if c < T x then 1 else if T x = c then γ else 0

/-- An unbiased estimator of `g`: a measurable `δ` that is integrable under every `P θ` with
mean `g θ`. -/
def IsUnbiasedEstimator {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (δ : X → ℝ) (g : Θ → ℝ) : Prop :=
  Measurable δ ∧ ∀ θ, Integrable δ (P θ) ∧ (∫ x, δ x ∂P θ) = g θ

/-- Sufficiency of a measurable statistic `T`: one Markov kernel `K` (the conditional law of the
observation given `T`) disintegrates every joint law of `(T, X)`, i.e.
`(P θ).map (T, id) = (P θ).map T ⊗ₘ K` for all `θ`. -/
def IsSufficientStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
    ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K

/-- Completeness of a statistic `T`: every measurable `g` with `g ∘ T` integrable and of mean zero
under every `P θ` vanishes `P θ`-almost everywhere on the range of `T`. -/
def IsCompleteStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g →
    (∀ θ, Integrable (g ∘ T) (P θ) ∧ (∫ x, g (T x) ∂P θ) = 0) →
    ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- Bounded completeness of a statistic `T`: completeness restricted to bounded measurable `g`. -/
def IsBoundedlyCompleteStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g → (∃ C, ∀ s, |g s| ≤ C) →
    (∀ θ, (∫ x, g (T x) ∂P θ) = 0) → ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- A uniformly most powerful level-`α` test of `H₀` against `H₁`: `φ` has level `α` on `H₀`
and at every `θ ∈ H₁` its power is at least that of every level-`α` test. -/
def IsUniformlyMostPowerfulTest {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    ∀ ψ, IsStatisticalTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- A uniformly most powerful unbiased level-`α` test: `φ` has level `α` on `H₀`, power at least
`α` on `H₁`, and maximal power on `H₁` among all such unbiased level-`α` tests. -/
def IsUniformlyMostPowerfulUnbiasedTest {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    (∀ θ ∈ H₁, α ≤ ∫ x, φ x ∂P θ) ∧
    ∀ ψ, IsStatisticalTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      (∀ θ ∈ H₁, α ≤ ∫ x, ψ x ∂P θ) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- A randomized decision rule: a Markov kernel from observations to actions. -/
abbrev RandomizedDecisionRule (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] :=
  {K : Kernel X A // IsMarkovKernel K}

/-- The risk `R(θ, δ) = ∫∫ L(θ, a) dδ(x)(a) dP θ(x)` of a randomized decision rule. It is a
Bochner integral, used for integrable (typically bounded) losses. -/
def risk {Θ X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Θ → Measure X) (L : Θ → A → ℝ) (δ : RandomizedDecisionRule X A) (θ : Θ) : ℝ :=
  ∫ x, ∫ a, L θ a ∂δ.val x ∂P θ

/-- A weak limit of probability measures is a probability measure. -/
theorem TendstoWeakly.isProbabilityMeasure {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {μ : ℕ → Measure E} {ν : Measure E} (h : TendstoWeakly μ ν)
    [∀ n, IsProbabilityMeasure (μ n)] : IsProbabilityMeasure ν := by
  have := h.finite_limit
  have h1 := h (BoundedContinuousFunction.const E 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, probReal_univ, smul_eq_mul,
    mul_one] at h1
  have hν : ν.real univ = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← measureReal_def, hν, ENNReal.ofReal_one]

/-- For a finite measure, convergence in probability to a constant is Mathlib's convergence in
measure to the constant function. -/
theorem tendstoInProbabilityConst_iff_tendstoInMeasure {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → E} {c : E} :
    TendstoInProbabilityConst μ X c ↔ TendstoInMeasure μ X atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · exact squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono fun ω (hω : ε ≤ dist (X n ω) c) ↦
        (show ε / 2 < dist (X n ω) c by linarith)) (h (ε / 2) (half_pos hε))
  · exact squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono fun ω (hω : ε < dist (X n ω) c) ↦ (le_of_lt hω : ε ≤ _)) (h ε hε)

namespace IsStatisticalTest

variable {X : Type*} [MeasurableSpace X] {φ : X → ℝ}

/-- A test takes nonnegative values. -/
theorem nonneg (hφ : IsStatisticalTest φ) (x : X) : 0 ≤ φ x := (hφ.2 x).1

/-- A test takes values at most one. -/
theorem le_one (hφ : IsStatisticalTest φ) (x : X) : φ x ≤ 1 := (hφ.2 x).2

/-- A test is bounded by one in absolute value. -/
theorem abs_le_one (hφ : IsStatisticalTest φ) (x : X) : |φ x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hφ.nonneg x], hφ.le_one x⟩

/-- A constant in `[0, 1]` is a test. -/
theorem const {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) : IsStatisticalTest (fun _ : X ↦ c) :=
  ⟨measurable_const, fun _ ↦ hc⟩

/-- The complementary test `1 - φ`. -/
theorem one_sub (hφ : IsStatisticalTest φ) : IsStatisticalTest (fun x ↦ 1 - φ x) :=
  ⟨measurable_const.sub hφ.1, fun x ↦ ⟨by linarith [hφ.le_one x], by linarith [hφ.nonneg x]⟩⟩

/-- A test is integrable for every finite measure. -/
theorem integrable (hφ : IsStatisticalTest φ) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable φ μ :=
  Integrable.of_bound (C := 1) hφ.1.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hφ.abs_le_one x)

/-- The product of a test with an integrable function is integrable. -/
theorem integrable_mul (hφ : IsStatisticalTest φ) {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) : Integrable (fun x ↦ φ x * f x) μ :=
  hf.bdd_mul (c := 1) hφ.1.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hφ.abs_le_one x)

/-- The mean of a test is nonnegative. -/
theorem integral_nonneg (hφ : IsStatisticalTest φ) (μ : Measure X) : 0 ≤ ∫ x, φ x ∂μ :=
  MeasureTheory.integral_nonneg hφ.nonneg

/-- The mean of a test under a probability measure is at most one. -/
theorem integral_le_one (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, φ x ∂μ ≤ 1 :=
  (integral_mono (hφ.integrable μ) (integrable_const 1) hφ.le_one).trans (by simp)

/-- The mean of a test under a probability measure lies in `[0, 1]`. -/
theorem integral_mem_Icc (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, φ x ∂μ ∈ Icc (0 : ℝ) 1 :=
  ⟨hφ.integral_nonneg μ, hφ.integral_le_one μ⟩

/-- The mean of the complementary test `1 - φ` under a probability measure. -/
theorem integral_one_sub (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, (1 - φ x) ∂μ = 1 - ∫ x, φ x ∂μ := by
  rw [integral_sub (integrable_const 1) (hφ.integrable μ)]
  simp

end IsStatisticalTest

/-- A threshold test with randomization `γ ∈ [0, 1]` in a measurable statistic is a test. -/
theorem isStatisticalTest_thresholdTest {X α : Type*} [MeasurableSpace X] [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {T : X → α} (hT : Measurable T) (c : α) {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) :
    IsStatisticalTest (thresholdTest T c γ) := by
  refine ⟨Measurable.ite (hT measurableSet_Ioi) measurable_const
    (Measurable.ite (hT (isClosed_singleton.measurableSet)) measurable_const measurable_const),
    fun x ↦ ?_⟩
  unfold thresholdTest
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ
  · exact ⟨le_rfl, zero_le_one⟩

end CKSD
