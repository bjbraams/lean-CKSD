module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.TightNormed
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

Basic vocabulary of the CKSD formalization: convergence in law and in probability, boundedness
in probability, empirical measures and averages, i.i.d. sequences, real densities,
sufficient and complete statistics, randomized tests, and randomized decision rules. Variances,
covariances, and distribution functions are Mathlib's `ProbabilityTheory.variance`,
`ProbabilityTheory.covariance`, and `ProbabilityTheory.cdf`. Convergence in law of random
variables is Mathlib's `MeasureTheory.TendstoInDistribution`; a sequence `X n` on one probability
space `μ` converging in law to a probability measure `ν` is written
`TendstoInDistribution X atTop id (fun _ ↦ μ) ν`. Weak convergence of probability measures that
are not presented as laws is convergence in Mathlib's `MeasureTheory.ProbabilityMeasure`
topology, characterized by `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.

## Main definitions

* `CKSD.IsBoundedInProbability μ X`: a real sequence is bounded in probability (uniformly
  tight), measured by the outer measure so that no measurability is required.
* `CKSD.IsStatisticalTest φ`: a measurable randomized test `φ : X → [0, 1]`;
  `CKSD.thresholdTest T c γ` is the one-sided test rejecting when `c < T`, with randomization
  `γ` on `T = c`.
* `CKSD.IsSufficientStatistic`, `CKSD.IsCompleteStatistic`, `CKSD.IsBoundedlyCompleteStatistic`,
  `CKSD.IsUnbiasedEstimator`, `CKSD.IsUniformlyMostPowerfulTest`, and `CKSD.risk` of a
  `CKSD.RandomizedDecisionRule` (a Markov kernel from observations to actions).

## Main results

* `CKSD.is_bounded_in_probability_iff_is_tight_measure_set`: for almost everywhere measurable
  sequences, boundedness in probability is tightness (Mathlib's `MeasureTheory.IsTightMeasureSet`)
  of the set of laws.
* `CKSD.tendsto_in_distribution_id_iff`: convergence in distribution to a law, with the identity
  as limit random variable, is convergence in the `ProbabilityMeasure` topology.
* `CKSD.tendsto_in_distribution_of_map_eq`: the limit random variable of convergence in
  distribution matters only through its law.
* `CKSD.tendsto_in_measure_iff_measure_real_lt_dist`: for a finite measure, convergence in
  measure (Mathlib's `MeasureTheory.TendstoInMeasure`) with strict inequalities and real-valued
  measures.
* `CKSD.IsStatisticalTest.integrable`, `CKSD.IsStatisticalTest.integral_mem_icc`: a test is
  integrable for every finite measure, with mean in `[0, 1]` under a probability measure.
* `CKSD.is_probability_measure_empirical_measure`, `CKSD.integrable_of_has_density`: the empirical
  measure of a nonempty sample is a probability measure, and a real density is integrable.

## Conventions

Convergence in probability of `X n` to a constant `c` is Mathlib's
`TendstoInMeasure μ X atTop (fun _ ↦ c)`.
Real-valued integrals and risks are Bochner integrals; theorems using them carry the
integrability hypotheses that exclude the junk value `0` of a nonintegrable function.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Convergence in distribution depends on the limit random variable only through its law. -/
theorem tendsto_in_distribution_of_map_eq {ι Ω' Ω'' E : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X : (i : ι) → Ω i → E} {l : Filter ι} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z μ μ') (hW : AEMeasurable W μ'')
    (hWZ : μ''.map W = μ'.map Z) :
    TendstoInDistribution X l W μ μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    have hP : (⟨μ''.map W, inferInstance⟩ : ProbabilityMeasure E) = ⟨μ'.map Z, inferInstance⟩ :=
      Subtype.ext hWZ
    rw [hP]
    exact h.tendsto

/-- Convergence in distribution to a law `ν`, with the identity as limit random variable, is
convergence of the laws to `ν` in Mathlib's `ProbabilityMeasure` topology. -/
theorem tendsto_in_distribution_id_iff {ι E : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {ν : Measure E}
    [IsProbabilityMeasure ν] {X : (i : ι) → Ω i → E} {l : Filter ι} :
    TendstoInDistribution X l id μ ν ↔ (∀ i, AEMeasurable (X i) (μ i)) ∧
      Tendsto (β := ProbabilityMeasure E) (fun i ↦ ⟨(μ i).map (X i), inferInstance⟩) l
        (𝓝 ⟨ν, inferInstance⟩) := by
  have hν : (⟨ν.map id, inferInstance⟩ : ProbabilityMeasure E) = ⟨ν, inferInstance⟩ :=
    Subtype.ext Measure.map_id
  constructor
  · intro h
    have h' := h.tendsto
    rw [hν] at h'
    exact ⟨h.forall_aemeasurable, h'⟩
  · rintro ⟨hX, h⟩
    refine ⟨hX, aemeasurable_id, ?_⟩
    rw [hν]
    exact h

/-- Chi-squared laws with natural-number degrees of freedom are probability measures; this
instance lets them serve as limits in `MeasureTheory.TendstoInDistribution`. -/
instance isProbabilityMeasure_chiSquaredMeasure_natCast (k : ℕ) :
    IsProbabilityMeasure (TauCeti.Probability.chiSquaredMeasure (k : ℝ)) :=
  TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure k.cast_nonneg

/-- The chi-squared law with one degree of freedom is a probability measure. -/
instance isProbabilityMeasure_chiSquaredMeasure_one :
    IsProbabilityMeasure (TauCeti.Probability.chiSquaredMeasure 1) :=
  TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure zero_le_one

/-- Boundedness in probability (uniform tightness) of a real sequence: for every `ε > 0` there is
`C > 0` with `μ {C < |X n|} ≤ ε` for all large `n`. The sets `{C < |X n|}` are measured by the
outer measure, so no measurability of `X n` is required; this serves the stochastic `O_P` algebra
of possibly nonmeasurable sequences. For almost everywhere measurable `X n` and finite `μ` it is
tightness of the laws, Mathlib's `IsTightMeasureSet (range fun n ↦ μ.map (X n))`
(`CKSD.is_bounded_in_probability_iff_is_tight_measure_set`). -/
def IsBoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < |X n ω|} ≤ ε

/-- For almost everywhere measurable real random variables under a finite measure, boundedness in
probability is tightness of the set of their laws (Mathlib's `MeasureTheory.IsTightMeasureSet`).
Eventual bounds suffice for tightness of the whole sequence since each finite measure on `ℝ` is
tight. -/
theorem is_bounded_in_probability_iff_is_tight_measure_set {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} (hX : ∀ n, AEMeasurable (X n) μ) :
    IsBoundedInProbability μ X ↔ IsTightMeasureSet (range fun n ↦ μ.map (X n)) := by
  rw [isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt]
  have hmap : ∀ (r : ℝ) n, μ.map (X n) {x | r < ‖x‖} = μ {ω | r < |X n ω|} := fun r n ↦ by
    rw [Measure.map_apply_of_aemeasurable (hX n)
      (measurableSet_lt measurable_const measurable_norm)]
    simp only [preimage_ofPred_eq, Real.norm_eq_abs]
  simp_rw [hmap]
  have hanti : ∀ n, Antitone fun r : ℝ ↦ μ {ω | r < |X n ω|} := fun n r s hrs ↦
    measure_mono fun ω (hω : s < |X n ω|) ↦ (lt_of_le_of_lt hrs hω : r < |X n ω|)
  constructor
  · intro h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεt
    · exact Eventually.of_forall fun _ ↦ le_top
    obtain ⟨C, -, hC⟩ := h ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
    filter_upwards [eventually_ge_atTop C] with r hr
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hC] with n hn
    calc μ {ω | r < |X n ω|} ≤ μ {ω | C < |X n ω|} := hanti n hr
      _ = ENNReal.ofReal (μ.real {ω | C < |X n ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hn
      _ = ε := ENNReal.ofReal_toReal hεt
  · intro h ε hε
    have hev := (ENNReal.tendsto_nhds_zero.1 h) (ENNReal.ofReal (ε / 2)) (by positivity)
    obtain ⟨C, hCle, hC⟩ := (hev.and (eventually_gt_atTop 0)).exists
    refine ⟨C, hC, ?_⟩
    have hlt : limsup (fun n ↦ μ {ω | C < |X n ω|}) atTop < ENNReal.ofReal ε :=
      hCle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))
    filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
    exact ENNReal.toReal_le_of_le_ofReal hε.le hn.le

/-- The empirical measure; the empty sample gives the zero measure. -/
def empiricalMeasure {E : Type*} [MeasurableSpace E] (n : ℕ) (x : Fin n → E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The empirical measure of a nonempty sample is a probability measure. -/
theorem is_probability_measure_empirical_measure {E : Type*} [MeasurableSpace E] {n : ℕ}
    (hn : 0 < n) (x : Fin n → E) : IsProbabilityMeasure (empiricalMeasure n x) := by
  constructor
  simp [empiricalMeasure]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- The empirical average of the first `n` observations of a sequence. -/
def sampleAverage {Ω E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- A measurable independent sequence with common law `P`. -/
def IsIndependentIdenticallyDistributed {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (P : Measure E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, μ.map (X i) = P

/-- `f` is a real density of `P` with respect to `μ`: `f` is measurable, `μ`-almost everywhere
nonnegative, and `P = μ.withDensity (ofReal ∘ f)`. -/
def HasDensity {X : Type*} [MeasurableSpace X]
    (P μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- A density of a probability law on `ℝ` is integrable. -/
theorem integrable_of_has_density (F : Measure ℝ) [IsProbabilityMeasure F] (f : ℝ → ℝ)
    (hf : HasDensity F volume f) : Integrable f := by
  refine ⟨hf.1.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf.2.1).2 ?_⟩
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hf.2.2]
  simp

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

/-- For a finite measure, convergence in measure is the vanishing of the real-valued measures of
the sets `{ε < dist (f i) (g)}`, with strict inequality; compare Mathlib's
`MeasureTheory.tendstoInMeasure_iff_measureReal_dist`. -/
theorem tendsto_in_measure_iff_measure_real_lt_dist {ι Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] {μ : Measure Ω} [IsFiniteMeasure μ] {l : Filter ι} {f : ι → Ω → E}
    {g : Ω → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i ↦ μ.real {x | ε < dist (f i x) (g x)}) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · exact squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono fun ω (hω : ε < dist (f n ω) (g ω)) ↦ (le_of_lt hω : ε ≤ _))
      (h ε hε)
  · exact squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono fun ω (hω : ε ≤ dist (f n ω) (g ω)) ↦
        (show ε / 2 < dist (f n ω) (g ω) by linarith)) (h (ε / 2) (half_pos hε))

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
theorem integral_mem_icc (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, φ x ∂μ ∈ Icc (0 : ℝ) 1 :=
  ⟨hφ.integral_nonneg μ, hφ.integral_le_one μ⟩

/-- The mean of the complementary test `1 - φ` under a probability measure. -/
theorem integral_one_sub (hφ : IsStatisticalTest φ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∫ x, (1 - φ x) ∂μ = 1 - ∫ x, φ x ∂μ := by
  rw [integral_sub (integrable_const 1) (hφ.integrable μ)]
  simp

end IsStatisticalTest

/-- A threshold test with randomization `γ ∈ [0, 1]` in a measurable statistic is a test. -/
theorem is_statistical_test_threshold_test {X α : Type*} [MeasurableSpace X] [LinearOrder α]
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
