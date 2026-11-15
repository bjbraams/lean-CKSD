module

public import CKSD.Inference.Basic

/-!
# Processes: basic definitions

Common notions for Section 106 (dependent data and stochastic models).

* Weak stationarity of a sequence in an inner-product space, in the Hilbert-space form
  `⟪X s, X t⟫ = ⟪X 0, X (t - s)⟫`; for centred square-integrable random variables this is
  weak stationarity of the process in `L²`.
* Independent identically distributed centred noise on `ℤ` with a prescribed variance, the
  innovation sequence of linear, ARMA and GARCH models.
* The sample autocovariance, and the Nelson–Aalen and Kaplan–Meier estimators of right-censored
  survival data.

## Main definitions

* `CKSD.IsWeaklyStationary`: shift-invariance of the Gram matrix of a sequence on `ℤ`.
* `CKSD.IsIIDNoise`: an iid sequence on `ℤ` with mean `0` and variance `σ² > 0`.
* `CKSD.sampleAutocovariance`: `γ̂(h) = n⁻¹ ∑_{i < n - h} (X_{i+h} - X̄)(X_i - X̄)`.
* `CKSD.riskSetSize`, `CKSD.nelsonAalenEstimator`, `CKSD.kaplanMeierEstimator`.

## Main results

* `CKSD.IsWeaklyStationary.inner_eq_inner_sub_zero`: the equivalent form
  `⟪X s, X t⟫ = ⟪X (s - t), X 0⟫`.
* `CKSD.IsIIDNoise.memLp_two`, `CKSD.IsIIDNoise.integral_eq_zero`,
  `CKSD.IsIIDNoise.integral_sq`: the moments of every term, not only of `Z 0`.
* `CKSD.integrable_and_integral_eq_of_tendsto_integral_indicator_le`: monotone convergence
  along the truncations `g 1_{N ≤ n}` of a nonnegative function.
* `CKSD.integral_integral_left_eq_zero_and_integral_sub_eq_zero`: the Hájek projection of a
  bounded kernel with mean zero in its second argument leaves a degenerate remainder.

## Conventions

Observations of a time series are `X 0, …, X (n - 1)`. In the survival estimators the `i`th
subject has failure time `T i` and censoring time `C i`, and one observes `min (T i) (C i)` and
whether `T i ≤ C i`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A sequence `X : ℤ → H` in an inner-product space is weakly stationary when its Gram matrix
is shift invariant: `⟪X s, X t⟫ = ⟪X 0, X (t - s)⟫` for all `s, t`. Applied to centred
square-integrable random variables in `L²`, this is weak (second-order) stationarity of the
process. -/
def IsWeaklyStationary (𝕜 : Type*) {H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (X : ℤ → H) : Prop :=
  ∀ s t, inner 𝕜 (X s) (X t) = inner 𝕜 (X 0) (X (t - s))

/-- For a weakly stationary sequence, `⟪X s, X t⟫ = ⟪X (s - t), X 0⟫`. -/
theorem IsWeaklyStationary.inner_eq_inner_sub_zero {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {X : ℤ → H} (hX : IsWeaklyStationary 𝕜 X)
    (s t : ℤ) : inner 𝕜 (X s) (X t) = inner 𝕜 (X (s - t)) (X 0) := by
  rw [hX s t, hX (s - t) 0]
  congr 2
  ring

/-- An iid centred noise sequence on `ℤ` with variance `σ² > 0`: the `Z t` are measurable,
mutually independent and identically distributed, `𝔼 Z_0 = 0` and `𝔼 Z_0² = σ²`. Square
integrability is not a separate condition: it follows from `𝔼 Z_0² = σ² ≠ 0`
(`IsIIDNoise.memLp_two`). -/
structure IsIIDNoise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : ℤ → Ω → ℝ)
    (σsq : ℝ) : Prop where
  /-- Each `Z t` is measurable. -/
  measurable : ∀ t, Measurable (Z t)
  /-- The `Z t` are mutually independent. -/
  iIndepFun : iIndepFun Z μ
  /-- All `Z t` have the law of `Z 0`. -/
  map_eq : ∀ t, μ.map (Z t) = μ.map (Z 0)
  /-- The noise is centred. -/
  integral_zero_eq_zero : ∫ ω, Z 0 ω ∂μ = 0
  /-- The noise has variance `σ²`. -/
  integral_zero_sq : ∫ ω, Z 0 ω ^ 2 ∂μ = σsq
  /-- The variance is positive. -/
  pos : 0 < σsq

namespace IsIIDNoise

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℤ → Ω → ℝ} {σsq : ℝ}

/-- Each term of an iid noise sequence has the law of `Z 0`. -/
theorem identDistrib (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : IdentDistrib (Z t) (Z 0) μ μ :=
  ⟨(hZ.measurable t).aemeasurable, (hZ.measurable 0).aemeasurable, hZ.map_eq t⟩

/-- Every term of an iid noise sequence is square integrable. -/
theorem memLp_two (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : MemLp (Z t) 2 μ := by
  have h0 : MemLp (Z 0) 2 μ := by
    refine (memLp_two_iff_integrable_sq (hZ.measurable 0).aestronglyMeasurable).2 ?_
    exact Integrable.of_integral_ne_zero (by rw [hZ.integral_zero_sq]; exact hZ.pos.ne')
  exact (hZ.identDistrib t).memLp_iff.2 h0

/-- Every term of an iid noise sequence is centred. -/
theorem integral_eq_zero (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : ∫ ω, Z t ω ∂μ = 0 := by
  rw [(hZ.identDistrib t).integral_eq, hZ.integral_zero_eq_zero]

/-- Every term of an iid noise sequence has second moment `σ²`. -/
theorem integral_sq (hZ : IsIIDNoise μ Z σsq) (t : ℤ) : ∫ ω, Z t ω ^ 2 ∂μ = σsq := by
  rw [← hZ.integral_zero_sq]
  exact ((hZ.identDistrib t).comp (measurable_id.pow_const 2)).integral_eq

end IsIIDNoise

/-- The sample autocovariance `γ̂(h) = n⁻¹ ∑_{i < n - h} (X_{i+h} - X̄_n)(X_i - X̄_n)` at lag
`h` of `X 0, …, X (n - 1)`, with the sample mean `X̄_n` and divisor `n`. -/
def sampleAutocovariance {Ω : Type*} (X : ℕ → Ω → ℝ) (lag n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n - lag),
    (X (i + lag) ω - sampleAverage X n ω) * (X i ω - sampleAverage X n ω)) / n

/-- The sample autocovariance is the lagged sum of centred products divided by `n`. -/
theorem sampleAutocovariance_def {Ω : Type*} (X : ℕ → Ω → ℝ) (lag n : ℕ) (ω : Ω) :
    sampleAutocovariance X lag n ω = (∑ i ∈ Finset.range (n - lag),
      (X (i + lag) ω - sampleAverage X n ω) * (X i ω - sampleAverage X n ω)) / n := by
  rw [sampleAutocovariance]

/-- The size `#{j < n : min (T j) (C j) ≥ min (T i) (C i)}` of the risk set at the observed time
of subject `i`. -/
def riskSetSize {Ω : Type*} (T C : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter fun j ↦ min (T i ω) (C i ω) ≤ min (T j ω) (C j ω)).card

/-- The risk set size counts the subjects whose observed time is at least that of `i`. -/
theorem riskSetSize_def {Ω : Type*} (T C : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) :
    riskSetSize T C n i ω =
      ((Finset.range n).filter fun j ↦ min (T i ω) (C i ω) ≤ min (T j ω) (C j ω)).card := by
  rw [riskSetSize]

/-- The Nelson–Aalen estimator `Λ̂(t) = ∑ 1 / #(risk set)` of the cumulative hazard, with one
term for each subject `i < n` whose failure `T i ≤ C i` is observed by time `t`. -/
def nelsonAalenEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    (riskSetSize T C n i ω : ℝ)⁻¹ else 0

/-- The Nelson–Aalen estimator sums the inverse risk set sizes of the observed failures. -/
theorem nelsonAalenEstimator_def {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    nelsonAalenEstimator T C n ω t = ∑ i ∈ Finset.range n,
      if T i ω ≤ C i ω ∧ T i ω ≤ t then (riskSetSize T C n i ω : ℝ)⁻¹ else 0 := by
  rw [nelsonAalenEstimator]

/-- The Kaplan–Meier estimator `Ŝ(t) = ∏ (1 - 1 / #(risk set))` of the survival function, with
one factor for each subject `i < n` whose failure `T i ≤ C i` is observed by time `t`. -/
def kaplanMeierEstimator {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, if T i ω ≤ C i ω ∧ T i ω ≤ t then
    1 - (riskSetSize T C n i ω : ℝ)⁻¹ else 1

/-- The Kaplan–Meier estimator multiplies the factors `1 - 1 / #(risk set)` of the observed
failures. -/
theorem kaplanMeierEstimator_def {Ω : Type*} (T C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    kaplanMeierEstimator T C n ω t = ∏ i ∈ Finset.range n,
      if T i ω ≤ C i ω ∧ T i ω ≤ t then 1 - (riskSetSize T C n i ω : ℝ)⁻¹ else 1 := by
  rw [kaplanMeierEstimator]

/-- If `s ∈ (a, b)` and `1 ≤ m`, then `exp (t s) / m ^ n ≤ exp (|t| max |a| |b|)`. -/
theorem exp_mul_div_pow_le_of_mem_Ioo {a b s m : ℝ} (t : ℝ) (hs : a < s ∧ s < b) (hm : 1 ≤ m)
    (n : ℕ) : Real.exp (t * s) / m ^ n ≤ Real.exp (|t| * max |a| |b|) := by
  have habs : |s| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · linarith [hs.1, le_max_left |a| |b|, neg_abs_le a]
    · linarith [hs.2, le_max_right |a| |b|, le_abs_self b]
  calc Real.exp (t * s) / m ^ n ≤ Real.exp (t * s) :=
        div_le_self (Real.exp_pos _).le (one_le_pow₀ hm)
    _ ≤ Real.exp (|t| * max |a| |b|) := by
        refine Real.exp_le_exp.2 ?_
        calc t * s ≤ |t * s| := le_abs_self _
          _ = |t| * |s| := abs_mul _ _
          _ ≤ |t| * max |a| |b| := by gcongr

/-- Let `g ≥ 0` be measurable and `N` a measurable `ℕ`-valued function. If the truncations
`g 1_{N ≤ n}` are integrable and their integrals tend to `c`, then `g` is integrable with
integral `c` (monotone convergence). -/
theorem integrable_and_integral_eq_of_tendsto_integral_indicator_le {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → ℕ} (hN : Measurable N) {g : Ω → ℝ}
    (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (hint : ∀ n, Integrable ({ω | N ω ≤ n}.indicator g) P) {c : ℝ}
    (hlim : Tendsto (fun n ↦ ∫ ω, {ω | N ω ≤ n}.indicator g ω ∂P) atTop (𝓝 c)) :
    Integrable g P ∧ ∫ ω, g ω ∂P = c := by
  set f : ℕ → Ω → ℝ := fun n ↦ {ω | N ω ≤ n}.indicator g with hf
  have hf0 : ∀ n ω, 0 ≤ f n ω := fun n ω ↦ Set.indicator_nonneg (fun ω _ ↦ hg0 ω) ω
  have hc0 : 0 ≤ c := ge_of_tendsto' hlim fun n ↦ integral_nonneg (hf0 n)
  have hmono : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (g ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ ((hg.indicator (measurableSet_le hN measurable_const)).ennreal_ofReal
        ).aemeasurable) (ae_of_all _ fun ω i j hij ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
    · apply ENNReal.ofReal_le_ofReal
      by_cases h : N ω ≤ i
      · have hj : N ω ≤ j := h.trans hij
        simp [f, h, hj]
      · simp only [f, Set.indicator, Set.mem_ofPred_eq, h, ite_false]
        split_ifs <;> simp [hg0]
    · refine tendsto_atTop_of_eventually_const (i₀ := N ω) fun n hn ↦ ?_
      simp [f, hn]
  have hlim' : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop
      (𝓝 (ENNReal.ofReal c)) :=
    (ENNReal.tendsto_ofReal hlim).congr fun n ↦
      ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hf0 n))
  have hlin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ENNReal.ofReal c :=
    tendsto_nhds_unique hmono hlim'
  refine ⟨⟨hg.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩,
    ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable, hlin,
    ENNReal.toReal_ofReal hc0]

/-- A weight `0 ≤ a ≤ 1` divided by a power of `b` is bounded by `1 / c ^ n` when `0 < c` and
`c ≤ b` wherever `a ≠ 0`. -/
theorem abs_div_pow_le_one_div_pow {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 < c)
    (hcb : a ≠ 0 → c ≤ b) (n : ℕ) : |a / b ^ n| ≤ 1 / c ^ n := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, abs_zero]; positivity
  have hb := hcb ha
  rw [abs_of_nonneg (div_nonneg ha0 (pow_nonneg (hc.le.trans hb) n))]
  exact div_le_div₀ zero_le_one ha1 (by positivity) (pow_le_pow_left₀ hc.le hb n)

/-- A centred indicator is bounded by one: `|1_p - v| ≤ 1` when `0 ≤ v ≤ 1`. -/
theorem abs_ite_one_zero_sub_le_one (p : Prop) [Decidable p] {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : |(if p then (1 : ℝ) else 0) - v| ≤ 1 := by
  rw [abs_le]
  constructor <;> split_ifs <;> linarith

/-- The fraction `n⁻¹ #{j < n : p j}` lies in `[0, 1]`. -/
theorem sum_range_ite_one_zero_div_mem_Icc (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ j ∈ Finset.range n, if p j then (1 : ℝ) else 0) / n ∈ Set.Icc 0 1 := by
  have h0 : 0 ≤ ∑ j ∈ Finset.range n, if p j then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun j _ ↦ by split_ifs <;> norm_num
  have h1 : ∑ j ∈ Finset.range n, (if p j then (1 : ℝ) else 0) ≤ n := by
    calc _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ by split_ifs <;> norm_num
      _ = n := by simp
  refine ⟨div_nonneg h0 (Nat.cast_nonneg n), ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact div_le_one_of_le₀ h1 (Nat.cast_nonneg n)

/-- Hájek projection of a bounded kernel `F` with `P`-mean zero in its second argument: with
`b(z') = ∫ F(z, z') dP(z)`, the projection `b` has mean zero and the remainder `F - b` is
degenerate, `∫ (F(z, z') - b(z')) dP(z) = 0` and `∫ (F(z, z') - b(z')) dP(z') = 0`. -/
theorem integral_integral_left_eq_zero_and_integral_sub_eq_zero {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] {F : E → E → ℝ}
    (hFm : Measurable (Function.uncurry F)) {c : ℝ} (hFB : ∀ z z', |F z z'| ≤ c)
    (hF0 : ∀ z, ∫ z', F z z' ∂P = 0) :
    ∫ z', ∫ z, F z z' ∂P ∂P = 0 ∧ (∀ z', ∫ z, (F z z' - ∫ w, F w z' ∂P) ∂P = 0) ∧
      ∀ z, ∫ z', (F z z' - ∫ w, F w z' ∂P) ∂P = 0 := by
  have hbm : Measurable fun z' ↦ ∫ z, F z z' ∂P :=
    (StronglyMeasurable.integral_prod_left (μ := P) (f := F) hFm.stronglyMeasurable).measurable
  have hb_bd (z' : E) : ‖∫ z, F z z' ∂P‖ ≤ c := by
    simpa using norm_integral_le_of_norm_le_const (μ := P) (f := fun z ↦ F z z')
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hFB z z')
  have hFint : Integrable (Function.uncurry F) (P.prod P) :=
    Integrable.of_bound hFm.aestronglyMeasurable c
      (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hFB p.1 p.2)
  have hb0 : ∫ z', ∫ z, F z z' ∂P ∂P = 0 := by
    rw [← integral_integral_swap hFint]
    simp [hF0]
  refine ⟨hb0, fun z' ↦ ?_, fun z ↦ ?_⟩
  · rw [integral_sub ?_ (integrable_const _), integral_const]
    · simp
    exact Integrable.of_bound (hFm.comp (measurable_id.prodMk measurable_const)
      ).aestronglyMeasurable c (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hFB z z')
  · rw [integral_sub ?_ (Integrable.of_bound hbm.aestronglyMeasurable c (ae_of_all _ hb_bd)),
      hb0, hF0, sub_zero]
    exact Integrable.of_bound (hFm.comp (measurable_const.prodMk measurable_id)
      ).aestronglyMeasurable c (ae_of_all _ fun z' ↦ by rw [Real.norm_eq_abs]; exact hFB z z')

/-- The truncated second moments `∫_{|X| > τ} X²` of a square-integrable `X` tend to zero as
the threshold `τ` tends to infinity. -/
theorem tendsto_integral_ite_lt_abs_sq {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (hXm : Measurable X) {l : Filter ι} [l.IsCountablyGenerated]
    {τ : ι → ℝ} (hτ : Tendsto τ l atTop) :
    Tendsto (fun i ↦ ∫ ω, (if τ i < |X ω| then X ω ^ 2 else 0) ∂μ) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (fun ω ↦ X ω ^ 2)
    (F := fun i ω ↦ if τ i < |X ω| then X ω ^ 2 else 0) (f := fun _ ↦ 0)
    (Eventually.of_forall fun i ↦ (Measurable.ite (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp hXm)) (hXm.pow_const 2)
      measurable_const).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ ae_of_all _ fun ω ↦ by
      split_ifs <;> simp [sq_nonneg])
    hX.integrable_sq
    (ae_of_all _ fun ω ↦ tendsto_const_nhds.congr' (by
      filter_upwards [hτ.eventually_gt_atTop |X ω|] with i hi
      simp only [ite_eq_right (not_lt.2 hi.le)]))
  simpa using h

end CKSD
