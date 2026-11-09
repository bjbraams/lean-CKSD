module

public import CKSD.Asymptotics.Basic
public import CKSD.Inference.Density
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
import CKSD.Asymptotics.Estimators

/-!
# Contiguity, Le Cam's lemmas, and local asymptotic normality

## Main results

* `CKSD.tendsto_integral_mul_of_tendsto`: weighted weak convergence of probability measures.
* `CKSD.isContiguous_of_integral_likelihood_ratio_limit_eq_one`: Le Cam's first lemma
  (GAPS 102.12).
* `CKSD.tendstoInDistribution_of_log_likelihood_ratio`: Le Cam's third lemma, for observation spaces
  depending on the sample size (GAPS 102.14).
* `CKSD.tendsto_local_normal_power`: local power under a normal limit (GAPS 102.21).
* `CKSD.memLp_and_tendsto_sqrt_likelihood_ratio_of_dqm`,
  `CKSD.tendstoInMeasure_log_likelihood_ratio_sub_of_dqm`, and
  `CKSD.tendstoInDistribution_score_and_log_likelihood_ratio_expansion_of_dqm`: differentiability
  in quadratic mean implies local asymptotic normality (GAPS 102.13).

## References

The LAN expansion follows van der Vaart, *Asymptotic Statistics*, Theorem 7.2: the root density
ratios are controlled by Chebyshev's and Markov's inequalities for i.i.d. sums, Mathlib's weak law
and central limit theorem (through the adapters of `CKSD.Asymptotics.Basic`), and Mathlib's
logarithmic Taylor bound `Real.abs_log_sub_add_sum_range_le`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Truncation `x ↦ max 0 (min x k)` as a bounded continuous function. -/
def clipBCF (k : ℝ) (hk : 0 ≤ k) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x ↦ max 0 (min x k), by fun_prop⟩ (2 * k) (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 : 0 ≤ max 0 (min x k) ∧ max 0 (min x k) ≤ k := ⟨le_max_left _ _, max_le hk (min_le_right _ _)⟩
    have h2 : 0 ≤ max 0 (min y k) ∧ max 0 (min y k) ≤ k := ⟨le_max_left _ _, max_le hk (min_le_right _ _)⟩
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

/-- Weighted weak convergence: if probability measures `μₙ` converge weakly to `ν` and a
continuous nonnegative weight `w` has integral one under every `μₙ` and under `ν`, then
`∫ w f dμₙ → ∫ w f dν` for bounded continuous `f`. -/
theorem tendsto_integral_mul_of_tendsto {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)] (ν : Measure X)
    [IsProbabilityMeasure ν]
    (h : Tendsto (β := ProbabilityMeasure X) (fun n ↦ ⟨μs n, inferInstance⟩) atTop
      (𝓝 ⟨ν, inferInstance⟩))
    (w : X → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hμw : ∀ n, ∫ x, w x ∂μs n = 1) (hνw : ∫ x, w x ∂ν = 1)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n ↦ ∫ x, w x * f x ∂μs n) atTop (𝓝 (∫ x, w x * f x ∂ν)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h
  simp only [ProbabilityMeasure.coe_mk] at h
  have hwint : ∀ n, Integrable w (μs n) := fun n ↦ by
    by_contra hni; have := hμw n; rw [integral_undef hni] at this; exact zero_ne_one this
  have hνint : Integrable w ν := by
    by_contra hni; rw [integral_undef hni] at hνw; exact zero_ne_one hνw
  -- truncations
  let t : ℕ → BoundedContinuousFunction X ℝ := fun k ↦
    (clipBCF k (Nat.cast_nonneg k)).compContinuous ⟨w, hw⟩
  have ht : ∀ k x, t k x = min (w x) k := fun k x ↦ by
    simp [t, clipBCF, hw0 x]
  have htint : ∀ (m : Measure X) [IsProbabilityMeasure m] k, Integrable (t k) m :=
    fun m _ k ↦ (t k).integrable m
  -- error bound for a probability measure m with ∫ w dm = 1
  have herr : ∀ (m : Measure X) [IsProbabilityMeasure m], Integrable w m → ∫ x, w x ∂m = 1 →
      ∀ k : ℕ, |∫ x, w x * f x ∂m - ∫ x, t k x * f x ∂m| ≤ ‖f‖ * (1 - ∫ x, t k x ∂m) := by
    intro m _ hwm h1 k
    have hi1 : Integrable (fun x ↦ w x * f x) m := hwm.mul_bdd f.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
    have hi2 : Integrable (fun x ↦ t k x * f x) m := (htint m k).mul_bdd
      f.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
    have hi3 : Integrable (fun x ↦ ‖f‖ * (w x - t k x)) m := (hwm.sub (htint m k)).const_mul _
    rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hi3 (ae_of_all _ fun x ↦ ?_)).trans_eq ?_
    · have hle : t k x ≤ w x := by rw [ht]; exact min_le_left _ _
      rw [← sub_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle), mul_comm]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (sub_nonneg.2 hle)
    · rw [integral_const_mul, integral_sub hwm (htint m k), h1]
  have hD : Tendsto (fun k : ℕ ↦ ∫ x, t k x ∂ν) atTop (𝓝 (∫ x, w x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence w (fun k ↦ (t k).continuous.aestronglyMeasurable)
      hνint (fun k ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · rw [ht, Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 x) (Nat.cast_nonneg k))]
      exact min_le_left _ _
    · have : ∀ᶠ k : ℕ in atTop, t k x = w x := by
        filter_upwards [eventually_ge_atTop ⌈w x⌉₊] with k hk
        rw [ht]; exact min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hk))
      exact tendsto_const_nhds.congr' (this.mono fun k hk ↦ hk.symm)
  rw [hνw] at hD
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfn : 0 ≤ ‖f‖ := norm_nonneg f
  have hD' : Tendsto (fun k : ℕ ↦ ‖f‖ * (1 - ∫ x, t k x ∂ν)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hD).const_mul ‖f‖
  obtain ⟨k, hk⟩ := (hD'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have h1 : Tendsto (fun n ↦ ‖f‖ * (1 - ∫ x, t k x ∂μs n)) atTop
      (𝓝 (‖f‖ * (1 - ∫ x, t k x ∂ν))) := ((tendsto_const_nhds.sub (h (t k))).const_mul ‖f‖)
  have h2 := h (t k * f)
  simp only [FunLike.coe_mul, Pi.mul_apply] at h2
  filter_upwards [h1.eventually (gt_mem_nhds hk), Metric.tendsto_nhds.1 h2 (ε / 4) (by positivity)]
    with n hn1 hn2
  have e1 := herr (μs n) (hwint n) (hμw n) k
  have e2 := herr ν hνint hνw k
  rw [Real.dist_eq] at hn2 ⊢
  calc |∫ x, w x * f x ∂μs n - ∫ x, w x * f x ∂ν|
      ≤ |∫ x, w x * f x ∂μs n - ∫ x, t k x * f x ∂μs n| +
        |∫ x, t k x * f x ∂μs n - ∫ x, t k x * f x ∂ν| +
        |∫ x, w x * f x ∂ν - ∫ x, t k x * f x ∂ν| := by
          have := abs_sub_le (∫ x, w x * f x ∂μs n) (∫ x, t k x * f x ∂μs n) (∫ x, w x * f x ∂ν)
          have := abs_sub_le (∫ x, t k x * f x ∂μs n) (∫ x, t k x * f x ∂ν) (∫ x, w x * f x ∂ν)
          rw [abs_sub_comm (∫ x, t k x * f x ∂ν)] at this
          linarith
    _ < ε := by linarith

/-- GAPS 102.12: Le Cam's first lemma, for absolutely continuous alternatives. If `Q n ≪ P n`
and the likelihood ratios `dQ n / dP n` under `P n` converge in law to a limit `ν` with mean one,
then `Q n` is contiguous with respect to `P n`: `P n (A n) → 0` implies `Q n (A n) → 0`. -/
theorem isContiguous_of_integral_likelihood_ratio_limit_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (hac : ∀ n, Q n ≪ P n)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlim : TendstoInDistribution (fun n ω ↦ ((Q n).rnDeriv (P n) ω).toReal) atTop id P ν)
    (hmean : (∫ x, x ∂ν) = 1) :
    IsContiguous P Q := by
  have hlimI := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendstoInDistribution_id_iff.1 hlim).2
  simp only [ProbabilityMeasure.coe_mk] at hlimI
  have hint : Integrable id ν := by
    by_contra hni
    have hni' : ¬ Integrable (fun x : ℝ ↦ x) ν := hni
    rw [integral_undef hni'] at hmean
    exact zero_ne_one hmean
  intro A hA hPA
  set L := fun n ω ↦ ((Q n).rnDeriv (P n) ω).toReal with hLdef
  have hLm : ∀ n, Measurable (L n) := fun n ↦ (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hL0 : ∀ n ω, 0 ≤ L n ω := fun n ω ↦ ENNReal.toReal_nonneg
  -- Key inequality for each truncation level.
  have hkey : ∀ (k : ℝ) (hk : 0 ≤ k) n, (Q n).real (A n) ≤
      k * (P n).real (A n) + (1 - ∫ x, clipBCF k hk x ∂(P n).map (L n)) := by
    intro k hk n
    have := hP n; have := hQ n
    have hLint : Integrable (L n) (P n) := Measure.integrable_toReal_rnDeriv
    have hclip : ∀ ω, clipBCF k hk (L n ω) = min (L n ω) k := by
      intro ω; simp [clipBCF, hL0 n ω, hk]
    have hcint : Integrable (fun ω ↦ min (L n ω) k) (P n) := by
      refine (integrable_const k).mono' ((hLm n).min measurable_const).aestronglyMeasurable ?_
      exact ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hL0 n ω) hk)]; exact min_le_right _ _
    rw [integral_map (hLm n).aemeasurable (clipBCF k hk).continuous.aestronglyMeasurable]
    simp_rw [hclip]
    have h1 : (Q n).real (A n) = ∫ ω in A n, L n ω ∂P n :=
      (Measure.setIntegral_toReal_rnDeriv (hac n) (A n)).symm
    have h2 : ∫ ω, L n ω ∂P n = 1 := by
      rw [Measure.integral_toReal_rnDeriv (hac n), probReal_univ]
    have h3 : ∫ ω in A n, L n ω ∂P n = ∫ ω in A n, min (L n ω) k ∂P n +
        ∫ ω in A n, (L n ω - min (L n ω) k) ∂P n := by
      rw [← integral_add (f := fun ω ↦ min (L n ω) k) (g := fun ω ↦ L n ω - min (L n ω) k)
        hcint.integrableOn (hLint.sub hcint).integrableOn]
      congr 1; funext ω; ring
    have h4 : ∫ ω in A n, min (L n ω) k ∂P n ≤ k * (P n).real (A n) := by
      have := setIntegral_mono_on (μ := P n) (s := A n) hcint.integrableOn
        (integrableOn_const (by simp)) (hA n) (fun ω _ ↦ min_le_right (L n ω) k)
      rw [setIntegral_const, smul_eq_mul, mul_comm] at this; exact this
    have h5 : ∫ ω in A n, (L n ω - min (L n ω) k) ∂P n ≤ ∫ ω, (L n ω - min (L n ω) k) ∂P n :=
      setIntegral_le_integral (hLint.sub hcint) (ae_of_all _ fun ω ↦ sub_nonneg.2 (min_le_left _ _))
    rw [integral_sub hLint hcint, h2] at h5
    linarith
  -- Truncated means of the limit approach at least one.
  have hlimk : Tendsto (fun k : ℕ ↦ ∫ x, clipBCF k (Nat.cast_nonneg k) x ∂ν) atTop
      (𝓝 (∫ x, max 0 x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ |x|)
      (fun k ↦ (clipBCF _ _).continuous.aestronglyMeasurable) hint.abs ?_ ?_
    · intro k; refine ae_of_all _ fun x ↦ ?_
      simp only [clipBCF, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le (abs_nonneg x) ((min_le_left _ _).trans (le_abs_self x))
    · refine ae_of_all _ fun x ↦ ?_
      simp only [clipBCF, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
      refine tendsto_const_nhds.max ?_
      have : ∀ᶠ k : ℕ in atTop, min x (k : ℝ) = x := by
        filter_upwards [eventually_ge_atTop ⌈x⌉₊] with k hk
        exact min_eq_left ((Nat.le_ceil x).trans (by exact_mod_cast hk))
      exact tendsto_const_nhds.congr' (this.mono fun k hk ↦ hk.symm)
  have hmax : Integrable (fun x : ℝ ↦ max 0 x) ν := by
    refine hint.abs.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg x) (le_abs_self x)
  have hge : 1 ≤ ∫ x, max 0 x ∂ν := by
    rw [← hmean]
    exact integral_mono hint hmax fun x ↦ le_max_right 0 x
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦
    ha.trans_le measureReal_nonneg, fun ε hε ↦ ?_⟩
  obtain ⟨k, hk⟩ := (hlimk.eventually (lt_mem_nhds (show 1 - ε / 3 < ∫ x, max 0 x ∂ν by
    linarith))).exists
  have hk' := (hlimI (clipBCF k (Nat.cast_nonneg k))).eventually
    (lt_mem_nhds (show 1 - 2 * ε / 3 < ∫ x, clipBCF k (Nat.cast_nonneg k) x ∂ν by linarith))
  have hPk := (hPA.const_mul (k : ℝ)).eventually (gt_mem_nhds (show (k : ℝ) * 0 < ε / 3 by
    rw [mul_zero]; positivity))
  filter_upwards [hk', hPk] with n h1 h2
  have := hkey k (Nat.cast_nonneg k) n
  simp only [hLdef] at this
  linarith

/-- GAPS 102.14: Le Cam's third lemma in change-of-law form, for observation spaces `Ω n`
depending on the sample size. If `Q n = exp (Λ n) · P n` and `(S n, Λ n)` under `P n` converges
in law to `ν` with `∫ exp z₂ dν(z) = 1`, then `S n` under `Q n` converges in law to the first
marginal `L` of `exp z₂ · ν` (a probability measure by the mean condition, supplied as `L` with
its instance). Taking a joint Gaussian limit gives the mean shift stated in GAPS. -/
theorem tendstoInDistribution_of_log_likelihood_ratio {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {E : Type*}
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : ∀ n, Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (S : ∀ n, Ω n → E) (Λ : ∀ n, Ω n → ℝ)
    (hS : ∀ n, Measurable (S n)) (hΛ : ∀ n, Measurable (Λ n))
    (hrn : ∀ n, Q n = (P n).withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (Λ n ω))))
    (ν : Measure (E × ℝ)) [IsProbabilityMeasure ν]
    (hlim : TendstoInDistribution (fun n ω ↦ (S n ω, Λ n ω)) atTop id P ν)
    (hmean : (∫ z, Real.exp z.2 ∂ν) = 1) (L : Measure E) [IsProbabilityMeasure L]
    (hL : (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp z.2)).map Prod.fst = L) :
    TendstoInDistribution S atTop id Q L := by
  subst hL
  have hint : Integrable (fun z : E × ℝ ↦ Real.exp z.2) ν := by
    by_contra hni
    rw [integral_undef hni] at hmean
    exact zero_ne_one hmean
  have : ∀ n, IsProbabilityMeasure (Q n) := hQ
  have : IsFiniteMeasure (ν.withDensity fun z : E × ℝ ↦ ENNReal.ofReal (Real.exp z.2)) :=
    isFiniteMeasure_withDensity hint.lintegral_lt_top.ne
  refine (tendstoInDistribution_id_iff.2 ⟨fun n ↦ (hS n).aemeasurable,
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f ↦ ?_⟩)
  simp only [ProbabilityMeasure.coe_mk]
  have hSΛ : ∀ n, Measurable fun ω ↦ (S n ω, Λ n ω) := fun n ↦ (hS n).prodMk (hΛ n)
  have : ∀ n, IsProbabilityMeasure ((P n).map fun ω ↦ (S n ω, Λ n ω)) := fun n ↦ by
    have := hP n; infer_instance
  have hden : ∀ n, Measurable fun ω ↦ ENNReal.ofReal (Real.exp (Λ n ω)) := fun n ↦
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hΛ n))
  have hdenν : Measurable fun z : E × ℝ ↦ ENNReal.ofReal (Real.exp z.2) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd)
  let F : BoundedContinuousFunction (E × ℝ) ℝ := f.compContinuous ⟨Prod.fst, continuous_fst⟩
  have key := tendsto_integral_mul_of_tendsto _ ν (tendstoInDistribution_id_iff.1 hlim).2
    (fun z ↦ Real.exp z.2)
    (by fun_prop) (fun z ↦ (Real.exp_pos _).le) ?_ hmean F
  · convert key using 1
    · funext n
      rw [integral_map (hS n).aemeasurable f.continuous.aestronglyMeasurable, hrn n,
        integral_withDensity_eq_integral_toReal_smul (hden n)
          (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
        integral_map (hSΛ n).aemeasurable (by fun_prop)]
      simp [F, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    · rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hdenν
          (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp [F, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · intro n
    have := hQ n
    rw [integral_map (hSΛ n).aemeasurable (by fun_prop)]
    have h1 : ∫ ω, Real.exp (Λ n ω) ∂P n = (Q n).real univ := by
      rw [hrn n, measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← integral_toReal (hden n).aemeasurable (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simpa using h1

/-- GAPS 102.21: local power of a test with a normal limit. If `T n` converges in law to `N(a, 1)`
under the alternatives `P n`, the power `P n {T n > z}` tends to `1 - Φ(z - a)`. -/
theorem tendsto_local_normal_power {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (a z : ℝ)
    (hlim : TendstoInDistribution T atTop id P (gaussianReal a 1)) :
    Tendsto (fun n ↦ (P n).real {ω | z < T n ω}) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) (z - a))) := by
  have : ∀ n, IsProbabilityMeasure ((P n).map (T n)) := fun n ↦ by
    have := hP n; infer_instance
  have hfr : gaussianReal a 1 (frontier (Ioi z)) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := a) (v := 1) one_ne_zero
    rw [frontier_Ioi]; exact measure_singleton z
  have key : Tendsto (fun n ↦ ((P n).map (T n)).real (Ioi z)) atTop
      (𝓝 ((gaussianReal a 1).real (Ioi z))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        (tendstoInDistribution_id_iff.1 hlim).2 hfr)
  have heq : ∀ n, (P n).real {ω | z < T n ω} = ((P n).map (T n)).real (Ioi z) := by
    intro n
    rw [map_measureReal_apply (hT n) measurableSet_Ioi]; rfl
  simp_rw [heq]
  convert key using 2
  have hcdf : cdf (gaussianReal 0 1) (z - a) = (gaussianReal a 1).real (Iic z) := by
    rw [cdf_eq_real, show gaussianReal a 1 = (gaussianReal 0 1).map (· + a) by
        rw [gaussianReal_map_add_const, zero_add],
      map_measureReal_apply (measurable_add_const a) measurableSet_Iic]
    congr 1
    ext x; simp [le_sub_iff_add_le]
  rw [hcdf, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- The deterministic step of LAN under differentiability in quadratic mean. For the root
likelihood ratios `gₙ = √(f (θ₀ + h / √n) / f θ₀) - 1` and their linearizations
`uₙ = gₙ - (h / √n) / 2 · ℓ̇` with the score `ℓ̇`, each `uₙ` is in `L²(P θ₀)`,
`n E[uₙ²] → 0`, and `n E[gₙ] → -h² I / 8`, where `I = E[ℓ̇²]`. -/
theorem memLp_and_tendsto_sqrt_likelihood_ratio_of_dqm
    {E : Type*} [MeasurableSpace E] (nu : Measure E)
    (P : ℝ → Measure E) (hP : ∀ theta, IsProbabilityMeasure (P theta))
    (f : ℝ → E → ℝ) (hf : ∀ theta, HasDensity (P theta) nu (f theta))
    (hpos : ∀ theta x, 0 < f theta x) (theta₀ : ℝ) (score : E → ℝ)
    (hs : Measurable score) (hs2 : MemLp score 2 (P theta₀))
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (theta₀ + h) x) - Real.sqrt (f theta₀ x) -
        h / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu) (fun h : ℝ ↦ h ^ 2)) (h : ℝ) :
    (∀ n : ℕ, MemLp (fun x ↦ Real.sqrt (f (theta₀ + h / Real.sqrt n) x / f theta₀ x) - 1 -
      h / Real.sqrt n / 2 * score x) 2 (P theta₀)) ∧
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∫ x, (Real.sqrt (f (theta₀ + h / Real.sqrt n) x /
      f theta₀ x) - 1 - h / Real.sqrt n / 2 * score x) ^ 2 ∂P theta₀) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∫ x, (Real.sqrt (f (theta₀ + h / Real.sqrt n) x / f theta₀ x) - 1)
      ∂P theta₀) atTop (𝓝 (-(h ^ 2 * (∫ x, score x ^ 2 ∂P theta₀) / 8))) := by
  have hP0 := hP theta₀
  set I := ∫ x, score x ^ 2 ∂P theta₀ with hI
  set p₀ : E → ℝ := f theta₀ with hp₀
  set t : ℕ → ℝ := fun n ↦ h / Real.sqrt n with ht
  set q : ℕ → E → ℝ := fun n ↦ f (theta₀ + t n) with hq
  set g : ℕ → E → ℝ := fun n x ↦ Real.sqrt (q n x / p₀ x) - 1 with hg
  set u : ℕ → E → ℝ := fun n x ↦ g n x - t n / 2 * score x with hu
  set v : ℕ → E → ℝ := fun n x ↦
    Real.sqrt (q n x) - Real.sqrt (p₀ x) - t n / 2 * score x * Real.sqrt (p₀ x) with hv
  set D : ℝ → ℝ := fun τ ↦ ∫ x, (Real.sqrt (f (theta₀ + τ) x) - Real.sqrt (f theta₀ x) -
    τ / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu with hD
  have hp₀pos : ∀ x, 0 < p₀ x := hpos theta₀
  have hqpos : ∀ n x, 0 < q n x := fun n ↦ hpos _
  have hp₀m : Measurable p₀ := (hf theta₀).1
  have hqm : ∀ n, Measurable (q n) := fun n ↦ (hf _).1
  have hgm : ∀ n, Measurable (g n) := fun n ↦
    (((hqm n).div hp₀m).sqrt).sub_const 1
  have hum : ∀ n, Measurable (u n) := fun n ↦ (hgm n).sub (hs.const_mul _)
  -- densities
  have hp₀i : Integrable p₀ nu := HasDensity.integrable (hf theta₀)
  have hp₀1 : ∫ x, p₀ x ∂nu = 1 := HasDensity.integral_eq_one (hf theta₀)
  have hqi1 : ∀ n, Integrable (q n) nu ∧ ∫ x, q n x ∂nu = 1 := fun n ↦ by
    have := hP (theta₀ + t n)
    exact ⟨HasDensity.integrable (hf _), HasDensity.integral_eq_one (hf _)⟩
  have hdens : ∀ φ : E → ℝ, (Integrable φ (P theta₀) ↔ Integrable (fun x ↦ p₀ x * φ x) nu) ∧
      ∫ x, φ x ∂P theta₀ = ∫ x, p₀ x * φ x ∂nu :=
    fun φ ↦ ⟨HasDensity.integrable_iff (hf theta₀) φ, HasDensity.integral_eq (hf theta₀) φ⟩
  -- `v = √p₀ u` and `v² = p₀ u²`
  have hvu : ∀ n x, v n x = Real.sqrt (p₀ x) * u n x := by
    intro n x
    have hs0' : Real.sqrt (p₀ x) ≠ 0 := (Real.sqrt_pos.2 (hp₀pos x)).ne'
    simp only [hv, hu, hg]
    rw [Real.sqrt_div' _ (hp₀pos x).le]
    field_simp
  have hvsq : ∀ n x, v n x ^ 2 = p₀ x * u n x ^ 2 := by
    intro n x
    rw [hvu, mul_pow, Real.sq_sqrt (hp₀pos x).le]
  have hs2P : Integrable (fun x ↦ score x ^ 2) (P theta₀) := hs2.integrable_sq
  have hsν : Integrable (fun x ↦ (score x * Real.sqrt (p₀ x)) ^ 2) nu ∧
      ∫ x, (score x * Real.sqrt (p₀ x)) ^ 2 ∂nu = I := by
    have e : (fun x ↦ (score x * Real.sqrt (p₀ x)) ^ 2) = fun x ↦ p₀ x * score x ^ 2 := by
      funext x; rw [mul_pow, Real.sq_sqrt (hp₀pos x).le, mul_comm]
    obtain ⟨h1, h2⟩ := hdens (fun x ↦ score x ^ 2)
    rw [e]
    exact ⟨h1.1 hs2P, h2.symm⟩
  have hvm : ∀ n, Measurable (v n) := fun n ↦
    (((hqm n).sqrt.sub hp₀m.sqrt).sub ((hs.const_mul _).mul hp₀m.sqrt))
  have hv2 : ∀ n, Integrable (fun x ↦ v n x ^ 2) nu := by
    intro n
    refine (((((hqi1 n).1.add hp₀i).add (hsν.1.const_mul ((t n / 2) ^ 2))).const_mul 3)).mono'
      ((hvm n).pow_const 2).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have key : ∀ a b c : ℝ, (a - b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := fun a b c ↦ by
      nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b - c)]
    show v n x ^ 2 ≤ 3 * (q n x + p₀ x + (t n / 2) ^ 2 * (score x * Real.sqrt (p₀ x)) ^ 2)
    calc v n x ^ 2 ≤ 3 * (Real.sqrt (q n x) ^ 2 + Real.sqrt (p₀ x) ^ 2 +
          (t n / 2 * score x * Real.sqrt (p₀ x)) ^ 2) := key _ _ _
      _ = 3 * (q n x + p₀ x + (t n / 2) ^ 2 * (score x * Real.sqrt (p₀ x)) ^ 2) := by
          rw [Real.sq_sqrt (hqpos n x).le, Real.sq_sqrt (hp₀pos x).le]; ring
  have hu2 : ∀ n, Integrable (fun x ↦ u n x ^ 2) (P theta₀) ∧
      ∫ x, u n x ^ 2 ∂P theta₀ = D (t n) := by
    intro n
    obtain ⟨h1, h2⟩ := hdens (fun x ↦ u n x ^ 2)
    have e : (fun x ↦ p₀ x * u n x ^ 2) = fun x ↦ v n x ^ 2 := by
      funext x; rw [hvsq]
    rw [e] at h1 h2
    exact ⟨h1.2 (hv2 n), h2⟩
  have hu2' : ∀ n, MemLp (u n) 2 (P theta₀) := fun n ↦
    (memLp_two_iff_integrable_sq (hum n).aestronglyMeasurable).2 (hu2 n).1
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have htn : Tendsto t atTop (𝓝 0) := tendsto_const_nhds.div_atTop hsqrt
  have hnt2 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * t n ^ 2 = h ^ 2 := by
    intro n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [ht, div_pow, Real.sq_sqrt this.le]
    field_simp
  have hD0 : ∀ τ, 0 ≤ D τ := fun τ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hnD : Tendsto (fun n : ℕ ↦ n * D (t n)) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    have hc : 0 < ε / 2 / (h ^ 2 + 1) := by positivity
    have hev := htn.eventually (hdqm.def hc)
    obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨hb, hn1⟩ := hN n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hD0 _),
      abs_of_nonneg (sq_nonneg _)] at hb
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (hD0 _))]
    calc (n : ℝ) * D (t n) ≤ n * (ε / 2 / (h ^ 2 + 1) * t n ^ 2) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ = ε / 2 / (h ^ 2 + 1) * h ^ 2 := by rw [← hnt2 n hn1]; ring
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [sq_nonneg h]
  -- the mean of `gₙ`
  set a : E → ℝ := fun x ↦ score x * Real.sqrt (p₀ x) with ha
  have ham : Measurable a := hs.mul hp₀m.sqrt
  have hav : ∀ n, |∫ x, a x * v n x ∂nu| ≤ Real.sqrt I * Real.sqrt (D (t n)) := by
    intro n
    have := abs_integral_mul_le_sqrt_mul_sqrt nu a (v n) ham.aestronglyMeasurable
      (hvm n).aestronglyMeasurable hsν.1 (hv2 n)
    rwa [hsν.2] at this
  have havi : ∀ n, Integrable (fun x ↦ a x * v n x) nu := by
    intro n
    refine ((hsν.1.add (hv2 n)).div_const 2).mono' (ham.mul (hvm n)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    show |a x| * |v n x| ≤ (a x ^ 2 + v n x ^ 2) / 2
    nlinarith [sq_nonneg (|a x| - |v n x|), sq_abs (a x), sq_abs (v n x)]
  have hw : ∀ n, ∫ x, (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2 ∂nu =
      t n ^ 2 / 4 * I + t n * ∫ x, a x * v n x ∂nu + D (t n) := by
    intro n
    have e : (fun x ↦ (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2) =
        fun x ↦ (t n ^ 2 / 4 * a x ^ 2 + t n * (a x * v n x)) + v n x ^ 2 := by
      funext x
      simp only [hv, ha]
      ring
    have hI' : ∫ x, a x ^ 2 ∂nu = I := hsν.2
    have ha2 : Integrable (fun x ↦ a x ^ 2) nu := hsν.1
    rw [e, integral_add (f := fun x ↦ t n ^ 2 / 4 * a x ^ 2 + t n * (a x * v n x))
      (g := fun x ↦ v n x ^ 2) ((ha2.const_mul _).add ((havi n).const_mul _)) (hv2 n),
      integral_add (f := fun x ↦ t n ^ 2 / 4 * a x ^ 2) (g := fun x ↦ t n * (a x * v n x))
        (ha2.const_mul _) ((havi n).const_mul _), integral_const_mul, integral_const_mul, hI']
  have hwi : ∀ n, Integrable (fun x ↦ (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2) nu := by
    intro n
    have e : (fun x ↦ (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2) =
        fun x ↦ (t n ^ 2 / 4 * a x ^ 2 + t n * (a x * v n x)) + v n x ^ 2 := by
      funext x
      simp only [hv, ha]
      ring
    rw [e]
    exact ((hsν.1.const_mul _).add ((havi n).const_mul _)).add (hv2 n)
  have hgeq : ∀ n x, p₀ x * g n x =
      (q n x - p₀ x - (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2) / 2 := by
    intro n x
    have hs0' : Real.sqrt (p₀ x) ≠ 0 := (Real.sqrt_pos.2 (hp₀pos x)).ne'
    simp only [hg]
    rw [Real.sqrt_div' _ (hp₀pos x).le]
    have e1 := Real.sq_sqrt (hqpos n x).le
    have e2 := Real.sq_sqrt (hp₀pos x).le
    field_simp
    linear_combination (Real.sqrt (p₀ x) - 2 * Real.sqrt (q n x)) * e2 + Real.sqrt (p₀ x) * e1
  have hgint : ∀ n, ∫ x, g n x ∂P theta₀ =
      -(1 / 2) * ∫ x, (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2 ∂nu := by
    intro n
    rw [(hdens (g n)).2]
    simp_rw [hgeq]
    rw [integral_div, integral_sub (f := fun x ↦ q n x - p₀ x)
      (g := fun x ↦ (Real.sqrt (q n x) - Real.sqrt (p₀ x)) ^ 2) ((hqi1 n).1.sub hp₀i) (hwi n),
      integral_sub (hqi1 n).1 hp₀i, (hqi1 n).2, hp₀1]
    ring
  have hgmean : Tendsto (fun n : ℕ ↦ n * ∫ x, g n x ∂P theta₀) atTop (𝓝 (-(h ^ 2 * I / 8))) := by
    have hcross : Tendsto (fun n : ℕ ↦ n * t n * ∫ x, a x * v n x ∂nu) atTop (𝓝 0) := by
      have hb : Tendsto (fun n : ℕ ↦ |h| * Real.sqrt I * Real.sqrt (n * D (t n))) atTop (𝓝 0) := by
        have := ((Real.continuous_sqrt.tendsto 0).comp hnD).const_mul (|h| * Real.sqrt I)
        simpa using this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hn0, Real.sqrt_mul hn0.le]
      have hnt : (n : ℝ) * |t n| = |h| * Real.sqrt n := by
        simp only [ht, abs_div, abs_of_pos (Real.sqrt_pos.2 hn0)]
        field_simp
        rw [Real.sq_sqrt hn0.le]
        ring
      calc (n : ℝ) * |t n| * |∫ x, a x * v n x ∂nu|
          ≤ (n : ℝ) * |t n| * (Real.sqrt I * Real.sqrt (D (t n))) := by gcongr; exact hav n
        _ = |h| * Real.sqrt I * (Real.sqrt n * Real.sqrt (D (t n))) := by rw [hnt]; ring
    have hlim : Tendsto (fun n : ℕ ↦ -(1 / 2) * (h ^ 2 / 4 * I + n * t n * ∫ x, a x * v n x ∂nu +
        n * D (t n))) atTop (𝓝 (-(h ^ 2 * I / 8))) := by
      have := (((tendsto_const_nhds (x := h ^ 2 / 4 * I)).add hcross).add hnD).const_mul
        (-(1 / 2))
      rwa [show -(1 / 2) * (h ^ 2 / 4 * I + 0 + 0) = -(h ^ 2 * I / 8) by ring] at this
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hgint, hw]
    have := hnt2 n hn
    simp only [ht] at this ⊢
    linear_combination ((1 / 8) * I) * this
  exact ⟨hu2', hnD.congr fun n ↦ by rw [(hu2 n).2], hgmean⟩

/-- GAPS 102.13: differentiability in quadratic mean implies local asymptotic normality, for a
scalar parameter and common strictly positive densities. If `√f θ` is differentiable in
quadratic mean at `θ₀` with score `ℓ̇` (centred, square-integrable) and `I = E[ℓ̇²]`, then for an
i.i.d. sample from `P θ₀` and every `h`, the log likelihood ratio of `θ₀ + h / √n` against `θ₀`
satisfies `∑ log (f (θ₀ + h/√n) (Xᵢ) / f θ₀ (Xᵢ)) = (h / √n) ∑ ℓ̇(Xᵢ) - h² I / 2 + o_P(1)`.
The proof follows van der Vaart, *Asymptotic Statistics*, Theorem 7.2. -/
theorem tendstoInMeasure_log_likelihood_ratio_sub_of_dqm
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (nu : Measure E)
    (P : ℝ → Measure E) (hP : ∀ theta, IsProbabilityMeasure (P theta))
    (f : ℝ → E → ℝ) (hf : ∀ theta, HasDensity (P theta) nu (f theta))
    (hpos : ∀ theta x, 0 < f theta x) (theta₀ : ℝ) (score : E → ℝ)
    (hs : Measurable score) (hs2 : MemLp score 2 (P theta₀))
    (hs0 : (∫ x, score x ∂P theta₀) = 0)
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (theta₀ + h) x) - Real.sqrt (f theta₀ x) -
        h / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu) (fun h : ℝ ↦ h ^ 2))
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X (P theta₀)) (h : ℝ) :
    TendstoInMeasure mu (fun (n : ℕ) w ↦
      (∑ i ∈ Finset.range n, Real.log (f (theta₀ + h / Real.sqrt n) (X i w) / f theta₀ (X i w))) -
        h / Real.sqrt n * (∑ i ∈ Finset.range n, score (X i w)) +
          h ^ 2 * (∫ x, score x ^ 2 ∂P theta₀) / 2) atTop (fun _ ↦ 0) := by
  have hP0 := hP theta₀
  set I := ∫ x, score x ^ 2 ∂P theta₀ with hI
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  obtain ⟨hu2'', hnDu', hgmean'⟩ :=
    memLp_and_tendsto_sqrt_likelihood_ratio_of_dqm nu P hP f hf hpos theta₀ score hs hs2 hdqm h
  set p₀ : E → ℝ := f theta₀ with hp₀
  set t : ℕ → ℝ := fun n ↦ h / Real.sqrt n with ht
  set q : ℕ → E → ℝ := fun n ↦ f (theta₀ + t n) with hq
  set g : ℕ → E → ℝ := fun n x ↦ Real.sqrt (q n x / p₀ x) - 1 with hg
  set u : ℕ → E → ℝ := fun n x ↦ g n x - t n / 2 * score x with hu
  set v : ℕ → E → ℝ := fun n x ↦
    Real.sqrt (q n x) - Real.sqrt (p₀ x) - t n / 2 * score x * Real.sqrt (p₀ x) with hv
  set D : ℝ → ℝ := fun τ ↦ ∫ x, (Real.sqrt (f (theta₀ + τ) x) - Real.sqrt (f theta₀ x) -
    τ / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu with hD
  have hp₀pos : ∀ x, 0 < p₀ x := hpos theta₀
  have hqpos : ∀ n x, 0 < q n x := fun n ↦ hpos _
  have hgm : ∀ n, Measurable (g n) := fun n ↦
    ((((hf _).1.div (hf theta₀).1).sqrt).sub_const 1)
  have hum : ∀ n, Measurable (u n) := fun n ↦ (hgm n).sub (hs.const_mul _)
  have hs2P : Integrable (fun x ↦ score x ^ 2) (P theta₀) := hs2.integrable_sq
  have hu2' : ∀ n, MemLp (u n) 2 (P theta₀) := hu2''
  have hu2 : ∀ n, Integrable (fun x ↦ u n x ^ 2) (P theta₀) := fun n ↦ (hu2' n).integrable_sq
  have hgmean : Tendsto (fun n : ℕ ↦ n * ∫ x, g n x ∂P theta₀) atTop (𝓝 (-(h ^ 2 * I / 8))) :=
    hgmean'
  have hnDu' : Tendsto (fun n : ℕ ↦ n * ∫ x, u n x ^ 2 ∂P theta₀) atTop (𝓝 0) := hnDu'
  -- sample-level quantities
  have hiid' : IsIndependentIdenticallyDistributed mu X (P theta₀) := ⟨hXm, hind, hlaw⟩
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, score (X i w) with hZ
  set G1 : ℕ → Ω → ℝ := fun n w ↦ ∑ i ∈ Finset.range n, g n (X i w) with hG1
  set G2 : ℕ → Ω → ℝ := fun n w ↦ ∑ i ∈ Finset.range n, g n (X i w) ^ 2 with hG2
  have hs1 : Integrable score (P theta₀) := hs2.integrable one_le_two
  have hgu : ∀ n x, g n x = u n x + t n / 2 * score x := fun n x ↦ by simp only [hu]; ring
  have hgi : ∀ n, Integrable (g n) (P theta₀) := fun n ↦ by
    have : g n = fun x ↦ u n x + t n / 2 * score x := funext (hgu n)
    rw [this]
    exact ((hu2' n).integrable one_le_two).add (hs1.const_mul _)
  have hui : ∀ n, ∫ x, u n x ∂P theta₀ = ∫ x, g n x ∂P theta₀ := fun n ↦ by
    simp only [hu]
    rw [integral_sub (hgi n) (hs1.const_mul _), integral_const_mul, hs0, mul_zero, sub_zero]
  have hnDu := hnDu'
  have hF2 : TendstoInMeasure mu
      (fun (n : ℕ) w ↦ G1 n w - h / 2 * Z n w + h ^ 2 * I / 8) atTop (fun _ ↦ 0) := by
    have h1 := tendstoInMeasure_sum_sub_of_iid mu (P theta₀) X hiid' u hum hu2' hnDu
    have h2 := tendstoInMeasure_const_of_tendsto mu
      (fun n : ℕ ↦ n * ∫ x, g n x ∂P theta₀ + h ^ 2 * I / 8)
      (by convert hgmean.add_const (h ^ 2 * I / 8) using 2; ring)
    have := tendstoInMeasure_add_zero mu _ _ h1 h2
    convert this using 3 with n w
    have hsplit : G1 n w = ∑ i ∈ Finset.range n, u n (X i w) +
        t n / 2 * ∑ i ∈ Finset.range n, score (X i w) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ hgu n _
    rw [hsplit, hui]
    simp only [hZ, ht]
    ring
  -- the sum of squares
  have hsqm : Measurable (fun x ↦ score x ^ 2) := hs.pow_const 2
  set B2 : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, score (X i w) ^ 2 with hB2
  have hB2lim : TendstoInMeasure mu B2 atTop (fun _ ↦ I) :=
    tendstoInMeasure_sampleMean_of_iid mu (P theta₀) X hiid' (fun x ↦ score x ^ 2) hsqm
      hs2P
  set U2 : ℕ → Ω → ℝ := fun n w ↦ ∑ i ∈ Finset.range n, u n (X i w) ^ 2 with hU2
  have hU2lim : TendstoInMeasure mu U2 atTop (fun _ ↦ 0) :=
    tendstoInMeasure_sum_sq_of_iid mu (P theta₀) X hiid' u hum hu2 hnDu
  have ht2 : ∀ n : ℕ, t n ^ 2 = h ^ 2 * (n : ℝ)⁻¹ := fun n ↦ by
    simp only [ht, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hF3 : TendstoInMeasure mu (fun (n : ℕ) w ↦ G2 n w - h ^ 2 * I / 4) atTop (fun _ ↦ 0) := by
    have hA : TendstoInMeasure mu (fun (n : ℕ) w ↦ h ^ 2 / 4 * (B2 n w - I)) atTop (fun _ ↦ 0) :=
      tendstoInMeasure_const_mul_zero mu _ _ (by
        rw [tendstoInMeasure_iff_measureReal_lt_dist] at hB2lim ⊢
        intro ε hε; simpa [Real.dist_eq] using hB2lim ε hε)
    have hsq1 : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt (h ^ 2 * B2 n w))
        atTop (fun _ ↦ Real.sqrt (h ^ 2 * I)) :=
      tendstoInMeasure_comp_of_continuousAt mu B2 I (fun y ↦ Real.sqrt (h ^ 2 * y))
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).continuousAt hB2lim
    have hsq2 : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt (U2 n w)) atTop (fun _ ↦ 0) := by
      have := tendstoInMeasure_comp_of_continuousAt mu U2 0 Real.sqrt
        Real.continuous_sqrt.continuousAt hU2lim
      simpa using this
    have hX := tendstoInMeasure_mul_zero_of_isBoundedInProbability mu _ _
      (isBoundedInProbability_of_tendstoInMeasure mu _ _ hsq1) hsq2
    have hC : TendstoInMeasure mu (fun (n : ℕ) w ↦
        t n * ∑ i ∈ Finset.range n, score (X i w) * u n (X i w)) atTop (fun _ ↦ 0) := by
      refine tendstoInMeasure_zero_of_abs_le mu _ _ (fun _ _ ↦ (0 : ℝ)) one_pos
        (Eventually.of_forall fun n ↦ ae_of_all _ fun w _ ↦ ?_) hX
        (tendstoInMeasure_const_of_tendsto mu _ tendsto_const_nhds)
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun i ↦ score (X i w))
        (fun i ↦ u n (X i w))
      have hB2e : h ^ 2 * B2 n w = t n ^ 2 * ∑ i ∈ Finset.range n, score (X i w) ^ 2 := by
        rw [ht2]; simp only [hB2]; ring
      have hnn : 0 ≤ h ^ 2 * B2 n w := by
        rw [hB2e]; exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ← Real.sqrt_mul hnn, hB2e, ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      calc (t n * ∑ i ∈ Finset.range n, score (X i w) * u n (X i w)) ^ 2
          = t n ^ 2 * (∑ i ∈ Finset.range n, score (X i w) * u n (X i w)) ^ 2 := by ring
        _ ≤ t n ^ 2 * ((∑ i ∈ Finset.range n, score (X i w) ^ 2) *
            ∑ i ∈ Finset.range n, u n (X i w) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
        _ = t n ^ 2 * (∑ i ∈ Finset.range n, score (X i w) ^ 2) * U2 n w := by
          simp only [hU2]; ring
    have := tendstoInMeasure_add_zero mu _ _
      (tendstoInMeasure_add_zero mu _ _ hU2lim hC) hA
    convert this using 3 with n w
    have hG2e : G2 n w = U2 n w + t n * ∑ i ∈ Finset.range n, score (X i w) * u n (X i w) +
        t n ^ 2 / 4 * ∑ i ∈ Finset.range n, score (X i w) ^ 2 := by
      simp only [hG2, hU2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hgu]; ring
    rw [hG2e, ht2]
    simp only [hB2]
    ring
  -- the largest summand
  set M : ℕ → Ω → ℝ := fun n w ↦
    (((Finset.range n).sup fun i ↦ ‖g n (X i w)‖₊ : ℝ≥0) : ℝ) with hM
  have hM0 : ∀ n w, 0 ≤ M n w := fun n w ↦ NNReal.coe_nonneg _
  have hMle : ∀ n w, ∀ i ∈ Finset.range n, |g n (X i w)| ≤ M n w := by
    intro n w i hi
    have := Finset.le_sup (f := fun i ↦ ‖g n (X i w)‖₊) hi
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs] at this
    exact this
  have hgtail : ∀ ε > 0, Tendsto (fun n : ℕ ↦ n * (P theta₀).real {x | ε < |g n x|}) atTop
      (𝓝 0) := by
    intro ε hε
    set c := ε / (|h| + 1) with hc_def
    have hc : 0 < c := by positivity
    have h1 := tendsto_mul_measureReal_lt_abs_of_integrable_sq (P theta₀) score hs hs2P hc
    have h2 : Tendsto (fun n : ℕ ↦ n * (∫ x, u n x ^ 2 ∂P theta₀) / (ε / 2) ^ 2) atTop (𝓝 0) := by
      simpa using hnDu.div_const ((ε / 2) ^ 2)
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_
      (by simpa using h1.add h2)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn := Real.sqrt_pos.2 hn0
    have hsub : {x | ε < |g n x|} ⊆
        {x | c * Real.sqrt n < |score x|} ∪ {x | (ε / 2) ^ 2 ≤ u n x ^ 2} := by
      intro x hx
      simp only [mem_ofPred_eq, mem_union] at hx ⊢
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hu' : |u n x| < ε / 2 := abs_lt_of_sq_lt_sq h2 (by positivity)
      have ht' : |t n / 2 * score x| ≤ ε / 2 := by
        rw [abs_mul, abs_div, abs_two]
        simp only [ht, abs_div, abs_of_pos hsn]
        calc |h| / Real.sqrt n / 2 * |score x| ≤ |h| / Real.sqrt n / 2 * (c * Real.sqrt n) := by
              gcongr
          _ = |h| * c / 2 := by field_simp
          _ ≤ ε / 2 := by
              rw [hc_def, mul_div_assoc', div_le_div_iff_of_pos_right two_pos,
                div_le_iff₀ (by positivity)]
              nlinarith [abs_nonneg h]
      rw [hgu] at hx
      linarith [abs_add_le (u n x) (t n / 2 * score x)]
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P theta₀) (f := fun x ↦ u n x ^ 2)
      (ae_of_all _ fun _ ↦ sq_nonneg _) (hu2 n) ((ε / 2) ^ 2)
    have hmk' : (P theta₀).real {x | (ε / 2) ^ 2 ≤ u n x ^ 2} ≤
        (∫ x, u n x ^ 2 ∂P theta₀) / (ε / 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hmk]
    calc (n : ℝ) * (P theta₀).real {x | ε < |g n x|}
        ≤ n * ((P theta₀).real {x | c * Real.sqrt n < |score x|} +
            (P theta₀).real {x | (ε / 2) ^ 2 ≤ u n x ^ 2}) :=
          mul_le_mul_of_nonneg_left ((measureReal_mono hsub).trans (measureReal_union_le _ _))
            (Nat.cast_nonneg n)
      _ ≤ n * (P theta₀).real {x | c * Real.sqrt n < |score x|} +
            n * (∫ x, u n x ^ 2 ∂P theta₀) / (ε / 2) ^ 2 := by
          rw [mul_add, mul_div_assoc]
          gcongr
  have hF4 : TendstoInMeasure mu M atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_measureReal_lt_dist]
    intro ε hε
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) (hgtail ε hε)
    calc mu.real {w | ε < dist (M n w) 0}
        ≤ mu.real (⋃ i ∈ Finset.range n, {w | ε < |g n (X i w)|}) := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro w hw
          simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (hM0 n w)] at hw
          simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
          by_contra hcon
          push Not at hcon
          have hsup : ((Finset.range n).sup fun i ↦ ‖g n (X i w)‖₊) ≤ ε.toNNReal :=
            Finset.sup_le fun i hi ↦ (Real.le_toNNReal_iff_coe_le hε.le).2 (by
              rw [coe_nnnorm, Real.norm_eq_abs]; exact hcon i hi)
          have := (Real.le_toNNReal_iff_coe_le hε.le).1 hsup
          simp only [hM] at hw
          linarith
      _ ≤ ∑ i ∈ Finset.range n, mu.real {w | ε < |g n (X i w)|} :=
          measureReal_biUnion_finset_le _ _
      _ = n * (P theta₀).real {x | ε < |g n x|} := by
          have : ∀ i, mu.real {w | ε < |g n (X i w)|} = (P theta₀).real {x | ε < |g n x|} :=
            fun i ↦ by
              have hms : MeasurableSet {x | ε < |g n x|} :=
                measurableSet_lt measurable_const (continuous_abs.measurable.comp (hgm n))
              rw [← hlaw i, map_measureReal_apply (hXm i) hms]
              rfl
          simp [this]
  -- the logarithmic remainder
  have hG2lim : TendstoInMeasure mu G2 atTop (fun _ ↦ h ^ 2 * I / 4) := by
    rw [tendstoInMeasure_iff_measureReal_lt_dist] at hF3 ⊢
    intro ε hε; simpa [Real.dist_eq] using hF3 ε hε
  set R : ℕ → Ω → ℝ := fun n w ↦
    ∑ i ∈ Finset.range n, Real.log (q n (X i w) / p₀ (X i w)) - (2 * G1 n w - G2 n w) with hR
  have hR0 : TendstoInMeasure mu R atTop (fun _ ↦ 0) := by
    have hX := tendstoInMeasure_mul_zero_of_isBoundedInProbability mu _ _
      (isBoundedInProbability_of_tendstoInMeasure mu _ _ hG2lim)
      (tendstoInMeasure_const_mul_zero mu M 4 hF4)
    refine tendstoInMeasure_zero_of_abs_le mu _ _ M (by norm_num : (0 : ℝ) < 1 / 2)
      (Eventually.of_forall fun n ↦ ae_of_all _ fun w hMw ↦ ?_) hX hF4
    rw [abs_of_nonneg (hM0 n w)] at hMw
    have hlog : ∀ i, Real.log (q n (X i w) / p₀ (X i w)) = 2 * Real.log (1 + g n (X i w)) := by
      intro i
      simp only [hg, add_sub_cancel]
      rw [Real.log_sqrt (div_pos (hqpos _ _) (hp₀pos _)).le]
      ring
    have hRe : R n w = ∑ i ∈ Finset.range n,
        (2 * Real.log (1 + g n (X i w)) - (2 * g n (X i w) - g n (X i w) ^ 2)) := by
      simp only [hR, hG1, hG2]
      rw [Finset.sum_congr rfl fun i _ ↦ hlog i,
        Finset.sum_sub_distrib (f := fun i ↦ 2 * Real.log (1 + g n (X i w)))
          (g := fun i ↦ 2 * g n (X i w) - g n (X i w) ^ 2),
        Finset.sum_sub_distrib (f := fun i ↦ 2 * g n (X i w)) (g := fun i ↦ g n (X i w) ^ 2),
        ← Finset.mul_sum, ← Finset.mul_sum]
    have hG2nn : 0 ≤ G2 n w := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    rw [hRe, abs_of_nonneg (mul_nonneg hG2nn (by linarith [hM0 n w]))]
    calc |∑ i ∈ Finset.range n,
          (2 * Real.log (1 + g n (X i w)) - (2 * g n (X i w) - g n (X i w) ^ 2))|
        ≤ ∑ i ∈ Finset.range n,
          |2 * Real.log (1 + g n (X i w)) - (2 * g n (X i w) - g n (X i w) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, 4 * |g n (X i w)| ^ 3 := Finset.sum_le_sum fun i hi ↦
          abs_two_mul_log_one_add_sub_le ((hMle n w i hi).trans hMw.le)
      _ ≤ ∑ i ∈ Finset.range n, g n (X i w) ^ 2 * (4 * M n w) := Finset.sum_le_sum fun i hi ↦ by
          have h1 := hMle n w i hi
          rw [← sq_abs (g n (X i w))]
          have h2 := abs_nonneg (g n (X i w))
          nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg |g n (X i w)|)]
      _ = G2 n w * (4 * M n w) := by simp only [hG2, Finset.sum_mul]
  have := tendstoInMeasure_add_zero mu _ _
    (tendstoInMeasure_add_zero mu _ _ hR0 (tendstoInMeasure_const_mul_zero mu _ 2 hF2))
    (tendstoInMeasure_const_mul_zero mu _ (-1) hF3)
  convert this using 3 with n w
  simp only [hR, hZ]
  ring

/-- GAPS 102.13: local asymptotic normality from differentiability in quadratic mean, with the
central sequence: the normalized score sum `n^{-1/2} ∑ ℓ̇(Xᵢ)` converges in law to `N(0, I)`, and
the log likelihood ratio has the expansion of
`tendstoInMeasure_log_likelihood_ratio_sub_of_dqm`. -/
theorem tendstoInDistribution_score_and_log_likelihood_ratio_expansion_of_dqm
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (nu : Measure E)
    (P : ℝ → Measure E) (hP : ∀ theta, IsProbabilityMeasure (P theta))
    (f : ℝ → E → ℝ) (hf : ∀ theta, HasDensity (P theta) nu (f theta))
    (hpos : ∀ theta x, 0 < f theta x) (theta₀ : ℝ) (score : E → ℝ)
    (hs : Measurable score) (hs2 : MemLp score 2 (P theta₀))
    (hs0 : (∫ x, score x ∂P theta₀) = 0)
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (theta₀ + h) x) - Real.sqrt (f theta₀ x) -
        h / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu) (fun h : ℝ ↦ h ^ 2))
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X (P theta₀)) :
    TendstoInDistribution (fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, score (X i w))
      atTop id (fun _ ↦ mu)
        (gaussianReal 0 (Real.toNNReal (∫ x, score x ^ 2 ∂P theta₀))) ∧
      ∀ h : ℝ, TendstoInMeasure mu (fun (n : ℕ) w ↦
        (∑ i ∈ Finset.range n, Real.log (f (theta₀ + h / Real.sqrt n) (X i w) / f theta₀ (X i w))) -
          h / Real.sqrt n * (∑ i ∈ Finset.range n, score (X i w)) +
            h ^ 2 * (∫ x, score x ^ 2 ∂P theta₀) / 2) atTop (fun _ ↦ 0) :=
  have := hP theta₀
  ⟨tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu (P theta₀) X hiid score hs hs2 hs0,
    tendstoInMeasure_log_likelihood_ratio_sub_of_dqm mu nu P hP f hf hpos theta₀ score hs
      hs2 hs0 hdqm X hiid⟩

end CKSD
