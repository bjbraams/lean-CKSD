module

public import CKSD.Asymptotics.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Asymptotics: Experiments

Sources: `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
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

/-- Portmanteau for the CKSD weak-convergence predicate: probabilities of sets whose frontier is
null under the limit law converge. -/
theorem tendsto_measureReal_of_tendstoWeakly {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    (μs : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μs n)] (μ : Measure E) [IsProbabilityMeasure μ]
    (h : TendstoWeakly μs μ) (A : Set E) (hA : μ (frontier A) = 0) :
    Tendsto (fun n ↦ (μs n).real A) atTop (𝓝 (μ.real A)) := by
  let ν : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μs n, inferInstance⟩
  let ν₀ : ProbabilityMeasure E := ⟨μ, inferInstance⟩
  have hν : Tendsto ν atTop (𝓝 ν₀) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact h
  have := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν (E := A) hA
  exact (ENNReal.tendsto_toReal (measure_ne_top μ A)).comp this


/-- Weighted weak convergence: if `μₙ ⇒ ν` and a continuous nonnegative weight `w` has integral
one under every `μₙ` and under `ν`, then `∫ w f dμₙ → ∫ w f dν` for bounded continuous `f`. -/
theorem tendsto_integral_mul_of_tendstoWeakly {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)] (ν : Measure X)
    [IsProbabilityMeasure ν] (h : TendstoWeakly μs ν) (w : X → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hμw : ∀ n, ∫ x, w x ∂μs n = 1) (hνw : ∫ x, w x ∂ν = 1)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n ↦ ∫ x, w x * f x ∂μs n) atTop (𝓝 (∫ x, w x * f x ∂ν)) := by
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

/-- GAPS 102.12: Le Cam's first lemma, for absolutely continuous alternatives. -/
theorem isContiguous_of_integral_likelihood_ratio_limit_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (hac : ∀ n, Q n ≪ P n)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlim : TendstoWeakly (fun n ↦ (P n).map (fun ω ↦ ((Q n).rnDeriv (P n) ω).toReal)) ν)
    (hint : Integrable id ν) (hmean : (∫ x, x ∂ν) = 1) :
    IsContiguous P Q := by
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
  have hk' := (hlim (clipBCF k (Nat.cast_nonneg k))).eventually
    (lt_mem_nhds (show 1 - 2 * ε / 3 < ∫ x, clipBCF k (Nat.cast_nonneg k) x ∂ν by linarith))
  have hPk := (hPA.const_mul (k : ℝ)).eventually (gt_mem_nhds (show (k : ℝ) * 0 < ε / 3 by
    rw [mul_zero]; positivity))
  filter_upwards [hk', hPk] with n h1 h2
  have := hkey k (Nat.cast_nonneg k) n
  simp only [hLdef] at this
  linarith

/-- GAPS 102.14: the change-of-law form of the third lemma.
Taking a joint Gaussian limit gives the mean shift stated in GAPS. -/
theorem tendstoWeakly_of_log_likelihood_ratio {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (S : ℕ → Ω → E) (Λ : ℕ → Ω → ℝ)
    (hS : ∀ n, Measurable (S n)) (hΛ : ∀ n, Measurable (Λ n))
    (hrn : ∀ n, Q n = (P n).withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (Λ n ω))))
    (ν : Measure (E × ℝ)) [IsProbabilityMeasure ν]
    (hlim : TendstoWeakly (fun n ↦ (P n).map (fun ω ↦ (S n ω, Λ n ω))) ν)
    (_hint : Integrable (fun z ↦ Real.exp z.2) ν)
    (hmean : (∫ z, Real.exp z.2 ∂ν) = 1) :
    TendstoWeakly (fun n ↦ (Q n).map (S n))
      ((ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp z.2)).map Prod.fst) := by
  intro f
  have hSΛ : ∀ n, Measurable fun ω ↦ (S n ω, Λ n ω) := fun n ↦ (hS n).prodMk (hΛ n)
  have : ∀ n, IsProbabilityMeasure ((P n).map fun ω ↦ (S n ω, Λ n ω)) := fun n ↦ by
    have := hP n; infer_instance
  have hden : ∀ n, Measurable fun ω ↦ ENNReal.ofReal (Real.exp (Λ n ω)) := fun n ↦
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hΛ n))
  have hdenν : Measurable fun z : E × ℝ ↦ ENNReal.ofReal (Real.exp z.2) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd)
  let F : BoundedContinuousFunction (E × ℝ) ℝ := f.compContinuous ⟨Prod.fst, continuous_fst⟩
  have key := tendsto_integral_mul_of_tendstoWeakly _ ν hlim (fun z ↦ Real.exp z.2)
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

/-- GAPS 102.21, local power calculation for a normal limit with mean shift. -/
theorem tendsto_local_normal_power {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (a z : ℝ)
    (hlim : TendstoWeakly (fun n ↦ (P n).map (T n)) (gaussianReal a 1)) :
    Tendsto (fun n ↦ (P n).real {ω | z < T n ω}) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) (z - a))) := by
  have : ∀ n, IsProbabilityMeasure ((P n).map (T n)) := fun n ↦ by
    have := hP n; infer_instance
  have hfr : gaussianReal a 1 (frontier (Ioi z)) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := a) (v := 1) one_ne_zero
    rw [frontier_Ioi]; exact measure_singleton z
  have key := tendsto_measureReal_of_tendstoWeakly _ _ hlim (Ioi z) hfr
  have heq : ∀ n, (P n).real {ω | z < T n ω} = ((P n).map (T n)).real (Ioi z) := by
    intro n
    rw [map_measureReal_apply (hT n) measurableSet_Ioi]; rfl
  simp_rw [heq]
  convert key using 2
  have hcdf : cdf (gaussianReal 0 1) (z - a) = (gaussianReal a 1).real (Iic z) := by
    rw [cdf, show gaussianReal a 1 = (gaussianReal 0 1).map (· + a) by
        rw [gaussianReal_map_add_const, zero_add],
      map_measureReal_apply (measurable_add_const a) measurableSet_Iic]
    congr 1
    ext x; simp [le_sub_iff_add_le]
  rw [hcdf, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- GAPS 102.13, scalar DQM implies LAN, with common strictly positive densities. -/
theorem local_asymptotic_normality_of_differentiable_in_quadratic_mean
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (nu : Measure E) [SigmaFinite nu]
    (P : ℝ → Measure E) (hP : ∀ theta, IsProbabilityMeasure (P theta))
    (f : ℝ → E → ℝ) (hf : ∀ theta, HasDensity (P theta) nu (f theta))
    (hpos : ∀ theta x, 0 < f theta x) (theta₀ : ℝ) (score : E → ℝ)
    (hs : Measurable score) (hs2 : MemLp score 2 (P theta₀))
    (hs0 : (∫ x, score x ∂P theta₀) = 0)
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (theta₀ + h) x) - Real.sqrt (f theta₀ x) -
        h / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu) (fun h : ℝ ↦ h ^ 2))
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X (P theta₀)) :
    let I := ∫ x, score x ^ 2 ∂P theta₀;
    0 < I →
      TendstoInDistribution mu (fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, score (X i w))
        (gaussianReal 0 (Real.toNNReal I)) ∧
      ∀ h : ℝ, TendstoInProbabilityConst mu (fun n w ↦
        (∑ i ∈ Finset.range n, Real.log (f (theta₀ + h / Real.sqrt n) (X i w) / f theta₀ (X i w))) -
          h / Real.sqrt n * (∑ i ∈ Finset.range n, score (X i w)) + h ^ 2 * I / 2) 0 := by
  sorry


end CKSD
