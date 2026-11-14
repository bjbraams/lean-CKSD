module

public import CKSD.Asymptotics.LikelihoodTransfer
public import CKSD.Asymptotics.LikelihoodSingular
public import CKSD.Asymptotics.LANApproximation
/-!
# Likelihood limits without finite-sample absolute continuity

The truncation argument and Lebesgue decomposition transfer weak limits under
the alternatives when the limiting likelihood has unit mean. Closed null events
are controlled by Mathlib Portmanteau. These are the likelihood-transfer steps
in van der Vaart, *Asymptotic Statistics*, Theorem 7.10, printed p. 99.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace CKSD
/-- Le Cam's change-of-law lemma using the actual Radon–Nikodym density, without
finite-sample absolute continuity. Unit mean of the limiting density forces the
singular part of the alternatives to vanish. -/
theorem tendsto_in_distribution_of_joint_rn_deriv
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (S : ∀ n, Ω n → E)
    (hS : ∀ n, Measurable (S n)) (ν : Measure (E × ℝ)) [IsProbabilityMeasure ν]
    (hlim : TendstoInDistribution
      (fun n ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal)) atTop id P ν)
    (hmean : ∫ z, max 0 z.2 ∂ν = 1)
    (L : Measure E) [IsProbabilityMeasure L]
    (hL : (ν.withDensity (fun z ↦ ENNReal.ofReal (max 0 z.2))).map Prod.fst = L) :
    TendstoInDistribution S atTop id Q L := by
  have hm (n : ℕ) : Measurable fun ω ↦ ((Q n).rnDeriv (P n) ω).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpair (n : ℕ) : Measurable fun ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal) :=
    (hS n).prodMk (hm n)
  let μs : ℕ → Measure (E × ℝ) := fun n ↦ (P n).map
    (fun ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal))
  have hwi (n : ℕ) : Integrable (fun z : E × ℝ ↦ max 0 z.2) (μs n) := by
    dsimp only [μs]
    rw [integrable_map_measure (by fun_prop) (hpair n).aemeasurable]
    simpa only [Function.comp_def,max_eq_right ENNReal.toReal_nonneg] using
      (Measure.integrable_toReal_rnDeriv (μ := Q n) (ν := P n))
  have hmass (n : ℕ) : ∫ z : E × ℝ, max 0 z.2 ∂μs n =
      1 - ((Q n).singularPart (P n)).real univ := by
    dsimp only [μs]
    rw [integral_map (hpair n).aemeasurable (by fun_prop)]
    simp only [max_eq_right ENNReal.toReal_nonneg]
    rw [Measure.integral_toReal_rnDeriv',probReal_univ]
  have hwle (n : ℕ) : ∫ z : E × ℝ, max 0 z.2 ∂μs n ≤ 1 := by
    rw [hmass]; exact sub_le_self _ (measureReal_nonneg)
  have hweighted (f : BoundedContinuousFunction (E × ℝ) ℝ) :=
    tendsto_integral_mul_of_tendsto_of_integral_le_one μs ν (by simpa only [μs,Measure.map_id] using hlim.tendsto)
      (fun z ↦ max 0 z.2) (by fun_prop) (fun z ↦ le_max_left _ _) hwi hwle hmean f
  have hmasses : Tendsto (fun n ↦ ∫ ω, ((Q n).rnDeriv (P n) ω).toReal ∂P n)
      atTop (𝓝 1) := by
    have h := hweighted (1 : BoundedContinuousFunction (E × ℝ) ℝ)
    simp only [FunLike.coe_one,Pi.one_apply,mul_one] at h
    rw [hmean] at h
    convert h using 1
    funext n
    dsimp only [μs]
    rw [integral_map (hpair n).aemeasurable (by fun_prop)]
    simp only [max_eq_right ENNReal.toReal_nonneg]
  refine tendsto_in_distribution_id_iff.2 ⟨fun n ↦ (hS n).aemeasurable,
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f ↦ ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  let F : BoundedContinuousFunction (E × ℝ) ℝ := f.compContinuous ⟨Prod.fst,continuous_fst⟩
  have hkey : Tendsto (fun n ↦ ∫ ω, ((Q n).rnDeriv (P n) ω).toReal * f (S n ω) ∂P n)
      atTop (𝓝 (∫ x, f x ∂L)) := by
    convert hweighted F using 1
    · funext n
      dsimp only [μs]
      rw [integral_map (hpair n).aemeasurable (by fun_prop)]
      simp only [F,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
        max_eq_right ENNReal.toReal_nonneg]
    · rw [← hL, integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul (by fun_prop)
          (ae_of_all _ fun z ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (le_max_left _ _),smul_eq_mul,F,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk]
  have hgap : Tendsto (fun n ↦ ‖f‖ *
      (1 - ∫ ω, ((Q n).rnDeriv (P n) ω).toReal ∂P n)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hmasses).const_mul ‖f‖
  have hdiff : Tendsto (fun n ↦ (∫ ω, f (S n ω) ∂Q n) -
      ∫ ω, ((Q n).rnDeriv (P n) ω).toReal * f (S n ω) ∂P n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) hgap
    rw [Real.norm_eq_abs]
    exact abs_integral_sub_integral_rn_deriv_mul_le (P n) (Q n) _
      (f.continuous.measurable.comp (hS n)) ‖f‖ (fun ω ↦ f.norm_coe_le_norm _)
  have h := hdiff.add hkey
  simp only [sub_add_cancel,zero_add] at h
  convert h using 1
  funext n
  rw [integral_map (hS n).aemeasurable f.continuous.aestronglyMeasurable]


/-- A closed null event under a real weak limit has asymptotically zero probability. -/
theorem tendsto_measure_real_eq_zero_of_tendsto_in_distribution
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlim : TendstoInDistribution X atTop id P ν) (hzero : ν {0} = 0) :
    Tendsto (fun n ↦ (P n).real {ω | X n ω = 0}) atTop (𝓝 0) := by
  have hfront : ν (frontier ({0} : Set ℝ)) = 0 :=
    measure_mono_null isClosed_singleton.frontier_subset hzero
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hlim.tendsto (E := ({0} : Set ℝ)) (by simpa only [Measure.map_id,ProbabilityMeasure.coe_mk] using hfront)
  simp only [ProbabilityMeasure.coe_mk,Measure.map_id,hzero] at h
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at ht
  convert ht using 1
  funext n
  change ((P n) {ω | X n ω = 0}).toReal = ((P n).map (X n) {0}).toReal
  rw [Measure.map_apply (hX n) (measurableSet_singleton 0)]
  rfl

/-- Tilting a statistic-density graph and projecting back is the original tilt. -/
theorem map_fst_with_density_map_graph
    {E : Type*} [MeasurableSpace E] (ρ : Measure E) (w : E → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    ((ρ.map (fun x ↦ (x,w x))).withDensity
      (fun z : E × ℝ ↦ ENNReal.ofReal (max 0 z.2))).map Prod.fst =
      ρ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs,
    setLIntegral_map (g := fun x ↦ (x,w x)) (measurable_fst hs) (by fun_prop) (by fun_prop)]
  simp only [Set.preimage_preimage,max_eq_right (hw0 _)]
  rfl


/-- Weak convergence of a log likelihood with no limiting atom at zero also gives
weak convergence of the actual likelihood, despite the convention `Real.log 0 = 0`. -/
theorem tendsto_in_distribution_joint_rn_deriv_of_log
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (S : ∀ n, Ω n → E)
    (hS : ∀ n, Measurable (S n)) (ν : Measure (E × ℝ)) [IsProbabilityMeasure ν]
    (hlim : TendstoInDistribution
      (fun n ω ↦ (S n ω,Real.log (((Q n).rnDeriv (P n) ω).toReal))) atTop id P ν)
    (hzero : ν.snd {0} = 0) :
    TendstoInDistribution (fun n ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal)) atTop id P
      (ν.map (fun z ↦ (z.1,Real.exp z.2))) := by
  have hm (n : ℕ) : Measurable fun ω ↦ ((Q n).rnDeriv (P n) ω).toReal :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hl (n : ℕ) : Measurable fun ω ↦ Real.log (((Q n).rnDeriv (P n) ω).toReal) :=
    Real.measurable_log.comp (hm n)
  have hloglim : TendstoInDistribution
      (fun n ω ↦ Real.log (((Q n).rnDeriv (P n) ω).toReal)) atTop id P ν.snd := by
    refine ⟨fun n ↦ (hl n).aemeasurable,measurable_id.aemeasurable,?_⟩
    simp only [Measure.map_id]
    convert (hlim.continuous_comp continuous_snd).tendsto using 1; rfl
  have hz := tendsto_measure_real_eq_zero_of_tendsto_in_distribution P _ hl ν.snd hloglim hzero
  have hexp := hlim.continuous_comp
    (show Continuous (fun z : E × ℝ ↦ (z.1,Real.exp z.2)) by fun_prop)
  have hRN := tendsto_in_distribution_of_dist_small_in_probability
    (fun n ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal))
    (fun z : E × ℝ ↦ (z.1,Real.exp z.2)) hexp ?_
    (fun n ↦ ((hS n).prodMk (hm n)).aemeasurable)
  · refine ⟨fun n ↦ ((hS n).prodMk (hm n)).aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [Measure.map_id] using hRN.tendsto
  · intro ε hε
    apply squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) hz
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    have heq : ((Q n).rnDeriv (P n) ω).toReal = 0 := by
      by_contra hne
      have he := Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne))
      have hd : dist (S n ω,((Q n).rnDeriv (P n) ω).toReal)
          (S n ω,Real.exp (Real.log (((Q n).rnDeriv (P n) ω).toReal))) = 0 := by
        rw [he]; exact dist_self _
      exact (not_le_of_gt hε) (hd ▸ hω)
    change Real.log (((Q n).rnDeriv (P n) ω).toReal) = 0
    rw [heq,Real.log_zero]

/-- A nonnegative integrable density of real mass one defines a probability measure. -/
theorem is_probability_measure_with_density_of_real_integral_one
    {E : Type*} [MeasurableSpace E] (ρ : Measure E) (w : E → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hi : Integrable w ρ)
    (hm : ∫ x, w x ∂ρ = 1) :
    IsProbabilityMeasure (ρ.withDensity (fun x ↦ ENNReal.ofReal (w x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hw0),hm,ENNReal.ofReal_one]

/-- A limiting likelihood given by a density graph tilts the underlying joint limit. -/
theorem tendsto_in_distribution_of_joint_rn_deriv_graph
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (S : ∀ n, Ω n → E)
    (hS : ∀ n, Measurable (S n)) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (w : E → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hm : ∫ x, w x ∂ρ = 1)
    [IsProbabilityMeasure (ρ.withDensity (fun x ↦ ENNReal.ofReal (w x)))]
    (hlim : TendstoInDistribution
      (fun n ω ↦ (S n ω,((Q n).rnDeriv (P n) ω).toReal)) atTop id P
      (ρ.map (fun x ↦ (x,w x)))) :
    TendstoInDistribution S atTop id Q (ρ.withDensity (fun x ↦ ENNReal.ofReal (w x))) := by
  apply tendsto_in_distribution_of_joint_rn_deriv P Q S hS _ hlim
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simpa only [max_eq_right (hw0 _)] using hm
  · exact map_fst_with_density_map_graph ρ w hw.measurable hw0

end CKSD
