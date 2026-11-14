module

public import CKSD.Asymptotics.Statistics
import CKSD.Asymptotics.Estimators


/-!
# Consistency of extremum estimators

Empirical and population criteria, and Wald's consistency theorem for the maximum likelihood
estimator over a compact parameter space (GAPS 102.2). Wald consistency is stated with continuous
positive densities and an integrable envelope of their log likelihoods; the more general
upper-semicontinuous formulation is outside that scope. The proof combines a strict Gibbs
inequality, local integrable majorants on balls, and the weak law of large numbers
`tendsto_in_measure_sample_mean_of_iid` (from Mathlib's strong law). The `√n` rate, linearization,
and asymptotic normality of M-estimators are in `CKSD.Asymptotics.MEstimatorNormality`.

## Main definitions

* `CKSD.empiricalCriterion`, `CKSD.populationCriterion`: sample and population criteria.

## Main results

* `CKSD.integral_log_lt_integral_log_of_with_density_ne`: the strict Gibbs inequality.
* `CKSD.exists_ball_measurable_dominating_integral_lt`: local integrable majorants.
* `CKSD.tendsto_in_measure_mle_of_compact`: Wald consistency of the maximum likelihood estimator
  (GAPS 102.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Empirical average of a real criterion evaluated at a parameter. -/
def empiricalCriterion {Ω X Θ : Type*} (m : Θ → X → ℝ)
    (Xn : ℕ → Ω → X) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (∑ i ∈ Finset.range n, m θ (Xn i ω)) / n

/-- Population criterion under a fixed data-generating law. -/
def populationCriterion {X Θ : Type*} [MeasurableSpace X]
    (P : Measure X) (m : Θ → X → ℝ) (θ : Θ) : ℝ := ∫ x, m θ x ∂P

/-- Strict Gibbs inequality for strictly positive densities: if two probability laws with
strictly positive densities `f, g` differ, then `∫ log g dP_f < ∫ log f dP_f`. -/
theorem integral_log_lt_integral_log_of_with_density_ne {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x)
    (hPf : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f x)))
    (hPg : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x)))
    (hlf : Integrable (fun x ↦ Real.log (f x)) (ν.withDensity fun x ↦ ENNReal.ofReal (f x)))
    (hlg : Integrable (fun x ↦ Real.log (g x)) (ν.withDensity fun x ↦ ENNReal.ofReal (f x)))
    (hne : (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ≠
      ν.withDensity fun x ↦ ENNReal.ofReal (f x)) :
    ∫ x, Real.log (g x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (f x)) <
      ∫ x, Real.log (f x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (f x)) := by
  set P₀ := ν.withDensity fun x ↦ ENNReal.ofReal (f x) with hP₀
  have hfm : Measurable fun x ↦ ENNReal.ofReal (f x) := hf.ennreal_ofReal
  have hint_eq : ∀ h : X → ℝ, ∫ x, h x ∂P₀ = ∫ x, f x * h x ∂ν := by
    intro h
    rw [hP₀, integral_withDensity_eq_integral_toReal_smul hfm
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hfpos _).le, smul_eq_mul]
  set y : X → ℝ := fun x ↦ g x / f x with hy
  have hym : Measurable y := hg.div hf
  have hlintg : ∫⁻ x, ENNReal.ofReal (g x) ∂ν = 1 := by
    have := hPg.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hgint : Integrable g ν := by
    refine ⟨hg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun x ↦ (hgpos x).le)).2 (by rw [hlintg]; exact ENNReal.one_lt_top)⟩
  have hg1 : ∫ x, g x ∂ν = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ (hgpos x).le)
      hg.aestronglyMeasurable, hlintg, ENNReal.toReal_one]
  have hfy : ∀ x, f x * y x = g x := fun x ↦ by
    simp only [hy]; field_simp [(hfpos x).ne']
  have hyint : Integrable y P₀ := by
    rw [hP₀, integrable_withDensity_iff_integrable_smul' hfm
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    refine hgint.congr (ae_of_all _ fun x ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hfpos x).le, smul_eq_mul, hfy]
  have hy1 : ∫ x, y x ∂P₀ = 1 := by
    rw [hint_eq]; simp only [hfy]; exact hg1
  set h : X → ℝ := fun x ↦ y x - 1 - (Real.log (g x) - Real.log (f x)) with hh
  have hlogy : ∀ x, Real.log (y x) = Real.log (g x) - Real.log (f x) := fun x ↦
    Real.log_div (hgpos x).ne' (hfpos x).ne'
  have hh0 : 0 ≤ h := fun x ↦ by
    have := Real.log_le_sub_one_of_pos (div_pos (hgpos x) (hfpos x))
    simp only [hh, Pi.zero_apply, ← hlogy]
    simp only [hy]; linarith
  have hhint : Integrable h P₀ := ((hyint.sub (integrable_const 1)).sub (hlg.sub hlf))
  have hhval : ∫ x, h x ∂P₀ = -(∫ x, Real.log (g x) ∂P₀ - ∫ x, Real.log (f x) ∂P₀) := by
    simp only [hh]
    rw [integral_sub (f := fun x ↦ y x - 1) (g := fun x ↦ Real.log (g x) - Real.log (f x))
      (hyint.sub (integrable_const 1)) (hlg.sub hlf),
      integral_sub hyint (integrable_const 1), integral_sub hlg hlf, hy1]
    simp
  by_contra hcon
  push Not at hcon
  have hzero : ∫ x, h x ∂P₀ = 0 :=
    le_antisymm (by rw [hhval]; linarith) (integral_nonneg hh0)
  have hae := (integral_eq_zero_iff_of_nonneg hh0 hhint).1 hzero
  rw [hP₀, Filter.EventuallyEq, ae_withDensity_iff hfm] at hae
  apply hne
  refine withDensity_congr_ae ?_
  filter_upwards [hae] with x hx
  have hx' := hx (by simpa using hfpos x)
  have hyx : y x = 1 := by
    by_contra hy1'
    have := Real.log_lt_sub_one_of_pos (div_pos (hgpos x) (hfpos x)) hy1'
    simp only [hh, Pi.zero_apply, ← hlogy] at hx'
    simp only [hy] at this hx'
    linarith
  have : g x = f x := by
    have := hfy x; rw [hyx, mul_one] at this; exact this.symm
  rw [this]

/-- Wald's local bracketing step. For a criterion continuous in the parameter of a separable
metric space and dominated by an integrable envelope, if `∫ m θ < c` then on some ball about `θ`
the criterion is dominated by one measurable integrable function with integral below `c`. -/
theorem exists_ball_measurable_dominating_integral_lt {X Θ : Type*} [MeasurableSpace X]
    [MetricSpace Θ] [TopologicalSpace.SeparableSpace Θ] (P₀ : Measure X)
    (m : Θ → X → ℝ) (hm : ∀ θ, Measurable (m θ)) (hcont : ∀ x, Continuous fun θ ↦ m θ x)
    (B : X → ℝ) (hB : Integrable B P₀) (henv : ∀ θ x, |m θ x| ≤ B x) (θ : Θ) {c : ℝ}
    (hc : ∫ x, m θ x ∂P₀ < c) :
    ∃ ρ > 0, ∃ w : X → ℝ, Measurable w ∧ Integrable w P₀ ∧
      (∀ θ' ∈ Metric.ball θ ρ, ∀ x, m θ' x ≤ w x) ∧ ∫ x, w x ∂P₀ < c := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Θ
  let ρ : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hρ : ∀ k, 0 < ρ k := fun k ↦ Nat.one_div_pos_of_nat
  let w : ℕ → X → ℝ := fun k x ↦ ⨆ t : ↥(D ∩ Metric.ball θ (ρ k)), m t x
  have hne : ∀ k, Nonempty ↥(D ∩ Metric.ball θ (ρ k)) := fun k ↦ by
    rw [inter_comm]
    exact (hDd.inter_open_nonempty _ Metric.isOpen_ball
      ⟨θ, Metric.mem_ball_self (hρ k)⟩).to_subtype
  have hcount : ∀ k, Countable ↥(D ∩ Metric.ball θ (ρ k)) := fun k ↦
    (hDc.mono inter_subset_left).to_subtype
  have hbdd : ∀ k x, BddAbove (range fun t : ↥(D ∩ Metric.ball θ (ρ k)) ↦ m t x) := fun k x ↦
    ⟨B x, by rintro _ ⟨t, rfl⟩; exact (abs_le.1 (henv t x)).2⟩
  have hwm : ∀ k, Measurable (w k) := fun k ↦ by
    have := hcount k
    exact Measurable.iSup fun t ↦ hm t
  have hwle : ∀ k x, w k x ≤ B x := fun k x ↦ by
    have := hne k
    exact ciSup_le fun t ↦ (abs_le.1 (henv t x)).2
  have hupper : ∀ k, ∀ θ' ∈ Metric.ball θ (ρ k), ∀ x, m θ' x ≤ w k x := by
    intro k θ' hθ' x
    by_contra hlt
    push Not at hlt
    have hU : IsOpen {t | w k x < m t x} := isOpen_lt continuous_const (hcont x)
    obtain ⟨d, ⟨hdU, hdball⟩, hdD⟩ :=
      hDd.inter_open_nonempty _ (hU.inter Metric.isOpen_ball) ⟨θ', hlt, hθ'⟩
    have : m d x ≤ w k x := le_ciSup (hbdd k x) (⟨d, hdD, hdball⟩ : ↥(D ∩ Metric.ball θ (ρ k)))
    exact absurd hdU (not_lt.2 this)
  have hwge : ∀ k x, -B x ≤ w k x := fun k x ↦
    (abs_le.1 (henv θ x)).1.trans (hupper k θ (Metric.mem_ball_self (hρ k)) x)
  have hwabs : ∀ k x, |w k x| ≤ B x := fun k x ↦ abs_le.2 ⟨hwge k x, hwle k x⟩
  have hlim : ∀ x, Tendsto (fun k ↦ w k x) atTop (𝓝 (m θ x)) := by
    intro x
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun k ↦
      ha.trans_le (hupper k θ (Metric.mem_ball_self (hρ k)) x), fun a ha ↦ ?_⟩
    obtain ⟨δ, hδ, hδm⟩ := Metric.continuous_iff.1 (hcont x) θ ((a - m θ x) / 2) (by linarith)
    have hev : ∀ᶠ k in atTop, ρ k < δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (eventually_lt_nhds hδ)
    filter_upwards [hev] with k hk
    have := hne k
    refine lt_of_le_of_lt (ciSup_le fun t ↦ ?_) (show m θ x + (a - m θ x) / 2 < a by linarith)
    have ht : dist (t : Θ) θ < δ := lt_trans (Metric.mem_ball.1 t.2.2) hk
    have := hδm t ht
    rw [Real.dist_eq] at this
    linarith [le_abs_self (m t x - m θ x)]
  have hwint : ∀ k, Integrable (w k) P₀ := fun k ↦
    hB.mono' (hwm k).aestronglyMeasurable (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]; exact hwabs k x)
  have hDCT : Tendsto (fun k ↦ ∫ x, w k x ∂P₀) atTop (𝓝 (∫ x, m θ x ∂P₀)) :=
    tendsto_integral_of_dominated_convergence B (fun k ↦ (hwm k).aestronglyMeasurable) hB
      (fun k ↦ ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hwabs k x)
      (ae_of_all _ hlim)
  obtain ⟨k, hk⟩ := (hDCT.eventually (eventually_lt_nhds hc)).exists
  exact ⟨ρ k, hρ k, w k, hwm k, hwint k, hupper k, hk⟩

/-- GAPS 102.2: Wald consistency with continuous positive densities on a compact parameter space.
The log-likelihood envelope is integrable at the true law; identifiability concerns the laws,
so no irrelevant distinction between density versions is required. -/
theorem tendsto_in_measure_mle_of_compact
    {Ω X Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MetricSpace Θ] [CompactSpace Θ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Θ → Measure X)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (ν : Measure X)
    (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hcont : ∀ x, Continuous (fun θ ↦ f θ x))
    (hid : Function.Injective P) (θ₀ : Θ) (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn (P θ₀))
    (B : X → ℝ) (hB : Integrable B (P θ₀))
    (henv : ∀ θ x, |Real.log (f θ x)| ≤ B x)
    (T : ℕ → Ω → Θ)
    (r : ℕ → Ω → ℝ) (hr : TendstoInMeasure μ r atTop (fun _ ↦ 0))
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ,
      empiricalCriterion (fun θ x ↦ Real.log (f θ x)) Xn n ω θ₀ - r n ω ≤
        empiricalCriterion (fun θ x ↦ Real.log (f θ x)) Xn n ω (T n ω)) :
    TendstoInMeasure μ T atTop (fun _ ↦ θ₀) := by
  set P₀ := P θ₀ with hP₀
  have := hP θ₀
  set m : Θ → X → ℝ := fun θ x ↦ Real.log (f θ x) with hmdef
  have hmm : ∀ θ, Measurable (m θ) := fun θ ↦ (hf θ).1.log
  have hmc : ∀ x, Continuous fun θ ↦ m θ x := fun x ↦
    (hcont x).log fun θ ↦ (hpos θ x).ne'
  have hmi : ∀ θ, Integrable (m θ) P₀ := fun θ ↦
    hB.mono' (hmm θ).aestronglyMeasurable (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]; exact henv θ x)
  set Mpop : Θ → ℝ := fun θ ↦ ∫ x, m θ x ∂P₀ with hMpop
  have hgibbs : ∀ θ, θ ≠ θ₀ → Mpop θ < Mpop θ₀ := by
    intro θ hθ
    have hP0eq := (hf θ₀).2.2
    have hPeq := (hf θ).2.2
    have hne : P θ ≠ P θ₀ := fun h ↦ hθ (hid h)
    have hP0' : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f θ₀ x)) :=
      hP0eq ▸ hP θ₀
    have hP' : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f θ x)) :=
      hPeq ▸ hP θ
    have hi0 := hmi θ₀
    have hi := hmi θ
    simp only [hMpop, hP₀, hmdef] at hi0 hi ⊢
    rw [hP0eq] at hi0 hi ⊢
    exact integral_log_lt_integral_log_of_with_density_ne ν (f θ₀) (f θ) (hf θ₀).1 (hf θ).1
      (hpos θ₀) (hpos θ) hP0' hP' hi0 hi (by rwa [← hPeq, ← hP0eq])
  -- Local dominating functions.
  have hloc : ∀ θ, ∃ ρ > 0, ∃ w : X → ℝ, Measurable w ∧ Integrable w P₀ ∧
      (∀ θ' ∈ Metric.ball θ ρ, ∀ x, m θ' x ≤ w x) ∧ (θ ≠ θ₀ → ∫ x, w x ∂P₀ < Mpop θ₀) := by
    intro θ
    by_cases hθ : θ = θ₀
    · obtain ⟨ρ, hρ, w, h1, h2, h3, -⟩ := exists_ball_measurable_dominating_integral_lt P₀ m hmm
        hmc B hB henv θ (lt_add_one (Mpop θ))
      exact ⟨ρ, hρ, w, h1, h2, h3, fun h ↦ absurd hθ h⟩
    · obtain ⟨ρ, hρ, w, h1, h2, h3, h4⟩ := exists_ball_measurable_dominating_integral_lt P₀ m hmm
        hmc B hB henv θ (hgibbs θ hθ)
      exact ⟨ρ, hρ, w, h1, h2, h3, fun _ ↦ h4⟩
  choose ρ hρ w hwm hwi hwup hwlt using hloc
  rw [tendsto_in_measure_iff_measure_real_lt_dist]
  intro ε hε
  set K : Set Θ := {θ | ε ≤ dist θ θ₀} with hK
  have hKc : IsCompact K :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  obtain ⟨t, htK, hcover⟩ := hKc.elim_nhds_subcover (fun θ ↦ Metric.ball θ (ρ θ))
    (fun θ _ ↦ Metric.ball_mem_nhds θ (hρ θ))
  have hne0 : ∀ θ ∈ t, θ ≠ θ₀ := fun θ hθ h ↦ by
    have := htK θ hθ
    simp only [hK, mem_ofPred_eq, h, dist_self] at this
    linarith
  set γ : Θ → ℝ := fun θ ↦ Mpop θ₀ - ∫ x, w θ x ∂P₀ with hγ
  have hγpos : ∀ θ ∈ t, 0 < γ θ := fun θ hθ ↦ by
    simp only [hγ]; linarith [hwlt θ (hne0 θ hθ)]
  -- Laws of large numbers for the finitely many statistics involved.
  set Wn : Θ → ℕ → Ω → ℝ := fun θ n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, w θ (Xn i ω)
  set Mn0 : ℕ → Ω → ℝ := fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, m θ₀ (Xn i ω)
  have hW : ∀ θ, TendstoInMeasure μ (Wn θ) atTop (fun _ ↦ ∫ x, w θ x ∂P₀) := fun θ ↦
    tendsto_in_measure_sample_mean_of_iid μ P₀ Xn hiid (w θ) (hwm θ) (hwi θ)
  have hM0 : TendstoInMeasure μ Mn0 atTop (fun _ ↦ Mpop θ₀) :=
    tendsto_in_measure_sample_mean_of_iid μ P₀ Xn hiid (m θ₀) (hmm θ₀) (hmi θ₀)
  set bound : ℕ → ℝ := fun n ↦ ∑ θ ∈ t, (μ.real {ω | γ θ / 4 < dist (Wn θ n ω) (∫ x, w θ x ∂P₀)} +
    μ.real {ω | γ θ / 4 < dist (Mn0 n ω) (Mpop θ₀)} + μ.real {ω | γ θ / 4 < dist (r n ω) 0})
    with hbound
  have hbound0 : Tendsto bound atTop (𝓝 0) := by
    simp only [tendsto_in_measure_iff_measure_real_lt_dist] at hW hM0 hr
    have : Tendsto bound atTop (𝓝 (∑ θ ∈ t, ((0 : ℝ) + 0 + 0))) :=
      tendsto_finsetSum _ fun θ hθ ↦
        ((hW θ _ (by linarith [hγpos θ hθ])).add (hM0 _ (by linarith [hγpos θ hθ]))).add
          (hr _ (by linarith [hγpos θ hθ]))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hbound0
  filter_upwards [eventually_ge_atTop 1] with n hn1
  set N : Set Ω := {ω | ¬ (empiricalCriterion m Xn n ω θ₀ - r n ω ≤
    empiricalCriterion m Xn n ω (T n ω))} with hN
  have hNnull : μ N = 0 := by
    have := hopt n (by omega)
    rwa [ae_iff] at this
  set E : Θ → Set Ω := fun θ ↦ {ω | γ θ / 4 < dist (Wn θ n ω) (∫ x, w θ x ∂P₀)} ∪
    {ω | γ θ / 4 < dist (Mn0 n ω) (Mpop θ₀)} ∪ {ω | γ θ / 4 < dist (r n ω) 0} with hE
  have hsub : {ω | ε < dist (T n ω) θ₀} ⊆ N ∪ ⋃ θ ∈ t, E θ := by
    intro ω hω
    by_cases hωN : ω ∈ N
    · exact Or.inl hωN
    right
    simp only [hN, mem_ofPred_eq, not_not] at hωN
    have hTK : T n ω ∈ K := show ε ≤ dist (T n ω) θ₀ from le_of_lt hω
    obtain ⟨θ, hθt, hTball⟩ := mem_iUnion₂.1 (hcover hTK)
    refine mem_iUnion₂.2 ⟨θ, hθt, ?_⟩
    by_contra hcon
    simp only [hE, mem_union, mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [Real.dist_eq] at h1 h2 h3
    have hγ0 := hγpos θ hθt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hemp0 : empiricalCriterion m Xn n ω θ₀ = Mn0 n ω := by
      simp only [empiricalCriterion, Mn0]; rw [div_eq_inv_mul]
    have hempT : empiricalCriterion m Xn n ω (T n ω) ≤ Wn θ n ω := by
      simp only [empiricalCriterion, Wn]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ hwup θ (T n ω) hTball (Xn i ω)) (inv_nonneg.2 hn0.le)
    have e1 := (abs_le.1 h1).2
    have e2 := (abs_le.1 h2).1
    have e3 := (abs_le.1 h3).2
    simp only [sub_zero] at e3
    have : Mpop θ₀ - ∫ x, w θ x ∂P₀ = γ θ := rfl
    linarith
  calc μ.real {ω | ε < dist (T n ω) θ₀} ≤ μ.real (N ∪ ⋃ θ ∈ t, E θ) := measureReal_mono hsub
    _ ≤ μ.real N + μ.real (⋃ θ ∈ t, E θ) := measureReal_union_le _ _
    _ ≤ 0 + ∑ θ ∈ t, μ.real (E θ) := by
        rw [measureReal_def, hNnull, ENNReal.toReal_zero]
        gcongr
        exact measureReal_biUnion_finset_le _ _
    _ ≤ bound n := by
        rw [zero_add]
        refine Finset.sum_le_sum fun θ _ ↦ ?_
        exact (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)

/-- An empirical criterion is unchanged if its per-observation criterion is translated. -/
theorem empirical_criterion_add_const {Ω X Θ : Type*} (m : Θ → X → ℝ)
    (Xn : ℕ → Ω → X) (n : ℕ) (hn : n ≠ 0) (ω : Ω) (θ : Θ) (c : ℝ) :
    empiricalCriterion (fun θ x ↦ m θ x + c) Xn n ω θ =
      empiricalCriterion m Xn n ω θ + c := by
  simp only [empiricalCriterion, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

end CKSD
