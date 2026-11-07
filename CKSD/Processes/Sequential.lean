module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Statlib.Testing.Sequential.Wald
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Processes: Sequential

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
Wald's identity uses Rémy Degenne's general stopped-sum theorem in
`Statlib.Testing.Sequential.Wald`, with a zero term prepended to account for
this project's convention of summing over `range N`.
Ville's inequality applies Mathlib's optional stopping theorem to the submartingale `-M` at the
hitting time of a level capped at a finite horizon.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 106.37, Wald's stopped-sum identity under the past/future independence condition. -/
theorem integrable_stopped_sum_and_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (hX : Integrable id P)
    (N : Ω → ℕ) (hN : Measurable N) (hNi : Integrable (fun ω ↦ (N ω : ℝ)) μ)
    (hpast : ∀ i : ℕ, IndepFun (X i) (fun ω ↦ decide (i < N ω)) μ) :
    Integrable (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ ∧
      (∫ ω, ∑ i ∈ Finset.range (N ω), X i ω ∂μ) =
        (∫ ω, (N ω : ℝ) ∂μ) * ∫ x, x ∂P := by
  have hlaw (i : ℕ) : IdentDistrib (X i) id μ P :=
    ⟨(hiid.1 i).aemeasurable, measurable_id.aemeasurable, by simp [hiid.2.2 i]⟩
  have hXi (i : ℕ) : Integrable (X i) μ := (hlaw i).integrable_iff.mpr hX
  have hXmean (i : ℕ) : (∫ ω, X i ω ∂μ) = ∫ t, t ∂P := (hlaw i).integral_eq
  have hset (i : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ ω in {ω | i < N ω}, f (X i ω) ∂μ) =
        μ.real {ω | i < N ω} * ∫ t, f t ∂P := by
    let b : Ω → Bool := fun ω ↦ decide (i < N ω)
    have hb : Measurable b :=
      measurable_decide_mem (measurableSet_lt measurable_const hN)
    have hA : MeasurableSet[(inferInstance : MeasurableSpace Bool).comap b]
        {ω | i < N ω} := by
      apply MeasurableSpace.measurableSet_comap.mpr
      exact ⟨{true}, measurableSet_singleton true, by ext ω; simp [b]⟩
    have hind : Indep ((inferInstance : MeasurableSpace Bool).comap b)
        ((inferInstance : MeasurableSpace ℝ).comap (X i)) μ :=
      (IndepFun_iff_Indep _ _ _).mp (hpast i).symm
    rw [Indep.setIntegral_eq_mul hb.comap_le hind (hiid.1 i).aemeasurable hA
      hf.aestronglyMeasurable]
    congr 1
    simpa only [Function.comp_apply, id_eq] using ((hlaw i).comp hf).integral_eq
  let Y : ℕ → Ω → ℝ := fun n ↦ match n with
    | 0 => fun _ ↦ 0
    | n + 1 => X n
  have hYi (n : ℕ) : Integrable (Y n) μ := by
    cases n with
    | zero => simpa [Y] using (integrable_const (μ := μ) (0 : ℝ))
    | succ n => exact hXi n
  have hYind (n : ℕ) : (∫ ω in {ω | n ≤ N ω}, Y n ω ∂μ) =
      μ.real {ω | n ≤ N ω} * ∫ ω, Y n ω ∂μ := by
    cases n with
    | zero => simp [Y]
    | succ n =>
        simpa only [Y, Nat.succ_le_iff, id_eq, (hlaw n).integral_eq] using
          hset n id measurable_id
  have hYsum : Summable (fun n ↦ ∫ ω in {ω | n ≤ N ω}, |Y n ω| ∂μ) := by
    have htail := (hasSum_measureReal_le hNi).summable.mul_right (∫ t, |t| ∂P)
    apply htail.of_nonneg_of_le (fun n ↦ integral_nonneg fun ω ↦ abs_nonneg _)
    intro n
    cases n with
    | zero =>
        simpa [Y] using mul_nonneg
          (show 0 ≤ μ.real {ω | 0 ≤ N ω} from measureReal_nonneg)
          (integral_nonneg (μ := P) fun t ↦ abs_nonneg t)
    | succ n =>
        apply le_of_eq
        simpa only [Y, Nat.succ_le_iff] using (hset n (fun t : ℝ ↦ |t|) continuous_abs.measurable)
  have hsum (ω : Ω) : (∑ i ∈ Finset.Iic (N ω), Y i ω) =
      ∑ i ∈ Finset.range (N ω), X i ω := by
    rw [← Nat.range_succ_eq_Iic]
    simp [Finset.sum_range_succ', Y]
  have hmeanSum (ω : Ω) : (∑ i ∈ Finset.Iic (N ω), ∫ ω', Y i ω' ∂μ) =
      (N ω : ℝ) * ∫ t, t ∂P := by
    rw [← Nat.range_succ_eq_Iic, Finset.sum_range_succ']
    simp [Y, hXmean]
  refine ⟨?_, ?_⟩
  · simpa only [hsum] using integrable_sum_Iic_of_summable
      (fun n ↦ (hYi n).integrableOn) hN hYsum
  · rw [← integral_congr_ae (ae_of_all μ hsum),
      integral_sum_Iic_eq_integral_sum_Iic_integral hYi hN hYind hYsum]
    simp_rw [hmeanSum]
    rw [integral_mul_const]

/-- Finite-horizon maximal bound `c · P(max_{k ≤ n} M_k ≥ c) ≤ 1` for a nonnegative supermartingale
with `M_0 ≤ 1`, by optional stopping at the capped hitting time of `[c, ∞)`. -/
theorem ofReal_mul_measure_exists_le_supermartingale_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (M : ℕ → Ω → ℝ)
    (hsuper : Supermartingale M F μ) (hpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ M n ω)
    (hinit : M 0 ≤ᵐ[μ] fun _ ↦ 1) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ENNReal.ofReal c * μ {ω | ∃ k ≤ n, c ≤ M k ω} ≤ 1 := by
  let π : Ω → WithTop ℕ := fun ω ↦ ((hittingBtwn M {y : ℝ | c ≤ y} 0 n ω : ℕ) : WithTop ℕ)
  have hπ : IsStoppingTime F π :=
    hsuper.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, π ω ≤ n := fun ω ↦ WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
  have h0 : IsStoppingTime F (fun _ : Ω ↦ ((0 : ℕ) : WithTop ℕ)) := isStoppingTime_const F 0
  have hsub : Submartingale (-M) F μ := hsuper.neg
  have hmono := hsub.expected_stoppedValue_mono h0 hπ (fun ω ↦ by simp) hbdd
  let V : Ω → ℝ := fun ω ↦ M (hittingBtwn M {y : ℝ | c ≤ y} 0 n ω) ω
  have hV : stoppedValue (-M) π = fun ω ↦ -V ω := by
    funext ω; rfl
  have hV0 : stoppedValue (-M) (fun _ : Ω ↦ ((0 : ℕ) : WithTop ℕ)) = fun ω ↦ -M 0 ω := by
    funext ω; simp [stoppedValue]
  rw [hV, hV0, integral_neg, integral_neg, neg_le_neg_iff] at hmono
  have hVint : Integrable V μ := by
    have := hsub.integrable_stoppedValue hπ hbdd
    rw [hV] at this
    simpa using this.neg
  have hM0 : (∫ ω, M 0 ω ∂μ) ≤ 1 := by
    calc (∫ ω, M 0 ω ∂μ) ≤ ∫ _ω, (1 : ℝ) ∂μ :=
          integral_mono_ae (hsuper.integrable 0) (integrable_const _) hinit
      _ = 1 := by simp
  have hVpos : 0 ≤ᵐ[μ] V := by
    filter_upwards [ae_all_iff.2 hpos] with ω hω using hω _
  have hsubset : {ω | ∃ k ≤ n, c ≤ M k ω} ⊆ {ω | c ≤ V ω} := by
    intro ω ⟨k, hk, hck⟩
    exact stoppedValue_hittingBtwn_mem (s := {y : ℝ | c ≤ y}) ⟨k, ⟨Nat.zero_le k, hk⟩, hck⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hVpos hVint c
  calc ENNReal.ofReal c * μ {ω | ∃ k ≤ n, c ≤ M k ω}
      ≤ ENNReal.ofReal c * μ {ω | c ≤ V ω} := by gcongr
    _ = ENNReal.ofReal (c * μ.real {ω | c ≤ V ω}) := by
        rw [ENNReal.ofReal_mul hc.le, ofReal_measureReal]
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hmarkov.trans (hmono.trans hM0))
    _ = 1 := ENNReal.ofReal_one

/-- GAPS 106.38: infinite-horizon Ville inequality, including a supremum not attained. -/
theorem measure_iSup_supermartingale_ge_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (M : ℕ → Ω → ℝ)
    (hsuper : Supermartingale M F μ) (hpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ M n ω)
    (hinit : M 0 ≤ᵐ[μ] fun _ ↦ 1) (α : ℝ) (hα : α ∈ Ioo 0 1) :
    μ {ω | ENNReal.ofReal (1 / α) ≤ ⨆ n : ℕ, ENNReal.ofReal (M n ω)} ≤ ENNReal.ofReal α := by
  have hα0 : 0 < α := hα.1
  set S := {ω | ENNReal.ofReal (1 / α) ≤ ⨆ n : ℕ, ENNReal.ofReal (M n ω)}
  have key : ∀ c : ℝ, 0 < c → c < 1 / α → μ S ≤ ENNReal.ofReal (1 / c) := by
    intro c hc hcα
    let A : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, c ≤ M k ω}
    have hA : Monotone A := fun m n hmn ω ⟨k, hk, hck⟩ ↦ ⟨k, hk.trans hmn, hck⟩
    have hsub : S ⊆ ⋃ n, A n := by
      intro ω hω
      have hlt : ENNReal.ofReal c < ⨆ n : ℕ, ENNReal.ofReal (M n ω) :=
        lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hcα) hω
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
      exact mem_iUnion.2 ⟨n, n, le_rfl,
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc.le).1 hn).le⟩
    calc μ S ≤ μ (⋃ n, A n) := measure_mono hsub
      _ = ⨆ n, μ (A n) := hA.measure_iUnion
      _ ≤ ENNReal.ofReal (1 / c) := by
        refine iSup_le fun n ↦ ?_
        rw [one_div, ENNReal.ofReal_inv_of_pos hc, ENNReal.le_inv_iff_mul_le, mul_comm]
        exact ofReal_mul_measure_exists_le_supermartingale_le_one μ F M hsuper hpos hinit hc n
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hαε : 0 < α + ε := by positivity
  calc μ S ≤ ENNReal.ofReal (1 / (1 / (α + ε))) :=
        key _ (by positivity) (one_div_lt_one_div_of_lt hα.1 (by linarith [hε]))
    _ = ENNReal.ofReal α + ε := by
        rw [one_div_one_div, ENNReal.ofReal_add hα.1.le ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- GAPS 106.42: Anscombe's theorem for an observation-dependent random sample size. -/
theorem tendstoInDistribution_random_sampleAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (N : ℕ → Ω → ℕ) (hN : ∀ n, Measurable (N n))
    (hpos : ∀ n ω, 0 < N n ω) (k : ℝ) (hk : 0 < k)
    (hratio : TendstoInProbabilityConst μ (fun n ω ↦ (N n ω : ℝ) / n) k) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt (N n ω) *
      (sampleAverage X (N n ω) ω - ∫ x, x ∂P) / Real.sqrt (variance P id)) (gaussianReal 0 1) := by
  sorry


end CKSD
