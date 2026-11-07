module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Statlib.Testing.Sequential.Wald
public import Statlib.ForMathlib.MeasureTheory.Measure.Bool
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Independence.Integration
public import CKSD.Asymptotics.Estimators

/-!
# Processes: Sequential

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
Wald's identity uses Rémy Degenne's general stopped-sum theorem in
`Statlib.Testing.Sequential.Wald`, with a zero term prepended to account for
this project's convention of summing over `range N`.
Anscombe's theorem standardizes the observations, applies the central limit theorem along
`⌈k n⌉`, controls the random-index fluctuation with Kolmogorov's maximal inequality, and
concludes with Slutsky's lemma from `CKSD.Asymptotics.Estimators`.
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

/-- Functions measurable with respect to the σ-algebras generated by disjoint index sets of an
independent family are independent. -/
theorem indepFun_of_measurable_biSup {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ι → Ω → ℝ} (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) {S T : Set ι}
    (hST : Disjoint S T) {U V : Ω → ℝ}
    (hU : Measurable[⨆ i ∈ S, MeasurableSpace.comap (Y i) inferInstance] U)
    (hV : Measurable[⨆ i ∈ T, MeasurableSpace.comap (Y i) inferInstance] V) :
    IndepFun U V μ := by
  have h := indep_iSup_of_disjoint (m := fun i ↦ MeasurableSpace.comap (Y i) inferInstance)
    (fun i ↦ (hm i).comap_le) hind.iIndep hST
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h hU.comap_le) hV.comap_le

/-- A finite partial sum over indices in `S` is measurable for the σ-algebra generated by `S`. -/
theorem measurable_biSup_sum {Ω ι : Type*} [MeasurableSpace Ω] {Y : ι → Ω → ℝ} {S : Set ι}
    (s : Finset ι) (hs : ∀ i ∈ s, i ∈ S) :
    Measurable[⨆ i ∈ S, MeasurableSpace.comap (Y i) inferInstance]
      fun ω ↦ ∑ i ∈ s, Y i ω :=
  Finset.measurable_fun_sum _ fun i hi ↦
    Measurable.of_comap_le (le_iSup₂_of_le i (hs i hi) le_rfl)

/-- The σ-algebra generated by a subfamily of measurable functions is coarser than the ambient one. -/
theorem measurable_biSup_le {Ω ι : Type*} [MeasurableSpace Ω] {Y : ι → Ω → ℝ}
    (hm : ∀ i, Measurable (Y i)) (S : Set ι) :
    (⨆ i ∈ S, MeasurableSpace.comap (Y i) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ ↦ (hm i).comap_le

/-- **Kolmogorov's maximal inequality** for independent, centred, square-integrable variables. -/
theorem sq_mul_measureReal_exists_le_abs_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (h2 : ∀ i, MemLp (Y i) 2 μ) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    c ^ 2 * μ.real {ω | ∃ j ≤ r, c ≤ |∑ i ∈ Finset.range j, Y i ω|} ≤
      ∫ ω, (∑ i ∈ Finset.range r, Y i ω) ^ 2 ∂μ := by
  set S : ℕ → Ω → ℝ := fun j ω ↦ ∑ i ∈ Finset.range j, Y i ω with hS
  have hSm : ∀ j, Measurable (S j) := fun j ↦ Finset.measurable_fun_sum _ fun i _ ↦ hm i
  have hS2 : ∀ j, MemLp (S j) 2 μ := fun j ↦ memLp_finsetSum _ fun i _ ↦ h2 i
  let A : ℕ → Set Ω := fun k ↦ {ω | c ≤ |S k ω| ∧ ∀ i < k, |S i ω| < c}
  have hAm : ∀ k, MeasurableSet (A k) := fun k ↦ by
    have : A k = {ω | c ≤ |S k ω|} ∩ ⋂ i ∈ Finset.range k, {ω | |S i ω| < c} := by
      ext ω; simp [A]
    rw [this]
    exact (measurableSet_le measurable_const (continuous_abs.measurable.comp (hSm k))).inter
      (Finset.measurableSet_biInter _ fun i _ ↦ measurableSet_lt (continuous_abs.measurable.comp (hSm i)) measurable_const)
  have hunion : {ω | ∃ j ≤ r, c ≤ |S j ω|} ⊆ ⋃ k ∈ Finset.range (r + 1), A k := by
    intro ω ⟨j, hj, hcj⟩
    classical
    let k := Nat.find (⟨j, hcj⟩ : ∃ k, c ≤ |S k ω|)
    have hk : c ≤ |S k ω| := Nat.find_spec (⟨j, hcj⟩ : ∃ k, c ≤ |S k ω|)
    have hkj : k ≤ j := Nat.find_min' _ hcj
    refine mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (by omega), hk, fun i hi ↦ ?_⟩
    exact not_le.1 (Nat.find_min (⟨j, hcj⟩ : ∃ k, c ≤ |S k ω|) hi)
  have hdisj : ∀ k k' ω, ω ∈ A k → ω ∈ A k' → k = k' := by
    intro k k' ω h h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd h.1 (not_le.2 (h'.2 k hlt))
    · exact absurd h'.1 (not_le.2 (h.2 k' hlt))
  -- the key estimate on each `A k`
  have hkey : ∀ k ≤ r, c ^ 2 * μ.real (A k) ≤ ∫ ω, (A k).indicator (fun ω ↦ S r ω ^ 2) ω ∂μ := by
    intro k hk
    set D : Ω → ℝ := fun ω ↦ S r ω - S k ω
    have hD : D = fun ω ↦ ∑ i ∈ Finset.Ico k r, Y i ω := by
      funext ω; simp only [D, hS]; rw [Finset.sum_Ico_eq_sub _ hk]
    have hD2 : MemLp D 2 μ := (hS2 r).sub (hS2 k)
    have hD0 : ∫ ω, D ω ∂μ = 0 := by
      rw [hD, integral_finsetSum _ fun i _ ↦ (h2 i).integrable one_le_two]
      simp [h0]
    let U : Ω → ℝ := (A k).indicator (S k)
    have hU2 : MemLp U 2 μ := (hS2 k).indicator (hAm k).nullMeasurableSet
    have hUm : Measurable[⨆ i ∈ {i | i < k}, MeasurableSpace.comap (Y i) inferInstance] U := by
      have hA' : MeasurableSet[⨆ i ∈ {i | i < k}, MeasurableSpace.comap (Y i) inferInstance]
          (A k) := by
        have : A k = {ω | c ≤ |S k ω|} ∩ ⋂ i ∈ Finset.range k, {ω | |S i ω| < c} := by
          ext ω; simp [A]
        rw [this]
        have hSm' : ∀ j ≤ k, Measurable[⨆ i ∈ {i | i < k},
            MeasurableSpace.comap (Y i) inferInstance] (S j) := fun j hj ↦
          measurable_biSup_sum _ fun i hi ↦ by simp at hi ⊢; omega
        exact (measurableSet_le measurable_const (continuous_abs.measurable.comp (hSm' k le_rfl))).inter
          (Finset.measurableSet_biInter _ fun i hi ↦
            measurableSet_lt (continuous_abs.measurable.comp (hSm' i (Finset.mem_range.1 hi).le)) measurable_const)
      exact (measurable_biSup_sum (S := {i | i < k}) (Y := Y) (Finset.range k)
        fun i hi ↦ by simpa using hi).indicator hA'
    have hDm : Measurable[⨆ i ∈ {i | k ≤ i}, MeasurableSpace.comap (Y i) inferInstance] D := by
      rw [hD]
      exact measurable_biSup_sum _ fun i hi ↦ by simp at hi ⊢; omega
    have hUD : IndepFun U D μ := indepFun_of_measurable_biSup hm hind
      (Set.disjoint_left.2 fun i (hi : i < k) (hi' : k ≤ i) ↦ by omega) hUm hDm
    have hcross : ∫ ω, U ω * D ω ∂μ = 0 := by
      have := IndepFun.integral_mul_eq_mul_integral hUD hU2.aestronglyMeasurable
        hD2.aestronglyMeasurable
      simpa [hD0] using this
    have hpt : ∀ ω, (A k).indicator (fun ω ↦ S r ω ^ 2) ω =
        (A k).indicator (fun ω ↦ S k ω ^ 2) ω + 2 * (U ω * D ω) +
          (A k).indicator (fun ω ↦ D ω ^ 2) ω := by
      intro ω
      by_cases h : ω ∈ A k
      · simp only [Set.indicator_of_mem h, U, D]; ring
      · simp [Set.indicator_of_notMem h, U]
    have hI1 : Integrable ((A k).indicator fun ω ↦ S k ω ^ 2) μ :=
      (hS2 k).integrable_sq.indicator (hAm k)
    have hI2 : Integrable (fun ω ↦ U ω * D ω) μ := hU2.integrable_mul hD2
    have hI3 : Integrable ((A k).indicator fun ω ↦ D ω ^ 2) μ :=
      hD2.integrable_sq.indicator (hAm k)
    have hsplit : ∫ ω, ((A k).indicator (fun ω ↦ S k ω ^ 2) ω + 2 * (U ω * D ω) +
        (A k).indicator (fun ω ↦ D ω ^ 2) ω) ∂μ =
        ∫ ω, (A k).indicator (fun ω ↦ S k ω ^ 2) ω ∂μ + 2 * ∫ ω, U ω * D ω ∂μ +
          ∫ ω, (A k).indicator (fun ω ↦ D ω ^ 2) ω ∂μ := by
      have hI12 : Integrable (fun ω ↦ (A k).indicator (fun ω ↦ S k ω ^ 2) ω +
          2 * (U ω * D ω)) μ := hI1.add (hI2.const_mul 2)
      have hI2' : Integrable (fun ω ↦ 2 * (U ω * D ω)) μ := hI2.const_mul 2
      rw [integral_add hI12 hI3, integral_add hI1 hI2', integral_const_mul]
    rw [integral_congr_ae (ae_of_all _ hpt), hsplit, hcross]
    have h3 : 0 ≤ ∫ ω, (A k).indicator (fun ω ↦ D ω ^ 2) ω ∂μ :=
      integral_nonneg fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω
    have h1 : c ^ 2 * μ.real (A k) ≤ ∫ ω, (A k).indicator (fun ω ↦ S k ω ^ 2) ω ∂μ := by
      rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ (hAm k)]
      refine integral_mono ((integrable_const _).indicator (hAm k)) hI1 fun ω ↦ ?_
      by_cases h : ω ∈ A k
      · simp only [Set.indicator_of_mem h]
        have := h.1
        rw [← sq_abs (S k ω)]
        exact pow_le_pow_left₀ hc.le this 2
      · simp [Set.indicator_of_notMem h]
    linarith
  calc c ^ 2 * μ.real {ω | ∃ j ≤ r, c ≤ |S j ω|}
      ≤ c ^ 2 * ∑ k ∈ Finset.range (r + 1), μ.real (A k) := by
        gcongr
        exact (measureReal_mono hunion (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    _ = ∑ k ∈ Finset.range (r + 1), c ^ 2 * μ.real (A k) := Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ Finset.range (r + 1), ∫ ω, (A k).indicator (fun ω ↦ S r ω ^ 2) ω ∂μ :=
        Finset.sum_le_sum fun k hk ↦ hkey k (by simpa [Nat.lt_succ_iff] using hk)
    _ = ∫ ω, ∑ k ∈ Finset.range (r + 1), (A k).indicator (fun ω ↦ S r ω ^ 2) ω ∂μ :=
        (integral_finsetSum _ fun k _ ↦ (hS2 r).integrable_sq.indicator (hAm k)).symm
    _ ≤ ∫ ω, S r ω ^ 2 ∂μ := by
        refine integral_mono (integrable_finsetSum _ fun k _ ↦
          (hS2 r).integrable_sq.indicator (hAm k)) (hS2 r).integrable_sq fun ω ↦ ?_
        by_cases h : ∃ k ∈ Finset.range (r + 1), ω ∈ A k
        · obtain ⟨k, hk, hωk⟩ := h
          rw [Finset.sum_eq_single k (fun k' _ hk' ↦ Set.indicator_of_notMem
            (fun h' ↦ hk' (hdisj _ _ _ h' hωk)) _) (fun h' ↦ absurd hk h'),
            Set.indicator_of_mem hωk]
        · push Not at h
          rw [Finset.sum_eq_zero fun k hk ↦ Set.indicator_of_notMem (h k hk) _]
          exact sq_nonneg _


/-- For independent standardized variables, a block sum of length `n` has second moment `n`. -/
theorem integral_sq_sum_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (h2 : ∀ i, MemLp (Y i) 2 μ) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (h1 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1) (a n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y (a + i) ω) ^ 2 ∂μ = n := by
  have hS2 : MemLp (fun ω ↦ ∑ i ∈ Finset.range n, Y (a + i) ω) 2 μ :=
    memLp_finsetSum _ fun i _ ↦ h2 _
  have hmean : ∫ ω, ∑ i ∈ Finset.range n, Y (a + i) ω ∂μ = 0 := by
    rw [integral_finsetSum _ fun i _ ↦ (h2 _).integrable one_le_two]; simp [h0]
  have hvar := IndepFun.variance_sum (μ := μ) (X := fun i ↦ Y (a + i)) (s := Finset.range n)
    (fun i _ ↦ h2 _) (fun i _ j _ hij ↦ hind.indepFun (by omega))
  have hv : ∀ i, ProbabilityTheory.variance (Y i) μ = 1 := fun i ↦ by
    rw [variance_of_integral_eq_zero (hm i).aemeasurable (h0 i), h1 i]
  simp only [hv, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hvar
  rw [variance_of_integral_eq_zero (Finset.aemeasurable_sum _ fun i _ ↦ (hm _).aemeasurable)
    (by simpa only [Finset.sum_apply] using hmean)] at hvar
  simpa only [Finset.sum_apply] using hvar

/-- Kolmogorov's maximal inequality for a block of `r` standardized independent variables. -/
theorem sq_mul_measureReal_exists_le_abs_sum_shift_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (h2 : ∀ i, MemLp (Y i) 2 μ) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (h1 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1) (a r : ℕ) {c : ℝ} (hc : 0 < c) :
    c ^ 2 * μ.real {ω | ∃ j ≤ r, c ≤ |∑ i ∈ Finset.range j, Y (a + i) ω|} ≤ r := by
  have := sq_mul_measureReal_exists_le_abs_sum_le μ (fun i ↦ Y (a + i)) (fun i ↦ hm _)
    (hind.precomp (add_right_injective a)) (fun i ↦ h2 _) (fun i ↦ h0 _) r hc
  rwa [integral_sq_sum_shift hm hind h2 h0 h1 a r] at this


/-- Anscombe's comparison: when `N n / n → k` in probability, the partial sum at the random
index `N n` differs from the partial sum at `⌈k n⌉` by `o_P(√⌈k n⌉)`. -/
theorem tendstoInProbabilityConst_sum_randomIndex_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (h2 : ∀ i, MemLp (Y i) 2 μ) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (h1 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1) (N : ℕ → Ω → ℕ) (k : ℝ) (hk : 0 < k)
    (hratio : TendstoInProbabilityConst μ (fun n ω ↦ (N n ω : ℝ) / n) k) :
    TendstoInProbabilityConst μ (fun n ω ↦
      ((∑ i ∈ Finset.range (N n ω), Y i ω) - ∑ i ∈ Finset.range ⌈k * n⌉₊, Y i ω) /
        Real.sqrt ⌈k * n⌉₊) 0 := by
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  set δ : ℝ := min (η * ε ^ 2 / 16) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδη : 8 * δ / ε ^ 2 ≤ η / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := min_le_left (η * ε ^ 2 / 16) 1
    nlinarith
  set M : ℕ → ℕ := fun n ↦ ⌈k * n⌉₊ with hM
  set r : ℕ → ℕ := fun n ↦ ⌊δ * M n⌋₊ with hr
  set a : ℕ → ℕ := fun n ↦ M n - r n with ha
  have hrM : ∀ n, r n ≤ M n := fun n ↦ by
    simp only [hr]
    refine Nat.floor_le_of_le ?_
    have : (0 : ℝ) ≤ M n := Nat.cast_nonneg _
    nlinarith
  have hMge : ∀ n : ℕ, k * n ≤ M n := fun n ↦ Nat.le_ceil _
  have hMle : ∀ n : ℕ, (M n : ℝ) < k * n + 1 := fun n ↦ Nat.ceil_lt_add_one (by positivity)
  have hrge : ∀ n, δ * M n - 1 < r n := fun n ↦ by
    simp only [hr]; exact Nat.sub_one_lt_floor _
  have hrle : ∀ n, (r n : ℝ) ≤ δ * M n := fun n ↦ Nat.floor_le (by positivity)
  -- the event where the random index leaves the window
  have hE1 : ∀ᶠ n in atTop, μ.real {ω | ¬ (a n ≤ N n ω ∧ N n ω ≤ M n + r n)} ≤ η / 2 := by
    have hev := (hratio (δ * k / 4) (by positivity)).eventually (gt_mem_nhds (half_pos hη))
    have hinv : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ ≤ δ * k / 4 :=
      (tendsto_inv_atTop_nhds_zero_nat.eventually (ge_mem_nhds (by positivity)))
    filter_upwards [hev, hinv, eventually_gt_atTop 0] with n hn hninv hn0
    refine le_trans (measureReal_mono fun ω hω ↦ ?_) hn.le
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    simp only [mem_ofPred_eq, Real.dist_eq] at hω ⊢
    have hMn : (M n : ℝ) / n - k ≤ δ * k / 4 := by
      rw [div_sub' hn'.ne', div_le_iff₀ hn']
      have := hMle n
      have h' : (1 : ℝ) ≤ δ * k / 4 * n := by
        rw [inv_le_iff_one_le_mul₀' hn'] at hninv; linarith
      linarith
    have hMn' : k ≤ (M n : ℝ) / n := by rw [le_div_iff₀ hn']; linarith [hMge n]
    have hMa : (a n : ℝ) = M n - r n := by simp only [ha]; push_cast [hrM n]; ring
    rcases not_and_or.1 hω with h | h
    · have h' : (N n ω : ℝ) + 1 ≤ a n := by exact_mod_cast not_le.1 h
      rw [hMa] at h'
      have hr' := hrge n
      have : (N n ω : ℝ) / n + δ * k / 2 < k := by
        have e1 : (N n ω : ℝ) / n ≤ (M n - r n - 1) / n := by
          gcongr; linarith
        have e2 : ((M n : ℝ) - r n - 1) / n < (M n : ℝ) / n - δ * (M n / n) := by
          rw [div_lt_iff₀ hn']
          field_simp
          linarith
        have e3 : δ * k ≤ δ * (M n / n) := by gcongr
        linarith
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    · have h' : (M n : ℝ) + r n + 1 ≤ N n ω := by exact_mod_cast not_le.1 h
      have hr' := hrge n
      have : k + δ * k / 2 < (N n ω : ℝ) / n := by
        have e1 : ((M n : ℝ) + r n + 1) / n ≤ (N n ω : ℝ) / n := by gcongr
        have e2 : (M n : ℝ) / n + δ * (M n / n) < ((M n : ℝ) + r n + 1) / n := by
          rw [lt_div_iff₀ hn']
          field_simp
          linarith
        have e3 : δ * k ≤ δ * (M n / n) := by gcongr
        linarith
      rw [abs_of_pos (by linarith)]
      linarith
  -- the maximal event
  have hE2 : ∀ᶠ n in atTop, μ.real {ω | ∃ j ≤ 2 * r n,
      ε * Real.sqrt (M n) / 2 ≤ |∑ i ∈ Finset.range j, Y (a n + i) ω|} ≤ η / 2 := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hMpos : (0 : ℝ) < M n := by
      have : (0 : ℝ) < k * n := by positivity
      linarith [hMge n]
    have hc : 0 < ε * Real.sqrt (M n) / 2 := by positivity
    have hK := sq_mul_measureReal_exists_le_abs_sum_shift_le hm hind h2 h0 h1 (a n)
      (2 * r n) hc
    have hc2 : (ε * Real.sqrt (M n) / 2) ^ 2 = ε ^ 2 * M n / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hMpos.le]; norm_num
    rw [hc2] at hK
    have hr2 : ((2 * r n : ℕ) : ℝ) ≤ 2 * δ * M n := by push_cast; nlinarith [hrle n]
    calc _ ≤ ((2 * r n : ℕ) : ℝ) / (ε ^ 2 * M n / 4) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ 2 * δ * M n / (ε ^ 2 * M n / 4) := by gcongr
      _ = 8 * δ / ε ^ 2 := by field_simp; ring
      _ ≤ η / 2 := hδη
  filter_upwards [hE1, hE2, eventually_gt_atTop 0] with n h1n h2n hn0
  have hMpos : (0 : ℝ) < M n := by
    have : (0 : ℝ) < k * n := by positivity
    linarith [hMge n]
  calc μ.real {ω | ε < dist (((∑ i ∈ Finset.range (N n ω), Y i ω) -
          ∑ i ∈ Finset.range ⌈k * n⌉₊, Y i ω) / Real.sqrt ⌈k * n⌉₊) 0}
      ≤ μ.real ({ω | ¬ (a n ≤ N n ω ∧ N n ω ≤ M n + r n)} ∪ {ω | ∃ j ≤ 2 * r n,
          ε * Real.sqrt (M n) / 2 ≤ |∑ i ∈ Finset.range j, Y (a n + i) ω|}) := by
        refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
        simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, mem_union] at hω ⊢
        by_contra hcon
        push Not at hcon
        obtain ⟨⟨hlo, hhi⟩, hmax⟩ := hcon
        have hsplit : ∀ j, ∑ i ∈ Finset.range (a n + j), Y i ω =
            ∑ i ∈ Finset.range (a n), Y i ω + ∑ i ∈ Finset.range j, Y (a n + i) ω :=
          fun j ↦ Finset.sum_range_add _ _ _
        have hNa : N n ω = a n + (N n ω - a n) := by omega
        have hMa : M n = a n + r n := by have := hrM n; simp only [ha]; omega
        have h1 := hmax (N n ω - a n) (by have := hrM n; simp only [ha] at hlo ⊢; omega)
        have h2 := hmax (r n) (by omega)
        have hdiff : (∑ i ∈ Finset.range (N n ω), Y i ω) - ∑ i ∈ Finset.range (M n), Y i ω =
            ∑ i ∈ Finset.range (N n ω - a n), Y (a n + i) ω -
              ∑ i ∈ Finset.range (r n), Y (a n + i) ω := by
          conv_lhs => rw [hNa, hMa, hsplit, hsplit]
          ring
        have hsq : 0 < Real.sqrt (M n) := Real.sqrt_pos.2 hMpos
        change ε < |((∑ i ∈ Finset.range (N n ω), Y i ω) - ∑ i ∈ Finset.range (M n), Y i ω) /
          Real.sqrt (M n)| at hω
        rw [hdiff, abs_div, abs_of_pos hsq, lt_div_iff₀ hsq] at hω
        have := abs_sub _ _ |>.trans_lt (add_lt_add h1 h2)
        linarith
    _ ≤ μ.real {ω | ¬ (a n ≤ N n ω ∧ N n ω ≤ M n + r n)} + μ.real {ω | ∃ j ≤ 2 * r n,
          ε * Real.sqrt (M n) / 2 ≤ |∑ i ∈ Finset.range j, Y (a n + i) ω|} :=
        measureReal_union_le _ _
    _ ≤ η := by linarith


/-- If `W n` converges in law and `R n → 1` in probability, then `R n W n - W n → 0` in
probability. -/
theorem tendstoInProbabilityConst_mul_sub_self {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → ℝ) (hW : ∀ n, Measurable (W n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hWν : TendstoInDistribution μ W ν)
    (R : ℕ → Ω → ℝ) (hR : TendstoInProbabilityConst μ R 1) :
    TendstoInProbabilityConst μ (fun n ω ↦ R n ω * W n ω - W n ω) 0 := by
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨K, hK, hev⟩ :=
    exists_measureReal_lt_norm_le_of_tendstoInDistribution μ W hW ν hWν (half_pos hη)
  have hR' := (hR (ε / K) (div_pos hε hK)).eventually (gt_mem_nhds (half_pos hη))
  filter_upwards [hev, hR'] with n h1 h2
  calc μ.real {ω | ε < dist (R n ω * W n ω - W n ω) 0}
      ≤ μ.real ({ω | K < ‖W n ω‖} ∪ {ω | ε / K < dist (R n ω) 1}) := by
        refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
        simp only [mem_ofPred_eq, mem_union, Real.dist_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
        by_contra hcon
        push Not at hcon
        have : |R n ω * W n ω - W n ω| ≤ ε := by
          rw [show R n ω * W n ω - W n ω = (R n ω - 1) * W n ω by ring, abs_mul]
          calc |R n ω - 1| * |W n ω| ≤ ε / K * K :=
                mul_le_mul hcon.2 hcon.1 (abs_nonneg _) (by positivity)
            _ = ε := div_mul_cancel₀ ε hK.ne'
        linarith
    _ ≤ μ.real {ω | K < ‖W n ω‖} + μ.real {ω | ε / K < dist (R n ω) 1} :=
        measureReal_union_le _ _
    _ ≤ η := by linarith

/-- If `N n / n → k > 0` in probability, then `√(⌈k n⌉ / N n) → 1` in probability. -/
theorem tendstoInProbabilityConst_sqrt_ceil_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ → Ω → ℕ) (k : ℝ) (hk : 0 < k)
    (hratio : TendstoInProbabilityConst μ (fun n ω ↦ (N n ω : ℝ) / n) k) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt ((⌈k * n⌉₊ : ℝ) / N n ω)) 1 := by
  intro ε hε
  have hcont : ContinuousAt (fun p : ℝ × ℝ ↦ Real.sqrt (p.1 / p.2)) (k, k) :=
    (continuousAt_fst.div continuousAt_snd hk.ne').sqrt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont ε hε
  simp only [div_self hk.ne', Real.sqrt_one] at hδc
  have hM : Tendsto (fun n : ℕ ↦ (⌈k * n⌉₊ : ℝ) / n) atTop (𝓝 k) := by
    have h1 : Tendsto (fun n : ℕ ↦ k + (n : ℝ)⁻¹) atTop (𝓝 k) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat.const_add k
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn']; exact Nat.le_ceil _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hn', add_mul, inv_mul_cancel₀ hn'.ne']
      exact (Nat.ceil_lt_add_one (by positivity)).le
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
    (hratio (δ / 2) (half_pos hδ))
  filter_upwards [hM.eventually (Metric.ball_mem_nhds k (half_pos hδ)),
    eventually_gt_atTop 0] with n hn hn0
  refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hd : dist (((⌈k * n⌉₊ : ℝ) / n, (N n ω : ℝ) / n)) (k, k) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨lt_trans (Metric.mem_ball.1 hn) (half_lt_self hδ),
      lt_of_le_of_lt hcon (half_lt_self hδ)⟩
  have := hδc hd
  simp only at this
  rw [div_div_div_cancel_right₀ hn'.ne'] at this
  linarith


/-- Evaluating a sequence of measurable functions at a measurable random index is measurable. -/
theorem measurable_randomIndex {Ω : Type*} [MeasurableSpace Ω] {g : ℕ → Ω → ℝ}
    (hg : ∀ j, Measurable (g j)) {N : Ω → ℕ} (hN : Measurable N) :
    Measurable fun ω ↦ g (N ω) ω :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ℕ ↦ g p.2 p.1) hg).comp
    (measurable_id.prodMk hN)

/-- The standardized sample average at a fixed sample size is measurable. -/
theorem measurable_sqrt_mul_sampleAverage_sub {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (j : ℕ) (m σ : ℝ) :
    Measurable fun ω ↦ Real.sqrt j * (sampleAverage X j ω - m) / σ := by
  have : Measurable fun ω ↦ ∑ i ∈ Finset.range j, X i ω := Finset.measurable_sum _ fun i _ ↦ hX i
  unfold sampleAverage
  simp only [smul_eq_mul]
  fun_prop

/-- GAPS 106.42: Anscombe's theorem for an observation-dependent random sample size. -/
theorem tendstoInDistribution_random_sampleAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (N : ℕ → Ω → ℕ) (hN : ∀ n, Measurable (N n))
    (hpos : ∀ n ω, 0 < N n ω) (k : ℝ) (hk : 0 < k)
    (hratio : TendstoInProbabilityConst μ (fun n ω ↦ (N n ω : ℝ) / n) k) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt (N n ω) *
      (sampleAverage X (N n ω) ω - ∫ x, x ∂P) / Real.sqrt (variance P id)) (gaussianReal 0 1) := by
  set m : ℝ := ∫ x, x ∂P with hmdef
  set σ : ℝ := Real.sqrt (variance P id) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hv
  set s : ℝ → ℝ := fun x ↦ (x - m) * σ⁻¹ with hsdef
  have hs : Measurable s := by fun_prop
  have hint : Integrable (fun x : ℝ ↦ x) P := MemLp.integrable one_le_two h2
  have hs2 : MemLp s 2 P := by
    have h3 : MemLp (fun x : ℝ ↦ x - m) 2 P := MemLp.sub (f := fun x : ℝ ↦ x) h2 (memLp_const m)
    exact MemLp.mul_const h3 σ⁻¹
  have hs0 : ∫ x, s x ∂P = 0 := by
    simp only [hsdef]
    rw [integral_mul_const, integral_sub hint (integrable_const m)]
    simp [hmdef]
  have hs1 : ∫ x, s x ^ 2 ∂P = 1 := by
    simp only [hsdef, mul_pow]
    rw [integral_mul_const]
    have : variance P id = ∫ x, (x - m) ^ 2 ∂P := rfl
    rw [← this, inv_pow, hσdef, Real.sq_sqrt hv.le, mul_inv_cancel₀ hv.ne']
  set Y : ℕ → Ω → ℝ := fun i ω ↦ s (X i ω) with hYdef
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hs.comp (hiid.1 i)
  have hYind : iIndepFun Y μ := hiid.2.1.comp (fun _ ↦ s) (fun _ ↦ hs)
  have hY2 : ∀ i, MemLp (Y i) 2 μ := fun i ↦
    MemLp.comp_of_map (g := s) (f := X i) (by rw [hiid.2.2 i]; exact hs2) (hiid.1 i).aemeasurable
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := fun i ↦ by
    rw [← hs0, ← hiid.2.2 i, integral_map (hiid.1 i).aemeasurable hs.aestronglyMeasurable]
  have hY1 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1 := fun i ↦ by
    rw [← hs1, ← hiid.2.2 i, integral_map (hiid.1 i).aemeasurable (by fun_prop)]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid s hs hs2 hs0
  rw [hs1, Real.toNNReal_one] at hclt
  set M : ℕ → ℕ := fun n ↦ ⌈k * n⌉₊ with hMdef
  have hMtop : Tendsto M atTop atTop :=
    tendsto_nat_ceil_atTop.comp (Tendsto.const_mul_atTop hk tendsto_natCast_atTop_atTop)
  have hSm : ∀ j, Measurable fun ω ↦ ∑ i ∈ Finset.range j, Y i ω := fun j ↦
    Finset.measurable_sum _ fun i _ ↦ hYm i
  set Z : ℕ → Ω → ℝ := fun n ω ↦ (Real.sqrt (M n))⁻¹ * ∑ i ∈ Finset.range (M n), Y i ω
  have hZm : ∀ n, Measurable (Z n) := fun n ↦ (hSm (M n)).const_mul _
  have hZ : TendstoInDistribution μ Z (gaussianReal 0 1) := fun f ↦ (hclt f).comp hMtop
  set W : ℕ → Ω → ℝ := fun n ω ↦
    (Real.sqrt (M n))⁻¹ * ∑ i ∈ Finset.range (N n ω), Y i ω
  have hWm : ∀ n, Measurable (W n) := fun n ↦
    (measurable_randomIndex (g := fun j ω ↦ ∑ i ∈ Finset.range j, Y i ω) hSm (hN n)).const_mul _
  have hW : TendstoInDistribution μ W (gaussianReal 0 1) := by
    refine tendstoInDistribution_of_tendstoInProbabilityConst_sub μ Z W hZm hWm _ hZ ?_
    have hcore := tendstoInProbabilityConst_sum_randomIndex_sub hYm hYind hY2 hY0 hY1 N k hk hratio
    convert hcore using 3 with n ω
    simp only [W, Z, M]
    ring
  have hRW := tendstoInProbabilityConst_mul_sub_self μ W hWm _ hW _
    (tendstoInProbabilityConst_sqrt_ceil_div μ N k hk hratio)
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub μ W _ hWm (fun n ↦ ?_) _ hW ?_
  · exact measurable_randomIndex
      (g := fun j ω ↦ Real.sqrt j * (sampleAverage X j ω - m) / σ)
      (fun j ↦ measurable_sqrt_mul_sampleAverage_sub hiid.1 j m σ) (hN n)
  intro ε hε
  refine (hRW ε hε).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  congr! 2
  have hj : (0 : ℝ) < N n ω := by exact_mod_cast hpos n ω
  have hc : (0 : ℝ) < M n := by
    have : (0 : ℝ) < k * n := mul_pos hk (by exact_mod_cast hn)
    exact lt_of_lt_of_le this (Nat.le_ceil _)
  simp only [W, Y, hsdef, sampleAverage, smul_eq_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Real.sqrt_div hc.le]
  have hsj := Real.sq_sqrt hj.le
  have hsj0 := Real.sqrt_pos.2 hj
  have hsc0 := Real.sqrt_pos.2 hc
  generalize Real.sqrt (N n ω) = a at *
  generalize (N n ω : ℝ) = b at *
  subst hsj
  field_simp


end CKSD
