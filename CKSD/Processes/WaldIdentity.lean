module

public import CKSD.Processes.Independence
public import Mathlib.Probability.Independence.Integration

/-!
# Wald's fundamental identity

For an iid random walk `S_k = Z_0 + ⋯ + Z_(k-1)` and its first exit time `N` from an interval
`(a, b)`, the stopped exponential `exp (t S_N) / m(t)^N` has mean one whenever the moment
generating value `m(t) = 𝔼 exp (t Z_0)` is finite and at least one.

The proof shows by induction, using the independence of each increment from the past, that the
stopped exponential process has mean one at every finite horizon, and passes to the limit by
monotone convergence on the stopped part and boundedness of the process before exit.

## Main definitions

* `CKSD.rangePartialSum`: truncated partial sums of a vector indexed by `Finset.range n`.

## Main results

* `CKSD.integral_stopped_exponential_eq_one` (GAPS 106.41): Wald's fundamental identity at a
  first exit time.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Partial sums of a finite coordinate vector indexed by `range n`, truncated at `k`. -/
def rangePartialSum {n : ℕ} (v : Finset.range n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Finset.range n, if (i : ℕ) < k then v i else 0

/-- Truncated partial sums of a finite coordinate vector are measurable. -/
theorem measurable_rangePartialSum (n k : ℕ) :
    Measurable fun v : Finset.range n → ℝ ↦ rangePartialSum v k := by
  unfold rangePartialSum
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  by_cases h : (i : ℕ) < k
  · simp only [h, ite_true]; exact measurable_pi_apply i
  · simp only [h, ite_false]; exact measurable_const

/-- Up to the length of the vector, truncated partial sums of the restriction of a sequence are
its partial sums. -/
theorem rangePartialSum_restrict {Ω : Type*} (Z : ℕ → Ω → ℝ) (ω : Ω) {n k : ℕ} (hk : k ≤ n) :
    rangePartialSum (fun i : Finset.range n ↦ Z i ω) k = ∑ i ∈ Finset.range k, Z i ω := by
  unfold rangePartialSum
  rw [Finset.sum_coe_sort (Finset.range n) (fun i ↦ if i < k then Z i ω else 0),
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- GAPS 106.41: Wald's fundamental stopped exponential identity at a first exit time.
Let `Z` be iid with law `law`, `S_k = ∑_{i < k} Z_i`, and let `t` be such that `exp (t z)` is
`law`-integrable with mean `m(t) ≥ 1`. If `N` is a measurable, finite-valued first exit time of
`S` from the open interval `(a, b)` (almost surely `S_k ∈ (a, b)` for `k < N` and
`S_N ∉ (a, b)`), then `exp (t S_N) / m(t)^N` is integrable with mean one.
The finite-valued time `N` is a measurable version of the almost surely finite first exit;
its existence is a hypothesis. -/
theorem integral_stopped_exponential_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (law : Measure ℝ)
    (Z : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed P Z law)
    (a b : ℝ) (N : Ω → ℕ) (hN : Measurable N)
    (hstop : ∀ᵐ ω ∂P,
      (∑ i ∈ Finset.range (N ω), Z i ω ≤ a ∨ b ≤ ∑ i ∈ Finset.range (N ω), Z i ω) ∧
        ∀ k < N ω, a < ∑ i ∈ Finset.range k, Z i ω ∧ ∑ i ∈ Finset.range k, Z i ω < b)
    (t : ℝ) (hexp : Integrable (fun z ↦ Real.exp (t * z)) law)
    (hmgf : 1 ≤ ∫ z, Real.exp (t * z) ∂law) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ Finset.range (N ω), Z i ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ N ω) P ∧
    (∫ ω, Real.exp (t * ∑ i ∈ Finset.range (N ω), Z i ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ N ω ∂P) = 1 := by
  obtain ⟨hZm, hind, hlaw⟩ := hiid
  set m := ∫ z, Real.exp (t * z) ∂law with hm_def
  have hm0 : 0 < m := one_pos.trans_le hmgf
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ i ∈ Finset.range k, Z i ω with hS_def
  let G : ℕ → Ω → ℝ := fun k ω ↦ Real.exp (t * S k ω) / m ^ k
  let A : ℕ → Set Ω := fun n ↦ {ω | ∀ k ≤ n, a < S k ω ∧ S k ω < b}
  have hS_meas : ∀ k, Measurable (S k) := fun k ↦ by
    simp only [hS_def]
    exact Finset.measurable_sum _ fun i _ ↦ hZm i
  have hG_meas : ∀ k, Measurable (G k) := fun k ↦
    (Real.measurable_exp.comp ((hS_meas k).const_mul t)).div_const _
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n ↦ by
    have : A n = ⋂ k, ⋂ (_ : k ≤ n), ({ω | a < S k ω} ∩ {ω | S k ω < b}) := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_lt measurable_const (hS_meas k)).inter
        (measurableSet_lt (hS_meas k) measurable_const)
  have hNA : ∀ᵐ ω ∂P, ∀ n, (n < N ω ↔ ω ∈ A n) := by
    filter_upwards [hstop] with ω hω n
    refine ⟨fun hn k hk ↦ hω.2 k (lt_of_le_of_lt hk hn), fun hA ↦ ?_⟩
    by_contra hle
    replace hle := not_lt.1 hle
    rcases hω.1 with h | h
    · exact absurd h (not_le.2 (hA _ hle).1)
    · exact absurd h (not_le.2 (hA _ hle).2)
  set C := Real.exp (|t| * max |a| |b|) with hC
  have hGA_bdd : ∀ n ω, ω ∈ A n → 0 ≤ G n ω ∧ G n ω ≤ C := by
    intro n ω hω
    refine ⟨by positivity, ?_⟩
    have h1 : 1 ≤ m ^ n := one_le_pow₀ hmgf
    have h2 : Real.exp (t * S n ω) ≤ C := by
      apply Real.exp_le_exp.2
      have hs : |S n ω| ≤ max |a| |b| := by
        rw [abs_le]
        constructor
        · linarith [(hω n le_rfl).1, le_max_left |a| |b|, neg_abs_le a]
        · linarith [(hω n le_rfl).2, le_max_right |a| |b|, le_abs_self b]
      calc t * S n ω ≤ |t * S n ω| := le_abs_self _
        _ = |t| * |S n ω| := abs_mul _ _
        _ ≤ |t| * max |a| |b| := by gcongr
    calc G n ω = Real.exp (t * S n ω) / m ^ n := rfl
      _ ≤ Real.exp (t * S n ω) := div_le_self (Real.exp_pos _).le h1
      _ ≤ C := h2
  have hE_int : ∀ n, Integrable (fun ω ↦ Real.exp (t * Z n ω)) P := fun n ↦ by
    have := hexp
    rw [← hlaw n] at this
    exact (integrable_map_measure (by fun_prop) (hZm n).aemeasurable).1 this
  have hE_mean : ∀ n, ∫ ω, Real.exp (t * Z n ω) ∂P = m := fun n ↦ by
    rw [hm_def, ← hlaw n, integral_map (hZm n).aemeasurable (by fun_prop)]
  have hkey : ∀ n, ∫ ω, (A n).indicator (G n) ω * (Real.exp (t * Z n ω) / m - 1) ∂P = 0 := by
    intro n
    let φ : (Finset.range n → ℝ) → ℝ := fun v ↦
      if ∀ k ≤ n, a < rangePartialSum v k ∧ rangePartialSum v k < b then
        Real.exp (t * rangePartialSum v n) / m ^ n else 0
    let ψ : (({n} : Finset ℕ) → ℝ) → ℝ := fun v ↦
      Real.exp (t * v ⟨n, Finset.mem_singleton_self n⟩) / m - 1
    have hφ : Measurable φ := by
      refine Measurable.ite ?_ (((measurable_rangePartialSum n n).const_mul t).exp.div_const _)
        measurable_const
      have : {v : Finset.range n → ℝ | ∀ k ≤ n, a < rangePartialSum v k ∧
          rangePartialSum v k < b} = ⋂ k, ⋂ (_ : k ≤ n),
            ({v | a < rangePartialSum v k} ∩ {v | rangePartialSum v k < b}) := by
        ext v; simp
      rw [this]
      exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
        (measurableSet_lt measurable_const (measurable_rangePartialSum n k)).inter
          (measurableSet_lt (measurable_rangePartialSum n k) measurable_const)
    have hψ : Measurable ψ := by
      simp only [ψ]; fun_prop
    have hφeq : (φ ∘ fun ω (i : Finset.range n) ↦ Z i ω) = (A n).indicator (G n) := by
      funext ω
      simp only [Function.comp_apply, φ, Set.indicator, A, Set.mem_ofPred_eq]
      have hr : ∀ k ≤ n, rangePartialSum (fun i : Finset.range n ↦ Z i ω) k = S k ω :=
        fun k hk ↦ rangePartialSum_restrict Z ω hk
      by_cases h : ∀ k ≤ n, a < S k ω ∧ S k ω < b
      · rw [ite_eq_left (fun k hk ↦ (hr k hk).symm ▸ h k hk), ite_eq_left h, hr n le_rfl]
      · rw [ite_eq_right (fun h' ↦ h fun k hk ↦ (hr k hk) ▸ h' k hk), ite_eq_right h]
    have hψeq : (ψ ∘ fun ω (i : ({n} : Finset ℕ)) ↦ Z i ω) =
        fun ω ↦ Real.exp (t * Z n ω) / m - 1 := rfl
    have hindep : IndepFun ((A n).indicator (G n)) (fun ω ↦ Real.exp (t * Z n ω) / m - 1) P := by
      rw [← hφeq, ← hψeq]
      exact (hind.indepFun_finset (Finset.range n) {n} (by simp) hZm).comp hφ hψ
    have := IndepFun.integral_mul_eq_mul_integral hindep
      ((hG_meas n).indicator (hA_meas n)).aestronglyMeasurable
      (((hZm n).const_mul t).exp.div_const _ |>.sub_const _).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, integral_sub ((hE_int n).div_const _) (integrable_const _), integral_div,
      hE_mean n, div_self hm0.ne']
    simp
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hIA_bdd : ∀ n ω, ‖(A n).indicator (G n) ω‖ ≤ C := by
    intro n ω
    by_cases h : ω ∈ A n
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hGA_bdd n ω h).1]
      exact (hGA_bdd n ω h).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact hC0
  have hIA_meas : ∀ n, Measurable ((A n).indicator (G n)) := fun n ↦
    (hG_meas n).indicator (hA_meas n)
  have hIA_int : ∀ n, Integrable ((A n).indicator (G n)) P := fun n ↦
    (integrable_const C).mono' (hIA_meas n).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ hIA_bdd n ω)
  have hIA_nonneg : ∀ n ω, 0 ≤ (A n).indicator (G n) ω := fun n ω ↦
    Set.indicator_nonneg (fun ω h ↦ (hGA_bdd n ω h).1) ω
  have hS_succ : ∀ n ω, S (n + 1) ω = S n ω + Z n ω := fun n ω ↦ by
    simp only [hS_def, Finset.sum_range_succ]
  let Y : ℕ → Ω → ℝ := fun n ω ↦ G (min (N ω) n) ω
  have hYrec : ∀ n, Y (n + 1) =ᵐ[P] fun ω ↦
      Y n ω + (A n).indicator (G n) ω * (Real.exp (t * Z n ω) / m - 1) := by
    intro n
    filter_upwards [hNA] with ω hω
    by_cases h : n < N ω
    · have hA : ω ∈ A n := (hω n).1 h
      simp only [Y, Set.indicator_of_mem hA, min_eq_right h.le, min_eq_right (Nat.succ_le_of_lt h)]
      simp only [G, hS_succ, mul_add, Real.exp_add, pow_succ]
      field_simp
      ring
    · have hA : ω ∉ A n := fun hA ↦ h ((hω n).2 hA)
      have h' : N ω ≤ n := not_lt.1 h
      simp only [Y, Set.indicator_of_notMem hA, min_eq_left h', min_eq_left (h'.trans n.le_succ),
        zero_mul, add_zero]
  have hY : ∀ n, Integrable (Y n) P ∧ ∫ ω, Y n ω ∂P = 1 := by
    intro n
    induction n with
    | zero =>
      have : Y 0 = fun _ ↦ 1 := by
        funext ω
        simp [Y, G, hS_def]
      rw [this]
      exact ⟨integrable_const _, by simp⟩
    | succ n ih =>
      have hinc : Integrable (fun ω ↦
          (A n).indicator (G n) ω * (Real.exp (t * Z n ω) / m - 1)) P :=
        ((hE_int n).div_const m |>.sub (integrable_const 1)).bdd_mul
          (hIA_meas n).aestronglyMeasurable (ae_of_all _ fun ω ↦ hIA_bdd n ω)
      refine ⟨(ih.1.add hinc).congr (hYrec n).symm, ?_⟩
      rw [integral_congr_ae (hYrec n), integral_add ih.1 hinc, ih.2, hkey n, add_zero]
  let GN : Ω → ℝ := fun ω ↦ G (N ω) ω
  have hGN_meas : Measurable GN := measurable_randomIndex hG_meas hN
  have hGN_nonneg : ∀ ω, 0 ≤ GN ω := fun ω ↦ by positivity
  let f : ℕ → Ω → ℝ := fun n ↦ {ω | N ω ≤ n}.indicator GN
  have hdecomp : ∀ n, Y n =ᵐ[P] fun ω ↦ f n ω + (A n).indicator (G n) ω := by
    intro n
    filter_upwards [hNA] with ω hω
    by_cases h : n < N ω
    · have hA : ω ∈ A n := (hω n).1 h
      have hf : ω ∉ {ω | N ω ≤ n} := fun h' ↦ (not_le.2 h) h'
      simp only [Y, f, Set.indicator_of_mem hA, Set.indicator_of_notMem hf, min_eq_right h.le,
        zero_add]
    · have hA : ω ∉ A n := fun hA ↦ h ((hω n).2 hA)
      have h' : N ω ≤ n := not_lt.1 h
      have hf : ω ∈ {ω | N ω ≤ n} := h'
      simp only [Y, f, GN, Set.indicator_of_mem hf, Set.indicator_of_notMem hA, min_eq_left h',
        add_zero]
  have hf_int : ∀ n, Integrable (f n) P := fun n ↦
    ((hY n).1.sub (hIA_int n)).congr ((hdecomp n).mono fun ω hω ↦ by simp [hω])
  have hf_mean : ∀ n, ∫ ω, f n ω ∂P = 1 - ∫ ω, (A n).indicator (G n) ω ∂P := fun n ↦ by
    rw [← (hY n).2, integral_congr_ae (hdecomp n), integral_add (hf_int n) (hIA_int n)]
    ring
  have hA_anti : Antitone A := fun i j hij ω hω k hk ↦ hω k (hk.trans hij)
  have hA_null : P (⋂ n, A n) = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hNA)
    intro hall
    have := (hall (N ω)).2 (mem_iInter.1 hω (N ω))
    exact lt_irrefl _ this
  have hPA : Tendsto (fun n ↦ P.real (A n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (fun n ↦ (hA_meas n).nullMeasurableSet)
      hA_anti ⟨0, measure_ne_top P _⟩
    rw [hA_null] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def, measureReal_def] using this
  have hIA_lim : Tendsto (fun n ↦ ∫ ω, (A n).indicator (G n) ω ∂P) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ integral_nonneg (hIA_nonneg n)) (fun n ↦ ?_)
      (by simpa using hPA.const_mul C)
    calc ∫ ω, (A n).indicator (G n) ω ∂P ≤ ∫ ω, (A n).indicator (fun _ ↦ C) ω ∂P := by
          refine integral_mono (hIA_int n) ((integrable_const C).indicator (hA_meas n)) ?_
          intro ω
          by_cases h : ω ∈ A n
          · simp only [Set.indicator_of_mem h]; exact (hGA_bdd n ω h).2
          · simp only [Set.indicator_of_notMem h, le_refl]
      _ = C * P.real (A n) := by
          rw [integral_indicator_const _ (hA_meas n), smul_eq_mul, mul_comm]
  have hlin_lim : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (GN ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ ((hGN_meas.indicator (measurableSet_le hN measurable_const)).ennreal_ofReal
        ).aemeasurable) (ae_of_all _ fun ω i j hij ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
    · apply ENNReal.ofReal_le_ofReal
      by_cases h : N ω ≤ i
      · have hj : N ω ≤ j := h.trans hij
        simp [f, h, hj]
      · simp only [f, Set.indicator, Set.mem_ofPred_eq, h, ite_false]
        split_ifs <;> simp [hGN_nonneg]
    · refine tendsto_atTop_of_eventually_const (i₀ := N ω) fun n hn ↦ ?_
      simp [f, hn]
  have hlin_lim' : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop (𝓝 1) := by
    have : Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, f n ω ∂P)) atTop (𝓝 (ENNReal.ofReal 1)) := by
      refine ENNReal.tendsto_ofReal ?_
      simp_rw [hf_mean]
      simpa using hIA_lim.const_sub 1
    rw [ENNReal.ofReal_one] at this
    refine this.congr fun n ↦ ?_
    exact ofReal_integral_eq_lintegral_ofReal (hf_int n)
      (ae_of_all _ fun ω ↦ Set.indicator_nonneg (fun ω _ ↦ hGN_nonneg ω) ω)
  have hlin : ∫⁻ ω, ENNReal.ofReal (GN ω) ∂P = 1 := tendsto_nhds_unique hlin_lim hlin_lim'
  have hint : Integrable GN P :=
    ⟨hGN_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hGN_nonneg)).2
        (by rw [hlin]; exact ENNReal.one_lt_top)⟩
  refine ⟨hint, ?_⟩
  change ∫ ω, GN ω ∂P = 1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hGN_nonneg) hGN_meas.aestronglyMeasurable,
    hlin, ENNReal.toReal_one]

end CKSD
