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

* `CKSD.integrable_and_integral_stopped_exponential_min_eq_one`: the identity at the bounded
  times `N ∧ n`.
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

/-- The event that a random walk stays in `(a, b)` up to time `n` is measurable. -/
private theorem measurableSet_forall_le_sum_range_mem_Ioo {Ω : Type*} [MeasurableSpace Ω]
    {Z : ℕ → Ω → ℝ} (hZm : ∀ i, Measurable (Z i)) (a b : ℝ) (n : ℕ) :
    MeasurableSet {ω | ∀ k ≤ n, a < ∑ i ∈ Finset.range k, Z i ω ∧
      ∑ i ∈ Finset.range k, Z i ω < b} := by
  have hS : ∀ k, Measurable fun ω ↦ ∑ i ∈ Finset.range k, Z i ω := fun k ↦
    Finset.measurable_sum _ fun i _ ↦ hZm i
  have : {ω | ∀ k ≤ n, a < ∑ i ∈ Finset.range k, Z i ω ∧ ∑ i ∈ Finset.range k, Z i ω < b} =
      ⋂ k, ⋂ (_ : k ≤ n), ({ω | a < ∑ i ∈ Finset.range k, Z i ω} ∩
        {ω | ∑ i ∈ Finset.range k, Z i ω < b}) := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
    (measurableSet_lt measurable_const (hS k)).inter (measurableSet_lt (hS k) measurable_const)

/-- At a first exit time `N` from `(a, b)`, almost surely `n < N` holds exactly when the walk
stays in `(a, b)` up to time `n`. -/
private theorem ae_lt_iff_forall_le_sum_range_mem_Ioo {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℕ → Ω → ℝ} {a b : ℝ} {N : Ω → ℕ}
    (hstop : ∀ᵐ ω ∂P,
      (∑ i ∈ Finset.range (N ω), Z i ω ≤ a ∨ b ≤ ∑ i ∈ Finset.range (N ω), Z i ω) ∧
        ∀ k < N ω, a < ∑ i ∈ Finset.range k, Z i ω ∧ ∑ i ∈ Finset.range k, Z i ω < b) :
    ∀ᵐ ω ∂P, ∀ n, (n < N ω ↔ ∀ k ≤ n, a < ∑ i ∈ Finset.range k, Z i ω ∧
      ∑ i ∈ Finset.range k, Z i ω < b) := by
  filter_upwards [hstop] with ω hω n
  refine ⟨fun hn k hk ↦ hω.2 k (lt_of_le_of_lt hk hn), fun hA ↦ ?_⟩
  by_contra hle
  replace hle := not_lt.1 hle
  rcases hω.1 with h | h
  · exact absurd h (not_le.2 (hA _ hle).1)
  · exact absurd h (not_le.2 (hA _ hle).2)

/-- The increment of the stopped exponential martingale at time `n` has mean zero: the
indicator that the walk is still in `(a, b)` times the current exponential value is independent
of `exp (t Z_n) / m - 1`, whose mean is zero. -/
private theorem integral_indicator_mul_exp_div_sub_one_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {law : Measure ℝ} {Z : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed P Z law) (a b t : ℝ)
    (hexp : Integrable (fun z ↦ Real.exp (t * z)) law)
    (hm0 : 0 < ∫ z, Real.exp (t * z) ∂law) (n : ℕ) :
    ∫ ω, {ω | ∀ k ≤ n, a < ∑ i ∈ Finset.range k, Z i ω ∧
        ∑ i ∈ Finset.range k, Z i ω < b}.indicator
        (fun ω ↦ Real.exp (t * ∑ i ∈ Finset.range n, Z i ω) /
          (∫ z, Real.exp (t * z) ∂law) ^ n) ω *
      (Real.exp (t * Z n ω) / ∫ z, Real.exp (t * z) ∂law - 1) ∂P = 0 := by
  obtain ⟨hZm, hind, hlaw⟩ := hiid
  set m := ∫ z, Real.exp (t * z) ∂law with hm_def
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ i ∈ Finset.range k, Z i ω with hS_def
  set A : Set Ω := {ω | ∀ k ≤ n, a < S k ω ∧ S k ω < b} with hA_def
  set G : Ω → ℝ := fun ω ↦ Real.exp (t * S n ω) / m ^ n with hG_def
  have hS_meas : Measurable (S n) := Finset.measurable_sum _ fun i _ ↦ hZm i
  have hE_int : Integrable (fun ω ↦ Real.exp (t * Z n ω)) P := by
    rw [← hlaw n] at hexp
    exact (integrable_map_measure (by fun_prop) (hZm n).aemeasurable).1 hexp
  have hE_mean : ∫ ω, Real.exp (t * Z n ω) ∂P = m := by
    rw [hm_def, ← hlaw n, integral_map (hZm n).aemeasurable (by fun_prop)]
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
  have hφeq : (φ ∘ fun ω (i : Finset.range n) ↦ Z i ω) = A.indicator G := by
    funext ω
    simp only [Function.comp_apply, φ, Set.indicator, hA_def, Set.mem_ofPred_eq]
    have hr : ∀ k ≤ n, rangePartialSum (fun i : Finset.range n ↦ Z i ω) k = S k ω :=
      fun k hk ↦ rangePartialSum_restrict Z ω hk
    by_cases h : ∀ k ≤ n, a < S k ω ∧ S k ω < b
    · rw [ite_eq_left (fun k hk ↦ (hr k hk).symm ▸ h k hk), ite_eq_left h, hr n le_rfl]
    · rw [ite_eq_right (fun h' ↦ h fun k hk ↦ (hr k hk) ▸ h' k hk), ite_eq_right h]
  have hψeq : (ψ ∘ fun ω (i : ({n} : Finset ℕ)) ↦ Z i ω) =
      fun ω ↦ Real.exp (t * Z n ω) / m - 1 := rfl
  have hindep : IndepFun (A.indicator G) (fun ω ↦ Real.exp (t * Z n ω) / m - 1) P := by
    rw [← hφeq, ← hψeq]
    exact (hind.indepFun_finset (Finset.range n) {n} (by simp) hZm).comp hφ hψ
  have := IndepFun.integral_mul_eq_mul_integral hindep
    (((Real.measurable_exp.comp (hS_meas.const_mul t)).div_const _).indicator
      (measurableSet_forall_le_sum_range_mem_Ioo hZm a b n)).aestronglyMeasurable
    (((hZm n).const_mul t).exp.div_const _ |>.sub_const _).aestronglyMeasurable
  simp only [Pi.mul_apply] at this
  rw [this, integral_sub (hE_int.div_const _) (integrable_const _), integral_div,
    hE_mean, div_self hm0.ne']
  simp

/-- Wald's identity at a bounded horizon: with `N` a first exit time from `(a, b)` as in
`integral_stopped_exponential_eq_one`, for every `n` the stopped exponential
`exp (t S_{N ∧ n}) / m(t)^{N ∧ n}` is integrable with mean one. -/
theorem integrable_and_integral_stopped_exponential_min_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (law : Measure ℝ)
    (Z : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed P Z law)
    (a b : ℝ) (N : Ω → ℕ)
    (hstop : ∀ᵐ ω ∂P,
      (∑ i ∈ Finset.range (N ω), Z i ω ≤ a ∨ b ≤ ∑ i ∈ Finset.range (N ω), Z i ω) ∧
        ∀ k < N ω, a < ∑ i ∈ Finset.range k, Z i ω ∧ ∑ i ∈ Finset.range k, Z i ω < b)
    (t : ℝ) (hexp : Integrable (fun z ↦ Real.exp (t * z)) law)
    (hmgf : 1 ≤ ∫ z, Real.exp (t * z) ∂law) (n : ℕ) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ Finset.range (min (N ω) n), Z i ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ min (N ω) n) P ∧
    (∫ ω, Real.exp (t * ∑ i ∈ Finset.range (min (N ω) n), Z i ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ min (N ω) n ∂P) = 1 := by
  have hZm := hiid.1
  set m := ∫ z, Real.exp (t * z) ∂law with hm_def
  have hm0 : 0 < m := one_pos.trans_le hmgf
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ i ∈ Finset.range k, Z i ω with hS_def
  set G : ℕ → Ω → ℝ := fun k ω ↦ Real.exp (t * S k ω) / m ^ k with hG_def
  set A : ℕ → Set Ω := fun n ↦ {ω | ∀ k ≤ n, a < S k ω ∧ S k ω < b} with hA_def
  have hNA : ∀ᵐ ω ∂P, ∀ n, (n < N ω ↔ ω ∈ A n) := ae_lt_iff_forall_le_sum_range_mem_Ioo hstop
  have hE_int : ∀ n, Integrable (fun ω ↦ Real.exp (t * Z n ω)) P := fun n ↦ by
    have := hexp
    rw [← hiid.2.2 n] at this
    exact (integrable_map_measure (by fun_prop) (hZm n).aemeasurable).1 this
  have hIA_bdd : ∀ n ω, ‖(A n).indicator (G n) ω‖ ≤ Real.exp (|t| * max |a| |b|) := by
    intro n ω
    by_cases h : ω ∈ A n
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (by positivity)]
      exact exp_mul_div_pow_le_of_mem_Ioo t (h n le_rfl) hmgf n
    · rw [Set.indicator_of_notMem h, norm_zero]
      positivity
  have hIA_meas : ∀ n, Measurable ((A n).indicator (G n)) := fun n ↦
    ((Real.measurable_exp.comp ((Finset.measurable_sum _ fun i _ ↦ hZm i).const_mul t)).div_const
      _).indicator (measurableSet_forall_le_sum_range_mem_Ioo hZm a b n)
  have hS_succ : ∀ n ω, S (n + 1) ω = S n ω + Z n ω := fun n ω ↦ by
    simp only [hS_def, Finset.sum_range_succ]
  set Y : ℕ → Ω → ℝ := fun n ω ↦ G (min (N ω) n) ω with hY_def
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
  suffices h : Integrable (Y n) P ∧ ∫ ω, Y n ω ∂P = 1 from h
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
    rw [integral_congr_ae (hYrec n), integral_add ih.1 hinc, ih.2,
      integral_indicator_mul_exp_div_sub_one_eq_zero hiid a b t hexp hm0 n, add_zero]

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
  have hZm := hiid.1
  set m := ∫ z, Real.exp (t * z) ∂law with hm_def
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ i ∈ Finset.range k, Z i ω with hS_def
  set G : ℕ → Ω → ℝ := fun k ω ↦ Real.exp (t * S k ω) / m ^ k with hG_def
  set A : ℕ → Set Ω := fun n ↦ {ω | ∀ k ≤ n, a < S k ω ∧ S k ω < b} with hA_def
  have hS_meas : ∀ k, Measurable (S k) := fun k ↦ Finset.measurable_sum _ fun i _ ↦ hZm i
  have hG_meas : ∀ k, Measurable (G k) := fun k ↦
    (Real.measurable_exp.comp ((hS_meas k).const_mul t)).div_const _
  have hA_meas : ∀ n, MeasurableSet (A n) := measurableSet_forall_le_sum_range_mem_Ioo hZm a b
  have hNA : ∀ᵐ ω ∂P, ∀ n, (n < N ω ↔ ω ∈ A n) := ae_lt_iff_forall_le_sum_range_mem_Ioo hstop
  set C := Real.exp (|t| * max |a| |b|) with hC
  have hGA_bdd : ∀ n ω, ω ∈ A n → 0 ≤ G n ω ∧ G n ω ≤ C := fun n ω hω ↦
    ⟨by positivity, exp_mul_div_pow_le_of_mem_Ioo t (hω n le_rfl) hmgf n⟩
  have hIA_int : ∀ n, Integrable ((A n).indicator (G n)) P := fun n ↦
    (integrable_const C).mono' ((hG_meas n).indicator (hA_meas n)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        by_cases h : ω ∈ A n
        · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hGA_bdd n ω h).1]
          exact (hGA_bdd n ω h).2
        · rw [Set.indicator_of_notMem h, norm_zero]
          positivity)
  have hIA_nonneg : ∀ n ω, 0 ≤ (A n).indicator (G n) ω := fun n ω ↦
    Set.indicator_nonneg (fun ω h ↦ (hGA_bdd n ω h).1) ω
  set Y : ℕ → Ω → ℝ := fun n ω ↦ G (min (N ω) n) ω with hY_def
  have hY : ∀ n, Integrable (Y n) P ∧ ∫ ω, Y n ω ∂P = 1 :=
    integrable_and_integral_stopped_exponential_min_eq_one P law Z hiid a b N hstop t hexp hmgf
  set GN : Ω → ℝ := fun ω ↦ G (N ω) ω with hGN_def
  have hGN_meas : Measurable GN := measurable_randomIndex hG_meas hN
  set f : ℕ → Ω → ℝ := fun n ↦ {ω | N ω ≤ n}.indicator GN with hf_def
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
  have hA_null : P (⋂ n, A n) = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hNA)
    intro hall
    exact lt_irrefl _ ((hall (N ω)).2 (mem_iInter.1 hω (N ω)))
  have hPA : Tendsto (fun n ↦ P.real (A n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (fun n ↦ (hA_meas n).nullMeasurableSet)
      (fun i j hij ω hω k hk ↦ hω k (hk.trans hij)) ⟨0, measure_ne_top P _⟩
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
  exact integrable_and_integral_eq_of_tendsto_integral_indicator_le hN hGN_meas
    (fun ω ↦ by positivity) hf_int
    (by simpa using (hIA_lim.const_sub 1).congr fun n ↦ (hf_mean n).symm)

end CKSD
