module

public import CKSD.Learning.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.PSeries

/-!
# Play counts of the UCB1 index policy

Rewards are given as a table `R i j`, the `j`-th reward of arm `i`, with independent entries in
`[0,1]` almost surely and a common law along each arm. An arm process `A` plays each arm once
during the first `K` rounds and afterwards an arm maximizing the UCB1 index
`x̄ᵢ + √(2 log t / nᵢ)`, where `nᵢ` is the number of earlier plays of arm `i` and `x̄ᵢ` the
average of the first `nᵢ` rewards of that arm.

The main result bounds the expected number of plays of a suboptimal arm with gap `Δ` during
the first `T` rounds by `8 log T / Δ² + 3`. The argument is that of Auer, Cesa-Bianchi and
Fischer (2002): a suboptimal arm that has already been played `⌈8 log T / Δ²⌉` times can be
chosen only when one of two prefix averages deviates from its mean by the confidence radius,
and Hoeffding's inequality (Mathlib's `measure_sum_range_ge_le_of_iIndepFun` with Hoeffding's
lemma `hasSubgaussianMGF_of_mem_Icc`) bounds the probability of each deviation by `t⁻⁴`.

Source: GAPS 107.50 and 107.62.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

section Hoeffding

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {K : ℕ}
  {R : Fin K → ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- All rewards of an arm have the mean of its first reward when they share one law. -/
theorem integral_reward_eq_of_map_eq (hm : ∀ i j, Measurable (R i j))
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0)) (i : Fin K) (j : ℕ) :
    ∫ ω, R i j ω ∂P = ∫ ω, R i 0 ω ∂P := by
  rw [← integral_map (φ := R i j) (f := fun x ↦ x) (hm i j).aemeasurable
      aestronglyMeasurable_id, hlaw,
    integral_map (φ := R i 0) (f := fun x ↦ x) (hm i 0).aemeasurable aestronglyMeasurable_id]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The prefix sum of the centred rewards of one arm, rewritten from the prefix average. -/
theorem le_sum_sub_of_add_le_armSampleAverage {i : Fin K} {s : ℕ} (hs : 0 < s) {μ c : ℝ}
    {ω : Ω} (h : μ + c ≤ armSampleAverage R i s ω) :
    s * c ≤ ∑ j ∈ Finset.range s, (R i j ω - μ) := by
  have hsr : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  unfold armSampleAverage at h
  rw [le_div_iff₀ hsr] at h
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The prefix sum of the centred losses of one arm, rewritten from the prefix average. -/
theorem le_sum_sub_of_armSampleAverage_le {i : Fin K} {s : ℕ} (hs : 0 < s) {μ c : ℝ}
    {ω : Ω} (h : armSampleAverage R i s ω ≤ μ - c) :
    s * c ≤ ∑ j ∈ Finset.range s, (μ - R i j ω) := by
  have hsr : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  unfold armSampleAverage at h
  rw [div_le_iff₀ hsr] at h
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- Hoeffding's inequality for an upper deviation of the prefix average of one arm. -/
theorem measureReal_add_le_armSampleAverage_le (hm : ∀ i j, Measurable (R i j))
    (hb : ∀ i j, ∀ᵐ ω ∂P, R i j ω ∈ Icc 0 1)
    (hind : iIndepFun (fun z : Fin K × ℕ ↦ R z.1 z.2) P)
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0)) (i : Fin K) {s : ℕ} (hs : 0 < s) {c : ℝ}
    (hc : 0 ≤ c) :
    P.real {ω | (∫ ω, R i 0 ω ∂P) + c ≤ armSampleAverage R i s ω} ≤
      Real.exp (-2 * s * c ^ 2) := by
  set μ := ∫ ω, R i 0 ω ∂P
  have hsr : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hind' : iIndepFun (fun j : ℕ ↦ fun ω ↦ R i j ω - μ) P := by
    have h1 : iIndepFun (fun j : ℕ ↦ R i j) P :=
      hind.precomp (g := fun j : ℕ ↦ (i, j)) fun a b h ↦ by simpa using h
    exact h1.comp (fun _ x ↦ x - μ) fun _ ↦ measurable_id.sub_const _
  have hsub : ∀ j < s, HasSubgaussianMGF (fun ω ↦ R i j ω - μ)
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro j _
    have h := hasSubgaussianMGF_of_mem_Icc (hm i j).aemeasurable (hb i j)
    rwa [integral_reward_eq_of_map_eq hm hlaw i j] at h
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind' hsub (ε := s * c)
    (by positivity)
  refine (measureReal_mono (fun ω hω ↦ le_sum_sub_of_add_le_armSampleAverage hs hω)).trans
    (key.trans (le_of_eq ?_))
  congr 1
  simp only [sub_zero, nnnorm_one, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  field_simp

/-- Hoeffding's inequality for a lower deviation of the prefix average of one arm. -/
theorem measureReal_armSampleAverage_le_sub_le (hm : ∀ i j, Measurable (R i j))
    (hb : ∀ i j, ∀ᵐ ω ∂P, R i j ω ∈ Icc 0 1)
    (hind : iIndepFun (fun z : Fin K × ℕ ↦ R z.1 z.2) P)
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0)) (i : Fin K) {s : ℕ} (hs : 0 < s) {c : ℝ}
    (hc : 0 ≤ c) :
    P.real {ω | armSampleAverage R i s ω ≤ (∫ ω, R i 0 ω ∂P) - c} ≤
      Real.exp (-2 * s * c ^ 2) := by
  set μ := ∫ ω, R i 0 ω ∂P
  have hsr : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hind' : iIndepFun (fun j : ℕ ↦ fun ω ↦ μ - R i j ω) P := by
    have h1 : iIndepFun (fun j : ℕ ↦ R i j) P :=
      hind.precomp (g := fun j : ℕ ↦ (i, j)) fun a b h ↦ by simpa using h
    exact h1.comp (fun _ x ↦ μ - x) fun _ ↦ measurable_const.sub measurable_id
  have hsub : ∀ j < s, HasSubgaussianMGF (fun ω ↦ μ - R i j ω)
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro j _
    have h := (hasSubgaussianMGF_of_mem_Icc (hm i j).aemeasurable (hb i j)).neg
    rw [integral_reward_eq_of_map_eq hm hlaw i j] at h
    convert h using 1
    funext ω
    simp [μ]
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind' hsub (ε := s * c)
    (by positivity)
  refine (measureReal_mono (fun ω hω ↦ le_sum_sub_of_armSampleAverage_le hs hω)).trans
    (key.trans (le_of_eq ?_))
  congr 1
  simp only [sub_zero, nnnorm_one, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  field_simp

end Hoeffding

/-- Prefix averages of measurable rewards are measurable. -/
theorem measurable_armSampleAverage {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    {R : Fin K → ℕ → Ω → ℝ} (hm : ∀ i j, Measurable (R i j)) (i : Fin K) (s : ℕ) :
    Measurable (armSampleAverage R i s) := by
  unfold armSampleAverage
  exact (Finset.measurable_sum _ fun j _ ↦ hm i j).div_const _

section Counting

variable {Ω : Type*} {K : ℕ}

/-- The play count increases by one exactly at a play of the arm. -/
theorem armPlayCount_succ (A : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ) (ω : Ω) :
    armPlayCount A i (t + 1) ω = armPlayCount A i t ω + if A t ω = i then 1 else 0 := by
  unfold armPlayCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- Play counts are monotone in time. -/
theorem armPlayCount_mono (A : ℕ → Ω → Fin K) (i : Fin K) {t t' : ℕ} (h : t ≤ t') (ω : Ω) :
    armPlayCount A i t ω ≤ armPlayCount A i t' ω :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- The play count after `t` rounds is at most `t`. -/
theorem armPlayCount_le (A : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ) (ω : Ω) :
    armPlayCount A i t ω ≤ t :=
  (Finset.card_filter_le _ _).trans (Finset.card_range t).le

/-- A play of the arm at time `t` makes its count strictly larger at every later time. -/
theorem armPlayCount_lt_of_play (A : ℕ → Ω → Fin K) (i : Fin K) {t t' : ℕ} (h : t < t')
    {ω : Ω} (hA : A t ω = i) : armPlayCount A i t ω < armPlayCount A i t' ω := by
  have := armPlayCount_succ A i t ω
  simp only [hA, ↓reduceIte] at this
  have := armPlayCount_mono A i (show t + 1 ≤ t' from h) ω
  omega

/-- At most `ℓ` plays of an arm happen while its count is below `ℓ`. -/
theorem card_filter_play_count_lt_le (A : ℕ → Ω → Fin K) (i : Fin K) (T ℓ : ℕ) (ω : Ω) :
    ((Finset.range T).filter fun t ↦ A t ω = i ∧ armPlayCount A i t ω < ℓ).card ≤ ℓ := by
  calc _ ≤ (Finset.range ℓ).card := by
        refine Finset.card_le_card_of_injOn (fun t ↦ armPlayCount A i t ω) ?_ ?_
        · intro t ht
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
          simpa using ht.2.2
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact absurd hab (armPlayCount_lt_of_play A i h ha.2.1).ne
          · exact absurd hab (armPlayCount_lt_of_play A i h hb.2.1).ne'
    _ = ℓ := Finset.card_range ℓ

/-- If the first `K` rounds play each arm once, then every arm has been played at least once
by any time `t ≥ K`. -/
theorem one_le_armPlayCount (A : ℕ → Ω → Fin K)
    (hinit : ∀ t : ℕ, ∀ ht : t < K, ∀ ω, A t ω = ⟨t, ht⟩) (i : Fin K) {t : ℕ} (ht : K ≤ t)
    (ω : Ω) : 1 ≤ armPlayCount A i t ω := by
  unfold armPlayCount
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
  exact ⟨i.val, by simp [hinit i.val i.isLt ω, lt_of_lt_of_le i.isLt ht]⟩

/-- Plays during the initialization rounds: the count of an arm before its initial play is
zero, so with `1 ≤ ℓ` all plays with count at least `ℓ` happen at times `t ≥ K`. -/
theorem armPlayCount_le_add_card (A : ℕ → Ω → Fin K)
    (hinit : ∀ t : ℕ, ∀ ht : t < K, ∀ ω, A t ω = ⟨t, ht⟩) (i : Fin K) (T ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (ω : Ω) :
    armPlayCount A i T ω ≤ ℓ + ((Finset.Ico K T).filter fun t ↦
      A t ω = i ∧ ℓ ≤ armPlayCount A i t ω).card := by
  have hsub : (Finset.range T).filter (fun t ↦ A t ω = i) ⊆
      (Finset.range T).filter (fun t ↦ A t ω = i ∧ armPlayCount A i t ω < ℓ) ∪
      (Finset.Ico K T).filter fun t ↦ A t ω = i ∧ ℓ ≤ armPlayCount A i t ω := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hc : armPlayCount A i t ω < ℓ
    · exact Or.inl ⟨ht.1, ht.2, hc⟩
    · right
      refine ⟨⟨?_, ht.1⟩, ht.2, not_lt.1 hc⟩
      by_contra htK
      push Not at htK
      apply hc
      have hti : t = i.val := by
        have := hinit t htK ω
        rw [ht.2] at this
        rw [this]
      have h0 : armPlayCount A i t ω = 0 := by
        unfold armPlayCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj hji
        rw [Finset.mem_range] at hj
        have := hinit j (hj.trans htK) ω
        rw [hji] at this
        have : i.val = j := congrArg Fin.val this
        omega
      omega
  calc armPlayCount A i T ω ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by
      have := card_filter_play_count_lt_le A i T ℓ ω
      omega

/-- The deterministic step of the UCB1 analysis: if a suboptimal arm `i` with gap `Δ` is
played at a time `t ≥ K` after at least `ℓ` earlier plays, where `8 log t ≤ Δ² ℓ`, then either
the average of the optimal arm lies below its mean by the confidence radius, or the average of
arm `i` lies above its mean by the confidence radius. -/
theorem ucb_deviation_of_play (R : Fin K → ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (hucb : ∀ t ≥ K, ∀ ω i, armSampleAverage R i (armPlayCount A i t ω) ω +
        Real.sqrt (2 * Real.log t / armPlayCount A i t ω) ≤
      armSampleAverage R (A t ω) (armPlayCount A (A t ω) t ω) ω +
        Real.sqrt (2 * Real.log t / armPlayCount A (A t ω) t ω))
    {i star : Fin K} {μi μs : ℝ} (hΔ : μi < μs) {ℓ t : ℕ} (hℓ : 0 < ℓ)
    (hℓt : 8 * Real.log t ≤ (μs - μi) ^ 2 * ℓ) (ht : K ≤ t) {ω : Ω} (hA : A t ω = i)
    (hN : ℓ ≤ armPlayCount A i t ω) :
    armSampleAverage R star (armPlayCount A star t ω) ω ≤
        μs - Real.sqrt (2 * Real.log t / armPlayCount A star t ω) ∨
      μi + Real.sqrt (2 * Real.log t / armPlayCount A i t ω) ≤
        armSampleAverage R i (armPlayCount A i t ω) ω := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hu := hucb t ht ω star
  rw [hA] at hu
  set N := (armPlayCount A i t ω : ℝ)
  set ci := Real.sqrt (2 * Real.log t / N)
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
    exact this.trans_le (Nat.cast_le.mpr hN)
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hlt : μs - μi < 2 * ci := by linarith
  have hci : ci ^ 2 = 2 * Real.log t / N := Real.sq_sqrt (by positivity)
  have hsq : (μs - μi) ^ 2 < (2 * ci) ^ 2 :=
    pow_lt_pow_left₀ hlt (by linarith) two_ne_zero
  have hℓr : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
  have hNℓ : (ℓ : ℝ) ≤ N := Nat.cast_le.mpr hN
  have : 8 * Real.log t / N ≤ (μs - μi) ^ 2 := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have : (2 * ci) ^ 2 = 8 * Real.log t / N := by rw [mul_pow, hci]; ring
  linarith

end Counting

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

/-- Play counts of a measurable arm process are measurable. -/
theorem measurable_armPlayCount (A : ℕ → Ω → Fin K) (hA : ∀ t, Measurable (A t)) (i : Fin K)
    (t : ℕ) : Measurable fun ω ↦ armPlayCount A i t ω := by
  have : (fun ω ↦ armPlayCount A i t ω) =
      fun ω ↦ ∑ j ∈ Finset.range t, if A j ω = i then 1 else 0 := by
    funext ω; unfold armPlayCount; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun j _ ↦
    Measurable.ite (measurableSet_eq_fun (hA j) measurable_const) measurable_const
      measurable_const

/-- The Hoeffding bound at the UCB1 confidence radius: `exp(-2 s c²) = t⁻⁴` for
`c = √(2 log t / s)`. -/
theorem exp_neg_two_mul_sqrt_sq_eq (t s : ℕ) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    Real.exp (-2 * s * Real.sqrt (2 * Real.log t / s) ^ 2) = ((t : ℝ) ^ 4)⁻¹ := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog := Real.log_natCast_nonneg t
  rw [Real.sq_sqrt (div_nonneg (by positivity) hs'.le)]
  rw [show -2 * (s : ℝ) * (2 * Real.log t / s) = -Real.log ((t : ℝ) ^ 4) by
    rw [Real.log_pow]; field_simp; push_cast; ring]
  rw [Real.exp_neg, Real.exp_log (by positivity)]

/-- `t · t⁻⁴ ≤ t⁻²` for `t ≥ 1`. -/
theorem natCast_mul_inv_pow_four_le (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) * ((t : ℝ) ^ 4)⁻¹ ≤ ((t : ℝ) ^ 2)⁻¹ := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  rw [show (t : ℝ) * ((t : ℝ) ^ 4)⁻¹ = ((t : ℝ) ^ 2)⁻¹ * (t : ℝ)⁻¹ by field_simp]
  exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ ht')

/-- Expected play count of a suboptimal arm under UCB1 (Auer, Cesa-Bianchi and Fischer):
for an arm `i` whose mean is below that of an arm `star` by `Δ > 0`, the expected number of
plays of `i` during the first `T` rounds is at most `8 log T / Δ² + 3`. The reward table has
independent entries in `[0,1]` almost surely, with a common law along each arm; the arm
process plays each arm once during the first `K` rounds and afterwards an arm of maximal
UCB1 index. -/
theorem integral_armPlayCount_le_of_ucb (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin K → ℕ → Ω → ℝ) (hm : ∀ i j, Measurable (R i j))
    (hb : ∀ i j, ∀ᵐ ω ∂P, R i j ω ∈ Icc 0 1)
    (hind : iIndepFun (fun z : Fin K × ℕ ↦ R z.1 z.2) P)
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0))
    (A : ℕ → Ω → Fin K)
    (hinit : ∀ t : ℕ, ∀ ht : t < K, ∀ ω, A t ω = ⟨t, ht⟩)
    (hucb : ∀ t ≥ K, ∀ ω i, armSampleAverage R i (armPlayCount A i t ω) ω +
        Real.sqrt (2 * Real.log t / armPlayCount A i t ω) ≤
      armSampleAverage R (A t ω) (armPlayCount A (A t ω) t ω) ω +
        Real.sqrt (2 * Real.log t / armPlayCount A (A t ω) t ω))
    {i star : Fin K} (hΔ : ∫ ω, R i 0 ω ∂P < ∫ ω, R star 0 ω ∂P) (T : ℕ) :
    ∫ ω, (armPlayCount A i T ω : ℝ) ∂P ≤
      8 * Real.log T / (∫ ω, R star 0 ω ∂P - ∫ ω, R i 0 ω ∂P) ^ 2 + 3 := by
  have hK : 2 ≤ K := by
    have hne : i ≠ star := by rintro rfl; exact lt_irrefl _ hΔ
    have := Fin.val_ne_of_ne hne
    omega
  set μi := ∫ ω, R i 0 ω ∂P
  set μs := ∫ ω, R star 0 ω ∂P
  have hΔ0 : 0 < μs - μi := sub_pos.mpr hΔ
  have hNnn : ∀ ω, (0 : ℝ) ≤ armPlayCount A i T ω := fun ω ↦ Nat.cast_nonneg _
  have hlogT0 : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hfrac0 : 0 ≤ 8 * Real.log T / (μs - μi) ^ 2 := by positivity
  by_cases hT : T < 2
  · calc ∫ ω, (armPlayCount A i T ω : ℝ) ∂P ≤ ∫ _ω, (T : ℝ) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ hNnn) (integrable_const _)
            (ae_of_all _ fun ω ↦ Nat.cast_le.mpr (armPlayCount_le A i T ω))
      _ = T := by simp
      _ ≤ _ := by
        have : (T : ℝ) ≤ 1 := by exact_mod_cast (by omega : T ≤ 1)
        linarith
  push Not at hT
  have hTr : (1 : ℝ) < T := by exact_mod_cast hT
  have hlogT : 0 < Real.log T := Real.log_pos hTr
  set ℓ := ⌈8 * Real.log T / (μs - μi) ^ 2⌉₊ with hℓ_def
  have hℓpos : 0 < ℓ := Nat.lt_ceil.mpr (by simp only [Nat.cast_zero]; positivity)
  have hℓlt : (ℓ : ℝ) < 8 * Real.log T / (μs - μi) ^ 2 + 1 := Nat.ceil_lt_add_one hfrac0
  have hℓge : 8 * Real.log T / (μs - μi) ^ 2 ≤ ℓ := Nat.le_ceil _
  have hℓt : ∀ t : ℕ, 1 ≤ t → t < T → 8 * Real.log t ≤ (μs - μi) ^ 2 * ℓ := by
    intro t ht1 htT
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have hlog : Real.log t ≤ Real.log T :=
      Real.log_le_log ht0 (by exact_mod_cast htT.le)
    have : 8 * Real.log T ≤ (μs - μi) ^ 2 * ℓ := by
      rw [div_le_iff₀ (by positivity)] at hℓge
      linarith
    linarith
  set c : ℕ → ℕ → ℝ := fun t s ↦ Real.sqrt (2 * Real.log t / s)
  set B1 : ℕ → ℕ → Set Ω := fun t s ↦ {ω | armSampleAverage R star s ω ≤ μs - c t s}
  set B2 : ℕ → ℕ → Set Ω := fun t s ↦ {ω | μi + c t s ≤ armSampleAverage R i s ω}
  have hB1m : ∀ t s, MeasurableSet (B1 t s) := fun t s ↦
    measurableSet_le (measurable_armSampleAverage hm _ _) measurable_const
  have hB2m : ∀ t s, MeasurableSet (B2 t s) := fun t s ↦
    measurableSet_le measurable_const (measurable_armSampleAverage hm _ _)
  set F : Ω → ℝ := fun ω ↦ (ℓ : ℝ) + ∑ t ∈ Finset.Ico K T,
    (∑ s ∈ Finset.Icc 1 t, (B1 t s).indicator (1 : Ω → ℝ) ω +
      ∑ s ∈ Finset.Icc 1 t, (B2 t s).indicator (1 : Ω → ℝ) ω)
  have hpt : ∀ ω, (armPlayCount A i T ω : ℝ) ≤ F ω := by
    intro ω
    have h1 := armPlayCount_le_add_card A hinit i T ℓ hℓpos ω
    have h1r : (armPlayCount A i T ω : ℝ) ≤ ℓ + ∑ t ∈ Finset.Ico K T,
        if A t ω = i ∧ ℓ ≤ armPlayCount A i t ω then (1 : ℝ) else 0 := by
      rw [Finset.card_filter] at h1
      exact_mod_cast h1
    refine h1r.trans (add_le_add_right (Finset.sum_le_sum fun t ht ↦ ?_) _)
    rw [Finset.mem_Ico] at ht
    have hnn1 : 0 ≤ ∑ s ∈ Finset.Icc 1 t, (B1 t s).indicator (1 : Ω → ℝ) ω :=
      Finset.sum_nonneg fun s _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    have hnn2 : 0 ≤ ∑ s ∈ Finset.Icc 1 t, (B2 t s).indicator (1 : Ω → ℝ) ω :=
      Finset.sum_nonneg fun s _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    split_ifs with hc
    · have hdev := ucb_deviation_of_play R A hucb (star := star) hΔ hℓpos
        (hℓt t (by omega) ht.2) ht.1 hc.1 hc.2
      have hmem : ∀ k : Fin K, armPlayCount A k t ω ∈ Finset.Icc 1 t := fun k ↦
        Finset.mem_Icc.mpr ⟨one_le_armPlayCount A hinit k ht.1 ω, armPlayCount_le A k t ω⟩
      rcases hdev with h | h
      · have : (B1 t (armPlayCount A star t ω)).indicator (1 : Ω → ℝ) ω = 1 :=
          Set.indicator_of_mem h _
        have := Finset.single_le_sum (f := fun s ↦ (B1 t s).indicator (1 : Ω → ℝ) ω)
          (fun s _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hmem star)
        linarith
      · have : (B2 t (armPlayCount A i t ω)).indicator (1 : Ω → ℝ) ω = 1 :=
          Set.indicator_of_mem h _
        have := Finset.single_le_sum (f := fun s ↦ (B2 t s).indicator (1 : Ω → ℝ) ω)
          (fun s _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hmem i)
        linarith
    · positivity
  have hI1 : ∀ t s, Integrable ((B1 t s).indicator (1 : Ω → ℝ)) P := fun t s ↦
    (integrable_const 1).indicator (hB1m t s)
  have hI2 : ∀ t s, Integrable ((B2 t s).indicator (1 : Ω → ℝ)) P := fun t s ↦
    (integrable_const 1).indicator (hB2m t s)
  have hIt : ∀ t, Integrable (fun ω ↦ ∑ s ∈ Finset.Icc 1 t, (B1 t s).indicator (1 : Ω → ℝ) ω +
      ∑ s ∈ Finset.Icc 1 t, (B2 t s).indicator (1 : Ω → ℝ) ω) P := fun t ↦
    (integrable_finsetSum _ fun s _ ↦ hI1 t s).add (integrable_finsetSum _ fun s _ ↦ hI2 t s)
  have hFint : Integrable F P :=
    (integrable_const _).add (integrable_finsetSum _ fun t _ ↦ hIt t)
  have hFeq : ∫ ω, F ω ∂P = ℓ + ∑ t ∈ Finset.Ico K T,
      (∑ s ∈ Finset.Icc 1 t, P.real (B1 t s) + ∑ s ∈ Finset.Icc 1 t, P.real (B2 t s)) := by
    simp only [F]
    rw [integral_add (integrable_const _) (integrable_finsetSum _ fun t _ ↦ hIt t),
      integral_const, integral_finsetSum _ fun t _ ↦ hIt t]
    simp only [probReal_univ, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [integral_add (integrable_finsetSum _ fun s _ ↦ hI1 t s)
        (integrable_finsetSum _ fun s _ ↦ hI2 t s),
      integral_finsetSum _ fun s _ ↦ hI1 t s, integral_finsetSum _ fun s _ ↦ hI2 t s]
    simp only [integral_indicator_one (hB1m _ _), integral_indicator_one (hB2m _ _)]
  have hbound : ∀ t ∈ Finset.Ico K T,
      ∑ s ∈ Finset.Icc 1 t, P.real (B1 t s) + ∑ s ∈ Finset.Icc 1 t, P.real (B2 t s) ≤
        2 * ((t : ℝ) ^ 2)⁻¹ := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have ht1 : 1 ≤ t := by omega
    have hs1 : ∀ s ∈ Finset.Icc 1 t, P.real (B1 t s) ≤ ((t : ℝ) ^ 4)⁻¹ := by
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      rw [← exp_neg_two_mul_sqrt_sq_eq t s ht1 hs1]
      exact measureReal_armSampleAverage_le_sub_le hm hb hind hlaw star hs1
        (Real.sqrt_nonneg _)
    have hs2 : ∀ s ∈ Finset.Icc 1 t, P.real (B2 t s) ≤ ((t : ℝ) ^ 4)⁻¹ := by
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      rw [← exp_neg_two_mul_sqrt_sq_eq t s ht1 hs1]
      exact measureReal_add_le_armSampleAverage_le hm hb hind hlaw i hs1 (Real.sqrt_nonneg _)
    have hsum : ∑ _s ∈ Finset.Icc 1 t, ((t : ℝ) ^ 4)⁻¹ = (t : ℝ) * ((t : ℝ) ^ 4)⁻¹ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have := natCast_mul_inv_pow_four_le t ht1
    have h1 := Finset.sum_le_sum hs1
    have h2 := Finset.sum_le_sum hs2
    rw [hsum] at h1 h2
    linarith
  have hzeta : ∑ t ∈ Finset.Ico K T, 2 * ((t : ℝ) ^ 2)⁻¹ ≤ 2 := by
    rw [← Finset.mul_sum]
    have hsub : Finset.Ico K T ⊆ Finset.Ioo 1 T := by
      intro t ht
      simp only [Finset.mem_Ico, Finset.mem_Ioo] at ht ⊢
      omega
    have h1 : ∑ t ∈ Finset.Ico K T, ((t : ℝ) ^ 2)⁻¹ ≤ ∑ t ∈ Finset.Ioo 1 T, ((t : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    have h2 := sum_Ioo_inv_sq_le (α := ℝ) 1 T
    norm_num at h2
    linarith
  calc ∫ ω, (armPlayCount A i T ω : ℝ) ∂P ≤ ∫ ω, F ω ∂P :=
        integral_mono_of_nonneg (ae_of_all _ hNnn) hFint (ae_of_all _ hpt)
    _ ≤ ℓ + 2 := by
        rw [hFeq]
        linarith [Finset.sum_le_sum hbound]
    _ ≤ _ := by linarith

/-- Play counts of a measurable arm process are integrable. -/
theorem integrable_armPlayCount (P : Measure Ω) [IsFiniteMeasure P] (A : ℕ → Ω → Fin K)
    (hA : ∀ t, Measurable (A t)) (i : Fin K) (t : ℕ) :
    Integrable (fun ω ↦ (armPlayCount A i t ω : ℝ)) P := by
  refine Integrable.of_bound (C := t)
    (measurable_from_top.comp (measurable_armPlayCount A hA i t)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_natCast]
  exact Nat.cast_le.mpr (armPlayCount_le A i t ω)

omit [MeasurableSpace Ω] in
/-- A sum over rounds of a function of the arm played, regrouped by arms. -/
theorem sum_range_comp_eq_sum_mul_armPlayCount {M : Type*} [CommRing M]
    (A : ℕ → Ω → Fin K) (f : Fin K → M) (T : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range T, f (A t ω) = ∑ i, f i * armPlayCount A i T ω := by
  rw [← Finset.sum_fiberwise (Finset.range T) (fun t ↦ A t ω)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2], Finset.sum_const,
    nsmul_eq_mul, mul_comm]
  rfl

end Expectation

end CKSD
