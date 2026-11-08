module

public import CKSD.Inference.Density
public import TauCeti.Probability.Quantile

/-!
# The Neyman–Pearson lemma and threshold tests

The Neyman–Pearson lemma for two laws with densities, its generalized form with several side
conditions and signed multipliers, and the comparison steps behind the Karlin–Rubin theorem for
families with monotone likelihood ratio. Threshold tests `CKSD.thresholdTest` in a real
statistic attain every size in `(0, 1)`.

## Main results

* `CKSD.integral_le_of_generalized_neyman_pearson`: the generalized Neyman–Pearson lemma
  (GAPS 101.47).
* `CKSD.exists_neyman_pearson_test`: existence and optimality of a most powerful test of a simple
  hypothesis against a simple alternative (GAPS 101.14).
* `CKSD.integral_le_integral_thresholdTest_of_monotone_likelihood_ratio` and
  `CKSD.integral_thresholdTest_le_of_monotone_likelihood_ratio`: the two Neyman–Pearson
  comparisons for a monotone likelihood ratio.
* `CKSD.integral_thresholdTest`, `CKSD.exists_integral_thresholdTest_eq`: sizes of threshold
  tests.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, Sections 3.2–3.4 and 3.6.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X]

/-- GAPS 101.47: the generalized Neyman–Pearson lemma, sufficiency part, with signed multipliers.
If the test `φ` rejects where `f₀ > ∑ kᵢ fᵢ` and accepts where `f₀ < ∑ kᵢ fᵢ`, and a test `ψ`
satisfies the side conditions `kᵢ ∫ ψ fᵢ ≤ kᵢ ∫ φ fᵢ`, then `∫ ψ f₀ ≤ ∫ φ f₀`. -/
theorem integral_le_of_generalized_neyman_pearson {m : ℕ} (μ : Measure X) (f₀ : X → ℝ)
    (f : Fin m → X → ℝ) (k : Fin m → ℝ) (hf₀ : Integrable f₀ μ)
    (hf : ∀ i, Integrable (f i) μ) (φ ψ : X → ℝ)
    (hφ : IsStatisticalTest φ) (hψ : IsStatisticalTest ψ)
    (hthreshold : ∀ᵐ x ∂μ, ((∑ i, k i * f i x) < f₀ x → φ x = 1) ∧
      (f₀ x < (∑ i, k i * f i x) → φ x = 0))
    (hconstraints : ∀ i, k i * (∫ x, ψ x * f i x ∂μ) ≤
      k i * (∫ x, φ x * f i x ∂μ)) :
    (∫ x, ψ x * f₀ x ∂μ) ≤ ∫ x, φ x * f₀ x ∂μ := by
  have hiφ₀ := hφ.integrable_mul hf₀
  have hiψ₀ := hψ.integrable_mul hf₀
  have hiφ (i : Fin m) := hφ.integrable_mul (hf i)
  have hiψ (i : Fin m) := hψ.integrable_mul (hf i)
  have hi (i : Fin m) : Integrable (fun x ↦ k i * (ψ x * f i x - φ x * f i x)) μ :=
    ((hiψ i).sub (hiφ i)).const_mul (k i)
  have hpoint : ∀ᵐ x ∂μ, ψ x * f₀ x - φ x * f₀ x ≤
      ∑ i, k i * (ψ x * f i x - φ x * f i x) := by
    filter_upwards [hthreshold] with x ht
    have hprod : (ψ x - φ x) * (f₀ x - ∑ i, k i * f i x) ≤ 0 := by
      rcases lt_trichotomy (∑ i, k i * f i x) (f₀ x) with h | h | h
      · rw [ht.1 h]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hψ.2 x).2]) (by linarith)
      · simp [h]
      · rw [ht.2 h]
        exact mul_nonpos_of_nonneg_of_nonpos (by simpa using (hψ.2 x).1) (by linarith)
    have hsum : (∑ i, k i * (ψ x * f i x - φ x * f i x)) =
        (ψ x - φ x) * ∑ i, k i * f i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    nlinarith [hprod]
  have hmono := integral_mono_ae (hiψ₀.sub hiφ₀)
    (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)) hpoint
  have hleft : (∫ x, ψ x * f₀ x - φ x * f₀ x ∂μ) =
      (∫ x, ψ x * f₀ x ∂μ) - ∫ x, φ x * f₀ x ∂μ := by
    simpa only [Pi.sub_apply] using integral_sub hiψ₀ hiφ₀
  have hterm (i : Fin m) :
      (∫ x, k i * (ψ x * f i x - φ x * f i x) ∂μ) =
        k i * ((∫ x, ψ x * f i x ∂μ) - ∫ x, φ x * f i x ∂μ) := by
    rw [integral_const_mul]
    congr 1
    simpa only [Pi.sub_apply] using integral_sub (hiψ i) (hiφ i)
  have hright : (∫ x, ∑ i, k i * (ψ x * f i x - φ x * f i x) ∂μ) ≤ 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
    simp_rw [hterm]
    apply Finset.sum_nonpos
    intro i _
    nlinarith [hconstraints i]
  simp only [Pi.sub_apply] at hmono
  rw [hleft] at hmono
  linarith

/-- GAPS 101.14: the Neyman–Pearson lemma, existence and sufficiency. For laws `P₀`, `P₁` with
densities `f₀`, `f₁` with respect to `μ` and a size `α ∈ (0, 1)`, there are `k ≥ 0` and a test `φ`
of exact size `α` under `P₀` with `φ = 1` on `{f₁ > k f₀}` and `φ = 0` on `{f₁ < k f₀}`; it is
most powerful at level `α`. The almost-everywhere uniqueness of most powerful tests is not
included. -/
theorem exists_neyman_pearson_test (P₀ P₁ μ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (f₀ f₁ : X → ℝ)
    (h₀ : HasDensity P₀ μ f₀) (h₁ : HasDensity P₁ μ f₁)
    (α : ℝ) (hα : α ∈ Ioo 0 1) :
    ∃ k : ℝ, 0 ≤ k ∧ ∃ φ : X → ℝ, IsStatisticalTest φ ∧
      (∫ x, φ x ∂P₀) = α ∧
      (∀ᵐ x ∂μ, (k * f₀ x < f₁ x → φ x = 1) ∧
        (f₁ x < k * f₀ x → φ x = 0)) ∧
      ∀ ψ, IsStatisticalTest ψ → (∫ x, ψ x ∂P₀) ≤ α →
        (∫ x, ψ x ∂P₁) ≤ ∫ x, φ x ∂P₁ := by
  -- `f₀` is positive and `f₁` nonnegative `P₀`-almost everywhere
  have hpos0 : ∀ᵐ x ∂P₀, 0 < f₀ x := by
    rw [ae_iff]
    have hm : MeasurableSet {x | ¬ 0 < f₀ x} := (measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const h₀.1).compl
    rw [h₀.2.2, withDensity_apply _ hm]
    refine (setLIntegral_congr_fun hm fun x hx ↦ ?_).trans lintegral_zero
    exact ENNReal.ofReal_eq_zero.2 (not_lt.1 hx)
  have hac : P₀ ≪ μ := h₀.2.2 ▸ withDensity_absolutelyContinuous μ _
  have hnn1 : ∀ᵐ x ∂P₀, 0 ≤ f₁ x := hac.ae_le h₁.2.1
  -- the strict and weak likelihood-ratio regions, intersected with `{0 < f₀}`
  let S' : ℝ → Set X := fun k ↦ {x | 0 < f₀ x ∧ k * f₀ x < f₁ x}
  let T' : ℝ → Set X := fun k ↦ {x | 0 < f₀ x ∧ k * f₀ x ≤ f₁ x}
  have hpm : MeasurableSet {x | 0 < f₀ x} :=
    measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const h₀.1
  have hS'm (k : ℝ) : MeasurableSet (S' k) :=
    hpm.inter (measurableSet_lt (f := fun x ↦ k * f₀ x) (h₀.1.const_mul k) h₁.1)
  have hT'm (k : ℝ) : MeasurableSet (T' k) :=
    hpm.inter (measurableSet_le (f := fun x ↦ k * f₀ x) (h₀.1.const_mul k) h₁.1)
  have hanti {k k' : ℝ} (hkk : k ≤ k') : S' k' ⊆ S' k := fun x hx ↦
    ⟨hx.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hkk hx.1.le) hx.2⟩
  have hST (k : ℝ) : S' k ⊆ T' k := fun x hx ↦ ⟨hx.1, hx.2.le⟩
  have hαpos : (0 : ℝ≥0∞) < ENNReal.ofReal α := ENNReal.ofReal_pos.2 hα.1
  -- the masses of `S' n` tend to zero
  have hlim : Tendsto (fun n : ℕ ↦ P₀ (S' n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P₀) (s := fun n : ℕ ↦ S' n)
      (fun n ↦ (hS'm n).nullMeasurableSet)
      (fun m n hmn ↦ hanti (by exact_mod_cast hmn)) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, S' n) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      rw [mem_iInter] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (f₁ x / f₀ x)
      have h1 := (hx n).2
      have h2 := (hx n).1
      rw [div_lt_iff₀ h2] at hn
      linarith
    rw [hempty, measure_empty] at h
    exact h
  let K : Set ℝ := {k | 0 ≤ k ∧ P₀ (S' k) ≤ ENNReal.ofReal α}
  have hKne : K.Nonempty := by
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hαpos)).exists
    exact ⟨n, Nat.cast_nonneg n, hn.le⟩
  have hKbdd : BddBelow K := ⟨0, fun k hk ↦ hk.1⟩
  set k := sInf K with hkdef
  have hk0 : 0 ≤ k := le_csInf hKne fun k hk ↦ hk.1
  -- right continuity: the strict region at `k` has mass at most `α`
  have hright : P₀ (S' k) ≤ ENNReal.ofReal α := by
    have hU : S' k = ⋃ m : ℕ, S' (k + 1 / ((m : ℝ) + 1)) := by
      ext x
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 hx.2) hx.1)
        refine mem_iUnion.2 ⟨m, hx.1, ?_⟩
        rw [lt_div_iff₀ hx.1] at hm
        nlinarith
      · obtain ⟨m, hm⟩ := mem_iUnion.1 hx
        exact hanti (le_add_of_nonneg_right (by positivity)) hm
    have hmono : Monotone fun m : ℕ ↦ S' (k + 1 / ((m : ℝ) + 1)) := fun m n hmn ↦
      hanti (by
        have h1 : (m : ℝ) ≤ n := by exact_mod_cast hmn
        have h2 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
          (by linarith : (m : ℝ) + 1 ≤ (n : ℝ) + 1)
        linarith)
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun m ↦ ?_
    obtain ⟨k', hk'K, hk'lt⟩ := exists_lt_of_csInf_lt hKne
      (show sInf K < k + 1 / ((m : ℝ) + 1) by rw [← hkdef]; linarith [show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity])
    exact (measure_mono (hanti hk'lt.le)).trans hk'K.2
  -- left limit: the weak region at `k` has mass at least `α`
  have hleft : ENNReal.ofReal α ≤ P₀ (T' k) := by
    rcases hk0.lt_or_eq with hkpos | hkzero
    · let kk : ℕ → ℝ := fun m ↦ k - k / ((m : ℝ) + 2)
      have hkk_lt (m : ℕ) : kk m < k := sub_lt_self _ (by positivity)
      have hkk_nn (m : ℕ) : 0 ≤ kk m := by
        have : k / ((m : ℝ) + 2) ≤ k := div_le_self hk0 (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
        simp only [kk]; linarith
      have hbig (m : ℕ) : ENNReal.ofReal α < P₀ (S' (kk m)) := by
        by_contra h
        have hmem : kk m ∈ K := ⟨hkk_nn m, not_lt.1 h⟩
        exact absurd (csInf_le hKbdd hmem) (not_le.2 (hkdef ▸ hkk_lt m))
      have hanti' : Antitone fun m : ℕ ↦ S' (kk m) := fun m n hmn ↦ hanti (by
        simp only [kk]
        exact sub_le_sub_left (div_le_div_of_nonneg_left hk0 (by positivity)
          (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
              linarith)) k)
      have hsub : (⋂ m : ℕ, S' (kk m)) ⊆ T' k := by
        intro x hx
        rw [mem_iInter] at hx
        refine ⟨(hx 0).1, ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        have hf0 := (hx 0).1
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 hlt) (mul_pos hkpos hf0))
        have h1 := (hx m).2
        simp only [kk] at h1
        have h2 : 1 / ((m : ℝ) + 2) < 1 / ((m : ℝ) + 1) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
        have h3 : k * f₀ x / ((m : ℝ) + 2) < k * f₀ x - f₁ x := by
          have := mul_lt_mul_of_pos_left (h2.trans hm) (mul_pos hkpos hf0)
          rw [mul_div_cancel₀ _ (mul_pos hkpos hf0).ne'] at this
          rw [mul_one_div] at this
          exact this
        have h4 : (k - k / ((m : ℝ) + 2)) * f₀ x = k * f₀ x - k * f₀ x / ((m : ℝ) + 2) := by
          ring
        linarith
      calc ENNReal.ofReal α ≤ ⨅ m : ℕ, P₀ (S' (kk m)) := le_iInf fun m ↦ (hbig m).le
        _ = P₀ (⋂ m : ℕ, S' (kk m)) :=
          (hanti'.measure_iInter (fun m ↦ (hS'm _).nullMeasurableSet)
            ⟨0, measure_ne_top _ _⟩).symm
        _ ≤ P₀ (T' k) := measure_mono hsub
    · have hall : ∀ᵐ x ∂P₀, x ∈ T' k := by
        filter_upwards [hpos0, hnn1] with x hx1 hx2
        exact ⟨hx1, by rw [← hkzero, zero_mul]; exact hx2⟩
      have h1 : P₀ (T' k) = 1 := by
        rw [← prob_compl_eq_zero_iff (hT'm k)]
        exact ae_iff.1 hall
      rw [h1]
      exact ENNReal.ofReal_le_one.2 hα.2.le
  -- the randomization constant
  set a := P₀.real (S' k) with ha
  set t := P₀.real (T' k) with ht
  have haα : a ≤ α := ENNReal.toReal_le_of_le_ofReal hα.1.le hright
  have hαt : α ≤ t := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hleft
  let γ : ℝ := if t - a = 0 then 0 else (α - a) / (t - a)
  have hγ : γ ∈ Icc (0 : ℝ) 1 := by
    simp only [γ]
    split_ifs with h
    · exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < t - a := lt_of_le_of_ne (by linarith) (Ne.symm h)
      exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩
  have hγeq : a + γ * (t - a) = α := by
    simp only [γ]
    split_ifs with h
    · linarith
    · rw [div_mul_cancel₀ _ h]; ring
  -- the test
  let S : Set X := {x | k * f₀ x < f₁ x}
  let E : Set X := {x | f₁ x = k * f₀ x}
  have hSm : MeasurableSet S :=
    measurableSet_lt (f := fun x ↦ k * f₀ x) (h₀.1.const_mul k) h₁.1
  have hEm : MeasurableSet E :=
    measurableSet_eq_fun (f := f₁) (g := fun x ↦ k * f₀ x) h₁.1 (h₀.1.const_mul k)
  let φ : X → ℝ := fun x ↦ if k * f₀ x < f₁ x then 1 else if f₁ x = k * f₀ x then γ else 0
  have hφ : IsStatisticalTest φ := by
    refine ⟨Measurable.ite hSm measurable_const (Measurable.ite hEm measurable_const
      measurable_const), fun x ↦ ?_⟩
    simp only [φ]
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hγ
    · exact ⟨le_rfl, zero_le_one⟩
  have hφeq : φ = fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) x + E.indicator (fun _ ↦ γ) x := by
    funext x
    simp only [φ, S, E, indicator, mem_ofPred_eq]
    split_ifs <;> linarith
  have hSa : P₀.real S = a := by
    refine measureReal_congr ?_
    filter_upwards [hpos0] with x hx
    exact propext ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  have hEa : P₀.real E = t - a := by
    have hE' : E =ᵐ[P₀] (T' k \ S' k : Set X) := by
      filter_upwards [hpos0] with x hx
      refine propext ⟨fun h ↦ ⟨⟨hx, h.symm ▸ le_rfl⟩, fun h' ↦ ?_⟩, fun h ↦ ?_⟩
      · have := h'.2
        simp only [E, mem_ofPred_eq] at h
        linarith
      · exact le_antisymm (not_lt.1 fun h' ↦ h.2 ⟨hx, h'⟩) h.1.2
    rw [measureReal_congr hE', measureReal_sdiff (hST k) (hS'm k)]
  have hsize : (∫ x, φ x ∂P₀) = α := by
    rw [hφeq, integral_add ((integrable_const (1 : ℝ)).indicator hSm)
      ((integrable_const γ).indicator hEm), integral_indicator_const _ hSm,
      integral_indicator_const _ hEm, hSa, hEa, smul_eq_mul, smul_eq_mul]
    linarith
  refine ⟨k, hk0, φ, hφ, hsize, ae_of_all _ fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩,
    fun ψ hψ hψα ↦ ?_⟩
  · simp [φ, h]
  · simp [φ, not_lt.2 h.le, h.ne]
  · have key := integral_le_of_generalized_neyman_pearson (m := 1) μ f₁ (fun _ ↦ f₀)
      (fun _ ↦ k) h₁.integrable (fun _ ↦ h₀.integrable) φ ψ hφ hψ
      (ae_of_all _ fun x ↦ ?_) (fun _ ↦ ?_)
    · rw [h₁.integral_eq, h₁.integral_eq]
      simpa only [mul_comm] using key
    · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      exact ⟨fun h ↦ by simp [φ, h], fun h ↦ by simp [φ, not_lt.2 h.le, h.ne]⟩
    · have hle : (∫ x, ψ x ∂P₀) ≤ ∫ x, φ x ∂P₀ := hsize ▸ hψα
      rw [h₀.integral_eq, h₀.integral_eq] at hle
      simp only [mul_comm (f₀ _)] at hle
      exact mul_le_mul_of_nonneg_left hle hk0

/-- The Neyman–Pearson step of the Karlin–Rubin theorem: for laws `Pa`, `Pb` with positive
densities whose ratio `fb / fa` is a nondecreasing function of `T`, the threshold test in `T` is
at least as powerful under `Pb` as every test whose size under `Pa` does not exceed its own. -/
theorem integral_le_integral_thresholdTest_of_monotone_likelihood_ratio (μ : Measure X)
    (Pa Pb : Measure X) [IsProbabilityMeasure Pa] [IsProbabilityMeasure Pb] (fa fb : X → ℝ)
    (ha : HasDensity Pa μ fa) (hb : HasDensity Pb μ fb) (hpos : ∀ x, 0 < fa x) (hposb : ∀ x, 0 < fb x)
    (T : X → ℝ) (r : ℝ → ℝ) (hr : Monotone r) (hratio : ∀ x, fb x / fa x = r (T x))
    (c γ : ℝ) (hφ : IsStatisticalTest (thresholdTest T c γ))
    (ψ : X → ℝ) (hψ : IsStatisticalTest ψ)
    (hle : (∫ x, ψ x ∂Pa) ≤ ∫ x, thresholdTest T c γ x ∂Pa) :
    (∫ x, ψ x ∂Pb) ≤ ∫ x, thresholdTest T c γ x ∂Pb := by
  set φ := thresholdTest T c γ
  have hφdef : ∀ x, φ x = if c < T x then 1 else if T x = c then γ else 0 := fun _ ↦ rfl
  have hk : 0 ≤ max (r c) 0 := le_max_right _ _
  have hlt (x : X) : max (r c) 0 * fa x < fb x → c < T x := by
    intro h
    have h1 : max (r c) 0 < r (T x) := by
      rw [← hratio x, lt_div_iff₀ (hpos x)]; exact h
    by_contra hT
    exact absurd (hr (not_lt.1 hT)) (not_le.2 ((le_max_left _ _).trans_lt h1))
  have hgt (x : X) : fb x < max (r c) 0 * fa x → T x < c := by
    intro h
    have h1 : r (T x) < max (r c) 0 := by
      rw [← hratio x, div_lt_iff₀ (hpos x)]; exact h
    have h0 : 0 ≤ r (T x) := by rw [← hratio x]; exact (div_pos (hposb x) (hpos x)).le
    rcases le_total (r c) 0 with h2 | h2
    · rw [max_eq_right h2] at h1; linarith
    · rw [max_eq_left h2] at h1
      by_contra hT
      exact absurd (hr (not_lt.1 hT)) (not_le.2 h1)
  have key := integral_le_of_generalized_neyman_pearson (m := 1) μ fb (fun _ ↦ fa)
    (fun _ ↦ max (r c) 0) hb.integrable (fun _ ↦ ha.integrable) φ ψ hφ hψ
    (ae_of_all _ fun x ↦ ?_) (fun _ ↦ ?_)
  · rw [hb.integral_eq, hb.integral_eq]
    simpa only [mul_comm] using key
  · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simp [hφdef, hlt x h]
    · have := hgt x h
      simp [hφdef, not_lt.2 this.le, this.ne]
  · rw [ha.integral_eq, ha.integral_eq] at hle
    simp only [mul_comm (fa _)] at hle
    exact mul_le_mul_of_nonneg_left hle hk

/-- If `Pa` has an everywhere positive density and `Pb` has a density with respect to the same
measure, then a measurable `g : X → [0, 1]` with `∫ g dPa = 0` also has `∫ g dPb = 0`. -/
theorem integral_eq_zero_of_integral_eq_zero_of_pos_density {μ Pa Pb : Measure X}
    [IsFiniteMeasure Pa] {fa fb : X → ℝ}
    (ha : HasDensity Pa μ fa) (hb : HasDensity Pb μ fb) (hpos : ∀ x, 0 < fa x)
    {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (h0 : (∫ x, g x ∂Pa) = 0) : (∫ x, g x ∂Pb) = 0 := by
  rw [ha.integral_eq] at h0
  rw [hb.integral_eq]
  have hint : Integrable (fun x ↦ fa x * g x) μ := by
    refine ha.integrable.mul_bdd (c := 1) hg.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hg1 x
  have hz := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_nonneg (hpos x).le (hg0 x)) hint).1 h0
  have hg' : g =ᵐ[μ] 0 := hz.mono fun x hx ↦ by
    simpa [(hpos x).ne'] using hx
  rw [integral_congr_ae (hg'.mono fun x hx ↦ by simp [hx] : (fun x ↦ fb x * g x) =ᵐ[μ] 0)]
  simp


/-- The reversed Neyman–Pearson step of the Karlin–Rubin theorem: if the density ratio `fb / fa`
of positive densities is a nondecreasing function of `T`, a threshold test in `T` whose power
under `Pb` is at most that of a test `ψ` also has size at most that of `ψ` under `Pa`. -/
theorem integral_thresholdTest_le_of_monotone_likelihood_ratio (μ : Measure X)
    (Pa Pb : Measure X) [IsProbabilityMeasure Pa] [IsProbabilityMeasure Pb] (fa fb : X → ℝ)
    (ha : HasDensity Pa μ fa) (hb : HasDensity Pb μ fb) (hpos : ∀ x, 0 < fa x)
    (hposb : ∀ x, 0 < fb x)
    (T : X → ℝ) (r : ℝ → ℝ) (hr : Monotone r) (hratio : ∀ x, fb x / fa x = r (T x))
    (c γ : ℝ) (hφ : IsStatisticalTest (thresholdTest T c γ))
    (ψ : X → ℝ) (hψ : IsStatisticalTest ψ)
    (hle : (∫ x, thresholdTest T c γ x ∂Pb) ≤ ∫ x, ψ x ∂Pb) :
    (∫ x, thresholdTest T c γ x ∂Pa) ≤ ∫ x, ψ x ∂Pa := by
  set φ := thresholdTest T c γ
  have hφdef : ∀ x, φ x = if c < T x then 1 else if T x = c then γ else 0 := fun _ ↦ rfl
  have hφ' := hφ.one_sub
  have hψ' := hψ.one_sub
  by_cases hrc : 0 < r c
  · have key := integral_le_of_generalized_neyman_pearson (m := 1) μ fa (fun _ ↦ fb)
      (fun _ ↦ (r c)⁻¹) ha.integrable (fun _ ↦ hb.integrable) (fun x ↦ 1 - φ x)
      (fun x ↦ 1 - ψ x) hφ' hψ' (ae_of_all _ fun x ↦ ?_) (fun _ ↦ ?_)
    · have e : ∀ (P : Measure X) (f : X → ℝ), HasDensity P μ f → ∀ χ : X → ℝ,
          (∫ x, χ x * f x ∂μ) = ∫ x, χ x ∂P := by
        intro P f hP χ
        rw [hP.integral_eq]
        exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)
      rw [e Pa fa ha (fun x ↦ 1 - ψ x), e Pa fa ha (fun x ↦ 1 - φ x),
        hψ.integral_one_sub Pa,
        hφ.integral_one_sub Pa] at key
      linarith
    · simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have h1 : fb x < r c * fa x := by
          have := mul_lt_mul_of_pos_left h hrc
          rwa [← mul_assoc, mul_inv_cancel₀ hrc.ne', one_mul] at this
        have h2 : r (T x) < r c := by
          rw [← hratio x, div_lt_iff₀ (hpos x)]; exact h1
        have hT : T x < c := by
          by_contra hT
          exact absurd (hr (not_lt.1 hT)) (not_le.2 h2)
        simp [hφdef, not_lt.2 hT.le, hT.ne]
      · have h1 : r c * fa x < fb x := by
          have := mul_lt_mul_of_pos_left h hrc
          rwa [← mul_assoc, mul_inv_cancel₀ hrc.ne', one_mul] at this
        have h2 : r c < r (T x) := by
          rw [← hratio x, lt_div_iff₀ (hpos x)]; exact h1
        have hT : c < T x := by
          by_contra hT
          exact absurd (hr (not_lt.1 hT)) (not_le.2 h2)
        simp [hφdef, hT]
    · have e : ∀ χ : X → ℝ, IsStatisticalTest χ →
          (∫ x, (1 - χ x) * fb x ∂μ) = 1 - ∫ x, χ x ∂Pb := by
        intro χ hχ
        rw [← hχ.integral_one_sub Pb, hb.integral_eq]
        exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)
      rw [e ψ hψ, e φ hφ]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hrc.le)
  · -- every observation exceeds the threshold, so the threshold test is identically one
    have hall : ∀ x, c < T x := by
      intro x
      by_contra hT
      have h1 := hr (not_lt.1 hT)
      rw [← hratio x] at h1
      exact hrc (lt_of_lt_of_le (div_pos (hposb x) (hpos x)) h1)
    have hφ1 : ∀ x, φ x = 1 := fun x ↦ by simp [hφdef, hall x]
    simp only [hφ1, integral_const, probReal_univ, smul_eq_mul, mul_one] at hle ⊢
    have h0 : (∫ x, (1 - ψ x) ∂Pb) = 0 := by
      rw [hψ.integral_one_sub Pb]
      linarith [hψ.integral_le_one Pb]
    have := integral_eq_zero_of_integral_eq_zero_of_pos_density hb ha hposb hψ'.1
      (fun x ↦ (hψ'.2 x).1) (fun x ↦ (hψ'.2 x).2) h0
    rw [hψ.integral_one_sub Pa] at this
    linarith


/-- The size `P {c < T} + γ P {T = c}` of a threshold test in a real statistic. -/
theorem integral_thresholdTest (P : Measure X) [IsProbabilityMeasure P] {T : X → ℝ}
    (hT : Measurable T) (c γ : ℝ) :
    (∫ x, thresholdTest T c γ x ∂P) = P.real {x | c < T x} + γ * P.real {x | T x = c} := by
  unfold thresholdTest
  have hm1 : MeasurableSet {x | c < T x} := measurableSet_lt measurable_const hT
  have hm2 : MeasurableSet {x | T x = c} := measurableSet_eq_fun hT measurable_const
  have hpt : (fun x ↦ if c < T x then (1 : ℝ) else if T x = c then γ else 0) =
      fun x ↦ {x | c < T x}.indicator (fun _ ↦ (1 : ℝ)) x +
        {x | T x = c}.indicator (fun _ ↦ γ) x := by
    funext x
    by_cases h1 : c < T x
    · have h2 : T x ≠ c := h1.ne'
      simp [indicator, h1, h2]
    · by_cases h2 : T x = c
      · simp [indicator, h2]
      · simp [indicator, h1, h2]
  rw [hpt, integral_add ((integrable_const _).indicator hm1) ((integrable_const _).indicator hm2),
    integral_indicator_const _ hm1, integral_indicator_const _ hm2]
  simp [mul_comm]

/-- Every size `β ∈ (0, 1)` is attained by a threshold test in a real statistic `T`, with the
threshold the `(1 - β)`-quantile of the law of `T` (TauCeti's `Measure.quantile`). -/
theorem exists_integral_thresholdTest_eq (P : Measure X) [IsProbabilityMeasure P] {T : X → ℝ}
    (hT : Measurable T) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∃ c γ : ℝ, γ ∈ Icc 0 1 ∧ (∫ x, thresholdTest T c γ x ∂P) = β := by
  set ν := P.map T
  have h0 : 0 < 1 - β := by linarith [hβ.2]
  have h1 : 1 - β < 1 := by linarith [hβ.1]
  set c := ν.quantile (1 - β)
  have hlt := ν.measureReal_Iio_quantile_le h0 h1
  have hle := ν.le_cdf_quantile h1
  rw [ProbabilityTheory.cdf_eq_real] at hle
  rw [map_measureReal_apply hT measurableSet_Iio] at hlt
  rw [map_measureReal_apply hT measurableSet_Iic] at hle
  change P.real {x | T x < c} ≤ 1 - β at hlt
  change 1 - β ≤ P.real {x | T x ≤ c} at hle
  have hm1 : MeasurableSet {x | T x ≤ c} := measurableSet_le hT measurable_const
  have hgt : P.real {x | c < T x} = 1 - P.real {x | T x ≤ c} := by
    rw [← probReal_compl_eq_one_sub hm1]
    congr 1
    ext x; simp
  have heq : P.real {x | T x = c} = P.real {x | T x ≤ c} - P.real {x | T x < c} := by
    have hdisj : {x | T x ≤ c} = {x | T x < c} ∪ {x | T x = c} := by
      ext x; simp [le_iff_lt_or_eq]
    rw [hdisj, measureReal_union _ (measurableSet_eq_fun hT measurable_const)]
    · ring
    · exact Set.disjoint_left.2 fun x hx hx' ↦ (ne_of_lt hx) hx'
  set pg := P.real {x | c < T x}
  set pe := P.real {x | T x = c}
  have hA : pg ≤ β := by linarith
  have hB : β ≤ pg + pe := by linarith
  by_cases hpe : pe = 0
  · refine ⟨c, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [integral_thresholdTest P hT]
    simp only [zero_mul, add_zero]
    rw [hpe] at hB
    linarith
  · have hpe0 : 0 < pe := lt_of_le_of_ne measureReal_nonneg (Ne.symm hpe)
    refine ⟨c, (β - pg) / pe, ⟨div_nonneg (by linarith) hpe0.le, ?_⟩, ?_⟩
    · rw [div_le_one hpe0]; linarith
    · rw [integral_thresholdTest P hT]
      field_simp
      ring

end CKSD
