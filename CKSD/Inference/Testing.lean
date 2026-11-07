module

public import CKSD.Inference.Density
public import CKSD.Inference.InvariantTesting

/-!
# Inference: Testing

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.14: existence and optimality of a Neyman–Pearson test. The almost-everywhere
uniqueness of most powerful tests is not included. -/
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

/-- The Neyman–Pearson step of the Karlin–Rubin theorem: for two laws with positive densities whose
ratio is a nondecreasing function of `T`, the one-sided test in `T` is at least as powerful under
the second law as every test whose size under the first law does not exceed its own. -/
theorem integral_le_integral_threshold_test_of_monotone_likelihood_ratio (μ : Measure X)
    (Pa Pb : Measure X) [IsProbabilityMeasure Pa] [IsProbabilityMeasure Pb] (fa fb : X → ℝ)
    (ha : HasDensity Pa μ fa) (hb : HasDensity Pb μ fb) (hpos : ∀ x, 0 < fa x) (hposb : ∀ x, 0 < fb x)
    (T : X → ℝ) (r : ℝ → ℝ) (hr : Monotone r) (hratio : ∀ x, fb x / fa x = r (T x))
    (c γ : ℝ) (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (hφdef : ∀ x, φ x = if c < T x then 1 else if T x = c then γ else 0)
    (ψ : X → ℝ) (hψ : IsStatisticalTest ψ) (hle : (∫ x, ψ x ∂Pa) ≤ ∫ x, φ x ∂Pa) :
    (∫ x, ψ x ∂Pb) ≤ ∫ x, φ x ∂Pb := by
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

/-- GAPS 101.15: Karlin–Rubin for strictly positive densities on a common support.
This scope avoids the convention for ratios with zero denominator. The monotonicity of the power
function is not included. -/
theorem isUniformlyMostPowerfulTest_of_monotone_likelihood_ratio (P : ℝ → Measure X) (μ : Measure X)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : ℝ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (hpos : ∀ θ x, 0 < f θ x)
    (T : X → ℝ) (hT : Measurable T)
    (hmlr : ∀ a b, a < b → ∃ r : ℝ → ℝ, Monotone r ∧
      ∀ x, f b x / f a x = r (T x))
    (θ₀ c γ α : ℝ) (hγ : γ ∈ Icc 0 1) (_hα : α ∈ Ioo 0 1)
    (hsize : (∫ x, (if c < T x then 1 else if T x = c then γ else 0) ∂P θ₀) = α) :
    IsUniformlyMostPowerfulTest P (Iic θ₀) (Ioi θ₀) α
      (fun x ↦ if c < T x then 1 else if T x = c then γ else 0) := by
  set φ : X → ℝ := fun x ↦ if c < T x then 1 else if T x = c then γ else 0 with hφdef
  have hφ : IsStatisticalTest φ := by
    refine ⟨Measurable.ite (measurableSet_lt measurable_const hT) measurable_const
      (Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
        measurable_const), fun x ↦ ?_⟩
    simp only [φ]
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hγ
    · exact ⟨le_rfl, zero_le_one⟩
  have step (a b : ℝ) (hab : a < b) (ψ : X → ℝ) (hψ : IsStatisticalTest ψ)
      (hle : (∫ x, ψ x ∂P a) ≤ ∫ x, φ x ∂P a) : (∫ x, ψ x ∂P b) ≤ ∫ x, φ x ∂P b := by
    obtain ⟨r, hr, hratio⟩ := hmlr a b hab
    have := hP a
    have := hP b
    exact integral_le_integral_threshold_test_of_monotone_likelihood_ratio μ (P a) (P b) (f a)
      (f b) (hf a) (hf b) (hpos a) (hpos b) T r hr hratio c γ φ hφ (fun _ ↦ rfl) ψ hψ hle
  refine ⟨hφ, fun θ hθ ↦ ?_, fun ψ hψ hlevel θ hθ ↦ ?_⟩
  · rcases (mem_Iic.1 hθ).lt_or_eq with hlt | rfl
    · have := hP θ
      set β := ∫ x, φ x ∂P θ
      have hβ : β ∈ Icc (0 : ℝ) 1 := by
        refine ⟨integral_nonneg fun x ↦ (hφ.2 x).1, ?_⟩
        calc β ≤ ∫ _x, (1 : ℝ) ∂P θ := integral_mono
              (integrable_of_measurable_of_abs_le _ hφ.1 fun x ↦
                abs_le.2 ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩)
              (integrable_const 1) fun x ↦ (hφ.2 x).2
          _ = 1 := by simp
      have h := step θ θ₀ hlt (fun _ ↦ β) ⟨measurable_const, fun _ ↦ hβ⟩ (by simp [β])
      have := hP θ₀
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
      rw [← hsize]
      exact h
    · exact hsize.le
  · exact step θ₀ θ hθ ψ hψ ((hlevel θ₀ (mem_Iic.2 le_rfl)).trans hsize.symm.le)

/-- GAPS 101.17: chi-squared residual law and independence from the sample mean. -/
theorem gaussian_sample_mean_residual_laws (n : ℕ) (hn : 2 ≤ n) (m : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    let P := Measure.pi (fun _ : Fin n ↦ gaussianReal m v);
    let mean := fun x : Fin n → ℝ ↦ (∑ i, x i) / n;
    let ss := fun x : Fin n → ℝ ↦ ∑ i, (x i - mean x) ^ 2;
    P.map (fun x ↦ ss x / v) = TauCeti.Probability.chiSquaredMeasure (n - 1 : ℕ) ∧
      IndepFun mean ss P ∧
      P.map (fun x ↦ Real.sqrt n * (mean x - m) /
        Real.sqrt (ss x / (n - 1 : ℕ))) = TauCeti.Probability.studentTMeasure (n - 1 : ℕ) := by
  sorry


end CKSD
