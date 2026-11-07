module

public import CKSD.Asymptotics.Statistics

/-!
# Rate of convergence of M-estimators

The rate theorem for approximate maximizers of random criterion functions on a pseudometric
parameter space, with the modulus of continuity of the centred criterion process controlled by
an outer expectation (`outerExpectation`). Probabilities of events defined by the estimator are
outer probabilities, since `Measure` applied to an arbitrary set is the outer measure; no
measurability of the estimator or of the suprema is assumed. Source: GAPS 102.25.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Local modulus of the centred criterion process `Mₙ - M` on the ball of radius `δ` about
`θ₀`, as a nonnegative extended-real random quantity. -/
def centredCriterionModulus {Ω Θ : Type*} [PseudoMetricSpace Θ] (M : Θ → ℝ)
    (Mn : Ω → Θ → ℝ) (θ₀ : Θ) (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (θ : Θ) (_ : dist θ θ₀ < δ),
    ENNReal.ofReal |(Mn ω θ - M θ) - (Mn ω θ₀ - M θ₀)|

/-- Markov's inequality for outer expectations: a set on which `f ≥ t` has outer measure at
most `E* f / t`. -/
theorem measure_le_outerExpectation_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (A : Set Ω) {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ∞)
    (h : ∀ ω ∈ A, t ≤ f ω) : μ A ≤ outerExpectation μ f / t := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht')]
  unfold outerExpectation
  refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
  calc μ A * t = t * μ A := mul_comm _ _
    _ ≤ t * μ {ω | t ≤ g ω} := by
        gcongr
        intro ω hω
        exact (h ω hω).trans (hfg ω)
    _ ≤ ∫⁻ ω, g ω ∂μ := mul_meas_ge_le_lintegral₀ hg.aemeasurable t

/-- GAPS 102.25: the rate theorem for `M`-estimators. Suppose the deterministic criterion has
quadratic separation `M θ - M θ₀ ≤ -c d(θ,θ₀)²` near `θ₀`, and that for every `n ≥ 1` and all
`δ` in a fixed interval `(0, δ₀)`, the outer expectation of the local modulus of `Mₙ - M` is at
most `C φₙ(δ)/√n` with a constant `C ≥ 0`, where `δ ↦ φₙ(δ)/δ^a` is decreasing on `(0,∞)` for
a fixed `a < 2`. If `rₙ² φₙ(1/rₙ) ≤ √n`, the estimator maximizes `Mₙ` up to `O_P(rₙ⁻²)`, and it
is consistent in outer probability, then `rₙ d(Tₙ, θ₀) = O_P(1)`. -/
theorem isBoundedInProbability_rate_m_estimator {Ω Θ : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Θ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Θ → ℝ) (Mn : ℕ → Ω → Θ → ℝ) (θ₀ : Θ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hcurv : ∀ θ, dist θ θ₀ < η → M θ - M θ₀ ≤ -(c * dist θ θ₀ ^ 2))
    (φ : ℕ → ℝ → ℝ) (a : ℝ) (ha : a < 2)
    (hφ : ∀ n, AntitoneOn (fun δ ↦ φ n δ / δ ^ a) (Ioi 0))
    (C δ₀ : ℝ) (hC : 0 ≤ C) (hδ₀ : 0 < δ₀)
    (hmod : ∀ n : ℕ, 1 ≤ n → ∀ δ, 0 < δ → δ < δ₀ →
      outerExpectation μ (centredCriterionModulus M (Mn n) θ₀ δ) ≤
        ENNReal.ofReal (C * φ n δ / Real.sqrt n))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrate : ∀ n : ℕ, 1 ≤ n → r n ^ 2 * φ n (1 / r n) ≤ Real.sqrt n)
    (T : ℕ → Ω → Θ) (R : ℕ → Ω → ℝ)
    (hR : IsBoundedInProbability μ (fun n ω ↦ r n ^ 2 * R n ω))
    (hopt : ∀ n ω, Mn n ω θ₀ - R n ω ≤ Mn n ω (T n ω))
    (hcons : TendstoInProbabilityConst μ T θ₀) :
    IsBoundedInProbability μ (fun n ω ↦ r n * dist (T n ω) θ₀) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨K, hK, hKev⟩ := hR (ε / 3) hε3
  set η' : ℝ := min η δ₀ / 4 with hη'
  have hη'pos : 0 < η' := by positivity
  have hη'η : η' < η := by
    have := min_le_left η δ₀; rw [hη']; linarith
  have hη'δ : 2 * η' < δ₀ := by
    have := min_le_right η δ₀; rw [hη']; linarith
  set ρ : ℝ := (2 : ℝ) ^ a / 4 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by norm_num)]
    calc (2 : ℝ) ^ a < 2 ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ha
      _ = 4 := by norm_num
  set b : ℝ := 2 * 2 ^ a * |C| / c with hb
  have hb0 : 0 ≤ b := by positivity
  have htail : Tendsto (fun N : ℕ ↦ b * ρ ^ N / (1 - ρ)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul b).div_const (1 - ρ)
  have h4 : Tendsto (fun N : ℕ ↦ c * (4 : ℝ) ^ N) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).const_mul_atTop hc
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, b * ρ ^ N / (1 - ρ) ≤ ε / 3 ∧ 2 * K ≤ c * 4 ^ N :=
    ((htail.eventually (eventually_le_nhds hε3)).and (h4.eventually_ge_atTop (2 * K))).exists
  refine ⟨2 ^ N, by positivity, ?_⟩
  filter_upwards [hKev, (hcons η' hη'pos).eventually (eventually_le_nhds hε3),
    eventually_ge_atTop 1] with n hKn hcn hn1
  have hrn := hr n
  set Ak : ℕ → Set Ω := fun k ↦ {ω | (2 : ℝ) ^ (k + 1) / r n < δ₀ ∧
    ENNReal.ofReal (c * 4 ^ k / (2 * r n ^ 2)) ≤
      centredCriterionModulus M (Mn n) θ₀ ((2 : ℝ) ^ (k + 1) / r n) ω} with hAk
  have hsub : {ω | (2 : ℝ) ^ N < |r n * dist (T n ω) θ₀|} ⊆
      {ω | K < |r n ^ 2 * R n ω|} ∪ {ω | η' < dist (T n ω) θ₀} ∪ ⋃ j, Ak (j + N) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_ofPred_eq, not_lt] at hcon hω
    obtain ⟨⟨hRK, hdη⟩, hA⟩ := hcon
    set d := dist (T n ω) θ₀ with hd
    have hd0 : 0 ≤ d := dist_nonneg
    rw [abs_of_nonneg (by positivity)] at hω
    have h1 : (1 : ℝ) ≤ r n * d := le_trans (one_le_pow₀ (by norm_num)) hω.le
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near h1 (show (1 : ℝ) < 2 by norm_num)
    have hkN : N ≤ k := by
      by_contra hlt
      push Not at hlt
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hlt
      linarith
    obtain ⟨j, rfl⟩ : ∃ j, k = j + N := ⟨k - N, by omega⟩
    have hdδ : d < (2 : ℝ) ^ (j + N + 1) / r n := by
      rw [lt_div_iff₀ hrn, mul_comm]; exact hk2
    have hδ0 : (2 : ℝ) ^ (j + N + 1) / r n < δ₀ := by
      rw [div_lt_iff₀ hrn]
      have : (2 : ℝ) ^ (j + N + 1) ≤ 2 * (r n * d) := by rw [pow_succ]; linarith
      nlinarith
    refine hA j ⟨hδ0, ?_⟩
    have hcurv' := hcurv (T n ω) (lt_of_le_of_lt hdη hη'η)
    have hoptω := hopt n ω
    have hRle : R n ω ≤ K / r n ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact (le_abs_self _).trans hRK
    have hd2 : (4 : ℝ) ^ (j + N) / r n ^ 2 ≤ d ^ 2 := by
      rw [div_le_iff₀ (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
        mul_comm 2, pow_mul]
      calc ((2 : ℝ) ^ (j + N)) ^ 2 ≤ (r n * d) ^ 2 := pow_le_pow_left₀ (by positivity) hk1 2
        _ = d ^ 2 * r n ^ 2 := by ring
    have h4N : (4 : ℝ) ^ N ≤ 4 ^ (j + N) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hval : c * 4 ^ (j + N) / (2 * r n ^ 2) ≤
        |(Mn n ω (T n ω) - M (T n ω)) - (Mn n ω θ₀ - M θ₀)| := by
      refine le_trans ?_ (le_abs_self _)
      have hcd : c * ((4 : ℝ) ^ (j + N) / r n ^ 2) ≤ c * d ^ 2 :=
        mul_le_mul_of_nonneg_left hd2 hc.le
      have hK' : K / r n ^ 2 ≤ c * 4 ^ (j + N) / (2 * r n ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2K : 2 * K ≤ c * 4 ^ (j + N) := hN2.trans (mul_le_mul_of_nonneg_left h4N hc.le)
        have := mul_le_mul_of_nonneg_right h2K (pow_pos hrn 2).le
        linarith
      have : c * 4 ^ (j + N) / (2 * r n ^ 2) = c * ((4 : ℝ) ^ (j + N) / r n ^ 2) -
          c * 4 ^ (j + N) / (2 * r n ^ 2) := by field_simp; ring
      linarith
    calc ENNReal.ofReal (c * 4 ^ (j + N) / (2 * r n ^ 2))
        ≤ ENNReal.ofReal |(Mn n ω (T n ω) - M (T n ω)) - (Mn n ω θ₀ - M θ₀)| :=
          ENNReal.ofReal_le_ofReal hval
      _ ≤ centredCriterionModulus M (Mn n) θ₀ ((2 : ℝ) ^ (j + N + 1) / r n) ω :=
          le_iSup₂ (f := fun θ (_ : dist θ θ₀ < (2 : ℝ) ^ (j + N + 1) / r n) ↦
            ENNReal.ofReal |(Mn n ω θ - M θ) - (Mn n ω θ₀ - M θ₀)|) (T n ω) hdδ
  have hAkb : ∀ j, μ (Ak (j + N)) ≤ ENNReal.ofReal (b * ρ ^ (j + N)) := by
    intro j
    set k := j + N
    set δk : ℝ := (2 : ℝ) ^ (k + 1) / r n with hδk
    by_cases hδ : δk < δ₀
    swap
    · have : Ak k = ∅ := by
        ext ω; simp only [hAk, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h ↦ absurd h hδ
      rw [this, measure_empty]; exact zero_le
    have ht : 0 < c * 4 ^ k / (2 * r n ^ 2) := by positivity
    have hδpos : 0 < δk := by positivity
    refine (measure_le_outerExpectation_div μ _ (Ak k) (ENNReal.ofReal_pos.2 ht).ne'
      ENNReal.ofReal_ne_top (fun ω hω ↦ hω.2)).trans ?_
    refine (ENNReal.div_le_div_right (hmod n hn1 δk hδpos hδ) _).trans ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- scaling of `φ` between `1 / r n` and `δk`
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    have hrδ : r n * δk = 2 ^ (k + 1) := by rw [hδk]; field_simp
    have hle : 1 / r n ≤ δk := by
      rw [hδk, div_le_div_iff_of_pos_right hrn]
      exact one_le_pow₀ (by norm_num)
    have hanti : φ n δk / δk ^ a ≤ φ n (1 / r n) / (1 / r n) ^ a :=
      hφ n (show (0 : ℝ) < 1 / r n by positivity) hδpos hle
    have hF : (δk / (1 / r n)) ^ a = ((2 : ℝ) ^ a) ^ (k + 1) := by
      have : δk / (1 / r n) = (2 : ℝ) ^ (k + 1) := by rw [← hrδ]; field_simp
      rw [this, ← Real.rpow_pow_comm (by norm_num)]
    have hscale : φ n δk ≤ φ n (1 / r n) * ((2 : ℝ) ^ a) ^ (k + 1) := by
      rw [← hF, Real.div_rpow hδpos.le (by positivity)]
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hδpos a)
        (Real.rpow_pos_of_pos (by positivity) a)] at hanti
      have hpos1 : 0 < (1 / r n) ^ a := Real.rpow_pos_of_pos (by positivity) a
      rw [mul_div_assoc', le_div_iff₀ hpos1]
      linarith
    have hF0 : 0 ≤ ((2 : ℝ) ^ a) ^ (k + 1) := by positivity
    have hφmax : max (φ n δk) 0 ≤ ((2 : ℝ) ^ a) ^ (k + 1) * (Real.sqrt n / r n ^ 2) := by
      have h1 : φ n (1 / r n) ≤ Real.sqrt n / r n ^ 2 := by
        rw [le_div_iff₀ (by positivity), mul_comm]; exact hrate n hn1
      refine max_le ?_ (by positivity)
      calc φ n δk ≤ φ n (1 / r n) * ((2 : ℝ) ^ a) ^ (k + 1) := hscale
        _ ≤ Real.sqrt n / r n ^ 2 * ((2 : ℝ) ^ a) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right h1 hF0
        _ = _ := mul_comm _ _
    have hCφ : C * φ n δk ≤ |C| * (((2 : ℝ) ^ a) ^ (k + 1) * (Real.sqrt n / r n ^ 2)) :=
      calc C * φ n δk ≤ |C| * max (φ n δk) 0 := by
            rw [abs_of_nonneg hC]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC
        _ ≤ _ := mul_le_mul_of_nonneg_left hφmax (abs_nonneg C)
    rw [div_le_iff₀ hsn]
    calc C * φ n δk ≤ |C| * (((2 : ℝ) ^ a) ^ (k + 1) * (Real.sqrt n / r n ^ 2)) := hCφ
      _ = b * ρ ^ k * (c * 4 ^ k / (2 * r n ^ 2)) * Real.sqrt n := by
          rw [hb, hρ, div_pow, pow_succ]
          field_simp
  have hU : μ.real (⋃ j, Ak (j + N)) ≤ b * ρ ^ N / (1 - ρ) := by
    have hsum : Summable fun j : ℕ ↦ b * ρ ^ (j + N) := by
      simp_rw [pow_add]
      exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_right _).mul_left _
    have htsum : ∑' j : ℕ, b * ρ ^ (j + N) = b * ρ ^ N / (1 - ρ) := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1]
      ring
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc μ (⋃ j, Ak (j + N)) ≤ ∑' j, μ (Ak (j + N)) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (b * ρ ^ (j + N)) := tsum_le_tsum hAkb
      _ = ENNReal.ofReal (∑' j : ℕ, b * ρ ^ (j + N)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hsum).symm
      _ = ENNReal.ofReal (b * ρ ^ N / (1 - ρ)) := by rw [htsum]
  calc μ.real {ω | (2 : ℝ) ^ N < |r n * dist (T n ω) θ₀|}
      ≤ μ.real ({ω | K < |r n ^ 2 * R n ω|} ∪ {ω | η' < dist (T n ω) θ₀} ∪ ⋃ j, Ak (j + N)) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | K < |r n ^ 2 * R n ω|} + μ.real {ω | η' < dist (T n ω) θ₀} +
        μ.real (⋃ j, Ak (j + N)) :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr; linarith
    _ = ε := by ring


end CKSD
