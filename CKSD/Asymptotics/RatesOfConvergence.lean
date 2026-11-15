module

public import CKSD.Asymptotics.Basic

/-!
# Rate of convergence of M-estimators

The rate theorem for approximate maximizers of random criterion functions on a pseudometric
parameter space, with the modulus of continuity of the centred criterion process controlled by
an outer expectation (`outerExpectation`). Probabilities of events defined by the estimator are
outer probabilities, since `Measure` applied to an arbitrary set is the outer measure; no
measurability of the estimator or of the suprema is assumed. Source: GAPS 102.25.
-/

public section

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
  rw [outerExpectation_def]
  refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
  calc μ A * t = t * μ A := mul_comm _ _
    _ ≤ t * μ {ω | t ≤ g ω} := by
        gcongr
        intro ω hω
        exact (h ω hω).trans (hfg ω)
    _ ≤ ∫⁻ ω, g ω ∂μ := mul_meas_ge_le_lintegral₀ hg.aemeasurable t

/-- **Peeling step of the rate theorem.** Let `t` satisfy the quadratic separation
`M t - M θ₀ ≤ -c d(t, θ₀)²`, maximize `Mₙ(ω, ·)` up to `R ≤ K / r²` with `2K ≤ c 4^N`, and
satisfy `2^N < r d(t, θ₀)` and `2 d(t, θ₀) < δ₀`. Then for some shell index `j` the radius
`2^{j+N+1} / r` is below `δ₀` and the local modulus at that radius is at least
`c 4^{j+N} / (2 r²)`. -/
theorem exists_le_centredCriterionModulus_of_lt_mul_dist {Ω Θ : Type*} [PseudoMetricSpace Θ]
    (M : Θ → ℝ) (Mn : Ω → Θ → ℝ) (θ₀ : Θ) (ω : Ω) {t : Θ} {c r R K δ₀ : ℝ} {N : ℕ}
    (hc : 0 < c) (hr : 0 < r) (hcurv : M t - M θ₀ ≤ -(c * dist t θ₀ ^ 2))
    (hopt : Mn ω θ₀ - R ≤ Mn ω t) (hRK : R ≤ K / r ^ 2) (hN : 2 * K ≤ c * 4 ^ N)
    (hω : (2 : ℝ) ^ N < r * dist t θ₀) (hδ₀ : 2 * dist t θ₀ < δ₀) :
    ∃ j : ℕ, (2 : ℝ) ^ (j + N + 1) / r < δ₀ ∧
      ENNReal.ofReal (c * 4 ^ (j + N) / (2 * r ^ 2)) ≤
        centredCriterionModulus M Mn θ₀ ((2 : ℝ) ^ (j + N + 1) / r) ω := by
  set d := dist t θ₀ with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have h1 : (1 : ℝ) ≤ r * d := le_trans (one_le_pow₀ (by norm_num)) hω.le
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near h1 (show (1 : ℝ) < 2 by norm_num)
  have hkN : N ≤ k := by
    by_contra hlt
    push Not at hlt
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hlt
    linarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + N := ⟨k - N, by omega⟩
  have hdδ : d < (2 : ℝ) ^ (j + N + 1) / r := by
    rw [lt_div_iff₀ hr, mul_comm]; exact hk2
  have hδ0 : (2 : ℝ) ^ (j + N + 1) / r < δ₀ := by
    rw [div_lt_iff₀ hr]
    have : (2 : ℝ) ^ (j + N + 1) ≤ 2 * (r * d) := by rw [pow_succ]; linarith
    nlinarith
  refine ⟨j, hδ0, ?_⟩
  have hd2 : (4 : ℝ) ^ (j + N) / r ^ 2 ≤ d ^ 2 := by
    rw [div_le_iff₀ (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      mul_comm 2, pow_mul]
    calc ((2 : ℝ) ^ (j + N)) ^ 2 ≤ (r * d) ^ 2 := pow_le_pow_left₀ (by positivity) hk1 2
      _ = d ^ 2 * r ^ 2 := by ring
  have h4N : (4 : ℝ) ^ N ≤ 4 ^ (j + N) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hval : c * 4 ^ (j + N) / (2 * r ^ 2) ≤
      |(Mn ω t - M t) - (Mn ω θ₀ - M θ₀)| := by
    refine le_trans ?_ (le_abs_self _)
    have hcd : c * ((4 : ℝ) ^ (j + N) / r ^ 2) ≤ c * d ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 hc.le
    have hK' : K / r ^ 2 ≤ c * 4 ^ (j + N) / (2 * r ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2K : 2 * K ≤ c * 4 ^ (j + N) := hN.trans (mul_le_mul_of_nonneg_left h4N hc.le)
      have := mul_le_mul_of_nonneg_right h2K (pow_pos hr 2).le
      linarith
    have : c * 4 ^ (j + N) / (2 * r ^ 2) = c * ((4 : ℝ) ^ (j + N) / r ^ 2) -
        c * 4 ^ (j + N) / (2 * r ^ 2) := by field_simp; ring
    linarith
  calc ENNReal.ofReal (c * 4 ^ (j + N) / (2 * r ^ 2))
      ≤ ENNReal.ofReal |(Mn ω t - M t) - (Mn ω θ₀ - M θ₀)| :=
        ENNReal.ofReal_le_ofReal hval
    _ ≤ centredCriterionModulus M Mn θ₀ ((2 : ℝ) ^ (j + N + 1) / r) ω :=
        le_iSup₂ (f := fun θ (_ : dist θ θ₀ < (2 : ℝ) ^ (j + N + 1) / r) ↦
          ENNReal.ofReal |(Mn ω θ - M θ) - (Mn ω θ₀ - M θ₀)|) t hdδ

/-- **Scaling step of the rate theorem.** If `δ ↦ φ(δ) / δ^a` is decreasing on `(0, ∞)` and
`r² φ(1/r) ≤ s`, then at the dyadic radius `δ = 2^{k+1} / r`,
`C φ(δ) ≤ b ρ^k · (c 4^k / (2 r²)) · s` with `b = 2 · 2^a |C| / c` and `ρ = 2^a / 4`. -/
theorem mul_le_of_antitoneOn_div_rpow {φ : ℝ → ℝ} {a : ℝ}
    (hφ : AntitoneOn (fun δ ↦ φ δ / δ ^ a) (Ioi 0)) {C c r s : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hr : 0 < r) (hs : 0 < s) (hrate : r ^ 2 * φ (1 / r) ≤ s) (k : ℕ) :
    C * φ ((2 : ℝ) ^ (k + 1) / r) ≤
      2 * 2 ^ a * |C| / c * ((2 : ℝ) ^ a / 4) ^ k * (c * 4 ^ k / (2 * r ^ 2)) * s := by
  set δk : ℝ := (2 : ℝ) ^ (k + 1) / r with hδk
  have hδpos : 0 < δk := by positivity
  have hrδ : r * δk = 2 ^ (k + 1) := by rw [hδk]; field_simp
  have hle : 1 / r ≤ δk := by
    rw [hδk, div_le_div_iff_of_pos_right hr]
    exact one_le_pow₀ (by norm_num)
  have hanti : φ δk / δk ^ a ≤ φ (1 / r) / (1 / r) ^ a :=
    hφ (show (0 : ℝ) < 1 / r by positivity) hδpos hle
  have hF : (δk / (1 / r)) ^ a = ((2 : ℝ) ^ a) ^ (k + 1) := by
    have : δk / (1 / r) = (2 : ℝ) ^ (k + 1) := by rw [← hrδ]; field_simp
    rw [this, ← Real.rpow_pow_comm (by norm_num)]
  have hscale : φ δk ≤ φ (1 / r) * ((2 : ℝ) ^ a) ^ (k + 1) := by
    rw [← hF, Real.div_rpow hδpos.le (by positivity)]
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hδpos a)
      (Real.rpow_pos_of_pos (by positivity) a)] at hanti
    have hpos1 : 0 < (1 / r) ^ a := Real.rpow_pos_of_pos (by positivity) a
    rw [mul_div_assoc', le_div_iff₀ hpos1]
    linarith
  have hF0 : 0 ≤ ((2 : ℝ) ^ a) ^ (k + 1) := by positivity
  have hφmax : max (φ δk) 0 ≤ ((2 : ℝ) ^ a) ^ (k + 1) * (s / r ^ 2) := by
    have h1 : φ (1 / r) ≤ s / r ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hrate
    refine max_le ?_ (by positivity)
    calc φ δk ≤ φ (1 / r) * ((2 : ℝ) ^ a) ^ (k + 1) := hscale
      _ ≤ s / r ^ 2 * ((2 : ℝ) ^ a) ^ (k + 1) := mul_le_mul_of_nonneg_right h1 hF0
      _ = _ := mul_comm _ _
  calc C * φ δk ≤ |C| * max (φ δk) 0 := by
        rw [abs_of_nonneg hC]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC
    _ ≤ |C| * (((2 : ℝ) ^ a) ^ (k + 1) * (s / r ^ 2)) :=
        mul_le_mul_of_nonneg_left hφmax (abs_nonneg C)
    _ = _ := by
        rw [div_pow, pow_succ]
        field_simp

/-- GAPS 102.25: the rate theorem for `M`-estimators. Suppose the deterministic criterion has
quadratic separation `M θ - M θ₀ ≤ -c d(θ,θ₀)²` near `θ₀`, and that for every `n ≥ 1` and all
`δ` in a fixed interval `(0, δ₀)`, the outer expectation of the local modulus of `Mₙ - M` is at
most `C φₙ(δ) / √n` with a constant `C ≥ 0`, where `δ ↦ φₙ(δ) / δ^a` is decreasing on `(0,∞)` for
a fixed `a < 2`. If `rₙ² φₙ(1/rₙ) ≤ √n`, the estimator maximizes `Mₙ` up to `O_P(rₙ⁻²)`, and it
is consistent in outer probability, then `rₙ d(Tₙ, θ₀) = O_P(1)`. -/
theorem isBoundedInProbability_rate_mEstimator {Ω Θ : Type*} [MeasurableSpace Ω]
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
    (hcons : TendstoInMeasure μ T atTop (fun _ ↦ θ₀)) :
    IsBoundedInProbability μ (fun n ω ↦ r n * dist (T n ω) θ₀) := by
  rw [tendstoInMeasure_iff_measureReal_lt_dist] at hcons
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
    rw [abs_of_nonneg (by positivity)] at hω
    have hRle : R n ω ≤ K / r n ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact (le_abs_self _).trans hRK
    obtain ⟨j, hj⟩ := exists_le_centredCriterionModulus_of_lt_mul_dist M (Mn n) θ₀ ω hc hrn
      (hcurv (T n ω) (lt_of_le_of_lt hdη hη'η)) (hopt n ω) hRle hN2 hω
      (δ₀ := δ₀) (by linarith)
    exact hA j hj
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
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hn1))]
    exact mul_le_of_antitoneOn_div_rpow (hφ n) hC hc hrn
      (Real.sqrt_pos.2 (by exact_mod_cast hn1)) (hrate n hn1) k
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
