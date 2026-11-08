module

public import CKSD.Asymptotics.Convergence

/-!
# Integral and Taylor estimates for likelihood asymptotics

Square-integral bounds for iid triangular-array remainders, density-weighted integration,
measurability of parameter derivatives, and deterministic third-derivative remainder bounds.
These estimates support the scalar LAN and likelihood-root theorems of Section 102.
Sources: `GAPS.md`, `SYNOPSIS102.md`, and the proof of van der Vaart,
*Asymptotic Statistics*, Theorem 7.2. The logarithmic remainder uses Mathlib's
`Real.abs_log_sub_add_sum_range_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A real number `x` with `2 x ≤ δ A + B / δ` for every `δ > 0` satisfies `x ≤ √A √B`. -/
theorem le_sqrt_mul_sqrt_of_forall_two_mul_le {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ δ > 0, 2 * x ≤ δ * A + B / δ) : x ≤ Real.sqrt A * Real.sqrt B := by
  rcases hA.lt_or_eq with hA' | hA'
  · rcases hB.lt_or_eq with hB' | hB'
    · have hsA := Real.sqrt_pos.2 hA'
      have hsB := Real.sqrt_pos.2 hB'
      have := h (Real.sqrt B / Real.sqrt A) (div_pos hsB hsA)
      have e1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
        rw [div_mul_eq_mul_div, div_eq_iff hsA.ne',
          show Real.sqrt B * A = Real.sqrt B * (Real.sqrt A * Real.sqrt A) by
            rw [Real.mul_self_sqrt hA]]
        ring
      have e2 : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt A * Real.sqrt B := by
        rw [div_div_eq_mul_div, div_eq_iff hsB.ne',
          show B * Real.sqrt A = (Real.sqrt B * Real.sqrt B) * Real.sqrt A by
            rw [Real.mul_self_sqrt hB]]
        ring
      rw [e1, e2] at this
      linarith
    · subst hB'
      simp only [Real.sqrt_zero, mul_zero]
      by_contra hx
      push Not at hx
      have := h (x / (A + 1)) (by positivity)
      rw [zero_div, add_zero] at this
      have : x / (A + 1) * A < x := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  · subst hA'
    simp only [Real.sqrt_zero, zero_mul]
    by_contra hx
    push Not at hx
    have := h ((B + 1) / x) (by positivity)
    simp only [mul_zero, zero_add] at this
    rw [div_div_eq_mul_div] at this
    have : B * x / (B + 1) < x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- The Cauchy–Schwarz inequality for real integrals of square-integrable functions. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a b : α → ℝ) (ham : AEStronglyMeasurable a ν) (hbm : AEStronglyMeasurable b ν)
    (ha : Integrable (fun x ↦ a x ^ 2) ν) (hb : Integrable (fun x ↦ b x ^ 2) ν) :
    |∫ x, a x * b x ∂ν| ≤ Real.sqrt (∫ x, a x ^ 2 ∂ν) * Real.sqrt (∫ x, b x ^ 2 ∂ν) := by
  have hpt : ∀ δ > 0, ∀ x, 2 * |a x * b x| ≤ δ * a x ^ 2 + b x ^ 2 / δ := by
    intro δ hδ x
    rw [abs_mul, ← sq_abs (a x), ← sq_abs (b x)]
    have : 0 ≤ (δ * |a x| - |b x|) ^ 2 / δ := by positivity
    have e : (δ * |a x| - |b x|) ^ 2 / δ = δ * |a x| ^ 2 + |b x| ^ 2 / δ - 2 * (|a x| * |b x|) := by
      field_simp
      ring
    linarith
  have hab : Integrable (fun x ↦ a x * b x) ν := by
    refine ((ha.add hb).div_const 2).mono' (ham.mul hbm) (ae_of_all _ fun x ↦ ?_)
    have := hpt 1 one_pos x
    rw [Real.norm_eq_abs]
    simp only [one_mul, div_one] at this
    show |a x * b x| ≤ (a x ^ 2 + b x ^ 2) / 2
    linarith
  refine le_sqrt_mul_sqrt_of_forall_two_mul_le (integral_nonneg fun _ ↦ sq_nonneg _)
    (integral_nonneg fun _ ↦ sq_nonneg _) fun δ hδ ↦ ?_
  calc 2 * |∫ x, a x * b x ∂ν| ≤ ∫ x, 2 * |a x * b x| ∂ν := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by norm_num)
    _ ≤ ∫ x, (δ * a x ^ 2 + b x ^ 2 / δ) ∂ν :=
        integral_mono (hab.abs.const_mul 2) ((ha.const_mul δ).add (hb.div_const δ)) (hpt δ hδ)
    _ = δ * ∫ x, a x ^ 2 ∂ν + (∫ x, b x ^ 2 ∂ν) / δ := by
        rw [integral_add (ha.const_mul δ) (hb.div_const δ), integral_const_mul, integral_div]

/-- Chebyshev's inequality for a sum of a measurable square-integrable statistic of an iid
sequence. -/
theorem measureReal_le_abs_sum_sub_le_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : E → ℝ) (hφ : Measurable φ) (h2 : MemLp φ 2 P) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, φ (X i ω) - n * ∫ x, φ x ∂P|} ≤
      n * (∫ x, φ x ^ 2 ∂P) / ε ^ 2 := by
  obtain ⟨hindep, hident⟩ := iid_comp_pairwise_identDistrib hiid hφ
  have hm := hiid.1
  have h2i : ∀ i, MemLp (φ ∘ X i) 2 μ := fun i ↦ by
    have h := h2
    rw [← hiid.2.2 i] at h
    exact h.comp_of_map (hm i).aemeasurable
  set Y : Ω → ℝ := ∑ i ∈ Finset.range n, φ ∘ X i with hY
  have hYfun : ∀ ω, Y ω = ∑ i ∈ Finset.range n, φ (X i ω) := fun ω ↦ by
    simp [hY, Finset.sum_apply]
  have hY2 : MemLp Y 2 μ := memLp_finsetSum' _ fun i _ ↦ h2i i
  have hmeanY : μ[Y] = n * ∫ x, φ x ∂P := by
    rw [show μ[Y] = ∫ ω, ∑ i ∈ Finset.range n, (φ ∘ X i) ω ∂μ by simp only [hY, Finset.sum_apply],
      integral_finsetSum _ fun i _ ↦ (h2i i).integrable one_le_two]
    have : ∀ i, ∫ ω, (φ ∘ X i) ω ∂μ = ∫ x, φ x ∂P := fun i ↦ by
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable hφ.aestronglyMeasurable]; rfl
    rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hvarY : ProbabilityTheory.variance Y μ ≤ n * ∫ x, φ x ^ 2 ∂P := by
    rw [hY, IndepFun.variance_sum (fun i _ ↦ h2i i) (fun i _ j _ hij ↦ hindep hij)]
    have : ∀ i, ProbabilityTheory.variance (φ ∘ X i) μ ≤ ∫ x, φ x ^ 2 ∂P := fun i ↦ by
      refine (variance_le_expectation_sq (h2i i).aestronglyMeasurable).trans_eq ?_
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable (hφ.pow_const 2).aestronglyMeasurable]
      rfl
    calc ∑ i ∈ Finset.range n, ProbabilityTheory.variance (φ ∘ X i) μ
        ≤ ∑ _i ∈ Finset.range n, ∫ x, φ x ^ 2 ∂P := Finset.sum_le_sum fun i _ ↦ this i
      _ = n * ∫ x, φ x ^ 2 ∂P := by simp
  have hcheb := meas_ge_le_variance_div_sq hY2 hε
  rw [hmeanY] at hcheb
  have hset : {ω | ε ≤ |∑ i ∈ Finset.range n, φ (X i ω) - n * ∫ x, φ x ∂P|} =
      {ω | ε ≤ |Y ω - n * ∫ x, φ x ∂P|} := by
    ext ω; simp [hYfun]
  rw [hset, measureReal_def]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb).trans ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))]
  gcongr

/-- A triangular-array weak law: if `n ∫ φₙ² dP → 0`, then the centred sums
`∑_{i<n} (φₙ(Xᵢ) - ∫ φₙ dP)` of an iid sequence tend to zero in probability. -/
theorem tendstoInProbabilityConst_sum_sub_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n)) (h2 : ∀ n, MemLp (φ n) 2 P)
    (hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ
      (fun n ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) - n * ∫ x, φ n x ∂P) 0 := by
  intro ε hε
  have hb : Tendsto (fun n : ℕ ↦ n * (∫ x, φ n x ^ 2 ∂P) / ε ^ 2) atTop (𝓝 0) := by
    simpa using hlim.div_const (ε ^ 2)
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hb
  refine (measureReal_mono fun ω hω ↦ ?_).trans
    (measureReal_le_abs_sum_sub_le_of_iid μ P X hiid (φ n) (hφ n) (h2 n) n hε)
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.le

/-- Markov's inequality for sums of squares: if `n ∫ φₙ² dP → 0`, then `∑_{i<n} φₙ(Xᵢ)²` tends to
zero in probability. -/
theorem tendstoInProbabilityConst_sum_sq_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n)) (h2 : ∀ n, Integrable (fun x ↦ φ n x ^ 2) P)
    (hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ (fun n ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2) 0 := by
  intro ε hε
  have hm := hiid.1
  have hb : Tendsto (fun n : ℕ ↦ n * (∫ x, φ n x ^ 2 ∂P) / ε) atTop (𝓝 0) := by
    simpa using hlim.div_const ε
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hb
  have hint : ∀ i, Integrable (fun ω ↦ φ n (X i ω) ^ 2) μ := fun i ↦ by
    have h := h2 n
    rw [← hiid.2.2 i] at h
    exact h.comp_measurable (hm i)
  have hsum : ∫ ω, ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2 ∂μ = n * ∫ x, φ n x ^ 2 ∂P := by
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    have : ∀ i, ∫ ω, φ n (X i ω) ^ 2 ∂μ = ∫ x, φ n x ^ 2 ∂P := fun i ↦ by
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable
        ((hφ n).pow_const 2).aestronglyMeasurable]
    simp [this]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2)
    (ae_of_all _ fun ω ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg (φ n (X i ω)))
    (integrable_finsetSum (Finset.range n) fun i _ ↦ hint i) ε
  rw [hsum] at hmk
  have hsub : μ.real {ω | ε < dist (∑ i ∈ Finset.range n, φ n (X i ω) ^ 2) 0} ≤
      μ.real {x | ε ≤ ∑ i ∈ Finset.range n, φ n (X i x) ^ 2} := by
    refine measureReal_mono ?_
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)] at hω
    exact hω.le
  rw [le_div_iff₀ hε]
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans ((mul_comm _ _).le.trans hmk)

/-- A one-term logarithmic expansion: for `|g| ≤ 1/2`,
`|2 log (1 + g) - (2 g - g²)| ≤ 4 |g|³`. -/
theorem abs_two_mul_log_one_add_sub_le {g : ℝ} (hg : |g| ≤ 1 / 2) :
    |2 * Real.log (1 + g) - (2 * g - g ^ 2)| ≤ 4 * |g| ^ 3 := by
  have h1 : |-g| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  have hden : |g| ^ (2 + 1) / (1 - |g|) ≤ 2 * |g| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |g| ^ 3 := by positivity
    norm_num
    nlinarith
  have e : 2 * Real.log (1 + g) - (2 * g - g ^ 2) =
      2 * (0 + (-g) ^ (0 + 1) / ((0 : ℕ) + 1) + (-g) ^ (1 + 1) / ((1 : ℕ) + 1) +
        Real.log (1 + g)) := by
    push_cast
    ring
  rw [e, abs_mul, abs_two]
  linarith

/-- Uniform integrability of a square-integrable function along `√n`: for `c > 0`,
`n P(|s| > c √n) → 0`. -/
theorem tendsto_mul_measureReal_lt_abs_of_integrable_sq {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsFiniteMeasure P] (s : E → ℝ) (hs : Measurable s)
    (h2 : Integrable (fun x ↦ s x ^ 2) P) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ n * P.real {x | c * Real.sqrt n < |s x|}) atTop (𝓝 0) := by
  set A : ℕ → Set E := fun n ↦ {x | c * Real.sqrt n < |s x|} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hs)
  have h1 : ∀ n : ℕ, n * P.real (A n) ≤ (∫ x, (A n).indicator (fun x ↦ s x ^ 2) x ∂P) / c ^ 2 := by
    intro n
    rw [le_div_iff₀ (by positivity), integral_indicator (hAm n)]
    calc (n : ℝ) * P.real (A n) * c ^ 2 = ∫ _x in A n, c ^ 2 * n ∂P := by
          rw [setIntegral_const, smul_eq_mul]; ring
      _ ≤ ∫ x in A n, s x ^ 2 ∂P := by
          refine setIntegral_mono_on (integrableOn_const (by simp)) h2.integrableOn (hAm n) ?_
          intro x hx
          simp only [hA, mem_ofPred_eq] at hx
          have h0 : 0 ≤ c * Real.sqrt n := by positivity
          have := mul_self_lt_mul_self h0 hx
          rw [← sq_abs (s x)]
          calc c ^ 2 * n = (c * Real.sqrt n) * (c * Real.sqrt n) := by
                rw [mul_mul_mul_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]; ring
            _ ≤ |s x| ^ 2 := by rw [sq]; exact this.le
  have h2' : Tendsto (fun n : ℕ ↦ ∫ x, (A n).indicator (fun x ↦ s x ^ 2) x ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun x ↦ s x ^ 2)
      (F := fun n : ℕ ↦ (A n).indicator (fun x ↦ s x ^ 2))
      (f := fun _ ↦ (0 : ℝ))
      (fun n ↦ ((hs.pow_const 2).indicator (hAm n)).aestronglyMeasurable) h2
      (fun n ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
        exact indicator_le_self' (fun _ _ ↦ sq_nonneg _) x)
      (ae_of_all _ fun x ↦ by
        have hsq : Tendsto (fun n : ℕ ↦ c * Real.sqrt n) atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hsq.eventually_ge_atTop (|s x|)] with n hn
        simp only [hA]
        rw [indicator_of_notMem]
        simp only [mem_ofPred_eq, not_lt]
        exact hn)
    simpa using this
  refine squeeze_zero (fun n ↦ by positivity) h1 ?_
  simpa using h2'.div_const (c ^ 2)

/-- For a law with a density, a real function is integrable iff its product with the density is
integrable for the reference measure, and the integrals agree. -/
theorem integrable_and_integral_eq_of_hasDensity {E : Type*} [MeasurableSpace E]
    {P ν : Measure E} {p : E → ℝ} (hp : HasDensity P ν p) (φ : E → ℝ) :
    (Integrable φ P ↔ Integrable (fun x ↦ p x * φ x) ν) ∧
      ∫ x, φ x ∂P = ∫ x, p x * φ x ∂ν := by
  obtain ⟨hpm, hp0, hPe⟩ := hp
  have hae : (fun x ↦ (ENNReal.ofReal (p x)).toReal • φ x) =ᵐ[ν] fun x ↦ p x * φ x := by
    filter_upwards [hp0] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  subst hPe
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hpm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integrable_congr hae
  · rw [integral_withDensity_eq_integral_toReal_smul hpm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integral_congr_ae hae

/-- The density of a probability law is integrable with integral one. -/
theorem integrable_and_integral_eq_one_of_hasDensity {E : Type*} [MeasurableSpace E]
    {P ν : Measure E} [IsProbabilityMeasure P] {p : E → ℝ} (hp : HasDensity P ν p) :
    Integrable p ν ∧ ∫ x, p x ∂ν = 1 := by
  obtain ⟨h1, h2⟩ := integrable_and_integral_eq_of_hasDensity hp (fun _ ↦ 1)
  simp only [mul_one] at h1 h2
  exact ⟨h1.1 (integrable_const 1), by rw [← h2]; simp⟩

/-- The derivative in a real parameter of a family of measurable functions, differentiable in the
parameter, is measurable in the observation. -/
theorem measurable_deriv_param {E : Type*} [MeasurableSpace E] (φ : ℝ → E → ℝ)
    (hm : ∀ t, Measurable (φ t)) (hd : ∀ x, Differentiable ℝ (fun t ↦ φ t x)) (t₀ : ℝ) :
    Measurable (fun x ↦ deriv (fun t ↦ φ t x) t₀) := by
  let u : ℕ → ℝ := fun k ↦ t₀ + 1 / ((k : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝[≠] t₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
    · simpa [u] using (tendsto_const_nhds (x := t₀)).add tendsto_one_div_add_atTop_nhds_zero_nat
    · simp only [u, mem_compl_iff, mem_singleton_iff, add_eq_left]
      positivity
  refine measurable_of_tendsto_metrizable (f := fun k x ↦ slope (fun t ↦ φ t x) t₀ (u k))
    (fun k ↦ ?_) (tendsto_pi_nhds.2 fun x ↦ ((hd x t₀).hasDerivAt.tendsto_slope).comp hu)
  simp only [slope_def_field]
  exact ((hm _).sub (hm _)).div_const _

/-- A second-order Taylor bound for the derivative of a `C³` function whose third derivative is
bounded by `M` on a ball. -/
theorem abs_deriv_sub_taylor_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (θ₀ r M : ℝ)
    (hM : ∀ t, |t - θ₀| < r → |deriv (deriv (deriv φ)) t| ≤ M) (t : ℝ) (ht : |t - θ₀| < r) :
    |deriv φ t - deriv φ θ₀ - (t - θ₀) * deriv (deriv φ) θ₀| ≤ M * (t - θ₀) ^ 2 := by
  have h3 : ContDiff ℝ (2 + 1) φ := hφ
  have h2 : ContDiff ℝ (1 + 1) (deriv φ) := (contDiff_succ_iff_deriv.1 h3).2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv φ)) := (contDiff_succ_iff_deriv.1 h2).2.2
  have hd1 : Differentiable ℝ (deriv φ) := (contDiff_succ_iff_deriv.1 h2).1
  have hd2 : Differentiable ℝ (deriv (deriv φ)) := h1.differentiable one_ne_zero
  have hball : ∀ s, |s - θ₀| < r → s ∈ Metric.ball θ₀ r := fun s hs ↦ by
    rwa [Metric.mem_ball, Real.dist_eq]
  have hstep : ∀ s, |s - θ₀| < r →
      |deriv (deriv φ) s - deriv (deriv φ) θ₀| ≤ M * |s - θ₀| := by
    intro s hs
    have := (convex_ball θ₀ r).norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv φ))
      (fun x _ ↦ hd2 x) (fun x hx ↦ by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        simpa [Real.norm_eq_abs] using hM x hx)
      (Metric.mem_ball_self (lt_of_le_of_lt (abs_nonneg _) ht)) (hball s hs)
    simpa [Real.norm_eq_abs] using this
  let ψ : ℝ → ℝ := fun s ↦ deriv φ s - deriv φ θ₀ - (s - θ₀) * deriv (deriv φ) θ₀
  have hψd : ∀ s, HasDerivAt ψ (deriv (deriv φ) s - deriv (deriv φ) θ₀) s := by
    intro s
    have := ((hd1 s).hasDerivAt.sub_const (deriv φ θ₀)).sub
      (((hasDerivAt_id s).sub_const θ₀).mul_const (deriv (deriv φ) θ₀))
    convert this using 1
    · funext y; simp [ψ]
    · ring
  have hseg : uIcc θ₀ t ⊆ {s | |s - θ₀| ≤ |t - θ₀|} := by
    intro s hs
    simp only [mem_ofPred_eq]
    rcases le_total θ₀ t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]; linarith [hs.2]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]; linarith [hs.1]
  have hmv := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_deriv_le (f := ψ)
    (C := M * |t - θ₀|) (fun x _ ↦ (hψd x).differentiableAt) (fun x hx ↦ by
      rw [(hψd x).deriv, Real.norm_eq_abs]
      have hx' : |x - θ₀| ≤ |t - θ₀| := hseg hx
      calc |deriv (deriv φ) x - deriv (deriv φ) θ₀| ≤ M * |x - θ₀| :=
            hstep x (lt_of_le_of_lt hx' ht)
        _ ≤ M * |t - θ₀| := by
            have hM0 : 0 ≤ M := by
              have := hM θ₀ (by simpa using lt_of_le_of_lt (abs_nonneg _) ht)
              exact (abs_nonneg _).trans this
            exact mul_le_mul_of_nonneg_left hx' hM0)
    left_mem_uIcc right_mem_uIcc
  have hψ0 : ψ θ₀ = 0 := by simp [ψ]
  rw [hψ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc |deriv φ t - deriv φ θ₀ - (t - θ₀) * deriv (deriv φ) θ₀| = |ψ t| := rfl
    _ ≤ M * |t - θ₀| * |t - θ₀| := hmv
    _ = M * (t - θ₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A second-order Taylor bound for a `C³` function whose third derivative is bounded by `M`
on a ball: the remainder is at most `M |t - θ₀|³`. -/
theorem abs_sub_taylor_two_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (θ₀ r M : ℝ)
    (hM : ∀ t, |t - θ₀| < r → |deriv (deriv (deriv φ)) t| ≤ M) (t : ℝ) (ht : |t - θ₀| < r) :
    |φ t - φ θ₀ - (t - θ₀) * deriv φ θ₀ - (t - θ₀) ^ 2 / 2 * deriv (deriv φ) θ₀| ≤
      M * |t - θ₀| ^ 3 := by
  have h3 : ContDiff ℝ (2 + 1) φ := hφ
  have hd0 : Differentiable ℝ φ := (contDiff_succ_iff_deriv.1 h3).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM θ₀ (by simpa using lt_of_le_of_lt (abs_nonneg _) ht))
  let g : ℝ → ℝ := fun s ↦ φ s - φ θ₀ - (s - θ₀) * deriv φ θ₀ -
    (s - θ₀) ^ 2 / 2 * deriv (deriv φ) θ₀
  have hgd : ∀ s, HasDerivAt g (deriv φ s - deriv φ θ₀ - (s - θ₀) * deriv (deriv φ) θ₀) s := by
    intro s
    have h1 := (((hd0 s).hasDerivAt.sub_const (φ θ₀)).sub
      (((hasDerivAt_id s).sub_const θ₀).mul_const (deriv φ θ₀))).sub
      ((((hasDerivAt_id s).sub_const θ₀).pow 2).div_const 2 |>.mul_const (deriv (deriv φ) θ₀))
    convert h1 using 1
    · funext y; simp [g]
    · simp
  have hseg : ∀ s ∈ uIcc θ₀ t, |s - θ₀| ≤ |t - θ₀| := by
    intro s hs
    rcases le_total θ₀ t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]; linarith [hs.2]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]; linarith [hs.1]
  have hmv := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_deriv_le (f := g)
    (C := M * |t - θ₀| ^ 2) (fun x _ ↦ (hgd x).differentiableAt) (fun x hx ↦ by
      rw [(hgd x).deriv, Real.norm_eq_abs]
      have hx' := hseg x hx
      calc |deriv φ x - deriv φ θ₀ - (x - θ₀) * deriv (deriv φ) θ₀| ≤ M * (x - θ₀) ^ 2 :=
            abs_deriv_sub_taylor_le φ hφ θ₀ r M hM x (lt_of_le_of_lt hx' ht)
        _ ≤ M * |t - θ₀| ^ 2 := by
            rw [← sq_abs (x - θ₀)]
            gcongr)
    left_mem_uIcc right_mem_uIcc
  have hg0 : g θ₀ = 0 := by simp [g]
  rw [hg0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc _ = |g t| := rfl
    _ ≤ M * |t - θ₀| ^ 2 * |t - θ₀| := hmv
    _ = M * |t - θ₀| ^ 3 := by ring

/-- Deterministic core of Cramér's argument: from the linearized score equation
`Z + W B + q = 0` with `B` close to `-I` and a quadratic remainder `q`, the scaled error `W` is
within `4 κ |Z| / I²` of `Z / I`. -/
theorem abs_sub_div_le_of_score_equation {W Z B q d A I κ : ℝ} (hI : 0 < I) (hκ : κ ≤ I / 4)
    (heq : Z + W * B + q = 0) (hq : |q| ≤ |W| * (d * A)) (hB : |B + I| ≤ κ)
    (hdA : d * A ≤ κ) :
    |W - Z / I| ≤ 4 * κ * |Z| / I ^ 2 := by
  have hkey : W * I - Z = W * (B + I) + q := by linear_combination -heq
  have h1 : |W * I - Z| ≤ 2 * κ * |W| := by
    rw [hkey]
    calc |W * (B + I) + q| ≤ |W * (B + I)| + |q| := abs_add_le _ _
      _ ≤ |W| * κ + |W| * κ := by
          rw [abs_mul]
          gcongr
          exact hq.trans (mul_le_mul_of_nonneg_left hdA (abs_nonneg W))
      _ = 2 * κ * |W| := by ring
  have hW : |W| * I ≤ 2 * |Z| := by
    have : |W * I| ≤ |Z| + 2 * κ * |W| := by
      calc |W * I| = |(W * I - Z) + Z| := by ring_nf
        _ ≤ |W * I - Z| + |Z| := abs_add_le _ _
        _ ≤ 2 * κ * |W| + |Z| := by linarith
        _ = |Z| + 2 * κ * |W| := by ring
    rw [abs_mul, abs_of_pos hI] at this
    nlinarith [abs_nonneg W]
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hB
  have h2 : |W * I - Z| ≤ 4 * κ * |Z| / I := by
    rw [le_div_iff₀ hI]
    nlinarith [abs_nonneg W, abs_nonneg Z]
  have : W - Z / I = (W * I - Z) / I := by field_simp
  rw [this, abs_div, abs_of_pos hI, div_le_iff₀ hI]
  calc |W * I - Z| ≤ 4 * κ * |Z| / I := h2
    _ = 4 * κ * |Z| / I ^ 2 * I := by field_simp

end CKSD
