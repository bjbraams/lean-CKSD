module

public import CKSD.Asymptotics.LikelihoodSupport

/-!
# Empirical distribution functions and sample quantiles

Order and measurability of the empirical CDF and its left quantile, a local empirical-CDF
estimate, and the Bahadur representation and normal limit of sample quantiles.
Sources: GAPS 102.6 and `SYNOPSIS102.md`. The Bahadur proof follows Ghosh's crossing argument
(Ghosh, *Ann. Math. Statist.* 42 (1971)), using Chebyshev's inequality and Slutsky's theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The empirical distribution function as a normalised sum of indicators. -/
theorem empiricalCDF_eq_sum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    empiricalCDF X n ω t = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, if X i ω ≤ t then (1 : ℝ) else 0 := by
  rw [empiricalCDF, Finset.sum_boole, div_eq_inv_mul]

/-- The empirical distribution function is monotone. -/
theorem empiricalCDF_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (empiricalCDF X n ω) := by
  intro s t hst
  rw [empiricalCDF_eq_sum, empiricalCDF_eq_sum]
  gcongr with i hi
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hst) h2
  · norm_num
  · exact le_rfl

/-- The empirical distribution function is `1` at `∑ |Xᵢ|` and `0` below `-∑ |Xᵢ|`. -/
theorem empiricalCDF_extremes {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
    empiricalCDF X n ω (∑ i ∈ Finset.range n, |X i ω|) = 1 ∧
      ∀ s < -∑ i ∈ Finset.range n, |X i ω|, empiricalCDF X n ω s = 0 := by
  have hle : ∀ i ∈ Finset.range n, |X i ω| ≤ ∑ j ∈ Finset.range n, |X j ω| := fun i hi ↦
    Finset.single_le_sum (f := fun j ↦ |X j ω|) (fun j _ ↦ abs_nonneg _) hi
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  constructor
  · rw [empiricalCDF_eq_sum, Finset.sum_congr rfl fun i hi ↦
      (show (if X i ω ≤ ∑ j ∈ Finset.range n, |X j ω| then (1 : ℝ) else 0) = 1 by
        simp [(le_abs_self _).trans (hle i hi)])]
    simp [hn0]
  · intro s hs
    rw [empiricalCDF_eq_sum, Finset.sum_eq_zero fun i hi ↦ ?_, mul_zero]
    have := neg_abs_le (X i ω)
    have : ¬ X i ω ≤ s := by linarith [hle i hi]
    simp [this]

/-- Order characterisation of the left sample quantile, for `n ≥ 1` and `p ∈ (0, 1]`. -/
theorem le_empiricalCDF_of_sampleQuantile_lt {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ω : Ω) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ s, sampleQuantile X n ω p < s → p ≤ empiricalCDF X n ω s) ∧
      (∀ s, s < sampleQuantile X n ω p → empiricalCDF X n ω s < p) := by
  obtain ⟨h1, h0⟩ := empiricalCDF_extremes X n hn ω
  set A := {t | p ≤ empiricalCDF X n ω t} with hA
  have hne : A.Nonempty := ⟨∑ i ∈ Finset.range n, |X i ω|, by
    show p ≤ empiricalCDF X n ω _
    rw [h1]; exact hp1⟩
  have hbdd : BddBelow A := by
    refine ⟨-∑ i ∈ Finset.range n, |X i ω|, fun a ha ↦ ?_⟩
    by_contra h
    push Not at h
    have := h0 a h
    simp only [hA, mem_ofPred_eq, this] at ha
    linarith
  constructor
  · intro s hs
    obtain ⟨a, ha, has⟩ := exists_lt_of_csInf_lt hne hs
    exact le_trans ha (empiricalCDF_mono X n ω has.le)
  · intro s hs
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h) (not_le.2 hs)

/-- Measurability of the empirical distribution function at a fixed point. -/
theorem measurable_empiricalCDF {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) (t : ℝ) : Measurable fun ω ↦ empiricalCDF X n ω t := by
  simp_rw [empiricalCDF_eq_sum]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _
  exact Measurable.ite (measurableSet_le (hX i) measurable_const) measurable_const
    measurable_const

/-- Measurability of the left sample quantile, for `p ∈ (0, 1]`. -/
theorem measurable_sampleQuantile {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Measurable fun ω ↦ sampleQuantile X n ω p := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    have : ∀ ω, sampleQuantile X 0 ω p = sInf {t : ℝ | p ≤ 0} := fun ω ↦ by
      simp [sampleQuantile, empiricalCDF]
    simp_rw [this]
    exact measurable_const
  refine measurable_of_Iio fun s ↦ ?_
  have hset : (fun ω ↦ sampleQuantile X n ω p) ⁻¹' Iio s =
      ⋃ a : ℚ, ⋃ (_ : (a : ℝ) < s), {ω | p ≤ empiricalCDF X n ω a} := by
    ext ω
    obtain ⟨hlt, hgt⟩ := le_empiricalCDF_of_sampleQuantile_lt X n hn ω hp0 hp1
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn h
      exact ⟨a, ha2, hlt _ ha1⟩
    · rintro ⟨a, ha, hpa⟩
      by_contra hcon
      push Not at hcon
      have := hgt a (lt_of_lt_of_le ha hcon)
      linarith
  rw [hset]
  exact MeasurableSet.iUnion fun a ↦ MeasurableSet.iUnion fun _ ↦
    measurableSet_le measurable_const (measurable_empiricalCDF X hX n a)

/-- The integral of the indicator of `(-∞, a]` is the distribution function at `a`. -/
theorem integral_ite_le_eq_cdf (P : Measure ℝ) (a : ℝ) :
    ∫ x, (if x ≤ a then (1 : ℝ) else 0) ∂P = cdf P a := by
  have : (fun x : ℝ ↦ if x ≤ a then (1 : ℝ) else 0) = (Iic a).indicator 1 := by
    ext x; simp [indicator, mem_Iic]
  rw [this, integral_indicator_one measurableSet_Iic]
  rfl

/-- `√n / n = 1 / √n`, in the form used for normalised sums. -/
theorem sqrt_mul_inv_natCast (n : ℕ) : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
  rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]

/-- Local increments of a distribution function differentiable at `q`:
`√n (F(q + t/√n) - F(q)) → f t`. -/
theorem tendsto_sqrt_mul_cdf_sub (P : Measure ℝ) (q f t : ℝ)
    (hd : HasDerivAt (cdf P) f q) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (cdf P (q + t / Real.sqrt n) - cdf P q)) atTop
      (𝓝 (f * t)) := by
  by_cases ht : t = 0
  · simp [ht]
  have hsq : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ ↦ t / Real.sqrt n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop hsq, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    exact div_ne_zero ht this.ne'
  have hs := (hd.tendsto_slope_zero.comp hh).const_mul t
  rw [mul_comm f t]
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [Function.comp, smul_eq_mul]
  field_simp

/-- The local empirical process at `q`: `√n (Fₙ(q + t/√n) - Fₙ(q)) → f t` in probability when the
distribution function is differentiable at `q` with derivative `f`. -/
theorem tendstoInProbabilityConst_sqrt_mul_empiricalCDF_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (q f t : ℝ)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (empiricalCDF X n ω (q + t / Real.sqrt n) - empiricalCDF X n ω q)) (f * t) := by
  set a : ℕ → ℝ := fun n ↦ q + t / Real.sqrt n with ha
  set ind : ℝ → ℝ → ℝ := fun b x ↦ if x ≤ b then (1 : ℝ) else 0 with hind
  have hindm : ∀ b, Measurable (ind b) := fun b ↦
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  set φ : ℕ → ℝ → ℝ := fun n x ↦ (Real.sqrt n)⁻¹ * (ind (a n) x - ind q x) with hφ
  have hφm : ∀ n, Measurable (φ n) := fun n ↦ ((hindm _).sub (hindm _)).const_mul _
  have hbound : ∀ n x, |ind (a n) x - ind q x| ≤ 1 := fun n x ↦ by
    simp only [hind]; split_ifs <;> norm_num
  have hφ2 : ∀ n, MemLp (φ n) 2 P := fun n ↦
    MemLp.of_bound (hφm n).aestronglyMeasurable ((Real.sqrt n)⁻¹) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (hbound n x))
  have hsq : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hat : Tendsto a atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds (x := q)).add ((tendsto_const_nhds (x := t)).div_atTop hsq)
  have hcont : ContinuousAt (cdf P) q := hd.continuousAt
  have hsqid : ∀ b c x, (ind b x - ind c x) ^ 2 = ind b x + ind c x - 2 * ind (min b c) x :=
    fun b c x ↦ by simp only [hind, le_min_iff]; split_ifs <;> simp_all; norm_num
  have hint : ∀ b, Integrable (ind b) P := fun b ↦
    (integrable_const (1 : ℝ)).mono (hindm b).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simp only [hind]; split_ifs <;> norm_num)
  have hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ cdf P (a n)) atTop (𝓝 (cdf P q)) := hcont.tendsto.comp hat
    have hmin : Tendsto (fun n ↦ min (a n) q) atTop (𝓝 q) := by
      simpa using hat.min (tendsto_const_nhds (x := q))
    have h2 : Tendsto (fun n ↦ cdf P (min (a n) q)) atTop (𝓝 (cdf P q)) :=
      hcont.tendsto.comp hmin
    have hm : Tendsto (fun n ↦ cdf P (a n) + cdf P q - 2 * cdf P (min (a n) q)) atTop
        (𝓝 (cdf P q + cdf P q - 2 * cdf P q)) :=
      (h1.add tendsto_const_nhds).sub (h2.const_mul 2)
    rw [show cdf P q + cdf P q - 2 * cdf P q = 0 by ring] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [hφ, mul_pow, hsqid]
    rw [integral_const_mul, integral_sub (f := fun x ↦ ind (a n) x + ind q x)
      (g := fun x ↦ 2 * ind (min (a n) q) x) ((hint _).add (hint _)) ((hint _).const_mul 2),
      integral_add (hint _) (hint _), integral_const_mul]
    simp only [hind, integral_ite_le_eq_cdf]
    rw [inv_pow, hs2]
    field_simp
  have hW := tendstoInProbabilityConst_sum_sub_of_iid μ P X hiid φ hφm hφ2 hlim
  have hD := tendstoInProbabilityConst_const_of_tendsto μ _
    (by simpa using (tendsto_sqrt_mul_cdf_sub P q f t hd).sub_const (f * t))
  have hsum := tendstoInProbabilityConst_add_zero μ _ _ hW hD
  intro ε hε
  refine (hsum ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero]
  rw [empiricalCDF_eq_sum, empiricalCDF_eq_sum]
  simp only [hφ, integral_const_mul]
  rw [integral_sub (hint _) (hint _)]
  simp only [hind, integral_ite_le_eq_cdf, ← Finset.mul_sum, Finset.sum_sub_distrib, ha]
  have e1 : (n : ℝ) * (Real.sqrt n)⁻¹ = Real.sqrt n := by
    rw [mul_comm, inv_mul_eq_div, Real.div_sqrt]
  have e2 := sqrt_mul_inv_natCast n
  rw [← mul_assoc (n : ℝ), e1]
  apply iff_of_eq
  congr 2
  linear_combination (-((∑ x ∈ Finset.range n, if X x ω ≤ q + t / Real.sqrt n then (1 : ℝ) else 0) -
    ∑ x ∈ Finset.range n, if X x ω ≤ q then (1 : ℝ) else 0)) * e2

/-- Central limit theorem for the empirical distribution function at a point `q` with
`F(q) = p`: `√n (p - Fₙ(q)) / f` converges in law to `N(0, p(1-p)/f²)`. -/
theorem tendstoInDistribution_sqrt_mul_sub_empiricalCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hq : cdf P q = p) (hf : 0 < f) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f)
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  set ind : ℝ → ℝ := fun x ↦ if x ≤ q then (1 : ℝ) else 0 with hind
  have hindm : Measurable ind := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hinti : Integrable ind P := (integrable_const (1 : ℝ)).mono hindm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simp only [hind]; split_ifs <;> norm_num)
  set s : ℝ → ℝ := fun x ↦ ind x - p with hs
  have hsm : Measurable s := hindm.sub measurable_const
  have hs2 : MemLp s 2 P := MemLp.of_bound hsm.aestronglyMeasurable (1 + |p|)
    (ae_of_all _ fun x ↦ by
      simp only [hs, hind, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      gcongr
      split_ifs <;> norm_num)
  have hs0 : ∫ x, s x ∂P = 0 := by
    simp only [hs]
    rw [integral_sub hinti (integrable_const p), hind, integral_ite_le_eq_cdf, hq]
    simp
  have hsq : ∫ x, s x ^ 2 ∂P = p * (1 - p) := by
    have : ∀ x, s x ^ 2 = (1 - 2 * p) * ind x + p ^ 2 := fun x ↦ by
      simp only [hs, hind]; split_ifs <;> ring
    simp_rw [this]
    rw [integral_add (hinti.const_mul _) (integrable_const _), integral_const_mul, hind,
      integral_ite_le_eq_cdf, hq]
    simp; ring
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid s hsm hs2 hs0
  rw [hsq] at hclt
  have hZm : ∀ n : ℕ, Measurable fun ω ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω) :=
    fun n ↦ (Finset.measurable_sum _ fun i _ ↦ hsm.comp (hiid.1 i)).const_mul _
  have := tendstoInDistribution_comp_of_continuous μ _ hZm _ (fun x ↦ -f⁻¹ * x)
    (continuous_const.mul continuous_id) hclt
  have hpp : 0 ≤ p * (1 - p) := by
    have h0 : 0 ≤ p := by rw [← hq]; exact measureReal_nonneg
    have h1 : p ≤ 1 := by rw [← hq]; exact measureReal_le_one
    nlinarith
  convert this using 1
  · funext n ω
    simp only [hs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      empiricalCDF_eq_sum, hind]
    have e1 : (Real.sqrt n)⁻¹ * ((n : ℝ) * p) = Real.sqrt n * p := by
      rw [← mul_assoc, mul_comm _ (n : ℝ), ← div_eq_mul_inv, Real.div_sqrt]
    have e2 := sqrt_mul_inv_natCast n
    rw [div_eq_mul_inv]
    linear_combination (-f⁻¹ * ∑ i ∈ Finset.range n, if X i ω ≤ q then (1 : ℝ) else 0) * e2 -
      f⁻¹ * e1
  · rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpp,
      Real.coe_toNNReal _ (div_nonneg hpp (sq_nonneg f))]
    field_simp

/-- Ghosh's crossing lemma: if `Wₙ` is bounded in probability and, for all `t` and `ε > 0`, the
probabilities of the crossing events `{Vₙ ≤ t, Wₙ ≥ t + ε}` and `{Vₙ ≥ t + ε, Wₙ ≤ t}` tend to `0`,
then `Vₙ - Wₙ → 0` in probability. -/
theorem tendstoInProbabilityConst_sub_of_crossing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V W : ℕ → Ω → ℝ) (hW : IsBoundedInProbability μ W)
    (h1 : ∀ t ε, 0 < ε → Tendsto (fun n ↦ μ.real {ω | V n ω ≤ t ∧ t + ε ≤ W n ω}) atTop (𝓝 0))
    (h2 : ∀ t ε, 0 < ε → Tendsto (fun n ↦ μ.real {ω | t + ε ≤ V n ω ∧ W n ω ≤ t}) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ (fun n ω ↦ V n ω - W n ω) 0 := by
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun _ ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨C, hC, hev⟩ := hW (η / 2) (half_pos hη)
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := half_pos hε
  set N := ⌊2 * C / δ⌋₊ with hN
  set tk : ℕ → ℝ := fun k ↦ -C + k * δ with htk
  set E1 : ℕ → ℕ → Set Ω := fun n k ↦ {ω | tk (k + 1) + δ ≤ V n ω ∧ W n ω ≤ tk (k + 1)}
    with hE1
  set E2 : ℕ → ℕ → Set Ω := fun n k ↦ {ω | V n ω ≤ tk k - δ ∧ tk k - δ + δ ≤ W n ω} with hE2
  have hsum : Tendsto (fun n ↦ ∑ k ∈ Finset.range (N + 1), (μ.real (E1 n k) + μ.real (E2 n k)))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (N + 1)) fun k _ ↦
      (h2 (tk (k + 1)) δ hδ0).add (h1 (tk k - δ) δ hδ0)
    simp only [add_zero, Finset.sum_const_zero] at this
    exact this
  filter_upwards [hev, hsum.eventually (eventually_le_nhds (half_pos hη))] with n hn1 hn2
  have hsub : {ω | ε < dist (V n ω - W n ω) 0} ⊆
      {ω | C < |W n ω|} ∪ ⋃ k ∈ Finset.range (N + 1), (E1 n k ∪ E2 n k) := by
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    by_cases hWC : C < |W n ω|
    · exact Or.inl hWC
    right
    push Not at hWC
    rw [abs_le] at hWC
    have hnn : 0 ≤ (W n ω + C) / δ := div_nonneg (by linarith) hδ0.le
    set k := ⌊(W n ω + C) / δ⌋₊ with hk
    have hk1 : (k : ℝ) * δ ≤ W n ω + C := by
      have := Nat.floor_le hnn
      rwa [le_div_iff₀ hδ0] at this
    have hk2 : W n ω + C < ((k : ℝ) + 1) * δ := by
      have := Nat.lt_floor_add_one ((W n ω + C) / δ)
      rwa [div_lt_iff₀ hδ0] at this
    have hkN : k ≤ N := Nat.floor_mono (by gcongr; linarith)
    simp only [mem_iUnion, Finset.mem_range, mem_union, hE1, hE2, mem_ofPred_eq, htk]
    refine ⟨k, by omega, ?_⟩
    push_cast
    rcases lt_abs.1 hω with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ μ.real {ω | C < |W n ω|} +
        ∑ k ∈ Finset.range (N + 1), (μ.real (E1 n k) + μ.real (E2 n k)) := by
        refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
        exact (measureReal_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ measureReal_union_le _ _)
    _ ≤ η / 2 + η / 2 := add_le_add hn1 hn2
    _ = η := add_halves η

/-- GAPS 102.7: the first-order Bahadur representation. -/
theorem tendstoInProbabilityConst_bahadur_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (sampleQuantile X n ω p - q - (p - empiricalCDF X n ω q) / f)) 0 := by
  obtain ⟨hp0, hp1⟩ := hp
  set V : ℕ → Ω → ℝ := fun n ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q) with hV
  set W : ℕ → Ω → ℝ := fun n ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f with hW
  set G : ℕ → Ω → ℝ → ℝ := fun n ω s ↦ Real.sqrt n *
    (empiricalCDF X n ω (q + s / Real.sqrt n) - empiricalCDF X n ω q) with hG
  have hWm : ∀ n, Measurable (W n) := fun n ↦
    ((measurable_const.sub (measurable_empiricalCDF X hiid.1 n q)).const_mul _).div_const _
  have hWb : IsBoundedInProbability μ W :=
    isBoundedInProbability_of_tendstoInDistribution μ W hWm _
      (tendstoInDistribution_sqrt_mul_sub_empiricalCDF μ P X hiid p q f hq hf)
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ t s, (V n ω ≤ t → t < s → f * W n ω ≤ G n ω s) ∧
      (s < t → t ≤ V n ω → G n ω s < f * W n ω) := by
    intro n hn ω t s
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    obtain ⟨hlt, hgt⟩ := le_empiricalCDF_of_sampleQuantile_lt X n hn ω hp0 hp1.le
    have hfW : f * W n ω = Real.sqrt n * (p - empiricalCDF X n ω q) := by
      simp only [hW]; field_simp
    rw [hfW]
    constructor
    · intro hVt hts
      have : sampleQuantile X n ω p < q + s / Real.sqrt n := by
        have h1 : sampleQuantile X n ω p - q ≤ t / Real.sqrt n := by
          rw [le_div_iff₀ hsp, mul_comm]; exact hVt
        have h2 : t / Real.sqrt n < s / Real.sqrt n := div_lt_div_of_pos_right hts hsp
        linarith
      have := hlt _ this
      simp only [hG]
      gcongr
    · intro hst htV
      have : q + s / Real.sqrt n < sampleQuantile X n ω p := by
        have h1 : t / Real.sqrt n ≤ sampleQuantile X n ω p - q := by
          rw [div_le_iff₀ hsp, mul_comm]; exact htV
        have h2 : s / Real.sqrt n < t / Real.sqrt n := div_lt_div_of_pos_right hst hsp
        linarith
      have := hgt _ this
      simp only [hG]
      gcongr
  have hGlim : ∀ s, TendstoInProbabilityConst μ (fun n ω ↦ G n ω s) (f * s) := fun s ↦
    tendstoInProbabilityConst_sqrt_mul_empiricalCDF_sub μ P X hiid q f s hd
  have hmain := tendstoInProbabilityConst_sub_of_crossing μ V W hWb (fun t ε hε ↦ ?_)
    (fun t ε hε ↦ ?_)
  · convert hmain using 3 with n ω
    simp only [hV, hW]
    ring
  · have hc : 0 < f * ε / 4 := by positivity
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
      (hGlim (t + ε / 2) _ hc)
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measureReal_mono fun ω hω ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    have := (key n hn ω t (t + ε / 2)).1 h1 (by linarith)
    have hfw : f * (t + ε) ≤ f * W n ω := mul_le_mul_of_nonneg_left h2 hf.le
    simp only [mem_ofPred_eq, Real.dist_eq]
    rw [lt_abs]
    left
    nlinarith
  · have hc : 0 < f * ε / 4 := by positivity
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
      (hGlim (t + ε / 2) _ hc)
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measureReal_mono fun ω hω ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    have := (key n hn ω (t + ε) (t + ε / 2)).2 (by linarith) h1
    have hfw : f * W n ω ≤ f * t := mul_le_mul_of_nonneg_left h2 hf.le
    simp only [mem_ofPred_eq, Real.dist_eq]
    rw [lt_abs]
    right
    nlinarith

/-- GAPS 102.6: asymptotic normality of a sample quantile. -/
theorem tendstoInDistribution_sampleQuantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q))
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  have hWm : ∀ n : ℕ, Measurable fun ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f :=
    fun n ↦ ((measurable_const.sub (measurable_empiricalCDF X hiid.1 n q)).const_mul _).div_const _
  have hVm : ∀ n : ℕ, Measurable fun ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q) := fun n ↦
    ((measurable_sampleQuantile X hiid.1 n hp.1 hp.2.le).sub_const _).const_mul _
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub μ _ _ hWm hVm _
    (tendstoInDistribution_sqrt_mul_sub_empiricalCDF μ P X hiid p q f hq hf) ?_
  convert tendstoInProbabilityConst_bahadur_remainder μ P X hiid p q f hp hq hf hd using 3 with n ω
  ring

end CKSD
