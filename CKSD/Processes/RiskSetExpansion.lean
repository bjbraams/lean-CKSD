module

public import CKSD.Processes.Basic


/-!
# Risk-set estimators of independent samples

Second-moment bounds for kernels of iid sequences and a central limit theorem for risk-set
estimators `∑_{i<n} A(Zᵢ) / #{j < n : x(Zᵢ) ≤ x(Zⱼ)}`, the form of the Nelson–Aalen estimator
under random censoring. The proof expands `1 / Y` around the at-risk probability
`y(s) = P(x ≥ s)`; the first-order term is a `V`-statistic, whose Hájek projection contributes
to the influence function, and the degenerate part and the quadratic remainder are negligible
by second-moment bounds.

## Main results

* `CKSD.integral_comp_eq_zero_of_iid`: integrating out one coordinate of an iid sequence.
* `CKSD.integral_sq_sum_le_of_iid`, `CKSD.integral_sq_sum_sum_le_of_iid`: second moments of
  sums of kernels with mean zero in one or both arguments.
* `CKSD.tendsto_in_measure_zero_of_integral_le`, `CKSD.tendsto_in_measure_zero_of_integral_sq_le`:
  Markov's and Chebyshev's inequalities in sequential form.
* `CKSD.tendsto_in_distribution_sqrt_mul_risk_set_sum_sub`: the central limit theorem for
  risk-set estimators.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Integrating out one coordinate of an iid sequence: if `G z w` has `P`-mean zero in `z` for
every `w`, then `𝔼 G(Z i, (Z l)_{l ∈ T}) = 0` whenever `i ∉ T`. -/
theorem integral_comp_eq_zero_of_iid {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (i : ℕ) (T : Finset ℕ) (hi : i ∉ T) (G : E → (T → E) → ℝ)
    (hG : Measurable (Function.uncurry G)) (B : ℝ) (hB : ∀ z w, |G z w| ≤ B)
    (h0 : ∀ w, ∫ z, G z w ∂P = 0) :
    ∫ ω, G (Z i ω) (fun l : T ↦ Z l ω) ∂μ = 0 := by
  have hW : Measurable fun ω (l : T) ↦ Z l ω := measurable_pi_iff.2 fun l ↦ hiid.1 l
  have hind : IndepFun (fun ω (l : ({i} : Finset ℕ)) ↦ Z l ω) (fun ω (l : T) ↦ Z l ω) μ :=
    hiid.2.1.indepFun_finset {i} T (Finset.disjoint_singleton_left.2 hi) hiid.1
  have hind' : IndepFun (Z i) (fun ω (l : T) ↦ Z l ω) μ :=
    hind.comp (φ := fun v : ({i} : Finset ℕ) → E ↦ v ⟨i, Finset.mem_singleton_self i⟩)
      (ψ := id) (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset ℕ)))
      measurable_id
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hiid.1 i).aemeasurable
    hW.aemeasurable).1 hind'
  rw [hiid.2.2 i] at hmap
  have hint : Integrable (Function.uncurry G) (P.prod (μ.map fun ω (l : T) ↦ Z l ω)) :=
    Integrable.of_bound hG.aestronglyMeasurable B
      (ae_of_all _ fun p ↦ by
        rw [Real.norm_eq_abs]; exact hB p.1 p.2)
  have h := integral_map (μ := μ) ((hiid.1 i).prodMk hW).aemeasurable
    (f := Function.uncurry G) hG.aestronglyMeasurable
  simp only [Function.uncurry_apply_pair] at h
  rw [← h, hmap, integral_prod_symm _ hint]
  simp [h0]

/-- For an iid sequence and a bounded kernel `g` with `P`-mean zero in its first argument,
`𝔼[g(Z a, Z b) g(Z c, Z d)] = 0` whenever the index `a` occurs only once. -/
theorem integral_mul_eq_zero_of_iid_left {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (h0 : ∀ z', ∫ z, g z z' ∂P = 0)
    {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    ∫ ω, g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω) ∂μ = 0 := by
  set T : Finset ℕ := {b, c, d}
  have hbT : b ∈ T := by simp [T]
  have hcT : c ∈ T := by simp [T]
  have hdT : d ∈ T := by simp [T]
  have h := integral_comp_eq_zero_of_iid μ P Z hiid a T (by simp [T, hab, hac, had])
    (fun z w ↦ g z (w ⟨b, hbT⟩) * g (w ⟨c, hcT⟩) (w ⟨d, hdT⟩))
    (by
      have hgm {u v : E × (T → E) → E} (hu : Measurable u) (hv : Measurable v) :
          Measurable fun p ↦ g (u p) (v p) := hg.comp (hu.prodMk hv)
      exact (hgm measurable_fst ((measurable_pi_apply _).comp measurable_snd)).mul
        (hgm ((measurable_pi_apply _).comp measurable_snd)
          ((measurable_pi_apply _).comp measurable_snd))) (B * B)
    (fun z w ↦ by
      rw [abs_mul]
      exact mul_le_mul (hB _ _) (hB _ _) (abs_nonneg _) ((abs_nonneg _).trans (hB z z)))
    (fun w ↦ by rw [integral_mul_const, h0, zero_mul])
  exact h

/-- For an iid sequence and a bounded kernel `g` with `P`-mean zero in its second argument,
`𝔼[g(Z a, Z b) g(Z c, Z d)] = 0` whenever the index `b` occurs only once. -/
theorem integral_mul_eq_zero_of_iid_right {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (h0 : ∀ z, ∫ z', g z z' ∂P = 0)
    {a b c d : ℕ} (hba : b ≠ a) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∫ ω, g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω) ∂μ = 0 := by
  set T : Finset ℕ := {a, c, d}
  have haT : a ∈ T := by simp [T]
  have hcT : c ∈ T := by simp [T]
  have hdT : d ∈ T := by simp [T]
  have h := integral_comp_eq_zero_of_iid μ P Z hiid b T (by simp [T, hba, hbc, hbd])
    (fun z w ↦ g (w ⟨a, haT⟩) z * g (w ⟨c, hcT⟩) (w ⟨d, hdT⟩))
    (by
      have hgm {u v : E × (T → E) → E} (hu : Measurable u) (hv : Measurable v) :
          Measurable fun p ↦ g (u p) (v p) := hg.comp (hu.prodMk hv)
      exact (hgm ((measurable_pi_apply _).comp measurable_snd) measurable_fst).mul
        (hgm ((measurable_pi_apply _).comp measurable_snd)
          ((measurable_pi_apply _).comp measurable_snd))) (B * B)
    (fun z w ↦ by
      rw [abs_mul]
      exact mul_le_mul (hB _ _) (hB _ _) (abs_nonneg _) ((abs_nonneg _).trans (hB z z)))
    (fun w ↦ by rw [integral_mul_const, h0, zero_mul])
  exact h

/-- Integrability of a bounded measurable function of two coordinates of an iid sequence. -/
theorem integrable_comp_pair_of_iid {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (a b : ℕ) :
    Integrable (fun ω ↦ g (Z a ω) (Z b ω)) μ :=
  Integrable.of_bound (hg.comp ((hiid.1 a).prodMk (hiid.1 b))).aestronglyMeasurable B
    (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB _ _)

/-- Second moment of a sum of a bounded kernel with mean zero in its second argument:
`𝔼 (∑_{j<n} g(Z i, Z j))² ≤ n B²`, since the off-diagonal products have mean zero. -/
theorem integral_sq_sum_le_of_iid {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (h0 : ∀ z, ∫ z', g z z' ∂P = 0) (i n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)) ^ 2 ∂μ ≤ n * B ^ 2 := by
  have hint (a b c d : ℕ) : Integrable (fun ω ↦ g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω)) μ :=
    (integrable_comp_pair_of_iid μ P Z hiid g hg B hB a b).bdd_mul
      ((hg.comp ((hiid.1 c).prodMk (hiid.1 d))).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB _ _) |>.congr
      (ae_of_all _ fun ω ↦ mul_comm _ _)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hint _ _ _ _]
  simp_rw [fun j ↦ integral_finsetSum (Finset.range n) fun k _ ↦ hint i j i k]
  have hterm (j k : ℕ) : ∫ ω, g (Z i ω) (Z j ω) * g (Z i ω) (Z k ω) ∂μ ≤
      if j = k then B ^ 2 else 0 := by
    split_ifs with hjk
    · subst hjk
      calc _ ≤ ∫ _ω, B ^ 2 ∂μ := integral_mono (hint _ _ _ _) (integrable_const _) fun ω ↦ by
              rw [← sq, ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hB _ _) 2
        _ = B ^ 2 := by simp
    · by_cases hji : j = i
      · subst hji
        have hki : k ≠ j := Ne.symm hjk
        rw [integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)]
        exact (integral_mul_eq_zero_of_iid_right μ P Z hiid g hg B hB h0 hki hki hki).le
      · exact (integral_mul_eq_zero_of_iid_right μ P Z hiid g hg B hB h0 hji hji hjk).le
  calc ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∫ ω, g (Z i ω) (Z j ω) * g (Z i ω) (Z k ω) ∂μ
      ≤ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, if j = k then B ^ 2 else 0 :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦ hterm j k
    _ = ∑ _j ∈ Finset.range n, B ^ 2 :=
        Finset.sum_congr rfl fun j hj ↦ by simp [Finset.sum_ite_eq, Finset.mem_range.1 hj]
    _ = n * B ^ 2 := by simp
    _ = n * (B * B) := by ring

/-- Second moment of a degenerate `V`-statistic: for a bounded kernel `g` with `P`-mean zero in
each argument, `𝔼 (∑_{i,j<n} g(Z i, Z j))² ≤ 3 n² B²`, since a product
`g(Z i, Z j) g(Z k, Z l)` has mean zero unless the indices pair up. -/
theorem integral_sq_sum_sum_le_of_iid {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (h1 : ∀ z', ∫ z, g z z' ∂P = 0)
    (h2 : ∀ z, ∫ z', g z z' ∂P = 0) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)) ^ 2 ∂μ ≤
      3 * n ^ 2 * B ^ 2 := by
  have hint (a b c d : ℕ) : Integrable (fun ω ↦ g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω)) μ :=
    (integrable_comp_pair_of_iid μ P Z hiid g hg B hB a b).bdd_mul
      ((hg.comp ((hiid.1 c).prodMk (hiid.1 d))).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB _ _) |>.congr
      (ae_of_all _ fun ω ↦ mul_comm _ _)
  have hexp (ω : Ω) : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)) ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∑ l ∈ Finset.range n, g (Z i ω) (Z j ω) * g (Z k ω) (Z l ω) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
  have hswap : ∫ ω, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∑ l ∈ Finset.range n, g (Z i ω) (Z j ω) * g (Z k ω) (Z l ω)) ∂μ =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∑ l ∈ Finset.range n, ∫ ω, g (Z i ω) (Z j ω) * g (Z k ω) (Z l ω) ∂μ := by
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _
      fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint _ _ _ _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hint _ _ _ _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint _ _ _ _]
    exact Finset.sum_congr rfl fun k _ ↦ integral_finsetSum _ fun l _ ↦ hint _ _ _ _
  simp_rw [hexp]
  rw [hswap]
  have hB2 (a b c d : ℕ) : ∫ ω, g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω) ∂μ ≤ B ^ 2 := by
    have h : ∀ ω, g (Z a ω) (Z b ω) * g (Z c ω) (Z d ω) ≤ B ^ 2 := fun ω ↦
      (le_abs_self _).trans (by
        rw [abs_mul, sq]
        exact mul_le_mul (hB _ _) (hB _ _) (abs_nonneg _)
          ((abs_nonneg _).trans (hB (Z a ω) (Z b ω))))
    calc _ ≤ ∫ _ω, B ^ 2 ∂μ := integral_mono (hint _ _ _ _) (integrable_const _) h
      _ = B ^ 2 := by simp
  have hterm (i j k l : ℕ) : ∫ ω, g (Z i ω) (Z j ω) * g (Z k ω) (Z l ω) ∂μ ≤
      (if i = j ∧ k = l then B ^ 2 else 0) + (if i = k ∧ j = l then B ^ 2 else 0) +
        (if i = l ∧ j = k then B ^ 2 else 0) := by
    have hB0 : 0 ≤ B ^ 2 := sq_nonneg B
    by_cases hp : (i = j ∧ k = l) ∨ (i = k ∧ j = l) ∨ (i = l ∧ j = k)
    · refine (hB2 i j k l).trans ?_
      rcases hp with hp | hp | hp <;> simp only [hp, and_self, ↓reduceIte] <;>
        split_ifs <;> linarith
    have hzero : ∫ ω, g (Z i ω) (Z j ω) * g (Z k ω) (Z l ω) ∂μ = 0 := by
      by_cases hi : i ≠ j ∧ i ≠ k ∧ i ≠ l
      · exact integral_mul_eq_zero_of_iid_left μ P Z hiid g hg B hB h1 hi.1 hi.2.1 hi.2.2
      by_cases hj : j ≠ i ∧ j ≠ k ∧ j ≠ l
      · exact integral_mul_eq_zero_of_iid_right μ P Z hiid g hg B hB h2 hj.1 hj.2.1 hj.2.2
      rw [integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)]
      by_cases hk : k ≠ l ∧ k ≠ i ∧ k ≠ j
      · exact integral_mul_eq_zero_of_iid_left μ P Z hiid g hg B hB h1 hk.1 hk.2.1 hk.2.2
      by_cases hl : l ≠ k ∧ l ≠ i ∧ l ≠ j
      · exact integral_mul_eq_zero_of_iid_right μ P Z hiid g hg B hB h2 hl.1 hl.2.1 hl.2.2
      exfalso
      omega
    rw [hzero]
    positivity
  calc _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        ∑ l ∈ Finset.range n, ((if i = j ∧ k = l then B ^ 2 else 0) +
          (if i = k ∧ j = l then B ^ 2 else 0) + (if i = l ∧ j = k then B ^ 2 else 0)) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦
          Finset.sum_le_sum fun l _ ↦ hterm i j k l
    _ = 3 * n ^ 2 * B ^ 2 := by
        have hc (c : ℝ) : ∑ x ∈ Finset.range n, (if x < n then c else 0) = n * c := by
          rw [Finset.sum_congr rfl fun x hx ↦
            (by simp [Finset.mem_range.1 hx] : (if x < n then c else 0) = c)]
          simp
        simp [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, hc]
        ring

/-- Markov's inequality in sequential form: nonnegative random variables whose means are
eventually bounded by a null sequence converge to zero in probability. -/
theorem tendsto_in_measure_zero_of_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hint : ∀ n, Integrable (X n) μ) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, ∫ ω, X n ω ∂μ ≤ u n) :
    TendstoInMeasure μ X atTop fun _ ↦ 0 := by
  rw [tendsto_in_measure_iff_measure_real_lt_dist]
  intro ε hε
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
    (by simpa using hu.div_const ε)
  filter_upwards [hle] with n hn
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hX0 n)) (hint n) ε
  calc μ.real {ω | ε < dist (X n ω) 0} ≤ μ.real {ω | ε ≤ X n ω} :=
        measureReal_mono fun ω (hω : ε < dist (X n ω) 0) ↦ by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (hX0 n ω)] at hω
          exact hω.le
    _ ≤ u n / ε := by
        rw [le_div_iff₀ hε, mul_comm]
        exact hmk.trans hn

/-- Chebyshev's inequality in sequential form: random variables whose second moments are
eventually bounded by a null sequence converge to zero in probability. -/
theorem tendsto_in_measure_zero_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hint : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, ∫ ω, X n ω ^ 2 ∂μ ≤ u n) :
    TendstoInMeasure μ X atTop fun _ ↦ 0 := by
  have h := tendsto_in_measure_zero_of_integral_le μ (fun n ω ↦ X n ω ^ 2)
    (fun n ω ↦ sq_nonneg _) hint u hu hle
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at h ⊢
  intro ε hε
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ measureReal_mono fun ω hω ↦ ?_)
    (h (ε ^ 2) (by positivity))
  simp only [Real.dist_eq, sub_zero, mem_ofPred_eq] at hω ⊢
  rw [abs_of_nonneg (sq_nonneg _)]
  calc ε ^ 2 < |X n ω| ^ 2 := pow_lt_pow_left₀ hω hε.le two_ne_zero
    _ = X n ω ^ 2 := sq_abs _

/-- A normalized degenerate `V`-statistic of a bounded kernel is negligible:
`√n n⁻² ∑_{i,j<n} g(Z i, Z j) → 0` in probability. -/
theorem tendsto_in_measure_sqrt_mul_sum_sum_div_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (g : E → E → ℝ) (hg : Measurable (Function.uncurry g)) (B : ℝ)
    (hB : ∀ z z', |g z z'| ≤ B) (h1 : ∀ z', ∫ z, g z z' ∂P = 0)
    (h2 : ∀ z, ∫ z', g z z' ∂P = 0) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n / n ^ 2 *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)) atTop fun _ ↦ 0 := by
  have hmeas (n : ℕ) : Measurable fun ω ↦ Real.sqrt n / n ^ 2 *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Z i ω) (Z j ω) := by
    have hgij (i j : ℕ) : Measurable fun ω ↦ g (Z i ω) (Z j ω) :=
      hg.comp ((hiid.1 i).prodMk (hiid.1 j))
    exact (Finset.measurable_fun_sum _ fun i _ ↦
      Finset.measurable_fun_sum _ fun j _ ↦ hgij i j).const_mul _
  have hbd (n : ℕ) (ω : Ω) : |∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)| ≤
      n * (n * B) :=
    calc _ ≤ ∑ i ∈ Finset.range n, |∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range n, B :=
          Finset.sum_le_sum fun i _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ ↦ hB (Z i ω) (Z j ω))
      _ = n * (n * B) := by simp
  refine tendsto_in_measure_zero_of_integral_sq_le μ _ (fun n ↦ ?_) (fun n ↦ 3 * B ^ 2 / n)
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (3 * B ^ 2)) ?_
  · refine Integrable.of_bound ((hmeas n).pow_const 2).aestronglyMeasurable
      ((Real.sqrt n / n ^ 2 * (n * (n * B))) ^ 2) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ _)]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hbd n ω)
      (by positivity)) 2
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hV := integral_sq_sum_sum_le_of_iid μ P Z hiid g hg B hB h1 h2 n
    simp_rw [mul_pow, div_pow]
    rw [integral_const_mul, Real.sq_sqrt hn'.le]
    calc (n : ℝ) / (n ^ 2) ^ 2 * ∫ ω, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          g (Z i ω) (Z j ω)) ^ 2 ∂μ ≤ n / (n ^ 2) ^ 2 * (3 * n ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 3 * B ^ 2 / n := by field_simp

/-- The quadratic remainder of the risk-set expansion is negligible: with
`Yᵢ = n⁻¹ #{j < n : x(Z i) ≤ x(Z j)}` and `y(s) = P(x ≥ s)`, the sum
`√n n⁻¹ ∑_{i<n} A(Z i) (Yᵢ - y(x(Z i)))² / (y(x(Z i))² Yᵢ)` tends to zero in probability when
`0 ≤ A ≤ 1` vanishes off `{x ≤ t}` and `y(t) > 0`. -/
theorem tendsto_in_measure_risk_set_remainder {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (x : E → ℝ) (hx : Measurable x) (A : E → ℝ) (hA0 : ∀ z, 0 ≤ A z) (hA1 : ∀ z, A z ≤ 1)
    (t : ℝ) (hAt : ∀ z, A z ≠ 0 → x z ≤ t) (y : ℝ → ℝ) (hy : ∀ s, y s = P.real {z | s ≤ x z})
    (hyt : 0 < y t) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n / n * ∑ i ∈ Finset.range n,
      A (Z i ω) * ((∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n -
        y (x (Z i ω))) ^ 2 / (y (x (Z i ω)) ^ 2 *
          ((∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n)))
      atTop fun _ ↦ 0 := by
  have hyanti : Antitone y := fun s s' hss' ↦ by
    rw [hy, hy]
    exact measureReal_mono fun z (hz : s' ≤ x z) ↦ (hss'.trans hz : s ≤ x z)
  have hy0 (s : ℝ) : 0 ≤ y s := by rw [hy]; exact measureReal_nonneg
  have hy1 (s : ℝ) : y s ≤ 1 := by rw [hy]; exact measureReal_le_one
  have hym : Measurable y := hyanti.measurable
  set g : E → E → ℝ := fun z z' ↦ (if x z ≤ x z' then 1 else 0) - y (x z) with hg
  have hgm : Measurable (Function.uncurry g) :=
    (Measurable.ite (measurableSet_le (hx.comp measurable_fst) (hx.comp measurable_snd))
      measurable_const measurable_const).sub ((hym.comp hx).comp measurable_fst)
  have hgB (z z' : E) : |g z z'| ≤ 1 := by
    simp only [hg]
    rw [abs_le]
    constructor <;> split_ifs <;> linarith [hy0 (x z), hy1 (x z)]
  have hg0 (z : E) : ∫ z', g z z' ∂P = 0 := by
    have hS : MeasurableSet {z' | x z ≤ x z'} := measurableSet_le measurable_const hx
    have : (fun z' ↦ (if x z ≤ x z' then (1 : ℝ) else 0)) = {z' | x z ≤ x z'}.indicator 1 := by
      funext z'; simp [Set.indicator_apply]
    have hI : Integrable (fun z' ↦ if x z ≤ x z' then (1 : ℝ) else 0) P := by
      rw [this]; exact (integrable_const (1 : ℝ)).indicator hS
    simp only [hg]
    rw [integral_sub hI (integrable_const _), this, integral_indicator_one hS, integral_const,
      ← hy]
    simp
  -- the risk-set fractions and their deviations
  set Y : ℕ → ℕ → Ω → ℝ := fun n i ω ↦
    (∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n with hYdef
  have hY01 (n i : ℕ) (ω : Ω) : 0 ≤ Y n i ω ∧ Y n i ω ≤ 1 := by
    have h0 : 0 ≤ ∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun j _ ↦ by split_ifs <;> norm_num
    have h1 : ∑ j ∈ Finset.range n, (if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) ≤ n := by
      calc _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ ↦ by split_ifs <;> norm_num
        _ = n := by simp
    refine ⟨div_nonneg h0 (Nat.cast_nonneg n), ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hYdef]
    exact div_le_one_of_le₀ h1 (Nat.cast_nonneg n)
  have hdev (n : ℕ) (hn : 0 < n) (i : ℕ) (ω : Ω) :
      Y n i ω - y (x (Z i ω)) = (∑ j ∈ Finset.range n, g (Z i ω) (Z j ω)) / n := by
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [hYdef, hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
  have hIm (i j : ℕ) : Measurable fun ω ↦ (if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hx.comp (hiid.1 i)) (hx.comp (hiid.1 j)))
      measurable_const measurable_const
  have hYm (n i : ℕ) : Measurable (Y n i) :=
    (Finset.measurable_fun_sum _ fun j _ ↦ hIm i j).div_const _
  have hDm (n i : ℕ) : Measurable fun ω ↦ (Y n i ω - y (x (Z i ω))) ^ 2 :=
    ((hYm n i).sub ((hym.comp hx).comp (hiid.1 i))).pow_const 2
  have hD1 (n i : ℕ) (ω : Ω) : (Y n i ω - y (x (Z i ω))) ^ 2 ≤ 1 := by
    have := hY01 n i ω
    have h1 : |Y n i ω - y (x (Z i ω))| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hy0 (x (Z i ω)), hy1 (x (Z i ω))]
    calc _ = |Y n i ω - y (x (Z i ω))| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 1 := one_pow 2
  have hDint (n i : ℕ) : Integrable (fun ω ↦ (Y n i ω - y (x (Z i ω))) ^ 2) μ :=
    Integrable.of_bound (hDm n i).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hD1 n i ω)
  set W : ℕ → Ω → ℝ := fun n ω ↦ Real.sqrt n / n * ∑ i ∈ Finset.range n,
    (Y n i ω - y (x (Z i ω))) ^ 2 with hW
  have hWlim : TendstoInMeasure μ W atTop fun _ ↦ 0 := by
    refine tendsto_in_measure_zero_of_integral_le μ W
      (fun n ω ↦ mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
      (fun n ↦ (integrable_finsetSum _ fun i _ ↦ hDint n i).const_mul _)
      (fun n ↦ (Real.sqrt n)⁻¹)
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hterm (i : ℕ) : ∫ ω, (Y n i ω - y (x (Z i ω))) ^ 2 ∂μ ≤ 1 / n := by
      simp_rw [hdev n hn i, div_pow]
      rw [integral_div]
      have := integral_sq_sum_le_of_iid μ P Z hiid g hgm 1 hgB hg0 i n
      rw [div_le_div_iff₀ (by positivity) hn']
      nlinarith
    simp only [hW]
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hDint n i]
    calc Real.sqrt n / n * ∑ i ∈ Finset.range n, ∫ ω, (Y n i ω - y (x (Z i ω))) ^ 2 ∂μ
        ≤ Real.sqrt n / n * ∑ _i ∈ Finset.range n, 1 / (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hterm i) (by positivity)
      _ = (Real.sqrt n)⁻¹ := by
          have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
          have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
          exact hs
  -- the at-risk fraction at `t`
  set Yt : ℕ → Ω → ℝ := fun n ω ↦
    (∑ j ∈ Finset.range n, if t ≤ x (Z j ω) then (1 : ℝ) else 0) / n with hYt
  have hU : TendstoInMeasure μ (fun n ω ↦ Yt n ω - y t) atTop fun _ ↦ 0 := by
    have hs : Measurable fun z ↦ (if t ≤ x z then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_const hx) measurable_const measurable_const
    have hS : MeasurableSet {z | t ≤ x z} := measurableSet_le measurable_const hx
    have hind : (fun z ↦ (if t ≤ x z then (1 : ℝ) else 0)) = {z | t ≤ x z}.indicator 1 := by
      funext z; simp [Set.indicator_apply]
    have hint : Integrable (fun z ↦ (if t ≤ x z then (1 : ℝ) else 0)) P := by
      rw [hind]; exact (integrable_const (1 : ℝ)).indicator hS
    have hmean : ∫ z, (if t ≤ x z then (1 : ℝ) else 0) ∂P = y t := by
      rw [hind, integral_indicator_one hS, ← hy]
    have hlln := tendsto_in_measure_sample_mean_of_iid μ P Z hiid _ hs hint
    rw [hmean] at hlln
    rw [tendstoInMeasure_iff_norm] at hlln ⊢
    intro ε hε
    refine (hlln ε hε).congr fun n ↦ ?_
    congr 1
    ext ω
    simp [hYt, div_eq_inv_mul]
  refine tendsto_in_measure_zero_of_abs_le μ (fun n ω ↦ 2 / y t ^ 3 * W n ω) _
    (fun n ω ↦ Yt n ω - y t) (half_pos hyt) ?_ (tendsto_in_measure_const_mul_zero μ W _ hWlim) hU
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine ae_of_all _ fun ω hω ↦ ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hYtω : y t / 2 < Yt n ω := by
    rw [abs_lt] at hω; linarith
  have hterm (i : ℕ) : 0 ≤ A (Z i ω) * (Y n i ω - y (x (Z i ω))) ^ 2 /
        (y (x (Z i ω)) ^ 2 * Y n i ω) ∧
      A (Z i ω) * (Y n i ω - y (x (Z i ω))) ^ 2 / (y (x (Z i ω)) ^ 2 * Y n i ω) ≤
        2 / y t ^ 3 * (Y n i ω - y (x (Z i ω))) ^ 2 := by
    refine ⟨div_nonneg (mul_nonneg (hA0 _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (hY01 n i ω).1), ?_⟩
    by_cases hAi : A (Z i ω) = 0
    · rw [hAi, zero_mul, zero_div]
      exact mul_nonneg (by positivity) (sq_nonneg _)
    have hxt := hAt _ hAi
    have hyi : y t ≤ y (x (Z i ω)) := hyanti hxt
    have hYi : Yt n ω ≤ Y n i ω := by
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ ↦ ?_) hn'.le
      split_ifs with h1 h2 <;> first | exact absurd (hxt.trans h1) h2 | norm_num
    have hden : y t ^ 2 * (y t / 2) ≤ y (x (Z i ω)) ^ 2 * Y n i ω :=
      mul_le_mul (pow_le_pow_left₀ hyt.le hyi 2) (hYtω.le.trans hYi) (by positivity)
        (by positivity)
    calc A (Z i ω) * (Y n i ω - y (x (Z i ω))) ^ 2 / (y (x (Z i ω)) ^ 2 * Y n i ω)
        ≤ 1 * (Y n i ω - y (x (Z i ω))) ^ 2 / (y t ^ 2 * (y t / 2)) :=
          div_le_div₀ (mul_nonneg zero_le_one (sq_nonneg _))
            (mul_le_mul_of_nonneg_right (hA1 _) (sq_nonneg _)) (by positivity) hden
      _ = 2 / y t ^ 3 * (Y n i ω - y (x (Z i ω))) ^ 2 := by
          field_simp
  have hsum0 := Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) ↦ (hterm i).1
  rw [abs_of_nonneg (mul_nonneg (by positivity) hsum0), abs_of_nonneg (mul_nonneg
    (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)))]
  simp only [hW]
  rw [mul_left_comm, Finset.mul_sum (s := Finset.range n) (a := 2 / y t ^ 3)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ (hterm i).2) (by positivity)

/-- The algebraic decomposition behind `tendsto_in_distribution_sqrt_mul_risk_set_sum_sub`: with
risk-set counts `Nᵢ = ∑_j I i j ≥ 1`, fractions `Yᵢ = Nᵢ / n` and `a = A / y²`, the normalized
estimator splits into a linear term, a quadratic remainder and a `V`-statistic, using
`1 / Y = 1 / y - (Y - y) / y² + (Y - y)² / (y² Y)`. -/
theorem risk_set_sum_decomposition (n : ℕ) (hn : 0 < n) (Av yv bv : ℕ → ℝ) (I : ℕ → ℕ → ℝ)
    (θ : ℝ) (hI0 : ∀ i j, 0 ≤ I i j) (hIi : ∀ i, I i i = 1)
    (hAy : ∀ i, Av i ≠ 0 → 0 < yv i) :
    Real.sqrt n * (∑ i ∈ Finset.range n, Av i / (∑ j ∈ Finset.range n, I i j) - θ) =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Av i / yv i - θ - bv i) +
        (Real.sqrt n / n * ∑ i ∈ Finset.range n, Av i * ((∑ j ∈ Finset.range n, I i j) / n -
          yv i) ^ 2 / (yv i ^ 2 * ((∑ j ∈ Finset.range n, I i j) / n)) +
        -1 * (Real.sqrt n / n ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (Av i / yv i ^ 2 * (I i j - yv i) - bv j))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Y : ℕ → ℝ := fun i ↦ (∑ j ∈ Finset.range n, I i j) / n with hY
  have hper (i : ℕ) (hi : i ∈ Finset.range n) : Av i / (∑ j ∈ Finset.range n, I i j) =
      (1 / n) * (Av i / yv i - Av i / yv i ^ 2 * (Y i - yv i) +
        Av i * (Y i - yv i) ^ 2 / (yv i ^ 2 * Y i)) := by
    by_cases hAi : Av i = 0
    · simp [hAi]
    have hyi := hAy i hAi
    have hN : 1 ≤ ∑ j ∈ Finset.range n, I i j := by
      have := Finset.single_le_sum (f := fun j ↦ I i j) (fun j _ ↦ hI0 i j) hi
      rwa [hIi] at this
    have hYi : 0 < Y i := div_pos (by linarith) hn'
    have hNY : ∑ j ∈ Finset.range n, I i j = n * Y i := by
      simp only [hY]; field_simp
    rw [hNY]
    field_simp
    ring
  have hM (i : ℕ) : Av i / yv i ^ 2 * (Y i - yv i) =
      (∑ j ∈ Finset.range n, (Av i / yv i ^ 2 * (I i j - yv i) - bv j)) / n +
        (∑ j ∈ Finset.range n, bv j) / n := by
    simp only [hY, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp_rw [hM]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  generalize ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    (Av i / yv i ^ 2 * (I i j - yv i) - bv j) = SH
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  generalize ∑ i ∈ Finset.range n, Av i / yv i = SA
  generalize ∑ i ∈ Finset.range n, bv i = SB
  generalize ∑ i ∈ Finset.range n, Av i * (Y i - yv i) ^ 2 / (yv i ^ 2 * Y i) = SR
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  generalize Real.sqrt n = s at hs hs0 ⊢
  rw [← hs]
  field_simp
  ring

/-- Central limit theorem for a risk-set estimator `∑_{i<n} A(Z i) / #{j < n : x(Z i) ≤ x(Z j)}`
of `θ = ∫ A / y(x) dP`, with `y(s) = P(x ≥ s)`, a weight `0 ≤ A ≤ 1` vanishing off `{x ≤ t}`
and `y(t) > 0`. The estimator is expanded around `y` to first order; the first-order term is a
`V`-statistic whose Hájek projection adds `-b` to the influence function, with
`b(z') = ∫ a(z) (1{x z ≤ x z'} - y(x z)) dP(z)` and `a = A / y(x)²`, and the degenerate part and
the quadratic remainder are negligible. -/
theorem tendsto_in_distribution_sqrt_mul_risk_set_sum_sub {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ Z P)
    (x : E → ℝ) (hx : Measurable x) (A : E → ℝ) (hA : Measurable A) (hA0 : ∀ z, 0 ≤ A z)
    (hA1 : ∀ z, A z ≤ 1) (t : ℝ) (hAt : ∀ z, A z ≠ 0 → x z ≤ t) (y : ℝ → ℝ)
    (hy : ∀ s, y s = P.real {z | s ≤ x z}) (hyt : 0 < y t) :
    let a : E → ℝ := fun z ↦ A z / y (x z) ^ 2
    let b : E → ℝ := fun z' ↦ ∫ z, a z * ((if x z ≤ x z' then 1 else 0) - y (x z)) ∂P
    let θ := ∫ z, A z / y (x z) ∂P
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n * (∑ i ∈ Finset.range n,
        A (Z i ω) / (((Finset.range n).filter fun j ↦ x (Z i ω) ≤ x (Z j ω)).card : ℝ) - θ))
      atTop id (fun _ ↦ μ) (gaussianReal 0 (∫ z, (A z / y (x z) - θ - b z) ^ 2 ∂P).toNNReal) := by
  intro a b θ
  have hyanti : Antitone y := fun s s' hss' ↦ by
    rw [hy, hy]
    exact measureReal_mono fun z (hz : s' ≤ x z) ↦ (hss'.trans hz : s ≤ x z)
  have hy0 (s : ℝ) : 0 ≤ y s := by rw [hy]; exact measureReal_nonneg
  have hy1 (s : ℝ) : y s ≤ 1 := by rw [hy]; exact measureReal_le_one
  have hym : Measurable y := hyanti.measurable
  have hyA (z : E) (hz : A z ≠ 0) : y t ≤ y (x z) := hyanti (hAt z hz)
  set g : E → E → ℝ := fun z z' ↦ (if x z ≤ x z' then 1 else 0) - y (x z) with hg
  have hgm : Measurable (Function.uncurry g) :=
    (Measurable.ite (measurableSet_le (hx.comp measurable_fst) (hx.comp measurable_snd))
      measurable_const measurable_const).sub ((hym.comp hx).comp measurable_fst)
  have hgB (z z' : E) : |g z z'| ≤ 1 := by
    simp only [hg]
    rw [abs_le]
    constructor <;> split_ifs <;> linarith [hy0 (x z), hy1 (x z)]
  have hg0 (z : E) : ∫ z', g z z' ∂P = 0 := by
    have hS : MeasurableSet {z' | x z ≤ x z'} := measurableSet_le measurable_const hx
    have hind : (fun z' ↦ (if x z ≤ x z' then (1 : ℝ) else 0)) =
        {z' | x z ≤ x z'}.indicator 1 := by
      funext z'; simp [Set.indicator_apply]
    have hI : Integrable (fun z' ↦ if x z ≤ x z' then (1 : ℝ) else 0) P := by
      rw [hind]; exact (integrable_const (1 : ℝ)).indicator hS
    simp only [hg]
    rw [integral_sub hI (integrable_const _), hind, integral_indicator_one hS, integral_const,
      ← hy]
    simp
  -- bounds on the weights
  set c := 1 / y t ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have ha_bd (z : E) : |a z| ≤ c := by
    by_cases hz : A z = 0
    · simp [a, hz, hc0]
    have h1 := hyA z hz
    rw [abs_of_nonneg (div_nonneg (hA0 z) (sq_nonneg _))]
    exact div_le_div₀ zero_le_one (hA1 z) (by positivity) (pow_le_pow_left₀ hyt.le h1 2)
  have ham : Measurable a := hA.div ((hym.comp hx).pow_const 2)
  set F : E → E → ℝ := fun z z' ↦ a z * g z z' with hF
  have hFm : Measurable (Function.uncurry F) := (ham.comp measurable_fst).mul hgm
  have hFB (z z' : E) : |F z z'| ≤ c := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hgB z z')).trans (ha_bd z)
  have hbm : Measurable b :=
    (StronglyMeasurable.integral_prod_left (μ := P) (f := F) hFm.stronglyMeasurable).measurable
  have hb_bd (z' : E) : |b z'| ≤ c := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun z ↦ F z z')
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hFB z z')
    simpa [Real.norm_eq_abs] using this
  have hFint : Integrable (Function.uncurry F) (P.prod P) :=
    Integrable.of_bound hFm.aestronglyMeasurable c
      (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hFB p.1 p.2)
  have hb0 : ∫ z', b z' ∂P = 0 := by
    have := integral_integral_swap (μ := P) (ν := P) (f := F) hFint
    simp only [b]
    rw [← this]
    simp [hF, integral_const_mul, hg0]
  -- the degenerate kernel
  set H : E → E → ℝ := fun z z' ↦ F z z' - b z' with hH
  have hHm : Measurable (Function.uncurry H) := hFm.sub (hbm.comp measurable_snd)
  have hHB (z z' : E) : |H z z'| ≤ 2 * c :=
    (abs_sub _ _).trans (by linarith [hFB z z', hb_bd z'])
  have hFi1 (z' : E) : Integrable (fun z ↦ F z z') P :=
    Integrable.of_bound (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable c
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hFB z z')
  have hFi2 (z : E) : Integrable (fun z' ↦ F z z') P :=
    Integrable.of_bound (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable c
      (ae_of_all _ fun z' ↦ by rw [Real.norm_eq_abs]; exact hFB z z')
  have hbint : Integrable b P := Integrable.of_bound hbm.aestronglyMeasurable c
    (ae_of_all _ fun z' ↦ by rw [Real.norm_eq_abs]; exact hb_bd z')
  have hH1 (z' : E) : ∫ z, H z z' ∂P = 0 := by
    simp only [hH]
    rw [integral_sub (hFi1 z') (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_eq_zero.2 rfl
  have hH2 (z : E) : ∫ z', H z z' ∂P = 0 := by
    simp only [hH]
    rw [integral_sub (hFi2 z) hbint, hb0]
    simp [hF, integral_const_mul, hg0]
  -- the influence function
  set ψ : E → ℝ := fun z ↦ A z / y (x z) - θ - b z with hψ
  have hAy_bd (z : E) : |A z / y (x z)| ≤ 1 / y t := by
    by_cases hz : A z = 0
    · simp [hz, hyt.le]
    rw [abs_of_nonneg (div_nonneg (hA0 z) (hy0 _))]
    exact div_le_div₀ zero_le_one (hA1 z) hyt (hyA z hz)
  have hAym : Measurable fun z ↦ A z / y (x z) := hA.div (hym.comp hx)
  have hAyint : Integrable (fun z ↦ A z / y (x z)) P :=
    Integrable.of_bound hAym.aestronglyMeasurable (1 / y t)
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hAy_bd z)
  have hψm : Measurable ψ := (hAym.sub_const θ).sub hbm
  have hψ2 : MemLp ψ 2 P := by
    refine MemLp.of_bound hψm.aestronglyMeasurable (1 / y t + |θ| + c)
      (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs]
    calc |ψ z| ≤ |A z / y (x z) - θ| + |b z| := abs_sub _ _
      _ ≤ (|A z / y (x z)| + |θ|) + |b z| := by gcongr; exact abs_sub _ _
      _ ≤ 1 / y t + |θ| + c := by linarith [hAy_bd z, hb_bd z]
  have hψ0 : ∫ z, ψ z ∂P = 0 := by
    simp only [hψ]
    rw [integral_sub (f := fun z ↦ A z / y (x z) - θ) (hAyint.sub (integrable_const θ)) hbint,
      integral_sub hAyint (integrable_const θ), hb0, integral_const]
    simp [θ]
  have hL := tendsto_in_distribution_inv_sqrt_mul_sum_of_iid μ P Z hiid ψ hψm hψ2 hψ0
  have hV := tendsto_in_measure_sqrt_mul_sum_sum_div_of_iid μ P Z hiid H hHm (2 * c) hHB hH1 hH2
  have hQ := tendsto_in_measure_risk_set_remainder μ P Z hiid x hx A hA0 hA1 t hAt y hy hyt
  have hR := tendsto_in_measure_add_zero μ _ _ hQ (tendsto_in_measure_const_mul_zero μ _ (-1) hV)
  have hZm := hiid.1
  have hIm (i j : ℕ) : Measurable fun ω ↦ (if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hx.comp (hZm i)) (hx.comp (hZm j)))
      measurable_const measurable_const
  have hYm (n i : ℕ) : Measurable fun ω ↦
      (∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n :=
    (Finset.measurable_fun_sum _ fun j _ ↦ hIm i j).div_const _
  have hyZ (i : ℕ) : Measurable fun ω ↦ y (x (Z i ω)) := (hym.comp hx).comp (hZm i)
  have hHij (i j : ℕ) : Measurable fun ω ↦ H (Z i ω) (Z j ω) := by
    have h := hHm.comp ((hZm i).prodMk (hZm j))
    simp only [Function.comp_def, Function.uncurry_apply_pair] at h
    exact h
  have hQm (n : ℕ) : Measurable fun ω ↦ Real.sqrt n / n * ∑ i ∈ Finset.range n,
      A (Z i ω) * ((∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n -
        y (x (Z i ω))) ^ 2 / (y (x (Z i ω)) ^ 2 *
          ((∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0) / n)) :=
    (Finset.measurable_fun_sum _ fun i _ ↦
      ((hA.comp (hZm i)).mul (((hYm n i).sub (hyZ i)).pow_const 2)).div
        (((hyZ i).pow_const 2).mul (hYm n i))).const_mul _
  have hVm (n : ℕ) : Measurable fun ω ↦ -1 * (Real.sqrt n / n ^ 2 *
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, H (Z i ω) (Z j ω)) :=
    ((Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun j _ ↦
        hHij i j).const_mul _).const_mul _
  have hsum := hL.add_of_tendstoInMeasure_const hR fun n ↦ ((hQm n).add (hVm n)).aemeasurable
  have hlim : (fun ω : ℝ ↦ id ω + (0 : ℝ)) = id := by funext ω; simp
  rw [hlim] at hsum
  convert hsum using 1
  funext n ω
  simp only [Pi.add_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcard (i : ℕ) : (((Finset.range n).filter fun j ↦ x (Z i ω) ≤ x (Z j ω)).card : ℝ) =
      ∑ j ∈ Finset.range n, if x (Z i ω) ≤ x (Z j ω) then (1 : ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  simp_rw [hcard]
  exact risk_set_sum_decomposition n hn (fun i ↦ A (Z i ω)) (fun i ↦ y (x (Z i ω)))
    (fun j ↦ b (Z j ω)) (fun i j ↦ if x (Z i ω) ≤ x (Z j ω) then 1 else 0) θ
    (fun i j ↦ by split_ifs <;> norm_num) (fun i ↦ by simp)
    (fun i hAi ↦ hyt.trans_le (hyA _ hAi))

end CKSD
