module

public import CKSD.Learning.PrivateEstimation.Mechanisms

/-!
# Two-point lower bounds for central private mean estimation

Bernoulli alternatives, testing bounds, and privacy contraction yield a lower bound for the
central mean risk. Divergence inequalities use Statlib. Source: GAPS 107.66.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-! ### Two-point lower bounds for the central mean risk -/

/-- Integrals against the Bernoulli law `Ber(1, 0, p)` on the real line. -/
theorem integral_bernoulliMeasure_one_zero (p : unitInterval) (f : ℝ → ℝ) :
    ∫ x, f x ∂(Ber((1 : ℝ), 0, p)) = p * f 1 + (1 - p) * f 0 := by
  rw [bernoulliMeasure_def, integral_add_measure, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac]
  · simp [NNReal.smul_def, unitInterval.coe_symm_eq]
  · exact (integrable_dirac (by simp)).smul_measure_nnreal
  · exact (integrable_dirac (by simp)).smul_measure_nnreal

/-- The Bernoulli law `Ber(1, 0, p)` has mean `p`. -/
theorem integral_id_bernoulliMeasure_one_zero (p : unitInterval) :
    ∫ x, x ∂(Ber((1 : ℝ), 0, p)) = p := by
  rw [integral_bernoulliMeasure_one_zero p fun x ↦ x]
  ring

/-- The Bernoulli law `Ber(1, 0, p)` is supported by `[-1,1]`. -/
theorem bernoulliMeasure_one_zero_compl_Icc (p : unitInterval) :
    (Ber((1 : ℝ), 0, p)) (Icc (-1) 1)ᶜ = 0 :=
  bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_Icc.compl
    (by simp) (by simp)

/-- Group privacy: a mechanism that is `ε`-differentially private for Hamming neighbours
changes the probability of an event by at most the factor `exp(ε k)` between data sets that
differ in at most `k` coordinates. -/
theorem kernel_apply_le_exp_mul_card {n : ℕ} {M : Kernel (Fin n → ℝ) ℝ} {ε : ℝ}
    (hM : IsDifferentiallyPrivate IsHammingNeighbor ε 0 M) {B : Set ℝ} (hB : MeasurableSet B) :
    ∀ (s : Finset (Fin n)) (d d' : Fin n → ℝ), (∀ i ∉ s, d i = d' i) →
      M d B ≤ ENNReal.ofReal (Real.exp (ε * s.card)) * M d' B := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro d d' h
    have : d = d' := funext fun i ↦ h i (Finset.notMem_empty i)
    simp [this]
  | insert a s ha ih =>
    intro d d' h
    set d'' := Function.update d a (d' a)
    have hnb : IsHammingNeighbor d d'' := by
      unfold IsHammingNeighbor
      refine (Finset.card_le_card (t := {a}) fun i hi ↦ ?_).trans (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hia
      rw [Finset.mem_singleton] at hia
      exact hi (by simp [d'', Function.update_of_ne hia])
    have h1 := hM d d'' hnb B hB
    have h2 := ih d'' d' fun i hi ↦ by
      by_cases hia : i = a
      · subst hia; simp [d'']
      · simp only [d'', Function.update_of_ne hia]
        exact h i (by simp [hia, hi])
    rw [ENNReal.ofReal_zero, add_zero] at h1
    calc M d B ≤ ENNReal.ofReal (Real.exp ε) * M d'' B := h1
      _ ≤ ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (Real.exp (ε * s.card)) * M d' B) := by
        gcongr
      _ = ENNReal.ofReal (Real.exp (ε * (insert a s).card)) * M d' B := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          Finset.card_insert_of_notMem ha]
        push_cast
        ring_nf

/-- A lower bound for the central mean risk on a set of releases far from the mean. -/
theorem ofReal_mul_comp_le_centralMeanRisk {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ)
    (P : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) {r : ℝ}
    (hr : ∀ y ∈ B, r ≤ (y - ∫ x, x ∂P) ^ 2) :
    ENNReal.ofReal r * (M ∘ₘ Measure.pi fun _ : Fin n ↦ P) B ≤ centralMeanRisk M P := by
  rw [Measure.bind_apply hB M.aemeasurable, ← lintegral_const_mul _ (M.measurable_coe hB)]
  unfold centralMeanRisk
  refine lintegral_mono fun d ↦ ?_
  rw [← lintegral_indicator_const hB]
  refine lintegral_mono fun y ↦ ?_
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (hr y hy)
  · rw [indicator_of_notMem hy]
    exact zero_le

/-- Le Cam's two-point bound for Bernoulli laws `Ber(1, 0, a)` and `Ber(1, 0, b)` with
`a < b`: the sum of the two risks is at least `((b - a)/2)²` times the sum of the error
probabilities of the test that rejects `a` when the release exceeds `(a + b)/2`. -/
theorem centralMeanRisk_add_centralMeanRisk_ge {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ)
    {a b : unitInterval} (hab : (a : ℝ) < b) :
    ENNReal.ofReal (((b - a : ℝ) / 2) ^ 2) *
        ((M ∘ₘ Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)) {y | ((a + b : ℝ)) / 2 ≤ y} +
          (M ∘ₘ Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)) {y | ((a + b : ℝ)) / 2 ≤ y}ᶜ) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
  have hA : MeasurableSet {y : ℝ | ((a + b : ℝ)) / 2 ≤ y} := measurableSet_Ici
  rw [mul_add]
  gcongr
  · refine ofReal_mul_comp_le_centralMeanRisk M _ hA fun y hy ↦ ?_
    rw [integral_id_bernoulliMeasure_one_zero]
    simp only [Set.mem_ofPred_eq] at hy
    nlinarith
  · refine ofReal_mul_comp_le_centralMeanRisk M _ hA.compl fun y hy ↦ ?_
    rw [integral_id_bernoulliMeasure_one_zero]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
    nlinarith

/-- The binary Kullback–Leibler divergence is at most the χ² divergence
`(p - q)² / (q (1 - q))`. -/
theorem klBerReal_le_sq_div {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    InformationTheory.klBerReal p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  rw [InformationTheory.klBerReal_apply]
  have h1 : p * Real.log (p / q) ≤ p * (p / q - 1) := by
    rcases eq_or_lt_of_le hp0 with rfl | hp
    · simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hp hq0)) hp0
  have h2 : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ (1 - p) * ((1 - p) / (1 - q) - 1) := by
    rcases eq_or_lt_of_le (sub_nonneg.mpr hp1) with h | hp
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hp (by linarith))) hp.le
  have hq1' : 0 < 1 - q := by linarith
  have h3 : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) =
      (p - q) ^ 2 / (q * (1 - q)) := by
    field_simp
    ring
  linarith

/-- If a sum is at least `r`, one of the two terms is at least `r / 2`. -/
theorem ofReal_half_le_or_of_ofReal_le_add {x y : ℝ≥0∞} {r : ℝ} (h : ENNReal.ofReal r ≤ x + y) :
    ENNReal.ofReal (r / 2) ≤ x ∨ ENNReal.ofReal (r / 2) ≤ y := by
  rcases le_or_gt r 0 with hr | hr
  · left
    rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact zero_le
  by_contra hc
  push Not at hc
  have := ENNReal.add_lt_add hc.1 hc.2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at this
  exact absurd h (not_le.mpr this)

/-- The event bound from the total variation distance: `2 (Q A - Q' A) ≤ tvDist Q Q'`. -/
theorem two_mul_measureReal_sub_le_tvDist {Q Q' : Measure ℝ} [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] {A : Set ℝ} (hA : MeasurableSet A) :
    2 * (Q.real A - Q'.real A) ≤ tvDist Q Q' := by
  have hf : ∀ (ξ : Measure ℝ) [IsProbabilityMeasure ξ],
      ∫ y, (2 * A.indicator (1 : ℝ → ℝ) y - 1) ∂ξ = 2 * ξ.real A - 1 := by
    intro ξ _
    have hI : Integrable (A.indicator (1 : ℝ → ℝ)) ξ := (integrable_const (1 : ℝ)).indicator hA
    rw [integral_sub (hI.const_mul 2) (integrable_const 1), integral_const_mul,
      integral_indicator_one hA]
    simp
  have h := integral_sub_integral_le_tvDist (μ := Q) (ν := Q')
    (f := fun y ↦ 2 * A.indicator (1 : ℝ → ℝ) y - 1)
    ((((measurable_const.indicator hA).const_mul 2).sub_const 1).aestronglyMeasurable)
    (ae_of_all _ fun y ↦ by
      by_cases hy : y ∈ A
      · simp [indicator_of_mem hy]; norm_num
      · simp [indicator_of_notMem hy])
  rw [hf Q, hf Q'] at h
  linarith

/-- The non-private part of the central lower bound: for every mechanism some Bernoulli law
`Ber(1, 0, p)` has mean squared error at least `1 / (192 n)`. The two laws `Ber(1/2)` and
`Ber(1/2 + δ)` with `δ = 1/(2√n)` have product laws at Kullback–Leibler divergence at most `1`
(Statlib's `klDiv_pi_const` and `klDiv_bernoulliMeasure_eq_klBerReal`), so by the
Bretagnolle–Huber inequality (Statlib's `exp_neg_klDiv_le_two_sub_tvDist`) and data processing
(`tvDist_comp_le`) no test separates them well. -/
theorem exists_bernoulli_centralMeanRisk_ge_inv {n : ℕ} (hn : 0 < n)
    (M : Kernel (Fin n → ℝ) ℝ) [IsMarkovKernel M] :
    ∃ p : unitInterval,
      ENNReal.ofReal (1 / (192 * n)) ≤ centralMeanRisk M (Ber((1 : ℝ), 0, p)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set δ : ℝ := 1 / (2 * Real.sqrt n) with hδ_def
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnr
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ2 : δ ^ 2 = 1 / (4 * n) := by
    rw [hδ_def, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  set a : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  set b : unitInterval := ⟨1 / 2 + δ, by positivity, by linarith⟩
  have ha : (a : ℝ) = 1 / 2 := rfl
  have hb : (b : ℝ) = 1 / 2 + δ := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; linarith
  set μa := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- Kullback–Leibler divergence of the product laws
  have hkl : InformationTheory.klBerReal b a ≤ 1 / n := by
    refine (klBerReal_le_sq_div b.2.1 b.2.2 (by rw [ha]; norm_num) (by rw [ha]; norm_num)).trans
      (le_of_eq ?_)
    rw [ha, hb, show ((1 / 2 + δ - 1 / 2 : ℝ)) ^ 2 / (1 / 2 * (1 - 1 / 2)) = 4 * δ ^ 2 by ring,
      hδ2]
    field_simp
  have hKL : InformationTheory.klDiv μb μa =
      n * ENNReal.ofReal (InformationTheory.klBerReal b a) := by
    rw [klDiv_pi_const, Fintype.card_fin,
      InformationTheory.klDiv_bernoulliMeasure_eq_klBerReal (by norm_num : (1 : ℝ) ≠ 0) b]
    · intro h; have := congrArg Subtype.val h; rw [ha] at this; norm_num at this
    · intro h; have := congrArg Subtype.val h; rw [ha] at this; norm_num at this
  have hKLne : InformationTheory.klDiv μb μa ≠ ⊤ := by
    rw [hKL]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top
  have hKLr : (InformationTheory.klDiv μb μa).toReal ≤ 1 := by
    rw [hKL, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (InformationTheory.klBerReal_nonneg b.2.1 b.2.2
        (by rw [ha]; norm_num) (by rw [ha]; norm_num))]
    calc (n : ℝ) * InformationTheory.klBerReal b a ≤ n * (1 / n) :=
          mul_le_mul_of_nonneg_left hkl (by positivity)
      _ = 1 := by field_simp
  have hBH := exp_neg_klDiv_le_two_sub_tvDist μb μa hKLne
  have hexp : Real.exp (-1) ≤ Real.exp (-(InformationTheory.klDiv μb μa).toReal) :=
    Real.exp_le_exp.mpr (by linarith)
  have hTV := tvDist_comp_le μb μa M
  have hev := two_mul_measureReal_sub_le_tvDist (Q := M ∘ₘ μb) (Q' := M ∘ₘ μa) hA
  have he3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hcompl : (M ∘ₘ μb).real Aᶜ = 1 - (M ∘ₘ μb).real A := by
    rw [measureReal_compl hA, probReal_univ]
  have htest : 1 / 6 ≤ (M ∘ₘ μa).real A + (M ∘ₘ μb).real Aᶜ := by
    rw [hcompl]; linarith
  have hLC := centralMeanRisk_add_centralMeanRisk_ge M hab (n := n)
  have hsum : ENNReal.ofReal (1 / (96 * n)) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ hLC
    rw [← ofReal_measureReal (measure_ne_top (M ∘ₘ μa) A),
      ← ofReal_measureReal (measure_ne_top (M ∘ₘ μb) Aᶜ),
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsq' : ((b - a : ℝ) / 2) ^ 2 = 1 / (16 * n) := by
      rw [ha, hb, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, div_pow, hδ2]; ring
    rw [hsq']
    calc 1 / (96 * (n : ℝ)) = 1 / (16 * n) * (1 / 6) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (by positivity)
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, by convert h using 2; field_simp; ring⟩
  · exact ⟨b, by convert h using 2; field_simp; ring⟩

/-- The exponential moment of the number of nonzero coordinates under the product of
Bernoulli laws: `∫ exp(ε #{i | dᵢ ≠ 0}) = (1 + q (e^ε - 1))ⁿ`, written as a lower integral. -/
theorem lintegral_exp_mul_card_ne_zero {n : ℕ} (q : unitInterval) (ε : ℝ) :
    ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ)))
        ∂(Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, q)) =
      ENNReal.ofReal ((1 + q * (Real.exp ε - 1)) ^ n) := by
  set g : ℝ → ℝ := fun x ↦ Real.exp (ε * if x ≠ 0 then 1 else 0)
  have hg : Measurable g :=
    Real.measurable_exp.comp (measurable_const.mul (Measurable.ite
      (measurableSet_singleton 0).compl measurable_const measurable_const))
  have hprod : ∀ d : Fin n → ℝ,
      Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ)) = ∏ i, g (d i) := by
    intro d
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp only [g]
    split_ifs <;> simp
  simp_rw [hprod]
  have hgb : ∀ x, ‖g x‖ ≤ Real.exp |ε| := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    split_ifs <;> simp [le_abs_self, abs_nonneg]
  have hint : Integrable (fun d : Fin n → ℝ ↦ ∏ i, g (d i))
      (Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, q)) := by
    refine Integrable.of_bound (C := Real.exp |ε| ^ n)
      ((Finset.measurable_prod _ fun i _ ↦ hg.comp (measurable_pi_apply i)).aestronglyMeasurable)
      (ae_of_all _ fun d ↦ ?_)
    rw [norm_prod]
    calc ∏ i, ‖g (d i)‖ ≤ ∏ _i : Fin n, Real.exp |ε| :=
          Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦ hgb _
      _ = _ := by simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun d ↦ Finset.prod_nonneg fun i _ ↦ (Real.exp_pos _).le),
    integral_fintype_prod_eq_pow, integral_bernoulliMeasure_one_zero]
  simp only [g, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, mul_one, not_true_eq_false,
    mul_zero, Real.exp_zero, Fintype.card_fin]
  congr 2
  ring

/-- The exponential moment bound `(1 + q (e^ε - 1))ⁿ ≤ 9` when `q ε ≤ 1/n` and `ε ≤ 1`. -/
theorem one_add_mul_exp_sub_one_pow_le_nine {n : ℕ} (hn : 0 < n) {ε q : ℝ} (hε : ε ∈ Ioc 0 1)
    (hq0 : 0 ≤ q) (hq : q * ε ≤ 1 / n) : (1 + q * (Real.exp ε - 1)) ^ n ≤ 9 := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : Real.exp ε - 1 ≤ 2 * ε := by
    have := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε.1]; exact hε.2)
    rw [abs_of_pos hε.1] at this
    exact (le_abs_self _).trans this
  have hx0 : 0 ≤ q * (Real.exp ε - 1) :=
    mul_nonneg hq0 (by linarith [Real.add_one_le_exp ε, hε.1])
  have hx : n * (q * (Real.exp ε - 1)) ≤ 2 := by
    have : q * (Real.exp ε - 1) ≤ 2 * (q * ε) := by nlinarith
    calc (n : ℝ) * (q * (Real.exp ε - 1)) ≤ n * (2 * (q * ε)) :=
          mul_le_mul_of_nonneg_left this hnr.le
      _ ≤ n * (2 * (1 / n)) := by gcongr
      _ = 2 := by field_simp
  calc (1 + q * (Real.exp ε - 1)) ^ n ≤ Real.exp (q * (Real.exp ε - 1)) ^ n := by
        gcongr
        linarith [Real.add_one_le_exp (q * (Real.exp ε - 1))]
    _ = Real.exp (n * (q * (Real.exp ε - 1))) := (Real.exp_nat_mul _ n).symm
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hx
    _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 9 := by
        have := Real.exp_one_lt_d9
        have h0 := Real.exp_pos 1
        nlinarith

/-- The private part of the central lower bound: for an `ε`-differentially private mechanism
some Bernoulli law `Ber(1, 0, p)` has mean squared error at least `min(1, 1/(nε))² / 72`. The
two laws are `Ber(1, 0, 0) = δ₀` and `Ber(1, 0, q)` with `q = min(1, 1/(nε))`; by group
privacy the release law under the second is at most `(1 + q(e^ε - 1))ⁿ ≤ 9` times the release
law under the first. -/
theorem exists_bernoulli_centralMeanRisk_ge_private {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1) (M : Kernel (Fin n → ℝ) ℝ) [IsMarkovKernel M]
    (hM : IsDifferentiallyPrivate IsHammingNeighbor ε 0 M) :
    ∃ p : unitInterval, ENNReal.ofReal (min 1 (1 / (n * ε)) ^ 2 / 72) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, p)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set q : ℝ := min 1 (1 / (n * ε)) with hq_def
  have hq0 : 0 < q := lt_min one_pos (by have := hε.1; positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqε : q * ε ≤ 1 / n := by
    calc q * ε ≤ 1 / (n * ε) * ε := mul_le_mul_of_nonneg_right (min_le_right _ _) hε.1.le
      _ = 1 / n := by field_simp [hε.1.ne']
  set a : unitInterval := 0
  set b : unitInterval := ⟨q, hq0.le, hq1⟩
  have ha : (a : ℝ) = 0 := rfl
  have hb : (b : ℝ) = q := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; exact hq0
  set μa := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- the release law under `δ₀`
  have hae : ∀ᵐ d ∂μa, d = 0 := by
    have h : ∀ i, ∀ᵐ d ∂μa, d i = 0 := by
      intro i
      have hmap := (measurePreserving_eval (fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)) i).map_eq
      have h0 : ∀ᵐ x ∂(Ber((1 : ℝ), 0, a)), x = 0 := by
        rw [show a = 0 from rfl, bernoulliMeasure_zero]
        exact (ae_dirac_iff (measurableSet_singleton 0)).mpr rfl
      rw [← hmap] at h0
      exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h0
    exact (ae_all_iff.mpr h).mono fun d hd ↦ funext hd
  have hQa : (M ∘ₘ μa) A = M 0 A := by
    rw [Measure.bind_apply hA M.aemeasurable,
      lintegral_congr_ae (g := fun _ ↦ M 0 A) (hae.mono fun d hd ↦ by rw [hd]), lintegral_const,
      measure_univ,
      mul_one]
  -- group privacy
  have hgroup : ∀ d, M d A ≤
      ENNReal.ofReal (Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ))) *
        M 0 A := fun d ↦
    kernel_apply_le_exp_mul_card hM hA _ d 0 fun i hi ↦ by simpa using hi
  have hQb : (M ∘ₘ μb) A ≤ 9 * M 0 A := by
    rw [Measure.bind_apply hA M.aemeasurable]
    calc ∫⁻ d, M d A ∂μb ≤ ∫⁻ d, ENNReal.ofReal (Real.exp
          (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ))) * M 0 A ∂μb :=
          lintegral_mono hgroup
      _ = ENNReal.ofReal ((1 + q * (Real.exp ε - 1)) ^ n) * M 0 A := by
          rw [lintegral_mul_const' _ _ (measure_ne_top _ _), lintegral_exp_mul_card_ne_zero]
      _ ≤ 9 * M 0 A := by
          gcongr
          rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num]
          exact ENNReal.ofReal_le_ofReal
            (one_add_mul_exp_sub_one_pow_le_nine hn hε hq0.le hqε)
  have htest : ENNReal.ofReal (1 / 9) ≤ (M ∘ₘ μa) A + (M ∘ₘ μb) Aᶜ := by
    have h1 : (M ∘ₘ μb) A + (M ∘ₘ μb) Aᶜ = 1 := by
      rw [measure_add_measure_compl hA, measure_univ]
    have h2 : 1 ≤ 9 * ((M ∘ₘ μa) A + (M ∘ₘ μb) Aᶜ) := by
      rw [← h1, hQa, mul_add]
      gcongr
      calc (M ∘ₘ μb) Aᶜ = 1 * (M ∘ₘ μb) Aᶜ := (one_mul _).symm
        _ ≤ 9 * (M ∘ₘ μb) Aᶜ := by gcongr; norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
      show ENNReal.ofReal 9 = 9 by norm_num]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm]
    exact h2
  have hLC := centralMeanRisk_add_centralMeanRisk_ge M hab (n := n)
  have hsum : ENNReal.ofReal (q ^ 2 / 36) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ hLC
    calc ENNReal.ofReal (q ^ 2 / 36) = ENNReal.ofReal (((b - a : ℝ) / 2) ^ 2) *
          ENNReal.ofReal (1 / 9) := by
          rw [← ENNReal.ofReal_mul (by positivity), ha, hb]; congr 1; ring
      _ ≤ _ := by gcongr
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, by convert h using 2; ring⟩
  · exact ⟨b, by convert h using 2; ring⟩

/-- GAPS 107.66, central minimax lower bound: there is an absolute `c > 0` such that for
`0 < ε ≤ 1` every `ε`-differentially private mechanism has mean squared error at least
`c min(1, 1/n + 1/(nε)²)` for the mean of some law on `[-1,1]`. -/
theorem exists_centralMeanRisk_ge :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ M : Kernel (Fin n → ℝ) ℝ,
      IsMarkovKernel M → IsDifferentiallyPrivate IsHammingNeighbor ε 0 M →
      ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
        ENNReal.ofReal (c * min 1 (1 / n + 1 / (n * ε) ^ 2)) ≤ centralMeanRisk M P := by
  refine ⟨1 / 400, by norm_num, ?_⟩
  intro n hn ε hε M hMk hM
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set q : ℝ := min 1 (1 / (n * ε)) with hq_def
  have hz : 0 ≤ 1 / (n * ε) := by have := hε.1; positivity
  have hq0 : 0 ≤ q := le_min zero_le_one hz
  have hqsq : min 1 (1 / (n * ε) ^ 2) = q ^ 2 := by
    rw [hq_def, ← one_div_pow]
    rcases le_total (1 / (n * ε)) 1 with h | h
    · rw [min_eq_right h, min_eq_right (pow_le_one₀ hz h)]
    · rw [min_eq_left h, min_eq_left (one_le_pow₀ h), one_pow]
  have hmin : min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / n + q ^ 2 := by
    rw [← hqsq]
    have h1 : 0 ≤ 1 / (n : ℝ) := by positivity
    have h2 : 0 ≤ 1 / (n * ε) ^ 2 := by positivity
    rcases le_total (1 / (n * ε) ^ 2) 1 with h | h
    · rw [min_eq_right h]; exact min_le_right _ _
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
  by_cases h : q ^ 2 ≤ 1 / n
  · obtain ⟨p, hp⟩ := exists_bernoulli_centralMeanRisk_ge_inv hn M
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p,
      le_trans (ENNReal.ofReal_le_ofReal ?_) hp⟩
    calc 1 / 400 * min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / 400 * (1 / (n : ℝ) + 1 / n) := by
          gcongr; linarith
      _ ≤ 1 / (192 * n) := by
          rw [show 1 / 400 * (1 / (n : ℝ) + 1 / n) = 1 / (200 * n) by field_simp; ring]
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · push Not at h
    obtain ⟨p, hp⟩ := exists_bernoulli_centralMeanRisk_ge_private hn hε M hM
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p,
      le_trans (ENNReal.ofReal_le_ofReal ?_) hp⟩
    rw [← hq_def]
    calc 1 / 400 * min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / 400 * (q ^ 2 + q ^ 2) := by
          gcongr; linarith
      _ ≤ q ^ 2 / 72 := by nlinarith [sq_nonneg q]

end CKSD
