module

public import CKSD.Nonparametric.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.MeanInequalitiesPow
public import Statlib.Divergence.KullbackLeibler.Event
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
public import Mathlib.InformationTheory.Hamming


/-!
# Testing lower bounds for minimax risk

The classical reductions of estimation to testing, stated for an estimator `T` of a parameter
in a metric space and losses of the form `P(dist(T, θ) ≥ s)`. Total variation is in the
statistical normalization `sup_A |P(A) - Q(A)|` (`CKSD.totalVariationDistance`).

## Main results

* `CKSD.one_sub_total_variation_distance_div_two_le_max_measure_real` (Le Cam's two-point
  method): for `2s`-separated parameters, `max_i P_i(dist(T, θ_i) ≥ s) ≥ (1 - TV(P₀, P₁)) / 2`.
* `CKSD.measure_real_mul_neg_log_sub_log_two_le_kl_div`: the binary data-processing bound
  `P(A) log(1 / Q(A)) - log 2 ≤ KL(P, Q)`, from Statlib's event chain rule and the Bernoulli
  Kullback–Leibler formula.
* `CKSD.one_sub_div_log_le_s_sup_measure_real` (Fano's method): for `M ≥ 2` parameters that are
  `2s`-separated, `max_j P_j(dist(T, θ_j) ≥ s) ≥ 1 - (M⁻¹ ∑_j KL(P_j, Q) + log 2) / log M`.
* `CKSD.exists_hamming_packing` (Varshamov–Gilbert): for `m ≥ 8` there is a code in `{0,1}^m`
  containing `0`, of more than `2^(m/8)` words, with pairwise Hamming distance at least `m / 8`.
* `CKSD.mul_one_sub_div_two_le_s_sup_integral_hamming_dist` (Assouad's lemma, total variation
  form): if neighbouring vertices of the cube have laws at total variation at most `α`, every
  estimator has worst-case expected Hamming loss at least `m (1 - α) / 2`.

Sources: GAPS 103.39, 103.40, 103.45, and 103.46.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 103.39: Le Cam's two-point lower bound. If `dist θ₀ θ₁ ≥ 2 s`, every measurable
estimator `T` satisfies `max_i P_i(dist(T, θ_i) ≥ s) ≥ (1 - TV(P₀, P₁)) / 2`, with total
variation in the statistical normalization. -/
theorem one_sub_total_variation_distance_div_two_le_max_measure_real {X Θ : Type*}
    [MeasurableSpace X] [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (θ₀ θ₁ : Θ) (s : ℝ) (hsep : 2 * s ≤ dist θ₀ θ₁)
    (T : X → Θ) (hT : Measurable T) :
    (1 - totalVariationDistance P₀ P₁) / 2 ≤ max (P₀.real {x | s ≤ dist (T x) θ₀})
      (P₁.real {x | s ≤ dist (T x) θ₁}) := by
  let B := {x | dist (T x) θ₀ < s}
  have hB : MeasurableSet B := measurableSet_lt
    ((show Continuous (fun t : Θ ↦ dist t θ₀) from
      continuous_id.dist continuous_const).measurable.comp hT) measurable_const
  have hBc : Bᶜ = {x | s ≤ dist (T x) θ₀} := by
    ext x
    simp only [B, mem_compl_iff, mem_ofPred_eq, not_lt]
  have hsubset : B ⊆ {x | s ≤ dist (T x) θ₁} := by
    intro x hx
    have hdist := dist_triangle θ₀ (T x) θ₁
    rw [dist_comm θ₀ (T x)] at hdist
    change dist (T x) θ₀ < s at hx
    change s ≤ dist (T x) θ₁
    linarith
  have htv := abs_measure_real_sub_le_total_variation_distance P₀ P₁ B hB
  have hmass := measureReal_add_measureReal_compl (μ := P₀) hB
  rw [probReal_univ, hBc] at hmass
  have hother := measureReal_mono (μ := P₁) hsubset
  have hdiff := le_abs_self (P₀.real B - P₁.real B)
  have hmax₀ := le_max_left (P₀.real {x | s ≤ dist (T x) θ₀})
    (P₁.real {x | s ≤ dist (T x) θ₁})
  have hmax₁ := le_max_right (P₀.real {x | s ≤ dist (T x) θ₀})
    (P₁.real {x | s ≤ dist (T x) θ₁})
  linarith

/-- Binary data processing for one event: if `KL(P, Q)` is finite, then
`P(A) log (1 / Q(A)) - log 2 ≤ KL(P, Q)`. Uses Statlib's chain rule for an event and the
binary Kullback-Leibler formula. -/
theorem measure_real_mul_neg_log_sub_log_two_le_kl_div {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : InformationTheory.klDiv P Q ≠ ∞) (A : Set X) (hA : MeasurableSet A) :
    P.real A * (-Real.log (Q.real A)) - Real.log 2 ≤ (InformationTheory.klDiv P Q).toReal := by
  set p := P.real A
  set q := Q.real A
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  have hKL0 : 0 ≤ (InformationTheory.klDiv P Q).toReal := ENNReal.toReal_nonneg
  rcases hq0.eq_or_lt with hq | hq
  · rw [← hq, Real.log_zero]; linarith
  rcases hq1.eq_or_lt with hq' | hq'
  · rw [hq', Real.log_one]; linarith
  -- binary data processing
  have hchain := klDiv_eq_klDiv_boolMeasure_add_add (μ := P) (ν := Q) hA.compl
  rw [compl_compl] at hchain
  have hPA : P A = ENNReal.ofReal p := (ofReal_measureReal (measure_ne_top P A)).symm
  have hPAc : P Aᶜ = ENNReal.ofReal (1 - p) := by
    rw [← probReal_compl_eq_one_sub hA, ofReal_measureReal (measure_ne_top P _)]
  have hQA : Q A = ENNReal.ofReal q := (ofReal_measureReal (measure_ne_top Q A)).symm
  have hQAc : Q Aᶜ = ENNReal.ofReal (1 - q) := by
    rw [← probReal_compl_eq_one_sub hA, ofReal_measureReal (measure_ne_top Q _)]
  rw [hPA, hPAc, hQA, hQAc, InformationTheory.klDiv_boolMeasure_ofReal_eq_klBerReal hp0 hp1 hq hq']
    at hchain
  have hle : ENNReal.ofReal (InformationTheory.klBerReal p q) ≤ InformationTheory.klDiv P Q := by
    rw [hchain, add_assoc]; exact le_self_add
  have hle' : InformationTheory.klBerReal p q ≤ (InformationTheory.klDiv P Q).toReal := by
    have := (ENNReal.ofReal_le_iff_le_toReal hKL).mp hle
    exact this
  rw [InformationTheory.klBerReal_eq_neg_binEntropy_sub hq.ne' hq'.ne] at hle'
  have hb := Real.binEntropy_le_log_two (p := p)
  have hl : Real.log (1 - q) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have : (1 - p) * Real.log (1 - q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hl
  nlinarith


/-- GAPS 103.40: Fano's method with a reference law. For `M ≥ 2` parameters with pairwise
distances at least `2 s` and laws `P_j` of finite Kullback–Leibler divergence from a reference
probability `Q`, every measurable estimator satisfies
`max_j P_j(dist(T, θ_j) ≥ s) ≥ 1 - (M⁻¹ ∑_j KL(P_j, Q) + log 2) / log M`. -/
theorem one_sub_div_log_le_s_sup_measure_real {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (M : ℕ) (hM : 2 ≤ M)
    (θ : Fin M → Θ) (P : Fin M → Measure X) [∀ j, IsProbabilityMeasure (P j)]
    (Q : Measure X) [IsProbabilityMeasure Q] (hKL : ∀ j, InformationTheory.klDiv (P j) Q ≠ ∞)
    (s : ℝ) (hsep : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    (T : X → Θ) (hT : Measurable T) :
    1 - (((∑ j, (InformationTheory.klDiv (P j) Q).toReal) / M + Real.log 2) / Real.log M) ≤
      sSup (range fun j ↦ (P j).real {x | s ≤ dist (T x) (θ j)}) := by
  classical
  set F := sSup (range fun j ↦ (P j).real {x | s ≤ dist (T x) (θ j)}) with hF
  set A : Fin M → Set X := fun j ↦ {x | dist (T x) (θ j) < s} with hAdef
  have hA : ∀ j, MeasurableSet (A j) := fun j ↦ measurableSet_lt
    ((show Continuous (fun t : Θ ↦ dist t (θ j)) from
      continuous_id.dist continuous_const).measurable.comp hT) measurable_const
  have hAc : ∀ j, (A j)ᶜ = {x | s ≤ dist (T x) (θ j)} := by
    intro j; ext x; simp [A]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj ↦ ?_
    have h1 : dist (T x) (θ i) < s := hi
    have h2 : dist (T x) (θ j) < s := hj
    have := dist_triangle_left (θ i) (θ j) (T x)
    have := hsep i j hij
    linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hKL0 : 0 ≤ ∑ j, (InformationTheory.klDiv (P j) Q).toReal :=
    Finset.sum_nonneg fun j _ ↦ ENNReal.toReal_nonneg
  -- success probabilities are at least `1 - F`
  have hbdd : BddAbove (range fun j ↦ (P j).real {x | s ≤ dist (T x) (θ j)}) :=
    (finite_range _).bddAbove
  have hsucc : ∀ j, 1 - F ≤ (P j).real (A j) := by
    intro j
    have h1 : (P j).real {x | s ≤ dist (T x) (θ j)} ≤ F := le_csSup hbdd (mem_range_self j)
    rw [← hAc, probReal_compl_eq_one_sub (hA j)] at h1
    linarith
  set c := 1 - F with hc
  have hgoal : c ≤ ((∑ j, (InformationTheory.klDiv (P j) Q).toReal) / M + Real.log 2) /
      Real.log M := by
    rcases le_or_gt c 0 with hc0 | hc0
    · exact hc0.trans (by positivity)
    -- every reference mass is positive
    have hqpos : ∀ j, 0 < Q.real (A j) := by
      intro j
      refine lt_of_le_of_ne measureReal_nonneg fun h ↦ ?_
      have hac := (InformationTheory.klDiv_ne_top_iff.mp (hKL j)).1
      have hQ0 : Q (A j) = 0 := by
        rw [← ofReal_measureReal (measure_ne_top Q _), ← h, ENNReal.ofReal_zero]
      have hP0 : (P j).real (A j) = 0 := by
        simp [Measure.real, hac hQ0]
      linarith [hsucc j]
    have hqsum : ∑ j, Q.real (A j) ≤ 1 := by
      rw [← measureReal_iUnion_fintype hdisj hA]
      exact measureReal_le_one
    -- `M log M ≤ ∑ j, -log q_j`
    have hjensen : (M : ℝ) * Real.log M ≤ ∑ j, -Real.log (Q.real (A j)) := by
      have h : ∀ j, Real.log (M * Q.real (A j)) ≤ M * Q.real (A j) - 1 := fun j ↦
        Real.log_le_sub_one_of_pos (mul_pos hMpos (hqpos j))
      have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ h j
      have hrw : ∀ j, Real.log (M * Q.real (A j)) = Real.log M + Real.log (Q.real (A j)) :=
        fun j ↦ Real.log_mul hMpos.ne' (hqpos j).ne'
      simp only [hrw] at hs
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one] at hs
      rw [Finset.sum_neg_distrib]
      nlinarith
    have hneglog : ∀ j, 0 ≤ -Real.log (Q.real (A j)) := fun j ↦
      neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)
    have hevent : ∀ j, c * (-Real.log (Q.real (A j))) - Real.log 2 ≤
        (InformationTheory.klDiv (P j) Q).toReal := by
      intro j
      have := measure_real_mul_neg_log_sub_log_two_le_kl_div (P j) Q (hKL j) (A j) (hA j)
      have := mul_le_mul_of_nonneg_right (hsucc j) (hneglog j)
      linarith
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hevent j
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [le_div_iff₀ hlogM, div_add' _ _ _ hMpos.ne', le_div_iff₀ hMpos]
    nlinarith
  linarith

/-- Exponential moment of the Hamming distance to a fixed binary word:
`∑_y x ^ d(c, y) = (1 + x) ^ m`. -/
theorem sum_pow_hamming_dist_eq {m : ℕ} (c : Fin m → Bool) (x : ℝ) :
    ∑ y : Fin m → Bool, x ^ hammingDist c y = (1 + x) ^ m := by
  classical
  simp only [hammingDist]
  have h : ∀ y : Fin m → Bool, x ^ (Finset.univ.filter fun i ↦ c i ≠ y i).card =
      ∏ i, (if c i ≠ y i then x else 1) := by
    intro y
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp only [h]
  have := Finset.sum_prod_piFinset (ι := Fin m) (Finset.univ : Finset Bool)
    (fun i b ↦ if c i ≠ b then x else 1)
  rw [Fintype.piFinset_univ] at this
  rw [this]
  have hb : ∀ i, ∑ b : Bool, (if c i ≠ b then x else 1) = 1 + x := by
    intro i; cases c i <;> simp [add_comm]
  simp only [hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- GAPS 103.45: the Varshamov–Gilbert bound. For `m ≥ 8` there is a set `C ⊆ {0,1}^m`
containing the zero word with `|C| - 1 ≥ 2^(m/8)` and pairwise Hamming distances at least
`m / 8`. -/
theorem exists_hamming_packing (m : ℕ) (hm : 8 ≤ m) :
    ∃ C : Finset (Fin m → Bool), (fun _ ↦ false) ∈ C ∧
      Real.rpow 2 ((m : ℝ) / 8) ≤ (C.card : ℝ) - 1 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (m : ℝ) / 8 ≤ (hammingDist x y : ℝ) := by
  classical
  simp only [hammingDist]
  set d : ℝ := (m : ℝ) / 8 with hd
  have hd1 : 1 ≤ d := by rw [hd, le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 8 ≤ m)
  set h : (Fin m → Bool) → (Fin m → Bool) → ℕ :=
    fun x y ↦ (Finset.univ.filter fun i ↦ x i ≠ y i).card with hh
  have hsymm : ∀ x y, h x y = h y x := by
    intro x y; simp only [hh, ne_comm]
  set valid : Finset (Fin m → Bool) → Prop :=
    fun C ↦ (fun _ ↦ false) ∈ C ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ (h x y : ℝ) with hvalid
  -- a code of maximal size
  obtain ⟨C, hCmem, hCmax⟩ := Finset.exists_max_image
    (Finset.univ.filter valid) Finset.card ⟨{fun _ ↦ false}, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, valid]
      refine ⟨Finset.mem_singleton_self _, ?_⟩
      intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hCmem hCmax
  obtain ⟨h0, hsep⟩ := hCmem
  refine ⟨C, h0, ?_, hsep⟩
  -- maximality: the balls of radius `< d` around the code cover the cube
  have hcover : ∀ y, ∃ c ∈ C, (h c y : ℝ) < d := by
    intro y
    by_contra hcon
    push Not at hcon
    have hyC : y ∉ C := by
      intro hy
      have := hcon y hy
      simp only [hh, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty,
        Nat.cast_zero] at this
      linarith
    have hval : valid (insert y C) := by
      refine ⟨Finset.mem_insert_of_mem h0, ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · rw [hsymm]; exact hcon b hb
      · exact hcon a ha
      · exact hsep a ha b hb hab
    have := hCmax _ hval
    rw [Finset.card_insert_of_notMem hyC] at this
    omega
  -- ball size bound
  set t : ℝ := Real.rpow 2 d with ht
  have ht2 : 2 ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hd1
    simpa [ht] using this
  have ht0 : 0 < t := by linarith
  have ht8 : t ^ 8 = 2 ^ m := by
    rw [ht]
    change ((2 : ℝ) ^ d) ^ (8 : ℕ) = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show d * ((8 : ℕ) : ℝ) = (m : ℝ) by rw [hd]; push_cast; ring, Real.rpow_natCast]
  have hball : ∀ c, ((Finset.univ.filter fun y ↦ (h c y : ℝ) < d).card : ℝ) ≤ t ^ 5 := by
    intro c
    have hpt : ∀ y, (if (h c y : ℝ) < d then (1 : ℝ) else 0) ≤ t ^ 2 * (1 / 4 : ℝ) ^ h c y := by
      intro y
      split_ifs with hy
      · have h2 : (2 : ℝ) ^ (h c y) ≤ t := by
          rw [ht, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hy.le
        have : (4 : ℝ) ^ h c y ≤ t ^ 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
          exact pow_le_pow_left₀ (by positivity) h2 2
        rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
        exact this
      · positivity
    have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hpt y
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
    have hexp := sum_pow_hamming_dist_eq c (1 / 4 : ℝ)
    simp only [hammingDist] at hexp
    simp only [hh] at hsum
    rw [hexp] at hsum
    have h54 : (1 + 1 / 4 : ℝ) ^ m ≤ t ^ 3 := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
        (by norm_num : (8 : ℕ) ≠ 0)).mp ?_
      calc ((1 + 1 / 4 : ℝ) ^ m) ^ 8 = ((1 + 1 / 4 : ℝ) ^ 8) ^ m := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (8 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by norm_num) m
        _ = ((2 : ℝ) ^ m) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ = (t ^ 8) ^ 3 := by rw [ht8]
        _ = (t ^ 3) ^ 8 := by ring
    calc _ ≤ t ^ 2 * (1 + 1 / 4 : ℝ) ^ m := hsum
      _ ≤ t ^ 2 * t ^ 3 := by gcongr
      _ = t ^ 5 := by ring
  -- counting
  have hcount : (2 : ℝ) ^ m ≤ C.card * t ^ 5 := by
    have hsub : (Finset.univ : Finset (Fin m → Bool)) ⊆
        C.biUnion fun c ↦ Finset.univ.filter fun y ↦ (h c y : ℝ) < d := by
      intro y _
      obtain ⟨c, hc, hcy⟩ := hcover y
      exact Finset.mem_biUnion.mpr ⟨c, hc, by simp [hcy]⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := C)
      (t := fun c ↦ Finset.univ.filter fun y ↦ (h c y : ℝ) < d)
    have h3 : ((2 : ℕ) ^ m : ℝ) ≤ ∑ c ∈ C,
        ((Finset.univ.filter fun y ↦ (h c y : ℝ) < d).card : ℝ) := by
      have : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
      exact_mod_cast this ▸ h1.trans h2
    calc (2 : ℝ) ^ m ≤ _ := by exact_mod_cast h3
      _ ≤ ∑ _c ∈ C, t ^ 5 := Finset.sum_le_sum fun c _ ↦ hball c
      _ = C.card * t ^ 5 := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [← ht8] at hcount
  have hC : t ^ 3 ≤ C.card := by
    have h5 : 0 < t ^ 5 := by positivity
    nlinarith [pow_pos ht0 3, pow_pos ht0 5]
  have h4 : 4 ≤ t * t := by nlinarith
  have h3 : t + 1 ≤ t ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h4 ht0.le]
  change t ≤ _
  linarith

/-- GAPS 103.46: Assouad's lemma in total variation form. If the laws `P_w` indexed by the
cube `{0,1}^m` satisfy `TV(P_w, P_w') ≤ α` whenever `w` and `w'` differ in one coordinate, then
every measurable estimator `T` with values in the cube has worst-case expected Hamming loss
`max_w E_w d(T, w) ≥ m (1 - α) / 2`. -/
theorem mul_one_sub_div_two_le_s_sup_integral_hamming_dist {X : Type*} [MeasurableSpace X] (m : ℕ)
    (P : (Fin m → Bool) → Measure X) [∀ w, IsProbabilityMeasure (P w)]
    (α : ℝ)
    (hnear : ∀ w w', hammingDist w w' = 1 → totalVariationDistance (P w) (P w') ≤ α)
    (T : X → (Fin m → Bool)) (hT : Measurable T) :
    (m : ℝ) * (1 - α) / 2 ≤ sSup (range fun w ↦ ∫ x, (hammingDist (T x) w : ℝ) ∂P w) := by
  simp only [hammingDist] at hnear ⊢
  set f := fun w : Fin m → Bool ↦
    ∫ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) ∂P w with hf
  -- the events on which the `j`-th coordinate is wrong
  have hmeas : ∀ (j : Fin m) (b : Bool), MeasurableSet {x | T x j ≠ b} := by
    intro j b
    exact (measurableSet_singleton b).compl.preimage ((measurable_pi_apply j).comp hT)
  have hfeq : ∀ w, f w = ∑ j, (P w).real {x | T x j ≠ w j} := by
    intro w
    have hpt : ∀ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) =
        ∑ j, {x | T x j ≠ w j}.indicator (fun _ ↦ (1 : ℝ)) x := by
      intro x
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : T x j ≠ w j <;> simp [h, Set.indicator]
    simp only [hf, hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_indicator_const _ (hmeas j (w j)), smul_eq_mul, mul_one]
    · intro j _
      exact (integrable_const (1 : ℝ)).indicator (hmeas j (w j))
  -- flipping one coordinate
  let flip : Fin m → (Fin m → Bool) → (Fin m → Bool) := fun j w ↦ Function.update w j (!w j)
  have hflip_inv : ∀ j, Function.Involutive (flip j) := by
    intro j w
    ext i
    by_cases h : i = j
    · subst h; simp [flip]
    · simp [flip, Function.update_of_ne h]
  have hflip_j : ∀ j w, flip j w j = !w j := by intro j w; simp [flip]
  have hflip_card : ∀ j w, (Finset.univ.filter fun i ↦ w i ≠ flip j w i).card = 1 := by
    intro j w
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    by_cases h : i = j
    · subst h; simp [flip]
    · simp [flip, h]
  have hpair : ∀ j w, 1 - α ≤ (P w).real {x | T x j ≠ w j} +
      (P (flip j w)).real {x | T x j ≠ flip j w j} := by
    intro j w
    have hset : {x | T x j ≠ flip j w j} = {x | T x j ≠ w j}ᶜ := by
      ext x
      simp only [hflip_j, mem_ofPred_eq, mem_compl_iff]
      cases T x j <;> cases w j <;> simp
    rw [hset, probReal_compl_eq_one_sub (hmeas j (w j))]
    have htv := abs_measure_real_sub_le_total_variation_distance (P w) (P (flip j w))
      {x | T x j ≠ w j} (hmeas j (w j))
    have := hnear w (flip j w) (hflip_card j w)
    have := neg_abs_le ((P w).real {x | T x j ≠ w j} - (P (flip j w)).real {x | T x j ≠ w j})
    linarith
  have hcoord : ∀ j, (Fintype.card (Fin m → Bool) : ℝ) * (1 - α) / 2 ≤
      ∑ w, (P w).real {x | T x j ≠ w j} := by
    intro j
    have hre : ∑ w, (P w).real {x | T x j ≠ w j} =
        ∑ w, (P (flip j w)).real {x | T x j ≠ flip j w j} :=
      (Fintype.sum_equiv (hflip_inv j).toPerm _ _ fun w ↦ rfl).symm
    have hsum : ∑ _w : Fin m → Bool, (1 - α) ≤ ∑ w, ((P w).real {x | T x j ≠ w j} +
        (P (flip j w)).real {x | T x j ≠ flip j w j}) :=
      Finset.sum_le_sum fun w _ ↦ hpair j w
    rw [Finset.sum_add_distrib, ← hre, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    linarith
  have htotal : (Fintype.card (Fin m → Bool) : ℝ) * ((m : ℝ) * (1 - α) / 2) ≤ ∑ w, f w := by
    simp only [hfeq]
    rw [Finset.sum_comm]
    calc (Fintype.card (Fin m → Bool) : ℝ) * ((m : ℝ) * (1 - α) / 2)
        = ∑ _j : Fin m, (Fintype.card (Fin m → Bool) : ℝ) * (1 - α) / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hcoord j
  have hbdd : BddAbove (range f) := (finite_range f).bddAbove
  have hle : ∑ w, f w ≤ (Fintype.card (Fin m → Bool) : ℝ) * sSup (range f) := by
    calc ∑ w, f w ≤ ∑ _w : Fin m → Bool, sSup (range f) :=
          Finset.sum_le_sum fun w _ ↦ le_csSup hbdd (mem_range_self w)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card (Fin m → Bool) := by
    exact_mod_cast Fintype.card_pos
  exact le_of_mul_le_mul_left (htotal.trans hle) hcard

end CKSD
