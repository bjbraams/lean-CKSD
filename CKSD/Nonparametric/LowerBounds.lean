module

public import CKSD.Nonparametric.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Statlib.Divergence.KullbackLeibler.Event
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Nonparametric: LowerBounds

Sources: `GAPS.md`, `SYNOPSIS103.md`, and `STRUCTURE103.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.

Fano's bound uses Statlib's chain rule for an event
(`ProbabilityTheory.klDiv_eq_klDiv_boolMeasure_add_add`) and its Bernoulli formula
(`InformationTheory.klDiv_boolMeasure_ofReal_eq_klBerReal`,
`InformationTheory.klBerReal_eq_neg_binEntropy_sub`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common rank measurable structure.
attribute [local instance] rankMeasurableSpace

/-- Every measurable event difference is bounded by statistical total variation. -/
theorem abs_measureReal_sub_le_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set X) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ totalVariationDistance P Q := by
  apply le_csSup (show BddAbove {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ?_)
    (show |P.real A - Q.real A| ∈ {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ⟨A, hA, rfl⟩)
  refine ⟨1, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  apply abs_le.mpr
  constructor <;> linarith [measureReal_nonneg (μ := P) (s := B),
    measureReal_nonneg (μ := Q) (s := B),
    measureReal_le_one (μ := P) (s := B), measureReal_le_one (μ := Q) (s := B)]

/-- GAPS 103.39: Le Cam's two-point lower bound with the statistical TV normalization. -/
theorem le_cam_two_point_lower_bound {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (θ₀ θ₁ : Θ) (s : ℝ) (hs : 0 < s) (hsep : 2 * s ≤ dist θ₀ θ₁)
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
  have htv := abs_measureReal_sub_le_totalVariationDistance P₀ P₁ B hB
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
theorem measureReal_mul_neg_log_sub_log_two_le_klDiv {X : Type*} [MeasurableSpace X]
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


/-- GAPS 103.40: Fano's bound in its finite-reference-KL form. -/
theorem fano_lower_bound {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (M : ℕ) (hM : 2 ≤ M)
    (θ : Fin M → Θ) (P : Fin M → Measure X) (hP : ∀ j, IsProbabilityMeasure (P j))
    (Q : Measure X) [IsProbabilityMeasure Q] (hKL : ∀ j, InformationTheory.klDiv (P j) Q ≠ ∞)
    (s : ℝ) (hs : 0 < s) (hsep : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
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
      have := measureReal_mul_neg_log_sub_log_two_le_klDiv (P j) Q (hKL j) (A j) (hA j)
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
theorem sum_pow_hammingCard_eq {m : ℕ} (c : Fin m → Bool) (x : ℝ) :
    ∑ y : Fin m → Bool, x ^ (Finset.univ.filter fun i ↦ c i ≠ y i).card = (1 + x) ^ m := by
  classical
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

/-- GAPS 103.45: a separated binary packing containing zero. -/
theorem exists_hamming_packing (m : ℕ) (hm : 8 ≤ m) :
    ∃ C : Finset (Fin m → Bool), (fun _ ↦ false) ∈ C ∧
      Real.rpow 2 ((m : ℝ) / 8) ≤ (C.card : ℝ) - 1 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        (m : ℝ) / 8 ≤ ((Finset.univ.filter fun i ↦ x i ≠ y i).card : ℝ) := by
  classical
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
    have hexp := sum_pow_hammingCard_eq c (1 / 4 : ℝ)
    simp only [hh] at hsum
    rw [hexp] at hsum
    have h54 : (1 + 1 / 4 : ℝ) ^ m ≤ t ^ 3 := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (8 : ℕ) ≠ 0)).mp ?_
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

/-- GAPS 103.46, TV version of Assouad's lemma for binary-valued estimators. -/
theorem assouad_lower_bound {X : Type*} [MeasurableSpace X] (m : ℕ)
    (P : (Fin m → Bool) → Measure X) (hP : ∀ w, IsProbabilityMeasure (P w))
    (α : ℝ) (hα : α ∈ Icc 0 1)
    (hnear : ∀ w w', (Finset.univ.filter fun i ↦ w i ≠ w' i).card = 1 → totalVariationDistance (P w)
      (P w') ≤ α)
    (T : X → (Fin m → Bool)) (hT : Measurable T) :
    (m : ℝ) * (1 - α) / 2 ≤ sSup (range fun w ↦
      ∫ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) ∂P w) := by
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
    have htv := abs_measureReal_sub_le_totalVariationDistance (P w) (P (flip j w))
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

/-- The coordinatewise L1 norm splits over complementary coordinate sets. -/
theorem restrictedL1Norm_add_compl {p : ℕ} (S : Finset (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x + restrictedL1Norm Sᶜ x = restrictedL1Norm Finset.univ x := by
  exact S.sum_add_sum_compl (fun j ↦ |x j|)

/-- A restricted reverse triangle bound for coordinatewise L1 norms. -/
theorem restrictedL1Norm_le_add_sub {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x ≤ restrictedL1Norm S y + restrictedL1Norm S (y - x) := by
  unfold restrictedL1Norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  change |x j| ≤ |y j| + |y j - x j|
  calc
    |x j| = |y j + (x j - y j)| := by congr 1; ring
    _ ≤ |y j| + |x j - y j| := abs_add_le _ _
    _ = |y j| + |y j - x j| := by rw [abs_sub_comm]

/-- GAPS 103.48, equivalence between the nullspace property and unique basis pursuit. -/
theorem nullspace_property_iff_basis_pursuit_unique {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) :
    (∀ δ, A δ = 0 → δ ≠ 0 → restrictedL1Norm S δ < restrictedL1Norm Sᶜ δ) ↔
    ∀ β, (∀ j ∉ S, β j = 0) → ∀ b, A b = A β → b ≠ β →
      restrictedL1Norm Finset.univ β < restrictedL1Norm Finset.univ b := by
  constructor
  · intro hnsp β hβ b hab hne
    have hnull : A (b - β) = 0 := by rw [map_sub, hab, sub_self]
    have hstrict := hnsp (b - β) hnull (sub_ne_zero.mpr hne)
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hβ j (Finset.mem_compl.mp hj), abs_zero]
    have hcomp : restrictedL1Norm Sᶜ (b - β) = restrictedL1Norm Sᶜ b := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [PiLp.sub_apply, hβ j (Finset.mem_compl.mp hj), sub_zero]
    have htriangle := restrictedL1Norm_le_add_sub S β b
    have hsplitβ := restrictedL1Norm_add_compl S β
    have hsplitb := restrictedL1Norm_add_compl S b
    rw [hβc, add_zero] at hsplitβ
    rw [hcomp] at hstrict
    linarith
  · intro hunique δ hnull hne
    let β : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (fun j ↦ if j ∈ S then δ j else 0)
    let b := β - δ
    have hβ : ∀ j ∉ S, β j = 0 := by
      intro j hj
      simp [β, hj]
    have hab : A b = A β := by
      change A (β - δ) = A β
      rw [map_sub, hnull, sub_zero]
    have hbne : b ≠ β := by
      intro h
      change β - δ = β at h
      exact hne (sub_eq_self.mp h)
    have hlt := hunique β hβ b hab hbne
    have hβs : restrictedL1Norm S β = restrictedL1Norm S δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [β, hj]
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [β, Finset.mem_compl.mp hj]
    have hbs : restrictedL1Norm S b = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [b, β, PiLp.sub_apply, hj]
    have hbc : restrictedL1Norm Sᶜ b = restrictedL1Norm Sᶜ δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [b, β, PiLp.sub_apply, Finset.mem_compl.mp hj]
    rw [← restrictedL1Norm_add_compl S β, ← restrictedL1Norm_add_compl S b,
      hβs, hβc, hbs, hbc, add_zero, zero_add] at hlt
    exact hlt

/-- The support of `a • x + b • y` has at most `2 s` elements when `x` and `y` are
`s`-sparse. -/
theorem sparsity_smul_add_smul_le {p s : ℕ} (x y : EuclideanSpace ℝ (Fin p)) (a b : ℝ)
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) : sparsity (a • x + b • y) ≤ 2 * s := by
  classical
  unfold sparsity at *
  calc (Finset.univ.filter fun j ↦ (a • x + b • y) j ≠ 0).card
      ≤ ((Finset.univ.filter fun j ↦ x j ≠ 0) ∪ (Finset.univ.filter fun j ↦ y j ≠ 0)).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
        by_contra h
        push Not at h
        apply hj
        simp [h.1, h.2]
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 * s := by omega

/-- Restricted orthogonality from the restricted isometry property: for `s`-sparse vectors
with disjoint supports, `|⟪A x, A y⟫| ≤ δ ‖x‖ ‖y‖` when `A` has the RIP of order `2 s`. -/
theorem inner_apply_le_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (hrip : HasRestrictedIsometry A (2 * s) δ) (x y : EuclideanSpace ℝ (Fin p))
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) (hxy : ∀ j, x j = 0 ∨ y j = 0) :
    |⟪A x, A y⟫| ≤ δ * ‖x‖ * ‖y‖ := by
  have hinner : ⟪x, y⟫ = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rcases hxy j with h | h <;> simp [h]
  rcases (norm_nonneg x).eq_or_lt with hx0 | hx0
  · rw [eq_comm, norm_eq_zero] at hx0; simp [hx0]
  rcases (norm_nonneg y).eq_or_lt with hy0 | hy0
  · rw [eq_comm, norm_eq_zero] at hy0; simp [hy0]
  set α := Real.sqrt ‖x‖
  set β := Real.sqrt ‖y‖
  have hα : 0 < α := Real.sqrt_pos.mpr hx0
  have hβ : 0 < β := Real.sqrt_pos.mpr hy0
  have hα2 : α ^ 2 = ‖x‖ := Real.sq_sqrt hx0.le
  have hβ2 : β ^ 2 = ‖y‖ := Real.sq_sqrt hy0.le
  set a := β / α
  set b := α / β
  have hab : a * b = 1 := by
    simp only [a, b]; field_simp
  have h1 := (hrip (a • x + b • y) (sparsity_smul_add_smul_le x y a b hx hy)).2
  have h2 := (hrip (a • x + (-b) • y) (sparsity_smul_add_smul_le x y a (-b) hx hy)).1
  have h3 := (hrip (a • x + b • y) (sparsity_smul_add_smul_le x y a b hx hy)).1
  have h4 := (hrip (a • x + (-b) • y) (sparsity_smul_add_smul_le x y a (-b) hx hy)).2
  simp only [map_add, map_smul, norm_add_sq_real, inner_smul_left, inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hinner, RCLike.conj_to_real] at h1 h2 h3 h4
  have ha2 : a ^ 2 * ‖x‖ ^ 2 = ‖x‖ * ‖y‖ := by
    simp only [a]; rw [div_pow, hβ2, ← hα2]; field_simp
  have hb2 : b ^ 2 * ‖y‖ ^ 2 = ‖x‖ * ‖y‖ := by
    simp only [b]; rw [div_pow, hα2, ← hβ2]; field_simp
  have e : a * (b * ⟪A x, A y⟫) = ⟪A x, A y⟫ := by rw [← mul_assoc, hab, one_mul]
  have key : 4 * ⟪A x, A y⟫ ≤ 2 * δ * (a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2) := by
    nlinarith
  have key' : -(4 * ⟪A x, A y⟫) ≤ 2 * δ * (a ^ 2 * ‖x‖ ^ 2 + b ^ 2 * ‖y‖ ^ 2) := by
    nlinarith
  rw [ha2, hb2] at key key'
  rw [abs_le]
  constructor <;> nlinarith

/-- GAPS 103.48, restricted-isometry sufficient condition for exact sparse recovery. -/
theorem nullspace_property_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : δ ∈ Ico 0 (1 / 3 : ℝ)) (hrip : HasRestrictedIsometry A (2 * s) δ)
    (S : Finset (Fin p)) (hS : S.card ≤ s) :
    ∀ v, A v = 0 → v ≠ 0 → restrictedL1Norm S v < restrictedL1Norm Sᶜ v := by
  classical
  intro v hv hne
  obtain ⟨hδ0, hδ1⟩ := hδ
  -- positivity of the full L1 norm
  have hpos : 0 < restrictedL1Norm Finset.univ v := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (PiLp.ext fun j ↦ by simp [h j])
    calc (0 : ℝ) < |v j| := abs_pos.mpr hj
      _ ≤ restrictedL1Norm Finset.univ v :=
        Finset.single_le_sum (f := fun j ↦ |v j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have hsplit := restrictedL1Norm_add_compl S v
  have hS0 : 0 ≤ restrictedL1Norm S v := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hSc0 : 0 ≤ restrictedL1Norm Sᶜ v := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst this
    have h0 : restrictedL1Norm ∅ v = 0 := Finset.sum_empty
    linarith
  -- the key estimate `(1 - δ) ‖v_S‖₁ ≤ δ ‖v‖₁`
  have hkey : (1 - δ) * restrictedL1Norm S v ≤ δ * restrictedL1Norm Finset.univ v := by
    -- sort the coordinates by decreasing absolute value and cut into blocks of size `s`
    obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin p), Monotone ((fun j ↦ -|v j|) ∘ σ) :=
      ⟨_, Tuple.monotone_sort _⟩
    set r : Fin p → Fin p := fun j ↦ σ.symm j with hr
    set ℓ : Fin p → ℕ := fun j ↦ (r j : ℕ) / s with hℓ
    have hcmp : ∀ i j, ℓ j < ℓ i → |v i| ≤ |v j| := by
      intro i j hij
      have hle : r j ≤ r i := by
        by_contra h
        push Not at h
        exact absurd (Nat.div_le_div_right (c := s) (le_of_lt (show (r i : ℕ) < r j from h)))
          (not_le.mpr hij)
      have := hmono hle
      simp only [Function.comp, r, Equiv.apply_symm_apply] at this
      linarith
    set lev : ℕ → Finset (Fin p) := fun k ↦ Finset.univ.filter fun j ↦ ℓ j = k with hlev
    have hcard : ∀ k, (lev k).card ≤ s := by
      intro k
      calc (lev k).card ≤ (Finset.Ico (k * s) (k * s + s)).card := by
            refine Finset.card_le_card_of_injOn (fun j ↦ (r j : ℕ)) ?_ ?_
            · intro j hj
              simp only [lev, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hj
              simp only [Finset.coe_Ico, mem_Ico]
              constructor
              · rw [← hj]; exact Nat.div_mul_le_self _ _
              · have := Nat.lt_div_mul_add (a := (r j : ℕ)) hs
                rw [← hj]; exact this
            · intro i _ j _ hij
              exact σ.symm.injective (Fin.ext hij)
        _ = s := by simp
    have hfull : ∀ k, (∃ i, k < ℓ i) → (lev k).card = s := by
      rintro k ⟨i, hi⟩
      refine le_antisymm (hcard k) ?_
      have hbound : (k + 1) * s ≤ (r i : ℕ) :=
        (Nat.mul_le_mul_right s hi).trans (Nat.div_mul_le_self _ _)
      have hlt : ∀ t < s, k * s + t < p := fun t ht ↦ by
        have := (r i).isLt
        nlinarith
      calc s = (Finset.range s).card := (Finset.card_range s).symm
        _ ≤ (lev k).card := by
            refine Finset.card_le_card_of_injOn
              (fun t ↦ if ht : t < s then σ ⟨k * s + t, hlt t ht⟩ else σ ⟨0, by omega⟩) ?_ ?_
            · intro t ht
              have ht' : t < s := Finset.mem_range.mp ht
              simp only [lev, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq, ht',
                dite_true, ℓ, r, Equiv.symm_apply_apply]
              rw [show k * s + t = t + k * s by ring, Nat.add_mul_div_right _ _ hs,
                Nat.div_eq_of_lt ht', zero_add]
            · intro t ht t' ht' h
              have ht1 : t < s := Finset.mem_range.mp ht
              have ht2 : t' < s := Finset.mem_range.mp ht'
              simp only [ht1, ht2, dite_true] at h
              have := congrArg Fin.val (σ.injective h)
              simp at this
              exact this
    -- block vectors
    set vk : ℕ → EuclideanSpace ℝ (Fin p) :=
      fun k ↦ WithLp.toLp 2 (fun j ↦ if ℓ j = k then v j else 0) with hvk
    have hvk_apply : ∀ k j, vk k j = if ℓ j = k then v j else 0 := fun k j ↦ rfl
    have hsp : ∀ k, sparsity (vk k) ≤ s := by
      intro k
      refine le_trans (Finset.card_le_card ?_) (hcard k)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvk_apply] at hj
      simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra h
      exact hj (ite_eq_right h)
    have hdisj : ∀ k k', k ≠ k' → ∀ j, vk k j = 0 ∨ vk k' j = 0 := by
      intro k k' hkk j
      simp only [hvk_apply]
      by_cases h : ℓ j = k
      · right; rw [ite_eq_right]; rw [h]; exact hkk
      · left; rw [ite_eq_right h]
    have hnorm_sq : ∀ k, ‖vk k‖ ^ 2 = ∑ j ∈ lev k, v j ^ 2 := by
      intro k
      rw [EuclideanSpace.norm_sq_eq]
      simp only [hvk_apply, Real.norm_eq_abs, sq_abs, lev, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> simp
    set L : ℕ → ℝ := fun k ↦ ∑ j ∈ lev k, |v j| with hL
    have hℓlt : ∀ j, ℓ j < p := fun j ↦ (Nat.div_le_self _ _).trans_lt (r j).isLt
    have hdecomp : v = vk 0 + ∑ k ∈ Finset.range p, vk (k + 1) := by
      ext j
      simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply]
      change v j = vk 0 j + ∑ c ∈ Finset.range p, vk (c + 1) j
      simp only [hvk_apply]
      rcases Nat.eq_zero_or_pos (ℓ j) with h0 | h0
      · rw [ite_eq_left h0, Finset.sum_eq_zero fun k _ ↦ ite_eq_right (by omega)]; ring
      · obtain ⟨m, hm⟩ : ∃ m, ℓ j = m + 1 := ⟨ℓ j - 1, by omega⟩
        rw [ite_eq_right (by omega), zero_add, Finset.sum_eq_single m]
        · rw [ite_eq_left hm]
        · intro b _ hb; rw [ite_eq_right (by omega)]
        · intro hm'; exact absurd (Finset.mem_range.mpr (by have := hℓlt j; omega)) hm'
    have hblock_pt : ∀ k j, ℓ j = k + 1 → |v j| ≤ L k / s := by
      intro k j hj
      have hc := hfull k ⟨j, by omega⟩
      rw [le_div_iff₀ (by exact_mod_cast hs)]
      have := Finset.card_nsmul_le_sum (lev k) (fun i ↦ |v i|) (|v j|) (fun i hi ↦ by
        simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hcmp j i (by omega))
      rw [hc, nsmul_eq_mul] at this
      linarith
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hL0 : ∀ k, 0 ≤ L k := fun k ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    have hblock : ∀ k, ‖vk (k + 1)‖ ≤ L k / Real.sqrt s := by
      intro k
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (div_nonneg (hL0 k) hsqrt.le)
        two_ne_zero).mp ?_
      rw [hnorm_sq, div_pow, Real.sq_sqrt hspos.le]
      calc ∑ j ∈ lev (k + 1), v j ^ 2 ≤ ∑ _j ∈ lev (k + 1), (L k / s) ^ 2 := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hblock_pt k j hj) 2
        _ = (lev (k + 1)).card * (L k / s) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ s * (L k / s) ^ 2 := by
            gcongr; exact_mod_cast hcard (k + 1)
        _ = L k ^ 2 / s := by field_simp
    have hsumL : ∑ k ∈ Finset.range p, L k = restrictedL1Norm Finset.univ v := by
      simp only [L, lev, restrictedL1Norm]
      exact Finset.sum_fiberwise_of_maps_to (fun j _ ↦ Finset.mem_range.mpr (hℓlt j)) _
    have hL0le : L 0 ≤ restrictedL1Norm Finset.univ v := by
      rw [← hsumL]
      exact Finset.single_le_sum (fun k _ ↦ hL0 k) (Finset.mem_range.mpr (by
        have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ hne (by subst h; exact Subsingleton.elim _ _)
        omega))
    -- the RIP step `(1 - δ) ‖v₀‖ ≤ δ ∑ₖ ‖vₖ₊₁‖`
    set X := ∑ k ∈ Finset.range p, ‖vk (k + 1)‖ with hX
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ ↦ norm_nonneg _
    have hAsq : ‖A (vk 0)‖ ^ 2 ≤ δ * ‖vk 0‖ * X := by
      have h0 : ⟪A (vk 0), A v⟫ = 0 := by rw [hv, inner_zero_right]
      rw [hdecomp, map_add, inner_add_right, map_sum, inner_sum,
        real_inner_self_eq_norm_sq] at h0
      have hb : ∀ k ∈ Finset.range p, -(δ * ‖vk 0‖ * ‖vk (k + 1)‖) ≤
          ⟪A (vk 0), A (vk (k + 1))⟫ := fun k _ ↦
        (abs_le.mp (inner_apply_le_of_hasRestrictedIsometry A δ hrip _ _ (hsp 0) (hsp (k + 1))
          (hdisj 0 (k + 1) (by omega)))).1
      have := Finset.sum_le_sum hb
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at this
      linarith
    have hlow := (hrip (vk 0) ((hsp 0).trans (by omega))).1
    have hv0 : (1 - δ) * ‖vk 0‖ ≤ δ * X := by
      rcases (norm_nonneg (vk 0)).eq_or_lt with h | h
      · rw [← h, mul_zero]; positivity
      · nlinarith
    have hXle : X ≤ restrictedL1Norm Finset.univ v / Real.sqrt s := by
      rw [← hsumL, Finset.sum_div]
      exact Finset.sum_le_sum fun k _ ↦ hblock k
    have hL0v0 : L 0 ≤ Real.sqrt s * ‖vk 0‖ := by
      refine (pow_le_pow_iff_left₀ (hL0 0) (by positivity) two_ne_zero).mp ?_
      rw [mul_pow, Real.sq_sqrt hspos.le, hnorm_sq]
      calc L 0 ^ 2 ≤ (lev 0).card * ∑ j ∈ lev 0, |v j| ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ s * ∑ j ∈ lev 0, v j ^ 2 := by
            simp only [sq_abs]
            gcongr
            exact_mod_cast hcard 0
    -- the first block carries the largest entries
    have hSB : restrictedL1Norm S v ≤ L 0 := by
      have hmemB : ∀ j, j ∈ lev 0 ↔ ℓ j = 0 := fun j ↦ by simp [lev]
      by_cases hsub : S ⊆ lev 0
      · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ abs_nonneg _
      obtain ⟨j₀, hj₀S, hj₀B⟩ := Finset.not_subset.mp hsub
      have hcB : (lev 0).card = s := hfull 0 ⟨j₀, by
        rw [hmemB] at hj₀B; omega⟩
      set I := S ∩ lev 0 with hI
      have hIS : I ⊆ S := Finset.inter_subset_left
      have hIB : I ⊆ lev 0 := Finset.inter_subset_right
      have hsumS := Finset.sum_sdiff (f := fun j ↦ |v j|) hIS
      have hsumB := Finset.sum_sdiff (f := fun j ↦ |v j|) hIB
      have hcardS := Finset.card_sdiff_add_card_eq_card hIS
      have hcardB := Finset.card_sdiff_add_card_eq_card hIB
      have hne1 : (S \ I).Nonempty := ⟨j₀, Finset.mem_sdiff.mpr ⟨hj₀S, fun h ↦ hj₀B (hIB h)⟩⟩
      set m := (S \ I).sup' hne1 (fun j ↦ |v j|) with hm
      have hm0 : 0 ≤ m := (abs_nonneg _).trans (Finset.le_sup' (fun j ↦ |v j|)
        (Finset.mem_sdiff.mpr ⟨hj₀S, fun h ↦ hj₀B (hIB h)⟩))
      have h1 := Finset.sum_le_card_nsmul (S \ I) (fun j ↦ |v j|) m
        (fun j hj ↦ Finset.le_sup' (fun j ↦ |v j|) hj)
      have h2 := Finset.card_nsmul_le_sum (lev 0 \ I) (fun j ↦ |v j|) m (fun i hi ↦ by
        refine Finset.sup'_le _ _ fun j hj ↦ ?_
        have hiB : ℓ i = 0 := (hmemB i).mp (Finset.mem_sdiff.mp hi).1
        have hjB : ℓ j ≠ 0 := by
          intro h
          obtain ⟨hjS, hjI⟩ := Finset.mem_sdiff.mp hj
          exact hjI (Finset.mem_inter.mpr ⟨hjS, (hmemB j).mpr h⟩)
        exact hcmp j i (by omega))
      rw [nsmul_eq_mul] at h1 h2
      have hcd : ((S \ I).card : ℝ) ≤ ((lev 0 \ I).card : ℝ) := by
        exact_mod_cast (show (S \ I).card ≤ (lev 0 \ I).card by omega)
      have h3 := mul_le_mul_of_nonneg_right hcd hm0
      change ∑ j ∈ S, |v j| ≤ ∑ j ∈ lev 0, |v j|
      linarith
    have hsq : Real.sqrt s * X ≤ restrictedL1Norm Finset.univ v := by
      rw [le_div_iff₀ hsqrt] at hXle; linarith
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Blocks of coordinates of size `s` in order of decreasing absolute value: `ℓ j` is the index
of the block containing coordinate `j`. Blocks have at most `s` elements, a block followed by a
nonempty block is full, and all block indices are smaller than `p`. -/
theorem exists_decreasing_blocks {p : ℕ} (v : Fin p → ℝ) {s : ℕ} (hs : 0 < s) :
    ∃ ℓ : Fin p → ℕ, (∀ i j, ℓ j < ℓ i → |v i| ≤ |v j|) ∧
      (∀ k, (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ s) ∧
      (∀ k, (∃ i, k < ℓ i) → (Finset.univ.filter fun j ↦ ℓ j = k).card = s) ∧
      (∀ j, ℓ j < p) := by
  classical
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin p), Monotone ((fun j ↦ -|v j|) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  set r : Fin p → Fin p := fun j ↦ σ.symm j with hr
  set ℓ : Fin p → ℕ := fun j ↦ (r j : ℕ) / s with hℓ
  refine ⟨ℓ, ?_, ?_, ?_, fun j ↦ (Nat.div_le_self _ _).trans_lt (r j).isLt⟩
  · intro i j hij
    have hle : r j ≤ r i := by
      by_contra h
      push Not at h
      exact absurd (Nat.div_le_div_right (c := s) (le_of_lt (show (r i : ℕ) < r j from h)))
        (not_le.mpr hij)
    have := hmono hle
    simp only [Function.comp, r, Equiv.apply_symm_apply] at this
    linarith
  · intro k
    calc (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ (Finset.Ico (k * s) (k * s + s)).card := by
          refine Finset.card_le_card_of_injOn (fun j ↦ (r j : ℕ)) ?_ ?_
          · intro j hj
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hj
            simp only [Finset.coe_Ico, mem_Ico]
            constructor
            · rw [← hj]; exact Nat.div_mul_le_self _ _
            · have := Nat.lt_div_mul_add (a := (r j : ℕ)) hs
              rw [← hj]; exact this
          · intro i _ j _ hij
            exact σ.symm.injective (Fin.ext hij)
      _ = s := by simp
  · rintro k ⟨i, hi⟩
    refine le_antisymm ?_ ?_
    · calc (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ (Finset.Ico (k * s) (k * s + s)).card := by
            refine Finset.card_le_card_of_injOn (fun j ↦ (r j : ℕ)) ?_ ?_
            · intro j hj
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hj
              simp only [Finset.coe_Ico, mem_Ico]
              constructor
              · rw [← hj]; exact Nat.div_mul_le_self _ _
              · have := Nat.lt_div_mul_add (a := (r j : ℕ)) hs
                rw [← hj]; exact this
            · intro i _ j _ hij
              exact σ.symm.injective (Fin.ext hij)
        _ = s := by simp
    have hbound : (k + 1) * s ≤ (r i : ℕ) :=
      (Nat.mul_le_mul_right s hi).trans (Nat.div_mul_le_self _ _)
    have hlt : ∀ t < s, k * s + t < p := fun t ht ↦ by
      have := (r i).isLt
      nlinarith
    calc s = (Finset.range s).card := (Finset.card_range s).symm
      _ ≤ _ := by
          refine Finset.card_le_card_of_injOn
            (fun t ↦ if ht : t < s then σ ⟨k * s + t, hlt t ht⟩ else σ ⟨0, by omega⟩) ?_ ?_
          · intro t ht
            have ht' : t < s := Finset.mem_range.mp ht
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq, ht',
              dite_true, ℓ, r, Equiv.symm_apply_apply]
            rw [show k * s + t = t + k * s by ring, Nat.add_mul_div_right _ _ hs,
              Nat.div_eq_of_lt ht', zero_add]
          · intro t ht t' ht' h
            have ht1 : t < s := Finset.mem_range.mp ht
            have ht2 : t' < s := Finset.mem_range.mp ht'
            simp only [ht1, ht2, dite_true] at h
            have := congrArg Fin.val (σ.injective h)
            simp at this
            exact this

/-- Square-root lifting: if at most `s` values lie in `[m, M]` with `0 ≤ m`, and `m = 0`
unless there are exactly `s` of them, then their Euclidean norm is at most their sum divided
by `√s` plus `√s (M - m) / 4`. -/
theorem sqrt_sum_sq_le_lifting {ι : Type*} (B : Finset ι) (a : ι → ℝ) {s : ℕ} (hs : 0 < s)
    (hB : B.card ≤ s) {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M)
    (ha : ∀ j ∈ B, m ≤ a j ∧ a j ≤ M) (hfull : B.card < s → m = 0) :
    Real.sqrt (∑ j ∈ B, a j ^ 2) ≤ (∑ j ∈ B, a j) / Real.sqrt s + Real.sqrt s / 4 * (M - m) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hsR
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hsR.le
  set T1 := ∑ j ∈ B, a j with hT1
  set T2 := ∑ j ∈ B, a j ^ 2 with hT2
  have hT1nn : 0 ≤ T1 := Finset.sum_nonneg fun j hj ↦ hm.trans (ha j hj).1
  have h1 : T2 ≤ (M + m) * T1 - B.card * (M * m) := by
    have : 0 ≤ ∑ j ∈ B, (M - a j) * (a j - m) := Finset.sum_nonneg fun j hj ↦
      mul_nonneg (by linarith [(ha j hj).2]) (by linarith [(ha j hj).1])
    have e : ∑ j ∈ B, (M - a j) * (a j - m) = (M + m) * T1 - T2 - B.card * (M * m) := by
      simp only [hT1, hT2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    linarith
  have h2 : (B.card : ℝ) * (M * m) = s * (M * m) := by
    rcases hB.lt_or_eq with h | h
    · rw [hfull h]; ring
    · rw [h]
  rw [h2] at h1
  rw [Real.sqrt_le_iff]
  constructor
  · have : 0 ≤ M - m := by linarith
    positivity
  · rw [add_sq, div_pow, hss, mul_pow, div_pow, hss]
    have e : 2 * (T1 / Real.sqrt s) * (Real.sqrt s / 4 * (M - m)) = T1 * (M - m) / 2 := by
      field_simp; ring
    rw [e]
    have key : (M + m) * T1 - s * (M * m) ≤
        T1 ^ 2 / s + T1 * (M - m) / 2 + s / 4 ^ 2 * (M - m) ^ 2 := by
      have : 0 ≤ (T1 / s - m - (M - m) / 4) ^ 2 * s + m * (M - m) / 2 * s := by
        have : 0 ≤ M - m := by linarith
        positivity
      have e2 : T1 ^ 2 / s + T1 * (M - m) / 2 + s / 4 ^ 2 * (M - m) ^ 2 -
          ((M + m) * T1 - s * (M * m)) =
          (T1 / s - m - (M - m) / 4) ^ 2 * s + m * (M - m) / 2 * s := by
        field_simp; ring
      linarith
    linarith

/-- If `2 lam c ≤ lam ^ 2 D + 1` for every real `lam`, then `c ≤ √D`. -/
theorem le_sqrt_of_forall_two_mul_le {c D : ℝ} (h : ∀ lam : ℝ, 2 * lam * c ≤ lam ^ 2 * D + 1) :
    c ≤ Real.sqrt D := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (Real.sqrt_nonneg _)
  have h1 := h (1 / c)
  have e1 : 2 * (1 / c) * c = 2 := by field_simp
  have e2 : (1 / c) ^ 2 * D = D / c ^ 2 := by field_simp
  rw [e1, e2] at h1
  have : c ^ 2 ≤ D := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < c ^ 2)).mp (by linarith : 1 ≤ D / c ^ 2)
    linarith
  exact Real.le_sqrt_of_sq_le this

/-- Sharpened restricted orthogonality: if `‖A x‖² = (1 + t) ‖x‖²`, then for `s`-sparse
vectors with disjoint supports `|⟪A x, A y⟫| ≤ √(δ² - t²) ‖x‖ ‖y‖` when `A` has the RIP of
order `2 s` with constant `δ > 0`. -/
theorem inner_apply_le_sqrt_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 < δ)
    (hrip : HasRestrictedIsometry A (2 * s) δ) (x y : EuclideanSpace ℝ (Fin p))
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) (hxy : ∀ j, x j = 0 ∨ y j = 0) (t : ℝ)
    (ht : ‖A x‖ ^ 2 = (1 + t) * ‖x‖ ^ 2) :
    |⟪A x, A y⟫| ≤ Real.sqrt (δ ^ 2 - t ^ 2) * ‖x‖ * ‖y‖ := by
  have hinner : ⟪x, y⟫ = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rcases hxy j with h | h <;> simp [h]
  rcases (norm_nonneg x).eq_or_lt with hx0 | hx0
  · rw [eq_comm, norm_eq_zero] at hx0; simp [hx0]
  rcases (norm_nonneg y).eq_or_lt with hy0 | hy0
  · rw [eq_comm, norm_eq_zero] at hy0; simp [hy0]
  set X := ‖x‖
  set Y := ‖y‖
  set c := ⟪A x, A y⟫
  set q := ‖A y‖ ^ 2
  have hexpA : ∀ a b : ℝ, ‖A (a • x + b • y)‖ ^ 2 =
      a ^ 2 * ((1 + t) * X ^ 2) + 2 * a * b * c + b ^ 2 * q := by
    intro a b
    rw [map_add, map_smul, map_smul, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, ht]
    simp only [RCLike.conj_to_real]
    ring
  have hexp : ∀ a b : ℝ, ‖a • x + b • y‖ ^ 2 = a ^ 2 * X ^ 2 + b ^ 2 * Y ^ 2 := by
    intro a b
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hinner,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp only [mul_zero, add_zero]
    rfl
  have hup : ∀ a b : ℝ, a ^ 2 * ((1 + t) * X ^ 2) + 2 * a * b * c + b ^ 2 * q ≤
      (1 + δ) * (a ^ 2 * X ^ 2 + b ^ 2 * Y ^ 2) := fun a b ↦ by
    rw [← hexpA, ← hexp]; exact (hrip _ (sparsity_smul_add_smul_le x y a b hx hy)).2
  have hlow : ∀ a b : ℝ, (1 - δ) * (a ^ 2 * X ^ 2 + b ^ 2 * Y ^ 2) ≤
      a ^ 2 * ((1 + t) * X ^ 2) + 2 * a * b * c + b ^ 2 * q := fun a b ↦ by
    rw [← hexpA, ← hexp]; exact (hrip _ (sparsity_smul_add_smul_le x y a b hx hy)).1
  set c' := c / (X * Y) with hc'
  set D := δ ^ 2 - t ^ 2
  have hcomb : ∀ (ε : ℝ), ε ^ 2 = 1 → ∀ lam : ℝ, 2 * lam * (ε * c') ≤ lam ^ 2 * D + 1 := by
    intro ε hε lam
    set α := (δ + t) * lam
    set β := (δ - t) * lam
    have h1 := hup (α / X) (ε / Y)
    have h2 := hlow (β / X) (-ε / Y)
    have e1 : ∀ r : ℝ, (r / X) ^ 2 * ((1 + t) * X ^ 2) = r ^ 2 * (1 + t) := fun r ↦ by
      field_simp
    have e2 : ∀ r : ℝ, (r / X) ^ 2 * X ^ 2 = r ^ 2 := fun r ↦ by field_simp
    have e3 : ∀ r e : ℝ, 2 * (r / X) * (e / Y) * c = 2 * r * e * c' := fun r e ↦ by
      rw [hc']; field_simp
    have e4 : ∀ e : ℝ, (e / Y) ^ 2 * Y ^ 2 = e ^ 2 := fun e ↦ by field_simp
    rw [e1, e2, e3, e4] at h1 h2
    have e5 : (-ε / Y) ^ 2 = (ε / Y) ^ 2 := by ring
    rw [e5, show (-ε) ^ 2 = ε ^ 2 by ring, hε] at h2
    rw [hε] at h1
    have h3 : 2 * (α + β) * (ε * c') ≤ α ^ 2 * (δ - t) + β ^ 2 * (δ + t) + 2 * δ := by
      nlinarith
    have e6 : α + β = 2 * δ * lam := by ring
    have e7 : α ^ 2 * (δ - t) + β ^ 2 * (δ + t) + 2 * δ = 2 * δ * (lam ^ 2 * D + 1) := by ring
    rw [e6, e7] at h3
    have : 2 * δ * (2 * lam * (ε * c')) ≤ 2 * δ * (lam ^ 2 * D + 1) := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hpos := le_sqrt_of_forall_two_mul_le (hcomb 1 (by norm_num))
  have hneg := le_sqrt_of_forall_two_mul_le (hcomb (-1) (by norm_num))
  simp only [one_mul, neg_one_mul] at hpos hneg
  have habs : |c'| ≤ Real.sqrt D := abs_le.mpr ⟨by linarith, hpos⟩
  have hXY : 0 < X * Y := mul_pos hx0 hy0
  have : c = c' * (X * Y) := by rw [hc']; field_simp
  rw [this, abs_mul, abs_of_pos hXY]
  calc |c'| * (X * Y) ≤ Real.sqrt D * (X * Y) := mul_le_mul_of_nonneg_right habs hXY.le
    _ = _ := by ring

/-- A sum of nonnegative values over a set `S` is at most the sum over a set `B` that
dominates its complement, provided `S ⊆ B` or `S` has at most as many elements as `B`. -/
theorem sum_le_sum_of_dominates {ι : Type*} [DecidableEq ι] (S B : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hdom : ∀ i ∈ B, ∀ j ∉ B, f j ≤ f i)
    (hcard : S ⊆ B ∨ S.card ≤ B.card) : ∑ j ∈ S, f j ≤ ∑ j ∈ B, f j := by
  rcases hcard with hsub | hcard
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ hf j
  by_cases hsub : S ⊆ B
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ hf j
  obtain ⟨j₀, hj₀S, hj₀B⟩ := Finset.not_subset.mp hsub
  set I := S ∩ B with hI
  have hIS : I ⊆ S := Finset.inter_subset_left
  have hIB : I ⊆ B := Finset.inter_subset_right
  have hsumS := Finset.sum_sdiff (f := f) hIS
  have hsumB := Finset.sum_sdiff (f := f) hIB
  have hcardS := Finset.card_sdiff_add_card_eq_card hIS
  have hcardB := Finset.card_sdiff_add_card_eq_card hIB
  have hmem : j₀ ∈ S \ I := Finset.mem_sdiff.mpr ⟨hj₀S, fun h ↦ hj₀B (hIB h)⟩
  have hne1 : (S \ I).Nonempty := ⟨j₀, hmem⟩
  set m := (S \ I).sup' hne1 f with hm
  have hm0 : 0 ≤ m := (hf j₀).trans (Finset.le_sup' f hmem)
  have h1 := Finset.sum_le_card_nsmul (S \ I) f m (fun j hj ↦ Finset.le_sup' f hj)
  have h2 := Finset.card_nsmul_le_sum (B \ I) f m (fun i hi ↦ by
    refine Finset.sup'_le _ _ fun j hj ↦ ?_
    have hiB : i ∈ B := (Finset.mem_sdiff.mp hi).1
    have hjB : j ∉ B := by
      intro h
      obtain ⟨hjS, hjI⟩ := Finset.mem_sdiff.mp hj
      exact hjI (Finset.mem_inter.mpr ⟨hjS, h⟩)
    exact hdom i hiB j hjB)
  rw [nsmul_eq_mul] at h1 h2
  have hcd : ((S \ I).card : ℝ) ≤ ((B \ I).card : ℝ) := by
    exact_mod_cast (show (S \ I).card ≤ (B \ I).card by omega)
  have h3 := mul_le_mul_of_nonneg_right hcd hm0
  linarith

/-- The robust null space constant `ρ(δ) = δ / (√(1 - δ²) - δ / 4)` of the restricted
isometry analysis of basis pursuit. -/
def ripNullspaceRho (δ : ℝ) : ℝ := 4 * δ / (4 * Real.sqrt (1 - δ ^ 2) - δ)

/-- The robust null space constant `τ(δ) = √(1 + δ) / (√(1 - δ²) - δ / 4)` written as
`4 √(1 - δ²) / ((4 √(1 - δ²) - δ) √(1 - δ))`. -/
def ripNullspaceTau (δ : ℝ) : ℝ :=
  4 * Real.sqrt (1 - δ ^ 2) / ((4 * Real.sqrt (1 - δ ^ 2) - δ) * Real.sqrt (1 - δ))

/-- The constants of the robust null space property: for `0 ≤ δ < 4 / √41`,
`0 ≤ ρ(δ) < 1` and `τ(δ) > 0`. -/
theorem ripNullspace_constants {δ : ℝ} (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) :
    0 < 4 * Real.sqrt (1 - δ ^ 2) - δ ∧ 0 ≤ ripNullspaceRho δ ∧ ripNullspaceRho δ < 1 ∧
      0 < ripNullspaceTau δ ∧ δ < 1 := by
  obtain ⟨h0, h1⟩ := hδ
  have h41 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hs41 : 0 < Real.sqrt 41 := by positivity
  have hδ2 : δ ^ 2 < 16 / 41 := by
    rw [lt_div_iff₀ hs41] at h1
    have : (δ * Real.sqrt 41) ^ 2 < 4 ^ 2 := by
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    rw [mul_pow, h41] at this
    linarith
  have hδ1 : δ < 1 := by nlinarith
  have hr2 : Real.sqrt (1 - δ ^ 2) ^ 2 = 1 - δ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ Real.sqrt (1 - δ ^ 2) := Real.sqrt_nonneg _
  have h5 : 5 * δ < 4 * Real.sqrt (1 - δ ^ 2) := by nlinarith
  have hden : 0 < 4 * Real.sqrt (1 - δ ^ 2) - δ := by linarith
  refine ⟨hden, div_nonneg (by linarith) hden.le, (div_lt_one hden).mpr (by linarith), ?_, hδ1⟩
  have : 0 < Real.sqrt (1 - δ ^ 2) := by nlinarith
  have : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
  unfold ripNullspaceTau
  positivity

/-- GAPS 103.49, robust null space property: if `A` has the RIP of order `2 s` with constant
`δ < 4 / √41`, then `‖v_S‖₂ ≤ ρ(δ) / √s ‖v_{Sᶜ}‖₁ + τ(δ) ‖A v‖` for every `v` and every set
`S` of at most `s` coordinates. -/
theorem robust_nullspace_property_of_hasRestrictedIsometry {n p s : ℕ} (hs : 0 < s)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) (hrip : HasRestrictedIsometry A (2 * s) δ)
    (v : EuclideanSpace ℝ (Fin p)) (S : Finset (Fin p)) (hS : S.card ≤ s) :
    Real.sqrt (∑ j ∈ S, v j ^ 2) ≤
      ripNullspaceRho δ / Real.sqrt s * restrictedL1Norm Sᶜ v + ripNullspaceTau δ * ‖A v‖ := by
  classical
  obtain ⟨hden, hρ0, hρ1, hτ0, hδ1⟩ := ripNullspace_constants hδ
  have hδ0 : 0 ≤ δ := hδ.1
  obtain ⟨ℓ, hcmp, hcard, hfull, hℓlt⟩ := exists_decreasing_blocks (fun j ↦ v j) hs
  set lev : ℕ → Finset (Fin p) := fun k ↦ Finset.univ.filter fun j ↦ ℓ j = k with hlev
  have hmemlev : ∀ k j, j ∈ lev k ↔ ℓ j = k := fun k j ↦ by simp [lev]
  set vk : ℕ → EuclideanSpace ℝ (Fin p) :=
    fun k ↦ WithLp.toLp 2 (fun j ↦ if ℓ j = k then v j else 0) with hvk
  have hvk_apply : ∀ k j, vk k j = if ℓ j = k then v j else 0 := fun k j ↦ rfl
  have hsp : ∀ k, sparsity (vk k) ≤ s := by
    intro k
    refine le_trans (Finset.card_le_card ?_) (hcard k)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvk_apply] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    exact hj (ite_eq_right h)
  have hdisj : ∀ k k', k ≠ k' → ∀ j, vk k j = 0 ∨ vk k' j = 0 := by
    intro k k' hkk j
    simp only [hvk_apply]
    by_cases h : ℓ j = k
    · right; rw [ite_eq_right]; rw [h]; exact hkk
    · left; rw [ite_eq_right h]
  have hnorm_sq : ∀ k, ‖vk k‖ ^ 2 = ∑ j ∈ lev k, v j ^ 2 := by
    intro k
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hvk_apply, Real.norm_eq_abs, sq_abs, lev, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hnorm : ∀ k, ‖vk k‖ = Real.sqrt (∑ j ∈ lev k, |v j| ^ 2) := by
    intro k
    simp only [sq_abs]
    rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hdecomp : v = vk 0 + ∑ k ∈ Finset.range p, vk (k + 1) := by
    ext j
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply]
    change v j = vk 0 j + ∑ c ∈ Finset.range p, vk (c + 1) j
    simp only [hvk_apply]
    rcases Nat.eq_zero_or_pos (ℓ j) with h0 | h0
    · rw [ite_eq_left h0, Finset.sum_eq_zero fun k _ ↦ ite_eq_right (by omega)]; ring
    · obtain ⟨m, hm⟩ : ∃ m, ℓ j = m + 1 := ⟨ℓ j - 1, by omega⟩
      rw [ite_eq_right (by omega), zero_add, Finset.sum_eq_single m]
      · rw [ite_eq_left hm]
      · intro b _ hb; rw [ite_eq_right (by omega)]
      · intro hm'; exact absurd (Finset.mem_range.mpr (by have := hℓlt j; omega)) hm'
  set L : ℕ → ℝ := fun k ↦ ∑ j ∈ lev k, |v j| with hL
  have hL0 : ∀ k, 0 ≤ L k := fun k ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hsumL : ∑ k ∈ Finset.range p, L k = restrictedL1Norm Finset.univ v := by
    simp only [L, lev, restrictedL1Norm]
    exact Finset.sum_fiberwise_of_maps_to (fun j _ ↦ Finset.mem_range.mpr (hℓlt j)) _
  have hLp : L p = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have := hℓlt j
    rw [hmemlev] at hj; omega
  have hsumL1 : ∑ k ∈ Finset.range p, L (k + 1) = restrictedL1Norm Finset.univ v - L 0 := by
    have := Finset.sum_range_succ' L p
    rw [Finset.sum_range_succ, hLp, add_zero, hsumL] at this
    linarith
  -- block maxima and minima
  set Mx : ℕ → ℝ := fun k ↦ if h : (lev k).Nonempty then (lev k).sup' h (fun j ↦ |v j|) else 0
    with hMx
  set Mn : ℕ → ℝ := fun k ↦ if h : (lev k).Nonempty ∧ (lev k).card = s then
    (lev k).inf' h.1 (fun j ↦ |v j|) else 0 with hMn
  have hMx_ge : ∀ k, ∀ j ∈ lev k, |v j| ≤ Mx k := by
    intro k j hj
    have hne : (lev k).Nonempty := ⟨j, hj⟩
    simp only [hMx]
    rw [dite_eq_left hne]
    exact Finset.le_sup' (fun j ↦ |v j|) hj
  have hMn_le : ∀ k, ∀ j ∈ lev k, Mn k ≤ |v j| := by
    intro k j hj
    simp only [hMn]
    split_ifs with h
    · exact Finset.inf'_le (fun j ↦ |v j|) hj
    · exact abs_nonneg _
  have hMn0 : ∀ k, 0 ≤ Mn k := by
    intro k
    simp only [hMn]
    split_ifs with h
    · exact Finset.le_inf' _ _ fun j _ ↦ abs_nonneg _
    · exact le_rfl
  have hMnMx : ∀ k, Mn k ≤ Mx k := by
    intro k
    by_cases h : (lev k).Nonempty
    · obtain ⟨j, hj⟩ := h
      exact (hMn_le k j hj).trans (hMx_ge k j hj)
    · have h1 : Mx k = 0 := by simp only [hMx]; rw [dite_eq_right h]
      have h2 : Mn k = 0 := by
        simp only [hMn]
        rw [dite_eq_right (fun h' : (lev k).Nonempty ∧ (lev k).card = s ↦ h h'.1)]
      rw [h1, h2]
  have hMn_full : ∀ k, (lev k).card < s → Mn k = 0 := by
    intro k hk
    simp only [hMn]
    rw [dite_eq_right (fun h' : (lev k).Nonempty ∧ (lev k).card = s ↦ by omega)]
  have hstep : ∀ k, Mx (k + 1) ≤ Mn k := by
    intro k
    by_cases h : (lev (k + 1)).Nonempty
    · obtain ⟨i, hi⟩ := h
      have hc : (lev k).card = s := hfull k ⟨i, by rw [hmemlev] at hi; omega⟩
      have hne : (lev k).Nonempty := Finset.card_pos.mp (by omega)
      have hne1 : (lev (k + 1)).Nonempty := ⟨i, hi⟩
      have hne2 : (lev k).Nonempty ∧ (lev k).card = s := ⟨hne, hc⟩
      simp only [hMx, hMn]
      rw [dite_eq_left hne1, dite_eq_left hne2]
      refine Finset.sup'_le _ _ fun a ha ↦ Finset.le_inf' _ _ fun b hb ↦ ?_
      rw [hmemlev] at ha hb
      exact hcmp a b (by omega)
    · simp only [hMx]; rw [dite_eq_right h]; exact hMn0 k
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
  have hMx1 : Real.sqrt s * Mx 1 ≤ ‖vk 0‖ := by
    by_cases h : (lev 1).Nonempty
    · obtain ⟨i, hi⟩ := h
      have hc : (lev 0).card = s := hfull 0 ⟨i, by rw [hmemlev] at hi; omega⟩
      have hMx0 : 0 ≤ Mx 1 := (abs_nonneg _).trans (hMx_ge 1 i hi)
      have hb : ∀ b ∈ lev 0, Mx 1 ≤ |v b| := by
        intro b hb
        have hne1 : (lev 1).Nonempty := ⟨i, hi⟩
        simp only [hMx]
        rw [dite_eq_left hne1]
        refine Finset.sup'_le _ _ fun a ha ↦ ?_
        rw [hmemlev] at ha hb
        exact hcmp a b (by omega)
      refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
      rw [hnorm_sq, mul_pow, hss]
      calc (s : ℝ) * Mx 1 ^ 2 = ∑ _j ∈ lev 0, Mx 1 ^ 2 := by
            rw [Finset.sum_const, hc, nsmul_eq_mul]
        _ ≤ ∑ j ∈ lev 0, v j ^ 2 := Finset.sum_le_sum fun j hj ↦ by
            rw [← sq_abs (v j)]
            exact pow_le_pow_left₀ hMx0 (hb j hj) 2
    · simp only [hMx]; rw [dite_eq_right h, mul_zero]; exact norm_nonneg _
  have htele : ∀ K, ∑ k ∈ Finset.range (K + 1), (Mx (k + 1) - Mn (k + 1)) ≤ Mx 1 - Mn (K + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have := hstep (K + 1)
      linarith
  have htele' : ∑ k ∈ Finset.range p, (Mx (k + 1) - Mn (k + 1)) ≤ Mx 1 := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · rw [hp]; simp only [Finset.range_zero, Finset.sum_empty]
      exact (hMn0 1).trans (hMnMx 1)
    · have := htele (p - 1)
      rw [Nat.sub_add_cancel hp] at this
      linarith [hMn0 p]
  set X := ∑ k ∈ Finset.range p, ‖vk (k + 1)‖ with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ ↦ norm_nonneg _
  set Sc := restrictedL1Norm Finset.univ v - L 0 with hSc
  have hXle : X ≤ Sc / Real.sqrt s + ‖vk 0‖ / 4 := by
    have hblock : ∀ k ∈ Finset.range p, ‖vk (k + 1)‖ ≤
        L (k + 1) / Real.sqrt s + Real.sqrt s / 4 * (Mx (k + 1) - Mn (k + 1)) := by
      intro k _
      rw [hnorm]
      exact sqrt_sum_sq_le_lifting (lev (k + 1)) (fun j ↦ |v j|) hs (hcard (k + 1)) (hMn0 _)
        (hMnMx _) (fun j hj ↦ ⟨hMn_le _ j hj, hMx_ge _ j hj⟩) (hMn_full _)
    calc X ≤ ∑ k ∈ Finset.range p,
          (L (k + 1) / Real.sqrt s + Real.sqrt s / 4 * (Mx (k + 1) - Mn (k + 1))) :=
          Finset.sum_le_sum hblock
      _ = Sc / Real.sqrt s + Real.sqrt s / 4 * ∑ k ∈ Finset.range p, (Mx (k + 1) - Mn (k + 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hsumL1]
      _ ≤ Sc / Real.sqrt s + Real.sqrt s / 4 * Mx 1 := by gcongr
      _ ≤ Sc / Real.sqrt s + ‖vk 0‖ / 4 := by linarith
  -- the main estimate for the leading block
  set N0 := ‖vk 0‖ with hN0
  have hSc0 : 0 ≤ Sc := by
    rw [← hsumL1]; exact Finset.sum_nonneg fun k _ ↦ hL0 _
  have hmain : N0 ≤ ripNullspaceRho δ / Real.sqrt s * Sc + ripNullspaceTau δ * ‖A v‖ := by
    rcases (norm_nonneg (vk 0)).eq_or_lt with h0 | h0
    · rw [hN0, ← h0]
      exact add_nonneg (mul_nonneg (div_nonneg hρ0 hsqrt.le) hSc0)
        (mul_nonneg hτ0.le (norm_nonneg _))
    rw [← hN0] at h0
    set t := ‖A (vk 0)‖ ^ 2 / N0 ^ 2 - 1 with htdef
    have ht : ‖A (vk 0)‖ ^ 2 = (1 + t) * N0 ^ 2 := by rw [htdef]; field_simp; ring
    have hrip0 := hrip (vk 0) ((hsp 0).trans (by omega))
    rw [ht] at hrip0
    have hN2 : 0 < N0 ^ 2 := by positivity
    have htlo : -δ ≤ t := by
      have := le_of_mul_le_mul_right hrip0.1 hN2; linarith
    have hthi : t ≤ δ := by
      have := le_of_mul_le_mul_right hrip0.2 hN2; linarith
    set D := δ ^ 2 - t ^ 2 with hD
    have hinner_k : ∀ k ∈ Finset.range p,
        |⟪A (vk 0), A (vk (k + 1))⟫| ≤ Real.sqrt D * N0 * ‖vk (k + 1)‖ := by
      intro k _
      rcases hδ0.eq_or_lt with hδz | hδpos
      · have := inner_apply_le_of_hasRestrictedIsometry A δ hrip _ _ (hsp 0) (hsp (k + 1))
          (hdisj 0 (k + 1) (by omega))
        rw [← hδz, zero_mul, zero_mul] at this
        exact this.trans (by positivity)
      · exact inner_apply_le_sqrt_of_hasRestrictedIsometry A hδpos hrip _ _ (hsp 0)
          (hsp (k + 1)) (hdisj 0 (k + 1) (by omega)) t ht
    have hAsq : ‖A (vk 0)‖ ^ 2 ≤ ‖A (vk 0)‖ * ‖A v‖ + Real.sqrt D * N0 * X := by
      have h0' : ⟪A (vk 0), A v⟫ = ‖A (vk 0)‖ ^ 2 +
          ∑ k ∈ Finset.range p, ⟪A (vk 0), A (vk (k + 1))⟫ := by
        conv_lhs => rw [hdecomp]
        rw [map_add, inner_add_right, map_sum, inner_sum, real_inner_self_eq_norm_sq]
      have hle1 : ⟪A (vk 0), A v⟫ ≤ ‖A (vk 0)‖ * ‖A v‖ := real_inner_le_norm _ _
      have hb : ∀ k ∈ Finset.range p, -(Real.sqrt D * N0 * ‖vk (k + 1)‖) ≤
          ⟪A (vk 0), A (vk (k + 1))⟫ := fun k hk ↦ (abs_le.mp (hinner_k k hk)).1
      have := Finset.sum_le_sum hb
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at this
      linarith
    have h1t : 0 < 1 + t := by linarith
    set q := Real.sqrt (1 + t) with hq
    have hq0 : 0 < q := Real.sqrt_pos.mpr h1t
    have hq2 : q ^ 2 = 1 + t := Real.sq_sqrt h1t.le
    have hAv0 : ‖A (vk 0)‖ = q * N0 := by
      rw [← Real.sqrt_sq (norm_nonneg (A (vk 0))), ht, Real.sqrt_mul h1t.le,
        Real.sqrt_sq h0.le]
    rw [hAv0] at hAsq
    have hstep1 : q ^ 2 * N0 ≤ q * ‖A v‖ + Real.sqrt D * X := by
      have : N0 * (q ^ 2 * N0) ≤ N0 * (q * ‖A v‖ + Real.sqrt D * X) := by
        have e1 : N0 * (q ^ 2 * N0) = (q * N0) ^ 2 := by ring
        have e2 : N0 * (q * ‖A v‖ + Real.sqrt D * X) =
            q * N0 * ‖A v‖ + Real.sqrt D * N0 * X := by ring
        rw [e1, e2]; exact hAsq
      exact le_of_mul_le_mul_left this h0
    set r := Real.sqrt (1 - δ ^ 2) with hr
    have hδsq : δ ^ 2 < 1 := pow_lt_one₀ hδ0 hδ1 two_ne_zero
    have hr2 : r ^ 2 = 1 - δ ^ 2 := Real.sq_sqrt (by linarith)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hDr : Real.sqrt D * r ≤ q ^ 2 * δ := by
      rcases le_or_gt D 0 with hDn | hDp
      · rw [Real.sqrt_eq_zero'.mpr hDn, zero_mul]; positivity
      have hsD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDp.le
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
      rw [mul_pow, mul_pow, hsD, hr2, hq2, hD]
      have e : (1 + t) ^ 2 * δ ^ 2 - (δ ^ 2 - t ^ 2) * (1 - δ ^ 2) = (t + δ ^ 2) ^ 2 := by ring
      linarith [sq_nonneg (t + δ ^ 2)]
    have hstep2 : N0 ≤ ‖A v‖ / q + δ / r * X := by
      have hsDle : Real.sqrt D ≤ q ^ 2 * δ / r := by rw [le_div_iff₀ hr0]; exact hDr
      have : q ^ 2 * N0 ≤ q ^ 2 * (‖A v‖ / q + δ / r * X) := by
        have e : q ^ 2 * (‖A v‖ / q + δ / r * X) = q * ‖A v‖ + q ^ 2 * δ / r * X := by
          field_simp
        rw [e]
        have := mul_le_mul_of_nonneg_right hsDle hX0
        linarith
      exact le_of_mul_le_mul_left this (by positivity)
    have h1δ : 0 < 1 - δ := by linarith
    have hqge : Real.sqrt (1 - δ) ≤ q := Real.sqrt_le_sqrt (by linarith)
    have hsq1δ : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr h1δ
    have hstep3 : ‖A v‖ / q ≤ ‖A v‖ / Real.sqrt (1 - δ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hsq1δ hqge
    have hstep4 : N0 ≤ ‖A v‖ / Real.sqrt (1 - δ) + δ / r * (Sc / Real.sqrt s + N0 / 4) := by
      have : δ / r * X ≤ δ / r * (Sc / Real.sqrt s + N0 / 4) :=
        mul_le_mul_of_nonneg_left hXle (div_nonneg hδ0 hr0.le)
      linarith
    have hkey : (4 * r - δ) * N0 ≤
        4 * r * (‖A v‖ / Real.sqrt (1 - δ)) + 4 * δ * (Sc / Real.sqrt s) := by
      have e : 4 * r * (δ / r * (Sc / Real.sqrt s + N0 / 4)) =
          4 * δ * (Sc / Real.sqrt s) + δ * N0 := by field_simp
      have := mul_le_mul_of_nonneg_left hstep4 (by positivity : (0:ℝ) ≤ 4 * r)
      rw [mul_add, e] at this
      linarith
    have hfinal : N0 ≤ (4 * r * (‖A v‖ / Real.sqrt (1 - δ)) + 4 * δ * (Sc / Real.sqrt s)) /
        (4 * r - δ) := by
      rw [le_div_iff₀ hden]; linarith
    refine hfinal.trans (le_of_eq ?_)
    unfold ripNullspaceRho ripNullspaceTau
    rw [← hr]
    field_simp
    ring
  -- comparison with an arbitrary set of at most `s` coordinates
  have hcardS : S ⊆ lev 0 ∨ S.card ≤ (lev 0).card := by
    by_cases h : ∃ i, 0 < ℓ i
    · right; rw [hfull 0 h]; exact hS
    · left
      push Not at h
      intro j _
      rw [hmemlev]; exact Nat.le_zero.mp (h j)
  have hdom : ∀ i ∈ lev 0, ∀ j ∉ lev 0, |v j| ≤ |v i| := by
    intro i hi j hj
    rw [hmemlev] at hi hj
    exact hcmp j i (by omega)
  have h2 : ∑ j ∈ S, v j ^ 2 ≤ ∑ j ∈ lev 0, v j ^ 2 :=
    sum_le_sum_of_dominates S (lev 0) (fun j ↦ v j ^ 2) (fun j ↦ sq_nonneg _)
      (fun i hi j hj ↦ by
        rw [← sq_abs (v j), ← sq_abs (v i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hdom i hi j hj) 2) hcardS
  have h1 : restrictedL1Norm S v ≤ L 0 :=
    sum_le_sum_of_dominates S (lev 0) (fun j ↦ |v j|) (fun j ↦ abs_nonneg _) hdom hcardS
  have hSc_le : Sc ≤ restrictedL1Norm Sᶜ v := by
    have := restrictedL1Norm_add_compl S v
    rw [hSc]; linarith
  calc Real.sqrt (∑ j ∈ S, v j ^ 2) ≤ Real.sqrt (∑ j ∈ lev 0, v j ^ 2) := Real.sqrt_le_sqrt h2
    _ = N0 := by rw [hN0, ← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := hmain
    _ ≤ _ := by gcongr

/-- The square root is subadditive on nonnegative reals. -/
theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  have := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  linarith

/-- GAPS 103.49: stable basis pursuit, with constants depending only on the RIP bound. -/
theorem basis_pursuit_error_bound_of_hasRestrictedIsometry
    (δ : ℝ) (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) :
    ∃ C > 0, ∃ D > 0, ∀ (n p s : ℕ), 0 < s →
      ∀ A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n),
        HasRestrictedIsometry A (2 * s) δ → ∀ (β b : EuclideanSpace ℝ (Fin p))
        (y : EuclideanSpace ℝ (Fin n)) (η : ℝ), 0 ≤ η → ‖A β - y‖ ≤ η →
        ‖A b - y‖ ≤ η →
        (∀ t, ‖A t - y‖ ≤ η → restrictedL1Norm Finset.univ b ≤ restrictedL1Norm Finset.univ t) →
        restrictedL1Norm Finset.univ (b - β) ≤ C * bestSparseL1Error s β + D * Real.sqrt s * η ∧
        ‖b - β‖ ≤ C / Real.sqrt s * bestSparseL1Error s β + D * η := by
  classical
  obtain ⟨_, hρ0, hρ1, hτ0, _⟩ := ripNullspace_constants hδ
  set ρ := ripNullspaceRho δ with hρ
  set τ := ripNullspaceTau δ with hτ
  have h1ρ : 0 < 1 - ρ := by linarith
  set C₁ := 2 * (1 + ρ) / (1 - ρ) with hC₁
  set D₁ := 4 * τ / (1 - ρ) with hD₁
  have hC₁0 : 0 < C₁ := by positivity
  have hD₁0 : 0 < D₁ := by positivity
  refine ⟨(1 + ρ) * C₁, by positivity, (1 + ρ) * D₁ + 2 * τ, by positivity, ?_⟩
  intro n p s hs A hrip β b y η hη hβ hb hmin
  set v := b - β with hv
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hAv : ‖A v‖ ≤ 2 * η := by
    have : A v = (A b - y) - (A β - y) := by rw [hv, map_sub]; abel
    rw [this]
    calc ‖(A b - y) - (A β - y)‖ ≤ ‖A b - y‖ + ‖A β - y‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  have hbβ := hmin β hβ
  have hnsp := robust_nullspace_property_of_hasRestrictedIsometry hs A hδ hrip
  -- the `ℓ¹` bound against an arbitrary `s`-sparse vector
  have hl1w : ∀ w : EuclideanSpace ℝ (Fin p), sparsity w ≤ s →
      restrictedL1Norm Finset.univ v ≤
        C₁ * restrictedL1Norm Finset.univ (β - w) + D₁ * Real.sqrt s * η := by
    intro w hw
    set S := Finset.univ.filter fun j ↦ w j ≠ 0 with hS
    have hScard : S.card ≤ s := hw
    have hvS : restrictedL1Norm S v ≤ ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * (2 * η) := by
      have h1 := hnsp v S hScard
      have hCS : restrictedL1Norm S v ≤ Real.sqrt s * Real.sqrt (∑ j ∈ S, v j ^ 2) := by
        have hsq : restrictedL1Norm S v ^ 2 ≤ S.card * ∑ j ∈ S, v j ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j ↦ |v j|)
          simp only [sq_abs] at this
          exact this
        have hle : (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 ≤ s * ∑ j ∈ S, v j ^ 2 := by
          gcongr
        rw [← Real.sqrt_mul hspos.le]
        refine Real.le_sqrt_of_sq_le (hsq.trans hle)
      have h2 : Real.sqrt s * Real.sqrt (∑ j ∈ S, v j ^ 2) ≤
          ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * ‖A v‖ := by
        have := mul_le_mul_of_nonneg_left h1 hsqrt.le
        have e : Real.sqrt s * (ρ / Real.sqrt s * restrictedL1Norm Sᶜ v + τ * ‖A v‖) =
            ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * ‖A v‖ := by field_simp
        linarith
      have h3 : τ * Real.sqrt s * ‖A v‖ ≤ τ * Real.sqrt s * (2 * η) :=
        mul_le_mul_of_nonneg_left hAv (by positivity)
      linarith
    have hβSc : restrictedL1Norm Sᶜ β ≤ restrictedL1Norm Finset.univ (β - w) := by
      calc restrictedL1Norm Sᶜ β = restrictedL1Norm Sᶜ (β - w) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            have : w j = 0 := by
              simpa [hS] using hj
            simp [this]
        _ ≤ restrictedL1Norm Finset.univ (β - w) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
    have t1 := restrictedL1Norm_le_add_sub S β b
    have t2 := restrictedL1Norm_le_add_sub Sᶜ v b
    have e2 : b - v = β := by rw [hv]; abel
    rw [e2] at t2
    have s1 := restrictedL1Norm_add_compl S β
    have s2 := restrictedL1Norm_add_compl S b
    have s3 := restrictedL1Norm_add_compl S v
    have hvSc : (1 - ρ) * restrictedL1Norm Sᶜ v ≤
        2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η) := by
      linarith
    have hvSc' : restrictedL1Norm Sᶜ v ≤
        (2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η)) / (1 - ρ) := by
      rw [le_div_iff₀ h1ρ]; linarith
    have hfin : restrictedL1Norm Finset.univ v ≤ C₁ * restrictedL1Norm Sᶜ β + D₁ * Real.sqrt s * η := by
      have e : C₁ * restrictedL1Norm Sᶜ β + D₁ * Real.sqrt s * η =
          (1 + ρ) * ((2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η)) / (1 - ρ)) +
            τ * Real.sqrt s * (2 * η) := by
        rw [hC₁, hD₁]; field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hvSc' (by linarith : (0:ℝ) ≤ 1 + ρ)
      linarith
    exact hfin.trans (by gcongr)
  have : Nonempty {w : EuclideanSpace ℝ (Fin p) // sparsity w ≤ s} :=
    ⟨⟨0, by simp [sparsity]⟩⟩
  have hσ0 : 0 ≤ bestSparseL1Error s β :=
    le_ciInf fun w ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hl1 : restrictedL1Norm Finset.univ v ≤ C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η := by
    have : (restrictedL1Norm Finset.univ v - D₁ * Real.sqrt s * η) / C₁ ≤
        bestSparseL1Error s β := by
      refine le_ciInf fun w ↦ ?_
      rw [div_le_iff₀ hC₁0]
      have := hl1w w.val w.property
      linarith
    rw [div_le_iff₀ hC₁0] at this
    linarith
  refine ⟨?_, ?_⟩
  · calc restrictedL1Norm Finset.univ v ≤ C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η := hl1
      _ ≤ (1 + ρ) * C₁ * bestSparseL1Error s β + ((1 + ρ) * D₁ + 2 * τ) * Real.sqrt s * η := by
          gcongr
          · nlinarith
          · nlinarith
  · -- the `ℓ²` bound
    obtain ⟨ℓ, hcmp, hcard, hfull, -⟩ := exists_decreasing_blocks (fun j ↦ v j) hs
    set S0 := Finset.univ.filter fun j ↦ ℓ j = 0 with hS0
    have hmem : ∀ j, j ∈ S0 ↔ ℓ j = 0 := fun j ↦ by simp [hS0]
    have hL1nn : 0 ≤ restrictedL1Norm Finset.univ v := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    have hpt : ∀ j ∉ S0, |v j| ≤ restrictedL1Norm Finset.univ v / s := by
      intro j hj
      have hj0 : 0 < ℓ j := by rw [hmem] at hj; omega
      have hc : S0.card = s := hfull 0 ⟨j, hj0⟩
      rw [le_div_iff₀ hspos]
      calc |v j| * s = ∑ _i ∈ S0, |v j| := by rw [Finset.sum_const, hc, nsmul_eq_mul]; ring
        _ ≤ ∑ i ∈ S0, |v i| := Finset.sum_le_sum fun i hi ↦ by
            rw [hmem] at hi; exact hcmp j i (by omega)
        _ ≤ restrictedL1Norm Finset.univ v :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
    have htail : Real.sqrt (∑ j ∈ S0ᶜ, v j ^ 2) ≤ restrictedL1Norm Finset.univ v / Real.sqrt s := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, Real.sq_sqrt hspos.le]
      calc ∑ j ∈ S0ᶜ, v j ^ 2 ≤ ∑ j ∈ S0ᶜ, (restrictedL1Norm Finset.univ v / s) * |v j| :=
            Finset.sum_le_sum fun j hj ↦ by
              rw [← sq_abs, sq]
              exact mul_le_mul_of_nonneg_right (hpt j (Finset.mem_compl.mp hj)) (abs_nonneg _)
        _ = restrictedL1Norm Finset.univ v / s * restrictedL1Norm S0ᶜ v := by
            rw [← Finset.mul_sum]; rfl
        _ ≤ restrictedL1Norm Finset.univ v / s * restrictedL1Norm Finset.univ v := by
            gcongr
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
        _ = _ := by ring
    have hhead : Real.sqrt (∑ j ∈ S0, v j ^ 2) ≤ ρ / Real.sqrt s * restrictedL1Norm Finset.univ v +
        τ * (2 * η) := by
      have h1 := hnsp v S0 (hcard 0)
      have h2 : restrictedL1Norm S0ᶜ v ≤ restrictedL1Norm Finset.univ v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ abs_nonneg _
      have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hρ0 hsqrt.le)
      have h4 := mul_le_mul_of_nonneg_left hAv hτ0.le
      linarith
    have hnorm : ‖v‖ = Real.sqrt (∑ j ∈ S0, v j ^ 2 + ∑ j ∈ S0ᶜ, v j ^ 2) := by
      rw [Finset.sum_add_sum_compl, ← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    have hl2 : ‖v‖ ≤ (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η := by
      rw [hnorm]
      refine (sqrt_add_le_sqrt_add_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
        (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).trans ?_
      have e : (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η =
          (ρ / Real.sqrt s * restrictedL1Norm Finset.univ v + τ * (2 * η)) +
            restrictedL1Norm Finset.univ v / Real.sqrt s := by ring
      rw [e]
      exact add_le_add hhead htail
    calc ‖v‖ ≤ (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η := hl2
      _ ≤ (1 + ρ) / Real.sqrt s * (C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η) +
            2 * τ * η := by
          gcongr
      _ = (1 + ρ) * C₁ / Real.sqrt s * bestSparseL1Error s β +
            ((1 + ρ) * D₁ + 2 * τ) * η := by
          field_simp
          ring

/-- Schur test for a symmetric matrix: the Euclidean operator norm is at most any bound on
the absolute row sums. -/
theorem norm_toEuclideanCLM_le_of_rowSum_le {p : ℕ} (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : D.IsSymm) (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, |D i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D‖ ≤ R := by
  have hsymm : ∀ i j, D i j = D j i := fun i j ↦ by
    simpa using congrFun (congrFun hD.eq j) i
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun x ↦ ?_
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D x‖ ^ 2 ≤ (R * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
    calc ∑ i, (∑ j, D i j * x j) ^ 2
        ≤ ∑ i, (∑ j, |D i j|) * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ ↦ abs_nonneg _)
            (fun j _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun j _ ↦ ?_)
          rw [mul_pow, ← mul_assoc, ← sq, sq_abs]
      _ ≤ ∑ i, R * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          exact hrow i
      _ = R * ∑ j, x j ^ 2 * ∑ i, |D j i| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hsymm i j]; ring
      _ ≤ R * ∑ j, x j ^ 2 * R := by
          gcongr with j
          exact hrow j
      _ = R ^ 2 * ∑ j, x j ^ 2 := by rw [← Finset.sum_mul]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- GAPS 103.52, deterministic sparse-row bound for hard covariance thresholding. -/
theorem norm_thresholded_covariance_sub_le {p : ℕ} (Sigma S : Matrix (Fin p) (Fin p) ℝ)
    (hSigma : Sigma.IsSymm) (hS : S.IsSymm) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (herr : ∀ i j, |S i j - Sigma i j| ≤ lambda) (s : ℕ)
    (hs : ∀ i, (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card ≤ s) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma)‖ ≤ 2 * s * lambda := by
  classical
  set D := Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma with hDdef
  have hSs : ∀ i j, S i j = S j i := fun i j ↦ by simpa using congrFun (congrFun hS.eq j) i
  have hSigs : ∀ i j, Sigma i j = Sigma j i := fun i j ↦ by
    simpa using congrFun (congrFun hSigma.eq j) i
  have hDsymm : D.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hDdef, Matrix.sub_apply, Matrix.of_apply, hSs i j,
      hSigs i j]
  have hentry : ∀ i j, |D i j| ≤ if Sigma i j ≠ 0 then 2 * lambda else 0 := by
    intro i j
    have he := herr i j
    simp only [hDdef, Matrix.sub_apply, Matrix.of_apply]
    by_cases hz : Sigma i j = 0
    · have : ¬ lambda < |S i j| := by rw [hz, sub_zero] at he; exact not_lt.mpr he
      simp [hz, this]
    · simp only [ne_eq, hz, not_false_eq_true, ite_true]
      split_ifs with ht
      · linarith
      · rw [zero_sub, abs_neg]
        have h1 := abs_sub_abs_le_abs_sub (Sigma i j) (S i j)
        rw [abs_sub_comm] at h1
        linarith [not_lt.mp ht]
  refine norm_toEuclideanCLM_le_of_rowSum_le D hDsymm _ (by positivity) fun i ↦ ?_
  calc ∑ j, |D i j| ≤ ∑ j, (if Sigma i j ≠ 0 then 2 * lambda else 0) :=
        Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card * (2 * lambda) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ s * (2 * lambda) := by gcongr; exact_mod_cast hs i
    _ = 2 * s * lambda := by ring


end CKSD
