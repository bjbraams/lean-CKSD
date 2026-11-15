module

import CKSD.Nonparametric.Basic
import Mathlib.Probability.BrownianMotion.Basic
public import CKSD.Asymptotics.Basic

/-!
# The Grenander estimator of a decreasing density

The least concave majorant is taken on `[0, ∞)`, as the pointwise infimum of all concave
majorants there. The Grenander estimator at `x` is the left derivative at `x` of the least
concave majorant of the empirical distribution function. Two-sided Brownian motion is built
from two independent Brownian motions of Mathlib (`ProbabilityTheory.IsBrownianReal`) on
`[0, ∞)`, and Chernoff's random variable is specified as a measurable almost-sure maximizer of
`W(t) - t ^ 2`; its law, being that of the almost surely unique maximizer, does not depend
on the realization.

The finite-sample maximum-likelihood property is proved on the grid formed by the origin and
the distinct sample values: the least concave majorant is affine between consecutive grid
points and touches the empirical distribution function at each strict change of slope, so the
estimator is a step function, and a summation by parts compares its likelihood with that of any
nonincreasing density.
Source: GAPS 103.11.

## References

* P. Groeneboom and G. Jongbloed, *Nonparametric Estimation under Shape Constraints*, Cambridge
  University Press, 2014.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Least concave majorant on `[0, ∞)` of a real function, as the infimum of the values of
its concave majorants; the empty-set convention `sInf ∅ = 0` is never used for bounded
functions such as distribution functions. -/
def leastConcaveMajorant (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Ici 0) g ∧ (∀ s ∈ Ici (0 : ℝ), F s ≤ g s) ∧
    r = g t}

/-- The Grenander estimator at `x`: the left slope of the least concave majorant of the
empirical distribution function of the first `n` observations. -/
def grenanderEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  derivWithin (leastConcaveMajorant (empiricalCDF X n ω)) (Iio x) x

/-- A probability density vanishing on the negative half-line and nonincreasing on `(0, ∞)`;
its value at `0` is only required to be nonnegative. -/
def IsNonincreasingDensity (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ (∀ t, 0 ≤ g t) ∧ (∀ t < 0, g t = 0) ∧ AntitoneOn g (Ioi 0) ∧
    ∫ t, g t = 1

/-- The path of two-sided Brownian motion built from two one-sided paths: `B₁` on the
nonnegative half-line and `B₂` reflected on the negative half-line. -/
def twoSidedBrownianPath {Ω : Type*} (B₁ B₂ : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  if 0 ≤ t then B₁ t.toNNReal ω else B₂ (-t).toNNReal ω

/-- `Z` is a realization of Chernoff's random variable `argmax (W(t) - t ^ 2)` for the
two-sided Brownian motion `W` built from independent Brownian motions `B₁` and `B₂`. -/
def IsChernoffArgmax {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (B₁ B₂ : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ) : Prop :=
  IsBrownianReal B₁ ν ∧ IsBrownianReal B₂ ν ∧
    IndepFun (fun ω t ↦ B₁ t ω) (fun ω t ↦ B₂ t ω) ν ∧ Measurable Z ∧
    ∀ᵐ ω ∂ν, ∀ t : ℝ, twoSidedBrownianPath B₁ B₂ ω t - t ^ 2 ≤
      twoSidedBrownianPath B₁ B₂ ω (Z ω) - Z ω ^ 2

/-- A concave majorant of `F` on `[0, ∞)`. -/
def IsConcaveMajorant (F g : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Ici 0) g ∧ ∀ s ∈ Ici (0 : ℝ), F s ≤ g s

/-- The least concave majorant lies below every concave majorant on `[0, ∞)`. -/
theorem leastConcaveMajorant_le {F g : ℝ → ℝ} (hg : IsConcaveMajorant F g) {t : ℝ}
    (ht : 0 ≤ t) : leastConcaveMajorant F t ≤ g t := by
  refine csInf_le ⟨F t, ?_⟩ ⟨g, hg.1, hg.2, rfl⟩
  rintro r ⟨g', -, hg', rfl⟩
  exact hg' t ht

/-- A function bounded above on `[0, ∞)` lies below its least concave majorant there. -/
theorem le_leastConcaveMajorant {F : ℝ → ℝ} {C : ℝ} (hC : ∀ s, 0 ≤ s → F s ≤ C) {t : ℝ}
    (ht : 0 ≤ t) : F t ≤ leastConcaveMajorant F t := by
  refine le_csInf ⟨C, fun _ ↦ C, concaveOn_const C (convex_Ici 0), fun s hs ↦ hC s hs, rfl⟩ ?_
  rintro r ⟨g', -, hg', rfl⟩
  exact hg' t ht

/-- The least concave majorant of a function bounded above on `[0, ∞)` is concave there. -/
theorem concaveOn_leastConcaveMajorant {F : ℝ → ℝ} {C : ℝ} (hC : ∀ s, 0 ≤ s → F s ≤ C) :
    ConcaveOn ℝ (Ici 0) (leastConcaveMajorant F) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hxy : (0 : ℝ) ≤ a • x + b • y := (convex_Ici 0) hx hy ha hb hab
  refine le_csInf ⟨C, fun _ ↦ C, concaveOn_const C (convex_Ici 0), fun s hs ↦ hC s hs, rfl⟩ ?_
  rintro r ⟨g, hgc, hg, rfl⟩
  have h1 := leastConcaveMajorant_le ⟨hgc, hg⟩ (show (0:ℝ) ≤ x from hx)
  have h2 := leastConcaveMajorant_le ⟨hgc, hg⟩ (show (0:ℝ) ≤ y from hy)
  have h3 := hgc.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h3 ⊢
  nlinarith

/-- A concave function on `[x₀, ∞)` that is bounded below is monotone there. -/
theorem ConcaveOn.monotoneOn_of_bddBelow {f : ℝ → ℝ} {x₀ : ℝ} (hf : ConcaveOn ℝ (Ici x₀) f)
    {c : ℝ} (hc : ∀ t, x₀ ≤ t → c ≤ f t) : MonotoneOn f (Ici x₀) := by
  intro a ha b hb hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  set κ := (f a - f b) / (b - a) with hκ
  have hκpos : 0 < κ := div_pos (by linarith) (by linarith)
  set t := b + (f b - c + 1) / κ with ht
  have hbt : b < t := by
    have : 0 < (f b - c + 1) / κ := div_pos (by linarith [hc b hb]) hκpos
    linarith
  have hs := hf.slope_anti_adjacent ha (show t ∈ Ici x₀ from le_trans hb hbt.le) hab hbt
  have hs' : f t - f b ≤ -κ * (t - b) := by
    rw [div_le_iff₀ (by linarith)] at hs
    have : (f b - f a) / (b - a) = -κ := by rw [hκ]; ring
    rw [this] at hs; linarith
  have : -κ * (t - b) = -(f b - c + 1) := by
    rw [ht]; field_simp; ring
  have := hc t (le_trans hb hbt.le)
  linarith

/-- A concave function lies above its chord between two points. -/
theorem ConcaveOn.chord_le {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {a b t : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) :
    f a + (f b - f a) / (b - a) * (t - a) ≤ f t := by
  have hba : 0 < b - a := by linarith
  have h := hf.2 ha hb (show 0 ≤ (b - t) / (b - a) from div_nonneg (by linarith) hba.le)
    (show 0 ≤ (t - a) / (b - a) from div_nonneg (by linarith) hba.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at h
  have e : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by field_simp; ring
  rw [e] at h
  have e2 : (b - t) / (b - a) * f a + (t - a) / (b - a) * f b =
      f a + (f b - f a) / (b - a) * (t - a) := by field_simp; ring
  linarith

/-- A concave function lies below the extension of its chord to the right. -/
theorem ConcaveOn.le_chord_of_le {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {a b t : ℝ}
    (ha : a ∈ s) (ht : t ∈ s) (hab : a < b) (hbt : b ≤ t) :
    f t ≤ f a + (f b - f a) / (b - a) * (t - a) := by
  rcases hbt.eq_or_lt with rfl | hbt
  · field_simp; ring_nf; rfl
  have hs := hf.slope_anti_adjacent ha ht hab hbt
  have hba : 0 < b - a := by linarith
  have htb : 0 < t - b := by linarith
  rw [div_le_iff₀ htb] at hs
  have : f a + (f b - f a) / (b - a) * (t - a) =
      f b + (f b - f a) / (b - a) * (t - b) := by field_simp; ring
  linarith

/-- A concave function lies below the extension of its chord to the left. -/
theorem ConcaveOn.le_chord_of_ge {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {a b t : ℝ}
    (hb : b ∈ s) (ht : t ∈ s) (hab : a < b) (hta : t ≤ a) :
    f t ≤ f a + (f b - f a) / (b - a) * (t - a) := by
  rcases hta.eq_or_lt with rfl | hta
  · simp
  have hs := hf.slope_anti_adjacent ht hb hta hab
  have hba : 0 < b - a := by linarith
  have hat : 0 < a - t := by linarith
  rw [le_div_iff₀ hat] at hs
  have : (f b - f a) / (b - a) * (t - a) = -((f b - f a) / (b - a) * (a - t)) := by ring
  linarith


/-- The ordered distinct values of a positive sample, together with the origin. -/
theorem exists_sample_grid (x : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hpos : ∀ i < n, 0 < x i) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ y : ℕ → ℝ, StrictMonoOn y (Iic k) ∧ y 0 = 0 ∧
      (∀ i < n, ∃ l, 1 ≤ l ∧ l ≤ k ∧ x i = y l) ∧
      (∀ l, 1 ≤ l → l ≤ k → ∃ i < n, x i = y l) := by
  classical
  set T : Finset ℝ := insert 0 ((Finset.range n).image x) with hT
  have h0 : (0 : ℝ) ∉ (Finset.range n).image x := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi h; exact (hpos i hi).ne' h
  have hne : ((Finset.range n).image x).Nonempty :=
    (Finset.nonempty_range_iff.mpr hn.ne').image x
  have hcard : 2 ≤ T.card := by
    rw [hT, Finset.card_insert_of_notMem h0]
    have := hne.card_pos; omega
  set e := T.orderEmbOfFin rfl with he
  refine ⟨T.card - 1, by omega, fun j ↦ if h : j < T.card then e ⟨j, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a < T.card := by simp only [mem_Iic] at ha; omega
    have hb' : b < T.card := by simp only [mem_Iic] at hb; omega
    simp only [ha', hb', dite_true]
    exact e.strictMono (Fin.mk_lt_mk.mpr hab)
  · have hz : 0 < T.card := by omega
    simp only [hz, dite_true]
    rw [he, Finset.orderEmbOfFin_zero rfl hz]
    refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) ?_
    refine Finset.le_min' _ _ _ fun t ht ↦ ?_
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact le_rfl
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact (hpos i (Finset.mem_range.mp hi)).le
  · intro i hi
    have hxT : x i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem x
      (Finset.mem_range.mpr hi))
    have : x i ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hxT
    obtain ⟨j, hj⟩ := this
    have hj0 : j.val ≠ 0 := by
      intro h0'
      have hz : 0 < T.card := by omega
      have : e j = 0 := by
        have hjeq : j = ⟨0, hz⟩ := Fin.ext h0'
        rw [hjeq, he, Finset.orderEmbOfFin_zero rfl hz]
        refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) ?_
        refine Finset.le_min' _ _ _ fun t ht ↦ ?_
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact le_rfl
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
          exact (hpos i (Finset.mem_range.mp hi)).le
      rw [hj] at this; exact (hpos i hi).ne' this
    refine ⟨j.val, by omega, by have := j.isLt; omega, ?_⟩
    simp only [j.isLt, dite_true]
    exact hj.symm
  · intro l hl1 hlk
    have hl : l < T.card := by omega
    simp only [hl, dite_true]
    have hmem := Finset.orderEmbOfFin_mem T rfl ⟨l, hl⟩
    rw [← he] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exfalso
      have hz : 0 < T.card := by omega
      have hlt : e ⟨0, hz⟩ < e ⟨l, hl⟩ := e.strictMono (Fin.mk_lt_mk.mpr (by omega))
      have : e ⟨0, hz⟩ = 0 := by
        rw [he, Finset.orderEmbOfFin_zero rfl hz]
        refine le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) ?_
        refine Finset.le_min' _ _ _ fun t ht ↦ ?_
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact le_rfl
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
          exact (hpos i (Finset.mem_range.mp hi)).le
      rw [this, h] at hlt; exact lt_irrefl _ hlt
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp h
      exact ⟨i, Finset.mem_range.mp hi, hxi⟩


/-- Summation by parts: a nonincreasing nonnegative weight sequence preserves nonpositivity of
all partial sums. -/
theorem sum_mul_le_of_partialSum_nonpos (b c : ℕ → ℝ) (k : ℕ)
    (hb : ∀ j, j + 1 < k → b (j + 1) ≤ b j) (hb0 : ∀ j < k, 0 ≤ b j)
    (hc : ∀ l < k, ∑ j ∈ Finset.range (l + 1), c j ≤ 0) :
    ∑ j ∈ Finset.range k, b j * c j ≤ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have key : ∀ l < k, ∑ j ∈ Finset.range (l + 1), b j * c j ≤
      b l * ∑ j ∈ Finset.range (l + 1), c j := by
    intro l hl
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j ↦ c j), mul_add]
      have h1 := ih (by omega)
      have h2 := hc l (by omega)
      have h3 := hb l hl
      nlinarith
  have := key (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk] at this
  have h2 := hc (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk] at h2
  nlinarith [hb0 (k - 1) (by omega)]

/-- The discrete core of the Grenander likelihood inequality: on the grid of a cumulative sum
diagram with least concave majorant values `G`, slopes `s`, and counts `N`, weights `1 / s`
integrate a nonincreasing nonnegative sequence `b` against the counts by at most `n` times
its Riemann sum. -/
theorem sum_count_mul_div_slope_le (k : ℕ) (n : ℝ) (y G N s b : ℕ → ℝ)
    (hy : ∀ j < k, y j < y (j + 1)) (hs : ∀ j < k, s j = (G (j + 1) - G j) / (y (j + 1) - y j))
    (hspos : ∀ j < k, 0 < s j) (hsanti : ∀ j, j + 1 < k → s (j + 1) ≤ s j)
    (hknot : ∀ j, j + 1 < k → s (j + 1) < s j → n * G (j + 1) = N (j + 1))
    (hNG : ∀ j ≤ k, N j ≤ n * G j) (hG0 : G 0 = 0) (hN0 : N 0 = 0) (hy0 : y 0 = 0)
    (hb : ∀ j, j + 1 < k → b (j + 1) ≤ b j) (hb0 : ∀ j < k, 0 ≤ b j) :
    ∑ j ∈ Finset.range k, (N (j + 1) - N j) * b j / s j ≤
      n * ∑ j ∈ Finset.range k, b j * (y (j + 1) - y j) := by
  have hclaim : ∀ l < k, ∑ j ∈ Finset.range (l + 1), (N (j + 1) - N j) / s j ≤
      n * y (l + 1) - (n * G (l + 1) - N (l + 1)) / s l := by
    intro l hl
    induction l with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, hN0, sub_zero]
      have h0 := hspos 0 hl
      have hy1 := hy 0 hl
      rw [hs 0 hl, hG0, hy0, sub_zero, sub_zero] at h0 ⊢
      rw [hy0] at hy1
      have hG1 : 0 < G 1 := by
        by_contra h; push Not at h
        exact absurd h0 (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h hy1.le))
      field_simp
      ring_nf
      exact le_rfl
    | succ l ih =>
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have hsl := hspos l (by omega)
      have hsl1 := hspos (l + 1) hl
      have hyl := hy (l + 1) hl
      have hG : G (l + 2) = G (l + 1) + s (l + 1) * (y (l + 2) - y (l + 1)) := by
        rw [hs (l + 1) hl]; field_simp; ring
      have hle : (n * G (l + 1) - N (l + 1)) / s (l + 1) ≤
          (n * G (l + 1) - N (l + 1)) / s l := by
        rcases (hsanti l hl).lt_or_eq with hlt | heq
        · rw [hknot l hl hlt]; simp
        · rw [heq]
      have e : n * y (l + 1 + 1) - (n * G (l + 1 + 1) - N (l + 1 + 1)) / s (l + 1) =
          n * y (l + 1) - (n * G (l + 1) - N (l + 1)) / s (l + 1) +
            (N (l + 1 + 1) - N (l + 1)) / s (l + 1) := by
        rw [hG]; field_simp; ring
      rw [e]
      linarith
  set c : ℕ → ℝ := fun j ↦ (N (j + 1) - N j) / s j - n * (y (j + 1) - y j) with hcdef
  have hc : ∀ l < k, ∑ j ∈ Finset.range (l + 1), c j ≤ 0 := by
    intro l hl
    have e : ∑ j ∈ Finset.range (l + 1), c j =
        ∑ j ∈ Finset.range (l + 1), (N (j + 1) - N j) / s j - n * (y (l + 1) - y 0) := by
      simp only [hcdef]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_range_sub (fun j ↦ y j)]
    rw [e, hy0, sub_zero]
    have h1 := hclaim l hl
    have h2 : 0 ≤ (n * G (l + 1) - N (l + 1)) / s l :=
      div_nonneg (by linarith [hNG (l + 1) hl]) (hspos l hl).le
    linarith
  have := sum_mul_le_of_partialSum_nonpos b c k hb hb0 hc
  have e : ∑ j ∈ Finset.range k, b j * c j =
      ∑ j ∈ Finset.range k, (N (j + 1) - N j) * b j / s j -
        n * ∑ j ∈ Finset.range k, b j * (y (j + 1) - y j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [hcdef]; ring
  linarith


/-- An affine function is concave on `[0, ∞)`. -/
theorem concaveOn_affine (c σ a : ℝ) : ConcaveOn ℝ (Ici 0) (fun t ↦ c + σ * (t - a)) := by
  refine ⟨convex_Ici 0, fun x _ y _ p q _ _ hpq ↦ ?_⟩
  simp only [smul_eq_mul]
  rw [show q = 1 - p by linarith]
  ring_nf
  exact le_rfl

/-- The least concave majorant is affine on any interval where the majorized function is
constant except possibly at the right endpoint. -/
theorem leastConcaveMajorant_eq_affine {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hF1 : ∀ t, 0 ≤ t → F t ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hconst : ∀ t, a ≤ t → t < b → F t = F a) {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    leastConcaveMajorant F t = leastConcaveMajorant F a +
      (leastConcaveMajorant F b - leastConcaveMajorant F a) / (b - a) * (t - a) := by
  set G := leastConcaveMajorant F with hGdef
  have hGc : ConcaveOn ℝ (Ici 0) G := concaveOn_leastConcaveMajorant hF1
  have hFG : ∀ u, 0 ≤ u → F u ≤ G u := fun u hu ↦ le_leastConcaveMajorant hF1 hu
  have hGm : MonotoneOn G (Ici 0) :=
    ConcaveOn.monotoneOn_of_bddBelow hGc (c := 0) fun u hu ↦ (hF0 u hu).trans (hFG u hu)
  have hb : (0 : ℝ) ≤ b := ha.trans hab.le
  set L : ℝ → ℝ := fun u ↦ G a + (G b - G a) / (b - a) * (u - a) with hL
  have hGab : G a ≤ G b := hGm (show a ∈ Ici (0:ℝ) from ha) (show b ∈ Ici (0:ℝ) from hb) hab.le
  have hslope : 0 ≤ (G b - G a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hmaj : IsConcaveMajorant F (G ⊓ L) := by
    refine ⟨hGc.inf (concaveOn_affine _ _ _), fun u hu ↦ ?_⟩
    have hu' : (0 : ℝ) ≤ u := hu
    refine le_inf (hFG u hu') ?_
    rcases lt_or_ge u a with hua | hua
    · exact (hFG u hu').trans
        (ConcaveOn.le_chord_of_ge hGc (show b ∈ Ici (0:ℝ) from hb) hu hab hua.le)
    rcases lt_or_ge u b with hub | hub
    · rw [hconst u hua hub]
      have : G a ≤ L u := by
        simp only [hL]; nlinarith
      exact (hFG a ha).trans this
    · exact (hFG u hu').trans (ConcaveOn.le_chord_of_le hGc (show a ∈ Ici (0:ℝ) from ha) hu hab hub)
  have ht : 0 ≤ t := ha.trans hat
  have h1 := leastConcaveMajorant_le hmaj ht
  rw [← hGdef] at h1
  have h2 := ConcaveOn.chord_le hGc (show a ∈ Ici (0:ℝ) from ha) (show b ∈ Ici (0:ℝ) from hb)
    hab hat htb
  simp only [Pi.inf_apply] at h1
  exact le_antisymm ((h1.trans inf_le_right)) h2

/-- At a strict kink of the least concave majorant on a grid of constancy intervals, the
majorant touches the majorized function. -/
theorem leastConcaveMajorant_eq_of_slope_lt {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hF1 : ∀ t, 0 ≤ t → F t ≤ 1) {a c b : ℝ} (ha : 0 ≤ a) (hac : a < c) (hcb : c < b)
    (hconst₁ : ∀ t, a ≤ t → t < c → F t = F a) (hconst₂ : ∀ t, c ≤ t → t < b → F t = F c)
    (hkink : (leastConcaveMajorant F b - leastConcaveMajorant F c) / (b - c) <
      (leastConcaveMajorant F c - leastConcaveMajorant F a) / (c - a)) :
    leastConcaveMajorant F c = F c := by
  set G := leastConcaveMajorant F with hGdef
  have hGc : ConcaveOn ℝ (Ici 0) G := concaveOn_leastConcaveMajorant hF1
  have hFG : ∀ u, 0 ≤ u → F u ≤ G u := fun u hu ↦ le_leastConcaveMajorant hF1 hu
  have hGm : MonotoneOn G (Ici 0) :=
    ConcaveOn.monotoneOn_of_bddBelow hGc (c := 0) fun u hu ↦ (hF0 u hu).trans (hFG u hu)
  have hc : (0 : ℝ) ≤ c := ha.trans hac.le
  have hb : (0 : ℝ) ≤ b := hc.trans hcb.le
  have hab : a < b := hac.trans hcb
  set L : ℝ → ℝ := fun u ↦ G a + (G b - G a) / (b - a) * (u - a) with hL
  have hGab : G a ≤ G b := hGm (show a ∈ Ici (0:ℝ) from ha) (show b ∈ Ici (0:ℝ) from hb) hab.le
  have hslope : 0 ≤ (G b - G a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hLc : L c < G c := by
    have hca : 0 < c - a := by linarith
    have hbc : 0 < b - c := by linarith
    rw [div_lt_div_iff₀ hbc hca] at hkink
    have e : (G c - L c) * (b - a) = (G c - G a) * (b - c) - (G b - G c) * (c - a) := by
      simp only [hL]; field_simp; ring
    have : 0 < (G c - L c) * (b - a) := by rw [e]; linarith
    have hba : 0 < b - a := by linarith
    by_contra h; push Not at h
    nlinarith
  by_contra hne
  have hlt : F c < G c := lt_of_le_of_ne (hFG c hc) (Ne.symm hne)
  have hGcpos : 0 < G c := lt_of_le_of_lt (hF0 c hc) hlt
  set lam := F c / G c with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (hF0 c hc) hGcpos.le
  have hlam1 : lam < 1 := (div_lt_one hGcpos).mpr hlt
  have hGa0 : 0 ≤ G a := (hF0 a ha).trans (hFG a ha)
  have hmaj : IsConcaveMajorant F (fun u ↦ lam • G u + (1 - lam) • (G ⊓ L) u) := by
    refine ⟨(hGc.smul hlam0).add ((hGc.inf (concaveOn_affine _ _ _)).smul (by linarith)),
      fun u hu ↦ ?_⟩
    have hu' : (0 : ℝ) ≤ u := hu
    simp only [smul_eq_mul, Pi.inf_apply]
    have hout : (u < a ∨ b ≤ u) → F u ≤ lam * G u + (1 - lam) * min (G u) (L u) := by
      intro h
      have hGL : G u ≤ L u := by
        rcases h with h | h
        · exact ConcaveOn.le_chord_of_ge hGc (show b ∈ Ici (0:ℝ) from hb) hu hab h.le
        · exact ConcaveOn.le_chord_of_le hGc (show a ∈ Ici (0:ℝ) from ha) hu hab h
      rw [min_eq_left hGL]
      have := hFG u hu'; nlinarith
    rcases lt_or_ge u a with hua | hua
    · exact hout (Or.inl hua)
    rcases lt_or_ge u b with hub | hub
    swap
    · exact hout (Or.inr hub)
    have hGau : G a ≤ G u := hGm (show a ∈ Ici (0:ℝ) from ha) hu hua
    have hLu : G a ≤ L u := by simp only [hL]; nlinarith
    have hmin : G a ≤ min (G u) (L u) := le_min hGau hLu
    rcases lt_or_ge u c with huc | huc
    · rw [hconst₁ u hua huc]
      have := hFG a ha
      nlinarith
    · rw [hconst₂ u huc hub]
      have hGcu : G c ≤ G u := hGm (show c ∈ Ici (0:ℝ) from hc) hu huc
      have hFc : F c = lam * G c := by rw [hlam]; field_simp
      nlinarith
  have h1 := leastConcaveMajorant_le hmaj hc
  rw [← hGdef] at h1
  simp only [smul_eq_mul, Pi.inf_apply] at h1
  have : min (G c) (L c) = L c := min_eq_right hLc.le
  rw [this] at h1
  nlinarith

/-- The least concave majorant of a function with values in `[0, 1]` on `[0, ∞)` that vanishes
on `[0, y₁)`, for some `y₁ > 0`, vanishes at the origin. -/
theorem leastConcaveMajorant_zero_eq_zero {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hF1 : ∀ t, 0 ≤ t → F t ≤ 1) {y₁ : ℝ} (hy₁ : 0 < y₁)
    (hzero : ∀ t, 0 ≤ t → t < y₁ → F t = 0) : leastConcaveMajorant F 0 = 0 := by
  refine le_antisymm ?_ ((hF0 0 le_rfl).trans (le_leastConcaveMajorant hF1 le_rfl))
  have hmaj : IsConcaveMajorant F (fun t ↦ 0 + (1 / y₁) * (t - 0)) := by
    refine ⟨concaveOn_affine _ _ _, fun s hs ↦ ?_⟩
    have hs' : (0 : ℝ) ≤ s := hs
    simp only [zero_add, sub_zero]
    rcases lt_or_ge s y₁ with h | h
    · rw [hzero s hs' h]
      positivity
    · calc F s ≤ 1 := hF1 s hs'
        _ ≤ 1 / y₁ * s := by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hy₁]; linarith
  simpa using leastConcaveMajorant_le hmaj le_rfl

/-- Positivity of the chord slopes `s j` of a concave function `G` on `[0, ∞)` along a grid
`0 = y 0 < ⋯ < y k`: if the first slope is positive, `G (y k) = 1`, and `G` stays below `1`
at each interior grid point where the slope strictly decreases, then every slope is
positive. -/
theorem slope_pos_of_concaveOn_grid {G : ℝ → ℝ} (hGc : ConcaveOn ℝ (Ici 0) G) {k : ℕ}
    {y s : ℕ → ℝ} (hymono : StrictMonoOn y (Iic k)) (hy0 : y 0 = 0)
    (hs : ∀ j, s j = (G (y (j + 1)) - G (y j)) / (y (j + 1) - y j)) (hs0 : 0 < s 0)
    (hknot : ∀ j, j + 1 < k → s (j + 1) < s j → G (y (j + 1)) < 1) (hGk : G (y k) = 1) :
    ∀ j < k, 0 < s j := by
  have hynn : ∀ j ≤ k, y j ∈ Ici (0 : ℝ) := fun j hj ↦ by
    rw [mem_Ici, ← hy0]
    exact hymono.monotoneOn (mem_Iic.mpr (Nat.zero_le k)) (mem_Iic.mpr hj) (Nat.zero_le j)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact hs0
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    by_contra hcon
    push Not at hcon
    have hk' := hknot j' hj (lt_of_le_of_lt hcon (ih j' (by omega) (by omega)))
    have hchord := ConcaveOn.le_chord_of_le hGc (b := y (j' + 1 + 1)) (hynn (j' + 1) hj.le)
      (hynn k le_rfl) (hymono (mem_Iic.mpr (by omega)) (mem_Iic.mpr (by omega)) (by omega))
      (hymono.monotoneOn (mem_Iic.mpr (by omega)) (mem_Iic.mpr le_rfl) (by omega))
    rw [hGk, ← hs] at hchord
    have hyk : 0 ≤ y k - y (j' + 1) :=
      sub_nonneg.mpr (hymono.monotoneOn (mem_Iic.mpr hj.le) (mem_Iic.mpr le_rfl) hj.le)
    have := mul_nonpos_of_nonpos_of_nonneg hcon hyk
    linarith

/-- If `G` is affine with slope `s j` on each cell `[y j, y (j + 1)]` of a strictly increasing
grid `0 = y 0 < ⋯ < y k` and constant on `[y k, ∞)`, then on `(0, ∞)` the left derivative of
`G` is the step function with value `s j` on `(y j, y (j + 1)]` and `0` beyond `y k`. -/
theorem derivWithin_Iio_eq_sum_indicator {G : ℝ → ℝ} {k : ℕ} {y s : ℕ → ℝ}
    (hymono : StrictMonoOn y (Iic k)) (hy0 : y 0 = 0)
    (haff : ∀ j < k, ∀ t, y j ≤ t → t ≤ y (j + 1) → G t = G (y j) + s j * (t - y j))
    (htop : ∀ t, y k ≤ t → G t = G (y k)) {t : ℝ} (ht : 0 < t) :
    derivWithin G (Iio t) t =
      ∑ j ∈ Finset.range k, (Ioc (y j) (y (j + 1))).indicator (fun _ ↦ s j) t := by
  rcases lt_or_ge (y k) t with htk | htk
  · rw [sum_indicator_Ioc_eq_zero_of_notMem s hymono.monotoneOn fun h ↦ (not_le.mpr htk) h.2]
    exact derivWithin_Iio_eq_of_eq_affine (c := G (y k)) htk fun u hu _ ↦ by
      rw [htop u hu]; ring
  obtain ⟨j, hj, hmem⟩ := exists_mem_Ioc_of_grid (show y 0 < t by rw [hy0]; exact ht) htk
  rw [sum_indicator_Ioc_eq_of_mem s hymono hj hmem]
  exact derivWithin_Iio_eq_of_eq_affine hmem.1 fun u hu1 hu2 ↦
    haff j hj u hu1 (hu2.trans hmem.2)

/-- A step function on the cells of a strictly increasing grid `0 = y 0 < ⋯ < y k`, with
positive nonincreasing values `s j` whose Riemann sum `∑ s j * (y (j + 1) - y j)` is `1`, is a
nonincreasing density. -/
theorem isNonincreasingDensity_sum_indicator {k : ℕ} {y s : ℕ → ℝ}
    (hymono : StrictMonoOn y (Iic k)) (hy0 : y 0 = 0) (hspos : ∀ j < k, 0 < s j)
    (hsanti : ∀ j l, j ≤ l → l < k → s l ≤ s j)
    (hsum : ∑ j ∈ Finset.range k, s j * (y (j + 1) - y j) = 1) :
    IsNonincreasingDensity fun t ↦
      ∑ j ∈ Finset.range k, (Ioc (y j) (y (j + 1))).indicator (fun _ ↦ s j) t := by
  have h0 : ∀ t, 0 ≤ ∑ j ∈ Finset.range k, (Ioc (y j) (y (j + 1))).indicator (fun _ ↦ s j) t :=
    fun t ↦ Finset.sum_nonneg fun j hj ↦ indicator_nonneg
      (fun _ _ ↦ (hspos j (Finset.mem_range.mp hj)).le) _
  refine ⟨Finset.measurable_sum _ fun j _ ↦ measurable_const.indicator measurableSet_Ioc, h0,
    fun t ht ↦ sum_indicator_Ioc_eq_zero_of_notMem s hymono.monotoneOn
      fun h ↦ by linarith [h.1, hy0], ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂ h12
    dsimp only
    rcases lt_or_ge (y k) t₂ with h | h
    · rw [sum_indicator_Ioc_eq_zero_of_notMem s hymono.monotoneOn fun h' ↦ (not_le.mpr h) h'.2]
      exact h0 t₁
    have hy₁ : y 0 < t₁ := by rw [hy0]; exact h₁
    obtain ⟨j₁, hj₁, hm₁⟩ := exists_mem_Ioc_of_grid hy₁ (h12.trans h)
    obtain ⟨j₂, hj₂, hm₂⟩ := exists_mem_Ioc_of_grid (hy₁.trans_le h12) h
    rw [sum_indicator_Ioc_eq_of_mem s hymono hj₁ hm₁, sum_indicator_Ioc_eq_of_mem s hymono hj₂ hm₂]
    refine hsanti j₁ j₂ ?_ hj₂
    by_contra hc
    push Not at hc
    linarith [hymono.monotoneOn (mem_Iic.mpr (by omega : j₂ + 1 ≤ k)) (mem_Iic.mpr hj₁.le)
      (by omega : j₂ + 1 ≤ j₁), hm₁.1, hm₂.2]
  · beta_reduce
    rw [integral_finsetSum, ← hsum]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj' := Finset.mem_range.mp hj
      have hΔ : y j < y (j + 1) :=
        hymono (mem_Iic.mpr hj'.le) (mem_Iic.mpr (by omega)) (Nat.lt_succ_self j)
      rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc,
        max_eq_left (sub_nonneg.mpr hΔ.le), smul_eq_mul, mul_comm]
    · intro j _
      exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc

/-- On a strictly increasing grid that contains every observation, the empirical
distribution function is constant on each cell `[y l, y (l + 1))`. -/
theorem empiricalCDF_eq_of_mem_Ico_grid {Ω : Type*} {X : ℕ → Ω → ℝ} {n k : ℕ} {ω : Ω}
    {y : ℕ → ℝ} (hymono : StrictMonoOn y (Iic k))
    (hdata : ∀ i < n, ∃ l, 1 ≤ l ∧ l ≤ k ∧ X i ω = y l) {l : ℕ} (hl : l < k) {t : ℝ}
    (hlt : y l ≤ t) (htl : t < y (l + 1)) :
    empiricalCDF X n ω t = empiricalCDF X n ω (y l) := by
  have hset : ((Finset.range n).filter fun i ↦ X i ω ≤ t) =
      (Finset.range n).filter fun i ↦ X i ω ≤ y l := by
    refine Finset.filter_congr fun i hi ↦ ⟨fun hit ↦ ?_, fun hil ↦ hil.trans hlt⟩
    obtain ⟨m, -, hmk, hxm⟩ := hdata i (Finset.mem_range.mp hi)
    rw [hxm] at hit ⊢
    by_contra hcon
    push Not at hcon
    have hlm : l < m := (hymono.lt_iff_lt (mem_Iic.mpr hl.le) (mem_Iic.mpr hmk)).mp hcon
    have := hymono.monotoneOn (mem_Iic.mpr (by omega : l + 1 ≤ k)) (mem_Iic.mpr hmk)
      (by omega : l + 1 ≤ m)
    linarith
  rw [empiricalCDF_def, empiricalCDF_def, hset]

/-- The empirical distribution function of a nonempty sample is `1` from the largest point of
a grid that contains every observation on. -/
theorem empiricalCDF_eq_one_of_grid_le {Ω : Type*} {X : ℕ → Ω → ℝ} {n k : ℕ} {ω : Ω}
    {y : ℕ → ℝ} (hn : 0 < n) (hymono : StrictMonoOn y (Iic k))
    (hdata : ∀ i < n, ∃ l, 1 ≤ l ∧ l ≤ k ∧ X i ω = y l) {t : ℝ} (ht : y k ≤ t) :
    empiricalCDF X n ω t = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [empiricalCDF_def, Finset.filter_true_of_mem, Finset.card_range, div_self hnR.ne']
  intro i hi
  obtain ⟨m, -, hmk, hxm⟩ := hdata i (Finset.mem_range.mp hi)
  rw [hxm]
  exact (hymono.monotoneOn (mem_Iic.mpr hmk) (mem_Iic.mpr le_rfl) hmk).trans ht

/-- The empirical distribution function is below `1` at every point of a grid before its
largest point, when that largest point is an observation. -/
theorem empiricalCDF_lt_one_of_lt_grid {Ω : Type*} {X : ℕ → Ω → ℝ} {n k : ℕ} {ω : Ω}
    {y : ℕ → ℝ} (hymono : StrictMonoOn y (Iic k))
    (hgrid : ∀ l, 1 ≤ l → l ≤ k → ∃ i < n, X i ω = y l) (hk : 1 ≤ k) {l : ℕ} (hl : l < k) :
    empiricalCDF X n ω (y l) < 1 := by
  obtain ⟨i, hi, hxi⟩ := hgrid k hk le_rfl
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hi
  rw [empiricalCDF_def, div_lt_one hnR]
  have hss : ((Finset.range n).filter fun i ↦ X i ω ≤ y l) ⊂ Finset.range n := by
    refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
      ⟨i, Finset.mem_range.mpr hi, ?_⟩
    simp only [Finset.mem_filter, not_and, not_le]
    intro _; rw [hxi]; exact hymono (mem_Iic.mpr hl.le) (mem_Iic.mpr le_rfl) hl
  have := Finset.card_lt_card hss
  rw [Finset.card_range] at this
  exact_mod_cast this

/-- Grouping a sum over a sample by grid points: when every observation `x i`, `i < n`, is
one of the points `y 1, …, y k` of a strictly increasing grid, the sum of `f (x i)` is the sum
over the grid of `f (y (j + 1))` times the number of observations equal to `y (j + 1)`,
written as a difference of cumulative counts. -/
theorem sum_comp_eq_sum_count_sub (x : ℕ → ℝ) (n k : ℕ) (y : ℕ → ℝ)
    (hymono : StrictMonoOn y (Iic k)) (hdata : ∀ i < n, ∃ l, 1 ≤ l ∧ l ≤ k ∧ x i = y l)
    (f : ℝ → ℝ) :
    ∑ i ∈ Finset.range n, f (x i) = ∑ j ∈ Finset.range k,
      ((((Finset.range n).filter fun i ↦ x i ≤ y (j + 1)).card : ℝ) -
        ((Finset.range n).filter fun i ↦ x i ≤ y j).card) * f (y (j + 1)) := by
  classical
  have h1 : ∀ i ∈ Finset.range n, f (x i) =
      ∑ j ∈ Finset.range k, if x i = y (j + 1) then f (y (j + 1)) else 0 := by
    intro i hi
    obtain ⟨m, hm1, hmk, hxm⟩ := hdata i (Finset.mem_range.mp hi)
    rw [Finset.sum_eq_single (m - 1)]
    · rw [Nat.sub_add_cancel hm1, ite_eq_left hxm, hxm]
    · intro l hl hlm
      have hl' := Finset.mem_range.mp hl
      refine ite_eq_right fun h ↦ hlm ?_
      have := hymono.injOn (mem_Iic.mpr (by omega : l + 1 ≤ k)) (mem_Iic.mpr hmk) (h.symm.trans hxm)
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hlt : y j < y (j + 1) :=
    hymono (mem_Iic.mpr hj'.le) (mem_Iic.mpr (by omega)) (Nat.lt_succ_self j)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hunion : (Finset.range n).filter (fun i ↦ x i ≤ y (j + 1)) =
      (Finset.range n).filter (fun i ↦ x i ≤ y j) ∪
        (Finset.range n).filter (fun i ↦ x i = y (j + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    constructor
    · rintro ⟨hi, hle⟩
      obtain ⟨m, hm1, hmk, hxm⟩ := hdata i hi
      rcases lt_trichotomy m (j + 1) with h | h | h
      · left
        exact ⟨hi, hxm ▸ hymono.monotoneOn (mem_Iic.mpr hmk) (mem_Iic.mpr hj'.le) (by omega)⟩
      · right; exact ⟨hi, h ▸ hxm⟩
      · exfalso
        have := hymono (mem_Iic.mpr (by omega)) (mem_Iic.mpr hmk) h
        rw [hxm] at hle; linarith
    · rintro (⟨hi, hle⟩ | ⟨hi, heq⟩)
      · exact ⟨hi, hle.trans hlt.le⟩
      · exact ⟨hi, heq.le⟩
  have hdisj : Disjoint ((Finset.range n).filter (fun i ↦ x i ≤ y j))
      ((Finset.range n).filter (fun i ↦ x i = y (j + 1))) := by
    rw [Finset.disjoint_filter]
    intro i _ hle heq
    rw [heq] at hle; linarith
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hunion] at hcard
  rw [hcard, Nat.cast_add, add_sub_cancel_left]

/-- The values of a nonincreasing density at the right endpoints of the cells of a strictly
increasing grid `0 = y 0 < ⋯ < y k` have Riemann sum at most `1`. -/
theorem sum_mul_sub_le_one_of_isNonincreasingDensity {g : ℝ → ℝ}
    (hg : IsNonincreasingDensity g) {k : ℕ} {y : ℕ → ℝ} (hymono : StrictMonoOn y (Iic k))
    (hy0 : y 0 = 0) : ∑ j ∈ Finset.range k, g (y (j + 1)) * (y (j + 1) - y j) ≤ 1 := by
  obtain ⟨-, hg0, -, hganti, hgint⟩ := hg
  have hynn : ∀ j ≤ k, 0 ≤ y j := fun j hj ↦ by
    rw [← hy0]
    exact hymono.monotoneOn (mem_Iic.mpr (Nat.zero_le k)) (mem_Iic.mpr hj) (Nat.zero_le j)
  have hgi : Integrable g volume := Integrable.of_integral_ne_zero (by rw [hgint]; norm_num)
  have h1 : ∀ j ∈ Finset.range k,
      g (y (j + 1)) * (y (j + 1) - y j) ≤ ∫ t in y j..y (j + 1), g t := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hle := (hymono (mem_Iic.mpr hj'.le) (mem_Iic.mpr (by omega))
      (Nat.lt_succ_self j)).le
    have hyj1 : y (j + 1) ∈ Ioi (0 : ℝ) := lt_of_le_of_lt (hynn j hj'.le)
      (hymono (mem_Iic.mpr hj'.le) (mem_Iic.mpr (by omega)) (Nat.lt_succ_self j))
    have := intervalIntegral.integral_mono_on_of_le_Ioo hle
      (intervalIntegrable_const (c := g (y (j + 1)))) hgi.intervalIntegrable
      (fun t ht ↦ hganti (show t ∈ Ioi (0 : ℝ) from lt_of_le_of_lt (hynn j hj'.le) ht.1)
        hyj1 ht.2.le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith [mul_comm (g (y (j + 1))) (y (j + 1) - y j)]
  calc ∑ j ∈ Finset.range k, g (y (j + 1)) * (y (j + 1) - y j)
      ≤ ∑ j ∈ Finset.range k, ∫ t in y j..y (j + 1), g t := Finset.sum_le_sum h1
    _ = ∫ t in y 0..y k, g t :=
        intervalIntegral.sum_integral_adjacent_intervals fun j _ ↦ hgi.intervalIntegrable
    _ ≤ ∫ t, g t := by
        rw [intervalIntegral.integral_of_le (by rw [hy0]; exact hynn k le_rfl)]
        exact setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
    _ = 1 := hgint

/-- The least concave majorant of a step function on a grid. Let `F` take values in `[0, 1]`
on `[0, ∞)`, vanish at `0`, be constant on each cell `[y l, y (l + 1))` of a strictly
increasing grid `0 = y 0 < ⋯ < y k` with `k ≥ 1`, satisfy `0 < F (y 1)`, stay below `1` at
`y 0, …, y (k - 1)`, and equal `1` from `y k` on. Then its least concave majorant `G` vanishes
at `0`, equals `1` from `y k` on, and is affine on each cell `[y j, y (j + 1)]` with slope
`s j`; the slopes are positive and nonincreasing, and `G` touches `F` at each interior grid
point where the slope strictly decreases. -/
theorem leastConcaveMajorant_affine_on_grid {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hF1 : ∀ t, 0 ≤ t → F t ≤ 1) {k : ℕ} {y s : ℕ → ℝ} (hymono : StrictMonoOn y (Iic k))
    (hy0 : y 0 = 0) (hk : 1 ≤ k)
    (hFconst : ∀ l < k, ∀ t, y l ≤ t → t < y (l + 1) → F t = F (y l)) (hFy0 : F 0 = 0)
    (hFpos : 0 < F (y 1)) (hFlt : ∀ l < k, F (y l) < 1) (hFtop : ∀ t, y k ≤ t → F t = 1)
    (hs : ∀ j, s j = (leastConcaveMajorant F (y (j + 1)) - leastConcaveMajorant F (y j)) /
      (y (j + 1) - y j)) :
    leastConcaveMajorant F 0 = 0 ∧ (∀ t, y k ≤ t → leastConcaveMajorant F t = 1) ∧
      (∀ j < k, ∀ t, y j ≤ t → t ≤ y (j + 1) →
        leastConcaveMajorant F t = leastConcaveMajorant F (y j) + s j * (t - y j)) ∧
      (∀ j, j + 1 < k → s (j + 1) ≤ s j) ∧
      (∀ j, j + 1 < k → s (j + 1) < s j →
        leastConcaveMajorant F (y (j + 1)) = F (y (j + 1))) ∧
      ∀ j < k, 0 < s j := by
  set G := leastConcaveMajorant F
  have hylt : ∀ j l, j < l → l ≤ k → y j < y l := fun j l hjl hlk ↦
    hymono (show j ∈ Iic k by simp only [mem_Iic]; omega) (show l ∈ Iic k from hlk) hjl
  have hynn : ∀ j ≤ k, 0 ≤ y j := fun j hj ↦ by
    rw [← hy0]
    exact hymono.monotoneOn (mem_Iic.mpr (Nat.zero_le k)) (mem_Iic.mpr hj) (Nat.zero_le j)
  have hGc : ConcaveOn ℝ (Ici 0) G := concaveOn_leastConcaveMajorant hF1
  have hFG : ∀ t, 0 ≤ t → F t ≤ G t := fun t ht ↦ le_leastConcaveMajorant hF1 ht
  have hy1 : 0 < y 1 := hy0 ▸ hylt 0 1 one_pos hk
  have hG0 : G 0 = 0 := leastConcaveMajorant_zero_eq_zero hF0 hF1 hy1 fun t ht htl ↦ by
    rw [hFconst 0 hk t (hy0 ▸ ht) htl, hy0, hFy0]
  have hGtop : ∀ t, y k ≤ t → G t = 1 := fun t ht ↦
    le_antisymm (leastConcaveMajorant_le ⟨concaveOn_const 1 (convex_Ici 0), hF1⟩
      ((hynn k le_rfl).trans ht)) ((hFtop t ht).symm.le.trans (hFG t ((hynn k le_rfl).trans ht)))
  have hknot : ∀ j, j + 1 < k → s (j + 1) < s j → G (y (j + 1)) = F (y (j + 1)) := by
    intro j hj hlt
    rw [hs, hs] at hlt
    exact leastConcaveMajorant_eq_of_slope_lt hF0 hF1 (hynn j (by omega))
      (hylt j (j + 1) (by omega) (by omega)) (hylt (j + 1) (j + 2) (by omega) (by omega))
      (hFconst j (by omega)) (hFconst (j + 1) hj) hlt
  refine ⟨hG0, hGtop, fun j hj t h1 h2 ↦ ?_, fun j hj ↦ ?_, hknot, ?_⟩
  · rw [hs]
    exact leastConcaveMajorant_eq_affine hF0 hF1 (hynn j hj.le)
      (hylt j (j + 1) (by omega) hj) (hFconst j hj) h1 h2
  · rw [hs, hs]
    exact hGc.slope_anti_adjacent (show y j ∈ Ici (0 : ℝ) from hynn j (by omega))
      (show y (j + 2) ∈ Ici (0 : ℝ) from hynn (j + 2) (by omega))
      (hylt j (j + 1) (by omega) (by omega)) (hylt (j + 1) (j + 2) (by omega) (by omega))
  refine slope_pos_of_concaveOn_grid hGc hymono hy0 hs ?_
    (fun j hj hlt ↦ (hknot j hj hlt).trans_lt (hFlt (j + 1) hj)) (hGtop _ le_rfl)
  simp only [hs, zero_add, hy0, hG0, sub_zero]
  exact div_pos (hFpos.trans_le (hFG _ hy1.le)) hy1

/-- GAPS 103.11: the Grenander estimator is a nonparametric maximum likelihood estimator
among nonincreasing densities on `[0, ∞)`. Scope: a fixed sample of `n ≥ 1` positive
observations; the estimator is extended by zero to the nonpositive half-line, and the
likelihood is the product of density values at the observations. -/
theorem grenanderEstimator_isMaximumLikelihood {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ)
    (hn : 0 < n) (ω : Ω) (hpos : ∀ i < n, 0 < X i ω) :
    let ĝ := fun t ↦ if 0 < t then grenanderEstimator X n ω t else 0;
    IsNonincreasingDensity ĝ ∧ ∀ g : ℝ → ℝ, IsNonincreasingDensity g →
      ∏ i ∈ Finset.range n, g (X i ω) ≤ ∏ i ∈ Finset.range n, ĝ (X i ω) := by
  classical
  intro ĝ
  obtain ⟨k, hk, y, hymono, hy0, hdata, hgrid⟩ := exists_sample_grid (fun i ↦ X i ω) n hn hpos
  set F := empiricalCDF X n ω
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hylt : ∀ j l, j < l → l ≤ k → y j < y l := fun j l hjl hlk ↦
    hymono (show j ∈ Iic k by simp only [mem_Iic]; omega) (show l ∈ Iic k from hlk) hjl
  have hyle : ∀ j l, j ≤ l → l ≤ k → y j ≤ y l := fun j l hjl hlk ↦
    hymono.monotoneOn (mem_Iic.mpr (hjl.trans hlk)) (mem_Iic.mpr hlk) hjl
  have hynn : ∀ j ≤ k, 0 ≤ y j := fun j hj ↦ hy0 ▸ hyle 0 j (Nat.zero_le j) hj
  -- the empirical distribution function on the grid
  set N : ℕ → ℝ := fun j ↦ (((Finset.range n).filter fun i ↦ X i ω ≤ y j).card : ℝ) with hNdef
  have hFcard : ∀ t, F t = (((Finset.range n).filter fun i ↦ X i ω ≤ t).card : ℝ) / n :=
    fun t ↦ empiricalCDF_def X n ω t
  have hFN : ∀ j, F (y j) = N j / n := fun j ↦ hFcard (y j)
  have hF0 : ∀ t, 0 ≤ t → 0 ≤ F t := fun t _ ↦ by rw [hFcard]; positivity
  have hF1 : ∀ t, 0 ≤ t → F t ≤ 1 := fun t _ ↦ by
    rw [hFcard, div_le_one hnR]
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  have hFconst : ∀ l < k, ∀ t, y l ≤ t → t < y (l + 1) → F t = F (y l) :=
    fun l hl _ h1 h2 ↦ empiricalCDF_eq_of_mem_Ico_grid hymono hdata hl h1 h2
  have hNpos : 0 < N 1 := by
    obtain ⟨i, hi, hxi⟩ := hgrid 1 le_rfl hk
    simp only [hNdef, Nat.cast_pos, Finset.card_pos]
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hxi.le⟩⟩
  have hN0 : N 0 = 0 := by
    simp only [hNdef, hy0, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_range, not_le]
    exact fun i hi ↦ hpos i hi
  -- the least concave majorant
  have hFy0 : F 0 = 0 := by
    have := hFN 0
    rwa [hN0, zero_div, hy0] at this
  set s : ℕ → ℝ := fun j ↦ (leastConcaveMajorant F (y (j + 1)) -
    leastConcaveMajorant F (y j)) / (y (j + 1) - y j)
  obtain ⟨hG0, hGtop, haff, hsanti, hknot, hspos⟩ := leastConcaveMajorant_affine_on_grid hF0 hF1
    hymono hy0 hk hFconst hFy0 (by rw [hFN]; exact div_pos hNpos hnR)
    (fun l hl ↦ empiricalCDF_lt_one_of_lt_grid hymono hgrid hk hl)
    (fun t ht ↦ empiricalCDF_eq_one_of_grid_le hn hymono hdata ht) fun _ ↦ rfl
  set G := leastConcaveMajorant F
  have hFG : ∀ t, 0 ≤ t → F t ≤ G t := fun t ht ↦ le_leastConcaveMajorant hF1 ht
  have hsanti' : ∀ j l, j ≤ l → l < k → s l ≤ s j := by
    intro j l hjl hl
    induction l with
    | zero => rw [Nat.le_zero.mp hjl]
    | succ l ih =>
      rcases hjl.lt_or_eq with h | h
      · exact (hsanti l hl).trans (ih (by omega) (by omega))
      · rw [h]
  -- the estimator is a step function on the grid
  have hrep : ĝ = fun t ↦
      ∑ j ∈ Finset.range k, (Ioc (y j) (y (j + 1))).indicator (fun _ ↦ s j) t := by
    funext t
    rcases le_or_gt t 0 with ht | ht
    · simp only [ĝ, not_lt.mpr ht, ite_false]
      refine (sum_indicator_Ioc_eq_zero_of_notMem s hymono.monotoneOn fun h ↦ ?_).symm
      linarith [h.1]
    simp only [ĝ, ht, ite_true]
    exact derivWithin_Iio_eq_sum_indicator hymono hy0 haff
      (fun u hu ↦ by rw [hGtop u hu, hGtop _ le_rfl]) ht
  have hval : ∀ j < k, ∀ t ∈ Ioc (y j) (y (j + 1)), ĝ t = s j := fun j hj t ht ↦ by
    rw [hrep]; exact sum_indicator_Ioc_eq_of_mem s hymono hj ht
  have hdensity : IsNonincreasingDensity ĝ := by
    rw [hrep]
    refine isNonincreasingDensity_sum_indicator hymono hy0 hspos hsanti' ?_
    have htel := Finset.sum_range_sub (fun j ↦ G (y j)) k
    beta_reduce at htel
    rw [hGtop _ le_rfl, hy0, hG0, sub_zero] at htel
    rw [← htel]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    exact div_mul_cancel₀ _ (sub_pos.mpr (hylt j (j + 1) (by omega)
      (Finset.mem_range.mp hj))).ne'
  refine ⟨hdensity, fun g hg ↦ ?_⟩
  -- comparison of the likelihoods
  have hĝpos : ∀ i < n, 0 < ĝ (X i ω) := fun i hi ↦ by
    obtain ⟨m, hm1, hmk, hxm⟩ := hdata i hi
    have hm : X i ω ∈ Ioc (y (m - 1)) (y (m - 1 + 1)) := by
      rw [Nat.sub_add_cancel hm1, hxm]; exact ⟨hylt (m - 1) m (by omega) hmk, le_rfl⟩
    rw [hval (m - 1) (by omega) _ hm]; exact hspos _ (by omega)
  have hfiber : ∑ i ∈ Finset.range n, g (X i ω) / ĝ (X i ω) =
      ∑ j ∈ Finset.range k, (N (j + 1) - N j) * g (y (j + 1)) / s j := by
    rw [sum_comp_eq_sum_count_sub (fun i ↦ X i ω) n k y hymono hdata fun t ↦ g t / ĝ t]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    rw [hval j hj' _ ⟨hylt j (j + 1) (by omega) hj', le_rfl⟩, mul_div_assoc]
  have hkey := sum_count_mul_div_slope_le k n y (fun j ↦ G (y j)) N s (fun j ↦ g (y (j + 1)))
    (fun j hj ↦ hylt j (j + 1) (by omega) hj) (fun j _ ↦ rfl) hspos hsanti
    (fun j hj hlt ↦ by
      rw [hknot j hj hlt, hFN]; field_simp)
    (fun j hj ↦ by
      have := hFG (y j) (hynn j hj)
      rw [hFN, div_le_iff₀ hnR] at this; linarith)
    (by simp only [hy0, hG0]) hN0 hy0
    (fun j hj ↦ hg.2.2.2.1
      (show y (j + 1) ∈ Ioi (0 : ℝ) from hy0 ▸ hylt 0 (j + 1) (by omega) (by omega))
      (show y (j + 1 + 1) ∈ Ioi (0 : ℝ) from hy0 ▸ hylt 0 (j + 1 + 1) (by omega) (by omega))
      (hylt (j + 1) (j + 1 + 1) (by omega) (by omega)).le)
    (fun j _ ↦ hg.2.1 _)
  refine prod_le_prod_of_sum_div_le hĝpos (fun i _ ↦ hg.2.1 _) ?_
  calc ∑ i ∈ Finset.range n, g (X i ω) / ĝ (X i ω)
      = ∑ j ∈ Finset.range k, (N (j + 1) - N j) * g (y (j + 1)) / s j := hfiber
    _ ≤ n * ∑ j ∈ Finset.range k, g (y (j + 1)) * (y (j + 1) - y j) := hkey
    _ ≤ n * 1 :=
        mul_le_mul_of_nonneg_left (sum_mul_sub_le_one_of_isNonincreasingDensity hg hymono hy0)
          hnR.le
    _ = n := mul_one _

/-- GAPS 103.11: the cube-root limit law of the Grenander estimator at an interior point. Let
`X₁, X₂, …` be independent with law `P`, whose density `f` vanishes on `(-∞, 0)` and is
nonincreasing on `(0, ∞)`, and let `f` be differentiable at `x₀ > 0` with `f'(x₀) < 0` (which
gives continuity at `x₀`). Then `n^{1/3} (f̂ₙ(x₀) - f(x₀))` converges in distribution to
`|4 f(x₀) f'(x₀)|^{1/3} Z`, where `Z = argmax_t (W(t) - t²)` for a two-sided Brownian motion `W`.
Positivity `f(x₀) > 0` is not assumed: it follows from monotonicity and `f'(x₀) < 0`. -/
theorem tendstoInDistribution_grenanderEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f : ℝ → ℝ)
    (hf : HasDensity P volume f) (hneg : ∀ t < 0, f t = 0)
    (hanti : AntitoneOn f (Ioi 0)) (x₀ f' : ℝ) (hx₀ : 0 < x₀) (hderiv : HasDerivAt f f' x₀)
    (hf' : f' < 0) {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (B₁ B₂ : ℝ≥0 → Ω' → ℝ) (Z : Ω' → ℝ) (hZ : IsChernoffArgmax ν B₁ B₂ Z) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (grenanderEstimator X n ω x₀ - f x₀))
      atTop id (fun _ ↦ μ)
      (ν.map fun ω ↦ |4 * f x₀ * f'| ^ (1 / 3 : ℝ) * Z ω) := by
  sorry

end CKSD
