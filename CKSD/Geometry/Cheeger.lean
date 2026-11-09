module

public import CKSD.Geometry.Basic

/-!
# Cheeger's inequalities for weighted graphs

For a connected weighted graph with nonnegative symmetric weights, the spectral gap `λ₂` of the
normalized Laplacian and the Cheeger constant `h` satisfy `h² / 2 ≤ λ₂ ≤ 2 h`. The lower bound
is proved by the discrete co-area formula applied to a weighted median shift of a second
eigenvector, the upper bound by testing the Rayleigh quotient with the two-valued function of an
optimal cut.

## Main results

* `CKSD.cheegerConstant_nonneg`, `CKSD.cheegerConstant_le_cutWeight_div`: basic bounds for the
  Cheeger constant.
* `CKSD.spectralGap_cheegerConstant_bounds`: Cheeger's inequalities for the normalized Laplacian
  of a connected weighted graph (GAPS 108.1).

## References

* F. R. K. Chung, *Spectral graph theory*, CBMS Regional Conference Series in Mathematics 92,
  AMS, 1997.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

section Cheeger

open Finset

variable {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)

/-- For nonnegative weights all conductance ratios of nonempty proper sets are nonnegative. -/
private theorem conductanceRatio_nonneg (hpos : ∀ i j, 0 ≤ W i j) :
    ∀ r ∈ {r | ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ univ ∧
      r = cutWeight W S / min (graphVolume W S) (graphVolume W Sᶜ)}, 0 ≤ r := by
  rintro _ ⟨S, -, -, rfl⟩
  refine div_nonneg (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hpos i j) (le_min ?_ ?_) <;>
    exact sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hpos i j

/-- For nonnegative weights the Cheeger constant is nonnegative. -/
theorem cheegerConstant_nonneg (hpos : ∀ i j, 0 ≤ W i j) : 0 ≤ cheegerConstant W :=
  Real.sInf_nonneg (conductanceRatio_nonneg W hpos)

/-- For nonnegative weights the Cheeger constant is at most every conductance ratio. -/
theorem cheegerConstant_le_cutWeight_div (hpos : ∀ i j, 0 ≤ W i j) {T : Finset (Fin n)}
    (hT : T.Nonempty) (hTu : T ≠ univ) :
    cheegerConstant W ≤ cutWeight W T / min (graphVolume W T) (graphVolume W Tᶜ) :=
  csInf_le ⟨0, conductanceRatio_nonneg W hpos⟩ ⟨T, hT, hTu, rfl⟩

/-- In a connected weighted graph on at least two vertices every degree is positive. -/
theorem weightedDegree_pos (hn : 2 ≤ n) (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ univ → 0 < cutWeight W S) (i : Fin n) :
    0 < weightedDegree W i := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hj⟩ := exists_ne i
  have h := hconn {i} (singleton_nonempty i) fun h ↦ hj (mem_singleton.mp (h ▸ mem_univ j))
  rw [cutWeight, sum_singleton] at h
  exact h.trans_le (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ hpos i j)

/-- The double sum `∑_{i,j} W_{ij} (g_i² + g_j²)` of a symmetric weight matrix is
`2 ∑_i d_i g_i²`. -/
private theorem sum_sum_mul_sq_add_sq (hW : ∀ i j, W i j = W j i) (g : Fin n → ℝ) :
    ∑ i, ∑ j, W i j * (g i ^ 2 + g j ^ 2) = 2 * ∑ i, weightedDegree W i * g i ^ 2 := by
  have h1 : ∑ i, ∑ j, W i j * g i ^ 2 = ∑ i, weightedDegree W i * g i ^ 2 := by
    simp [weightedDegree, sum_mul]
  have h2 : ∑ i, ∑ j, W i j * g j ^ 2 = ∑ i, weightedDegree W i * g i ^ 2 := by
    rw [sum_comm]; simp only [weightedDegree, sum_mul]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ by rw [hW]
  simp only [mul_add, sum_add_distrib, h1, h2]
  ring

/-- Symmetrization of the positive part: for a symmetric weight matrix,
`∑_{i,j} W_{ij} |a_i - a_j| = 2 ∑_{i,j} W_{ij} (a_i - a_j)⁺`. -/
private theorem sum_sum_mul_abs_sub (hW : ∀ i j, W i j = W j i) (a : Fin n → ℝ) :
    ∑ i, ∑ j, W i j * |a i - a j| = 2 * ∑ i, ∑ j, W i j * max (a i - a j) 0 := by
  have hswap : ∑ i, ∑ j, W i j * max (-(a i - a j)) 0 = ∑ i, ∑ j, W i j * max (a i - a j) 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hW, neg_sub]
  have habs : ∀ x : ℝ, |x| = max x 0 + max (-x) 0 := fun x ↦ by
    rcases le_total 0 x with h | h <;> simp [abs_of_nonneg, abs_of_nonpos, h]
  simp only [habs, mul_add, sum_add_distrib, hswap]
  ring

/-- The co-area inequality for the positive part, proved by peeling off the smallest positive
level: if `a ≥ 0` and every nonempty vertex set `S` with `2 vol S ≤ vol V` satisfies
`h vol S ≤ w(S, Sᶜ)`, then `h ∑ d_i a_i ≤ ∑_{i,j} W_{ij} (a_i - a_j)⁺` whenever the support of
`a` has `2 vol ≤ vol V`. -/
private theorem mul_sum_le_sum_sum_mul_max_sub (hpos : ∀ i j, 0 ≤ W i j) (h : ℝ)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty →
      2 * graphVolume W S ≤ graphVolume W univ → h * graphVolume W S ≤ cutWeight W S) :
    ∀ (k : ℕ) (a : Fin n → ℝ), (∀ i, 0 ≤ a i) → (univ.filter fun i ↦ 0 < a i).card = k →
      2 * graphVolume W (univ.filter fun i ↦ 0 < a i) ≤ graphVolume W univ →
      h * ∑ i, weightedDegree W i * a i ≤ ∑ i, ∑ j, W i j * max (a i - a j) 0 := by
  have hdeg : ∀ i, 0 ≤ weightedDegree W i := fun i ↦ sum_nonneg fun j _ ↦ hpos i j
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a ha hk hvol
  set S := univ.filter fun i ↦ 0 < a i with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      by_contra hne
      have : i ∈ S := by simp [hS, lt_of_le_of_ne (ha i) (Ne.symm hne)]
      simp [hSe] at this
    simp [ha0]
  -- peel off the smallest positive level
  set m := S.inf' hSne a
  obtain ⟨i₀, hi₀S, hi₀⟩ := S.exists_mem_eq_inf' hSne a
  have hmS : ∀ i ∈ S, m ≤ a i := fun i hi ↦ S.inf'_le a hi
  have hmpos : 0 < m := by
    change 0 < S.inf' hSne a
    rw [hi₀]; exact (mem_filter.mp hi₀S).2
  have hnotS : ∀ i, i ∉ S → a i = 0 := fun i hi ↦
    le_antisymm (not_lt.mp fun h ↦ hi (by simp [hS, h])) (ha i)
  set a' : Fin n → ℝ := fun i ↦ if i ∈ S then a i - m else 0
  have ha' : ∀ i, 0 ≤ a' i := by
    intro i; simp only [a']; split_ifs with hi
    · linarith [hmS i hi]
    · exact le_rfl
  set S' := univ.filter fun i ↦ 0 < a' i
  have hS'sub : S' ⊆ S.erase i₀ := by
    intro i hi
    simp only [S', mem_filter, mem_univ, true_and, a'] at hi
    split_ifs at hi with hiS
    · refine mem_erase.mpr ⟨fun h ↦ ?_, hiS⟩
      rw [h, ← hi₀] at hi; linarith
    · exact absurd hi (lt_irrefl 0)
  have hcard : S'.card < k := by
    rw [← hk]
    exact (card_le_card hS'sub).trans_lt (card_erase_lt_of_mem hi₀S)
  have hvol' : 2 * graphVolume W S' ≤ graphVolume W univ := by
    refine le_trans ?_ hvol
    gcongr
    exact sum_le_sum_of_subset_of_nonneg (hS'sub.trans (erase_subset _ _)) fun i _ _ ↦ hdeg i
  have hIH := ih _ hcard a' ha' rfl hvol'
  -- the decomposition of both sides
  have hpt : ∀ i j, W i j * max (a i - a j) 0 =
      W i j * max (a' i - a' j) 0 + (if i ∈ S then (if j ∈ Sᶜ then m * W i j else 0) else 0) := by
    intro i j
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp only [a', hi, hj, ite_true, ite_false, mem_compl, not_true, not_false_eq_true]
    · ring_nf
    · rw [hnotS j hj, sub_zero, sub_zero, max_eq_left (ha i),
        max_eq_left (by linarith [hmS i hi])]
      ring
    · rw [hnotS i hi, zero_sub, max_eq_right (by linarith [ha j]), zero_sub,
        max_eq_right (by linarith [hmS j hj])]
      ring
    · rw [hnotS i hi, hnotS j hj]; ring
  have hsumR : ∑ i, ∑ j, W i j * max (a i - a j) 0 =
      ∑ i, ∑ j, W i j * max (a' i - a' j) 0 + m * cutWeight W S := by
    simp only [hpt, sum_add_distrib]
    congr 1
    have hin : ∀ i, ∑ j, (if i ∈ S then (if j ∈ Sᶜ then m * W i j else 0) else 0) =
        if i ∈ S then ∑ j ∈ Sᶜ, m * W i j else 0 := by
      intro i
      split_ifs
      · rw [sum_ite_mem, univ_inter]
      · simp
    rw [sum_congr rfl fun i _ ↦ hin i, sum_ite_mem, univ_inter, cutWeight, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [mul_sum]
  have hsumL : ∑ i, weightedDegree W i * a i =
      ∑ i, weightedDegree W i * a' i + m * graphVolume W S := by
    have e1 : ∑ i ∈ Sᶜ, weightedDegree W i * a i = 0 :=
      sum_eq_zero fun i hi ↦ by rw [hnotS i (mem_compl.mp hi), mul_zero]
    have e2 : ∑ i ∈ Sᶜ, weightedDegree W i * a' i = 0 :=
      sum_eq_zero fun i hi ↦ by simp [a', mem_compl.mp hi]
    rw [← sum_add_sum_compl S, ← sum_add_sum_compl S (fun i ↦ weightedDegree W i * a' i), e1, e2,
      add_zero, add_zero, graphVolume, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i hi ↦ by simp only [a', hi, ite_true]; ring
  rw [hsumR, hsumL, mul_add, mul_left_comm]
  linarith [mul_le_mul_of_nonneg_left (hcut S hSne hvol) hmpos.le]

/-- The sharp Rayleigh-quotient estimate behind Cheeger's inequality: for a function `g` whose
support has `2 vol ≤ vol V`, with `D = ∑ d_i g_i²` and `E = ½ ∑_{i,j} W_{ij} (g_i - g_j)²`,
`h² D² ≤ E (2D - E)`. -/
private theorem sq_mul_sq_le_of_support (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j)
    (h : ℝ) (hh : 0 ≤ h)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty →
      2 * graphVolume W S ≤ graphVolume W univ → h * graphVolume W S ≤ cutWeight W S)
    (g : Fin n → ℝ)
    (hsupp : 2 * graphVolume W (univ.filter fun i ↦ 0 < g i ^ 2) ≤ graphVolume W univ) :
    let D := ∑ i, weightedDegree W i * g i ^ 2
    let E := (∑ i, ∑ j, W i j * (g i - g j) ^ 2) / 2
    h ^ 2 * D ^ 2 ≤ E * (2 * D - E) := by
  intro D E
  have hdeg : ∀ i, 0 ≤ weightedDegree W i := fun i ↦ sum_nonneg fun j _ ↦ hpos i j
  have hD : 0 ≤ D := sum_nonneg fun i _ ↦ mul_nonneg (hdeg i) (sq_nonneg _)
  set a : Fin n → ℝ := fun i ↦ g i ^ 2
  have hco := mul_sum_le_sum_sum_mul_max_sub W hpos h hcut _ a (fun i ↦ sq_nonneg _) rfl hsupp
  set P := ∑ i, ∑ j, W i j * max (a i - a j) 0
  have habs := sum_sum_mul_abs_sub W hW a
  -- Cauchy–Schwarz over pairs
  have hCS : (∑ i, ∑ j, W i j * |a i - a j|) ^ 2 ≤
      (∑ i, ∑ j, W i j * (g i - g j) ^ 2) * ∑ i, ∑ j, W i j * (g i + g j) ^ 2 := by
    simp only [← Fintype.sum_prod_type']
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ ↦ mul_nonneg (hpos _ _) (sq_nonneg _))
      (fun p _ ↦ mul_nonneg (hpos _ _) (sq_nonneg _)) fun p _ ↦ le_of_eq ?_
    simp only [a]; rw [mul_pow, sq_abs]; ring
  have hplus : ∑ i, ∑ j, W i j * (g i + g j) ^ 2 = 4 * D - 2 * E := by
    have h1 := sum_sum_mul_sq_add_sq W hW g
    have h2 : ∀ i j, W i j * (g i + g j) ^ 2 =
        2 * (W i j * (g i ^ 2 + g j ^ 2)) - W i j * (g i - g j) ^ 2 := fun i j ↦ by ring
    simp only [h2, sum_sub_distrib, ← mul_sum, h1]
    simp only [D, E]
    ring
  rw [habs, hplus] at hCS
  have h2E : ∑ i, ∑ j, W i j * (g i - g j) ^ 2 = 2 * E := by simp only [E]; ring
  rw [h2E] at hCS
  change (2 * P) ^ 2 ≤ 2 * E * (4 * D - 2 * E) at hCS
  have : (h * D) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (mul_nonneg hh hD) hco 2
  linarith [show (2 * P) ^ 2 = 4 * P ^ 2 by ring, show (h * D) ^ 2 = h ^ 2 * D ^ 2 by ring,
    show 2 * E * (4 * D - 2 * E) = 4 * (E * (2 * D - E)) by ring]

/-- A weighted median: a level `c` with `2 vol {f > c} ≤ vol V` and `2 vol {f < c} ≤ vol V`. -/
private theorem exists_weighted_median (hpos : ∀ i j, 0 ≤ W i j) (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ c : ℝ, 2 * graphVolume W (univ.filter fun i ↦ c < f i) ≤ graphVolume W univ ∧
      2 * graphVolume W (univ.filter fun i ↦ f i < c) ≤ graphVolume W univ := by
  have hdeg : ∀ i, 0 ≤ weightedDegree W i := fun i ↦ sum_nonneg fun j _ ↦ hpos i j
  set V := graphVolume W univ
  set vle := fun c : ℝ ↦ graphVolume W (univ.filter fun i ↦ f i ≤ c)
  set T := univ.filter fun i : Fin n ↦ V ≤ 2 * vle (f i)
  have hsplit : ∀ c, graphVolume W (univ.filter fun i ↦ c < f i) = V - vle c := by
    intro c
    have := sum_filter_add_sum_filter_not univ (fun i ↦ f i ≤ c) (weightedDegree W)
    simp only [not_le] at this
    simp only [V, vle, graphVolume]
    linarith
  have hTne : T.Nonempty := by
    obtain ⟨k, -, hk⟩ := univ.exists_max_image f ⟨⟨0, hn⟩, mem_univ _⟩
    refine ⟨k, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have : (univ.filter fun i ↦ f i ≤ f k) = univ := by
      ext i; simp [hk i (mem_univ _)]
    simp only [vle, this]
    linarith [show 0 ≤ V from sum_nonneg fun i _ ↦ hdeg i]
  obtain ⟨k, hkT, hk⟩ := T.exists_min_image f hTne
  refine ⟨f k, ?_, ?_⟩
  · rw [hsplit]; linarith [(mem_filter.mp hkT).2]
  · rcases (univ.filter fun i ↦ f i < f k).eq_empty_or_nonempty with he | hne
    · rw [he, graphVolume, sum_empty, mul_zero]
      exact sum_nonneg fun i _ ↦ hdeg i
    obtain ⟨j, hj, hjmax⟩ := (univ.filter fun i ↦ f i < f k).exists_max_image f hne
    have hjk : f j < f k := (mem_filter.mp hj).2
    have hjT : j ∉ T := fun h ↦ absurd (hk j h) (not_le.mpr hjk)
    have hjv : 2 * vle (f j) < V :=
      not_le.mp fun hc ↦ hjT (mem_filter.mpr ⟨mem_univ _, hc⟩)
    have : graphVolume W _ ≤ graphVolume W _ := sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ mem_filter.mpr ⟨mem_univ _, hjmax i hi⟩ :
        (univ.filter fun i ↦ f i < f k) ⊆ univ.filter fun i ↦ f i ≤ f j) fun i _ _ ↦ hdeg i
    simp only [vle] at hjv
    linarith

/-- Positive and negative parts split the Dirichlet energy: for all reals `x, y`,
`(x⁺ - y⁺)² + (x⁻ - y⁻)² ≤ (x - y)²`. -/
private theorem sq_sub_posPart_add_sq_sub_negPart_le (x y : ℝ) :
    (max x 0 - max y 0) ^ 2 + (max (-x) 0 - max (-y) 0) ^ 2 ≤ (x - y) ^ 2 := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp [hx, hy] <;> nlinarith

/-- The core of the upper Cheeger bounds: for every admissible test function `f` of the Rayleigh
principle with energy `r`, `h² ≤ 2r`, and `h² ≤ r (2 - r)` unless `r ≥ 1`. -/
private theorem cheeger_sq_le_of_admissible (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j)
    (hn : 0 < n) (hdeg : ∀ i, 0 < weightedDegree W i) (h : ℝ) (hh : 0 ≤ h)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty →
      2 * graphVolume W S ≤ graphVolume W univ → h * graphVolume W S ≤ cutWeight W S)
    (f : Fin n → ℝ) (hf0 : ∑ i, weightedDegree W i * f i = 0)
    (hf1 : ∑ i, weightedDegree W i * f i ^ 2 = 1) :
    let r := (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2
    h ^ 2 ≤ 2 * r ∧ (1 ≤ r ∨ h ^ 2 ≤ r * (2 - r)) := by
  intro r
  have hr0 : 0 ≤ r := div_nonneg (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦
    mul_nonneg (hpos i j) (sq_nonneg _)) zero_le_two
  obtain ⟨c, hc1, hc2⟩ := exists_weighted_median W hpos hn f
  set gp : Fin n → ℝ := fun i ↦ max (f i - c) 0
  set gm : Fin n → ℝ := fun i ↦ max (-(f i - c)) 0
  set Dof := fun g : Fin n → ℝ ↦ ∑ i, weightedDegree W i * g i ^ 2
  set Eof := fun g : Fin n → ℝ ↦ (∑ i, ∑ j, W i j * (g i - g j) ^ 2) / 2
  have hEnn : ∀ g, 0 ≤ Eof g := fun g ↦ div_nonneg (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦
    mul_nonneg (hpos i j) (sq_nonneg _)) zero_le_two
  have hDnn : ∀ g, 0 ≤ Dof g := fun g ↦ sum_nonneg fun i _ ↦
    mul_nonneg (hdeg i).le (sq_nonneg _)
  have hE : Eof gp + Eof gm ≤ r := by
    simp only [Eof, r, ← add_div, ← sum_add_distrib]
    gcongr with i _ j _
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hpos i j)
    have := sq_sub_posPart_add_sq_sub_negPart_le (f i - c) (f j - c)
    rwa [sub_sub_sub_cancel_right] at this
  have hD : 1 ≤ Dof gp + Dof gm := by
    have hpt : ∀ i, weightedDegree W i * gp i ^ 2 + weightedDegree W i * gm i ^ 2 =
        weightedDegree W i * f i ^ 2 - 2 * c * (weightedDegree W i * f i) +
          c ^ 2 * weightedDegree W i := by
      intro i
      have hsq : ∀ x : ℝ, max x 0 ^ 2 + max (-x) 0 ^ 2 = x ^ 2 := fun x ↦ by
        rcases le_total 0 x with h | h <;> simp [h]
      have := hsq (f i - c)
      simp only [gp, gm, ← mul_add, this]
      ring
    have hV : 0 ≤ ∑ i, weightedDegree W i := sum_nonneg fun i _ ↦ (hdeg i).le
    calc (1 : ℝ) ≤ 1 - 2 * c * 0 + c ^ 2 * ∑ i, weightedDegree W i := by
          nlinarith [sq_nonneg c]
      _ = ∑ i, (weightedDegree W i * f i ^ 2 - 2 * c * (weightedDegree W i * f i) +
          c ^ 2 * weightedDegree W i) := by
          rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hf0, hf1]
      _ = Dof gp + Dof gm := by
          simp only [Dof]
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ ↦ (hpt i).symm
  have hpos2 : ∀ x : ℝ, 0 < max x 0 ^ 2 ↔ 0 < x := fun x ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [max_eq_left h.le, h]⟩
    by_contra hx
    simp [max_eq_right (not_lt.mp hx)] at h
  have hsuppp : 2 * graphVolume W (univ.filter fun i ↦ 0 < gp i ^ 2) ≤ graphVolume W univ := by
    simpa only [gp, hpos2, sub_pos] using hc1
  have hsuppm : 2 * graphVolume W (univ.filter fun i ↦ 0 < gm i ^ 2) ≤ graphVolume W univ := by
    simpa only [gm, hpos2, neg_sub, sub_pos] using hc2
  -- one of the two parts has Rayleigh quotient at most `r`
  obtain ⟨g, hgsupp, hgD, hgE⟩ : ∃ g : Fin n → ℝ,
      2 * graphVolume W (univ.filter fun i ↦ 0 < g i ^ 2) ≤ graphVolume W univ ∧
      0 < Dof g ∧ Eof g ≤ r * Dof g := by
    by_contra hno
    push Not at hno
    have key : ∀ g, 2 * graphVolume W (univ.filter fun i ↦ 0 < g i ^ 2) ≤ graphVolume W univ →
        r * Dof g ≤ Eof g := fun g hg ↦ by
      rcases (hDnn g).eq_or_lt with h0 | h0
      · rw [← h0, mul_zero]; exact hEnn g
      · exact (hno g hg h0).le
    rcases (hDnn gp).eq_or_lt with h0 | h0
    · nlinarith [hno gm hsuppm (by linarith), key gp hsuppp]
    · nlinarith [hno gp hsuppp h0, key gm hsuppm]
  have hcore := sq_mul_sq_le_of_support W hW hpos h hh hcut g hgsupp
  simp only at hcore
  change h ^ 2 * Dof g ^ 2 ≤ Eof g * (2 * Dof g - Eof g) at hcore
  have hEg := hEnn g
  have hD2 : 0 < Dof g ^ 2 := pow_pos hgD 2
  refine ⟨?_, ?_⟩
  · have : h ^ 2 * Dof g ^ 2 ≤ 2 * r * Dof g ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hD2
  · by_cases hr1 : 1 ≤ r
    · exact Or.inl hr1
    right
    push Not at hr1
    have : h ^ 2 * Dof g ^ 2 ≤ r * (2 - r) * Dof g ^ 2 := by
      have hkey : Eof g * (2 * Dof g - Eof g) ≤ r * Dof g * (2 * Dof g - r * Dof g) := by
        have h1 : 0 ≤ r * Dof g - Eof g := by linarith
        have h2 : 0 ≤ 2 * Dof g - Eof g - r * Dof g := by nlinarith
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right this hD2

/-- The two-valued test function of a cut: for a vertex set `S` with `vol S, vol Sᶜ > 0` there is
an admissible function for the Rayleigh principle whose energy is at most twice the conductance
ratio of `S`. -/
private theorem exists_admissible_energy_le (hW : ∀ i j, W i j = W j i) (hpos : ∀ i j, 0 ≤ W i j)
    (S : Finset (Fin n)) (hA : 0 < graphVolume W S) (hB : 0 < graphVolume W Sᶜ) :
    ∃ f : Fin n → ℝ, (∑ i, weightedDegree W i * f i) = 0 ∧
      (∑ i, weightedDegree W i * f i ^ 2) = 1 ∧
      (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2 ≤
        2 * (cutWeight W S / min (graphVolume W S) (graphVolume W Sᶜ)) := by
  set A := graphVolume W S
  set B := graphVolume W Sᶜ
  set α := (Real.sqrt (A * B * (A + B)))⁻¹
  have hα2 : α ^ 2 = (A * B * (A + B))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  set f : Fin n → ℝ := fun i ↦ if i ∈ S then α * B else -(α * A)
  have hfS : ∀ i ∈ S, f i = α * B := fun i hi ↦ by simp [f, hi]
  have hfSc : ∀ i ∈ Sᶜ, f i = -(α * A) := fun i hi ↦ by simp [f, mem_compl.mp hi]
  have hsplit : ∀ F : Fin n → ℝ, ∑ i, F i = ∑ i ∈ S, F i + ∑ i ∈ Sᶜ, F i :=
    fun F ↦ (sum_add_sum_compl S F).symm
  have hcut0 : 0 ≤ cutWeight W S := sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hpos i j
  have hsumf : ∀ F : ℝ → ℝ, ∑ i, weightedDegree W i * F (f i) =
      A * F (α * B) + B * F (-(α * A)) := fun F ↦ by
    rw [hsplit, sum_congr rfl fun i hi ↦ congrArg (fun x ↦ weightedDegree W i * F x) (hfS i hi),
      sum_congr rfl fun i hi ↦ congrArg (fun x ↦ weightedDegree W i * F x) (hfSc i hi),
      ← sum_mul, ← sum_mul]
    rfl
  refine ⟨f, ?_, ?_, ?_⟩
  · have := hsumf id
    simp only [id] at this
    rw [this]; ring
  · rw [hsumf (· ^ 2)]
    have : A * (α * B) ^ 2 + B * (-(α * A)) ^ 2 = α ^ 2 * (A * B * (A + B)) := by ring
    rw [this, hα2, inv_mul_cancel₀ (by positivity)]
  · -- block decomposition of the energy
    have hblock : ∑ i, ∑ j, W i j * (f i - f j) ^ 2 =
        (α * (A + B)) ^ 2 * (cutWeight W S + ∑ i ∈ Sᶜ, ∑ j ∈ S, W i j) := by
      rw [hsplit]
      simp only [hsplit (fun j ↦ W _ j * (f _ - f j) ^ 2)]
      rw [sum_add_distrib, sum_add_distrib]
      have h1 : ∑ i ∈ S, ∑ j ∈ S, W i j * (f i - f j) ^ 2 = 0 :=
        sum_eq_zero fun i hi ↦ sum_eq_zero fun j hj ↦ by rw [hfS i hi, hfS j hj]; ring
      have h2 : ∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, W i j * (f i - f j) ^ 2 = 0 :=
        sum_eq_zero fun i hi ↦ sum_eq_zero fun j hj ↦ by rw [hfSc i hi, hfSc j hj]; ring
      have h3 : ∑ i ∈ S, ∑ j ∈ Sᶜ, W i j * (f i - f j) ^ 2 =
          (α * (A + B)) ^ 2 * cutWeight W S := by
        rw [cutWeight, mul_sum]
        exact sum_congr rfl fun i hi ↦ by
          rw [mul_sum]
          exact sum_congr rfl fun j hj ↦ by rw [hfS i hi, hfSc j hj]; ring
      have h4 : ∑ i ∈ Sᶜ, ∑ j ∈ S, W i j * (f i - f j) ^ 2 =
          (α * (A + B)) ^ 2 * ∑ i ∈ Sᶜ, ∑ j ∈ S, W i j := by
        rw [mul_sum]
        exact sum_congr rfl fun i hi ↦ by
          rw [mul_sum]
          exact sum_congr rfl fun j hj ↦ by rw [hfSc i hi, hfS j hj]; ring
      rw [h1, h2, h3, h4]
      ring
    have hsymcut : ∑ i ∈ Sᶜ, ∑ j ∈ S, W i j = cutWeight W S := by
      refine Finset.sum_comm.trans ?_
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ hW j i
    rw [hblock, hsymcut]
    have hval : (α * (A + B)) ^ 2 * (cutWeight W S + cutWeight W S) / 2 =
        cutWeight W S / A + cutWeight W S / B := by
      rw [mul_pow, hα2]
      field_simp
      ring
    rw [hval, two_mul]
    have hm : 0 < min A B := lt_min hA hB
    exact add_le_add (div_le_div_of_nonneg_left hcut0 hm (min_le_left _ _))
      (div_le_div_of_nonneg_left hcut0 hm (min_le_right _ _))

/-- GAPS 108.1: Cheeger's inequalities for a finite weighted connected graph. For a symmetric
nonnegative weight matrix on `n ≥ 2` vertices in which every nonempty proper cut has positive
weight, the spectral gap `λ₁` of the normalized Laplacian and the conductance `h` satisfy
`λ₁ / 2 ≤ h ≤ √(2 λ₁)` and `1 - √(1 - h²) ≤ λ₁`. Under these hypotheses the sets defining `λ₁`
and `h` are nonempty and bounded below, so no junk values occur. -/
theorem spectralGap_cheegerConstant_bounds {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin n) (Fin n) ℝ)
    (hsym : W.IsSymm) (hpos : ∀ i j, 0 ≤ W i j)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 0 < cutWeight W S) :
    spectralGap W / 2 ≤ cheegerConstant W ∧ cheegerConstant W ≤ Real.sqrt (2 * spectralGap W) ∧
      1 - Real.sqrt (1 - cheegerConstant W ^ 2) ≤ spectralGap W := by
  have hW : ∀ i j, W i j = W j i := fun i j ↦ (hsym.apply i j).symm
  have hn0 : 0 < n := by omega
  have hdeg := weightedDegree_pos W hn hpos hconn
  have hvolpos : ∀ S : Finset (Fin n), S.Nonempty → 0 < graphVolume W S :=
    fun S hS ↦ sum_pos (fun i _ ↦ hdeg i) hS
  have hvolsplit : ∀ S : Finset (Fin n),
      graphVolume W S + graphVolume W Sᶜ = graphVolume W Finset.univ :=
    fun S ↦ sum_add_sum_compl S _
  set h := cheegerConstant W
  have hh0 : 0 ≤ h := cheegerConstant_nonneg W hpos
  have hcompl : ∀ S : Finset (Fin n), S ≠ Finset.univ → Sᶜ.Nonempty := fun S hS ↦ by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h ↦ hS (Finset.compl_eq_empty_iff _ |>.mp h)
  have hcut : ∀ S : Finset (Fin n), S.Nonempty →
      2 * graphVolume W S ≤ graphVolume W Finset.univ → h * graphVolume W S ≤ cutWeight W S := by
    intro S hS hvol
    have hSu : S ≠ Finset.univ := by
      rintro rfl
      linarith [hvolpos _ hS]
    have hle := cheegerConstant_le_cutWeight_div W hpos hS hSu
    have hs := hvolsplit S
    rw [min_eq_left (by linarith)] at hle
    exact (le_div_iff₀ (hvolpos S hS)).mp hle
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne (Fin n)
  have hS₀u : ({i₀} : Finset (Fin n)) ≠ Finset.univ :=
    fun h ↦ hi (mem_singleton.mp (h ▸ mem_univ i₁)).symm
  obtain ⟨f₀, hf₀0, hf₀1, -⟩ := exists_admissible_energy_le W hW hpos {i₀}
    (hvolpos _ (singleton_nonempty _)) (hvolpos _ (hcompl _ hS₀u))
  set Λ := {r | ∃ f : Fin n → ℝ, (∑ i, weightedDegree W i * f i) = 0 ∧
    (∑ i, weightedDegree W i * f i ^ 2) = 1 ∧ r = (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2}
  have hΛ : spectralGap W = sInf Λ := rfl
  have hne : Λ.Nonempty := ⟨_, f₀, hf₀0, hf₀1, rfl⟩
  have hbdd : BddBelow Λ := by
    refine ⟨0, ?_⟩
    rintro _ ⟨f, -, -, rfl⟩
    exact div_nonneg (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦
      mul_nonneg (hpos i j) (sq_nonneg _)) zero_le_two
  have hcore : ∀ r ∈ Λ, h ^ 2 ≤ 2 * r ∧ (1 ≤ r ∨ h ^ 2 ≤ r * (2 - r)) := by
    rintro _ ⟨f, hf0, hf1, rfl⟩
    exact cheeger_sq_le_of_admissible W hW hpos hn0 hdeg h hh0 hcut f hf0 hf1
  have hgap2 : h ^ 2 ≤ 2 * spectralGap W := by
    have : h ^ 2 / 2 ≤ sInf Λ := le_csInf hne fun r hr ↦ by linarith [(hcore r hr).1]
    rw [hΛ]; linarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_csInf ⟨_, {i₀}, singleton_nonempty _, hS₀u, rfl⟩ ?_
    rintro _ ⟨S, hS, hSu, rfl⟩
    obtain ⟨f, hf0, hf1, hfE⟩ := exists_admissible_energy_le W hW hpos S (hvolpos _ hS)
      (hvolpos _ (hcompl _ hSu))
    have : spectralGap W ≤ _ := csInf_le hbdd ⟨f, hf0, hf1, rfl⟩
    linarith
  · calc h = Real.sqrt (h ^ 2) := (Real.sqrt_sq hh0).symm
      _ ≤ Real.sqrt (2 * spectralGap W) := Real.sqrt_le_sqrt hgap2
  · rw [hΛ]
    refine le_csInf hne fun r hr ↦ ?_
    have hs0 := Real.sqrt_nonneg (1 - h ^ 2)
    rcases (hcore r hr).2 with h1 | h2
    · linarith
    · by_cases hr1 : r ≤ 1
      · have : 1 - r ≤ Real.sqrt (1 - h ^ 2) := by
          calc 1 - r = Real.sqrt ((1 - r) ^ 2) := (Real.sqrt_sq (by linarith)).symm
            _ ≤ Real.sqrt (1 - h ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        linarith
      · linarith

end Cheeger

end CKSD
