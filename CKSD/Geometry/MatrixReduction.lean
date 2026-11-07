module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The persistence pairing by matrix reduction

Simplices of a simplexwise filtration are indexed by `Fin m`, in filtration order, so the row and
column indices of the boundary matrix start at `0`. A column reduction is a factorization `R = D V`
with `V` invertible and upper triangular and `R` reduced (distinct nonzero columns have distinct
lowest nonzero rows). The pairing lemma identifies the lows of `R` through ranks of lower-left
submatrices of `D`; it holds for every square matrix over a field, in particular for boundary
matrices over `ℤ/2` and for signed boundary matrices over any field.

The lower-left submatrix of rows `a, a+1, …` and columns `0, …, b-1` is represented by masking
the remaining entries with zeros, which does not change the rank.

Source: GAPS 108.32.
-/

@[expose] public section

noncomputable section

open Matrix Module

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

/-- Row `i` carries the lowest nonzero entry of column `j`. -/
def IsColumnLow (R : Matrix (Fin m) (Fin m) 𝕜) (i j : Fin m) : Prop :=
  R i j ≠ 0 ∧ ∀ k, i < k → R k j = 0

/-- A matrix is reduced when distinct nonzero columns have distinct lows. -/
def IsReducedMatrix (R : Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  ∀ i j j', IsColumnLow R i j → IsColumnLow R i j' → j = j'

/-- `R = D V` is a column reduction of `D`: `V` is upper triangular with nonzero diagonal (hence
invertible) and `R` is reduced. -/
structure IsMatrixReduction (D R V : Matrix (Fin m) (Fin m) 𝕜) : Prop where
  /-- The factorization. -/
  eq_mul : R = D * V
  /-- `V` is upper triangular. -/
  upperTriangular : V.BlockTriangular id
  /-- The diagonal of `V` is nonzero. -/
  diag_ne_zero : ∀ i, V i i ≠ 0
  /-- `R` is reduced. -/
  reduced : IsReducedMatrix R

/-- The lower-left part of `D`: rows with index at least `a`, columns with index below `b`. -/
def lowerLeftPart (D : Matrix (Fin m) (Fin m) 𝕜) (a b : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun k l ↦ if a ≤ k.val ∧ l.val < b then D k l else 0

/-- Rank of the lower-left submatrix of rows `a, a+1, …` and columns `0, …, b-1`. -/
def lowerLeftRank (D : Matrix (Fin m) (Fin m) 𝕜) (a b : ℕ) : ℕ :=
  (lowerLeftPart D a b).rank

/-- A column has at most one low. -/
theorem IsColumnLow.unique {R : Matrix (Fin m) (Fin m) 𝕜} {i i' j : Fin m}
    (h : IsColumnLow R i j) (h' : IsColumnLow R i' j) : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (h.2 i' hlt) h'.1
  · exact heq
  · exact absurd (h'.2 i hgt) h.1

/-- A nonzero column has a low. -/
theorem exists_isColumnLow_of_ne_zero {R : Matrix (Fin m) (Fin m) 𝕜} {j : Fin m}
    (h : ∃ k, R k j ≠ 0) : ∃ i, IsColumnLow R i j := by
  classical
  obtain ⟨k, hk⟩ := h
  have hne : (Finset.univ.filter fun k ↦ R k j ≠ 0).Nonempty := ⟨k, by simpa using hk⟩
  refine ⟨(Finset.univ.filter fun k ↦ R k j ≠ 0).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro k hk'
    by_contra hne'
    have := Finset.le_max' (Finset.univ.filter fun k ↦ R k j ≠ 0) k
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩)
    exact absurd hk' (not_lt.mpr this)

/-- Masking is multiplication by diagonal projections on both sides. -/
theorem lowerLeftPart_eq_mul (D : Matrix (Fin m) (Fin m) 𝕜) (a b : ℕ) :
    lowerLeftPart D a b =
      diagonal (fun k : Fin m ↦ if a ≤ k.val then (1 : 𝕜) else 0) * D *
        diagonal (fun l : Fin m ↦ if l.val < b then (1 : 𝕜) else 0) := by
  ext k l
  simp only [lowerLeftPart, of_apply, mul_diagonal, diagonal_mul]
  by_cases ha : a ≤ k.val <;> by_cases hb : l.val < b <;> simp [ha, hb]

/-- Right multiplication by an upper triangular matrix does not raise lower-left ranks. -/
theorem lowerLeftRank_mul_le (A V : Matrix (Fin m) (Fin m) 𝕜) (hV : V.BlockTriangular id)
    (a b : ℕ) : lowerLeftRank (A * V) a b ≤ lowerLeftRank A a b := by
  set P := diagonal (fun k : Fin m ↦ if a ≤ k.val then (1 : 𝕜) else 0)
  set Q := diagonal (fun l : Fin m ↦ if l.val < b then (1 : 𝕜) else 0)
  have hVQ : V * Q = Q * V * Q := by
    ext k l
    simp only [Q, mul_diagonal, diagonal_mul]
    by_cases hl : l.val < b
    · by_cases hkl : V k l = 0
      · simp [hkl]
      · have hk : k ≤ l := by
          by_contra h
          exact hkl (hV (lt_of_not_ge h))
        have : k.val < b := lt_of_le_of_lt hk hl
        simp [hl, this]
    · simp [hl]
  have : lowerLeftPart (A * V) a b = lowerLeftPart A a b * (V * Q) := by
    rw [lowerLeftPart_eq_mul, lowerLeftPart_eq_mul]
    change P * (A * V) * Q = P * A * Q * (V * Q)
    calc P * (A * V) * Q = P * A * (V * Q) := by simp only [Matrix.mul_assoc]
      _ = P * A * (Q * V * Q) := by rw [hVQ]
      _ = P * A * Q * (V * Q) := by simp only [Matrix.mul_assoc]
  unfold lowerLeftRank
  rw [this]
  exact rank_mul_le_left _ _

/-- Lower-left ranks are invariant under a column reduction. -/
theorem lowerLeftRank_eq_of_isMatrixReduction {D R V : Matrix (Fin m) (Fin m) 𝕜}
    (h : IsMatrixReduction D R V) (a b : ℕ) : lowerLeftRank R a b = lowerLeftRank D a b := by
  have hdet : IsUnit V.det := by
    rw [det_of_isUpperTriangular h.upperTriangular]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ ↦ h.diag_ne_zero i).isUnit
  let _ := invertibleOfIsUnitDet V hdet
  have hinv : V⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular h.upperTriangular
  apply le_antisymm
  · rw [h.eq_mul]
    exact lowerLeftRank_mul_le D V h.upperTriangular a b
  · have hD : D = R * V⁻¹ := by
      rw [h.eq_mul, Matrix.mul_assoc, mul_nonsing_inv V hdet, Matrix.mul_one]
    conv_lhs => rw [hD]
    exact lowerLeftRank_mul_le R V⁻¹ hinv a b

/-- The rank of a reduced matrix is the number of its nonzero columns. -/
theorem rank_eq_card_of_isReducedMatrix [DecidableEq (Fin m)] {M : Matrix (Fin m) (Fin m) 𝕜}
    (hM : IsReducedMatrix M) :
    M.rank = Fintype.card {l : Fin m // ∃ i, IsColumnLow M i l} := by
  classical
  set S := {l : Fin m // ∃ i, IsColumnLow M i l}
  let low : S → Fin m := fun l ↦ l.2.choose
  have hlow : ∀ l : S, IsColumnLow M (low l) l.1 := fun l ↦ l.2.choose_spec
  let v : S → Fin m → 𝕜 := fun l ↦ Mᵀ l.1
  have hli : LinearIndependent 𝕜 v := by
    rw [linearIndependent_iff']
    intro s g hsum
    by_contra hcon
    push Not at hcon
    set T := s.filter fun l ↦ g l ≠ 0
    have hT : T.Nonempty := by
      obtain ⟨l, hl, hgl⟩ := hcon
      exact ⟨l, Finset.mem_filter.mpr ⟨hl, hgl⟩⟩
    obtain ⟨l₀, hl₀T, hmax⟩ := Finset.exists_max_image T low hT
    have hl₀ := Finset.mem_filter.mp hl₀T
    have hrow := congrFun hsum (low l₀)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v,
      transpose_apply] at hrow
    rw [Finset.sum_eq_single l₀] at hrow
    · exact mul_ne_zero hl₀.2 (hlow l₀).1 hrow
    · intro l hl hne
      by_cases hgl : g l = 0
      · simp [hgl]
      · have hle := hmax l (Finset.mem_filter.mpr ⟨hl, hgl⟩)
        have hne' : low l ≠ low l₀ := by
          intro heq
          apply hne
          apply Subtype.ext
          exact hM _ _ _ (hlow l) (heq ▸ hlow l₀)
        rw [(hlow l).2 _ (lt_of_le_of_ne hle hne'), mul_zero]
    · intro h
      exact absurd hl₀.1 h
  rw [rank_eq_finrank_span_cols]
  change finrank 𝕜 (Submodule.span 𝕜 (Set.range Mᵀ)) = _
  have hspan : Submodule.span 𝕜 (Set.range Mᵀ) = Submodule.span 𝕜 (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      by_cases hl : ∃ i, IsColumnLow M i l
      · exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
      · have : Mᵀ l = 0 := by
          ext k
          by_contra hk
          exact hl (exists_isColumnLow_of_ne_zero ⟨k, by simpa using hk⟩)
        rw [this]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact Submodule.subset_span ⟨l.1, rfl⟩
  rw [hspan, finrank_span_eq_card hli]

/-- Lows of the masked matrix are the lows of the original in the masked region. -/
theorem isColumnLow_lowerLeftPart_iff {R : Matrix (Fin m) (Fin m) 𝕜} {a b : ℕ} {i l : Fin m} :
    IsColumnLow (lowerLeftPart R a b) i l ↔ (l.val < b ∧ a ≤ i.val ∧ IsColumnLow R i l) := by
  simp only [IsColumnLow, lowerLeftPart, of_apply]
  constructor
  · rintro ⟨hne, hzero⟩
    have hab : a ≤ i.val ∧ l.val < b := by
      by_contra h
      exact hne (by simp [h])
    refine ⟨hab.2, hab.1, by simpa [hab] using hne, fun k hk ↦ ?_⟩
    have := hzero k hk
    have hak : a ≤ k.val := le_trans hab.1 (le_of_lt hk)
    simpa [hak, hab.2] using this
  · rintro ⟨hb, ha, hne, hzero⟩
    refine ⟨by simpa [ha, hb] using hne, fun k hk ↦ ?_⟩
    simp [hzero k hk]

/-- A masked reduced matrix is reduced. -/
theorem IsReducedMatrix.lowerLeftPart {R : Matrix (Fin m) (Fin m) 𝕜} (hR : IsReducedMatrix R)
    (a b : ℕ) : IsReducedMatrix (lowerLeftPart R a b) := by
  intro i j j' hj hj'
  rw [isColumnLow_lowerLeftPart_iff] at hj hj'
  exact hR i j j' hj.2.2 hj'.2.2

/-- Lower-left ranks of a reduced matrix count the columns with low in the region. -/
theorem lowerLeftRank_eq_card_of_isReducedMatrix {R : Matrix (Fin m) (Fin m) 𝕜}
    (hR : IsReducedMatrix R) (a b : ℕ) :
    lowerLeftRank R a b =
      (Finset.univ.filter fun l : Fin m ↦ l.val < b ∧ ∃ i, a ≤ i.val ∧ IsColumnLow R i l).card := by
  classical
  unfold lowerLeftRank
  rw [rank_eq_card_of_isReducedMatrix (hR.lowerLeftPart a b), Fintype.card_subtype]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isColumnLow_lowerLeftPart_iff]
  constructor
  · rintro ⟨i, hb, ha, hi⟩
    exact ⟨hb, i, ha, hi⟩
  · rintro ⟨hb, i, ha, hi⟩
    exact ⟨i, hb, ha, hi⟩

/-- The alternating rank combination of the pairing lemma, in the `0`-based indexing of
`Fin m`: with `D^i_j` the submatrix of rows `i, …, m-1` and columns `0, …, j`, it is
`rank D^i_j - rank D^{i+1}_j + rank D^{i+1}_{j-1} - rank D^i_{j-1}`. -/
def pairingRankCombination (D : Matrix (Fin m) (Fin m) 𝕜) (i j : Fin m) : ℤ :=
  (lowerLeftRank D i.val (j.val + 1) : ℤ) - lowerLeftRank D (i.val + 1) (j.val + 1) +
    lowerLeftRank D (i.val + 1) j.val - lowerLeftRank D i.val j.val

/-- GAPS 108.32, the pairing lemma: for every column reduction `R = D V` of a square matrix over a
field, row `i` is the low of column `j` of `R` exactly when the alternating combination of ranks
of lower-left submatrices of `D` equals `1`. In particular the pairing does not depend on the
reduction (`isColumnLow_iff_of_isMatrixReduction`). The statement holds for every square matrix,
so it covers boundary matrices over `ℤ/2` and signed boundary matrices over any field. Indices
start at `0`; the homological reading of the pairs is
`persistentBettiOfMatrix_eq_card_bars`. -/
theorem isColumnLow_iff_pairingRankCombination_eq_one {D R V : Matrix (Fin m) (Fin m) 𝕜}
    (h : IsMatrixReduction D R V) (i j : Fin m) :
    IsColumnLow R i j ↔ pairingRankCombination D i j = 1 := by
  classical
  unfold pairingRankCombination
  simp only [← lowerLeftRank_eq_of_isMatrixReduction h,
    lowerLeftRank_eq_card_of_isReducedMatrix h.reduced, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · have hj1 : j.val < j.val + 1 := Nat.lt_succ_self _
    simp only [hj1, true_and, lt_irrefl, false_and]
    by_cases hlow : IsColumnLow R i j
    · have h1' : ∃ i', i ≤ i' ∧ IsColumnLow R i' j := ⟨i, le_rfl, hlow⟩
      have h2 : ¬ ∃ i', i < i' ∧ IsColumnLow R i' j := by
        rintro ⟨i', hi', hl'⟩
        have := hlow.unique hl'
        subst this
        exact lt_irrefl _ hi'
      simp only [Fin.val_fin_le, Nat.succ_le_iff, Fin.val_fin_lt]
      simp only [h1', h2, ↓reduceIte]
      simp [hlow]
    · have hiff : (∃ i', i ≤ i' ∧ IsColumnLow R i' j) ↔
          ∃ i', i < i' ∧ IsColumnLow R i' j := by
        constructor
        · rintro ⟨i', hi', hl'⟩
          refine ⟨i', ?_, hl'⟩
          rcases lt_or_eq_of_le hi' with hlt | heq
          · exact hlt
          · exact absurd (heq ▸ hl') hlow
        · rintro ⟨i', hi', hl'⟩
          exact ⟨i', hi'.le, hl'⟩
      simp only [Fin.val_fin_le, Nat.succ_le_iff, Fin.val_fin_lt]
      by_cases h1 : ∃ i', i ≤ i' ∧ IsColumnLow R i' j
      · simp only [h1, hiff.mp h1, ↓reduceIte]
        simp [hlow]
      · simp only [h1, (not_congr hiff).mp h1, ↓reduceIte]
        simp [hlow]
  · intro l _ hne
    have hlj : l.val ≠ j.val := fun h ↦ hne (Fin.ext h)
    by_cases hlt : l.val < j.val
    · have : l.val < j.val + 1 := by omega
      simp [hlt, this]
    · have h1 : ¬ l.val < j.val + 1 := by omega
      simp [hlt, h1]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- GAPS 108.32: the pairing is independent of the chosen reduction. -/
theorem isColumnLow_iff_of_isMatrixReduction {D R V R' V' : Matrix (Fin m) (Fin m) 𝕜}
    (h : IsMatrixReduction D R V) (h' : IsMatrixReduction D R' V') (i j : Fin m) :
    IsColumnLow R i j ↔ IsColumnLow R' i j := by
  rw [isColumnLow_iff_pairingRankCombination_eq_one h,
    isColumnLow_iff_pairingRankCombination_eq_one h']

/-- `D` is the boundary matrix of a simplexwise filtration whose `k`th simplex has dimension
`dim k`: nonzero entries pair a face with a simplex of one dimension more that comes later in the
filtration, and `D * D = 0`. Over `ℤ/2` this is the incidence matrix of codimension-one faces;
over another field the entries are the signed incidence numbers. -/
structure IsFilteredBoundaryMatrix (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) : Prop where
  /-- The boundary of a boundary vanishes. -/
  mul_self_eq_zero : D * D = 0
  /-- Nonzero entries record codimension-one faces that precede the simplex. -/
  lt_and_dim_of_ne_zero : ∀ i j, D i j ≠ 0 → i < j ∧ dim i + 1 = dim j

/-- Chains of dimension `p` of the subcomplex formed by the first `a` simplices. -/
def filteredChains (dim : Fin m → ℕ) (p a : ℕ) : Submodule 𝕜 (Fin m → 𝕜) where
  carrier := {c | ∀ k, c k ≠ 0 → k.val < a ∧ dim k = p}
  zero_mem' := by simp
  add_mem' := by
    intro c c' hc hc' k hk
    by_cases h : c k = 0
    · exact hc' k (by simpa [h] using hk)
    · exact hc k h
  smul_mem' := by
    intro r c hc k hk
    exact hc k (right_ne_zero_of_mul (by simpa using hk))

/-- Cycles of dimension `p` of the subcomplex formed by the first `a` simplices. -/
def filteredCycles (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (p a : ℕ) :
    Submodule 𝕜 (Fin m → 𝕜) :=
  filteredChains dim p a ⊓ LinearMap.ker D.mulVecLin

/-- Boundaries of dimension `p` of the subcomplex formed by the first `b` simplices. -/
def filteredBoundaries (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (p b : ℕ) :
    Submodule 𝕜 (Fin m → 𝕜) :=
  (filteredChains dim (p + 1) b).map D.mulVecLin

/-- Persistent Betti number of the simplexwise filtration: the rank of the map in degree-`p`
homology induced by the inclusion of the first `a` simplices into the first `b`, computed as
`dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))`. -/
def persistentBettiOfMatrix (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (p a b : ℕ) : ℕ :=
  finrank 𝕜 (filteredCycles D dim p a) -
    finrank 𝕜 ↥(filteredCycles D dim p a ⊓ filteredBoundaries D dim p b)

/-- GAPS 108.32, homological meaning of the pairing (indices from `0`; the subcomplex `K_a`
consists of the first `a` simplices). If `low_R(j) = i`, then `σ_j` has dimension one more than
`σ_i`, adding `σ_i` raises the Betti number in its dimension (`σ_i` is positive) and adding `σ_j`
lowers the Betti number one dimension below its own (`σ_j` is negative). The bars are the pairs
`[i, j)` with `low_R(j) = i` and the essential intervals `[j, ∞)` for zero columns `j` that are
the low of no column: for `a ≤ b` the persistent Betti number in degree `p` counts exactly the
bars of degree `p` that contain `[a - 1, b - 1]`, that is, born at an index below `a` and dying at
an index of at least `b`. The restatement for monotone functions on simplices, with bars
`[f(σ_i), f(σ_j))`, is a relabelling and is not stated separately. -/
theorem persistentBettiOfMatrix_eq_card_bars {D R V : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (h : IsMatrixReduction D R V) :
    (∀ i j, IsColumnLow R i j →
      dim j = dim i + 1 ∧
      persistentBettiOfMatrix D dim (dim i) (i.val + 1) (i.val + 1) =
        persistentBettiOfMatrix D dim (dim i) i.val i.val + 1 ∧
      persistentBettiOfMatrix D dim (dim i) (j.val + 1) (j.val + 1) + 1 =
        persistentBettiOfMatrix D dim (dim i) j.val j.val) ∧
    ∀ p a b, a ≤ b →
      persistentBettiOfMatrix D dim p a b =
        (Finset.univ.filter fun j : Fin m ↦
          ∃ i, IsColumnLow R i j ∧ dim i = p ∧ i.val < a ∧ b ≤ j.val).card +
        (Finset.univ.filter fun j : Fin m ↦
          (∀ k, R k j = 0) ∧ (∀ l, ¬ IsColumnLow R j l) ∧ dim j = p ∧ j.val < a).card := by
  sorry

end CKSD
