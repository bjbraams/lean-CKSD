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

For a filtered boundary matrix, keeping the columns of one dimension of a reduction gives a
reduction of the corresponding part of `D`; this yields the dimension relation of paired simplices
and per-dimension rank counts. The columns of `V` at the zero columns of `R` span the kernel of
`D`, so a row that is a low indexes a zero column. Rank–nullity then expresses the persistent Betti
numbers through the pairs.

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

/-- The pairing combination of ranks is the indicator of the lows of any column reduction. -/
theorem pairingRankCombination_eq_ite {D R V : Matrix (Fin m) (Fin m) 𝕜}
    (h : IsMatrixReduction D R V) (i j : Fin m) :
    pairingRankCombination D i j = if IsColumnLow R i j then 1 else 0 := by
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
  rw [pairingRankCombination_eq_ite h]
  split_ifs with hlow <;> simp [hlow]

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

/-- Matrices with disjoint row supports and disjoint column supports have additive rank. -/
theorem rank_add_of_disjoint_supports {A B : Matrix (Fin m) (Fin m) 𝕜}
    (hcol : ∀ k l, A k l ≠ 0 → ∀ k', B k' l = 0) (hrow : ∀ k l, A k l ≠ 0 → ∀ l', B k l' = 0) :
    (A + B).rank = A.rank + B.rank := by
  classical
  set PA : Matrix (Fin m) (Fin m) 𝕜 := diagonal fun l ↦ if ∃ k, A k l ≠ 0 then 1 else 0
  set PB : Matrix (Fin m) (Fin m) 𝕜 := diagonal fun l ↦ if ∃ k, A k l ≠ 0 then 0 else 1
  have hA : A = (A + B) * PA := by
    ext k l
    simp only [PA, mul_diagonal]
    by_cases hl : ∃ k, A k l ≠ 0
    · obtain ⟨k₀, hk₀⟩ := hl
      simp [show ∃ k, A k l ≠ 0 from ⟨k₀, hk₀⟩, hcol k₀ l hk₀ k]
    · push Not at hl
      simp [hl]
  have hB : B = (A + B) * PB := by
    ext k l
    simp only [PB, mul_diagonal]
    by_cases hl : ∃ k, A k l ≠ 0
    · obtain ⟨k₀, hk₀⟩ := hl
      simp [show ∃ k, A k l ≠ 0 from ⟨k₀, hk₀⟩, hcol k₀ l hk₀ k]
    · push Not at hl
      simp [hl]
  have hle : ∀ N : Matrix (Fin m) (Fin m) 𝕜, LinearMap.range ((A + B) * N).mulVecLin ≤
      LinearMap.range (A + B).mulVecLin := by
    intro N
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hsup : LinearMap.range (A + B).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    apply le_antisymm
    · rw [Matrix.mulVecLin_add]
      exact LinearMap.range_add_le _ _
    · have h1 := hle PA
      have h2 := hle PB
      rw [← hA] at h1
      rw [← hB] at h2
      exact sup_le h1 h2
  have hinf : LinearMap.range A.mulVecLin ⊓ LinearMap.range B.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    rw [Submodule.mem_bot]
    ext k
    simp only [Matrix.mulVecLin_apply, Pi.zero_apply] at hy ⊢
    by_cases hk : ∃ l, A k l ≠ 0
    · obtain ⟨l, hl⟩ := hk
      rw [← hy]
      simp [mulVec, dotProduct, hrow k l hl]
    · push Not at hk
      simp [mulVec, dotProduct, hk]
  unfold Matrix.rank
  rw [hsup, ← Submodule.finrank_sup_add_finrank_inf_eq, hinf, finrank_bot, add_zero]

/-- The part of `D` in the columns of dimension `q`. -/
def dimColumnPart (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (q : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun k l ↦ if dim l = q then D k l else 0

/-- The part of `D` in the columns of dimension other than `q`. -/
def dimColumnPartCompl (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (q : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun k l ↦ if dim l = q then 0 else D k l

/-- Lower-left ranks split along column dimensions for a matrix whose nonzero entries raise
the dimension by one. -/
theorem lowerLeftRank_eq_add_dimColumnPart {D : Matrix (Fin m) (Fin m) 𝕜} {dim : Fin m → ℕ}
    (hD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j) (q a b : ℕ) :
    lowerLeftRank D a b =
      lowerLeftRank (dimColumnPart D dim q) a b + lowerLeftRank (dimColumnPartCompl D dim q) a b := by
  unfold lowerLeftRank
  have hsum : lowerLeftPart D a b = lowerLeftPart (dimColumnPart D dim q) a b +
      lowerLeftPart (dimColumnPartCompl D dim q) a b := by
    ext k l
    simp only [lowerLeftPart, dimColumnPart, dimColumnPartCompl, of_apply]
    by_cases h1 : a ≤ k.val ∧ l.val < b <;> by_cases h2 : dim l = q <;> simp [h1, h2]
  rw [hsum]
  apply rank_add_of_disjoint_supports
  · intro k l hkl k'
    simp only [lowerLeftPart, dimColumnPart, dimColumnPartCompl, of_apply] at hkl ⊢
    split_ifs at hkl ⊢ <;> simp_all
  · intro k l hkl l'
    simp only [lowerLeftPart, dimColumnPart, dimColumnPartCompl, of_apply] at hkl ⊢
    split_ifs at hkl ⊢ with h1 h2 h3 h4 h5 <;> simp_all
    by_contra hne
    have e1 := hD k l (by simpa [h2] using hkl)
    have e2 := hD k l' hne
    omega

/-- Adding a zero column does not change lower-left ranks. -/
theorem lowerLeftRank_succ_of_col_eq_zero {M : Matrix (Fin m) (Fin m) 𝕜} {l : Fin m}
    (hl : ∀ k, M k l = 0) (a : ℕ) : lowerLeftRank M a (l.val + 1) = lowerLeftRank M a l.val := by
  unfold lowerLeftRank
  congr 1
  ext k l'
  simp only [lowerLeftPart, of_apply]
  by_cases h : l' = l
  · subst h; simp [hl]
  · have : l'.val < l.val + 1 ↔ l'.val < l.val := by
      have : l'.val ≠ l.val := fun e ↦ h (Fin.ext e)
      omega
    simp only [this]

/-- Adding a zero row does not change lower-left ranks. -/
theorem lowerLeftRank_of_row_eq_zero {M : Matrix (Fin m) (Fin m) 𝕜} {k : Fin m}
    (hk : ∀ l, M k l = 0) (b : ℕ) : lowerLeftRank M k.val b = lowerLeftRank M (k.val + 1) b := by
  unfold lowerLeftRank
  congr 1
  ext k' l
  simp only [lowerLeftPart, of_apply]
  by_cases h : k' = k
  · subst h; simp [hk]
  · have : k.val ≤ k'.val ↔ k.val + 1 ≤ k'.val := by
      have : k'.val ≠ k.val := fun e ↦ h (Fin.ext e)
      omega
    simp only [this]

/-- The pairing combination vanishes at a zero column. -/
theorem pairingRankCombination_eq_zero_of_col {M : Matrix (Fin m) (Fin m) 𝕜} {i l : Fin m}
    (hl : ∀ k, M k l = 0) : pairingRankCombination M i l = 0 := by
  unfold pairingRankCombination
  rw [lowerLeftRank_succ_of_col_eq_zero hl, lowerLeftRank_succ_of_col_eq_zero hl]
  ring

/-- The pairing combination vanishes at a zero row. -/
theorem pairingRankCombination_eq_zero_of_row {M : Matrix (Fin m) (Fin m) 𝕜} {i l : Fin m}
    (hi : ∀ k, M i k = 0) : pairingRankCombination M i l = 0 := by
  unfold pairingRankCombination
  rw [lowerLeftRank_of_row_eq_zero hi, lowerLeftRank_of_row_eq_zero hi]
  ring

/-- In a column reduction of a matrix whose nonzero entries raise the dimension by one, the low
of column `j` has dimension one less than `j`. -/
theorem IsColumnLow.dim_eq {D R V : Matrix (Fin m) (Fin m) 𝕜} {dim : Fin m → ℕ}
    (hD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j) (h : IsMatrixReduction D R V) {i j : Fin m}
    (hij : IsColumnLow R i j) : dim j = dim i + 1 := by
  have h1 : pairingRankCombination D i j = 1 := by
    simp [pairingRankCombination_eq_ite h, hij]
  have hsplit : pairingRankCombination D i j =
      pairingRankCombination (dimColumnPart D dim (dim j)) i j +
        pairingRankCombination (dimColumnPartCompl D dim (dim j)) i j := by
    unfold pairingRankCombination
    simp only [lowerLeftRank_eq_add_dimColumnPart hD (dim j)]
    push_cast
    ring
  have h0 : pairingRankCombination (dimColumnPartCompl D dim (dim j)) i j = 0 :=
    pairingRankCombination_eq_zero_of_col fun k ↦ by simp [dimColumnPartCompl]
  rw [h0, add_zero] at hsplit
  by_contra hne
  have hrow : ∀ k, dimColumnPart D dim (dim j) i k = 0 := by
    intro k
    simp only [dimColumnPart, of_apply]
    split_ifs with hk
    · by_contra hD0
      exact hne ((hD i k hD0).trans hk).symm
    · rfl
  rw [pairingRankCombination_eq_zero_of_row hrow] at hsplit
  omega

/-- In a column reduction of a strictly upper triangular matrix, the low of a column lies
strictly above the diagonal. -/
theorem IsColumnLow.lt {D R V : Matrix (Fin m) (Fin m) 𝕜}
    (hD : ∀ i j, D i j ≠ 0 → i < j) (h : IsMatrixReduction D R V) {i j : Fin m}
    (hij : IsColumnLow R i j) : i < j := by
  have hne := hij.1
  rw [h.eq_mul, Matrix.mul_apply] at hne
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h1 := hD i k (left_ne_zero_of_mul hk)
  have h2 : k ≤ j := by
    by_contra hkj
    exact right_ne_zero_of_mul hk (h.upperTriangular (lt_of_not_ge hkj))
  exact lt_of_lt_of_le h1 h2

/-- The matrix obtained from a column reduction `R` by keeping the columns of dimension `q` and,
in them, the rows of dimension `q - 1`. -/
def dimReducedPart (R : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (q : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun k l ↦ if dim l = q ∧ dim k + 1 = q then R k l else 0

/-- The transformation matrix of `dimReducedPart`: the columns of `V` of dimension `q`, and
standard basis vectors in the other columns. -/
def dimTransformPart (V : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ) (q : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun k l ↦ if dim l = q then V k l else if k = l then 1 else 0

/-- Lows of the restricted reduction are the lows of `R` in columns of dimension `q`. -/
theorem isColumnLow_dimReducedPart_iff {D R V : Matrix (Fin m) (Fin m) 𝕜} {dim : Fin m → ℕ}
    (hD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j) (h : IsMatrixReduction D R V) (q : ℕ)
    (i l : Fin m) : IsColumnLow (dimReducedPart R dim q) i l ↔ dim l = q ∧ IsColumnLow R i l := by
  constructor
  · rintro ⟨hne, hzero⟩
    simp only [dimReducedPart, of_apply] at hne hzero
    have hc : dim l = q ∧ dim i + 1 = q := by
      by_contra hc
      exact hne (ite_eq_right hc)
    rw [ite_eq_left hc] at hne
    refine ⟨hc.1, hne, fun k hk ↦ ?_⟩
    obtain ⟨i', hi'⟩ := exists_isColumnLow_of_ne_zero ⟨i, hne⟩
    have hdim := hi'.dim_eq hD h
    have hii' : i ≤ i' := by
      by_contra hlt
      exact hne (hi'.2 i (lt_of_not_ge hlt))
    have hi'i : i' ≤ i := by
      by_contra hlt
      have := hzero i' (lt_of_not_ge hlt)
      rw [ite_eq_left ⟨hc.1, by omega⟩] at this
      exact hi'.1 this
    have : i = i' := le_antisymm hii' hi'i
    subst this
    exact hi'.2 k hk
  · rintro ⟨hq, hlow⟩
    have hdim := hlow.dim_eq hD h
    refine ⟨?_, fun k hk ↦ ?_⟩
    · simp only [dimReducedPart, of_apply]
      rw [ite_eq_left ⟨hq, by omega⟩]
      exact hlow.1
    · simp only [dimReducedPart, of_apply]
      split_ifs
      · exact hlow.2 k hk
      · rfl

/-- Keeping the columns of dimension `q` of a column reduction gives a column reduction of the
part of `D` in the columns of dimension `q`. -/
theorem isMatrixReduction_dimColumnPart {D R V : Matrix (Fin m) (Fin m) 𝕜} {dim : Fin m → ℕ}
    (hD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j) (h : IsMatrixReduction D R V) (q : ℕ) :
    IsMatrixReduction (dimColumnPart D dim q) (dimReducedPart R dim q)
      (dimTransformPart V dim q) where
  eq_mul := by
    ext k l
    simp only [dimReducedPart, dimColumnPart, dimTransformPart, of_apply, Matrix.mul_apply]
    by_cases hl : dim l = q
    · simp only [hl, true_and, ite_true]
      rw [h.eq_mul, Matrix.mul_apply]
      split_ifs with hk
      · refine Finset.sum_congr rfl fun k' _ ↦ ?_
        by_cases hD0 : D k k' = 0
        · simp [hD0]
        · rw [ite_eq_left ((hD k k' hD0).symm.trans hk)]
      · symm
        refine Finset.sum_eq_zero fun k' _ ↦ ?_
        by_cases hD0 : D k k' = 0
        · simp [hD0]
        · rw [ite_eq_right fun h' ↦ hk ((hD k k' hD0).trans h')]
          simp
    · simp only [hl, false_and, ite_false]
      symm
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      by_cases hk' : k' = l
      · subst hk'; simp [hl]
      · simp [hk']
  upperTriangular := by
    intro k l hlk
    simp only [dimTransformPart, of_apply]
    split_ifs with h1 h2
    · exact h.upperTriangular hlk
    · exact absurd (h2 ▸ hlk) (lt_irrefl _)
    · rfl
  diag_ne_zero := by
    intro k
    simp only [dimTransformPart, of_apply]
    split_ifs
    · exact h.diag_ne_zero k
    · exact one_ne_zero
  reduced := by
    intro i j j' hj hj'
    rw [isColumnLow_dimReducedPart_iff hD h] at hj hj'
    exact h.reduced i j j' hj.2 hj'.2

/-- Lower-left ranks of the part of `D` in the columns of dimension `q` count the columns of
dimension `q` whose low lies in the region. -/
theorem lowerLeftRank_dimColumnPart_eq_card {D R V : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j) (h : IsMatrixReduction D R V)
    (q a b : ℕ) :
    lowerLeftRank (dimColumnPart D dim q) a b =
      (Finset.univ.filter fun l : Fin m ↦
        l.val < b ∧ dim l = q ∧ ∃ i, a ≤ i.val ∧ IsColumnLow R i l).card := by
  have h' := isMatrixReduction_dimColumnPart hD h q
  rw [← lowerLeftRank_eq_of_isMatrixReduction h', lowerLeftRank_eq_card_of_isReducedMatrix
    h'.reduced]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isColumnLow_dimReducedPart_iff hD h]
  constructor
  · rintro ⟨hb, i, ha, hq, hi⟩
    exact ⟨hb, hq, i, ha, hi⟩
  · rintro ⟨hb, hq, i, ha, hi⟩
    exact ⟨hb, i, ha, hq, hi⟩

/-- A row that is the low of some column of a column reduction of `D`, with `D * D = 0`, indexes
a zero column: positive simplices have zero reduced columns. -/
theorem IsColumnLow.col_eq_zero {D R V : Matrix (Fin m) (Fin m) 𝕜} (hDD : D * D = 0)
    (h : IsMatrixReduction D R V) {i l : Fin m} (hil : IsColumnLow R i l) : ∀ k, R k i = 0 := by
  classical
  set Z := {j : Fin m // ∀ k, R k j = 0}
  let v : Z → Fin m → 𝕜 := fun j ↦ fun k ↦ V k j.1
  have hdet : V.det ≠ 0 := by
    rw [det_of_isUpperTriangular h.upperTriangular]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ h.diag_ne_zero i
  have hli : LinearIndependent 𝕜 v :=
    (linearIndependent_cols_of_det_ne_zero hdet).comp (fun j : Z ↦ j.1) Subtype.val_injective
  have hcolR : ∀ j, D *ᵥ (fun k ↦ V k j) = fun k ↦ R k j := by
    intro j
    ext k
    rw [h.eq_mul]
    simp [mulVec, dotProduct, Matrix.mul_apply]
  have hle : Submodule.span 𝕜 (Set.range v) ≤ LinearMap.ker D.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, v, hcolR]
    ext k
    exact j.2 k
  -- the kernel of `D` has dimension the number of zero columns of `R`
  have hrank : D.rank = Fintype.card {l : Fin m // ∃ i, IsColumnLow R i l} := by
    have h0 := lowerLeftRank_eq_of_isMatrixReduction h 0 m
    have hfull : ∀ M : Matrix (Fin m) (Fin m) 𝕜, lowerLeftPart M 0 m = M := by
      intro M; ext k l; simp [lowerLeftPart]
    unfold lowerLeftRank at h0
    rw [hfull, hfull] at h0
    rw [← h0, rank_eq_card_of_isReducedMatrix h.reduced]
  have hcardZ : Fintype.card Z + Fintype.card {l : Fin m // ∃ i, IsColumnLow R i l} = m := by
    have hiff : ∀ l : Fin m, (∀ k, R k l = 0) ↔ ¬ ∃ i, IsColumnLow R i l := by
      intro l
      constructor
      · rintro hz ⟨i, hi⟩
        exact hi.1 (hz i)
      · intro hn k
        by_contra hk
        exact hn (exists_isColumnLow_of_ne_zero ⟨k, hk⟩)
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_of_disjoint]
    · rw [show (Finset.univ.filter fun l : Fin m ↦ ∀ k, R k l = 0) ∪
          Finset.univ.filter (fun l : Fin m ↦ ∃ i, IsColumnLow R i l) = Finset.univ by
        ext l; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          hiff]; tauto]
      simp
    · rw [Finset.disjoint_filter]
      intro l _ hz
      exact (hiff l).mp hz
  have hker : finrank 𝕜 (LinearMap.ker D.mulVecLin) = Fintype.card Z := by
    have := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  have heq : Submodule.span 𝕜 (Set.range v) = LinearMap.ker D.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli, hker])
  have hRl : (fun k ↦ R k l) ∈ LinearMap.ker D.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hcolR, mulVec_mulVec, hDD, zero_mulVec]
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hRl
  obtain ⟨c, hc⟩ := hRl
  have hentry : ∀ k, R k l = ∑ j : Z, c j * V k j.1 := by
    intro k
    have := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
    exact this.symm
  set T := Finset.univ.filter fun j : Z ↦ c j ≠ 0
  have hT : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hT
    apply hil.1
    rw [hentry]
    exact Finset.sum_eq_zero fun j _ ↦ by
      have : c j = 0 := by simpa using hT (Finset.mem_univ j)
      simp [this]
  obtain ⟨j₀, hj₀T, hmax⟩ := Finset.exists_max_image T (fun j : Z ↦ j.1) hT
  have hj₀ : c j₀ ≠ 0 := (Finset.mem_filter.mp hj₀T).2
  have hlow : IsColumnLow R j₀.1 l := by
    constructor
    · rw [hentry, Finset.sum_eq_single j₀]
      · exact mul_ne_zero hj₀ (h.diag_ne_zero _)
      · intro j _ hne
        by_cases hcj : c j = 0
        · simp [hcj]
        · have hle' := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)
          have hlt : j.1 < j₀.1 := lt_of_le_of_ne hle' fun e ↦ hne (Subtype.ext e)
          rw [h.upperTriangular hlt, mul_zero]
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro k hk
      rw [hentry]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hcj : c j = 0
      · simp [hcj]
      · have hle' := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)
        rw [h.upperTriangular (lt_of_le_of_lt hle' hk), mul_zero]
  have : i = j₀.1 := hil.unique hlow
  rw [this]
  exact j₀.2

/-- Rank–nullity for the restriction of a linear map to a subspace. -/
theorem finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] [AddCommGroup W] [Module 𝕜 W] (f : V →ₗ[𝕜] W) (p : Submodule 𝕜 V) :
    finrank 𝕜 (p.map f) + finrank 𝕜 ↥(p ⊓ LinearMap.ker f) = finrank 𝕜 p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : finrank 𝕜 ((LinearMap.ker f).comap p.subtype) = finrank 𝕜 ↥(p ⊓ LinearMap.ker f) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective _ p.injective_subtype _).finrank_eq
  rw [he] at h
  exact h

/-- Chains of the subcomplex are the range of a diagonal projection. -/
theorem filteredChains_eq_range (dim : Fin m → ℕ) (p a : ℕ) :
    filteredChains (𝕜 := 𝕜) dim p a = LinearMap.range
      (diagonal fun k : Fin m ↦ if k.val < a ∧ dim k = p then (1 : 𝕜) else 0).mulVecLin := by
  ext c
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · intro hc
    refine ⟨c, ?_⟩
    ext k
    simp only [mulVec_diagonal]
    by_cases hk : c k = 0
    · simp [hk]
    · simp [(hc k hk).1, (hc k hk).2]
  · rintro ⟨x, rfl⟩ k hk
    simp only [mulVec_diagonal] at hk
    by_contra hcon
    exact hk (by simp [hcon])

/-- The dimension of the chains of the subcomplex. -/
theorem finrank_filteredChains (dim : Fin m → ℕ) (p a : ℕ) :
    finrank 𝕜 (filteredChains (𝕜 := 𝕜) dim p a) =
      (Finset.univ.filter fun k : Fin m ↦ k.val < a ∧ dim k = p).card := by
  classical
  rw [filteredChains_eq_range, ← Matrix.rank, rank_diagonal, Fintype.card_subtype]
  congr 1
  ext k
  simp

/-- The boundary of the chains of the subcomplex is the range of a masked part of `D`. -/
theorem map_filteredChains_eq_range (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ)
    (p a : ℕ) :
    (filteredChains (𝕜 := 𝕜) dim p a).map D.mulVecLin =
      LinearMap.range (lowerLeftPart (dimColumnPart D dim p) 0 a).mulVecLin := by
  rw [filteredChains_eq_range, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
  congr 2
  ext k l
  simp only [mul_diagonal, lowerLeftPart, dimColumnPart, of_apply, zero_le, true_and]
  by_cases h1 : l.val < a <;> by_cases h2 : dim l = p <;> simp [h1, h2]

/-- Dimension of the cycles of the subcomplex formed by the first `a` simplices. -/
theorem finrank_filteredCycles_add (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ)
    (p a : ℕ) :
    finrank 𝕜 (filteredCycles D dim p a) + lowerLeftRank (dimColumnPart D dim p) 0 a =
      (Finset.univ.filter fun k : Fin m ↦ k.val < a ∧ dim k = p).card := by
  have h := finrank_map_add_finrank_inf_ker D.mulVecLin (filteredChains (𝕜 := 𝕜) dim p a)
  rw [map_filteredChains_eq_range] at h
  have h2 : filteredCycles D dim p a = filteredChains dim p a ⊓ LinearMap.ker D.mulVecLin := rfl
  rw [← finrank_filteredChains (𝕜 := 𝕜), h2]
  unfold lowerLeftRank Matrix.rank
  omega

/-- Dimension of the cycles of `K_a` that bound in `K_b`. -/
theorem finrank_filteredCycles_inf_filteredBoundaries_add {D : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (p a b : ℕ) :
    finrank 𝕜 ↥(filteredCycles D dim p a ⊓ filteredBoundaries D dim p b) +
        lowerLeftRank (dimColumnPart D dim (p + 1)) a b =
      lowerLeftRank (dimColumnPart D dim (p + 1)) 0 b := by
  classical
  set Pa : Matrix (Fin m) (Fin m) 𝕜 := diagonal fun k ↦ if a ≤ k.val then 1 else 0
  set B := filteredBoundaries D dim p b
  have hB : B = LinearMap.range (lowerLeftPart (dimColumnPart D dim (p + 1)) 0 b).mulVecLin :=
    map_filteredChains_eq_range D dim (p + 1) b
  have hinf : filteredCycles D dim p a ⊓ B = B ⊓ LinearMap.ker Pa.mulVecLin := by
    ext v
    simp only [filteredCycles, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨⟨hc, -⟩, hvB⟩
      refine ⟨hvB, ?_⟩
      ext k
      simp only [Pa, mulVec_diagonal, Pi.zero_apply]
      by_cases hk : v k = 0
      · simp [hk]
      · have := (hc k hk).1
        simp [show ¬ a ≤ k.val by omega]
    · rintro ⟨hvB, hPa⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hvB
      refine ⟨⟨fun k hk ↦ ?_, ?_⟩, hvB⟩
      · simp only [Matrix.mulVecLin_apply, mulVec, dotProduct] at hk
        obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
        have hcl := hc l (right_ne_zero_of_mul hl)
        have hdim := (hD.lt_and_dim_of_ne_zero k l (left_ne_zero_of_mul hl)).2
        refine ⟨?_, by omega⟩
        by_contra hka
        have := congrFun hPa k
        simp only [Pa, mulVec_diagonal, Pi.zero_apply, Matrix.mulVecLin_apply] at this
        rw [ite_eq_left (by omega), one_mul] at this
        exact hk this
      · simp only [Matrix.mulVecLin_apply, mulVec_mulVec,
          hD.mul_self_eq_zero, zero_mulVec]
  have h := finrank_map_add_finrank_inf_ker Pa.mulVecLin B
  rw [← hinf] at h
  have hmap : B.map Pa.mulVecLin =
      LinearMap.range (lowerLeftPart (dimColumnPart D dim (p + 1)) a b).mulVecLin := by
    rw [hB, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
    congr 2
    ext k l
    simp only [Pa, diagonal_mul, lowerLeftPart, dimColumnPart, of_apply, zero_le, true_and]
    by_cases h1 : a ≤ k.val <;> simp [h1]
  have hfB : finrank 𝕜 B = (lowerLeftPart (dimColumnPart D dim (p + 1)) 0 b).rank := by
    rw [hB]; rfl
  rw [hmap, ← Matrix.rank] at h
  unfold lowerLeftRank
  omega

/-- Counting a disjoint union of two filters. -/
theorem card_filter_eq_add_of_iff {α : Type*} [Fintype α] {P Q S : α → Prop}
    [DecidablePred P] [DecidablePred Q] [DecidablePred S] (hiff : ∀ x, P x ↔ Q x ∨ S x) (hdisj : ∀ x, Q x → ¬ S x) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card + (Finset.univ.filter S).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp [hiff]
  · rw [Finset.disjoint_filter]
    exact fun x _ ↦ hdisj x

/-- A statement about the low of a column can be read off at any low of that column. -/
theorem IsColumnLow.exists_and_iff {R : Matrix (Fin m) (Fin m) 𝕜} {i l : Fin m}
    (hi : IsColumnLow R i l) {P : Fin m → Prop} : (∃ i', IsColumnLow R i' l ∧ P i') ↔ P i := by
  constructor
  · rintro ⟨i', hi', hP⟩
    exact hi.unique hi' ▸ hP
  · exact fun hP ↦ ⟨i, hi, hP⟩

/-- A column has a low exactly when it is nonzero. -/
theorem exists_isColumnLow_iff {R : Matrix (Fin m) (Fin m) 𝕜} {l : Fin m} :
    (∃ i, IsColumnLow R i l) ↔ ¬ ∀ k, R k l = 0 := by
  constructor
  · rintro ⟨i, hi⟩ hz
    exact hi.1 (hz i)
  · intro hn
    push Not at hn
    exact exists_isColumnLow_of_ne_zero hn

/-- GAPS 108.32, the persistent Betti numbers of a reduced filtered boundary matrix count the bars
`[i, j)` with `low_R(j) = i`, `i < a ≤ b ≤ j`, and the essential bars born before `a`. The
inequality `a ≤ b` is not needed. -/
theorem persistentBettiOfMatrix_eq_card {D R V : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (h : IsMatrixReduction D R V)
    (p a b : ℕ) :
    persistentBettiOfMatrix D dim p a b =
      (Finset.univ.filter fun j : Fin m ↦
        ∃ i, IsColumnLow R i j ∧ dim i = p ∧ i.val < a ∧ b ≤ j.val).card +
      (Finset.univ.filter fun j : Fin m ↦
        (∀ k, R k j = 0) ∧ (∀ l, ¬ IsColumnLow R j l) ∧ dim j = p ∧ j.val < a).card := by
  have hdD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).2
  have hZ := finrank_filteredCycles_add D dim p a
  have hZB := finrank_filteredCycles_inf_filteredBoundaries_add hD p a b
  rw [lowerLeftRank_dimColumnPart_eq_card hdD h] at hZ
  rw [lowerLeftRank_dimColumnPart_eq_card hdD h, lowerLeftRank_dimColumnPart_eq_card hdD h] at hZB
  -- split the `p`-simplices of `K_a` into negative, paired positive, and essential ones
  have hI1 := card_filter_eq_add_of_iff (α := Fin m) (P := fun k ↦ k.val < a ∧ dim k = p)
    (Q := fun l ↦ l.val < a ∧ dim l = p ∧ ∃ i, 0 ≤ i.val ∧ IsColumnLow R i l)
    (S := fun k ↦ k.val < a ∧ dim k = p ∧ ∀ j, R j k = 0)
    (fun k ↦ by
      have := (exists_isColumnLow_iff (R := R) (l := k))
      simp only [zero_le, true_and]
      tauto)
    (fun k hQ hS ↦ by
      obtain ⟨i, -, hi⟩ := hQ.2.2
      exact hi.1 (hS.2.2 i))
  have hI2 := card_filter_eq_add_of_iff (α := Fin m)
    (P := fun k ↦ k.val < a ∧ dim k = p ∧ ∀ j, R j k = 0)
    (Q := fun j ↦ j.val < a ∧ dim j = p ∧ ∃ l, IsColumnLow R j l)
    (S := fun j ↦ (∀ k, R k j = 0) ∧ (∀ l, ¬ IsColumnLow R j l) ∧ dim j = p ∧ j.val < a)
    (fun k ↦ by
      constructor
      · rintro ⟨ha, hp, hz⟩
        by_cases hl : ∃ l, IsColumnLow R k l
        · exact Or.inl ⟨ha, hp, hl⟩
        · push Not at hl
          exact Or.inr ⟨hz, hl, hp, ha⟩
      · rintro (⟨ha, hp, l, hl⟩ | ⟨hz, -, hp, ha⟩)
        · exact ⟨ha, hp, hl.col_eq_zero hD.mul_self_eq_zero h⟩
        · exact ⟨ha, hp, hz⟩)
    (fun k hQ hS ↦ by
      obtain ⟨l, hl⟩ := hQ.2.2
      exact hS.2.1 l hl)
  -- paired positive simplices correspond to the columns they are paired with
  have hI3 : (Finset.univ.filter fun j : Fin m ↦ j.val < a ∧ dim j = p ∧
        ∃ l, IsColumnLow R j l).card =
      (Finset.univ.filter fun l : Fin m ↦ ∃ i, IsColumnLow R i l ∧ i.val < a ∧ dim i = p).card := by
    symm
    refine Finset.card_bij (fun l hl ↦ (Finset.mem_filter.mp hl).2.choose) ?_ ?_ ?_
    · intro l hl
      obtain ⟨hlow, ha, hp⟩ := (Finset.mem_filter.mp hl).2.choose_spec
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hp, l, hlow⟩
    · intro l₁ hl₁ l₂ hl₂ heq
      have h1 := (Finset.mem_filter.mp hl₁).2.choose_spec.1
      have h2 := (Finset.mem_filter.mp hl₂).2.choose_spec.1
      rw [heq] at h1
      exact h.reduced _ _ _ h1 h2
    · intro j hj
      obtain ⟨-, ha, hp, l, hl⟩ := Finset.mem_filter.mp hj
      have hlmem : l ∈ Finset.univ.filter fun l : Fin m ↦
          ∃ i, IsColumnLow R i l ∧ i.val < a ∧ dim i = p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hl, ha, hp⟩
      refine ⟨l, hlmem, ?_⟩
      exact ((Finset.mem_filter.mp hlmem).2.choose_spec.1).unique hl
  -- split the paired columns according to `l < b`
  have hI4 := card_filter_eq_add_of_iff (α := Fin m)
    (P := fun l ↦ ∃ i, IsColumnLow R i l ∧ i.val < a ∧ dim i = p)
    (Q := fun l ↦ l.val < b ∧ dim l = p + 1 ∧ ∃ i, IsColumnLow R i l ∧ i.val < a)
    (S := fun j ↦ ∃ i, IsColumnLow R i j ∧ dim i = p ∧ i.val < a ∧ b ≤ j.val)
    (fun l ↦ by
      by_cases hl : ∃ i, IsColumnLow R i l
      · obtain ⟨i, hi⟩ := hl
        have hdim := hi.dim_eq hdD h
        rw [hi.exists_and_iff, hi.exists_and_iff, hi.exists_and_iff]
        omega
      · push Not at hl
        simp [hl])
    (fun l hQ hS ↦ by
      obtain ⟨i, hi, -, -, hb⟩ := hS
      omega)
  have hI5 := card_filter_eq_add_of_iff (α := Fin m)
    (P := fun l ↦ l.val < b ∧ dim l = p + 1 ∧ ∃ i, 0 ≤ i.val ∧ IsColumnLow R i l)
    (Q := fun l ↦ l.val < b ∧ dim l = p + 1 ∧ ∃ i, IsColumnLow R i l ∧ i.val < a)
    (S := fun l ↦ l.val < b ∧ dim l = p + 1 ∧ ∃ i, a ≤ i.val ∧ IsColumnLow R i l)
    (fun l ↦ by
      by_cases hl : ∃ i, IsColumnLow R i l
      · obtain ⟨i, hi⟩ := hl
        have e1 : (∃ i', 0 ≤ i'.val ∧ IsColumnLow R i' l) ↔ True :=
          ⟨fun _ ↦ trivial, fun _ ↦ ⟨i, Nat.zero_le _, hi⟩⟩
        have e2 : (∃ i', a ≤ i'.val ∧ IsColumnLow R i' l) ↔ a ≤ i.val := by
          rw [← hi.exists_and_iff (P := fun i' ↦ a ≤ i'.val)]
          exact ⟨fun ⟨i', h1, h2⟩ ↦ ⟨i', h2, h1⟩, fun ⟨i', h1, h2⟩ ↦ ⟨i', h2, h1⟩⟩
        rw [e1, e2, hi.exists_and_iff]
        rcases lt_or_ge i.val a with hia | hia
        · simp [hia, not_le.mpr hia]
        · simp [hia, not_lt.mpr hia]
      · push Not at hl
        simp [hl])
    (fun l hQ hS ↦ by
      obtain ⟨-, -, i, hi, ha⟩ := hQ
      obtain ⟨-, -, i', ha', hi'⟩ := hS
      have : a ≤ i.val := by rw [hi.unique hi']; exact ha'
      omega)
  unfold persistentBettiOfMatrix
  omega

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
  have hdD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).2
  have hlt : ∀ i j, D i j ≠ 0 → i < j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).1
  refine ⟨fun i j hij ↦ ?_, fun p a b _ ↦ persistentBettiOfMatrix_eq_card hD h p a b⟩
  have hdim := hij.dim_eq hdD h
  have hij' : i < j := hij.lt hlt h
  have hzi := hij.col_eq_zero hD.mul_self_eq_zero h
  refine ⟨hdim, ?_, ?_⟩
  · rw [persistentBettiOfMatrix_eq_card hD h, persistentBettiOfMatrix_eq_card hD h]
    have hT : (Finset.univ.filter fun j' : Fin m ↦ (∀ k, R k j' = 0) ∧
          (∀ l, ¬ IsColumnLow R j' l) ∧ dim j' = dim i ∧ j'.val < i.val + 1) =
        Finset.univ.filter fun j' : Fin m ↦ (∀ k, R k j' = 0) ∧
          (∀ l, ¬ IsColumnLow R j' l) ∧ dim j' = dim i ∧ j'.val < i.val := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, h3, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h4 with h4 | h4
        · exact h4
        · exact absurd hij (Fin.ext h4 ▸ h2 j)
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, h3, by omega⟩
    have hS : (Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧ dim i' = dim i ∧
          i'.val < i.val + 1 ∧ i.val + 1 ≤ l.val) =
        insert j (Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧ dim i' = dim i ∧
          i'.val < i.val ∧ i.val ≤ l.val) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨i', hi', hd, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact Or.inr ⟨i', hi', hd, h1, by omega⟩
        · have : i' = i := Fin.ext h1
          subst this
          exact Or.inl (h.reduced _ _ _ hi' hij)
      · rintro (rfl | ⟨i', hi', hd, h1, h2⟩)
        · exact ⟨i, hij, rfl, by omega, by have := Fin.lt_def.mp hij'; omega⟩
        · refine ⟨i', hi', hd, by omega, ?_⟩
          rcases Nat.lt_or_eq_of_le h2 with h2 | h2
          · omega
          · have : l = i := Fin.ext h2.symm
            subst this
            exact absurd (hzi i') hi'.1
    have hjS : j ∉ Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧
        dim i' = dim i ∧ i'.val < i.val ∧ i.val ≤ l.val := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro i' hi' _ h1
      have := hij.unique hi'
      subst this
      omega
    rw [hT, hS, Finset.card_insert_of_notMem hjS]
    ring
  · rw [persistentBettiOfMatrix_eq_card hD h, persistentBettiOfMatrix_eq_card hD h]
    have hT : (Finset.univ.filter fun j' : Fin m ↦ (∀ k, R k j' = 0) ∧
          (∀ l, ¬ IsColumnLow R j' l) ∧ dim j' = dim i ∧ j'.val < j.val + 1) =
        Finset.univ.filter fun j' : Fin m ↦ (∀ k, R k j' = 0) ∧
          (∀ l, ¬ IsColumnLow R j' l) ∧ dim j' = dim i ∧ j'.val < j.val := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, h3, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h4 with h4 | h4
        · exact h4
        · have : j' = j := Fin.ext h4
          subst this
          omega
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, h3, by omega⟩
    have hS : (Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧ dim i' = dim i ∧
          i'.val < j.val ∧ j.val ≤ l.val) =
        insert j (Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧ dim i' = dim i ∧
          i'.val < j.val + 1 ∧ j.val + 1 ≤ l.val) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨i', hi', hd, h1, h2⟩
        rcases Nat.lt_or_eq_of_le h2 with h2 | h2
        · exact Or.inr ⟨i', hi', hd, by omega, by omega⟩
        · exact Or.inl (Fin.ext h2.symm)
      · rintro (rfl | ⟨i', hi', hd, h1, h2⟩)
        · exact ⟨i, hij, rfl, Fin.lt_def.mp hij', le_rfl⟩
        · refine ⟨i', hi', hd, ?_, by omega⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
          · exact h1
          · have : i' = j := Fin.ext h1
            subst this
            omega
    have hjS : j ∉ Finset.univ.filter fun l : Fin m ↦ ∃ i', IsColumnLow R i' l ∧
        dim i' = dim i ∧ i'.val < j.val + 1 ∧ j.val + 1 ≤ l.val := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro _ _ _ _ h2
      omega
    rw [hT, hS, Finset.card_insert_of_notMem hjS]
    ring

end CKSD
