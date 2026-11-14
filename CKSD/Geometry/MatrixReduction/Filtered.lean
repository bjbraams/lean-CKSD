module

public import CKSD.Geometry.MatrixReduction.Basic

/-!
# Graded reductions and filtered chains

Filtered chain, cycle, and boundary subspaces, together with the compatibility of column
reductions with the grading (used for GAPS 108.32).

## Main definitions

* `CKSD.IsFilteredBoundaryMatrix`, `CKSD.filteredChains`, `CKSD.filteredCycles`,
  `CKSD.filteredBoundaries`, `CKSD.persistentBettiOfMatrix`.

## Main results

* `CKSD.Matrix.rank_add_of_disjoint_supports`, `CKSD.lowerLeftRank_eq_add_dimColumnPart`.
* `CKSD.IsColumnLow.dim_eq`, `CKSD.IsColumnLow.col_eq_zero`.
-/

@[expose] public section

noncomputable section

open Matrix Module

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

/-- A graded filtered chain-complex boundary matrix whose `k`th basis vector has degree `dim k`:
nonzero entries lower degree by one and precede the column in filtration order, and `D * D = 0`.
Signed simplicial incidence matrices are examples; the axioms do not require incidence entries. -/
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
theorem Matrix.rank_add_of_disjoint_supports {A B : Matrix (Fin m) (Fin m) 𝕜}
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
  apply Matrix.rank_add_of_disjoint_supports
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

end CKSD
