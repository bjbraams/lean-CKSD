module

public import CKSD.Geometry.MatrixReduction.Filtered
public import CKSD.Geometry.FiniteCombinatorics


/-!
# Persistent Betti numbers from a reduced boundary matrix

Rank-nullity identifies persistent homology ranks with the pairs of column lows in a reduced
filtered boundary matrix, including the unpaired essential classes.

## Main results

* `CKSD.persistent_betti_of_matrix_eq_card`: persistent Betti numbers count bars (GAPS 108.32).
* `CKSD.IsColumnLow.dim_eq_and_persistent_betti_of_matrix_eq`: the homological meaning of a pair
  (GAPS 108.32).
-/

@[expose] public section

noncomputable section

open Matrix Module

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

/-- Rank–nullity for the restriction of a linear map to a subspace. -/
theorem Submodule.finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V] [Module 𝕜 V]
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
theorem filtered_chains_eq_range (dim : Fin m → ℕ) (p a : ℕ) :
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
theorem finrank_filtered_chains (dim : Fin m → ℕ) (p a : ℕ) :
    finrank 𝕜 (filteredChains (𝕜 := 𝕜) dim p a) =
      (Finset.univ.filter fun k : Fin m ↦ k.val < a ∧ dim k = p).card := by
  classical
  rw [filtered_chains_eq_range, ← Matrix.rank, rank_diagonal, Fintype.card_subtype]
  congr 1
  ext k
  simp

/-- The boundary of the chains of the subcomplex is the range of a masked part of `D`. -/
theorem map_filtered_chains_eq_range (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ)
    (p a : ℕ) :
    (filteredChains (𝕜 := 𝕜) dim p a).map D.mulVecLin =
      LinearMap.range (lower_left_part (dimColumnPart D dim p) 0 a).mulVecLin := by
  rw [filtered_chains_eq_range, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
  congr 2
  ext k l
  simp only [mul_diagonal, lower_left_part, dimColumnPart, of_apply, zero_le, true_and]
  by_cases h1 : l.val < a <;> by_cases h2 : dim l = p <;> simp [h1, h2]

/-- Dimension of the cycles of the subcomplex formed by the first `a` simplices. -/
theorem finrank_filtered_cycles_add (D : Matrix (Fin m) (Fin m) 𝕜) (dim : Fin m → ℕ)
    (p a : ℕ) :
    finrank 𝕜 (filteredCycles D dim p a) + lowerLeftRank (dimColumnPart D dim p) 0 a =
      (Finset.univ.filter fun k : Fin m ↦ k.val < a ∧ dim k = p).card := by
  have h := Submodule.finrank_map_add_finrank_inf_ker D.mulVecLin (filteredChains (𝕜 := 𝕜) dim p a)
  rw [map_filtered_chains_eq_range] at h
  have h2 : filteredCycles D dim p a = filteredChains dim p a ⊓ LinearMap.ker D.mulVecLin := rfl
  rw [← finrank_filtered_chains (𝕜 := 𝕜), h2]
  unfold lowerLeftRank Matrix.rank
  omega

/-- Dimension of the cycles of `K_a` that bound in `K_b`. -/
theorem finrank_filtered_cycles_inf_filtered_boundaries_add {D : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (p a b : ℕ) :
    finrank 𝕜 ↥(filteredCycles D dim p a ⊓ filteredBoundaries D dim p b) +
        lowerLeftRank (dimColumnPart D dim (p + 1)) a b =
      lowerLeftRank (dimColumnPart D dim (p + 1)) 0 b := by
  classical
  set Pa : Matrix (Fin m) (Fin m) 𝕜 := diagonal fun k ↦ if a ≤ k.val then 1 else 0
  set B := filteredBoundaries D dim p b
  have hB : B = LinearMap.range (lower_left_part (dimColumnPart D dim (p + 1)) 0 b).mulVecLin :=
    map_filtered_chains_eq_range D dim (p + 1) b
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
  have h := Submodule.finrank_map_add_finrank_inf_ker Pa.mulVecLin B
  rw [← hinf] at h
  have hmap : B.map Pa.mulVecLin =
      LinearMap.range (lower_left_part (dimColumnPart D dim (p + 1)) a b).mulVecLin := by
    rw [hB, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul]
    congr 2
    ext k l
    simp only [Pa, diagonal_mul, lower_left_part, dimColumnPart, of_apply, zero_le, true_and]
    by_cases h1 : a ≤ k.val <;> simp [h1]
  have hfB : finrank 𝕜 B = (lower_left_part (dimColumnPart D dim (p + 1)) 0 b).rank := by
    rw [hB]; rfl
  rw [hmap, ← Matrix.rank] at h
  unfold lowerLeftRank
  omega

/-- A statement about the low of a column can be read off at any low of that column. -/
theorem IsColumnLow.exists_and_iff {R : Matrix (Fin m) (Fin m) 𝕜} {i l : Fin m}
    (hi : IsColumnLow R i l) {P : Fin m → Prop} : (∃ i', IsColumnLow R i' l ∧ P i') ↔ P i := by
  constructor
  · rintro ⟨i', hi', hP⟩
    exact hi.unique hi' ▸ hP
  · exact fun hP ↦ ⟨i, hi, hP⟩

/-- A column has a low exactly when it is nonzero. -/
theorem exists_is_column_low_iff {R : Matrix (Fin m) (Fin m) 𝕜} {l : Fin m} :
    (∃ i, IsColumnLow R i l) ↔ ¬ ∀ k, R k l = 0 := by
  constructor
  · rintro ⟨i, hi⟩ hz
    exact hi.1 (hz i)
  · intro hn
    push Not at hn
    exact exists_is_column_low_of_ne_zero hn

/-- GAPS 108.32, the persistent Betti numbers of a reduced filtered boundary matrix count the bars
`[i, j)` with `low_R(j) = i`, `i < a ≤ b ≤ j`, and the essential bars born before `a`. The
inequality `a ≤ b` is not needed. -/
theorem persistent_betti_of_matrix_eq_card {D R V : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (h : IsMatrixReduction D R V)
    (p a b : ℕ) :
    persistentBettiOfMatrix D dim p a b =
      (Finset.univ.filter fun j : Fin m ↦
        ∃ i, IsColumnLow R i j ∧ dim i = p ∧ i.val < a ∧ b ≤ j.val).card +
      (Finset.univ.filter fun j : Fin m ↦
        (∀ k, R k j = 0) ∧ (∀ l, ¬ IsColumnLow R j l) ∧ dim j = p ∧ j.val < a).card := by
  have hdD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).2
  have hZ := finrank_filtered_cycles_add D dim p a
  have hZB := finrank_filtered_cycles_inf_filtered_boundaries_add hD p a b
  rw [lower_left_rank_dim_column_part_eq_card hdD h] at hZ
  rw [lower_left_rank_dim_column_part_eq_card hdD h, lower_left_rank_dim_column_part_eq_card hdD h] at hZB
  -- split the `p`-simplices of `K_a` into negative, paired positive, and essential ones
  have hI1 := card_filter_eq_add_of_iff (α := Fin m) (P := fun k ↦ k.val < a ∧ dim k = p)
    (Q := fun l ↦ l.val < a ∧ dim l = p ∧ ∃ i, 0 ≤ i.val ∧ IsColumnLow R i l)
    (S := fun k ↦ k.val < a ∧ dim k = p ∧ ∀ j, R j k = 0)
    (fun k ↦ by
      have := (exists_is_column_low_iff (R := R) (l := k))
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
the low of no column; the count of bars by persistent Betti numbers is
`CKSD.persistent_betti_of_matrix_eq_card`. The restatement for monotone functions on simplices, with
bars `[f(σ_i), f(σ_j))`, is a relabelling and is not stated separately. -/
theorem IsColumnLow.dim_eq_and_persistent_betti_of_matrix_eq {D R V : Matrix (Fin m) (Fin m) 𝕜}
    {dim : Fin m → ℕ} (hD : IsFilteredBoundaryMatrix D dim) (h : IsMatrixReduction D R V)
    {i j : Fin m} (hij : IsColumnLow R i j) :
    dim j = dim i + 1 ∧
      persistentBettiOfMatrix D dim (dim i) (i.val + 1) (i.val + 1) =
        persistentBettiOfMatrix D dim (dim i) i.val i.val + 1 ∧
      persistentBettiOfMatrix D dim (dim i) (j.val + 1) (j.val + 1) + 1 =
        persistentBettiOfMatrix D dim (dim i) j.val j.val := by
  have hdD : ∀ i j, D i j ≠ 0 → dim i + 1 = dim j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).2
  have hlt : ∀ i j, D i j ≠ 0 → i < j := fun i j h ↦ (hD.lt_and_dim_of_ne_zero i j h).1
  have hdim := hij.dim_eq hdD h
  have hij' : i < j := hij.lt hlt h
  have hzi := hij.col_eq_zero hD.mul_self_eq_zero h
  refine ⟨hdim, ?_, ?_⟩
  · rw [persistent_betti_of_matrix_eq_card hD h, persistent_betti_of_matrix_eq_card hD h]
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
  · rw [persistent_betti_of_matrix_eq_card hD h, persistent_betti_of_matrix_eq_card hD h]
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
