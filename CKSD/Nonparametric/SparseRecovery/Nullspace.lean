module

public import CKSD.Nonparametric.SparseRecovery.Basic

/-!
# Restricted isometry and the null space property

The classical block argument: sort the coordinates of `v` by decreasing absolute value and cut
them into consecutive blocks of `s` coordinates. Restricted orthogonality of the leading block
against the others, together with the comparison of each block with the preceding one, gives the
null space property under the restricted isometry property. The sharpened estimates of this file
are used for the robust null space property in `CKSD.Nonparametric.SparseRecovery.Robust`.

## Main definitions

* `CKSD.blockVector ℓ v k`: the restriction of `v` to the coordinates `j` with `ℓ j = k`.
* `CKSD.ripNullspaceRho`, `CKSD.ripNullspaceTau`: the constants `ρ(δ)` and `τ(δ)` of the
  robust null space property.

## Main results

* `CKSD.exists_decreasing_blocks`: the decomposition into blocks of decreasing absolute value.
* `CKSD.hasNullspaceProperty_of_hasRestrictedIsometry`: the restricted isometry property of
  order `2 s` with constant `δ < 1/3` implies the null space property on every set of at most
  `s` coordinates.
* `CKSD.abs_inner_apply_le_sqrt_of_hasRestrictedIsometry`: the sharpened restricted
  orthogonality bound `|⟪A x, A y⟫| ≤ √(δ² - t²) ‖x‖ ‖y‖` when `‖A x‖² = (1 + t) ‖x‖²`.

Sources: GAPS 103.48 and 103.49.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

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
  have hcard : ∀ k, (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ s := by
    intro k
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
  refine ⟨ℓ, ?_, hcard, ?_, fun j ↦ (Nat.div_le_self _ _).trans_lt (r j).isLt⟩
  · intro i j hij
    have hle : r j ≤ r i := by
      by_contra h
      push Not at h
      exact absurd (Nat.div_le_div_right (c := s) (le_of_lt (show (r i : ℕ) < r j from h)))
        (not_le.mpr hij)
    have := hmono hle
    simp only [Function.comp, r, Equiv.apply_symm_apply] at this
    linarith
  · rintro k ⟨i, hi⟩
    refine le_antisymm (hcard k) ?_
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

/-- The restriction `v_{B_k}` of `v` to the block `B_k = {j | ℓ j = k}`. -/
def blockVector {p : ℕ} (ℓ : Fin p → ℕ) (v : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun j ↦ if ℓ j = k then v j else 0)

/-- Coordinates of a block vector. -/
theorem blockVector_apply {p : ℕ} (ℓ : Fin p → ℕ) (v : EuclideanSpace ℝ (Fin p)) (k : ℕ)
    (j : Fin p) : blockVector ℓ v k j = if ℓ j = k then v j else 0 := rfl

/-- A block vector is supported in its block. -/
theorem sparsity_blockVector_le {p s : ℕ} (ℓ : Fin p → ℕ) (v : EuclideanSpace ℝ (Fin p))
    (k : ℕ) (hcard : (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ s) :
    sparsity (blockVector ℓ v k) ≤ s := by
  refine le_trans (Finset.card_le_card ?_) hcard
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockVector_apply] at hj ⊢
  by_contra h
  exact hj (ite_eq_right h)

/-- Distinct block vectors have disjoint supports. -/
theorem blockVector_eq_zero_or_eq_zero {p : ℕ} (ℓ : Fin p → ℕ) (v : EuclideanSpace ℝ (Fin p))
    {k k' : ℕ} (hkk : k ≠ k') (j : Fin p) :
    blockVector ℓ v k j = 0 ∨ blockVector ℓ v k' j = 0 := by
  simp only [blockVector_apply]
  by_cases h : ℓ j = k
  · right; rw [ite_eq_right]; rw [h]; exact hkk
  · left; rw [ite_eq_right h]

/-- The squared norm of a block vector is the sum of squares over its block. -/
theorem norm_blockVector_sq {p : ℕ} (ℓ : Fin p → ℕ) (v : EuclideanSpace ℝ (Fin p)) (k : ℕ) :
    ‖blockVector ℓ v k‖ ^ 2 = ∑ j ∈ Finset.univ.filter (fun j ↦ ℓ j = k), v j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [blockVector_apply, Real.norm_eq_abs, sq_abs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

/-- A vector is the sum of its blocks when all block indices are below `p`. -/
theorem eq_blockVector_zero_add_sum {p : ℕ} (ℓ : Fin p → ℕ) (hℓ : ∀ j, ℓ j < p)
    (v : EuclideanSpace ℝ (Fin p)) :
    v = blockVector ℓ v 0 + ∑ k ∈ Finset.range p, blockVector ℓ v (k + 1) := by
  ext j
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply]
  change v j = blockVector ℓ v 0 j + ∑ c ∈ Finset.range p, blockVector ℓ v (c + 1) j
  simp only [blockVector_apply]
  rcases Nat.eq_zero_or_pos (ℓ j) with h0 | h0
  · rw [ite_eq_left h0, Finset.sum_eq_zero fun k _ ↦ ite_eq_right (by omega)]; ring
  · obtain ⟨m, hm⟩ : ∃ m, ℓ j = m + 1 := ⟨ℓ j - 1, by omega⟩
    rw [ite_eq_right (by omega), zero_add, Finset.sum_eq_single m]
    · rw [ite_eq_left hm]
    · intro b _ hb; rw [ite_eq_right (by omega)]
    · intro hm'; exact absurd (Finset.mem_range.mpr (by have := hℓ j; omega)) hm'

/-- The block `ℓ¹` norms add up to the full `ℓ¹` norm. -/
theorem sum_range_sum_abs_eq_restrictedL1Norm {p : ℕ} (ℓ : Fin p → ℕ) (hℓ : ∀ j, ℓ j < p)
    (v : EuclideanSpace ℝ (Fin p)) :
    ∑ k ∈ Finset.range p, ∑ j ∈ Finset.univ.filter (fun j ↦ ℓ j = k), |v j| =
      restrictedL1Norm Finset.univ v :=
  Finset.sum_fiberwise_of_maps_to (fun j _ ↦ Finset.mem_range.mpr (hℓ j)) _

/-- Expanding `⟪A v₀, A v⟫` over the blocks of `v`, where `v₀` is the leading block. -/
theorem inner_apply_blockVector_zero_apply {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (ℓ : Fin p → ℕ)
    (hℓ : ∀ j, ℓ j < p) (v : EuclideanSpace ℝ (Fin p)) :
    ⟪A (blockVector ℓ v 0), A v⟫ = ‖A (blockVector ℓ v 0)‖ ^ 2 +
      ∑ k ∈ Finset.range p, ⟪A (blockVector ℓ v 0), A (blockVector ℓ v (k + 1))⟫ := by
  calc ⟪A (blockVector ℓ v 0), A v⟫ = ⟪A (blockVector ℓ v 0),
        A (blockVector ℓ v 0 + ∑ k ∈ Finset.range p, blockVector ℓ v (k + 1))⟫ :=
        congrArg (fun w ↦ ⟪A (blockVector ℓ v 0), A w⟫) (eq_blockVector_zero_add_sum ℓ hℓ v)
    _ = _ := by rw [map_add, inner_add_right, map_sum, inner_sum, real_inner_self_eq_norm_sq]

/-- A sum of nonnegative values over a set `S` is at most the sum over a set `B` that
dominates its complement and has at least as many elements as `S`. -/
theorem sum_le_sum_of_forall_le_of_card_le {ι : Type*} [DecidableEq ι] (S B : Finset ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hdom : ∀ i ∈ B, ∀ j ∉ B, f j ≤ f i)
    (hcard : S.card ≤ B.card) : ∑ j ∈ S, f j ≤ ∑ j ∈ B, f j := by
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

/-- For decreasing blocks, a sum over at most `s` coordinates of a quantity nondecreasing in
`|v j|` is at most the sum over the leading block. -/
theorem sum_le_sum_filter_eq_zero_of_decreasing_blocks {p s : ℕ} {v : Fin p → ℝ}
    {ℓ : Fin p → ℕ} (hcmp : ∀ i j, ℓ j < ℓ i → |v i| ≤ |v j|)
    (hfull : ∀ k, (∃ i, k < ℓ i) → (Finset.univ.filter fun j ↦ ℓ j = k).card = s)
    (S : Finset (Fin p)) (hS : S.card ≤ s) (f : Fin p → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, |v i| ≤ |v j| → f i ≤ f j) :
    ∑ j ∈ S, f j ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ ℓ j = 0), f j := by
  refine sum_le_sum_of_forall_le_of_card_le S _ f hf (fun i hi j hj ↦ ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hmono j i (hcmp j i (by omega))
  · by_cases h : ∃ i, 0 < ℓ i
    · rw [hfull 0 h]; exact hS
    · push Not at h
      refine Finset.card_le_card fun j _ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.le_zero.mp (h j)

/-- GAPS 103.48, restricted-isometry sufficient condition for exact sparse recovery: if `A` has
the restricted isometry property of order `2 s` with constant `0 ≤ δ < 1/3`, then `A` has the
null space property on every set `S` of at most `s` coordinates. -/
theorem hasNullspaceProperty_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : δ ∈ Ico 0 (1 / 3 : ℝ)) (hrip : HasRestrictedIsometry A (2 * s) δ)
    (S : Finset (Fin p)) (hS : S.card ≤ s) : HasNullspaceProperty A S := by
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
    obtain ⟨ℓ, hcmp, hcard, hfull, hℓlt⟩ := exists_decreasing_blocks (fun j ↦ v j) hs
    set lev : ℕ → Finset (Fin p) := fun k ↦ Finset.univ.filter fun j ↦ ℓ j = k with hlev
    set vk : ℕ → EuclideanSpace ℝ (Fin p) := blockVector ℓ v with hvk
    have hsp : ∀ k, sparsity (vk k) ≤ s := fun k ↦ sparsity_blockVector_le ℓ v k (hcard k)
    set L : ℕ → ℝ := fun k ↦ ∑ j ∈ lev k, |v j| with hL
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
      rw [hvk, norm_blockVector_sq, div_pow, Real.sq_sqrt hspos.le]
      calc ∑ j ∈ lev (k + 1), v j ^ 2 ≤ ∑ _j ∈ lev (k + 1), (L k / s) ^ 2 := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            simp only [lev, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hblock_pt k j hj) 2
        _ = (lev (k + 1)).card * (L k / s) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ s * (L k / s) ^ 2 := by
            gcongr; exact_mod_cast hcard (k + 1)
        _ = L k ^ 2 / s := by field_simp
    have hsumL : ∑ k ∈ Finset.range p, L k = restrictedL1Norm Finset.univ v :=
      sum_range_sum_abs_eq_restrictedL1Norm ℓ hℓlt v
    have hL0le : L 0 ≤ restrictedL1Norm Finset.univ v := by
      rw [← hsumL]
      exact Finset.single_le_sum (fun k _ ↦ hL0 k) (Finset.mem_range.mpr (by
        have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ hne (by subst h; exact Subsingleton.elim _ _)
        omega))
    -- the RIP step `(1 - δ) ‖v₀‖ ≤ δ ∑ₖ ‖vₖ₊₁‖`
    set X := ∑ k ∈ Finset.range p, ‖vk (k + 1)‖ with hX
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ ↦ norm_nonneg _
    have hAsq : ‖A (vk 0)‖ ^ 2 ≤ δ * ‖vk 0‖ * X := by
      have h0 := inner_apply_blockVector_zero_apply A ℓ hℓlt v
      rw [hv, inner_zero_right] at h0
      have hb : ∀ k ∈ Finset.range p, -(δ * ‖vk 0‖ * ‖vk (k + 1)‖) ≤
          ⟪A (vk 0), A (vk (k + 1))⟫ := fun k _ ↦
        (abs_le.mp (abs_inner_apply_le_of_hasRestrictedIsometry A δ hrip _ _ (hsp 0)
          (hsp (k + 1)) (blockVector_eq_zero_or_eq_zero ℓ v (by omega)))).1
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
      rw [mul_pow, Real.sq_sqrt hspos.le, hvk, norm_blockVector_sq]
      calc L 0 ^ 2 ≤ (lev 0).card * ∑ j ∈ lev 0, |v j| ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ s * ∑ j ∈ lev 0, v j ^ 2 := by
            simp only [sq_abs]
            gcongr
            exact_mod_cast hcard 0
    -- the first block carries the largest entries
    have hSB : restrictedL1Norm S v ≤ L 0 :=
      sum_le_sum_filter_eq_zero_of_decreasing_blocks hcmp hfull S hS (fun j ↦ |v j|)
        (fun j ↦ abs_nonneg _) fun _ _ h ↦ h
    have hsq : Real.sqrt s * X ≤ restrictedL1Norm Finset.univ v := by
      rw [le_div_iff₀ hsqrt] at hXle; linarith
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Square-root lifting bound used for the blocks of the restricted isometry argument: if at
most `s` values lie in `[m, M]` with `0 ≤ m`, and `m = 0` unless there are exactly `s` of them,
then their Euclidean norm is at most their sum divided by `√s` plus `√s (M - m) / 4`. -/
theorem sqrt_sum_sq_le_sum_div_sqrt_add {ι : Type*} (B : Finset ι) (a : ι → ℝ) {s : ℕ}
    (hs : 0 < s)
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
theorem abs_inner_apply_le_sqrt_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) {δ : ℝ} (hδ : 0 < δ)
    (hrip : HasRestrictedIsometry A (2 * s) δ) (x y : EuclideanSpace ℝ (Fin p))
    (hx : sparsity x ≤ s) (hy : sparsity y ≤ s) (hxy : ∀ j, x j = 0 ∨ y j = 0) (t : ℝ)
    (ht : ‖A x‖ ^ 2 = (1 + t) * ‖x‖ ^ 2) :
    |⟪A x, A y⟫| ≤ Real.sqrt (δ ^ 2 - t ^ 2) * ‖x‖ * ‖y‖ := by
  have hinner : ⟪x, y⟫ = 0 := inner_eq_zero_of_forall_eq_zero_or_eq_zero hxy
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

end CKSD
