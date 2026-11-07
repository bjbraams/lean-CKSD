module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# LinearModels: Design

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
Randomization p-value validity uses Mathlib's minimum-on-a-finite-set theorem.
Fisher's inequality uses Mathlib's matrix rank bounds `Matrix.rank_mul_le_left` and
`Matrix.rank_le_width`; the complete families of orthogonal Latin squares use Mathlib's
`GaloisField` and its cardinality `GaloisField.card`.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- GAPS 105.37, Kiefer–Wolfowitz equivalence for a finite design space. -/
theorem kiefer_wolfowitz_equivalence {s p : ℕ} (hp : 0 < p)
    (f : Fin s → EuclideanSpace ℝ (Fin p)) (w : Fin s → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    let M := fun a : Fin s → ℝ ↦ Matrix.of (fun j k ↦ ∑ i, a i * f i j * f i k);
    ∀ (hM : (M w).PosDef),
    (∀ a, (∀ i, 0 ≤ a i) → (∑ i, a i = 1) → (M a).det ≤ (M w).det) ↔
      (∀ i, matrixQuadraticForm (M w)⁻¹ (f i) ≤ p) ∧
        ∀ i, 0 < w i → matrixQuadraticForm (M w)⁻¹ (f i) = p := by
  sorry

/-- GAPS 105.38, conservative finite randomization p-values, including ties. -/
theorem randomization_p_value_valid {s : ℕ} (w T : Fin s → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (α : ℝ) (hα : α ∈ Icc 0 1) :
    let p := fun i ↦ ∑ j, if T i ≤ T j then w j else 0;
    (∑ i, if p i ≤ α then w i else 0) ≤ α := by
  classical
  dsimp only
  let p := fun i ↦ ∑ j, if T i ≤ T j then w j else 0
  change (∑ i, if p i ≤ α then w i else 0) ≤ α
  by_cases hs : ({i | p i ≤ α} : Set (Fin s)).Nonempty
  · obtain ⟨i, hi, hmin⟩ :=
      Set.exists_min_image {i | p i ≤ α} T (Set.toFinite _) hs
    calc
      (∑ j, if p j ≤ α then w j else 0) ≤
          ∑ j, if T i ≤ T j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : p j ≤ α
        · simp [hj, hmin j hj]
        · simp only [if_neg hj]
          exact ite_nonneg (hw j) (le_refl 0)
      _ = p i := rfl
      _ ≤ α := hi
  · have hz : (∑ i, if p i ≤ α then w i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi ↦ hs ⟨i, hi⟩)
    rw [hz]
    exact hα.1

/-- GAPS 105.42, Fisher's inequality for nontrivial balanced incomplete blocks. -/
theorem fisher_inequality_of_balanced_incomplete_block_design
    (v b k r ell : ℕ) (hv : 2 ≤ v) (hk : 0 < k) (hkv : k < v)
    (hr : 0 < r) (hell : 0 < ell) (B : Fin b → Finset (Fin v))
    (hsize : ∀ j, (B j).card = k)
    (hrep : ∀ i, (Finset.univ.filter fun j ↦ i ∈ B j).card = r)
    (hpair : ∀ i i', i ≠ i' → (Finset.univ.filter fun j ↦ i ∈ B j ∧ i' ∈ B j).card = ell) :
    v ≤ b := by
  classical
  -- `ell < r`: some block through a point misses another point
  have hlt : ell < r := by
    let i : Fin v := ⟨0, by omega⟩
    obtain ⟨j₀, hj₀⟩ : (Finset.univ.filter fun j ↦ i ∈ B j).Nonempty := by
      rw [← Finset.card_pos, hrep]; exact hr
    have hj₀' : i ∈ B j₀ := (Finset.mem_filter.1 hj₀).2
    obtain ⟨i', -, hi'⟩ : ∃ i' ∈ Finset.univ, i' ∉ B j₀ := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset (Fin v)) ⊆ B j₀ := fun x _ ↦ hcon x (Finset.mem_univ x)
      have := Finset.card_le_card this
      simp [hsize] at this
      omega
    have hii' : i ≠ i' := fun h ↦ hi' (h ▸ hj₀')
    rw [← hpair i i' hii', ← hrep i]
    refine Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.1⟩
    · have := hsub hj₀
      simp only [Finset.mem_filter] at this
      exact hi' this.2.2
  let N : Matrix (Fin v) (Fin b) ℝ := Matrix.of fun i j ↦ if i ∈ B j then 1 else 0
  have hM : ∀ i i', (N * N.transpose) i i' = if i = i' then (r : ℝ) else ell := by
    intro i i'
    simp only [N, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_ite, mul_one,
      mul_zero]
    split_ifs with h
    · subst h
      rw [← hrep i]
      simp [Finset.sum_ite, Finset.filter_filter]
    · rw [← hpair i i' h]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one, Finset.filter_filter]
      congr 2
      ext j
      simp [and_comm]
  have hdet : (N * N.transpose).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ i, ((r : ℝ) - ell) * x i + ell * ∑ i', x i' = 0 := by
      intro i
      have := congrFun hx i
      simp only [Matrix.mulVec, dotProduct, hM, Pi.zero_apply] at this
      have e : ∀ i', (if i = i' then (r : ℝ) else ell) * x i' =
          ell * x i' + if i = i' then ((r : ℝ) - ell) * x i' else 0 := by
        intro i'; split_ifs <;> ring
      simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        ← Finset.mul_sum] at this
      linarith
    have hpos : (0 : ℝ) < r - ell := by
      have : (ell : ℝ) < r := by exact_mod_cast hlt
      linarith
    have hsum : ∑ i', x i' = 0 := by
      generalize hS : ∑ i', x i' = S at hrow
      have hconst : ∀ i, x i = -(ell * S) / (r - ell) := by
        intro i
        field_simp
        linarith [hrow i]
      have : ∑ i', x i' = ∑ _i : Fin v, (-(ell * S) / (r - ell) : ℝ) :=
        Finset.sum_congr rfl fun i _ ↦ hconst i
      rw [hS] at this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      have hv0 : (0 : ℝ) ≤ v * ell := by positivity
      field_simp at this
      nlinarith
    apply hx0
    funext i
    have := hrow i
    rw [hsum, mul_zero, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hpos.ne'
  have hrank : (N * N.transpose).rank = v := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)),
      Fintype.card_fin]
  calc v = (N * N.transpose).rank := hrank.symm
    _ ≤ N.rank := Matrix.rank_mul_le_left _ _
    _ ≤ b := Matrix.rank_le_width N

/-- GAPS 105.44, the upper bound on a family of mutually orthogonal Latin squares. -/
theorem card_orthogonal_latin_squares_le (s k : ℕ) (hs : 2 ≤ s)
    (L : Fin k → Fin s → Fin s → Fin s)
    (hLatin : ∀ i, IsLatinSquare (L i))
    (hortho : ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j)) : k ≤ s - 1 := by
  classical
  let r₀ : Fin s := ⟨0, by omega⟩
  let r₁ : Fin s := ⟨1, by omega⟩
  have h01 : r₀ ≠ r₁ := by simp [r₀, r₁, Fin.ext_iff]
  -- the column of row `r₀` carrying the symbol in cell `(r₁, r₀)`
  let t : Fin k → Fin s := fun i ↦
    (Equiv.ofBijective (L i r₀) ((hLatin i).1 r₀)).symm (L i r₁ r₀)
  have ht : ∀ i, L i r₀ (t i) = L i r₁ r₀ := fun i ↦
    Equiv.ofBijective_apply_symm_apply (L i r₀) ((hLatin i).1 r₀) _
  have hne : ∀ i, t i ≠ r₀ := by
    intro i h
    have := ht i
    rw [h] at this
    exact h01 (((hLatin i).2 r₀).1 this)
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne'
    have h := hortho i j hne' (a₁ := (r₀, t i)) (a₂ := (r₁, r₀)) (by
      simp only [Prod.mk.injEq]
      exact ⟨ht i, hij ▸ ht j⟩)
    exact h01 (congrArg Prod.fst h)
  have := Finset.card_le_card_of_injOn t (s := Finset.univ) (t := Finset.univ.erase r₀)
    (fun i _ ↦ Finset.mem_erase.2 ⟨hne i, Finset.mem_univ _⟩) hinj.injOn
  simpa [Finset.card_erase_of_mem] using this

/-- Over a finite field `F` identified with `Fin s`, the squares `(x, y) ↦ a x + y` for the
nonzero elements `a` form a complete family of mutually orthogonal Latin squares. -/
theorem exists_complete_orthogonal_latin_squares_of_equiv {F : Type*} [Field F] {t : ℕ}
    (e : F ≃ Fin (t + 1)) :
    ∃ L : Fin t → Fin (t + 1) → Fin (t + 1) → Fin (t + 1),
      (∀ i, IsLatinSquare (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j) := by
  let a : Fin t → F := fun i ↦ e.symm ((e 0).succAbove i)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := congrArg e h
    simp only [a, Equiv.apply_symm_apply] at this
    exact Fin.succAbove_ne _ _ this
  have ha_inj : Function.Injective a := fun i j h ↦
    Fin.succAbove_right_injective (e.symm.injective h)
  refine ⟨fun i x y ↦ e (a i * e.symm x + e.symm y), fun i ↦ ⟨fun x ↦ ?_, fun y ↦ ?_⟩,
    fun i j hij ↦ ?_⟩
  · refine Finite.injective_iff_bijective.1 fun y y' h ↦ ?_
    simpa using h
  · refine Finite.injective_iff_bijective.1 fun x x' h ↦ ?_
    simpa [ha i] using h
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨h₁, h₂⟩ := h
    have hx : e.symm x = e.symm x' := by
      have : (a i - a j) * (e.symm x - e.symm x') = 0 := by linear_combination h₁ - h₂
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (ha_inj (sub_eq_zero.1 h0)) hij
      · exact sub_eq_zero.1 h0
    have hy : e.symm y = e.symm y' := by
      rw [hx] at h₁
      exact add_left_cancel h₁
    simp only [Prod.mk.injEq]
    exact ⟨e.symm.injective hx, e.symm.injective hy⟩

/-- GAPS 105.44, existence of a complete family at prime-power orders. -/
theorem exists_complete_orthogonal_latin_squares_of_isPrimePow (s : ℕ) (hs : IsPrimePow s) :
    ∃ L : Fin (s - 1) → Fin s → Fin s → Fin s,
      (∀ i, IsLatinSquare (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j) := by
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff s).1 hs
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
  obtain ⟨t, ht⟩ : ∃ t, p ^ n = t + 1 := ⟨p ^ n - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)).symm⟩
  have e : GaloisField p n ≃ Fin (t + 1) := (Finite.equivFin _).trans (finCongr (hcard.trans ht))
  obtain ⟨L, hL⟩ := exists_complete_orthogonal_latin_squares_of_equiv e
  rw [ht, Nat.add_sub_cancel]
  exact ⟨L, hL⟩


end CKSD
