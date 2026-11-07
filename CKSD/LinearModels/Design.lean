module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# LinearModels: Design

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
Randomization p-value validity uses Mathlib's minimum-on-a-finite-set theorem.
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
  sorry

/-- GAPS 105.44, the upper bound on a family of mutually orthogonal Latin squares. -/
theorem card_orthogonal_latin_squares_le (s k : ℕ) (hs : 2 ≤ s)
    (L : Fin k → Fin s → Fin s → Fin s)
    (hLatin : ∀ i, IsLatinSquare (L i))
    (hortho : ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j)) : k ≤ s - 1 := by
  sorry

/-- GAPS 105.44, existence of a complete family at prime-power orders. -/
theorem exists_complete_orthogonal_latin_squares_of_isPrimePow (s : ℕ) (hs : IsPrimePow s) :
    ∃ L : Fin (s - 1) → Fin s → Fin s → Fin s,
      (∀ i, IsLatinSquare (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j) := by
  sorry


end CKSD
