module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Fisher–Rao metric on the probability simplex

## Main definitions

* `CKSD.fisherRaoMetric`, `CKSD.amariChentsovTensor`: the Fisher–Rao metric and the
  Amari–Chentsov tensor at a point of the probability simplex.
* `CKSD.openProbabilitySimplex`, `CKSD.simplexTangentSpace`: the open simplex and its tangent
  space of zero-sum vectors.
* `CKSD.CongruentSimplexEmbedding`: Markov congruent embeddings of simplices.

## Main results

* `CKSD.fisherRaoMetric_congruent_embedding`: invariance of the Fisher–Rao metric under
  congruent embeddings (GAPS 102.58).

## References

Čencov, *Statistical Decision Rules and Optimal Inference*, for congruent embeddings.
-/
public section

noncomputable section

namespace CKSD

/-- Fisher–Rao bilinear form `∑ᵢ uᵢ vᵢ / pᵢ` at a point `p` of the open finite probability
simplex. -/
def fisherRaoMetric {ι : Type*} [Fintype ι] (p u v : ι → ℝ) : ℝ := ∑ i, u i * v i / p i

/-- Amari–Chentsov symmetric cubic tensor on the open probability simplex. -/
def amariChentsovTensor {ι : Type*} [Fintype ι] (p u v w : ι → ℝ) : ℝ :=
  ∑ i, u i * v i * w i / p i ^ 2

/-- The open probability simplex. -/
def openProbabilitySimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- Tangent space of the probability simplex, represented by zero-sum vectors. -/
def simplexTangentSpace (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) where
  carrier := {u | ∑ i, u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at hu hv ⊢
    rw [Finset.sum_add_distrib, hu, hv, add_zero]
  smul_mem' := by
    intro a u hu
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hu ⊢
    rw [← Finset.mul_sum, hu, mul_zero]

/-- A congruent embedding splits each input category into a block of output categories, with
strictly positive conditional weights summing to one on each block. Each block is nonempty
(`CongruentSimplexEmbedding.surjective_block`). -/
structure CongruentSimplexEmbedding (ι κ : Type*) [DecidableEq ι] [Fintype κ] where
  /-- Block label of an output category. -/
  block : κ → ι
  /-- Conditional probability of each output category within its block. -/
  weight : κ → ℝ
  /-- Strictly positive weights. -/
  weight_pos : ∀ j, 0 < weight j
  /-- Weights in a block sum to one. -/
  sum_weight : ∀ i, ∑ j, (if block j = i then weight j else 0) = 1

/-- Every input category of a congruent embedding has a nonempty block. -/
theorem CongruentSimplexEmbedding.surjective_block {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (f : CongruentSimplexEmbedding ι κ) : Function.Surjective f.block := by
  intro i
  by_contra h
  have h' : ∀ j, f.block j ≠ i := fun j hj ↦ h ⟨j, hj⟩
  have := f.sum_weight i
  simp [h'] at this

/-- The map `p ↦ (p (block j) · weight j)ⱼ` of a congruent simplex embedding; it is the
restriction of a linear map, and so is its own derivative. -/
def CongruentSimplexEmbedding.map {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (f : CongruentSimplexEmbedding ι κ) (p : ι → ℝ) : κ → ℝ := fun j ↦ p (f.block j) * f.weight j

/-- GAPS 102.58: the Fisher–Rao metric `∑ uᵢ vᵢ / pᵢ` on the open simplex is invariant under
congruent embeddings (Chentsov's defining invariance). With the convention `x / 0 = 0` the
identity holds for every `p`, not only on the open simplex. -/
theorem fisherRaoMetric_congruent_embedding {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : CongruentSimplexEmbedding ι κ) (p u v : ι → ℝ) :
    fisherRaoMetric (f.map p) (f.map u) (f.map v) = fisherRaoMetric p u v := by
  let a := fun i ↦ u i * v i / p i
  have hterm (j : κ) : f.map u j * f.map v j / f.map p j = a (f.block j) * f.weight j := by
    dsimp [CongruentSimplexEmbedding.map, a]
    rcases eq_or_ne (p (f.block j)) 0 with h0 | h0
    · simp [h0]
    · field_simp [h0, ne_of_gt (f.weight_pos j)]
  unfold fisherRaoMetric
  simp_rw [hterm]
  calc
    (∑ j, a (f.block j) * f.weight j) =
        ∑ j, ∑ i, if f.block j = i then a i * f.weight j else 0 := by simp
    _ = ∑ i, ∑ j, if f.block j = i then a i * f.weight j else 0 := Finset.sum_comm
    _ = ∑ i, a i * (∑ j, if f.block j = i then f.weight j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ i, u i * v i / p i := by simp_rw [f.sum_weight, mul_one]; rfl

end CKSD
