module

public import CKSD.Nonparametric.Basic

/-!
# Learning: definitions

Sources: `GAPS.md`, `SYNOPSIS107.md`, and `STRUCTURE107.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical Rademacher complexity, using a uniform sign vector and the supremum of the class. -/
def empiricalRademacherComplexity
    {H X : Type*} (n : ℕ) (f : H → X → ℝ) (x : Fin n → X) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ∑ σ : Fin n → Bool,
    sSup (range fun h ↦ (∑ i, (if σ i then (1 : ℝ) else -1) * f h (x i)) / n)

/-- Conditional binary-classification risk under a specified regression function. -/
def classificationRisk {X : Type*} [MeasurableSpace X] (P : Measure X)
    (η : X → ℝ) (g : X → Bool) : ℝ :=
  ∫ x, if g x then 1 - η x else η x ∂P

/-- Exponential-weights probabilities after `t` losses. -/
def hedgeWeight {K : ℕ} (loss : ℕ → Fin K → ℝ) (eta : ℝ) (t : ℕ) (i : Fin K) : ℝ :=
  Real.exp (-eta * ∑ s ∈ Finset.range t, loss s i) /
    (∑ j, Real.exp (-eta * ∑ s ∈ Finset.range t, loss s j))

/-- Privacy of a kernel for a supplied symmetric neighboring-data relation. -/
def IsDifferentiallyPrivate {D Y : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    (R : D → D → Prop) (epsilon delta : ℝ) (M : Kernel D Y) : Prop :=
  ∀ d d', R d d' → ∀ A : Set Y, MeasurableSet A →
    M d A ≤ ENNReal.ofReal (Real.exp epsilon) * M d' A + ENNReal.ofReal delta

/-- A finite discounted decision model, using real stochastic transition rows. -/
structure FiniteMarkovDecisionProcess (s a : ℕ) where
  /-- Discount in the open unit interval. -/
  discount : ℝ
  /-- Positive discount. -/
  discount_pos : 0 < discount
  /-- Strict discount. -/
  discount_lt_one : discount < 1
  /-- Expected one-step reward. -/
  reward : Fin s → Fin a → ℝ
  /-- Transition probabilities. -/
  transition : Fin s → Fin a → Fin s → ℝ
  /-- Nonnegative transition probabilities. -/
  transition_nonneg : ∀ i b j, 0 ≤ transition i b j
  /-- Transition rows sum to one. -/
  sum_transition_eq_one : ∀ i b, ∑ j, transition i b j = 1

/-- The state-value Bellman optimality operator of a finite model. -/
def bellmanOperator
    {s a : ℕ} (M : FiniteMarkovDecisionProcess s a) (V : Fin s → ℝ) (i : Fin s) : ℝ :=
  sSup (range fun b : Fin a ↦ M.reward i b + M.discount * ∑ j, M.transition i b j * V j)

/-- Number of plays of an arm before time `t`. -/
def armPlayCount {Ω : Type*} {K : ℕ} (A : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter fun j ↦ A j ω = i).card

/-- Prefix empirical reward average for one arm. -/
def armSampleAverage {Ω : Type*} {K : ℕ} (R : Fin K → ℕ → Ω → ℝ)
    (i : Fin K) (n : ℕ) (ω : Ω) : ℝ := (∑ j ∈ Finset.range n, R i j ω) / n


end CKSD
