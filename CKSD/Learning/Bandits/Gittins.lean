module

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# The Gittins index for finite Markov bandits

Markov bandits are stated for finitely many arms on a common finite state space. The Gittins
index is the supremum, over continuation sets `C`, of the ratio of expected discounted reward to
expected discounted time up to the first exit time `τ ≥ 1` from `C`; for finite chains these
exit times attain the supremum over all stopping times `τ ≥ 1`.

## Main definitions

* `CKSD.FiniteMarkovBandit`, `CKSD.FiniteMarkovBandit.gittinsIndex`,
  `CKSD.FiniteMarkovBandit.banditPolicyValue`: Markov bandits and the Gittins index.

## Main results

* `CKSD.FiniteMarkovBandit.banditPolicyValue_le_of_gittins`: the Gittins index theorem
  (GAPS 107.51).
-/

public section

noncomputable section

open Filter Set
open scoped BigOperators Matrix

namespace CKSD

/-- A finite Markov bandit: arms indexed by `ι` on a common finite state space `X`, each with a
stochastic transition matrix and a reward function, and a discount `β ∈ [0,1)`. Only the played
arm moves. -/
structure FiniteMarkovBandit (ι X : Type*) [Fintype X] where
  /-- Discount factor. -/
  discount : ℝ
  /-- Nonnegative discount. -/
  discount_nonneg : 0 ≤ discount
  /-- Strict discount. -/
  discount_lt_one : discount < 1
  /-- Transition matrices of the arms. -/
  transition : ι → Matrix X X ℝ
  /-- Nonnegative transition probabilities. -/
  transition_nonneg : ∀ k x y, 0 ≤ transition k x y
  /-- Transition rows sum to one. -/
  sum_transition : ∀ k x, ∑ y, transition k x y = 1
  /-- Reward of playing an arm in a state. -/
  reward : ι → X → ℝ

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

namespace FiniteMarkovBandit

/-- Expected discounted reward and discounted time until the first exit time `τ ≥ 1` from the
continuation set `C`, for arm `k` started in each state. -/
def gittinsRewardAndTime (B : FiniteMarkovBandit ι X) (k : ι)
    (C : Finset X) : (X → ℝ) × (X → ℝ) :=
  let PC : Matrix X X ℝ := fun x y ↦ if y ∈ C then B.transition k x y else 0
  ((1 - B.discount • PC)⁻¹ *ᵥ B.reward k, (1 - B.discount • PC)⁻¹ *ᵥ fun _ ↦ 1)

/-- The Gittins index of arm `k` in state `x`. -/
def gittinsIndex (B : FiniteMarkovBandit ι X) (k : ι) (x : X) : ℝ :=
  sSup (range fun C : Finset X ↦
    (gittinsRewardAndTime B k C).1 x / (gittinsRewardAndTime B k C).2 x)

/-- Joint transition when arm `k` is played: only its coordinate moves. -/
def banditJointTransition (B : FiniteMarkovBandit ι X) (k : ι)
    (x y : ι → X) : ℝ :=
  if ∀ j ≠ k, y j = x j then B.transition k (x k) (y k) else 0

/-- Discounted value of a stationary deterministic arm-selection rule on joint states. -/
def banditPolicyValue (B : FiniteMarkovBandit ι X) (π : (ι → X) → ι) :
    (ι → X) → ℝ :=
  (1 - B.discount • (fun x y ↦ banditJointTransition B (π x) x y :
      Matrix (ι → X) (ι → X) ℝ))⁻¹ *ᵥ fun x ↦ B.reward (π x) (x (π x))

/-- GAPS 107.51, Gittins index theorem for finite Markov bandits: always playing an arm of
largest current Gittins index maximizes the expected discounted reward from every joint state.
The comparison class is the stationary deterministic rules on joint states, which attain the
optimum over all policies of this finite discounted model (GAPS 107.58). Countable state
spaces are not covered. -/
theorem banditPolicyValue_le_of_gittins (B : FiniteMarkovBandit ι X)
    (πG : (ι → X) → ι)
    (hG : ∀ x k, gittinsIndex B k (x k) ≤ gittinsIndex B (πG x) (x (πG x)))
    (π : (ι → X) → ι) (x : ι → X) :
    banditPolicyValue B π x ≤ banditPolicyValue B πG x := by
  sorry

end FiniteMarkovBandit

end CKSD
