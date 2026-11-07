module

public import CKSD.Learning.Basic

/-!
# Policy optimization and index policies in finite discounted models

Stationary randomized policies of a finite discounted model are row-stochastic tables
`π i b`. Their values are the unnormalized discounted values `V^π = (I - γ P^π)⁻¹ r^π`, with
`Q^π(i,b) = r(i,b) + γ ∑ⱼ P(j | i,b) V^π(j)` and advantage `A^π = Q^π - V^π`; for an initial
law `ρ`, `J(π) = ∑ᵢ ρ i V^π(i)` and `J⋆` is the supremum over stationary randomized policies,
which equals the optimum over all policies (GAPS 107.58).

Markov bandits are stated for finitely many arms on a common finite state space. The Gittins
index is the supremum, over continuation sets `C`, of the ratio of expected discounted reward to
expected discounted time up to the first exit time `τ ≥ 1` from `C`; for finite chains these
exit times attain the supremum over all stopping times `τ ≥ 1`.

Sources: GAPS 107.51 and 107.61.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators Matrix

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {s a : ℕ}

/-- A stationary randomized policy: each row is a probability vector. -/
def IsStationaryPolicy (π : Fin s → Fin a → ℝ) : Prop :=
  (∀ i b, 0 ≤ π i b) ∧ ∀ i, ∑ b, π i b = 1

/-- State transition matrix under a stationary randomized policy. -/
def policyTransition (M : FiniteMarkovDecisionProcess s a) (π : Fin s → Fin a → ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  fun i j ↦ ∑ b, π i b * M.transition i b j

/-- Expected one-step reward under a stationary randomized policy. -/
def policyReward (M : FiniteMarkovDecisionProcess s a) (π : Fin s → Fin a → ℝ) :
    Fin s → ℝ :=
  fun i ↦ ∑ b, π i b * M.reward i b

/-- Discounted value `V^π = (I - γ P^π)⁻¹ r^π` of a stationary randomized policy. -/
def policyValue (M : FiniteMarkovDecisionProcess s a) (π : Fin s → Fin a → ℝ) : Fin s → ℝ :=
  (1 - M.discount • policyTransition M π)⁻¹ *ᵥ policyReward M π

/-- State-action value of a stationary randomized policy. -/
def policyActionValue (M : FiniteMarkovDecisionProcess s a) (π : Fin s → Fin a → ℝ)
    (i : Fin s) (b : Fin a) : ℝ :=
  M.reward i b + M.discount * ∑ j, M.transition i b j * policyValue M π j

/-- Advantage `A^π(i,b) = Q^π(i,b) - V^π(i)`. -/
def policyAdvantage (M : FiniteMarkovDecisionProcess s a) (π : Fin s → Fin a → ℝ)
    (i : Fin s) (b : Fin a) : ℝ :=
  policyActionValue M π i b - policyValue M π i

/-- Expected value `J(π) = ∑ᵢ ρ i V^π(i)` under an initial law. -/
def policyObjective (M : FiniteMarkovDecisionProcess s a) (ρ : Fin s → ℝ)
    (π : Fin s → Fin a → ℝ) : ℝ :=
  ∑ i, ρ i * policyValue M π i

/-- Optimal objective over stationary randomized policies. -/
def optimalObjective (M : FiniteMarkovDecisionProcess s a) (ρ : Fin s → ℝ) : ℝ :=
  sSup ((policyObjective M ρ) '' {π | IsStationaryPolicy π})

/-- Natural policy gradient iterates for the softmax parameterization started at `θ = 0`:
`π⁽ᵗ⁺¹⁾(b | i) ∝ π⁽ᵗ⁾(b | i) exp(η A⁽ᵗ⁾(i,b) / (1 - γ))`. -/
def naturalPolicyGradientIterate (M : FiniteMarkovDecisionProcess s a) (η : ℝ) :
    ℕ → Fin s → Fin a → ℝ
  | 0 => fun _ _ ↦ (a : ℝ)⁻¹
  | t + 1 =>
    let π := naturalPolicyGradientIterate M η t
    fun i b ↦ π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) /
      ∑ b', π i b' * Real.exp (η * policyAdvantage M π i b' / (1 - M.discount))

/-- GAPS 107.61: convergence of natural policy gradient with softmax policies from `θ = 0`, for
rewards in `[0,1]`, any initial law `ρ`, and any step `η > 0` (Agarwal–Kakade–Lee–Mahajan):
`J⋆(ρ) - J(π⁽ᵀ⁾) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem optimalObjective_sub_npg_le (M : FiniteMarkovDecisionProcess s a) (ha : 0 < a)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) (ρ : Fin s → ℝ)
    (hρ : (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1)
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T) :
    optimalObjective M ρ - policyObjective M ρ (naturalPolicyGradientIterate M η T) ≤
      Real.log a / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
  sorry

/-- A finite Markov bandit: `K` arms on the common state space `Fin S`, each with a stochastic
transition matrix and a reward function, and a discount `β ∈ (0,1)`. Only the played arm moves. -/
structure FiniteMarkovBandit (K S : ℕ) where
  /-- Discount factor. -/
  discount : ℝ
  /-- Positive discount. -/
  discount_pos : 0 < discount
  /-- Strict discount. -/
  discount_lt_one : discount < 1
  /-- Transition matrices of the arms. -/
  transition : Fin K → Matrix (Fin S) (Fin S) ℝ
  /-- Nonnegative transition probabilities. -/
  transition_nonneg : ∀ k x y, 0 ≤ transition k x y
  /-- Transition rows sum to one. -/
  sum_transition : ∀ k x, ∑ y, transition k x y = 1
  /-- Reward of playing an arm in a state. -/
  reward : Fin K → Fin S → ℝ

/-- Expected discounted reward and discounted time until the first exit time `τ ≥ 1` from the
continuation set `C`, for arm `k` started in each state. -/
def gittinsRewardAndTime {K S : ℕ} (B : FiniteMarkovBandit K S) (k : Fin K)
    (C : Finset (Fin S)) : (Fin S → ℝ) × (Fin S → ℝ) :=
  let PC : Matrix (Fin S) (Fin S) ℝ := fun x y ↦ if y ∈ C then B.transition k x y else 0
  ((1 - B.discount • PC)⁻¹ *ᵥ B.reward k, (1 - B.discount • PC)⁻¹ *ᵥ fun _ ↦ 1)

/-- The Gittins index of arm `k` in state `x`. -/
def gittinsIndex {K S : ℕ} (B : FiniteMarkovBandit K S) (k : Fin K) (x : Fin S) : ℝ :=
  sSup (range fun C : Finset (Fin S) ↦
    (gittinsRewardAndTime B k C).1 x / (gittinsRewardAndTime B k C).2 x)

/-- Joint transition when arm `k` is played: only its coordinate moves. -/
def banditJointTransition {K S : ℕ} (B : FiniteMarkovBandit K S) (k : Fin K)
    (x y : Fin K → Fin S) : ℝ :=
  if ∀ j ≠ k, y j = x j then B.transition k (x k) (y k) else 0

/-- Discounted value of a stationary deterministic arm-selection rule on joint states. -/
def banditPolicyValue {K S : ℕ} (B : FiniteMarkovBandit K S) (π : (Fin K → Fin S) → Fin K) :
    (Fin K → Fin S) → ℝ :=
  (1 - B.discount • (fun x y ↦ banditJointTransition B (π x) x y :
      Matrix (Fin K → Fin S) (Fin K → Fin S) ℝ))⁻¹ *ᵥ fun x ↦ B.reward (π x) (x (π x))

/-- GAPS 107.51, Gittins index theorem for finite Markov bandits: always playing an arm of
largest current Gittins index maximizes the expected discounted reward from every joint state.
The comparison class is the stationary deterministic rules on joint states, which attain the
optimum over all policies of this finite discounted model (GAPS 107.58). Countable state
spaces are not covered. -/
theorem banditPolicyValue_le_of_gittins {K S : ℕ} (B : FiniteMarkovBandit K S)
    (πG : (Fin K → Fin S) → Fin K)
    (hG : ∀ x k, gittinsIndex B k (x k) ≤ gittinsIndex B (πG x) (x (πG x)))
    (π : (Fin K → Fin S) → Fin K) (x : Fin K → Fin S) :
    banditPolicyValue B π x ≤ banditPolicyValue B πG x := by
  sorry

end CKSD
