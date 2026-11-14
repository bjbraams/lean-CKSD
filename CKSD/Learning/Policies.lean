module

public import CKSD.Learning.MarkovDecision


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

## Main definitions

* `CKSD.IsStationaryPolicy`, `CKSD.policyTransition`, `CKSD.policyReward`,
  `CKSD.policyValue`, `CKSD.policyActionValue`, `CKSD.policyAdvantage`,
  `CKSD.policyObjective`, `CKSD.optimalObjective`: stationary policies and their values.
* `CKSD.naturalPolicyGradientIterate`: natural policy gradient with softmax policies.
* `CKSD.FiniteMarkovBandit`, `CKSD.gittinsIndex`, `CKSD.banditPolicyValue`: Markov bandits and
  the Gittins index.

## Main results

* `CKSD.policy_value_sub_eq`: the performance-difference identity.
* `CKSD.policy_objective_sub_le_of_log_update`: the mirror-descent bound for logarithmic policy
  updates.
* `CKSD.optimal_objective_sub_npg_le`: convergence of natural policy gradient (GAPS 107.61).
* `CKSD.bandit_policy_value_le_of_gittins`: the Gittins index theorem (GAPS 107.51).
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped BigOperators Matrix

namespace CKSD

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- A stationary randomized policy: each row is a probability vector. -/
def IsStationaryPolicy (π : S → A → ℝ) : Prop :=
  (∀ i b, 0 ≤ π i b) ∧ ∀ i, ∑ b, π i b = 1

/-- State transition matrix under a stationary randomized policy. -/
def policyTransition (M : FiniteMarkovDecisionProcess S A) (π : S → A → ℝ) :
    Matrix S S ℝ :=
  fun i j ↦ ∑ b, π i b * M.transition i b j

/-- Expected one-step reward under a stationary randomized policy. -/
def policyReward (M : FiniteMarkovDecisionProcess S A) (π : S → A → ℝ) :
    S → ℝ :=
  fun i ↦ ∑ b, π i b * M.reward i b

/-- Discounted value `V^π = (I - γ P^π)⁻¹ r^π` of a stationary randomized policy. -/
def policyValue (M : FiniteMarkovDecisionProcess S A) (π : S → A → ℝ) : S → ℝ :=
  (1 - M.discount • policyTransition M π)⁻¹ *ᵥ policyReward M π

/-- State-action value of a stationary randomized policy. -/
def policyActionValue (M : FiniteMarkovDecisionProcess S A) (π : S → A → ℝ)
    (i : S) (b : A) : ℝ :=
  M.reward i b + M.discount * ∑ j, M.transition i b j * policyValue M π j

/-- Advantage `A^π(i,b) = Q^π(i,b) - V^π(i)`. -/
def policyAdvantage (M : FiniteMarkovDecisionProcess S A) (π : S → A → ℝ)
    (i : S) (b : A) : ℝ :=
  policyActionValue M π i b - policyValue M π i

/-- Expected value `J(π) = ∑ᵢ ρ i V^π(i)` under an initial law. -/
def policyObjective (M : FiniteMarkovDecisionProcess S A) (ρ : S → ℝ)
    (π : S → A → ℝ) : ℝ :=
  ∑ i, ρ i * policyValue M π i

/-- Optimal objective over stationary randomized policies. -/
def optimalObjective (M : FiniteMarkovDecisionProcess S A) (ρ : S → ℝ) : ℝ :=
  sSup ((policyObjective M ρ) '' {π | IsStationaryPolicy π})

/-- Natural policy gradient iterates for the softmax parameterization started at `θ = 0`:
`π⁽ᵗ⁺¹⁾(b | i) ∝ π⁽ᵗ⁾(b | i) exp(η A⁽ᵗ⁾(i,b) / (1 - γ))`. -/
def naturalPolicyGradientIterate (M : FiniteMarkovDecisionProcess S A) (η : ℝ) :
    ℕ → S → A → ℝ
  | 0 => fun _ _ ↦ (Fintype.card A : ℝ)⁻¹
  | t + 1 =>
    let π := naturalPolicyGradientIterate M η t
    fun i b ↦ π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) /
      ∑ b', π i b' * Real.exp (η * policyAdvantage M π i b' / (1 - M.discount))


omit [DecidableEq S] in
/-- The state transition matrix of a stationary policy has nonnegative entries. -/
theorem policy_transition_nonneg (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) (i j : S) :
    0 ≤ policyTransition M π i j :=
  Finset.sum_nonneg fun b _ ↦ mul_nonneg (hπ.1 i b) (M.transition_nonneg i b j)

omit [DecidableEq S] in
/-- The state transition matrix of a stationary policy is row-stochastic. -/
theorem sum_policy_transition (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) (i : S) :
    ∑ j, policyTransition M π i j = 1 := by
  simp only [policyTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.sum_transition_eq_one, mul_one]
  exact hπ.2 i

/-- The state transition matrix of a stationary policy is row-stochastic. -/
theorem policy_transition_mem_row_stochastic (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) :
    policyTransition M π ∈ Matrix.rowStochastic ℝ S :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨policy_transition_nonneg M hπ, sum_policy_transition M hπ⟩

/-- Bellman equation `V^π = r^π + γ P^π V^π` of a stationary policy. -/
theorem policy_value_eq_add (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) (i : S) :
    policyValue M π i =
      policyReward M π i + M.discount * (policyTransition M π *ᵥ policyValue M π) i := by
  have h := congrFun (one_sub_smul_mul_vec_inv_mul_vec
    (policy_transition_mem_row_stochastic M hπ) M.discount_pos.le M.discount_lt_one
    (policyReward M π)) i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  unfold policyValue
  linarith

/-- Averaging the advantage of `π` under the action law of a policy `π'`. -/
theorem sum_mul_policy_advantage (M : FiniteMarkovDecisionProcess S A)
    (π π' : S → A → ℝ) (hπ' : ∀ i, ∑ b, π' i b = 1) (i : S) :
    ∑ b, π' i b * policyAdvantage M π i b =
      policyReward M π' i + M.discount * (policyTransition M π' *ᵥ policyValue M π) i -
        policyValue M π i := by
  simp only [policyAdvantage, policyActionValue, policyReward, policyTransition, Matrix.mulVec,
    dotProduct, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hπ' i, one_mul]
  congr 2
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The advantage of a stationary policy averages to zero under its own action law. -/
theorem sum_mul_policy_advantage_self (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) (i : S) :
    ∑ b, π i b * policyAdvantage M π i b = 0 := by
  rw [sum_mul_policy_advantage M π π hπ.2 i, ← policy_value_eq_add M hπ i, sub_self]

/-- Performance difference identity: `V^{π'} - V^π = (I - γ P^{π'})⁻¹ ā`, where
`ā(i) = ∑_b π'(b | i) A^π(i,b)`. -/
theorem policy_value_sub_eq (M : FiniteMarkovDecisionProcess S A)
    {π π' : S → A → ℝ} (hπ' : IsStationaryPolicy π') :
    policyValue M π' - policyValue M π =
      (1 - M.discount • policyTransition M π')⁻¹ *ᵥ
        fun i ↦ ∑ b, π' i b * policyAdvantage M π i b := by
  have hPr := policy_transition_mem_row_stochastic M hπ'
  have hkey : (1 - M.discount • policyTransition M π') *ᵥ
      (policyValue M π' - policyValue M π) =
        fun i ↦ ∑ b, π' i b * policyAdvantage M π i b := by
    funext i
    rw [sum_mul_policy_advantage M π π' hπ'.2 i, Matrix.mulVec_sub]
    unfold policyValue
    rw [one_sub_smul_mul_vec_inv_mul_vec hPr M.discount_pos.le M.discount_lt_one, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← hkey, inv_one_sub_smul_mul_vec_mul_vec hPr M.discount_pos.le M.discount_lt_one]

/-- Values of stationary policies with rewards in `[0,1]` lie in `[0, 1/(1-γ)]`. -/
theorem policy_value_mem_icc (M : FiniteMarkovDecisionProcess S A)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) {π : S → A → ℝ} (hπ : IsStationaryPolicy π)
    (i : S) : policyValue M π i ∈ Icc 0 (1 / (1 - M.discount)) := by
  have hPr := policy_transition_mem_row_stochastic M hπ
  have hr0 : ∀ j, 0 ≤ policyReward M π j := fun j ↦
    Finset.sum_nonneg fun b _ ↦ mul_nonneg (hπ.1 j b) (hr j b).1
  have hr1 : ∀ j, policyReward M π j ≤ 1 := fun j ↦
    sum_mul_le_of_sum_eq_one _ (hπ.1 j) (hπ.2 j) _ _ fun b ↦ (hr j b).2
  have hγ0 := M.discount_pos.le
  have hγ1 := M.discount_lt_one
  refine ⟨(hr0 i).trans (le_inv_one_sub_smul_mul_vec hPr hγ0 hγ1 hr0 i), ?_⟩
  have := inv_one_sub_smul_mul_vec_mono hPr hγ0 hγ1 (v := fun _ ↦ 1) hr1 i
  rwa [inv_one_sub_smul_mul_vec_const hPr hγ0 hγ1] at this

/-- Gibbs' inequality for positive probability vectors: `∑ p (log p - log q) ≥ 0`. -/
theorem sum_mul_log_sub_log_nonneg {ι : Type*} (S : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ S, 0 < p i) (hq : ∀ i ∈ S, 0 < q i) (hpq : ∑ i ∈ S, p i = ∑ i ∈ S, q i) :
    0 ≤ ∑ i ∈ S, p i * (Real.log (p i) - Real.log (q i)) := by
  have h : ∀ i ∈ S, p i * (Real.log (q i) - Real.log (p i)) ≤ q i - p i := by
    intro i hi
    rw [← Real.log_div (hq i hi).ne' (hp i hi).ne']
    have := Real.log_le_sub_one_of_pos (div_pos (hq i hi) (hp i hi))
    calc p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
          mul_le_mul_of_nonneg_left this (hp i hi).le
      _ = q i - p i := by rw [mul_sub, mul_div_cancel₀ _ (hp i hi).ne', mul_one]
  have := Finset.sum_le_sum h
  rw [Finset.sum_sub_distrib, hpq, sub_self] at this
  have heq : ∑ i ∈ S, p i * (Real.log (p i) - Real.log (q i)) =
      -∑ i ∈ S, p i * (Real.log (q i) - Real.log (p i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

/-- The normalizer `Z(i) = ∑_b π(b | i) exp(η A^π(i,b) / (1-γ))` of a natural policy gradient
step from a stationary policy is at least `1`. -/
theorem one_le_sum_mul_exp_policy_advantage (M : FiniteMarkovDecisionProcess S A)
    {π : S → A → ℝ} (hπ : IsStationaryPolicy π) (η : ℝ) (i : S) :
    1 ≤ ∑ b, π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) := by
  have h : ∀ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount) + 1) ≤
      π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) := fun b ↦
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hπ.1 i b)
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) ↦ h b
  have h0 : ∑ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount) + 1) = 1 := by
    have h1 := sum_mul_policy_advantage_self M hπ i
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hπ.2 i]
    have : ∑ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount)) =
        η / (1 - M.discount) * ∑ b, π i b * policyAdvantage M π i b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [this, h1, mul_zero, zero_add]
  linarith

/-- Natural policy gradient iterates are stationary policies with positive entries. -/
theorem natural_policy_gradient_iterate_pos [Nonempty A] (M : FiniteMarkovDecisionProcess S A)
    (η : ℝ) (t : ℕ) :
    (∀ i b, 0 < naturalPolicyGradientIterate M η t i b) ∧
      ∀ i, ∑ b, naturalPolicyGradientIterate M η t i b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun _ _ ↦ by simp [naturalPolicyGradientIterate, Fintype.card_pos], fun i ↦ ?_⟩
    simp only [naturalPolicyGradientIterate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  | succ t ih =>
    have hZ : ∀ i, 0 < ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
        (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)) :=
      fun i ↦ Finset.sum_pos (fun b _ ↦ mul_pos (ih.1 i b) (Real.exp_pos _))
        Finset.univ_nonempty
    refine ⟨fun i b ↦ ?_, fun i ↦ ?_⟩
    · simp only [naturalPolicyGradientIterate]
      exact div_pos (mul_pos (ih.1 i b) (Real.exp_pos _)) (hZ i)
    · simp only [naturalPolicyGradientIterate]
      rw [← Finset.sum_div]
      exact div_self (hZ i).ne'

/-- Natural policy gradient iterates are stationary policies. -/
theorem is_stationary_policy_natural_policy_gradient_iterate [Nonempty A]
    (M : FiniteMarkovDecisionProcess S A)
    (η : ℝ) (t : ℕ) : IsStationaryPolicy (naturalPolicyGradientIterate M η t) :=
  ⟨fun i b ↦ ((natural_policy_gradient_iterate_pos M η t).1 i b).le,
    (natural_policy_gradient_iterate_pos M η t).2⟩

/-- Logarithmic form of the natural policy gradient step:
`log π⁽ᵗ⁺¹⁾(b | i) = log π⁽ᵗ⁾(b | i) + η A⁽ᵗ⁾(i,b) / (1-γ) - log Z⁽ᵗ⁾(i)`. -/
theorem log_natural_policy_gradient_iterate_succ [Nonempty A]
    (M : FiniteMarkovDecisionProcess S A)
    (η : ℝ) (t : ℕ) (i : S) (b : A) :
    Real.log (naturalPolicyGradientIterate M η (t + 1) i b) =
      Real.log (naturalPolicyGradientIterate M η t i b) +
        η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b / (1 - M.discount) -
        Real.log (∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
          (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' /
            (1 - M.discount))) := by
  have hpos := (natural_policy_gradient_iterate_pos M η t).1
  have hZ : 0 < ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
      (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)) :=
    Finset.sum_pos (fun b _ ↦ mul_pos (hpos i b) (Real.exp_pos _)) Finset.univ_nonempty
  simp only [naturalPolicyGradientIterate]
  rw [Real.log_div (mul_pos (hpos i b) (Real.exp_pos _)).ne' hZ.ne',
    Real.log_mul (hpos i b).ne' (Real.exp_pos _).ne', Real.log_exp]

/-- One step of the logarithmic update improves the value: if positive stationary policies
`π, π'` satisfy `A^π(i,b) = (1-γ)/η (log π'(b | i) - log π(b | i) + log Z(i))` with `Z ≥ 1`,
then `V^{π'}(i) - V^π(i) ≥ (1-γ)/η · log Z(i)` for every state `i`. -/
theorem mul_log_le_policy_value_sub_of_log_update (M : FiniteMarkovDecisionProcess S A)
    {η : ℝ} (hη : 0 < η) {π π' : S → A → ℝ} {Z : S → ℝ}
    (hpos : ∀ i b, 0 < π i b) (hpos' : ∀ i b, 0 < π' i b)
    (hsum : ∀ i, ∑ b, π i b = 1) (hsum' : ∀ i, ∑ b, π' i b = 1) (hZ1 : ∀ i, 1 ≤ Z i)
    (hA : ∀ i b, policyAdvantage M π i b = (1 - M.discount) / η *
      (Real.log (π' i b) - Real.log (π i b) + Real.log (Z i))) (i : S) :
    (1 - M.discount) / η * Real.log (Z i) ≤ policyValue M π' i - policyValue M π i := by
  have hc : 0 < (1 - M.discount) / η := div_pos (sub_pos.mpr M.discount_lt_one) hη
  have hst' : IsStationaryPolicy π' := ⟨fun i b ↦ (hpos' i b).le, hsum'⟩
  have hgZ : ∀ i, (1 - M.discount) / η * Real.log (Z i) ≤
      ∑ b, π' i b * policyAdvantage M π i b := by
    intro i
    have hgi : ∑ b, π' i b * policyAdvantage M π i b =
        (1 - M.discount) / η * (∑ b, π' i b * (Real.log (π' i b) - Real.log (π i b)) +
          (∑ b, π' i b) * Real.log (Z i)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ ↦ by rw [hA]; ring
    have hgibbs := sum_mul_log_sub_log_nonneg Finset.univ
      (fun b _ ↦ hpos' i b) (fun b _ ↦ hpos i b) (by rw [hsum' i, hsum i])
    rw [hgi, hsum' i, one_mul]
    nlinarith
  have hg0 : ∀ i, 0 ≤ ∑ b, π' i b * policyAdvantage M π i b := fun i ↦
    (mul_nonneg hc.le (Real.log_nonneg (hZ1 i))).trans (hgZ i)
  have hdiff := congrFun (policy_value_sub_eq M (π := π) hst') i
  rw [Pi.sub_apply] at hdiff
  rw [hdiff]
  exact (hgZ i).trans (le_inv_one_sub_smul_mul_vec (policy_transition_mem_row_stochastic M hst')
    M.discount_pos.le M.discount_lt_one hg0 i)

/-- Mirror-descent bound behind natural policy gradient: if positive stationary policies
`π⁽ᵗ⁾`, started from the uniform policy, satisfy the logarithmic update
`A⁽ᵗ⁾(i,b) = (1-γ)/η (log π⁽ᵗ⁺¹⁾(b | i) - log π⁽ᵗ⁾(b | i) + log Z⁽ᵗ⁾(i))` with normalizers
`Z⁽ᵗ⁾ ≥ 1`, then for rewards in `[0,1]` and every stationary comparator `π⋆`,
`J(π⋆) - J(π⁽ᵀ⁾) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem policy_objective_sub_le_of_log_update (M : FiniteMarkovDecisionProcess S A)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) (ρ : S → ℝ)
    (hρ : (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1) (η : ℝ) (hη : 0 < η)
    (π : ℕ → S → A → ℝ) (Z : ℕ → S → ℝ)
    (hpos : ∀ t i b, 0 < π t i b) (hsum : ∀ t i, ∑ b, π t i b = 1)
    (h0 : ∀ i b, π 0 i b = (Fintype.card A : ℝ)⁻¹) (hZ1 : ∀ t i, 1 ≤ Z t i)
    (hA : ∀ t i b, policyAdvantage M (π t) i b = (1 - M.discount) / η *
      (Real.log (π (t + 1) i b) - Real.log (π t i b) + Real.log (Z t i)))
    (T : ℕ) (hT : 1 ≤ T) {πs : S → A → ℝ} (hπs : IsStationaryPolicy πs) :
    policyObjective M ρ πs - policyObjective M ρ (π T) ≤
      Real.log (Fintype.card A) / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
  have h1γ : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hc : 0 < (1 - M.discount) / η := div_pos h1γ hη
  have hst : ∀ t, IsStationaryPolicy (π t) := fun t ↦ ⟨fun i b ↦ (hpos t i b).le, hsum t⟩
  have hlogZ : ∀ t i, 0 ≤ Real.log (Z t i) := fun t i ↦ Real.log_nonneg (hZ1 t i)
  have hinc : ∀ t i, (1 - M.discount) / η * Real.log (Z t i) ≤
      policyValue M (π (t + 1)) i - policyValue M (π t) i := fun t ↦
    mul_log_le_policy_value_sub_of_log_update M hη (hpos t) (hpos (t + 1)) (hsum t)
      (hsum (t + 1)) (hZ1 t) (hA t)
  -- the comparator functional `L u = ρ ⬝ (I - γ P⋆)⁻¹ u`
  have hPsr := policy_transition_mem_row_stochastic M hπs
  obtain ⟨L, hL⟩ : ∃ L : (S → ℝ) → ℝ, ∀ u, L u =
      ρ ⬝ᵥ ((1 - M.discount • policyTransition M πs)⁻¹ *ᵥ u) := ⟨_, fun _ ↦ rfl⟩
  have hLmono : ∀ u v : S → ℝ, (∀ i, u i ≤ v i) → L u ≤ L v := fun u v huv ↦ by
    rw [hL, hL]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (inv_one_sub_smul_mul_vec_mono hPsr M.discount_pos.le M.discount_lt_one huv i) (hρ.1 i)
  have hLadd : ∀ u v, L (u + v) = L u + L v := fun u v ↦ by
    simp only [hL, Matrix.mulVec_add, dotProduct_add]
  have hLsub : ∀ u v, L (u - v) = L u - L v := fun u v ↦ by
    simp only [hL, Matrix.mulVec_sub, dotProduct_sub]
  have hLsmul : ∀ (c : ℝ) u, L (c • u) = c * L u := fun c u ↦ by
    simp only [hL, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hLconst : ∀ c : ℝ, L (fun _ ↦ c) = c / (1 - M.discount) := fun c ↦ by
    rw [hL, inv_one_sub_smul_mul_vec_const hPsr M.discount_pos.le M.discount_lt_one]
    simp only [dotProduct, ← Finset.sum_mul, hρ.2, one_mul]
  -- the potential
  obtain ⟨D, hD⟩ : ∃ D : ℕ → S → ℝ, ∀ t i, D t i = ∑ b, πs i b * Real.log (π t i b) :=
    ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, ∀ t,
      Φ t = (1 - M.discount) / η * L (D t) + L (policyValue M (π t)) := ⟨_, fun _ ↦ rfl⟩
  have hJ : ∀ t, policyObjective M ρ πs - policyObjective M ρ (π t) =
      L (fun i ↦ ∑ b, πs i b * policyAdvantage M (π t) i b) := by
    intro t
    rw [hL, ← policy_value_sub_eq M hπs]
    simp only [policyObjective, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hstep : ∀ t, policyObjective M ρ πs - policyObjective M ρ (π t) ≤ Φ (t + 1) - Φ t := by
    intro t
    have hh : (fun i ↦ ∑ b, πs i b * policyAdvantage M (π t) i b) =
        ((1 - M.discount) / η) • (D (t + 1) - D t) +
          ((1 - M.discount) / η) • fun i ↦ Real.log (Z t i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hD]
      have : ∑ b, πs i b * policyAdvantage M (π t) i b =
          (1 - M.discount) / η * (∑ b, (πs i b * Real.log (π (t + 1) i b) -
            πs i b * Real.log (π t i b))) +
              (1 - M.discount) / η * ((∑ b, πs i b) * Real.log (Z t i)) := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ ↦ by rw [hA]; ring
      rw [this, hπs.2 i, one_mul, Finset.sum_sub_distrib]
    have hZle : L (((1 - M.discount) / η) • fun i ↦ Real.log (Z t i)) ≤
        L (policyValue M (π (t + 1)) - policyValue M (π t)) :=
      hLmono _ _ fun i ↦ by simpa using hinc t i
    rw [hJ t, hh, hLadd, hLsmul, hLsub]
    rw [hLsub] at hZle
    rw [hΦ, hΦ]
    linarith
  -- telescoping
  have htel : ∑ t ∈ Finset.range T, (policyObjective M ρ πs - policyObjective M ρ (π t)) ≤
      Φ T - Φ 0 := by
    rw [← Finset.sum_range_sub]
    exact Finset.sum_le_sum fun t _ ↦ hstep t
  -- bounding the potential increment
  have hDT : L (D T) ≤ 0 := by
    have := hLmono (D T) (fun _ ↦ 0) fun i ↦ by
      rw [hD]
      refine Finset.sum_nonpos fun b _ ↦ mul_nonpos_of_nonneg_of_nonpos (hπs.1 i b) ?_
      refine Real.log_nonpos (hpos T i b).le ?_
      rw [← hsum T i]
      exact Finset.single_le_sum (fun b' _ ↦ (hpos T i b').le) (Finset.mem_univ b)
    rwa [hLconst, zero_div] at this
  have hD0 : D 0 = fun _ ↦ -Real.log (Fintype.card A) := by
    funext i
    simp only [hD, h0, Real.log_inv, ← Finset.sum_mul, hπs.2 i, one_mul]
  have hVT : L (policyValue M (π T)) ≤ 1 / (1 - M.discount) / (1 - M.discount) := by
    rw [← hLconst]
    exact hLmono _ _ fun i ↦ (policy_value_mem_icc M hr (hst T) i).2
  have hV0 : 0 ≤ L (policyValue M (π 0)) := by
    have := hLmono (fun _ ↦ 0) _ fun i ↦ (policy_value_mem_icc M hr (hst 0) i).1
    rwa [hLconst, zero_div] at this
  have hΦb : Φ T - Φ 0 ≤ Real.log (Fintype.card A) / η + 1 / (1 - M.discount) ^ 2 := by
    rw [hΦ, hΦ, hD0, hLconst]
    have hfac : (1 - M.discount) / η * (-Real.log (Fintype.card A) / (1 - M.discount)) =
        -(Real.log (Fintype.card A) / η) := by
      field_simp
    have h2 : 1 / (1 - M.discount) / (1 - M.discount) = 1 / (1 - M.discount) ^ 2 := by
      rw [div_div, sq]
    have h3 : (1 - M.discount) / η * L (D T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le hDT
    linarith
  -- monotonicity of the objective along the iterates
  have hmono : Monotone fun t ↦ policyObjective M ρ (π t) := by
    refine monotone_nat_of_le_succ fun t ↦ ?_
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hρ.1 i)
    have := hinc t i
    have := mul_nonneg hc.le (hlogZ t i)
    linarith
  have hsumT : (T : ℝ) * (policyObjective M ρ πs - policyObjective M ρ (π T)) ≤
      ∑ t ∈ Finset.range T, (policyObjective M ρ πs - policyObjective M ρ (π t)) := by
    have hc : ∑ _t ∈ Finset.range T, (policyObjective M ρ πs - policyObjective M ρ (π T)) =
        (T : ℝ) * (policyObjective M ρ πs - policyObjective M ρ (π T)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hc]
    exact Finset.sum_le_sum fun t ht ↦
      sub_le_sub_left (hmono (Finset.mem_range.mp ht).le) _
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hfin : policyObjective M ρ πs - policyObjective M ρ (π T) ≤
      (Real.log (Fintype.card A) / η + 1 / (1 - M.discount) ^ 2) / T := by
    rw [le_div_iff₀ hTpos]
    linarith
  have heq : (Real.log (Fintype.card A) / η + 1 / (1 - M.discount) ^ 2) / T =
      Real.log (Fintype.card A) / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
    rw [add_div, div_div, div_div]
  rw [← heq]
  exact hfin

/-- GAPS 107.61: convergence of natural policy gradient with softmax policies from `θ = 0`, for
rewards in `[0,1]`, any initial law `ρ`, and any step `η > 0` (Agarwal–Kakade–Lee–Mahajan):
`J⋆(ρ) - J(π⁽ᵀ⁾) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem optimal_objective_sub_npg_le [Nonempty A] (M : FiniteMarkovDecisionProcess S A)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) (ρ : S → ℝ)
    (hρ : (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1)
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T) :
    optimalObjective M ρ - policyObjective M ρ (naturalPolicyGradientIterate M η T) ≤
      Real.log (Fintype.card A) / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
  have hbound : ∀ πs, IsStationaryPolicy πs →
      policyObjective M ρ πs - policyObjective M ρ (naturalPolicyGradientIterate M η T) ≤
        Real.log (Fintype.card A) / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
    intro πs hπs
    refine policy_objective_sub_le_of_log_update M hr ρ hρ η hη
      (naturalPolicyGradientIterate M η)
      (fun t i ↦ ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
        (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)))
      (fun t ↦ (natural_policy_gradient_iterate_pos M η t).1)
      (fun t ↦ (natural_policy_gradient_iterate_pos M η t).2) (fun _ _ ↦ rfl)
      (fun t i ↦ one_le_sum_mul_exp_policy_advantage M
        (is_stationary_policy_natural_policy_gradient_iterate M η t) η i)
      (fun t i b ↦ ?_) T hT hπs
    rw [log_natural_policy_gradient_iterate_succ M η t i b]
    have h1γ : (1 - M.discount) ≠ 0 := (sub_pos.mpr M.discount_lt_one).ne'
    field_simp
    ring
  have hne : ((policyObjective M ρ) '' {π | IsStationaryPolicy π}).Nonempty :=
    ⟨_, naturalPolicyGradientIterate M η 0,
      is_stationary_policy_natural_policy_gradient_iterate M η 0, rfl⟩
  rw [sub_le_iff_le_add, optimalObjective]
  refine csSup_le hne ?_
  rintro _ ⟨πs, hπs, rfl⟩
  have := hbound πs hπs
  linarith

/-- A finite Markov bandit: arms indexed by `ι` on a common finite state space `X`, each with a
stochastic transition matrix and a reward function, and a discount `β ∈ (0,1)`. Only the played
arm moves. -/
structure FiniteMarkovBandit (ι X : Type*) [Fintype X] where
  /-- Discount factor. -/
  discount : ℝ
  /-- Positive discount. -/
  discount_pos : 0 < discount
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
theorem bandit_policy_value_le_of_gittins (B : FiniteMarkovBandit ι X)
    (πG : (ι → X) → ι)
    (hG : ∀ x k, gittinsIndex B k (x k) ≤ gittinsIndex B (πG x) (x (πG x)))
    (π : (ι → X) → ι) (x : ι → X) :
    banditPolicyValue B π x ≤ banditPolicyValue B πG x := by
  sorry

end CKSD
