module

public import CKSD.Learning.Basic
public import CKSD.Learning.Sequential

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

section Resolvent

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j, 0 ≤ H i j)
  (hH1 : ∀ i, ∑ j, H i j = 1) (γ : ℝ) (hg : γ ∈ Ioo 0 1)
include hH hH1 hg

/-- The resolvent `(I - γH)⁻¹` is a right inverse on vectors. -/
theorem one_sub_smul_mulVec_inv_mulVec (v : Fin n → ℝ) :
    (1 - γ • H) *ᵥ ((1 - γ • H)⁻¹ *ᵥ v) = v := by
  have hd : IsUnit (1 - γ • H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_smul H hH hH1 γ hg)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

/-- The resolvent `(I - γH)⁻¹` is a left inverse on vectors. -/
theorem inv_one_sub_smul_mulVec_mulVec (v : Fin n → ℝ) :
    (1 - γ • H)⁻¹ *ᵥ ((1 - γ • H) *ᵥ v) = v := by
  have hd : IsUnit (1 - γ • H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_smul H hH hH1 γ hg)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

/-- For a row-stochastic `H`, the resolvent `(I - γH)⁻¹` dominates the identity on
nonnegative vectors: `v ≤ (I - γH)⁻¹ v`, and in particular the resolvent is positive. -/
theorem le_inv_one_sub_smul_mulVec {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (i : Fin n) :
    v i ≤ ((1 - γ • H)⁻¹ *ᵥ v) i := by
  set w := (1 - γ • H)⁻¹ *ᵥ v
  have hw : ∀ j, w j = v j + γ * (H *ᵥ w) j := by
    intro j
    have := congrFun (one_sub_smul_mulVec_inv_mulVec H hH hH1 γ hg v) j
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hpos : ∀ j, 0 ≤ w j := by
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ w ⟨i, Finset.mem_univ _⟩
    have hk' : ∀ j, w k ≤ w j := fun j ↦ hk j (Finset.mem_univ _)
    have hHw : w k ≤ (H *ᵥ w) k := by
      have := sum_mul_le_of_stochastic (H k) (hH k) (hH1 k) (fun j ↦ -w j) (-w k)
        fun j ↦ neg_le_neg (hk' j)
      simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at this
      exact this
    have h1 := hw k
    have h2 := hv k
    have hwk : 0 ≤ w k := by nlinarith [hg.1, hg.2]
    exact fun j ↦ hwk.trans (hk' j)
  have hHw : 0 ≤ (H *ᵥ w) i := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hH i j) (hpos j)
  rw [hw i]
  nlinarith [hg.1]

/-- The resolvent `(I - γH)⁻¹` is monotone on vectors for a row-stochastic `H`. -/
theorem inv_one_sub_smul_mulVec_mono {u v : Fin n → ℝ} (huv : ∀ i, u i ≤ v i) (i : Fin n) :
    ((1 - γ • H)⁻¹ *ᵥ u) i ≤ ((1 - γ • H)⁻¹ *ᵥ v) i := by
  have h := le_inv_one_sub_smul_mulVec H hH hH1 γ hg (v := v - u)
    (fun j ↦ sub_nonneg.mpr (huv j)) i
  have h0 : 0 ≤ (v - u) i := sub_nonneg.mpr (huv i)
  rw [Matrix.mulVec_sub, Pi.sub_apply] at h
  rw [Pi.sub_apply] at h0 h
  linarith

/-- The resolvent `(I - γH)⁻¹` maps the constant `c` to the constant `c / (1 - γ)`. -/
theorem inv_one_sub_smul_mulVec_const (c : ℝ) :
    (1 - γ • H)⁻¹ *ᵥ (fun _ ↦ c) = fun _ ↦ c / (1 - γ) := by
  have h1 : (1 - γ) ≠ 0 := (sub_pos.mpr hg.2).ne'
  have : (1 - γ • H) *ᵥ (fun _ : Fin n ↦ c / (1 - γ)) = fun _ ↦ c := by
    funext i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      ← Finset.sum_mul, hH1, one_mul]
    field_simp
  rw [← this, inv_one_sub_smul_mulVec_mulVec H hH hH1 γ hg]

end Resolvent

/-- The discount of a finite model lies in the open unit interval. -/
theorem FiniteMarkovDecisionProcess.discount_mem_Ioo (M : FiniteMarkovDecisionProcess s a) : M.discount ∈ Ioo 0 1 :=
  ⟨M.discount_pos, M.discount_lt_one⟩

/-- The state transition matrix of a stationary policy has nonnegative entries. -/
theorem policyTransition_nonneg (M : FiniteMarkovDecisionProcess s a)
    {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π) (i j : Fin s) :
    0 ≤ policyTransition M π i j :=
  Finset.sum_nonneg fun b _ ↦ mul_nonneg (hπ.1 i b) (M.transition_nonneg i b j)

/-- The state transition matrix of a stationary policy is row-stochastic. -/
theorem sum_policyTransition (M : FiniteMarkovDecisionProcess s a)
    {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π) (i : Fin s) :
    ∑ j, policyTransition M π i j = 1 := by
  simp only [policyTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.sum_transition_eq_one, mul_one]
  exact hπ.2 i

/-- Bellman equation `V^π = r^π + γ P^π V^π` of a stationary policy. -/
theorem policyValue_eq_add (M : FiniteMarkovDecisionProcess s a)
    {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π) (i : Fin s) :
    policyValue M π i =
      policyReward M π i + M.discount * (policyTransition M π *ᵥ policyValue M π) i := by
  have h := congrFun (one_sub_smul_mulVec_inv_mulVec (policyTransition M π)
    (policyTransition_nonneg M hπ) (sum_policyTransition M hπ) M.discount M.discount_mem_Ioo
    (policyReward M π)) i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  unfold policyValue
  linarith

/-- Averaging the advantage of `π` under the action law of a policy `π'`. -/
theorem sum_mul_policyAdvantage (M : FiniteMarkovDecisionProcess s a)
    (π π' : Fin s → Fin a → ℝ) (hπ' : ∀ i, ∑ b, π' i b = 1) (i : Fin s) :
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
theorem sum_mul_policyAdvantage_self (M : FiniteMarkovDecisionProcess s a)
    {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π) (i : Fin s) :
    ∑ b, π i b * policyAdvantage M π i b = 0 := by
  rw [sum_mul_policyAdvantage M π π hπ.2 i, ← policyValue_eq_add M hπ i, sub_self]

/-- Performance difference identity: `V^{π'} - V^π = (I - γ P^{π'})⁻¹ ā`, where
`ā(i) = ∑_b π'(b | i) A^π(i,b)`. -/
theorem policyValue_sub_eq (M : FiniteMarkovDecisionProcess s a)
    {π π' : Fin s → Fin a → ℝ} (hπ' : IsStationaryPolicy π') :
    policyValue M π' - policyValue M π =
      (1 - M.discount • policyTransition M π')⁻¹ *ᵥ
        fun i ↦ ∑ b, π' i b * policyAdvantage M π i b := by
  have hP := policyTransition_nonneg M hπ'
  have hP1 := sum_policyTransition M hπ'
  have hkey : (1 - M.discount • policyTransition M π') *ᵥ
      (policyValue M π' - policyValue M π) =
        fun i ↦ ∑ b, π' i b * policyAdvantage M π i b := by
    funext i
    rw [sum_mul_policyAdvantage M π π' hπ'.2 i, Matrix.mulVec_sub]
    unfold policyValue
    rw [one_sub_smul_mulVec_inv_mulVec _ hP hP1 _ M.discount_mem_Ioo, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← hkey, inv_one_sub_smul_mulVec_mulVec _ hP hP1 _ M.discount_mem_Ioo]

/-- Values of stationary policies with rewards in `[0,1]` lie in `[0, 1/(1-γ)]`. -/
theorem policyValue_mem_Icc (M : FiniteMarkovDecisionProcess s a)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π)
    (i : Fin s) : policyValue M π i ∈ Icc 0 (1 / (1 - M.discount)) := by
  have hP := policyTransition_nonneg M hπ
  have hP1 := sum_policyTransition M hπ
  have hr0 : ∀ j, 0 ≤ policyReward M π j := fun j ↦
    Finset.sum_nonneg fun b _ ↦ mul_nonneg (hπ.1 j b) (hr j b).1
  have hr1 : ∀ j, policyReward M π j ≤ 1 := fun j ↦
    sum_mul_le_of_stochastic _ (hπ.1 j) (hπ.2 j) _ _ fun b ↦ (hr j b).2
  refine ⟨(hr0 i).trans (le_inv_one_sub_smul_mulVec _ hP hP1 _ M.discount_mem_Ioo hr0 i), ?_⟩
  have := inv_one_sub_smul_mulVec_mono _ hP hP1 _ M.discount_mem_Ioo (v := fun _ ↦ 1) hr1 i
  rwa [inv_one_sub_smul_mulVec_const _ hP hP1 _ M.discount_mem_Ioo] at this

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
theorem one_le_sum_mul_exp_policyAdvantage (M : FiniteMarkovDecisionProcess s a)
    {π : Fin s → Fin a → ℝ} (hπ : IsStationaryPolicy π) (η : ℝ) (i : Fin s) :
    1 ≤ ∑ b, π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) := by
  have h : ∀ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount) + 1) ≤
      π i b * Real.exp (η * policyAdvantage M π i b / (1 - M.discount)) := fun b ↦
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hπ.1 i b)
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) ↦ h b
  have h0 : ∑ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount) + 1) = 1 := by
    have h1 := sum_mul_policyAdvantage_self M hπ i
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hπ.2 i]
    have : ∑ b, π i b * (η * policyAdvantage M π i b / (1 - M.discount)) =
        η / (1 - M.discount) * ∑ b, π i b * policyAdvantage M π i b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [this, h1, mul_zero, zero_add]
  linarith

/-- Natural policy gradient iterates are stationary policies with positive entries. -/
theorem naturalPolicyGradientIterate_pos (M : FiniteMarkovDecisionProcess s a) (ha : 0 < a)
    (η : ℝ) (t : ℕ) :
    (∀ i b, 0 < naturalPolicyGradientIterate M η t i b) ∧
      ∀ i, ∑ b, naturalPolicyGradientIterate M η t i b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun _ _ ↦ by simp [naturalPolicyGradientIterate, ha], fun i ↦ ?_⟩
    simp only [naturalPolicyGradientIterate, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast ha.ne')
  | succ t ih =>
    have hZ : ∀ i, 0 < ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
        (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)) :=
      fun i ↦ Finset.sum_pos (fun b _ ↦ mul_pos (ih.1 i b) (Real.exp_pos _))
        ⟨⟨0, ha⟩, Finset.mem_univ _⟩
    refine ⟨fun i b ↦ ?_, fun i ↦ ?_⟩
    · simp only [naturalPolicyGradientIterate]
      exact div_pos (mul_pos (ih.1 i b) (Real.exp_pos _)) (hZ i)
    · simp only [naturalPolicyGradientIterate]
      rw [← Finset.sum_div]
      exact div_self (hZ i).ne'

/-- Natural policy gradient iterates are stationary policies. -/
theorem isStationaryPolicy_naturalPolicyGradientIterate (M : FiniteMarkovDecisionProcess s a)
    (ha : 0 < a) (η : ℝ) (t : ℕ) : IsStationaryPolicy (naturalPolicyGradientIterate M η t) :=
  ⟨fun i b ↦ ((naturalPolicyGradientIterate_pos M ha η t).1 i b).le,
    (naturalPolicyGradientIterate_pos M ha η t).2⟩

/-- Logarithmic form of the natural policy gradient step:
`log π⁽ᵗ⁺¹⁾(b | i) = log π⁽ᵗ⁾(b | i) + η A⁽ᵗ⁾(i,b) / (1-γ) - log Z⁽ᵗ⁾(i)`. -/
theorem log_naturalPolicyGradientIterate_succ (M : FiniteMarkovDecisionProcess s a)
    (ha : 0 < a) (η : ℝ) (t : ℕ) (i : Fin s) (b : Fin a) :
    Real.log (naturalPolicyGradientIterate M η (t + 1) i b) =
      Real.log (naturalPolicyGradientIterate M η t i b) +
        η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b / (1 - M.discount) -
        Real.log (∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
          (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' /
            (1 - M.discount))) := by
  have hpos := (naturalPolicyGradientIterate_pos M ha η t).1
  have hZ : 0 < ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
      (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)) :=
    Finset.sum_pos (fun b _ ↦ mul_pos (hpos i b) (Real.exp_pos _)) ⟨⟨0, ha⟩, Finset.mem_univ _⟩
  simp only [naturalPolicyGradientIterate]
  rw [Real.log_div (mul_pos (hpos i b) (Real.exp_pos _)).ne' hZ.ne',
    Real.log_mul (hpos i b).ne' (Real.exp_pos _).ne', Real.log_exp]

/-- Mirror-descent bound behind natural policy gradient: if positive stationary policies
`π⁽ᵗ⁾`, started from the uniform policy, satisfy the logarithmic update
`A⁽ᵗ⁾(i,b) = (1-γ)/η (log π⁽ᵗ⁺¹⁾(b | i) - log π⁽ᵗ⁾(b | i) + log Z⁽ᵗ⁾(i))` with normalizers
`Z⁽ᵗ⁾ ≥ 1`, then for rewards in `[0,1]` and every stationary comparator `π⋆`,
`J(π⋆) - J(π⁽ᵀ⁾) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem policyObjective_sub_le_of_log_update (M : FiniteMarkovDecisionProcess s a)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) (ρ : Fin s → ℝ)
    (hρ : (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1) (η : ℝ) (hη : 0 < η)
    (π : ℕ → Fin s → Fin a → ℝ) (Z : ℕ → Fin s → ℝ)
    (hpos : ∀ t i b, 0 < π t i b) (hsum : ∀ t i, ∑ b, π t i b = 1)
    (h0 : ∀ i b, π 0 i b = (a : ℝ)⁻¹) (hZ1 : ∀ t i, 1 ≤ Z t i)
    (hA : ∀ t i b, policyAdvantage M (π t) i b = (1 - M.discount) / η *
      (Real.log (π (t + 1) i b) - Real.log (π t i b) + Real.log (Z t i)))
    (T : ℕ) (hT : 1 ≤ T) {πs : Fin s → Fin a → ℝ} (hπs : IsStationaryPolicy πs) :
    policyObjective M ρ πs - policyObjective M ρ (π T) ≤
      Real.log a / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
  have hg : M.discount ∈ Ioo 0 1 := M.discount_mem_Ioo
  have h1γ : 0 < 1 - M.discount := sub_pos.mpr hg.2
  have hc : 0 < (1 - M.discount) / η := div_pos h1γ hη
  have hst : ∀ t, IsStationaryPolicy (π t) := fun t ↦ ⟨fun i b ↦ (hpos t i b).le, hsum t⟩
  have hlogZ : ∀ t i, 0 ≤ Real.log (Z t i) := fun t i ↦ Real.log_nonneg (hZ1 t i)
  -- monotone improvement
  have hinc : ∀ t i, (1 - M.discount) / η * Real.log (Z t i) ≤
      policyValue M (π (t + 1)) i - policyValue M (π t) i := by
    intro t i
    have hgZ : ∀ i, (1 - M.discount) / η * Real.log (Z t i) ≤
        ∑ b, π (t + 1) i b * policyAdvantage M (π t) i b := by
      intro i
      have hgi : ∑ b, π (t + 1) i b * policyAdvantage M (π t) i b =
          (1 - M.discount) / η * (∑ b, π (t + 1) i b *
            (Real.log (π (t + 1) i b) - Real.log (π t i b)) +
              (∑ b, π (t + 1) i b) * Real.log (Z t i)) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ ↦ by rw [hA]; ring
      have hgibbs := sum_mul_log_sub_log_nonneg Finset.univ
        (fun b _ ↦ hpos (t + 1) i b) (fun b _ ↦ hpos t i b)
        (by rw [hsum (t + 1) i, hsum t i])
      rw [hgi, hsum (t + 1) i, one_mul]
      nlinarith
    have hg0 : ∀ i, 0 ≤ ∑ b, π (t + 1) i b * policyAdvantage M (π t) i b := fun i ↦
      (mul_nonneg hc.le (hlogZ t i)).trans (hgZ i)
    have hdiff := congrFun (policyValue_sub_eq M (π := π t) (hst (t + 1))) i
    have hle := le_inv_one_sub_smul_mulVec _ (policyTransition_nonneg M (hst (t + 1)))
      (sum_policyTransition M (hst (t + 1))) M.discount hg hg0 i
    rw [Pi.sub_apply] at hdiff
    rw [hdiff]
    exact (hgZ i).trans hle
  -- the comparator functional `L u = ρ ⬝ (I - γ P⋆)⁻¹ u`
  have hPs := policyTransition_nonneg M hπs
  have hPs1 := sum_policyTransition M hπs
  obtain ⟨L, hL⟩ : ∃ L : (Fin s → ℝ) → ℝ, ∀ u, L u =
      ρ ⬝ᵥ ((1 - M.discount • policyTransition M πs)⁻¹ *ᵥ u) := ⟨_, fun _ ↦ rfl⟩
  have hLmono : ∀ u v : Fin s → ℝ, (∀ i, u i ≤ v i) → L u ≤ L v := fun u v huv ↦ by
    rw [hL, hL]
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (inv_one_sub_smul_mulVec_mono _ hPs hPs1 _ hg huv i) (hρ.1 i)
  have hLadd : ∀ u v, L (u + v) = L u + L v := fun u v ↦ by
    simp only [hL, Matrix.mulVec_add, dotProduct_add]
  have hLsub : ∀ u v, L (u - v) = L u - L v := fun u v ↦ by
    simp only [hL, Matrix.mulVec_sub, dotProduct_sub]
  have hLsmul : ∀ (c : ℝ) u, L (c • u) = c * L u := fun c u ↦ by
    simp only [hL, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hLconst : ∀ c : ℝ, L (fun _ ↦ c) = c / (1 - M.discount) := fun c ↦ by
    rw [hL, inv_one_sub_smul_mulVec_const _ hPs hPs1 _ hg]
    simp only [dotProduct, ← Finset.sum_mul, hρ.2, one_mul]
  -- the potential
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Fin s → ℝ, ∀ t i, D t i = ∑ b, πs i b * Real.log (π t i b) :=
    ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, ∀ t,
      Φ t = (1 - M.discount) / η * L (D t) + L (policyValue M (π t)) := ⟨_, fun _ ↦ rfl⟩
  have hJ : ∀ t, policyObjective M ρ πs - policyObjective M ρ (π t) =
      L (fun i ↦ ∑ b, πs i b * policyAdvantage M (π t) i b) := by
    intro t
    rw [hL, ← policyValue_sub_eq M hπs]
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
  have hD0 : D 0 = fun _ ↦ -Real.log a := by
    funext i
    simp only [hD, h0, Real.log_inv, ← Finset.sum_mul, hπs.2 i, one_mul]
  have hVT : L (policyValue M (π T)) ≤ 1 / (1 - M.discount) / (1 - M.discount) := by
    rw [← hLconst]
    exact hLmono _ _ fun i ↦ (policyValue_mem_Icc M hr (hst T) i).2
  have hV0 : 0 ≤ L (policyValue M (π 0)) := by
    have := hLmono (fun _ ↦ 0) _ fun i ↦ (policyValue_mem_Icc M hr (hst 0) i).1
    rwa [hLconst, zero_div] at this
  have hΦb : Φ T - Φ 0 ≤ Real.log a / η + 1 / (1 - M.discount) ^ 2 := by
    rw [hΦ, hΦ, hD0, hLconst]
    have hfac : (1 - M.discount) / η * (-Real.log a / (1 - M.discount)) = -(Real.log a / η) := by
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
      (Real.log a / η + 1 / (1 - M.discount) ^ 2) / T := by
    rw [le_div_iff₀ hTpos]
    linarith
  have heq : (Real.log a / η + 1 / (1 - M.discount) ^ 2) / T =
      Real.log a / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
    rw [add_div, div_div, div_div]
  rw [← heq]
  exact hfin

/-- GAPS 107.61: convergence of natural policy gradient with softmax policies from `θ = 0`, for
rewards in `[0,1]`, any initial law `ρ`, and any step `η > 0` (Agarwal–Kakade–Lee–Mahajan):
`J⋆(ρ) - J(π⁽ᵀ⁾) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem optimalObjective_sub_npg_le (M : FiniteMarkovDecisionProcess s a) (ha : 0 < a)
    (hr : ∀ i b, M.reward i b ∈ Icc 0 1) (ρ : Fin s → ℝ)
    (hρ : (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1)
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T) :
    optimalObjective M ρ - policyObjective M ρ (naturalPolicyGradientIterate M η T) ≤
      Real.log a / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
  have hbound : ∀ πs, IsStationaryPolicy πs →
      policyObjective M ρ πs - policyObjective M ρ (naturalPolicyGradientIterate M η T) ≤
        Real.log a / (η * T) + 1 / ((1 - M.discount) ^ 2 * T) := by
    intro πs hπs
    refine policyObjective_sub_le_of_log_update M hr ρ hρ η hη
      (naturalPolicyGradientIterate M η)
      (fun t i ↦ ∑ b', naturalPolicyGradientIterate M η t i b' * Real.exp
        (η * policyAdvantage M (naturalPolicyGradientIterate M η t) i b' / (1 - M.discount)))
      (fun t ↦ (naturalPolicyGradientIterate_pos M ha η t).1)
      (fun t ↦ (naturalPolicyGradientIterate_pos M ha η t).2) (fun _ _ ↦ rfl)
      (fun t i ↦ one_le_sum_mul_exp_policyAdvantage M
        (isStationaryPolicy_naturalPolicyGradientIterate M ha η t) η i)
      (fun t i b ↦ ?_) T hT hπs
    rw [log_naturalPolicyGradientIterate_succ M ha η t i b]
    have h1γ : (1 - M.discount) ≠ 0 := (sub_pos.mpr M.discount_lt_one).ne'
    field_simp
    ring
  have hne : ((policyObjective M ρ) '' {π | IsStationaryPolicy π}).Nonempty :=
    ⟨_, naturalPolicyGradientIterate M η 0,
      isStationaryPolicy_naturalPolicyGradientIterate M ha η 0, rfl⟩
  rw [sub_le_iff_le_add, optimalObjective]
  refine csSup_le hne ?_
  rintro _ ⟨πs, hπs, rfl⟩
  have := hbound πs hπs
  linarith

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
