module

public import CKSD.Learning.Basic
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Topology.MetricSpace.Contracting


/-!
# Finite discounted Markov decision processes

A finite discounted Markov decision process has a finite state space `S`, an action set `A`, a
discount `γ ∈ (0,1)`, expected rewards `r(i,b)` and row-stochastic transition probabilities
`P(j | i,b)`. Value functions are real functions on `S` with the sup norm.

## Main definitions

* `CKSD.FiniteMarkovDecisionProcess`: the model.
* `CKSD.bellmanOperator`: the Bellman optimality operator
  `(TV)(i) = max_b (r(i,b) + γ ∑ⱼ P(j | i,b) V(j))`.
* `CKSD.optimalStateValue`: its unique fixed point, the optimal value function.

## Main results

* `CKSD.bellman_operator_contracting_with`: `T` is a `γ`-contraction in the sup norm.
* `CKSD.bellman_operator_optimal_state_value`, `CKSD.exists_greedy_optimal_state_value`,
  `CKSD.optimal_state_value_le_of_forall_le`, `CKSD.sum_mul_optimal_state_value_le`,
  `CKSD.sum_mul_optimal_state_value_eq_iff`: Bellman optimality, existence of a greedy stationary
  deterministic policy, and the primal linear program `min ∑ ρ U` over superharmonic `U`,
  whose unique minimizer for positive weights is the optimal value (GAPS 107.58).
* `CKSD.is_unit_one_sub_smul_of_mem_row_stochastic` and the resolvent lemmas: for a
  row-stochastic `H` and `0 ≤ γ < 1` the resolvent `(I - γH)⁻¹` exists, is positive and
  monotone, and has sup-norm at most `1/(1-γ)`.
* `CKSD.inv_one_sub_smul_mul_vec_sub_eq`, `CKSD.norm_inv_one_sub_smul_mul_vec_sub_le`: the
  resolvent identity comparing the values of two transition matrices (GAPS 107.59).
* `CKSD.norm_projected_fixed_point_sub_le`: the projected fixed-point error bound behind
  TD(λ) (GAPS 107.60).
* `CKSD.ae_tendsto_asynchronous_stochastic_approximation`: asynchronous stochastic
  approximation for a sup-norm contraction, the convergence theorem behind tabular Q-learning
  (GAPS 107.54).

## Conventions

The Bellman operator uses the real `⨆` over actions, which is `0` for an empty action set; all
results assume a nonempty finite action set, where the supremum is a maximum. Row-stochastic
matrices are Mathlib's `Matrix.rowStochastic`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix

namespace CKSD

/-- A finite discounted Markov decision process on the finite state space `S` with actions `A`. -/
structure FiniteMarkovDecisionProcess (S A : Type*) [Fintype S] where
  /-- Discount factor `γ`. -/
  discount : ℝ
  /-- The discount is positive. -/
  discount_pos : 0 < discount
  /-- The discount is smaller than one. -/
  discount_lt_one : discount < 1
  /-- Expected one-step reward `r(i,b)`. -/
  reward : S → A → ℝ
  /-- Transition probabilities `P(j | i,b)`. -/
  transition : S → A → S → ℝ
  /-- Transition probabilities are nonnegative. -/
  transition_nonneg : ∀ i b j, 0 ≤ transition i b j
  /-- Transition rows sum to one. -/
  sum_transition_eq_one : ∀ i b, ∑ j, transition i b j = 1

variable {S A : Type*} [Fintype S]

/-- The discount of a finite model lies in the open unit interval. -/
theorem FiniteMarkovDecisionProcess.discount_mem_ioo (M : FiniteMarkovDecisionProcess S A) :
    M.discount ∈ Ioo 0 1 :=
  ⟨M.discount_pos, M.discount_lt_one⟩

/-- The Bellman optimality operator `(TV)(i) = ⨆_b (r(i,b) + γ ∑ⱼ P(j | i,b) V(j))`. The real
supremum is a maximum for a nonempty finite action set (and `0` for an empty one). -/
def bellmanOperator (M : FiniteMarkovDecisionProcess S A) (V : S → ℝ) (i : S) : ℝ :=
  ⨆ b : A, M.reward i b + M.discount * ∑ j, M.transition i b j * V j

/-- A probability average of values bounded by `c` is bounded by `c`. -/
theorem sum_mul_le_of_sum_eq_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (v : ι → ℝ) (c : ℝ) (hv : ∀ j, v j ≤ c) : ∑ j, p j * v j ≤ c := by
  calc ∑ j, p j * v j ≤ ∑ j, p j * c := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hv j) (hp j)
    _ = c := by rw [← Finset.sum_mul, hp1, one_mul]

/-- Pointwise domination up to `c` passes to suprema over a nonempty finite index. -/
private theorem ci_sup_le_ci_sup_add {ι : Type*} [Finite ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ)
    (h : ∀ b, f b ≤ g b + c) : ⨆ b, f b ≤ (⨆ b, g b) + c :=
  ciSup_le fun b ↦ (h b).trans (by linarith [le_ciSup (finite_range g).bddAbove b])

section Bellman

variable [Fintype A] [Nonempty A] (M : FiniteMarkovDecisionProcess S A)

/-- The Bellman optimality operator is a `γ`-contraction for the sup norm. -/
theorem bellman_operator_contracting_with :
    ContractingWith (⟨M.discount, M.discount_pos.le⟩ : ℝ≥0) (bellmanOperator M) := by
  set γ := M.discount
  have hstep : ∀ (V U : S → ℝ) (i : S) (b : A),
      M.reward i b + γ * ∑ j, M.transition i b j * V j ≤
        (M.reward i b + γ * ∑ j, M.transition i b j * U j) + γ * ‖V - U‖ := by
    intro V U i b
    have h : ∑ j, M.transition i b j * (V - U) j ≤ ‖V - U‖ :=
      sum_mul_le_of_sum_eq_one _ (M.transition_nonneg i b) (M.sum_transition_eq_one i b) _ _
        fun j ↦ (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (V - U) j)
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h
    nlinarith [M.discount_pos]
  refine ⟨NNReal.coe_lt_coe.mp (by rw [NNReal.coe_one]; exact M.discount_lt_one),
    LipschitzWith.of_dist_le_mul fun V U ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ M.discount * _
  refine (pi_norm_le_iff_of_nonneg (by positivity [M.discount_pos])).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.sub_apply, bellmanOperator]
  constructor
  · have := ci_sup_le_ci_sup_add _ _ _ fun b ↦ hstep U V i b
    rw [norm_sub_rev] at this
    linarith
  · have := ci_sup_le_ci_sup_add _ _ _ fun b ↦ hstep V U i b
    linarith

/-- The optimal value function: the unique fixed point of the Bellman optimality operator. -/
def optimalStateValue : S → ℝ :=
  ContractingWith.fixedPoint (bellmanOperator M) (bellman_operator_contracting_with M)

/-- GAPS 107.58, Bellman optimality: the optimal value function is a fixed point of the Bellman
optimality operator (and it is the only one, by the contraction property). -/
theorem bellman_operator_optimal_state_value :
    bellmanOperator M (optimalStateValue M) = optimalStateValue M :=
  ContractingWith.fixedPoint_isFixedPt _

/-- GAPS 107.58, greedy policy: some stationary deterministic policy `π` attains the maximum in
the Bellman equation at every state, `V⋆(i) = r(i,π i) + γ ∑ⱼ P(j | i,π i) V⋆(j)`. -/
theorem exists_greedy_optimal_state_value : ∃ pi : S → A, ∀ i,
    optimalStateValue M i = M.reward i (pi i) +
      M.discount * ∑ j, M.transition i (pi i) j * optimalStateValue M j := by
  choose pi hpi using fun i ↦ exists_eq_ciSup_of_finite (ι := A)
    (f := fun b ↦ M.reward i b + M.discount * ∑ j, M.transition i b j * optimalStateValue M j)
  refine ⟨pi, fun i ↦ ?_⟩
  rw [hpi i]
  exact (congrFun (bellman_operator_optimal_state_value M) i).symm

/-- GAPS 107.58, primal linear program: every superharmonic `U`, that is
`r(i,b) + γ ∑ⱼ P(j | i,b) U(j) ≤ U(i)` for all `i, b`, dominates the optimal value. -/
theorem optimal_state_value_le_of_forall_le {U : S → ℝ}
    (hU : ∀ i b, M.reward i b + M.discount * ∑ j, M.transition i b j * U j ≤ U i) (i : S) :
    optimalStateValue M i ≤ U i := by
  obtain ⟨pi, hpi⟩ := exists_greedy_optimal_state_value M
  set V := optimalStateValue M
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i ↦ V i - U i)
    ⟨i, Finset.mem_univ _⟩
  have hk' : ∀ j, V j - U j ≤ V k - U k := fun j ↦ hk j (Finset.mem_univ _)
  have hsum := sum_mul_le_of_sum_eq_one _ (M.transition_nonneg k (pi k))
    (M.sum_transition_eq_one k (pi k)) (fun j ↦ V j - U j) _ hk'
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  have h1 := hpi k
  have h2 := hU k (pi k)
  have hγ0 := M.discount_pos
  have hγ1 := M.discount_lt_one
  have hm : V k - U k ≤ M.discount * (V k - U k) := by nlinarith
  have hm0 : V k - U k ≤ 0 := by nlinarith
  linarith [hk' i]

/-- GAPS 107.58, primal linear program: for nonnegative weights `ρ`, the optimal value
minimizes `∑ ρ U` over superharmonic `U`. -/
theorem sum_mul_optimal_state_value_le {ρ : S → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {U : S → ℝ}
    (hU : ∀ i b, M.reward i b + M.discount * ∑ j, M.transition i b j * U j ≤ U i) :
    ∑ i, ρ i * optimalStateValue M i ≤ ∑ i, ρ i * U i :=
  Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_left (optimal_state_value_le_of_forall_le M hU i) (hρ i)

/-- GAPS 107.58, primal linear program: for positive weights `ρ`, the optimal value is the
unique minimizer of `∑ ρ U` over superharmonic `U`. -/
theorem sum_mul_optimal_state_value_eq_iff {ρ : S → ℝ} (hρ : ∀ i, 0 < ρ i) {U : S → ℝ}
    (hU : ∀ i b, M.reward i b + M.discount * ∑ j, M.transition i b j * U j ≤ U i) :
    ∑ i, ρ i * optimalStateValue M i = ∑ i, ρ i * U i ↔ optimalStateValue M = U := by
  refine ⟨fun heq ↦ ?_, fun h ↦ by rw [h]⟩
  have hle := optimal_state_value_le_of_forall_le M hU
  have hz : ∑ i, ρ i * (U i - optimalStateValue M i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]; linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
    mul_nonneg (hρ i).le (sub_nonneg.mpr (hle i))).mp hz
  funext i
  rcases mul_eq_zero.mp (hz' i (Finset.mem_univ _)) with h | h
  · exact absurd h (hρ i).ne'
  · linarith

end Bellman

/-! ### Resolvents of row-stochastic matrices -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ}
  (hH : H ∈ Matrix.rowStochastic ℝ n) {γ : ℝ}
include hH

/-- A row-stochastic matrix does not increase the sup norm. -/
theorem norm_mul_vec_le_of_mem_row_stochastic (v : n → ℝ) : ‖H *ᵥ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  calc |∑ j, H i j * v j| ≤ ∑ j, |H i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, H i j * ‖v‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hH)]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j)
          (Matrix.nonneg_of_mem_rowStochastic hH)
    _ = ‖v‖ := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hH, one_mul]

variable (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hγ0 hγ1

/-- Resolvent bound `‖x‖ ≤ ‖(I - γH)x‖ / (1 - γ)` for a row-stochastic `H` and `0 ≤ γ < 1`. -/
theorem norm_le_norm_one_sub_smul_mul_vec_div (x : n → ℝ) :
    ‖x‖ ≤ ‖(1 - γ • H) *ᵥ x‖ / (1 - γ) := by
  have hx : x = (1 - γ • H) *ᵥ x + γ • (H *ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]; abel
  have h1 : ‖x‖ ≤ ‖(1 - γ • H) *ᵥ x‖ + γ * ‖x‖ := by
    calc ‖x‖ = ‖(1 - γ • H) *ᵥ x + γ • (H *ᵥ x)‖ := by rw [← hx]
      _ ≤ ‖(1 - γ • H) *ᵥ x‖ + ‖γ • (H *ᵥ x)‖ := norm_add_le _ _
      _ ≤ ‖(1 - γ • H) *ᵥ x‖ + γ * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (norm_mul_vec_le_of_mem_row_stochastic hH x) hγ0)
  rw [le_div_iff₀ (sub_pos.mpr hγ1)]
  linarith

/-- `I - γH` is invertible for a row-stochastic `H` and `0 ≤ γ < 1`. -/
theorem is_unit_one_sub_smul_of_mem_row_stochastic : IsUnit (1 - γ • H) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h := norm_le_norm_one_sub_smul_mul_vec_div hH hγ0 hγ1 (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The resolvent `(I - γH)⁻¹` is a right inverse on vectors. -/
theorem one_sub_smul_mul_vec_inv_mul_vec (v : n → ℝ) :
    (1 - γ • H) *ᵥ ((1 - γ • H)⁻¹ *ᵥ v) = v := by
  have hd : IsUnit (1 - γ • H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (is_unit_one_sub_smul_of_mem_row_stochastic hH hγ0 hγ1)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

/-- The resolvent `(I - γH)⁻¹` is a left inverse on vectors. -/
theorem inv_one_sub_smul_mul_vec_mul_vec (v : n → ℝ) :
    (1 - γ • H)⁻¹ *ᵥ ((1 - γ • H) *ᵥ v) = v := by
  have hd : IsUnit (1 - γ • H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (is_unit_one_sub_smul_of_mem_row_stochastic hH hγ0 hγ1)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

/-- For a row-stochastic `H`, the resolvent `(I - γH)⁻¹` dominates the identity on
nonnegative vectors: `v ≤ (I - γH)⁻¹ v`; in particular the resolvent is positive. -/
theorem le_inv_one_sub_smul_mul_vec {v : n → ℝ} (hv : ∀ i, 0 ≤ v i) (i : n) :
    v i ≤ ((1 - γ • H)⁻¹ *ᵥ v) i := by
  set w := (1 - γ • H)⁻¹ *ᵥ v
  have hw : ∀ j, w j = v j + γ * (H *ᵥ w) j := by
    intro j
    have := congrFun (one_sub_smul_mul_vec_inv_mul_vec hH hγ0 hγ1 v) j
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hpos : ∀ j, 0 ≤ w j := by
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ w ⟨i, Finset.mem_univ _⟩
    have hk' : ∀ j, w k ≤ w j := fun j ↦ hk j (Finset.mem_univ _)
    have hHw : w k ≤ (H *ᵥ w) k := by
      have := sum_mul_le_of_sum_eq_one (H k) (fun j ↦ Matrix.nonneg_of_mem_rowStochastic hH)
        (Matrix.sum_row_of_mem_rowStochastic hH k) (fun j ↦ -w j) (-w k)
        fun j ↦ neg_le_neg (hk' j)
      simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at this
      exact this
    have h1 := hw k
    have h2 := hv k
    have hwk : 0 ≤ w k := by nlinarith
    exact fun j ↦ hwk.trans (hk' j)
  have hHw : 0 ≤ (H *ᵥ w) i := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hH) (hpos j)
  rw [hw i]
  nlinarith

/-- The resolvent `(I - γH)⁻¹` is monotone on vectors for a row-stochastic `H`. -/
theorem inv_one_sub_smul_mul_vec_mono {u v : n → ℝ} (huv : ∀ i, u i ≤ v i) (i : n) :
    ((1 - γ • H)⁻¹ *ᵥ u) i ≤ ((1 - γ • H)⁻¹ *ᵥ v) i := by
  have h := le_inv_one_sub_smul_mul_vec hH hγ0 hγ1 (v := v - u)
    (fun j ↦ sub_nonneg.mpr (huv j)) i
  have h0 : 0 ≤ (v - u) i := sub_nonneg.mpr (huv i)
  rw [Matrix.mulVec_sub, Pi.sub_apply] at h
  rw [Pi.sub_apply] at h0 h
  linarith

/-- The resolvent `(I - γH)⁻¹` maps the constant `c` to the constant `c / (1 - γ)`. -/
theorem inv_one_sub_smul_mul_vec_const (c : ℝ) :
    (1 - γ • H)⁻¹ *ᵥ (fun _ ↦ c) = fun _ ↦ c / (1 - γ) := by
  have h1 : (1 - γ) ≠ 0 := (sub_pos.mpr hγ1).ne'
  have : (1 - γ • H) *ᵥ (fun _ : n ↦ c / (1 - γ)) = fun _ ↦ c := by
    funext i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hH, one_mul]
    field_simp
  rw [← this, inv_one_sub_smul_mul_vec_mul_vec hH hγ0 hγ1]

omit hγ0 hγ1 in
/-- GAPS 107.59, resolvent identity: for row-stochastic `P, H` and `0 ≤ γ < 1`, the values
`V = (I - γP)⁻¹ r` and `W = (I - γH)⁻¹ r` satisfy `V - W = γ (I - γH)⁻¹ (P - H) V`. -/
theorem inv_one_sub_smul_mul_vec_sub_eq {P : Matrix n n ℝ} (hP : P ∈ Matrix.rowStochastic ℝ n)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : n → ℝ) :
    (1 - γ • P)⁻¹ *ᵥ r - (1 - γ • H)⁻¹ *ᵥ r =
      γ • (1 - γ • H)⁻¹ *ᵥ ((P - H) *ᵥ ((1 - γ • P)⁻¹ *ᵥ r)) := by
  set V := (1 - γ • P)⁻¹ *ᵥ r
  have hkey : (1 - γ • H) *ᵥ (V - (1 - γ • H)⁻¹ *ᵥ r) = γ • ((P - H) *ᵥ V) := by
    rw [Matrix.mulVec_sub, one_sub_smul_mul_vec_inv_mul_vec hH hγ0 hγ1,
      ← one_sub_smul_mul_vec_inv_mul_vec hP hγ0 hγ1 r]
    simp only [V, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_sub]
    abel
  have := congrArg (fun v ↦ (1 - γ • H)⁻¹ *ᵥ v) hkey
  simp only [inv_one_sub_smul_mul_vec_mul_vec hH hγ0 hγ1, Matrix.mulVec_smul] at this
  rw [this]

omit hγ0 hγ1 in
/-- GAPS 107.59, sup-norm error bound: with `V = (I - γP)⁻¹ r` and `W = (I - γH)⁻¹ r` for
row-stochastic `P, H` and `0 ≤ γ < 1`, `‖V - W‖ ≤ γ/(1-γ) ‖(P - H) V‖`. -/
theorem norm_inv_one_sub_smul_mul_vec_sub_le {P : Matrix n n ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ n) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : n → ℝ) :
    ‖(1 - γ • P)⁻¹ *ᵥ r - (1 - γ • H)⁻¹ *ᵥ r‖ ≤
      γ / (1 - γ) * ‖(P - H) *ᵥ ((1 - γ • P)⁻¹ *ᵥ r)‖ := by
  have hb := norm_le_norm_one_sub_smul_mul_vec_div hH hγ0 hγ1
    ((1 - γ • P)⁻¹ *ᵥ r - (1 - γ • H)⁻¹ *ᵥ r)
  rw [inv_one_sub_smul_mul_vec_sub_eq hH hP hγ0 hγ1] at hb ⊢
  rw [Matrix.mulVec_smul, one_sub_smul_mul_vec_inv_mul_vec hH hγ0 hγ1, norm_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hγ0] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
  calc _ ≤ _ := hb
    _ = _ := by ring

end Resolvent

/-- GAPS 107.60, the deterministic error bound underlying TD(λ): if `P` is a norm contraction,
`T` is Lipschitz with constant `γ(1-λ)/(1-γλ)` for `γ ∈ (0,1)` and `λ ≤ 1`, `V` is the fixed
point of `T` and `w` the fixed point of `P ∘ T`, then
`‖w - V‖ ≤ (1-γλ)/(1-γ) ‖PV - V‖`. -/
theorem norm_projected_fixed_point_sub_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H →L[ℝ] H) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (gamma lambda : ℝ) (hg : gamma ∈ Ioo 0 1) (hl : lambda ≤ 1)
    (T : H → H)
    (hc : ∀ x y, ‖T x - T y‖ ≤ gamma * (1 - lambda) / (1 - gamma * lambda) * ‖x - y‖)
    (V w : H) (hV : T V = V) (hw : P (T w) = w) :
    ‖w - V‖ ≤ (1 - gamma * lambda) / (1 - gamma) * ‖P V - V‖ := by
  have hd : 0 < 1 - gamma * lambda := by nlinarith [mul_le_mul_of_nonneg_left hl hg.1.le, hg.2]
  have hmain : ‖w - V‖ ≤ gamma * (1 - lambda) / (1 - gamma * lambda) * ‖w - V‖ +
      ‖P V - V‖ := by
    calc
      ‖w - V‖ = ‖P (T w) - V‖ := by rw [hw]
      _ ≤ ‖P (T w) - P V‖ + ‖P V - V‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖T w - V‖ + ‖P V - V‖ := by
        rw [← map_sub]
        exact add_le_add (hP _) le_rfl
      _ ≤ gamma * (1 - lambda) / (1 - gamma * lambda) * ‖w - V‖ + ‖P V - V‖ :=
        add_le_add (by simpa [hV] using hc w V) le_rfl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hg.2)).mpr
  have hm := mul_le_mul_of_nonneg_right hmain hd.le
  have hcancel : gamma * (1 - lambda) / (1 - gamma * lambda) * ‖w - V‖ *
      (1 - gamma * lambda) = gamma * (1 - lambda) * ‖w - V‖ := by field_simp
  rw [add_mul, hcancel] at hm
  nlinarith

/-- GAPS 107.54, asynchronous stochastic approximation (Tsitsiklis; Jaakkola–Jordan–Singh):
let `T` be a `γ`-contraction of `ℝ^ι` in the sup norm with fixed point `x⋆`, and let
`Qₙ₊₁(i) = (1 - αₙ(i)) Qₙ(i) + αₙ(i) (T(Qₙ)(i) + Eₙ(i))` with `𝓕ₙ`-measurable steps
`αₙ(i) ∈ [0,1]`, `∑ₙ αₙ(i) = ∞`, `∑ₙ αₙ(i)² < ∞` almost surely, and martingale-difference noise
`Eₙ` with bounded conditional second moments. Then `Qₙ → x⋆` almost surely. Tabular
Q-learning is the case of the Bellman operator on state-action pairs, with steps only on the
visited pair. -/
theorem ae_tendsto_asynchronous_stochastic_approximation {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : (ι → ℝ) → (ι → ℝ)) (gamma : ℝ≥0) (hg : gamma < 1)
    (hc : LipschitzWith gamma T) (star : ι → ℝ) (hstar : T star = star)
    (Q E alpha : ℕ → Ω → ι → ℝ)
    (hQ : ∀ n, Measurable[F n] (Q n)) (hE : ∀ n, Measurable[F (n + 1)] (E n))
    (ha : ∀ n, Measurable[F n] (alpha n)) (ha01 : ∀ n ω i, alpha n ω i ∈ Icc 0 1)
    (hE2 : ∀ n i, MemLp (fun ω ↦ E n ω i) 2 P)
    (hE0 : ∀ n i, P[(fun ω ↦ E n ω i) | F n] =ᵐ[P] fun _ ↦ 0)
    (C : ℝ) (hvar : ∀ n i, P[(fun ω ↦ E n ω i ^ 2) | F n] ≤ᵐ[P] fun _ ↦ C)
    (hsteps : ∀ i, ∀ᵐ ω ∂P, Summable (fun n ↦ alpha n ω i ^ 2) ∧
      Tendsto (fun n ↦ ∑ t ∈ Finset.range n, alpha t ω i) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂P, ∀ i, Q (n + 1) ω i =
      (1 - alpha n ω i) * Q n ω i + alpha n ω i * (T (Q n ω) i + E n ω i)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ Q n ω) atTop (𝓝 star) := by
  sorry

end CKSD
