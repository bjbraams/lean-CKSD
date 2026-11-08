module

public import CKSD.Learning.Basic
public import CKSD.Learning.UCBAnalysis
public import Mathlib.Analysis.Real.Pi.Bounds
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic

/-!
# Learning: Sequential

Sources: `GAPS.md`, `SYNOPSIS107.md`, and `STRUCTURE107.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator Matrix

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 107.50: UCB1 regret, with prefix rewards and all tie choices explicit. -/
theorem ucb_regret_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (R : Fin K → ℕ → Ω → ℝ) (hm : ∀ i j, Measurable (R i j))
    (hb : ∀ i j ω, R i j ω ∈ Icc 0 1)
    (hind : iIndepFun (fun z : Fin K × ℕ ↦ R z.1 z.2) P)
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0)) :
    let mu := fun i ↦ ∫ ω, R i 0 ω ∂P;
    ∀ (star : Fin K),
    ∀ (hstar : ∀ i, mu i ≤ mu star),
    ∀ (A : ℕ → Ω → Fin K),
    ∀ (hA : ∀ t, Measurable (A t)),
    ∀ (hinit : ∀ t : ℕ, ∀ ht : t < K, ∀ ω, A t ω = ⟨t, ht⟩),
    let index := fun t i ω ↦ armSampleAverage R i (armPlayCount A i t ω) ω +
      Real.sqrt (2 * Real.log t / armPlayCount A i t ω);
    ∀ (hucb : ∀ t ≥ K, ∀ ω i, index t i ω ≤ index t (A t ω) ω),
    ∀ (T : ℕ),
    (∫ ω, ∑ t ∈ Finset.range T, (mu star - mu (A t ω)) ∂P) ≤
      8 * (∑ i, if mu i < mu star then Real.log T / (mu star - mu i) else 0) +
        (1 + Real.pi ^ 2 / 3) * ∑ i, (mu star - mu i) := by
  intro mu star hstar A hA hinit index hucb T
  have hb' : ∀ i j, ∀ᵐ ω ∂P, R i j ω ∈ Icc 0 1 := fun i j ↦ ae_of_all _ (hb i j)
  have hpt : ∀ ω, ∑ t ∈ Finset.range T, (mu star - mu (A t ω)) =
      ∑ i, (mu star - mu i) * (armPlayCount A i T ω : ℝ) := fun ω ↦
    sum_range_comp_eq_sum_mul_armPlayCount A (fun i ↦ mu star - mu i) T ω
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ ↦ (integrable_armPlayCount P A hA i T).const_mul _,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [integral_const_mul]
  have hπ : (3 : ℝ) ≤ 1 + Real.pi ^ 2 / 3 := by nlinarith [Real.pi_gt_three]
  have hΔnn : 0 ≤ mu star - mu i := sub_nonneg.mpr (hstar i)
  split_ifs with hlt
  · have hcount := integral_armPlayCount_le_of_ucb P R hm hb' hind hlaw A hinit hucb hlt T
    have hΔ : 0 < mu star - mu i := sub_pos.mpr hlt
    calc (mu star - mu i) * ∫ ω, (armPlayCount A i T ω : ℝ) ∂P
        ≤ (mu star - mu i) * (8 * Real.log T / (mu star - mu i) ^ 2 + 3) :=
          mul_le_mul_of_nonneg_left hcount hΔnn
      _ = 8 * (Real.log T / (mu star - mu i)) + 3 * (mu star - mu i) := by
          field_simp
      _ ≤ _ := by nlinarith
  · have : mu star - mu i = 0 := by linarith [not_lt.mp hlt, hstar i]
    rw [this]
    simp

/-- GAPS 107.54, bounded-noise asynchronous stochastic approximation for a contraction.
The tabular Q-learning application uses the Bellman operator and visited-pair steps. -/
theorem ae_tendsto_asynchronous_stochastic_approximation {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : (Fin p → ℝ) → (Fin p → ℝ)) (gamma : ℝ≥0) (hg : gamma < 1)
    (hc : LipschitzWith gamma T) (star : Fin p → ℝ) (hstar : T star = star)
    (Q E alpha : ℕ → Ω → Fin p → ℝ)
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

/-- Pointwise domination up to `c` passes to suprema over a nonempty finite index. -/
theorem sSup_range_le_add {a : ℕ} (ha : 0 < a) (f g : Fin a → ℝ) (c : ℝ)
    (h : ∀ b, f b ≤ g b + c) : sSup (range f) ≤ sSup (range g) + c := by
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  refine csSup_le (range_nonempty f) ?_
  rintro _ ⟨b, rfl⟩
  exact (h b).trans (by linarith [le_csSup (finite_range g).bddAbove (⟨b, rfl⟩ : g b ∈ range g)])

/-- The supremum over a nonempty finite index is attained. -/
theorem exists_eq_sSup_range {a : ℕ} (ha : 0 < a) (f : Fin a → ℝ) :
    ∃ b, sSup (range f) = f b := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ f ⟨⟨0, ha⟩, Finset.mem_univ _⟩
  refine ⟨k, le_antisymm ?_ (le_csSup (finite_range f).bddAbove ⟨k, rfl⟩)⟩
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact csSup_le (range_nonempty f) (by rintro _ ⟨i, rfl⟩; exact hk i (Finset.mem_univ _))

/-- A probability average of values bounded by `c` is bounded by `c`. -/
theorem sum_mul_le_of_stochastic {s : ℕ} (p : Fin s → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (v : Fin s → ℝ) (c : ℝ) (hv : ∀ j, v j ≤ c) : ∑ j, p j * v j ≤ c := by
  calc ∑ j, p j * v j ≤ ∑ j, p j * c := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hv j) (hp j)
    _ = c := by rw [← Finset.sum_mul, hp1, one_mul]

/-- GAPS 107.58, Bellman optimality, a greedy stationary policy, and the primal LP. -/
theorem exists_bellman_fixed_point_and_greedy_policy
    {s a : ℕ} (ha : 0 < a) (M : FiniteMarkovDecisionProcess s a) :
    ∃ V : Fin s → ℝ, bellmanOperator M V = V ∧
      (∃ pi : Fin s → Fin a, ∀ i,
        V i = M.reward i (pi i) + M.discount * ∑ j, M.transition i (pi i) j * V j) ∧
      (∀ U : Fin s → ℝ, (∀ i b,
        M.reward i b + M.discount * ∑ j, M.transition i b j * U j ≤ U i) → ∀ i, V i ≤ U i) ∧
      ∀ rho : Fin s → ℝ, (∀ i, 0 < rho i) → ∀ U : Fin s → ℝ,
        (∀ i b, M.reward i b + M.discount * ∑ j, M.transition i b j * U j ≤ U i) →
        (∑ i, rho i * V i) ≤ (∑ i, rho i * U i) ∧
          ((∑ i, rho i * V i) = (∑ i, rho i * U i) ↔ V = U) := by
  set γ := M.discount
  have hγ0 := M.discount_pos
  have hγ1 := M.discount_lt_one
  -- one-step dependence on `V`
  have hstep : ∀ (V U : Fin s → ℝ) (i : Fin s) (b : Fin a),
      M.reward i b + γ * ∑ j, M.transition i b j * V j ≤
        (M.reward i b + γ * ∑ j, M.transition i b j * U j) + γ * ‖V - U‖ := by
    intro V U i b
    have h : ∑ j, M.transition i b j * (V - U) j ≤ ‖V - U‖ :=
      sum_mul_le_of_stochastic _ (M.transition_nonneg i b) (M.sum_transition_eq_one i b) _ _ fun j ↦
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (V - U) j)
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h
    nlinarith
  let K : ℝ≥0 := ⟨γ, hγ0.le⟩
  have hK : (K : ℝ) = γ := rfl
  have hlip : LipschitzWith K (bellmanOperator M) := by
    refine LipschitzWith.of_dist_le_mul fun V U ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, hK]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.sub_apply, bellmanOperator]
    constructor
    · have := sSup_range_le_add ha _ _ _ fun b ↦ hstep U V i b
      rw [norm_sub_rev] at this
      linarith
    · have := sSup_range_le_add ha _ _ _ fun b ↦ hstep V U i b
      linarith
  have hcon : ContractingWith K (bellmanOperator M) :=
    ⟨by rw [← NNReal.coe_lt_coe, hK, NNReal.coe_one]; exact hγ1, hlip⟩
  set V := ContractingWith.fixedPoint (bellmanOperator M) hcon
  have hV : bellmanOperator M V = V := ContractingWith.fixedPoint_isFixedPt hcon
  have hgreedy : ∃ pi : Fin s → Fin a, ∀ i,
      V i = M.reward i (pi i) + γ * ∑ j, M.transition i (pi i) j * V j := by
    choose pi hpi using fun i ↦ exists_eq_sSup_range ha
      (fun b ↦ M.reward i b + γ * ∑ j, M.transition i b j * V j)
    refine ⟨pi, fun i ↦ ?_⟩
    rw [← hpi i]
    exact (congrFun hV i).symm
  obtain ⟨pi, hpi⟩ := hgreedy
  have hmin : ∀ U : Fin s → ℝ, (∀ i b,
      M.reward i b + γ * ∑ j, M.transition i b j * U j ≤ U i) → ∀ i, V i ≤ U i := by
    intro U hU i
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i ↦ V i - U i)
      ⟨i, Finset.mem_univ _⟩
    have hk' : ∀ j, V j - U j ≤ V k - U k := fun j ↦ hk j (Finset.mem_univ _)
    have hsum := sum_mul_le_of_stochastic _ (M.transition_nonneg k (pi k)) (M.sum_transition_eq_one k (pi k))
      (fun j ↦ V j - U j) _ hk'
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    have h1 := hpi k
    have h2 := hU k (pi k)
    have hm : V k - U k ≤ γ * (V k - U k) := by nlinarith
    have hm0 : V k - U k ≤ 0 := by nlinarith
    linarith [hk' i]
  refine ⟨V, hV, ⟨pi, hpi⟩, hmin, fun rho hrho U hU ↦ ?_⟩
  have hle := hmin U hU
  have hsum : (∑ i, rho i * V i) ≤ ∑ i, rho i * U i :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) (hrho i).le
  refine ⟨hsum, ⟨fun heq ↦ ?_, fun h ↦ by rw [h]⟩⟩
  have hz : ∑ i, rho i * (U i - V i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]; linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
    mul_nonneg (hrho i).le (sub_nonneg.mpr (hle i))).mp hz
  funext i
  have := hz' i (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (hrho i).ne'
  · linarith

/-- A row-stochastic matrix does not increase the sup norm. -/
theorem norm_mulVec_le_of_stochastic {s : ℕ} (H : Matrix (Fin s) (Fin s) ℝ)
    (hH : ∀ i j, 0 ≤ H i j) (hH1 : ∀ i, ∑ j, H i j = 1) (v : Fin s → ℝ) :
    ‖H *ᵥ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  calc |∑ j, H i j * v j| ≤ ∑ j, |H i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, H i j * ‖v‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul, abs_of_nonneg (hH i j)]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j)
          (hH i j)
    _ = ‖v‖ := by rw [← Finset.sum_mul, hH1, one_mul]

/-- Resolvent bound `‖x‖ ≤ ‖(I - γH)x‖ / (1 - γ)` for a row-stochastic `H`. -/
theorem norm_le_of_resolvent {s : ℕ} (H : Matrix (Fin s) (Fin s) ℝ)
    (hH : ∀ i j, 0 ≤ H i j) (hH1 : ∀ i, ∑ j, H i j = 1) (gamma : ℝ) (hg : gamma ∈ Ioo 0 1)
    (x : Fin s → ℝ) : ‖x‖ ≤ ‖(1 - gamma • H) *ᵥ x‖ / (1 - gamma) := by
  have hx : x = (1 - gamma • H) *ᵥ x + gamma • (H *ᵥ x) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]; abel
  have h1 : ‖x‖ ≤ ‖(1 - gamma • H) *ᵥ x‖ + gamma * ‖x‖ := by
    calc ‖x‖ = ‖(1 - gamma • H) *ᵥ x + gamma • (H *ᵥ x)‖ := by rw [← hx]
      _ ≤ ‖(1 - gamma • H) *ᵥ x‖ + ‖gamma • (H *ᵥ x)‖ := norm_add_le _ _
      _ ≤ ‖(1 - gamma • H) *ᵥ x‖ + gamma * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hg.1]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (norm_mulVec_le_of_stochastic H hH hH1 x) hg.1.le)
  rw [le_div_iff₀ (sub_pos.mpr hg.2)]
  linarith

/-- `I - γH` is invertible for a row-stochastic `H` and `γ ∈ (0,1)`. -/
theorem isUnit_one_sub_smul {s : ℕ} (H : Matrix (Fin s) (Fin s) ℝ)
    (hH : ∀ i j, 0 ≤ H i j) (hH1 : ∀ i, ∑ j, H i j = 1) (gamma : ℝ) (hg : gamma ∈ Ioo 0 1) :
    IsUnit (1 - gamma • H) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h := norm_le_of_resolvent H hH hH1 gamma hg (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- GAPS 107.59, the fixed-policy resolvent identity and sup-norm error bound. -/
theorem policy_value_resolvent_identity_and_error_bound {s : ℕ} (P H : Matrix (Fin s) (Fin s) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hH : ∀ i j, 0 ≤ H i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hH1 : ∀ i, ∑ j, H i j = 1)
    (gamma : ℝ) (hg : gamma ∈ Ioo 0 1) (r : Fin s → ℝ) :
    let V : Fin s → ℝ := ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • P)⁻¹.mulVec r;
    let W : Fin s → ℝ := ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • H)⁻¹.mulVec r;
    V - W = gamma • ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • H)⁻¹.mulVec ((P - H).mulVec V) ∧
      ‖V - W‖ ≤ gamma / (1 - gamma) * ‖(P - H).mulVec V‖ := by
  intro V W
  have uP := isUnit_one_sub_smul P hP hP1 gamma hg
  have uH := isUnit_one_sub_smul H hH hH1 gamma hg
  have hdP : IsUnit (1 - gamma • P).det := (Matrix.isUnit_iff_isUnit_det _).mp uP
  have hdH : IsUnit (1 - gamma • H).det := (Matrix.isUnit_iff_isUnit_det _).mp uH
  have hV : (1 - gamma • P) *ᵥ V = r := by
    simp only [V, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdP, Matrix.one_mulVec]
  have hW : (1 - gamma • H) *ᵥ W = r := by
    simp only [W, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdH, Matrix.one_mulVec]
  have hkey : (1 - gamma • H) *ᵥ (V - W) = gamma • ((P - H) *ᵥ V) := by
    rw [Matrix.mulVec_sub, hW, ← hV]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_sub]
    abel
  have hid : V - W = gamma • ((1 - gamma • H)⁻¹ *ᵥ ((P - H) *ᵥ V)) := by
    have := congrArg (fun v ↦ (1 - gamma • H)⁻¹ *ᵥ v) hkey
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mulVec,
      Matrix.mulVec_smul] at this
    rw [this]
    exact congrArg (gamma • ·) (Matrix.mulVec_mulVec _ _ _).symm
  refine ⟨hid, ?_⟩
  have hb := norm_le_of_resolvent H hH hH1 gamma hg (V - W)
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos hg.1] at hb
  calc ‖V - W‖ ≤ gamma * ‖(P - H) *ᵥ V‖ / (1 - gamma) := hb
    _ = _ := by ring

/-- GAPS 107.60, deterministic projected-contraction error bound underlying TD(lambda). -/
theorem norm_projected_fixed_point_sub_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H →L[ℝ] H) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (gamma lambda : ℝ) (hg : gamma ∈ Ioo 0 1) (hl : lambda ∈ Icc 0 1)
    (T : H → H)
    (hc : ∀ x y, ‖T x - T y‖ ≤ gamma * (1 - lambda) / (1 - gamma * lambda) * ‖x - y‖)
    (V w : H) (hV : T V = V) (hw : P (T w) = w) :
    ‖w - V‖ ≤ (1 - gamma * lambda) / (1 - gamma) * ‖P V - V‖ := by
  have hd : 0 < 1 - gamma * lambda := by nlinarith [mul_nonneg hg.1.le (sub_nonneg.mpr hl.2), hg.2]
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


end CKSD
