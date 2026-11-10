module

public import CKSD.Bayes.StochasticApproximation.Basic
public import Mathlib.Analysis.ODE.Gronwall

/-!
# The deterministic ODE method for stochastic approximation

Positive steps define an affine interpolation. Vanishing steps, bounded iterates, and convergence
of the accumulated additive error imply that this interpolation follows the autonomous flow
uniformly on every fixed future time window.

The proof subtracts the limit of the accumulated error from the corrected interpolation. Its
right derivative differs from the limiting vector field by a term tending to zero. Mathlib's
`dist_le_of_approx_trajectories_ODE` then controls the error by Grönwall's inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The index of the interpolation interval containing a nonnegative time. -/
def stochasticApproxIndex (a : ℕ → ℝ) (s : ℝ) : ℕ :=
  sSup {n : ℕ | stochasticApproxTime a n ≤ s}

/-- The next interpolation time is the previous time plus the current step. -/
theorem stochasticApproxTime_succ (a : ℕ → ℝ) (n : ℕ) :
    stochasticApproxTime a (n + 1) = stochasticApproxTime a n + a n :=
  Finset.sum_range_succ _ _

/-- Positive steps give strictly increasing interpolation times. -/
theorem strictMono_stochasticApproxTime {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) :
    StrictMono (stochasticApproxTime a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [stochasticApproxTime_succ]
  exact lt_add_of_pos_right _ (ha n)

/-- Divergence of the interpolation times bounds every time sublevel in the natural numbers. -/
theorem bddAbove_stochasticApproxTime_sublevel {a : ℕ → ℝ} (_ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (s : ℝ) :
    BddAbove {n : ℕ | stochasticApproxTime a n ≤ s} := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (eventually_gt_atTop s))
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra h
  exact (not_lt_of_ge hn) (hN n (by omega))

/-- Inside a half-open interpolation interval, its index is the corresponding natural number. -/
theorem stochasticApproxIndex_eq {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) {s : ℝ} {n : ℕ}
    (hs : s ∈ Ico (stochasticApproxTime a n) (stochasticApproxTime a (n + 1))) :
    stochasticApproxIndex a s = n := by
  apply le_antisymm
  · apply csSup_le ⟨n, hs.1⟩
    intro k hk
    by_contra h
    have hnk : n + 1 ≤ k := by omega
    exact (not_lt_of_ge ((strictMono_stochasticApproxTime ha).monotone hnk |>.trans hk)) hs.2
  · exact le_csSup (bddAbove_stochasticApproxTime_sublevel ha ht s) hs.1

/-- The left endpoint of the interpolation interval is at most the given nonnegative time. -/
theorem stochasticApproxTime_index_le {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) {s : ℝ} (hs : 0 ≤ s) :
    stochasticApproxTime a (stochasticApproxIndex a s) ≤ s := by
  have hne : ({n : ℕ | stochasticApproxTime a n ≤ s} : Set ℕ).Nonempty := by
    exact ⟨0, by simpa [stochasticApproxTime] using hs⟩
  exact hne.csSup_mem (bddAbove_stochasticApproxTime_sublevel ha ht s).finite

/-- A time lies strictly below the right endpoint of its interpolation interval. -/
theorem lt_stochasticApproxTime_index_succ {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (s : ℝ) :
    s < stochasticApproxTime a (stochasticApproxIndex a s + 1) := by
  by_contra h
  have hh : stochasticApproxIndex a s + 1 ≤ stochasticApproxIndex a s :=
    le_csSup (bddAbove_stochasticApproxTime_sublevel ha ht s) (not_lt.1 h)
  omega

/-- The interpolation agrees with its affine formula on each closed interpolation interval. -/
theorem stochasticApproxInterp_eq_of_mem_Icc {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) {s : ℝ} {n : ℕ}
    (hs : s ∈ Icc (stochasticApproxTime a n) (stochasticApproxTime a (n + 1))) :
    stochasticApproxInterp a x s =
      x n + ((s - stochasticApproxTime a n) / a n) • (x (n + 1) - x n) := by
  by_cases htop : s = stochasticApproxTime a (n + 1)
  · subst s
    have hi := stochasticApproxIndex_eq ha ht (n := n + 1)
      (s := stochasticApproxTime a (n + 1)) ⟨le_rfl, strictMono_stochasticApproxTime ha (Nat.lt_succ_self _)⟩
    change x (stochasticApproxIndex a (stochasticApproxTime a (n + 1))) +
      ((stochasticApproxTime a (n + 1) -
          stochasticApproxTime a (stochasticApproxIndex a (stochasticApproxTime a (n + 1)))) /
          a (stochasticApproxIndex a (stochasticApproxTime a (n + 1)))) •
        (x (stochasticApproxIndex a (stochasticApproxTime a (n + 1)) + 1) -
          x (stochasticApproxIndex a (stochasticApproxTime a (n + 1)))) = _
    rw [hi, sub_self, zero_div, zero_smul, add_zero, stochasticApproxTime_succ,
      add_sub_cancel_left, div_self (ha n).ne', one_smul, add_sub_cancel]
  · have hi := stochasticApproxIndex_eq ha ht ⟨hs.1, lt_of_le_of_ne hs.2 htop⟩
    change x (stochasticApproxIndex a s) +
      ((s - stochasticApproxTime a (stochasticApproxIndex a s)) / a (stochasticApproxIndex a s)) •
      (x (stochasticApproxIndex a s + 1) - x (stochasticApproxIndex a s)) = _
    rw [hi]


/-- The interpolation index tends to infinity with time. -/
theorem tendsto_stochasticApproxIndex {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) :
    Tendsto (stochasticApproxIndex a) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (stochasticApproxTime a n)] with s hs
  exact le_csSup (bddAbove_stochasticApproxTime_sublevel ha ht s) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interpolation is continuous up to each interpolation time. -/
theorem continuousOn_stochasticApproxInterp_Icc {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) (n : ℕ) :
    ContinuousOn (stochasticApproxInterp a x) (Icc 0 (stochasticApproxTime a n)) := by
  have hcell (k : ℕ) : ContinuousOn (stochasticApproxInterp a x)
      (Icc (stochasticApproxTime a k) (stochasticApproxTime a (k + 1))) := by
    have hh : Continuous (fun s : ℝ ↦ x k +
        ((s - stochasticApproxTime a k) / a k) • (x (k + 1) - x k)) :=
      continuous_const.add ((continuous_id.sub continuous_const).div_const _ |>.smul continuous_const)
    exact hh.continuousOn.congr fun s hs ↦ stochasticApproxInterp_eq_of_mem_Icc ha ht x hs
  induction n with
  | zero => simp [stochasticApproxTime]
  | succ n ih =>
    have h0 : 0 ≤ stochasticApproxTime a n :=
      Finset.sum_nonneg fun k _ ↦ (ha k).le
    rw [← Icc_union_Icc_eq_Icc h0 ((strictMono_stochasticApproxTime ha).monotone (Nat.le_succ n))]
    exact ih.union_of_isClosed (hcell n) isClosed_Icc isClosed_Icc

/-- The interpolation is continuous on the nonnegative real line. -/
theorem continuousOn_stochasticApproxInterp {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) :
    ContinuousOn (stochasticApproxInterp a x) (Ici 0) := by
  intro s hs
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (eventually_gt_atTop s))
  have hN' : s < stochasticApproxTime a N := hN N le_rfl
  have hcont := continuousOn_stochasticApproxInterp_Icc ha ht x N s ⟨hs, hN'.le⟩
  apply hcont.mono_of_mem_nhdsWithin
  have heq : Icc 0 (stochasticApproxTime a N) = Ici 0 ∩ Iic (stochasticApproxTime a N) := rfl
  rw [heq]
  exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds hN'))

/-- The right derivative of the interpolation is its slope on the current interval. -/
theorem hasDerivWithinAt_stochasticApproxInterp {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (stochasticApproxInterp a x)
      ((a (stochasticApproxIndex a s))⁻¹ •
        (x (stochasticApproxIndex a s + 1) - x (stochasticApproxIndex a s))) (Ici s) s := by
  let n := stochasticApproxIndex a s
  have hlo : stochasticApproxTime a n ≤ s := stochasticApproxTime_index_le ha ht hs
  have hhi : s < stochasticApproxTime a (n + 1) := lt_stochasticApproxTime_index_succ ha ht s
  have hd : HasDerivAt (fun r : ℝ ↦ x n +
      ((r - stochasticApproxTime a n) / a n) • (x (n + 1) - x n))
      ((a n)⁻¹ • (x (n + 1) - x n)) s := by
    convert (((hasDerivAt_id s).sub_const (stochasticApproxTime a n)).div_const (a n)).smul_const
      (x (n + 1) - x n) |>.const_add (x n) using 1 <;> simp
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by exact le_rfl)
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hhi), self_mem_nhdsWithin] with r hr hrs
  exact stochasticApproxInterp_eq_of_mem_Icc ha ht x ⟨hlo.trans hrs, hr.le⟩


/-- The distance from an interpolation value to its left node is bounded by the node increment. -/
theorem norm_stochasticApproxInterp_sub_node_le {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) {s : ℝ} (hs : 0 ≤ s) :
    ‖stochasticApproxInterp a x s - x (stochasticApproxIndex a s)‖ ≤
      ‖x (stochasticApproxIndex a s + 1) - x (stochasticApproxIndex a s)‖ := by
  let n := stochasticApproxIndex a s
  have hlo := stochasticApproxTime_index_le ha ht hs
  have hhi := lt_stochasticApproxTime_index_succ ha ht s
  have hα : 0 ≤ (s - stochasticApproxTime a n) / a n :=
    div_nonneg (sub_nonneg.2 hlo) (ha n).le
  rw [stochasticApproxInterp_eq_of_mem_Icc ha ht x ⟨hlo, hhi.le⟩,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [div_le_one (ha n)]
  rw [stochasticApproxTime_succ] at hhi
  linarith

/-- Vanishing node increments make interpolation values approach their left nodes. -/
theorem tendsto_stochasticApproxInterp_sub_node {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E)
    (hx : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0)) :
    Tendsto (fun s ↦ stochasticApproxInterp a x s - x (stochasticApproxIndex a s))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
    (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using
      norm_stochasticApproxInterp_sub_node_le ha ht x hs)
  simpa only [norm_zero, Function.comp_def] using hx.norm.comp (tendsto_stochasticApproxIndex ha ht)

/-- Interpolation preserves the limit of a convergent sequence. -/
theorem tendsto_stochasticApproxInterp {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) {c : E}
    (hx : Tendsto x atTop (𝓝 c)) :
    Tendsto (stochasticApproxInterp a x) atTop (𝓝 c) := by
  have hinc : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0) := by
    simpa using (hx.comp (tendsto_add_atTop_nat 1)).sub hx
  have hh := (tendsto_stochasticApproxInterp_sub_node ha ht x hinc).add
    (hx.comp (tendsto_stochasticApproxIndex ha ht))
  simpa using hh

/-- Interpolation commutes with addition of sequences. -/
theorem stochasticApproxInterp_add (a : ℕ → ℝ) (x y : ℕ → E) (s : ℝ) :
    stochasticApproxInterp a (fun n ↦ x n + y n) s =
      stochasticApproxInterp a x s + stochasticApproxInterp a y s := by
  simp only [stochasticApproxInterp, add_sub_add_comm, smul_add]
  abel

/-- A curve differing by a vanishing error from an approximate ODE solution is an asymptotic
pseudotrajectory of the Lipschitz flow. The derivative error is required to vanish at infinity. -/
theorem asymptotic_pseudotrajectory_of_approx_ode
    (h : E → E) (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (x q v : ℝ → E) (hq : ContinuousOn q (Ici 0))
    (hd : ∀ s ≥ 0, HasDerivWithinAt q (v s) (Ici s) s)
    (herr : Tendsto (fun s ↦ v s + h (q s)) atTop (𝓝 0))
    (hxq : Tendsto (fun s ↦ x s - q s) atTop (𝓝 0)) (T : ℝ) (_hT : 0 < T) :
    ∀ ε > 0, ∀ᶠ s in atTop, ∀ u ∈ Icc 0 T, ‖x (s + u) - Φ u (x s)‖ ≤ ε := by
  intro ε hε
  have hc : Continuous (fun δ : ℝ ↦ δ + gronwallBound δ L δ T) := by
    unfold gronwallBound
    split_ifs <;> fun_prop
  have hc0 : (0 : ℝ) + gronwallBound 0 L 0 T = 0 := by simp [gronwallBound_ε0_δ0]
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) ε hε
  let δ := η / 2
  have hδ : 0 < δ := half_pos hη
  have heps : δ + gronwallBound δ L δ T < ε := by
    have hh := hηbound (x := δ) (by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using
        (show δ < η from half_lt_self hη))
    rw [hc0, Real.dist_eq, sub_zero] at hh
    exact lt_of_le_of_lt (le_abs_self _) hh
  have her : ∀ᶠ s in atTop, ‖v s + h (q s)‖ < δ :=
    herr.norm.eventually (by simpa only [norm_zero] using eventually_lt_nhds hδ)
  have hxr : ∀ᶠ s in atTop, ‖x s - q s‖ < δ :=
    hxq.norm.eventually (by simpa only [norm_zero] using eventually_lt_nhds hδ)
  obtain ⟨S, hS⟩ := eventually_atTop.1 (her.and hxr)
  filter_upwards [eventually_ge_atTop (max S 0)] with s hs
  have hs0 : 0 ≤ s := (le_max_right _ _).trans hs
  have hsS : S ≤ s := (le_max_left _ _).trans hs
  have hcont : ContinuousOn (fun u ↦ q (s + u)) (Icc 0 T) := by
    apply hq.comp (continuous_const.add continuous_id).continuousOn
    intro u hu
    exact add_nonneg hs0 hu.1
  have hderiv (u : ℝ) (hu : u ∈ Ico 0 T) : HasDerivWithinAt (fun r ↦ q (s + r))
      (v (s + u)) (Ici u) u := by
    have hshift : HasDerivWithinAt (fun r : ℝ ↦ s + r) 1 (Ici u) u := by
      convert ((hasDerivAt_id u).const_add s).hasDerivWithinAt using 1; simp
    have hh := (hd (s + u) (add_nonneg hs0 hu.1)).scomp u hshift
      (show MapsTo (fun r : ℝ ↦ s + r) (Ici u) (Ici (s + u)) from fun r hr ↦ by
        change s + u ≤ s + r
        exact add_le_add le_rfl hr)
    simpa only [Function.comp_def, one_smul] using hh
  have hflow : ContinuousOn (fun u ↦ Φ u (x s)) (Icc 0 T) :=
    (continuous_iff_continuousAt.2 fun u ↦ ((hΦ (x s)).2 u).continuousAt).continuousOn
  have hbound := dist_le_of_approx_trajectories_ODE
    (v := fun _ z ↦ -h z) (K := L) (δ := δ) (εf := δ) (εg := 0)
    (fun _ ↦ hL.neg) hcont hderiv
    (fun u hu ↦ by
      rw [dist_eq_norm, sub_neg_eq_add]
      exact (hS (s + u) (hsS.trans (le_add_of_nonneg_right hu.1))).1.le)
    hflow (fun u _ ↦ ((hΦ (x s)).2 u).hasDerivWithinAt)
    (fun u _ ↦ by simp)
    (by simpa only [add_zero, (hΦ (x s)).1, dist_eq_norm, norm_sub_rev] using (hS s hsS).2.le)
  intro u hu
  calc ‖x (s + u) - Φ u (x s)‖ ≤ ‖x (s + u) - q (s + u)‖ + ‖q (s + u) - Φ u (x s)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ + gronwallBound δ L δ u := by
      gcongr
      · exact (hS (s + u) (hsS.trans (le_add_of_nonneg_right hu.1))).2.le
      · simpa [dist_eq_norm] using hbound u hu
    _ ≤ δ + gronwallBound δ L δ T :=
      add_le_add le_rfl (gronwallBound_mono hδ.le hδ.le L.coe_nonneg hu.2)
    _ ≤ ε := heps.le


/-- Bounded stochastic-approximation iterates with vanishing steps and convergent cumulative
noise have an interpolated path that is an asymptotic pseudotrajectory of the limiting flow. -/
theorem asymptotic_pseudotrajectory_stochasticApproxInterp
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a atTop (𝓝 0)) (ht : Tendsto (stochasticApproxTime a) atTop atTop)
    (h : E → E) (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (x S : ℕ → E) {c : E} (hS : Tendsto S atTop (𝓝 c))
    (hbdd : BddAbove (range fun n ↦ ‖x n‖))
    (hrec : ∀ n, x (n + 1) = x n - a n • h (x n) - (S (n + 1) - S n))
    (T : ℝ) (hT : 0 < T) :
    ∀ ε > 0, ∀ᶠ s in atTop, ∀ u ∈ Icc 0 T,
      ‖stochasticApproxInterp a x (s + u) - Φ u (stochasticApproxInterp a x s)‖ ≤ ε := by
  obtain ⟨R, hR⟩ := hbdd
  let B := ‖h 0‖ + (L : ℝ) * max R 0
  have hB (n : ℕ) : ‖h (x n)‖ ≤ B := by
    calc ‖h (x n)‖ ≤ ‖h (x n) - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖x n‖ + ‖h 0‖ := by
        gcongr
        simpa using hL.norm_sub_le (x n) 0
      _ ≤ B := by
        dsimp [B]
        have hxR : ‖x n‖ ≤ max R 0 := (hR (mem_range_self n)).trans (le_max_left _ _)
        nlinarith [L.coe_nonneg, mul_le_mul_of_nonneg_left hxR L.coe_nonneg]
  have hadrift : Tendsto (fun n ↦ a n • h (x n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n ↦ by simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (hB n) (abs_nonneg (a n)))
    simpa using ha0.abs.mul_const B
  have hSinc : Tendsto (fun n ↦ S (n + 1) - S n) atTop (𝓝 0) := by
    simpa using (hS.comp (tendsto_add_atTop_nat 1)).sub hS
  have hxinc : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0) := by
    convert hadrift.neg.sub hSinc using 1
    · funext n
      rw [hrec]
      abel
    · simp
  let z : ℕ → E := fun n ↦ x n + S n
  have hzinc (n : ℕ) : z (n + 1) - z n = -(a n) • h (x n) := by
    dsimp [z]
    rw [hrec]
    simp only [neg_smul]
    abel
  let q : ℝ → E := fun s ↦ stochasticApproxInterp a z s - c
  have hq : ContinuousOn q (Ici 0) :=
    (continuousOn_stochasticApproxInterp ha ht z).sub continuousOn_const
  have hxq : Tendsto (fun s ↦ stochasticApproxInterp a x s - q s) atTop (𝓝 0) := by
    have hh : Tendsto (fun s : ℝ ↦ c - stochasticApproxInterp a S s) atTop (𝓝 (c - c)) :=
      tendsto_const_nhds.sub (tendsto_stochasticApproxInterp ha ht S hS)
    have hh0 : Tendsto (fun s ↦ c - stochasticApproxInterp a S s) atTop (𝓝 0) := by
      simpa using hh
    refine hh0.congr fun s ↦ ?_
    dsimp [q, z]
    rw [stochasticApproxInterp_add]
    abel
  have hqn : Tendsto (fun s ↦ q s - x (stochasticApproxIndex a s)) atTop (𝓝 0) := by
    convert hxq.neg.add (tendsto_stochasticApproxInterp_sub_node ha ht x hxinc) using 1
    · funext s
      abel
    · simp
  let v : ℝ → E := fun s ↦ -h (x (stochasticApproxIndex a s))
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt q (v s) (Ici s) s := by
    have hh := (hasDerivWithinAt_stochasticApproxInterp ha ht z hs).sub_const c
    have heq : (a (stochasticApproxIndex a s))⁻¹ •
        (z (stochasticApproxIndex a s + 1) - z (stochasticApproxIndex a s)) = v s := by
      rw [hzinc, smul_smul]
      dsimp [v]
      rw [mul_neg, inv_mul_cancel₀ (ha _).ne', neg_one_smul]
    rwa [heq] at hh
  have herr : Tendsto (fun s ↦ v s + h (q s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun s ↦ ?_)
      (by simpa using hqn.norm.const_mul (L : ℝ))
    rw [show v s + h (q s) = h (q s) - h (x (stochasticApproxIndex a s)) by
      dsimp [v]; abel]
    exact hL.norm_sub_le (q s) (x (stochasticApproxIndex a s))
  exact asymptotic_pseudotrajectory_of_approx_ode h L hL Φ hΦ
    (stochasticApproxInterp a x) q v hq hd herr hxq T hT

end CKSD
