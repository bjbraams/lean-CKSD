module

public import CKSD.Bayes.MeanFieldPathMap
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor


/-!
# Continuous solution maps for Lipschitz equations with additive forcing

The integral equation `x(t) = f(t) + ∫₀ᵗ v(s,x(s)) ds` has a unique continuous solution on any
bounded interval when `f` is continuous and the jointly continuous drift is uniformly Lipschitz
in position. The solution depends Lipschitz continuously on the forcing in the uniform norm.

The factorial Picard-iterate argument follows Mathlib's Picard–Lindelöf theorem and the pinned
TauCeti `Analysis.ODE.Caratheodory` proof, generalized from linear equations to continuous
nonlinear drifts and from constant initial values to continuous additive forcings. Stability
uses TauCeti's integral Grönwall inequality through `MeanFieldCoupling`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Function
open scoped Nat NNReal ENNReal Topology BigOperators
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Picard map for an equation with a prescribed continuous additive forcing. -/
def forcedPicardMap {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) (f y : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) :=
  f + y - pathForcingMap hT v hv y

/-- Evaluation of the Picard map is the forcing plus the integrated drift. -/
theorem forced_picard_map_apply {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) (f y : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    forcedPicardMap hT v hv f y t = f t + ∫ s in (0 : ℝ)..t, v s (y.IccExtend hT s) := by
  change f t + y t - (y t - _) = _
  abel

/-- The factorial Picard estimate holds for arbitrary continuous additive forcings. -/
theorem dist_iterate_forced_picard_map_apply_le {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s))
    (f : C(Icc (0 : ℝ) T, E)) (n : ℕ) (y z : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    dist ((forcedPicardMap hT v hv f)^[n] y t) ((forcedPicardMap hT v hv f)^[n] z t) ≤
      ((L : ℝ) * t) ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    let Y := (forcedPicardMap hT v hv f)^[n] y
    let Z := (forcedPicardMap hT v hv f)^[n] z
    have hint (W : C(Icc (0 : ℝ) T, E)) : IntervalIntegrable
        (fun s ↦ v s (W.IccExtend hT s)) volume 0 t :=
      (hv.comp (continuous_id.prodMk (W.IccExtend hT).continuous)).intervalIntegrable _ _
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, forced_picard_map_apply,
      forced_picard_map_apply, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub (hint Y) (hint Z)]
    calc _ ≤ ∫ s in (0 : ℝ)..t, (L : ℝ) * (((L : ℝ) * s) ^ n / n ! * dist y z) := by
          apply intervalIntegral.norm_integral_le_of_norm_le t.2.1 _
            (Continuous.intervalIntegrable (by fun_prop) _ _)
          filter_upwards [] with s hs
          have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.2.2⟩
          rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
            Set.IccExtend_of_mem (h := hT) (fun z ↦ Y z) hs',
            Set.IccExtend_of_mem (h := hT) (fun z ↦ Z z) hs']
          refine ((hvL s).norm_sub_le _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
          simpa only [dist_eq_norm] using ih ⟨s, hs'⟩
      _ = ((L : ℝ) * t) ^ (n + 1) / (n + 1)! * dist y z := by
          have heq : (∫ s in (0 : ℝ)..t, (L : ℝ) * (((L : ℝ) * s) ^ n / n ! * dist y z)) =
              (L : ℝ) ^ (n + 1) * dist y z / n ! * ∫ s in (0 : ℝ)..t, s ^ n := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1
            ext s
            rw [mul_pow, pow_succ]
            ring
          rw [heq, integral_pow, zero_pow n.succ_ne_zero, sub_zero, Nat.factorial_succ, mul_pow]
          push_cast
          field_simp

/-- Some iterate of the forced Picard map is a contraction on the whole continuous path space. -/
theorem exists_contracting_with_iterate_forced_picard_map {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s))
    (f : C(Icc (0 : ℝ) T, E)) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (forcedPicardMap hT v hv f)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((L : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h0 : 0 ≤ ((L : ℝ) * T) ^ n / n ! := by positivity
  refine ⟨n, ⟨_, h0⟩, hn, LipschitzWith.of_dist_le_mul fun y z ↦ ?_⟩
  change dist ((forcedPicardMap hT v hv f)^[n] y) ((forcedPicardMap hT v hv f)^[n] z) ≤
    (((L : ℝ) * T) ^ n / n !) * dist y z
  apply (ContinuousMap.dist_le (mul_nonneg h0 dist_nonneg)).2
  intro t
  refine (dist_iterate_forced_picard_map_apply_le hT v hv hvL f n y z t).trans ?_
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (n !))
  exact pow_le_pow_left₀ (mul_nonneg L.coe_nonneg t.2.1)
    (mul_le_mul_of_nonneg_left t.2.2 L.coe_nonneg) n

/-- Every continuous forcing admits a unique continuous solution of a uniformly Lipschitz
nonautonomous integral equation on a bounded interval. -/
theorem surjective_path_forcing_map {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    Function.Surjective (pathForcingMap hT v hv) := by
  intro f
  obtain ⟨n, C, hC⟩ := exists_contracting_with_iterate_forced_picard_map hT v hv hvL f
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (forcedPicardMap hT v hv f) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  refine ⟨y, ?_⟩
  change f + y - pathForcingMap hT v hv y = y at hy
  exact add_left_cancel ((sub_eq_iff_eq_add.mp hy).symm.trans (add_comm f y))
/-- A solution's uniform distance is controlled exponentially by the uniform distance between
its additive forcings. -/
theorem dist_le_exp_mul_dist_path_forcing_map {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s))
    (f g : C(Icc (0 : ℝ) T, E)) :
    dist f g ≤ Real.exp ((L : ℝ) * T) * dist (pathForcingMap hT v hv f) (pathForcingMap hT v hv g) := by
  let x := f.IccExtend hT
  let y := g.IccExtend hT
  let c := dist (pathForcingMap hT v hv f) (pathForcingMap hT v hv g)
  have hx : Continuous x := x.continuous
  have hy : Continuous y := y.continuous
  have hc : 0 ≤ c := dist_nonneg
  have hφ : Continuous (fun t ↦ ‖x t - y t‖) := (hx.sub hy).norm
  have hineq (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖x t - y t‖ ≤ c + L * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
    have hfi : IntervalIntegrable (fun s ↦ v s (x s)) volume 0 t :=
      (hv.comp (continuous_id.prodMk hx)).intervalIntegrable 0 t
    have hgi : IntervalIntegrable (fun s ↦ v s (y s)) volume 0 t :=
      (hv.comp (continuous_id.prodMk hy)).intervalIntegrable 0 t
    have hforcing : ‖(x t - y t) - (∫ s in (0 : ℝ)..t, v s (x s) - v s (y s))‖ ≤ c := by
      have hp := ContinuousMap.dist_apply_le_dist (f := pathForcingMap hT v hv f)
        (g := pathForcingMap hT v hv g) ⟨t, ht⟩
      rw [dist_eq_norm] at hp
      change ‖(f ⟨t, ht⟩ - ∫ s in (0 : ℝ)..t, v s (x s)) -
        (g ⟨t, ht⟩ - ∫ s in (0 : ℝ)..t, v s (y s))‖ ≤ c at hp
      rw [intervalIntegral.integral_sub hfi hgi]
      change ‖((f.IccExtend hT) t - (g.IccExtend hT) t) - _‖ ≤ _
      rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
        Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) ht,
        Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) ht]
      convert hp using 1
      congr 1
      abel
    have hbound : ‖∫ s in (0 : ℝ)..t, v s (x s) - v s (y s)‖ ≤
        (L : ℝ) * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
      calc _ ≤ ∫ s in (0 : ℝ)..t, ‖v s (x s) - v s (y s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.1
        _ ≤ ∫ s in (0 : ℝ)..t, (L : ℝ) * ‖x s - y s‖ :=
          intervalIntegral.integral_mono ht.1 (((hv.comp (continuous_id.prodMk hx)).sub
            (hv.comp (continuous_id.prodMk hy))).norm.intervalIntegrable _ _)
            ((hφ.const_mul _).intervalIntegrable _ _) (fun s ↦ (hvL s).norm_sub_le _ _)
        _ = _ := intervalIntegral.integral_const_mul _ _
    calc _ ≤ ‖(x t - y t) - (∫ s in (0 : ℝ)..t, v s (x s) - v s (y s))‖ +
          ‖∫ s in (0 : ℝ)..t, v s (x s) - v s (y s)‖ := by
            have h := norm_add_le ((x t - y t) - (∫ s in (0 : ℝ)..t, v s (x s) - v s (y s)))
              (∫ s in (0 : ℝ)..t, v s (x s) - v s (y s))
            simpa only [sub_add_cancel] using h
      _ ≤ _ := add_le_add hforcing hbound
  have hgr := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn L.coe_nonneg hineq
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le hc)).2
  intro t
  have h := hgr t t.2
  simp only [sub_zero] at h
  have he : Real.exp ((L : ℝ) * t) ≤ Real.exp ((L : ℝ) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 L.coe_nonneg)
  have hle := h.trans (mul_le_mul_of_nonneg_left he hc)
  simpa only [x, y, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) t.2,
    Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) t.2, sub_zero, mul_comm, dist_eq_norm] using hle

/-- The forcing map is a bijection on continuous paths for uniformly Lipschitz drifts. -/
def pathForcingEquiv {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    C(Icc (0 : ℝ) T, E) ≃ C(Icc (0 : ℝ) T, E) :=
  Equiv.ofBijective (pathForcingMap hT v hv)
    ⟨injective_path_forcing_map hT v hv hvL, surjective_path_forcing_map hT v hv hvL⟩

/-- Solving a forced Lipschitz integral equation is a Lipschitz map of the forcing path. -/
theorem lipschitz_with_path_forcing_equiv_symm {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    LipschitzWith (Real.toNNReal (Real.exp ((L : ℝ) * T))) (pathForcingEquiv hT v hv hvL).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  have h := dist_le_exp_mul_dist_path_forcing_map hT v hv hvL
    ((pathForcingEquiv hT v hv hvL).symm f) ((pathForcingEquiv hT v hv hvL).symm g)
  change dist ((pathForcingEquiv hT v hv hvL).symm f) ((pathForcingEquiv hT v hv hvL).symm g) ≤
    Real.exp ((L : ℝ) * T) * dist (pathForcingEquiv hT v hv hvL ((pathForcingEquiv hT v hv hvL).symm f))
      (pathForcingEquiv hT v hv hvL ((pathForcingEquiv hT v hv hvL).symm g)) at h
  simpa only [Equiv.apply_symm_apply] using h
/-- The inverse forcing map satisfies the prescribed integral equation at every time. -/
theorem path_forcing_equiv_symm_apply_eq {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s))
    (f : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    (pathForcingEquiv hT v hv hvL).symm f t = f t + ∫ s in (0 : ℝ)..t,
      v s (((pathForcingEquiv hT v hv hvL).symm f).IccExtend hT s) := by
  have heq := congrArg (fun g : C(Icc (0 : ℝ) T, E) ↦ g t)
    ((pathForcingEquiv hT v hv hvL).apply_symm_apply f)
  change (pathForcingEquiv hT v hv hvL).symm f t - (∫ s in (0 : ℝ)..t,
      v s (((pathForcingEquiv hT v hv hvL).symm f).IccExtend hT s)) = f t at heq
  exact sub_eq_iff_eq_add.mp heq

end CKSD
