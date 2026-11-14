module
public import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.Deriv.Prod
/-!
# Smooth backward transport tests with uniform error bounds

A bounded globally Lipschitz space-time velocity has smooth approximations with the same
Lipschitz bound. Backward transport along their augmented flows gives tests whose residual for
the original velocity tends uniformly to zero. A smooth bounded clock agrees with time near the
interval and supplies a global derivative bound independent of the approximation error.

Pinned TauCeti supplies uniform smooth Lipschitz approximation and joint smoothness of global
ODE flows. Mathlib supplies the chain rule, operator norm estimates and smooth bump functions.
These tests support weak continuity-equation uniqueness in GAPS 104.53, without assumptions on
the comparison measures beyond their weak equation and narrow continuity.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology ContDiff
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option backward.isDefEq.respectTransparency false in
/-- The time coordinate of an augmented flow increases at unit speed. -/
theorem globalSolution_fst_eq_add
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hwfst : ∀ q, (w q).1 = 1) (q : ℝ × E) (s : ℝ) :
    (ODE.globalSolution w hw q s).1 = q.1 + s := by
  have hd (r : ℝ) : HasDerivAt (fun r ↦ (ODE.globalSolution w hw q r).1) 1 r := by
    have h := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt r
      (ODE.hasDerivAt_globalSolution w hw q r)
    change HasDerivAt (fun r ↦ (ODE.globalSolution w hw q r).1)
      (w (ODE.globalSolution w hw q r)).1 r at h
    rwa [hwfst] at h
  have hd0 (r : ℝ) : HasDerivAt (fun r ↦ (ODE.globalSolution w hw q r).1 - r) 0 r := by
    convert (hd r).sub (hasDerivAt_id r) using 1 <;> first | rfl | simp only [sub_self]
  have hh := is_const_of_deriv_eq_zero (fun r ↦ (hd0 r).differentiableAt) (fun r ↦ (hd0 r).deriv)
  have heq := hh s 0
  change (ODE.globalSolution w hw q s).1 - s = (ODE.globalSolution w hw q 0).1 - 0 at heq
  rw [ODE.globalSolution_zero, sub_zero] at heq
  exact sub_eq_iff_eq_add.1 heq

/-- Pull a terminal spatial test backward along an augmented flow. -/
def backwardFlowTest (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (g : E → ℝ) (T : ℝ) (q : ℝ × E) : ℝ :=
  g ((ODE.globalSolution w hw q (T - q.1)).2)

/-- The backward-flow test is constant along every augmented trajectory. -/
theorem backwardFlowTest_globalSolution
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hwfst : ∀ q, (w q).1 = 1) (g : E → ℝ) (T : ℝ) (q : ℝ × E) (s : ℝ) :
    backwardFlowTest w hw g T (ODE.globalSolution w hw q s) = backwardFlowTest w hw g T q := by
  rw [backwardFlowTest, globalSolution_fst_eq_add w hw hwfst,
    ← ODE.globalSolution_add]
  congr 2
  ring_nf

/-- A smooth vector field and smooth terminal test give a smooth backward-flow test. -/
theorem contDiff_backwardFlowTest [FiniteDimensional ℝ E]
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hws : ContDiff ℝ ∞ w) (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (T : ℝ) :
    ContDiff ℝ ∞ (backwardFlowTest w hw g T) := by
  have hflow := ODE.contDiff_globalSolution w hw (n := (⊤ : ℕ∞)) (by simpa using hws)
  exact hg.comp (contDiff_snd.comp (hflow.comp (contDiff_id.prodMk (contDiff_const.sub contDiff_fst))))

set_option backward.isDefEq.respectTransparency false in
/-- The backward-flow test solves the backward transport equation for the smooth field. -/
theorem fderiv_backwardFlowTest_apply_field [FiniteDimensional ℝ E]
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hws : ContDiff ℝ ∞ w) (hwfst : ∀ q, (w q).1 = 1)
    (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (T : ℝ) (q : ℝ × E) :
    fderiv ℝ (backwardFlowTest w hw g T) q (w q) = 0 := by
  have hdiff := (contDiff_backwardFlowTest w hw hws g hg T).differentiable (by simp)
  have hd := (hdiff (ODE.globalSolution w hw q 0)).hasFDerivAt.comp_hasDerivAt 0
    (ODE.hasDerivAt_globalSolution w hw q 0)
  have heq : (fun s ↦ backwardFlowTest w hw g T (ODE.globalSolution w hw q s)) =
      (fun _ : ℝ ↦ backwardFlowTest w hw g T q) :=
    funext fun s ↦ backwardFlowTest_globalSolution w hw hwfst g T q s
  have hz : HasDerivAt (fun s ↦ backwardFlowTest w hw g T (ODE.globalSolution w hw q s)) 0 0 := by
    rw [heq]
    exact hasDerivAt_const _ _
  have huniq := hd.unique hz
  simpa only [ODE.globalSolution_zero] using huniq

/-- The backward-flow test agrees with its prescribed terminal value. -/
theorem backwardFlowTest_terminal (w : ℝ × E → ℝ × E) {K : ℝ≥0}
    (hw : LipschitzWith K w) (g : E → ℝ) (T : ℝ) (x : E) :
    backwardFlowTest w hw g T (T, x) = g x := by
  rw [backwardFlowTest, sub_self, ODE.globalSolution_zero]

/-- A uniform bound on the terminal test bounds the backward-flow test at every space-time point. -/
theorem norm_backwardFlowTest_le (w : ℝ × E → ℝ × E) {K : ℝ≥0}
    (hw : LipschitzWith K w) (g : E → ℝ) (T M : ℝ) (hg : ∀ x, ‖g x‖ ≤ M) (q : ℝ × E) :
    ‖backwardFlowTest w hw g T q‖ ≤ M := hg _

/-- A bounded vector field gives a uniform Lipschitz bound in flow time. -/
theorem lipschitzWith_globalSolution_time_of_bound
    (w : ℝ × E → ℝ × E) {K M : ℝ≥0} (hw : LipschitzWith K w)
    (hM : ∀ q, ‖w q‖₊ ≤ M) (q : ℝ × E) :
    LipschitzWith M (ODE.globalSolution w hw q) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro s
    exact (ODE.hasDerivAt_globalSolution w hw q s).differentiableAt
  · intro s
    rw [(ODE.hasDerivAt_globalSolution w hw q s).deriv]
    exact hM _

/-- A compactly supported smooth clock agrees with time on a neighbourhood of a bounded
nonnegative interval. Its bounds do not depend on any vector field. -/
theorem exists_smooth_bounded_clock {T : ℝ} (hT : 0 ≤ T) :
    ∃ (β : ℝ → ℝ) (J : ℝ≥0) (R : ℝ), ContDiff ℝ ∞ β ∧ LipschitzWith J β ∧
      (∀ t, |β t| ≤ R) ∧ EqOn β id (Ioo (-1 : ℝ) (T + 1)) := by
  let η : ContDiffBump (0 : ℝ) := ⟨T + 1, T + 2, by linarith, by linarith⟩
  let β : ℝ → ℝ := fun t ↦ η t * t
  have hβ : ContDiff ℝ ∞ β := η.contDiff.mul contDiff_id
  have hβsupp : HasCompactSupport β := η.hasCompactSupport.mul_right
  obtain ⟨J, hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hβsupp hβ (by simp)
  obtain ⟨R, hR⟩ := hβsupp.exists_bound_of_continuous hβ.continuous
  refine ⟨β, J, R, hβ, hJ, fun t ↦ ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using hR t
  · intro t ht
    have hη : η t = 1 := η.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨by change -(T + 1) ≤ t; linarith [ht.1], by change t ≤ T + 1; linarith [ht.2]⟩)
    simp only [β, hη, one_mul, id_eq]

/-- A bounded smooth clock makes backward transport tests well-behaved on the whole time line. -/
def boundedBackwardFlowTest (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (g : E → ℝ) (T : ℝ) (β : ℝ → ℝ) (q : ℝ × E) : ℝ :=
  backwardFlowTest w hw g T (β q.1, q.2)

/-- The global Lipschitz bound of a clocked backward test depends only on uniform bounds of
the clock, field and terminal test. -/
theorem lipschitzWith_boundedBackwardFlowTest
    (w : ℝ × E → ℝ × E) {K M G J : ℝ≥0} (hw : LipschitzWith K w)
    (hM : ∀ q, ‖w q‖₊ ≤ M) (g : E → ℝ) (hg : LipschitzWith G g)
    (T : ℝ) (β : ℝ → ℝ) (hβ : LipschitzWith J β) (R : ℝ) (hR : ∀ t, |β t| ≤ R) :
    LipschitzWith (Real.toNNReal ((G : ℝ) *
      (Real.exp ((K : ℝ) * (|T| + R)) * ((J : ℝ) + 1) + (M : ℝ) * J)))
      (boundedBackwardFlowTest w hw g T β) := by
  have ha : LipschitzWith J (fun q : ℝ × E ↦ β q.1) := by
    simpa only [mul_one, Function.comp_def] using hβ.comp LipschitzWith.prod_fst
  have hP : LipschitzWith (J + 1) (fun q : ℝ × E ↦ (β q.1, q.2)) := by
    apply (ha.prodMk LipschitzWith.prod_snd).weaken
    exact max_le (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ J from zero_le))
  have hτ : LipschitzWith J (fun q : ℝ × E ↦ T - β q.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simpa only [dist_sub_left] using ha.dist_le_mul q q'
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  let p := (β q.1, q.2)
  let p' := (β q'.1, q'.2)
  let τ := T - β q.1
  let τ' := T - β q'.1
  have hτbound : |τ| ≤ |T| + R := (abs_sub _ _).trans (add_le_add_right (hR q.1) _)
  have hflow := ODE.dist_globalSolution_le w hw p p' τ
  have htime := (lipschitzWith_globalSolution_time_of_bound w hw hM p').dist_le_mul τ τ'
  have hL := hP.dist_le_mul q q'
  have hL' := hτ.dist_le_mul q q'
  have hfull : dist (ODE.globalSolution w hw p τ) (ODE.globalSolution w hw p' τ') ≤
      (Real.exp ((K : ℝ) * (|T| + R)) * ((J : ℝ) + 1) + (M : ℝ) * J) * dist q q' := by
    calc
      _ ≤ dist (ODE.globalSolution w hw p τ) (ODE.globalSolution w hw p' τ) +
          dist (ODE.globalSolution w hw p' τ) (ODE.globalSolution w hw p' τ') := dist_triangle _ _ _
      _ ≤ dist p p' * Real.exp ((K : ℝ) * |τ|) + (M : ℝ) * dist τ τ' := add_le_add hflow htime
      _ ≤ (((J : ℝ) + 1) * dist q q') * Real.exp ((K : ℝ) * (|T| + R)) +
          (M : ℝ) * ((J : ℝ) * dist q q') := by
        apply add_le_add
        · apply mul_le_mul
          · simpa only [NNReal.coe_add, NNReal.coe_one] using hL
          · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτbound K.coe_nonneg)
          · positivity
          · positivity
        · exact mul_le_mul_of_nonneg_left hL' M.coe_nonneg
      _ = _ := by ring
  have hproj : dist (ODE.globalSolution w hw p τ).2 (ODE.globalSolution w hw p' τ').2 ≤
      dist (ODE.globalSolution w hw p τ) (ODE.globalSolution w hw p' τ') := by
    simpa only [NNReal.coe_one, one_mul] using
      (LipschitzWith.prod_snd.dist_le_mul (ODE.globalSolution w hw p τ) (ODE.globalSolution w hw p' τ'))
  have hout : dist (boundedBackwardFlowTest w hw g T β q)
      (boundedBackwardFlowTest w hw g T β q') ≤ (G : ℝ) *
        ((Real.exp ((K : ℝ) * (|T| + R)) * ((J : ℝ) + 1) + (M : ℝ) * J) * dist q q') := by
    exact (hg.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (hproj.trans hfull) G.coe_nonneg)
  exact hout.trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg)

/-- On an open interval where the clock is the identity, the clocked and ordinary tests agree
on a neighbourhood of every space-time point. -/
theorem boundedBackwardFlowTest_eventuallyEq
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (g : E → ℝ) (T : ℝ) (β : ℝ → ℝ) {a b : ℝ}
    (hβ : EqOn β id (Ioo a b)) (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    boundedBackwardFlowTest w hw g T β =ᶠ[𝓝 (t, x)] backwardFlowTest w hw g T := by
  have htime : ∀ᶠ q : ℝ × E in 𝓝 (t, x), q.1 ∈ Ioo a b :=
    continuous_fst.continuousAt.tendsto.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [htime] with q hq
  dsimp only [boundedBackwardFlowTest]
  rw [hβ hq]
  rfl

/-- The clocked test satisfies the exact backward equation on intervals where the clock equals
time. -/
theorem fderiv_boundedBackwardFlowTest_apply_field [FiniteDimensional ℝ E]
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hws : ContDiff ℝ ∞ w) (hwfst : ∀ q, (w q).1 = 1)
    (g : E → ℝ) (hg : ContDiff ℝ ∞ g) (T : ℝ) (β : ℝ → ℝ) {a b : ℝ}
    (hβ : EqOn β id (Ioo a b)) (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    fderiv ℝ (boundedBackwardFlowTest w hw g T β) (t, x) (w (t, x)) = 0 := by
  rw [(boundedBackwardFlowTest_eventuallyEq w hw g T β hβ t ht x).fderiv_eq]
  exact fderiv_backwardFlowTest_apply_field w hw hws hwfst g hg T _

/-- A bounded clocked test inherits the smoothness of the field, clock and terminal data. -/
theorem contDiff_boundedBackwardFlowTest [FiniteDimensional ℝ E]
    (w : ℝ × E → ℝ × E) {K : ℝ≥0} (hw : LipschitzWith K w)
    (hws : ContDiff ℝ ∞ w) (g : E → ℝ) (hg : ContDiff ℝ ∞ g)
    (T : ℝ) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (boundedBackwardFlowTest w hw g T β) :=
  (contDiff_backwardFlowTest w hw hws g hg T).comp
    ((hβ.comp contDiff_fst).prodMk contDiff_snd)

set_option maxHeartbeats 800000 in
/-- Bounded Lipschitz velocity fields admit globally bounded smooth backward test functions
whose transport residual tends uniformly to zero, with one derivative bound for all errors. -/
theorem exists_approximate_backward_test [FiniteDimensional ℝ E]
    (v : ℝ × E → E) {K M G : ℝ≥0} (hv : LipschitzWith K v)
    (hM : ∀ q, ‖v q‖₊ ≤ M) (g : E → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgLip : LipschitzWith G g) (A : ℝ) (hgA : ∀ x, ‖g x‖ ≤ A)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ ε > 0, ∃ u : ℝ × E → ℝ, ContDiff ℝ 1 u ∧
      (∀ q, ‖u q‖ ≤ A) ∧ (∀ q, ‖fderiv ℝ u q‖ ≤ C) ∧
      (∀ x, u (T, x) = g x) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ u (t, x) (1, v (t, x))‖ ≤ C * ε := by
  obtain ⟨β, J, R, hβs, hβLip, hβR, hβid⟩ := exists_smooth_bounded_clock hT
  let M' : ℝ≥0 := max 1 (M + 1)
  let C : ℝ≥0 := Real.toNNReal ((G : ℝ) *
    (Real.exp ((K : ℝ) * (|T| + R)) * ((J : ℝ) + 1) + (M' : ℝ) * J))
  refine ⟨C, C.coe_nonneg, fun ε hε ↦ ?_⟩
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  obtain ⟨v', hv's, hv'Lip, hclose⟩ := hv.exists_contDiff_lipschitzWith_dist_lt hδ
  let w : ℝ × E → ℝ × E := fun q ↦ (1, v' q)
  have hw : LipschitzWith K w := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    change max (dist (1 : ℝ) 1) (dist (v' q) (v' q')) ≤ _
    rw [dist_self]
    exact max_le (by positivity) (hv'Lip.dist_le_mul q q')
  have hws : ContDiff ℝ ∞ w := contDiff_const.prodMk hv's
  have hwM (q : ℝ × E) : ‖w q‖₊ ≤ M' := by
    have hc : ‖v' q - v q‖ ≤ δ := by simpa only [dist_eq_norm] using (hclose q).le
    have hmq : ‖v q‖ ≤ (M : ℝ) := hM q
    have hvq : ‖v' q‖ ≤ (M : ℝ) + 1 := by
      calc
        ‖v' q‖ ≤ ‖v' q - v q‖ + ‖v q‖ := by
          simpa only [sub_add_cancel] using norm_add_le (v' q - v q) (v q)
        _ ≤ δ + M := add_le_add hc hmq
        _ ≤ M + 1 := by linarith [min_le_right ε (1 : ℝ)]
    apply NNReal.coe_le_coe.mp
    simpa only [w, M', coe_nnnorm, Prod.norm_def, norm_one, NNReal.coe_max, NNReal.coe_one,
      NNReal.coe_add] using max_le_max (le_refl (1 : ℝ)) hvq
  let u := boundedBackwardFlowTest w hw g T β
  have hus : ContDiff ℝ ∞ u := contDiff_boundedBackwardFlowTest w hw hws g hg T β hβs
  have huLip : LipschitzWith C u := lipschitzWith_boundedBackwardFlowTest w hw hwM g hgLip T β hβLip R hβR
  have hDu (q : ℝ × E) : ‖fderiv ℝ u q‖ ≤ (C : ℝ) := norm_fderiv_le_of_lipschitz ℝ huLip
  refine ⟨u, hus.of_le (by simp), fun q ↦ hgA _, hDu, ?_, ?_⟩
  · intro x
    have ht : T ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by linarith, by linarith⟩
    dsimp only [u, boundedBackwardFlowTest]
    rw [hβid ht, id_eq, backwardFlowTest_terminal]
  · intro t ht x
    have ht' : t ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hzero : fderiv ℝ u (t, x) (w (t, x)) = 0 :=
      fderiv_boundedBackwardFlowTest_apply_field w hw hws (fun _ ↦ rfl) g hg T β hβid t ht' x
    have he : ‖(1, v (t, x)) - w (t, x)‖ ≤ δ := by
      have hc : ‖v (t, x) - v' (t, x)‖ ≤ δ := by
        simpa only [dist_comm, dist_eq_norm] using (hclose (t, x)).le
      simpa only [w, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hc
    calc
      ‖fderiv ℝ u (t, x) (1, v (t, x))‖ =
          ‖fderiv ℝ u (t, x) ((1, v (t, x)) - w (t, x))‖ := by rw [map_sub, hzero, sub_zero]
      _ ≤ ‖fderiv ℝ u (t, x)‖ * ‖(1, v (t, x)) - w (t, x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C : ℝ) * δ := mul_le_mul (hDu _) he (norm_nonneg _) C.coe_nonneg
      _ ≤ (C : ℝ) * ε := mul_le_mul_of_nonneg_left (min_le_left _ _) C.coe_nonneg
end CKSD
