module

public import CKSD.Bayes.MeanFieldCoupling
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic


/-!
# Measurable solution maps for additive-noise equations

For a continuous drift globally Lipschitz in position, recovering the additive forcing from a
continuous solution path is a Lipschitz injective map on the path space. Lusin–Souslin makes its
inverse on its range measurable. A separate countable-coordinate embedding reconstructs
continuous paths from projected rational evaluations, preserving measurable dependence on the
input data without assuming measurability of arbitrary uncountable process-valued maps.

Mathlib supplies continuous path spaces and Lusin–Souslin. The forcing-map injection uses
TauCeti's integral Grönwall inequality.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Recover the additive forcing from a continuous solution path of a time-dependent drift. -/
def pathForcingMap {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) (f : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) where
  toFun t := f t - ∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)
  continuous_toFun := by
    have hcont : Continuous (fun s : ℝ ↦ v s (f.IccExtend hT s)) :=
      hv.comp (continuous_id.prodMk (f.IccExtend hT).continuous)
    have hprim : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
    exact f.continuous.sub (hprim.comp continuous_subtype_val)

/-- The map recovering a solution's forcing is Lipschitz in the uniform path norm. -/
theorem lipschitz_with_path_forcing_map {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    LipschitzWith (1 + L * Real.toNNReal T) (pathForcingMap hT v hv) := by
  let : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  apply LipschitzWith.of_dist_le_mul
  intro f g
  apply ContinuousMap.dist_le_iff_of_nonempty.2
  intro t
  change dist (f t - ∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s))
      (g t - ∫ s in (0 : ℝ)..t, v s (g.IccExtend hT s)) ≤ _
  have hfi : IntervalIntegrable (fun s ↦ v s (f.IccExtend hT s)) volume 0 t :=
    (hv.comp (continuous_id.prodMk (f.IccExtend hT).continuous)).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun s ↦ v s (g.IccExtend hT s)) volume 0 t :=
    (hv.comp (continuous_id.prodMk (g.IccExtend hT).continuous)).intervalIntegrable _ _
  have hi : ‖∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s) - v s (g.IccExtend hT s)‖ ≤
      (L : ℝ) * dist f g * t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (L : ℝ) * dist f g) (a := (0 : ℝ)) (b := (t : ℝ)) (f := fun s ↦
        v s (f.IccExtend hT s) - v s (g.IccExtend hT s)) (fun s hs ↦ ?_)
    · simpa only [sub_zero, abs_of_nonneg t.2.1] using h
    · have hs' : s ∈ Icc (0 : ℝ) T := by
        rw [uIoc_of_le t.2.1] at hs
        exact ⟨hs.1.le, hs.2.trans t.2.2⟩
      rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
        Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) hs', Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) hs']
      refine (hvL s).norm_sub_le _ _ |>.trans ?_
      apply mul_le_mul_of_nonneg_left ?_ L.coe_nonneg
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) ⟨s, hs'⟩
  rw [dist_eq_norm,
    show (f t - ∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)) -
      (g t - ∫ s in (0 : ℝ)..t, v s (g.IccExtend hT s)) =
      (f t - g t) - ((∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)) -
        ∫ s in (0 : ℝ)..t, v s (g.IccExtend hT s)) by abel]
  calc
    ‖(f t - g t) - ((∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)) -
        ∫ s in (0 : ℝ)..t, v s (g.IccExtend hT s))‖ ≤
      ‖f t - g t‖ + ‖(∫ s in (0 : ℝ)..t, v s (f.IccExtend hT s)) -
        ∫ s in (0 : ℝ)..t, v s (g.IccExtend hT s)‖ := norm_sub_le _ _
    _ ≤ dist f g + (L : ℝ) * dist f g * t := by
      apply add_le_add
      · simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t
      · rw [← intervalIntegral.integral_sub hfi hgi]
        exact hi
    _ ≤ _ := by
      rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal T hT]
      have := mul_le_mul_of_nonneg_left t.2.2 (mul_nonneg L.coe_nonneg (dist_nonneg : 0 ≤ dist f g))
      nlinarith

/-- A continuous path solving a Lipschitz drift equation is determined by its additive forcing. -/
theorem injective_path_forcing_map {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    Function.Injective (pathForcingMap hT v hv) := by
  intro f g heq
  let x : ℝ → E := f.IccExtend hT
  let y : ℝ → E := g.IccExtend hT
  have hx : Continuous x := (f.IccExtend hT).continuous
  have hy : Continuous y := (g.IccExtend hT).continuous
  have hφ : Continuous (fun t ↦ ‖x t - y t‖) := (hx.sub hy).norm
  have hΔ (t : ℝ) (ht : t ∈ Icc 0 T) : x t - y t = ∫ s in (0 : ℝ)..t, v s (x s) - v s (y s) := by
    have hpoint := congrArg (fun z : C(Icc (0 : ℝ) T, E) ↦ z ⟨t, ht⟩) heq
    change f ⟨t, ht⟩ - (∫ s in (0 : ℝ)..t, v s (x s)) =
      g ⟨t, ht⟩ - (∫ s in (0 : ℝ)..t, v s (y s)) at hpoint
    have hxi : IntervalIntegrable (fun s ↦ v s (x s)) volume 0 t :=
      (hv.comp (continuous_id.prodMk hx)).intervalIntegrable _ _
    have hyi : IntervalIntegrable (fun s ↦ v s (y s)) volume 0 t :=
      (hv.comp (continuous_id.prodMk hy)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hxi hyi]
    change (f.IccExtend hT) t - (g.IccExtend hT) t = _
    rw [ContinuousMap.coe_IccExtend, ContinuousMap.coe_IccExtend,
      Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) ht,
      Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) ht]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hpoint
  have hineq (t : ℝ) (ht : t ∈ Icc 0 T) : ‖x t - y t‖ ≤ 0 + L * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
    rw [hΔ t ht, zero_add]
    calc ‖∫ s in (0 : ℝ)..t, v s (x s) - v s (y s)‖ ≤ ∫ s in (0 : ℝ)..t, ‖v s (x s) - v s (y s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in (0 : ℝ)..t, (L : ℝ) * ‖x s - y s‖ :=
        intervalIntegral.integral_mono ht.1
          (((hv.comp (continuous_id.prodMk hx)).sub (hv.comp (continuous_id.prodMk hy))).norm.intervalIntegrable _ _)
          ((hφ.const_mul _).intervalIntegrable _ _) (fun s ↦ (hvL s).norm_sub_le _ _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hzero := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn L.coe_nonneg hineq
  apply ContinuousMap.ext
  intro t
  have hn : ‖x t - y t‖ = 0 := le_antisymm (by simpa only [zero_mul] using hzero t t.2) (norm_nonneg _)
  have hxy := sub_eq_zero.mp (norm_eq_zero.mp hn)
  simpa only [x, y, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) t.2,
    Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) t.2] using hxy

/-- The inverse solution map on the range of the forcing map is measurable. -/
theorem measurable_embedding_path_forcing_map [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) {L : ℝ≥0} (hvL : ∀ s, LipschitzWith L (v s)) :
    MeasurableEmbedding (pathForcingMap hT v hv) :=
  (lipschitz_with_path_forcing_map hT v hv hvL).continuous.measurableEmbedding
    (injective_path_forcing_map hT v hv hvL)

/-- Countable coordinates of a continuous path, using rational times projected to its interval. -/
def pathRationalCoordinates {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) : ℚ → E :=
  fun q ↦ f (Set.projIcc 0 T hT q)

omit [NormedSpace ℝ E] in
/-- Rational-time coordinates determine a continuous path and identify it measurably with their
range in the countable product. -/
theorem measurable_embedding_path_rational_coordinates [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {T : ℝ} (hT : 0 ≤ T) :
    MeasurableEmbedding (pathRationalCoordinates (E := E) hT) := by
  have hcont : Continuous (pathRationalCoordinates (E := E) hT) :=
    continuous_pi fun q ↦ continuous_eval_const _
  apply hcont.measurableEmbedding
  intro f g heq
  have hext : (f.IccExtend hT : ℝ → E) = g.IccExtend hT := by
    apply Rat.denseRange_cast.equalizer (f.IccExtend hT).continuous (g.IccExtend hT).continuous
    exact heq
  apply ContinuousMap.ext
  intro t
  have h := congrFun hext t
  simpa only [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) t.2,
    Set.IccExtend_of_mem (h := hT) (fun z ↦ g z) t.2] using h

/-- A measurable reconstruction of a continuous path from its projected rational coordinates.
Coordinate families not representing a continuous path are assigned an arbitrary fixed path. -/
def pathOfRationalCoordinates [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 ≤ T) : (ℚ → E) → C(Icc (0 : ℝ) T, E) :=
  (measurable_embedding_path_rational_coordinates hT).invFun

omit [NormedSpace ℝ E] in
/-- Reconstructing the coordinates of a continuous path returns that path. -/
theorem path_of_rational_coordinates_apply [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    pathOfRationalCoordinates hT (pathRationalCoordinates hT f) = f :=
  (measurable_embedding_path_rational_coordinates hT).leftInverse_invFun f

omit [NormedSpace ℝ E] in
/-- The reconstruction of continuous paths from countably many coordinates is measurable. -/
theorem measurable_path_of_rational_coordinates [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 ≤ T) : Measurable (pathOfRationalCoordinates (E := E) hT) :=
  (measurable_embedding_path_rational_coordinates hT).measurable_invFun

end CKSD
