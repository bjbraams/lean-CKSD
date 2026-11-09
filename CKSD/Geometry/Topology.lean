module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Isometry

/-!
# Čech and Rips inclusions and the distance to a measure

The Euclidean comparison of Čech and Vietoris–Rips conditions on a finite point set, through the
minimal enclosing ball, and the Wasserstein stability of the distance to a measure.

## Main results

* `CKSD.mem_convexHull_farthest_of_isMin`: a minimizer of the largest squared distance to a finite
  set lies in the convex hull of the farthest points.
* `CKSD.exists_dist_le_sqrt_two_mul_of_dist_le`: a finite set of diameter at most `2r` lies in a
  closed ball of radius `√2 r`.
* `CKSD.cech_rips_inclusions`: the Čech/Rips inclusions (GAPS 108.21).
* `CKSD.abs_distanceToMeasure_sub_le_wasserstein`: stability of the distance to a measure
  (GAPS 108.24).

## Implementation notes

The mass radius `δ_{P,u}(x)` is the quantile function of the law of `y ↦ d(x, y)`, so `d_{P,m}(x)`
is an `L²(0, m)` norm of a quantile function. The stability bound then follows from Minkowski's
inequality, TauCeti's one-dimensional quantile formula for `W₂`
(`TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub`) and its contraction of `W₂` under Lipschitz
pushforward (`TauCeti.wassersteinEDist_map_le_mul`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- At a point `c` minimizing the largest squared distance to a nonempty finite set `S`, the
point `c` lies in the convex hull of the farthest points of `S`. -/
theorem mem_convexHull_farthest_of_isMin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (S : Finset E) (hne : S.Nonempty) (c : E)
    (hc : ∀ c', S.sup' hne (fun x ↦ ‖x - c‖ ^ 2) ≤ S.sup' hne (fun x ↦ ‖x - c'‖ ^ 2)) :
    c ∈ convexHull ℝ (↑(S.filter fun x ↦ ‖x - c‖ ^ 2 = S.sup' hne (fun x ↦ ‖x - c‖ ^ 2)) :
      Set E) := by
  set R2 := S.sup' hne (fun x ↦ ‖x - c‖ ^ 2)
  set F := S.filter fun x ↦ ‖x - c‖ ^ 2 = R2
  by_contra hnot
  obtain ⟨f, u, hfc, hfF⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (F.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
  set w := (InnerProductSpace.toDual ℝ E).symm f
  have hw : ∀ z, inner ℝ w z = f z := fun z ↦ InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
  have hexp : ∀ x (t : ℝ), ‖x - (c + t • w)‖ ^ 2 =
      ‖x - c‖ ^ 2 - t * (2 * inner ℝ w (x - c) - t * ‖w‖ ^ 2) := by
    intro x t
    rw [show x - (c + t • w) = (x - c) - t • w by abel, norm_sub_sq_real, inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
    ring
  have hev : ∀ x ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖x - (c + t • w)‖ ^ 2 < R2 := by
    intro x hx
    by_cases hxF : x ∈ F
    · have hpos : 0 < inner ℝ w (x - c) := by
        rw [inner_sub_right, hw, hw]
        linarith [hfF x (subset_convexHull ℝ _ hxF)]
      have hlim : Tendsto (fun t : ℝ ↦ 2 * inner ℝ w (x - c) - t * ‖w‖ ^ 2) (𝓝[>] 0)
          (𝓝 (2 * inner ℝ w (x - c) - 0 * ‖w‖ ^ 2)) :=
        (tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)).mono_left
          nhdsWithin_le_nhds
      rw [zero_mul, sub_zero] at hlim
      filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < 2 * _)),
        self_mem_nhdsWithin] with t ht ht0
      rw [hexp, (Finset.mem_filter.mp hxF).2]
      have : 0 < t * (2 * inner ℝ w (x - c) - t * ‖w‖ ^ 2) := mul_pos ht0 ht
      linarith
    · have hlt : ‖x - c‖ ^ 2 < R2 := by
        refine lt_of_le_of_ne (Finset.le_sup' (fun x ↦ ‖x - c‖ ^ 2) hx) fun h ↦ hxF ?_
        exact Finset.mem_filter.mpr ⟨hx, h⟩
      have hcont : Continuous fun t : ℝ ↦ ‖x - (c + t • w)‖ ^ 2 := by fun_prop
      have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [zero_smul, add_zero] at hlim
      exact hlim.eventually (gt_mem_nhds hlt)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ S, ‖x - (c + t • w)‖ ^ 2 < R2 :=
    (Filter.eventually_all_finset S).mpr hev
  obtain ⟨t, ht⟩ := hall.exists
  have : S.sup' hne (fun x ↦ ‖x - (c + t • w)‖ ^ 2) < R2 := (Finset.sup'_lt_iff hne).mpr ht
  exact absurd (hc (c + t • w)) (not_le.mpr this)

/-- A finite set of diameter at most `2r` in a finite-dimensional real inner product space lies in
a closed ball of radius `√2 r`, centered at a point minimizing the largest distance. -/
theorem exists_dist_le_sqrt_two_mul_of_dist_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (S : Finset E) (r : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) :
    ∃ c, ∀ x ∈ S, dist x c ≤ Real.sqrt 2 * r := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  set f : E → ℝ := fun c ↦ S.sup' hne (fun x ↦ ‖x - c‖ ^ 2)
  have hfc : Continuous f :=
    Continuous.finset_sup'_apply hne fun x _ ↦ by fun_prop
  obtain ⟨x₀, hx₀⟩ := hne
  have hr : 0 ≤ r := by linarith [h x₀ hx₀ x₀ hx₀, dist_self x₀]
  have hlim : Tendsto f (cocompact E) atTop := by
    have h1 : Tendsto (fun c : E ↦ ‖c‖ - (‖x₀‖ + 1)) (cocompact E) atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono (fun c ↦ ?_) h1
    have hle : ‖x₀ - c‖ ^ 2 ≤ f c := Finset.le_sup' (fun x ↦ ‖x - c‖ ^ 2) hx₀
    have htri : ‖c‖ - ‖x₀‖ ≤ ‖x₀ - c‖ := by
      have := norm_sub_norm_le c x₀
      rw [norm_sub_rev] at this
      linarith
    nlinarith [sq_nonneg (‖x₀ - c‖ - 1)]
  obtain ⟨c, hc⟩ := hfc.exists_forall_le hlim
  have hmem := mem_convexHull_farthest_of_isMin S ⟨x₀, hx₀⟩ c hc
  set R2 := f c
  set F := S.filter fun x ↦ ‖x - c‖ ^ 2 = R2
  rw [Finset.mem_convexHull] at hmem
  obtain ⟨wt, hw0, hw1, hcm⟩ := hmem
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  obtain ⟨j, hjS, hjeq⟩ := Finset.exists_mem_eq_sup' ⟨x₀, hx₀⟩ (fun x ↦ ‖x - c‖ ^ 2)
  have hjF : j ∈ F := Finset.mem_filter.mpr ⟨hjS, hjeq.symm⟩
  -- the weighted mean squared distance to `j` equals `2 R²`
  have hzero : ∑ y ∈ F, wt y • (y - c) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
    simpa using sub_eq_zero.mpr hcm
  have hkey : ∑ y ∈ F, wt y * ‖y - j‖ ^ 2 = 2 * R2 := by
    have hpt : ∀ y ∈ F, wt y * ‖y - j‖ ^ 2 =
        wt y * R2 - 2 * inner ℝ (wt y • (y - c)) (j - c) + wt y * R2 := by
      intro y hy
      rw [show y - j = (y - c) - (j - c) by abel, norm_sub_sq_real, real_inner_smul_left,
        (Finset.mem_filter.mp hy).2, (Finset.mem_filter.mp hjF).2]
      ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← sum_inner, hzero, inner_zero_left, ← Finset.sum_mul, hw1]
    ring
  have hbound : ∑ y ∈ F, wt y * ‖y - j‖ ^ 2 ≤ ∑ y ∈ F, wt y * (2 * r) ^ 2 := by
    refine Finset.sum_le_sum fun y hy ↦ mul_le_mul_of_nonneg_left ?_ (hw0 y hy)
    have := h y (Finset.mem_filter.mp hy).1 j hjS
    rw [dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [← Finset.sum_mul, hw1, one_mul, hkey] at hbound
  refine ⟨c, fun x hx ↦ ?_⟩
  have hx2 : ‖x - c‖ ^ 2 ≤ R2 := Finset.le_sup' (fun x ↦ ‖x - c‖ ^ 2) hx
  rw [dist_eq_norm]
  have : ‖x - c‖ ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this

/-- GAPS 108.21, the Euclidean Čech/Rips inclusions, in the diameter-`2r` convention: for a finite
set `S` in a finite-dimensional real inner product space, if `S` lies in a closed ball of radius
`r` then all pairwise distances are at most `2r`, and if all pairwise distances are at most `2r`
then `S` lies in a closed ball of radius `√2 r`. -/
theorem cech_rips_inclusions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Finset E) (r : ℝ) :
    ((∃ c, ∀ x ∈ S, dist x c ≤ r) → ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) ∧
      ((∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) →
        ∃ c, ∀ x ∈ S, dist x c ≤ Real.sqrt 2 * r) := by
  refine ⟨fun ⟨c, hc⟩ x hx y hy ↦ ?_, exists_dist_le_sqrt_two_mul_of_dist_le S r⟩
  calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (hc x hx) (by simpa [dist_comm] using hc y hy)
    _ = 2 * r := by ring

/-- On a probability space, the mass radius `δ_{P,u}(x)` at a level `u ≥ 0` is the quantile at
level `u` of the law of the distance `y ↦ d(x, y)`. -/
theorem massRadius_eq_quantile_map_dist {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (x : X) {u : ℝ}
    (hu : 0 ≤ u) : massRadius P u x = (P.map fun y ↦ dist x y).quantile u := by
  rcases hu.eq_or_lt with rfl | hu
  · rw [Measure.quantile_of_nonpos _ le_rfl, massRadius]
    have : {r : ℝ | 0 ≤ r ∧ ENNReal.ofReal 0 ≤ P (Metric.closedBall x r)} = Ici 0 := by
      ext r; simp
    rw [this, csInf_Ici]
  have hm : Measurable fun y ↦ dist x y := (continuous_const.dist continuous_id).measurable
  rw [massRadius, Measure.quantile_def]
  congr 1
  ext r
  simp only [mem_ofPred_eq]
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hm measurableSet_Iic]
  have hpre : (fun y ↦ dist x y) ⁻¹' Iic r = Metric.closedBall x r := by
    ext y; simp [dist_comm]
  rw [hpre, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hr
    have : Metric.closedBall x r = ∅ := Metric.closedBall_eq_empty.mpr (not_le.mp hr)
    rw [this, measure_empty, ENNReal.toReal_zero] at h
    linarith

/-- For an `L²` function, the real `L²` seminorm is the square root of the integral of the
square. -/
private theorem toReal_eLpNorm_two_eq_sqrt_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ a, f a ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  norm_num

/-- GAPS 108.24: stability of distance to a measure. For laws `P, Q` on `ℝ^d` with finite second
moments and a mass parameter `m ∈ (0, 1]`, the distance functions satisfy
`|d_{P,m}(x) - d_{Q,m}(x)| ≤ W₂(P, Q) / √m` at every point `x`. -/
theorem abs_distanceToMeasure_sub_le_wasserstein {d : ℕ}
    (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 2 P) (hQ : MemLp id 2 Q) (m : ℝ) (hm : m ∈ Ioc 0 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    |distanceToMeasure P m x - distanceToMeasure Q m x| ≤
      (TauCeti.wassersteinEDist 2 P Q).toReal / Real.sqrt m := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ dist x y
  have hfm : Measurable f := (continuous_const.dist continuous_id).measurable
  have hflip : LipschitzWith 1 f := LipschitzWith.dist_right x
  set νP := P.map f
  set νQ := Q.map f
  -- finite second moments
  have hmom : ∀ (R : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R],
      MemLp id 2 R → TauCeti.HasFiniteMoment 2 R := by
    intro R _ hR
    refine TauCeti.hasFiniteMoment_def.2
      ⟨0, (TauCeti.memLp_dist_iff_memLp_edist (by fun_prop)).1 ?_⟩
    simpa [dist_zero_right] using hR.norm
  have hPm := hmom P hP
  have hQm := hmom Q hQ
  have hWne : TauCeti.wassersteinEDist 2 P Q ≠ ∞ :=
    (TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment
      measurable_edist hPm).1 hQm
  have hνPm : TauCeti.HasFiniteMoment 2 νP :=
    hPm.map (fun _ ↦ measurable_edist_right) hfm hflip
  have hνQm : TauCeti.HasFiniteMoment 2 νQ :=
    hQm.map (fun _ ↦ measurable_edist_right) hfm hflip
  have hqP := (TauCeti.hasFiniteMoment_iff_memLp_quantile νP).1 hνPm
  have hqQ := (TauCeti.hasFiniteMoment_iff_memLp_quantile νQ).1 hνQm
  -- the restricted measure on `(0, m]`
  set μm := volume.restrict (Ioc (0 : ℝ) m)
  have hle : μm ≤ volume.restrict (Ioo (0 : ℝ) 1) := by
    refine Measure.restrict_mono_ae ?_
    refine (Filter.EventuallyLE.trans ?_ Ioo_ae_eq_Ioc.symm.le)
    exact Eventually.of_forall (Ioc_subset_Ioc_right hm.2)
  have hqPm : MemLp νP.quantile 2 μm := hqP.mono_measure hle
  have hqQm : MemLp νQ.quantile 2 μm := hqQ.mono_measure hle
  -- the distances to the measures as `L²` norms
  have hdtm : ∀ (R : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure R],
      MemLp (R.map f).quantile 2 μm →
      distanceToMeasure R m x = (eLpNorm (R.map f).quantile 2 μm).toReal / Real.sqrt m := by
    intro R _ hR
    rw [distanceToMeasure, toReal_eLpNorm_two_eq_sqrt_integral hR,
      intervalIntegral.integral_of_le hm.1.le, ← Real.sqrt_div' _ hm.1.le]
    congr 2
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
    show massRadius R u x ^ 2 = (R.map f).quantile u ^ 2
    rw [massRadius_eq_quantile_map_dist R x hu.1.le]
  rw [hdtm P hqPm, hdtm Q hqQm, ← sub_div, abs_div, abs_of_pos (Real.sqrt_pos.mpr hm.1)]
  gcongr
  -- Minkowski, restriction, the quantile formula and the contraction
  have hmink : |(eLpNorm νP.quantile 2 μm).toReal - (eLpNorm νQ.quantile 2 μm).toReal| ≤
      (eLpNorm (νP.quantile - νQ.quantile) 2 μm).toReal := by
    have h := abs_norm_sub_norm_le (hqPm.toLp _) (hqQm.toLp _)
    rwa [Lp.norm_toLp, Lp.norm_toLp, ← MemLp.toLp_sub, Lp.norm_toLp] at h
  refine hmink.trans ?_
  have hW1 : TauCeti.wassersteinEDist 2 νP νQ ≤ TauCeti.wassersteinEDist 2 P Q := by
    simpa using TauCeti.wassersteinEDist_map_le_mul (p := 2) measurable_edist hfm hflip P Q
  rw [TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub one_le_two] at hW1
  refine ENNReal.toReal_mono hWne ((eLpNorm_mono_measure _ hle).trans ?_)
  exact hW1

end CKSD
