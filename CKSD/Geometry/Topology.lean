module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Dual

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
  sorry

end CKSD
