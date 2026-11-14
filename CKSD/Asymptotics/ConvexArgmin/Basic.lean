module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The convexity lemma for random convex functions

Pointwise convergence in probability of random convex functions on a finite-dimensional space
to a continuous limit is automatically uniform on bounded sets, and the minimizers of a random
convex function that is approximately quadratic are close to the minimizer of the quadratic
approximation. These are the two parts of the convexity lemma of Hjort and Pollard, which is
the standard route to the asymptotics of convex M-estimators (least absolute deviations,
quantile regression, Huber regression, generalized linear models with canonical link).

The uniformity is reduced to finitely many points: a convex function on a ball is bounded by
its values on the vertices of a polytope containing a larger ball and at the centre
(`ConvexOn.le_sup_of_mem_convexHull`), hence Lipschitz on the ball with a controlled constant
(`ConvexOn.lipschitzOnWith_of_abs_le`), and a finite net then suffices. Convergence in measure
is measured by the outer measure, so no measurability of the random functions in the parameter
is needed.

## Main results

* `CKSD.tendsto_measure_exists_abs_sub_of_convexOn`: pointwise convergence in probability of
  random convex functions to a continuous function is uniform on balls.
* `CKSD.norm_sub_lt_of_convexOn_of_abs_sub_lt`: the deterministic argmin bound for a convex
  function uniformly close to a positive definite quadratic on a ball.
* `CKSD.tendstoInMeasure_sub_of_convexOn_of_isMinOn`: the Hjort–Pollard basic corollary; if
  `Zₙ(h) = -⟪Uₙ, h⟫ + ½⟪h, A h⟫ + o_P(1)` pointwise with `Uₙ` bounded in probability and `A`
  positive definite, then every minimizer `αₙ` of `Zₙ` satisfies `αₙ - A⁻¹ Uₙ → 0` in probability.

## References

* N. L. Hjort and D. Pollard, *Asymptotics for minimisers of convex processes*, preprint, 1993
  (arXiv:1107.3806), Lemma 1 and Basic Corollary.
* D. Pollard, *Asymptotics for least absolute deviation regression estimators*, Econometric
  Theory 7 (1991), 186–199.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace

namespace CKSD

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex function on `E` whose values on a finite set `F` are within `1` of those of `q`,
and likewise at the origin, is bounded on any set of points `h` with `h, -h ∈ conv F` by
`∑_{v ∈ F} (|q v| + 1) + 2 (|q 0| + 1)`. -/
private lemma abs_le_of_convexOn_of_mem_convexHull {f q : E → ℝ} (hf : ConvexOn ℝ univ f)
    (F : Finset E) (hF : ∀ v ∈ F, |f v - q v| < 1) (h0 : |f 0 - q 0| < 1) {h : E}
    (hh : h ∈ convexHull ℝ (F : Set E)) (hh' : -h ∈ convexHull ℝ (F : Set E)) :
    |f h| ≤ ∑ v ∈ F, (|q v| + 1) + 2 * (|q 0| + 1) := by
  have hne : F.Nonempty := Finset.coe_nonempty.1 (convexHull_nonempty_iff.1 ⟨h, hh⟩)
  have hsup : ∀ y ∈ convexHull ℝ (F : Set E), f y ≤ ∑ v ∈ F, (|q v| + 1) := by
    intro y hy
    refine (hf.le_sup_of_mem_convexHull (subset_univ _) hy).trans ?_
    obtain ⟨v, hv, hve⟩ := Finset.exists_mem_eq_sup' hne f
    rw [hve]
    have h1 : f v ≤ |q v| + 1 := by
      have := hF v hv
      have := le_abs_self (q v)
      have := (abs_lt.1 (hF v hv)).2
      linarith
    exact h1.trans (Finset.single_le_sum (f := fun v ↦ |q v| + 1)
      (fun w _ ↦ by positivity) hv)
  have hmid : f 0 ≤ (f h + f (-h)) / 2 := by
    have := hf.2 (mem_univ h) (mem_univ (-h)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_neg, add_neg_cancel, smul_eq_mul] at this
    linarith
  have hq0 := (abs_lt.1 h0).1
  have hq0' := neg_abs_le (q 0)
  have hS : 0 ≤ ∑ v ∈ F, (|q v| + 1) := Finset.sum_nonneg fun v _ ↦ by positivity
  have habs := abs_nonneg (q 0)
  have h1 := hsup h hh
  have h2 := hsup (-h) hh'
  rw [abs_le]
  constructor <;> linarith

/-- A convex function that is uniformly close to a continuous function `q` at finitely many
well-chosen points is uniformly close to `q` on a ball: for `R` and `ε > 0` there is a finite
set `S` and `ε' > 0` such that `|f v - q v| < ε'` on `S` implies `|f h - q h| < ε` whenever
`‖h‖ ≤ R`, for every convex `f`. The points are the vertices of a polytope containing a larger
ball, the origin, and a fine net of the ball. -/
private lemma exists_finset_abs_sub_lt_of_convexOn [FiniteDimensional ℝ E] {q : E → ℝ}
    (hq : Continuous q) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset E, ∃ ε' > 0, ∀ f : E → ℝ, ConvexOn ℝ univ f →
      (∀ v ∈ S, |f v - q v| < ε') → ∀ h, ‖h‖ ≤ R → |f h - q h| < ε := by
  classical
  set r : ℝ := max R 1 with hr_def
  have hr : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨F, hF, -⟩ := (convex_closedBall (0 : E) (3 * r)).exists_subset_interior_convexHull_finset_of_isCompact
    (isCompact_closedBall 0 (3 * r)) (t := univ) Filter.univ_mem
  set K : ℝ := ∑ v ∈ F, (|q v| + 1) + 2 * (|q 0| + 1) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ v ∈ F, (|q v| + 1) := Finset.sum_nonneg fun v _ ↦ by positivity
    positivity
  set L : ℝ := 2 * K / r with hL
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨δ₀, hδ₀, hqδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : E) r).uniformContinuousOn_of_continuous hq.continuousOn)
    (ε / 3) (by positivity)
  set δ : ℝ := min δ₀ (ε / (3 * (L + 1))) with hδ
  have hδ0 : 0 < δ := lt_min hδ₀ (by positivity)
  obtain ⟨N, hNs, hN⟩ := (isCompact_closedBall (0 : E) r).elim_nhds_subcover _
    (fun x _ ↦ ball_mem_nhds x hδ0)
  refine ⟨F ∪ {0} ∪ N, min 1 (ε / 3), lt_min one_pos (by positivity), fun f hf hS h hh ↦ ?_⟩
  have hS1 : ∀ v ∈ F ∪ {0} ∪ N, |f v - q v| < 1 := fun v hv ↦ (hS v hv).trans_le (min_le_left _ _)
  have hS3 : ∀ v ∈ F ∪ {0} ∪ N, |f v - q v| < ε / 3 :=
    fun v hv ↦ (hS v hv).trans_le (min_le_right _ _)
  -- bound on the ball of radius `3 r`
  have hbd : ∀ a, dist a 0 < 3 * r → |f a| ≤ K := by
    intro a ha
    have ha' : a ∈ closedBall (0 : E) (3 * r) := ball_subset_closedBall ha
    have hna : -a ∈ closedBall (0 : E) (3 * r) := by simpa using ha'
    exact abs_le_of_convexOn_of_mem_convexHull hf F
      (fun v hv ↦ hS1 v (by simp [hv])) (hS1 0 (by simp))
      (interior_subset (hF ha')) (interior_subset (hF hna))
  have hlip := (hf.subset (subset_univ _) (convex_ball 0 (3 * r))).lipschitzOnWith_of_abs_le hr hbd
  have hhr : ‖h‖ ≤ r := hh.trans (le_max_left _ _)
  have hh_cb : h ∈ closedBall (0 : E) r := by simpa using hhr
  obtain ⟨v, hvN, hv⟩ := mem_iUnion₂.1 (hN hh_cb)
  have hv_cb : v ∈ closedBall (0 : E) r := hNs v hvN
  have hball : ∀ y ∈ closedBall (0 : E) r, y ∈ ball (0 : E) (3 * r - r) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_ball, dist_zero_right]
    linarith
  have hfv : |f h - f v| ≤ L * δ := by
    have := hlip.dist_le_mul h (hball h hh_cb) v (hball v hv_cb)
    rw [Real.dist_eq, Real.coe_toNNReal _ hL0] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL0)
    exact (mem_ball.1 hv).le
  have hqv : |q v - q h| < ε / 3 := by
    have hvh : dist h v < δ := mem_ball.1 hv
    have hvh' : dist v h < δ₀ := by
      rw [dist_comm]; exact hvh.trans_le (min_le_left _ _)
    have := hqδ v hv_cb h hh_cb hvh'
    rwa [Real.dist_eq] at this
  have hLδ : L * δ ≤ ε / 3 := by
    calc L * δ ≤ (L + 1) * (ε / (3 * (L + 1))) :=
          mul_le_mul (by linarith) (min_le_right _ _) hδ0.le (by linarith)
      _ = ε / 3 := by field_simp
  have h3 := hS3 v (by simp [hvN])
  calc |f h - q h| = |(f h - f v) + (f v - q v) + (q v - q h)| := by ring_nf
    _ ≤ |f h - f v| + |f v - q v| + |q v - q h| := abs_add_three _ _ _
    _ < ε := by linarith

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}

/-- **Convexity lemma, uniform part.** If random convex functions `gₙ` on a finite-dimensional
space converge pointwise in probability to a continuous function `q`, then the convergence is
uniform on every ball: `μ {ω | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |gₙ ω h - q h|} → 0` for all `R` and `ε > 0`.
No measurability in `ω` is assumed; the measure is the outer measure. -/
theorem tendsto_measure_exists_abs_sub_of_convexOn [FiniteDimensional ℝ E]
    (g : ι → Ω → E → ℝ) (hg : ∀ n ω, ConvexOn ℝ univ (g n ω)) {q : E → ℝ} (hq : Continuous q)
    (hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦ μ {ω | ε ≤ |g n ω h - q h|}) l (𝓝 0))
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ μ {ω | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n ω h - q h|}) l (𝓝 0) := by
  obtain ⟨S, ε', hε', hS⟩ := exists_finset_abs_sub_lt_of_convexOn hq R hε
  have hsub : ∀ n, {ω | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n ω h - q h|} ⊆
      ⋃ v ∈ S, {ω | ε' ≤ |g n ω v - q v|} := by
    intro n ω ⟨h, hh, hεh⟩
    by_contra hω
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hω
    exact (hS (g n ω) (hg n ω) (fun v hv ↦ hω v hv) h hh).not_ge hεh
  have hsum : Tendsto (fun n ↦ ∑ v ∈ S, μ {ω | ε' ≤ |g n ω v - q v|}) l (𝓝 0) := by
    simpa using tendsto_finsetSum S fun v _ ↦ hpt v ε' hε'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ bot_le)
    fun n ↦ (measure_mono (hsub n)).trans (measure_biUnion_finset_le S _)

end Uniform

section Argmin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Convexity lemma, deterministic argmin bound.** Let `f` be convex and uniformly within
`c δ² / 4` of the quadratic `C + ½ ⟪h - β, A (h - β)⟫` on the closed ball of radius `δ` about
`β`, where `⟪h, A h⟫ ≥ c ‖h‖²`. Then every `α` with `f α ≤ f β` satisfies `‖α - β‖ < δ`. -/
theorem norm_sub_lt_of_convexOn_of_abs_sub_lt {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (A : E →L[ℝ] E) {c δ C : ℝ} (hA : ∀ h, c * ‖h‖ ^ 2 ≤ ⟪h, A h⟫_ℝ) (hδ : 0 < δ) {β α : E}
    (happ : ∀ h, ‖h - β‖ ≤ δ → |f h - (C + ⟪h - β, A (h - β)⟫_ℝ / 2)| < c * δ ^ 2 / 4)
    (hα : f α ≤ f β) : ‖α - β‖ < δ := by
  by_contra hge
  push Not at hge
  have hpos : 0 < ‖α - β‖ := hδ.trans_le hge
  set t : ℝ := δ / ‖α - β‖ with ht
  have ht0 : 0 < t := div_pos hδ hpos
  have ht1 : t ≤ 1 := (div_le_one hpos).2 hge
  set p : E := β + t • (α - β) with hp
  have hpβ : ‖p - β‖ = δ := by
    rw [hp, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le, ht,
      div_mul_cancel₀ _ hpos.ne']
  have hconv : f p ≤ (1 - t) * f β + t * f α := by
    have := hf.2 (mem_univ β) (mem_univ α) (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    have hpe : (1 - t) • β + t • α = p := by
      rw [hp, smul_sub, sub_smul, one_smul]; abel
    simpa only [hpe, smul_eq_mul] using this
  have h1 := happ p hpβ.le
  have h2 := happ β (by simp [hδ.le])
  simp only [sub_self, map_zero, inner_zero_right, zero_div, add_zero] at h2
  have hq := hA (p - β)
  rw [hpβ] at hq
  have h1' := (abs_lt.1 h1).1
  have h2' := (abs_lt.1 h2).2
  have hc : 0 ≤ c * δ ^ 2 := by
    by_contra hc
    push Not at hc
    have := (abs_nonneg _).trans_lt h2
    linarith
  nlinarith

variable [FiniteDimensional ℝ E] {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {l : Filter ι}

/-- **Convexity lemma, basic corollary** (Hjort–Pollard). Let `Zₙ` be random convex functions
on a finite-dimensional inner product space with
`Zₙ(h) = -⟪Uₙ, h⟫ + ½ ⟪h, A h⟫ + rₙ(h)` where `rₙ(h) → 0` in probability for each `h`, `Uₙ` is
bounded in probability, and `A` is self-adjoint with `⟪h, A h⟫ ≥ c ‖h‖²`, `c > 0`, with right
inverse `B`. Then every (almost sure) minimizer `αₙ` of `Zₙ` satisfies `αₙ - B Uₙ → 0` in
probability. -/
theorem tendstoInMeasure_sub_of_convexOn_of_isMinOn (Z : ι → Ω → E → ℝ)
    (hZ : ∀ n ω, ConvexOn ℝ univ (Z n ω)) (U : ι → Ω → E) (A B : E →L[ℝ] E)
    (hAB : ∀ u, A (B u) = u) (hAsymm : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) {c : ℝ} (hc : 0 < c)
    (hA : ∀ h, c * ‖h‖ ^ 2 ≤ ⟪h, A h⟫_ℝ)
    (hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      μ {ω | ε ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|}) l (𝓝 0))
    (htight : ∀ η > (0 : ℝ≥0∞), ∃ M : ℝ, ∀ᶠ n in l, μ {ω | M < ‖U n ω‖} ≤ η)
    (α : ι → Ω → E) (hmin : ∀ᶠ n in l, ∀ᵐ ω ∂μ, ∀ h, Z n ω (α n ω) ≤ Z n ω h) :
    TendstoInMeasure μ (fun n ω ↦ α n ω - B (U n ω)) l (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM⟩ := htight (η / 2) (ENNReal.half_pos hη.ne')
  set R : ℝ := ‖B‖ * |M| + ε with hR
  have hq : Continuous fun h : E ↦ ⟪h, A h⟫_ℝ / 2 :=
    (continuous_id.inner A.continuous).div_const 2
  have hunif := tendsto_measure_exists_abs_sub_of_convexOn
    (fun n ω h ↦ Z n ω h + ⟪U n ω, h⟫_ℝ)
    (fun n ω ↦ (hZ n ω).add (((innerSL ℝ (U n ω)) : E →ₗ[ℝ] ℝ).convexOn convex_univ)) hq
    (fun h ε hε ↦ by simpa only [add_sub_assoc] using hpt h ε hε) R
    (by positivity : 0 < c * ε ^ 2 / 4)
  have hunif' := ENNReal.tendsto_nhds_zero.1 hunif (η / 2) (ENNReal.half_pos hη.ne')
  filter_upwards [hmin, hM, hunif'] with n hn hMn hun
  have hsub : {ω | ε ≤ ‖α n ω - B (U n ω) - 0‖} ⊆
      {ω | M < ‖U n ω‖} ∪ {ω | ∃ h, ‖h‖ ≤ R ∧
        c * ε ^ 2 / 4 ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|} ∪
      {ω | ¬ ∀ h, Z n ω (α n ω) ≤ Z n ω h} := by
    intro ω hω
    simp only [sub_zero, mem_ofPred_eq] at hω
    by_contra hω'
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_exists, not_and, not_le,
      not_not] at hω'
    obtain ⟨⟨hUM, hgood⟩, hmin'⟩ := hω'
    set β := B (U n ω) with hβ
    have hUβ : U n ω = A β := (hAB _).symm
    have hβR : ‖β‖ ≤ ‖B‖ * |M| :=
      (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hUM.trans (le_abs_self M))
        (norm_nonneg _))
    refine (norm_sub_lt_of_convexOn_of_abs_sub_lt (hZ n ω) A hA hε
      (C := -(⟪β, A β⟫_ℝ / 2)) (fun h hh ↦ ?_) (hmin' β)).not_ge hω
    have hhR : ‖h‖ ≤ R := by
      calc ‖h‖ = ‖(h - β) + β‖ := by rw [sub_add_cancel]
        _ ≤ ‖h - β‖ + ‖β‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    have hid : Z n ω h - (-(⟪β, A β⟫_ℝ / 2) + ⟪h - β, A (h - β)⟫_ℝ / 2) =
        Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2 := by
      have h1 : ⟪β, A h⟫_ℝ = ⟪U n ω, h⟫_ℝ := by rw [hUβ, hAsymm]
      have h2 : ⟪h, A β⟫_ℝ = ⟪U n ω, h⟫_ℝ := by rw [hUβ, real_inner_comm]
      simp only [map_sub, inner_sub_left, inner_sub_right, h1, h2]
      ring
    rw [hid]
    exact hgood h hhR
  calc μ {ω | ε ≤ ‖α n ω - B (U n ω) - 0‖}
      ≤ μ {ω | M < ‖U n ω‖} + μ {ω | ∃ h, ‖h‖ ≤ R ∧
          c * ε ^ 2 / 4 ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|} +
        μ {ω | ¬ ∀ h, Z n ω (α n ω) ≤ Z n ω h} :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add_left (measure_union_le _ _) _))
    _ ≤ η / 2 + η / 2 + 0 := by
      gcongr
      exact le_of_eq (ae_iff.1 hn)
    _ = η := by rw [add_zero, ENNReal.add_halves]

end Argmin

end CKSD
