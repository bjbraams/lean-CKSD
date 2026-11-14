module

public import CKSD.Inference.Model
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Convex.Intrinsic


/-!
# Maximum likelihood in natural exponential families

Existence, the likelihood equation, and uniqueness of the maximum likelihood estimator in a
regular minimal natural exponential family with base measure `ν` on a finite-dimensional inner
product space `E` and statistic the identity (GAPS 101.69).

## Main results

* `CKSD.exists_is_max_on_log_likelihood_iff_mem_interior_convex_hull_support`: the log likelihood
  of an observation `t` attains its maximum on the natural parameter space if and only if `t`
  lies in the interior of the convex hull of the support of `ν`.
* `CKSD.has_f_deriv_at_log_partition_and_eq_of_is_max_on`: a maximizer solves the likelihood equation
  `∇ logPartition ν id η = t` and is unique.
* `CKSD.exists_ne_zero_forall_inner_le_of_not_mem_interior`: a point outside the interior of a
  nonempty convex set is weakly separated from it.

## Implementation notes

Existence uses that the shifted partition function `η ↦ ∫⁻ exp ⟪η, x - t⟫ dν` is lower
semicontinuous and coercive when `t` is interior to the convex hull of the support; the converse
separates `t` from that convex hull. Differentiability of the log partition function on the
interior of the natural parameter space is proved by dominated differentiation under the
integral, and uniqueness by strict convexity of the log partition function for a minimal family.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The norm is at most the sum of the absolute coordinates in an orthonormal basis. -/
private theorem norm_le_sum_abs_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ≤ ∑ i, |inner ℝ (b i) x| := by
  conv_lhs => rw [← b.sum_repr' x]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]

section MaximumLikelihood

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point outside the interior of a convex set `C` of a finite-dimensional inner product space
is weakly separated from `C`: some `u ≠ 0` has `⟪u, x⟫ ≤ ⟪u, t⟫` for all `x ∈ C`. If `C` has
empty interior it lies in a hyperplane `⟪u, ·⟫ = c`, and `±u` works. -/
theorem exists_ne_zero_forall_inner_le_of_not_mem_interior [FiniteDimensional ℝ E]
    {C : Set E} (hC : Convex ℝ C) (hCne : C.Nonempty) {t : E} (ht : t ∉ interior C) :
    ∃ u : E, u ≠ 0 ∧ ∀ x ∈ C, inner ℝ u x ≤ inner ℝ u t := by
  rcases (interior C).eq_empty_or_nonempty with hint | hint
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun h ↦ by
      have := (hC.interior_nonempty_iff_affineSpan_eq_top).2 h
      rw [hint] at this; exact not_nonempty_empty this
    obtain ⟨x₀, hx₀⟩ := hCne
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := fun h ↦ hspan
      ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, subset_affineSpan ℝ C hx₀⟩).1 h)
    obtain ⟨u, hu, hu0⟩ : ∃ u ∈ (affineSpan ℝ C).directionᗮ, u ≠ 0 := by
      by_contra! h
      exact hdir (Submodule.orthogonal_eq_bot_iff.1 (eq_bot_iff.2 fun u hu ↦ h u hu))
    have hc : ∀ x ∈ C, inner ℝ u x = inner ℝ u x₀ := fun x hx ↦ by
      have hmem : x -ᵥ x₀ ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hx) (subset_affineSpan ℝ C hx₀)
      have := Submodule.inner_left_of_mem_orthogonal hmem hu
      rw [vsub_eq_sub, inner_sub_right] at this; linarith
    rcases le_total (inner ℝ u x₀) (inner ℝ u t) with h | h
    · exact ⟨u, hu0, fun x hx ↦ (hc x hx).trans_le h⟩
    · refine ⟨-u, neg_ne_zero.2 hu0, fun x hx ↦ ?_⟩
      rw [inner_neg_left, inner_neg_left, hc x hx]; linarith
  · obtain ⟨f, hf0, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point hC ht hint
    refine ⟨(InnerProductSpace.toDual ℝ E).symm f, fun h ↦ hf0 ?_, fun x hx ↦ ?_⟩
    · simpa using congrArg (InnerProductSpace.toDual ℝ E) h
    · simpa [InnerProductSpace.toDual_symm_apply] using hf x hx

/-- A finite subset of the convex hull of `A` lies in the convex hull of a finite subset of `A`. -/
private theorem exists_finset_subset_convex_hull_of_finite (A : Set E) (P : Finset E)
    (hP : ↑P ⊆ convexHull ℝ A) : ∃ F : Finset E, ↑F ⊆ A ∧ ↑P ⊆ convexHull ℝ (F : Set E) := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert z P _ ih =>
    obtain ⟨F, hFA, hPF⟩ := ih (fun x hx ↦ hP (Finset.mem_insert_of_mem hx))
    have hz := hP (Finset.mem_insert_self z P)
    rw [convexHull_eq_union_convexHull_finite_subsets] at hz
    simp only [mem_iUnion] at hz
    obtain ⟨G, hGA, hzG⟩ := hz
    refine ⟨F ∪ G, by simp [hFA, hGA], fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact convexHull_mono (by simp) hzG
    · exact convexHull_mono (by simp) (hPF hx)

/-- If `t` is an interior point of the convex hull of `A`, then finitely many points of `A`
surround `t` uniformly: there are a finite `F ⊆ A` and `κ > 0` such that every direction `η`
has some `y ∈ F` with `κ ‖η‖ ≤ ⟪η, y - t⟫`. -/
private theorem exists_finset_forall_exists_inner_ge [FiniteDimensional ℝ E] {A : Set E}
    {t : E}
    (ht : t ∈ interior (convexHull ℝ A)) :
    ∃ F : Finset E, ↑F ⊆ A ∧ ∃ κ > 0, ∀ η : E, ∃ y ∈ F, κ * ‖η‖ ≤ inner ℝ η (y - t) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ht)
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let z : Fin d × Bool → E := fun p ↦ t + ((if p.2 then 1 else -1) * (ε / 2)) • b p.1
  have hz : ∀ p, z p ∈ convexHull ℝ A := fun p ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, b.orthonormal.1 p.1,
      mul_one, Real.norm_eq_abs, abs_mul]
    split_ifs <;> simp [abs_of_pos (half_pos hε)] <;> linarith)
  obtain ⟨F, hFA, hPF⟩ := exists_finset_subset_convex_hull_of_finite A
    (insert t (Finset.univ.image z)) (by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, image_univ,
        mem_insert_iff, mem_range] at hx
      rcases hx with rfl | ⟨p, rfl⟩
      · exact interior_subset ht
      · exact hz p)
  refine ⟨F, hFA, ε / 2 / (d + 1), by positivity, fun η ↦ ?_⟩
  have hlin : ConvexOn ℝ univ (fun x : E ↦ inner ℝ η x) :=
    (innerSL ℝ η).toLinearMap.convexOn convex_univ
  have hgo : ∀ w ∈ insert t (Finset.univ.image z), ∃ y ∈ F, inner ℝ η (w - t) ≤
      inner ℝ η (y - t) := fun w hw ↦ by
    obtain ⟨y, hy, hwy⟩ := hlin.exists_ge_of_mem_convexHull (subset_univ _) (hPF hw)
    exact ⟨y, hy, by rw [inner_sub_right, inner_sub_right]; linarith⟩
  have hnorm := norm_le_sum_abs_inner b η
  have hκ0 : 0 ≤ ε / 2 / (d + 1) := by positivity
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hη : ‖η‖ = 0 := le_antisymm (by simpa using hnorm) (norm_nonneg _)
    obtain ⟨y, hy, hle⟩ := hgo t (Finset.mem_insert_self _ _)
    refine ⟨y, hy, ?_⟩
    rw [hη, mul_zero]
    simpa using hle
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |inner ℝ (b i) η|)
    Finset.univ_nonempty
  have hsum : ‖η‖ ≤ (d + 1) * |inner ℝ (b j) η| := by
    have h4 := hnorm.trans (Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ hj i hi)
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
    nlinarith [abs_nonneg (inner ℝ (b j) η)]
  obtain ⟨y, hy, hle⟩ := hgo (z (j, decide (0 ≤ inner ℝ (b j) η)))
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  refine ⟨y, hy, le_trans ?_ hle⟩
  have hzt : inner ℝ η (z (j, decide (0 ≤ inner ℝ (b j) η)) - t) =
      ε / 2 * |inner ℝ (b j) η| := by
    simp only [z, add_sub_cancel_left, inner_smul_right, real_inner_comm η]
    by_cases h : 0 ≤ inner ℝ (b j) η
    · have h' : 0 ≤ inner ℝ η (b j) := by rwa [real_inner_comm]
      simp [h', abs_of_nonneg h']
    · have h' : inner ℝ η (b j) < 0 := by rw [real_inner_comm]; exact not_le.1 h
      simp [h'.not_ge, abs_of_neg h']
  rw [hzt]
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
  nlinarith


/-- The partition function `∫ exp ⟪ζ, x⟫ dν` is positive on the natural parameter set when
`ν ≠ 0`. -/
private theorem integral_exp_inner_pos [MeasurableSpace E] (ν : Measure E) (hne : ν ≠ 0)
    {ζ : E}
    (hζ : ζ ∈ naturalParameterSpace ν id) : 0 < ∫ x, Real.exp (inner ℝ ζ x) ∂ν := by
  have hζ' : Integrable (fun x ↦ Real.exp (inner ℝ ζ x)) ν := hζ
  refine (integral_pos_iff_support_of_nonneg (fun x ↦ (Real.exp_pos _).le) hζ').2 ?_
  have : Function.support (fun x : E ↦ Real.exp (inner ℝ ζ x)) = univ :=
    Function.support_eq_univ fun x ↦ (Real.exp_pos _).ne'
  rw [this, pos_iff_ne_zero]
  exact (Measure.measure_univ_ne_zero).2 hne

/-- Coercivity of the shifted partition function: if `t` is interior to the convex hull of the
support of `ν`, then `∫⁻ exp ⟪η, x - t⟫ dν ≥ m exp (ρ ‖η‖)` for some `ρ > 0`, `m > 0` and all
`η`. -/
private theorem exists_lintegral_exp_inner_sub_ge [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]    (ν : Measure E) {t : E}
    (ht : t ∈ interior (convexHull ℝ ν.support)) :
    ∃ ρ > 0, ∃ m : ℝ≥0∞, 0 < m ∧ ∀ η : E, ENNReal.ofReal (Real.exp (ρ * ‖η‖)) * m ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ η (x - t))) ∂ν := by
  obtain ⟨F, hF, κ, hκ, hdir⟩ := exists_finset_forall_exists_inner_ge ht
  refine ⟨κ / 2, half_pos hκ, F.inf fun y ↦ ν (Metric.ball y (κ / 2)), ?_, fun η ↦ ?_⟩
  · rw [Finset.lt_inf_iff ENNReal.zero_lt_top]
    intro y hy
    exact (Measure.mem_support_iff_forall y).1 (hF hy) _ (Metric.ball_mem_nhds y (half_pos hκ))
  obtain ⟨y, hy, hyη⟩ := hdir η
  calc ENNReal.ofReal (Real.exp (κ / 2 * ‖η‖)) * F.inf (fun y ↦ ν (Metric.ball y (κ / 2)))
      ≤ ENNReal.ofReal (Real.exp (κ / 2 * ‖η‖)) * ν (Metric.ball y (κ / 2)) := by
        gcongr; exact Finset.inf_le hy
    _ = ∫⁻ x, (Metric.ball y (κ / 2)).indicator
          (fun _ ↦ ENNReal.ofReal (Real.exp (κ / 2 * ‖η‖))) x ∂ν :=
        (lintegral_indicator_const measurableSet_ball _).symm
    _ ≤ _ := lintegral_mono fun x ↦ by
        by_cases hx : x ∈ Metric.ball y (κ / 2)
        · rw [indicator_of_mem hx]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h1 : inner ℝ η (x - t) = inner ℝ η (y - t) + inner ℝ η (x - y) := by
            rw [← inner_add_right]; congr 1; abel
          have hxy : ‖x - y‖ < κ / 2 := by rwa [← dist_eq_norm, ← Metric.mem_ball]
          have h2 := neg_abs_le (inner ℝ η (x - y))
          have h3 := abs_real_inner_le_norm η (x - y)
          have h4 := mul_le_mul_of_nonneg_left hxy.le (norm_nonneg η)
          nlinarith
        · rw [indicator_of_notMem hx]; exact zero_le

/-- If the log likelihood of `t` attains its maximum on the natural parameter set of a minimal
family, then `t` is interior to the convex hull of the support: otherwise a separating direction
`u` gives `⟪u, x⟫ ≤ ⟪u, t⟫` a.e., not a.e. equal, and moving the parameter from `η` to `η + u`
strictly increases the likelihood. -/
private theorem mem_interior_convex_hull_support_of_is_max_on [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]    (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) {t η : E}
    (hη : η ∈ naturalParameterSpace ν id)
    (hmax : IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id)
      η) :
    t ∈ interior (convexHull ℝ ν.support) := by
  by_contra ht
  obtain ⟨u, hu0, hu⟩ := exists_ne_zero_forall_inner_le_of_not_mem_interior
    (convex_convexHull ℝ _) ((Measure.nonempty_support hne).mono (subset_convexHull ℝ _)) ht
  have hle : ∀ᵐ x ∂ν, inner ℝ u x ≤ inner ℝ u t := by
    filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
      using hu x (subset_convexHull ℝ _ hx)
  have hpos : ν {x | inner ℝ u x < inner ℝ u t} ≠ 0 := by
    intro h0
    refine hminimal u hu0 (inner ℝ u t) ?_
    filter_upwards [hle, measure_eq_zero_iff_ae_notMem.1 h0] with x h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  have hηi : Integrable (fun x ↦ Real.exp (inner ℝ η x)) ν := hη
  set g : E → ℝ := fun x ↦ Real.exp (inner ℝ (η + u) x) with hg
  have hg_eq : ∀ x, g x = Real.exp (inner ℝ u x) * Real.exp (inner ℝ η x) := fun x ↦ by
    simp only [g, inner_add_left, Real.exp_add, mul_comm]
  set h : E → ℝ := fun x ↦ Real.exp (inner ℝ u t) * Real.exp (inner ℝ η x) with hh
  have hgle : ∀ᵐ x ∂ν, g x ≤ h x := by
    filter_upwards [hle] with x hx
    rw [hg_eq]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hx) (by positivity)
  have hhi : Integrable h ν := hηi.const_mul _
  have hgi : Integrable g ν := hhi.mono' (by fun_prop : Continuous g).aestronglyMeasurable
    (by filter_upwards [hgle] with x hx; rw [Real.norm_of_nonneg (by positivity)]; exact hx)
  have hlt : ∫ x, g x ∂ν < ∫ x, h x ∂ν := by
    rw [← sub_pos, ← integral_sub hhi hgi]
    refine (integral_pos_iff_support_of_nonneg_ae (by
      filter_upwards [hgle] with x hx; simp only [Pi.zero_apply, Pi.sub_apply]; linarith)
      (hhi.sub hgi)).2 (pos_iff_ne_zero.2 fun h0 ↦ hpos (measure_mono_null (fun x hx ↦ ?_) h0))
    simp only [mem_ofPred_eq] at hx
    simp only [Function.mem_support, Pi.sub_apply, hg_eq, h]
    have := mul_lt_mul_of_pos_right (Real.exp_lt_exp.2 hx) (Real.exp_pos (inner ℝ η x))
    linarith
  have hmem : η + u ∈ naturalParameterSpace ν id := hgi
  have hgpos : 0 < ∫ x, g x ∂ν := integral_exp_inner_pos ν hne hmem
  have hZpos := integral_exp_inner_pos ν hne hη
  have key := hmax hmem
  simp only [mem_ofPred_eq, logPartition, id] at key
  have hlog : Real.log (∫ x, g x ∂ν) < inner ℝ u t + Real.log (∫ x, Real.exp (inner ℝ η x) ∂ν) := by
    have := Real.log_lt_log hgpos hlt
    rwa [hh, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
      at this
  rw [inner_add_left] at key
  linarith

/-- If `t` is interior to the convex hull of the support of `ν`, the log likelihood of `t` attains
its maximum on the natural parameter set: `η ↦ ∫⁻ exp ⟪η, x - t⟫ dν` is lower semicontinuous
(Fatou) and coercive, so it attains its minimum, which is finite. -/
private theorem exists_is_max_on_of_mem_interior [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]    (ν : Measure E) (hne : ν ≠ 0)
    (hNne : (naturalParameterSpace ν id).Nonempty) {t : E}
    (ht : t ∈ interior (convexHull ℝ ν.support)) :
    ∃ η ∈ naturalParameterSpace ν id,
        IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id) η := by
  set Φ : E → ℝ≥0∞ := fun η ↦ ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ η (x - t))) ∂ν with hΦ
  have hexp : ∀ η x : E, Real.exp (inner ℝ η (x - t)) =
      Real.exp (-inner ℝ η t) * Real.exp (inner ℝ η x) := by
    intro η x; rw [inner_sub_right, ← Real.exp_add]; ring_nf
  have hΦN : ∀ ζ ∈ naturalParameterSpace ν id, Φ ζ =
      ENNReal.ofReal (Real.exp (-inner ℝ ζ t) * ∫ x, Real.exp (inner ℝ ζ x) ∂ν) := by
    intro ζ hζ
    have hζ' : Integrable (fun x ↦ Real.exp (inner ℝ ζ x)) ν := hζ
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hζ'.const_mul _)
      (Eventually.of_forall fun x ↦ by positivity)]
    simp only [hΦ, hexp]
  have hNΦ : ∀ ζ, Φ ζ ≠ ⊤ → ζ ∈ naturalParameterSpace ν id := by
    intro ζ hζ
    have hi : Integrable (fun x ↦ Real.exp (inner ℝ ζ (x - t))) ν :=
      ⟨(by fun_prop : Continuous _).aestronglyMeasurable, by
        rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ (Real.exp_pos _).le)]
        exact hζ.lt_top⟩
    refine (hi.const_mul (Real.exp (inner ℝ ζ t))).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [id, hexp, ← Real.exp_add]
    ring_nf
  have hlsc : LowerSemicontinuous Φ := by
    refine lowerSemicontinuous_iff_le_liminf.2 fun η ↦ ?_
    calc Φ η = ∫⁻ x, liminf (fun ζ ↦ ENNReal.ofReal (Real.exp (inner ℝ ζ (x - t)))) (𝓝 η) ∂ν :=
          lintegral_congr fun x ↦ ((ENNReal.continuous_ofReal.comp (by fun_prop :
            Continuous fun ζ : E ↦
            Real.exp (inner ℝ ζ (x - t)))).tendsto η).liminf_eq.symm
      _ ≤ liminf Φ (𝓝 η) := lintegral_liminf_le fun ζ ↦
          (ENNReal.continuous_ofReal.comp (by fun_prop :
          Continuous fun x : E ↦ Real.exp (inner ℝ ζ (x - t)))).measurable
  obtain ⟨ρ, hρ, m, hm, hcoer⟩ := exists_lintegral_exp_inner_sub_ge ν ht
  obtain ⟨η₀, hη₀⟩ := hNne
  have hΦ₀ : Φ η₀ ≠ ⊤ := by rw [hΦN η₀ hη₀]; exact ENNReal.ofReal_ne_top
  set K := {η | Φ η ≤ Φ η₀} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (hlsc.isClosed_preimage _) ?_
    have hm'top : min m 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hm'0 : 0 < (min m 1).toReal :=
      ENNReal.toReal_pos (lt_min hm one_pos).ne' hm'top
    refine (Metric.isBounded_closedBall (x := (0 : E))
      (r := (Φ η₀).toReal / ((min m 1).toReal * ρ))).subset fun η hη ↦ ?_
    rw [mem_closedBall_zero_iff, le_div_iff₀ (by positivity)]
    have h1 : ENNReal.ofReal (Real.exp (ρ * ‖η‖) * (min m 1).toReal) ≤ Φ η₀ := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hm'top]
      exact (mul_le_mul_right (min_le_left _ _) _).trans ((hcoer η).trans hη)
    rw [ENNReal.ofReal_le_iff_le_toReal hΦ₀] at h1
    have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (ρ * ‖η‖)) hm'0.le
    nlinarith
  obtain ⟨η, hηK, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨η₀, show Φ η₀ ≤ Φ η₀ from le_rfl⟩ hKc
      (hlsc.lowerSemicontinuousOn K)
  have hηN : η ∈ naturalParameterSpace ν id := hNΦ η (ne_top_of_le_ne_top hΦ₀ hηK)
  refine ⟨η, hηN, fun ζ hζ ↦ ?_⟩
  have hle : Φ η ≤ Φ ζ := by
    by_cases hζK : ζ ∈ K
    · exact hmin hζK
    · exact hηK.trans (not_le.1 hζK).le
  have hZη := integral_exp_inner_pos ν hne hηN
  have hZζ := integral_exp_inner_pos ν hne hζ
  rw [hΦN η hηN, hΦN ζ hζ,
    ENNReal.ofReal_le_ofReal_iff (mul_pos (Real.exp_pos _) hZζ).le] at hle
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hZη) hle
  rw [Real.log_mul (Real.exp_pos _).ne' hZη.ne', Real.log_mul (Real.exp_pos _).ne' hZζ.ne',
    Real.log_exp, Real.log_exp] at hlog
  simp only [mem_ofPred_eq, logPartition, id]
  linarith

end MaximumLikelihood

/-- GAPS 101.69: existence of the maximum likelihood estimator in a regular minimal natural
exponential family. For the family with base measure `ν` on `E` and statistic the identity,
whose natural parameter space `N` is nonempty, the log likelihood
`η ↦ ⟪η, t⟫ - logPartition ν id η` of an observation `t` attains its maximum on `N` if and only
if `t` lies in the interior of the convex hull of the support of `ν`. Openness of `N` (regularity)
is not needed: the shifted partition function `η ↦ ∫⁻ exp ⟪η, x - t⟫ dν` is lower semicontinuous
and coercive on all of `E`, and is infinite off `N`. -/
theorem exists_is_max_on_log_likelihood_iff_mem_interior_convex_hull_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id)
    (hNne : (naturalParameterSpace ν id).Nonempty) (t : E) :
    (∃ η ∈ naturalParameterSpace ν id,
        IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id) η) ↔
      t ∈ interior (convexHull ℝ ν.support) :=
  ⟨fun ⟨_, hη, hmax⟩ ↦ mem_interior_convex_hull_support_of_is_max_on ν hne hminimal hη hmax,
    fun ht ↦ exists_is_max_on_of_mem_interior ν hne hNne ht⟩

/-- Near an interior point `η` of the natural parameter set, `‖x‖ exp ⟪ζ, x⟫` has an integrable
bound uniform in `ζ`; it uses the parameters `η ± K bᵢ` along an orthonormal basis. -/
private theorem exists_integrable_bound_norm_mul_exp_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) {N : Set E}
    (hNint : ∀ ζ ∈ N, Integrable (fun x ↦ Real.exp (inner ℝ ζ x)) ν) {η : E} (hη : N ∈ 𝓝 η) :
    ∃ r > 0, Metric.ball η r ⊆ N ∧ ∃ B : E → ℝ, Integrable B ν ∧
      ∀ x, ∀ ζ ∈ Metric.ball η r, ‖x‖ * Real.exp (inner ℝ ζ x) ≤ B x := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hη
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  set r : ℝ := ρ / (4 * (d + 1)) with hr
  have hr0 : 0 < r := by positivity
  set K : ℝ := 2 * r * (d + 1) with hK
  have hKρ : K < ρ := by
    rw [hK, hr]; field_simp; linarith
  have hK0 : 0 < K := by positivity
  have hmem : ∀ i (s : ℝ), |s| = 1 → η + (s * K) • b i ∈ N := fun i s hs ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, b.orthonormal.1 i,
      mul_one, Real.norm_eq_abs, abs_mul, hs, one_mul, abs_of_pos hK0]
    exact hKρ)
  refine ⟨r, hr0, fun ζ hζ ↦ hball (Metric.ball_subset_ball (by
    rw [hr]; apply div_le_self hρ.le; norm_cast; omega) hζ), fun x ↦ r⁻¹ * ∑ i,
      (Real.exp (inner ℝ (η + (1 * K) • b i) x) + Real.exp (inner ℝ (η + (-1 * K) • b i) x)),
    ?_, ?_⟩
  · have hi : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x ↦
        Real.exp (inner ℝ (η + (1 * K) • b i) x) +
          Real.exp (inner ℝ (η + (-1 * K) • b i) x)) ν := fun i _ ↦
      (hNint _ (hmem i 1 (by simp))).add (hNint _ (hmem i (-1) (by simp)))
    have := (integrable_finsetSum Finset.univ hi).const_mul r⁻¹
    exact this
  intro x ζ hζ
  have hBnn : 0 ≤ ∑ i, (Real.exp (inner ℝ (η + (1 * K) • b i) x) +
      Real.exp (inner ℝ (η + (-1 * K) • b i) x)) :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hx : ‖x‖ = 0 := le_antisymm (by simpa using norm_le_sum_abs_inner b x) (norm_nonneg _)
    rw [hx, zero_mul]
    exact mul_nonneg (inv_nonneg.2 hr0.le) hBnn
  have h1 : inner ℝ ζ x ≤ inner ℝ η x + r * ‖x‖ := by
    have : inner ℝ ζ x - inner ℝ η x ≤ r * ‖x‖ := by
      rw [← inner_sub_left]
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hζ).le
    linarith
  have h2 : ‖x‖ ≤ r⁻¹ * Real.exp (r * ‖x‖) := by
    rw [le_inv_mul_iff₀ hr0]
    linarith [Real.add_one_le_exp (r * ‖x‖)]
  have h12 : ‖x‖ * Real.exp (inner ℝ ζ x) ≤ r⁻¹ * Real.exp (inner ℝ η x + 2 * r * ‖x‖) := by
    calc ‖x‖ * Real.exp (inner ℝ ζ x) ≤ (r⁻¹ * Real.exp (r * ‖x‖)) *
          Real.exp (inner ℝ η x + r * ‖x‖) :=
          mul_le_mul h2 (Real.exp_le_exp.2 h1) (by positivity) (by positivity)
      _ = r⁻¹ * Real.exp (inner ℝ η x + 2 * r * ‖x‖) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  refine h12.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hr0.le))
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |inner ℝ (b i) x|)
    Finset.univ_nonempty
  have h3 : 2 * r * ‖x‖ ≤ K * |inner ℝ (b j) x| := by
    have h4 := (norm_le_sum_abs_inner b x).trans (Finset.sum_le_card_nsmul _ _ _
      fun i hi ↦ hj i hi)
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
    have h5 : (d : ℝ) * |inner ℝ (b j) x| ≤ (d + 1) * |inner ℝ (b j) x| := by
      nlinarith [abs_nonneg (inner ℝ (b j) x)]
    rw [hK]; nlinarith
  have hj1 : inner ℝ (η + (1 * K) • b j) x = inner ℝ η x + K * inner ℝ (b j) x := by
    rw [inner_add_left, inner_smul_left]; simp
  have hj2 : inner ℝ (η + (-1 * K) • b j) x = inner ℝ η x - K * inner ℝ (b j) x := by
    rw [inner_add_left, inner_smul_left]; simp; ring
  refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦ Real.exp (inner ℝ (η + (1 * K) • b i) x)
    + Real.exp (inner ℝ (η + (-1 * K) • b i) x)) (fun i _ ↦ by positivity) (Finset.mem_univ j))
  simp only [hj1, hj2]
  rcases le_total 0 (inner ℝ (b j) x) with h | h
  · rw [abs_of_nonneg h] at h3
    have := Real.exp_le_exp.2 (by linarith : inner ℝ η x + 2 * r * ‖x‖ ≤
      inner ℝ η x + K * inner ℝ (b j) x)
    linarith [Real.exp_pos (inner ℝ η x - K * inner ℝ (b j) x)]
  · rw [abs_of_nonpos h] at h3
    have := Real.exp_le_exp.2 (by linarith : inner ℝ η x + 2 * r * ‖x‖ ≤
      inner ℝ η x - K * inner ℝ (b j) x)
    linarith [Real.exp_pos (inner ℝ η x + K * inner ℝ (b j) x)]

/-- The log partition function is Fréchet differentiable at interior points of the natural
parameter space, by differentiation under the integral sign. -/
private theorem exists_has_f_deriv_at_log_partition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) (hne : ν ≠ 0) {η : E}
    (hη : naturalParameterSpace ν id ∈ 𝓝 η) :
    ∃ A' : E →L[ℝ] ℝ, HasFDerivAt (logPartition ν id) A' η := by
  have hNint : ∀ ζ ∈ naturalParameterSpace ν id,
      Integrable (fun x ↦ Real.exp (inner ℝ ζ x)) ν := fun ζ hζ ↦ hζ
  obtain ⟨r, hr0, -, B, hBi, hB⟩ := exists_integrable_bound_norm_mul_exp_inner ν hNint hη
  have hd : ∀ x ζ, HasFDerivAt (fun ζ : E ↦ Real.exp (inner ℝ ζ x))
      (Real.exp (inner ℝ ζ x) • innerSL ℝ x) ζ := fun x ζ ↦ by
    have h : HasFDerivAt (fun ζ : E ↦ inner ℝ ζ x) (innerSL ℝ x) ζ :=
      (innerSL ℝ x).hasFDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall fun ζ ↦ by simp [real_inner_comm])
    exact h.exp
  have hZ : HasFDerivAt (fun ζ : E ↦ ∫ x, Real.exp (inner ℝ ζ x) ∂ν)
      (∫ x, Real.exp (inner ℝ η x) • innerSL ℝ x ∂ν) η := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds η hr0)
      (Eventually.of_forall fun ζ ↦ (by fun_prop : Continuous fun x : E ↦
        Real.exp (inner ℝ ζ x)).aestronglyMeasurable)
      (hNint η (mem_of_mem_nhds hη))
      ((by fun_prop : Continuous fun x : E ↦
        Real.exp (inner ℝ η x) • innerSL ℝ x).aestronglyMeasurable)
      (ae_of_all _ fun x ζ hζ ↦ ?_) hBi (ae_of_all _ fun x ζ _ ↦ hd x ζ)
    rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact hB x ζ hζ
  have : NeZero ν := ⟨hne⟩
  have hpos : 0 < ∫ x, Real.exp (inner ℝ η x) ∂ν := integral_exp_pos (hNint η (mem_of_mem_nhds hη))
  exact ⟨_, hZ.log hpos.ne'⟩

/-- Strict midpoint convexity of the log partition function in a minimal family: the midpoint of
two distinct natural parameters is a natural parameter, and the log partition function there lies
strictly below the average. The proof is the equality case of the Cauchy–Schwarz inequality. -/
private theorem log_partition_midpoint_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) {ζ η : E}
    (hζ : ζ ∈ naturalParameterSpace ν id) (hη : η ∈ naturalParameterSpace ν id) (hζη : ζ ≠ η) :
    (2⁻¹ : ℝ) • (ζ + η) ∈ naturalParameterSpace ν id ∧
      logPartition ν id ((2⁻¹ : ℝ) • (ζ + η)) <
        (logPartition ν id ζ + logPartition ν id η) / 2 := by
  set m : E := (2⁻¹ : ℝ) • (ζ + η) with hm
  have hζi : Integrable (fun x ↦ Real.exp (inner ℝ ζ x)) ν := hζ
  have hηi : Integrable (fun x ↦ Real.exp (inner ℝ η x)) ν := hη
  set f : E → ℝ := fun x ↦ Real.exp (inner ℝ ζ x / 2) with hf
  set g : E → ℝ := fun x ↦ Real.exp (inner ℝ η x / 2) with hg
  have hf2 : ∀ x, f x ^ 2 = Real.exp (inner ℝ ζ x) := fun x ↦ by
    rw [hf, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hg2 : ∀ x, g x ^ 2 = Real.exp (inner ℝ η x) := fun x ↦ by
    rw [hg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hfg : ∀ x, f x * g x = Real.exp (inner ℝ m x) := fun x ↦ by
    rw [hf, hg, ← Real.exp_add, hm, inner_smul_left, inner_add_left]; congr 1; simp; ring
  have hmi : Integrable (fun x ↦ Real.exp (inner ℝ m x)) ν := by
    refine Integrable.mono' ((hζi.add hηi).div_const 2) (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← hfg]
    simp only [Pi.add_apply, ← hf2, ← hg2]
    nlinarith [sq_nonneg (f x - g x)]
  refine ⟨hmi, ?_⟩
  have : NeZero ν := ⟨hne⟩
  set Zζ := ∫ x, Real.exp (inner ℝ ζ x) ∂ν with hZζ
  set Zη := ∫ x, Real.exp (inner ℝ η x) ∂ν with hZη
  set Zm := ∫ x, Real.exp (inner ℝ m x) ∂ν with hZm
  have hZζp : 0 < Zζ := integral_exp_pos hζi
  have hZηp : 0 < Zη := integral_exp_pos hηi
  have hZmp : 0 < Zm := integral_exp_pos hmi
  set a := Real.sqrt Zζ with ha
  set c := Real.sqrt Zη with hc
  have ha0 : 0 < a := Real.sqrt_pos.2 hZζp
  have hc0 : 0 < c := Real.sqrt_pos.2 hZηp
  have ha2 : a ^ 2 = Zζ := Real.sq_sqrt hZζp.le
  have hc2 : c ^ 2 = Zη := Real.sq_sqrt hZηp.le
  -- the strict Cauchy–Schwarz inequality `Zm < a c`
  have hsq : ∀ x, (f x - a / c * g x) ^ 2 = Real.exp (inner ℝ ζ x) -
      2 * (a / c) * Real.exp (inner ℝ m x) + (a / c) ^ 2 * Real.exp (inner ℝ η x) := fun x ↦ by
    rw [← hf2, ← hg2, ← hfg]; ring
  have hint : Integrable (fun x ↦ (f x - a / c * g x) ^ 2) ν := by
    simp_rw [hsq]
    exact (hζi.sub (hmi.const_mul _)).add (hηi.const_mul _)
  have hI : ∫ x, (f x - a / c * g x) ^ 2 ∂ν = 2 * a ^ 2 - 2 * (a / c) * Zm := by
    simp_rw [hsq]
    have h1 : Integrable (fun x ↦ Real.exp (inner ℝ ζ x) - 2 * (a / c) * Real.exp (inner ℝ m x))
        ν := hζi.sub (hmi.const_mul _)
    rw [integral_add h1 (hηi.const_mul _),
      integral_sub hζi (hmi.const_mul _), integral_const_mul, integral_const_mul, ← hZζ, ← hZη,
      ← hZm, ← ha2, ← hc2]
    field_simp
    ring
  have hIpos : 0 < ∫ x, (f x - a / c * g x) ^ 2 ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun x ↦ sq_nonneg _) fun h ↦ ?_
    have h0 := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg _) hint).1 h.symm
    refine hminimal (ζ - η) (sub_ne_zero.2 hζη) (2 * Real.log (a / c)) ?_
    filter_upwards [h0] with x hx
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hx
    have hl := congrArg Real.log hx
    rw [hf, Real.log_exp, Real.log_mul (div_pos ha0 hc0).ne' (Real.exp_pos _).ne',
      Real.log_exp] at hl
    simp only [id, inner_sub_left]
    linarith
  have hlt : Zm < a * c := by
    rw [hI] at hIpos
    have : (a / c) * Zm < a ^ 2 := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hc0] at this
    nlinarith
  have hlog : Real.log Zm < (Real.log Zζ + Real.log Zη) / 2 := by
    have h1 := Real.log_lt_log hZmp hlt
    rw [Real.log_mul ha0.ne' hc0.ne', ← ha2, ← hc2, Real.log_pow, Real.log_pow] at *
    push_cast at *
    linarith
  exact hlog

/-- GAPS 101.69: in a regular minimal natural exponential family with open natural parameter
space `N`, a maximizer `η ∈ N` of the log likelihood `ζ ↦ ⟪ζ, t⟫ - logPartition ν id ζ` solves the
likelihood equation `∇ logPartition ν id η = t` (the mean of the law at `η` is `t`), and it is the
unique maximizer on `N`. -/
theorem has_f_deriv_at_log_partition_and_eq_of_is_max_on
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    {t η : E} (hη : η ∈ naturalParameterSpace ν id)
    (hmax : IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id) η) :
    HasFDerivAt (logPartition ν id) (innerSL ℝ t) η ∧
      ∀ ζ ∈ naturalParameterSpace ν id,
        inner ℝ ζ t - logPartition ν id ζ = inner ℝ η t - logPartition ν id η → ζ = η := by
  refine ⟨?_, fun ζ hζ heq ↦ ?_⟩
  · obtain ⟨A', hA⟩ := exists_has_f_deriv_at_log_partition ν hne (hN.mem_nhds hη)
    have hlin : HasFDerivAt (fun ζ : E ↦ inner ℝ ζ t) (innerSL ℝ t) η :=
      (innerSL ℝ t).hasFDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall fun ζ ↦ by simp [real_inner_comm])
    have h0 := (hmax.isLocalMax (hN.mem_nhds hη)).hasFDerivAt_eq_zero (hlin.sub hA)
    rwa [← sub_eq_zero.1 h0] at hA
  · by_contra hζη
    obtain ⟨hmN, hlt⟩ := log_partition_midpoint_lt ν hne hminimal hζ hη hζη
    have h1 : inner ℝ ((2⁻¹ : ℝ) • (ζ + η)) t - logPartition ν id ((2⁻¹ : ℝ) • (ζ + η)) ≤
        inner ℝ η t - logPartition ν id η := hmax hmN
    rw [real_inner_smul_left, inner_add_left] at h1
    linarith

end CKSD
