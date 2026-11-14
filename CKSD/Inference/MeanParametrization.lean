module

public import CKSD.Inference.ExponentialFamily
public import CKSD.Inference.LogPartition
public import CKSD.Inference.ExponentialFamilyMLE
public import Mathlib.Analysis.Calculus.MeanValue


/-!
# The mean map of a natural exponential family

For a nonzero base measure `ν` on a finite-dimensional real inner product space `E` whose natural
parameter space `N` is open, the mean map `M η = ∫ x dP_η(x)` of the natural exponential family
`P_η = exponentialFamilyMeasure ν id η` is the gradient of the log partition function. When the
family is minimal, the Hessian of the log partition function is positive definite, so `M` is
injective on `N`, has invertible derivative, and takes values in the interior of the convex hull
of the support of `ν`.

## Main results

* `CKSD.analytic_on_nhd_mean_exponential_family_measure`: `M` is real analytic on `N`.
* `CKSD.inj_on_mean_exponential_family_measure`: `M` is injective on `N` for a minimal family.
* `CKSD.mean_exponential_family_measure_mem_interior_convex_hull_support`: `M η` lies in the
  interior of the convex hull of the support of `ν`.
* `CKSD.exists_has_strict_f_deriv_at_mean_exponential_family_measure`: the derivative of `M` at a point
  of `N` is a continuous linear equivalence.

## Implementation notes

The gradient of the log partition function is converted to a vector through a fixed orthonormal
basis; injectivity follows from the mean value theorem along segments, and the location of the
mean from a separating hyperplane together with minimality.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Riesz map `f ↦ ∑ f (bᵢ) bᵢ` from functionals to vectors, along an orthonormal basis. -/
private def rieszVec (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.apply ℝ ℝ (stdOrthonormalBasis ℝ E i)).smulRight
    (stdOrthonormalBasis ℝ E i)

/-- `⟪rieszVec f, u⟫ = f u`. -/
private theorem inner_riesz_vec (f : E →L[ℝ] ℝ) (u : E) : inner ℝ (rieszVec E f) u = f u := by
  set b := stdOrthonormalBasis ℝ E
  simp only [rieszVec, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply, sum_inner,
    real_inner_smul_left]
  conv_rhs => rw [← b.sum_repr' u]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- `rieszVec ⟪m, ·⟫ = m`. -/
private theorem riesz_vec_inner_sl (m : E) : rieszVec E (innerSL ℝ m) = m :=
  ext_inner_right ℝ fun u ↦ by rw [inner_riesz_vec, innerSL_apply_apply]

variable [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The base measure is absolutely continuous with respect to every law of the family. -/
private theorem absolutely_continuous_exponential_family_measure (ν : Measure E) (η : E) :
    ν ≪ exponentialFamilyMeasure ν id η :=
  withDensity_absolutelyContinuous' (by fun_prop) (ae_of_all _ fun x ↦ by simp [Real.exp_pos])

/-- In a minimal family the covariance form of an interior law is positive definite. -/
private theorem covariance_inner_pos (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) {η : E}
    (hη : η ∈ interior (naturalParameterSpace ν id)) {u : E} (hu : u ≠ 0) :
    0 < cov[fun x ↦ inner ℝ u x, fun x ↦ inner ℝ u x; exponentialFamilyMeasure ν id η] := by
  have := is_probability_measure_exponential_family_measure ν hne hη
  have hL2 := mem_lp_inner_exponential_family_measure ν hne hη u
  rw [covariance_self hL2.aemeasurable]
  refine lt_of_le_of_ne (variance_nonneg _ _) fun h ↦ ?_
  have hae := ae_eq_integral_of_variance_eq_zero hL2 h.symm
  exact hminimal u hu _ (absolutely_continuous_exponential_family_measure ν η |>.ae_le hae)

/-- Near a point of an open natural parameter space, the mean map is the Riesz vector of the
derivative of the log partition function. -/
private theorem mean_eventually_eq_riesz_vec_fderiv (ν : Measure E) (hne : ν ≠ 0)
    (hN : IsOpen (naturalParameterSpace ν id)) {η : E} (hη : η ∈ naturalParameterSpace ν id) :
    (fun ζ ↦ ∫ x, x ∂exponentialFamilyMeasure ν id ζ) =ᶠ[𝓝 η]
      rieszVec E ∘ fderiv ℝ (logPartition ν id) := by
  filter_upwards [hN.mem_nhds hη] with ζ hζ
  simp only [Function.comp_apply,
    (has_f_deriv_at_log_partition ν hne (hN.interior_eq.symm ▸ hζ)).fderiv, riesz_vec_inner_sl]

/-- On an open natural parameter space, the derivative of the log partition function is
differentiable. -/
private theorem has_f_deriv_at_fderiv_log_partition (ν : Measure E) (hne : ν ≠ 0)
    (hN : IsOpen (naturalParameterSpace ν id)) {η : E} (hη : η ∈ naturalParameterSpace ν id) :
    HasFDerivAt (fderiv ℝ (logPartition ν id))
      (fderiv ℝ (fderiv ℝ (logPartition ν id)) η) η :=
  ((analytic_on_nhd_log_partition ν hne η (hN.interior_eq.symm ▸ hη)).fderiv).differentiableAt
    |>.hasFDerivAt

/-- The derivative of the mean map is the Riesz image of the Hessian of the log partition
function. -/
private theorem has_f_deriv_at_mean (ν : Measure E) (hne : ν ≠ 0)
    (hN : IsOpen (naturalParameterSpace ν id)) {η : E} (hη : η ∈ naturalParameterSpace ν id) :
    HasFDerivAt (fun ζ ↦ ∫ x, x ∂exponentialFamilyMeasure ν id ζ)
      ((rieszVec E).comp (fderiv ℝ (fderiv ℝ (logPartition ν id)) η)) η :=
  ((rieszVec E).hasFDerivAt.comp η (has_f_deriv_at_fderiv_log_partition ν hne hN hη))
    |>.congr_of_eventuallyEq (mean_eventually_eq_riesz_vec_fderiv ν hne hN hη)

/-- In a minimal family the Hessian of the log partition function is positive definite at every
point of an open natural parameter space. -/
private theorem fderiv_fderiv_log_partition_pos (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    {η : E} (hη : η ∈ naturalParameterSpace ν id) {u : E} (hu : u ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (logPartition ν id)) η u u := by
  have hη' : η ∈ interior (naturalParameterSpace ν id) := hN.interior_eq.symm ▸ hη
  rw [fderiv_fderiv_log_partition_apply ν hne hη']
  exact covariance_inner_pos ν hne hminimal hη' hu

/-- The mean map of a natural exponential family with open natural parameter space `N` is real
analytic on `N`. -/
theorem analytic_on_nhd_mean_exponential_family_measure (ν : Measure E) (hne : ν ≠ 0)
    (hN : IsOpen (naturalParameterSpace ν id)) :
    AnalyticOnNhd ℝ (fun η ↦ ∫ x, x ∂exponentialFamilyMeasure ν id η)
      (naturalParameterSpace ν id) := fun η hη ↦
  (((rieszVec E).analyticAt _).comp
      ((hN.interior_eq ▸ analytic_on_nhd_log_partition ν hne).fderiv η hη)).congr
    (mean_eventually_eq_riesz_vec_fderiv ν hne hN hη).symm

/-- The mean map of a minimal natural exponential family with open natural parameter space `N` is
injective on `N`. -/
theorem inj_on_mean_exponential_family_measure (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id)) :
    InjOn (fun η ↦ ∫ x, x ∂exponentialFamilyMeasure ν id η) (naturalParameterSpace ν id) := by
  intro η hη ζ hζ hMηζ
  by_contra hne'
  set A := logPartition ν id
  set w := η - ζ with hw
  have hw0 : w ≠ 0 := sub_ne_zero.2 hne'
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, ζ + s • w ∈ naturalParameterSpace ν id := fun s hs ↦
    (convex_natural_parameter_space ν).add_smul_sub_mem hζ hη hs
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s ↦ fderiv ℝ A (ζ + s • w) w)
      (fderiv ℝ (fderiv ℝ A) (ζ + s • w) w w) s := fun s hs ↦ by
    have h1 := (has_f_deriv_at_fderiv_log_partition ν hne hN (hγ s hs)).clm_apply
      (hasFDerivAt_const w (ζ + s • w))
    have h2 : HasDerivAt (fun s : ℝ ↦ ζ + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add ζ
    convert h1.comp_hasDerivAt s h2 using 1
    · rfl
    · simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.flip_apply, zero_add]; rfl
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope
    (fun s ↦ fderiv ℝ A (ζ + s • w) w) (fun s ↦ fderiv ℝ (fderiv ℝ A) (ζ + s • w) w w)
    zero_lt_one (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ hderiv s (Ioo_subset_Icc_self hs))
  have hc0 := fderiv_fderiv_log_partition_pos ν hne hminimal hN
    (hγ c (Ioo_subset_Icc_self hc)) hw0
  simp only [zero_smul, add_zero, one_smul, hw, add_sub_cancel, sub_zero, div_one] at hcd
  rw [(has_f_deriv_at_log_partition ν hne (hN.interior_eq.symm ▸ hη)).fderiv,
    (has_f_deriv_at_log_partition ν hne (hN.interior_eq.symm ▸ hζ)).fderiv, innerSL_apply_apply,
    innerSL_apply_apply] at hcd
  simp only at hMηζ
  rw [hMηζ, sub_self] at hcd
  rw [hw] at hc0
  linarith

/-- For a minimal natural exponential family with open natural parameter space, the mean of every
law of the family lies in the interior of the convex hull of the support of the base measure. -/
theorem mean_exponential_family_measure_mem_interior_convex_hull_support (ν : Measure E)
    (hne : ν ≠ 0) (hminimal : IsMinimalExponentialFamily ν id)
    (hN : IsOpen (naturalParameterSpace ν id)) {η : E} (hη : η ∈ naturalParameterSpace ν id) :
    (∫ x, x ∂exponentialFamilyMeasure ν id η) ∈ interior (convexHull ℝ ν.support) := by
  have hη' : η ∈ interior (naturalParameterSpace ν id) := hN.interior_eq.symm ▸ hη
  set m := ∫ x, x ∂exponentialFamilyMeasure ν id η
  by_contra ht
  have hsupp : ν.support.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := Measure.measure_compl_support (μ := ν)
    rw [h, compl_empty] at this
    exact hne (Measure.measure_univ_eq_zero.1 this)
  obtain ⟨u, hu, hsep⟩ := exists_ne_zero_forall_inner_le_of_not_mem_interior
    (convex_convexHull ℝ ν.support) (hsupp.mono (subset_convexHull ℝ _)) ht
  set P := exponentialFamilyMeasure ν id η
  have := is_probability_measure_exponential_family_measure ν hne hη'
  have hPν : P ≪ ν := withDensity_absolutelyContinuous _ _
  have hle : ∀ᵐ x ∂P, inner ℝ u x ≤ inner ℝ u m := hPν.ae_le <|
    (show ∀ᵐ x ∂ν, x ∈ ν.support from Measure.support_mem_ae).mono fun x hx ↦
      hsep x (subset_convexHull ℝ _ hx)
  have hui : Integrable (fun x ↦ inner ℝ u x) P :=
    (mem_lp_inner_exponential_family_measure ν hne hη' u).integrable one_le_two
  have hmean : ∫ x, inner ℝ u x ∂P = inner ℝ u m :=
    integral_inner (integrable_id_exponential_family_measure ν hne hη') u
  have h0 : ∫ x, (inner ℝ u m - inner ℝ u x) ∂P = 0 := by
    rw [integral_sub (integrable_const _) hui, hmean, integral_const, probReal_univ, one_smul,
      sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun x hx ↦ sub_nonneg.2 hx)
    ((integrable_const _).sub hui)).1 h0
  refine hminimal u hu (inner ℝ u m)
    (absolutely_continuous_exponential_family_measure ν η |>.ae_le (hae.mono fun x hx ↦ ?_))
  simp only [Pi.zero_apply, sub_eq_zero] at hx
  exact hx.symm

/-- For a minimal natural exponential family with open natural parameter space `N`, the mean map
has at every point of `N` a strict derivative that is a continuous linear equivalence. -/
theorem exists_has_strict_f_deriv_at_mean_exponential_family_measure (ν : Measure E) (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    {η : E} (hη : η ∈ naturalParameterSpace ν id) :
    ∃ i : E ≃L[ℝ] E, fderiv ℝ (fun ζ ↦ ∫ x, x ∂exponentialFamilyMeasure ν id ζ) η = i ∧
      HasStrictFDerivAt (fun ζ ↦ ∫ x, x ∂exponentialFamilyMeasure ν id ζ) (i : E →L[ℝ] E) η := by
  set D : E →L[ℝ] E := (rieszVec E).comp (fderiv ℝ (fderiv ℝ (logPartition ν id)) η)
  have hDinj : Function.Injective D := by
    intro u v huv
    by_contra hne'
    have h0 : D (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hp := fderiv_fderiv_log_partition_pos ν hne hminimal hN hη (sub_ne_zero.2 hne')
    have h1 : fderiv ℝ (fderiv ℝ (logPartition ν id)) η (u - v) (u - v) =
        inner ℝ (D (u - v)) (u - v) := by
      simp only [D, ContinuousLinearMap.comp_apply, inner_riesz_vec]
    rw [h1, h0, inner_zero_left] at hp
    exact lt_irrefl _ hp
  set i : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (D : E →ₗ[ℝ] E) hDinj).toContinuousLinearEquiv
  have hi : (i : E →L[ℝ] E) = D := by ext u; rfl
  have hfd : fderiv ℝ (fun ζ ↦ ∫ x, x ∂exponentialFamilyMeasure ν id ζ) η = i := by
    rw [hi]; exact (has_f_deriv_at_mean ν hne hN hη).fderiv
  exact ⟨i, hfd,
    hfd ▸ (analytic_on_nhd_mean_exponential_family_measure ν hne hN η hη).hasStrictFDerivAt⟩

end CKSD
