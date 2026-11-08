module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import TauCeti.Probability.Distributions.Gaussian.Projection
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared

/-!
# Gaussian linear models: Gauss–Markov and the residual law

The linear model `Y = μ + ε` on `ℝⁿ`, with mean `μ` in the range of an orthogonal projection `P`
(a star projection: idempotent and self-adjoint), fitted value `P Y` and residual `Y - P Y`.

## Main results

* `CKSD.integral_inner_map_eq_of_map_integral_eq`, `CKSD.variance_inner_map_le`: the scalar
  Gauss–Markov comparison. If `P E[Y] = E[Y]`, then `⟪P a, Y⟫` is unbiased for the same
  functional as `⟪a, Y⟫`, and with uncorrelated coordinates of common variance it has no larger
  variance.
* `CKSD.map_norm_sq_sub_div_eq_chiSquared`: for `Y ∼ N(μ, σ² I)` with `P μ = μ`, the scaled
  residual sum of squares `‖Y - P Y‖² / σ²` has the chi-squared law with `n - rank P` degrees of
  freedom.
* `CKSD.indepFun_map_norm_sq_sub`: the fitted value `P Y` and the residual sum of squares are
  independent.
* `CKSD.indepFun_matrixQuadraticForm_iff`: the Craig–Sakamoto criterion for independence of
  two Gaussian quadratic forms.

The exact F law of nested models is in `CKSD.LinearModels.FTest`. The residual law uses
TauCeti's projection and affine-image results for standard Gaussian measures.

## References

* H. Scheffé, *The Analysis of Variance*, Wiley, 1959.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- A star projection is idempotent, pointwise. -/
theorem IsStarProjection.apply_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {P : E →L[ℝ] E} (hP : IsStarProjection P) (x : E) :
    P (P x) = P x :=
  congr($(hP.isIdempotentElem.eq) x)

/-- A star projection is symmetric for the inner product. -/
theorem IsStarProjection.inner_map_left {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {P : E →L[ℝ] E} (hP : IsStarProjection P)
    (x y : E) : inner ℝ (P x) y = inner ℝ x (P y) :=
  hP.isSelfAdjoint.isSymmetric x y

/-- A star projection is the orthogonal projection onto its range. -/
theorem IsStarProjection.starProjection_range_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {P : E →L[ℝ] E} (hP : IsStarProjection P)
    [(LinearMap.range P.toLinearMap).HasOrthogonalProjection] (x : E) :
    (LinearMap.range P.toLinearMap).starProjection x = P x := by
  obtain ⟨_, h⟩ := _root_.isStarProjection_iff_eq_starProjection_range.1 hP
  exact (congr($h x)).symm

/-- With uncorrelated coordinates of common variance `v`, the variance of `⟪b, Y⟫` is
`v ‖b‖²`. -/
theorem variance_inner_of_covariance_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (b : EuclideanSpace ℝ (Fin n)) :
    variance μ (fun ω ↦ inner ℝ b (Y ω)) = v * ‖b‖ ^ 2 := by
  have hYi : ∀ i, MemLp (fun ω ↦ Y ω i) 2 μ := fun i ↦
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hY
  have hbY : ∀ i, MemLp (fun ω ↦ b i * Y ω i) 2 μ := fun i ↦ (hYi i).const_mul (b i)
  have hinner : (fun ω ↦ inner ℝ b (Y ω)) = fun ω ↦ ∑ i, b i * Y ω i := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have hmeas : AEMeasurable (fun ω ↦ inner ℝ b (Y ω)) μ := by
    exact (aestronglyMeasurable_const.inner hY.aestronglyMeasurable).aemeasurable
  have hvar : variance μ (fun ω ↦ inner ℝ b (Y ω)) =
      ProbabilityTheory.variance (fun ω ↦ inner ℝ b (Y ω)) μ :=
    (ProbabilityTheory.variance_eq_integral hmeas).symm
  rw [hvar, ← covariance_self hmeas, hinner,
    covariance_fun_sum_fun_sum hbY hbY]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  have := hcov
  simp only [covariance] at this
  simp_rw [this, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- GAPS 105.1, scalar Gauss–Markov comparison, unbiasedness: if the mean of `Y` lies in the
range of the star projection `P`, then `⟪P a, Y⟫` and `⟪a, Y⟫` have the same expectation. -/
theorem integral_inner_map_eq_of_map_integral_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (Y : Ω → EuclideanSpace ℝ (Fin n)) (hY : Integrable Y μ)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsStarProjection P)
    (hm : P (∫ ω, Y ω ∂μ) = ∫ ω, Y ω ∂μ) (a : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (P a) (Y ω) ∂μ) = ∫ ω, inner ℝ a (Y ω) ∂μ := by
  rw [integral_inner hY, integral_inner hY, IsStarProjection.inner_map_left hP, hm]

/-- GAPS 105.1, scalar Gauss–Markov comparison, variance: if the coordinates of `Y` are
uncorrelated with common variance `v ≥ 0`, then for every star projection `P` the variance of
`⟪P a, Y⟫` is at most that of `⟪a, Y⟫`. Together with
`integral_inner_map_eq_of_map_integral_eq` this says that projecting the coefficient vector of
a linear unbiased estimator onto the model space does not increase its variance. -/
theorem variance_inner_map_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ) (hv : 0 ≤ v)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsStarProjection P)
    (a : EuclideanSpace ℝ (Fin n)) :
    variance μ (fun ω ↦ inner ℝ (P a) (Y ω)) ≤ variance μ (fun ω ↦ inner ℝ a (Y ω)) := by
  rw [variance_inner_of_covariance_eq μ Y hY v hcov, variance_inner_of_covariance_eq μ Y hY v hcov]
  refine mul_le_mul_of_nonneg_left ?_ hv
  have horth : inner ℝ (P a) (a - P a) = 0 := by
    rw [inner_sub_right, IsStarProjection.inner_map_left hP a (P a),
      IsStarProjection.apply_apply hP, real_inner_comm, sub_self]
  have : ‖a‖ ^ 2 = ‖P a‖ ^ 2 + ‖a - P a‖ ^ 2 := by
    have h := norm_add_sq_real (P a) (a - P a)
    rw [horth, mul_zero, add_zero, add_sub_cancel] at h
    exact h
  rw [this]
  nlinarith [sq_nonneg ‖a - P a‖]

/-- The Gaussian law `N(m, v I)` is the image of the standard Gaussian measure under
`z ↦ m + √v z`. -/
theorem multivariateGaussian_smul_one_eq_map {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) :
    multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun z ↦ m + Real.sqrt v • z) := by
  have h := TauCeti.Probability.map_add_smul_multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin n)) (Matrix.PosSemidef.one) m (Real.sqrt v)
  simpa only [multivariateGaussian_zero_one, smul_zero, add_zero,
    Real.sq_sqrt v.coe_nonneg] using h.symm

/-- Under `N(m, v I)` with `v > 0`, the standardized vector `(x - m) / √v` is standard
Gaussian. -/
theorem hasLaw_smul_sub_multivariateGaussian {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0)
    (hv : 0 < v) :
    HasLaw (fun x ↦ (Real.sqrt v)⁻¹ • (x - m)) (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  refine ⟨by fun_prop, ?_⟩
  rw [multivariateGaussian_smul_one_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (fun x ↦ (Real.sqrt v)⁻¹ • (x - m)) ∘ (fun z ↦ m + Real.sqrt v • z) = id := by
    funext z
    simp [smul_smul, hs.ne']
  rw [hid, Measure.map_id]

/-- GAPS 105.2, residual chi-squared law: for `Y ∼ N(m, v I_n)` with `v > 0` and `m` in the
range of the star projection `P`, the scaled residual sum of squares `‖Y - P Y‖² / v` has the
chi-squared law with `n - rank P` degrees of freedom. -/
theorem map_norm_sq_sub_div_eq_chiSquared {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0)
    (hv : 0 < v) (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : IsStarProjection P) (hm : P m = m) :
    (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))).map
        (fun x ↦ ‖x - P x‖ ^ 2 / v) =
      TauCeti.Probability.chiSquaredMeasure
        (n - Module.finrank ℝ (LinearMap.range P.toLinearMap) : ℕ) := by
  let K := LinearMap.range P.toLinearMap
  have hdim : Module.finrank ℝ Kᗮ = n - Module.finrank ℝ K := by
    have h := K.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace_fin] at h
    omega
  have hs2 : Real.sqrt (v : ℝ) ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have hZ := hasLaw_smul_sub_multivariateGaussian m v hv
  have hnorm : ∀ x, ‖Kᗮ.orthogonalProjectionOnto ((Real.sqrt (v : ℝ))⁻¹ • (x - m))‖ ^ 2 = ‖x - P x‖ ^ 2 / v := by
    intro x
    change ‖Kᗮ.starProjection ((Real.sqrt (v : ℝ))⁻¹ • (x - m))‖ ^ 2 = _
    rw [K.starProjection_orthogonal_val, IsStarProjection.starProjection_range_apply hP]
    have hpt : (Real.sqrt (v : ℝ))⁻¹ • (x - m) - P ((Real.sqrt (v : ℝ))⁻¹ • (x - m)) = (Real.sqrt (v : ℝ))⁻¹ • (x - P x) := by
      simp only [map_smul, map_sub, hm]
      module
    rw [hpt, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs2, div_eq_inv_mul]
  simpa only [hnorm, hdim] using (hZ.norm_sq_orthogonalProjectionOnto_stdGaussian Kᗮ).map_eq

/-- GAPS 105.2, projection independence: for `Y ∼ N(m, v I_n)` with `v > 0` and any star
projection `P`, the fitted value `P Y` and the residual sum of squares `‖Y - P Y‖²` are
independent. -/
theorem indepFun_map_norm_sq_sub {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0)
    (hv : 0 < v) (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : IsStarProjection P) :
    IndepFun P (fun x ↦ ‖x - P x‖ ^ 2)
      (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  let K := LinearMap.range P.toLinearMap
  set s := Real.sqrt (v : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  have hZ := hasLaw_smul_sub_multivariateGaussian m v hv
  let Ks : Bool → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun b ↦ if b then K else Kᗮ
  have horth : Pairwise fun i j ↦ (Ks i).IsOrtho (Ks j) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact K.isOrtho_orthogonal_left
    · exact K.isOrtho_orthogonal_right
    · exact (hij rfl).elim
  have hi := (hZ.iIndepFun_orthogonalProjectionOnto_stdGaussian Ks horth).indepFun
    (show true ≠ false by decide)
  have hfit : ∀ x, P m + s • (K.orthogonalProjectionOnto (s⁻¹ • (x - m)) :
      EuclideanSpace ℝ (Fin n)) = P x := by
    intro x
    change P m + s • K.starProjection (s⁻¹ • (x - m)) = P x
    rw [IsStarProjection.starProjection_range_apply hP]
    simp only [map_smul, map_sub, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  have hres : ∀ x, ‖(m - P m) + s • (Kᗮ.orthogonalProjectionOnto (s⁻¹ • (x - m)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 = ‖x - P x‖ ^ 2 := by
    intro x
    change ‖(m - P m) + s • Kᗮ.starProjection (s⁻¹ • (x - m))‖ ^ 2 = _
    rw [K.starProjection_orthogonal_val, IsStarProjection.starProjection_range_apply hP]
    congr 2
    simp only [map_smul, map_sub, smul_sub, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  have h := hi.comp (φ := fun z : K ↦ P m + s • (z : EuclideanSpace ℝ (Fin n)))
    (ψ := fun z : Kᗮ ↦ ‖(m - P m) + s • (z : EuclideanSpace ℝ (Fin n))‖ ^ 2)
    (by fun_prop) (by fun_prop)
  change IndepFun (fun x ↦ P m + s • (K.orthogonalProjectionOnto (s⁻¹ • (x - m)) :
      EuclideanSpace ℝ (Fin n)))
    (fun x ↦ ‖(m - P m) + s • (Kᗮ.orthogonalProjectionOnto (s⁻¹ • (x - m)) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2) _ at h
  simpa only [hfit, hres] using h

/-- GAPS 105.15, Craig–Sakamoto criterion: for `Y ∼ N(0, Σ)` with `Σ` positive definite and
symmetric matrices `A`, `B`, the quadratic forms `Yᵀ A Y` and `Yᵀ B Y` are independent if and
only if `A Σ B = 0`. -/
theorem indepFun_matrixQuadraticForm_iff {n : ℕ} (Sigma A B : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm) :
    IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B)
      (multivariateGaussian 0 Sigma) ↔ A * Sigma * B = 0 := by
  sorry

end CKSD
