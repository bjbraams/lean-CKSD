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
import TauCeti.Probability.Distributions.Gaussian.QuadraticForm
import TauCeti.Probability.Distributions.Gaussian.Independence

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

The Craig–Sakamoto proof combines TauCeti's moment-generating function
`det (1 - 2t √Σ Θ √Σ) ^ (-1/2)` of a Gaussian quadratic form and its independence criterion for
linear images with a characteristic-polynomial comparison of fourth trace powers. The exact
F law of nested models is in `CKSD.LinearModels.FTest`. The residual law uses TauCeti's projection and affine-image results for standard Gaussian measures.

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
    (hcov : ∀ i j, cov[fun ω ↦ Y ω i, fun ω ↦ Y ω j; μ] = if i = j then v else 0)
    (b : EuclideanSpace ℝ (Fin n)) :
    Var[fun ω ↦ inner ℝ b (Y ω); μ] = v * ‖b‖ ^ 2 := by
  have hYi : ∀ i, MemLp (fun ω ↦ Y ω i) 2 μ := fun i ↦
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hY
  have hbY : ∀ i, MemLp (fun ω ↦ b i * Y ω i) 2 μ := fun i ↦ (hYi i).const_mul (b i)
  have hinner : (fun ω ↦ inner ℝ b (Y ω)) = fun ω ↦ ∑ i, b i * Y ω i := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have hmeas : AEMeasurable (fun ω ↦ inner ℝ b (Y ω)) μ := by
    exact (aestronglyMeasurable_const.inner hY.aestronglyMeasurable).aemeasurable
  rw [← covariance_self hmeas, hinner,
    covariance_fun_sum_fun_sum hbY hbY]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  simp_rw [hcov, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
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
    (hcov : ∀ i j, cov[fun ω ↦ Y ω i, fun ω ↦ Y ω j; μ] = if i = j then v else 0)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hP : IsStarProjection P)
    (a : EuclideanSpace ℝ (Fin n)) :
    Var[fun ω ↦ inner ℝ (P a) (Y ω); μ] ≤ Var[fun ω ↦ inner ℝ a (Y ω); μ] := by
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

section CraigSakamoto

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For symmetric real `X`, `Y`, the identity `tr (X + Y)⁴ + tr (X - Y)⁴ = 2 tr X⁴ + 2 tr Y⁴`
forces `X Y = 0`: the difference is `8 ‖X Y‖² + 4 tr ((X Y)²) ≥ 4 ‖X Y‖²` (Frobenius norm). -/
private theorem mul_eq_zero_of_trace_pow_four {X Y : Matrix ι ι ℝ} (hX : Xᵀ = X) (hY : Yᵀ = Y)
    (h : ((X + Y) ^ 4).trace + ((X - Y) ^ 4).trace = 2 * (X ^ 4).trace + 2 * (Y ^ 4).trace) :
    X * Y = 0 := by
  have hexp : (X + Y) ^ 4 + (X - Y) ^ 4 = (2 : ℝ) • X ^ 4 + (2 : ℝ) • Y ^ 4 +
      (2 : ℝ) • (X * X * Y * Y + X * Y * X * Y + X * Y * Y * X + Y * X * X * Y + Y * X * Y * X +
        Y * Y * X * X) := by
    simp only [pow_succ, pow_zero, Matrix.one_mul, two_smul]
    noncomm_ring
  have h1 : (X * X * Y * Y).trace = (X * Y * Y * X).trace := by
    rw [show X * X * Y * Y = X * (X * Y * Y) by noncomm_ring, trace_mul_comm]
  have h2 : (Y * X * X * Y).trace = (X * Y * Y * X).trace := by
    rw [show Y * X * X * Y = Y * (X * X * Y) by noncomm_ring, trace_mul_comm, h1]
  have h3 : (Y * Y * X * X).trace = (X * Y * Y * X).trace := by
    rw [show Y * Y * X * X = (Y * Y) * (X * X) by noncomm_ring, trace_mul_comm,
      show X * X * (Y * Y) = X * X * Y * Y by noncomm_ring, h1]
  have h4 : (Y * X * Y * X).trace = (X * Y * X * Y).trace := by
    rw [show Y * X * Y * X = Y * (X * Y * X) by noncomm_ring, trace_mul_comm]
  have htr := congrArg Matrix.trace hexp
  simp only [trace_add, trace_smul, smul_eq_mul] at htr
  rw [h1, h2, h3, h4] at htr
  set M := X * Y with hM
  have hMt : Mᵀ = Y * X := by rw [hM, transpose_mul, hX, hY]
  have e1 : (X * Y * Y * X).trace = ∑ i, ∑ j, M i j * M i j := by
    rw [show X * Y * Y * X = M * Mᵀ by rw [hMt, hM]; simp only [Matrix.mul_assoc]]
    simp [trace, Matrix.mul_apply]
  have e2 : (X * Y * X * Y).trace = ∑ i, ∑ j, M i j * M j i := by
    rw [show X * Y * X * Y = M * M by rw [hM]; simp only [Matrix.mul_assoc]]
    simp [trace, Matrix.mul_apply]
  rw [e1, e2] at htr
  have hsym : ∑ i, ∑ j, M j i * M j i = ∑ i, ∑ j, M i j * M i j := Finset.sum_comm
  have hnn : 0 ≤ ∑ i, ∑ j, (M i j + M j i) * (M i j + M j i) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _
  have hexp2 : ∑ i, ∑ j, (M i j + M j i) * (M i j + M j i) =
      2 * ∑ i, ∑ j, M i j * M i j + 2 * ∑ i, ∑ j, M i j * M j i := by
    have : ∑ i, ∑ j, (M i j + M j i) * (M i j + M j i) = ∑ i, ∑ j, M i j * M i j +
        2 * ∑ i, ∑ j, M i j * M j i + ∑ i, ∑ j, M j i * M j i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [this, hsym]
    ring
  have hzero : ∑ i, ∑ j, M i j * M i j = 0 := by
    have hnn' : 0 ≤ ∑ i, ∑ j, M i j * M i j :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _
    linarith
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ mul_self_nonneg (M i j)).1 hzero i (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_self_nonneg (M i j)).1 hi j
    (Finset.mem_univ j)
  simpa using mul_self_eq_zero.1 hij

open Polynomial in
/-- If `det (1 - s M) = det (1 - s P) det (1 - s Q)` for all small `s > 0`, for Hermitian `M`,
`P`, `Q`, then `X ^ dim · χ_M = χ_P χ_Q`, so the nonzero eigenvalues of `M` are those of `P` and
`Q` together and `tr Mᵏ = tr Pᵏ + tr Qᵏ` for `k ≠ 0`. -/
private theorem trace_pow_eq_add_of_det_one_sub_smul {M P Q : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s, 0 < s → s < ε → (1 - s • M).det = (1 - s • P).det * (1 - s • Q).det) {k : ℕ}
    (hk : k ≠ 0) : (M ^ k).trace = (P ^ k).trace + (Q ^ k).trace := by
  have key (N : Matrix ι ι ℝ) (x : ℝ) (hx : x ≠ 0) :
      (1 - x⁻¹ • N).det = x⁻¹ ^ Fintype.card ι * N.charpoly.eval x := by
    rw [eval_charpoly, ← det_smul]
    congr 1
    rw [smul_sub, scalar_apply]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [inv_mul_cancel₀ hx]
    · simp [hab]
  have hpoly : X ^ Fintype.card ι * M.charpoly = P.charpoly * Q.charpoly := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (fun x hx ↦ ?_) (Set.Ioi_infinite (1 / ε))
    have hx' : 1 / ε < x := hx
    have hxpos : 0 < x := lt_trans (by positivity) hx'
    have hs : x⁻¹ < ε := by
      rw [inv_lt_comm₀ hxpos hε]
      simpa using hx'
    have h' := h x⁻¹ (inv_pos.2 hxpos) hs
    rw [key M x hxpos.ne', key P x hxpos.ne', key Q x hxpos.ne'] at h'
    simp only [Set.mem_ofPred_eq, eval_mul, eval_pow, eval_X]
    have hxc : x ^ Fintype.card ι * x⁻¹ ^ Fintype.card ι = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hxpos.ne', one_pow]
    linear_combination (x ^ Fintype.card ι * x ^ Fintype.card ι) * h' +
      (-(x ^ Fintype.card ι * M.charpoly.eval x) + P.charpoly.eval x * Q.charpoly.eval x *
        (x ^ Fintype.card ι * x⁻¹ ^ Fintype.card ι + 1)) * hxc
  have hroots := congrArg Polynomial.roots hpoly
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) M.charpoly_monic.ne_zero), roots_X_pow,
    roots_mul (mul_ne_zero P.charpoly_monic.ne_zero Q.charpoly_monic.ne_zero),
    hM.roots_charpoly_eq_eigenvalues, hP.roots_charpoly_eq_eigenvalues,
    hQ.roots_charpoly_eq_eigenvalues] at hroots
  have hsum := congrArg (fun m : Multiset ℝ ↦ (m.map (· ^ k)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, zero_pow hk, nsmul_zero, zero_add,
    Multiset.map_map] at hsum
  rw [hM.trace_pow_eq_sum_eigenvalues_pow k, hP.trace_pow_eq_sum_eigenvalues_pow k,
    hQ.trace_pow_eq_sum_eigenvalues_pow k, Finset.sum_eq_multiset_sum,
    Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  simpa [Function.comp_def] using hsum

/-- A Hermitian real matrix has a generalized inverse `P` with `A P A = A` (the functional
calculus of `x ↦ x⁻¹`). -/
private theorem exists_mul_mul_eq_self_of_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    ∃ P : Matrix ι ι ℝ, A * P * A = A := by
  refine ⟨cfc (fun x : ℝ ↦ x⁻¹) A, ?_⟩
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) :=
    fun f ↦ A.finite_real_spectrum.continuousOn f
  have h1 := cfc_mul (fun x : ℝ ↦ x) (fun x ↦ x⁻¹) A (hc _) (hc _)
  have h2 := cfc_mul (fun x : ℝ ↦ x * x⁻¹) (fun x ↦ x) A (hc _) (hc _)
  rw [cfc_id' ℝ A hA.isSelfAdjoint] at h1 h2
  rw [← h1, ← h2]
  calc cfc (fun x ↦ x * x⁻¹ * x) A = cfc (fun x : ℝ ↦ x) A :=
        cfc_congr fun x _ ↦ mul_inv_mul_cancel x
    _ = A := cfc_id' ℝ A hA.isSelfAdjoint

/-- With `A P A = A` and `A` symmetric, the quadratic form of `A` factors through `x ↦ A x`:
`xᵀ A x = (A x)ᵀ P (A x)`. -/
private theorem matrixQuadraticForm_eq_comp {n : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hP : A * P * A = A) (x : EuclideanSpace ℝ (Fin n)) :
    matrixQuadraticForm A x = matrixQuadraticForm P (A.toEuclideanLin x) := by
  have hform (M : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
      matrixQuadraticForm M v = (M *ᵥ WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
    simp [matrixQuadraticForm, Matrix.toEuclideanCLM_apply,
      EuclideanSpace.inner_eq_star_dotProduct]
  rw [hform, hform]
  simp only [toLpLin_apply, WithLp.ofLp_toLp]
  have hAx : A *ᵥ WithLp.ofLp x = WithLp.ofLp x ᵥ* A := by
    rw [← mulVec_transpose, hA.eq]
  calc A *ᵥ WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = WithLp.ofLp x ⬝ᵥ (A * P * A) *ᵥ WithLp.ofLp x := by
        rw [hP, dotProduct_comm]
    _ = (WithLp.ofLp x ᵥ* A) ⬝ᵥ (P *ᵥ (A *ᵥ WithLp.ofLp x)) := by
        rw [← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [← hAx, dotProduct_comm]

/-- The sufficiency half of Craig–Sakamoto: if `A Σ B = 0`, then `A Y` and `B Y` are
independent, hence so are the quadratic forms, which factor through them. -/
private theorem indepFun_matrixQuadraticForm_of_mul_mul_eq_zero {n : ℕ}
    {Sigma A B : Matrix (Fin n) (Fin n) ℝ} (hS : Sigma.PosSemidef) (hA : A.IsSymm)
    (hB : B.IsSymm) (h : A * Sigma * B = 0) :
    IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B) (multivariateGaussian 0 Sigma) := by
  have hAH : A.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hA
  have hBH : B.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hB
  obtain ⟨PA, hPA⟩ := exists_mul_mul_eq_self_of_isHermitian hAH
  obtain ⟨PB, hPB⟩ := exists_mul_mul_eq_self_of_isHermitian hBH
  have hind := (TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff 0 hS A B).2
    (by rw [hB.eq]; exact h)
  have h' := hind.comp (measurable_matrixQuadraticForm PA) (measurable_matrixQuadraticForm PB)
  convert h' using 1
  · funext x
    exact matrixQuadraticForm_eq_comp hA hPA x
  · funext x
    exact matrixQuadraticForm_eq_comp hB hPB x

open scoped RealInnerProductSpace in
/-- The necessity half of Craig–Sakamoto: independence factors the moment-generating functions
of `Q_A ± Q_B` near `0`, giving `det (1 - s(Ã ± B̃)) = det (1 - sÃ) det (1 ∓ sB̃)` for
`Ã = √Σ A √Σ`, `B̃ = √Σ B √Σ`; the fourth trace powers then force `Ã B̃ = 0`. -/
private theorem mul_mul_eq_zero_of_indepFun_matrixQuadraticForm {n : ℕ}
    {Sigma A B : Matrix (Fin n) (Fin n) ℝ} (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm)
    (hind : IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B)
      (multivariateGaussian 0 Sigma)) :
    A * Sigma * B = 0 := by
  have hAH : A.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hA
  have hBH : B.IsHermitian := by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hB
  let q : Matrix (Fin n) (Fin n) ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun Θ x ↦ ⟪x, Θ.toEuclideanLin x⟫
  have hq (Θ : Matrix (Fin n) (Fin n) ℝ) : matrixQuadraticForm Θ = q Θ := by
    funext x
    rfl
  have hqm (Θ : Matrix (Fin n) (Fin n) ℝ) : Measurable (q Θ) := by
    rw [← hq]
    exact measurable_matrixQuadraticForm Θ
  have hqadd (Θ Θ' : Matrix (Fin n) (Fin n) ℝ) : q (Θ + Θ') = q Θ + q Θ' := by
    funext x
    simp [q, map_add, inner_add_right]
  have hqneg (Θ : Matrix (Fin n) (Fin n) ℝ) : q (-Θ) = fun x ↦ -q Θ x := by
    funext x
    simp [q, inner_neg_right]
  have hind1 : IndepFun (q A) (q B) (multivariateGaussian 0 Sigma) := by rwa [hq, hq] at hind
  have hind2 : IndepFun (q A) (q (-B)) (multivariateGaussian 0 Sigma) := by
    rw [hqneg]
    exact hind1.comp measurable_id measurable_neg
  have hm1 (s : ℝ) : mgf (q (A + B)) (multivariateGaussian 0 Sigma) s =
      mgf (q A) (multivariateGaussian 0 Sigma) s * mgf (q B) (multivariateGaussian 0 Sigma) s := by
    rw [hqadd]
    exact hind1.mgf_add' (hqm A).aestronglyMeasurable (hqm B).aestronglyMeasurable
  have hm2 (s : ℝ) : mgf (q (A + -B)) (multivariateGaussian 0 Sigma) s =
      mgf (q A) (multivariateGaussian 0 Sigma) s *
        mgf (q (-B)) (multivariateGaussian 0 Sigma) s := by
    rw [hqadd]
    exact hind2.mgf_add' (hqm A).aestronglyMeasurable (hqm (-B)).aestronglyMeasurable
  have hev (Θ : Matrix (Fin n) (Fin n) ℝ) (hΘ : Θ.IsHermitian) :
      ∀ᶠ s in 𝓝 (0 : ℝ), (1 - (2 * s) • (CFC.sqrt Sigma * Θ * CFC.sqrt Sigma)).PosDef := by
    have h2 : Tendsto (fun s : ℝ ↦ 2 * s) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (Matrix.isHermitian_sqrt_mul_mul_sqrt Sigma hΘ
      |>.eventually_posDef_one_sub_smul)
  have hall := (hev A hAH).and ((hev B hBH).and ((hev (-B) hBH.neg).and
    ((hev (A + B) (hAH.add hBH)).and (hev (A + -B) (hAH.add hBH.neg)))))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  have hdet_of (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) ℝ) (h₁ : Θ₁.IsHermitian) (h₂ : Θ₂.IsHermitian)
      (hm : ∀ s, mgf (q (Θ₁ + Θ₂)) (multivariateGaussian 0 Sigma) s =
        mgf (q Θ₁) (multivariateGaussian 0 Sigma) s * mgf (q Θ₂) (multivariateGaussian 0 Sigma) s)
      (s : ℝ)
      (hp0 : (1 - (2 * s) • (CFC.sqrt Sigma * (Θ₁ + Θ₂) * CFC.sqrt Sigma)).PosDef)
      (hp1 : (1 - (2 * s) • (CFC.sqrt Sigma * Θ₁ * CFC.sqrt Sigma)).PosDef)
      (hp2 : (1 - (2 * s) • (CFC.sqrt Sigma * Θ₂ * CFC.sqrt Sigma)).PosDef) :
      (1 - (2 * s) • (CFC.sqrt Sigma * (Θ₁ + Θ₂) * CFC.sqrt Sigma)).det =
        (1 - (2 * s) • (CFC.sqrt Sigma * Θ₁ * CFC.sqrt Sigma)).det *
          (1 - (2 * s) • (CFC.sqrt Sigma * Θ₂ * CFC.sqrt Sigma)).det := by
    have h := hm s
    simp only [q] at h
    rw [TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt Sigma
        (h₁.add h₂) hp0,
      TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt Sigma h₁ hp1,
      TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt Sigma h₂ hp2,
      ← Real.mul_rpow hp1.det_pos.le hp2.det_pos.le] at h
    exact (Real.rpow_left_inj hp0.det_pos.le (mul_nonneg hp1.det_pos.le hp2.det_pos.le)
      (by norm_num)).1 h
  have hMA := Matrix.isHermitian_sqrt_mul_mul_sqrt Sigma hAH
  have hMB := Matrix.isHermitian_sqrt_mul_mul_sqrt Sigma hBH
  have hsplit (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) ℝ) : CFC.sqrt Sigma * (Θ₁ + Θ₂) * CFC.sqrt Sigma =
      CFC.sqrt Sigma * Θ₁ * CFC.sqrt Sigma + CFC.sqrt Sigma * Θ₂ * CFC.sqrt Sigma := by
    noncomm_ring
  have hnegB : CFC.sqrt Sigma * -B * CFC.sqrt Sigma = -(CFC.sqrt Sigma * B * CFC.sqrt Sigma) := by
    noncomm_ring
  have hhalf (s : ℝ) (hs : 0 < s) (hs' : s < 2 * ε) : dist (s / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have L1 := trace_pow_eq_add_of_det_one_sub_smul (hMA.add hMB) hMA hMB (by positivity : 0 < 2 * ε)
    (fun s hs hs' ↦ by
      obtain ⟨h1, h2, -, h4, -⟩ := hball (hhalf s hs hs')
      have := hdet_of A B hAH hBH hm1 (s / 2) h4 h1 h2
      rwa [show 2 * (s / 2) = s by ring, hsplit] at this) (k := 4) (by norm_num)
  have L2 := trace_pow_eq_add_of_det_one_sub_smul (hMA.add hMB.neg) hMA hMB.neg
    (by positivity : 0 < 2 * ε)
    (fun s hs hs' ↦ by
      obtain ⟨h1, -, h3, -, h5⟩ := hball (hhalf s hs hs')
      have := hdet_of A (-B) hAH hBH.neg hm2 (s / 2) h5 h1 h3
      rwa [show 2 * (s / 2) = s by ring, hsplit, hnegB] at this) (k := 4) (by norm_num)
  rw [Even.neg_pow ⟨2, rfl⟩, ← sub_eq_add_neg] at L2
  have hXt : (CFC.sqrt Sigma * A * CFC.sqrt Sigma)ᵀ = CFC.sqrt Sigma * A * CFC.sqrt Sigma := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hMA.eq
  have hYt : (CFC.sqrt Sigma * B * CFC.sqrt Sigma)ᵀ = CFC.sqrt Sigma * B * CFC.sqrt Sigma := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hMB.eq
  have hXY := mul_eq_zero_of_trace_pow_four hXt hYt (by rw [L1, L2]; ring)
  have hRR : CFC.sqrt Sigma * CFC.sqrt Sigma = Sigma :=
    CFC.sqrt_mul_sqrt_self Sigma (nonneg_iff_posSemidef.2 hS.posSemidef)
  have hRu : IsUnit (CFC.sqrt Sigma) := by
    rw [isUnit_iff_isUnit_det]
    refine isUnit_iff_ne_zero.2 fun h0 ↦ hS.det_pos.ne' ?_
    rw [← hRR, det_mul, h0, zero_mul]
  have h3 : CFC.sqrt Sigma * (A * Sigma * B) * CFC.sqrt Sigma = 0 := by
    have e : CFC.sqrt Sigma * A * CFC.sqrt Sigma * (CFC.sqrt Sigma * B * CFC.sqrt Sigma) =
        CFC.sqrt Sigma * (A * (CFC.sqrt Sigma * CFC.sqrt Sigma) * B) * CFC.sqrt Sigma := by
      noncomm_ring
    rw [hRR] at e
    rw [← e, hXY]
  exact (hRu.mul_right_eq_zero).1 ((hRu.mul_left_eq_zero).1 h3)

end CraigSakamoto

/-- GAPS 105.15, Craig–Sakamoto criterion: for `Y ∼ N(0, Σ)` with `Σ` positive definite and
symmetric matrices `A`, `B`, the quadratic forms `Yᵀ A Y` and `Yᵀ B Y` are independent if and
only if `A Σ B = 0`. -/
theorem indepFun_matrixQuadraticForm_iff {n : ℕ} (Sigma A B : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm) :
    IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B)
      (multivariateGaussian 0 Sigma) ↔ A * Sigma * B = 0 :=
  ⟨mul_mul_eq_zero_of_indepFun_matrixQuadraticForm hS hA hB,
    indepFun_matrixQuadraticForm_of_mul_mul_eq_zero hS.posSemidef hA hB⟩

end CKSD
