module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import CKSD.Processes.Dependence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearCombination

/-!
# Stationary Gaussian processes

Coordinate selection of Gaussian vectors and projective consistency construct a real
stationary Gaussian process for every positive-definite stationary covariance.
The construction uses Mathlib Kolmogorov extension. Source: GAPS 106.14.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Coordinate selection `x ↦ (x (σ k))_k` as a continuous linear map of Euclidean spaces. -/
def euclideanSelect {ι κ : Type*} (σ : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k ↦ EuclideanSpace.proj (σ k))

/-- Coordinates of a coordinate selection. -/
@[simp] theorem euclideanSelect_apply {ι κ : Type*} (σ : κ → ι)
    (x : EuclideanSpace ℝ ι) (k : κ) : euclideanSelect σ x k = x (σ k) := rfl

/-- The image of a centred multivariate Gaussian law under the coordinate selection
`x ↦ (x (σ k))_k`, with `σ` not necessarily injective, is the centred Gaussian law with covariance
`S.submatrix σ σ`. This generalizes Mathlib's `measurePreserving_restrict₂_multivariateGaussian`,
whose proof it follows. -/
theorem map_euclideanSelect_multivariateGaussian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (σ : κ → ι) :
    (multivariateGaussian 0 S).map (euclideanSelect σ) =
      multivariateGaussian 0 (S.submatrix σ σ) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have (i : κ) : (fun u ↦ ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
        euclideanSelect σ = fun u ↦ u (σ i) := by ext; simp [PiLp.inner_apply]
    simp_rw [this, covariance_eval_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian (hS.submatrix _)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id


/-- The stationary covariance matrix `(γ (t k - t l))_{k,l}` at times `t`. -/
def stationaryCovMatrix {κ : Type*} (γ : ℤ → ℝ) (t : κ → ℤ) : Matrix κ κ ℝ :=
  Matrix.of fun k l ↦ γ (t k - t l)

/-- A symmetric positive-definite sequence gives positive-semidefinite covariance matrices at
every finite family of times. -/
theorem posSemidef_stationaryCovMatrix (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j)
    {κ : Type*} [Fintype κ] (t : κ → ℤ) : (stationaryCovMatrix γ t).PosSemidef := by
  classical
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · ext k l
    simp only [Matrix.conjTranspose_apply, stationaryCovMatrix, Matrix.of_apply, star_trivial]
    rw [← hsym, neg_sub]
  · let e := Fintype.equivFin κ
    have h1 := hpd (Fintype.card κ) (t ∘ e.symm) (x ∘ e.symm)
    have h2 : (∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ),
        (x ∘ e.symm) i * γ ((t ∘ e.symm) i - (t ∘ e.symm) j) * (x ∘ e.symm) j) =
          ∑ k, ∑ l, x k * γ (t k - t l) * x l := by
      rw [← e.symm.sum_comp (fun k ↦ ∑ l, x k * γ (t k - t l) * x l)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← e.symm.sum_comp (fun l ↦ x (e.symm i) * γ (t (e.symm i) - t l) * x l)]
      rfl
    rw [h2] at h1
    simp only [dotProduct, Matrix.mulVec, stationaryCovMatrix, Matrix.of_apply, star_trivial,
      Finset.mul_sum]
    refine h1.trans_eq (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
    ring

/-- The finite-dimensional Gaussian laws with stationary covariance `γ`, indexed by finite sets
of times. -/
def stationaryGaussianFamily (γ : ℤ → ℝ) (J : Finset ℤ) : Measure (J → ℝ) :=
  (multivariateGaussian 0 (stationaryCovMatrix γ (fun j : J ↦ (j : ℤ)))).map (WithLp.ofLp)

/-- The stationary Gaussian laws are probability measures. -/
instance (γ : ℤ → ℝ) (J : Finset ℤ) : IsProbabilityMeasure (stationaryGaussianFamily γ J) :=
  by unfold stationaryGaussianFamily; infer_instance


/-- The stationary Gaussian laws form a projective family. -/
theorem isProjectiveMeasureFamily_stationaryGaussianFamily (γ : ℤ → ℝ)
    (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ) := by
  intro I J hJI
  let σ : J → I := fun j ↦ ⟨j, hJI j.2⟩
  have hfun : Finset.restrict₂ (π := fun _ : ℤ ↦ ℝ) hJI ∘ WithLp.ofLp =
      WithLp.ofLp ∘ euclideanSelect (ι := I) σ := by
    funext x; rfl
  have h1 : (stationaryGaussianFamily γ I).map (Finset.restrict₂ (π := fun _ : ℤ ↦ ℝ) hJI) =
      ((multivariateGaussian 0 (stationaryCovMatrix γ (fun i : I ↦ (i : ℤ)))).map
        (euclideanSelect σ)).map WithLp.ofLp := by
    rw [stationaryGaussianFamily, Measure.map_map, hfun, Measure.map_map]
    all_goals first | fun_prop | exact Finset.measurable_restrict₂ _
  rw [h1, map_euclideanSelect_multivariateGaussian (posSemidef_stationaryCovMatrix γ hsym hpd _)]
  rfl

/-- The Kolmogorov extension of the stationary Gaussian family has centred Gaussian
finite-dimensional laws with covariance `γ (t k - t l)`, for any finite family of times, with
repetitions allowed. -/
theorem map_eval_projectiveLimit_stationaryGaussianFamily (γ : ℤ → ℝ)
    (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℤ) :
    (projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ)
        (isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd)).map
      (fun x ↦ WithLp.toLp 2 (fun k ↦ x (t k))) =
      multivariateGaussian 0 (stationaryCovMatrix γ t) := by
  set hP := isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd
  let J : Finset ℤ := Finset.univ.image t
  let σ : κ → J := fun k ↦ ⟨t k, Finset.mem_image_of_mem t (Finset.mem_univ k)⟩
  have hfun : (fun x : ℤ → ℝ ↦ WithLp.toLp 2 (fun k ↦ x (t k))) =
      euclideanSelect σ ∘ WithLp.toLp 2 ∘ J.restrict := by
    funext x; rfl
  rw [hfun, ← Measure.map_map, ← Measure.map_map, isProjectiveLimit_projectiveLimit hP J,
    stationaryGaussianFamily, Measure.map_map (WithLp.measurable_toLp _ _)
    (WithLp.measurable_ofLp _ _)]
  rotate_left
  any_goals fun_prop
  have : (WithLp.toLp 2 ∘ WithLp.ofLp : EuclideanSpace ℝ J → EuclideanSpace ℝ J) = id := by
    funext x; rfl
  rw [this, Measure.map_id,
    map_euclideanSelect_multivariateGaussian (posSemidef_stationaryCovMatrix γ hsym hpd _)]
  rfl

/-- GAPS 106.14, real Gaussian realization of a positive-definite stationary covariance. -/
theorem exists_stationary_gaussian_process_of_posSemidef (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    ∃ P : Measure (ℤ → ℝ), IsProbabilityMeasure P ∧
      (∀ h : ℤ, P.map (fun x t ↦ x (t + h)) = P) ∧
      ∀ n : ℕ, ∀ t : Fin n → ℤ,
        P.map (fun x ↦ WithLp.toLp 2 (fun i : Fin n ↦ x (t i))) =
          multivariateGaussian 0 (fun i j ↦ γ (t i - t j)) := by
  set hP := isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd
  set Q := projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ) hP
  refine ⟨Q, inferInstance, fun h ↦ ?_, fun n t ↦
    map_eval_projectiveLimit_stationaryGaussianFamily γ hsym hpd t⟩
  have hshift : Measurable fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h) :=
    Measurable.of_eval fun t ↦ measurable_pi_apply (t + h)
  refine IsProjectiveLimit.unique (α := fun _ : ℤ ↦ ℝ) (P := stationaryGaussianFamily γ) (fun J ↦ ?_)
    (isProjectiveLimit_projectiveLimit hP)
  rw [Measure.map_map (Finset.measurable_restrict J) hshift]
  have hfun : (J.restrict ∘ fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h)) =
      WithLp.ofLp ∘ fun x ↦ WithLp.toLp 2 (fun j : J ↦ x ((j : ℤ) + h)) := by
    funext x; rfl
  rw [hfun, ← Measure.map_map, map_eval_projectiveLimit_stationaryGaussianFamily γ hsym hpd,
    stationaryGaussianFamily]
  rotate_left
  · exact WithLp.measurable_ofLp _ _
  · exact (WithLp.measurable_toLp _ _).comp (Measurable.of_eval fun j ↦ measurable_pi_apply _)
  congr 2
  ext i j
  simp [stationaryCovMatrix]

end CKSD
