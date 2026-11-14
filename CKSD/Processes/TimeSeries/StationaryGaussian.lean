module

public import CKSD.Processes.Basic
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Distributions.Gaussian.Affine


/-!
# Stationary Gaussian processes

Every symmetric positive-semidefinite sequence `γ : ℤ → ℝ` is the autocovariance of a real
strictly stationary centred Gaussian process: the centred Gaussian laws with covariance matrices
`(γ(t_k - t_l))_{k,l}` on finite sets of times form a projective family, whose Kolmogorov
extension is shift invariant.

## Main definitions

* `CKSD.IsPositiveSemidefiniteSequence`: `γ(-t) = γ(t)` and `∑_{i,j} a_i γ(t_i - t_j) a_j ≥ 0`.
* `CKSD.euclideanSelect`: coordinate selection `x ↦ (x (σ k))_k` of Euclidean vectors.
* `CKSD.stationaryCovMatrix`, `CKSD.stationaryGaussianFamily`: the covariance matrices and the
  finite-dimensional Gaussian laws.

## Main results

* `CKSD.map_euclidean_select_multivariate_gaussian`: coordinate selections of centred Gaussian
  vectors are centred Gaussian with the selected covariance submatrix.
* `CKSD.IsPositiveSemidefiniteSequence.exists_stationary_gaussian` (GAPS 106.14): the stationary
  Gaussian realization.

The construction uses Mathlib's Kolmogorov extension theorem and TauCeti's affine images of
multivariate Gaussian laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Coordinate selection `x ↦ (x (σ k))_k` as a continuous linear map of Euclidean spaces. -/
def euclideanSelect {ι κ : Type*} (σ : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k ↦ EuclideanSpace.proj (σ k))

/-- Coordinates of a coordinate selection. -/
@[simp] theorem euclidean_select_apply {ι κ : Type*} (σ : κ → ι)
    (x : EuclideanSpace ℝ ι) (k : κ) : euclideanSelect σ x k = x (σ k) := rfl

/-- The image of a centred multivariate Gaussian law under the coordinate selection
`x ↦ (x (σ k))_k`, with `σ` not necessarily injective, is the centred Gaussian law with covariance
`S.submatrix σ σ`. This generalizes Mathlib's `measurePreserving_restrict₂_multivariateGaussian`;
the selection is the matrix `(1_{σ k = i})_{k,i}`, and TauCeti's
`map_affine_multivariateGaussian` applies. -/
theorem map_euclidean_select_multivariate_gaussian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (σ : κ → ι) :
    (multivariateGaussian 0 S).map (euclideanSelect σ) =
      multivariateGaussian 0 (S.submatrix σ σ) := by
  let L : Matrix κ ι ℝ := Matrix.of fun k i ↦ if σ k = i then 1 else 0
  have hL : ⇑(euclideanSelect σ) = fun x ↦ L.toEuclideanLin x + 0 := by
    funext x; ext k; simp [L, Matrix.mulVec, dotProduct]
  rw [hL, TauCeti.Probability.map_affine_multivariateGaussian 0 hS L 0]
  congr 1
  · simp
  · ext k l; simp [L, Matrix.mul_apply]

/-- A real sequence `γ` on `ℤ` is positive semidefinite (nonnegative definite) when it is
symmetric and all its quadratic forms `∑_{i,j} a_i γ(t_i - t_j) a_j` are nonnegative; these are
exactly the autocovariance functions of real weakly stationary processes. -/
structure IsPositiveSemidefiniteSequence (γ : ℤ → ℝ) : Prop where
  /-- Symmetry `γ(-t) = γ(t)`. -/
  symm : ∀ t, γ (-t) = γ t
  /-- Nonnegativity of the quadratic forms. -/
  sum_nonneg : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j

/-- The stationary covariance matrix `(γ (t k - t l))_{k,l}` at times `t`. -/
def stationaryCovMatrix {κ : Type*} (γ : ℤ → ℝ) (t : κ → ℤ) : Matrix κ κ ℝ :=
  Matrix.of fun k l ↦ γ (t k - t l)

/-- A positive-semidefinite sequence gives positive-semidefinite covariance matrices at every
finite family of times. -/
theorem IsPositiveSemidefiniteSequence.pos_semidef_stationary_cov_matrix {γ : ℤ → ℝ}
    (hγ : IsPositiveSemidefiniteSequence γ) {κ : Type*} [Fintype κ] (t : κ → ℤ) :
    (stationaryCovMatrix γ t).PosSemidef := by
  classical
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · ext k l
    simp only [Matrix.conjTranspose_apply, stationaryCovMatrix, Matrix.of_apply, star_trivial]
    rw [← hγ.symm, neg_sub]
  · let e := Fintype.equivFin κ
    have h1 := hγ.sum_nonneg (Fintype.card κ) (t ∘ e.symm) (x ∘ e.symm)
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
theorem IsPositiveSemidefiniteSequence.is_projective_measure_family_stationary_gaussian_family
    {γ : ℤ → ℝ} (hγ : IsPositiveSemidefiniteSequence γ) :
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
  rw [h1, map_euclidean_select_multivariate_gaussian (hγ.pos_semidef_stationary_cov_matrix _)]
  rfl

/-- The Kolmogorov extension of the stationary Gaussian family has centred Gaussian
finite-dimensional laws with covariance `γ (t k - t l)`, for any finite family of times, with
repetitions allowed. -/
theorem IsPositiveSemidefiniteSequence.map_eval_projective_limit_stationary_gaussian_family
    {γ : ℤ → ℝ} (hγ : IsPositiveSemidefiniteSequence γ)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℤ) :
    (projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ)
        hγ.is_projective_measure_family_stationary_gaussian_family).map
      (fun x ↦ WithLp.toLp 2 (fun k ↦ x (t k))) =
      multivariateGaussian 0 (stationaryCovMatrix γ t) := by
  set hP := hγ.is_projective_measure_family_stationary_gaussian_family
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
    map_euclidean_select_multivariate_gaussian (hγ.pos_semidef_stationary_cov_matrix _)]
  rfl

/-- GAPS 106.14, real Gaussian realization of a stationary covariance: for every
positive-semidefinite sequence `γ` there is a shift-invariant probability measure on `ℤ → ℝ`
whose finite-dimensional laws are centred Gaussian with covariance `γ(t_i - t_j)`; that is,
`γ` is the autocovariance of a strictly stationary centred Gaussian process. -/
theorem IsPositiveSemidefiniteSequence.exists_stationary_gaussian {γ : ℤ → ℝ}
    (hγ : IsPositiveSemidefiniteSequence γ) :
    ∃ P : Measure (ℤ → ℝ), IsProbabilityMeasure P ∧
      (∀ h : ℤ, P.map (fun x t ↦ x (t + h)) = P) ∧
      ∀ n : ℕ, ∀ t : Fin n → ℤ,
        P.map (fun x ↦ WithLp.toLp 2 (fun i : Fin n ↦ x (t i))) =
          multivariateGaussian 0 (fun i j ↦ γ (t i - t j)) := by
  set hP := hγ.is_projective_measure_family_stationary_gaussian_family
  set Q := projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ) hP
  refine ⟨Q, inferInstance, fun h ↦ ?_, fun n t ↦
    hγ.map_eval_projective_limit_stationary_gaussian_family t⟩
  have hshift : Measurable fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h) :=
    Measurable.of_eval fun t ↦ measurable_pi_apply (t + h)
  refine IsProjectiveLimit.unique (α := fun _ : ℤ ↦ ℝ) (P := stationaryGaussianFamily γ)
    (fun J ↦ ?_)
    (isProjectiveLimit_projectiveLimit hP)
  rw [Measure.map_map (Finset.measurable_restrict J) hshift]
  have hfun : (J.restrict ∘ fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h)) =
      WithLp.ofLp ∘ fun x ↦ WithLp.toLp 2 (fun j : J ↦ x ((j : ℤ) + h)) := by
    funext x; rfl
  rw [hfun, ← Measure.map_map, hγ.map_eval_projective_limit_stationary_gaussian_family,
    stationaryGaussianFamily]
  rotate_left
  · exact WithLp.measurable_ofLp _ _
  · exact (WithLp.measurable_toLp _ _).comp (Measurable.of_eval fun j ↦ measurable_pi_apply _)
  congr 2
  ext i j
  simp [stationaryCovMatrix]

end CKSD
