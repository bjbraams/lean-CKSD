module

public import CKSD.Processes.Independence
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Gaussian.Sum
public import TauCeti.Probability.Distributions.Gaussian.Independence
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Linear images and conditional laws of Gaussian vectors

Linear combinations of independent centred Gaussian vectors, their independence criterion
through the cross-covariance, the Gaussian location kernel `m ↦ N(m, S)`, and the conditional law
of `g(Y) + Z` given `Y` for `Z ~ N(0, S)` independent of `Y`. Gaussian laws, densities, affine
maps and the independence criterion are reused from pinned TauCeti. These probability tools
support the Kalman filter but do not depend on its model.

## Main definitions

* `CKSD.gaussianShiftKernel`: the Markov kernel `m ↦ N(m, S)`.

## Main results

* `CKSD.posSemidef_mul_mul_transpose`: `A S Aᵀ` is positive semidefinite when `S` is.
* `CKSD.hasLaw_toEuclideanLin_add_of_indepFun`: `A₁ ε + A₂ v ~ N(0, A₁ S₁ A₁ᵀ + A₂ S₂ A₂ᵀ)`.
* `CKSD.indepFun_toEuclideanLin_add_of_indepFun`: two such combinations are independent when
  their cross-covariance vanishes.
* `CKSD.condDistrib_add_eq_multivariateGaussian`: the conditional law of `g(Y) + Z` given
  `Y = y` is `N(g y, S)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

section GaussianPair

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ]

omit [Fintype κ] [Fintype σ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- A real congruence `A S Aᵀ` of a positive-semidefinite matrix is positive semidefinite; this
is Mathlib's `Matrix.PosSemidef.mul_mul_conjTranspose_same` for real matrices. -/
theorem posSemidef_mul_mul_transpose {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (A : Matrix τ ι ℝ) :
    (A * S * A.transpose).PosSemidef := by
  simpa using hS.mul_mul_conjTranspose_same A

/-- A matrix image of a centered multivariate Gaussian vector is centered Gaussian with the
congruent covariance. -/
theorem hasLaw_toEuclideanLin_multivariateGaussian_zero {X : Ω → EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateGaussian 0 S) P) (A : Matrix τ ι ℝ) :
    HasLaw (fun ω ↦ A.toEuclideanLin (X ω))
      (multivariateGaussian 0 (A * S * A.transpose)) P := by
  have h := TauCeti.Probability.map_affine_multivariateGaussian 0 hS A 0
  simp only [map_zero, add_zero] at h
  exact HasLaw.comp (Y := fun x ↦ A.toEuclideanLin x) ⟨by fun_prop, h⟩ hX

/-- For independent centered Gaussian vectors `ε` and `v`, the combination `A₁ ε + A₂ v` is
centered Gaussian with covariance `A₁ S₁ A₁ᵀ + A₂ S₂ A₂ᵀ`. -/
theorem hasLaw_toEuclideanLin_add_of_indepFun {ε : Ω → EuclideanSpace ℝ ι}
    {v : Ω → EuclideanSpace ℝ κ} {S₁ : Matrix ι ι ℝ} {S₂ : Matrix κ κ ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hε : HasLaw ε (multivariateGaussian 0 S₁) P) (hv : HasLaw v (multivariateGaussian 0 S₂) P)
    (hεv : IndepFun ε v P) (A₁ : Matrix τ ι ℝ) (A₂ : Matrix τ κ ℝ) :
    HasLaw (fun ω ↦ A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω))
      (multivariateGaussian 0 (A₁ * S₁ * A₁.transpose + A₂ * S₂ * A₂.transpose)) P := by
  have h₁ := hasLaw_toEuclideanLin_multivariateGaussian_zero hS₁ hε A₁
  have h₂ := hasLaw_toEuclideanLin_multivariateGaussian_zero hS₂ hv A₂
  have hind : IndepFun (fun ω ↦ A₁.toEuclideanLin (ε ω)) (fun ω ↦ A₂.toEuclideanLin (v ω)) P :=
    hεv.comp (φ := fun x ↦ A₁.toEuclideanLin x) (ψ := fun x ↦ A₂.toEuclideanLin x)
      (by fun_prop) (by fun_prop)
  have h := hind.hasLaw_fun_add h₁ h₂
  rw [TauCeti.Probability.multivariateGaussian_conv_multivariateGaussian _ _
    (posSemidef_mul_mul_transpose hS₁ A₁) (posSemidef_mul_mul_transpose hS₂ A₂),
    add_zero] at h
  exact h

omit [DecidableEq τ] [DecidableEq σ] in
/-- Two linear combinations `A₁ ε + A₂ v` and `B₁ ε + B₂ v` of independent centered Gaussian
vectors are independent when their cross-covariance `A₁ S₁ B₁ᵀ + A₂ S₂ B₂ᵀ` vanishes. -/
theorem indepFun_toEuclideanLin_add_of_indepFun {ε : Ω → EuclideanSpace ℝ ι}
    {v : Ω → EuclideanSpace ℝ κ} {S₁ : Matrix ι ι ℝ} {S₂ : Matrix κ κ ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hε : HasLaw ε (multivariateGaussian 0 S₁) P) (hv : HasLaw v (multivariateGaussian 0 S₂) P)
    (hεv : IndepFun ε v P) (A₁ : Matrix τ ι ℝ) (A₂ : Matrix τ κ ℝ) (B₁ : Matrix σ ι ℝ)
    (B₂ : Matrix σ κ ℝ)
    (hcov : A₁ * S₁ * B₁.transpose + A₂ * S₂ * B₂.transpose = 0) :
    IndepFun (fun ω ↦ A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω))
      (fun ω ↦ B₁.toEuclideanLin (ε ω) + B₂.toEuclideanLin (v ω)) P := by
  let J₁ : Matrix (ι ⊕ κ) ι ℝ := Matrix.fromRows 1 0
  let J₂ : Matrix (ι ⊕ κ) κ ℝ := Matrix.fromRows 0 1
  have hU := hasLaw_toEuclideanLin_add_of_indepFun hS₁ hS₂ hε hv hεv J₁ J₂
  have hS : (J₁ * S₁ * J₁.transpose + J₂ * S₂ * J₂.transpose).PosSemidef :=
    (posSemidef_mul_mul_transpose hS₁ J₁).add (posSemidef_mul_mul_transpose hS₂ J₂)
  have key := (TauCeti.Probability.indepFun_matrix_of_hasLaw_multivariateGaussian_iff hS hU
    (Matrix.fromCols A₁ A₂) (Matrix.fromCols B₁ B₂)).2 (by
      calc Matrix.fromCols A₁ A₂ * (J₁ * S₁ * J₁.transpose + J₂ * S₂ * J₂.transpose) *
            (Matrix.fromCols B₁ B₂).transpose
          = (Matrix.fromCols A₁ A₂ * J₁) * S₁ * (Matrix.fromCols B₁ B₂ * J₁).transpose +
            (Matrix.fromCols A₁ A₂ * J₂) * S₂ * (Matrix.fromCols B₁ B₂ * J₂).transpose := by
            simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by simpa [J₁, J₂, Matrix.fromCols_mul_fromRows] using hcov)
  have hA : ∀ ω, (Matrix.fromCols A₁ A₂).toEuclideanLin
      (J₁.toEuclideanLin (ε ω) + J₂.toEuclideanLin (v ω)) =
        A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω) := by
    intro ω
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    simp [J₁, J₂, Matrix.fromCols_mul_fromRows]
  have hB : ∀ ω, (Matrix.fromCols B₁ B₂).toEuclideanLin
      (J₁.toEuclideanLin (ε ω) + J₂.toEuclideanLin (v ω)) =
        B₁.toEuclideanLin (ε ω) + B₂.toEuclideanLin (v ω) := by
    intro ω
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    simp [J₁, J₂, Matrix.fromCols_mul_fromRows]
  simpa only [hA, hB] using key

/-- The Gaussian location kernel `m ↦ N(m, S)`. -/
def gaussianShiftKernel (S : Matrix ι ι ℝ) :
    ProbabilityTheory.Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) where
  toFun m := multivariateGaussian m S
  measurable' := by
    change Measurable (Function.uncurry multivariateGaussian ∘ fun m ↦ (m, S))
    exact measurable_multivariateGaussian.comp (measurable_id.prodMk measurable_const)

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- The Gaussian shift kernel at `m` is the Gaussian law with mean `m` and covariance `S`. -/
@[simp]
theorem gaussianShiftKernel_apply (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) :
    gaussianShiftKernel S m = multivariateGaussian m S := rfl

instance (S : Matrix ι ι ℝ) : IsMarkovKernel (gaussianShiftKernel S) where
  isProbabilityMeasure m := by rw [gaussianShiftKernel_apply]; infer_instance

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- The multivariate Gaussian density is jointly measurable in the mean and the point. -/
theorem measurable_multivariateGaussianPDF_uncurry (S : Matrix ι ι ℝ) :
    Measurable fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      TauCeti.Probability.multivariateGaussianPDF q.1 S q.2 := by
  simp only [TauCeti.Probability.multivariateGaussianPDF_def,
    TauCeti.Probability.multivariateGaussianPDFReal_def]
  fun_prop

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- If `Z` has law `N(0, S)` and is independent of `Y`, then the joint law of `Y` and
`g(Y) + Z` is the composition of the law of `Y` with the Gaussian kernel `y ↦ N(g y, S)`. -/
theorem map_prodMk_add_eq_compProd {β : Type*} [MeasurableSpace β] [IsProbabilityMeasure P]
    {Y : Ω → β} {Z : Ω → EuclideanSpace ℝ ι} {g : β → EuclideanSpace ℝ ι} (hg : Measurable g)
    (hY : AEMeasurable Y P) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hZ : HasLaw Z (multivariateGaussian 0 S) P) (hYZ : IndepFun Y Z P) :
    P.map (fun ω ↦ (Y ω, g (Y ω) + Z ω)) =
      P.map Y ⊗ₘ (gaussianShiftKernel S).comap g hg := by
  have hpair : P.map (fun ω ↦ (Y ω, Z ω)) = (P.map Y).prod (multivariateGaussian 0 S) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hY hZ.aemeasurable] at hYZ
    rw [hYZ, hZ.map_eq]
  have hF : Measurable fun q : β × EuclideanSpace ℝ ι ↦ (q.1, g q.1 + q.2) :=
    measurable_fst.prodMk ((hg.comp measurable_fst).add measurable_snd)
  have hcomp : (fun ω ↦ (Y ω, g (Y ω) + Z ω)) =
      (fun q : β × EuclideanSpace ℝ ι ↦ (q.1, g q.1 + q.2)) ∘ fun ω ↦ (Y ω, Z ω) := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
    (hY.prodMk hZ.aemeasurable), hpair]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.compProd_apply hs]
  refine lintegral_congr fun b ↦ ?_
  rw [Kernel.comap_apply, gaussianShiftKernel_apply]
  have hshift : multivariateGaussian (g b) S =
      (multivariateGaussian 0 S).map fun z ↦ g b + z := by
    have h := TauCeti.Probability.map_affine_multivariateGaussian 0 hS
      (1 : Matrix ι ι ℝ) (g b)
    simp only [Matrix.toLpLin_one, LinearMap.id_apply, map_zero, zero_add, Matrix.one_mul,
      Matrix.transpose_one, Matrix.mul_one] at h
    rw [← h]
    congr 1
    funext z
    exact add_comm _ _
  rw [hshift, Measure.map_apply (measurable_const_add _) (measurable_prodMk_left hs)]
  rfl

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- If `Z` has law `N(0, S)` and is independent of `Y`, then the conditional law of
`g(Y) + Z` given `Y = y` is `N(g y, S)` for almost every `y`. -/
theorem condDistrib_add_eq_multivariateGaussian {β : Type*} [MeasurableSpace β]
    [IsProbabilityMeasure P] {Y : Ω → β} {Z : Ω → EuclideanSpace ℝ ι}
    {g : β → EuclideanSpace ℝ ι} (hg : Measurable g) (hY : AEMeasurable Y P)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hZ : HasLaw Z (multivariateGaussian 0 S) P)
    (hYZ : IndepFun Y Z P) :
    ∀ᵐ b ∂(P.map Y), condDistrib (fun ω ↦ g (Y ω) + Z ω) Y P b =
      multivariateGaussian (g b) S := by
  have h := condDistrib_ae_eq_of_measure_eq_compProd hY
    (show AEMeasurable (fun ω ↦ g (Y ω) + Z ω) P from
      (hg.comp_aemeasurable hY).add hZ.aemeasurable)
    (map_prodMk_add_eq_compProd hg hY hS hZ hYZ)
  filter_upwards [h] with b hb
  rw [hb, Kernel.comap_apply, gaussianShiftKernel_apply]

end GaussianPair

end CKSD
