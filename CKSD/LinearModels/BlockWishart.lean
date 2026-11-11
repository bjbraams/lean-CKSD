module
public import CKSD.LinearModels.WishartRatioMoments
public import TauCeti.Probability.Distributions.Gaussian.Independence
public import TauCeti.Probability.Distributions.Wishart.Marginal
public import Mathlib.MeasureTheory.Constructions.Pi
/-!
# Independent principal blocks of Gaussian-Gram Wishart matrices

Two rectangular images of a centred Gaussian with zero cross covariance are independent.
Applying this to every independent Gaussian row and regrouping the finite product gives the
joint law of two Wishart congruence images, including singular scales and arbitrary degrees.
Principal coordinate blocks are a special case.

This is the block-independence step of Muirhead, *Aspects of Multivariate Statistical Theory*,
Theorem 11.2.3, printed page 532 (PDF page 558 of the local 2005 copy). Pinned TauCeti supplies
Gaussian linear-image independence and Wishart congruence identities; Mathlib supplies the
finite-product regrouping equivalence.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology MatrixOrder BigOperators
namespace CKSD
/-- Orthogonal Gaussian coordinate groups give independent Wishart congruence images. -/
theorem map_pair_symmetricCongruenceLinearMap_wishartGramMeasure
    {d p q : ℕ} (ν : ℕ) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef)
    (L : Matrix (Fin p) (Fin d) ℝ) (R : Matrix (Fin q) (Fin d) ℝ)
    (hcross : L * S * R.transpose = 0) :
    (TauCeti.Probability.wishartGramMeasure ν S).map
      (fun A ↦ (Matrix.symmetricCongruenceLinearMap L A,
        Matrix.symmetricCongruenceLinearMap R A)) =
      (TauCeti.Probability.wishartGramMeasure ν (L * S * L.transpose)).prod
        (TauCeti.Probability.wishartGramMeasure ν (R * S * R.transpose)) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  let μL := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (L * S * L.transpose)
  let μR := multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (R * S * R.transpose)
  let f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) :=
    fun x ↦ (L.toEuclideanLin x, R.toEuclideanLin x)
  have hLm : μ.map L.toEuclideanLin = μL := by
    simpa [μ, μL] using TauCeti.Probability.map_affine_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) hS L (0 : EuclideanSpace ℝ (Fin p))
  have hRm : μ.map R.toEuclideanLin = μR := by
    simpa [μ, μR] using TauCeti.Probability.map_affine_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) hS R (0 : EuclideanSpace ℝ (Fin q))
  have hpair : μ.map f = μL.prod μR := by
    rw [← hLm, ← hRm]
    exact (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1
      ((TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff 0 hS L R).2 hcross)
  have hpi : (Measure.pi fun _ : Fin ν ↦ μ).map (fun x r ↦ f (x r)) =
      Measure.pi (fun _ : Fin ν ↦ μL.prod μR) := by
    rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop : Measurable f).aemeasurable), hpair]
  have hshuffle := (measurePreserving_arrowProdEquivProdArrow
    (EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin q)) (Fin ν)
    (fun _ ↦ μL) (fun _ ↦ μR)).map_eq
  rw [TauCeti.Probability.wishartGramMeasure_eq_map_pi, Measure.map_map
    (by fun_prop) TauCeti.Probability.measurable_wishartGram]
  have hfun :
      (fun A ↦ (Matrix.symmetricCongruenceLinearMap L A,
        Matrix.symmetricCongruenceLinearMap R A)) ∘ TauCeti.Probability.wishartGram =
      (fun z : (Fin ν → EuclideanSpace ℝ (Fin p)) × (Fin ν → EuclideanSpace ℝ (Fin q)) ↦
        (TauCeti.Probability.wishartGram z.1, TauCeti.Probability.wishartGram z.2)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow (EuclideanSpace ℝ (Fin p))
          (EuclideanSpace ℝ (Fin q)) (Fin ν)) ∘ (fun x r ↦ f (x r)) := by
    funext x
    exact Prod.ext (TauCeti.Probability.wishartGram_toEuclideanLin L x).symm
      (TauCeti.Probability.wishartGram_toEuclideanLin R x).symm
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, hshuffle]
  rw [TauCeti.Probability.wishartGramMeasure_eq_map_pi,
    TauCeti.Probability.wishartGramMeasure_eq_map_pi]
  exact (Measure.map_prod_map _ _ TauCeti.Probability.measurable_wishartGram
    TauCeti.Probability.measurable_wishartGram).symm
/-- Congruence by selected identity rows reads off the corresponding principal submatrix. -/
theorem coe_symmetricCongruenceLinearMap_submatrix_one {d p : ℕ}
    (f : Fin p → Fin d) (A : selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℝ)) :
    ((Matrix.symmetricCongruenceLinearMap
      ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix f id) A) : Matrix (Fin p) (Fin p) ℝ) =
      (A : Matrix (Fin d) (Fin d) ℝ).submatrix f f := by
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_submatrix,
    Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one]
/-- Distinct uncorrelated groups of coordinates have independent principal Wishart blocks. -/
theorem map_pair_principalBlocks_wishartGramMeasure
    {d p q : ℕ} (ν : ℕ) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef)
    (f : Fin p → Fin d) (g : Fin q → Fin d)
    (hcross : S.submatrix f g = 0) :
    (TauCeti.Probability.wishartGramMeasure ν S).map
      (fun A ↦ (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix f id) A,
        Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix g id) A)) =
      (TauCeti.Probability.wishartGramMeasure ν (S.submatrix f f)).prod
        (TauCeti.Probability.wishartGramMeasure ν (S.submatrix g g)) := by
  have hcross' : (1 : Matrix (Fin d) (Fin d) ℝ).submatrix f id * S *
      ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix g id).transpose = 0 := by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one]
    calc
      _ = S.submatrix f id * (1 : Matrix (Fin d) (Fin d) ℝ).submatrix id g := by
        congr 1
        exact Matrix.one_submatrix_mul f (Equiv.refl _) S
      _ = S.submatrix f g := Matrix.mul_submatrix_one (Equiv.refl _) g _
      _ = 0 := hcross
  have h := map_pair_symmetricCongruenceLinearMap_wishartGramMeasure ν hS
    ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix f id)
    ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix g id) hcross'
  simpa only [Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one] using h
end CKSD
