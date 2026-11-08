module

public import CKSD.LinearModels.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Gaussian graphical concentration models

For an undirected graph `G` on a finite index type `ι` (Mathlib's `SimpleGraph`), the Gaussian
concentration model consists of the nondegenerate Gaussian laws whose concentration (precision)
matrix `Σ⁻¹` vanishes off the edges of `G`.

## Main definitions

* `CKSD.concentrationModel`: the positive definite matrices with zero entries off the edges.
* `CKSD.HasGaussianPairwiseMarkovProperty`: nonadjacent coordinates of `N(m, Σ)` are
  conditionally independent given all the other coordinates.
* `CKSD.gaussianConcentrationLogLikelihood`: the Gaussian log likelihood of a concentration
  matrix, up to an additive constant and a positive factor.
* `CKSD.IsConcentrationMLE`: a concentration matrix of the model that is the unique maximizer of
  the likelihood over the model.

## Main results

* `CKSD.condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero`: for positive definite `Σ`,
  coordinates `i ≠ j` of `N(m, Σ)` are conditionally independent given the other coordinates
  exactly when `(Σ⁻¹)ᵢⱼ = 0`.
* `CKSD.hasGaussianPairwiseMarkovProperty_iff_inv_mem_concentrationModel`: the pairwise Markov
  property relative to `G` holds exactly when `Σ⁻¹` lies in the concentration model of `G`.

The Hammersley–Clifford theorem and the intersection property for general positive densities
are not stated. Source: GAPS 105.26, Gaussian precision-matrix part.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace CKSD

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinates of `x` other than the `i`-th and the `j`-th. -/
def otherCoordinates (i j : ι) (x : EuclideanSpace ℝ ι) :
    {k : ι // k ≠ i ∧ k ≠ j} → ℝ := fun k ↦ x k.val

omit [Fintype ι] [DecidableEq ι] in
/-- The map to the coordinates other than `i` and `j` is measurable. -/
@[fun_prop] theorem measurable_otherCoordinates (i j : ι) :
    Measurable (otherCoordinates i j) := by
  unfold otherCoordinates
  fun_prop

/-- The concentration matrices of the Gaussian graphical model of `G`: positive definite
matrices with zero entries off the edges of `G`. -/
def concentrationModel (G : SimpleGraph ι) : Set (Matrix ι ι ℝ) :=
  {K | K.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → K i j = 0}

/-- The Gaussian pairwise Markov property of `N(m, Σ)` relative to an undirected graph: for
nonadjacent `i ≠ j`, the coordinates `xᵢ` and `xⱼ` are conditionally independent given the
remaining coordinates. -/
def HasGaussianPairwiseMarkovProperty (G : SimpleGraph ι) (m : EuclideanSpace ℝ ι)
    (Sigma : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬ G.Adj i j →
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : ι // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_otherCoordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma)

/-- GAPS 105.26: for a positive definite covariance `Σ` and `i ≠ j`, the coordinates `xᵢ` and
`xⱼ` of `N(m, Σ)` are conditionally independent given the remaining coordinates exactly when the
`(i, j)` entry of the concentration matrix `Σ⁻¹` vanishes. -/
theorem condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero
    (m : EuclideanSpace ℝ ι) (Sigma : Matrix ι ι ℝ)
    (hSigma : Sigma.PosDef) (i j : ι) (hij : i ≠ j) :
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : ι // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_otherCoordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma) ↔ Sigma⁻¹ i j = 0 := by
  sorry

/-- GAPS 105.26: for a positive definite covariance `Σ`, the law `N(m, Σ)` has the pairwise
Markov property relative to `G` exactly when its concentration matrix `Σ⁻¹` lies in the
concentration model of `G`. -/
theorem hasGaussianPairwiseMarkovProperty_iff_inv_mem_concentrationModel (G : SimpleGraph ι)
    (m : EuclideanSpace ℝ ι) {Sigma : Matrix ι ι ℝ} (hSigma : Sigma.PosDef) :
    HasGaussianPairwiseMarkovProperty G m Sigma ↔ Sigma⁻¹ ∈ concentrationModel G :=
  ⟨fun h ↦ ⟨hSigma.inv, fun i j hij hG ↦
      (condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero m Sigma hSigma i j hij).1
        (h i j hij hG)⟩,
    fun h i j hij hG ↦
      (condIndepFun_multivariateGaussian_iff_inv_apply_eq_zero m Sigma hSigma i j hij).2
        (h.2 i j hij hG)⟩

/-- The Gaussian log likelihood of a concentration matrix `K` for `n` observations with centred
sum-of-squares matrix `ssd`, up to an additive constant and the factor `n / 2`:
`log det K - tr(K ssd) / n`. -/
def gaussianConcentrationLogLikelihood (n : ℕ) (ssd K : Matrix ι ι ℝ) : ℝ :=
  Real.log K.det - Matrix.trace (K * ssd) / n

/-- `K` is the maximum likelihood estimate of the concentration matrix in the Gaussian graphical
model of `G`: it lies in the concentration model and has strictly larger likelihood than every
other concentration matrix of the model. -/
def IsConcentrationMLE (G : SimpleGraph ι) (n : ℕ) (ssd K : Matrix ι ι ℝ) : Prop :=
  K ∈ concentrationModel G ∧ ∀ K' ∈ concentrationModel G, K' ≠ K →
    gaussianConcentrationLogLikelihood n ssd K' < gaussianConcentrationLogLikelihood n ssd K

end CKSD
