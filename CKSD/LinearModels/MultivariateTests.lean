module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic

/-!
# Multivariate normal test statistics and eigenvalue limits

Wishart matrices use TauCeti's Gaussian-Gram laws, including singular hypothesis matrices.
Ordered eigenvalues reuse Mathlib's Hermitian spectral theorem and are set to zero on
non-Hermitian inputs; the statistical applications below always have Hermitian inputs.
Sources: GAPS 105.23, 105.24, 105.33, and 105.34.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Sample covariance with the maximum-likelihood divisor `n`. -/
def sampleCovarianceMatrix {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ := (n : ℝ)⁻¹ • scatterMatrix x

/-- Ordered Hermitian eigenvalues, with an explicit zero convention outside the Hermitian locus. -/
def symmetricMatrixEigenvalues {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues₀ ⟨j.val, by simpa using j.isLt⟩ else 0

/-- Wilks's determinant ratio for error and hypothesis scatter matrices. -/
def wilksLambda {p : ℕ} (E H : Matrix (Fin p) (Fin p) ℝ) : ℝ := E.det / (E + H).det

/-- The sphericity likelihood ratio before taking its sample-size power. -/
def sphericityRatio {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  A.det / (Matrix.trace A / p) ^ p

/-- The determinant ratio for independence of two consecutive coordinate blocks. -/
def blockIndependenceRatio {p q : ℕ} (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) : ℝ :=
  A.det / ((A.submatrix (Fin.castAdd q) (Fin.castAdd q)).det *
    (A.submatrix (Fin.natAdd p) (Fin.natAdd p)).det)

/-- Roots of a positive-error multivariate hypothesis, computed after symmetric whitening. -/
def multivariateHypothesisRoots {p : ℕ} (E H : Matrix (Fin p) (Fin p) ℝ) : Fin p → ℝ :=
  symmetricMatrixEigenvalues ((CFC.sqrt E)⁻¹ * H * (CFC.sqrt E)⁻¹)

/-- Lawley–Hotelling trace statistic. -/
def lawleyHotellingTrace {p : ℕ} (E H : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Matrix.trace (H * E⁻¹)

/-- Pillai trace statistic. -/
def pillaiTrace {p : ℕ} (E H : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Matrix.trace (H * (E + H)⁻¹)

/-- Roy's largest root, with the value zero for a zero-dimensional response space. -/
def royLargestRoot {p : ℕ} (E H : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  sSup (range (multivariateHypothesisRoots E H))

/-- Sample covariance is Hermitian, including an empty sample. -/
theorem sampleCovarianceMatrix_isHermitian {n p : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin p)) : (sampleCovarianceMatrix x).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [sampleCovarianceMatrix, scatterMatrix, mul_comm]

/-- GAPS 105.23: the exact Wilks product law for independent Wishart error and hypothesis matrices.
This is the distributional core; the linear-model projection reduction and Bartlett correction
are separate assertions of the catalogue family. -/
theorem map_wilksLambda_wishart_eq_beta_product {p : ℕ} (hp : 0 < p)
    (e h : ℕ) (he : p ≤ e) (hh : 0 < h)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hSigma : Sigma.PosDef) :
    ((TauCeti.Probability.wishartGramMeasure e Sigma).prod
      (TauCeti.Probability.wishartGramMeasure h Sigma)).map
      (fun z ↦ wilksLambda z.1.val z.2.val) =
      (Measure.pi fun i : Fin p ↦ ProbabilityTheory.betaMeasure
        (((e : ℝ) - i.val) / 2) ((h : ℝ) / 2)).map (fun v ↦ ∏ i, v i) := by
  sorry

/-- GAPS 105.24: central limit theorem for a simple eigenvalue of a centered Gaussian sample
covariance with divisor `n`. Multiplicities in other population eigenvalues are allowed. -/
theorem tendstoInDistribution_gaussian_sample_covariance_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (m : EuclideanSpace ℝ (Fin p))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hSigma : Sigma.PosDef)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hiid : IsIndependentIdenticallyDistributed P X (multivariateGaussian m Sigma))
    (j : Fin p) (hpos : 0 < symmetricMatrixEigenvalues Sigma j)
    (hsimple : ∀ i : Fin p, i ≠ j →
      symmetricMatrixEigenvalues Sigma i ≠ symmetricMatrixEigenvalues Sigma j) :
    TendstoInDistribution P (fun n ω ↦ Real.sqrt n *
      (symmetricMatrixEigenvalues (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω)) j -
        symmetricMatrixEigenvalues Sigma j))
      (gaussianReal 0 (Real.toNNReal (2 * symmetricMatrixEigenvalues Sigma j ^ 2))) := by
  sorry

/-- GAPS 105.33: Wilks's chi-squared limit for sphericity in fixed dimension.
The second-order Bartlett approximation is outside this first-order limit statement. -/
theorem tendstoInDistribution_sphericity_likelihood_ratio
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 2 ≤ p)
    (P : Measure Ω) [IsProbabilityMeasure P] (m : EuclideanSpace ℝ (Fin p))
    (v : ℝ≥0) (hv : 0 < v) (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hiid : IsIndependentIdenticallyDistributed P X
      (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)))) :
    TendstoInDistribution P (fun n ω ↦ -(n : ℝ) * Real.log
      (sphericityRatio (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω))))
      (TauCeti.Probability.chiSquaredMeasure (p * (p + 1) / 2 - 1 : ℕ)) := by
  sorry

/-- GAPS 105.33: the first-order likelihood-ratio limit for two independent Gaussian blocks. -/
theorem tendstoInDistribution_block_independence_likelihood_ratio
    {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (P : Measure Ω) [IsProbabilityMeasure P] (m : EuclideanSpace ℝ (Fin (p + q)))
    (Sigma : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (hSigma : Sigma.PosDef)
    (hblock : ∀ i : Fin p, ∀ j : Fin q, Sigma (Fin.castAdd q i) (Fin.natAdd p j) = 0)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin (p + q)))
    (hiid : IsIndependentIdenticallyDistributed P X (multivariateGaussian m Sigma)) :
    TendstoInDistribution P (fun n ω ↦ -(n : ℝ) * Real.log
      (blockIndependenceRatio (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω))))
      (TauCeti.Probability.chiSquaredMeasure (p * q : ℕ)) := by
  sorry

/-- GAPS 105.34: generalized roots classify scatter-matrix pairs under simultaneous congruence.
This is the algebraic maximal-invariant assertion for response transformations. -/
theorem multivariateHypothesisRoots_eq_iff_congruent {p : ℕ}
    (E H E' H' : Matrix (Fin p) (Fin p) ℝ)
    (hE : E.PosDef) (hE' : E'.PosDef) (hH : H.PosSemidef) (hH' : H'.PosSemidef) :
    multivariateHypothesisRoots E H = multivariateHypothesisRoots E' H' ↔
      ∃ A : Matrix (Fin p) (Fin p) ℝ, IsUnit A ∧
        E' = A.transpose * E * A ∧ H' = A.transpose * H * A := by
  sorry

/-- GAPS 105.34: the determinant, Lawley–Hotelling, and Pillai statistics in generalized roots. -/
theorem multivariate_test_statistics_eq_roots {p : ℕ}
    (E H : Matrix (Fin p) (Fin p) ℝ) (hE : E.PosDef) (hH : H.PosSemidef) :
    wilksLambda E H = ∏ i, (1 + multivariateHypothesisRoots E H i)⁻¹ ∧
      lawleyHotellingTrace E H = (∑ i, multivariateHypothesisRoots E H i) ∧
      pillaiTrace E H = ∑ i, multivariateHypothesisRoots E H i /
        (1 + multivariateHypothesisRoots E H i) := by
  sorry

end CKSD
