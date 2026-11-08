module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import CKSD.LinearModels.CanonicalCorrelation

/-!
# Multivariate normal test statistics and eigenvalue limits

Likelihood-ratio statistics for multivariate normal samples, their exact and asymptotic laws,
and their expression through the generalized roots of a pair of scatter matrices.

## Main definitions

* `CKSD.sampleCovarianceMatrix`: the sample covariance with divisor `n`.
* `CKSD.symmetricMatrixEigenvalues`: the eigenvalues of a symmetric matrix in decreasing order
  (Mathlib's `Matrix.IsHermitian.eigenvalues₀`), with the value `0` off the symmetric matrices.
* `CKSD.wilksLambda`, `CKSD.lawleyHotellingTrace`, `CKSD.pillaiTrace`, `CKSD.royLargestRoot`:
  the classical statistics of an error matrix `E` and a hypothesis matrix `H`.
* `CKSD.multivariateHypothesisRoots`: the generalized roots of `det(H - λ E) = 0`, computed as
  the eigenvalues of `E^{-1/2} H E^{-1/2}`.
* `CKSD.sphericityRatio`, `CKSD.blockIndependenceRatio`: the determinant ratios of the
  likelihood-ratio tests of sphericity and of independence of two blocks.

## Main results

* `CKSD.map_wilksLambda_wishart_eq_beta_product`: for independent `E ∼ W_p(e, Σ)` and
  `H ∼ W_p(h, Σ)`, Wilks's `Λ` is a product of independent beta variables.
* `CKSD.tendstoInDistribution_gaussian_sample_covariance_eigenvalue`: asymptotic normality of a
  simple eigenvalue of the sample covariance.
* `CKSD.tendstoInDistribution_sphericity_likelihood_ratio`,
  `CKSD.tendstoInDistribution_block_independence_likelihood_ratio`: Wilks's chi-squared limits.
* `CKSD.multivariateHypothesisRoots_eq_iff_congruent`: the generalized roots classify pairs
  `(E, H)` under simultaneous congruence, so they form a maximal invariant.
* `CKSD.multivariate_test_statistics_eq_roots`: Wilks's `Λ`, the Lawley–Hotelling trace and
  Pillai's trace as functions of the generalized roots.

The root forms use Mathlib's spectral theorem `Matrix.IsHermitian.spectral_theorem` and
`Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff`; the Wishart laws are TauCeti's
Gaussian-Gram laws, which also cover singular scale matrices.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapters 8–11 and 13.
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
  if h : A.IsHermitian then h.eigenvalues₀ ⟨j.val, by simp⟩ else 0

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

/-- GAPS 105.23: for independent Wishart matrices `E ∼ W_p(e, Σ)` and `H ∼ W_p(h, Σ)` with
`p ≤ e`, `0 < h` and `Σ` positive definite, Wilks's `Λ = det E / det(E + H)` has the law of a
product `∏_{i<p} Bᵢ` of independent `Bᵢ ∼ Beta((e - i)/2, h/2)`. This is the distributional
core; the linear-model projection reduction and the Bartlett correction are not stated. -/
theorem map_wilksLambda_wishart_eq_beta_product {p : ℕ}
    (e h : ℕ) (he : p ≤ e) (hh : 0 < h)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hSigma : Sigma.PosDef) :
    ((TauCeti.Probability.wishartGramMeasure e Sigma).prod
      (TauCeti.Probability.wishartGramMeasure h Sigma)).map
      (fun z ↦ wilksLambda z.1.val z.2.val) =
      (Measure.pi fun i : Fin p ↦ ProbabilityTheory.betaMeasure
        (((e : ℝ) - i.val) / 2) ((h : ℝ) / 2)).map (fun v ↦ ∏ i, v i) := by
  sorry

/-- GAPS 105.24: central limit theorem for a simple eigenvalue: for an i.i.d. sample from
`N_p(m, Σ)` with `Σ` positive definite and a simple eigenvalue `λ_j` of `Σ`, the `j`-th largest
eigenvalue `λ̂_j` of the sample covariance (divisor `n`) satisfies
`√n (λ̂_j - λ_j) ⇒ N(0, 2 λ_j²)`. Multiplicities of the other eigenvalues are allowed. -/
theorem tendstoInDistribution_gaussian_sample_covariance_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (m : EuclideanSpace ℝ (Fin p))
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hSigma : Sigma.PosDef)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hiid : IsIndependentIdenticallyDistributed P X (multivariateGaussian m Sigma))
    (j : Fin p)
    (hsimple : ∀ i : Fin p, i ≠ j →
      symmetricMatrixEigenvalues Sigma i ≠ symmetricMatrixEigenvalues Sigma j) :
    TendstoInDistribution P (fun n ω ↦ Real.sqrt n *
      (symmetricMatrixEigenvalues (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω)) j -
        symmetricMatrixEigenvalues Sigma j))
      (gaussianReal 0 (Real.toNNReal (2 * symmetricMatrixEigenvalues Sigma j ^ 2))) := by
  sorry

/-- GAPS 105.33: Wilks's chi-squared limit for sphericity in fixed dimension `p ≥ 2`: under
`N_p(m, v I)` with `v > 0`, the likelihood-ratio statistic `-n log(det S / (tr S / p)^p)` converges
in distribution to `χ²` with `p(p+1)/2 - 1` degrees of freedom. The second-order Bartlett
approximation is not stated. -/
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

/-- GAPS 105.33: under `N_{p+q}(m, Σ)` with `Σ` positive definite and block diagonal, the
likelihood-ratio statistic `-n log(det S / (det S₁₁ det S₂₂))` for independence of the two
blocks converges in distribution to `χ²` with `p q` degrees of freedom. -/
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

section RootStatistics

open Matrix

/-- Two real symmetric matrices have the same ordered eigenvalues exactly when they have the same
characteristic polynomial. -/
theorem isHermitian_eigenvalues₀_eq_iff {p : ℕ} {A B : Matrix (Fin p) (Fin p) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues₀ = hB.eigenvalues₀ ↔ A.charpoly = B.charpoly := by
  rw [← hA.eigenvalues_eq_eigenvalues_iff hB]
  constructor
  · intro h
    unfold IsHermitian.eigenvalues
    rw [h]
  · intro h
    funext k
    have := congrFun h (Fintype.equivOfCardEq (Fintype.card_fin _) k)
    simpa [IsHermitian.eigenvalues] using this

/-- When the whitened hypothesis matrices `E^{-1/2} H E^{-1/2}` are symmetric, two pairs have the
same generalized roots exactly when these matrices have the same characteristic polynomial. -/
theorem multivariateHypothesisRoots_eq_iff_charpoly_eq {p : ℕ}
    (E H E' H' : Matrix (Fin p) (Fin p) ℝ)
    (hM : ((CFC.sqrt E)⁻¹ * H * (CFC.sqrt E)⁻¹).IsHermitian)
    (hM' : ((CFC.sqrt E')⁻¹ * H' * (CFC.sqrt E')⁻¹).IsHermitian) :
    multivariateHypothesisRoots E H = multivariateHypothesisRoots E' H' ↔
      ((CFC.sqrt E)⁻¹ * H * (CFC.sqrt E)⁻¹).charpoly =
        ((CFC.sqrt E')⁻¹ * H' * (CFC.sqrt E')⁻¹).charpoly := by
  rw [← isHermitian_eigenvalues₀_eq_iff hM hM']
  have h₁ : multivariateHypothesisRoots E H = fun j ↦ hM.eigenvalues₀ ⟨j.val, by simp⟩ := by
    funext j
    simp only [multivariateHypothesisRoots, symmetricMatrixEigenvalues]
    split_ifs with h
    · rfl
    · exact absurd hM h
  have h₂ : multivariateHypothesisRoots E' H' = fun j ↦ hM'.eigenvalues₀ ⟨j.val, by simp⟩ := by
    funext j
    simp only [multivariateHypothesisRoots, symmetricMatrixEigenvalues]
    split_ifs with h
    · rfl
    · exact absurd hM' h
  rw [h₁, h₂]
  constructor
  · intro h
    funext k
    have := congrFun h ⟨k.val, by simpa using k.isLt⟩
    simpa using this
  · intro h
    rw [h]

/-- GAPS 105.34: generalized roots classify scatter-matrix pairs under simultaneous congruence:
for `E`, `E'` positive definite and `H`, `H'` positive semidefinite, the pairs `(E, H)` and
`(E', H')` have the same generalized roots exactly when `E' = Aᵀ E A` and `H' = Aᵀ H A` for some
invertible `A`. This is the algebraic maximal-invariant assertion for response
transformations. -/
theorem multivariateHypothesisRoots_eq_iff_congruent {p : ℕ}
    (E H E' H' : Matrix (Fin p) (Fin p) ℝ)
    (hE : E.PosDef) (hE' : E'.PosDef) (hH : H.PosSemidef) (hH' : H'.PosSemidef) :
    multivariateHypothesisRoots E H = multivariateHypothesisRoots E' H' ↔
      ∃ A : Matrix (Fin p) (Fin p) ℝ, IsUnit A ∧
        E' = A.transpose * E * A ∧ H' = A.transpose * H * A := by
  have hRt := transpose_inv_sqrt_of_posSemidef hE.posSemidef
  have hRR := inv_sqrt_mul_inv_sqrt_of_posSemidef hE.posSemidef
  have hRt' := transpose_inv_sqrt_of_posSemidef hE'.posSemidef
  have hRR' := inv_sqrt_mul_inv_sqrt_of_posSemidef hE'.posSemidef
  have hRER := inv_sqrt_mul_mul_inv_sqrt_of_posDef hE
  have hRER' := inv_sqrt_mul_mul_inv_sqrt_of_posDef hE'
  have hRu := isUnit_det_inv_sqrt_of_posDef hE
  have hRu' := isUnit_det_inv_sqrt_of_posDef hE'
  set R := (CFC.sqrt E)⁻¹
  set R' := (CFC.sqrt E')⁻¹
  have hpsd : ∀ {S K : Matrix (Fin p) (Fin p) ℝ}, Sᵀ = S → K.PosSemidef → (S * K * S).PosSemidef := by
    intro S K hS hK
    have := hK.conjTranspose_mul_mul_same S
    rwa [conjTranspose_eq_transpose_of_trivial, hS] at this
  have hM := (hpsd hRt hH).isHermitian
  have hM' := (hpsd hRt' hH').isHermitian
  rw [multivariateHypothesisRoots_eq_iff_charpoly_eq E H E' H' hM hM']
  have hRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRinv' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hRu
  have hR'inv : R' * R'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRu'
  have hR'inv' : R'⁻¹ * R' = 1 := Matrix.nonsing_inv_mul _ hRu'
  have hEeq : ∀ {S T : Matrix (Fin p) (Fin p) ℝ}, S * S⁻¹ = 1 → S⁻¹ * S = 1 → S * T * S = 1 →
      T = S⁻¹ * S⁻¹ := by
    intro S T h1 h2 h3
    calc T = S⁻¹ * (S * T * S) * S⁻¹ := by
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
      _ = S⁻¹ * S⁻¹ := by rw [h3, Matrix.mul_one]
  have hE₀ := hEeq hRinv hRinv' hRER
  have hE₀' := hEeq hR'inv hR'inv' hRER'
  have hEdet : IsUnit E.det := isUnit_iff_ne_zero.2 hE.det_pos.ne'
  constructor
  · intro hchar
    -- diagonalize both whitened matrices with the same eigenvalues
    have heig : hM.eigenvalues = hM'.eigenvalues := (hM.eigenvalues_eq_eigenvalues_iff hM').2 hchar
    have hs := hM.spectral_theorem
    have hs' := hM'.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs hs'
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at hs hs'
    set U : Matrix (Fin p) (Fin p) ℝ := ↑hM.eigenvectorUnitary
    set U' : Matrix (Fin p) (Fin p) ℝ := ↑hM'.eigenvectorUnitary
    have hu1 : star U * U = 1 := Unitary.coe_star_mul_self _
    have hu2 : U * star U = 1 := Unitary.coe_mul_star_self _
    have hu1' : star U' * U' = 1 := Unitary.coe_star_mul_self _
    have hu2' : U' * star U' = 1 := Unitary.coe_mul_star_self _
    rw [heig] at hs
    set D := diagonal hM'.eigenvalues
    -- `W = U U'ᵀ` carries one whitened matrix to the other
    let W := U * star U'
    have hWW : star W * W = 1 := by
      simp only [W, star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U), hu1, Matrix.one_mul, hu2']
    have hMM : R' * H' * R' = star W * (R * H * R) * W := by
      rw [hs', hs]
      simp only [W, star_mul, star_star, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hu1, Matrix.one_mul, ← Matrix.mul_assoc (star U) U,
        hu1, Matrix.one_mul]
    have hstarW : (star W)ᵀ = W := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_transpose]
    have hAt : (R * W * R'⁻¹)ᵀ = R'⁻¹ * star W * R := by
      rw [transpose_mul, transpose_mul, transpose_nonsing_inv, hRt', hRt, Matrix.mul_assoc,
        star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    have hconj : ∀ X : Matrix (Fin p) (Fin p) ℝ, (R * W * R'⁻¹)ᵀ * X * (R * W * R'⁻¹) =
        R'⁻¹ * (star W * (R * X * R) * W) * R'⁻¹ := by
      intro X
      rw [hAt]
      simp only [Matrix.mul_assoc]
    refine ⟨R * W * R'⁻¹, ?_, ?_, ?_⟩
    · refine ((Matrix.isUnit_iff_isUnit_det _).2 hRu).mul
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse hWW)) |>.mul
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det R' hRu'))
    · rw [hconj, hRER, Matrix.mul_one, hWW, Matrix.mul_one, hE₀']
    · rw [hconj, ← hMM, Matrix.mul_assoc, Matrix.mul_assoc, hR'inv, Matrix.mul_one,
        ← Matrix.mul_assoc, hR'inv', Matrix.one_mul]
  · rintro ⟨A, hA, rfl, rfl⟩
    have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
    have hAtd : IsUnit Aᵀ.det := Matrix.isUnit_det_transpose A hAd
    calc (R * H * R).charpoly = (R * R * H).charpoly := by
          rw [charpoly_mul_comm, ← Matrix.mul_assoc]
      _ = (A⁻¹ * (E⁻¹ * H * A)).charpoly := by
          rw [charpoly_mul_comm A⁻¹ (E⁻¹ * H * A), hRR, Matrix.mul_assoc (E⁻¹ * H),
            Matrix.mul_nonsing_inv _ hAd, Matrix.mul_one]
      _ = (R' * R' * (Aᵀ * H * A)).charpoly := by
          rw [hRR', Matrix.mul_inv_rev, Matrix.mul_inv_rev]
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Aᵀ⁻¹ Aᵀ, Matrix.nonsing_inv_mul _ hAtd, Matrix.one_mul]
      _ = (R' * (Aᵀ * H * A) * R').charpoly := by
          rw [Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc]

/-- For a real symmetric matrix `M`, `det (1 + M) = ∏ᵢ (1 + λᵢ)` over its eigenvalues `λᵢ`. -/
theorem isHermitian_det_one_add_eq_prod {p : ℕ} {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.IsHermitian) : (1 + M).det = ∏ i, (1 + hM.eigenvalues i) := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at h
  set U : Matrix (Fin p) (Fin p) ℝ := ↑hM.eigenvectorUnitary
  set d := hM.eigenvalues
  have hu1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hu2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have h1M : 1 + M = U * diagonal (fun i ↦ 1 + d i) * star U := by
    have : diagonal (fun i ↦ 1 + d i) = 1 + diagonal d := by
      rw [← diagonal_one, diagonal_add]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hu2, ← h]
  rw [h1M, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, hu1, det_one,
    one_mul]

/-- For a real symmetric matrix `M` with nonnegative eigenvalues `λᵢ`,
`tr (M (1 + M)⁻¹) = ∑ᵢ λᵢ / (1 + λᵢ)`. -/
theorem isHermitian_trace_mul_inv_one_add_eq_sum {p : ℕ}
    {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.IsHermitian) (hnn : ∀ i, 0 ≤ hM.eigenvalues i) :
    trace (M * (1 + M)⁻¹) = ∑ i, hM.eigenvalues i / (1 + hM.eigenvalues i) := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at h
  set U : Matrix (Fin p) (Fin p) ℝ := ↑hM.eigenvectorUnitary
  set d := hM.eigenvalues
  have hu1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hu2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hd : ∀ i, 1 + d i ≠ 0 := fun i ↦ by linarith [hnn i]
  have h1M : 1 + M = U * diagonal (fun i ↦ 1 + d i) * star U := by
    have : diagonal (fun i ↦ 1 + d i) = 1 + diagonal d := by
      rw [← diagonal_one, diagonal_add]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hu2, ← h]
  have hinv : (1 + M)⁻¹ = U * diagonal (fun i ↦ (1 + d i)⁻¹) * star U := by
    refine Matrix.inv_eq_left_inv ?_
    rw [h1M]
    calc U * diagonal (fun i ↦ (1 + d i)⁻¹) * star U * (U * diagonal (fun i ↦ 1 + d i) * star U)
        = U * (diagonal (fun i ↦ (1 + d i)⁻¹) * (star U * U) * diagonal (fun i ↦ 1 + d i)) *
            star U := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hu1, Matrix.mul_one, diagonal_mul_diagonal]
        have : (fun i ↦ (1 + d i)⁻¹ * (1 + d i)) = fun _ ↦ (1 : ℝ) :=
          funext fun i ↦ inv_mul_cancel₀ (hd i)
        rw [this, diagonal_one, Matrix.mul_one, hu2]
  rw [hinv]
  conv_lhs => rw [h]
  calc trace (U * diagonal d * star U * (U * diagonal (fun i ↦ (1 + d i)⁻¹) * star U))
      = trace (U * (diagonal d * (star U * U) * diagonal (fun i ↦ (1 + d i)⁻¹)) * star U) := by
        simp only [Matrix.mul_assoc]
    _ = trace (diagonal d * diagonal (fun i ↦ (1 + d i)⁻¹) * (star U * U)) := by
        rw [hu1, Matrix.mul_one, trace_mul_comm, ← Matrix.mul_assoc, hu1, Matrix.one_mul,
          Matrix.mul_one]
    _ = _ := by
        rw [hu1, Matrix.mul_one, diagonal_mul_diagonal, trace_diagonal]
        rfl

/-- Sums over the ordered eigenvalues agree with sums over the matrix-indexed eigenvalues. -/
theorem isHermitian_sum_eigenvalues₀_eq {p : ℕ} {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    ∑ j : Fin p, f (hM.eigenvalues₀ ⟨j.val, by simp⟩) =
      ∑ i, f (hM.eigenvalues i) := by
  simp only [IsHermitian.eigenvalues]
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k ↦ f (hM.eigenvalues₀ k))]
  exact Fintype.sum_equiv (finCongr (by simp)) _ _ fun j ↦ rfl

/-- Products over the ordered eigenvalues agree with products over the matrix-indexed
eigenvalues. -/
theorem isHermitian_prod_eigenvalues₀_eq {p : ℕ} {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    ∏ j : Fin p, f (hM.eigenvalues₀ ⟨j.val, by simp⟩) =
      ∏ i, f (hM.eigenvalues i) := by
  simp only [IsHermitian.eigenvalues]
  rw [Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k ↦ f (hM.eigenvalues₀ k))]
  exact Fintype.prod_equiv (finCongr (by simp)) _ _ fun j ↦ rfl

/-- GAPS 105.34: in terms of the generalized roots `λᵢ` of a positive definite `E` and a positive
semidefinite `H`, Wilks's `Λ = ∏ (1 + λᵢ)⁻¹`, the Lawley–Hotelling trace is `∑ λᵢ`, and Pillai's
trace is `∑ λᵢ / (1 + λᵢ)`. -/
theorem multivariate_test_statistics_eq_roots {p : ℕ}
    (E H : Matrix (Fin p) (Fin p) ℝ) (hE : E.PosDef) (hH : H.PosSemidef) :
    wilksLambda E H = ∏ i, (1 + multivariateHypothesisRoots E H i)⁻¹ ∧
      lawleyHotellingTrace E H = (∑ i, multivariateHypothesisRoots E H i) ∧
      pillaiTrace E H = ∑ i, multivariateHypothesisRoots E H i /
        (1 + multivariateHypothesisRoots E H i) := by
  have hRt := transpose_inv_sqrt_of_posSemidef hE.posSemidef
  have hRR := inv_sqrt_mul_inv_sqrt_of_posSemidef hE.posSemidef
  have hRER := inv_sqrt_mul_mul_inv_sqrt_of_posDef hE
  have hRu := isUnit_det_inv_sqrt_of_posDef hE
  set R := (CFC.sqrt E)⁻¹
  set M := R * H * R with hMdef
  have hMpsd : M.PosSemidef := by
    have := hH.conjTranspose_mul_mul_same R
    rwa [conjTranspose_eq_transpose_of_trivial, hRt] at this
  have hM : M.IsHermitian := hMpsd.isHermitian
  have hnn : ∀ i, 0 ≤ hM.eigenvalues i := hMpsd.eigenvalues_nonneg
  have hdet := isHermitian_det_one_add_eq_prod hM
  have htr := isHermitian_trace_mul_inv_one_add_eq_sum hM hnn
  have hroots : ∀ j, multivariateHypothesisRoots E H j =
      hM.eigenvalues₀ ⟨j.val, by simp⟩ := fun j ↦ by
    simp only [multivariateHypothesisRoots, symmetricMatrixEigenvalues]
    split_ifs with h
    · rfl
    · exact absurd hM h
  simp_rw [hroots]
  have e₁ := isHermitian_sum_eigenvalues₀_eq hM (fun t ↦ t)
  have e₂ := isHermitian_sum_eigenvalues₀_eq hM (fun t ↦ t / (1 + t))
  have e₃ := isHermitian_prod_eigenvalues₀_eq hM (fun t ↦ (1 + t)⁻¹)
  rw [e₁, e₂, e₃]
  have hRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRinv' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hRu
  have hEeq : E = R⁻¹ * R⁻¹ := by
    calc E = R⁻¹ * (R * E * R) * R⁻¹ := by
          simp only [Matrix.mul_assoc, hRinv, Matrix.mul_one]
          rw [← Matrix.mul_assoc, hRinv', Matrix.one_mul]
      _ = R⁻¹ * R⁻¹ := by rw [hRER, Matrix.mul_one]
  have hEH : E + H = R⁻¹ * (1 + M) * R⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hEeq, hMdef]
    congr 1
    simp only [← Matrix.mul_assoc, hRinv', Matrix.one_mul]
    rw [Matrix.mul_assoc, hRinv, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [wilksLambda, hEH, hEeq, det_mul, det_mul, det_mul, hdet, Finset.prod_inv_distrib]
    have : (R⁻¹).det ≠ 0 := by
      have h := congrArg det hRinv'
      rw [det_mul, det_one] at h
      exact left_ne_zero_of_mul_eq_one h
    field_simp
  · rw [lawleyHotellingTrace, ← hRR, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
      ← hMdef, hM.trace_eq_sum_eigenvalues]
    simp
  · rw [pillaiTrace, hEH, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hRu, ← htr]
    rw [show H * (R * ((1 + M)⁻¹ * R)) = (H * R) * ((1 + M)⁻¹ * R) by
      simp only [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

end RootStatistics

end CKSD
