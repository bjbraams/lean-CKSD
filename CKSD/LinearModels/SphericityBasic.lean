module
public import CKSD.LinearModels.Multivariate
/-!
# Sphericity ratios and Gaussian sample covariance

Nonzero rescaling leaves the determinant-to-average-trace ratio invariant. The Gaussian sample
covariance therefore has the same ratio law as its Wishart scatter matrix. Matrix measurability
uses Mathlib's finite sums and coordinate evaluations; the Gaussian scatter law is imported from
the local multivariate sample theory using pinned TauCeti Wishart laws.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators MatrixOrder
namespace CKSD
/-- Sample covariance with the maximum-likelihood divisor `n`. -/
def sampleCovarianceMatrix {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ := (n : ℝ)⁻¹ • scatterMatrix x
/-- The sphericity likelihood ratio before taking its sample-size power. -/
def sphericityRatio {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  A.det / (Matrix.trace A / p) ^ p
/-- Nonzero rescaling leaves the sphericity determinant ratio invariant. -/
theorem sphericityRatio_smul {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphericityRatio (r • A) = sphericityRatio A := by
  simp only [sphericityRatio, Matrix.det_smul, Fintype.card_fin, Matrix.trace_smul, smul_eq_mul,
    show r * Matrix.trace A / (p:ℝ) = r * (Matrix.trace A / (p:ℝ)) by ring, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero p hr)
/-- The sphericity ratio is a Borel measurable function of the matrix. -/
theorem measurable_sphericityRatio (p : ℕ) :
    Measurable (sphericityRatio : Matrix (Fin p) (Fin p) ℝ → ℝ) := by
  unfold sphericityRatio
  fun_prop
/-- The finite Euclidean sample mean is Borel measurable. -/
theorem measurable_sampleMean {n p : ℕ} : Measurable (sampleMean : (Fin n → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p)) := by
  unfold sampleMean
  fun_prop

/-- The finite centered scatter matrix is Borel measurable. -/
theorem measurable_scatterMatrix {n p : ℕ} : Measurable (scatterMatrix : (Fin n → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) (Fin p) ℝ) := by
  unfold scatterMatrix
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro l
  apply Finset.measurable_fun_sum
  intro i _
  exact ((((PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) j).measurable) |>.comp (measurable_pi_apply i)).sub
    ((((PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) j).measurable)).comp measurable_sampleMean)).mul
    ((((PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) l).measurable) |>.comp (measurable_pi_apply i)).sub
      ((((PiLp.continuous_apply 2 (fun _ : Fin p ↦ ℝ) l).measurable)).comp measurable_sampleMean))

/-- The sample covariance with divisor `n` is Borel measurable, including an empty sample. -/
theorem measurable_sampleCovarianceMatrix {n p : ℕ} :
    Measurable (sampleCovarianceMatrix : (Fin n → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) (Fin p) ℝ) := by
  change Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ (n:ℝ)⁻¹ • scatterMatrix x)
  exact (measurable_const (a := (n:ℝ)⁻¹)).smul (measurable_scatterMatrix (n := n) (p := p))

set_option maxHeartbeats 800000 in
/-- Gaussian sample covariance and the Wishart scatter have the same sphericity ratio law. -/
theorem map_sphericityRatio_sampleCovarianceMatrix_eq_wishart
    {n p : ℕ} (hp : 0 < p) (hn : p + 1 ≤ n)
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ) (hS : Sigma.PosDef) :
    (Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma)).map
      (fun x ↦ sphericityRatio (sampleCovarianceMatrix x)) =
      (TauCeti.Probability.wishartGramMeasure (n-1) Sigma).map
        (fun A ↦ sphericityRatio (A.val : Matrix (Fin p) (Fin p) ℝ)) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have heq : (fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ sphericityRatio (sampleCovarianceMatrix x)) =
      fun x ↦ sphericityRatio (scatterMatrix x) := by
    funext x
    exact sphericityRatio_smul _ (inv_ne_zero hn0)
  rw [heq]
  change (Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma)).map
    (sphericityRatio ∘ scatterMatrix) = _
  rw [← Measure.map_map (measurable_sphericityRatio p) measurable_scatterMatrix,
    (gaussian_sampleMean_scatterMatrix_wishart_and_hotelling hp hn m Sigma hS).2.1,
    Measure.map_map (measurable_sphericityRatio p) measurable_subtype_coe]
  rfl
end CKSD
