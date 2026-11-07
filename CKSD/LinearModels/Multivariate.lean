module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# LinearModels: Multivariate

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- GAPS 105.22, normal sample mean/covariance independence and Hotelling's exact law. -/
theorem gaussian_sampleMean_scatterMatrix_wishart_and_hotelling
    {n p : ℕ} (hp : 0 < p) (hn : p + 1 ≤ n)
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hS : Sigma.PosDef) :
    let P := Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma);
    let S := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ ((n - 1 : ℕ) : ℝ)⁻¹ • scatterMatrix x;
    IndepFun sampleMean scatterMatrix P ∧
      P.map scatterMatrix = (TauCeti.Probability.wishartGramMeasure (n - 1) Sigma).map
        (fun W ↦ (W.val : Matrix (Fin p) (Fin p) ℝ)) ∧
      P.map (fun x ↦ ((n - p : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) * p) *
        ((n : ℝ) * matrixQuadraticForm (S x)⁻¹ (sampleMean x - m))) =
        TauCeti.Probability.fisherSnedecorMeasure p (n - p : ℕ) := by
  sorry

/-- GAPS 105.28, the full-rank Gaussian covariance likelihood has a unique minimum. -/
theorem gaussianNegLogLikelihood_minimum_unique
    {n p : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    let S := (n : ℝ)⁻¹ • scatterMatrix x;
    ∀ (hS : S.PosDef),
    ∀ (m : EuclideanSpace ℝ (Fin p)),
    ∀ (C : Matrix (Fin p) (Fin p) ℝ),
    ∀ (hC : C.PosDef),
    gaussianNegLogLikelihood x (sampleMean x) S ≤ gaussianNegLogLikelihood x m C ∧
      (gaussianNegLogLikelihood x (sampleMean x) S = gaussianNegLogLikelihood x m C ↔ m = sampleMean x ∧ C = S) := by
  sorry

/-- GAPS 105.31, determinant law obtained from Bartlett's decomposition. -/
theorem wishart_determinant_law {p : ℕ} (n : ℕ) (hn : p ≤ n)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hS : Sigma.PosDef) :
    (TauCeti.Probability.wishartGramMeasure n Sigma).map (fun W ↦ Matrix.det W.val) =
      (Measure.pi (fun i : Fin p ↦ TauCeti.Probability.chiSquaredMeasure (n - i.val : ℕ))).map
        (fun z ↦ Sigma.det * ∏ i, z i) := by
  sorry

/-- GAPS 105.32, exact correlation t law for independent standard-normal coordinates. -/
theorem gaussian_sample_correlation_student_law (N : ℕ) (hN : 2 < N) :
    let P := Measure.pi (fun _ : Fin N ↦ (gaussianReal 0 1).prod (gaussianReal 0 1));
    let a := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).1) / N;
    let b := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).2) / N;
    let r := fun x : Fin N → ℝ × ℝ ↦
      (∑ i, ((x i).1 - a x) * ((x i).2 - b x)) /
        Real.sqrt ((∑ i, ((x i).1 - a x) ^ 2) * (∑ i, ((x i).2 - b x) ^ 2));
    P.map (fun x ↦ Real.sqrt (N - 2 : ℕ) * r x / Real.sqrt (1 - r x ^ 2)) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) := by
  sorry


end CKSD
