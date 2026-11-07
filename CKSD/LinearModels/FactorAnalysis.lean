module

public import CKSD.LinearModels.MultivariateTests

/-!
# Orthogonal factor models

The factor covariance and Gaussian likelihood criterion are explicit matrix functions.
Identification below concerns the nonzero, distinct normalized-loading regime; it does not
assert identifiability of the decomposition into common and unique covariance components.
Sources: GAPS 105.35 and SYNOPSIS105, item 35.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Covariance of an orthogonal factor model with diagonal unique variances. -/
def factorCovariance {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ := L * L.transpose + Matrix.diagonal psi

/-- Gaussian covariance criterion for a factor model, up to a constant and sample-size factor. -/
def factorLikelihoodCriterion {p m : ℕ} (C : Matrix (Fin p) (Fin p) ℝ)
    (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) : ℝ :=
  Real.log (factorCovariance L psi).det + Matrix.trace (C * (factorCovariance L psi)⁻¹)

/-- Normalized loadings have distinct decreasing positive weighted column squared lengths. -/
def IsNormalizedFactorLoading {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (psi : Fin p → ℝ) : Prop :=
  ∃ a : Fin m → ℝ, StrictAnti a ∧ (∀ i, 0 < a i) ∧
    L.transpose * (Matrix.diagonal psi)⁻¹ * L = Matrix.diagonal a

/-- A signed relabeling that changes only factor-column signs. -/
def factorColumnSigns {m : ℕ} (s : Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun j ↦ if s j then (1 : ℝ) else -1)

/-- Distance between two loading matrices modulo factor-column signs, in operator norm. -/
def loadingSignDistance {p m : ℕ} (L M : Matrix (Fin p) (Fin m) ℝ) : ℝ :=
  sInf (range fun s : Fin m → Bool ↦
    ‖LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℝ) (L * factorColumnSigns s - M))‖)

/-- Orthogonal rotations of factors do not change their implied covariance. -/
theorem factorCovariance_mul_orthogonal {p m : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ)
    (O : Matrix (Fin m) (Fin m) ℝ) (hO : O * O.transpose = 1) :
    factorCovariance (L * O) psi = factorCovariance L psi := by
  simp only [factorCovariance, Matrix.transpose_mul]
  congr 1
  calc
    (L * O) * (O.transpose * L.transpose) = L * (O * O.transpose) * L.transpose := by
      simp only [Matrix.mul_assoc]
    _ = L * L.transpose := by rw [hO, Matrix.mul_one]

/-- GAPS 105.35: normalized nondegenerate loadings are identified up to column signs once
both their common covariance and the diagonal unique covariance are specified. -/
theorem normalizedFactorLoading_eq_up_to_signs {p m : ℕ}
    (L M : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) (hpsi : ∀ i, 0 < psi i)
    (hL : IsNormalizedFactorLoading L psi) (hM : IsNormalizedFactorLoading M psi)
    (hcov : L * L.transpose = M * M.transpose) :
    ∃ s : Fin m → Bool, M = L * factorColumnSigns s := by
  sorry

/-- GAPS 105.35: consistency of factor maximum likelihood on a compact identified parameter set.
Compactness and uniform positive unique variances are explicit restrictions of this formulation;
the unrestricted parameter-space and asymptotic-normality assertions are not included. -/
theorem tendstoInProbabilityConst_factor_mle_of_compact
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set (Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ))) (hK : IsCompact K)
    (a : ℝ) (ha : 0 < a) (hpos : ∀ z ∈ K, ∀ i, a ≤ z.2 i)
    (L₀ : Matrix (Fin p) (Fin m) ℝ) (psi₀ : Fin p → ℝ) (hmem : (L₀, psi₀) ∈ K)
    (hidentified : ∀ z ∈ K, factorCovariance z.1 z.2 = factorCovariance L₀ psi₀ →
      z.2 = psi₀ ∧ ∃ s : Fin m → Bool, z.1 = L₀ * factorColumnSigns s)
    (C : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hC : ∀ n, Measurable (C n))
    (hClim : TendstoInProbabilityConst P C (factorCovariance L₀ psi₀))
    (T : ℕ → Ω → Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ))
    (hT : ∀ n, Measurable (T n)) (hTK : ∀ n ω, T n ω ∈ K)
    (hopt : ∀ n, ∀ᵐ ω ∂P, ∀ z ∈ K,
      factorLikelihoodCriterion (C n ω) (T n ω).1 (T n ω).2 ≤
        factorLikelihoodCriterion (C n ω) z.1 z.2) :
    TendstoInProbabilityConst P (fun n ω ↦ (T n ω).2) psi₀ ∧
      TendstoInProbabilityConst P (fun n ω ↦ loadingSignDistance (T n ω).1 L₀) 0 := by
  sorry

end CKSD
