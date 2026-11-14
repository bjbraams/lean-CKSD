module

public import TauCeti.Probability.Distributions.Wishart.Agreement
public import TauCeti.Probability.Distributions.Wishart.Determinant
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Determinant tilts of Wishart laws

Multiplication of a nonsingular Wishart density by a natural determinant power shifts its
degree by twice that power. The normalizing factor is the ratio of the two Wishart constants.

This is a direct density calculation from pinned TauCeti's nonsingular Wishart definition.
TauCeti also supplies the Gram-density agreement and determinant-moment formulas used by callers.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
namespace CKSD
/-- The normalizing denominator of a nonsingular Wishart density. -/
def wishartNormalizer {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  2 ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) * TauCeti.multivariateGamma p (n / 2)
/-- A valid Wishart normalizer is strictly positive. -/
theorem wishart_normalizer_pos {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) : 0 < wishartNormalizer n S := by
  apply mul_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos hS.det_pos _))
  exact TauCeti.multivariateGamma_pos (by linarith)
/-- Multiplication by a determinant power shifts the Wishart density's degree. -/
theorem det_pow_mul_wishart_pdf_real {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (k : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (A : Matrix (Fin p) (Fin p) ℝ).det ^ k *
      TauCeti.Probability.nonsingularWishartPDFReal n S A =
      (wishartNormalizer (n+2*k) S / wishartNormalizer n S) *
        TauCeti.Probability.nonsingularWishartPDFReal (n+2*k) S A := by
  have hnk : (p : ℝ) - 1 < n + 2*k := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  by_cases hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [TauCeti.Probability.nonsingularWishartPDFReal_of_posDef _ _ hA,
      TauCeti.Probability.nonsingularWishartPDFReal_of_posDef _ _ hA]
    change _ * (_ * _ / wishartNormalizer n S) = _ * (_ * _ / wishartNormalizer (n+2*k) S)
    have hp : (A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n+2*k-(p:ℝ)-1)/2) =
        (A : Matrix (Fin p) (Fin p) ℝ).det ^ k *
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n-(p:ℝ)-1)/2) := by
      rw [show (n+2*(k:ℝ)-(p:ℝ)-1)/2 = (k:ℝ)+(n-(p:ℝ)-1)/2 by ring,
        Real.rpow_add hA.det_pos, Real.rpow_natCast]
    rw [hp]
    field_simp [(wishart_normalizer_pos hS hn).ne', (wishart_normalizer_pos hS hnk).ne']
  · simp only [TauCeti.Probability.nonsingularWishartPDFReal_of_not_posDef _ _ hA, mul_zero]
/-- Determinant tilting of a valid Wishart law gives a scaled law with shifted degree. -/
theorem with_density_det_pow_nonsingular_wishart_measure {p : ℕ} {n : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (k : ℕ) :
    (TauCeti.Probability.nonsingularWishartMeasure n S).withDensity
      (fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k)) =
      ENNReal.ofReal (wishartNormalizer (n+2*k) S / wishartNormalizer n S) •
        TauCeti.Probability.nonsingularWishartMeasure (n+2*k) S := by
  have hnk : (p : ℝ) - 1 < n+2*k := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [TauCeti.Probability.nonsingularWishartMeasure_of_posDef hS hn,
    TauCeti.Probability.nonsingularWishartMeasure_of_posDef hS hnk,
    ← withDensity_mul _ (TauCeti.Probability.measurable_nonsingularWishartPDF _ _) (by fun_prop),
    ← withDensity_smul _ (TauCeti.Probability.measurable_nonsingularWishartPDF _ _)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro A
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    TauCeti.Probability.nonsingularWishartPDF_def]
  rw [← ENNReal.ofReal_mul (TauCeti.Probability.nonsingularWishartPDFReal_nonneg hS hn A),
    ← ENNReal.ofReal_mul (div_pos (wishart_normalizer_pos hS hnk) (wishart_normalizer_pos hS hn)).le]
  congr 1
  rw [mul_comm, det_pow_mul_wishart_pdf_real hS hn]
end CKSD
