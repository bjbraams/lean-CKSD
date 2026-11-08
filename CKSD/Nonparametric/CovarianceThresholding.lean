module

public import CKSD.Nonparametric.Basic

/-!
# Deterministic covariance thresholding bounds

A symmetric Schur estimate controls the Euclidean operator norm by absolute row sums. It gives
the sparse-row error bound for hard covariance thresholding. Source: GAPS 103.52.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Schur test for a symmetric matrix: the Euclidean operator norm is at most any bound on
the absolute row sums. -/
theorem norm_toEuclideanCLM_le_of_rowSum_le {p : ℕ} (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : D.IsSymm) (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, |D i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D‖ ≤ R := by
  have hsymm : ∀ i j, D i j = D j i := fun i j ↦ by
    simpa using congrFun (congrFun hD.eq j) i
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun x ↦ ?_
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D x‖ ^ 2 ≤ (R * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
    calc ∑ i, (∑ j, D i j * x j) ^ 2
        ≤ ∑ i, (∑ j, |D i j|) * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ ↦ abs_nonneg _)
            (fun j _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun j _ ↦ ?_)
          rw [mul_pow, ← mul_assoc, ← sq, sq_abs]
      _ ≤ ∑ i, R * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          exact hrow i
      _ = R * ∑ j, x j ^ 2 * ∑ i, |D j i| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hsymm i j]; ring
      _ ≤ R * ∑ j, x j ^ 2 * R := by
          gcongr with j
          exact hrow j
      _ = R ^ 2 * ∑ j, x j ^ 2 := by rw [← Finset.sum_mul]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- GAPS 103.52, deterministic sparse-row bound for hard covariance thresholding. -/
theorem norm_thresholded_covariance_sub_le {p : ℕ} (Sigma S : Matrix (Fin p) (Fin p) ℝ)
    (hSigma : Sigma.IsSymm) (hS : S.IsSymm) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (herr : ∀ i j, |S i j - Sigma i j| ≤ lambda) (s : ℕ)
    (hs : ∀ i, (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card ≤ s) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma)‖ ≤ 2 * s * lambda := by
  classical
  set D := Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma with hDdef
  have hSs : ∀ i j, S i j = S j i := fun i j ↦ by simpa using congrFun (congrFun hS.eq j) i
  have hSigs : ∀ i j, Sigma i j = Sigma j i := fun i j ↦ by
    simpa using congrFun (congrFun hSigma.eq j) i
  have hDsymm : D.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hDdef, Matrix.sub_apply, Matrix.of_apply, hSs i j,
      hSigs i j]
  have hentry : ∀ i j, |D i j| ≤ if Sigma i j ≠ 0 then 2 * lambda else 0 := by
    intro i j
    have he := herr i j
    simp only [hDdef, Matrix.sub_apply, Matrix.of_apply]
    by_cases hz : Sigma i j = 0
    · have : ¬ lambda < |S i j| := by rw [hz, sub_zero] at he; exact not_lt.mpr he
      simp [hz, this]
    · simp only [ne_eq, hz, not_false_eq_true, ite_true]
      split_ifs with ht
      · linarith
      · rw [zero_sub, abs_neg]
        have h1 := abs_sub_abs_le_abs_sub (Sigma i j) (S i j)
        rw [abs_sub_comm] at h1
        linarith [not_lt.mp ht]
  refine norm_toEuclideanCLM_le_of_rowSum_le D hDsymm _ (by positivity) fun i ↦ ?_
  calc ∑ j, |D i j| ≤ ∑ j, (if Sigma i j ≠ 0 then 2 * lambda else 0) :=
        Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card * (2 * lambda) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ s * (2 * lambda) := by gcongr; exact_mod_cast hs i
    _ = 2 * s * lambda := by ring

end CKSD
