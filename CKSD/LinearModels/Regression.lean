module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# LinearModels: Regression

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

/-- With uncorrelated coordinates of common variance `v`, the variance of `⟪b, Y⟫` is
`v ‖b‖²`. -/
theorem variance_inner_of_covariance_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (b : EuclideanSpace ℝ (Fin n)) :
    variance μ (fun ω ↦ inner ℝ b (Y ω)) = v * ‖b‖ ^ 2 := by
  have hYi : ∀ i, MemLp (fun ω ↦ Y ω i) 2 μ := fun i ↦
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hY
  have hbY : ∀ i, MemLp (fun ω ↦ b i * Y ω i) 2 μ := fun i ↦ (hYi i).const_mul (b i)
  have hinner : (fun ω ↦ inner ℝ b (Y ω)) = fun ω ↦ ∑ i, b i * Y ω i := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have hmeas : AEMeasurable (fun ω ↦ inner ℝ b (Y ω)) μ := by
    exact (aestronglyMeasurable_const.inner hY.aestronglyMeasurable).aemeasurable
  have hvar : variance μ (fun ω ↦ inner ℝ b (Y ω)) =
      ProbabilityTheory.variance (fun ω ↦ inner ℝ b (Y ω)) μ :=
    (ProbabilityTheory.variance_eq_integral hmeas).symm
  rw [hvar, ← covariance_self hmeas, hinner,
    covariance_fun_sum_fun_sum hbY hbY]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  have := hcov
  simp only [covariance] at this
  simp_rw [this, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- GAPS 105.1, scalar Gauss–Markov comparison by projecting an unbiased coefficient. -/
theorem variance_projection_le_of_unbiased {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ) (hv : 0 ≤ v)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hm : P (∫ ω, Y ω ∂μ) = ∫ ω, Y ω ∂μ) (a : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (P a) (Y ω) ∂μ) = ∫ ω, inner ℝ a (Y ω) ∂μ ∧
      variance μ (fun ω ↦ inner ℝ (P a) (Y ω)) ≤
        variance μ (fun ω ↦ inner ℝ a (Y ω)) := by
  have hint : Integrable Y μ := hY.integrable one_le_two
  refine ⟨?_, ?_⟩
  · rw [integral_inner hint, integral_inner hint, hPsym, hm]
  · rw [variance_inner_of_covariance_eq μ Y hY v hcov, variance_inner_of_covariance_eq μ Y hY v hcov]
    refine mul_le_mul_of_nonneg_left ?_ hv
    have horth : inner ℝ (P a) (a - P a) = 0 := by
      rw [inner_sub_right, hPsym a (P a), hPid, real_inner_comm, sub_self]
    have : ‖a‖ ^ 2 = ‖P a‖ ^ 2 + ‖a - P a‖ ^ 2 := by
      have h := norm_add_sq_real (P a) (a - P a)
      rw [horth, mul_zero, add_zero, add_sub_cancel] at h
      exact h
    rw [this]
    nlinarith [sq_nonneg ‖a - P a‖]

/-- GAPS 105.2, residual chi-squared law and projection independence. -/
theorem gaussian_projection_residual_law_and_indepFun
    {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (hm : P m = m) :
    let r := Module.finrank ℝ (LinearMap.range P.toLinearMap);
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ ‖x - P x‖ ^ 2 / v) = TauCeti.Probability.chiSquaredMeasure (n - r : ℕ) ∧
      IndepFun P (fun x ↦ ‖x - P x‖ ^ 2) G := by
  sorry

/-- GAPS 105.10, exact null F law for nested Gaussian projection models. -/
theorem nested_gaussian_projection_fisher_law
    {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hid : ∀ x, P₀ (P₀ x) = P₀ x ∧ P₁ (P₁ x) = P₁ x)
    (hsym : ∀ x y, inner ℝ (P₀ x) y = inner ℝ x (P₀ y) ∧
      inner ℝ (P₁ x) y = inner ℝ x (P₁ y))
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x) (hm : P₀ m = m) :
    let r₀ := Module.finrank ℝ (LinearMap.range P₀.toLinearMap);
    let r₁ := Module.finrank ℝ (LinearMap.range P₁.toLinearMap);
    ∀ (hr : r₀ < r₁),
    ∀ (hrn : r₁ < n),
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ (‖P₁ x - P₀ x‖ ^ 2 / (r₁ - r₀ : ℕ)) /
      (‖x - P₁ x‖ ^ 2 / (n - r₁ : ℕ))) =
      TauCeti.Probability.fisherSnedecorMeasure (r₁ - r₀ : ℕ) (n - r₁ : ℕ) := by
  sorry

/-- GAPS 105.15, Craig–Sakamoto criterion for centered quadratic forms. -/
theorem indepFun_matrixQuadraticForm_iff {n : ℕ} (Sigma A B : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm) :
    IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B)
      (multivariateGaussian 0 Sigma) ↔ A * Sigma * B = 0 := by
  sorry


end CKSD
