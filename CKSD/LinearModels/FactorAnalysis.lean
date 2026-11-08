module

public import CKSD.LinearModels.MultivariateTests
public import Mathlib.Order.Hom.Set
public import TauCeti.Analysis.Matrix.GramFactorization.Uniqueness

/-!
# Orthogonal factor models

The orthogonal factor model `X = μ + L F + ε` with `m` common factors has covariance
`Σ = L Lᵀ + Ψ`, where `L` is the `p × m` loading matrix and `Ψ = diag ψ` the diagonal matrix of
unique variances. The loadings are determined by `Σ` only up to an orthogonal rotation; under
the normalization that `Lᵀ Ψ⁻¹ L` is diagonal with distinct positive decreasing entries they
are determined up to the signs of the columns.

## Main definitions

* `CKSD.factorCovariance`: the implied covariance `L Lᵀ + diag ψ`.
* `CKSD.factorLikelihoodCriterion`: the Gaussian criterion `log det Σ + tr(C Σ⁻¹)`.
* `CKSD.IsNormalizedFactorLoading`: `Lᵀ Ψ⁻¹ L` is diagonal with distinct positive decreasing
  entries.
* `CKSD.factorColumnSigns`, `CKSD.loadingSignDistance`: sign changes of the factor columns and
  the operator-norm distance of two loading matrices modulo such sign changes.

## Main results

* `CKSD.factorCovariance_mul_orthogonal`: rotating the factors does not change the covariance.
* `CKSD.IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns`: normalized loadings with the
  same common covariance agree up to column signs. The proof uses TauCeti's uniqueness of Gram
  factors and Mathlib's uniqueness of order embeddings with equal ranges.
* `CKSD.tendstoInProbabilityConst_factor_mle_of_compact`: consistency of the Gaussian
  maximum-likelihood estimator on a compact identified parameter set.

The identification result concerns the normalized-loading regime with known unique variances; it
does not assert identifiability of the decomposition of `Σ` into its common and unique parts.
Sources: GAPS 105.35 and SYNOPSIS105, item 35.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 14.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Covariance `L Lᵀ + diag ψ` of an orthogonal factor model with loadings `L` and unique
variances `ψ`. -/
def factorCovariance {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ := L * L.transpose + Matrix.diagonal psi

/-- The Gaussian covariance criterion `log det Σ + tr(C Σ⁻¹)` at `Σ = L Lᵀ + diag ψ`, for a sample
covariance `C`; it is the negative log-likelihood up to a constant and the factor `n / 2`. -/
def factorLikelihoodCriterion {p m : ℕ} (C : Matrix (Fin p) (Fin p) ℝ)
    (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) : ℝ :=
  Real.log (factorCovariance L psi).det + Matrix.trace (C * (factorCovariance L psi)⁻¹)

/-- Normalized loadings: `Lᵀ (diag ψ)⁻¹ L` is a diagonal matrix with distinct positive entries in
decreasing order. -/
def IsNormalizedFactorLoading {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (psi : Fin p → ℝ) : Prop :=
  ∃ a : Fin m → ℝ, StrictAnti a ∧ (∀ i, 0 < a i) ∧
    L.transpose * (Matrix.diagonal psi)⁻¹ * L = Matrix.diagonal a

/-- The diagonal sign matrix changing the signs of the factor columns `j` with `s j = false`. -/
def factorColumnSigns {m : ℕ} (s : Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun j ↦ if s j then (1 : ℝ) else -1)

/-- Distance between two loading matrices modulo factor-column signs: the least operator norm of
`L S - M` over the sign matrices `S`. -/
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

/-- GAPS 105.35: normalized loadings are identified up to column signs once both their common
covariance `L Lᵀ` and the diagonal unique covariance `diag ψ` are specified: if `L` and `M` are
normalized for `ψ` and `L Lᵀ = M Mᵀ`, then `M = L S` for a diagonal sign matrix `S`. -/
theorem IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns {p m : ℕ}
    {L M : Matrix (Fin p) (Fin m) ℝ} {psi : Fin p → ℝ}
    (hL : IsNormalizedFactorLoading L psi) (hM : IsNormalizedFactorLoading M psi)
    (hcov : L * L.transpose = M * M.transpose) :
    ∃ s : Fin m → Bool, M = L * factorColumnSigns s := by
  classical
  obtain ⟨a, ha, _, hLa⟩ := hL
  obtain ⟨b, hb, _, hMb⟩ := hM
  have hgram : L.transpose.conjTranspose * L.transpose = M.transpose.conjTranspose * M.transpose := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hcov
  obtain ⟨U, hU⟩ := TauCeti.conjTranspose_mul_self_eq_iff_exists_unitary_mul.mp hgram
  let Q : Matrix (Fin m) (Fin m) ℝ := (U : Matrix (Fin m) (Fin m) ℝ).transpose
  have hMQ : M = L * Q := by
    have ht := congrArg Matrix.transpose hU
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using ht
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff'.mp U.property)
  have hQQ' : Q.transpose * Q = 1 := by
    simpa only [Q, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp U.property)
  have hab : Matrix.diagonal a * Q = Q * Matrix.diagonal b := by
    calc
      Matrix.diagonal a * Q = Q * (Q.transpose * Matrix.diagonal a * Q) := by
        simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      _ = Q * Matrix.diagonal b := by
        rw [← hLa, ← hMb, hMQ, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
  have hentry : ∀ i j, Q i j ≠ 0 → a i = b j := by
    intro i j hq
    have he := congrArg (fun A ↦ A i j) hab
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    exact (mul_right_cancel₀ hq (he.trans (mul_comm _ _)))
  have hrow : ∀ i, ∃ j, Q i j ≠ 0 := by
    intro i
    by_contra! h
    have he := congrArg (fun A ↦ A i i) hQQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, h, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at he
    exact zero_ne_one he
  have hcol : ∀ j, ∃ i, Q i j ≠ 0 := by
    intro j
    by_contra! h
    have he := congrArg (fun A ↦ A j j) hQQ'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, h, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at he
    exact zero_ne_one he
  have hrange : Set.range a = Set.range b := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hrow i
      exact ⟨j, (hentry i j hj).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hcol j
      exact ⟨i, hentry i j hi⟩
  have heq : a = b := ha.dual_right.eq_of_range_eq hb.dual_right hrange
  have hoff : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    by_contra hq
    exact hij (ha.injective ((hentry i j hq).trans (congrFun heq j).symm))
  have hdiag : Q = Matrix.diagonal (fun i ↦ Q i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij, hoff i j hij]
  have hsign : ∀ i, Q i i = 1 ∨ Q i i = -1 := by
    intro i
    have he := congrArg (fun A ↦ A i i) hQQ
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at he
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at he
    rcases mul_self_eq_one_iff.mp he with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨fun i ↦ decide (Q i i = 1), hMQ.trans ?_⟩
  congr 1
  rw [hdiag]
  apply congrArg Matrix.diagonal
  funext i
  rcases hsign i with h | h <;> simp [h]

/-- GAPS 105.35: consistency of factor maximum likelihood on a compact identified parameter set:
if the sample covariances `Cₙ` converge in probability to `Σ₀ = L₀ L₀ᵀ + diag ψ₀`, the parameter
`(L₀, ψ₀)` lies in a compact set `K` on which the unique variances are bounded below by `a > 0`
and on which `Σ₀` determines `ψ₀` and `L₀` up to column signs, then every minimizer `Tₙ` of the
criterion over `K` has `ψ̂ₙ → ψ₀` and `L̂ₙ → L₀` modulo column signs, in probability.
Compactness and the uniform lower bound on the unique variances are restrictions of this
formulation; the unrestricted parameter space and asymptotic normality are not included. -/
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
