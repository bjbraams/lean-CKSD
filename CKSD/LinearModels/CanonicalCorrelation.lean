module

public import CKSD.LinearModels.Basic
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Probability.Distributions.Gaussian.Independence

/-!
# Canonical correlations

For centred random vectors `U ∈ ℝ^p` and `V ∈ ℝ^q` with covariance blocks `Σ_UU`, `Σ_UV`,
`Σ_VV`, the canonical correlations are the singular values of
`Σ_UU^{-1/2} Σ_UV Σ_VV^{-1/2}`; the largest one is its L2 operator norm. Matrix square roots
are Mathlib's continuous functional calculus `CFC.sqrt`. The squared canonical correlations are
the roots of the characteristic polynomial of `M Mᵀ` for this matrix `M`.

The invariance theorem and the Gaussian independence criterion are proved; the latter reuses
TauCeti's criterion `indepFun_matrix_multivariateGaussian_iff` for independence of linear
images of a Gaussian vector. Source: GAPS 105.29.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Matrix
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

variable {p q : ℕ}

/-- The correlation of `aᵀU` and `bᵀV` for covariance blocks `Suu`, `Suv`, `Svv`. -/
def linearCombinationCorrelation (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (a : Fin p → ℝ) (b : Fin q → ℝ) : ℝ :=
  a ⬝ᵥ (Suv *ᵥ b) / Real.sqrt ((a ⬝ᵥ (Suu *ᵥ a)) * (b ⬝ᵥ (Svv *ᵥ b)))

/-- The whitened cross-covariance `Σ_UU^{-1/2} Σ_UV Σ_VV^{-1/2}`, whose singular values are the
canonical correlations. -/
def canonicalCorrelationMatrix (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin p) (Fin q) ℝ :=
  (CFC.sqrt Suu)⁻¹ * Suv * (CFC.sqrt Svv)⁻¹

/-- GAPS 105.29: the largest correlation between linear combinations `aᵀU` and `bᵀV` is the
largest singular value (the L2 operator norm) of `Σ_UU^{-1/2} Σ_UV Σ_VV^{-1/2}`, and it is
attained. The characterization of the subsequent canonical correlations under successive
uncorrelatedness constraints is not stated. -/
theorem isGreatest_linearCombinationCorrelation (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ) (hp : 0 < p)
    (hq : 0 < q) (hUU : Suu.PosDef) (hVV : Svv.PosDef) :
    IsGreatest {r | ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ r = linearCombinationCorrelation Suu Suv Svv a b}
      ‖canonicalCorrelationMatrix Suu Suv Svv‖ := by
  sorry

/-- GAPS 105.29: for a positive semidefinite joint covariance with positive definite diagonal
blocks, the canonical correlations lie in `[0, 1]`. -/
theorem norm_canonicalCorrelationMatrix_le_one (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef)
    (hjoint : (Matrix.fromBlocks Suu Suv Suvᵀ Svv).PosSemidef) :
    ‖canonicalCorrelationMatrix Suu Suv Svv‖ ≤ 1 := by
  sorry


/-- A real positive semidefinite matrix has a symmetric inverse square root whose square is the
inverse. -/
theorem PosDef.inv_sqrt_facts {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    ((CFC.sqrt S)⁻¹)ᵀ = (CFC.sqrt S)⁻¹ ∧ (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by
  rw [hS.posSemidef.inv_sqrt]
  have hnn : 0 ≤ S⁻¹ := hS.inv.posSemidef.nonneg
  refine ⟨?_, CFC.sqrt_mul_sqrt_self _ hnn⟩
  have h := (CFC.sqrt_nonneg S⁻¹).posSemidef.isHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- The squared canonical correlations are the roots of the characteristic polynomial of
`Σ_UU⁻¹ Σ_UV Σ_VV⁻¹ Σ_VU`. -/
theorem charpoly_canonicalCorrelationMatrix_mul_transpose (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef) :
    (canonicalCorrelationMatrix Suu Suv Svv * (canonicalCorrelationMatrix Suu Suv Svv)ᵀ).charpoly =
      (Suu⁻¹ * Suv * Svv⁻¹ * Suvᵀ).charpoly := by
  obtain ⟨hR, hRR⟩ := PosDef.inv_sqrt_facts hUU
  obtain ⟨hT, hTT⟩ := PosDef.inv_sqrt_facts hVV
  have hM : canonicalCorrelationMatrix Suu Suv Svv * (canonicalCorrelationMatrix Suu Suv Svv)ᵀ =
      (CFC.sqrt Suu)⁻¹ * ((Suv * Svv⁻¹ * Suvᵀ) * (CFC.sqrt Suu)⁻¹) := by
    simp only [canonicalCorrelationMatrix, Matrix.transpose_mul, hR, hT, ← hTT, Matrix.mul_assoc]
  rw [hM, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hRR, Matrix.charpoly_mul_comm]
  simp only [Matrix.mul_assoc]

/-- GAPS 105.29: canonical correlations are unchanged by nonsingular linear transformations
`U ↦ P U` and `V ↦ Q V`; the characteristic polynomial of `M Mᵀ`, whose roots are the squared
canonical correlations, is invariant. -/
theorem charpoly_canonicalCorrelationMatrix_transform (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef) (P : Matrix (Fin p) (Fin p) ℝ)
    (Q : Matrix (Fin q) (Fin q) ℝ) (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    let M' := canonicalCorrelationMatrix (P * Suu * Pᵀ) (P * Suv * Qᵀ) (Q * Svv * Qᵀ)
    let M := canonicalCorrelationMatrix Suu Suv Svv
    (M' * M'ᵀ).charpoly = (M * Mᵀ).charpoly := by
  intro M' M
  have hcong : ∀ {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ},
      S.PosDef → IsUnit R.det → (R * S * Rᵀ).PosDef := by
    intro n S R hS hR
    have hinj : Function.Injective R.vecMul :=
      Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det R).2 hR)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same hinj
  have hPT : IsUnit Pᵀ.det := Matrix.isUnit_det_transpose P hP
  have hQT : IsUnit Qᵀ.det := Matrix.isUnit_det_transpose Q hQ
  simp only [M', M]
  rw [charpoly_canonicalCorrelationMatrix_mul_transpose _ _ _ (hcong hUU hP) (hcong hVV hQ),
    charpoly_canonicalCorrelationMatrix_mul_transpose _ _ _ hUU hVV]
  have hK : (P * Suu * Pᵀ)⁻¹ * (P * Suv * Qᵀ) * (Q * Svv * Qᵀ)⁻¹ * (P * Suv * Qᵀ)ᵀ =
      Pᵀ⁻¹ * (Suu⁻¹ * Suv * Svv⁻¹ * Suvᵀ * Pᵀ) := by
    simp only [Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.mul_nonsing_inv_cancel_left _ _ hQT,
      Matrix.nonsing_inv_mul_cancel_left _ _ hQ]
  rw [hK, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPT,
    Matrix.mul_one]

/-- The inverse square root of a real positive definite matrix is invertible. -/
theorem PosDef.isUnit_det_inv_sqrt {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    IsUnit ((CFC.sqrt S)⁻¹).det := by
  have h := congrArg Matrix.det (PosDef.inv_sqrt_facts hS).2
  rw [Matrix.det_mul] at h
  have hpos : 0 < S⁻¹.det := hS.inv.det_pos
  refine isUnit_iff_ne_zero.2 fun h0 ↦ ?_
  rw [h0, zero_mul] at h
  exact hpos.ne' h.symm

/-- The whitened cross-covariance vanishes exactly when the cross-covariance does. -/
theorem canonicalCorrelationMatrix_eq_zero_iff (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef) :
    canonicalCorrelationMatrix Suu Suv Svv = 0 ↔ Suv = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [canonicalCorrelationMatrix, h]⟩
  have hR := PosDef.isUnit_det_inv_sqrt hUU
  have hT := PosDef.isUnit_det_inv_sqrt hVV
  unfold canonicalCorrelationMatrix at h
  have h₁ : Suv * (CFC.sqrt Svv)⁻¹ = 0 := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ (Suv * (CFC.sqrt Svv)⁻¹) hR,
      ← Matrix.mul_assoc (CFC.sqrt Suu)⁻¹, h, Matrix.mul_zero]
  rw [← Matrix.mul_nonsing_inv_cancel_right _ Suv hT, h₁, Matrix.zero_mul]

/-- Selection of the first `p` coordinates of `ℝ^{p+q}`. -/
def firstBlockSelection (p q : ℕ) : Matrix (Fin p) (Fin (p + q)) ℝ :=
  Matrix.of fun i k ↦ if k = Fin.castAdd q i then 1 else 0

/-- Selection of the last `q` coordinates of `ℝ^{p+q}`. -/
def secondBlockSelection (p q : ℕ) : Matrix (Fin q) (Fin (p + q)) ℝ :=
  Matrix.of fun j k ↦ if k = Fin.natAdd p j then 1 else 0

/-- GAPS 105.29: for a jointly Gaussian pair `(U, V)` with positive definite marginal
covariances, `U` and `V` are independent exactly when all canonical correlations vanish. -/
theorem indepFun_gaussian_blocks_iff_canonicalCorrelationMatrix_eq_zero
    (m : EuclideanSpace ℝ (Fin (p + q))) (S : Matrix (Fin (p + q)) (Fin (p + q)) ℝ)
    (hS : S.PosSemidef) (hUU : (S.submatrix (Fin.castAdd q) (Fin.castAdd q)).PosDef)
    (hVV : (S.submatrix (Fin.natAdd p) (Fin.natAdd p)).PosDef) :
    IndepFun (fun x ↦ (firstBlockSelection p q).toEuclideanLin x)
        (fun x ↦ (secondBlockSelection p q).toEuclideanLin x) (multivariateGaussian m S) ↔
      canonicalCorrelationMatrix (S.submatrix (Fin.castAdd q) (Fin.castAdd q))
        (S.submatrix (Fin.castAdd q) (Fin.natAdd p))
        (S.submatrix (Fin.natAdd p) (Fin.natAdd p)) = 0 := by
  rw [TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff m hS,
    canonicalCorrelationMatrix_eq_zero_iff _ _ _ hUU hVV]
  have hcross : firstBlockSelection p q * S * (secondBlockSelection p q)ᵀ =
      S.submatrix (Fin.castAdd q) (Fin.natAdd p) := by
    ext i j
    simp [firstBlockSelection, secondBlockSelection, Matrix.mul_apply]
  rw [hcross]

end CKSD
