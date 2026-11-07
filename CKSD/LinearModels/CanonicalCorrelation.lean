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

The extremal characterization of the largest canonical correlation, the bound by one, the
invariance theorem, and the Gaussian independence criterion are proved; the last reuses
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

/-- The quadratic form of a block matrix on a block vector. -/
theorem sum_elim_dotProduct_fromBlocks_mulVec (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (a : Fin p → ℝ) (b : Fin q → ℝ) :
    Sum.elim a b ⬝ᵥ (fromBlocks Suu Suv Suvᵀ Svv *ᵥ Sum.elim a b) =
      a ⬝ᵥ (Suu *ᵥ a) + 2 * (a ⬝ᵥ (Suv *ᵥ b)) + b ⬝ᵥ (Svv *ᵥ b) := by
  rw [fromBlocks_mulVec]
  have hcomp₁ : (Sum.elim a b ∘ Sum.inl) = a := rfl
  have hcomp₂ : (Sum.elim a b ∘ Sum.inr) = b := rfl
  rw [hcomp₁, hcomp₂]
  have hsplit : ∀ (u : Fin p → ℝ) (w : Fin q → ℝ) (u' : Fin p → ℝ) (w' : Fin q → ℝ),
      Sum.elim u w ⬝ᵥ Sum.elim u' w' = u ⬝ᵥ u' + w ⬝ᵥ w' := by
    intro u w u' w'
    simp [dotProduct, Fintype.sum_sum_type]
  rw [hsplit, dotProduct_add, dotProduct_add]
  have hT : b ⬝ᵥ (Suvᵀ *ᵥ a) = a ⬝ᵥ (Suv *ᵥ b) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [hT]
  ring

/-- Cauchy–Schwarz for the cross block of a positive semidefinite block matrix. -/
theorem sq_dotProduct_mulVec_le_of_posSemidef_fromBlocks (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hjoint : (fromBlocks Suu Suv Suvᵀ Svv).PosSemidef) (a : Fin p → ℝ) (b : Fin q → ℝ) :
    (a ⬝ᵥ (Suv *ᵥ b)) ^ 2 ≤ (a ⬝ᵥ (Suu *ᵥ a)) * (b ⬝ᵥ (Svv *ᵥ b)) := by
  have h : ∀ t : ℝ, 0 ≤ (a ⬝ᵥ (Suu *ᵥ a)) * (t * t) + 2 * (a ⬝ᵥ (Suv *ᵥ b)) * t +
      b ⬝ᵥ (Svv *ᵥ b) := by
    intro t
    have := hjoint.dotProduct_mulVec_nonneg (Sum.elim (t • a) b)
    rw [star_trivial, sum_elim_dotProduct_fromBlocks_mulVec] at this
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at this
    linarith
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

/-- A whitening identity: `Σ^{-1/2} Σ Σ^{-1/2} = 1`. -/
theorem PosDef.inv_sqrt_mul_mul_inv_sqrt {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ = 1 := by
  have key : ∀ R : Matrix (Fin n) (Fin n) ℝ, IsUnit R.det → R * R = S⁻¹ → R * S * R = 1 := by
    intro R hR hRR
    have hSdet : IsUnit S.det := isUnit_iff_ne_zero.2 hS.det_pos.ne'
    have hS' : S = R⁻¹ * R⁻¹ := by
      rw [← Matrix.mul_inv_rev, hRR, Matrix.nonsing_inv_nonsing_inv _ hSdet]
    rw [hS', Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hR,
      Matrix.mul_nonsing_inv _ hR]
  exact key _ (PosDef.isUnit_det_inv_sqrt hS) (PosDef.inv_sqrt_facts hS).2

/-- The Euclidean norm as the square root of the dot product. -/
theorem norm_euclideanSpace_eq_sqrt_dotProduct {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

/-- Cauchy–Schwarz for the real dot product. -/
theorem sq_dotProduct_le_dotProduct_self_mul {n : ℕ} (x w : Fin n → ℝ) :
    (x ⬝ᵥ w) ^ 2 ≤ (x ⬝ᵥ x) * (w ⬝ᵥ w) := by
  have h : ∀ t : ℝ, 0 ≤ (x ⬝ᵥ x) * (t * t) + 2 * (x ⬝ᵥ w) * t + w ⬝ᵥ w := by
    intro t
    have : 0 ≤ (t • x + w) ⬝ᵥ (t • x + w) := by
      simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg ((t • x + w) i)
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm w x] at this
    linarith
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

/-- The squared L2 operator-norm bound for a real matrix, in dot-product form. -/
theorem dotProduct_mulVec_self_le {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    (K *ᵥ y) ⬝ᵥ (K *ᵥ y) ≤ ‖K‖ ^ 2 * (y ⬝ᵥ y) := by
  have h := K.l2_opNorm_mulVec (WithLp.toLp 2 y)
  rw [norm_euclideanSpace_eq_sqrt_dotProduct, norm_euclideanSpace_eq_sqrt_dotProduct] at h
  simp only [EuclideanSpace.equiv] at h
  have hK : 0 ≤ ‖K‖ := norm_nonneg _
  have hy : 0 ≤ y ⬝ᵥ y := by
    simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (y i)
  calc (K *ᵥ y) ⬝ᵥ (K *ᵥ y) = Real.sqrt ((K *ᵥ y) ⬝ᵥ (K *ᵥ y)) ^ 2 := by
        rw [Real.sq_sqrt]
        simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg ((K *ᵥ y) i)
    _ ≤ (‖K‖ * Real.sqrt (y ⬝ᵥ y)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    _ = ‖K‖ ^ 2 * (y ⬝ᵥ y) := by rw [mul_pow, Real.sq_sqrt hy]

/-- The L2 operator norm of a real matrix with a nonempty column index is attained on a unit
vector. -/
theorem exists_dotProduct_self_eq_one_and_mulVec_eq_norm {m n : ℕ} (hn : 0 < n)
    (K : Matrix (Fin m) (Fin n) ℝ) :
    ∃ y : Fin n → ℝ, y ⬝ᵥ y = 1 ∧ (K *ᵥ y) ⬝ᵥ (K *ᵥ y) = ‖K‖ ^ 2 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun v ↦ (K *ᵥ v.ofLp) ⬝ᵥ (K *ᵥ v.ofLp)
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin n) ↦ K *ᵥ v.ofLp :=
    Continuous.matrix_mulVec continuous_const (PiLp.continuous_ofLp _ _)
  have hf : Continuous f := hc.dotProduct hc
  have hnn : ∀ w : Fin m → ℝ, 0 ≤ w ⬝ᵥ w := fun w ↦ by
    simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)
  obtain ⟨y₀, hy₀S, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hf.continuousOn
  have hy₀ : y₀.ofLp ⬝ᵥ y₀.ofLp = 1 := by
    have h := mem_sphere_zero_iff_norm.1 hy₀S
    rw [norm_euclideanSpace_eq_sqrt_dotProduct, Real.sqrt_eq_one] at h
    exact h
  refine ⟨y₀.ofLp, hy₀, le_antisymm ?_ ?_⟩
  · have := dotProduct_mulVec_self_le K y₀.ofLp
    rwa [hy₀, mul_one] at this
  · have hbound : ‖K‖ ≤ Real.sqrt (f y₀) := by
      rw [l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v ↦ ?_
      change ‖toEuclideanLin K v‖ ≤ _
      rw [norm_euclideanSpace_eq_sqrt_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
      have h : f (‖v‖⁻¹ • v) ≤ f y₀ := hmax hu
      simp only [f, WithLp.ofLp_smul, mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul] at h
      have hfv : (K *ᵥ v.ofLp) ⬝ᵥ (K *ᵥ v.ofLp) ≤ f y₀ * ‖v‖ ^ 2 := by
        have h2 : 0 < ‖v‖ ^ 2 := by positivity
        have : ‖v‖⁻¹ * (‖v‖⁻¹ * ((K *ᵥ v.ofLp) ⬝ᵥ (K *ᵥ v.ofLp))) =
            ((K *ᵥ v.ofLp) ⬝ᵥ (K *ᵥ v.ofLp)) / ‖v‖ ^ 2 := by
          field_simp
        rw [this, div_le_iff₀ h2] at h
        exact h
      calc Real.sqrt ((K *ᵥ v.ofLp) ⬝ᵥ (K *ᵥ v.ofLp)) ≤ Real.sqrt (f y₀ * ‖v‖ ^ 2) :=
            Real.sqrt_le_sqrt hfv
        _ = Real.sqrt (f y₀) * ‖v‖ := by
            rw [Real.sqrt_mul (hnn _), Real.sqrt_sq (norm_nonneg _)]
    have := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rwa [Real.sq_sqrt (hnn _)] at this

/-- Whitening identities for canonical correlations: with `a = Σ_UU^{-1/2} x` and
`b = Σ_VV^{-1/2} y`, the cross form becomes `xᵀ K y` and the variances become `‖x‖²`, `‖y‖²`. -/
theorem canonicalCorrelationMatrix_whitening (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    ((CFC.sqrt Suu)⁻¹ *ᵥ x) ⬝ᵥ (Suv *ᵥ ((CFC.sqrt Svv)⁻¹ *ᵥ y)) =
        x ⬝ᵥ (canonicalCorrelationMatrix Suu Suv Svv *ᵥ y) ∧
      ((CFC.sqrt Suu)⁻¹ *ᵥ x) ⬝ᵥ (Suu *ᵥ ((CFC.sqrt Suu)⁻¹ *ᵥ x)) = x ⬝ᵥ x ∧
      ((CFC.sqrt Svv)⁻¹ *ᵥ y) ⬝ᵥ (Svv *ᵥ ((CFC.sqrt Svv)⁻¹ *ᵥ y)) = y ⬝ᵥ y := by
  obtain ⟨hRt, -⟩ := PosDef.inv_sqrt_facts hUU
  obtain ⟨hTt, -⟩ := PosDef.inv_sqrt_facts hVV
  have hRSR := PosDef.inv_sqrt_mul_mul_inv_sqrt hUU
  have hTST := PosDef.inv_sqrt_mul_mul_inv_sqrt hVV
  set R := (CFC.sqrt Suu)⁻¹
  set T := (CFC.sqrt Svv)⁻¹
  have e2 : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
      (hM : Mᵀ = M) (hMSM : M * S * M = 1) (z : Fin n → ℝ),
      (M *ᵥ z) ⬝ᵥ (S *ᵥ (M *ᵥ z)) = z ⬝ᵥ z := by
    intro n M S hM hMSM z
    rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, hM, vecMul_vecMul,
      ← dotProduct_mulVec, ← Matrix.mul_assoc, hMSM, one_mulVec]
  refine ⟨?_, e2 R Suu hRt hRSR x, e2 T Svv hTt hTST y⟩
  have hxR : x ᵥ* R = R *ᵥ x := by rw [← vecMul_transpose, hRt]
  rw [show canonicalCorrelationMatrix Suu Suv Svv = R * Suv * T from rfl, ← mulVec_mulVec,
    ← mulVec_mulVec, dotProduct_mulVec x R, hxR]

/-- GAPS 105.29: for a positive semidefinite joint covariance with positive definite diagonal
blocks, the canonical correlations lie in `[0, 1]`. -/
theorem norm_canonicalCorrelationMatrix_le_one (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ)
    (hUU : Suu.PosDef) (hVV : Svv.PosDef)
    (hjoint : (Matrix.fromBlocks Suu Suv Suvᵀ Svv).PosSemidef) :
    ‖canonicalCorrelationMatrix Suu Suv Svv‖ ≤ 1 := by
  have hW := canonicalCorrelationMatrix_whitening Suu Suv Svv hUU hVV
  set K := canonicalCorrelationMatrix Suu Suv Svv
  have hnn : ∀ {n : ℕ} (w : Fin n → ℝ), 0 ≤ w ⬝ᵥ w := fun w ↦ by
    simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ ?_
  change ‖toEuclideanLin K y‖ ≤ 1 * ‖y‖
  rw [one_mul, norm_euclideanSpace_eq_sqrt_dotProduct, norm_euclideanSpace_eq_sqrt_dotProduct,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  apply Real.sqrt_le_sqrt
  set w := K *ᵥ y.ofLp
  obtain ⟨h1, h2, h3⟩ := hW w y.ofLp
  have h := sq_dotProduct_mulVec_le_of_posSemidef_fromBlocks Suu Suv Svv hjoint
    ((CFC.sqrt Suu)⁻¹ *ᵥ w) ((CFC.sqrt Svv)⁻¹ *ᵥ y.ofLp)
  rw [h1, h2, h3] at h
  have hw := hnn w
  have hy := hnn y.ofLp
  nlinarith

/-- GAPS 105.29: the largest correlation between linear combinations `aᵀU` and `bᵀV` is the
largest singular value (the L2 operator norm) of `Σ_UU^{-1/2} Σ_UV Σ_VV^{-1/2}`, and it is
attained. The characterization of the subsequent canonical correlations under successive
uncorrelatedness constraints is not stated. -/
theorem isGreatest_linearCombinationCorrelation (Suu : Matrix (Fin p) (Fin p) ℝ)
    (Suv : Matrix (Fin p) (Fin q) ℝ) (Svv : Matrix (Fin q) (Fin q) ℝ) (hp : 0 < p)
    (hq : 0 < q) (hUU : Suu.PosDef) (hVV : Svv.PosDef) :
    IsGreatest {r | ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ r = linearCombinationCorrelation Suu Suv Svv a b}
      ‖canonicalCorrelationMatrix Suu Suv Svv‖ := by
  set K := canonicalCorrelationMatrix Suu Suv Svv
  set R := (CFC.sqrt Suu)⁻¹
  set T := (CFC.sqrt Svv)⁻¹
  have hW := canonicalCorrelationMatrix_whitening Suu Suv Svv hUU hVV
  have hnn : ∀ {n : ℕ} (w : Fin n → ℝ), 0 ≤ w ⬝ᵥ w := fun w ↦ by
    simpa [dotProduct] using Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy1, hyK⟩ := exists_dotProduct_self_eq_one_and_mulVec_eq_norm hq K
    rcases eq_or_lt_of_le (norm_nonneg K) with hc | hc
    · have hK : K = 0 := norm_eq_zero.1 hc.symm
      have hSuv : Suv = 0 := (canonicalCorrelationMatrix_eq_zero_iff _ _ _ hUU hVV).1 hK
      refine ⟨Pi.single ⟨0, hp⟩ 1, Pi.single ⟨0, hq⟩ 1, by simp, by simp, ?_⟩
      rw [← hc]
      simp [linearCombinationCorrelation, hSuv]
    · set c := ‖K‖
      let x : Fin p → ℝ := c⁻¹ • (K *ᵥ y)
      obtain ⟨h1, h2, h3⟩ := hW x y
      have hxK : x ⬝ᵥ (K *ᵥ y) = c := by
        simp only [x, smul_dotProduct, hyK, smul_eq_mul]
        field_simp
      have hxx : x ⬝ᵥ x = 1 := by
        simp only [x, smul_dotProduct, dotProduct_smul, hyK, smul_eq_mul]
        field_simp
      refine ⟨R *ᵥ x, T *ᵥ y, ?_, ?_, ?_⟩
      · intro h0
        rw [h0, hxx] at h2
        simp at h2
      · intro h0
        rw [h0, hy1] at h3
        simp at h3
      · rw [linearCombinationCorrelation, h1, h2, h3, hxK, hxx, hy1]
        simp
  · rintro r ⟨a, b, ha, hb, rfl⟩
    have hR := PosDef.isUnit_det_inv_sqrt hUU
    have hT := PosDef.isUnit_det_inv_sqrt hVV
    obtain ⟨x, rfl⟩ : ∃ x, R *ᵥ x = a :=
      ⟨R⁻¹ *ᵥ a, by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hR, one_mulVec]⟩
    obtain ⟨y, rfl⟩ : ∃ y, T *ᵥ y = b :=
      ⟨T⁻¹ *ᵥ b, by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, one_mulVec]⟩
    obtain ⟨h1, h2, h3⟩ := hW x y
    rw [linearCombinationCorrelation, h1, h2, h3]
    set c := ‖K‖
    have hc : 0 ≤ c := norm_nonneg _
    have hsq : (x ⬝ᵥ (K *ᵥ y)) ^ 2 ≤ c ^ 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
      have := sq_dotProduct_le_dotProduct_self_mul x (K *ᵥ y)
      have := dotProduct_mulVec_self_le K y
      have := hnn x
      nlinarith
    rcases eq_or_lt_of_le (mul_nonneg (hnn x) (hnn y)) with h0 | h0
    · rw [← h0]; simpa using hc
    · rw [div_le_iff₀ (Real.sqrt_pos.2 h0)]
      calc x ⬝ᵥ (K *ᵥ y) ≤ |x ⬝ᵥ (K *ᵥ y)| := le_abs_self _
        _ = Real.sqrt ((x ⬝ᵥ (K *ᵥ y)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (c ^ 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y))) := Real.sqrt_le_sqrt hsq
        _ = c * Real.sqrt ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
          rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

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
