module

public import CKSD.Learning.Algorithms
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.L2

/-!
# Kernel ridge regression and compact-support clustering

The ridge model is represented by a finite feature matrix, hence a positive semidefinite Gram
matrix. Its normalization matches the objective with squared-error coefficient `1/(2n)`.
The clustering statement uses a compact set containing both observations and centers and asks
for uniqueness only of the center set; different orderings are identified by Hausdorff distance.
Matrices, Gaussian laws, and Hausdorff distance are Mathlib APIs.

## Main definitions

* `CKSD.ridgeSmoother`, `CKSD.ridgePrediction`: fixed-design ridge regression.
* `CKSD.HasKernelCriticalRadius`: the empirical kernel critical-radius inequality.
* `CKSD.kmeansSampleRisk`: the empirical `k`-means distortion.

## Main results

* `CKSD.ridgePrediction_oracle_bounds`: kernel-ridge oracle bounds (GAPS 107.13).
* `CKSD.ae_tendsto_kmeans_centers_of_compact`: consistency of empirical `k`-means
  (GAPS 107.16).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Fixed-design ridge smoother for the objective `‖y - Aβ‖²/(2n) + λ‖β‖²`. -/
def ridgeSmoother {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (lambda : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A * (A.transpose * A + (2 * (n : ℝ) * lambda) • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ *
    A.transpose

/-- Predicted values of a fixed-design ridge fit. -/
def ridgePrediction {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ) (lambda : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lambda) y

/-- Empirical kernel critical-radius inequality in terms of normalized Gram eigenvalues. -/
def HasKernelCriticalRadius {n : ℕ} (eigenvalues : Fin n → ℝ) (R sigma delta : ℝ) : Prop :=
  Real.sqrt ((2 / (n : ℝ)) * ∑ j, min (delta ^ 2) (eigenvalues j)) ≤
    R * delta ^ 2 / (4 * sigma)

section RidgeOracle

open Matrix TauCeti.Probability
open scoped RealInnerProductSpace

variable {n p : ℕ}

/-- The regularized Gram matrix `Aᵀ A + c I` is positive definite for `0 < c`. -/
private theorem posDef_transpose_mul_add (A : Matrix (Fin n) (Fin p) ℝ) {c : ℝ} (hc : 0 < c) :
    (Aᵀ * A + c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
  have h1 := Matrix.posSemidef_conjTranspose_mul_self A
  rw [conjTranspose_eq_transpose_of_trivial] at h1
  exact PosDef.posSemidef_add h1 (PosDef.one.smul hc)

/-- The regularized Gram matrix `A Aᵀ + c I` is positive definite for `0 < c`. -/
private theorem posDef_mul_transpose_add (A : Matrix (Fin n) (Fin p) ℝ) {c : ℝ} (hc : 0 < c) :
    (A * Aᵀ + c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have h1 := Matrix.posSemidef_self_mul_conjTranspose A
  rw [conjTranspose_eq_transpose_of_trivial] at h1
  exact PosDef.posSemidef_add h1 (PosDef.one.smul hc)

/-- Push-through form of the ridge smoother. -/
private theorem ridgeSmoother_eq (A : Matrix (Fin n) (Fin p) ℝ) {lam : ℝ}
    (hc : 0 < 2 * (n : ℝ) * lam) :
    ridgeSmoother A lam =
      A * Aᵀ * (A * Aᵀ + (2 * (n : ℝ) * lam) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ := by
  set c := 2 * (n : ℝ) * lam
  have hM := (isUnit_iff_isUnit_det _).mp (posDef_transpose_mul_add A hc).isUnit
  have hN := (isUnit_iff_isUnit_det _).mp (posDef_mul_transpose_add A hc).isUnit
  have h : Aᵀ * (A * Aᵀ + c • 1) = (Aᵀ * A + c • 1) * Aᵀ := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have key : (Aᵀ * A + c • 1)⁻¹ * Aᵀ = Aᵀ * (A * Aᵀ + c • 1)⁻¹ := by
    calc (Aᵀ * A + c • 1)⁻¹ * Aᵀ
        = (Aᵀ * A + c • 1)⁻¹ * (Aᵀ * (A * Aᵀ + c • 1)) * (A * Aᵀ + c • 1)⁻¹ := by
          rw [Matrix.mul_assoc _ (Aᵀ * _), Matrix.mul_assoc Aᵀ, Matrix.mul_nonsing_inv _ hN,
            Matrix.mul_one]
      _ = Aᵀ * (A * Aᵀ + c • 1)⁻¹ := by
          rw [h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  unfold ridgeSmoother
  rw [Matrix.mul_assoc A, key, ← Matrix.mul_assoc]

/-- Coordinates of a matrix acting on Euclidean space. -/
private theorem toEuclideanLin_ofLp {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    (Matrix.toEuclideanLin (𝕜 := ℝ) M v).ofLp = M *ᵥ v.ofLp := by
  simp [Matrix.toLpLin_apply]

/-- The squared Euclidean norm is the dot product of the coordinate vector with itself. -/
private theorem norm_sq_eq_dotProduct {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

/-- An eigenvector of the normalized Gram matrix `A Aᵀ / n` with eigenvalue `μ` has `0 ≤ μ` and
is an eigenvector of the ridge smoother with eigenvalue `μ / (μ + 2λ)`. -/
private theorem ridgeSmoother_eigen (A : Matrix (Fin n) (Fin p) ℝ) {lam : ℝ} (hn : 0 < n)
    (hlam : 0 < lam) {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) {μ : ℝ}
    (h : Matrix.toEuclideanLin (𝕜 := ℝ) (((n : ℝ)⁻¹) • (A * A.transpose)) v = μ • v) :
    0 ≤ μ ∧
      Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lam) v = (μ / (μ + 2 * lam)) • v := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < 2 * (n : ℝ) * lam := by positivity
  set w := v.ofLp with hw
  have hAA : (A * Aᵀ) *ᵥ w = ((n : ℝ) * μ) • w := by
    have h' := congrArg WithLp.ofLp h
    rw [toEuclideanLin_ofLp, Matrix.smul_mulVec, WithLp.ofLp_smul] at h'
    calc (A * Aᵀ) *ᵥ w = (n : ℝ) • ((n : ℝ)⁻¹ • ((A * Aᵀ) *ᵥ w)) := by
          rw [smul_smul, mul_inv_cancel₀ hn'.ne', one_smul]
      _ = _ := by rw [h', smul_smul]
  have hww : w ⬝ᵥ w = 1 := by rw [← norm_sq_eq_dotProduct, hv, one_pow]
  have hμ : 0 ≤ μ := by
    have h1 : w ⬝ᵥ ((A * Aᵀ) *ᵥ w) = (Aᵀ *ᵥ w) ⬝ᵥ (Aᵀ *ᵥ w) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have h2 : 0 ≤ (Aᵀ *ᵥ w) ⬝ᵥ (Aᵀ *ᵥ w) := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    rw [← h1, hAA, dotProduct_smul, hww, smul_eq_mul, mul_one] at h2
    exact nonneg_of_mul_nonneg_right (by linarith) hn'
  refine ⟨hμ, ?_⟩
  set c := 2 * (n : ℝ) * lam with hcdef
  set N := A * Aᵀ + c • (1 : Matrix (Fin n) (Fin n) ℝ) with hNdef
  have hN := (isUnit_iff_isUnit_det _).mp (posDef_mul_transpose_add A hc).isUnit
  have hpos : 0 < (n : ℝ) * μ + c := by positivity
  have hNw : N *ᵥ w = ((n : ℝ) * μ + c) • w := by
    rw [hNdef, Matrix.add_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul]
  have hNinv : N⁻¹ *ᵥ w = ((n : ℝ) * μ + c)⁻¹ • w := by
    have h' : N⁻¹ *ᵥ (N *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hN, Matrix.one_mulVec]
    rw [hNw, Matrix.mulVec_smul] at h'
    calc N⁻¹ *ᵥ w = ((n : ℝ) * μ + c)⁻¹ • (((n : ℝ) * μ + c) • N⁻¹ *ᵥ w) := by
          rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      _ = _ := by rw [h']
  have hscal : ((n : ℝ) * μ + c)⁻¹ * ((n : ℝ) * μ) = μ / (μ + 2 * lam) := by
    rw [hcdef]
    field_simp
  ext i
  rw [toEuclideanLin_ofLp, ridgeSmoother_eq A hc, ← Matrix.mulVec_mulVec, hNinv,
    Matrix.mulVec_smul, hAA, smul_smul, hscal]
  rfl

/-- Ridge bias bound: the residual of the ridge fit of `y` is at most the penalized residual
`‖A β - y‖² + 2nλ‖β‖²` of any coefficient vector `β`. -/
private theorem norm_sq_ridge_residual_le (A : Matrix (Fin n) (Fin p) ℝ) {lam : ℝ}
    (hc : 0 < 2 * (n : ℝ) * lam) (y : EuclideanSpace ℝ (Fin n)) (β : EuclideanSpace ℝ (Fin p)) :
    ‖Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lam) y - y‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin (𝕜 := ℝ) A β - y‖ ^ 2 + 2 * n * lam * ‖β‖ ^ 2 := by
  set c := 2 * (n : ℝ) * lam with hcdef
  set M := Aᵀ * A + c • (1 : Matrix (Fin p) (Fin p) ℝ) with hMdef
  have hM := (isUnit_iff_isUnit_det _).mp (posDef_transpose_mul_add A hc).isUnit
  set L := Matrix.toEuclideanLin (𝕜 := ℝ) A with hL
  set Lt := Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ with hLt
  set b := Matrix.toEuclideanLin (𝕜 := ℝ) M⁻¹ (Lt y) with hb
  have hH : Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lam) y = L b := by
    ext i
    simp only [hL, hb, hLt, toEuclideanLin_ofLp, ridgeSmoother, Matrix.mulVec_mulVec, hMdef,
      Matrix.mul_assoc]
    rfl
  have hadj : ∀ u w, ⟪u, L w⟫ = ⟪Lt u, w⟫ := by
    intro u w
    rw [hL, hLt, ← conjTranspose_eq_transpose_of_trivial,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hnormal : Lt (y - L b) = c • b := by
    have hMb : M *ᵥ b.ofLp = Aᵀ *ᵥ y.ofLp := by
      rw [hb, toEuclideanLin_ofLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM,
        Matrix.one_mulVec, hLt, toEuclideanLin_ofLp]
    rw [hMdef, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hMb
    ext i
    have := congrFun hMb i
    simp only [hLt, hL, toEuclideanLin_ofLp, WithLp.ofLp_sub, WithLp.ofLp_smul, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at this ⊢
    linarith
  set r := y - L b with hr
  set d := β - b with hd
  have h1 : L β - y = L d - r := by
    rw [hd, hr, map_sub]
    abel
  have h2 : ⟪L d, r⟫ = c * ⟪b, d⟫ := by
    rw [real_inner_comm, hadj, hnormal, real_inner_smul_left]
  have h3 : ‖β‖ ^ 2 = ‖b‖ ^ 2 + 2 * ⟪b, d⟫ + ‖d‖ ^ 2 := by
    rw [← norm_add_sq_real, hd, add_sub_cancel]
  have h4 : ‖L b - y‖ = ‖r‖ := by rw [hr, norm_sub_rev]
  rw [hH, h4, h1, norm_sub_sq_real (L d) r, h2, h3]
  nlinarith [mul_nonneg hc.le (sq_nonneg ‖b‖), mul_nonneg hc.le (sq_nonneg ‖d‖),
    sq_nonneg ‖L d‖]

/-- For a map diagonal in an orthonormal basis, `‖T z‖² = ∑ h_j² ⟪e_j, z⟫²`. -/
private theorem norm_sq_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) (h : ι → ℝ)
    (hT : ∀ j, T (e j) = h j • e j) (z : E) :
    ‖T z‖ ^ 2 = ∑ j, h j ^ 2 * ⟪e j, z⟫ ^ 2 := by
  have hz : T z = ∑ j, (h j * ⟪e j, z⟫) • e j := by
    conv_lhs => rw [← e.sum_repr z]
    simp only [map_sum, map_smul, hT, smul_smul, OrthonormalBasis.repr_apply_apply, mul_comm]
  rw [← real_inner_self_eq_norm_sq, ← e.sum_inner_mul_inner, hz]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [real_inner_comm, e.orthonormal.inner_right_fintype]
  ring

/-- The elementary bound `(1 - y)^(-1/2) ≤ exp y` for `0 ≤ y ≤ 1/2`. -/
private theorem rpow_neg_half_le_exp {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) :
    (1 - y) ^ (-1 / 2 : ℝ) ≤ Real.exp y := by
  have hq : 0 < 1 - y := by linarith
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  have hlog : -2 * y ≤ Real.log (1 - y) := by
    rw [Real.le_log_iff_exp_le hq]
    have h2 := Real.add_one_le_exp (2 * y)
    have h3 : Real.exp (-2 * y) * Real.exp (2 * y) = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-2 * y)
    nlinarith [mul_le_mul_of_nonneg_left h2 h4.le, mul_nonneg h0 (by linarith : 0 ≤ 1 - 2 * y)]
  linarith

/-- Chernoff bound for a weighted chi-squared sum with weights in `[0, 1]`. -/
private theorem pi_tail_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∀ j, w j ≤ 1) {a : ℝ} (hsum : ∑ j, w j ≤ a / 32) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real {x | 2 * a ≤ ∑ j, w j * x j ^ 2} ≤
      Real.exp (-(a / 4)) := by
  have hint : Integrable (fun x : ι → ℝ ↦ Real.exp ((1 / 4 : ℝ) * ∑ j, w j * x j ^ 2))
      (Measure.pi fun _ ↦ gaussianReal 0 1) :=
    (mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff w (1 / 4)).mpr
      fun j ↦ by linarith [hw1 j]
  refine (measure_ge_le_exp_mul_mgf (X := fun x : ι → ℝ ↦ ∑ j, w j * x j ^ 2) (2 * a)
    (by norm_num) hint).trans ?_
  rw [mgf_sum_mul_sq_pi_gaussianReal fun j ↦ by linarith [hw1 j]]
  have hprod : ∏ j, (1 - 2 * (1 / 4) * w j) ^ (-1 / 2 : ℝ) ≤ Real.exp (∑ j, w j / 2) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (by linarith [hw1 j]) _)
      fun j _ ↦ ?_
    have := rpow_neg_half_le_exp (y := w j / 2) (by linarith [hw0 j]) (by linarith [hw1 j])
    convert this using 2
    ring
  calc Real.exp (-(1 / 4) * (2 * a)) * ∏ j, (1 - 2 * (1 / 4) * w j) ^ (-1 / 2 : ℝ)
      ≤ Real.exp (-(1 / 4) * (2 * a)) * Real.exp (∑ j, w j / 2) := by gcongr
    _ = Real.exp (-(1 / 4) * (2 * a) + ∑ j, w j / 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(a / 4)) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.sum_div]
      have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ ↦ hw0 j
      linarith

/-- Integrability and mean of a weighted sum of squared standard Gaussian coordinates. -/
private theorem integrable_and_integral_sum_sq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (w : ι → ℝ) :
    Integrable (fun z ↦ ∑ j, w j * ⟪e j, z⟫ ^ 2) (stdGaussian E) ∧
      ∫ z, ∑ j, w j * ⟪e j, z⟫ ^ 2 ∂stdGaussian E = ∑ j, w j := by
  have hi : ∀ j, Integrable (fun z ↦ w j * ⟪e j, z⟫ ^ 2) (stdGaussian E) := fun j ↦
    ((memLp_inner_stdGaussian (e j) 2 (by simp)).integrable_sq).const_mul _
  refine ⟨integrable_finsetSum _ fun j _ ↦ hi j, ?_⟩
  rw [integral_finsetSum _ fun j _ ↦ hi j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul, integral_sq_inner_stdGaussian, e.orthonormal.1 j, one_pow, mul_one]


/-- The critical-radius inequality bounds the sum of the squared ridge-smoother eigenvalues
`μ / (μ + 2λ)` by `n R² δ² / (32 σ²)` when `2 δ² ≤ λ`. -/
private theorem sum_sq_ridgeEigen_le {n : ℕ} {mu : Fin n → ℝ} (hmu : ∀ j, 0 ≤ mu j)
    {R sigma delta lambda : ℝ} (hn' : (0 : ℝ) < n) (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (hcrit : HasKernelCriticalRadius mu R sigma delta) (hlam : 2 * delta ^ 2 ≤ lambda) :
    ∑ j, (mu j / (mu j + 2 * lambda)) ^ 2 ≤ (n : ℝ) * R ^ 2 * delta ^ 2 / sigma ^ 2 / 32 := by
  have hd2 : 0 < delta ^ 2 := by positivity
  set h : Fin n → ℝ := fun j ↦ mu j / (mu j + 2 * lambda) with hh
  have hpos : ∀ j, 0 < mu j + 2 * lambda := fun j ↦ by linarith [hmu j]
  have hh0 : ∀ j, 0 ≤ h j := fun j ↦ div_nonneg (hmu j) (hpos j).le
  have hh1 : ∀ j, h j ≤ 1 := fun j ↦ (div_le_one (hpos j)).mpr (by linarith)
  have hhsq : ∀ j, h j ^ 2 * delta ^ 2 ≤ min (delta ^ 2) (mu j) := by
    intro j
    have hsq : h j ^ 2 ≤ h j := by nlinarith [hh0 j, hh1 j]
    have hmu' : h j * delta ^ 2 ≤ mu j := by
      rw [hh, div_mul_eq_mul_div, div_le_iff₀ (hpos j)]
      nlinarith [hmu j]
    refine le_min ?_ ?_
    · nlinarith [hh0 j, hh1 j]
    · nlinarith
  set X := ∑ j, min (delta ^ 2) (mu j) with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ ↦ le_min hd2.le (hmu j)
  have hXle : X ≤ (R * delta ^ 2 / (4 * sigma)) ^ 2 * n / 2 := by
    have h1 : (2 / (n : ℝ)) * X ≤ (R * delta ^ 2 / (4 * sigma)) ^ 2 := by
      rw [← Real.sq_sqrt (by positivity : 0 ≤ (2 / (n : ℝ)) * X)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hcrit 2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hn'] at h1
    linarith
  have h1 : (∑ j, h j ^ 2) * delta ^ 2 ≤ X := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦ hhsq j
  have h2 : (R * delta ^ 2 / (4 * sigma)) ^ 2 * n / 2 =
      (n : ℝ) * R ^ 2 * delta ^ 2 / sigma ^ 2 / 32 * delta ^ 2 := by
    field_simp
    ring
  rw [← mul_le_mul_iff_of_pos_right hd2]
  linarith

/-- GAPS 107.13: fixed-design kernel-ridge oracle bounds for a finite feature representation.
The constants are universal. Both the expected bound and the Gaussian tail bound use the same
critical radius. The eigenvalues `mu j` of the normalized Gram matrix `A Aᵀ / n` are
automatically nonnegative. This does not formalize the eigenvalue-decay calculation for infinite
RKHSs. -/
theorem ridgePrediction_oracle_bounds :
    ∃ c₀ > (0 : ℝ), ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∃ c₃ > (0 : ℝ),
      ∀ n p : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin p) ℝ,
      ∀ e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ mu : Fin n → ℝ,
      (∀ j, Matrix.toEuclideanLin (𝕜 := ℝ) (((n : ℝ)⁻¹) • (A * A.transpose)) (e j) =
        mu j • e j) →
      ∀ R sigma delta lambda : ℝ,
      0 < R → 0 < sigma → 0 < delta → HasKernelCriticalRadius mu R sigma delta →
      2 * delta ^ 2 ≤ lambda → ∀ truth : EuclideanSpace ℝ (Fin n),
      ∀ beta : EuclideanSpace ℝ (Fin p), ‖beta‖ ≤ R →
      let bound := c₀ * (‖Matrix.toEuclideanLin (𝕜 := ℝ) A beta - truth‖ ^ 2 / n +
        c₁ * R ^ 2 * (delta ^ 2 + lambda));
      (∫ z, ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ bound ∧
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {z | bound < ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n} ≤
          c₂ * Real.exp (-c₃ * n * R ^ 2 * delta ^ 2 / sigma ^ 2) := by
  refine ⟨2, by norm_num, 2, by norm_num, 1, by norm_num, 1 / 4, by norm_num, ?_⟩
  intro n p hn A e mu hmu R sigma delta lambda hR hsigma hdelta hcrit hlam truth beta hbeta
    bound
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlam0 : 0 < lambda := by nlinarith [pow_pos hdelta 2]
  have hc : 0 < 2 * (n : ℝ) * lambda := by positivity
  set H := Matrix.toEuclideanLin (𝕜 := ℝ) (ridgeSmoother A lambda) with hHdef
  have heig := fun j ↦ ridgeSmoother_eigen A hn hlam0 (e.orthonormal.1 j) (hmu j)
  set h : Fin n → ℝ := fun j ↦ mu j / (mu j + 2 * lambda) with hh
  have hh0 : ∀ j, 0 ≤ h j := fun j ↦ div_nonneg (heig j).1 (by linarith [(heig j).1])
  have hh1 : ∀ j, h j ≤ 1 := fun j ↦
    (div_le_one (by linarith [(heig j).1])).mpr (by linarith [(heig j).1])
  set a := (n : ℝ) * R ^ 2 * delta ^ 2 / sigma ^ 2 with ha
  have hsum : ∑ j, h j ^ 2 ≤ a / 32 :=
    sum_sq_ridgeEigen_le (fun j ↦ (heig j).1) hn' hsigma hdelta hcrit hlam
  have hvar : 2 * sigma ^ 2 * ∑ j, h j ^ 2 ≤ n * R ^ 2 * delta ^ 2 / 16 := by
    have : 2 * sigma ^ 2 * (a / 32) = n * R ^ 2 * delta ^ 2 / 16 := by
      rw [ha]
      field_simp
      ring
    rw [← this]
    gcongr
  -- the noise term
  set S : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ ∑ j, h j ^ 2 * ⟪e j, z⟫ ^ 2 with hS
  have hnorm : ∀ z, ‖H z‖ ^ 2 = S z := fun z ↦
    norm_sq_apply_of_eigen e H h (fun j ↦ (heig j).2) z
  set E := ‖Matrix.toEuclideanLin (𝕜 := ℝ) A beta - truth‖ ^ 2 with hE
  set K := 2 * E + 4 * n * lambda * R ^ 2 with hK
  have hbias : ‖H truth - truth‖ ^ 2 ≤ E + 2 * n * lambda * R ^ 2 := by
    refine (norm_sq_ridge_residual_le A hc truth beta).trans ?_
    have : ‖beta‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbeta 2
    nlinarith
  have hpt : ∀ z, ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n ≤
      (K + 2 * sigma ^ 2 * S z) / n := by
    intro z
    have hsplit : ridgePrediction A lambda (truth + sigma • z) - truth =
        (H truth - truth) + sigma • H z := by
      simp only [ridgePrediction, ← hHdef, map_add, map_smul]
      abel
    rw [hsplit, ← hnorm z]
    gcongr
    have h1 := norm_add_le (H truth - truth) (sigma • H z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsigma] at h1
    have h2 : ‖H truth - truth + sigma • H z‖ ^ 2 ≤ (‖H truth - truth‖ + sigma * ‖H z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖H truth - truth‖ - sigma * ‖H z‖)]
  have hbn : bound * n = 2 * E + 4 * n * R ^ 2 * (delta ^ 2 + lambda) := by
    simp only [bound]
    field_simp
    ring
  obtain ⟨hSi, hSint⟩ := integrable_and_integral_sum_sq_inner e (fun j ↦ h j ^ 2)
  have hScont : Continuous S := by
    simp only [hS]
    fun_prop
  refine ⟨?_, ?_⟩
  · calc (∫ z, ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)))
        ≤ ∫ z, (K + 2 * sigma ^ 2 * S z) / n ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z ↦ by positivity)
            (((integrable_const K).add (hSi.const_mul _)).div_const _)
            (Filter.Eventually.of_forall hpt)
      _ = (K + 2 * sigma ^ 2 * ∑ j, h j ^ 2) / n := by
          rw [integral_div, integral_add (integrable_const K) (hSi.const_mul _),
            integral_const_mul, hSint]
          simp
      _ ≤ bound := by
          rw [div_le_iff₀ hn', hbn, hK]
          have : 0 ≤ (n : ℝ) * R ^ 2 * delta ^ 2 := by positivity
          nlinarith
  · have hsub : {z | bound < ‖ridgePrediction A lambda (truth + sigma • z) - truth‖ ^ 2 / n} ⊆
        {z | 2 * a ≤ S z} := by
      intro z hz
      have h1 : bound < (K + 2 * sigma ^ 2 * S z) / n := lt_of_lt_of_le hz (hpt z)
      rw [lt_div_iff₀ hn', hbn, hK] at h1
      show 2 * a ≤ S z
      rw [ha, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    refine (measureReal_mono hsub).trans ?_
    have hφ : Measurable fun x : Fin n → ℝ ↦ ∑ i, x i • e i := by fun_prop
    rw [stdGaussian_eq_map_pi_orthonormalBasis e,
      map_measureReal_apply hφ (measurableSet_le measurable_const hScont.measurable)]
    have hpre : (fun x : Fin n → ℝ ↦ ∑ i, x i • e i) ⁻¹' {z | 2 * a ≤ S z} =
        {x | 2 * a ≤ ∑ j, h j ^ 2 * x j ^ 2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hS, e.orthonormal.inner_right_fintype]
    rw [hpre]
    refine (pi_tail_le (fun j ↦ h j ^ 2) (fun j ↦ sq_nonneg _)
      (fun j ↦ pow_le_one₀ (hh0 j) (hh1 j)) hsum).trans (le_of_eq ?_)
    rw [one_mul, ha]
    ring_nf

end RidgeOracle

/-- Empirical `k`-means distortion of a finite sample, using an ordered center representation. -/
def kmeansSampleRisk {X : Type*} [PseudoMetricSpace X] {n k : ℕ}
    (x : Fin n → X) (centers : Fin k → X) : ℝ :=
  (∑ i, sInf (range fun j ↦ dist (x i) (centers j) ^ 2)) / n

/-- Infima of two finite families differ by at most a uniform bound on their pointwise
differences. -/
private theorem abs_ciInf_sub_ciInf_le {ι : Type*} [Nonempty ι] [Finite ι] {f g : ι → ℝ}
    {ε : ℝ} (h : ∀ j, |f j - g j| ≤ ε) : |(⨅ j, f j) - ⨅ j, g j| ≤ ε := by
  have hf := (Set.finite_range f).bddBelow
  have hg := (Set.finite_range g).bddBelow
  have h1 : (⨅ j, f j) - ε ≤ ⨅ j, g j := le_ciInf fun j ↦ by
    linarith [ciInf_le hf j, (abs_sub_le_iff.mp (h j)).1]
  have h2 : (⨅ j, g j) - ε ≤ ⨅ j, f j := le_ciInf fun j ↦ by
    linarith [ciInf_le hg j, (abs_sub_le_iff.mp (h j)).2]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- On a bounded set `K` of diameter `D`, the squared distance to a point is `2D`-Lipschitz in
that point: `|d(x,a)² - d(x,b)²| ≤ 2D d(a,b)` for `x, a, b ∈ K`. -/
private theorem abs_dist_sq_sub_dist_sq_le {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : Bornology.IsBounded K) {x a b : E} (hx : x ∈ K) (ha : a ∈ K) (hb : b ∈ K) :
    |dist x a ^ 2 - dist x b ^ 2| ≤ 2 * Metric.diam K * dist a b := by
  have h1 := Metric.dist_le_diam_of_mem hK hx ha
  have h2 := Metric.dist_le_diam_of_mem hK hx hb
  have h3 : |dist x a - dist x b| ≤ dist a b := by
    rw [dist_comm x a, dist_comm x b]; exact abs_dist_sub_le a b x
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
  nlinarith [abs_nonneg (dist x a - dist x b), dist_nonneg (x := x) (y := a),
    dist_nonneg (x := x) (y := b), dist_nonneg (x := a) (y := b)]

/-- Averages of two families whose terms differ by at most `L ≥ 0` differ by at most `L`. -/
private theorem abs_sum_div_sub_sum_div_le {n : ℕ} {a b : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ i, |a i - b i| ≤ L) :
    |(∑ i ∈ Finset.range n, a i) / n - (∑ i ∈ Finset.range n, b i) / n| ≤ L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc |∑ i ∈ Finset.range n, (a i - b i)| ≤ ∑ i ∈ Finset.range n, |a i - b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, L := Finset.sum_le_sum fun i _ ↦ h i
    _ = L * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- If functions `Sₙ` and `R` are `L`-Lipschitz and `Sₙ c → R c` on a dense set of points `c`,
then `Sₙ c → R c` everywhere. -/
private theorem tendsto_of_lipschitz_of_dense {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (hSd : Dense S) {Sn : ℕ → X → ℝ} {R : X → ℝ} {L : ℝ} (hL0 : 0 < L)
    (hSnlip : ∀ n c c', |Sn n c - Sn n c'| ≤ L * dist c c')
    (hRlip : ∀ c c', |R c - R c'| ≤ L * dist c c')
    (hS : ∀ c ∈ S, Tendsto (fun n ↦ Sn n c) atTop (𝓝 (R c))) (c : X) :
    Tendsto (fun n ↦ Sn n c) atTop (𝓝 (R c)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c', hc'S, hcc'⟩ := hSd.exists_dist_lt c (show 0 < ε / (4 * L) by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS c' hc'S) (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := hSnlip n c c'
  have h2 := hRlip c c'
  have h3 := hN n hn
  have h4 : L * dist c c' < ε / 4 := by
    calc L * dist c c' < L * (ε / (4 * L)) := mul_lt_mul_of_pos_left hcc' hL0
      _ = ε / 4 := by field_simp
  rw [Real.dist_eq] at h3 ⊢
  calc |Sn n c - R c| ≤ |Sn n c - Sn n c'| + |Sn n c' - R c'| + |R c' - R c| := by
        have := abs_sub_le (Sn n c) (Sn n c') (R c)
        have := abs_sub_le (Sn n c') (R c') (R c)
        linarith
    _ < ε := by rw [abs_sub_comm (R c')]; linarith

/-- In a compact set `K`, if every subsequential limit of a sequence of `k`-tuples of points has
the same range as a fixed tuple `star`, then the ranges converge to that of `star` in Hausdorff
distance. -/
private theorem tendsto_hausdorffDist_range_of_forall_tendsto_subseq {E : Type*} [MetricSpace E]
    {K : Set E} [CompactSpace K] {k : ℕ} (C : ℕ → Fin k → K) (star : Fin k → K)
    (hlimit : ∀ (c : Fin k → K) (ψ : ℕ → ℕ), StrictMono ψ →
      Tendsto (fun j ↦ C (ψ j)) atTop (𝓝 c) →
        range (fun i ↦ (c i).val) = range (fun i ↦ (star i).val)) :
    Tendsto (fun n ↦ Metric.hausdorffDist (range fun j ↦ (C n j).val)
      (range fun j ↦ (star j).val)) atTop (𝓝 0) := by
  by_contra hne
  rw [Metric.tendsto_atTop] at hne
  push Not at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  have hfreq' : ∃ᶠ n in atTop, ε ≤ Metric.hausdorffDist (range fun j ↦ (C n j).val)
      (range fun j ↦ (star j).val) := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, h⟩ := hfreq N
    refine ⟨n, hn, ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h
  obtain ⟨ψ₁, hψ₁, hψ₁ε⟩ := Filter.extraction_of_frequently_atTop hfreq'
  obtain ⟨c, ψ₂, hψ₂, hc⟩ := CompactSpace.tendsto_subseq fun j ↦ C (ψ₁ j)
  have hrange := hlimit c (ψ₁ ∘ ψ₂) (hψ₁.comp hψ₂) hc
  obtain ⟨j, hj⟩ := (Metric.tendsto_atTop.mp hc ε hε).imp fun N h ↦ h N le_rfl
  have hHle : Metric.hausdorffDist (range fun i ↦ (C (ψ₁ (ψ₂ j)) i).val)
      (range fun i ↦ (star i).val) ≤ dist (C (ψ₁ (ψ₂ j))) c := by
    rw [← hrange]
    refine Metric.hausdorffDist_le_of_mem_dist dist_nonneg ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine ⟨(c i).val, ⟨i, rfl⟩, ?_⟩
      rw [← Subtype.dist_eq]; exact dist_le_pi_dist _ _ i
    · rintro _ ⟨i, rfl⟩
      refine ⟨(C (ψ₁ (ψ₂ j)) i).val, ⟨i, rfl⟩, ?_⟩
      rw [← Subtype.dist_eq, dist_comm]; exact dist_le_pi_dist _ _ i
  have := hψ₁ε (ψ₂ j)
  simp only [Function.comp_apply] at hj
  linarith

/-- GAPS 107.16: almost-sure consistency of compactly constrained empirical `k`-means minimizers.
This scope assumes a fixed compact support containing all centers. The unbounded-support theorem
under only a second moment requires an additional localization argument. (For `k = 0` all center
sets are empty and the statement is trivial.) -/
theorem ae_tendsto_kmeans_centers_of_compact
    {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hsupp : P K = 1)
    (star : Fin k → K)
    (hmin : ∀ c : Fin k → K, kmeansRisk P (fun i ↦ (star i).val) ≤
      kmeansRisk P (fun i ↦ (c i).val))
    (hunique : ∀ c : Fin k → K, kmeansRisk P (fun i ↦ (c i).val) =
      kmeansRisk P (fun i ↦ (star i).val) →
        range (fun i ↦ (c i).val) = range (fun i ↦ (star i).val))
    (C : ℕ → Ω → Fin k → K)
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ c : Fin k → K,
      kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (C n ω j).val) ≤
        kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (c j).val)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Metric.hausdorffDist
      (range fun j ↦ (C n ω j).val) (range fun j ↦ (star j).val)) atTop (𝓝 0) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine Eventually.of_forall fun ω ↦ ?_
    simp only [Set.range_eq_empty, Metric.hausdorffDist_empty]
    exact tendsto_const_nhds
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- the loss `φ x c = minⱼ ‖x - cⱼ‖²` and its Lipschitz constant on `K`
  set φ : EuclideanSpace ℝ (Fin d) → (Fin k → K) → ℝ := fun x c ↦
    ⨅ j, dist x (c j : EuclideanSpace ℝ (Fin d)) ^ 2 with hφ
  set L : ℝ := 2 * Metric.diam K + 1 with hL
  have hKb := hK.isBounded
  have hD0 : 0 ≤ Metric.diam K := Metric.diam_nonneg
  have hL0 : 0 < L := by rw [hL]; linarith
  have hlip : ∀ x ∈ K, ∀ c c' : Fin k → K, |φ x c - φ x c'| ≤ L * dist c c' := by
    intro x hx c c'
    refine abs_ciInf_sub_ciInf_le fun j ↦ ?_
    refine (abs_dist_sq_sub_dist_sq_le hKb hx (c j).2 (c' j).2).trans ?_
    have hj : dist (c j : EuclideanSpace ℝ (Fin d)) (c' j : EuclideanSpace ℝ (Fin d)) ≤ dist c c' := by
      rw [← Subtype.dist_eq]; exact dist_le_pi_dist c c' j
    have := dist_nonneg (x := c) (y := c')
    nlinarith
  have hbound : ∀ x ∈ K, ∀ c : Fin k → K, |φ x c| ≤ Metric.diam K ^ 2 := by
    intro x hx c
    have h0 : 0 ≤ φ x c := le_ciInf fun j ↦ sq_nonneg _
    have h1 : φ x c ≤ dist x (c ⟨0, hk⟩ : EuclideanSpace ℝ (Fin d)) ^ 2 :=
      ciInf_le (Set.finite_range _).bddBelow _
    have h2 := Metric.dist_le_diam_of_mem hKb hx (c ⟨0, hk⟩).2
    rw [abs_of_nonneg h0]
    nlinarith [dist_nonneg (x := x) (y := (c ⟨0, hk⟩ : EuclideanSpace ℝ (Fin d)))]
  have hmeas : ∀ c, Measurable fun x ↦ φ x c := fun c ↦
    Measurable.iInf fun j ↦ ((continuous_id.dist continuous_const).pow 2).measurable
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hPK : ∀ᵐ x ∂P, x ∈ K := by
    rw [ae_iff]
    have : P Kᶜ = 0 := (prob_compl_eq_zero_iff hKm).mpr hsupp
    simpa [Set.compl_def] using this
  have hint : ∀ c, Integrable (fun x ↦ φ x c) P := fun c ↦
    Integrable.of_bound (hmeas c).aestronglyMeasurable (Metric.diam K ^ 2)
      (hPK.mono fun x hx ↦ by rw [Real.norm_eq_abs]; exact hbound x hx c)
  set R : (Fin k → K) → ℝ := fun c ↦ ∫ x, φ x c ∂P with hR
  have hRdef : ∀ c : Fin k → K, kmeansRisk P (fun i ↦ (c i).val) = R c := fun c ↦ rfl
  have hRlip : ∀ c c' : Fin k → K, |R c - R c'| ≤ L * dist c c' := by
    intro c c'
    rw [hR, ← integral_sub (hint c) (hint c')]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |φ x c - φ x c'| ∂P ≤ ∫ _x, L * dist c c' ∂P :=
          integral_mono_ae ((hint c).sub (hint c')).abs (integrable_const _)
            (hPK.mono fun x hx ↦ hlip x hx c c')
      _ = L * dist c c' := by simp
  -- almost sure events
  have hXK : ∀ᵐ ω ∂μ, ∀ i, X i ω ∈ K := ae_all_iff.mpr fun i ↦ by
    have h := hPK
    rw [← hiid.2.2 i] at h
    exact ae_of_ae_map (hiid.1 i).aemeasurable h
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Fin k → K)
  have hslln : ∀ c : Fin k → K, ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦
      (∑ i ∈ Finset.range n, φ (X i ω) c) / n) atTop (𝓝 (R c)) := by
    intro c
    have hlaw : μ.map (X 0) = P := hiid.2.2 0
    have hint0 : Integrable ((fun x ↦ φ x c) ∘ X 0) μ := by
      have := hint c
      rw [← hlaw] at this
      exact this.comp_measurable (hiid.1 0)
    have h := strong_law_ae (fun i ω ↦ φ (X i ω) c) hint0
      (hiid.pairwise_indepFun_comp (hmeas c)) (hiid.identDistrib_comp (hmeas c))
    have hmean : ∫ ω, φ (X 0 ω) c ∂μ = R c := by
      rw [hR]
      simp only
      rw [← hlaw, integral_map (hiid.1 0).aemeasurable (hmeas c).aestronglyMeasurable]
    filter_upwards [h] with ω hω
    rw [hmean] at hω
    simpa [smul_eq_mul, div_eq_inv_mul] using hω
  have hallS : ∀ᵐ ω ∂μ, ∀ c ∈ S, Tendsto (fun n : ℕ ↦
      (∑ i ∈ Finset.range n, φ (X i ω) c) / n) atTop (𝓝 (R c)) :=
    (ae_ball_iff hSc).mpr fun c _ ↦ hslln c
  have hopt' : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n → ∀ c : Fin k → K,
      kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (C n ω j).val) ≤
        kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (c j).val) := by
    refine ae_all_iff.mpr fun n ↦ ?_
    by_cases hn : 0 < n
    · exact (hopt n hn).mono fun ω h _ ↦ h
    · exact Eventually.of_forall fun ω h ↦ absurd h hn
  filter_upwards [hXK, hallS, hopt'] with ω hXω hSω hoptω
  -- the sample risk at `ω`
  set Sn : ℕ → (Fin k → K) → ℝ := fun n c ↦ (∑ i ∈ Finset.range n, φ (X i ω) c) / n with hSn
  have hSndef : ∀ n (c : Fin k → K),
      kmeansSampleRisk (fun i : Fin n ↦ X i.val ω) (fun j ↦ (c j).val) = Sn n c := by
    intro n c
    simp only [kmeansSampleRisk, hSn]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i ↦ φ (X i ω) c) n
  have hSnlip : ∀ n (c c' : Fin k → K), |Sn n c - Sn n c'| ≤ L * dist c c' := fun n c c' ↦
    abs_sum_div_sub_sum_div_le (by positivity) fun i ↦ hlip _ (hXω i) c c'
  have hconv : ∀ c, Tendsto (fun n ↦ Sn n c) atTop (𝓝 (R c)) :=
    tendsto_of_lipschitz_of_dense hSd hL0 hSnlip hRlip hSω
  -- limit points of the empirical minimizers have the optimal center set
  have hlimit : ∀ (c : Fin k → K) (ψ : ℕ → ℕ), StrictMono ψ →
      Tendsto (fun j ↦ C (ψ j) ω) atTop (𝓝 c) →
        range (fun i ↦ (c i).val) = range (fun i ↦ (star i).val) := by
    intro c ψ hψ hC
    have hψt := hψ.tendsto_atTop
    have h1 : Tendsto (fun j ↦ Sn (ψ j) (C (ψ j) ω)) atTop (𝓝 (R c)) := by
      refine ((hconv c).comp hψt).congr_dist (squeeze_zero (fun _ ↦ dist_nonneg)
        (fun j ↦ ?_) (?_ : Tendsto (fun j ↦ L * dist (C (ψ j) ω) c) atTop (𝓝 0)))
      · rw [Real.dist_eq, abs_sub_comm]; exact hSnlip _ _ _
      · simpa using (tendsto_iff_dist_tendsto_zero.mp hC).const_mul L
    have h2 := (hconv star).comp hψt
    have hle : R c ≤ R star := by
      refine le_of_tendsto_of_tendsto h1 h2 ?_
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hpos : 0 < ψ j := lt_of_lt_of_le hj (hψ.id_le j)
      have := hoptω (ψ j) hpos star
      rwa [hSndef, hSndef] at this
    have heq : kmeansRisk P (fun i ↦ (c i).val) = kmeansRisk P (fun i ↦ (star i).val) := by
      rw [hRdef, hRdef]
      exact le_antisymm hle (by rw [← hRdef, ← hRdef]; exact hmin c)
    exact hunique c heq
  -- conclusion by compactness
  exact tendsto_hausdorffDist_range_of_forall_tendsto_subseq (fun n ↦ C n ω) star hlimit

/-- Permuting center labels leaves the population distortion unchanged. -/
theorem kmeansRisk_comp_perm {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {k : ℕ} (P : Measure X) (c : Fin k → X) (σ : Equiv.Perm (Fin k)) :
    kmeansRisk P (c ∘ σ) = kmeansRisk P c := by
  unfold kmeansRisk
  congr 1 with x
  exact congrArg sInf (EquivLike.range_comp (fun j ↦ dist x (c j) ^ 2) σ)

/-- A ridge smoother sends zero observations to zero predicted values. -/
@[simp] theorem ridgePrediction_zero {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (lambda : ℝ) : ridgePrediction A lambda 0 = 0 := by simp [ridgePrediction]

end CKSD
