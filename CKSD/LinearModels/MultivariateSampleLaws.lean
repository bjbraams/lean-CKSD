module

public import CKSD.LinearModels.Basic
public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.Probability.Distributions.Wishart.Agreement
public import TauCeti.Probability.Distributions.Wishart.Congruence
public import TauCeti.Probability.Distributions.Wishart.Inverse.Marginal
public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared
public import TauCeti.Probability.Distributions.Chi.Gaussian
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Constructions.Pi


/-!
# Exact laws for multivariate normal samples

Helmert's orthogonal decomposition of an i.i.d. sample from `N_p(m, Σ)` and Hotelling's law
for a Gaussian vector and an independent Wishart matrix.

## Main results

* `CKSD.map_orthogonal_mix_pi_multivariate_gaussian`: an orthogonal mixing of a centred
  i.i.d. `N(m, Σ)` sample is again i.i.d. `N(0, Σ)`.
* `CKSD.exists_helmert_decomposition`: an i.i.d. `N(m, Σ)` sample of size `n` splits into
  `n - 1` independent `N(0, Σ)` vectors whose Gram sum is the scatter matrix and an independent
  `N(0, Σ)` vector `U` with `x̄ = m + n^{-1/2} U`.
* `CKSD.map_quad_form_div_quad_form_inv_wishart_gram_measure`: for `A ∼ W_p(ν, Σ)` and a fixed
  nonzero `u`, `uᵀ Σ⁻¹ u / uᵀ A⁻¹ u ∼ χ²(ν - p + 1)`.
* `CKSD.map_quad_form_inv_multivariate_gaussian`: `Uᵀ Σ⁻¹ U ∼ χ²(p)` for `U ∼ N_p(0, Σ)`.
* `CKSD.map_hotelling_multivariate_gaussian_wishart_gram_measure`: for independent
  `U ∼ N_p(0, Σ)` and `A ∼ W_p(ν, Σ)`, `(ν - p + 1) / p · Uᵀ A⁻¹ U ∼ F(p, ν - p + 1)`.

The Helmert decomposition uses TauCeti's matrix normal law under orthogonal mixing
(`TauCeti.Probability.map_mul_mul_add_matrixNormalMeasure`). The ratio law reduces, by a
congruence moving `u` to the first basis vector, to the law of the `(1,1)` entry of an inverse
Wishart matrix (`TauCeti.Probability.map_inv_inv_apply_nonsingularWishartMeasure`). Hotelling's
law follows by conditioning on `U` and TauCeti's
`TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 5.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix MatrixOrder

namespace CKSD

variable {p : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The `p × κ` matrix whose columns are the vectors of a sample indexed by `κ`. -/
def sampleColumns (X : κ → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) κ ℝ :=
  Matrix.of fun i r ↦ X r i

omit [Fintype κ] [DecidableEq κ] in
/-- `sampleColumns` is measurable. -/
@[fun_prop]
theorem measurable_sample_columns :
    Measurable (sampleColumns : (κ → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) κ ℝ) := by
  unfold sampleColumns
  fun_prop

/-- Sample columns of independent standard Gaussian vectors are matrix normal `MN(0, 1, 1)`. -/
theorem map_sample_columns_pi_std_gaussian :
    (Measure.pi fun _ : κ ↦
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)).map sampleColumns =
      TauCeti.Probability.matrixNormalMeasure (0 : Matrix (Fin p) κ ℝ) 1 1 := by
  classical
  simp_rw [TauCeti.Probability.multivariateGaussian_one_eq_map_pi]
  simp_rw [WithLp.ofLp_zero, Pi.zero_apply]
  rw [← Measure.pi_map_pi (fun _ : κ ↦ (by fun_prop :
    AEMeasurable (WithLp.toLp 2) (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1)))]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [TauCeti.Probability.matrixNormalMeasure_of_posSemidef 0 Matrix.PosSemidef.one
      Matrix.PosSemidef.one,
    Matrix.one_kronecker_one, Matrix.vec_zero, WithLp.toLp_zero, multivariateGaussian_zero_one,
    ← map_pi_eq_stdGaussian, Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  have hc := TauCeti.measurePreserving_piCurry
    (fun _ : κ ↦ fun _ : Fin p ↦ (gaussianReal 0 1 : Measure ℝ))
  let e : κ × Fin p ≃ (Σ _ : κ, Fin p) :=
    (Equiv.sigmaEquivProd κ (Fin p)).symm
  have hp := measurePreserving_piCongrLeft
    (fun _ : (Σ _ : κ, Fin p) ↦ (gaussianReal 0 1 : Measure ℝ)) e
  have hflat := hc.comp hp
  rw [← hflat.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i r
  simp [sampleColumns, e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Sigma.curry,
    Equiv.piCongrLeft'_apply]

/-- `sampleColumns` as a measurable equivalence. -/
def sampleColumnsEquiv : (κ → EuclideanSpace ℝ (Fin p)) ≃ᵐ Matrix (Fin p) κ ℝ where
  toFun := sampleColumns
  invFun X k := WithLp.toLp 2 fun i ↦ X i k
  left_inv X := by ext k i; simp [sampleColumns]
  right_inv X := by ext i k; simp [sampleColumns]
  measurable_toFun := measurable_sample_columns
  measurable_invFun := by
    show Measurable (fun (X : Matrix (Fin p) κ ℝ) (k : κ) ↦ WithLp.toLp 2 fun i ↦ X i k)
    fun_prop

/-- Sample columns of independent `N(M_k, Σ)` vectors are matrix normal `MN(M, Σ, 1)`. -/
theorem map_sample_columns_pi_multivariate_gaussian (M : Matrix (Fin p) κ ℝ)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (Measure.pi fun k : κ ↦ multivariateGaussian (WithLp.toLp 2 fun i ↦ M i k) S).map
      sampleColumns = TauCeti.Probability.matrixNormalMeasure M S 1 := by
  set A := CFC.sqrt S
  have hA : A * 1 * Aᵀ = S := by rw [Matrix.mul_one]; exact hS.sqrt_mul_transpose_sqrt
  have hk : ∀ k : κ, multivariateGaussian (WithLp.toLp 2 fun i ↦ M i k) S =
      (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (fun z ↦ A.toEuclideanLin z + WithLp.toLp 2 fun i ↦ M i k) := by
    intro k
    rw [TauCeti.Probability.map_affine_multivariateGaussian 0 Matrix.PosSemidef.one, hA, map_zero,
      zero_add]
  simp_rw [hk]
  rw [← Measure.pi_map_pi (fun _ ↦ (by fun_prop)), Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (sampleColumns ∘ fun (z : κ → EuclideanSpace ℝ (Fin p)) k ↦
      A.toEuclideanLin (z k) + WithLp.toLp 2 fun i ↦ M i k) =
      (fun X ↦ A * X * (1 : Matrix κ κ ℝ) + M) ∘ sampleColumns := by
    funext z
    ext i k
    simp [sampleColumns, Matrix.mul_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_sample_columns_pi_std_gaussian,
    TauCeti.Probability.map_mul_mul_add_matrixNormalMeasure 0 Matrix.PosSemidef.one
      Matrix.PosSemidef.one, hA]
  simp

/-- Orthogonal mixing of a Gaussian sample: if `Bᵀ B = 1` and `x₁, …, x_n` are independent
`N(m, Σ)`, then the vectors `y_k = ∑ᵢ B i k (xᵢ - m)` are independent `N(0, Σ)`. -/
theorem map_orthogonal_mix_pi_multivariate_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι κ ℝ) (hB : Bᵀ * B = 1) (m : EuclideanSpace ℝ (Fin p))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    (Measure.pi fun _ : ι ↦ multivariateGaussian m S).map
        (fun x k ↦ ∑ i, B i k • (x i - m)) =
      Measure.pi fun _ : κ ↦ multivariateGaussian 0 S := by
  set Mm : Matrix (Fin p) ι ℝ := Matrix.of fun j _ ↦ m j
  have hx : (Measure.pi fun _ : ι ↦ multivariateGaussian m S).map sampleColumns =
      TauCeti.Probability.matrixNormalMeasure Mm S 1 := by
    rw [← map_sample_columns_pi_multivariate_gaussian Mm hS]
    rfl
  have h0 : (Measure.pi fun _ : κ ↦ multivariateGaussian 0 S).map sampleColumns =
      TauCeti.Probability.matrixNormalMeasure 0 S 1 := by
    rw [← map_sample_columns_pi_multivariate_gaussian 0 hS]
    rfl
  have hfun : (sampleColumns ∘ fun (x : ι → EuclideanSpace ℝ (Fin p)) (k : κ) ↦
      ∑ i, B i k • (x i - m)) =
      (fun X ↦ (1 : Matrix (Fin p) (Fin p) ℝ) * X * B + -(Mm * B)) ∘ sampleColumns := by
    funext x
    ext j k
    simp only [Function.comp_apply, sampleColumns, Mm, Matrix.of_apply, Matrix.add_apply,
      Matrix.neg_apply, Matrix.one_mul, Matrix.mul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
      WithLp.ofLp_sub, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib]
    simp only [mul_comm, sub_eq_add_neg]
  have hmeasY : Measurable fun (x : ι → EuclideanSpace ℝ (Fin p)) (k : κ) ↦
      ∑ i, B i k • (x i - m) := by fun_prop
  have hmap : ((Measure.pi fun _ : ι ↦ multivariateGaussian m S).map
      (fun x k ↦ ∑ i, B i k • (x i - m))).map sampleColumnsEquiv =
      (Measure.pi fun _ : κ ↦ multivariateGaussian 0 S).map sampleColumnsEquiv := by
    change _ = Measure.map sampleColumns _
    rw [h0]
    change Measure.map sampleColumns _ = _
    rw [Measure.map_map measurable_sample_columns hmeasY, hfun,
      ← Measure.map_map (by fun_prop) measurable_sample_columns, hx,
      TauCeti.Probability.map_mul_mul_add_matrixNormalMeasure Mm hS Matrix.PosSemidef.one]
    simp [hB]
  have := congrArg (fun μ ↦ μ.map sampleColumnsEquiv.symm) hmap
  simpa only [MeasurableEquiv.map_symm_map] using this

/-- A unit vector `v` of `ℝⁿ` is the last column of a real orthogonal `n × n` matrix whose
columns are indexed by `Fin (n - 1) ⊕ Unit`. -/
theorem exists_orthogonal_matrix_last_column {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) :
    ∃ B : Matrix (Fin n) (Fin (n - 1) ⊕ Unit) ℝ, Bᵀ * B = 1 ∧ ∀ i, B i (Sum.inr ()) = v i := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := ℝ ∙ v
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (Subsingleton.elim v 0) hv0
    · exact h
  have hfin : Module.finrank ℝ Kᗮ = n - 1 := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
      ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    exact Submodule.finrank_orthogonal_span_singleton hv0
  let b : OrthonormalBasis (Fin (n - 1)) ℝ Kᗮ := (stdOrthonormalBasis ℝ Kᗮ).reindex (finCongr hfin)
  let B : Matrix (Fin n) (Fin (n - 1) ⊕ Unit) ℝ := fun i a ↦ match a with
    | Sum.inl k => ((b k : Kᗮ) : EuclideanSpace ℝ (Fin n)) i
    | Sum.inr _ => v i
  have hinner : ∀ v w : EuclideanSpace ℝ (Fin n), inner ℝ v w = ∑ i, v i * w i := fun v w ↦ by
    simp [PiLp.inner_apply, mul_comm]
  have horth : ∀ k, ∑ i, v i * B i (Sum.inl k) = 0 := by
    intro k
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (b k).2
    rw [hinner] at h
    simpa [B] using h
  have hvv : ∑ i, v i * v i = 1 := by
    rw [← hinner, real_inner_self_eq_norm_sq, hv, one_pow]
  refine ⟨B, ?_, fun i ↦ rfl⟩
  ext a a'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rcases a with k | u <;> rcases a' with l | u'
  · have h := b.orthonormal
    rw [orthonormal_iff_ite] at h
    have := h k l
    rw [Submodule.coe_inner, hinner] at this
    simpa [B, Matrix.one_apply] using this
  · have := horth k
    simp only [B] at this ⊢
    rw [Matrix.one_apply_ne (by simp)]
    simpa [mul_comm] using this
  · have := horth l
    simp only [B] at this ⊢
    rw [Matrix.one_apply_ne (by simp)]
    exact this
  · simpa [B] using hvv

/-- A real orthogonal `n × n` matrix, with columns indexed by `Fin (n - 1) ⊕ Unit`, whose last
column is the constant vector `n^{-1/2}`; the other columns are then orthogonal to the
constants. -/
theorem exists_orthogonal_matrix_last_column_const (n : ℕ) (hn : 0 < n) :
    ∃ B : Matrix (Fin n) (Fin (n - 1) ⊕ Unit) ℝ, Bᵀ * B = 1 ∧
      (∀ i, B i (Sum.inr ()) = (Real.sqrt n)⁻¹) ∧ ∀ k, ∑ i, B i (Sum.inl k) = 0 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun _ ↦ (Real.sqrt n)⁻¹
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [v, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_inv_cancel₀ (by positivity), Real.sqrt_one]
  obtain ⟨B, hB, hlast⟩ := exists_orthogonal_matrix_last_column v hv
  refine ⟨B, hB, fun i ↦ hlast i, fun k ↦ ?_⟩
  have h := congrFun (congrFun hB (Sum.inl k)) (Sum.inr ())
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hlast, Matrix.one_apply] at h
  have hc : (Real.sqrt n)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (by positivity)).ne'
  have : ∑ i, B i (Sum.inl k) * (Real.sqrt n)⁻¹ = 0 := by simpa [v] using h
  rw [← Finset.sum_mul] at this
  exact (mul_eq_zero.1 this).resolve_right hc

omit [DecidableEq κ] in
/-- For `B Bᵀ = 1`, the mixed coordinates `(Bᵀ u)_a` preserve the dot product. -/
private theorem sum_mix_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι κ ℝ)
    (hBB : B * Bᵀ = 1) (u v : ι → ℝ) :
    ∑ a, (∑ i, B i a * u i) * (∑ i, B i a * v i) = ∑ i, u i * v i := by
  have h : (Bᵀ *ᵥ u) ⬝ᵥ (Bᵀ *ᵥ v) = u ⬝ᵥ v := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hBB,
      Matrix.one_mulVec]
  simpa [dotProduct, Matrix.mulVec, Matrix.transpose_apply, mul_comm] using h

/-- The Helmert decomposition of a Gaussian sample: for `n ≥ 1` independent `N(m, Σ)` vectors
there are measurable maps `Y` to `n - 1` vectors and `U` to one vector, jointly distributed as
`n` independent `N(0, Σ)` vectors, with `x̄ = m + n^{-1/2} U` and with the scatter matrix equal
to the Gram sum of `Y`. -/
theorem exists_helmert_decomposition {n : ℕ} (hn : 0 < n) (m : EuclideanSpace ℝ (Fin p))
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) :
    ∃ (Y : (Fin n → EuclideanSpace ℝ (Fin p)) → Fin (n - 1) → EuclideanSpace ℝ (Fin p))
      (U : (Fin n → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p)),
      Measurable Y ∧ Measurable U ∧
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian m S).map (fun x ↦ (Y x, U x)) =
        (Measure.pi fun _ : Fin (n - 1) ↦ multivariateGaussian 0 S).prod
          (multivariateGaussian 0 S) ∧
      (∀ x, sampleMean x = m + (Real.sqrt n)⁻¹ • U x) ∧
      ∀ x, scatterMatrix x = (TauCeti.Probability.wishartGram (Y x) : Matrix _ _ ℝ) := by
  obtain ⟨B, hB, hBlast, hB0⟩ := exists_orthogonal_matrix_last_column_const n hn
  have hcard : Fintype.card (Fin (n - 1) ⊕ Unit) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hBB : B * Bᵀ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 hB
  let Z : (Fin n → EuclideanSpace ℝ (Fin p)) → Fin (n - 1) ⊕ Unit → EuclideanSpace ℝ (Fin p) :=
    fun x k ↦ ∑ i, B i k • (x i - m)
  have hZ : Measurable Z := by fun_prop
  have hsum_dev : ∀ x : Fin n → EuclideanSpace ℝ (Fin p),
      ∑ i, (x i - m) = (n : ℝ) • (sampleMean x - m) := by
    intro x
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      sampleMean, smul_sub, smul_smul, mul_inv_cancel₀ (by positivity), one_smul,
      ← Nat.cast_smul_eq_nsmul ℝ]
  have hsn0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hU : ∀ x, Z x (Sum.inr ()) = Real.sqrt n • (sampleMean x - m) := by
    intro x
    simp only [Z, hBlast, ← Finset.smul_sum, hsum_dev, smul_smul]
    congr 1
    have h := Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp
    linarith
  refine ⟨fun x k ↦ Z x (Sum.inl k), fun x ↦ Z x (Sum.inr ()), by fun_prop, by fun_prop, ?_, ?_, ?_⟩
  · have hlaw := map_orthogonal_mix_pi_multivariate_gaussian B hB m hS
    have h1 : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) :=
      inferInstance
    have : SFinite (Measure.pi fun _ : Fin (n - 1) ↦
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := inferInstance
    have : SFinite (Measure.pi fun _ : Unit ↦
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := inferInstance
    have hsplit := measurePreserving_sumPiEquivProdPi
      (fun _ : Fin (n - 1) ⊕ Unit ↦ multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
    have hunit := measurePreserving_piUnique
      (fun _ : Unit ↦ multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
    have hpair := (MeasurePreserving.id
      (Measure.pi fun _ : Fin (n - 1) ↦ multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)).prod
      hunit
    have hall := hpair.comp hsplit
    rw [← hall.map_eq, ← hlaw, Measure.map_map hall.measurable hZ]
    rfl
  · intro x
    show sampleMean x = m + (Real.sqrt n)⁻¹ • Z x (Sum.inr ())
    rw [hU x, smul_smul, inv_mul_cancel₀ hsn0, one_smul]
    abel
  · intro x
    ext j l
    rw [TauCeti.Probability.coe_wishartGram]
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    -- the full sum of products over all `n` mixed vectors
    have hfull : ∑ a, (Z x a) j * (Z x a) l = ∑ i, (x i - m) j * (x i - m) l := by
      have h := sum_mix_mul B hBB (fun i ↦ (x i - m) j) (fun i ↦ (x i - m) l)
      simpa only [Z, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] using h
    rw [Fintype.sum_sum_type,
      Fintype.sum_unique (fun u : Unit ↦ (Z x (Sum.inr u)) j * (Z x (Sum.inr u)) l)] at hfull
    have hlast : (Z x (Sum.inr default)) j * (Z x (Sum.inr default)) l =
        n * ((sampleMean x - m) j * (sampleMean x - m) l) := by
      have : (default : Unit) = () := rfl
      rw [this, hU x]
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      have h := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)
      linear_combination ((sampleMean x - m) j * (sampleMean x - m) l) * h
    have hsc : scatterMatrix x j l = ∑ i, (x i - m) j * (x i - m) l -
        n * ((sampleMean x - m) j * (sampleMean x - m) l) := by
      have hsum : ∀ j, ∑ i, (x i - m) j = n * (sampleMean x - m) j := fun j ↦ by
        have := congrArg (fun v : EuclideanSpace ℝ (Fin p) ↦ v j) (hsum_dev x)
        simpa [WithLp.ofLp_sum, Finset.sum_apply] using this
      simp only [scatterMatrix]
      have e : ∀ i, (x i j - sampleMean x j) * (x i l - sampleMean x l) =
          (x i - m) j * (x i - m) l - (x i - m) j * (sampleMean x - m) l -
            (sampleMean x - m) j * (x i - m) l +
            (sampleMean x - m) j * (sampleMean x - m) l := fun i ↦ by
        simp only [WithLp.ofLp_sub, Pi.sub_apply]
        ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [hsc]
    linarith [hfull, hlast]
omit [Fintype κ] [DecidableEq κ] in
/-- The Euclidean quadratic form in coordinates. -/
theorem matrix_quadratic_form_eq_sum (A : Matrix (Fin p) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin p)) :
    matrixQuadraticForm A u = ∑ i, ∑ j, u i * A i j * u j := by
  simp [matrixQuadraticForm, Matrix.toEuclideanCLM_apply, PiLp.inner_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

omit [Fintype κ] [DecidableEq κ] in
/-- For a nonzero vector `u` there is an orthogonal matrix `N` whose first column is
`u / ‖u‖`. -/
theorem exists_orthogonal_first_column (u : EuclideanSpace ℝ (Fin p)) (hu : u ≠ 0)
    (h0 : 0 < p) :
    ∃ N : Matrix (Fin p) (Fin p) ℝ, Nᵀ * N = 1 ∧ N * Nᵀ = 1 ∧
      ∀ i, N i ⟨0, h0⟩ = ‖u‖⁻¹ * u i := by
  set v : EuclideanSpace ℝ (Fin p) := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu)]
  obtain ⟨B, hB, hlast⟩ := exists_orthogonal_matrix_last_column v hv
  have hcard : Fintype.card (Fin p) = Fintype.card (Fin (p - 1) ⊕ Unit) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let e0 := Fintype.equivOfCardEq hcard
  let e : Fin p ≃ Fin (p - 1) ⊕ Unit := e0.trans (Equiv.swap (e0 ⟨0, h0⟩) (Sum.inr ()))
  have he : e ⟨0, h0⟩ = Sum.inr () := by simp [e]
  let N : Matrix (Fin p) (Fin p) ℝ := B.submatrix id e
  have hN : Nᵀ * N = 1 := by
    ext a b
    have := congrFun (congrFun hB (e a)) (e b)
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this ⊢
    simp only [N, Matrix.submatrix_apply, id]
    rw [this, Matrix.one_apply, Matrix.one_apply]
    simp
  refine ⟨N, hN, mul_eq_one_comm.1 hN, fun i ↦ ?_⟩
  simp [N, he, hlast, v]

omit [Fintype κ] [DecidableEq κ] in
/-- For a Wishart matrix `A ∼ W_p(ν, Σ)` with `p ≤ ν` and a fixed nonzero `u`, the ratio
`uᵀ Σ⁻¹ u / uᵀ A⁻¹ u` is chi-squared with `ν - p + 1` degrees of freedom. -/
theorem map_quad_form_div_quad_form_inv_wishart_gram_measure {ν : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hν : p ≤ ν)
    (u : EuclideanSpace ℝ (Fin p)) (hu : u ≠ 0) :
    (TauCeti.Probability.wishartGramMeasure ν S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          matrixQuadraticForm S⁻¹ u / matrixQuadraticForm (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ u) =
      TauCeti.Probability.chiSquaredMeasure ((ν : ℝ) - p + 1) := by
  have h0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h
      exact absurd (Subsingleton.elim u 0) hu
    · exact h
  obtain ⟨N, hN, hN', hcol⟩ := exists_orthogonal_first_column u hu h0
  set i0 : Fin p := ⟨0, h0⟩
  have hNinv : N⁻¹ = Nᵀ := Matrix.inv_eq_left_inv hN
  have hNtinv : Nᵀ⁻¹ = N := Matrix.inv_eq_left_inv hN'
  have hconj : ∀ X : Matrix (Fin p) (Fin p) ℝ, (Nᵀ * X * N)⁻¹ = Nᵀ * X⁻¹ * N := fun X ↦ by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hNinv, hNtinv, Matrix.mul_assoc]
  set c : ℝ := ‖u‖⁻¹ ^ 2
  have hc : c ≠ 0 := by positivity
  have hentry : ∀ X : Matrix (Fin p) (Fin p) ℝ,
      (Nᵀ * X * N) i0 i0 = c * matrixQuadraticForm X u := fun X ↦ by
    rw [matrix_quadratic_form_eq_sum, Finset.mul_sum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hdetN : N.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hN
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, h, mul_zero] at h'
    exact zero_ne_one h'
  have hNunit : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hdetN)
  have hT : (Nᵀ * S * N).PosDef := by
    have h := hS.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hNunit)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hS' : (Nᵀ * S * N)⁻¹.PosDef := hT.inv
  have hn : (p : ℝ) - 1 < ν := by
    have : (p : ℝ) ≤ ν := Nat.cast_le.2 hν
    linarith
  have key := TauCeti.Probability.map_inv_inv_apply_nonsingularWishartMeasure hS' hn i0
  rw [Matrix.nonsing_inv_nonsing_inv _ hT.det_pos.ne'.isUnit] at key
  have ha : (Nᵀ * S * N)⁻¹ i0 i0 = c * matrixQuadraticForm S⁻¹ u := by rw [hconj, hentry]
  have hapos : 0 < c * matrixQuadraticForm S⁻¹ u := ha ▸ hS'.diag_pos
  rw [ha] at key
  have hdetNt : Nᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hcong :=
    TauCeti.Probability.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
      (ν : ℝ) S hdetNt
  rw [Matrix.transpose_transpose] at hcong
  rw [TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS hν]
  set g : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ :=
    fun W ↦ ((W : Matrix (Fin p) (Fin p) ℝ)⁻¹ i0 i0)⁻¹ with hg
  have hgm : Measurable g := by
    have h1 : Measurable fun W : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (W : Matrix (Fin p) (Fin p) ℝ)⁻¹ :=
      TauCeti.measurable_matrix_inv.comp measurable_subtype_coe
    exact measurable_inv.comp ((measurable_pi_apply i0).comp ((measurable_pi_apply i0).comp h1))
  have hcm : Measurable (Matrix.symmetricCongruenceLinearMap Nᵀ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      matrixQuadraticForm S⁻¹ u / matrixQuadraticForm (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ u) =
      (fun t ↦ (c * matrixQuadraticForm S⁻¹ u) * t) ∘ g ∘
        Matrix.symmetricCongruenceLinearMap Nᵀ := by
    funext A
    simp only [Function.comp_apply, hg, Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.transpose_transpose, hconj, hentry]
    rw [mul_inv, div_eq_mul_inv]
    field_simp
  rw [hfun, ← Measure.map_map (measurable_const_mul _) (hgm.comp hcm),
    ← Measure.map_map hgm hcm, hcong, key, Measure.map_map (measurable_const_mul _)
      (measurable_const_mul _)]
  have hid : ((fun t ↦ (c * matrixQuadraticForm S⁻¹ u) * t) ∘
      fun t ↦ (c * matrixQuadraticForm S⁻¹ u)⁻¹ * t) = id := by
    funext t
    simp only [Function.comp_apply, id]
    rw [← mul_assoc, mul_inv_cancel₀ hapos.ne', one_mul]
  rw [hid, Measure.map_id]

omit [Fintype κ] [DecidableEq κ] in
/-- The Euclidean quadratic form as a coordinate dot product. -/
theorem matrix_quadratic_form_eq_mul_vec_dot_product (A : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    matrixQuadraticForm A v = (A *ᵥ (v : Fin p → ℝ)) ⬝ᵥ (v : Fin p → ℝ) := by
  simp [matrixQuadraticForm, Matrix.toEuclideanCLM_apply,
    EuclideanSpace.inner_eq_star_dotProduct]

omit [Fintype κ] [DecidableEq κ] in
/-- For `U ∼ N(0, Σ)` with `Σ` positive definite, `Uᵀ Σ⁻¹ U` is chi-squared with `p` degrees of
freedom. -/
theorem map_quad_form_inv_multivariate_gaussian {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    (multivariateGaussian 0 S).map (fun u ↦ matrixQuadraticForm S⁻¹ u) =
      TauCeti.Probability.chiSquaredMeasure p := by
  set R := CFC.sqrt S
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRt : Rᵀ = R := by
    have h := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hRdet : IsUnit R.det := by
    have h := congrArg Matrix.det hRR
    rw [Matrix.det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 ↦ ?_
    rw [h0, zero_mul] at h
    exact hS.det_pos.ne' h.symm
  have hW : R * S⁻¹ * R = 1 := by
    rw [← hRR, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRdet,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hRdet]
  have hfun : (fun u ↦ matrixQuadraticForm S⁻¹ u) ∘
      (fun x : EuclideanSpace ℝ (Fin p) ↦ 0 + Matrix.toEuclideanCLM (𝕜 := ℝ) R x) =
      fun x ↦ ‖x‖ ^ 2 := by
    funext x
    simp only [Function.comp_apply, zero_add, matrix_quadratic_form_eq_mul_vec_dot_product,
      Matrix.toEuclideanCLM_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
  rw [multivariateGaussian, Measure.map_map (measurable_matrix_quadratic_form _) (by fun_prop),
    hfun, TauCeti.Probability.stdGaussian_map_norm_sq, finrank_euclideanSpace_fin]

omit [Fintype κ] [DecidableEq κ] in
/-- The quadratic form `uᵀ A⁻¹ u` is jointly measurable in a symmetric matrix `A` and `u`. -/
theorem measurable_matrix_quadratic_form_inv :
    Measurable fun z : EuclideanSpace ℝ (Fin p) ×
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1 := by
  have h1 : Measurable fun z : EuclideanSpace ℝ (Fin p) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ :=
    TauCeti.measurable_matrix_inv.comp (measurable_subtype_coe.comp measurable_snd)
  simp_rw [matrix_quadratic_form_eq_sum]
  refine Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ ?_
  have hu : ∀ k : Fin p, Measurable fun z : EuclideanSpace ℝ (Fin p) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ z.1 k := fun k ↦
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp measurable_fst)
  exact ((hu i).mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1))).mul (hu j)

omit [Fintype κ] [DecidableEq κ] in
/-- Measurability of `A ↦ uᵀ A⁻¹ u` on symmetric matrices. -/
theorem measurable_matrix_quadratic_form_inv_left (u : EuclideanSpace ℝ (Fin p)) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      matrixQuadraticForm (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ u := by
  have h1 : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ :=
    TauCeti.measurable_matrix_inv.comp measurable_subtype_coe
  simp_rw [matrix_quadratic_form_eq_sum]
  refine Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ ?_
  exact (measurable_const.mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1))).mul
    measurable_const

omit [Fintype κ] [DecidableEq κ] in
/-- A nonzero vector has positive quadratic form under a positive definite matrix. -/
private theorem quad_form_pos {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    {u : EuclideanSpace ℝ (Fin p)} (hu : u ≠ 0) : 0 < matrixQuadraticForm S u := by
  have hu' : (u : Fin p → ℝ) ≠ 0 := fun h ↦ hu (WithLp.ofLp_injective 2 (by simpa using h))
  have := hS.dotProduct_mulVec_pos hu'
  simp only [star_trivial] at this
  rw [matrix_quadratic_form_eq_mul_vec_dot_product, dotProduct_comm]
  exact this

omit [Fintype κ] [DecidableEq κ] in
/-- A centred nondegenerate Gaussian vector is almost surely nonzero. -/
theorem multivariate_gaussian_singleton_zero (hp : 0 < p) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) : multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S {0} = 0 := by
  have hX := measurable_matrix_quadratic_form (n := p) S⁻¹
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hnull : multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S
      ((fun u ↦ matrixQuadraticForm S⁻¹ u) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hX (measurableSet_singleton 0),
      map_quad_form_inv_multivariate_gaussian hS]
    have := TauCeti.Probability.nullSingletonClass_chiSquaredMeasure (k := (p : ℝ)) hp0
    exact measure_singleton 0
  refine measure_mono_null (fun u hu ↦ ?_) hnull
  rw [Set.mem_singleton_iff] at hu
  simp [hu, matrixQuadraticForm]

omit [Fintype κ] [DecidableEq κ] in
/-- Joint law of `U` and `Uᵀ Σ⁻¹ U / Uᵀ A⁻¹ U` for independent `U ∼ N_p(0, Σ)` and
`A ∼ W_p(ν, Σ)`: the ratio is independent of `U` with law `χ²(ν - p + 1)`. -/
theorem map_prod_quad_form_ratio (hp : 0 < p) {ν : ℕ} (hν : p ≤ ν)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    ((multivariateGaussian 0 S).prod (TauCeti.Probability.wishartGramMeasure ν S)).map
        (fun z ↦ (z.1, matrixQuadraticForm S⁻¹ z.1 /
          matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1)) =
      (multivariateGaussian 0 S).prod
        (TauCeti.Probability.chiSquaredMeasure ((ν : ℝ) - p + 1)) := by
  have hR : Measurable fun z : EuclideanSpace ℝ (Fin p) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        matrixQuadraticForm S⁻¹ z.1 / matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1 :=
    ((measurable_matrix_quadratic_form _).comp measurable_fst).div
      measurable_matrix_quadratic_form_inv
  have hmeas := measurable_fst.prodMk hR
  have hk : (0 : ℝ) ≤ (ν : ℝ) - p + 1 := by
    have : (p : ℝ) ≤ ν := by exact_mod_cast hν
    linarith
  have := TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure hk
  refine (Measure.prod_eq fun s t (hs : MeasurableSet s) (ht : MeasurableSet t) ↦ ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.prod_apply (hmeas (hs.prod ht))]
  have h0 : ∀ᵐ u ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S), u ≠ 0 :=
    measure_mono_null (fun u hu ↦ by simpa using hu) (multivariate_gaussian_singleton_zero hp hS)
  have hae : ∀ᵐ u ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S),
      TauCeti.Probability.wishartGramMeasure ν S (Prod.mk u ⁻¹' ((fun z ↦ (z.1,
        matrixQuadraticForm S⁻¹ z.1 / matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1))
          ⁻¹' s ×ˢ t)) =
        s.indicator (fun _ ↦ TauCeti.Probability.chiSquaredMeasure ((ν : ℝ) - p + 1) t) u := by
    filter_upwards [h0] with u hu
    by_cases hus : u ∈ s
    · have hm : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          matrixQuadraticForm S⁻¹ u / matrixQuadraticForm (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ u :=
        measurable_const.div (measurable_matrix_quadratic_form_inv_left u)
      rw [Set.indicator_of_mem hus, ← map_quad_form_div_quad_form_inv_wishart_gram_measure hS hν u hu,
        Measure.map_apply hm ht]
      congr 1
      ext A
      simp [hus]
    · rw [Set.indicator_of_notMem hus]
      convert measure_empty (μ := TauCeti.Probability.wishartGramMeasure ν S)
      ext A
      simp [hus]
  rw [lintegral_congr_ae hae, lintegral_indicator_const hs, mul_comm]

omit [Fintype κ] [DecidableEq κ] in
/-- Hotelling's law: for independent `U ∼ N_p(0, Σ)` and `A ∼ W_p(ν, Σ)` with `0 < p ≤ ν` and
`Σ` positive definite, `(ν - p + 1) / p · Uᵀ A⁻¹ U` has the F law with `p` and `ν - p + 1`
degrees of freedom. -/
theorem map_hotelling_multivariate_gaussian_wishart_gram_measure (hp : 0 < p) {ν : ℕ} (hν : p ≤ ν)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) :
    ((multivariateGaussian 0 S).prod (TauCeti.Probability.wishartGramMeasure ν S)).map
        (fun z ↦ ((ν - p + 1 : ℕ) : ℝ) / p *
          matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1) =
      TauCeti.Probability.fisherSnedecorMeasure p (ν - p + 1 : ℕ) := by
  set P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).prod
    (TauCeti.Probability.wishartGramMeasure ν S)
  have hk : ((ν : ℝ) - p + 1) = ((ν - p + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hν, Nat.cast_one]
  have hk0 : (0 : ℝ) < ((ν - p + 1 : ℕ) : ℝ) := by
    have : 0 < ν - p + 1 := by omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpair := map_prod_quad_form_ratio hp hν hS
  rw [hk] at hpair
  have := TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure hk0.le
  have hX : Measurable fun u : EuclideanSpace ℝ (Fin p) ↦ matrixQuadraticForm S⁻¹ u :=
    measurable_matrix_quadratic_form _
  have hR : Measurable fun z : EuclideanSpace ℝ (Fin p) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        matrixQuadraticForm S⁻¹ z.1 / matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1 :=
    (hX.comp measurable_fst).div measurable_matrix_quadratic_form_inv
  have hX1 : Measurable fun z : EuclideanSpace ℝ (Fin p) ×
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ matrixQuadraticForm S⁻¹ z.1 :=
    hX.comp measurable_fst
  have hpm := measurable_fst.prodMk hR
  -- marginal laws and independence of `X = Uᵀ Σ⁻¹ U` and the ratio
  have hRlaw : P.map (fun z ↦ matrixQuadraticForm S⁻¹ z.1 /
      matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1) =
      TauCeti.Probability.chiSquaredMeasure ((ν - p + 1 : ℕ) : ℝ) := by
    have h := congrArg (Measure.map Prod.snd) hpair
    rwa [Measure.map_map measurable_snd hpm, Measure.map_snd_prod, measure_univ, one_smul] at h
  have hXlaw : P.map (fun z ↦ matrixQuadraticForm S⁻¹ z.1) =
      TauCeti.Probability.chiSquaredMeasure p := by
    have h1 : P.map Prod.fst = multivariateGaussian 0 S := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← map_quad_form_inv_multivariate_gaussian hS, ← h1, Measure.map_map hX measurable_fst]
    rfl
  have hind : IndepFun (fun z ↦ matrixQuadraticForm S⁻¹ z.1)
      (fun z ↦ matrixQuadraticForm S⁻¹ z.1 /
        matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hX1.aemeasurable
      hR.aemeasurable, hXlaw, hRlaw, ← map_quad_form_inv_multivariate_gaussian hS]
    have h := congrArg (Measure.map (Prod.map (fun u ↦ matrixQuadraticForm S⁻¹ u) id)) hpair
    rw [Measure.map_map (hX.prodMap measurable_id) hpm, ← Measure.map_prod_map _ _ hX measurable_id,
      Measure.map_id] at h
    exact h
  have hF := TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared hp0 hk0 hind
    ⟨hX1.aemeasurable, hXlaw⟩ ⟨hR.aemeasurable, hRlaw⟩
  -- the F statistic agrees almost surely with the Hotelling statistic
  have h0 : ∀ᵐ z ∂P, z.1 ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [show {a : EuclideanSpace ℝ (Fin p) × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      a.1 = 0} = {0} ×ˢ Set.univ by ext; simp, Measure.prod_prod,
      multivariate_gaussian_singleton_zero hp hS, zero_mul]
  refine (hF.congr ?_).map_eq
  filter_upwards [h0] with z hz
  have hXz := quad_form_pos hS.inv hz
  by_cases hQ : matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1 = 0
  · simp [hQ]
  · field_simp

omit [Fintype κ] [DecidableEq κ] in
/-- Homogeneity of the matrix quadratic form in the matrix and in the vector. -/
theorem matrix_quadratic_form_smul_smul (c a : ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin p)) :
    matrixQuadraticForm (c • A) (a • u) = c * a ^ 2 * matrixQuadraticForm A u := by
  simp only [matrix_quadratic_form_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end CKSD

end
