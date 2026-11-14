module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import Statlib.ForMathlib.MeasureTheory.Integral.Pi


/-!
# Projections of isotropic Gaussian vectors

For `ε ~ N(0, σ² I)` on `ℝⁿ` and an orthonormal family `v`, the coordinates `⟪vᵢ, ε⟫` are
independent `N(0, σ²)` variables. This gives the exponential moment
`E exp(‖Π_K ε‖² / (4σ²)) = √2 ^ dim K` of a projected Gaussian vector, the chi-square bound
behind penalized model selection, together with the residual and risk expansions of
orthogonal-projection fits.

## Main results

* `CKSD.multivariate_gaussian_smul_one_eq_map_pi`: `N(m, σ² I)` is the product of its coordinate
  laws, from TauCeti's `TauCeti.Probability.map_affine_multivariateGaussian` and
  `TauCeti.Probability.multivariateGaussian_one_eq_map_pi`.
* `CKSD.lintegral_exp_sq_div_gaussian_real`: `E exp(Z² / (4σ²)) = √2` for `Z ~ N(0, σ²)`.
* `CKSD.lintegral_exp_sum_sq_inner_multivariate_gaussian`: for an orthonormal family `v`,
  `E exp(∑ᵢ ⟪vᵢ, ε⟫² / (4σ²)) = √2 ^ |ι|`, using Statlib's Tonelli theorem for products.
* `CKSD.lintegral_exp_norm_star_projection_sq_le`: the same bound for `‖Π_K ε‖²` plus the square
  of one coordinate orthogonal to `K`.
* `CKSD.norm_sub_star_projection_add_sq`, `CKSD.norm_star_projection_add_sub_sq`,
  `CKSD.norm_star_projection_sq_eq_sum`: residual, risk, and Parseval identities for projections.

Source: GAPS 103.35.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace

namespace CKSD

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The isotropic Gaussian `N(m, σ² I)` on `ℝ^ι` is the product of its coordinate laws
`N(m_i, σ²)`, transported to Euclidean space. -/
theorem multivariate_gaussian_smul_one_eq_map_pi (m : EuclideanSpace ℝ ι) (σ : ℝ) :
    multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ)) =
      (Measure.pi fun i ↦ gaussianReal (m i) (Real.toNNReal (σ ^ 2))).map (WithLp.toLp 2) := by
  have haff := TauCeti.Probability.map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι)
    Matrix.PosSemidef.one (σ • (1 : Matrix ι ι ℝ)) m
  have hcov : σ • (1 : Matrix ι ι ℝ) * 1 * (σ • (1 : Matrix ι ι ℝ)).transpose =
      σ ^ 2 • (1 : Matrix ι ι ℝ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_one, smul_mul_smul,
      Matrix.mul_one, sq]
  rw [hcov, map_zero, zero_add] at haff
  rw [← haff, TauCeti.Probability.multivariateGaussian_one_eq_map_pi,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hpi : (Measure.pi fun i : ι ↦ gaussianReal ((0 : EuclideanSpace ℝ ι) i) 1).map
      (fun x i ↦ σ * x i + m i) =
        Measure.pi fun i ↦ gaussianReal (m i) (Real.toNNReal (σ ^ 2)) := by
    rw [Measure.pi_map_pi (f := fun i (x : ℝ) ↦ σ * x + m i) (fun _ ↦ by fun_prop)]
    congr 1; funext i
    have : (fun x : ℝ ↦ σ * x + m i) = (fun x ↦ x + m i) ∘ (fun x ↦ σ * x) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    simp only [PiLp.zero_apply, mul_zero, zero_add, mul_one]
    congr 1
    ext; simp [sq_nonneg]
  rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i
  simp [Matrix.toEuclideanLin, add_comm]

/-- The exponential moment `E exp(Z² / 4) = √2` of a centered Gaussian `Z` of variance `σ²`,
written with `Z² / (4 σ²)`. -/
theorem lintegral_exp_sq_div_gaussian_real {σ : ℝ} (hσ : σ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (w ^ 2 / (4 * σ ^ 2))) ∂gaussianReal 0 (Real.toNNReal (σ ^ 2)) =
      ENNReal.ofReal (Real.sqrt 2) := by
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by simp [hσ]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hvv : ((Real.toNNReal (σ ^ 2) : ℝ)) = σ ^ 2 := Real.coe_toNNReal _ hσ2.le
  rw [gaussianReal_of_var_ne_zero _ hv, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF _ _) (by fun_prop)]
  have hpt : ∀ w : ℝ, (gaussianPDF 0 (Real.toNNReal (σ ^ 2)) * fun w ↦
      ENNReal.ofReal (Real.exp (w ^ 2 / (4 * σ ^ 2)))) w =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-(1 / (4 * σ ^ 2)) * w ^ 2)) := by
    intro w
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal, hvv, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    field_simp
    ring
  simp_rw [hpt]
  have hb : 0 < 1 / (4 * σ ^ 2) := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun w ↦ by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have hpos : 0 < Real.sqrt (2 * Real.pi * σ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [show Real.pi / (1 / (4 * σ ^ 2)) = 2 * (2 * Real.pi * σ ^ 2) by field_simp; ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (2 * Real.pi * σ ^ 2)]
  field_simp

/-- For an orthonormal family `v` and `ε ~ N(0, σ² I)`, the coordinates `⟪v i, ε⟫` are
independent `N(0, σ²)`, so `E exp(∑ᵢ ⟪v i, ε⟫² / (4σ²)) = √2 ^ |ι|`. -/
theorem lintegral_exp_sum_sq_inner_multivariate_gaussian {n : ℕ} (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) {σ : ℝ} (hσ : σ ≠ 0) :
    ∫⁻ ε, ENNReal.ofReal (Real.exp ((∑ i, ⟪v i, ε⟫ ^ 2) / (4 * σ ^ 2)))
        ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      ENNReal.ofReal (Real.sqrt 2) ^ Fintype.card ι := by
  set L : Matrix ι (Fin n) ℝ := Matrix.of fun i j ↦ v i j with hLdef
  have hL : ∀ ε : EuclideanSpace ℝ (Fin n),
      L.toEuclideanLin ε = WithLp.toLp 2 (fun i ↦ ⟪v i, ε⟫) := by
    intro ε
    ext i
    simp [hLdef, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hLL : L * (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) * L.transpose =
      σ ^ 2 • (1 : Matrix ι ι ℝ) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    congr 1
    ext i k
    have := (orthonormal_iff_ite.mp hv) i k
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hLdef, Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hmap := TauCeti.Probability.map_affine_multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin n)) (Matrix.PosSemidef.one.smul (sq_nonneg σ)) L 0
  rw [hLL, map_zero, add_zero] at hmap
  simp_rw [add_zero] at hmap
  set F : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun w ↦ ENNReal.ofReal (Real.exp ((∑ i, w i ^ 2) / (4 * σ ^ 2))) with hF
  have hFm : Measurable F := by fun_prop
  have hlhs : (fun ε : EuclideanSpace ℝ (Fin n) ↦
      ENNReal.ofReal (Real.exp ((∑ i, ⟪v i, ε⟫ ^ 2) / (4 * σ ^ 2)))) =
      F ∘ fun ε ↦ L.toEuclideanLin ε := by
    funext ε; simp [hF, hL]
  rw [hlhs]
  change ∫⁻ ε, F (L.toEuclideanLin ε)
    ∂(multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) = _
  rw [← lintegral_map hFm (by fun_prop), hmap, multivariate_gaussian_smul_one_eq_map_pi,
    lintegral_map hFm (by fun_prop)]
  have hprod : ∀ x : ι → ℝ, F (WithLp.toLp 2 x) =
      ∏ i, ENNReal.ofReal (Real.exp (x i ^ 2 / (4 * σ ^ 2))) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
      ← Finset.sum_div]
  simp_rw [hprod]
  rw [lintegral_fintype_prod_eq_prod
    (f := fun _ (w : ℝ) ↦ ENNReal.ofReal (Real.exp (w ^ 2 / (4 * σ ^ 2)))) fun i ↦ by fun_prop]
  simp only [PiLp.zero_apply, lintegral_exp_sq_div_gaussian_real hσ, Finset.prod_const,
    Finset.card_univ]

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Submodule ℝ E)
  [K.HasOrthogonalProjection]

/-- Residual expansion for an observation `f + ε`:
`‖(f + ε) - Π(f + ε)‖² = ‖f - Πf‖² + 2⟪f - Πf, ε⟫ + ‖ε‖² - ‖Πε‖²`. -/
theorem norm_sub_star_projection_add_sq (f ε : E) :
    ‖(f + ε) - K.starProjection (f + ε)‖ ^ 2 =
      ‖f - K.starProjection f‖ ^ 2 + 2 * ⟪f - K.starProjection f, ε⟫ + ‖ε‖ ^ 2 -
        ‖K.starProjection ε‖ ^ 2 := by
  have h1 : (f + ε) - K.starProjection (f + ε) =
      (f - K.starProjection f) + (ε - K.starProjection ε) := by
    rw [map_add]; abel
  have h2 : ⟪f - K.starProjection f, K.starProjection ε⟫ = 0 :=
    Submodule.starProjection_inner_eq_zero f _ (K.starProjection_apply_mem ε)
  have h3 : ⟪K.starProjection ε, ε - K.starProjection ε⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero ε _ (K.starProjection_apply_mem ε)
  have h4 : ‖ε‖ ^ 2 = ‖K.starProjection ε‖ ^ 2 + ‖ε - K.starProjection ε‖ ^ 2 := by
    conv_lhs => rw [show ε = K.starProjection ε + (ε - K.starProjection ε) by abel]
    rw [norm_add_sq_real, h3]; ring
  rw [h1, norm_add_sq_real, inner_sub_right, h2, sub_zero]
  linarith

/-- Risk expansion for an observation `f + ε`: `‖Π(f + ε) - f‖² = ‖f - Πf‖² + ‖Πε‖²`. -/
theorem norm_star_projection_add_sub_sq (f ε : E) :
    ‖K.starProjection (f + ε) - f‖ ^ 2 =
      ‖f - K.starProjection f‖ ^ 2 + ‖K.starProjection ε‖ ^ 2 := by
  have h1 : K.starProjection (f + ε) - f = K.starProjection ε - (f - K.starProjection f) := by
    rw [map_add]; abel
  have h2 : ⟪K.starProjection ε, f - K.starProjection f⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero f _ (K.starProjection_apply_mem ε)
  rw [h1, norm_sub_sq_real, h2]; ring

/-- Parseval for a projection: `‖Πε‖² = ∑ₖ ⟪bₖ, ε⟫²` for an orthonormal basis `b` of `K`. -/
theorem norm_star_projection_sq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ K)
    (ε : E) : ‖K.starProjection ε‖ ^ 2 = ∑ k, ⟪(b k : E), ε⟫ ^ 2 := by
  rw [← Submodule.coe_orthogonalProjectionOnto_apply, Submodule.norm_coe,
    ← b.sum_sq_inner_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
    ← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr
      (b k).2]

end Projection

/-- Exponential moment of a projected isotropic Gaussian vector together with one orthogonal
direction: for `g ⊥ K`, `E exp((‖Π_K ε‖² + ⟪g, ε⟫² / ‖g‖²) / (4σ²)) ≤ √2 ^ (dim K + 1)`. -/
theorem lintegral_exp_norm_star_projection_sq_le {n : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n)) (hg : g ∈ Kᗮ)
    {σ : ℝ} (hσ : σ ≠ 0) :
    ∫⁻ ε, ENNReal.ofReal (Real.exp ((‖K.starProjection ε‖ ^ 2 + ⟪g, ε⟫ ^ 2 / ‖g‖ ^ 2) /
        (4 * σ ^ 2))) ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤
      ENNReal.ofReal (Real.sqrt 2) ^ (Module.finrank ℝ K + 1) := by
  set b := stdOrthonormalBasis ℝ K
  set e : Fin (Module.finrank ℝ K) → EuclideanSpace ℝ (Fin n) := fun k ↦ (b k : _) with he
  have heo : Orthonormal ℝ e := b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hsqrt : 1 ≤ ENNReal.ofReal (Real.sqrt 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_sqrt.mpr (by norm_num))
  by_cases hg0 : g = 0
  · subst hg0
    have := lintegral_exp_sum_sq_inner_multivariate_gaussian e heo hσ
    simp only [inner_zero_left, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, add_zero, norm_star_projection_sq_eq_sum K b]
    rw [this, Fintype.card_fin, pow_succ]
    exact le_mul_of_one_le_right' hsqrt
  set u := ‖g‖⁻¹ • g with hu
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg0
  set v : Option (Fin (Module.finrank ℝ K)) → EuclideanSpace ℝ (Fin n) :=
    fun o ↦ o.elim u e with hv
  have hvo : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    have hu1 : ⟪u, u⟫ = 1 := by
      rw [hu, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hue : ∀ k, ⟪u, e k⟫ = 0 := by
      intro k
      rw [hu, real_inner_smul_left, (Submodule.mem_orthogonal' K g).mp hg _ (b k).2, mul_zero]
    rintro (_ | i) (_ | j)
    · simpa [hv] using hu1
    · simpa [hv] using hue j
    · simpa [hv, real_inner_comm] using hue i
    · simpa [hv] using (orthonormal_iff_ite.mp heo) i j
  have := lintegral_exp_sum_sq_inner_multivariate_gaussian v hvo hσ
  rw [Fintype.card_option, Fintype.card_fin] at this
  refine le_of_eq (Eq.trans ?_ this)
  refine lintegral_congr fun ε ↦ ?_
  congr 3
  rw [Fintype.sum_option, norm_star_projection_sq_eq_sum K b, add_comm]
  simp only [hv, Option.elim, hu, real_inner_smul_left, he]
  congr 1
  field_simp

end CKSD

end
