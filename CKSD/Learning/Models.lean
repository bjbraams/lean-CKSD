module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.Wishart.Inverse.Moments
public import TauCeti.Probability.Distributions.Wishart.Agreement
public import TauCeti.Probability.Distributions.Gaussian.L2
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.Matrix.MeasurableSpace


/-!
# Log partition functions, tangent-kernel dynamics and least squares

This file collects results on simple learning models from Section 107 of the catalogue: the
entropy variational formula and zero-temperature limit of a finite log partition function, the
finite-width tangent-kernel dynamics of gradient flow, the risk of the ridgeless least-squares
estimator, and the implicit bias of gradient descent on least squares.

## Main results

* `CKSD.sum_mul_sub_mul_log_le_log_sum_exp`,
  `CKSD.sum_softmax_mul_sub_mul_log_eq_log_sum_exp`: `log ∑ᵢ exp aᵢ = max_w (⟨w, a⟩ + H(w))`
  over probability vectors, attained at the softmax vector (GAPS 107.26).
* `CKSD.tendsto_log_sum_exp_div_at_top`: `β⁻¹ log ∑ᵢ exp(β aᵢ) → maxᵢ aᵢ` (GAPS 107.26).
* `CKSD.has_deriv_at_predictions_of_gradient_flow`: predictions along the squared-loss gradient
  flow evolve through the tangent kernel `Df Dfᵀ` (GAPS 107.30).
* `CKSD.ridgeless_gaussian_risk_eq`: the risk `v p / (n - p - 1)` of ordinary least squares
  with Gaussian design (GAPS 107.31).
* `CKSD.tendsto_least_squares_gradient_descent`: gradient descent on least squares converges to
  the least-squares solution closest to the initial point in the sense that the `ker A`
  component is preserved (GAPS 107.40).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

section LogSumExp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- GAPS 107.26, finite-state entropy variational formula for the log partition function, upper
bound: for every probability vector `w`, `∑ᵢ wᵢ aᵢ + H(w) ≤ log ∑ᵢ exp aᵢ`. -/
theorem sum_mul_sub_mul_log_le_log_sum_exp (a : ι → ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) :
    ∑ i, (w i * a i - w i * Real.log (w i)) ≤ Real.log (∑ i, Real.exp (a i)) := by
  set Z := ∑ i, Real.exp (a i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hq1 : ∑ i, Real.exp (a i) / Z = 1 := by rw [← Finset.sum_div, div_self hZ.ne']
  have hpt : ∀ i, w i * a i - w i * Real.log (w i) ≤
      w i * Real.log Z + (Real.exp (a i) / Z - w i) := by
    intro i
    rcases (hw i).lt_or_eq with hpos | hzero
    · have hq : 0 < Real.exp (a i) / Z := div_pos (Real.exp_pos _) hZ
      have hl := Real.log_le_sub_one_of_pos (div_pos hq hpos)
      rw [Real.log_div hq.ne' hpos.ne', Real.log_div (Real.exp_pos _).ne' hZ.ne',
        Real.log_exp] at hl
      have := mul_le_mul_of_nonneg_left hl hpos.le
      have hc : w i * (Real.exp (a i) / Z / w i - 1) = Real.exp (a i) / Z - w i := by
        field_simp
      rw [hc] at this
      nlinarith
    · rw [← hzero]; simp only [zero_mul, sub_zero, zero_add]; positivity
  calc (∑ i, (w i * a i - w i * Real.log (w i)))
      ≤ ∑ i, (w i * Real.log Z + (Real.exp (a i) / Z - w i)) := Finset.sum_le_sum fun i _ ↦ hpt i
    _ = Real.log Z := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, Finset.sum_sub_distrib, hq1, hw1]
      ring

/-- GAPS 107.26, finite-state entropy variational formula for the log partition function,
attainment: the Gibbs (softmax) vector `exp aᵢ / Z` attains `log Z`. -/
theorem sum_softmax_mul_sub_mul_log_eq_log_sum_exp (a : ι → ℝ) :
    ∑ i, ((Real.exp (a i) / ∑ j, Real.exp (a j)) * a i -
      (Real.exp (a i) / ∑ j, Real.exp (a j)) *
        Real.log (Real.exp (a i) / ∑ j, Real.exp (a j))) =
      Real.log (∑ i, Real.exp (a i)) := by
  set Z := ∑ i, Real.exp (a i)
  have hZ : 0 < Z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hq1 : ∑ i, Real.exp (a i) / Z = 1 := by rw [← Finset.sum_div, div_self hZ.ne']
  have hpt : ∀ i, (Real.exp (a i) / Z) * a i -
      (Real.exp (a i) / Z) * Real.log (Real.exp (a i) / Z) = (Real.exp (a i) / Z) * Real.log Z := by
    intro i
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]; ring
  simp_rw [hpt]
  rw [← Finset.sum_mul, hq1, one_mul]

/-- GAPS 107.26, the zero-temperature limit of a finite log partition function:
`β⁻¹ log ∑ᵢ exp(β aᵢ) → maxᵢ aᵢ` as `β → ∞`. -/
theorem tendsto_log_sum_exp_div_at_top (a : ι → ℝ) :
    Tendsto (fun beta : ℝ ↦ Real.log (∑ i, Real.exp (beta * a i)) / beta)
      atTop (𝓝 (sSup (range a))) := by
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ a hne
  have hM : sSup (range a) = a k :=
    le_antisymm (csSup_le (range_nonempty a) (by rintro _ ⟨i, rfl⟩; exact hk i (Finset.mem_univ _)))
      (le_csSup (finite_range a).bddAbove ⟨k, rfl⟩)
  rw [hM]
  have hlow : ∀ β > (0 : ℝ), a k ≤ Real.log (∑ i, Real.exp (β * a i)) / β := by
    intro β hβ
    rw [le_div_iff₀ hβ, ← Real.log_exp (a k * β)]
    apply Real.log_le_log (Real.exp_pos _)
    rw [mul_comm]
    exact Finset.single_le_sum (f := fun i ↦ Real.exp (β * a i)) (fun i _ ↦ (Real.exp_pos _).le)
      (Finset.mem_univ k)
  set n := Fintype.card ι
  have hup : ∀ β > (0 : ℝ), Real.log (∑ i, Real.exp (β * a i)) / β ≤ a k + Real.log n / β := by
    intro β hβ
    have hsum : ∑ i, Real.exp (β * a i) ≤ n * Real.exp (β * a k) := by
      calc ∑ i, Real.exp (β * a i) ≤ ∑ _i : ι, Real.exp (β * a k) :=
            Finset.sum_le_sum fun i _ ↦ Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left (hk i (Finset.mem_univ _)) hβ.le)
        _ = n * Real.exp (β * a k) := by simp [n]
    have hpos : 0 < ∑ i, Real.exp (β * a i) := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) hne
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
    have hl := Real.log_le_log hpos hsum
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    rw [div_le_iff₀ hβ, add_mul, div_mul_cancel₀ _ hβ.ne']
    linarith
  have hlim : Tendsto (fun β : ℝ ↦ a k + Real.log n / β) atTop (𝓝 (a k)) := by
    have := (tendsto_const_nhds (x := a k)).add
      ((tendsto_const_nhds (x := Real.log n)).div_atTop tendsto_id)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (eventually_gt_atTop 0 |>.mono hlow) (eventually_gt_atTop 0 |>.mono hup)

end LogSumExp

/-- GAPS 107.30, finite-width tangent-kernel training dynamics for a differentiable model: along
the gradient flow `θ' = -n⁻¹ Dfᵀ (f(θ) - y)` of the empirical squared loss on `n` outputs, the
predictions evolve by `(f ∘ θ)' = -n⁻¹ Df Dfᵀ (f(θ) - y)`, with tangent kernel `Df Dfᵀ`. The
parameter and output spaces are arbitrary real Hilbert spaces. -/
theorem has_deriv_at_predictions_of_gradient_flow {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (n : ℕ) (f : E → F) (theta : ℝ → E) (y : F) (t : ℝ) (D : E →L[ℝ] F)
    (hf : HasFDerivAt f D (theta t))
    (hflow : HasDerivAt theta (-((n : ℝ)⁻¹) • D.adjoint (f (theta t) - y)) t) :
    HasDerivAt (f ∘ theta) (-((n : ℝ)⁻¹) • D (D.adjoint (f (theta t) - y))) t := by
  simpa only [map_smul] using hf.comp_hasDerivAt t hflow

/-- The standard Gaussian on `ℝᵖ` is the centred multivariate Gaussian with identity covariance. -/
private theorem std_gaussian_eq_multivariate_gaussian (p : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin p)) = multivariateGaussian 0 1 := by
  rw [TauCeti.Probability.multivariateGaussian_zero_eq_map_stdGaussian_sqrt, CFC.sqrt_one]
  have : (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin p) (Fin p) ℝ) :
      EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) = id := by
    funext x; simp
  rw [this, Measure.map_id]

/-- The Gram matrix `XᵀX` of the rows of a design. -/
private theorem coe_wishart_gram_eq {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    (TauCeti.Probability.wishartGram x : Matrix (Fin p) (Fin p) ℝ) =
      (Matrix.of fun i j ↦ x i j)ᵀ * Matrix.of fun i j ↦ x i j := by
  ext i j
  simp [TauCeti.Probability.coe_wishartGram, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.mul_apply]

/-- The trace on the symmetric-matrix subspace, as a continuous linear functional. -/
private def symmetricTraceCLM (p : ℕ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin p) ℝ ℝ) ∘ₗ (selfAdjoint.submodule ℝ _).subtype)

/-- Evaluation of the trace functional. -/
private theorem symmetric_trace_clm_apply {p : ℕ}
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    symmetricTraceCLM p B = (B : Matrix (Fin p) (Fin p) ℝ).trace :=
  rfl

/-- The law of the inverse Gram matrix of a standard Gaussian design with `n ≥ p` rows is the
inverse-Wishart law of degree `n` and identity scale. -/
private theorem map_inv_gram_eq_inverse_wishart_measure {n p : ℕ} (hn : p ≤ n) :
    (Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))).map
        (fun x ↦ TauCeti.symmetricInv (TauCeti.Probability.wishartGram x)) =
      TauCeti.Probability.inverseWishartMeasure (n : ℝ) 1 := by
  rw [show (fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦
      TauCeti.symmetricInv (TauCeti.Probability.wishartGram x)) =
      TauCeti.symmetricInv ∘ TauCeti.Probability.wishartGram from rfl,
    ← Measure.map_map TauCeti.measurable_symmetricInv
      TauCeti.Probability.measurable_wishartGram, std_gaussian_eq_multivariate_gaussian,
    ← TauCeti.Probability.wishartGramMeasure_eq_map_pi,
    TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure Matrix.PosDef.one hn,
    TauCeti.Probability.inverseWishartMeasure_def, inv_one]

/-- The mean trace of the inverse Gram matrix of a standard Gaussian design: integrability and
the value `p / (n - p - 1)`. The inverse-Wishart mean is TauCeti's
`TauCeti.Probability.integral_id_inverseWishartMeasure`. -/
private theorem integrable_and_integral_trace_inv_gram {n p : ℕ} (hn : p + 1 < n) :
    Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦
        (((Matrix.of fun i j ↦ x i j)ᵀ * Matrix.of fun i j ↦ x i j)⁻¹).trace)
        (Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))) ∧
      ∫ x : Fin n → EuclideanSpace ℝ (Fin p),
        (((Matrix.of fun i j ↦ x i j)ᵀ * Matrix.of fun i j ↦ x i j)⁻¹).trace
          ∂(Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))) =
        p / (n - p - 1 : ℕ) := by
  set μ := Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))
  set φ := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦
    TauCeti.symmetricInv (TauCeti.Probability.wishartGram x)
  have hφ : Measurable φ :=
    TauCeti.measurable_symmetricInv.comp TauCeti.Probability.measurable_wishartGram
  have hf : (fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦
      (((Matrix.of fun i j ↦ x i j)ᵀ * Matrix.of fun i j ↦ x i j)⁻¹).trace) =
      fun x ↦ symmetricTraceCLM p (φ x) := by
    funext x
    rw [symmetric_trace_clm_apply, TauCeti.coe_symmetricInv, coe_wishart_gram_eq]
  have hn' : (p : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hn
  have hmap := map_inv_gram_eq_inverse_wishart_measure (n := n) (p := p) (by omega)
  have hint := TauCeti.Probability.integrable_id_inverseWishartMeasure Matrix.PosDef.one hn'
  rw [hf]
  constructor
  · have := (symmetricTraceCLM p).integrable_comp hint
    rw [← hmap] at this
    exact (integrable_map_measure this.aestronglyMeasurable hφ.aemeasurable).mp this
  · rw [← integral_map hφ.aemeasurable (symmetricTraceCLM p).continuous.aestronglyMeasurable,
      hmap, (symmetricTraceCLM p).integral_comp_comm hint,
      TauCeti.Probability.integral_id_inverseWishartMeasure Matrix.PosDef.one hn', map_smul,
      symmetric_trace_clm_apply]
    simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    field_simp

/-- The squared norm of a matrix image is the sum of the squared inner products with the rows. -/
private theorem norm_sq_to_euclidean_lin {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ)
    (e : EuclideanSpace ℝ (Fin p)) :
    ‖Matrix.toEuclideanLin M e‖ ^ 2 = ∑ i, (inner ℝ (WithLp.toLp 2 (M i)) e) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.norm_eq_abs, sq_abs]
  congr 1
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]

/-- The second moment of a matrix image of a standard Gaussian vector is the squared Frobenius
norm of the matrix. -/
private theorem integrable_and_integral_norm_sq_to_euclidean_lin {m p : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) :
    Integrable (fun e ↦ ‖Matrix.toEuclideanLin M e‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin p))) ∧
      ∫ e, ‖Matrix.toEuclideanLin M e‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin p)) =
        ∑ i, ∑ j, M i j ^ 2 := by
  have hint : ∀ i, Integrable (fun e ↦ (inner ℝ (WithLp.toLp 2 (M i)) e) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) := fun i ↦
    (TauCeti.Probability.memLp_inner_stdGaussian _ 2 (by simp)).integrable_sq
  simp_rw [norm_sq_to_euclidean_lin]
  refine ⟨integrable_finsetSum _ fun i _ ↦ hint i, ?_⟩
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [TauCeti.Probability.integral_sq_inner_stdGaussian, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- With an invertible Gram matrix the least-squares error is a linear image of the noise. -/
private theorem least_squares_sub_eq {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (hA : (Aᵀ * A).det ≠ 0) (beta : EuclideanSpace ℝ (Fin p)) (c : ℝ)
    (e : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (Aᵀ * A)⁻¹ (Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ
        (Matrix.toEuclideanLin (𝕜 := ℝ) A beta + c • e)) - beta =
      c • Matrix.toEuclideanLin (𝕜 := ℝ) ((Aᵀ * A)⁻¹ * Aᵀ) e := by
  have h1 : (Aᵀ * A)⁻¹ * (Aᵀ * A) = 1 := Matrix.nonsing_inv_mul _ hA.isUnit
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
    WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [h1, Matrix.one_mulVec]
  simp

/-- The squared Frobenius norm of `(AᵀA)⁻¹Aᵀ` is the trace of `(AᵀA)⁻¹`. -/
private theorem sum_sq_inv_mul_transpose {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℝ)
    (hA : (Aᵀ * A).det ≠ 0) :
    ∑ i, ∑ j, ((Aᵀ * A)⁻¹ * Aᵀ) i j ^ 2 = ((Aᵀ * A)⁻¹).trace := by
  have h1 : (Aᵀ * A)⁻¹ * (Aᵀ * A) = 1 := Matrix.nonsing_inv_mul _ hA.isUnit
  have h2 : ((Aᵀ * A)⁻¹ * Aᵀ) * ((Aᵀ * A)⁻¹ * Aᵀ)ᵀ = ((Aᵀ * A)⁻¹)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᵀ, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← Matrix.trace_transpose ((Aᵀ * A)⁻¹), ← h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]

/-- The squared error of the least-squares fit is measurable in the design and the noise. -/
private theorem measurable_norm_sq_least_squares_sub {n p : ℕ} (beta : EuclideanSpace ℝ (Fin p))
    (v : ℝ≥0) :
    Measurable fun z : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin n) ↦
      ‖Matrix.toEuclideanLin (𝕜 := ℝ) (((Matrix.of (fun i j ↦ z.1 i j)).transpose) *
          Matrix.of (fun i j ↦ z.1 i j))⁻¹
        (Matrix.toEuclideanLin (𝕜 := ℝ) ((Matrix.of (fun i j ↦ z.1 i j)).transpose)
          (Matrix.toEuclideanLin (𝕜 := ℝ) (Matrix.of (fun i j ↦ z.1 i j)) beta +
            Real.sqrt v • z.2)) - beta‖ ^ 2 := by
  have hW : Measurable fun z : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin n) ↦
      (((Matrix.of (fun i j ↦ z.1 i j)).transpose) * Matrix.of (fun i j ↦ z.1 i j))⁻¹ := by
    refine TauCeti.measurable_matrix_inv.comp ?_
    rw [Matrix.measurable_iff]
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  simp only [PiLp.sub_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.add_apply,
    PiLp.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  have := fun k ↦ (Matrix.measurable_iff.mp hW) i k
  fun_prop


/-- A standard Gaussian design with `n ≥ p` rows has an almost surely invertible Gram matrix. -/
private theorem ae_det_gram_ne_zero {n p : ℕ} (hn : p ≤ n) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))),
      ((Matrix.of fun i j ↦ x i j)ᵀ * Matrix.of fun i j ↦ x i j).det ≠ 0 := by
  have h := TauCeti.Probability.ae_posDef_wishartGramMeasure (ν := n) Matrix.PosDef.one hn
  rw [TauCeti.Probability.wishartGramMeasure_eq_map_pi,
    ← std_gaussian_eq_multivariate_gaussian] at h
  filter_upwards [ae_of_ae_map TauCeti.Probability.measurable_wishartGram.aemeasurable h]
    with x hx
  rw [coe_wishart_gram_eq] at hx
  exact hx.det_pos.ne'

/-- GAPS 107.31, the underparameterized ridgeless risk with Gaussian noise. -/
theorem ridgeless_gaussian_risk_eq {n p : ℕ} (hn : p + 1 < n)
    (beta : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0) :
    let P := (Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)));
    let A := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ Matrix.of (fun i j ↦ x i j);
    let fit := fun z : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin n) ↦
      Matrix.toEuclideanLin (𝕜 := ℝ) (((A z.1).transpose) * A z.1)⁻¹
        (Matrix.toEuclideanLin (𝕜 := ℝ) ((A z.1).transpose)
          (Matrix.toEuclideanLin (𝕜 := ℝ) (A z.1) beta + Real.sqrt v • z.2));
    (∫ z, ‖fit z - beta‖ ^ 2 ∂P) = (v : ℝ) * p / (n - p - 1 : ℕ) := by
  intro P A fit
  obtain ⟨hTint, hTval⟩ := integrable_and_integral_trace_inv_gram hn
  have hae := ae_det_gram_ne_zero (n := n) (p := p) (by omega)
  have hsec : ∀ x, ((A x)ᵀ * A x).det ≠ 0 →
      Integrable (fun e ↦ ‖fit (x, e) - beta‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
        ∫ e, ‖fit (x, e) - beta‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
          v * (((A x)ᵀ * A x)⁻¹).trace := by
    intro x hx
    have hfun : (fun e ↦ ‖fit (x, e) - beta‖ ^ 2) = fun e ↦
        (v : ℝ) * ‖Matrix.toEuclideanLin (𝕜 := ℝ) (((A x)ᵀ * A x)⁻¹ * (A x)ᵀ) e‖ ^ 2 := by
      funext e
      simp only [fit]
      rw [least_squares_sub_eq _ hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (NNReal.coe_nonneg v)]
    obtain ⟨h1, h2⟩ := integrable_and_integral_norm_sq_to_euclidean_lin
      (((A x)ᵀ * A x)⁻¹ * (A x)ᵀ)
    rw [hfun, integral_const_mul, h2, sum_sq_inv_mul_transpose _ hx]
    exact ⟨h1.const_mul _, rfl⟩
  have hmeas := measurable_norm_sq_least_squares_sub (n := n) beta v
  have hint : Integrable (fun z ↦ ‖fit z - beta‖ ^ 2) P := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨hae.mono fun x hx ↦ (hsec x hx).1, (hTint.const_mul (v : ℝ)).congr ?_⟩
    filter_upwards [hae] with x hx
    simp_rw [norm_pow, norm_norm]
    exact ((hsec x hx).2).symm
  rw [integral_prod _ hint, integral_congr_ae (hae.mono fun x hx ↦ (hsec x hx).2),
    integral_const_mul, hTval, mul_div_assoc]

/-- GAPS 107.40, least-squares gradient descent and the preserved nullspace component: for a
step `0 < η < 2 / ‖A‖²`, the iterates `θ ↦ θ - η Aᵀ(Aθ - y)` converge to a solution `θ*` of the
normal equations with `θ* - θ₀ ∈ range Aᵀ`, i.e. the component of `θ₀` in `ker A` is preserved.
The parameter space is a finite-dimensional real inner product space and the output space a real
Hilbert space. -/
theorem tendsto_least_squares_gradient_descent {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (A : E →L[ℝ] F) (y : F) (theta₀ : E)
    (eta : ℝ) (he : 0 < eta) (hstep : eta * ‖A‖ ^ 2 < 2) :
    let update := fun x ↦ x - eta • A.adjoint (A x - y);
    ∃ thetaStar, A.adjoint (A thetaStar - y) = 0 ∧
      thetaStar - theta₀ ∈ LinearMap.range A.adjoint.toLinearMap ∧
      Tendsto (fun t : ℕ ↦ update^[t] theta₀) atTop (𝓝 thetaStar) := by
  intro update
  set K := LinearMap.range A.adjoint.toLinearMap with hK
  set R := LinearMap.range A.toLinearMap with hR
  -- a least-squares solution in `θ₀ + K`
  set r := y - A theta₀
  obtain ⟨z, hz⟩ : R.starProjection r ∈ R := R.starProjection_apply_mem r
  have hz' : A z = R.starProjection r := hz
  have hres : A.adjoint (r - A z) = 0 := by
    rw [hz']
    have horth := R.sub_starProjection_mem_orthogonal r
    refine ext_inner_left ℝ fun v ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal' R _).mp horth _ ⟨v, rfl⟩)
  set k := K.starProjection z
  have hkK : k ∈ K := K.starProjection_apply_mem z
  have hAk : A k = A z := by
    have horth := K.sub_starProjection_mem_orthogonal z
    have h0 : A (z - k) = 0 := by
      refine ext_inner_right ℝ fun w ↦ ?_
      rw [← ContinuousLinearMap.adjoint_inner_right, inner_zero_left]
      exact (Submodule.mem_orthogonal' K _).mp horth _ ⟨w, rfl⟩
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  set thetaStar := theta₀ + k
  have hnormal : A.adjoint (A thetaStar - y) = 0 := by
    have : A thetaStar - y = -(r - A z) := by
      simp only [thetaStar, map_add, hAk, r]; abel
    rw [this, map_neg, hres, neg_zero]
  refine ⟨thetaStar, hnormal, by simpa [thetaStar] using hkK, ?_⟩
  -- error recursion
  set e : ℕ → E := fun t ↦ update^[t] theta₀ - thetaStar
  have he_succ : ∀ t, e (t + 1) = e t - eta • A.adjoint (A (e t)) := by
    intro t
    simp only [e, Function.iterate_succ_apply', update]
    have : A.adjoint (A (update^[t] theta₀) - y) =
        A.adjoint (A (update^[t] theta₀ - thetaStar)) := by
      have h : A (update^[t] theta₀) - y =
          A (update^[t] theta₀ - thetaStar) + (A thetaStar - y) := by
        rw [map_sub]; abel
      rw [h, map_add, hnormal, add_zero]
    rw [this]
    abel
  have heK : ∀ t, e t ∈ K := by
    intro t
    induction t with
    | zero =>
      have : e 0 = -k := by simp [e, thetaStar]
      rw [this]; exact K.neg_mem hkK
    | succ t ih =>
      rw [he_succ]
      exact K.sub_mem ih (K.smul_mem _ ⟨_, rfl⟩)
  -- energy decrease
  set c := eta * (2 - eta * ‖A‖ ^ 2)
  have hc : 0 < c := mul_pos he (by linarith)
  have henergy : ∀ t, ‖e (t + 1)‖ ^ 2 + c * ‖A (e t)‖ ^ 2 ≤ ‖e t‖ ^ 2 := by
    intro t
    rw [he_succ]
    have h1 : ‖A.adjoint (A (e t))‖ ≤ ‖A‖ * ‖A (e t)‖ := by
      calc ‖A.adjoint (A (e t))‖ ≤ ‖A.adjoint‖ * ‖A (e t)‖ := A.adjoint.le_opNorm _
        _ = ‖A‖ * ‖A (e t)‖ := by rw [LinearIsometryEquiv.norm_map]
    have h2 : (inner ℝ (e t) (A.adjoint (A (e t)))) = ‖A (e t)‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    rw [norm_sub_sq_real, inner_smul_right, h2, norm_smul, Real.norm_eq_abs, abs_of_pos he]
    have h3 : (eta * ‖A.adjoint (A (e t))‖) ^ 2 ≤ eta ^ 2 * ‖A‖ ^ 2 * ‖A (e t)‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 he.le
      have h0 : 0 ≤ eta * ‖A.adjoint (A (e t))‖ := by positivity
      calc (eta * ‖A.adjoint (A (e t))‖) ^ 2 ≤ (eta * (‖A‖ * ‖A (e t)‖)) ^ 2 :=
            pow_le_pow_left₀ h0 this 2
        _ = eta ^ 2 * ‖A‖ ^ 2 * ‖A (e t)‖ ^ 2 := by ring
    calc ‖e t‖ ^ 2 - 2 * (eta * ‖A (e t)‖ ^ 2) + (eta * ‖A.adjoint (A (e t))‖) ^ 2 +
          c * ‖A (e t)‖ ^ 2 = ‖e t‖ ^ 2 - (eta ^ 2 * ‖A‖ ^ 2 * ‖A (e t)‖ ^ 2 -
            (eta * ‖A.adjoint (A (e t))‖) ^ 2) := by simp only [c]; ring
      _ ≤ ‖e t‖ ^ 2 := by linarith
  -- `A` is bounded below on `K`
  have hinjK : ∀ v ∈ K, A v = 0 → v = 0 := by
    rintro v ⟨w, rfl⟩ hv
    have : inner ℝ (A.adjoint w) (A.adjoint w) = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [ContinuousLinearMap.coe_coe] at hv
      rw [hv, inner_zero_right]
    exact inner_self_eq_zero.mp this
  obtain ⟨C, -, hC⟩ := (A.toLinearMap.comp K.subtype).exists_antilipschitzWith (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hinjK v v.2 hv))
  have hbelow : ∀ v ∈ K, ‖v‖ ≤ C * ‖A v‖ := fun v hv ↦ by
    have := ZeroHomClass.bound_of_antilipschitz _ hC (⟨v, hv⟩ : K)
    simpa using this
  -- summability of the residuals
  have hsum : Summable fun t ↦ c * ‖A (e t)‖ ^ 2 := by
    refine summable_of_sum_range_le (c := ‖e 0‖ ^ 2) (fun t ↦ by positivity) fun T ↦ ?_
    have : ∀ T, ∑ t ∈ Finset.range T, c * ‖A (e t)‖ ^ 2 + ‖e T‖ ^ 2 ≤ ‖e 0‖ ^ 2 := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
        rw [Finset.sum_range_succ]
        linarith [henergy T]
    linarith [this T, sq_nonneg ‖e T‖]
  have hA0 : Tendsto (fun t ↦ ‖A (e t)‖) atTop (𝓝 0) := by
    have h := hsum.tendsto_atTop_zero
    have h' : Tendsto (fun t ↦ ‖A (e t)‖ ^ 2) atTop (𝓝 0) := by
      have := h.const_mul c⁻¹
      simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
      exact this
    have := h'.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have he0 : Tendsto (fun t ↦ ‖e t‖) atTop (𝓝 0) := by
    have hup : Tendsto (fun t ↦ (C : ℝ) * ‖A (e t)‖) atTop (𝓝 0) := by
      simpa using hA0.const_mul (C : ℝ)
    exact squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ hbelow _ (heK t)) hup
  have : Tendsto (fun t ↦ e t + thetaStar) atTop (𝓝 (0 + thetaStar)) :=
    (tendsto_zero_iff_norm_tendsto_zero.mpr he0).add tendsto_const_nhds
  simpa [e] using this

end CKSD
