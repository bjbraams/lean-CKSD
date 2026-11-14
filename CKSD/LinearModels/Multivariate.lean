module

public import CKSD.LinearModels.Basic
public import CKSD.LinearModels.CanonicalCorrelation
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import TauCeti.Probability.Distributions.Wishart.Agreement
public import TauCeti.Probability.Distributions.Wishart.Determinant
public import CKSD.Inference.Testing
public import CKSD.LinearModels.MultivariateSampleLaws


/-!
# Multivariate normal samples: Wishart and Hotelling laws, covariance likelihood

Exact distribution theory for samples from `N_p(μ, Σ)` and the Gaussian covariance likelihood.

## Main results

* `CKSD.gaussian_sample_mean_scatter_matrix_wishart_and_hotelling`: for an i.i.d. normal sample,
  the sample mean and the scatter matrix are independent, the scatter matrix is Wishart with
  `n - 1` degrees of freedom, and Hotelling's `T²`, suitably scaled, has an F law.
* `CKSD.log_det_le_trace_sub_card`, `CKSD.log_det_eq_trace_sub_card_iff`: the spectral
  inequality `log det A ≤ tr A - p` for positive definite `A`, with equality only at `A = 1`.
* `CKSD.log_det_add_card_le_log_det_add_trace_mul_inv`,
  `CKSD.log_det_add_card_eq_log_det_add_trace_mul_inv_iff`: the criterion
  `C ↦ log det C + tr(S C⁻¹)` has the unique minimizer `C = S` over positive definite matrices.
* `CKSD.gaussian_neg_log_likelihood_sample_mean_le`, `CKSD.gaussian_neg_log_likelihood_eq_iff`: the
  Gaussian likelihood of a sample with positive definite sample covariance has the unique
  maximizer (sample mean, sample covariance with divisor `n`).
* `CKSD.wishart_determinant_law`: Bartlett's decomposition gives the law of `det W` for a
  Wishart matrix as `det Σ` times a product of independent chi-squared variables; this uses
  TauCeti's Wishart agreement and determinant theorems.
* `CKSD.gaussian_sample_correlation_student_law`: under independence, the sample correlation
  `r` satisfies `√(N-2) r / √(1-r²) ∼ t_{N-2}`.

The sampling laws of 105.22 use the Helmert decomposition
`CKSD.exists_helmert_decomposition` and Hotelling's law
`CKSD.map_hotelling_multivariate_gaussian_wishart_gram_measure` from
`CKSD.LinearModels.MultivariateSampleLaws`.

The correlation law conditions on the second sample: for a fixed non-constant second sample,
the statistic is `Z / √(V / (N - 2))` with `Z` the inner product of the first sample with the
normalized centered second sample and `V` the squared length of the projection onto the
orthogonal complement of that vector and the constants. It uses TauCeti's
`HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian`,
`HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian` and
`TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared`.

The likelihood results use Mathlib's spectral theorem for Hermitian matrices and the inequality
`Real.log_le_sub_one_of_pos` together with its strict case.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapters 3, 5 and 7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator Matrix

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- GAPS 105.22: for `n ≥ p + 1` independent observations from `N_p(m, Σ)` with `Σ` positive
definite, the sample mean and the scatter matrix `A = ∑ᵢ (xᵢ - x̄)(xᵢ - x̄)ᵀ` are independent,
`A` has the Wishart law `W_p(n - 1, Σ)`, and with `S = A / (n - 1)` the scaled Hotelling
statistic `(n - p) / ((n - 1) p) · n (x̄ - m)ᵀ S⁻¹ (x̄ - m)` has the F law with `p` and `n - p`
degrees of freedom. -/
theorem gaussian_sample_mean_scatter_matrix_wishart_and_hotelling
    {n p : ℕ} (hp : 0 < p) (hn : p + 1 ≤ n)
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hS : Sigma.PosDef) :
    let P := Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma);
    let S := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ ((n - 1 : ℕ) : ℝ)⁻¹ • scatterMatrix x;
    IndepFun sampleMean scatterMatrix P ∧
      P.map scatterMatrix = (TauCeti.Probability.wishartGramMeasure (n - 1) Sigma).map
        (fun W ↦ (W.val : Matrix (Fin p) (Fin p) ℝ)) ∧
      P.map (fun x ↦ ((n - p : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) * p) *
        ((n : ℝ) * matrixQuadraticForm (S x)⁻¹ (sampleMean x - m))) =
        TauCeti.Probability.fisherSnedecorMeasure p (n - p : ℕ) := by
  intro P S
  obtain ⟨Y, U, hY, hU, hlaw, hmean, hscat⟩ :=
    exists_helmert_decomposition (by omega : 0 < n) m hS.posSemidef
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Sigma) :=
    inferInstance
  have : IsProbabilityMeasure
      (Measure.pi fun _ : Fin (n - 1) ↦
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Sigma) :=
    inferInstance
  have : SFinite
      (Measure.pi fun _ : Fin (n - 1) ↦
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Sigma) :=
    inferInstance
  have hpm : Measurable fun x ↦ (Y x, U x) := hY.prodMk hU
  have hYlaw : P.map Y = Measure.pi fun _ : Fin (n - 1) ↦ multivariateGaussian 0 Sigma := by
    have h := congrArg (Measure.map Prod.fst) hlaw
    rwa [Measure.map_map measurable_fst hpm, Measure.map_fst_prod, measure_univ, one_smul] at h
  have hUlaw : P.map U = multivariateGaussian 0 Sigma := by
    have h := congrArg (Measure.map Prod.snd) hlaw
    rwa [Measure.map_map measurable_snd hpm, Measure.map_snd_prod, measure_univ, one_smul] at h
  have hind : IndepFun U Y P := by
    have : IsProbabilityMeasure P := inferInstance
    rw [indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hY.aemeasurable, hYlaw, hUlaw,
      ← Measure.prod_swap, hlaw.symm, Measure.map_map measurable_swap hpm]
    rfl
  have hWm : Measurable fun x ↦ TauCeti.Probability.wishartGram (Y x) :=
    TauCeti.Probability.measurable_wishartGram.comp hY
  refine ⟨?_, ?_, ?_⟩
  · have h := hind.comp (φ := fun u ↦ m + (Real.sqrt n)⁻¹ • u)
      (ψ := fun y ↦ (TauCeti.Probability.wishartGram y : Matrix (Fin p) (Fin p) ℝ))
      (by fun_prop) (measurable_subtype_coe.comp TauCeti.Probability.measurable_wishartGram)
    convert h using 1
    · exact funext hmean
    · exact funext hscat
  · rw [show scatterMatrix = fun x ↦ (TauCeti.Probability.wishartGram (Y x) :
        Matrix (Fin p) (Fin p) ℝ) from funext hscat,
      TauCeti.Probability.wishartGramMeasure_eq_map_pi,
      ← hYlaw, Measure.map_map TauCeti.Probability.measurable_wishartGram hY,
      Measure.map_map measurable_subtype_coe (TauCeti.Probability.measurable_wishartGram.comp hY)]
    rfl
  · have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    have hν0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - 1 := by omega
      positivity
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hstat : (fun x ↦ ((n - p : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) * p) *
        ((n : ℝ) * matrixQuadraticForm (S x)⁻¹ (sampleMean x - m))) =
        (fun z : EuclideanSpace ℝ (Fin p) × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          ((n - 1 - p + 1 : ℕ) : ℝ) / p *
            matrixQuadraticForm (z.2 : Matrix (Fin p) (Fin p) ℝ)⁻¹ z.1) ∘
          (fun x ↦ (U x, TauCeti.Probability.wishartGram (Y x))) := by
      funext x
      have hsq : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      simp only [Function.comp_apply, S, hmean x, hscat x, add_sub_cancel_left,
        matrix_inv_smul_of_ne_zero (inv_ne_zero hν0), inv_inv, matrix_quadratic_form_smul_smul, hsq,
        show n - 1 - p + 1 = n - p by omega]
      field_simp
    have hjoint : P.map (fun x ↦ (U x, TauCeti.Probability.wishartGram (Y x))) =
        (multivariateGaussian 0 Sigma).prod
          (TauCeti.Probability.wishartGramMeasure (n - 1) Sigma) := by
      have hg : Measurable fun z : (Fin (n - 1) → EuclideanSpace ℝ (Fin p)) ×
          EuclideanSpace ℝ (Fin p) ↦ (z.2, TauCeti.Probability.wishartGram z.1) :=
        measurable_snd.prodMk (TauCeti.Probability.measurable_wishartGram.comp measurable_fst)
      rw [show (fun x ↦ (U x, TauCeti.Probability.wishartGram (Y x))) =
          (fun z : (Fin (n - 1) → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) ↦
            (z.2, TauCeti.Probability.wishartGram z.1)) ∘ (fun x ↦ (Y x, U x)) from rfl,
        ← Measure.map_map hg hpm, hlaw, TauCeti.Probability.wishartGramMeasure_eq_map_pi]
      have h2 := Measure.map_prod_map (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) Sigma)
        (Measure.pi fun _ : Fin (n - 1) ↦ multivariateGaussian 0 Sigma) measurable_id
        TauCeti.Probability.measurable_wishartGram
      rw [Measure.map_id] at h2
      rw [h2, ← Measure.prod_swap, Measure.map_map hg measurable_swap]
      rfl
    rw [hstat, ← Measure.map_map (by exact (measurable_const.mul
        measurable_matrix_quadratic_form_inv)) (hU.prodMk hWm), hjoint,
      map_hotelling_multivariate_gaussian_wishart_gram_measure hp (by omega) hS,
      show n - 1 - p + 1 = n - p by omega]

/-- The spectral inequality `log det A ≤ tr A - dim` for a positive-definite real matrix,
together with its equality case `A = 1`. -/
private theorem log_det_le_trace_sub_card_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι ∧
      (Real.log A.det = A.trace - Fintype.card ι ↔ A = 1) := by
  classical
  have hlog : Real.log A.det = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod fun i _ ↦ (hA.eigenvalues_pos i).ne'
  have htrace : A.trace - Fintype.card ι = ∑ i, (hA.isHermitian.eigenvalues i - 1) := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Finset.sum_sub_distrib]
    simp
  have hle : ∀ i ∈ Finset.univ, Real.log (hA.isHermitian.eigenvalues i) ≤
      hA.isHermitian.eigenvalues i - 1 := fun i _ ↦ Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
  refine ⟨by rw [hlog, htrace]; exact Finset.sum_le_sum hle, ?_⟩
  constructor
  · intro he
    rw [hlog, htrace] at he
    have hi := Finset.sum_eq_sum_iff_of_le hle |>.mp he
    have hone : ∀ i, hA.isHermitian.eigenvalues i = 1 := by
      intro i
      by_contra hne
      exact (Real.log_lt_sub_one_of_pos (hA.eigenvalues_pos i) hne).ne (hi i (Finset.mem_univ _))
    rw [hA.isHermitian.spectral_theorem]
    have hfun : hA.isHermitian.eigenvalues = fun _ ↦ 1 := funext hone
    simp [hfun]
  · rintro rfl
    simp

/-- The spectral inequality `log det A ≤ tr A - dim` for a positive-definite real matrix. -/
theorem log_det_le_trace_sub_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι :=
  (log_det_le_trace_sub_card_aux A hA).1

/-- Equality holds in `log det A ≤ tr A - dim` for a positive-definite real matrix exactly at the
identity. -/
theorem log_det_eq_trace_sub_card_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Real.log A.det = A.trace - Fintype.card ι ↔ A = 1 :=
  (log_det_le_trace_sub_card_aux A hA).2

/-- The Gaussian covariance criterion `log det C + tr(S C⁻¹)` is uniquely minimized at `C = S`
when both covariance matrices are positive definite. -/
private theorem log_det_add_trace_mul_inv_aux {p : ℕ}
    (S C : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef) (hC : C.PosDef) :
    Real.log S.det + p ≤ Real.log C.det + (S * C⁻¹).trace ∧
      (Real.log S.det + p = Real.log C.det + (S * C⁻¹).trace ↔ C = S) := by
  let R := (CFC.sqrt C)⁻¹
  have hRt := transpose_inv_sqrt_of_pos_semidef hC.posSemidef
  have hRR := inv_sqrt_mul_inv_sqrt_of_pos_semidef hC.posSemidef
  have hRu := is_unit_det_inv_sqrt_of_pos_def hC
  have hRC := inv_sqrt_mul_mul_inv_sqrt_of_pos_def hC
  have hRunit : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).2 hRu
  have hT : (R * S * R).PosDef := by
    have h := hS.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hRunit)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hRt] at h
  have hle := log_det_le_trace_sub_card _ hT
  have heq := log_det_eq_trace_sub_card_iff _ hT
  have htr : (R * S * R).trace = (S * C⁻¹).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  have hd : (R * S * R).det = S.det / C.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc R.det * S.det * R.det = (R.det * R.det) * S.det := by ring
      _ = C⁻¹.det * S.det := by rw [← Matrix.det_mul, hRR]
      _ = S.det / C.det := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; ring
  have hlog : Real.log (R * S * R).det = Real.log S.det - Real.log C.det := by
    rw [hd, Real.log_div hS.det_pos.ne' hC.det_pos.ne']
  have hteq : R * S * R = 1 ↔ C = S := by
    constructor
    · intro he
      have hsame : R * S * R = R * C * R := he.trans hRC.symm
      exact (hRunit.mul_right_inj.mp (hRunit.mul_left_inj.mp hsame)).symm
    · rintro rfl
      exact hRC
  simp only [Fintype.card_fin] at hle heq
  rw [htr, hlog] at hle heq
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    exact hteq.1 (heq.1 (by linarith))
  · intro h
    have := heq.2 (hteq.2 h)
    linarith

/-- The Gaussian covariance criterion `log det C + tr(S C⁻¹)` is at least its value
`log det S + p` at `C = S`, for positive definite `S` and `C`. -/
theorem log_det_add_card_le_log_det_add_trace_mul_inv {p : ℕ}
    (S C : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef) (hC : C.PosDef) :
    Real.log S.det + p ≤ Real.log C.det + (S * C⁻¹).trace :=
  (log_det_add_trace_mul_inv_aux S C hS hC).1

/-- The Gaussian covariance criterion `log det C + tr(S C⁻¹)` attains its minimum
`log det S + p` only at `C = S`, for positive definite `S` and `C`. -/
theorem log_det_add_card_eq_log_det_add_trace_mul_inv_iff {p : ℕ}
    (S C : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef) (hC : C.PosDef) :
    Real.log S.det + p = Real.log C.det + (S * C⁻¹).trace ↔ C = S :=
  (log_det_add_trace_mul_inv_aux S C hS hC).2

/-- The Euclidean quadratic form agrees with the coordinate dot product. -/
theorem matrix_quadratic_form_eq_dot_product {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    matrixQuadraticForm A v = (A *ᵥ (v : Fin p → ℝ)) ⬝ᵥ (v : Fin p → ℝ) := by
  simp [matrixQuadraticForm, Matrix.toEuclideanCLM_apply,
    EuclideanSpace.inner_eq_star_dotProduct]

/-- A nonempty finite sample has zero sum of deviations from its sample mean. -/
theorem sum_sub_sample_mean_eq_zero {n p : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    ∑ i, (x i - sampleMean x) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [sampleMean, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn.ne']

/-- Centering a quadratic sum at the sample mean separates its location error. -/
theorem sum_matrix_quadratic_form_sub_eq {n p : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (m : EuclideanSpace ℝ (Fin p))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ∑ i, matrixQuadraticForm A (x i - m) =
      (∑ i, matrixQuadraticForm A (x i - sampleMean x)) +
        n * matrixQuadraticForm A (sampleMean x - m) := by
  have hx : ∀ i, x i - m = (x i - sampleMean x) + (sampleMean x - m) := fun i ↦ by abel
  simp_rw [hx, matrixQuadraticForm, map_add, inner_add_left, inner_add_right]
  simp only [Finset.sum_add_distrib, ← sum_inner, ← inner_sum, ← map_sum,
    sum_sub_sample_mean_eq_zero hn x, map_zero, inner_zero_right, inner_zero_left, add_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]

/-- A centered quadratic sum is the trace pairing of the scatter matrix and its coefficient. -/
theorem sum_matrix_quadratic_form_sub_sample_mean_eq_trace {n p : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (A : Matrix (Fin p) (Fin p) ℝ) :
    (∑ i, matrixQuadraticForm A (x i - sampleMean x)) = (scatterMatrix x * A).trace := by
  have hs : scatterMatrix x = ∑ i, Matrix.vecMulVec
      ((x i - sampleMean x) : Fin p → ℝ) ((x i - sampleMean x) : Fin p → ℝ) := by
    ext j k
    simp [scatterMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply]
  rw [Matrix.trace_mul_comm, hs, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, matrix_quadratic_form_eq_dot_product]
  rfl

/-- A positive-definite real matrix has a positive quadratic form on every nonzero vector. -/
theorem matrix_quadratic_form_pos {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (hv : v ≠ 0) : 0 < matrixQuadraticForm A v := by
  rw [matrix_quadratic_form_eq_dot_product, dotProduct_comm]
  have hv' : (v : Fin p → ℝ) ≠ 0 := by
    intro hvz
    apply hv
    apply WithLp.ofLp_injective 2
    exact hvz
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv'

/-- The Gaussian negative log-likelihood of a sample with positive definite sample covariance
`S = n⁻¹ ∑ᵢ (xᵢ - x̄)(xᵢ - x̄)ᵀ` is at least its value at `(x̄, S)`, with equality only there.
The sample may be empty: then `S` is positive definite only in dimension zero. -/
private theorem gaussian_neg_log_likelihood_aux {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p))
    (hS : ((n : ℝ)⁻¹ • scatterMatrix x).PosDef) (m : EuclideanSpace ℝ (Fin p))
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.PosDef) :
    gaussianNegLogLikelihood x (sampleMean x) ((n : ℝ)⁻¹ • scatterMatrix x) ≤
        gaussianNegLogLikelihood x m C ∧
      (gaussianNegLogLikelihood x (sampleMean x) ((n : ℝ)⁻¹ • scatterMatrix x) =
          gaussianNegLogLikelihood x m C ↔
        m = sampleMean x ∧ C = (n : ℝ)⁻¹ • scatterMatrix x) := by
  set S := (n : ℝ)⁻¹ • scatterMatrix x with hSdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- an empty sample: `S = 0` is positive definite only when `p = 0`
    have h0 : S = 0 := by simp [S]
    obtain rfl : p = 0 := by
      by_contra hp
      have : Nonempty (Fin p) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hp)
      have h := (h0 ▸ hS).det_pos
      rw [Matrix.det_zero] at h
      exact lt_irrefl _ h
    have hm : m = sampleMean x := Subsingleton.elim _ _
    have hCS : C = S := Subsingleton.elim _ _
    subst hm hCS
    exact ⟨le_rfl, iff_of_true rfl ⟨rfl, rfl⟩⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : scatterMatrix x = (n : ℝ) • S := by
    simp [S, smul_smul, hn'.ne']
  have hsum : ∀ m C, (∑ i, matrixQuadraticForm C⁻¹ (x i - m)) =
      n * ((S * C⁻¹).trace + matrixQuadraticForm C⁻¹ (sampleMean x - m)) := by
    intro m C
    rw [sum_matrix_quadratic_form_sub_eq hn x m C⁻¹, sum_matrix_quadratic_form_sub_sample_mean_eq_trace x C⁻¹,
      hs, Matrix.smul_mul, Matrix.trace_smul]
    simp only [smul_eq_mul]
    ring
  have hNLL : ∀ m C, gaussianNegLogLikelihood x m C = (n : ℝ) / 2 *
      (Real.log C.det + (S * C⁻¹).trace + matrixQuadraticForm C⁻¹ (sampleMean x - m)) := by
    intro m C
    unfold gaussianNegLogLikelihood
    rw [hsum]
    ring
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).1 hS.isUnit)
  have hbase : gaussianNegLogLikelihood x (sampleMean x) S =
      (n : ℝ) / 2 * (Real.log S.det + p) := by
    rw [hNLL]
    simp [hSS, matrixQuadraticForm]
  have hcrit := log_det_add_card_le_log_det_add_trace_mul_inv S C hS hC
  have hcrit_eq := log_det_add_card_eq_log_det_add_trace_mul_inv_iff S C hS hC
  have hq : 0 ≤ matrixQuadraticForm C⁻¹ (sampleMean x - m) := by
    by_cases he : sampleMean x - m = 0
    · simp [he, matrixQuadraticForm]
    · exact (matrix_quadratic_form_pos C⁻¹ hC.inv _ he).le
  rw [hbase, hNLL]
  refine ⟨mul_le_mul_of_nonneg_left (by linarith) (by positivity), ?_⟩
  constructor
  · intro he
    have he' := (mul_left_cancel₀ (show (n : ℝ) / 2 ≠ 0 by positivity) he)
    have hqz : matrixQuadraticForm C⁻¹ (sampleMean x - m) = 0 := by linarith
    have hm : m = sampleMean x := by
      by_contra hne
      have hv : sampleMean x - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      exact (matrix_quadratic_form_pos C⁻¹ hC.inv _ hv).ne' hqz
    exact ⟨hm, hcrit_eq.1 (by linarith)⟩
  · rintro ⟨rfl, rfl⟩
    simp [hSS, matrixQuadraticForm]

/-- GAPS 105.28: the Gaussian negative log-likelihood of a sample whose sample covariance
`S = n⁻¹ ∑ᵢ (xᵢ - x̄)(xᵢ - x̄)ᵀ` is positive definite is minimized, over all means `m` and positive
definite covariances `C`, at `(x̄, S)`. -/
theorem gaussian_neg_log_likelihood_sample_mean_le {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p))
    (hS : ((n : ℝ)⁻¹ • scatterMatrix x).PosDef) (m : EuclideanSpace ℝ (Fin p))
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.PosDef) :
    gaussianNegLogLikelihood x (sampleMean x) ((n : ℝ)⁻¹ • scatterMatrix x) ≤
      gaussianNegLogLikelihood x m C :=
  (gaussian_neg_log_likelihood_aux x hS m C hC).1

/-- GAPS 105.28: the minimizer of the Gaussian negative log-likelihood is unique: for a sample
whose sample covariance `S` (divisor `n`) is positive definite, the value at `(m, C)`, `C`
positive definite, equals the value at `(x̄, S)` only if `m = x̄` and `C = S`. -/
theorem gaussian_neg_log_likelihood_eq_iff {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p))
    (hS : ((n : ℝ)⁻¹ • scatterMatrix x).PosDef) (m : EuclideanSpace ℝ (Fin p))
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.PosDef) :
    gaussianNegLogLikelihood x (sampleMean x) ((n : ℝ)⁻¹ • scatterMatrix x) =
        gaussianNegLogLikelihood x m C ↔
      m = sampleMean x ∧ C = (n : ℝ)⁻¹ • scatterMatrix x :=
  (gaussian_neg_log_likelihood_aux x hS m C hC).2

/-- GAPS 105.31: for `p ≤ n` and positive definite `Σ`, the determinant of a Wishart matrix
`W ∼ W_p(n, Σ)` has the law of `det Σ · ∏_{i<p} χ²_{n-i}` with independent chi-squared factors
(Bartlett's decomposition). -/
theorem wishart_determinant_law {p : ℕ} (n : ℕ) (hn : p ≤ n)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hS : Sigma.PosDef) :
    (TauCeti.Probability.wishartGramMeasure n Sigma).map (fun W ↦ Matrix.det W.val) =
      (Measure.pi (fun i : Fin p ↦ TauCeti.Probability.chiSquaredMeasure (n - i.val : ℕ))).map
        (fun z ↦ Sigma.det * ∏ i, z i) := by
  rw [TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS hn]
  have hdeg : (p : ℝ) - 1 < n := by
    have : (p : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hcast : ∀ i : Fin p, ((n - i.val : ℕ) : ℝ) = (n : ℝ) - i.val :=
    fun i ↦ Nat.cast_sub (by omega)
  simpa only [hcast] using TauCeti.Probability.map_det_nonsingularWishartMeasure hS hdeg

/-- The sample correlation statistic `√(N - 2) r / √(1 - r²)` of paired samples `x`, `y`. -/
private noncomputable def correlationStat (N : ℕ) (x y : Fin N → ℝ) : ℝ :=
  let a := (∑ i, x i) / N
  let b := (∑ i, y i) / N
  let r := (∑ i, (x i - a) * (y i - b)) /
    Real.sqrt ((∑ i, (x i - a) ^ 2) * (∑ i, (y i - b) ^ 2))
  Real.sqrt (N - 2 : ℕ) * r / Real.sqrt (1 - r ^ 2)

/-- The sample correlation statistic is jointly measurable in the two samples. -/
private theorem measurable_correlation_stat (N : ℕ) :
    Measurable (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ correlationStat N z.1 z.2) := by
  unfold correlationStat
  fun_prop

/-- The sample correlation statistic is measurable in the first sample. -/
private theorem measurable_correlation_stat_left (N : ℕ) (y : Fin N → ℝ) :
    Measurable (fun x ↦ correlationStat N x y) := by
  unfold correlationStat
  fun_prop

/-- The Euclidean inner product in coordinates. -/
private theorem inner_to_lp_eq_sum {N : ℕ} (f g : Fin N → ℝ) :
    inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 g) = ∑ i, f i * g i := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

/-- The algebraic core: with `Z = ⟨u, x⟩` and `V = ∑ (xᵢ - x̄)² - Z²`, the statistic equals
`Z / √(V / (N - 2))`. -/
private theorem correlation_stat_eq {N : ℕ} (x y : Fin N → ℝ) (s Z V : ℝ) (hs : 0 < s)
    (hyy : ∑ i, (y i - (∑ j, y j) / N) ^ 2 = s ^ 2)
    (hxy : ∑ i, (x i - (∑ j, x j) / N) * (y i - (∑ j, y j) / N) = s * Z)
    (hV : V = ∑ i, (x i - (∑ j, x j) / N) ^ 2 - Z ^ 2) (hV0 : 0 ≤ V) :
    correlationStat N x y = Z / Real.sqrt (V / (N - 2 : ℕ)) := by
  unfold correlationStat
  simp only
  set Sxx := ∑ i, (x i - (∑ j, x j) / N) ^ 2 with hSxx
  rw [hyy, hxy]
  have hS0 : 0 ≤ Sxx := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  rw [Real.sqrt_mul hS0, Real.sqrt_sq hs.le]
  rcases hS0.eq_or_lt with h0 | hpos
  · have hZ : Z = 0 := by nlinarith [sq_nonneg Z]
    simp [hZ]
  set q := Real.sqrt Sxx with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hpos
  have hqq : q ^ 2 = Sxx := Real.sq_sqrt hS0
  have hr : s * Z / (q * s) = Z / q := by field_simp
  rw [hr]
  have h1 : 1 - (Z / q) ^ 2 = V / q ^ 2 := by
    rw [hV, ← hqq]
    field_simp
  rw [h1, Real.sqrt_div hV0, Real.sqrt_sq hq0.le]
  rcases hV0.eq_or_lt with hV0' | hVpos
  · simp [← hV0']
  have hk : (0 : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_div hV0]
  rcases hk.eq_or_lt with hk0 | hkpos
  · rw [← hk0]
    simp
  have hsv : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
  have hsk : 0 < Real.sqrt ((N - 2 : ℕ) : ℝ) := Real.sqrt_pos.2 hkpos
  field_simp


/-- For a fixed non-constant second sample `y`, the statistic of a standard Gaussian first
sample has Student's law with `N - 2` degrees of freedom. -/
private theorem map_correlation_stat_left {N : ℕ} (hN : 2 < N) (y : Fin N → ℝ)
    (hy : (fun i ↦ y i - (∑ j, y j) / N) ≠ 0) :
    (Measure.pi fun _ : Fin N ↦ gaussianReal 0 1).map (fun x ↦ correlationStat N x y) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) := by
  set μ := Measure.pi fun _ : Fin N ↦ gaussianReal 0 1
  set yc : Fin N → ℝ := fun i ↦ y i - (∑ j, y j) / N with hyc
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hsum_yc : ∑ i, yc i = 0 := by
    simp only [yc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  set s := Real.sqrt (∑ i, yc i ^ 2) with hsdef
  have hss : 0 < ∑ i, yc i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hi' : yc i ≠ 0 := by simpa [yc] using hi
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i ↦ yc i ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i))
  have hs : 0 < s := Real.sqrt_pos.2 hss
  have hs2 : s ^ 2 = ∑ i, yc i ^ 2 := Real.sq_sqrt hss.le
  let E := EuclideanSpace ℝ (Fin N)
  let e1 : E := WithLp.toLp 2 fun _ ↦ (Real.sqrt N)⁻¹
  let u : E := WithLp.toLp 2 fun i ↦ s⁻¹ * yc i
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
  have hsN0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have he1 : inner ℝ e1 e1 = 1 := by
    rw [inner_to_lp_eq_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    exact hsN.symm
  have hu : inner ℝ u u = 1 := by
    rw [inner_to_lp_eq_sum]
    have : ∑ i, s⁻¹ * yc i * (s⁻¹ * yc i) = (∑ i, yc i ^ 2) / s ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    rw [this, hs2, div_self hss.ne']
  have he1u : inner ℝ e1 u = 0 := by
    rw [inner_to_lp_eq_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum_yc]
    simp
  -- the subspaces `span {u}` and `span {e₁, u}ᗮ`
  let S2 : Submodule ℝ E := Submodule.span ℝ {e1, u}
  let K : Submodule ℝ E := Submodule.span ℝ {u}
  let L : Submodule ℝ E := S2ᗮ
  have hKS : K ≤ S2 := Submodule.span_mono (by simp)
  have hKL : K ⟂ L := (Submodule.isOrtho_orthogonal_right S2).mono_left hKS
  have hne1 : ‖e1‖ = 1 := by
    have h := real_inner_self_eq_norm_sq e1
    rw [he1] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h.symm)
  have hnu : ‖u‖ = 1 := by
    have h := real_inner_self_eq_norm_sq u
    rw [hu] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h.symm)
  have hON : Orthonormal ℝ ![e1, u] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hne1, hnu, he1u, real_inner_comm]
  have hfin2 : Module.finrank ℝ S2 = 2 := by
    have := finrank_span_eq_card hON.linearIndependent
    have hr : Set.range ![e1, u] = {e1, u} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hr] at this
    simpa using this
  have hfinL : Module.finrank ℝ L = N - 2 := by
    show Module.finrank ℝ S2ᗮ = N - 2
    have := Submodule.finrank_add_finrank_orthogonal S2
    rw [hfin2, finrank_euclideanSpace_fin] at this
    omega
  have hproj : ∀ X : E, L.starProjection X = X - inner ℝ e1 X • e1 - inner ℝ u X • u := by
    intro X
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_
    · rw [Submodule.mem_orthogonal]
      intro v hv
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hv
      simp only [inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right, he1, hu,
        he1u, real_inner_comm e1 u, RCLike.conj_to_real]
      ring
    · have hmem : inner ℝ e1 X • e1 + inner ℝ u X • u ∈ S2 :=
        S2.add_mem (S2.smul_mem _ (Submodule.subset_span (by simp)))
          (S2.smul_mem _ (Submodule.subset_span (by simp)))
      rw [show X - (X - inner ℝ e1 X • e1 - inner ℝ u X • u) =
        inner ℝ e1 X • e1 + inner ℝ u X • u by abel]
      exact Submodule.inner_right_of_mem_orthogonal hmem hw
  have hnormL : ∀ X : E, ‖L.orthogonalProjectionOnto X‖ ^ 2 =
      inner ℝ X X - inner ℝ e1 X ^ 2 - inner ℝ u X ^ 2 := by
    intro X
    rw [← Submodule.norm_coe, ← Submodule.starProjection_apply, hproj, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, he1, hu,
      he1u, real_inner_comm e1 u, real_inner_comm X e1, real_inner_comm X u, RCLike.conj_to_real]
    ring
  -- the standardized sample and the two independent pieces
  let Y : (Fin N → ℝ) → E := fun x ↦ WithLp.toLp 2 x
  have hY : HasLaw Y (stdGaussian E) μ := by
    have h := has_law_standardize_pi_gaussian_real N 0 1 one_pos
    have hf : (fun x : Fin N → ℝ ↦ (WithLp.toLp 2 (fun i ↦ (x i - 0) / Real.sqrt ((1 : ℝ≥0) : ℝ)) :
        EuclideanSpace ℝ (Fin N))) = Y := by
      funext x
      simp [Y]
    rwa [hf] at h
  let Zf : (Fin N → ℝ) → ℝ := fun x ↦ inner ℝ u (Y x)
  let Vf : (Fin N → ℝ) → ℝ := fun x ↦ ‖L.orthogonalProjectionOnto (Y x)‖ ^ 2
  have hZ : HasLaw Zf (gaussianReal 0 1) μ :=
    HasLaw.comp ⟨by fun_prop, std_gaussian_map_inner_of_norm_eq_one u hnu⟩ hY
  have hV : HasLaw Vf (TauCeti.Probability.chiSquaredMeasure (N - 2 : ℕ)) μ := by
    have := hY.norm_sq_orthogonalProjectionOnto_stdGaussian L
    rwa [hfinL] at this
  have hK2 : Pairwise fun i j : Bool ↦ (bif i then K else L) ⟂ (bif j then K else L) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact hKL.symm
    · exact hKL
    · exact absurd rfl hij
  have hTF : IndepFun (fun x ↦ K.orthogonalProjectionOnto (Y x))
      (fun x ↦ L.orthogonalProjectionOnto (Y x)) μ :=
    (hY.iIndepFun_orthogonalProjectionOnto_stdGaussian (fun b ↦ bif b then K else L) hK2).indepFun
      (i := true) (j := false) (by decide)
  have hZV : IndepFun Zf Vf μ := by
    have := hTF.comp (φ := fun z : K ↦ inner ℝ u (z : E)) (ψ := fun z : L ↦ ‖z‖ ^ 2)
      (by fun_prop) (by fun_prop)
    convert this using 1
    · funext x
      simp only [Function.comp_apply, Zf]
      rw [Submodule.coe_orthogonalProjectionOnto_apply,
        ← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 (Submodule.mem_span_singleton_self u)]
    · rfl
  have hν : (0 : ℝ) < ((N - 2 : ℕ) : ℝ) := by
    have : 1 ≤ N - 2 := by omega
    exact_mod_cast this
  rw [← (TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared hν hZV hZ hV).map_eq]
  congr 1
  funext x
  have hZx : Zf x = ∑ i, s⁻¹ * yc i * x i := inner_to_lp_eq_sum _ _
  have hxx : inner ℝ (Y x) (Y x) = ∑ i, x i * x i := inner_to_lp_eq_sum _ _
  have he1x : inner ℝ e1 (Y x) = ∑ i, (Real.sqrt N)⁻¹ * x i := inner_to_lp_eq_sum _ _
  refine correlation_stat_eq x y s (Zf x) (Vf x) hs hs2.symm ?_ ?_ (by positivity)
  · show ∑ i, (x i - (∑ j, x j) / N) * yc i = _
    rw [hZx, Finset.mul_sum]
    have : ∀ i, (x i - (∑ j, x j) / N) * yc i = s * (s⁻¹ * yc i * x i) -
        (∑ j, x j) / N * yc i := fun i ↦ by
      rw [← mul_assoc s, ← mul_assoc s, mul_inv_cancel₀ hs.ne', one_mul]
      ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_yc, mul_zero, sub_zero]
  · simp only [Vf, hnormL, hxx, he1x, ← Finset.mul_sum, sub_sq, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    field_simp
    rw [hsN]
    ring

/-- A standard Gaussian sample of size `N ≥ 2` is almost surely non-constant. -/
private theorem ae_sub_mean_ne_zero {N : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ y ∂(Measure.pi fun _ : Fin N ↦ gaussianReal 0 1),
      (fun i ↦ y i - (∑ j, y j) / (N : ℝ)) ≠ 0 := by
  set μ := Measure.pi fun _ : Fin N ↦ gaussianReal 0 1
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let E := EuclideanSpace ℝ (Fin N)
  let w : E := (Real.sqrt 2)⁻¹ • (EuclideanSpace.single i0 1 - EuclideanSpace.single i1 1)
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hw : ‖w‖ = 1 := by
    have h2 : ‖EuclideanSpace.single i0 (1 : ℝ) - EuclideanSpace.single i1 1‖ = Real.sqrt 2 := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      rw [Fintype.sum_eq_add_sum_compl i0, Finset.sum_eq_single i1]
      · simp [h01, h01.symm]
        norm_num
      · intro j _ hj
        have hj0 : j ≠ i0 := Finset.notMem_singleton.1 (Finset.mem_compl.1 ‹_›)
        simp [hj, hj0]
      · simp [h01.symm]
    rw [norm_smul, h2, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity),
      inv_mul_cancel₀ (by positivity)]
  have hY := has_law_standardize_pi_gaussian_real N 0 1 one_pos
  have hf : (fun x : Fin N → ℝ ↦ (WithLp.toLp 2 (fun i ↦ (x i - 0) / Real.sqrt ((1 : ℝ≥0) : ℝ)) :
      EuclideanSpace ℝ (Fin N))) = fun x ↦ WithLp.toLp 2 x := by
    funext x
    simp
  rw [hf] at hY
  have hZ : HasLaw (fun x : Fin N → ℝ ↦ inner ℝ w (WithLp.toLp 2 x : E)) (gaussianReal 0 1) μ :=
    HasLaw.comp ⟨by fun_prop, std_gaussian_map_inner_of_norm_eq_one w hw⟩ hY
  have h0 : μ ((fun x : Fin N → ℝ ↦ inner ℝ w (WithLp.toLp 2 x : E)) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hZ.aemeasurable (measurableSet_singleton 0),
      hZ.map_eq]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton 0
  refine measure_mono_null (fun y hy ↦ ?_) h0
  have hy' : (fun i ↦ y i - (∑ j, y j) / (N : ℝ)) = 0 := not_not.1 hy
  have h1 := congrFun hy' i0
  have h2 := congrFun hy' i1
  simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
  simp only [Set.mem_preimage, Set.mem_singleton_iff, w, inner_smul_left, inner_sub_left]
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp [h1, h2]

/-- GAPS 105.32: for `N > 2` independent pairs of independent standard normal variables, the
sample correlation coefficient `r` satisfies `√(N - 2) r / √(1 - r²) ∼ t_{N-2}`. -/
theorem gaussian_sample_correlation_student_law (N : ℕ) (hN : 2 < N) :
    let P := Measure.pi (fun _ : Fin N ↦ (gaussianReal 0 1).prod (gaussianReal 0 1));
    let a := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).1) / N;
    let b := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).2) / N;
    let r := fun x : Fin N → ℝ × ℝ ↦
      (∑ i, ((x i).1 - a x) * ((x i).2 - b x)) /
        Real.sqrt ((∑ i, ((x i).1 - a x) ^ 2) * (∑ i, ((x i).2 - b x) ^ 2));
    P.map (fun x ↦ Real.sqrt (N - 2 : ℕ) * r x / Real.sqrt (1 - r x ^ 2)) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) := by
  intro P a b r
  set μ := Measure.pi fun _ : Fin N ↦ gaussianReal 0 1
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)
  let F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun z ↦ correlationStat N z.1 z.2
  have hF : Measurable F := measurable_correlation_stat N
  have hfun : (fun x ↦ Real.sqrt (N - 2 : ℕ) * r x / Real.sqrt (1 - r x ^ 2)) = F ∘ e := rfl
  have he : P.map e = μ.prod μ :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ ↦ gaussianReal 0 1)
      (fun _ ↦ gaussianReal 0 1)).map_eq
  rw [hfun, ← Measure.map_map hF e.measurable, he]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply_symm (hF hs)]
  have hae : ∀ᵐ y ∂μ, μ ((fun x ↦ (x, y)) ⁻¹' (F ⁻¹' s)) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) s := by
    filter_upwards [ae_sub_mean_ne_zero hN.le] with y hy
    rw [← map_correlation_stat_left hN y hy,
      Measure.map_apply (measurable_correlation_stat_left N y) hs]
    rfl
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

end CKSD
