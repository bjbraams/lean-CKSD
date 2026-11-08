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

/-!
# LinearModels: Multivariate

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
The determinant law uses TauCeti's Wishart agreement and determinant theorems.
The Gaussian likelihood minimum uses Mathlib’s Hermitian spectral theorem and the scalar
inequality `Real.log_le_sub_one_of_pos`, together with its strict equality case.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
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

/-- GAPS 105.22, normal sample mean/covariance independence and Hotelling's exact law. -/
theorem gaussian_sampleMean_scatterMatrix_wishart_and_hotelling
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
  sorry

/-- The spectral inequality `log det A ≤ tr A - dim` for a positive-definite real matrix,
with equality exactly at the identity. -/
theorem log_det_le_trace_sub_card_and_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
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
/-- The Gaussian covariance criterion `log det C + tr(S C⁻¹)` is uniquely minimized at `C = S`
when both covariance matrices are positive definite. -/
theorem log_det_add_trace_mul_inv_minimum_unique {p : ℕ}
    (S C : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef) (hC : C.PosDef) :
    Real.log S.det + p ≤ Real.log C.det + (S * C⁻¹).trace ∧
      (Real.log S.det + p = Real.log C.det + (S * C⁻¹).trace ↔ C = S) := by
  let R := (CFC.sqrt C)⁻¹
  obtain ⟨hRt, hRR⟩ := PosDef.inv_sqrt_facts hC
  have hRu := PosDef.isUnit_det_inv_sqrt hC
  have hRC := PosDef.inv_sqrt_mul_mul_inv_sqrt hC
  have hRunit : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).2 hRu
  have hT : (R * S * R).PosDef := by
    have h := hS.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hRunit)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hRt] at h
  obtain ⟨hle, heq⟩ := log_det_le_trace_sub_card_and_eq_iff _ hT
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
/-- The Euclidean quadratic form agrees with the coordinate dot product. -/
theorem matrixQuadraticForm_eq_dotProduct {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    matrixQuadraticForm A v = (A *ᵥ (v : Fin p → ℝ)) ⬝ᵥ (v : Fin p → ℝ) := by
  simp [matrixQuadraticForm, Matrix.toEuclideanCLM_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
/-- A nonempty finite sample has zero sum of deviations from its sample mean. -/
theorem sum_sub_sampleMean_eq_zero {n p : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    ∑ i, (x i - sampleMean x) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [sampleMean, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn.ne']

/-- Centering a quadratic sum at the sample mean separates its location error. -/
theorem sum_matrixQuadraticForm_sub_eq {n p : ℕ} (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (m : EuclideanSpace ℝ (Fin p))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ∑ i, matrixQuadraticForm A (x i - m) =
      (∑ i, matrixQuadraticForm A (x i - sampleMean x)) +
        n * matrixQuadraticForm A (sampleMean x - m) := by
  have hx : ∀ i, x i - m = (x i - sampleMean x) + (sampleMean x - m) := fun i ↦ by abel
  simp_rw [hx, matrixQuadraticForm, map_add, inner_add_left, inner_add_right]
  simp only [Finset.sum_add_distrib, ← sum_inner, ← inner_sum, ← map_sum,
    sum_sub_sampleMean_eq_zero hn x, map_zero, inner_zero_right, inner_zero_left, add_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]

/-- A centered quadratic sum is the trace pairing of the scatter matrix and its coefficient. -/
theorem sum_matrixQuadraticForm_sub_sampleMean_eq_trace {n p : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (A : Matrix (Fin p) (Fin p) ℝ) :
    (∑ i, matrixQuadraticForm A (x i - sampleMean x)) = (scatterMatrix x * A).trace := by
  have hs : scatterMatrix x = ∑ i, Matrix.vecMulVec
      ((x i - sampleMean x) : Fin p → ℝ) ((x i - sampleMean x) : Fin p → ℝ) := by
    ext j k
    simp [scatterMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply]
  rw [Matrix.trace_mul_comm, hs, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, matrixQuadraticForm_eq_dotProduct]
  rfl
/-- A positive-definite real matrix has a positive quadratic form on every nonzero vector. -/
theorem matrixQuadraticForm_pos {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (hv : v ≠ 0) : 0 < matrixQuadraticForm A v := by
  rw [matrixQuadraticForm_eq_dotProduct, dotProduct_comm]
  have hv' : (v : Fin p → ℝ) ≠ 0 := by
    intro hvz
    apply hv
    apply WithLp.ofLp_injective 2
    exact hvz
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv'


/-- GAPS 105.28, the full-rank Gaussian covariance likelihood has a unique minimum. -/
theorem gaussianNegLogLikelihood_minimum_unique
    {n p : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    let S := (n : ℝ)⁻¹ • scatterMatrix x;
    ∀ (hS : S.PosDef),
    ∀ (m : EuclideanSpace ℝ (Fin p)),
    ∀ (C : Matrix (Fin p) (Fin p) ℝ),
    ∀ (hC : C.PosDef),
    gaussianNegLogLikelihood x (sampleMean x) S ≤ gaussianNegLogLikelihood x m C ∧
      (gaussianNegLogLikelihood x (sampleMean x) S = gaussianNegLogLikelihood x m C ↔ m = sampleMean x ∧ C = S) := by
  intro S hS m C hC
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : scatterMatrix x = (n : ℝ) • S := by
    simp [S, smul_smul, hn'.ne']
  have hsum : ∀ m C, (∑ i, matrixQuadraticForm C⁻¹ (x i - m)) =
      n * ((S * C⁻¹).trace + matrixQuadraticForm C⁻¹ (sampleMean x - m)) := by
    intro m C
    rw [sum_matrixQuadraticForm_sub_eq hn x m C⁻¹, sum_matrixQuadraticForm_sub_sampleMean_eq_trace x C⁻¹,
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
  obtain ⟨hcrit, hcrit_eq⟩ := log_det_add_trace_mul_inv_minimum_unique S C hS hC
  have hq : 0 ≤ matrixQuadraticForm C⁻¹ (sampleMean x - m) := by
    by_cases he : sampleMean x - m = 0
    · simp [he, matrixQuadraticForm]
    · exact (matrixQuadraticForm_pos C⁻¹ hC.inv _ he).le
  rw [hbase, hNLL]
  refine ⟨mul_le_mul_of_nonneg_left (by linarith) (by positivity), ?_⟩
  constructor
  · intro he
    have he' := (mul_left_cancel₀ (show (n : ℝ) / 2 ≠ 0 by positivity) he)
    have hqz : matrixQuadraticForm C⁻¹ (sampleMean x - m) = 0 := by linarith
    have hm : m = sampleMean x := by
      by_contra hne
      have hv : sampleMean x - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      exact (matrixQuadraticForm_pos C⁻¹ hC.inv _ hv).ne' hqz
    exact ⟨hm, hcrit_eq.1 (by linarith)⟩
  · rintro ⟨rfl, rfl⟩
    simp [hSS, matrixQuadraticForm]

/-- GAPS 105.31, determinant law obtained from Bartlett's decomposition. -/
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

/-- GAPS 105.32, exact correlation t law for independent standard-normal coordinates. -/
theorem gaussian_sample_correlation_student_law (N : ℕ) (hN : 2 < N) :
    let P := Measure.pi (fun _ : Fin N ↦ (gaussianReal 0 1).prod (gaussianReal 0 1));
    let a := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).1) / N;
    let b := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).2) / N;
    let r := fun x : Fin N → ℝ × ℝ ↦
      (∑ i, ((x i).1 - a x) * ((x i).2 - b x)) /
        Real.sqrt ((∑ i, ((x i).1 - a x) ^ 2) * (∑ i, ((x i).2 - b x) ^ 2));
    P.map (fun x ↦ Real.sqrt (N - 2 : ℕ) * r x / Real.sqrt (1 - r x ^ 2)) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) := by
  sorry


end CKSD
