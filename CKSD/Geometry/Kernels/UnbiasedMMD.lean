module

public import CKSD.Geometry.Basic
public import TauCeti.Probability.Moments.Covariance
import CKSD.Asymptotics.MultivariateCLT
import TauCeti.Probability.Distributions.Gaussian.Affine
public import CKSD.Inference.Basic
import CKSD.Asymptotics.Basic
import Mathlib.Probability.StrongLaw

/-!
# Limit laws of the unbiased MMD statistic

Null and alternative limit laws of the unbiased estimator `CKSD.unbiasedSquaredMMD` of the squared
maximum mean discrepancy, for an inner-product kernel `k(x, y) = ⟪φ x, φ y⟫` with a bounded
finite-dimensional feature map `φ`. The proofs reduce the statistic to the feature means and apply
the multivariate central limit theorem.

## Main results

* `CKSD.unbiasedSquaredMMD_inner_eq`: the unbiased squared MMD in terms of the feature means.
* `CKSD.tendstoInDistribution_unbiasedSquaredMMD_null`,
  `CKSD.tendstoInDistribution_unbiasedSquaredMMD_alternative`: null and alternative limit laws of
  the unbiased MMD estimator for a bounded finite-dimensional feature map (GAPS 108.61).

## References

* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*,
  J. Mach. Learn. Res. 13 (2012).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The unbiased squared MMD of an inner-product feature kernel, in terms of the two feature means
`A = n⁻¹ ∑ φ(x_i)` and `B = n⁻¹ ∑ φ(y_i)`: for `n ≥ 2` it is `‖A - B‖²` plus the correction
`(‖A‖² + ‖B‖² - n⁻¹ ∑ (‖φ(x_i)‖² + ‖φ(y_i)‖²)) / (n - 1)`. -/
theorem unbiasedSquaredMMD_inner_eq {X E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (phi : X → E) {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → X) :
    let A := (n : ℝ)⁻¹ • ∑ i, phi (x i)
    let B := (n : ℝ)⁻¹ • ∑ i, phi (y i)
    unbiasedSquaredMMD (fun x y ↦ inner ℝ (phi x) (phi y)) n x y =
      ‖A - B‖ ^ 2 + (‖A‖ ^ 2 + ‖B‖ ^ 2 -
        (n : ℝ)⁻¹ * ∑ i, (‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2)) / (n - 1) := by
  intro A B
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  set SA := ∑ i, phi (x i)
  set SB := ∑ i, phi (y i)
  have hdiag : ∀ (a : Fin n → E), ∑ i, ∑ j, (if i ≠ j then inner ℝ (a i) (a j) else 0) =
      ‖∑ i, a i‖ ^ 2 - ∑ i, ‖a i‖ ^ 2 := by
    intro a
    have h1 : ∑ i, ∑ j, inner ℝ (a i) (a j) = ‖∑ i, a i‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      exact Finset.sum_congr rfl fun i _ ↦ (inner_sum _ _ _).symm
    have h2 : ∀ i, ∑ j, (if i ≠ j then inner ℝ (a i) (a j) else 0) =
        ∑ j, inner ℝ (a i) (a j) - ‖a i‖ ^ 2 := by
      intro i
      rw [← real_inner_self_eq_norm_sq, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add (s := Finset.univ) (a := i) (fun j ↦ inner ℝ (a i) (a j))
          (Finset.mem_univ i)]
      simp only [ne_eq, not_true_eq_false, ite_false, add_zero, add_sub_cancel_right]
      exact Finset.sum_congr rfl fun j hj ↦ by
        rw [ite_eq_left_iff.mpr fun h ↦ absurd (Ne.symm (Finset.ne_of_mem_erase hj)) h]
    simp only [h2, Finset.sum_sub_distrib, h1]
  have hsplit : ∑ i, ∑ j, (if i ≠ j then inner ℝ (phi (x i)) (phi (x j)) +
      inner ℝ (phi (y i)) (phi (y j)) else 0) =
      (‖SA‖ ^ 2 - ∑ i, ‖phi (x i)‖ ^ 2) + (‖SB‖ ^ 2 - ∑ i, ‖phi (y i)‖ ^ 2) := by
    rw [← hdiag (fun i ↦ phi (x i)), ← hdiag (fun i ↦ phi (y i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
  have hcross : ∑ i, ∑ j, inner ℝ (phi (x i)) (phi (y j)) = inner ℝ SA SB := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ ↦ (inner_sum _ _ _).symm
  rw [unbiasedSquaredMMD_def, hsplit, hcross, hcast]
  have hA : A = (n : ℝ)⁻¹ • SA := rfl
  have hB : B = (n : ℝ)⁻¹ • SB := rfl
  rw [hA, hB, ← smul_sub, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity), mul_pow, mul_pow, mul_pow, norm_sub_sq_real,
    Finset.sum_add_distrib]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- For square-integrable `a, b` and independent copies `x, x'` with law `P`, the covariance of
`a(x) - a(x')` and `b(x) - b(x')` is `2 Cov_P(a, b)`. -/
private theorem covariance_sub_prod_self {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (a b : X → ℝ) (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    cov[fun z : X × X ↦ a z.1 - a z.2, fun z ↦ b z.1 - b z.2; P.prod P] = 2 * cov[a, b; P] := by
  have ha1 : MemLp (fun z : X × X ↦ a z.1) 2 (P.prod P) := ha.comp_fst P
  have ha2 : MemLp (fun z : X × X ↦ a z.2) 2 (P.prod P) := ha.comp_snd P
  have hb1 : MemLp (fun z : X × X ↦ b z.1) 2 (P.prod P) := hb.comp_fst P
  have hb2 : MemLp (fun z : X × X ↦ b z.2) 2 (P.prod P) := hb.comp_snd P
  have hai : Integrable a P := ha.integrable one_le_two
  have hbi : Integrable b P := hb.integrable one_le_two
  have hab : Integrable (a * b) P := ha.integrable_mul hb
  have hX2 : MemLp (fun z : X × X ↦ a z.1 - a z.2) 2 (P.prod P) := ha1.sub ha2
  have hY2 : MemLp (fun z : X × X ↦ b z.1 - b z.2) 2 (P.prod P) := hb1.sub hb2
  rw [covariance_eq_sub hX2 hY2, covariance_eq_sub ha hb]
  have hX : ∫ z, (fun z : X × X ↦ a z.1 - a z.2) z ∂(P.prod P) = 0 := by
    simp only
    rw [integral_sub (hai.comp_fst P) (hai.comp_snd P), integral_fun_fst a, integral_fun_snd a,
      sub_self]
  simp only [Pi.mul_apply] at hX ⊢
  rw [hX, zero_mul, sub_zero]
  have hpt : ∀ z : X × X, (a z.1 - a z.2) * (b z.1 - b z.2) =
      (a z.1 * b z.1 - a z.1 * b z.2) - (a z.2 * b z.1 - a z.2 * b z.2) := fun z ↦ by ring
  simp_rw [hpt]
  have h11 : Integrable (fun z : X × X ↦ a z.1 * b z.1) (P.prod P) := hab.comp_fst P
  have h22 : Integrable (fun z : X × X ↦ a z.2 * b z.2) (P.prod P) := hab.comp_snd P
  have h12 : Integrable (fun z : X × X ↦ a z.1 * b z.2) (P.prod P) := hai.mul_prod hbi
  have h21 : Integrable (fun z : X × X ↦ a z.2 * b z.1) (P.prod P) := by
    have := hbi.mul_prod hai
    simpa only [mul_comm] using this
  have hI1 : Integrable (fun z : X × X ↦ a z.1 * b z.1 - a z.1 * b z.2) (P.prod P) := h11.sub h12
  have hI2 : Integrable (fun z : X × X ↦ a z.2 * b z.1 - a z.2 * b z.2) (P.prod P) := h21.sub h22
  rw [integral_sub hI1 hI2, integral_sub h11 h12, integral_sub h21 h22,
    integral_fun_fst (fun x ↦ a x * b x), integral_fun_snd (fun x ↦ a x * b x),
    integral_prod_mul a b]
  have : ∫ z : X × X, a z.2 * b z.1 ∂(P.prod P) = (∫ x, a x ∂P) * ∫ x, b x ∂P := by
    simp_rw [mul_comm (a _)]
    rw [integral_prod_mul b a, mul_comm]
  rw [this, probReal_univ]
  ring


/-- Strong law of large numbers for a measurable integrable statistic `f` of an i.i.d.
sequence with law `P`: almost surely `n⁻¹ ∑_{i<n} f(Z_i) → ∫ f dP`. -/
private theorem ae_tendsto_average_comp_of_iid {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) (Z : ℕ → Ω → E)
    (hiid : IsIndependentIdenticallyDistributed μ Z P) (f : E → F) (hf : Measurable f)
    (hint : Integrable f P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (Z i ω)) atTop
      (𝓝 (∫ x, f x ∂P)) := by
  obtain ⟨hm, hind, hlaw⟩ := hiid
  have hident : ∀ i, IdentDistrib (f ∘ Z i) (f ∘ Z 0) μ μ := fun i ↦
    ⟨(hf.comp (hm i)).aemeasurable, (hf.comp (hm 0)).aemeasurable, by
      rw [← Measure.map_map hf (hm i), ← Measure.map_map hf (hm 0), hlaw i, hlaw 0]⟩
  have hint0 : Integrable (f ∘ Z 0) μ := by
    rw [← hlaw 0] at hint; exact hint.comp_measurable (hm 0)
  have h := strong_law_ae (fun i ↦ f ∘ Z i) hint0
    (fun i j hij ↦ (hind.comp (fun _ ↦ f) (fun _ ↦ hf)).indepFun hij) hident
  have hmean : μ[f ∘ Z 0] = ∫ x, f x ∂P := by
    rw [← hlaw 0, integral_map (hm 0).aemeasurable hf.aestronglyMeasurable]; rfl
  rw [hmean] at h
  exact h

/-- The trace of the covariance matrix of a bounded measurable feature vector `φ(X)` is
`E ‖φ(X)‖² - ‖E φ(X)‖²`. -/
private theorem trace_covMatrix_map_eq {X : Type*} [MeasurableSpace X] {d : ℕ} (P : Measure X)
    [IsProbabilityMeasure P] (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (C : ℝ) (hC : ∀ x, ‖phi x‖ ≤ C) :
    Matrix.trace (TauCeti.covMatrix (P.map phi)) =
      (∫ x, ‖phi x‖ ^ 2 ∂P) - ‖∫ x, phi x ∂P‖ ^ 2 := by
  have hj : ∀ j, MemLp (fun x ↦ phi x j) 2 P := fun j ↦
    MemLp.of_bound (by fun_prop) C (ae_of_all _ fun x ↦
      (by simpa using PiLp.norm_apply_le (phi x) j : ‖phi x j‖ ≤ ‖phi x‖).trans (hC x))
  have hint : Integrable phi P := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hdiag : ∀ j, TauCeti.covMatrix (P.map phi) j j =
      (∫ x, phi x j ^ 2 ∂P) - (∫ x, phi x j ∂P) ^ 2 := fun j ↦ by
    rw [TauCeti.covMatrix_apply, covariance_map_fun (by fun_prop) (by fun_prop) hm.aemeasurable,
      covariance_eq_sub (hj j) (hj j)]
    simp only [Pi.mul_apply, sq]
  rw [Matrix.trace]
  simp only [Matrix.diag]
  rw [Finset.sum_congr rfl fun j _ ↦ hdiag j, Finset.sum_sub_distrib,
    EuclideanSpace.norm_sq_eq]
  congr 1
  · rw [← integral_finsetSum _ fun j _ ↦ (hj j).integrable_sq]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs])
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Real.norm_eq_abs, sq_abs, eval_integral_piLp (fun j ↦ (hj j).integrable one_le_two)]


/-- The central limit theorem behind the null limit of MMD: for a bounded measurable feature map
`φ` and independent pairs `(X_i, Y_i)` with law `P ⊗ P`, the scaled mean difference
`√n (φ̄_X - φ̄_Y)` converges in distribution to `N(0, 2C)`, `C` the covariance matrix of
`φ(X_1)`. -/
theorem tendstoInDistribution_sqrt_smul_sampleAverage_feature_sub
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (Xn i ω, Yn i ω))
      (P.prod P))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi) (B : ℝ)
    (hB : ∀ x, ‖phi x‖ ≤ B) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n •
      sampleAverage (fun i ω ↦ phi (Xn i ω) - phi (Yn i ω)) n ω) atTop id (fun _ ↦ μ)
      (multivariateGaussian 0 ((2 : ℝ) • TauCeti.covMatrix (P.map phi))) := by
  set C := TauCeti.covMatrix (P.map phi)
  set v : X × X → EuclideanSpace ℝ (Fin d) := fun z ↦ phi z.1 - phi z.2
  have hv : Measurable v := by fun_prop
  set Z : ℕ → Ω → X × X := fun i ω ↦ (Xn i ω, Yn i ω)
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun i ω ↦ v (Z i ω)
  set L := (P.prod P).map v
  have hiidV : IsIndependentIdenticallyDistributed μ V L :=
    ⟨fun i ↦ hv.comp (hiid.1 i), hiid.2.1.comp (fun _ ↦ v) (fun _ ↦ hv),
      fun i ↦ by rw [show V i = v ∘ Z i from rfl, ← Measure.map_map hv (hiid.1 i), hiid.2.2 i]⟩
  have hint : Integrable phi P := Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hL2 : MemLp id 2 L := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hv.aemeasurable]
    refine MemLp.of_bound hv.aestronglyMeasurable (2 * B) (ae_of_all _ fun z ↦ ?_)
    exact (norm_sub_le _ _).trans (by linarith [hB z.1, hB z.2])
  have hLmean : ∫ x, x ∂L = 0 := by
    -- unfold the local law `L` as an image measure
    change ∫ x, id x ∂((P.prod P).map v) = 0
    rw [integral_map hv.aemeasurable aestronglyMeasurable_id]
    simp only [v, id]
    rw [integral_sub (hint.comp_fst P) (hint.comp_snd P), integral_fun_fst phi,
      integral_fun_snd phi]
    simp
  have hj : ∀ j, MemLp (fun x ↦ phi x j) 2 P := fun j ↦
    MemLp.of_bound (by fun_prop) B (ae_of_all _ fun x ↦
      (by simpa using PiLp.norm_apply_le (phi x) j : ‖phi x j‖ ≤ ‖phi x‖).trans (hB x))
  have hcovL : TauCeti.covMatrix L = (2 : ℝ) • C := by
    ext i j
    rw [TauCeti.covMatrix_apply, covariance_map_fun (by fun_prop) (by fun_prop) hv.aemeasurable]
    simp only [Matrix.smul_apply, C, TauCeti.covMatrix_apply, smul_eq_mul]
    rw [covariance_map_fun (by fun_prop) (by fun_prop) hm.aemeasurable]
    simpa only [v, PiLp.sub_apply] using covariance_sub_prod_self P _ _ (hj i) (hj j)
  have hclt := tendstoInDistribution_sqrt_smul_sampleAverage μ L V hiidV hL2
  simp only [hLmean, hcovL, sub_zero] at hclt
  exact hclt

/-- The unbiased squared MMD of the inner-product kernel of a measurable feature map is a
measurable function of measurable samples. -/
theorem measurable_unbiasedSquaredMMD_inner {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {d : ℕ} (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi) {Xn Yn : ℕ → Ω → X}
    (hXm : ∀ i, Measurable (Xn i)) (hYm : ∀ i, Measurable (Yn i)) (n : ℕ) :
    Measurable (fun ω ↦ unbiasedSquaredMMD (fun x y ↦ inner ℝ (phi x) (phi y)) n
      (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω)) := by
  simp only [unbiasedSquaredMMD_def]
  refine Measurable.sub (Measurable.div_const ?_ _) (Measurable.const_mul ?_ _)
  · exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ by
      split_ifs <;> fun_prop
  · exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ by fun_prop

/-- Doubling the covariance of a centered Gaussian: the law of `‖W‖² + c` for
`W ∼ N(0, 2 C)` is the law of `2 ‖Z‖² + c` for `Z ∼ N(0, C)`. -/
theorem map_multivariateGaussian_two_smul_norm_sq_add {d : ℕ}
    {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) (c : ℝ) :
    (multivariateGaussian 0 ((2 : ℝ) • C)).map (fun w ↦ ‖w‖ ^ 2 + c) =
      (multivariateGaussian 0 C).map (fun z ↦ 2 * ‖z‖ ^ 2 + c) := by
  have hG : multivariateGaussian 0 ((2 : ℝ) • C) =
      (multivariateGaussian 0 C).map (fun z ↦ Real.sqrt 2 • z) := by
    have := TauCeti.Probability.map_add_smul_multivariateGaussian 0 hC 0 (Real.sqrt 2)
    simp only [zero_add, smul_zero, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at this
    exact this.symm
  rw [hG, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- GAPS 108.61, the null limit of MMD for a bounded finite-dimensional feature map. Let
`φ : X → ℝ^d` be bounded and measurable, `k(x, y) = ⟨φ x, φ y⟩`, and let the pairs `(X_i, Y_i)` be
independent with law `P ⊗ P`. With `C` the covariance matrix of `φ(X_1)`, the scaled unbiased
estimator `n MMD_u²` converges in distribution to `2 (‖Z‖² - tr C)` and the scaled plug-in estimator
`n ‖φ̄_X - φ̄_Y‖²` to `2 ‖Z‖²`, where `Z ∼ N(0, C)`. -/
theorem tendstoInDistribution_unbiasedSquaredMMD_null
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (Xn i ω, Yn i ω))
      (P.prod P))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (hb : ∃ C, ∀ x, ‖phi x‖ ≤ C) :
    let C := TauCeti.covMatrix (P.map phi);
    let k := fun x y ↦ inner ℝ (phi x) (phi y);
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) * unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
      (fun i ↦ Yn i.val ω)) atTop id (fun _ ↦ μ)
      ((multivariateGaussian 0 C).map (fun z ↦ 2 * (‖z‖ ^ 2 - Matrix.trace C))) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) *
        ‖sampleAverage (fun i ω ↦ phi (Xn i ω)) n ω - sampleAverage (fun i ω ↦ phi
          (Yn i ω)) n ω‖ ^ 2) atTop id (fun _ ↦ μ)
        ((multivariateGaussian 0 C).map (fun z ↦ 2 * ‖z‖ ^ 2)) := by
  intro C k
  obtain ⟨B₀, hB₀⟩ := hb
  set B := max B₀ 0
  have hB : ∀ x, ‖phi x‖ ≤ B := fun x ↦ (hB₀ x).trans (le_max_left _ _)
  have hXm : ∀ i, Measurable (Xn i) := fun i ↦ (hiid.1 i).fst
  have hYm : ∀ i, Measurable (Yn i) := fun i ↦ (hiid.1 i).snd
  have hint : Integrable phi P := Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hphi2 : MemLp id 2 (P.map phi) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable]
    exact MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)
  have hCpsd : C.PosSemidef := TauCeti.posSemidef_covMatrix _ hphi2
  -- the central limit theorem for `V i = φ(X_i) - φ(Y_i)`
  set Z : ℕ → Ω → X × X := fun i ω ↦ (Xn i ω, Yn i ω)
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun i ω ↦ phi (Xn i ω) - phi (Yn i ω)
  have hVm : ∀ i, Measurable (V i) := fun i ↦ (hm.comp (hXm i)).sub (hm.comp (hYm i))
  have hclt := tendstoInDistribution_sqrt_smul_sampleAverage_feature_sub μ P Xn Yn hiid phi hm B hB
  set W : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω ↦ Real.sqrt n • sampleAverage V n ω
  have hsa : ∀ n ω, sampleAverage (fun i ω ↦ phi (Xn i ω)) n ω -
      sampleAverage (fun i ω ↦ phi (Yn i ω)) n ω = sampleAverage V n ω := fun n ω ↦ by
    simp only [sampleAverage, V, ← smul_sub, Finset.sum_sub_distrib]
  have hnorm : ∀ (n : ℕ) ω, (n : ℝ) * ‖sampleAverage V n ω‖ ^ 2 = ‖W n ω‖ ^ 2 := fun n ω ↦ by
    simp only [W, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hWm : ∀ n, Measurable (W n) := fun n ↦ by
    have := Finset.measurable_fun_sum (Finset.range n) fun i _ ↦ hVm i
    exact (this.const_smul ((n : ℝ)⁻¹)).const_smul (Real.sqrt n)
  have hmapG := map_multivariateGaussian_two_smul_norm_sq_add hCpsd
  have hmmdm : ∀ n, Measurable (fun ω ↦ unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
      (fun i ↦ Yn i.val ω)) := measurable_unbiasedSquaredMMD_inner phi hm hXm hYm
  -- the remainder `n MMD_u² - n ‖φ̄_X - φ̄_Y‖²` and its almost sure limit `-2 tr C`
  set Y : ℕ → Ω → ℝ := fun n ω ↦ (n : ℝ) * unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
    (fun i ↦ Yn i.val ω) - ‖W n ω‖ ^ 2
  have hYm' : ∀ n, Measurable (Y n) := fun n ↦
    ((hmmdm n).const_mul _).sub ((hWm n).norm.pow_const 2)
  have hsq2 : Integrable (fun x ↦ ‖phi x‖ ^ 2) P :=
    Integrable.of_bound (by fun_prop) (B ^ 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)
  have hA := ae_tendsto_average_comp_of_iid μ (P.prod P) Z hiid (fun z ↦ phi z.1)
    (by fun_prop) (hint.comp_fst P)
  have hB' := ae_tendsto_average_comp_of_iid μ (P.prod P) Z hiid (fun z ↦ phi z.2)
    (by fun_prop) (hint.comp_snd P)
  have hS := ae_tendsto_average_comp_of_iid μ (P.prod P) Z hiid
    (fun z ↦ ‖phi z.1‖ ^ 2 + ‖phi z.2‖ ^ 2) (by fun_prop)
    ((hsq2.comp_fst P).add (hsq2.comp_snd P))
  rw [integral_fun_fst phi] at hA
  rw [integral_fun_snd phi] at hB'
  rw [integral_add (hsq2.comp_fst P) (hsq2.comp_snd P), integral_fun_fst (fun x ↦ ‖phi x‖ ^ 2),
    integral_fun_snd (fun x ↦ ‖phi x‖ ^ 2)] at hS
  simp only [probReal_univ, one_smul] at hA hB' hS
  have htr := trace_covMatrix_map_eq P phi hm B hB
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) - 1)⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp ?_
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop
  have hYlim : TendstoInMeasure μ Y atTop (fun _ ↦ -2 * Matrix.trace C) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hYm' n).aestronglyMeasurable) ?_
    filter_upwards [hA, hB', hS] with ω hAω hBω hSω
    have hR := (((hAω.norm.pow 2).add (hBω.norm.pow 2)).sub hSω).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add hinv)
    have hval : (‖∫ x, phi x ∂P‖ ^ 2 + ‖∫ x, phi x ∂P‖ ^ 2 -
        ((∫ x, ‖phi x‖ ^ 2 ∂P) + ∫ x, ‖phi x‖ ^ 2 ∂P)) * (1 + 0) = -2 * Matrix.trace C := by
      rw [htr]; ring
    rw [hval] at hR
    refine hR.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hmmd := unbiasedSquaredMMD_inner_eq phi hn (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω)
    simp only at hmmd
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ phi (Xn i ω)),
      Fin.sum_univ_eq_sum_range (fun i ↦ phi (Yn i ω)),
      Fin.sum_univ_eq_sum_range (fun i ↦ ‖phi (Xn i ω)‖ ^ 2 + ‖phi (Yn i ω)‖ ^ 2)] at hmmd
    simp only [Y, k]
    rw [hmmd, ← hnorm, ← hsa]
    simp only [sampleAverage, smul_eq_mul]
    generalize ∑ i ∈ Finset.range n, phi (Xn i ω) = SX
    generalize ∑ i ∈ Finset.range n, phi (Yn i ω) = SY
    generalize ∑ i ∈ Finset.range n, (‖phi (Xn i ω)‖ ^ 2 + ‖phi (Yn i ω)‖ ^ 2) = SS
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · have hsl := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ ‖p.1‖ ^ 2 + p.2) (by fun_prop) hYlim
      (fun n ↦ (hYm' n).aemeasurable)
    have e1 : (fun (n : ℕ) ω ↦ (n : ℝ) * unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
        (fun i ↦ Yn i.val ω)) = fun n ω ↦ ‖W n ω‖ ^ 2 + Y n ω := by
      funext n ω; simp only [Y]; ring
    rw [e1]
    refine tendstoInDistribution_of_map_eq hsl aemeasurable_id ?_
    rw [Measure.map_id]
    -- name the limit law in the form used by `hmapG`
    change _ = (multivariateGaussian 0 ((2 : ℝ) • C)).map
      (fun w ↦ ‖w‖ ^ 2 + -2 * Matrix.trace C)
    rw [hmapG]
    congr 1
    funext z
    ring
  · have h2 := hclt.continuous_comp (g := fun w : EuclideanSpace ℝ (Fin d) ↦ ‖w‖ ^ 2)
      (by fun_prop)
    have e2 : (fun (n : ℕ) ω ↦ (n : ℝ) * ‖sampleAverage (fun i ω ↦ phi (Xn i ω)) n ω -
        sampleAverage (fun i ω ↦ phi (Yn i ω)) n ω‖ ^ 2) =
        fun n ↦ (fun w ↦ ‖w‖ ^ 2) ∘ W n := by
      funext n ω
      simp only [Function.comp_apply, hsa, hnorm]
    rw [e2]
    refine tendstoInDistribution_of_map_eq h2 aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id]
    simpa only [add_zero] using (hmapG 0).symm

/-- The linear term of the alternative MMD central limit theorem: for a bounded measurable feature
map `φ` into `ℝ^d`, `δ = E_P φ - E_Q φ` and `s(x, y) = 2 ⟨φ x - φ y - δ, δ⟩`, the statistic `s`
is centered under `P ⊗ Q` and its second moment is `4 Var_P ⟨φ, δ⟩ + 4 Var_Q ⟨φ, δ⟩`. -/
theorem integral_mmdLinearTerm {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi) (C : ℝ)
    (hC : ∀ x, ‖phi x‖ ≤ C) :
    let δ := (∫ x, phi x ∂P) - ∫ x, phi x ∂Q
    let s := fun z : X × X ↦ 2 * inner ℝ (phi z.1 - phi z.2 - δ) δ
    (∫ z, s z ∂(P.prod Q)) = 0 ∧ (∫ z, s z ^ 2 ∂(P.prod Q)) =
      4 * Var[fun x ↦ inner ℝ (phi x) δ; P] + 4 * Var[fun x ↦ inner ℝ (phi x) δ; Q] := by
  intro δ s
  have hint : ∀ R : Measure X, IsProbabilityMeasure R → Integrable phi R := fun R _ ↦
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  set g : X → ℝ := fun x ↦ inner ℝ (phi x) δ
  have hg : Measurable g := by fun_prop
  have hgb : ∀ x, |g x| ≤ C * ‖δ‖ := fun x ↦
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  set mP := ∫ x, g x ∂P
  set mQ := ∫ x, g x ∂Q
  have hδδ : inner ℝ δ δ = mP - mQ := by
    have e : ∀ R : Measure X, IsProbabilityMeasure R →
        ∫ x, inner ℝ (phi x) δ ∂R = inner ℝ δ (∫ x, phi x ∂R) := fun R hR ↦ by
      simp_rw [real_inner_comm δ]
      exact integral_inner (hint R hR) δ
    -- unfold the local means `mP`, `mQ`
    change _ = (∫ x, inner ℝ (phi x) δ ∂P) - ∫ x, inner ℝ (phi x) δ ∂Q
    rw [e P inferInstance, e Q inferInstance, ← inner_sub_right]
  set a : X → ℝ := fun x ↦ g x - mP
  set b : X → ℝ := fun x ↦ g x - mQ
  have hs : ∀ z, s z = 2 * (a z.1 - b z.2) := fun z ↦ by
    simp only [s, a, b, g, inner_sub_left, hδδ]; ring
  have hgi : ∀ R : Measure X, IsProbabilityMeasure R → Integrable g R := fun R _ ↦
    Integrable.of_bound hg.aestronglyMeasurable (C * ‖δ‖) (ae_of_all _ fun x ↦ hgb x)
  have hcen : ∀ (R : Measure X) [IsProbabilityMeasure R],
      ∫ x, (g x - ∫ y, g y ∂R) ∂R = 0 := fun R _ ↦ by
    rw [integral_sub (hgi R inferInstance) (integrable_const _), integral_const, probReal_univ,
      one_smul, sub_self]
  have hsq : ∀ (R : Measure X) [IsProbabilityMeasure R],
      Integrable (fun x ↦ (g x - ∫ y, g y ∂R) ^ 2) R :=
    fun R _ ↦ Integrable.of_bound (by fun_prop) ((C * ‖δ‖ + |∫ y, g y ∂R|) ^ 2)
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hgb x) le_rfl)) 2)
  have hai : Integrable a P := (hgi P inferInstance).sub (integrable_const _)
  have hbi : Integrable b Q := (hgi Q inferInstance).sub (integrable_const _)
  refine ⟨?_, ?_⟩
  · simp only [hs]
    rw [integral_const_mul, integral_sub (hai.comp_fst Q) (hbi.comp_snd P), integral_fun_fst a,
      integral_fun_snd b, hcen P, hcen Q]
    simp
  · have hpt : ∀ z : X × X, s z ^ 2 = 4 * a z.1 ^ 2 - 8 * (a z.1 * b z.2) + 4 * b z.2 ^ 2 :=
      fun z ↦ by rw [hs]; ring
    simp only [hpt]
    have h1 : Integrable (fun z : X × X ↦ 4 * a z.1 ^ 2) (P.prod Q) :=
      ((hsq P).comp_fst Q).const_mul 4
    have h2 : Integrable (fun z : X × X ↦ 8 * (a z.1 * b z.2)) (P.prod Q) :=
      (hai.mul_prod hbi).const_mul 8
    have h3 : Integrable (fun z : X × X ↦ 4 * b z.2 ^ 2) (P.prod Q) :=
      ((hsq Q).comp_snd P).const_mul 4
    have h12 : Integrable (fun z : X × X ↦ 4 * a z.1 ^ 2 - 8 * (a z.1 * b z.2)) (P.prod Q) :=
      h1.sub h2
    rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_fun_fst (fun x ↦ a x ^ 2), integral_fun_snd (fun y ↦ b y ^ 2),
      integral_prod_mul a b, hcen P, variance_eq_integral hg.aemeasurable,
      variance_eq_integral hg.aemeasurable]
    simp [a, b, mP, mQ]

/-- The correction term of the unbiased MMD estimator is bounded: for a feature map bounded by `C`,
`|‖A‖² + ‖B‖² - n⁻¹ ∑ (‖φ(x_i)‖² + ‖φ(y_i)‖²)| ≤ 2 C²` with `A, B` the two feature means. -/
private theorem abs_unbiasedMMD_correction_le {X E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (phi : X → E) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖phi x‖ ≤ C)
    (n : ℕ) (x y : Fin n → X) :
    |‖(n : ℝ)⁻¹ • ∑ i, phi (x i)‖ ^ 2 + ‖(n : ℝ)⁻¹ • ∑ i, phi (y i)‖ ^ 2 -
      (n : ℝ)⁻¹ * ∑ i, (‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2)| ≤ 2 * C ^ 2 := by
  have hn1 : (n : ℝ)⁻¹ * n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [inv_mul_cancel₀ (by positivity)]
  have havg : ∀ w : Fin n → X, ‖(n : ℝ)⁻¹ • ∑ i, phi (w i)‖ ≤ C := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    calc (n : ℝ)⁻¹ * ‖∑ i, phi (w i)‖ ≤ (n : ℝ)⁻¹ * (n * C) := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          exact (Finset.sum_le_sum fun (i : Fin n) (_ : i ∈ Finset.univ) ↦ hC (w i)).trans_eq
            (by simp)
      _ ≤ C := by nlinarith
  have hsum : 0 ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, (‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2) ∧
      (n : ℝ)⁻¹ * ∑ i : Fin n, (‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2) ≤ 2 * C ^ 2 := by
    refine ⟨by positivity, ?_⟩
    calc (n : ℝ)⁻¹ * ∑ i : Fin n, (‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2)
        ≤ (n : ℝ)⁻¹ * (n * (2 * C ^ 2)) := by
          gcongr
          refine (Finset.sum_le_sum fun (i : Fin n) (_ : i ∈ Finset.univ) ↦ show
            ‖phi (x i)‖ ^ 2 + ‖phi (y i)‖ ^ 2 ≤ 2 * C ^ 2 by
              nlinarith [hC (x i), hC (y i), norm_nonneg (phi (x i)),
                norm_nonneg (phi (y i))]).trans_eq (by simp)
      _ ≤ 2 * C ^ 2 := by nlinarith [sq_nonneg C]
  have h1 := havg x
  have h2 := havg y
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖(n : ℝ)⁻¹ • ∑ i : Fin n, phi (x i)‖,
    sq_nonneg ‖(n : ℝ)⁻¹ • ∑ i : Fin n, phi (y i)‖]

/-- `√n / (n - 1) → 0`. -/
private theorem tendsto_sqrt_div_sub_one :
    Tendsto (fun n : ℕ ↦ Real.sqrt n / (n - 1)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n ↦ ?_) ?_
    (by simpa using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul 2)
  · rcases Nat.lt_or_ge n 1 with h | h
    · simp [Nat.lt_one_iff.mp h]
    · exact div_nonneg (Real.sqrt_nonneg _) (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast h
        linarith)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
    rw [div_le_iff₀ (by linarith),
      show 2 * (Real.sqrt n)⁻¹ * ((n : ℝ) - 1) = 2 * (n - 1) / Real.sqrt n by ring,
      le_div_iff₀ hs]
    nlinarith

/-- GAPS 108.61, alternative MMD CLT for a bounded finite-dimensional feature map. Let the pairs
`(X_i, Y_i)` be independent with law `P ⊗ Q` and `δ = E φ(X) - E φ(Y)`. Then
`√n (MMD_u² - ‖δ‖²)` converges in distribution to the centered normal law with variance
`4 Var_P ⟨φ, δ⟩ + 4 Var_Q ⟨φ, δ⟩`. -/
theorem tendstoInDistribution_unbiasedSquaredMMD_alternative
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xn Yn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (Xn i ω, Yn i ω))
      (P.prod Q))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (hb : ∃ C, ∀ x, ‖phi x‖ ≤ C) :
    let delta := (∫ x, phi x ∂P) - ∫ x, phi x ∂Q;
    let k := fun x y ↦ inner ℝ (phi x) (phi y);
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
      (unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω) - ‖delta‖ ^ 2))
      atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal
        (4 * Var[fun x ↦ inner ℝ (phi x) delta; P] +
          4 * Var[fun x ↦ inner ℝ (phi x) delta; Q]))) := by
  intro delta k
  obtain ⟨C₀, hC₀⟩ := hb
  set C := max C₀ 0
  have hC : ∀ x, ‖phi x‖ ≤ C := fun x ↦ (hC₀ x).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hXm : ∀ i, Measurable (Xn i) := fun i ↦ (hiid.1 i).fst
  have hYm : ∀ i, Measurable (Yn i) := fun i ↦ (hiid.1 i).snd
  -- the vector sequence `V i = φ(X_i) - φ(Y_i)` and its central limit theorem
  set v : X × X → EuclideanSpace ℝ (Fin d) := fun z ↦ phi z.1 - phi z.2
  have hv : Measurable v := by fun_prop
  set Z : ℕ → Ω → X × X := fun i ω ↦ (Xn i ω, Yn i ω)
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun i ω ↦ v (Z i ω)
  set L := (P.prod Q).map v
  have hiidV : IsIndependentIdenticallyDistributed μ V L :=
    ⟨fun i ↦ hv.comp (hiid.1 i), hiid.2.1.comp (fun _ ↦ v) (fun _ ↦ hv),
      fun i ↦ by rw [show V i = v ∘ Z i from rfl, ← Measure.map_map hv (hiid.1 i), hiid.2.2 i]⟩
  have hint : ∀ R : Measure X, IsProbabilityMeasure R → Integrable phi R := fun R _ ↦
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hL2 : MemLp id 2 L := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hv.aemeasurable]
    refine MemLp.of_bound hv.aestronglyMeasurable (2 * C) (ae_of_all _ fun z ↦ ?_)
    exact (norm_sub_le _ _).trans (by linarith [hC z.1, hC z.2])
  have hLmean : ∫ x, x ∂L = delta := by
    -- unfold the local law `L` as an image measure
    change ∫ x, id x ∂((P.prod Q).map v) = delta
    rw [integral_map hv.aemeasurable aestronglyMeasurable_id]
    simp only [v, id]
    rw [integral_sub ((hint P inferInstance).comp_fst Q) ((hint Q inferInstance).comp_snd P),
      integral_fun_fst phi, integral_fun_snd phi]
    simp [delta]
  have hclt := tendstoInDistribution_sqrt_smul_sampleAverage μ L V hiidV hL2
  rw [hLmean] at hclt
  set U : ℕ → Ω → ℝ := fun n ω ↦ ‖Real.sqrt n • (sampleAverage V n ω - delta)‖
  have hUb : IsBoundedInProbability μ U :=
    isBoundedInProbability_of_tendstoInDistribution μ U (hclt.continuous_comp continuous_norm)
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hT1 : TendstoInMeasure μ (fun (n : ℕ) ω ↦ U n ω * (U n ω * (Real.sqrt n)⁻¹)) atTop
      (fun _ ↦ 0) :=
    tendstoInMeasure_mul_zero_of_isBoundedInProbability μ U _ hUb
      (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ U _ hUb
        (tendstoInMeasure_const_of_tendsto μ _ hinv))
  -- the bounded correction term of the unbiased estimator
  set R : ℕ → Ω → ℝ := fun n ω ↦
    ‖(n : ℝ)⁻¹ • ∑ i : Fin n, phi (Xn i ω)‖ ^ 2 + ‖(n : ℝ)⁻¹ • ∑ i : Fin n, phi (Yn i ω)‖ ^ 2 -
      (n : ℝ)⁻¹ * ∑ i : Fin n, (‖phi (Xn i ω)‖ ^ 2 + ‖phi (Yn i ω)‖ ^ 2)
  have hRb : ∀ n ω, |R n ω| ≤ 2 * C ^ 2 := fun n ω ↦
    abs_unbiasedMMD_correction_le phi hC0 hC n (fun i ↦ Xn i ω) (fun i ↦ Yn i ω)
  have hRB : IsBoundedInProbability μ R := by
    intro ε hε
    refine ⟨2 * C ^ 2 + 1, by positivity, Eventually.of_forall fun n ↦ ?_⟩
    have : {ω | 2 * C ^ 2 + 1 < |R n ω|} = ∅ :=
      eq_empty_of_forall_notMem fun ω hω ↦ by
        have := hRb n ω
        simp only [mem_ofPred_eq] at hω
        linarith
    rw [this, measureReal_empty]
    exact hε.le
  have hT2 : TendstoInMeasure μ (fun (n : ℕ) ω ↦ R n ω * (Real.sqrt n / (n - 1))) atTop
      (fun _ ↦ 0) :=
    tendstoInMeasure_mul_zero_of_isBoundedInProbability μ R _ hRB
      (tendstoInMeasure_const_of_tendsto μ _ tendsto_sqrt_div_sub_one)
  -- the linear term and its central limit theorem
  set s : X × X → ℝ := fun z ↦ 2 * inner ℝ (v z - delta) delta
  have hs : Measurable s := by fun_prop
  obtain ⟨hs0, hs2⟩ := integral_mmdLinearTerm P Q phi hm C hC
  have h2s : MemLp s 2 (P.prod Q) := by
    refine MemLp.of_bound hs.aestronglyMeasurable (2 * ((2 * C + ‖delta‖) * ‖delta‖))
      (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    gcongr
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [hC z.1, hC z.2])
  have hS := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ (P.prod Q) Z hiid s hs h2s hs0
  rw [hs2] at hS
  -- Slutsky
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ _ _ (fun n ↦ ?_)
    (fun n ↦ ?_) hS ((tendstoInMeasure_add_zero μ _ _ hT1 hT2).congr' ?_ EventuallyEq.rfl)
  · exact (Finset.measurable_sum _ fun i _ ↦ hs.comp (hiid.1 i)).const_mul _
  · exact ((measurable_unbiasedSquaredMMD_inner phi hm hXm hYm n).sub
      measurable_const).const_mul _
  filter_upwards [eventually_ge_atTop 2] with n hn
  refine ae_of_all _ fun ω ↦ ?_
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmmd := unbiasedSquaredMMD_inner_eq phi hn (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω)
  simp only at hmmd
  set A := (n : ℝ)⁻¹ • ∑ i : Fin n, phi (Xn i ω)
  set B := (n : ℝ)⁻¹ • ∑ i : Fin n, phi (Yn i ω)
  have hw : sampleAverage V n ω = A - B := by
    simp only [sampleAverage, V, v, Z, A, B, ← smul_sub, Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ phi (Xn i ω)),
      Fin.sum_univ_eq_sum_range (fun i ↦ phi (Yn i ω))]
  have hsumV : ∑ i ∈ Finset.range n, V i ω = (n : ℝ) • (A - B) := by
    rw [← hw, sampleAverage, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hsS : ∑ i ∈ Finset.range n, s (Z i ω) = 2 * n * inner ℝ (A - B - delta) delta := by
    simp only [s]
    rw [← Finset.mul_sum, ← sum_inner, Finset.sum_sub_distrib]
    rw [hsumV, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, ← smul_sub,
      real_inner_smul_left]
    ring
  have hU : U n ω = Real.sqrt n * ‖A - B - delta‖ := by
    simp only [U, hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by linarith)
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hnorm : ‖A - B‖ ^ 2 = ‖A - B - delta‖ ^ 2 + 2 * inner ℝ (A - B - delta) delta +
      ‖delta‖ ^ 2 := by
    have := norm_add_sq_real (A - B - delta) delta
    rw [sub_add_cancel] at this
    rw [this]
  -- unfold the local abbreviations of the decomposition to expose `U`, `R` and `s` for `rw`
  show U n ω * (U n ω * (Real.sqrt n)⁻¹) + R n ω * (Real.sqrt n / (n - 1)) =
    Real.sqrt n * (unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω) -
      ‖delta‖ ^ 2) - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, s (Z i ω)
  rw [hU, hsS, show unbiasedSquaredMMD k n _ _ = _ from hmmd, hnorm]
  generalize ‖A - B - delta‖ = a
  generalize inner ℝ (A - B - delta) delta = ip
  simp only [R, A, B]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  rw [show (Real.sqrt n) ^ 2 = n by rw [sq, hss]]
  ring

end CKSD
