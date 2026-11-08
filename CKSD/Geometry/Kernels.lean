module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import TauCeti.Analysis.PositiveDefinite.Kernel.MeanEmbedding
public import TauCeti.Probability.Moments.Covariance

/-!
# Kernel discrepancies: MMD, energy distance, HSIC, Stein identities, random features

Statements about the squared maximum mean discrepancy `CKSD.squaredMMD` and the kernels built
from distances, together with random Fourier features.

## Main results

* `CKSD.squaredMMD_eq_norm_kernelMeanEmbedding_sub_sq`: for a positive semidefinite kernel the
  squared MMD is the squared distance of TauCeti's kernel mean embeddings.
* `CKSD.tendstoInDistribution_unbiasedSquaredMMD_null`,
  `CKSD.tendstoInDistribution_unbiasedSquaredMMD_alternative`: null and alternative limit laws of
  the unbiased MMD estimator for a bounded finite-dimensional feature map (GAPS 108.61).
* `CKSD.energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD`,
  `CKSD.distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD`: energy distance and distance
  covariance (GAPS 108.62).
* `CKSD.squaredMMD_joint_prod_eq_zero_iff_indepFun`: the HSIC independence criterion (GAPS 108.63).
* `CKSD.isCharacteristicKernel_iff_spectral_measure_full_support`,
  `CKSD.squaredMMD_quadratic_polynomial_eq`: criteria for characteristic kernels (GAPS 108.68).
* `CKSD.tendstoWeakly_iff_tendsto_squaredMMD_of_tight`: MMD metrizes weak convergence along tight
  sequences (GAPS 108.70).
* `CKSD.integral_langevin_stein_operator_eq_zero`: the scalar Langevin Stein identity
  (GAPS 108.71).
* `CKSD.integral_randomFourierFeatureKernel`,
  `CKSD.measureReal_abs_randomFourierFeatureKernel_sub_ge_le`,
  `CKSD.measure_uniform_randomFourierFeatureKernel_error_le`,
  `CKSD.abs_squaredMMD_sub_le_of_uniform_kernel_error`: random Fourier features (GAPS 108.74).

## References

* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*,
  J. Mach. Learn. Res. 13 (2012).
* A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A bounded kernel that is measurable on the product space is integrable against every finite
measure on the product. -/
theorem integrable_kernel_of_bounded {X : Type*} [MeasurableSpace X] {k : X → X → ℝ}
    (hkm : Measurable fun z : X × X ↦ k z.1 z.2) (hb : ∃ C, ∀ x y, |k x y| ≤ C)
    (μ : Measure (X × X)) [IsFiniteMeasure μ] : Integrable (fun z : X × X ↦ k z.1 z.2) μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hkm.aestronglyMeasurable C
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hC z.1 z.2)

/-- For a bounded measurable characteristic kernel, the squared MMD of two probability laws
vanishes exactly when the laws are equal. -/
theorem IsCharacteristicKernel.squaredMMD_eq_zero_iff {X : Type*} [MeasurableSpace X]
    {k : X → X → ℝ} (hk : IsCharacteristicKernel k) (hkm : Measurable fun z : X × X ↦ k z.1 z.2)
    (hb : ∃ C, ∀ x y, |k x y| ≤ C) (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : squaredMMD k P Q = 0 ↔ P = Q :=
  hk P Q inferInstance inferInstance (integrable_kernel_of_bounded hkm hb _)
    (integrable_kernel_of_bounded hkm hb _) (integrable_kernel_of_bounded hkm hb _)

/-- For a positive semidefinite kernel `k` whose feature map is integrable for `P` and `Q`, and
which is integrable against the three product measures, the squared MMD is the squared distance
`‖m_P - m_Q‖²` of TauCeti's kernel mean embeddings. -/
theorem squaredMMD_eq_norm_kernelMeanEmbedding_sub_sq {X : Type*} [MeasurableSpace X]
    {k : X → X → ℝ} (hk : Matrix.PosSemidef k) {P Q : Measure X} [SFinite P] [SFinite Q]
    (hP : Integrable hk.kolmogorovFeature P) (hQ : Integrable hk.kolmogorovFeature Q)
    (hPP : Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod P))
    (hQQ : Integrable (fun z : X × X ↦ k z.1 z.2) (Q.prod Q))
    (hPQ : Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod Q)) :
    squaredMMD k P Q = ‖hk.kernelMeanEmbedding P - hk.kernelMeanEmbedding Q‖ ^ 2 := by
  rw [hk.norm_kernelMeanEmbedding_sub_sq hP hQ, squaredMMD, integral_prod_symm _ hPP,
    integral_prod_symm _ hQQ, integral_prod_symm _ hPQ]
  ring

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
    TendstoInDistribution μ (fun n ω ↦ (n : ℝ) * unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
      (fun i ↦ Yn i.val ω))
      ((multivariateGaussian 0 C).map (fun z ↦ 2 * (‖z‖ ^ 2 - Matrix.trace C))) ∧
      TendstoInDistribution μ (fun n ω ↦ (n : ℝ) *
        ‖sampleAverage (fun i ω ↦ phi (Xn i ω)) n ω - sampleAverage (fun i ω ↦ phi
          (Yn i ω)) n ω‖ ^ 2)
        ((multivariateGaussian 0 C).map (fun z ↦ 2 * ‖z‖ ^ 2)) := by
  sorry

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
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n *
      (unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω) - ‖delta‖ ^ 2))
      (gaussianReal 0 (Real.toNNReal
        (4 * variance P (fun x ↦ inner ℝ (phi x) delta) +
          4 * variance Q (fun x ↦ inner ℝ (phi x) delta)))) := by
  sorry

/-- GAPS 108.62: for laws `P, Q` on `ℝ^d` with finite first moments, the energy distance
`D = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖` is nonnegative, vanishes exactly when `P = Q`, and equals
twice the squared MMD of the distance kernel `CKSD.distanceKernel`. -/
theorem energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD
    {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    let D := 2 * (∫ z, ‖z.1 - z.2‖ ∂P.prod Q) - (∫ z, ‖z.1 - z.2‖ ∂P.prod P) -
      ∫ z, ‖z.1 - z.2‖ ∂Q.prod Q;
    0 ≤ D ∧ (D = 0 ↔ P = Q) ∧ D = 2 * squaredMMD distanceKernel P Q := by
  sorry

/-- GAPS 108.62: for a law `P` on `ℝ^d × ℝ^e` with finite second moments and marginals `μ, ν`, the
squared distance covariance `V = E[A(X, X') B(Y, Y')]` of the doubly centered distances is
nonnegative, vanishes exactly when `P = μ ⊗ ν`, and equals four times the squared MMD (the HSIC) of
the product of the two distance kernels between `P` and `μ ⊗ ν`. -/
theorem distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD {d e : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)))
    [IsProbabilityMeasure P] (h2 : MemLp id 2 P) :
    let mu := P.map Prod.fst;
    let nu := P.map Prod.snd;
    let V := ∫ z, centeredDistance mu z.1.1 z.2.1 * centeredDistance nu z.1.2 z.2.2 ∂P.prod P;
    let k := fun x y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) ↦
      distanceKernel x.1 y.1 * distanceKernel x.2 y.2;
    0 ≤ V ∧ (V = 0 ↔ P = mu.prod nu) ∧ V = 4 * squaredMMD k P (mu.prod nu) := by
  sorry

/-- GAPS 108.63, independence criterion for a characteristic product-space kernel: for a bounded
measurable characteristic kernel `k` on `X × Y` and a law `P` of a pair, the HSIC
`MMD²(P, P_X ⊗ P_Y)` vanishes exactly when the two coordinates are independent under `P`. -/
theorem squaredMMD_joint_prod_eq_zero_iff_indepFun
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (k : (X × Y) → (X × Y) → ℝ)
    (hk : IsCharacteristicKernel k) (hkm : Measurable fun z : (X × Y) × (X × Y) ↦ k z.1 z.2)
    (hb : ∃ C, ∀ x y, |k x y| ≤ C) :
    squaredMMD k P ((P.map Prod.fst).prod (P.map Prod.snd)) = 0 ↔
      IndepFun Prod.fst Prod.snd P := by
  rw [hk.squaredMMD_eq_zero_iff hkm hb]
  have h := indepFun_iff_map_prod_eq_prod_map_map
    (μ := P) measurable_fst.aemeasurable measurable_snd.aemeasurable
  simpa only [Prod.mk.eta, Measure.map_id'] using h.symm

/-- GAPS 108.68(c), characteristicness iff the symmetric spectral measure has full support: for a
symmetric finite measure `L` on `ℝ^d`, `d ≥ 1`, the translation-invariant kernel
`k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)` is characteristic exactly when every open ball has positive
`L`-measure. -/
theorem isCharacteristicKernel_iff_spectral_measure_full_support {d : ℕ} (hd : 0 < d)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure L]
    (hsym : L.map (fun x ↦ -x) = L) :
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    IsCharacteristicKernel k ↔ ∀ x, ∀ r > 0, 0 < L (Metric.ball x r) := by
  sorry

/-- Products of two coordinates are integrable under a law with finite second moments. -/
theorem integrable_coord_mul_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (h2 : MemLp id 2 P) (i j : Fin d) : Integrable (fun x ↦ x i * x j) P := by
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) P := h2.norm.integrable_sq
  refine hsq.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul (by simpa using PiLp.norm_apply_le x i) (by simpa using PiLp.norm_apply_le x j)
    (abs_nonneg _) (norm_nonneg _)

/-- Coordinates are integrable under a law with integrable identity. -/
theorem integrable_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (h1 : Integrable id P) (i : Fin d) : Integrable (fun x ↦ x i) P :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integrable_comp h1

/-- The coordinates of the mean are the means of the coordinates. -/
theorem integral_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (h1 : Integrable id P) (i : Fin d) : (∫ x, x ∂P) i = ∫ x, x i ∂P := by
  have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm h1
  simpa using this.symm

/-- The product-measure integral of the quadratic polynomial kernel `(1 + ⟨x, y⟩)²` in terms of
first and second moments. -/
theorem integral_quadratic_kernel_prod {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hP : MemLp id 2 P) (hQ : MemLp id 2 Q) :
    ∫ z, (1 + inner ℝ z.1 z.2) ^ 2 ∂P.prod Q =
      1 + 2 * ∑ i, (∫ x, x i ∂P) * (∫ y, y i ∂Q) +
        ∑ i, ∑ j, (∫ x, x i * x j ∂P) * (∫ y, y i * y j ∂Q) := by
  have hP1 : Integrable id P := hP.integrable one_le_two
  have hQ1 : Integrable id Q := hQ.integrable one_le_two
  have hpt : ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      (1 + inner ℝ z.1 z.2) ^ 2 = 1 + 2 * ∑ i, z.1 i * z.2 i +
        ∑ i, ∑ j, (z.1 i * z.1 j) * (z.2 i * z.2 j) := by
    intro z
    have hin : inner ℝ z.1 z.2 = ∑ i, z.1 i * z.2 i := by
      rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun i _ ↦ by simp [mul_comm]
    rw [hin, add_sq, one_pow, mul_one, sq, Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [hpt]
  have hlin : ∀ i, Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      z.1 i * z.2 i) (P.prod Q) := fun i ↦
    (integrable_coord P hP1 i).mul_prod (integrable_coord Q hQ1 i)
  have hquad : ∀ i j, Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      (z.1 i * z.1 j) * (z.2 i * z.2 j)) (P.prod Q) := fun i j ↦
    (integrable_coord_mul_coord P hP i j).mul_prod (integrable_coord_mul_coord Q hQ i j)
  rw [integral_add (by
      exact (integrable_const _).add
        ((integrable_finsetSum Finset.univ fun i _ ↦ hlin i).const_mul 2))
      (integrable_finsetSum Finset.univ fun i _ ↦
        integrable_finsetSum Finset.univ fun j _ ↦ hquad i j),
    integral_add (integrable_const _)
      ((integrable_finsetSum Finset.univ fun i _ ↦ hlin i).const_mul 2),
    integral_const, integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hlin i,
    integral_finsetSum Finset.univ fun i _ ↦ integrable_finsetSum Finset.univ fun j _ ↦ hquad i j]
  have h1 : ∑ i, ∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      z.1 i * z.2 i ∂P.prod Q = ∑ i, (∫ x, x i ∂P) * (∫ y, y i ∂Q) :=
    Finset.sum_congr rfl fun i _ ↦ integral_prod_mul (fun x : EuclideanSpace ℝ (Fin d) ↦ x i)
      (fun y : EuclideanSpace ℝ (Fin d) ↦ y i)
  have h2 : ∑ i, ∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ∑ j, (z.1 i * z.1 j) * (z.2 i * z.2 j) ∂P.prod Q
      = ∑ i, ∑ j, (∫ x, x i * x j ∂P) * (∫ y, y i * y j ∂Q) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum Finset.univ fun j _ ↦ hquad i j]
    exact Finset.sum_congr rfl fun j _ ↦
      integral_prod_mul (fun x : EuclideanSpace ℝ (Fin d) ↦ x i * x j)
        (fun y : EuclideanSpace ℝ (Fin d) ↦ y i * y j)
  rw [h1, h2]
  simp

/-- GAPS 108.68(d), quadratic-polynomial MMD depends only on the first two moments: for laws with
finite second moments, the squared MMD of the kernel `(1 + ⟨x, y⟩)²` is
`2 ‖m_P - m_Q‖² + ∑_{i,j} (E_P[x_i x_j] - E_Q[x_i x_j])²`. In particular this kernel is not
characteristic. -/
theorem squaredMMD_quadratic_polynomial_eq {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 2 P) (hQ : MemLp id 2 Q) :
    let m := (∫ x, x ∂P) - ∫ x, x ∂Q;
    squaredMMD (fun x y ↦ (1 + inner ℝ x y) ^ 2) P Q =
      2 * ‖m‖ ^ 2 + ∑ i, ∑ j,
        ((∫ x, x i * x j ∂P) - ∫ x, x i * x j ∂Q) ^ 2 := by
  intro m
  have hP1 : Integrable id P := hP.integrable one_le_two
  have hQ1 : Integrable id Q := hQ.integrable one_le_two
  unfold squaredMMD
  rw [integral_quadratic_kernel_prod P P hP hP, integral_quadratic_kernel_prod Q Q hQ hQ,
    integral_quadratic_kernel_prod P Q hP hQ, EuclideanSpace.norm_sq_eq]
  have hm : ∀ i, m i = (∫ x, x i ∂P) - ∫ x, x i ∂Q := fun i ↦ by
    simp only [m, PiLp.sub_apply, integral_coord P hP1, integral_coord Q hQ1]
  simp only [hm, Real.norm_eq_abs, sq_abs]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

/-- For a bounded continuous kernel, squared MMD is continuous in its first probability law. -/
theorem continuous_squaredMMD_probabilityMeasure {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (k : X → X → ℝ) (hk : Continuous (Function.uncurry k))
    (hb : ∃ C, ∀ x y, |k x y| ≤ C) (Q : ProbabilityMeasure X) :
    Continuous (fun P : ProbabilityMeasure X ↦ squaredMMD k P Q) := by
  obtain ⟨C, hC⟩ := hb
  let f : BoundedContinuousFunction (X × X) ℝ :=
    ⟨⟨Function.uncurry k, hk⟩, ⟨2 * C, fun x y ↦ by
      change |k x.1 x.2 - k y.1 y.2| ≤ 2 * C
      exact (abs_sub _ _).trans (by linarith [hC x.1 x.2, hC y.1 y.2])⟩⟩
  have heval := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have hPP : Continuous (fun P : ProbabilityMeasure X ↦ P.prod P) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have hPQ : Continuous (fun P : ProbabilityMeasure X ↦ P.prod Q) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_const)
  exact ((heval.comp hPP).add continuous_const).sub
    (continuous_const.mul (heval.comp hPQ))

/-- GAPS 108.70, MMD metrizes weak convergence along uniformly tight sequences: for a bounded
continuous characteristic kernel on a separable metric space and a uniformly tight sequence of
probability laws `P n`, `P n → Q` weakly exactly when `MMD²(P n, Q) → 0`. -/
theorem tendstoWeakly_iff_tendsto_squaredMMD_of_tight {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (P : ℕ → Measure X) (Q : Measure X) (hP : ∀ n, IsProbabilityMeasure (P n))
    [IsProbabilityMeasure Q] (k : X → X → ℝ)
    (hk : Continuous (Function.uncurry k)) (hb : ∃ C, ∀ x y, |k x y| ≤ C)
    (hchar : IsCharacteristicKernel k)
    (htight : ∀ epsilon > 0, ∃ K : Set X, IsCompact K ∧
      ∀ n, (P n) Kᶜ ≤ ENNReal.ofReal epsilon) :
    TendstoWeakly P Q ↔ Tendsto (fun n ↦ squaredMMD k (P n) Q) atTop (𝓝 0) := by
  have : ∀ n, IsProbabilityMeasure (P n) := hP
  let Ps : ℕ → ProbabilityMeasure X := fun n ↦ ⟨P n, hP n⟩
  let Qs : ProbabilityMeasure X := ⟨Q, inferInstance⟩
  let F : ProbabilityMeasure X → ℝ := fun R ↦ squaredMMD k R Q
  have hF : Continuous F := continuous_squaredMMD_probabilityMeasure k hk hb Qs
  have hFQ : F Qs = 0 := by simp [F, Qs, squaredMMD]; ring
  have hweak : TendstoWeakly P Q ↔ Tendsto Ps atTop (𝓝 Qs) := by
    rw [TendstoWeakly.iff_forall_integral_tendsto]
    simpa only [Ps, Qs, ProbabilityMeasure.coe_mk] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (μs := Ps) (μ := Qs)).symm
  rw [hweak]
  constructor
  · intro h
    have hlim : Tendsto (fun n ↦ F (Ps n)) atTop (𝓝 (F Qs)) :=
      hF.continuousAt.tendsto.comp h
    rw [hFQ] at hlim
    exact hlim.congr' (Eventually.of_forall fun n ↦ by
      change squaredMMD k ((Ps n : ProbabilityMeasure X) : Measure X) Q = _
      exact congrArg (fun R : Measure X ↦ squaredMMD k R Q)
        (ProbabilityMeasure.coe_mk (P n) (hP n)))
  · intro hzero
    have ht : IsTightMeasureSet {((R : ProbabilityMeasure X) : Measure X) | R ∈ range Ps} := by
      apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
      intro ε hε
      by_cases he : ε = ⊤
      · exact ⟨∅, isCompact_empty, fun R hR ↦ he ▸ le_top⟩
      obtain ⟨K, hK, hbound⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' he)
      refine ⟨K, hK, ?_⟩
      rintro R ⟨S, ⟨n, rfl⟩, rfl⟩
      exact (hbound n).trans_eq (ENNReal.ofReal_toReal he)
    have hc := isCompact_closure_of_isTightMeasureSet ht
    apply hc.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
    intro R hR hcluster
    have hne : (atTop ⊓ Filter.comap Ps (𝓝 R)).NeBot :=
      Filter.neBot_inf_comap_iff_map.2
        (by simpa only [MapClusterPt, ClusterPt, inf_comm] using hcluster)
    have hconv : Tendsto Ps (atTop ⊓ Filter.comap Ps (𝓝 R)) (𝓝 R) :=
      Filter.tendsto_iff_comap.2 inf_le_right
    have hFR : F R = 0 := tendsto_nhds_unique
      (hF.continuousAt.tendsto.comp hconv) (hzero.mono_left inf_le_left)
    exact Subtype.ext ((hchar.squaredMMD_eq_zero_iff hk.measurable hb R Q).mp hFR)

/-- GAPS 108.71, scalar Langevin Stein identity for bounded continuously differentiable tests: if
`P` has a positive `C¹` density `p` with integrable score `p'/p`, then
`E_P[g (p'/p) + g'] = 0` for every bounded `C¹` function `g` with integrable derivative. -/
theorem integral_langevin_stein_operator_eq_zero
    (P : Measure ℝ) [IsProbabilityMeasure P] (p g : ℝ → ℝ)
    (hp : HasDensity P volume p) (hpos : ∀ x, 0 < p x)
    (hp1 : ContDiff ℝ 1 p) (hg : ContDiff ℝ 1 g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) (hscore : Integrable (fun x ↦ |deriv p x / p x|) P)
    (hder : Integrable (deriv g) P) :
    (∫ x, g x * (deriv p x / p x) + deriv g x ∂P) = 0 := by
  obtain ⟨hpm, -, hPeq⟩ := hp
  obtain ⟨C, hC⟩ := hb
  set q : ℝ → ℝ≥0 := fun x ↦ (p x).toNNReal
  have hqm : Measurable q := hpm.real_toNNReal
  have hPq : P = volume.withDensity fun x ↦ (q x : ℝ≥0∞) := by
    rw [hPeq]; rfl
  have hq : ∀ x, (q x : ℝ) = p x := fun x ↦ Real.coe_toNNReal _ (hpos x).le
  have hgc : Continuous g := hg.continuous
  have hpc : Continuous p := hp1.continuous
  have hdpc : Continuous (deriv p) := hp1.continuous_deriv le_rfl
  have hdg : ∀ x, HasDerivAt g (deriv g x) x := fun x ↦
    ((hg.differentiable one_ne_zero) x).hasDerivAt
  have hdp : ∀ x, HasDerivAt p (deriv p x) x := fun x ↦
    ((hp1.differentiable one_ne_zero) x).hasDerivAt
  -- integrability of the score term under `P`
  have hscoreP : Integrable (fun x ↦ g x * (deriv p x / p x)) P := by
    refine (hscore.const_mul C).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (hgc.mul (hdpc.div hpc fun x ↦ (hpos x).ne')).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  have hsum : Integrable (fun x ↦ g x * (deriv p x / p x) + deriv g x) P := hscoreP.add hder
  rw [hPq] at hsum ⊢
  rw [integral_withDensity_eq_integral_smul hqm]
  rw [integrable_withDensity_iff_integrable_smul hqm] at hsum
  have hpt : ∀ x, (q x) • (g x * (deriv p x / p x) + deriv g x) =
      deriv g x * p x + g x * deriv p x := fun x ↦ by
    rw [NNReal.smul_def, smul_eq_mul, hq]
    field_simp [(hpos x).ne']
    ring
  simp_rw [hpt] at hsum ⊢
  -- `g p` is integrable since `p` is
  have hpint : Integrable p volume := by
    have h1 : Integrable (fun _ : ℝ ↦ (1 : ℝ)) (volume.withDensity fun x ↦ (q x : ℝ≥0∞)) := by
      rw [← hPq]; exact integrable_const _
    rw [integrable_withDensity_iff_integrable_smul hqm] at h1
    simpa [NNReal.smul_def, hq] using h1
  have hgp : Integrable (fun x ↦ g x * p x) volume := by
    refine (hpint.const_mul C).mono' (hgc.mul hpc).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos x)]
    exact mul_le_mul_of_nonneg_right (hC x) (hpos x).le
  exact integral_eq_zero_of_hasDerivAt_of_integrable (fun x ↦ (hdg x).mul (hdp x)) hsum hgp

/-- Over a uniformly distributed phase on `[0, 2π]`, `cos (c + 2b)` has mean zero. -/
theorem integral_cos_add_two_mul_uniformPhase (phase : Measure ℝ)
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (c : ℝ) : ∫ b, Real.cos (c + 2 * b) ∂phase = 0 := by
  rw [hphase, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]
  have hderiv : ∀ b ∈ uIcc 0 (2 * Real.pi),
      HasDerivAt (fun b ↦ Real.sin (c + 2 * b) / 2) (Real.cos (c + 2 * b)) b := by
    intro b _
    have := ((hasDerivAt_id' b).const_mul 2).const_add c |>.sin
    convert this.div_const 2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : Real.sin (c + 2 * (2 * Real.pi)) = Real.sin c := by
    rw [show c + 2 * (2 * Real.pi) = c + ((2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_nat_mul_two_pi c 2
  rw [this]
  simp

/-- The random-feature summand is continuous in the frequency and phase. -/
theorem continuous_randomFourierFeatureTerm {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    Continuous (randomFourierFeatureTerm x y) := by
  unfold randomFourierFeatureTerm; fun_prop

/-- The random-feature summand takes values in `[-2, 2]`. -/
theorem randomFourierFeatureTerm_mem_Icc {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) : randomFourierFeatureTerm x y s ∈ Icc (-2 : ℝ) 2 := by
  unfold randomFourierFeatureTerm
  have h1 := Real.abs_cos_le_one (inner ℝ s.1 x + s.2)
  have h2 := Real.abs_cos_le_one (inner ℝ s.1 y + s.2)
  have : |2 * Real.cos (inner ℝ s.1 x + s.2) * Real.cos (inner ℝ s.1 y + s.2)| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (Real.cos (inner ℝ s.1 x + s.2)),
      abs_nonneg (Real.cos (inner ℝ s.1 y + s.2))]
  exact abs_le.mp this

/-- The random-feature summand is unbiased for the translation-invariant kernel. -/
theorem integral_randomFourierFeatureTerm {d : ℕ}
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ s, randomFourierFeatureTerm x y s ∂L.prod phase = ∫ w, Real.cos (inner ℝ w (x - y)) ∂L := by
  have hint : Integrable (randomFourierFeatureTerm x y) (L.prod phase) := by
    refine Integrable.of_bound (C := 2)
      (continuous_randomFourierFeatureTerm x y).measurable.aestronglyMeasurable
      (ae_of_all _ fun s ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact randomFourierFeatureTerm_mem_Icc x y s
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  have hpt : ∀ b, randomFourierFeatureTerm x y (w, b) =
      Real.cos (inner ℝ w (x - y)) + Real.cos ((inner ℝ w x + inner ℝ w y) + 2 * b) := by
    intro b
    have e1 : inner ℝ w (x - y) = (inner ℝ w x + b) - (inner ℝ w y + b) := by
      rw [inner_sub_right]; ring
    have e2 : inner ℝ w x + inner ℝ w y + 2 * b = (inner ℝ w x + b) + (inner ℝ w y + b) := by
      ring
    rw [e1, e2, Real.cos_sub (inner ℝ w x + b), Real.cos_add (inner ℝ w x + b) (inner ℝ w y + b)]
    simp only [randomFourierFeatureTerm]
    ring
  simp_rw [hpt]
  rw [integral_add (integrable_const _) ?_, integral_const, probReal_univ, one_smul,
    integral_cos_add_two_mul_uniformPhase phase hphase, add_zero]
  exact Integrable.of_bound (C := 1) (by fun_prop) (ae_of_all _ fun b ↦ by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- Hoeffding's inequality for a sample of `D` independent copies of a variable with values in
`[a, b]`: the sum of the centered copies exceeds `D ε` with probability at most
`exp (-2 D ε² / (b - a)²)`. -/
theorem measureReal_pi_sum_sub_integral_ge_le {Y : Type*} [MeasurableSpace Y] (D : ℕ)
    (μ : Measure Y) [IsProbabilityMeasure μ] {g : Y → ℝ} (hg : Measurable g) {a b : ℝ}
    (hb : ∀ s, g s ∈ Icc a b) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin D ↦ μ).real
        {s | D * ε ≤ ∑ j, (g (s j) - ∫ t, g t ∂μ)} ≤
      Real.exp (-2 * (D : ℝ) * ε ^ 2 / (b - a) ^ 2) := by
  set P := Measure.pi fun _ : Fin D ↦ μ
  have hindep : iIndepFun (fun (j : Fin D) (s : Fin D → Y) ↦ g (s j) - ∫ t, g t ∂μ) P :=
    iIndepFun_pi (X := fun _ t ↦ g t - ∫ t, g t ∂μ) fun _ ↦ (hg.sub_const _).aemeasurable
  have hsub : ∀ j : Fin D, HasSubgaussianMGF (fun s : Fin D → Y ↦ g (s j) - ∫ t, g t ∂μ)
      ((‖b - a‖₊ / 2) ^ 2) P := by
    intro j
    have hm : AEMeasurable (fun s : Fin D → Y ↦ g (s j)) P :=
      (hg.comp (measurable_pi_apply j)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc hm (ae_of_all _ fun s ↦ hb (s j))
    have hint : ∫ s, g (s j) ∂P = ∫ t, g t ∂μ :=
      integral_comp_eval (μ := fun _ : Fin D ↦ μ) hg.aestronglyMeasurable
    simpa only [hint] using h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep (s := Finset.univ)
    (fun j _ ↦ hsub j) (ε := D * ε) (by positivity)
  refine h.trans_eq ?_
  congr 1
  have hc : (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (b - a) ^ 2 / 4 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [div_pow, sq_abs]
    norm_num
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, hc]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  rcases eq_or_ne (b - a) 0 with hab | hab
  · simp [hab]
  · have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
    ring

/-- GAPS 108.74: random Fourier features are unbiased. The random Fourier feature kernel of an
independent sample of frequencies `w_j ∼ L` and uniform phases `b_j ∈ [0, 2π]` has mean
`k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)`. -/
theorem integral_randomFourierFeatureKernel {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ sample, randomFourierFeatureKernel sample x y ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) =
      ∫ w, Real.cos (inner ℝ w (x - y)) ∂L := by
  have hmeas : Measurable (randomFourierFeatureTerm x y) :=
    (continuous_randomFourierFeatureTerm x y).measurable
  have hcoord : ∀ j : Fin D, ∫ s, randomFourierFeatureTerm x y (s j)
      ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) = ∫ w, Real.cos (inner ℝ w (x - y)) ∂L :=
    fun j ↦ by
      rw [← integral_randomFourierFeatureTerm L phase hphase x y]
      exact integral_comp_eval (μ := fun _ : Fin D ↦ L.prod phase) hmeas.aestronglyMeasurable
  have hintj : ∀ j : Fin D, Integrable (fun s : Fin D → _ ↦ randomFourierFeatureTerm x y (s j))
      (Measure.pi fun _ : Fin D ↦ L.prod phase) :=
    fun j ↦ Integrable.of_bound (C := 2)
      (hmeas.comp (measurable_pi_apply j)).aestronglyMeasurable
      (ae_of_all _ fun s ↦ by
        rw [Real.norm_eq_abs, abs_le]; exact randomFourierFeatureTerm_mem_Icc x y (s j))
  have hDpos : (D : ℝ) ≠ 0 := by exact_mod_cast (show 0 < D by omega).ne'
  simp only [randomFourierFeatureKernel]
  rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hintj j]
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- GAPS 108.74: the pointwise Hoeffding bound for random Fourier features. For an independent
sample of `D ≥ 1` frequencies `w_j ∼ L` and uniform phases, the random-feature kernel deviates from
`k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)` by at least `ε > 0` with probability at most
`2 exp(-D ε² / 8)`. Its unbiasedness is `CKSD.integral_randomFourierFeatureKernel`. -/
theorem measureReal_abs_randomFourierFeatureKernel_sub_ge_le {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) (epsilon : ℝ) (he : 0 < epsilon) :
    (Measure.pi fun _ : Fin D ↦ L.prod phase).real
        {sample | epsilon ≤ |randomFourierFeatureKernel sample x y -
          ∫ w, Real.cos (inner ℝ w (x - y)) ∂L|} ≤
      2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
  set P := Measure.pi fun _ : Fin D ↦ L.prod phase
  set k := ∫ w, Real.cos (inner ℝ w (x - y)) ∂L
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hmeas : Measurable (randomFourierFeatureTerm x y) :=
    (continuous_randomFourierFeatureTerm x y).measurable
  have hk : ∫ s, randomFourierFeatureTerm x y s ∂L.prod phase = k :=
    integral_randomFourierFeatureTerm L phase hphase x y
  have hcenter : ∀ s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ,
      randomFourierFeatureKernel s x y - k =
        (D : ℝ)⁻¹ * ∑ j, (randomFourierFeatureTerm x y (s j) - k) := by
    intro s
    rw [randomFourierFeatureKernel, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hexp : Real.exp (-2 * (D : ℝ) * epsilon ^ 2 / (2 - -2) ^ 2) =
      Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
    congr 1; ring
  have hup := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas
    (randomFourierFeatureTerm_mem_Icc x y) he.le
  have hlo := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas.neg (a := -2) (b := 2)
    (fun s ↦ by
      have := randomFourierFeatureTerm_mem_Icc x y s
      exact ⟨by simp only [Pi.neg_apply]; linarith [this.2],
        by simp only [Pi.neg_apply]; linarith [this.1]⟩) he.le
  rw [hk, hexp] at hup
  simp only [Pi.neg_apply, integral_neg, hk] at hlo
  rw [hexp] at hlo
  set A := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ |
    (D : ℝ) * epsilon ≤ ∑ j, (randomFourierFeatureTerm x y (s j) - k)}
  set B := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ |
    (D : ℝ) * epsilon ≤ ∑ j, (-randomFourierFeatureTerm x y (s j) - -k)}
  have hsub : {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|} ⊆ A ∪ B := by
    intro s hs
    simp only [mem_ofPred_eq, hcenter] at hs
    simp only [A, B, mem_union, mem_ofPred_eq]
    have hsum : ∑ j, (-randomFourierFeatureTerm x y (s j) - -k) =
        -∑ j, (randomFourierFeatureTerm x y (s j) - k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum]
    rcases le_abs'.mp hs with h | h
    · right
      have := mul_le_mul_of_nonneg_left h hDpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hDpos.ne', one_mul] at this
      linarith
    · left
      have := mul_le_mul_of_nonneg_left h hDpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hDpos.ne', one_mul] at this
  calc P.real {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|}
      ≤ P.real (A ∪ B) := measureReal_mono hsub
    _ ≤ P.real A + P.real B := measureReal_union_le _ _
    _ ≤ Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) + Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) :=
        add_le_add hup hlo
    _ = 2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by ring

/-- GAPS 108.74: the uniform compact-set random-feature bound. For a compact set `M ⊆ ℝ^d`, a
frequency law `L` with finite second moment `σ² = E ‖w‖²`, and `ε ≤ σ diam M`, the probability that
the random-feature kernel of `D` features deviates from `k` by at least `ε` somewhere on `M × M` is
at most `98 (σ diam M / ε)² exp(-D ε² / (32 (d + 1)))`. -/
theorem measure_uniform_randomFourierFeatureKernel_error_le {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (M : Set (EuclideanSpace ℝ (Fin d))) (hM : IsCompact M)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hscale : epsilon ≤ Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) * Metric.diam M) :
    let sigma := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L);
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    let P := Measure.pi (fun _ : Fin D ↦ L.prod phase);
    P.real {sample | ∃ x ∈ M, ∃ y ∈ M, epsilon ≤ |randomFourierFeatureKernel sample x y - k x y|} ≤
      98 * (sigma * Metric.diam M / epsilon) ^ 2 *
        Real.exp (-(D : ℝ) * epsilon ^ 2 / (32 * (d + 1))) := by
  sorry

/-- A function continuous on `M × M`, for a compact `M`, is integrable for every finite measure
concentrated on `M × M`. No second countability of the ambient space is needed. -/
theorem integrable_of_continuousOn_compact_prod
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {M : Set X} (hM : IsCompact M) (ρ : Measure (X × X)) [IsFiniteMeasure ρ]
    (hρ : ρ (M ×ˢ M)ᶜ = 0) {g : X × X → ℝ} (hg : ContinuousOn g (M ×ˢ M)) :
    Integrable g ρ := by
  have hMm : MeasurableSet M := hM.isClosed.measurableSet
  have hs : MeasurableSet (M ×ˢ M) := hMm.prod hMm
  have hρs : ρ.restrict (M ×ˢ M) = ρ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hρ)
  rw [← hρs, ← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).integrable_map_iff]
  have : CompactSpace M := isCompact_iff_compactSpace.mp hM
  let G : M × M → ℝ := fun p ↦ g (p.1, p.2)
  have hG : Continuous G := by
    have : Continuous (fun p : M × M ↦ ((p.1 : X), (p.2 : X))) := by fun_prop
    exact hg.comp_continuous this fun p ↦ ⟨p.1.2, p.2.2⟩
  have hmeas : Measurable (g ∘ ((↑) : ↥(M ×ˢ M) → X × X)) :=
    hG.measurable.comp (MeasurableEquiv.Set.prod M M).measurable
  obtain ⟨C, hC⟩ := hM.prod hM |>.exists_bound_of_continuousOn hg
  have : IsFiniteMeasure (Measure.comap ((↑) : ↥(M ×ˢ M) → X × X) ρ) := by
    constructor
    rw [(MeasurableEmbedding.subtype_coe hs).comap_apply]
    simp
  exact Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ fun z ↦ hC z z.2)

/-- GAPS 108.74, deterministic transfer of a uniform kernel error to squared MMD: if two continuous
kernels differ by at most `ε` on `M × M` for a compact `M` carrying both laws, their squared MMDs
differ by at most `4 ε`. -/
theorem abs_squaredMMD_sub_le_of_uniform_kernel_error
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (M : Set X) (hM : IsCompact M) (hP : P M = 1) (hQ : Q M = 1)
    (k l : X → X → ℝ) (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (epsilon : ℝ)  (herr : ∀ x ∈ M, ∀ y ∈ M, |k x y - l x y| ≤ epsilon) :
    |squaredMMD k P Q - squaredMMD l P Q| ≤ 4 * epsilon := by
  have hMm : MeasurableSet M := hM.isClosed.measurableSet
  have hconc : ∀ (R S : Measure X) [IsProbabilityMeasure R] [IsProbabilityMeasure S],
      R M = 1 → S M = 1 → (R.prod S) (M ×ˢ M)ᶜ = 0 := by
    intro R S _ _ hR hS
    rw [prob_compl_eq_zero_iff (hMm.prod hMm), Measure.prod_prod, hR, hS, one_mul]
  have hk' := hk.continuousOn (s := M ×ˢ M)
  have hl' := hl.continuousOn (s := M ×ˢ M)
  -- each of the three double integrals moves by at most `epsilon`
  have hpiece : ∀ (R S : Measure X) [IsProbabilityMeasure R] [IsProbabilityMeasure S],
      R M = 1 → S M = 1 →
      |(∫ z, k z.1 z.2 ∂R.prod S) - ∫ z, l z.1 z.2 ∂R.prod S| ≤ epsilon := by
    intro R S _ _ hR hS
    have hρ := hconc R S hR hS
    rw [← integral_sub
      (integrable_of_continuousOn_compact_prod (g := fun z : X × X ↦ k z.1 z.2) hM _ hρ hk')
      (integrable_of_continuousOn_compact_prod (g := fun z : X × X ↦ l z.1 z.2) hM _ hρ hl')]
    have hb := norm_integral_le_of_norm_le_const (μ := R.prod S)
      (f := fun z : X × X ↦ k z.1 z.2 - l z.1 z.2) (C := epsilon)
      (Filter.Eventually.mono (p := fun z ↦ z ∈ M ×ˢ M) (mem_ae_iff.mpr hρ)
        fun z hz ↦ herr z.1 hz.1 z.2 hz.2)
    simpa using hb
  have h1 := hpiece P P hP hP
  have h2 := hpiece Q Q hQ hQ
  have h3 := hpiece P Q hP hQ
  unfold squaredMMD
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


end CKSD
