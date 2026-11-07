module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Geometry: Kernels

Sources: `GAPS.md`, `SYNOPSIS108.md`, and `STRUCTURE108.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 108.61, the null limit of MMD for a bounded finite-dimensional feature map. -/
theorem tendstoInDistribution_squaredMMD_null_finite_features
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ (Xn i ω, Yn i ω))
      (P.prod P))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (hb : ∃ C, ∀ x, ‖phi x‖ ≤ C) :
    let m := ∫ x, phi x ∂P;
    let C := Matrix.of fun i j ↦ ∫ x, (phi x i - m i) * (phi x j - m j) ∂P;
    let k := fun x y ↦ inner ℝ (phi x) (phi y);
    TendstoInDistribution μ (fun n ω ↦ (n : ℝ) * unbiasedSquaredMMD k n (fun i ↦ Xn i.val ω)
      (fun i ↦ Yn i.val ω))
      ((multivariateGaussian 0 C).map (fun z ↦ 2 * (‖z‖ ^ 2 - Matrix.trace C))) ∧
      TendstoInDistribution μ (fun n ω ↦ (n : ℝ) *
        ‖sampleAverage (fun i ω ↦ phi (Xn i ω)) n ω - sampleAverage (fun i ω ↦ phi
          (Yn i ω)) n ω‖ ^ 2)
        ((multivariateGaussian 0 C).map (fun z ↦ 2 * ‖z‖ ^ 2)) := by
  sorry

/-- GAPS 108.61, alternative MMD CLT for a bounded finite-dimensional feature map. -/
theorem tendstoInDistribution_squaredMMD_alternative_finite_features
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

/-- GAPS 108.62: nonnegativity, separation, and the kernel form of energy distance. -/
theorem energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD
    {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    let D := 2 * (∫ z, ‖z.1 - z.2‖ ∂P.prod Q) - (∫ z, ‖z.1 - z.2‖ ∂P.prod P) -
      ∫ z, ‖z.1 - z.2‖ ∂Q.prod Q;
    0 ≤ D ∧ (D = 0 ↔ P = Q) ∧ D = 2 * squaredMMD distanceKernel P Q := by
  sorry

/-- GAPS 108.62: distance covariance detects independence and equals four times HSIC. -/
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

/-- GAPS 108.63, independence criterion for a characteristic product-space kernel. -/
theorem squaredMMD_joint_prod_eq_zero_iff_indepFun
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (k : (X × Y) → (X × Y) → ℝ)
    (hk : IsCharacteristicKernel k) :
    squaredMMD k P ((P.map Prod.fst).prod (P.map Prod.snd)) = 0 ↔
      IndepFun Prod.fst Prod.snd P := by
  rw [hk P ((P.map Prod.fst).prod (P.map Prod.snd)) inferInstance inferInstance]
  have h := indepFun_iff_map_prod_eq_prod_map_map
    (μ := P) measurable_fst.aemeasurable measurable_snd.aemeasurable
  simpa only [Prod.mk.eta, Measure.map_id'] using h.symm

/-- GAPS 108.68(c), characteristicness iff the symmetric spectral measure has full support. -/
theorem isCharacteristicKernel_iff_spectral_measure_full_support {d : ℕ} (hd : 0 < d)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure L]
    (hsym : L.map (fun x ↦ -x) = L) :
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    IsCharacteristicKernel k ↔ ∀ x, ∀ r > 0, 0 < L (Metric.ball x r) := by
  sorry

/-- Products of two coordinates are integrable under a law with finite second moments. -/
theorem integrable_coord_mul_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure P]
    (h2 : MemLp id 2 P) (i j : Fin d) : Integrable (fun x ↦ x i * x j) P := by
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) P := h2.norm.integrable_sq
  refine hsq.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul (by simpa using PiLp.norm_apply_le x i) (by simpa using PiLp.norm_apply_le x j)
    (abs_nonneg _) (norm_nonneg _)

/-- Coordinates are integrable under a law with integrable identity. -/
theorem integrable_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure P]
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

/-- GAPS 108.68(d), quadratic-polynomial MMD depends only on the first two moments. -/
theorem squaredMMD_quadratic_polynomial_eq {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 4 P) (hQ : MemLp id 4 Q) :
    let m := (∫ x, x ∂P) - ∫ x, x ∂Q;
    squaredMMD (fun x y ↦ (1 + inner ℝ x y) ^ 2) P Q =
      2 * ‖m‖ ^ 2 + ∑ i, ∑ j,
        ((∫ x, x i * x j ∂P) - ∫ x, x i * x j ∂Q) ^ 2 := by
  intro m
  have hP2 : MemLp id 2 P := hP.mono_exponent (by norm_num)
  have hQ2 : MemLp id 2 Q := hQ.mono_exponent (by norm_num)
  have hP1 : Integrable id P := hP2.integrable one_le_two
  have hQ1 : Integrable id Q := hQ2.integrable one_le_two
  unfold squaredMMD
  rw [integral_quadratic_kernel_prod P P hP2 hP2, integral_quadratic_kernel_prod Q Q hQ2 hQ2,
    integral_quadratic_kernel_prod P Q hP2 hQ2, EuclideanSpace.norm_sq_eq]
  have hm : ∀ i, m i = (∫ x, x i ∂P) - ∫ x, x i ∂Q := fun i ↦ by
    simp only [m, PiLp.sub_apply, integral_coord P hP1, integral_coord Q hQ1]
  simp only [hm, Real.norm_eq_abs, sq_abs]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

/-- GAPS 108.70, MMD metrizes weak convergence along uniformly tight sequences. -/
theorem tendstoWeakly_iff_tendsto_squaredMMD_of_tight {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (P : ℕ → Measure X) (Q : Measure X) (hP : ∀ n, IsProbabilityMeasure (P n))
    [IsProbabilityMeasure Q] (k : X → X → ℝ)
    (hk : Continuous (Function.uncurry k)) (hb : ∃ C, ∀ x y, |k x y| ≤ C)
    (hchar : IsCharacteristicKernel k)
    (htight : ∀ epsilon > 0, ∃ K : Set X, IsCompact K ∧
      ∀ n, (P n) Kᶜ ≤ ENNReal.ofReal epsilon) :
    TendstoWeakly P Q ↔ Tendsto (fun n ↦ squaredMMD k (P n) Q) atTop (𝓝 0) := by
  sorry

/-- GAPS 108.71, scalar Langevin Stein identity for bounded continuously differentiable tests. -/
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

/-- The random-feature summand `2 cos(⟨w, x⟩ + b) cos(⟨w, y⟩ + b)`. -/
noncomputable def randomFourierFeatureTerm {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  2 * Real.cos (inner ℝ s.1 x + s.2) * Real.cos (inner ℝ s.1 y + s.2)

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
`[-2, 2]`: the sum of the centered copies exceeds `D ε` with probability at most
`exp (-D ε² / 8)`. -/
theorem measureReal_pi_sum_sub_integral_ge_le {Y : Type*} [MeasurableSpace Y] (D : ℕ)
    (μ : Measure Y) [IsProbabilityMeasure μ] {g : Y → ℝ} (hg : Measurable g)
    (hb : ∀ s, g s ∈ Icc (-2 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin D ↦ μ).real
        {s | D * ε ≤ ∑ j, (g (s j) - ∫ t, g t ∂μ)} ≤ Real.exp (-(D : ℝ) * ε ^ 2 / 8) := by
  set P := Measure.pi fun _ : Fin D ↦ μ
  have hindep : iIndepFun (fun (j : Fin D) (s : Fin D → Y) ↦ g (s j) - ∫ t, g t ∂μ) P :=
    iIndepFun_pi (X := fun _ t ↦ g t - ∫ t, g t ∂μ) fun _ ↦ (hg.sub_const _).aemeasurable
  have hsub : ∀ j : Fin D, HasSubgaussianMGF (fun s : Fin D → Y ↦ g (s j) - ∫ t, g t ∂μ)
      ((‖(2 : ℝ) - (-2)‖₊ / 2) ^ 2) P := by
    intro j
    have hm : AEMeasurable (fun s : Fin D → Y ↦ g (s j)) P :=
      (hg.comp (measurable_pi_apply j)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc hm (ae_of_all _ fun s ↦ hb (s j))
    have hint : ∫ s, g (s j) ∂P = ∫ t, g t ∂μ :=
      integral_comp_eval (μ := fun _ : Fin D ↦ μ) hg.aestronglyMeasurable
    simpa only [hint] using h
  have hc : ((‖(2 : ℝ) - (-2)‖₊ / 2) ^ 2 : ℝ≥0) = 4 := by
    ext
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    norm_num
  rw [hc] at hsub
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep (c := fun _ ↦ 4) (s := Finset.univ)
    (fun j _ ↦ hsub j) (ε := D * ε) (by positivity)
  refine h.trans_eq ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp
    ring

/-- The random-feature kernel is the sample mean of the random-feature summands. -/
theorem randomFourierFeatureKernel_eq_mean {d D : ℕ}
    (sample : Fin D → EuclideanSpace ℝ (Fin d) × ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    randomFourierFeatureKernel sample x y =
      (D : ℝ)⁻¹ * ∑ j, randomFourierFeatureTerm x y (sample j) := by
  unfold randomFourierFeatureKernel randomFourierFeatureTerm
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- GAPS 108.74: unbiased random Fourier features and their pointwise Hoeffding bound. -/
theorem randomFourierFeatureKernel_unbiased_and_concentration {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) (epsilon : ℝ) (he : 0 < epsilon) :
    let P := Measure.pi (fun _ : Fin D ↦ L.prod phase);
    let k := ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    (∫ sample, randomFourierFeatureKernel sample x y ∂P) = k ∧
      P.real {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|} ≤
        2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
  intro P k
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hmeas : Measurable (randomFourierFeatureTerm x y) :=
    (continuous_randomFourierFeatureTerm x y).measurable
  have hk : ∫ s, randomFourierFeatureTerm x y s ∂L.prod phase = k :=
    integral_randomFourierFeatureTerm L phase hphase x y
  have hcoord : ∀ j : Fin D, ∫ s, randomFourierFeatureTerm x y (s j) ∂P = k := fun j ↦ by
    rw [← hk]
    exact integral_comp_eval (μ := fun _ : Fin D ↦ L.prod phase) hmeas.aestronglyMeasurable
  have hintj : ∀ j : Fin D, Integrable (fun s : Fin D → _ ↦ randomFourierFeatureTerm x y (s j)) P :=
    fun j ↦ Integrable.of_bound (C := 2)
      (hmeas.comp (measurable_pi_apply j)).aestronglyMeasurable
      (ae_of_all _ fun s ↦ by
        rw [Real.norm_eq_abs, abs_le]; exact randomFourierFeatureTerm_mem_Icc x y (s j))
  refine ⟨?_, ?_⟩
  · simp_rw [randomFourierFeatureKernel_eq_mean]
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hintj j]
    simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · have hcenter : ∀ s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ,
        randomFourierFeatureKernel s x y - k =
          (D : ℝ)⁻¹ * ∑ j, (randomFourierFeatureTerm x y (s j) - k) := by
      intro s
      rw [randomFourierFeatureKernel_eq_mean, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hup := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas
      (randomFourierFeatureTerm_mem_Icc x y) he.le
    have hlo := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas.neg
      (fun s ↦ by
        have := randomFourierFeatureTerm_mem_Icc x y s
        exact ⟨by simp only [Pi.neg_apply]; linarith [this.2],
          by simp only [Pi.neg_apply]; linarith [this.1]⟩) he.le
    rw [hk] at hup
    simp only [Pi.neg_apply, integral_neg, hk] at hlo
    have hsub : {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|} ⊆
        {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | (D : ℝ) * epsilon ≤ ∑ j, (randomFourierFeatureTerm x y (s j) - k)} ∪
          {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | (D : ℝ) * epsilon ≤ ∑ j, (-randomFourierFeatureTerm x y (s j) - -k)} := by
      intro s hs
      simp only [mem_ofPred_eq, hcenter] at hs
      simp only [mem_union, mem_ofPred_eq]
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
        ≤ P.real ({s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | (D : ℝ) * epsilon ≤ ∑ j, (randomFourierFeatureTerm x y (s j) - k)} ∪
          {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | (D : ℝ) * epsilon ≤ ∑ j, (-randomFourierFeatureTerm x y (s j) - -k)}) :=
          measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) + Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) :=
          add_le_add hup hlo
      _ = 2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by ring

/-- GAPS 108.74: the uniform compact-set random-feature bound. -/
theorem measure_uniform_randomFourierFeatureKernel_error_le {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (M : Set (EuclideanSpace ℝ (Fin d))) (hM : IsCompact M)
    (epsilon : ℝ) (he : 0 < epsilon) :
    let sigma := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L);
    ∀ (hscale : epsilon ≤ sigma * Metric.diam M),
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

/-- GAPS 108.74, deterministic transfer of a uniform kernel error to squared MMD. -/
theorem abs_squaredMMD_sub_le_of_uniform_kernel_error
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (M : Set X) (hM : IsCompact M) (hP : P M = 1) (hQ : Q M = 1)
    (k l : X → X → ℝ) (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (epsilon : ℝ) (he : 0 ≤ epsilon) (herr : ∀ x ∈ M, ∀ y ∈ M, |k x y - l x y| ≤ epsilon) :
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
