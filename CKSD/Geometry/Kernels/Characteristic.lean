module

public import CKSD.Geometry.Kernels.EnergyDistance
import CKSD.Geometry.Kernels.DistanceProductSeparation
import CKSD.Geometry.Kernels.DistanceCovarianceCentering
import CKSD.Geometry.Kernels.Spectral
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
public import CKSD.Inference.Basic

/-!
# Kernel discrepancies: energy distance, HSIC, characteristic kernels, Stein identities

Statements about the squared maximum mean discrepancy `CKSD.squaredMMD` and the kernels built
from distances. The limit laws of the unbiased MMD estimator (GAPS 108.61) are in
`CKSD.Geometry.Kernels.UnbiasedMMD`; random Fourier features (GAPS 108.74) are in
`CKSD.Geometry.Kernels.RandomFeatures`; the identification of the squared MMD of a positive
semidefinite kernel with the squared distance of kernel mean embeddings
(`CKSD.squaredMMD_eq_norm_kernelMeanEmbedding_sub_sq`) is in `CKSD.Geometry.Kernels.Distance`.

## Main results

* `CKSD.IsCharacteristicKernel.squaredMMD_eq_zero_iff`: for a bounded measurable characteristic
  kernel the squared MMD separates probability laws.
* `CKSD.energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD`,
  `CKSD.distance_covariance_nonneg_eq_zero_iff_and_eq_squaredMMD`: energy distance and distance
  covariance (GAPS 108.62).
* `CKSD.squaredMMD_joint_prod_eq_zero_iff_indepFun`: the HSIC independence criterion (GAPS 108.63).
* `CKSD.isCharacteristicKernel_iff_spectral_measure_full_support`,
  `CKSD.squaredMMD_quadratic_polynomial_eq`: criteria for characteristic kernels (GAPS 108.68).
* `CKSD.tendsto_probabilityMeasure_iff_tendsto_squaredMMD_of_tight`: MMD metrizes weak
  convergence along tight sequences (GAPS 108.70).
* `CKSD.integral_langevin_stein_operator_eq_zero`: the scalar Langevin Stein identity
  (GAPS 108.71).
-/

public section

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

/-- GAPS 108.62: for laws `P, Q` on `ℝ^d` with finite first moments, the energy distance
`energyDistance P Q = 2 E‖X - Y‖ - E‖X - X'‖ - E‖Y - Y'‖` is nonnegative, vanishes exactly when
`P = Q`, and equals twice the squared MMD of the distance kernel `CKSD.distanceKernel`. -/
theorem energy_distance_nonneg_eq_zero_iff_and_eq_squaredMMD
    {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    0 ≤ energyDistance P Q ∧ (energyDistance P Q = 0 ↔ P = Q) ∧
      energyDistance P Q = 2 * squaredMMD distanceKernel P Q := by
  obtain ⟨hnonneg, hzero⟩ := energyDistance_nonneg_eq_zero_iff P Q hP hQ
  exact ⟨hnonneg, hzero, energyDistance_eq_two_mul_squaredMMD P Q hP hQ⟩

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
  dsimp only
  have hP : Integrable (fun z ↦ ‖z‖) P := (h2.integrable (by norm_num)).norm
  have hQ := integrable_norm_prod_marginals P hP
  have hfst : P.map Prod.fst =
      ((P.map Prod.fst).prod (P.map Prod.snd)).map Prod.fst := by simp
  have hsnd : P.map Prod.snd =
      ((P.map Prod.fst).prod (P.map Prod.snd)).map Prod.snd := by simp
  obtain ⟨hnonneg, hzero⟩ := distanceProductKernel_squaredMMD_nonneg_eq_zero_iff
    P ((P.map Prod.fst).prod (P.map Prod.snd)) hP hQ hfst hsnd
  have hV := integral_centeredDistance_mul_eq_four_mul_squaredMMD P h2
  rw [hV]
  exact ⟨mul_nonneg (by norm_num) hnonneg, by simpa only [mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] using hzero, rfl⟩

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
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact isCharacteristicKernel_spectral_iff L hsym

/-- Products of two coordinates are integrable under a law with finite second moments. -/
theorem integrable_coord_mul_coord {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (h2 : MemLp id 2 P) (i j : Fin d) : Integrable (fun x ↦ x i * x j) P := by
  have hsq : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) P := h2.norm.integrable_sq
  refine hsq.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul (by simpa using PiLp.norm_apply_le x i) (by simpa using PiLp.norm_apply_le x j)
    (abs_nonneg _) (norm_nonneg _)

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
    (hP1.eval_piLp i).mul_prod (hQ1.eval_piLp i)
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
  simp only [squaredMMD_def]
  rw [integral_quadratic_kernel_prod P P hP hP, integral_quadratic_kernel_prod Q Q hQ hQ,
    integral_quadratic_kernel_prod P Q hP hQ, EuclideanSpace.norm_sq_eq]
  have hm : ∀ i, m i = (∫ x, x i ∂P) - ∫ x, x i ∂Q := fun i ↦ by
    simp only [m, PiLp.sub_apply]
    rw [eval_integral_piLp (f := fun x ↦ x) hP1.eval_piLp,
      eval_integral_piLp (f := fun x ↦ x) hQ1.eval_piLp]
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
      -- unfold the distance of the uncurried kernel values
      change |k x.1 x.2 - k y.1 y.2| ≤ 2 * C
      exact (abs_sub _ _).trans (by linarith [hC x.1 x.2, hC y.1 y.2])⟩⟩
  have heval := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have hPP : Continuous (fun P : ProbabilityMeasure X ↦ P.prod P) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have hPQ : Continuous (fun P : ProbabilityMeasure X ↦ P.prod Q) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_const)
  simp only [squaredMMD_def]
  exact ((heval.comp hPP).add continuous_const).sub
    (continuous_const.mul (heval.comp hPQ))

/-- GAPS 108.70, MMD metrizes weak convergence along uniformly tight sequences: for a bounded
continuous characteristic kernel on a separable metric space and a uniformly tight sequence of
probability laws `P n`, `P n → Q` weakly (in Mathlib's `ProbabilityMeasure` topology) exactly when
`MMD²(P n, Q) → 0`. -/
theorem tendsto_probabilityMeasure_iff_tendsto_squaredMMD_of_tight {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (P : ℕ → Measure X) (Q : Measure X) (hP : ∀ n, IsProbabilityMeasure (P n))
    [IsProbabilityMeasure Q] (k : X → X → ℝ)
    (hk : Continuous (Function.uncurry k)) (hb : ∃ C, ∀ x y, |k x y| ≤ C)
    (hchar : IsCharacteristicKernel k)
    (htight : ∀ epsilon > 0, ∃ K : Set X, IsCompact K ∧
      ∀ n, (P n) Kᶜ ≤ ENNReal.ofReal epsilon) :
    Tendsto (β := ProbabilityMeasure X) (fun n ↦ ⟨P n, hP n⟩) atTop (𝓝 ⟨Q, inferInstance⟩) ↔
      Tendsto (fun n ↦ squaredMMD k (P n) Q) atTop (𝓝 0) := by
  let Ps : ℕ → ProbabilityMeasure X := fun n ↦ ⟨P n, hP n⟩
  let Qs : ProbabilityMeasure X := ⟨Q, inferInstance⟩
  let F : ProbabilityMeasure X → ℝ := fun R ↦ squaredMMD k R Q
  have hF : Continuous F := continuous_squaredMMD_probabilityMeasure k hk hb Qs
  have hFQ : F Qs = 0 := by simp [F, Qs, squaredMMD_def]; ring
  constructor
  · intro h
    have hlim : Tendsto (fun n ↦ F (Ps n)) atTop (𝓝 (F Qs)) :=
      hF.continuousAt.tendsto.comp h
    rw [hFQ] at hlim
    exact hlim.congr' (Eventually.of_forall fun n ↦ by
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

end CKSD
