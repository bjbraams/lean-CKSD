module

public import CKSD.Geometry.EnergyDistance
public import TauCeti.Analysis.PositiveDefinite.Kernel.MeanEmbedding
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Distance kernels and separation of finite laws

The positive semidefinite distance kernel is obtained from the energy-distance criterion.
TauCeti's Kolmogorov feature map and kernel mean embedding identify its MMD with a squared
Hilbert norm. Finite atomic mixtures connect the measure criterion to positive semidefiniteness.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
namespace CKSD

/-- Distance-kernel sections are nonnegative and bounded by either endpoint's norm. -/
theorem distance_kernel_nonneg_le {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    0 ≤ distanceKernel x y ∧ distanceKernel x y ≤ ‖x‖ ∧ distanceKernel x y ≤ ‖y‖ := by
  have hxy := norm_sub_le x y
  have hx := norm_sub_le (x - y) (-y)
  have hy := norm_sub_le (y - x) (-x)
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at hx
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_sub_rev] at hy
  unfold distanceKernel
  constructor
  · linarith
  constructor <;> linarith

/-- Integrating a function against a finite atomic mixture is a finite weighted sum. -/
theorem integral_finite_atomic {E ι : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Fintype ι] (x : ι → E) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (f : E → ℝ) :
    (∫ y, f y ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))) = ∑ i, a i * f (x i) := by
  rw [integral_finsetSum_measure fun i _ ↦
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (ha _), integral_dirac, smul_eq_mul]

/-- Every real function is integrable under a finite atomic law. -/
theorem integrable_finite_atomic {E ι : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Fintype ι] (x : ι → E) (a : ι → ℝ) (f : E → ℝ) :
    Integrable f (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) := by
  rw [integrable_finsetSum_measure]
  exact fun i _ ↦ (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

/-- Integrating a kernel against two finite atomic laws gives its quadratic finite sum. -/
theorem integral_finite_atomic_prod {E ι κ : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Fintype ι] [Fintype κ] (x : ι → E) (y : κ → E) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (k : E → E → ℝ) :
    (∫ z : E × E, k z.1 z.2 ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)).prod
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))) =
      ∑ i, ∑ j, a i * b j * k (x i) (y j) := by
  rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.prod_sum]
  simp_rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac, smul_smul,
    ← ENNReal.ofReal_mul (ha _)]
  rw [Measure.sum_fintype, integral_finite_atomic (fun ij : ι × κ ↦ (x ij.1, y ij.2))
    (fun ij ↦ a ij.1 * b ij.2) (fun ij ↦ mul_nonneg (ha _) (hb _))]
  rw [Fintype.sum_prod_type]

/-- A finite atomic mixture with nonnegative weights summing to one is a probability measure. -/
theorem is_probability_measure_finite_atomic {E ι : Type*} [MeasurableSpace E]
    [Fintype ι] (x : ι → E) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : (∑ i, a i) = 1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) := by
  constructor
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ ha i), hsum, ENNReal.ofReal_one]

/-- Zero-sum finite coefficient families have nonnegative quadratic distance-kernel energy. -/
theorem distance_kernel_sum_nonneg_of_sum_eq_zero {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] (x : ι → E) (c : ι → ℝ) (hc0 : (∑ i, c i) = 0) :
    0 ≤ ∑ i, ∑ j, c i * c j * distanceKernel (x i) (x j) := by
  let a : ι → ℝ := fun i ↦ max (c i) 0
  let b : ι → ℝ := fun i ↦ max (-c i) 0
  have ha (i : ι) : 0 ≤ a i := le_max_right _ _
  have hb (i : ι) : 0 ≤ b i := le_max_right _ _
  have hc (i : ι) : c i = a i - b i := by
    dsimp only [a, b]
    rcases le_total 0 (c i) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
      ring
  let A := ∑ i, a i
  have hba : (∑ i, b i) = A := by
    have hsum : (∑ i, a i) - (∑ i, b i) = 0 := by
      rw [← Finset.sum_sub_distrib]
      simpa only [← hc] using hc0
    dsimp [A]
    linarith
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ ha i
  rcases hA0.eq_or_lt with hAz | hA
  · have haz : ∀ i, a i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ ha j).1 hAz.symm i (Finset.mem_univ i)
    have hbz : ∀ i, b i = 0 := fun i ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hb j).1 (hba.trans hAz.symm) i (Finset.mem_univ i)
    have hcz (i : ι) : c i = 0 := by rw [hc, haz, hbz]; ring
    simp [hcz]
  let an := fun i ↦ a i / A
  let bn := fun i ↦ b i / A
  have han (i : ι) : 0 ≤ an i := div_nonneg (ha i) hA.le
  have hbn (i : ι) : 0 ≤ bn i := div_nonneg (hb i) hA.le
  have hsa : (∑ i, an i) = 1 := by rw [← Finset.sum_div]; exact div_self hA.ne'
  have hsb : (∑ i, bn i) = 1 := by rw [← Finset.sum_div, hba]; exact div_self hA.ne'
  let P := ∑ i, ENNReal.ofReal (an i) • Measure.dirac (x i)
  let Q := ∑ i, ENNReal.ofReal (bn i) • Measure.dirac (x i)
  have := is_probability_measure_finite_atomic x an han hsa
  have := is_probability_measure_finite_atomic x bn hbn hsb
  have hPi : Integrable (fun y ↦ ‖y‖) P := integrable_finite_atomic x an _
  have hQi : Integrable (fun y ↦ ‖y‖) Q := integrable_finite_atomic x bn _
  have hMMD : 0 ≤ squaredMMD distanceKernel P Q := by
    have h := (energy_distance_nonneg_eq_zero_iff P Q hPi hQi).1
    rw [energy_distance_eq_two_mul_squared_mmd P Q hPi hQi] at h
    linarith
  let B (u v : ι → ℝ) := ∑ i, ∑ j, u i * v j * distanceKernel (x i) (x j)
  have hsymm : B b a = B a b := by
    dsimp only [B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [distanceKernel, norm_sub_rev]
    ring
  have hdiff : B c c = B a a + B b b - 2 * B a b := by
    have heq : B c c = B a a + B b b - B a b - B b a := by
      dsimp only [B]
      simp only [hc, sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [heq, hsymm]
    ring
  have hscale (u v : ι → ℝ) : B (fun i ↦ u i / A) (fun j ↦ v j / A) = B u v / A ^ 2 := by
    dsimp only [B]
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hrep : squaredMMD distanceKernel P Q =
      B a a / A ^ 2 + B b b / A ^ 2 - 2 * (B a b / A ^ 2) := by
    rw [squaredMMD,
      show (∫ z : E × E, distanceKernel z.1 z.2 ∂P.prod P) = B an an from
        integral_finite_atomic_prod x x an an han han _,
      show (∫ z : E × E, distanceKernel z.1 z.2 ∂Q.prod Q) = B bn bn from
        integral_finite_atomic_prod x x bn bn hbn hbn _,
      show (∫ z : E × E, distanceKernel z.1 z.2 ∂P.prod Q) = B an bn from
        integral_finite_atomic_prod x x an bn han hbn _]
    rw [show an = fun i ↦ a i / A from rfl, show bn = fun i ↦ b i / A from rfl,
      hscale, hscale, hscale]
  change 0 ≤ B c c
  have hfin : B c c = A ^ 2 * squaredMMD distanceKernel P Q := by
    rw [hrep, hdiff]
    field_simp
  rw [hfin]
  exact mul_nonneg (sq_nonneg _) hMMD

/-- The Euclidean distance-induced kernel is positive semidefinite. -/
theorem pos_semidef_distance_kernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Matrix.PosSemidef (distanceKernel : E → E → ℝ) := by
  rw [TauCeti.posSemidef_iff_finite_sum.{0, _, 0}]
  refine ⟨?_, ?_⟩
  · intro x y
    simp [distanceKernel, norm_sub_rev, add_comm]
  · intro ι _ x c
    let y : Option ι → E := fun i ↦ i.elim 0 x
    let d : Option ι → ℝ := fun i ↦ i.elim (-(∑ j, c j)) c
    have hd : (∑ i, d i) = 0 := by simp [d, Fintype.sum_option]
    have h := distance_kernel_sum_nonneg_of_sum_eq_zero y d hd
    simpa [y, d, Fintype.sum_option, distanceKernel, mul_comm, mul_left_comm, mul_assoc] using h

/-- The distance-induced kernel is symmetric. -/
theorem distance_kernel_comm {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    distanceKernel x y = distanceKernel y x := by simp [distanceKernel, norm_sub_rev, add_comm]

/-- A distance-kernel product integral is finite when its first law has a finite first moment. -/
theorem integrable_distance_kernel_prod {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) :
    Integrable (fun z : E × E ↦ distanceKernel z.1 z.2) (P.prod Q) := by
  refine (hP.comp_fst Q).mono' (by unfold distanceKernel; fun_prop) (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (distance_kernel_nonneg_le z.1 z.2).1]
  exact (distance_kernel_nonneg_le z.1 z.2).2.1

/-- Distance-kernel product integrals are symmetric in their two laws. -/
theorem integral_distance_kernel_prod_comm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    (∫ z : E × E, distanceKernel z.1 z.2 ∂P.prod Q) =
      ∫ z : E × E, distanceKernel z.1 z.2 ∂Q.prod P := by
  rw [integral_prod _ (integrable_distance_kernel_prod P Q hP),
    integral_prod_symm _ (integrable_distance_kernel_prod Q P hQ)]
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ integral_congr_ae (ae_of_all _ fun y ↦ distance_kernel_comm x y)

/-- The sections of the distance kernel determine finite equal-mass laws with finite first
moments. This extends the probability energy-distance criterion by normalization. -/
theorem measure_eq_of_integral_distance_kernel_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P Q : Measure E) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hmass : P univ = Q univ) (hP : Integrable (fun x ↦ ‖x‖) P)
    (hQ : Integrable (fun x ↦ ‖x‖) Q)
    (hsec : ∀ x, (∫ y, distanceKernel x y ∂P) = ∫ y, distanceKernel x y ∂Q) : P = Q := by
  by_cases hP0 : P univ = 0
  · have hp : P = 0 := Measure.measure_univ_eq_zero.1 hP0
    have hq : Q = 0 := Measure.measure_univ_eq_zero.1 (hmass ▸ hP0)
    rw [hp, hq]
  let c := P univ
  have hc : c ≠ 0 := hP0
  have hctop : c ≠ ∞ := measure_ne_top _ _
  let P' := c⁻¹ • P
  let Q' := c⁻¹ • Q
  have hP' : IsProbabilityMeasure P' := by
    constructor
    change c⁻¹ * P univ = 1
    exact ENNReal.inv_mul_cancel hc hctop
  have hQ' : IsProbabilityMeasure Q' := by
    constructor
    change c⁻¹ * Q univ = 1
    rw [← hmass]
    exact ENNReal.inv_mul_cancel hc hctop
  have := hP'
  have := hQ'
  have hPi : Integrable (fun x ↦ ‖x‖) P' := hP.smul_measure (ENNReal.inv_ne_top.2 hc)
  have hQi : Integrable (fun x ↦ ‖x‖) Q' := hQ.smul_measure (ENNReal.inv_ne_top.2 hc)
  have hsec' (x : E) : (∫ y, distanceKernel x y ∂P') = ∫ y, distanceKernel x y ∂Q' := by
    simp only [P', Q', integral_smul_measure, hsec x]
  have hPP : (∫ z : E × E, distanceKernel z.1 z.2 ∂P'.prod P') =
      ∫ z : E × E, distanceKernel z.1 z.2 ∂P'.prod Q' := by
    rw [integral_prod _ (integrable_distance_kernel_prod P' P' hPi),
      integral_prod _ (integrable_distance_kernel_prod P' Q' hPi)]
    exact integral_congr_ae (ae_of_all _ hsec')
  have hQQ : (∫ z : E × E, distanceKernel z.1 z.2 ∂Q'.prod Q') =
      ∫ z : E × E, distanceKernel z.1 z.2 ∂P'.prod Q' := by
    rw [integral_prod _ (integrable_distance_kernel_prod Q' Q' hQi),
      integral_distance_kernel_prod_comm P' Q' hPi hQi,
      integral_prod _ (integrable_distance_kernel_prod Q' P' hQi)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (hsec' x).symm)
  have hMMD : squaredMMD distanceKernel P' Q' = 0 := by
    rw [squaredMMD, hPP, hQQ]
    ring
  have hE : energyDistance P' Q' = 0 := by
    rw [energy_distance_eq_two_mul_squared_mmd P' Q' hPi hQi, hMMD, mul_zero]
  have hnorm := (energy_distance_nonneg_eq_zero_iff P' Q' hPi hQi).2.1 hE
  have h := congrArg (fun μ : Measure E ↦ c • μ) hnorm
  simpa only [P', Q', smul_smul, ENNReal.mul_inv_cancel hc hctop, one_smul] using h

/-- For a positive semidefinite kernel `k` whose feature map is integrable for `P` and `Q`, and
which is integrable against the three product measures, the squared MMD is the squared distance
`‖m_P - m_Q‖²` of TauCeti's kernel mean embeddings. -/
theorem squared_mmd_eq_norm_kernel_mean_embedding_sub_sq {X : Type*} [MeasurableSpace X]
    {k : X → X → ℝ} (hk : Matrix.PosSemidef k) {P Q : Measure X} [SFinite P] [SFinite Q]
    (hP : Integrable hk.kolmogorovFeature P) (hQ : Integrable hk.kolmogorovFeature Q)
    (hPP : Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod P))
    (hQQ : Integrable (fun z : X × X ↦ k z.1 z.2) (Q.prod Q))
    (hPQ : Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod Q)) :
    squaredMMD k P Q = ‖hk.kernelMeanEmbedding P - hk.kernelMeanEmbedding Q‖ ^ 2 := by
  rw [hk.norm_kernelMeanEmbedding_sub_sq hP hQ, squaredMMD, integral_prod_symm _ hPP,
    integral_prod_symm _ hQQ, integral_prod_symm _ hPQ]
  ring


/-- The tensor product of the two distance-induced kernels. -/
def distanceProductKernel {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (x y : E × F) : ℝ := distanceKernel x.1 y.1 * distanceKernel x.2 y.2

/-- The product of distance-induced kernels is positive semidefinite. -/
theorem pos_semidef_distance_product_kernel {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] :
    Matrix.PosSemidef (distanceProductKernel : (E × F) → (E × F) → ℝ) := by
  exact ((pos_semidef_distance_kernel (E := E)).submatrix Prod.fst).hadamard
    ((pos_semidef_distance_kernel (E := F)).submatrix Prod.snd)

/-- Product distance-kernel values are nonnegative and bounded by the product of the two
observation norms. -/
theorem distance_product_kernel_nonneg_le {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (z w : E × F) :
    0 ≤ distanceProductKernel z w ∧ distanceProductKernel z w ≤ ‖z‖ * ‖w‖ := by
  have hx := distance_kernel_nonneg_le z.1 w.1
  have hy := distance_kernel_nonneg_le z.2 w.2
  refine ⟨mul_nonneg hx.1 hy.1, ?_⟩
  exact mul_le_mul (hx.2.1.trans (norm_fst_le z)) (hy.2.2.trans (norm_snd_le w))
    hy.1 (norm_nonneg z)

/-- The product distance kernel is integrable against product laws with finite first moments. -/
theorem integrable_distance_product_kernel_prod {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (P Q : Measure (E × F)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    Integrable (fun z : (E × F) × (E × F) ↦ distanceProductKernel z.1 z.2) (P.prod Q) := by
  refine (hP.mul_prod hQ).mono' (by unfold distanceProductKernel distanceKernel; fun_prop)
    (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (distance_product_kernel_nonneg_le z.1 z.2).1]
  exact (distance_product_kernel_nonneg_le z.1 z.2).2

/-- The canonical feature map of the product distance kernel is integrable under every law
with a finite first moment. -/
theorem integrable_distance_product_feature {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (P : Measure (E × F))
    (hP : Integrable (fun x ↦ ‖x‖) P) :
    Integrable (pos_semidef_distance_product_kernel (E := E) (F := F)).kolmogorovFeature P := by
  let hk := pos_semidef_distance_product_kernel (E := E) (F := F)
  have hkc : Continuous (Function.uncurry (distanceProductKernel : (E × F) → (E × F) → ℝ)) := by
    unfold distanceProductKernel distanceKernel
    fun_prop
  refine hP.mono' (hk.continuous_kolmogorovFeature hkc).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  have hdiag : ‖hk.kolmogorovFeature z‖ ^ 2 = ‖z.1‖ * ‖z.2‖ := by
    rw [hk.norm_kolmogorovFeature_sq]
    simp [distanceProductKernel, distanceKernel]
  have hm := mul_le_mul (norm_fst_le z) (norm_snd_le z) (norm_nonneg _) (norm_nonneg z)
  nlinarith [norm_nonneg (hk.kolmogorovFeature z), norm_nonneg z]

/-- Vanishing product-kernel MMD gives equality of every product-kernel section integral. -/
theorem integral_distance_product_kernel_eq_of_squared_mmd_eq_zero {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (P Q : Measure (E × F)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q)
    (hzero : squaredMMD distanceProductKernel P Q = 0) (z : E × F) :
    (∫ w, distanceProductKernel z w ∂P) = ∫ w, distanceProductKernel z w ∂Q := by
  let hk := pos_semidef_distance_product_kernel (E := E) (F := F)
  have hPi := integrable_distance_product_feature P hP
  have hQi := integrable_distance_product_feature Q hQ
  have hnorm := squared_mmd_eq_norm_kernel_mean_embedding_sub_sq hk hPi hQi
    (integrable_distance_product_kernel_prod P P hP hP)
    (integrable_distance_product_kernel_prod Q Q hQ hQ)
    (integrable_distance_product_kernel_prod P Q hP hQ)
  rw [hzero] at hnorm
  have heq : hk.kernelMeanEmbedding P = hk.kernelMeanEmbedding Q :=
    sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hnorm.symm))
  rw [← hk.inner_kolmogorovFeature_kernelMeanEmbedding hPi z,
    ← hk.inner_kolmogorovFeature_kernelMeanEmbedding hQi z, heq]

end CKSD
