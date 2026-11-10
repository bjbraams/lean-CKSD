module
public import CKSD.Geometry.DistanceKernel
/-!
# Double centering and distance covariance

Double centering two symmetric square-integrable kernels cancels their marginal terms.
For distance-induced kernels, the centered distances are minus twice the centered kernels.
Fubini and the independent marginal product then identify distance covariance with four times
the squared maximum mean discrepancy of the product distance kernel.

The arguments use Mathlib's product-integral and square-integrable product APIs.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- Linearity of the integral of a centered expression against a square-integrable function. -/
theorem integral_sub_sub_add_mul {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (f r s b : Z → ℝ)
    (hf : MemLp f 2 μ) (hr : MemLp r 2 μ) (hs : MemLp s 2 μ)
    (hb : MemLp b 2 μ) (c : ℝ) :
    (∫ z, (f z - r z - s z + c) * b z ∂μ) =
      (∫ z, f z * b z ∂μ) - (∫ z, r z * b z ∂μ) -
        (∫ z, s z * b z ∂μ) + c * ∫ z, b z ∂μ := by
  simp_rw [add_mul, sub_mul]
  have h1 := integral_sub (hf.integrable_mul hb) (hr.integrable_mul hb)
  have h2 := integral_sub ((hf.integrable_mul hb).sub (hr.integrable_mul hb)) (hs.integrable_mul hb)
  have h3 := integral_add (((hf.integrable_mul hb).sub (hr.integrable_mul hb)).sub
    (hs.integrable_mul hb)) ((hb.integrable (by norm_num)).const_mul c)
  simp only [Pi.sub_apply, Pi.mul_apply] at h1 h2 h3
  rw [h3, h2, h1, integral_const_mul]

/-- Integrating a symmetric kernel against a one-coordinate weight uses its marginal mean. -/
theorem integral_kernel_mul_fst {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (a : Z → Z → ℝ) (b : Z → ℝ)
    (h : Integrable (fun z : Z × Z ↦ a z.1 z.2 * b z.1) (μ.prod μ)) :
    (∫ z, a z.1 z.2 * b z.1 ∂μ.prod μ) = ∫ x, (∫ y, a x y ∂μ) * b x ∂μ := by
  rw [integral_prod _ h]
  simp_rw [integral_mul_const]

/-- Symmetry permits the same marginal reduction in the second coordinate. -/
theorem integral_kernel_mul_snd {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (a : Z → Z → ℝ) (b : Z → ℝ)
    (ha : ∀ x y, a x y = a y x)
    (h : Integrable (fun z : Z × Z ↦ a z.1 z.2 * b z.2) (μ.prod μ)) :
    (∫ z, a z.1 z.2 * b z.2 ∂μ.prod μ) = ∫ x, (∫ y, a x y ∂μ) * b x ∂μ := by
  rw [integral_prod_symm _ h]
  simp_rw [ha, integral_mul_const]

/-- Double centering two symmetric square-integrable kernels cancels the marginal terms. -/
theorem integral_double_centered_kernels {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (a b : Z → Z → ℝ)
    (ha : ∀ x y, a x y = a y x) (hb : ∀ x y, b x y = b y x)
    (hA : MemLp (fun z : Z × Z ↦ a z.1 z.2) 2 (μ.prod μ))
    (hB : MemLp (fun z : Z × Z ↦ b z.1 z.2) 2 (μ.prod μ))
    (hα : MemLp (fun x ↦ ∫ y, a x y ∂μ) 2 μ)
    (hβ : MemLp (fun x ↦ ∫ y, b x y ∂μ) 2 μ) :
    let α := fun x ↦ ∫ y, a x y ∂μ;
    let β := fun x ↦ ∫ y, b x y ∂μ;
    let c := ∫ x, α x ∂μ;
    let d := ∫ x, β x ∂μ;
    (∫ z, (a z.1 z.2 - α z.1 - α z.2 + c) *
      (b z.1 z.2 - β z.1 - β z.2 + d) ∂μ.prod μ) =
      (∫ z, a z.1 z.2 * b z.1 z.2 ∂μ.prod μ) - 2 * (∫ x, α x * β x ∂μ) + c * d := by
  intro α β c d
  let ac := fun z : Z × Z ↦ a z.1 z.2 - α z.1 - α z.2 + c
  have hac : MemLp ac 2 (μ.prod μ) :=
    ((hA.sub (hα.comp_fst μ)).sub (hα.comp_snd μ)).add (memLp_const c)
  have hab : (∫ z, a z.1 z.2 * β z.1 ∂μ.prod μ) = ∫ x, α x * β x ∂μ :=
    integral_kernel_mul_fst μ a β (hA.integrable_mul (hβ.comp_fst μ))
  have hab' : (∫ z, a z.1 z.2 * β z.2 ∂μ.prod μ) = ∫ x, α x * β x ∂μ :=
    integral_kernel_mul_snd μ a β ha (hA.integrable_mul (hβ.comp_snd μ))
  have hba : (∫ z, b z.1 z.2 * α z.1 ∂μ.prod μ) = ∫ x, α x * β x ∂μ := by
    rw [integral_kernel_mul_fst μ b α (hB.integrable_mul (hα.comp_fst μ))]
    congr 1
    funext x
    exact mul_comm _ _
  have hba' : (∫ z, b z.1 z.2 * α z.2 ∂μ.prod μ) = ∫ x, α x * β x ∂μ := by
    rw [integral_kernel_mul_snd μ b α hb (hB.integrable_mul (hα.comp_snd μ))]
    congr 1
    funext x
    exact mul_comm _ _
  have hmeanA : (∫ z, a z.1 z.2 ∂μ.prod μ) = c := integral_prod _ (hA.integrable (by norm_num))
  have hmeanB : (∫ z, b z.1 z.2 ∂μ.prod μ) = d := integral_prod _ (hB.integrable (by norm_num))
  have hmeanac : (∫ z, ac z ∂μ.prod μ) = 0 := by
    dsimp only [ac]
    have h1 := integral_sub (hA.integrable (by norm_num)) ((hα.comp_fst μ).integrable (by norm_num))
    have h2 := integral_sub ((hA.integrable (by norm_num)).sub
      ((hα.comp_fst μ).integrable (by norm_num))) ((hα.comp_snd μ).integrable (by norm_num))
    have h3 := integral_add (((hA.integrable (by norm_num)).sub
      ((hα.comp_fst μ).integrable (by norm_num))).sub
      ((hα.comp_snd μ).integrable (by norm_num))) (integrable_const c)
    simp only [Pi.sub_apply] at h1 h2 h3
    rw [h3, h2, h1]
    change (∫ z, a z.1 z.2 ∂μ.prod μ) - (∫ z : Z × Z, α z.1 ∂μ.prod μ) -
      (∫ z : Z × Z, α z.2 ∂μ.prod μ) + (∫ _ : Z × Z, c ∂μ.prod μ) = 0
    rw [hmeanA, integral_fun_fst α, integral_fun_snd α]
    simp only [integral_const, probReal_univ, one_smul]
    change c - c - c + c = 0
    ring
  have hzero1 : (∫ z, ac z * β z.1 ∂μ.prod μ) = 0 := by
    rw [integral_sub_sub_add_mul _ _ _ _ _ hA (hα.comp_fst μ) (hα.comp_snd μ)
      (hβ.comp_fst μ) c, hab]
    rw [show (∫ z : Z × Z, α z.1 * β z.1 ∂μ.prod μ) = ∫ x, α x * β x ∂μ by
      simpa using (integral_fun_fst (μ := μ) (ν := μ) (fun x ↦ α x * β x)),
      show (∫ z : Z × Z, α z.2 * β z.1 ∂μ.prod μ) = c * d by
        rw [show (fun z : Z × Z ↦ α z.2 * β z.1) = fun z ↦ β z.1 * α z.2 by
          funext z; ring, integral_prod_mul]; dsimp [c,d]; ring]
    change (∫ x, α x * β x ∂μ) - (∫ x, α x * β x ∂μ) - c*d +
      c * (∫ z : Z × Z, β z.1 ∂μ.prod μ) = 0
    rw [integral_fun_fst β]
    simp only [probReal_univ, one_smul]
    change (∫ x, α x * β x ∂μ) - (∫ x, α x * β x ∂μ) - c * d + c * d = 0
    ring
  have hzero2 : (∫ z, ac z * β z.2 ∂μ.prod μ) = 0 := by
    rw [integral_sub_sub_add_mul _ _ _ _ _ hA (hα.comp_fst μ) (hα.comp_snd μ)
      (hβ.comp_snd μ) c, hab']
    rw [integral_prod_mul (μ := μ) (ν := μ) α β]
    rw [show (∫ z : Z × Z, α z.2 * β z.2 ∂μ.prod μ) = ∫ x, α x * β x ∂μ by
      simpa using (integral_fun_snd (μ := μ) (ν := μ) (fun x ↦ α x * β x))]
    change (∫ x, α x * β x ∂μ) - c*d - (∫ x, α x * β x ∂μ) +
      c * (∫ z : Z × Z, β z.2 ∂μ.prod μ) = 0
    rw [integral_fun_snd β]
    simp only [probReal_univ, one_smul]
    change (∫ x, α x * β x ∂μ) - c*d - (∫ x, α x * β x ∂μ) + c*d = 0
    ring
  have hlast : (∫ z, ac z * b z.1 z.2 ∂μ.prod μ) =
      (∫ z, a z.1 z.2 * b z.1 z.2 ∂μ.prod μ) - 2*(∫ x, α x * β x ∂μ) + c*d := by
    rw [integral_sub_sub_add_mul _ _ _ _ _ hA (hα.comp_fst μ) (hα.comp_snd μ) hB c]
    have ht1 : (∫ z, α z.1 * b z.1 z.2 ∂μ.prod μ) = ∫ x, α x * β x ∂μ := by
      simpa only [mul_comm] using hba
    have ht2 : (∫ z, α z.2 * b z.1 z.2 ∂μ.prod μ) = ∫ x, α x * β x ∂μ := by
      simpa only [mul_comm] using hba'
    rw [ht1, ht2, hmeanB]
    ring
  calc
    _ = ∫ z : Z × Z, (b z.1 z.2 - β z.1 - β z.2 + d) * ac z ∂μ.prod μ := by
      congr 1
      funext z
      exact mul_comm _ _
    _ = (∫ z, b z.1 z.2 * ac z ∂μ.prod μ) := by
      rw [integral_sub_sub_add_mul _ _ _ _ _ hB (hβ.comp_fst μ) (hβ.comp_snd μ) hac d]
      have hz1 : (∫ z, β z.1 * ac z ∂μ.prod μ) = 0 := by simpa only [mul_comm] using hzero1
      have hz2 : (∫ z, β z.2 * ac z ∂μ.prod μ) = 0 := by simpa only [mul_comm] using hzero2
      rw [hz1, hz2, hmeanac]
      ring
    _ = _ := by simpa only [mul_comm] using hlast

/-- The mean of a distance-kernel section in terms of the mean distance. -/
theorem integral_distanceKernel_right {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure E) [IsProbabilityMeasure P] (hP : Integrable (fun x ↦ ‖x‖) P) (x : E) :
    (∫ y, distanceKernel x y ∂P) =
      (‖x‖ + (∫ y, ‖y‖ ∂P) - (∫ y, ‖x-y‖ ∂P)) / 2 := by
  have hs : Integrable (fun y ↦ ‖x‖ + ‖y‖) P := (integrable_const _).add hP
  have hd : Integrable (fun y ↦ ‖x-y‖) P :=
    hs.mono' (by fun_prop) (ae_of_all _ fun y ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using norm_sub_le x y)
  unfold distanceKernel
  rw [integral_div, integral_sub hs hd, integral_add (integrable_const _) hP, integral_const]
  simp

/-- A centered distance is minus twice the centered distance kernel. -/
theorem centeredDistance_eq_neg_two_mul_centered_kernel {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure E) [IsProbabilityMeasure P] (hP : Integrable (fun x ↦ ‖x‖) P) (x y : E) :
    centeredDistance P x y = -2 * (distanceKernel x y -
      (∫ z, distanceKernel x z ∂P) - (∫ z, distanceKernel y z ∂P) +
      (∫ z, ∫ w, distanceKernel z w ∂P ∂P)) := by
  rw [← integral_prod _ (integrable_distanceKernel_prod P P hP),
    integral_distanceKernel_prod P P hP hP, integral_distanceKernel_right P hP x,
    integral_distanceKernel_right P hP y]
  unfold centeredDistance distanceKernel
  simp_rw [dist_eq_norm, norm_sub_rev _ y]
  ring

/-- Kernel means dominated by a coordinate norm retain its second moment. -/
theorem memLp_kernelMean_of_dominated {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (a : Z → Z → ℝ) (w : Z → ℝ)
    (ha : Measurable (Function.uncurry a)) (hw : MemLp w 2 P)
    (hbd : ∀ x y, ‖a x y‖ ≤ w x) :
    MemLp (fun x ↦ ∫ y, a x y ∂P) 2 P := by
  refine hw.mono' ha.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  exact by simpa using (norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ (hbd x)))

/-- Finite first moments persist when the coordinates are made independent. -/
theorem integrable_norm_prod_marginals {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (P : Measure (E × F)) [IsProbabilityMeasure P]
    (hP : Integrable (fun z ↦ ‖z‖) P) :
    Integrable (fun z ↦ ‖z‖) ((P.map Prod.fst).prod (P.map Prod.snd)) := by
  have hfst : Integrable (fun z : E × F ↦ ‖z.1‖) P :=
    hP.mono' (by fun_prop) (ae_of_all _ fun z ↦ by simpa using norm_fst_le z)
  have hsnd : Integrable (fun z : E × F ↦ ‖z.2‖) P :=
    hP.mono' (by fun_prop) (ae_of_all _ fun z ↦ by simpa using norm_snd_le z)
  have hμ : Integrable (fun x : E ↦ ‖x‖) (P.map Prod.fst) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).2 hfst
  have hν : Integrable (fun y : F ↦ ‖y‖) (P.map Prod.snd) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).2 hsnd
  refine ((hμ.comp_fst _).add (hν.comp_snd _)).mono' (by fun_prop) (ae_of_all _ fun z ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  change max ‖z.1‖ ‖z.2‖ ≤ _
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- Distance-kernel means are measurable. -/
theorem measurable_integral_distanceKernel {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure E) [SFinite P] : Measurable (fun x ↦ ∫ y, distanceKernel x y ∂P) := by
  have hm : StronglyMeasurable (Function.uncurry (distanceKernel : E → E → ℝ)) := by
    unfold distanceKernel
    fun_prop
  exact hm.integral_prod_right.measurable

/-- Independent marginal averaging factors the product distance kernel. -/
theorem integral_distanceProductKernel_prod_marginals_right {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (P : Measure (E × F)) [IsProbabilityMeasure P] (x : E × F) :
    (∫ y, distanceProductKernel x y ∂(P.map Prod.fst).prod (P.map Prod.snd)) =
      (∫ y, distanceKernel x.1 y.1 ∂P) * (∫ y, distanceKernel x.2 y.2 ∂P) := by
  change (∫ y, distanceKernel x.1 y.1 * distanceKernel x.2 y.2
    ∂(P.map Prod.fst).prod (P.map Prod.snd)) = _
  rw [integral_prod_mul, integral_map (by fun_prop) (by unfold distanceKernel; fun_prop),
    integral_map (by fun_prop) (by unfold distanceKernel; fun_prop)]

/-- Product-kernel MMD against the independent marginals has the double-centering expansion. -/
theorem squaredMMD_distanceProductKernel_prod_marginals {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (P : Measure (E × F)) [IsProbabilityMeasure P]
    (hP : Integrable (fun z ↦ ‖z‖) P) :
    let α := fun x : E ↦ ∫ y, distanceKernel x y ∂P.map Prod.fst;
    let β := fun x : F ↦ ∫ y, distanceKernel x y ∂P.map Prod.snd;
    squaredMMD distanceProductKernel P ((P.map Prod.fst).prod (P.map Prod.snd)) =
      (∫ z, distanceProductKernel z.1 z.2 ∂P.prod P) - 2 * (∫ z, α z.1 * β z.2 ∂P) +
      (∫ z, α z.1 ∂P) * (∫ z, β z.2 ∂P) := by
  intro α β
  let Q := (P.map Prod.fst).prod (P.map Prod.snd)
  have hQ := integrable_norm_prod_marginals P hP
  have hinner (x : E × F) : (∫ y, distanceProductKernel x y ∂Q) = α x.1 * β x.2 := by
    rw [integral_distanceProductKernel_prod_marginals_right]
    dsimp only [α, β]
    rw [integral_map (by fun_prop) (by unfold distanceKernel; fun_prop),
      integral_map (by fun_prop) (by unfold distanceKernel; fun_prop)]
  have hpq : (∫ z, distanceProductKernel z.1 z.2 ∂P.prod Q) = ∫ z, α z.1 * β z.2 ∂P := by
    rw [integral_prod _ (integrable_distanceProductKernel_prod P Q hP hQ)]
    simp_rw [hinner]
  have hqq : (∫ z, distanceProductKernel z.1 z.2 ∂Q.prod Q) =
      (∫ z, α z.1 ∂P) * (∫ z, β z.2 ∂P) := by
    rw [integral_prod _ (integrable_distanceProductKernel_prod Q Q hQ hQ)]
    simp_rw [hinner]
    change (∫ z, α z.1 * β z.2 ∂(P.map Prod.fst).prod (P.map Prod.snd)) = _
    rw [integral_prod_mul, integral_map (by fun_prop)
      (measurable_integral_distanceKernel _).aestronglyMeasurable,
      integral_map (by fun_prop) (measurable_integral_distanceKernel _).aestronglyMeasurable]
  unfold squaredMMD
  rw [hpq, hqq]
  ring

/-- Distance covariance equals four times the product distance-kernel MMD. -/
theorem integral_centeredDistance_mul_eq_four_mul_squaredMMD
    {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (P : Measure (E × F)) [IsProbabilityMeasure P]
    (h2 : MemLp id 2 P) :
    (∫ z, centeredDistance (P.map Prod.fst) z.1.1 z.2.1 *
      centeredDistance (P.map Prod.snd) z.1.2 z.2.2 ∂P.prod P) =
      4 * squaredMMD distanceProductKernel P ((P.map Prod.fst).prod (P.map Prod.snd)) := by
  let a : (E × F) → (E × F) → ℝ := fun x y ↦ distanceKernel x.1 y.1
  let b : (E × F) → (E × F) → ℝ := fun x y ↦ distanceKernel x.2 y.2
  let α := fun x ↦ ∫ y, a x y ∂P
  let β := fun x ↦ ∫ y, b x y ∂P
  let c := ∫ x, α x ∂P
  let d := ∫ x, β x ∂P
  have hx : MemLp (fun z : E × F ↦ z.1) 2 P :=
    h2.mono (by fun_prop) (ae_of_all _ norm_fst_le)
  have hy : MemLp (fun z : E × F ↦ z.2) 2 P :=
    h2.mono (by fun_prop) (ae_of_all _ norm_snd_le)
  have ha : Measurable (Function.uncurry a) := by dsimp [a]; unfold distanceKernel; fun_prop
  have hb : Measurable (Function.uncurry b) := by dsimp [b]; unfold distanceKernel; fun_prop
  have hba (x y : E × F) : ‖a x y‖ ≤ ‖x.1‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (distanceKernel_nonneg_le _ _).1]
    exact (distanceKernel_nonneg_le _ _).2.1
  have hbb (x y : E × F) : ‖b x y‖ ≤ ‖x.2‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (distanceKernel_nonneg_le _ _).1]
    exact (distanceKernel_nonneg_le _ _).2.1
  have hA : MemLp (fun z : (E × F) × (E × F) ↦ a z.1 z.2) 2 (P.prod P) :=
    (hx.norm.comp_fst P).mono' ha.aestronglyMeasurable (ae_of_all _ fun z ↦ hba z.1 z.2)
  have hB : MemLp (fun z : (E × F) × (E × F) ↦ b z.1 z.2) 2 (P.prod P) :=
    (hy.norm.comp_fst P).mono' hb.aestronglyMeasurable (ae_of_all _ fun z ↦ hbb z.1 z.2)
  have hα : MemLp α 2 P := memLp_kernelMean_of_dominated P a _ ha hx.norm hba
  have hβ : MemLp β 2 P := memLp_kernelMean_of_dominated P b _ hb hy.norm hbb
  have hcan := integral_double_centered_kernels P a b
    (fun x y ↦ distanceKernel_comm _ _) (fun x y ↦ distanceKernel_comm _ _) hA hB hα hβ
  change (∫ z, (a z.1 z.2 - α z.1 - α z.2 + c) *
    (b z.1 z.2 - β z.1 - β z.2 + d) ∂P.prod P) = _ at hcan
  have hμ : Integrable (fun x : E ↦ ‖x‖) (P.map Prod.fst) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).2 (hx.norm.integrable (by norm_num))
  have hν : Integrable (fun x : F ↦ ‖x‖) (P.map Prod.snd) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).2 (hy.norm.integrable (by norm_num))
  have hxmean (x : E) : (∫ z, distanceKernel x z ∂P.map Prod.fst) =
      ∫ z, distanceKernel x z.1 ∂P := integral_map (by fun_prop) (by unfold distanceKernel; fun_prop)
  have hymean (x : F) : (∫ z, distanceKernel x z ∂P.map Prod.snd) =
      ∫ z, distanceKernel x z.2 ∂P := integral_map (by fun_prop) (by unfold distanceKernel; fun_prop)
  have hcentx (x y : E × F) : centeredDistance (P.map Prod.fst) x.1 y.1 =
      -2 * (a x y - α x - α y + c) := by
    rw [centeredDistance_eq_neg_two_mul_centered_kernel _ hμ,
      integral_map (by fun_prop) (measurable_integral_distanceKernel _).aestronglyMeasurable]
    simp_rw [hxmean]
    rfl
  have hcenty (x y : E × F) : centeredDistance (P.map Prod.snd) x.2 y.2 =
      -2 * (b x y - β x - β y + d) := by
    rw [centeredDistance_eq_neg_two_mul_centered_kernel _ hν,
      integral_map (by fun_prop) (measurable_integral_distanceKernel _).aestronglyMeasurable]
    simp_rw [hymean]
    rfl
  have hmmd := squaredMMD_distanceProductKernel_prod_marginals P
    ((h2.integrable (by norm_num)).norm)
  simp_rw [hxmean, hymean] at hmmd
  change squaredMMD distanceProductKernel P ((P.map Prod.fst).prod (P.map Prod.snd)) =
    (∫ z, a z.1 z.2 * b z.1 z.2 ∂P.prod P) - 2 * (∫ z, α z * β z ∂P) + c*d at hmmd
  rw [hmmd, ← hcan, ← integral_const_mul]
  congr 1
  funext z
  rw [hcentx, hcenty]
  ring
end CKSD
