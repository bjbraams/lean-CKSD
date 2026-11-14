module

public import CKSD.Inference.KernelDisintegration
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext
public import CKSD.Asymptotics.GaussianShiftComplete
public import CKSD.Asymptotics.KernelTranslation
public import CKSD.Asymptotics.GaussianKernelTranslation
public import CKSD.Asymptotics.KernelConvolution
/-!
# Complete kernel identification and residual laws

A boundedly complete family identifies Markov kernels from their averaged laws. Equality of
all measurable-set masses lifts to almost-everywhere equality of entire probability rows.
For nondegenerate Gaussian location families this gives the kernel uniqueness needed by
Hájek's convolution theorem. The residual kernel records an output minus its input.

Mathlib supplies measurable kernel maps, product kernels and real-valued conditional masses.
Pinned TauCeti supplies almost-everywhere extensionality of random probability measures. Local
Gaussian completeness and translation invariance provide the classification ingredients for
GAPS 102.16, giving a completeness-based proof of the Gaussian convolution result in
van der Vaart (1998), Proposition 8.4
and Theorem 8.8, printed pages 113–115.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Function
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace CKSD
/-- The residual kernel records the output minus the observed input. -/
def residualKernel {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Kernel E E) : Kernel E E :=
  (Kernel.id ×ₖ K).map (fun z : E × E ↦ z.2-z.1)

/-- Residual kernels remain Markov kernels. -/
instance isMarkovKernel_residualKernel {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (K : Kernel E E) [IsMarkovKernel K] :
    IsMarkovKernel (residualKernel K) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- A residual row is the translated output distribution. -/
theorem residual_kernel_apply {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : Kernel E E) [IsMarkovKernel K] (x : E) :
    residualKernel K x = (K x).map (fun y ↦ y-x) := by
  rw [residualKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A boundedly complete family identifies Markov kernels up to almost-everywhere equality. -/
theorem ae_eq_kernel_of_bounded_complete
    {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y] [CountablyGenerated Y]
    (ν : Measure X) (μ : H → Measure X) [∀ h, IsProbabilityMeasure (μ h)]
    (hcomplete : ∀ (f : X → ℝ), Measurable f → ∀ M : ℝ, (∀ x, |f x|≤M) →
      (∀ h, ∫ x,f x ∂μ h=0) → ∀ᵐ x ∂ν,f x=0)
    (K J : Kernel X Y) [IsMarkovKernel K] [IsMarkovKernel J]
    (heq : ∀ h,K ∘ₘ μ h=J ∘ₘ μ h) : ∀ᵐ x ∂ν,K x=J x := by
  have hall (A : Set Y) (hA : MeasurableSet A) : ∀ᵐ x ∂ν,K x A=J x A := by
    let f : X → ℝ := fun x ↦ (K x).real A-(J x).real A
    have hm : Measurable f := (K.measurable_coe hA).ennreal_toReal.sub
      (J.measurable_coe hA).ennreal_toReal
    have hb (x : X) : |f x|≤2 := by
      have hK : (K x).real A≤1 := by exact measureReal_le_one
      have hJ : (J x).real A≤1 := by exact measureReal_le_one
      have hKn : 0≤(K x).real A := ENNReal.toReal_nonneg
      have hJn : 0≤(J x).real A := ENNReal.toReal_nonneg
      dsimp [f]
      rw [abs_le]
      constructor <;> linarith
    have hint (η : Kernel X Y) [IsMarkovKernel η] (h : H) :
        Integrable (fun x ↦ (η x).real A) (μ h) := by
      apply Integrable.of_bound (η.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1
      exact ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
        exact measureReal_le_one
    have hz (h : H) : ∫ x,f x ∂μ h=0 := by
      rw [show f=(fun x ↦ (K x).real A-(J x).real A) from rfl,
        integral_sub (hint K h) (hint J h),integral_kernel_real_apply _ _ hA,
        integral_kernel_real_apply _ _ hA,heq h,sub_self]
    have hc := hcomplete f hm 2 hb hz
    filter_upwards [hc] with x hx
    have hr : (K x).real A=(J x).real A := sub_eq_zero.mp hx
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hr
  let P : X → ProbabilityMeasure Y := fun x ↦ ⟨K x,inferInstance⟩
  let Q : X → ProbabilityMeasure Y := fun x ↦ ⟨J x,inferInstance⟩
  have he := ProbabilityMeasure.ae_eq_of_forall_apply_ae_eq (ν := P) (ν' := Q) hall
  exact he.mono fun x hx ↦ congrArg ProbabilityMeasure.toMeasure hx
/-- Equal randomizations of every nondegenerate Gaussian shift identify their kernels
Lebesgue-almost everywhere. -/
theorem ae_eq_kernel_of_multivariate_gaussian_comp_eq
    {d : ℕ} {Y : Type*} [MeasurableSpace Y] [CountablyGenerated Y]
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (K J : Kernel (EuclideanSpace ℝ (Fin d)) Y) [IsMarkovKernel K] [IsMarkovKernel J]
    (heq : ∀ h,K ∘ₘ multivariateGaussian h S=J ∘ₘ multivariateGaussian h S) :
    ∀ᵐ x ∂volume,K x=J x := by
  exact ae_eq_kernel_of_bounded_complete volume (fun h ↦ multivariateGaussian h S)
    (fun f hf M hM hzero ↦ ae_eq_zero_of_bounded_integral_multivariate_gaussian_eq_zero hS f hf M hM hzero)
    K J heq
section GaussianClassification
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Gaussian shift equivariance forces almost-everywhere translation covariance of the
randomization kernel. -/
theorem ae_covariant_kernel_of_gaussian_shift_laws
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (K : Kernel E E) [IsMarkovKernel K] (L : Measure E)
    (hLaw : ∀ h,K ∘ₘ multivariateGaussian h S=L.map (fun y ↦ h+y)) (a : E) :
    ∀ᵐ x ∂volume,(K (a+x)).map (fun y ↦ y-a)=K x := by
  let J : Kernel E E := (K.comap (fun x ↦ a+x) (by fun_prop)).map (fun y ↦ y-a)
  have : IsMarkovKernel J := Kernel.IsMarkovKernel.map _ (by fun_prop)
  have heq (h : E) : J ∘ₘ multivariateGaussian h S=K ∘ₘ multivariateGaussian h S := by
    change ((K.comap (fun x ↦ a+x) (by fun_prop)).map (fun y ↦ y-a)) ∘ₘ multivariateGaussian h S = _
    rw [translated_kernel_comp_multivariate_gaussian K a h hS.posSemidef,hLaw (a+h),
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hfun : (fun y ↦ y-a) ∘ (fun y : E ↦ (a+h)+y) = fun y ↦ h+y := by
      funext y
      dsimp only [Function.comp_def]
      abel
    rw [hfun]
    exact (hLaw h).symm
  have he := ae_eq_kernel_of_multivariate_gaussian_comp_eq hS J K heq
  filter_upwards [he] with x hx
  change ((K.comap (fun x ↦ a+x) (by fun_prop)).map (fun y ↦ y-a)) x=K x at hx
  have hm : Measurable (fun y : E ↦ y-a) := by fun_prop
  rw [Kernel.map_apply _ hm,Kernel.comap_apply] at hx
  exact hx
end GaussianClassification

/-- Translation covariance of output rows makes the corresponding residual rows invariant. -/
theorem ae_residual_kernel_add_eq_of_ae_covariant
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ν : Measure E) (K : Kernel E E) [IsMarkovKernel K]
    (a : E) (hcov : ∀ᵐ x ∂ν,(K (a+x)).map (fun y ↦ y-a)=K x) :
    ∀ᵐ x ∂ν,residualKernel K (a+x)=residualKernel K x := by
  filter_upwards [hcov] with x hx
  rw [residual_kernel_apply K (a+x),residual_kernel_apply K x]
  calc (K (a+x)).map (fun y ↦ y-(a+x)) =
      ((K (a+x)).map (fun y ↦ y-a)).map (fun y ↦ y-x) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext y
        dsimp only [Function.comp_def]
        abel
    _ = _ := by rw [hx]

/-- A constant residual law gives the original kernel rows as translates of that law. -/
theorem ae_eq_map_add_of_residual_kernel_ae_eq_const
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) (K : Kernel E E) [IsMarkovKernel K]
    (M : Measure E) (hR : ∀ᵐ x ∂μ,residualKernel K x=M) :
    ∀ᵐ x ∂μ,K x=M.map (fun y ↦ x+y) := by
  filter_upwards [hR] with x hx
  rw [residual_kernel_apply K x] at hx
  have he := congrArg (fun ρ : Measure E ↦ ρ.map (fun y ↦ x+y)) hx
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  have hfun : (fun y ↦ x+y) ∘ (fun y : E ↦ y-x) = id := by
    funext y
    dsimp only [Function.comp_def,id_eq]
    abel
  rw [hfun,Measure.map_id] at he
  exact he

/-- Every equivariant Gaussian randomization has an independent-noise convolution law. -/
theorem exists_convolution_of_gaussian_shift_kernel
    {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (K : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel K]
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (hLaw : ∀ h,K ∘ₘ multivariateGaussian h S=L.map (fun y ↦ h+y)) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)),IsProbabilityMeasure M ∧
      L=(multivariateGaussian 0 S).conv M := by
  obtain ⟨M,hM,hR⟩ := exists_ae_eq_const_kernel_of_forall_add_ae_eq
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (residualKernel K)
    (fun a ↦ ae_residual_kernel_add_eq_of_ae_covariant volume K a
      (ae_covariant_kernel_of_gaussian_shift_laws hS K L hLaw a))
  have := hM
  have hgauss : multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S ≪ volume := by
    rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS]
    exact withDensity_absolutelyContinuous _ _
  have hK := ae_eq_map_add_of_residual_kernel_ae_eq_const (multivariateGaussian 0 S) K M
    (hgauss.ae_le hR)
  have h0 : K ∘ₘ multivariateGaussian 0 S=L := by
    simpa only [zero_add,Measure.map_id'] using hLaw 0
  exact ⟨M,hM,h0.symm.trans (comp_eq_conv_of_ae_eq_map_add _ _ K hK)⟩

end CKSD
