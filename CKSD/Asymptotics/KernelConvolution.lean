module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Translation kernels and convolution of probability laws

A Markov kernel that is almost everywhere a translate of a fixed probability law acts on its
input law by convolution. This final measure identity uses only a measurable additive monoid;
no Euclidean, topological or Gaussian hypotheses are needed.

The proof unfolds Mathlib's convolution and kernel-measure composition and applies its
product-measure integration formula. The statistical application is the residual-noise
representation of a Gaussian shift kernel, supporting GAPS 102.16.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CKSD
/-- A kernel that is almost everywhere a translate of one fixed law acts by convolution. -/
theorem comp_eq_conv_of_ae_eq_map_add
    {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ M : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure M]
    (K : Kernel E E) [IsMarkovKernel K]
    (hK : ∀ᵐ x ∂μ, K x = M.map (fun y ↦ x + y)) : K ∘ₘ μ = μ.conv M := by
  ext s hs
  change μ.bind (fun x ↦ K x) s = _
  rw [Measure.bind_apply hs K.aemeasurable]
  rw [Measure.conv,Measure.map_apply measurable_add hs,
    Measure.prod_apply (measurable_add hs)]
  apply lintegral_congr_ae
  filter_upwards [hK] with x hx
  have hm : Measurable (fun y : E ↦ x + y) := measurable_const.add measurable_id
  rw [hx,Measure.map_apply hm hs]
  rfl
end CKSD
