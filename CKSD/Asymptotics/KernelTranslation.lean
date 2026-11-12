module
public import Mathlib.MeasureTheory.Group.Prod
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Separable
public import Mathlib.Probability.Kernel.Basic
/-!
# Almost-everywhere constant translation-invariant kernels

A measurable function invariant almost everywhere under each translation is
almost everywhere constant for a nonzero invariant measure. Fubini exchanges
the translation and base-point quantifiers; inverse translation then gives
constancy. Lifting Markov kernels to probability-measure-valued functions gives
the corresponding constant-kernel result.

This is the Fubini argument underlying Mathlib's ergodicity of the regular group
action (`Mathlib.Dynamics.Ergodic.Action.Regular`), applied directly to functions.
Pinned TauCeti identifies the Giry and Borel structures and provides separability
of probability measures. The statistical use is the convolution representation
of equivariant Gaussian estimators, van der Vaart (1998), Proposition 8.4 and
Theorem 8.8, printed pp. 113–115, PDF pp. 129–131.
-/
@[expose] public section
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
namespace CKSD
/-- A measurable function invariant almost everywhere under every translation is constant
almost everywhere for a nonzero invariant measure. -/
theorem ae_eq_const_of_forall_add_ae_eq
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] [MeasurableSpace Y] [MeasurableEq Y]
    (μ : Measure G) [SFinite μ] [NeZero μ] [IsAddLeftInvariant μ]
    (f : G → Y) (hf : Measurable f)
    (h : ∀ a, ∀ᵐ x ∂μ, f (a+x) = f x) : ∃ c, ∀ᵐ x ∂μ, f x = c := by
  have hh : ∀ᵐ x ∂μ, ∀ᵐ a ∂μ, f (a+x)=f x := by
    rw [ae_ae_comm]
    · exact ae_of_all _ h
    · exact measurableSet_eq_fun (hf.comp (measurable_snd.add measurable_fst))
        (hf.comp measurable_fst)
  obtain ⟨x₀,hx₀⟩ := hh.exists
  refine ⟨f x₀, ?_⟩
  have ht := (quasiMeasurePreserving_add_right μ (-x₀)).ae hx₀
  simpa only [add_assoc,neg_add_cancel,add_zero] using ht
/-- A Markov kernel invariant under every translation is almost everywhere constant. -/
theorem exists_ae_eq_const_kernel_of_forall_add_ae_eq
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    (μ : Measure G) [SFinite μ] [NeZero μ] [IsAddLeftInvariant μ]
    (K : ProbabilityTheory.Kernel G Y) [ProbabilityTheory.IsMarkovKernel K]
    (h : ∀ a, ∀ᵐ x ∂μ, K (a+x) = K x) :
    ∃ M : Measure Y, IsProbabilityMeasure M ∧ ∀ᵐ x ∂μ, K x=M := by
  let f : G → ProbabilityMeasure Y := fun x ↦ ⟨K x,inferInstance⟩
  have hf : Measurable f := K.measurable.subtype_mk
  have hi (a : G) : ∀ᵐ x ∂μ, f (a+x)=f x :=
    (h a).mono fun x hx ↦ Subtype.ext hx
  obtain ⟨c,hc⟩ := ae_eq_const_of_forall_add_ae_eq μ f hf hi
  refine ⟨c,inferInstance,?_⟩
  exact hc.mono fun x hx ↦ congrArg (fun ν : ProbabilityMeasure Y ↦ (ν:Measure Y)) hx
end CKSD
