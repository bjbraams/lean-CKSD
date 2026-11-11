module
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Common randomization kernels from tilted joint laws

If the joint limiting law of an observation and a statistic changes with the parameter only
through a density on the observation coordinate, one conditional kernel represents all the
statistic laws. A measurable coordinate change pulls this kernel back to the original
observation experiment. No inverse coordinate map or measurable parameter space is required.

This is the conditional-law step in van der Vaart, *Asymptotic Statistics* (1998), Theorem 7.10,
printed pp. 98–99 (PDF pp. 114–115 in the local Cambridge scan). It supplies a component of the
asymptotic representation theorem, GAPS 102.15; joint-limit extraction and the Gaussian
likelihood-ratio identity remain separate obligations.

Mathlib supplies standard-Borel disintegration, composition with measures, and the identity for
composition-products after changing the first-coordinate density. The proofs use those results
directly; they do not implement the book's explicit quantile randomization construction.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CKSD
variable {A S H : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S]
/-- A tilt depending only on the conditioning coordinate preserves the conditional kernel. -/
theorem condKernel_comp_withDensity_eq_snd (ρ : Measure (A × S)) [IsFiniteMeasure ρ]
    (f : A → ℝ≥0∞) (hf : Measurable f) :
    ρ.condKernel ∘ₘ (ρ.fst.withDensity f) = (ρ.withDensity (fun p ↦ f p.1)).snd := by
  rw [← Measure.snd_compProd, Measure.withDensity_compProd hf, ρ.disintegrate ρ.condKernel]

/-- A family obtained by tilting one joint law in its first coordinate has one common Markov
randomization for all its second marginal laws. -/
theorem exists_markovKernel_of_tilted_joint_laws
    (ρ : Measure (A × S)) [IsFiniteMeasure ρ]
    (f : H → A → ℝ≥0∞) (hf : ∀ h, Measurable (f h))
    (μ : H → Measure A) (L : H → Measure S)
    (hμ : ∀ h, μ h = ρ.fst.withDensity (f h))
    (hL : ∀ h, L h = (ρ.withDensity (fun p ↦ f h p.1)).snd) :
    ∃ K : Kernel A S, IsMarkovKernel K ∧ ∀ h, L h = K ∘ₘ μ h := by
  refine ⟨ρ.condKernel, inferInstance, fun h ↦ ?_⟩
  rw [hμ h, hL h, condKernel_comp_withDensity_eq_snd ρ (f h) (hf h)]

/-- Equality of tilted event probabilities suffices to construct a common randomization kernel.
This form applies directly to the limiting likelihood-ratio identity. -/
theorem exists_markovKernel_of_tilted_event_probabilities
    (ρ : Measure (A × S)) [IsFiniteMeasure ρ]
    (f : H → A → ℝ≥0∞) (hf : ∀ h, Measurable (f h))
    (μ : H → Measure A) (L : H → Measure S)
    (hμ : ∀ h, μ h = ρ.fst.withDensity (f h))
    (hL : ∀ h, ∀ s, MeasurableSet s →
      L h s = ∫⁻ p, f h p.1 * s.indicator (fun _ ↦ 1) p.2 ∂ρ) :
    ∃ K : Kernel A S, IsMarkovKernel K ∧ ∀ h, L h = K ∘ₘ μ h := by
  apply exists_markovKernel_of_tilted_joint_laws ρ f hf μ L hμ
  intro h
  ext s hs
  rw [hL h s hs, Measure.snd_apply hs, withDensity_apply _ (measurable_snd hs),
    ← lintegral_indicator (measurable_snd hs)]
  apply lintegral_congr
  intro p
  by_cases hp : p.2 ∈ s <;> simp [hp]

/-- A measurable change of observation coordinates pulls the common randomization back to the
original observation laws, without needing an inverse coordinate map. -/
theorem exists_markovKernel_of_map_eq_tilted_joint_laws
    {B : Type*} [MeasurableSpace B]
    (ρ : Measure (A × S)) [IsFiniteMeasure ρ]
    (f : H → A → ℝ≥0∞) (hf : ∀ h, Measurable (f h))
    (g : B → A) (hg : Measurable g) (ν : H → Measure B) (L : H → Measure S)
    (hν : ∀ h, (ν h).map g = ρ.fst.withDensity (f h))
    (hL : ∀ h, L h = (ρ.withDensity (fun p ↦ f h p.1)).snd) :
    ∃ K : Kernel B S, IsMarkovKernel K ∧ ∀ h, L h = K ∘ₘ ν h := by
  refine ⟨ρ.condKernel.comap g hg, inferInstance, fun h ↦ ?_⟩
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hg, hν h, condKernel_comp_withDensity_eq_snd ρ (f h) (hf h), hL h]
end CKSD
