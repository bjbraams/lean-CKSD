module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import CKSD.Inference.Factorization
import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Weighted coupling limits for comparison of experiments

Composition products lift finite randomizations to joint measures. Mapping and
weighting their first coordinate identifies randomized alternative laws. Weak
limits preserve bounded continuous coordinate weights and their marginals;
pointwise finite quantizations converge weakly under each finite law. These
measure-theoretic steps support the compact likelihood-vector proof of
Blackwell's comparison theorem (GAPS 101.62).
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace CKSD

/-- Weighting the first coordinate of a mapped composition product commutes with
mixing the correspondingly weighted input law. -/
theorem snd_withDensity_map_compProd
    {X A C D : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure X) [SFinite μ] (K : Kernel X A) [IsSFiniteKernel K]
    (u : X → C) (hu : Measurable u) (v : A → D) (hv : Measurable v)
    (w : C → ℝ≥0∞) (hw : Measurable w) :
    (((μ ⊗ₘ K).map (fun p : X × A ↦ (u p.1, v p.2))).withDensity
      (fun z : C × D ↦ w z.1)).snd =
      (K ∘ₘ μ.withDensity (w ∘ u)).map v := by
  let F : X × A → C × D := fun p ↦ (u p.1, v p.2)
  have hF : Measurable F := (hu.comp measurable_fst).prodMk (hv.comp measurable_snd)
  -- Expose the marginal map and local coordinate map for the composition identities.
  change (((μ ⊗ₘ K).map F).withDensity (w ∘ Prod.fst)).map Prod.snd = _
  rw [← map_withDensity_comp (μ ⊗ₘ K) hF (hw.comp measurable_fst)]
  have he : (w ∘ Prod.fst) ∘ F = fun p : X × A ↦ (w ∘ u) p.1 := rfl
  rw [he, ← Measure.withDensity_compProd (hw.comp hu), Measure.map_map measurable_snd hF]
  have hs : Prod.snd ∘ F = v ∘ Prod.snd := rfl
  rw [hs, ← Measure.map_map hv measurable_snd]
  -- Expose the marginal map and local coordinate map for the composition identities.
  change ((μ.withDensity (w ∘ u) ⊗ₘ K).snd).map v = _
  rw [Measure.snd_compProd]

/-- Mapping both coordinates of a Markov composition product preserves the pushed-forward
first marginal. -/
theorem fst_map_compProd
    {X A C D : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure X) [SFinite μ] (K : Kernel X A) [IsMarkovKernel K]
    (u : X → C) (hu : Measurable u) (v : A → D) (hv : Measurable v) :
    ((μ ⊗ₘ K).map (fun p : X × A ↦ (u p.1, v p.2))).fst = μ.map u := by
  let F : X × A → C × D := fun p ↦ (u p.1, v p.2)
  have hF : Measurable F := (hu.comp measurable_fst).prodMk (hv.comp measurable_snd)
  -- Expose the marginal map and local coordinate map for the composition identities.
  change ((μ ⊗ₘ K).map F).map Prod.fst = _
  rw [Measure.map_map measurable_fst hF]
  have he : Prod.fst ∘ F = u ∘ Prod.fst := rfl
  rw [he, ← Measure.map_map hu measurable_fst]
  -- Expose the marginal map and local coordinate map for the composition identities.
  change ((μ ⊗ₘ K).fst).map u = _
  rw [Measure.fst_compProd]

/-- Bounded continuous weighting and taking the second marginal preserve finite weak limits. -/
theorem snd_withDensity_eq_of_finiteMeasure_tendsto
    {C D : Type*} [MetricSpace C] [MetricSpace D]
    [MeasurableSpace C] [MeasurableSpace D] [BorelSpace C] [BorelSpace D]
    [SecondCountableTopology C] [SecondCountableTopology D]
    (μs : ℕ → FiniteMeasure (C × D)) (μ : FiniteMeasure (C × D))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (νs : ℕ → FiniteMeasure D) (ν : FiniteMeasure D)
    (hν : Tendsto νs atTop (𝓝 ν)) (w : BoundedContinuousFunction C ℝ) (hw : ∀ x, 0 ≤ w x)
    (heq : ∀ n, ((μs n : Measure (C × D)).withDensity
      (fun p ↦ ENNReal.ofReal (w p.1))).snd = (νs n : Measure D)) :
    ((μ : Measure (C × D)).withDensity (fun p ↦ ENNReal.ofReal (w p.1))).snd = (ν : Measure D) := by
  have hi : Integrable (fun p : C × D ↦ w p.1) (μ : Measure (C × D)) :=
    (w.compContinuous ⟨Prod.fst, continuous_fst⟩).integrable _
  have : IsFiniteMeasure ((μ : Measure (C × D)).withDensity
      (fun p ↦ ENNReal.ofReal (w p.1))) := isFiniteMeasure_withDensity hi.lintegral_lt_top.ne
  suffices h : (⟨((μ : Measure (C × D)).withDensity
      (fun p ↦ ENNReal.ofReal (w p.1))).snd, inferInstance⟩ : FiniteMeasure D) = ν by
    exact congrArg FiniteMeasure.toMeasure h
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  let F : BoundedContinuousFunction (C × D) ℝ :=
    (w.compContinuous ⟨Prod.fst, continuous_fst⟩) * (f.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have hF (η : FiniteMeasure (C × D)) :
      (∫ p, F p ∂(η : Measure (C × D))) =
      ∫ y, f y ∂((η : Measure (C × D)).withDensity (fun p ↦ ENNReal.ofReal (w p.1))).snd := by
    rw [Measure.snd, integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [F, FunLike.coe_mul, Pi.mul_apply, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  have h1 := FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hμ F
  have h2 := FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hν f
  have h1' : Tendsto (fun n ↦ ∫ y, f y ∂(νs n : Measure D)) atTop
      (𝓝 (∫ y, f y ∂((μ : Measure (C × D)).withDensity
        (fun p ↦ ENNReal.ofReal (w p.1))).snd)) := by
    simpa only [hF, heq] using h1
  exact tendsto_nhds_unique h1' h2

/-- Pointwise convergent measurable quantizations give weak convergence of every finite
push-forward law. -/
theorem finiteMeasure_tendsto_map_of_pointwise
    {C D : Type*} [MetricSpace C] [MetricSpace D]
    [MeasurableSpace C] [MeasurableSpace D] [BorelSpace C] [BorelSpace D]
    (μ : FiniteMeasure C) (f : ℕ → C → D) (hf : ∀ n, Measurable (f n))
    (g : C → D) (hg : Measurable g)
    (hfg : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ μ.map (f n)) atTop (𝓝 (μ.map g)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.2
  intro test
  have hi := tendsto_integral_of_dominated_convergence (μ := (μ : Measure C))
    (F := fun n x ↦ test (f n x)) (f := fun x ↦ test (g x)) (fun _ : C ↦ ‖test‖)
    (fun n ↦ test.continuous.aestronglyMeasurable.comp_measurable (hf n))
    (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ test.norm_coe_le_norm _)
    (ae_of_all _ fun x ↦ test.continuous.continuousAt.tendsto.comp (hfg x))
  simpa only [FiniteMeasure.toMeasure_map,
    integral_map (hf _).aemeasurable test.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable test.continuous.aestronglyMeasurable] using hi


end CKSD
