module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Semicontinuity.Defs
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
import TauCeti.MeasureTheory.OptimalTransport.Gluing
import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic
import TauCeti.MeasureTheory.OptimalTransport.Compactness
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Function.Lusin
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.EulerLagrange

/-!
# Couplings and quadratic displacement costs

A transport plan from a measurable image law lifts through the image map. For fixed-marginal
couplings, the quadratic displacement cost remains weakly lower semicontinuous when the vector
field is only measurable: common Lusin sets come from the fixed source marginal. Its exact
quadratic expansion and a uniform bound on its linear coefficient use finite second moments.

These facts support first variations of squared Wasserstein distance without imposing continuity
or boundedness on the displacement field. The proofs reuse TauCeti's graph-plan gluing, Lusin
approximation, lower semicontinuity of integrals, and coupling integration formulas.

## Main results

* `CKSD.exists_isCoupling_map_prodMap_eq`: lift a coupling through a measurable map.
* `CKSD.lowerSemicontinuous_integral_coupling_displacement_sq`: lower semicontinuity of costs.
* `CKSD.integral_norm_displacement_coupling_sq`: exact quadratic cost expansion.
* `CKSD.abs_integral_inner_displacement_coupling_le`: uniform coefficient bound.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace CKSD

/-- A coupling out of a measurable pushforward lifts to a coupling out of the original law. -/
theorem exists_isCoupling_map_prodMap_eq {X Y Z : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
      [MeasurableEq Z]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) (f : X → Z) (hf : Measurable f)
    {π : Measure (Z × Y)} (hπ : TauCeti.IsCoupling π (μ.map f) ν) :
    ∃ γ : Measure (X × Y), TauCeti.IsCoupling γ μ ν ∧ γ.map (Prod.map f id) = π := by
  let H : X × Z × Y → X × Y := fun z ↦ (z.1, z.2.2)
  let J : X × Z × Y → X × Z := fun z ↦ (z.1, z.2.1)
  have hH : Measurable H := by fun_prop
  have hJ : Measurable J := by fun_prop
  have hpg : (TauCeti.graphPlan f μ).snd = π.fst :=
    (TauCeti.snd_graphPlan hf.aemeasurable).trans hπ.fst_eq.symm
  obtain ⟨σ, hσpair, hσsnd⟩ := TauCeti.Measure.exists_glue_of_standardBorel_left
    (TauCeti.graphPlan f μ) π hpg
  -- Express the glued marginal using its named measurable projection.
  change σ.map J = TauCeti.graphPlan f μ at hσpair
  have hσfst : σ.map (fun z : X × Z × Y ↦ z.1) = μ := by
    calc σ.map (fun z : X × Z × Y ↦ z.1) = (σ.map J).fst := by
            rw [Measure.fst, Measure.map_map measurable_fst hJ]
            rfl
      _ = (TauCeti.graphPlan f μ).fst := congrArg Measure.fst hσpair
      _ = μ := TauCeti.fst_graphPlan hf.aemeasurable
  have hσlast : σ.map (fun z : X × Z × Y ↦ z.2.2) = ν := by
    calc σ.map (fun z : X × Z × Y ↦ z.2.2) = σ.snd.snd := by
            rw [Measure.snd, Measure.snd, Measure.map_map measurable_snd measurable_snd]
            rfl
      _ = π.snd := congrArg Measure.snd hσsnd
      _ = ν := hπ.snd_eq
  have hae : ∀ᵐ z : X × Z × Y ∂σ, z.2.1 = f z.1 := by
    have h := TauCeti.ae_snd_eq_graphPlan (μ := μ) hf.aemeasurable
    rw [← hσpair] at h
    exact ae_of_ae_map hJ.aemeasurable h
  refine ⟨σ.map H, ⟨?_, ?_⟩, ?_⟩
  · rw [Measure.fst, Measure.map_map measurable_fst hH]
    exact hσfst
  · rw [Measure.snd, Measure.map_map measurable_snd hH]
    exact hσlast
  · rw [Measure.map_map (hf.prodMap measurable_id) hH]
    calc σ.map (Prod.map f id ∘ H) = σ.map Prod.snd := by
          apply Measure.map_congr
          filter_upwards [hae] with z hz
          exact Prod.ext hz.symm rfl
      _ = π := hσsnd

end CKSD

namespace CKSD

/-- Lower semicontinuity of the nonnegative extended-real coercion implies real lower
  semicontinuity. -/
lemma lowerSemicontinuous_of_ennreal_ofReal {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (h : LowerSemicontinuous fun x ↦ ENNReal.ofReal (f x)) : LowerSemicontinuous f := by
  intro x a hax
  by_cases ha : a < 0
  · exact Eventually.of_forall fun y ↦ ha.trans_le (hf y)
  · have hax' : ENNReal.ofReal a < ENNReal.ofReal (f x) :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (le_of_not_gt ha) hax)).mpr hax
    filter_upwards [h x _ hax'] with y hy
    exact lt_of_not_ge fun hle ↦ hy.not_ge (ENNReal.ofReal_le_ofReal hle)

/-- The nonnegative displacement cost is weakly lower semicontinuous on a family of plans with
fixed first marginal, even when the vector field is merely measurable. Lusin sets for the fixed
marginal provide the uniform continuity sets required by the portmanteau theorem. -/
theorem lowerSemicontinuous_lintegral_coupling_displacement {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ ν : ProbabilityMeasure E) (v : E → E) (hv : Measurable v) (t : ℝ) :
    LowerSemicontinuous (fun γ : TauCeti.Coupling μ ν ↦
      ∫⁻ z, ENNReal.ofReal (‖z.1 + t • v z.1 - z.2‖ ^ 2) ∂γ.1.toMeasure) := by
  let Φ : E × E → E × E × E := fun z ↦ (z.1, v z.1, z.2)
  let c : E × E × E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖z.1 + t • z.2.1 - z.2.2‖ ^ 2)
  have hc : Continuous c := ENNReal.continuous_ofReal.comp (by fun_prop)
  have h : LowerSemicontinuousOn (fun γ : ProbabilityMeasure (E × E) ↦
      ∫⁻ z, c (Φ z) ∂γ.toMeasure) {γ | TauCeti.IsCoupling γ.toMeasure μ.toMeasure ν.toMeasure} := by
    apply TauCeti.lowerSemicontinuousOn_lintegral_comp hc.lowerSemicontinuous
    · intro ε hε
      obtain ⟨F, -, hF, hsmall, hvF⟩ := hv.exists_isClosed_measure_sdiff_lt_continuousOn
        (μ := μ.toMeasure) MeasurableSet.univ (measure_ne_top _ _) hε
      refine ⟨F ×ˢ univ, hF.prod isClosed_univ, ?_, ?_⟩
      · -- Write the Lusin-set restriction in coordinates to apply continuity rules.
        change ContinuousOn (fun z : E × E ↦ (z.1, v z.1, z.2)) (F ×ˢ univ)
        have hvC : ContinuousOn (fun z : E × E ↦ v z.1) (F ×ˢ univ) :=
          hvF.comp continuousOn_fst (fun _ hz ↦ hz.1)
        exact continuousOn_fst.prodMk (hvC.prodMk continuousOn_snd)
      · intro γ hγ
        have hset : (F ×ˢ (univ : Set E))ᶜ = Prod.fst ⁻¹' Fᶜ := by ext z; simp
        rw [hset, ← Measure.map_apply measurable_fst hF.measurableSet.compl, ← Measure.fst,
          hγ.fst_eq]
        have hdiff : (univ : Set E) \ F = Fᶜ := by
          ext x
          simp only [Set.mem_sdiff, mem_univ, mem_compl_iff, true_and]
        rw [hdiff] at hsmall
        exact hsmall.le
    · intro γ _
      exact (hc.measurable.comp (measurable_fst.prodMk ((hv.comp measurable_fst).prodMk
        measurable_snd))).aemeasurable
  have h' : LowerSemicontinuousOn (fun γ : TauCeti.Coupling μ ν ↦
      ∫⁻ z, c (Φ z) ∂γ.1.toMeasure) univ :=
    h.comp continuous_subtype_val.continuousOn (fun γ _ ↦ γ.2)
  exact lowerSemicontinuousOn_univ_iff.mp h'

end CKSD

namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ ν : Measure E} {γ : Measure (E × E)} {v : E → E}

omit [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
/-- Finite second moments make the displaced quadratic cost integrable against every coupling. -/
lemma integrable_norm_displacement_coupling_sq (hγ : TauCeti.IsCoupling γ μ ν)
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) (hv : MemLp v 2 μ) (t : ℝ) :
    Integrable (fun z : E × E ↦ ‖z.1 + t • v z.1 - z.2‖ ^ 2) γ := by
  have hfst := hμ.comp_measurePreserving hγ.measurePreserving_fst
  have hsnd := hν.comp_measurePreserving hγ.measurePreserving_snd
  have hvec := hv.comp_measurePreserving hγ.measurePreserving_fst
  have h := (hfst.add (hvec.const_smul t)).sub hsnd
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

omit [CompleteSpace E] in
/-- Exact quadratic expansion of a coupling cost along a square-integrable displacement. -/
lemma integral_norm_displacement_coupling_sq (hγ : TauCeti.IsCoupling γ μ ν)
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) (hv : MemLp v 2 μ) (t : ℝ) :
    (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ) =
      (∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ) +
        t * (2 * ∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ) +
        t ^ 2 * ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have hd := (hμ.comp_measurePreserving hγ.measurePreserving_fst).sub
    (hν.comp_measurePreserving hγ.measurePreserving_snd)
  have hdi : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hvi := hv.comp_measurePreserving hγ.measurePreserving_fst
  have hv₂ : Integrable (fun z : E × E ↦ ‖v z.1‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hvi.aestronglyMeasurable).mp hvi
  have hin := hγ.integrable_inner_sub_comp_fst hdi hv
  have hpt : (fun z : E × E ↦ ‖z.1 + t • v z.1 - z.2‖ ^ 2) = fun z ↦
      (‖z.1 - z.2‖ ^ 2 + 2 * t * inner ℝ (z.1 - z.2) (v z.1)) + t ^ 2 * ‖v z.1‖ ^ 2 := by
    funext z
    rw [add_sub_right_comm, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have hmul : Integrable (fun z : E × E ↦ 2 * t * inner ℝ (z.1 - z.2) (v z.1)) γ :=
    hin.const_mul (2 * t)
  have hsum : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 +
      2 * t * inner ℝ (z.1 - z.2) (v z.1)) γ := hdi.add hmul
  have hlast : Integrable (fun z : E × E ↦ t ^ 2 * ‖v z.1‖ ^ 2) γ := hv₂.const_mul _
  rw [hpt]
  have he₁ := integral_add hsum hlast
  rw [he₁]
  have he₂ := integral_add hdi hmul
  rw [he₂, integral_const_mul, integral_const_mul,
    hγ.integral_comp_fst (f := fun x ↦ ‖v x‖ ^ 2) (hv.aestronglyMeasurable.norm.pow 2)]
  ring

omit [CompleteSpace E] in
/-- The linear displacement coefficient is uniformly bounded by the marginal second moments. -/
lemma abs_integral_inner_displacement_coupling_le (hγ : TauCeti.IsCoupling γ μ ν)
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) (hv : MemLp v 2 μ) :
    |2 * ∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ| ≤
      2 * ∫ x, ‖x‖ ^ 2 ∂μ + 2 * ∫ y, ‖y‖ ^ 2 ∂ν + ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have hfst := hμ.comp_measurePreserving hγ.measurePreserving_fst
  have hsnd := hν.comp_measurePreserving hγ.measurePreserving_snd
  have hvγ := hv.comp_measurePreserving hγ.measurePreserving_fst
  have hi₁ : Integrable (fun z : E × E ↦ ‖z.1‖ ^ 2) γ := (memLp_two_iff_integrable_sq_norm
    hfst.aestronglyMeasurable).mp hfst
  have hi₂ : Integrable (fun z : E × E ↦ ‖z.2‖ ^ 2) γ := (memLp_two_iff_integrable_sq_norm
    hsnd.aestronglyMeasurable).mp hsnd
  have hi₃ : Integrable (fun z : E × E ↦ ‖v z.1‖ ^ 2) γ := (memLp_two_iff_integrable_sq_norm
    hvγ.aestronglyMeasurable).mp hvγ
  have hd := hfst.sub hsnd
  have hdi : Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hin := hγ.integrable_inner_sub_comp_fst hdi hv
  have hpt (z : E × E) : 2 * |inner ℝ (z.1 - z.2) (v z.1)| ≤
      2 * ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 + ‖v z.1‖ ^ 2 := by
    have hc := abs_real_inner_le_norm (z.1 - z.2) (v z.1)
    have hd := norm_sub_le z.1 z.2
    nlinarith [sq_nonneg (‖z.1 - z.2‖ - ‖v z.1‖),
      sq_nonneg (‖z.1‖ - ‖z.2‖), norm_nonneg (z.1 - z.2), norm_nonneg (v z.1),
      norm_nonneg z.1, norm_nonneg z.2]
  have hle := integral_mono (hin.norm.const_mul 2)
    (((hi₁.const_mul 2).add (hi₂.const_mul 2)).add hi₃) hpt
  simp only [Pi.add_apply, Real.norm_eq_abs] at hle
  rw [integral_const_mul] at hle
  have he₁ := integral_add ((hi₁.const_mul 2).add (hi₂.const_mul 2)) hi₃
  have he₂ := integral_add (hi₁.const_mul 2) (hi₂.const_mul 2)
  simp only [Pi.add_apply] at he₁ he₂
  rw [he₁, he₂, integral_const_mul, integral_const_mul,
    hγ.integral_comp_fst (f := fun x ↦ ‖x‖ ^ 2) (by fun_prop),
    hγ.integral_comp_snd (f := fun y ↦ ‖y‖ ^ 2) (by fun_prop),
    hγ.integral_comp_fst (f := fun x ↦ ‖v x‖ ^ 2) (hv.aestronglyMeasurable.norm.pow 2)] at hle
  calc |2 * ∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ| =
        2 * |∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ| := by rw [abs_mul]; norm_num
    _ ≤ 2 * ∫ z, |inner ℝ (z.1 - z.2) (v z.1)| ∂γ := by
      gcongr
      exact abs_integral_le_integral_abs
    _ ≤ _ := hle

end CKSD

namespace CKSD

/-- The real quadratic displacement cost is lower semicontinuous on fixed-marginal couplings
with finite second moments, for any measurable square-integrable displacement field. -/
theorem lowerSemicontinuous_integral_coupling_displacement_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ ν : ProbabilityMeasure E) (hμ : MemLp id 2 μ.toMeasure)
    (hν : MemLp id 2 ν.toMeasure) (v : E → E) (hv : Measurable v)
    (hv₂ : MemLp v 2 μ.toMeasure) (t : ℝ) :
    LowerSemicontinuous (fun γ : TauCeti.Coupling μ ν ↦
      ∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure) := by
  apply lowerSemicontinuous_of_ennreal_ofReal _
    (fun γ ↦ integral_nonneg fun z ↦ sq_nonneg _)
  have heq : (fun γ : TauCeti.Coupling μ ν ↦ ENNReal.ofReal
      (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure)) =
      fun γ : TauCeti.Coupling μ ν ↦
        ∫⁻ z, ENNReal.ofReal (‖z.1 + t • v z.1 - z.2‖ ^ 2) ∂γ.1.toMeasure := by
    funext γ
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_displacement_coupling_sq γ.2 hμ hν hv₂ t)
      (Eventually.of_forall fun z ↦ sq_nonneg _)
  rw [heq]
  exact lowerSemicontinuous_lintegral_coupling_displacement μ ν v hv t

end CKSD
