module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import CKSD.Geometry.CompactEnvelope
import CKSD.Geometry.TransportVariationBasic
import CKSD.Geometry.OptimalMapStability
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# First variation of squared quadratic Wasserstein distance

At a finite-dimensional absolutely continuous source law, the squared Wasserstein distance has
a derivative along every measurable square-integrable displacement. This is a compact-coupling
proof of the directional consequence of Panaretos--Zemel, Theorem 3.1.14, printed page 67.

A measurable-map coupling lift identifies the displaced transport problem with a compact
fixed-marginal minimization problem. Its cost is quadratic in time. TauCeti's Brenier uniqueness
identifies the coefficient at every unperturbed minimizer; the compact-envelope differentiation
rule then applies. The displacement field need not be continuous or bounded.

## Main results

* `CKSD.integral_displacement_cost_eq_wasserstein_of_minimizer`: identify the minimum cost.
* `CKSD.has_deriv_at_wasserstein_sq_displacement`: the directional first variation.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace CKSD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A least-cost coupling for the displaced quadratic cost realizes the squared Wasserstein
distance of the displaced source to the target. -/
theorem integral_displacement_cost_eq_wasserstein_of_minimizer
    (μ ν : TauCeti.WassersteinSpace 2 E)
    (v : E → E) (hv : Measurable v)
    (hv₂ : MemLp v 2 ((μ : ProbabilityMeasure E) : Measure E)) (t : ℝ)
    (γ : TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E))
    (hmin : ∀ η : TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E),
      (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure) ≤
        ∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂η.1.toMeasure) :
    (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure) =
      (TauCeti.wassersteinEDist 2
        (((μ : ProbabilityMeasure E) : Measure E).map fun x ↦ x + t • v x)
        ((ν : ProbabilityMeasure E) : Measure E)).toReal ^ 2 := by
  let P := ((μ : ProbabilityMeasure E) : Measure E)
  let Q := ((ν : ProbabilityMeasure E) : Measure E)
  let f : E → E := fun x ↦ x + t • v x
  have hf : Measurable f := measurable_id.add (hv.const_smul t)
  have hμ₂ := μ.hasFiniteMoment.memLp_id
  have hν₂ := ν.hasFiniteMoment.memLp_id
  have hf₂ : MemLp f 2 P := hμ₂.add (hv₂.const_smul t)
  obtain ⟨μt, hμt⟩ := TauCeti.exists_coe_eq_map_of_memLp hf₂
  have hdist : dist μt ν = (TauCeti.wassersteinEDist 2 (P.map f) Q).toReal := by
    rw [TauCeti.WassersteinSpace.dist_def, hμt]
  have hmap (η : TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E)) :
      TauCeti.IsCoupling (η.1.toMeasure.map (Prod.map f id)) (P.map f) Q := by
    simpa only [Measure.map_id] using η.2.map hf measurable_id
  have hcost (η : TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E)) :
      (∫ z, ‖z.1 - z.2‖ ^ 2 ∂η.1.toMeasure.map (Prod.map f id)) =
        ∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂η.1.toMeasure := by
    rw [integral_map (hf.prodMap measurable_id).aemeasurable (by fun_prop)]
    rfl
  have hlo := TauCeti.WassersteinSpace.dist_sq_le_integral (ν₀ := μt) (ν₁ := ν)
    (hμt ▸ hmap γ)
  rw [hdist, hcost] at hlo
  obtain ⟨π, hπ⟩ := TauCeti.exists_isOptimalCoupling_edist_rpow (P.map f) Q 2
  obtain ⟨etaRaw, hη, hlift⟩ := exists_is_coupling_map_prod_map_eq P Q f hf hπ.toIsCoupling
  have hηprob : IsProbabilityMeasure etaRaw := hη.isProbabilityMeasure
  let η : TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E) :=
    ⟨⟨etaRaw, hηprob⟩, hη⟩
  have heq := TauCeti.WassersteinSpace.dist_sq_eq_integral (ν₀ := μt) (ν₁ := ν)
    (hμt ▸ hπ)
  rw [hdist, ← hlift] at heq
  -- Read the lifted plan as its bundled coupling before changing variables.
  change _ = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂η.1.toMeasure.map (Prod.map f id) at heq
  rw [hcost] at heq
  exact le_antisymm ((hmin η).trans_eq heq.symm) hlo

/-- First variation of the squared quadratic Wasserstein distance along an arbitrary measurable
square-integrable displacement, at an absolutely continuous source law. -/
theorem has_deriv_at_wasserstein_sq_displacement [FiniteDimensional ℝ E]
    {ρ : Measure E} [ρ.IsAddHaarMeasure]
    (μ ν : TauCeti.WassersteinSpace 2 E)
    (hac : ((μ : ProbabilityMeasure E) : Measure E) ≪ ρ)
    (T : E → E) (hT : Measurable T)
    (hlaw : (((μ : ProbabilityMeasure E) : Measure E).map T) =
      ((ν : ProbabilityMeasure E) : Measure E))
    (hopt : (∫ x, ‖x - T x‖ ^ 2 ∂((μ : ProbabilityMeasure E) : Measure E)) =
      (TauCeti.wassersteinEDist 2 ((μ : ProbabilityMeasure E) : Measure _)
        ((ν : ProbabilityMeasure E) : Measure E)).toReal ^ 2)
    (v : E → E) (hv : Measurable v)
    (hv₂ : MemLp v 2 ((μ : ProbabilityMeasure E) : Measure E)) :
    HasDerivAt (fun t : ℝ ↦ (TauCeti.wassersteinEDist 2
      (((μ : ProbabilityMeasure E) : Measure E).map fun x ↦ x + t • v x)
      ((ν : ProbabilityMeasure E) : Measure E)).toReal ^ 2)
      (2 * ∫ x, inner ℝ (x - T x) (v x) ∂((μ : ProbabilityMeasure E) : Measure E)) 0 := by
  let P := ((μ : ProbabilityMeasure E) : Measure E)
  let Q := ((ν : ProbabilityMeasure E) : Measure E)
  let X := TauCeti.Coupling (μ : ProbabilityMeasure E) (ν : ProbabilityMeasure E)
  let _ : CompactSpace X := TauCeti.Coupling.instCompactSpace
  let _ : FirstCountableTopology X := TopologicalSpace.Subtype.firstCountableTopology
    {π : ProbabilityMeasure (E × E) | TauCeti.IsCoupling π.toMeasure P Q}
  have hμ₂ := μ.hasFiniteMoment.memLp_id
  have hν₂ := ν.hasFiniteMoment.memLp_id
  have hgc : TauCeti.IsCoupling (TauCeti.graphPlan T P) P Q :=
    TauCeti.isCoupling_graphPlan ⟨hT.aemeasurable, hlaw⟩
  let g : X := ⟨⟨TauCeti.graphPlan T P, hgc.isProbabilityMeasure⟩, hgc⟩
  have hgo := is_optimal_coupling_graph_plan_of_integral_norm_sq_eq μ ν T hT hlaw hopt
  let A : X → ℝ := fun γ ↦ ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure
  let B : X → ℝ := fun γ ↦ 2 * ∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ.1.toMeasure
  let C : ℝ := ∫ x, ‖v x‖ ^ 2 ∂P
  let a : ℝ := dist μ ν ^ 2
  let D : ℝ := 2 * ∫ x, inner ℝ (x - T x) (v x) ∂P
  let M : ℝ := 2 * ∫ x, ‖x‖ ^ 2 ∂P + 2 * ∫ y, ‖y‖ ^ 2 ∂Q + C
  have hcost (γ : X) (t : ℝ) :
      (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure) = A γ + t * B γ + t ^ 2 * C :=
    integral_norm_displacement_coupling_sq γ.2 hμ₂ hν₂ hv₂ t
  have hAg : A g = a := (TauCeti.WassersteinSpace.dist_sq_eq_integral hgo).symm
  have hBg : B g = D := by
    dsimp [B, D, g]
    rw [TauCeti.integral_graphPlan hT.aemeasurable (by fun_prop)]
  have hA : LowerSemicontinuous A := by
    simpa only [A, zero_smul, add_zero] using
      lower_semicontinuous_integral_coupling_displacement_sq (μ : ProbabilityMeasure E)
        (ν : ProbabilityMeasure E) hμ₂ hν₂ v hv hv₂ 0
  have hAp : LowerSemicontinuous (fun γ ↦ A γ + B γ) := by
    have h := (lower_semicontinuous_integral_coupling_displacement_sq (μ : ProbabilityMeasure E)
      (ν : ProbabilityMeasure E) hμ₂ hν₂ v hv hv₂ 1).add
      (lowerSemicontinuous_const (z := -C))
    convert h using 1
    funext γ
    rw [hcost]
    ring
  have hAm : LowerSemicontinuous (fun γ ↦ A γ - B γ) := by
    have h := (lower_semicontinuous_integral_coupling_displacement_sq (μ : ProbabilityMeasure E)
      (ν : ProbabilityMeasure E) hμ₂ hν₂ v hv hv₂ (-1)).add
      (lowerSemicontinuous_const (z := -C))
    convert h using 1
    funext γ
    rw [hcost]
    ring
  have ha : ∀ γ : X, a ≤ A γ := fun γ ↦ TauCeti.WassersteinSpace.dist_sq_le_integral γ.2
  have hD : ∀ γ : X, A γ = a → B γ = D := by
    intro γ hγ
    have ho := TauCeti.WassersteinSpace.isOptimalCoupling_of_integral_le_dist_sq γ.2 hγ.le
    have heq := (TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two ho).unique
      (ρ := ρ) hac (TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two hgo)
      (TauCeti.transportCost_norm_sub_sq_div_two_ne_top μ ν)
    -- Identify the two underlying optimal measures before rewriting their integrals.
    change γ.1.toMeasure = g.1.toMeasure at heq
    -- Expand the named linear coefficient for the measure substitution.
    change 2 * (∫ z, inner ℝ (z.1 - z.2) (v z.1) ∂γ.1.toMeasure) = D
    rw [heq]
    exact hBg
  have hsel (t : ℝ) : ∃ γ : X, ∀ η : X,
      (∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂γ.1.toMeasure) ≤
        ∫ z, ‖z.1 + t • v z.1 - z.2‖ ^ 2 ∂η.1.toMeasure := by
    obtain ⟨γ, -, hγ⟩ :=
      (lower_semicontinuous_integral_coupling_displacement_sq (μ : ProbabilityMeasure E)
        (ν : ProbabilityMeasure E) hμ₂ hν₂ v hv hv₂ t).lowerSemicontinuousOn univ
        |>.exists_isMinOn Set.univ_nonempty isCompact_univ
    exact ⟨γ, fun η ↦ hγ (mem_univ η)⟩
  choose q hq using hsel
  have hqmin (t : ℝ) : A (q t) + t * B (q t) ≤ a + t * D := by
    have h := hq t g
    rw [hcost, hcost, hAg, hBg] at h
    linarith
  have hder := has_deriv_at_compact_quadratic_minimum (S := (univ : Set X)) isCompact_univ
    A B (hA.lowerSemicontinuousOn _) (hAp.lowerSemicontinuousOn _) (hAm.lowerSemicontinuousOn _)
    a D M C (fun γ _ ↦ ha γ) (fun γ _ ↦ hD γ)
    (fun γ _ ↦ abs_integral_inner_displacement_coupling_le γ.2 hμ₂ hν₂ hv₂)
    q (fun _ ↦ mem_univ _) hqmin
  have heq : (fun t : ℝ ↦ (TauCeti.wassersteinEDist 2 (P.map fun x ↦ x + t • v x) Q).toReal ^ 2) =
      fun t ↦ A (q t) + t * B (q t) + t ^ 2 * C := by
    funext t
    exact (integral_displacement_cost_eq_wasserstein_of_minimizer μ ν v hv hv₂ t (q t)
      (hq t)).symm.trans (hcost (q t) t)
  rw [← heq] at hder
  exact hder

end CKSD
