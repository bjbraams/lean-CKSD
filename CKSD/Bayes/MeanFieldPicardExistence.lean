module

public import CKSD.Bayes.MeanFieldPicardComparison
public import CKSD.Bayes.MeanFieldFactorial
public import CKSD.Bayes.MeanFieldForcing

/-!
# Finite-horizon McKean–Vlasov existence by path-space Picard iteration

The frozen-law Picard operator has a contracting iterate on `L¹(P; C([0,T],E))` by the factorial
Volterra estimate. Its fixed point is an integrable random continuous path solving the nonlinear
integral equation. An integrable initial condition and a Brownian motion supply the required
integrable continuous forcing without any independence assumption between them.

This proves the finite-horizon existence step of GAPS 104.51. Mathlib provides Banach's fixed-point
theorem; the frozen-law estimates, factorial criterion and forcing adapter are in the imported
local modules.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Integrable random continuous forcings admit a nonlinear McKean–Vlasov solution on every
bounded time interval. -/
theorem exists_nonlinear_path_solution (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (F : Ω → C(Icc (0 : ℝ) T, E))
    (hFm : Measurable F) (hFi : Integrable F P) :
    ∃ U : Ω → C(Icc (0 : ℝ) T, E), Measurable U ∧ Integrable U P ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, U ω t = F ω t + ∫ s in (0 : ℝ)..t,
        b ((U ω).IccExtend hT s) (P.map (fun z ↦ (U z).IccExtend hT s)) := by
  let G := nonlinearPathPicard P hT b hb F hFm hFi
  let q : Lp C(Icc (0 : ℝ) T, E) 1 P → Lp C(Icc (0 : ℝ) T, E) 1 P → ℝ → ℝ :=
    fun U V ↦ meanPathDistance P hT U V
  let a := (Real.toNNReal L : ℝ) * Real.exp ((Real.toNNReal L : ℝ) * T)
  have ha : 0 ≤ a := mul_nonneg (Real.toNNReal L).coe_nonneg (Real.exp_pos _).le
  have hbound (U V : Lp C(Icc (0 : ℝ) T, E) 1 P) :
      ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
        ‖(G U ω).IccExtend hT t - (G V ω).IccExtend hT t‖ ≤ a * ∫ s in (0 : ℝ)..t, q U V s :=
    nonlinearPathPicard_ae_norm_sub_le P hT b hb F hFm hFi U V
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_of_integral_estimates G q ha hT
    (fun U V ↦ continuous_meanPathDistance_L1 P hT U V)
    (fun U V t _ ↦ by simpa only [dist_eq_norm] using meanPathDistance_le_norm_sub P hT U V t)
    (fun U V t ht ↦ meanPathDistance_le_integral_of_ae_bound P hT (G U) (G V) a (q U V) (hbound U V) t ht)
    (fun U V ↦ dist_L1_le_integral_of_ae_bound P hT (G U) (G V) a ha (q U V)
      (continuous_meanPathDistance_L1 P hT U V) (fun s _ ↦ meanPathDistance_nonneg P hT U V s) (hbound U V))
  obtain ⟨U, hU⟩ : ∃ U, Function.IsFixedPt G U := ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  change G U = U at hU
  have hraw : (U : Ω → C(Icc (0 : ℝ) T, E)) =ᵐ[P]
      fun ω ↦ frozenPathSolutionMap P hT b hb U (Lp.stronglyMeasurable U).measurable
        (L1.integrable_coeFn U) (F ω) := by
    have h := nonlinearPathPicard_ae_eq P hT b hb F hFm hFi U
    change (G U : Ω → C(Icc (0 : ℝ) T, E)) =ᵐ[P] _ at h
    rwa [hU] at h
  refine ⟨U, (Lp.stronglyMeasurable U).measurable, L1.integrable_coeFn U, ?_⟩
  filter_upwards [hraw] with ω hω
  intro t
  have heq := frozenPathSolutionMap_apply_eq P hT b hb U (Lp.stronglyMeasurable U).measurable
    (L1.integrable_coeFn U) (F ω) t
  rw [← hω] at heq
  simpa only [nonlinearFrozenDrift, pathMarginalLaw_toMeasure] using heq

/-- An integrable initial condition and Brownian forcing admit nonlinear solution paths on any
bounded interval. -/
theorem exists_nonlinear_brownian_path_solution (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (ξ : Ω → E) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → E) (hW : IsBrownianEuclidean W P) :
    ∃ U : Ω → C(Icc (0 : ℝ) T, E), Measurable U ∧ Integrable U P ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, U ω t = ξ ω + W (t : ℝ).toNNReal ω + ∫ s in (0 : ℝ)..t,
        b ((U ω).IccExtend hT s) (P.map (fun z ↦ (U z).IccExtend hT s)) := by
  obtain ⟨F, hFm, hFi, hF⟩ := exists_integrable_brownian_forcing_path P ξ hξ W hW hT
  obtain ⟨U, hUm, hUi, hU⟩ := exists_nonlinear_path_solution P hT b hb F hFm hFi
  refine ⟨U, hUm, hUi, ?_⟩
  filter_upwards [hU, hF] with ω hω hFω
  intro t
  rw [hω t, hFω t]
end CKSD
