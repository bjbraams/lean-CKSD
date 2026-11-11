module

public import CKSD.Bayes.MeanFieldTransport
public import CKSD.Bayes.MeanFieldForcing
public import CKSD.Bayes.MeanFieldUniqueness
public import CKSD.Bayes.MeanFieldPicardLaw

/-!
# Independent nonlinear paths driven by iid original inputs

An integrable path version of one McKean–Vlasov solution has first-Wasserstein-continuous
marginal laws. Freezing those laws gives a measurable invertible forcing map. Transporting along
the original iid input forcings constructs independent nonlinear copies with the original
solution's path law, each sharing its prescribed initial state and Brownian driver.

The proof uses Mathlib's independence/identical-distribution transfer and the local path
reconstruction, moment bounds and frozen-law continuity. It supports GAPS 104.51 propagation of
chaos without assuming independence of separately chosen nonlinear solutions.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- One nonlinear solution supplies iid nonlinear path copies driven by the original iid
initial states and Brownian motions, for a general Wasserstein-Lipschitz drift. -/
theorem exists_iid_mcKeanVlasov_paths_on_Icc {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (hξ : Integrable (X₀ 0) P) (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b (X₀ 0) (W 0) Y P) {T : ℝ} (hT : 0 ≤ T) :
    ∃ Z : ℕ → Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)),
      (∀ i, Measurable (Z i)) ∧ (∀ i, Integrable (Z i) P) ∧ iIndepFun Z P ∧
      (∀ i, IdentDistrib (Z i) (fun ω ↦ pathOn T (fun t ↦ Y t ω)) P P) ∧
      ∀ i, ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T,
        Z i ω t = X₀ i ω + (∫ s in (0 : ℝ)..t,
          b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z i z).IccExtend hT s))) + W i (t : ℝ).toNNReal ω := by
  have hYc := hY.2.2.mono fun _ hω ↦ hω.1
  obtain ⟨D, hDi, hD⟩ := IsMcKeanVlasovSolution.exists_integrable_uniform_bound P b hb
    (X₀ 0) hξ (W 0) (hiid.2.2.1 0) Y hY hT
  obtain ⟨S, hSm, hSi, hS⟩ := exists_integrable_measurable_continuousPath_version P Y
    (fun t ↦ (hY.1 t).aemeasurable) hYc hT D hDi hD
  have hSext : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, (S ω).IccExtend hT t = Y t ω := by
    filter_upwards [hS] with ω hω
    intro t ht
    rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ S ω z) ht]
    exact hω ⟨t, ht⟩
  have hSmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      P.map (fun ω ↦ (S ω).IccExtend hT t) = P.map (Y t) :=
    Measure.map_congr (hSext.mono fun ω hω ↦ hω t ht)
  have hSraw : S =ᵐ[P] (fun ω ↦ pathOn T (fun t ↦ Y t ω)) := by
    filter_upwards [hS, hYc] with ω hω hc
    apply ContinuousMap.ext
    intro t
    rw [pathOn_apply_of_continuousOn T (fun s ↦ Y s ω) hc.continuousOn t]
    exact hω t
  let v := nonlinearFrozenDrift P hT b S hSm hSi
  have hv : Continuous (Function.uncurry v) := continuous_nonlinearFrozenDrift P hT b hb S hSm hSi
  have hvL := lipschitzWith_nonlinearFrozenDrift P hT b hb S hSm hSi
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : EuclideanSpace ℝ (Fin d)) :
      b x (P.map (Y t)) = v t x := by
    change b x (P.map (Y t)) = nonlinearFrozenDrift P hT b S hSm hSi t x
    rw [nonlinearFrozenDrift, pathMarginalLaw_toMeasure, hSmap t ht]
  let times : ℚ → ℝ≥0 := fun q ↦ (Set.projIcc 0 T hT q : ℝ).toNNReal
  let U : ℕ → Ω → ℚ → EuclideanSpace ℝ (Fin d) := fun i ω q ↦ X₀ i ω + W i (times q) ω
  have hU₀ : (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (S ω))) =ᵐ[P] U 0 := by
    filter_upwards [hSext, hY.2.2] with ω hSω hω
    funext q
    let t := Set.projIcc 0 T hT q
    change S ω t - (∫ s in (0 : ℝ)..t, v s ((S ω).IccExtend hT s)) = X₀ 0 ω + W 0 (times q) ω
    have hSt : S ω t = Y t ω := by
      simpa only [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ S ω z) t.2]
        using hSω t t.2
    rw [hSt]
    have hint : (∫ s in (0 : ℝ)..t, v s ((S ω).IccExtend hT s)) =
        ∫ s in (0 : ℝ)..t, b (Y s ω) (P.map (Y s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.2.1] at hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
      dsimp only
      rw [hSω s hsT, ← hmap s hsT]
    rw [hint, hω.2 t t.2.1]
    dsimp [times, t]
    abel
  obtain ⟨Z, hZm, hZind, hZid, hZeq⟩ := exists_iid_paths_of_forcing_coordinates P hT v hv hvL U
    (IsIIDInitialAndDrivers.iIndepFun_forcing_evals P X₀ W μ₀ hiid times)
    (fun i ↦ IsIIDInitialAndDrivers.identDistrib_forcing_evals P X₀ W μ₀ hiid times 0 i) S hU₀
  have hEval (s : ℝ) : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)) ↦ f.IccExtend hT s) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT s)
  have hZmap (i : ℕ) (s : ℝ) : P.map (fun ω ↦ (Z i ω).IccExtend hT s) =
      P.map (fun ω ↦ (S ω).IccExtend hT s) := ((hZid i).comp (hEval s)).map_eq
  refine ⟨Z, hZm, fun i ↦ (hZid i).integrable_iff.mpr hSi, hZind,
    fun i ↦ (hZid i).trans (IdentDistrib.of_ae_eq hSm.aemeasurable hSraw), fun i ↦ ?_⟩
  filter_upwards [hZeq i, (hiid.2.2.1 i).ae_continuous_toNNReal] with ω hω hB
  have heq := eq_integral_of_forcing_coordinates hT v hv (Z i ω) (X₀ i ω)
    (fun t ↦ W i t.toNNReal ω) hB hω
  intro t
  have hp := heq t t.2
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ Z i ω z) t.2] at hp
  rw [hp]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  change nonlinearFrozenDrift P hT b S hSm hSi s ((Z i ω).IccExtend hT s) = _
  rw [nonlinearFrozenDrift, pathMarginalLaw_toMeasure, hZmap i s]
end CKSD
