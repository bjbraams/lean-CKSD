module

public import CKSD.Bayes.MeanFieldPicard
public import Mathlib.Probability.IdentDistribIndep

/-!
# Transporting solutions along iid continuous forcings

A measurable inverse of the forcing map transports one continuous solution to identically
distributed independent forcing coordinates. Equality at projected rational times recovers
the entire pathwise integral equation. These generic path-space results do not require a
specific nonlinear drift or Brownian motion.

Mathlib provides independence and identical-distribution transfer; the local path embeddings
and continuous forcing maps provide the measurable reconstruction.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
attribute [local instance] Classical.propDecidable

/-- A measurable inverse solution map transports one solution path to an iid family of input
forcings, giving iid solution paths and retaining the forcing equations. -/
theorem exists_iid_paths_of_forcing_coordinates {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (v : ℝ → E → E) (hv : Continuous (Function.uncurry v)) {L : ℝ≥0}
    (hvL : ∀ s, LipschitzWith L (v s))
    (U : ℕ → Ω → ℚ → E) (hUind : iIndepFun U P)
    (hUid : ∀ i, IdentDistrib (U 0) (U i) P P)
    (Y₀ : Ω → C(Icc (0 : ℝ) T, E))
    (hU₀ : (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (Y₀ ω))) =ᵐ[P] U 0) :
    ∃ Z : ℕ → Ω → C(Icc (0 : ℝ) T, E),
      (∀ i, Measurable (Z i)) ∧ iIndepFun Z P ∧ (∀ i, IdentDistrib (Z i) Y₀ P P) ∧
        ∀ i, (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (Z i ω))) =ᵐ[P] U i := by
  let emb := measurableEmbedding_pathForcingMap hT v hv hvL
  let S : (ℚ → E) → C(Icc (0 : ℝ) T, E) := fun u ↦ emb.invFun (pathOfRationalCoordinates hT u)
  have hS : Measurable S := emb.measurable_invFun.comp (measurable_pathOfRationalCoordinates hT)
  let R : ℕ → Ω → C(Icc (0 : ℝ) T, E) := fun i ω ↦ S (U i ω)
  have hR (i : ℕ) : AEMeasurable (R i) P := hS.comp_aemeasurable (hUid i).aemeasurable_snd
  have hR₀ : R 0 =ᵐ[P] Y₀ := by
    filter_upwards [hU₀] with ω hω
    dsimp [R, S]
    rw [← hω, pathOfRationalCoordinates_apply]
    exact emb.leftInverse_invFun (Y₀ ω)
  let Z : ℕ → Ω → C(Icc (0 : ℝ) T, E) := fun i ↦ (hR i).mk (R i)
  have hZ (i : ℕ) : Measurable (Z i) := (hR i).measurable_mk
  have hZae (i : ℕ) : R i =ᵐ[P] Z i := (hR i).ae_eq_mk
  have hindR : iIndepFun R P := hUind.comp (fun _ ↦ S) (fun _ ↦ hS)
  have hindZ : iIndepFun Z P := hindR.congr hZae
  have hZid (i : ℕ) : IdentDistrib (Z i) Y₀ P P := by
    have hRi : IdentDistrib (R 0) (R i) P P := (hUid i).comp hS
    exact (IdentDistrib.of_ae_eq (hR i) (hZae i)).symm.trans
      (hRi.symm.trans (IdentDistrib.of_ae_eq (hR 0) hR₀))
  have hCoords : Measurable (pathRationalCoordinates (E := E) hT) :=
    (measurableEmbedding_pathRationalCoordinates hT).measurable
  have hΦ : Measurable (pathForcingMap hT v hv) := emb.measurable
  have hGood : MeasurableSet {u : ℚ → E | pathRationalCoordinates hT (pathForcingMap hT v hv (S u)) = u} :=
    measurableSet_eq_fun (hCoords.comp (hΦ.comp hS)) measurable_id
  have hGood₀ : ∀ᵐ ω ∂P, pathRationalCoordinates hT (pathForcingMap hT v hv (S (U 0 ω))) = U 0 ω := by
    filter_upwards [hR₀, hU₀] with ω hω hUω
    change pathRationalCoordinates hT (pathForcingMap hT v hv (R 0 ω)) = U 0 ω
    rw [hω]
    exact hUω
  refine ⟨Z, hZ, hindZ, hZid, fun i ↦ ?_⟩
  have hGoodi := (hUid i).ae_snd hGood hGood₀
  filter_upwards [hGoodi, hZae i] with ω hω hZω
  rw [← hZω]
  exact hω

/-- Equality of the forcing at projected rational times yields the whole pathwise integral equation. -/
theorem eq_integral_of_forcing_coordinates {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E) (hv : Continuous (Function.uncurry v))
    (f : C(Icc (0 : ℝ) T, E)) (ξ : E) (B : ℝ → E) (hB : Continuous B)
    (heq : pathRationalCoordinates hT (pathForcingMap hT v hv f) =
      fun q : ℚ ↦ ξ + B (Set.projIcc 0 T hT q)) :
    ∀ t ∈ Icc (0 : ℝ) T, (f.IccExtend hT) t =
      ξ + (∫ s in (0 : ℝ)..t, v s ((f.IccExtend hT) s)) + B t := by
  let g : C(Icc (0 : ℝ) T, E) := ⟨fun t ↦ ξ + B t, continuous_const.add (hB.comp continuous_subtype_val)⟩
  have hΦ : pathForcingMap hT v hv f = g :=
    (measurableEmbedding_pathRationalCoordinates hT).injective heq
  intro t ht
  have hpoint := congrArg (fun z : C(Icc (0 : ℝ) T, E) ↦ z ⟨t, ht⟩) hΦ
  change f ⟨t, ht⟩ - (∫ s in (0 : ℝ)..t, v s ((f.IccExtend hT) s)) = ξ + B t at hpoint
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) ht]
  have h := sub_eq_iff_eq_add.mp hpoint
  rw [h]
  abel

end CKSD
