module

public import CKSD.Bayes.MeanFieldParticles
public import CKSD.Bayes.MeanFieldPicardLaw


/-!
# Finite-vector equations for synchronous particle coupling

The original particle-system equations and same-input nonlinear path equations combine into
finite-dimensional vector integral equations. Identical reference path laws give a common
marginal drift, and continuous frozen laws justify commuting finite coordinate projections
with the Bochner time integral.

Mathlib supplies finite-coordinate continuous linear projections and integral interchange;
the local Wasserstein-Lipschitz and frozen-law results supply continuity of both vector drifts.
This adapter supports GAPS 104.51 propagation of chaos.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- Same-input particle systems and identically distributed nonlinear paths satisfy the finite
vector integral equations used by the synchronous propagation-of-chaos estimate. -/
theorem IsParticleSystem.ae_coupled_vector_integral_eq_on_icc
    {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (X : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : IsParticleSystem b X₀ W N X P)
    (Z : ℕ → Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)))
    (hZm : ∀ i, Measurable (Z i)) (hZi : Integrable (Z 0) P)
    (hZid : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hZeq : ∀ i, ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T,
      Z i ω t = X₀ i ω + (∫ s in (0 : ℝ)..t,
        b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z i z).IccExtend hT s))) + W i (t : ℝ).toNNReal ω) :
    ∀ᵐ ω ∂P,
      Continuous (fun t ↦ fun j : Fin N ↦ X j t ω) ∧
      Continuous (fun t ↦ fun j : Fin N ↦ (Z j ω).IccExtend hT t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, (fun j : Fin N ↦ X j t ω) =
        (fun j : Fin N ↦ X₀ j ω + W j t.toNNReal ω) + ∫ s in (0 : ℝ)..t,
          fun j : Fin N ↦ b (X j s ω) (empiricalMeasure N (fun l : Fin N ↦ X l s ω))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, (fun j : Fin N ↦ (Z j ω).IccExtend hT t) =
        (fun j : Fin N ↦ X₀ j ω + W j t.toNNReal ω) + ∫ s in (0 : ℝ)..t,
          fun j : Fin N ↦ b ((Z j ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let v : (Fin N → E) → Fin N → E := fun x j ↦ b (x j) (empiricalMeasure N x)
  have hv := hb.lipschitz_with_particle_drift b hN
  let w : ℝ → (Fin N → E) → Fin N → E := fun t x j ↦
    b (x j) (P.map (fun z ↦ (Z 0 z).IccExtend hT t))
  have hw : Continuous (Function.uncurry w) := by
    have hc := continuous_nonlinear_frozen_drift P hT b hb (Z 0) (hZm 0) hZi
    have hc' : Continuous (fun p : ℝ × E ↦ b p.2 (P.map (fun z ↦ (Z 0 z).IccExtend hT p.1))) := by
      convert hc using 1
      funext p
      change b p.2 (P.map (fun z ↦ (Z 0 z).IccExtend hT p.1)) =
        nonlinearFrozenDrift P hT b (Z 0) (hZm 0) hZi p.1 p.2
      rw [nonlinearFrozenDrift, path_marginal_law_to_measure]
    apply continuous_pi
    intro j
    exact hc'.comp (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))
  have hEval (s : ℝ) : Measurable (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT s) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT s)
  have hZmap (j : ℕ) (s : ℝ) : P.map (fun z ↦ (Z j z).IccExtend hT s) =
      P.map (fun z ↦ (Z 0 z).IccExtend hT s) := ((hZid j).comp (hEval s)).map_eq
  filter_upwards [ae_all_iff.2 (fun j : Fin N ↦ hX.2 j j.isLt),
    ae_all_iff.2 (fun j : Fin N ↦ hZeq j)] with ω hx hz
  let x : ℝ → Fin N → E := fun t j ↦ X j t ω
  let y : ℝ → Fin N → E := fun t j ↦ (Z j ω).IccExtend hT t
  have hxc : Continuous x := continuous_pi fun j ↦ (hx j).1
  have hyc : Continuous y := continuous_pi fun j ↦ ((Z j ω).IccExtend hT).continuous
  refine ⟨hxc, hyc, ?_, ?_⟩
  · intro t ht
    have hi : IntervalIntegrable (fun s ↦ v (x s)) volume 0 t := (hv.continuous.comp hxc).intervalIntegrable _ _
    funext j
    have hp := (ContinuousLinearMap.proj j : (Fin N → E) →L[ℝ] E).intervalIntegral_comp_comm hi
    change (∫ s in (0 : ℝ)..t, b (X j s ω) (empiricalMeasure N (fun l : Fin N ↦ X l s ω))) =
      (∫ s in (0 : ℝ)..t, fun l : Fin N ↦ b (X l s ω) (empiricalMeasure N (fun m : Fin N ↦ X m s ω))) j at hp
    change X j t ω = X₀ j ω + W j t.toNNReal ω + _
    rw [← hp, (hx j).2 t ht.1]
    abel
  · intro t ht
    have hi : IntervalIntegrable (fun s ↦ w s (y s)) volume 0 t :=
      (hw.comp (continuous_id.prodMk hyc)).intervalIntegrable _ _
    funext j
    have hp := (ContinuousLinearMap.proj j : (Fin N → E) →L[ℝ] E).intervalIntegral_comp_comm hi
    change (∫ s in (0 : ℝ)..t, b ((Z j ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) =
      (∫ s in (0 : ℝ)..t, fun l : Fin N ↦ b ((Z l ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) j at hp
    have hzt : (Z j ω).IccExtend hT t = Z j ω ⟨t, ht⟩ :=
      Set.IccExtend_of_mem (h := hT) (fun z ↦ Z j ω z) ht
    change (Z j ω).IccExtend hT t = X₀ j ω + W j t.toNNReal ω + _
    rw [hzt, ← hp, hz j ⟨t, ht⟩]
    have he : (∫ s in (0 : ℝ)..t, b ((Z j ω).IccExtend hT s) (P.map (fun z ↦ (Z j z).IccExtend hT s))) =
        ∫ s in (0 : ℝ)..t, b ((Z j ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hZmap j s]
    rw [he]
    abel
end CKSD
