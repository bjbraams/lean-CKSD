module

public import CKSD.Bayes.MeanFieldGlobal
public import CKSD.Bayes.MeanFieldPicardLaw
public import CKSD.Bayes.MeanFieldUniqueness
/-!
# Global nonlinear solutions from integrable compact-interval paths

Finite-interval nonlinear solutions have integrable uniform path bounds. Local same-forcing
uniqueness therefore makes these solutions consistent on overlaps. Countably many increasing
intervals give a single almost-sure event of consistency, and measurable path gluing produces a
global process. Its marginal moments and integral equation follow from the corresponding local
properties and equality of the marginal laws.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology
namespace CKSD
/-- Integrable nonlinear solutions on every compact interval yield a global solution. -/
theorem exists_mc_kean_vlasov_solution_of_compact_solutions
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hlocal : ∀ (T : ℝ) (hT : 0 ≤ T),
      ∃ U : Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)), Measurable U ∧ Integrable U P ∧
        ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T,
          U ω t = ξ ω + W (t:ℝ).toNNReal ω + ∫ s in (0 : ℝ)..t,
            b ((U ω).IccExtend hT s) (P.map (fun ω ↦ (U ω).IccExtend hT s))) :
    ∃ Y, IsMcKeanVlasovSolution b ξ W Y P := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let T : ℕ → ℝ := fun n ↦ (n:ℝ)+1
  have hT (n : ℕ) : 0 ≤ T n := by dsimp [T]; positivity
  choose U hUm hUi hU using fun n ↦ hlocal (T n) (hT n)
  let Y : ℕ → ℝ → Ω → E := fun n t ω ↦ (U n ω).IccExtend (hT n) t
  have hYm (n : ℕ) (t : ℝ) : Measurable (Y n t) :=
    (ContinuousMap.measurable_eval (projIcc 0 (T n) (hT n) t)).comp (hUm n)
  have hYi (n : ℕ) (t : ℝ) : Integrable (Y n t) P :=
    integrable_icc_extend_eval P (hT n) (U n) (hUm n) (hUi n) t
  have hYc (n : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y n t ω) :=
    ae_of_all _ fun ω ↦ ((U n ω).IccExtend (hT n)).continuous
  have hYbound (n : ℕ) : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0:ℝ) (T n), ‖Y n t ω‖ ≤ ‖U n ω‖ :=
    ae_of_all _ fun ω t _ ↦ (U n ω).norm_coe_le_norm _
  have hbm (n : ℕ) : ∀ᵐ ω ∂P, AEStronglyMeasurable
      (fun s ↦ b (Y n s ω) (P.map (Y n s))) volume := by
    refine ae_of_all _ fun ω ↦ ?_
    have hc := (continuous_nonlinear_frozen_drift P (hT n) b hb (U n) (hUm n) (hUi n)).comp
      (continuous_id.prodMk (((U n ω).IccExtend (hT n)).continuous))
    simpa only [nonlinearFrozenDrift, path_marginal_law_to_measure, Function.comp_def,
      Function.uncurry_apply_pair, Y, id_eq] using (hc.aestronglyMeasurable (μ := volume))
  have hYe (n : ℕ) : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) (T n),
      Y n t ω = ξ ω + W t.toNNReal ω + ∫ s in (0:ℝ)..t, b (Y n s ω) (P.map (Y n s)) := by
    filter_upwards [hU n] with ω hω
    intro t ht
    have he := hω ⟨t,ht⟩
    have hev : Y n t ω = U n ω ⟨t,ht⟩ :=
      Set.IccExtend_of_mem (h := hT n) (fun z ↦ U n ω z) ht
    exact hev.trans he
  have hconsPair (n m : ℕ) : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) (min (T n) (T m)),
      Y n t ω = Y m t ω := by
    apply ae_eq_of_wasserstein_integral_eq_on_icc P b hb (Y n) (Y m) (hYm n) (hYm m)
      (hYc n) (hYc m) (le_min (hT n) (hT m))
      (fun t _ ↦ (hYi n t).norm) (fun t _ ↦ (hYi m t).norm)
      (fun ω ↦ ‖U n ω‖) (fun ω ↦ ‖U m ω‖) (hUi n).norm (hUi m).norm
    · exact (hYbound n).mono fun ω hω t ht ↦ hω t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    · exact (hYbound m).mono fun ω hω t ht ↦ hω t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
    · exact (hbm n).mono fun ω hω ↦ hω.mono_measure Measure.restrict_le_self
    · exact (hbm m).mono fun ω hω ↦ hω.mono_measure Measure.restrict_le_self
    · filter_upwards [hYe n, hYe m] with ω hn hm
      intro t ht
      rw [hn t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩,
        hm t ⟨ht.1,ht.2.trans (min_le_right _ _)⟩]
      abel
  have hcons : ∀ᵐ ω ∂P, ∀ (n m : ℕ) (t : ℝ), 0 ≤ t → t ≤ (n:ℝ)+1 → t ≤ (m:ℝ)+1 →
      (U n ω).IccExtend (by positivity) t = (U m ω).IccExtend (by positivity) t := by
    filter_upwards [ae_all_iff.2 (fun n ↦ ae_all_iff.2 (hconsPair n))] with ω hω
    intro n m t ht hn hm
    exact hω n m t ⟨ht,le_min hn hm⟩
  obtain ⟨X,hXm,hX⟩ := exists_measurable_process_of_consistent_paths P U hUm hcons
  have hsame (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T n)) : X t =ᵐ[P] Y n t := by
    filter_upwards [hX] with ω hω
    exact (hω.2 n ⟨t,ht⟩).trans (Set.IccExtend_of_mem (h := hT n) (fun z ↦ U n ω z) ht).symm
  have hlaw (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T n)) :
      P.map (X t) = P.map (Y n t) := Measure.map_congr (hsame n t ht)
  refine ⟨X,hXm,?_,?_⟩
  · intro t ht
    obtain ⟨n,hnt⟩ := exists_nat_gt t
    have htn : t ≤ T n := by dsimp [T]; linarith
    exact ((hYi n t).norm).congr ((hsame n t ⟨ht,htn⟩).mono fun ω hω ↦ congrArg norm hω.symm)
  · filter_upwards [hX,ae_all_iff.2 hYe] with ω hω hye
    refine ⟨hω.1,?_⟩
    intro t ht
    obtain ⟨n,hnt⟩ := exists_nat_gt t
    have htn : t ≤ T n := by dsimp [T]; linarith
    have hs (s : ℝ) (hst : s ∈ Icc (0:ℝ) t) : X s ω = Y n s ω :=
      (hω.2 n ⟨s,⟨hst.1,hst.2.trans htn⟩⟩).trans
        (Set.IccExtend_of_mem (h := hT n) (fun z ↦ U n ω z) ⟨hst.1,hst.2.trans htn⟩).symm
    have hi : (∫ s in (0:ℝ)..t, b (X s ω) (P.map (X s))) =
        ∫ s in (0:ℝ)..t, b (Y n s ω) (P.map (Y n s)) := by
      apply intervalIntegral.integral_congr
      intro s hst
      have hst' : s ∈ Icc (0:ℝ) t := by simpa only [uIcc_of_le ht] using hst
      dsimp only
      rw [hs s hst', hlaw n s ⟨hst'.1,hst'.2.trans htn⟩]
    rw [hs t ⟨ht,le_rfl⟩,hi,hye n t ⟨ht,htn⟩]
    abel
end CKSD
