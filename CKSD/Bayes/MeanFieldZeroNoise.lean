module
public import CKSD.Bayes.MeanFieldUniqueness
public import CKSD.Bayes.MeanFieldPicardExistence
public import CKSD.Bayes.MeanFieldGlue
public import CKSD.Bayes.MeanFieldLaw
public import CKSD.Bayes.MeanFieldWasserstein
public import CKSD.Bayes.MeanFieldContinuityCurves
/-!
# Deterministic nonlinear trajectories with integrable initial laws

The compact-path Picard construction and consistent-path gluing give global zero-forcing
nonlinear integral solutions. For uniformly bounded drift their paths are uniformly Lipschitz
on nonnegative time, and the common-source coupling gives the same Lipschitz bound for their
marginal laws in first-Wasserstein distance.

The construction uses the local McKean–Vlasov path-space theory; Mathlib supplies integrability
and the fundamental integral bounds, and pinned TauCeti supplies Wasserstein coupling through
the local adapter. These results support the deterministic mean-field limit in GAPS 104.53.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
/-- A globally Wasserstein-Lipschitz drift has a global nonlinear integral solution from any
integrable initial state, with zero additional forcing. -/
theorem exists_mcKeanVlasovSolution_zero_forcing
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξm : Measurable ξ) (hξi : Integrable ξ P) :
    ∃ Y, IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P := by
  apply exists_mcKeanVlasovSolution_of_compact_solutions P b hb ξ (fun _ _ ↦ 0)
  intro T hT
  let F : Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)) :=
    fun ω ↦ ContinuousMap.const _ (ξ ω)
  have hFm : Measurable F := ContinuousMap.measurable_iff_eval.2 fun _ ↦ hξm
  have hFi : Integrable F P := hξi.norm.mono' hFm.aestronglyMeasurable (ae_of_all _ fun ω ↦ by
    apply (ContinuousMap.norm_le _ (norm_nonneg (ξ ω))).2
    intro t
    exact le_rfl)
  obtain ⟨U, hUm, hUi, hU⟩ := exists_nonlinear_path_solution P hT b hb F hFm hFi
  refine ⟨U, hUm, hUi, ?_⟩
  filter_upwards [hU] with ω hω
  intro t
  simpa only [zero_add, add_zero, F, ContinuousMap.const_apply] using hω t

/-- Bounded drift makes every zero-forcing nonlinear solution uniformly Lipschitz in time
on the nonnegative half-line, under the original pointwise-moment solution predicate. -/
theorem IsMcKeanVlasovSolution.ae_norm_sub_le_of_zero_forcing_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M) :
    ∀ᵐ ω ∂P, ∀ s ≥ 0, ∀ t ≥ 0, ‖Y s ω - Y t ω‖ ≤ (M : ℝ) * |t - s| := by
  have hc := hY.2.2.mono fun ω hω ↦ hω.1
  filter_upwards [hY.2.2] with ω hω
  let F : ℝ → EuclideanSpace ℝ (Fin d) := fun r ↦ b (Y r ω) (P.map (Y r))
  have hFm := hb.aestronglyMeasurable_drift_of_ae_continuous P b Y hY.1 hc hY.2.1
    (fun r ↦ Y r ω) hω.1
  have hFbound (r : ℝ) : ‖F r‖ ≤ M := hM _ inferInstance _
  have hi (r : ℝ) (hr : 0 ≤ r) : IntervalIntegrable F volume 0 r := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).2
    apply Integrable.of_bound
      (hFm.mono_measure (Measure.restrict_mono_set _ (show Ioc (0 : ℝ) r ⊆ Ici 0 from fun _ hs ↦ hs.1.le))) M
    exact ae_of_all _ hFbound
  have he (r : ℝ) (hr : 0 ≤ r) : Y r ω = ξ ω + ∫ q in (0 : ℝ)..r, F q := by
    simpa only [add_zero] using hω.2 r hr
  have hfor (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (hst : s ≤ t) :
      ‖Y s ω - Y t ω‖ ≤ (M : ℝ) * (t - s) := by
    have hit : IntervalIntegrable F volume s t := (hi s hs).symm.trans (hi t (hs.trans hst))
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hi s hs) hit
    have heq : Y s ω - Y t ω = -(∫ q in s..t, F q) := by
      rw [he s hs, he t (hs.trans hst), ← hadd]
      abel
    rw [heq, norm_neg]
    simpa only [sub_nonneg.2 hst, abs_of_nonneg (sub_nonneg.2 hst)] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (fun r _ ↦ hFbound r)
  intro s hs t ht
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.2 hst)] using hfor s hs t hst
  · have hh := hfor t ht s hts
    simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 hts), neg_sub] using hh

/-- The laws of a bounded-drift zero-forcing nonlinear solution are Lipschitz in first
Wasserstein distance on nonnegative time. -/
theorem IsMcKeanVlasovSolution.wassersteinEDist_toReal_le_of_zero_forcing_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M)
    (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (ht : 0 ≤ t) :
    (TauCeti.wassersteinEDist 1 (P.map (Y s)) (P.map (Y t))).toReal ≤ (M : ℝ) * |t - s| := by
  have his : Integrable (Y s) P := (integrable_norm_iff (hY.1 s).aestronglyMeasurable).1 (hY.2.1 s hs)
  have hit : Integrable (Y t) P := (integrable_norm_iff (hY.1 t).aestronglyMeasurable).1 (hY.2.1 t ht)
  have hW := wassersteinEDist_one_map_toReal_le_integral_norm_sub P
    (hY.1 s).aestronglyMeasurable (hY.1 t).aestronglyMeasurable (his.sub hit)
  have hbd := (hY.ae_norm_sub_le_of_zero_forcing_of_bound P b hb ξ Y M hM).mono
    fun ω hω ↦ hω s hs t ht
  apply hW.trans
  calc
    (∫ ω, ‖Y s ω - Y t ω‖ ∂P) ≤ ∫ _ : Ω, (M : ℝ) * |t - s| ∂P :=
      integral_mono_ae (his.sub hit).norm (integrable_const _) hbd
    _ = _ := by simp

/-- A bounded drift bounds a zero-forcing solution by its initial norm plus elapsed time. -/
theorem IsMcKeanVlasovSolution.ae_norm_le_of_zero_forcing_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M)
    {T : ℝ} (_hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ ‖ξ ω‖ + (M : ℝ) * T := by
  filter_upwards [hY.2.2] with ω hω
  intro t ht
  rw [hω.2 t ht.1, add_zero]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s ↦ b (Y s ω) (P.map (Y s))) (C := (M : ℝ)) (fun _ _ ↦ hM _ inferInstance _)
  simp only [sub_zero, abs_of_nonneg ht.1] at hi
  exact (norm_add_le _ _).trans (add_le_add le_rfl (hi.trans (mul_le_mul_of_nonneg_left ht.2 M.coe_nonneg)))

/-- Bounded-drift nonlinear solutions with the same initial state and zero forcing are
indistinguishable on each compact nonnegative interval. -/
theorem IsMcKeanVlasovSolution.ae_eq_on_Icc_of_zero_forcing_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξi : Integrable ξ P)
    (Y Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P)
    (hZ : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Z P)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Y t ω = Z t ω := by
  let D : Ω → ℝ := fun ω ↦ ‖ξ ω‖ + (M : ℝ) * T
  have hDi : Integrable D P := hξi.norm.add (integrable_const _)
  have hcY := hY.2.2.mono fun ω hω ↦ hω.1
  have hcZ := hZ.2.2.mono fun ω hω ↦ hω.1
  have hmY : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hcY] with ω hω
    exact (hb.aestronglyMeasurable_drift_of_ae_continuous P b Y hY.1 hcY hY.2.1
      (fun s ↦ Y s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  have hmZ : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Z s ω) (P.map (Z s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hcZ] with ω hω
    exact (hb.aestronglyMeasurable_drift_of_ae_continuous P b Z hZ.1 hcZ hZ.2.1
      (fun s ↦ Z s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  apply ae_eq_of_wasserstein_integral_eq_on_Icc P b hb Y Z hY.1 hZ.1 hcY hcZ hT
    (fun t ht ↦ hY.2.1 t ht.1) (fun t ht ↦ hZ.2.1 t ht.1) D D hDi hDi
    (hY.ae_norm_le_of_zero_forcing_of_bound P b ξ Y M hM hT)
    (hZ.ae_norm_le_of_zero_forcing_of_bound P b ξ Z M hM hT) hmY hmZ
  filter_upwards [hY.2.2, hZ.2.2] with ω hy hz
  intro t ht
  rw [hy.2 t ht.1, hz.2 t ht.1]
  abel

/-- Bounded-drift nonlinear solutions with the same initial state and zero forcing agree
almost surely at every nonnegative time. -/
theorem IsMcKeanVlasovSolution.ae_eq_of_zero_forcing_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξi : Integrable ξ P)
    (Y Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Y P)
    (hZ : IsMcKeanVlasovSolution b ξ (fun _ _ ↦ 0) Z P)
    (M : ℝ≥0) (hM : ∀ μ, IsProbabilityMeasure μ → ∀ x, ‖b x μ‖ ≤ M) :
    ∀ᵐ ω ∂P, ∀ t ≥ 0, Y t ω = Z t ω := by
  have hlocal (n : ℕ) := hY.ae_eq_on_Icc_of_zero_forcing_of_bound P b hb ξ hξi Y Z hZ M hM
    (T := (n : ℝ)) (Nat.cast_nonneg n)
  filter_upwards [ae_all_iff.2 hlocal] with ω hω
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t ⟨ht, hn⟩
end CKSD
