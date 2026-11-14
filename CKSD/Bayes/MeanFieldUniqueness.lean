module

public import CKSD.Bayes.MeanFieldLaw
public import CKSD.Bayes.MeanFieldLocalMoments
public import CKSD.Bayes.MeanFieldBrownianBound
public import CKSD.Bayes.MeanFieldWasserstein


/-!
# Same-forcing uniqueness for Wasserstein-Lipschitz nonlinear equations

The nonlinear solution predicate assumes finite first moments at each time, without a locally
uniform bound. Time measurability of the law-dependent drift and an integrable bound on Brownian
forcing first give a uniform integrable envelope on each compact interval. Comparing the drift
with its value at the origin and the Dirac law at the origin then gives actual interval
integrability of each drift along almost every path.

For two solutions with the same forcing, the common-source first-Wasserstein bound controls the
law difference by the expected path difference. The local integrable envelopes justify dominated
convergence and Fubini. The integral inequality for the expected difference, followed by the
pathwise inequality, gives uniqueness. Countably many compact intervals give one almost-sure
event of equality at every nonnegative time.

The local theorem applies to finite-horizon constructions before gluing; its only moment
conditions are the displayed local envelopes and pointwise first moments. The full nonlinear
solution theorem derives these envelopes from the original solution assumptions.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- A solution with integrable initial state and Brownian forcing admits an integrable random
bound uniform on each compact time interval, under exactly the pointwise moment solution predicate. -/
theorem IsMcKeanVlasovSolution.exists_integrable_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hW : IsBrownianEuclidean W P)
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hY : IsMcKeanVlasovSolution b ξ W Y P)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ D ω := by
  have hc := hY.2.2.mono fun ω hω ↦ hω.1
  have hm (s : ℝ) (hs : 0 ≤ s) : Integrable (fun z ↦ ‖z‖) (P.map (Y s)) :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable (hY.1 s).aemeasurable).2 (hY.2.1 s hs)
  have hLip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : LipschitzWith (Real.toNNReal L)
      (fun x ↦ b x (P.map (Y s))) := by
    have : IsProbabilityMeasure (P.map (Y s)) := (Measure.isProbabilityMeasure_map_iff
      (hY.1 s).aemeasurable).2 inferInstance
    exact hb.lipschitz_with_position b _ (hm s hs.1)
  have hbm : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hc] with ω hω
    exact (hb.aestrongly_measurable_drift_of_ae_continuous P b Y hY.1 hc hY.2.1
      (fun s ↦ Y s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  have heq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      Y t ω = (ξ ω + W t.toNNReal ω) + ∫ s in (0 : ℝ)..t, b (Y s ω) (P.map (Y s)) := by
    filter_upwards [hY.2.2] with ω hω
    intro t ht
    rw [hω.2 t ht.1]
    abel
  obtain ⟨B, hBi, hFB⟩ := exists_integrable_uniform_bound_add_brownian_euclidean P ξ hξ W hW.1 T
  exact exists_integrable_uniform_bound_of_spatially_lipschitz_integral_eq P
    (fun s x ↦ b x (P.map (Y s))) (Real.toNNReal L) hT hLip Y
    (fun t ω ↦ ξ ω + W t.toNNReal ω) hc hbm heq B hBi hFB

/-- A time-measurable Wasserstein-Lipschitz drift along an integrably bounded process is
interval-integrable on compact time intervals, by comparison with the drift at the origin. -/
theorem ae_interval_integrable_wasserstein_drift_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hYm : ∀ t, Measurable (Y t))
    {T : ℝ} (_hT : 0 ≤ T)
    (hYint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ω ↦ ‖Y t ω‖) P)
    (hbm : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)))
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ D ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s ↦ b (Y s ω) (P.map (Y s))) volume 0 t := by
  let E := EuclideanSpace ℝ (Fin d)
  let A := (Real.toNNReal L : ℝ)
  let C := ‖b 0 (Measure.dirac (0 : E))‖
  have hm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : Integrable (fun z ↦ ‖z‖) (P.map (Y s)) :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable (hYm s).aemeasurable).2 (hYint s hs)
  have hgrowth (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (z : E) :
      ‖b z (P.map (Y s))‖ ≤ C + A * (‖z‖ + ∫ ω, ‖Y s ω‖ ∂P) := by
    have hpm : IsProbabilityMeasure (P.map (Y s)) := (Measure.isProbabilityMeasure_map_iff
      (hYm s).aemeasurable).2 inferInstance
    have hYi : Integrable (Y s) P := (integrable_norm_iff (hYm s).aestronglyMeasurable).1 (hYint s hs)
    have hwass := wasserstein_e_dist_one_map_to_real_le_integral_norm_sub P
      (hYm s).aestronglyMeasurable aestronglyMeasurable_const (hYi.sub (integrable_const (0 : E)))
    simp only [sub_zero, Measure.map_const, measure_univ, one_smul] at hwass
    have h0 : Integrable (fun z : E ↦ ‖z‖) (Measure.dirac (0 : E)) := integrable_dirac (by finiteness)
    have hh := hb z 0 (P.map (Y s)) (Measure.dirac (0 : E)) hpm inferInstance (hm s hs) h0
    rw [sub_zero] at hh
    have hnn : 0 ≤ ‖z‖ + (TauCeti.wassersteinEDist 1 (P.map (Y s)) (Measure.dirac (0 : E))).toReal := by positivity
    calc ‖b z (P.map (Y s))‖ ≤ ‖b z (P.map (Y s)) - b 0 (Measure.dirac (0 : E))‖ + C :=
        norm_le_norm_sub_add _ _
      _ ≤ A * (‖z‖ + ∫ ω, ‖Y s ω‖ ∂P) + C := by
        apply add_le_add _ le_rfl
        exact (hh.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) hnn)).trans
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hwass) (Real.toNNReal L).coe_nonneg)
      _ = _ := by ring
  have hmean (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : (∫ ω, ‖Y s ω‖ ∂P) ≤ ∫ ω, D ω ∂P :=
    integral_mono_ae (hYint s hs) hD (hbound.mono fun ω hω ↦ hω s hs)
  filter_upwards [hbm, hbound] with ω hbmω hboundω
  have hint : IntegrableOn (fun s ↦ b (Y s ω) (P.map (Y s))) (Ioc (0 : ℝ) T) := by
    apply Integrable.of_bound hbmω (C + A * (D ω + ∫ z, D z ∂P))
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    exact (hgrowth s hs' _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add (hboundω s hs') (hmean s hs')) (Real.toNNReal L).coe_nonneg))
  intro t ht
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hint.mono_set (Ioc_subset_Ioc le_rfl ht.2))

/-- A local integrable envelope makes a nonlinear solution drift interval-integrable. -/
theorem IsMcKeanVlasovSolution.ae_interval_integrable_drift_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hY : IsMcKeanVlasovSolution b ξ W Y P)
    {T : ℝ} (hT : 0 ≤ T) (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ D ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s ↦ b (Y s ω) (P.map (Y s))) volume 0 t := by
  have hc := hY.2.2.mono fun ω hω ↦ hω.1
  have hbm : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hc] with ω hω
    exact (hb.aestrongly_measurable_drift_of_ae_continuous P b Y hY.1 hc hY.2.1
      (fun s ↦ Y s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  exact ae_interval_integrable_wasserstein_drift_of_bound P b hb Y hY.1 hT
    (fun t ht ↦ hY.2.1 t ht.1) hbm D hD hbound

/-- Two locally integrably bounded nonlinear integral equations with the same additive forcing
and a Wasserstein-Lipschitz drift agree almost surely on their common compact time interval. -/
theorem ae_eq_of_wasserstein_integral_eq_on_icc
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Y Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hYm : ∀ t, Measurable (Y t)) (hZm : ∀ t, Measurable (Z t))
    (hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) (hZc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Z t ω))
    {T : ℝ} (hT : 0 ≤ T)
    (hYnorm : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ω ↦ ‖Y t ω‖) P)
    (hZnorm : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ω ↦ ‖Z t ω‖) P)
    (DY DZ : Ω → ℝ) (hDYi : Integrable DY P) (hDZi : Integrable DZ P)
    (hDY : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ DY ω)
    (hDZ : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Z t ω‖ ≤ DZ ω)
    (hbmY : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)))
    (hbmZ : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Z s ω) (P.map (Z s)))
      (volume.restrict (Ioc (0 : ℝ) T)))
    (heq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Y t ω - Z t ω =
      (∫ s in (0 : ℝ)..t, b (Y s ω) (P.map (Y s))) -
        ∫ s in (0 : ℝ)..t, b (Z s ω) (P.map (Z s))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Y t ω = Z t ω := by
  let D : Ω → ℝ := fun ω ↦ DY ω + DZ ω
  let Δ : ℝ → Ω → ℝ := fun t ω ↦ ‖Y t ω - Z t ω‖
  let F : ℝ → ℝ := fun t ↦ ∫ ω, Δ t ω ∂P
  let A := (Real.toNNReal L : ℝ)
  have hDi : Integrable D P := hDYi.add hDZi
  have hΔm (t : ℝ) : Measurable (Δ t) := ((hYm t).sub (hZm t)).norm
  have hΔc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Δ t ω) := by
    filter_upwards [hYc, hZc] with ω hy hz
    exact (hy.sub hz).norm
  have hΔbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Δ t ω ≤ D ω := by
    filter_upwards [hDY, hDZ] with ω hy hz
    intro t ht
    exact (norm_sub_le _ _).trans (add_le_add (hy t ht) (hz t ht))
  have hΔi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Integrable (Δ t) P :=
    hDi.mono' (hΔm t).aestronglyMeasurable (hΔbound.mono fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hω t ht)
  have hFc : ContinuousOn F (Icc (0 : ℝ) T) := by
    apply continuousOn_of_dominated (bound := D)
    · intro t ht
      exact (hΔm t).aestronglyMeasurable
    · intro t ht
      filter_upwards [hΔbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hω t ht
    · exact hDi
    · exact hΔc.mono fun ω hω ↦ hω.continuousOn
  have hbd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (ω : Ω) :
      ‖b (Y s ω) (P.map (Y s)) - b (Z s ω) (P.map (Z s))‖ ≤ A * (Δ s ω + F s) := by
    have hpmY : IsProbabilityMeasure (P.map (Y s)) :=
      (Measure.isProbabilityMeasure_map_iff (hYm s).aemeasurable).2 inferInstance
    have hpmZ : IsProbabilityMeasure (P.map (Z s)) :=
      (Measure.isProbabilityMeasure_map_iff (hZm s).aemeasurable).2 inferInstance
    have hmY : Integrable (fun z ↦ ‖z‖) (P.map (Y s)) :=
      (integrable_map_measure continuous_norm.aestronglyMeasurable (hYm s).aemeasurable).2 (hYnorm s hs)
    have hmZ : Integrable (fun z ↦ ‖z‖) (P.map (Z s)) :=
      (integrable_map_measure continuous_norm.aestronglyMeasurable (hZm s).aemeasurable).2 (hZnorm s hs)
    have hdiff : Integrable (fun ω ↦ Y s ω - Z s ω) P :=
      (integrable_norm_iff ((hYm s).sub (hZm s)).aestronglyMeasurable).1 (hΔi s hs)
    have hwass := wasserstein_e_dist_one_map_to_real_le_integral_norm_sub P
      (hYm s).aestronglyMeasurable (hZm s).aestronglyMeasurable hdiff
    have hh := hb (Y s ω) (Z s ω) (P.map (Y s)) (P.map (Z s)) hpmY hpmZ hmY hmZ
    have hnn : 0 ≤ Δ s ω + (TauCeti.wassersteinEDist 1 (P.map (Y s)) (P.map (Z s))).toReal := by
      exact add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    exact (hh.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) hnn)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hwass) (Real.toNNReal L).coe_nonneg)
  have hYint := ae_interval_integrable_wasserstein_drift_of_bound P b hb Y hYm hT hYnorm hbmY DY hDYi hDY
  have hZint := ae_interval_integrable_wasserstein_drift_of_bound P b hb Z hZm hT hZnorm hbmZ DZ hDZi hDZ
  have hineq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Δ t ω ≤
      A * (∫ s in (0 : ℝ)..t, Δ s ω) + A * (∫ s in (0 : ℝ)..t, F s) := by
    filter_upwards [heq, hYc, hZc, hYint, hZint] with ω heqω hy hz hyi hzi
    intro t ht
    have heq : Y t ω - Z t ω = ∫ s in (0 : ℝ)..t,
        b (Y s ω) (P.map (Y s)) - b (Z s ω) (P.map (Z s)) := by
      exact (heqω t ht).trans (intervalIntegral.integral_sub (hyi t ht) (hzi t ht)).symm
    have hFi : IntervalIntegrable F volume 0 t := by
      have hsub : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2
      exact (hFc.integrableOn_Icc.mono_set hsub).intervalIntegrable
    have hΔci : IntervalIntegrable (fun s ↦ Δ s ω) volume 0 t :=
      (hy.sub hz).norm.intervalIntegrable _ _
    change ‖Y t ω - Z t ω‖ ≤ _
    rw [heq]
    calc _ ≤ ∫ s in (0 : ℝ)..t, ‖b (Y s ω) (P.map (Y s)) - b (Z s ω) (P.map (Z s))‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in (0 : ℝ)..t, A * (Δ s ω + F s) := by
        exact intervalIntegral.integral_mono_on ht.1 ((hyi t ht).sub (hzi t ht)).norm
          ((hΔci.add hFi).const_mul A) (fun s hs ↦ hbd s ⟨hs.1, hs.2.trans ht.2⟩ ω)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hΔci hFi]
        ring
  have hz := ae_eq_zero_of_le_integral_add_integral_mean_of_integrable_bound P Δ hΔm
    (fun _ _ ↦ norm_nonneg _) hΔc D hDi hT (Real.toNNReal L).coe_nonneg
    (Real.toNNReal L).coe_nonneg hΔbound hineq
  filter_upwards [hz] with ω hω
  intro t ht
  exact sub_eq_zero.1 (norm_eq_zero.1 (hω t ht))

/-- Nonlinear solutions with the same integrable initial state and Brownian forcing agree
almost surely on every compact nonnegative time interval. -/
theorem IsMcKeanVlasovSolution.ae_eq_on_icc
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hW : IsBrownianEuclidean W P)
    (Y Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ W Y P) (hZ : IsMcKeanVlasovSolution b ξ W Z P)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Y t ω = Z t ω := by
  obtain ⟨DY, hDYi, hDY⟩ := hY.exists_integrable_uniform_bound P b hb ξ hξ W hW Y hT
  obtain ⟨DZ, hDZi, hDZ⟩ := hZ.exists_integrable_uniform_bound P b hb ξ hξ W hW Z hT
  have hcY := hY.2.2.mono fun ω hω ↦ hω.1
  have hcZ := hZ.2.2.mono fun ω hω ↦ hω.1
  have hmY : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Y s ω) (P.map (Y s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hcY] with ω hω
    exact (hb.aestrongly_measurable_drift_of_ae_continuous P b Y hY.1 hcY hY.2.1
      (fun s ↦ Y s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  have hmZ : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b (Z s ω) (P.map (Z s)))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    filter_upwards [hcZ] with ω hω
    exact (hb.aestrongly_measurable_drift_of_ae_continuous P b Z hZ.1 hcZ hZ.2.1
      (fun s ↦ Z s ω) hω).mono_measure (Measure.restrict_mono_set _ (fun _ hs ↦ hs.1.le))
  apply ae_eq_of_wasserstein_integral_eq_on_icc P b hb Y Z hY.1 hZ.1 hcY hcZ hT
    (fun t ht ↦ hY.2.1 t ht.1) (fun t ht ↦ hZ.2.1 t ht.1) DY DZ hDYi hDZi hDY hDZ hmY hmZ
  filter_upwards [hY.2.2, hZ.2.2] with ω hy hz
  intro t ht
  rw [hy.2 t ht.1, hz.2 t ht.1]
  abel

/-- Nonlinear solutions with the same integrable initial state and Brownian forcing are
indistinguishable on nonnegative times. -/
theorem IsMcKeanVlasovSolution.ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hW : IsBrownianEuclidean W P)
    (Y Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution b ξ W Y P) (hZ : IsMcKeanVlasovSolution b ξ W Z P) :
    ∀ᵐ ω ∂P, ∀ t ≥ 0, Y t ω = Z t ω := by
  have hfinite (n : ℕ) := hY.ae_eq_on_icc P b hb ξ hξ W hW Y Z hZ (T := (n : ℝ)) (Nat.cast_nonneg n)
  filter_upwards [ae_all_iff.2 hfinite] with ω hω
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t ⟨ht, hn⟩

end CKSD
