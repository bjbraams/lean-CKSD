module

public import CKSD.Bayes.MeanFieldCoupling


/-!
# Local moment bounds from spatial Lipschitz continuity

For a common spatially Lipschitz time-dependent drift, two continuous integral-equation paths
satisfy a Grönwall bound in terms of their additive forcing. This estimate requires time
measurability of the drift integrands, but it does not assume their integrability in advance.
On a compact time interval, their difference is integrable by the spatial Lipschitz bound.
Hence either both drift integrals are defined, when they can be subtracted, or both are zero
under the total Bochner-integral convention, when the same inequality holds directly.

Anchoring one good continuous sample path and applying this relative-path estimate gives an
integrable random bound uniform over the whole time interval whenever the additive forcing
has such a bound. This supplies local moment domination without assuming it in the solution
predicate. The final scalar integral Grönwall step uses pinned TauCeti.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Continuous integral-equation paths with a common spatially Lipschitz drift satisfy the
forcing-dependent Grönwall bound, assuming time measurability of their drift integrands.
Their drift integrability is simultaneous because the difference is integrable. -/
theorem norm_sub_le_of_spatially_lipschitz_integral_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℝ → E → E) (L : ℝ≥0) {T R : ℝ} (_hT : 0 ≤ T) (hR : 0 ≤ R)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, LipschitzWith L (b s))
    (x y f g : ℝ → E) (hx : Continuous x) (hy : Continuous y)
    (hxm : AEStronglyMeasurable (fun s ↦ b s (x s)) (volume.restrict (Ioc (0 : ℝ) T)))
    (hym : AEStronglyMeasurable (fun s ↦ b s (y s)) (volume.restrict (Ioc (0 : ℝ) T)))
    (hforcing : ∀ t ∈ Icc (0 : ℝ) T, ‖f t - g t‖ ≤ R)
    (heqx : ∀ t ∈ Icc (0 : ℝ) T, x t = f t + ∫ s in (0 : ℝ)..t, b s (x s))
    (heqy : ∀ t ∈ Icc (0 : ℝ) T, y t = g t + ∫ s in (0 : ℝ)..t, b s (y s)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤ R * Real.exp ((L : ℝ) * T) := by
  let d : ℝ → E := fun s ↦ b s (x s) - b s (y s)
  have hφ : Continuous (fun s ↦ ‖x s - y s‖) := (hx.sub hy).norm
  have hdT : IntegrableOn d (Ioc (0 : ℝ) T) := by
    have hdom : IntegrableOn (fun s ↦ (L : ℝ) * ‖x s - y s‖) (Ioc (0 : ℝ) T) :=
      (hφ.const_mul L).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact hdom.mono' (hxm.sub hym) (ae_restrict_of_forall_mem measurableSet_Ioc
      fun s hs ↦ (hLip s ⟨hs.1.le, hs.2⟩).norm_sub_le (x s) (y s))
  have hineq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖x t - y t‖ ≤ R + (L : ℝ) * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
    have hdt : IntervalIntegrable d volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
        (hdT.mono_set (Ioc_subset_Ioc le_rfl ht.2))
    by_cases hxi : IntervalIntegrable (fun s ↦ b s (x s)) volume 0 t
    · have hyi : IntervalIntegrable (fun s ↦ b s (y s)) volume 0 t := by
        have heq : (fun s ↦ b s (y s)) = (fun s ↦ b s (x s)) - d := by
          funext s
          simp only [Pi.sub_apply, d]
          abel
        rw [heq]
        exact hxi.sub hdt
      have heq : x t - y t = (f t - g t) + ∫ s in (0 : ℝ)..t, d s := by
        rw [heqx t ht, heqy t ht]
        rw [show (∫ s in (0 : ℝ)..t, d s) = (∫ s in (0 : ℝ)..t, b s (x s)) -
          (∫ s in (0 : ℝ)..t, b s (y s)) from intervalIntegral.integral_sub hxi hyi]
        abel
      rw [heq]
      calc ‖f t - g t + ∫ s in (0 : ℝ)..t, d s‖ ≤ ‖f t - g t‖ + ‖∫ s in (0 : ℝ)..t, d s‖ := norm_add_le _ _
        _ ≤ R + ∫ s in (0 : ℝ)..t, ‖d s‖ :=
          add_le_add (hforcing t ht) (intervalIntegral.norm_integral_le_integral_norm ht.1)
        _ ≤ R + ∫ s in (0 : ℝ)..t, (L : ℝ) * ‖x s - y s‖ := by
          apply add_le_add le_rfl
          exact intervalIntegral.integral_mono_on ht.1 hdt.norm
            ((hφ.const_mul _).intervalIntegrable _ _) (fun s hs ↦
              (hLip s ⟨hs.1, hs.2.trans ht.2⟩).norm_sub_le (x s) (y s))
        _ = _ := by rw [intervalIntegral.integral_const_mul]
    · have hyi : ¬IntervalIntegrable (fun s ↦ b s (y s)) volume 0 t := by
        intro hyi
        apply hxi
        have heq : (fun s ↦ b s (x s)) = (fun s ↦ b s (y s)) + d := by
          funext s
          simp only [Pi.add_apply, d]
          abel
        rw [heq]
        exact hyi.add hdt
      rw [heqx t ht, heqy t ht, intervalIntegral.integral_undef hxi,
        intervalIntegral.integral_undef hyi, add_zero, add_zero]
      exact (hforcing t ht).trans (le_add_of_nonneg_right (mul_nonneg L.coe_nonneg
        (intervalIntegral.integral_nonneg ht.1 (fun _ _ ↦ norm_nonneg _))))
  intro t ht
  have hh := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn L.coe_nonneg hineq t ht
  rw [sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left ht.2 L.coe_nonneg)) hR)


/-- Continuous paths solving an integral equation with a common spatially Lipschitz drift
and integrably bounded forcing admit an integrable bound uniform on a compact time interval.
Only time measurability of the drift integrands is assumed before deriving this bound. -/
theorem exists_integrable_uniform_bound_of_spatially_lipschitz_integral_eq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (b : ℝ → E → E) (L : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) (hLip : ∀ s ∈ Icc (0 : ℝ) T, LipschitzWith L (b s))
    (Y F : ℝ → Ω → E)
    (hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω))
    (hbm : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun s ↦ b s (Y s ω))
      (volume.restrict (Ioc (0 : ℝ) T)))
    (heq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, Y t ω = F t ω + ∫ s in (0 : ℝ)..t, b s (Y s ω))
    (B : Ω → ℝ) (hB : Integrable B P)
    (hFB : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖F t ω‖ ≤ B ω) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ D ω := by
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧
      AEStronglyMeasurable (fun s ↦ b s (Y s ω)) (volume.restrict (Ioc (0 : ℝ) T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, Y t ω = F t ω + ∫ s in (0 : ℝ)..t, b s (Y s ω)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖F t ω‖ ≤ B ω) := by
    filter_upwards [hYc, hbm, heq, hFB] with ω hc hm he hf using ⟨hc, hm, he, hf⟩
  obtain ⟨η, hη⟩ := hgood.exists
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun t ↦ Y t η) hη.1.continuousOn
  let D : Ω → ℝ := fun ω ↦ M + (B ω + B η) * Real.exp ((L : ℝ) * T)
  refine ⟨D, (integrable_const M).add ((hB.add (integrable_const (B η))).mul_const _), ?_⟩
  filter_upwards [hgood] with ω hω
  have hBω : 0 ≤ B ω := (norm_nonneg _).trans (hω.2.2.2 0 ⟨le_rfl, hT⟩)
  have hBη : 0 ≤ B η := (norm_nonneg _).trans (hη.2.2.2 0 ⟨le_rfl, hT⟩)
  have hforcing (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖F t ω - F t η‖ ≤ B ω + B η :=
    (norm_sub_le _ _).trans (add_le_add (hω.2.2.2 t ht) (hη.2.2.2 t ht))
  have hrel := norm_sub_le_of_spatially_lipschitz_integral_eq b L hT (add_nonneg hBω hBη) hLip
    (fun t ↦ Y t ω) (fun t ↦ Y t η) (fun t ↦ F t ω) (fun t ↦ F t η)
    hω.1 hη.1 hω.2.1 hη.2.1 hforcing hω.2.2.1 hη.2.2.1
  intro t ht
  calc ‖Y t ω‖ ≤ ‖Y t ω - Y t η‖ + ‖Y t η‖ := norm_le_norm_sub_add _ _
    _ ≤ (B ω + B η) * Real.exp ((L : ℝ) * T) + M := add_le_add (hrel t ht) (hM t ht)
    _ = D ω := by dsimp [D]; ring

end CKSD
