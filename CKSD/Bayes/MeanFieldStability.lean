module
public import CKSD.Bayes.MeanFieldPicard
/-!
# Stability under time-dependent perturbations of a Lipschitz drift

Solutions driven by the same continuous forcing differ by at most the time-integrated drift
perturbation multiplied by the spatial Grönwall factor. The estimate uses Mathlib interval
integration and TauCeti's integral Grönwall theorem.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Function
open scoped NNReal ENNReal Topology
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Stability under a time-dependent perturbation of the drift and a common additive forcing. -/
theorem norm_sub_le_exp_mul_integral_of_forced_eq
    {T : ℝ} (v w : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) (hw : Continuous (Function.uncurry w))
    {K : ℝ≥0} (hvK : ∀ s, LipschitzWith K (v s))
    (a : ℝ → ℝ) (ha : Continuous a) (ha0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s)
    (hvw : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, ‖v s z - w s z‖ ≤ a s)
    (x y F : ℝ → E) (hx : Continuous x) (hy : Continuous y)
    (hxe : ∀ t ∈ Icc (0 : ℝ) T, x t = F t + ∫ s in (0 : ℝ)..t, v s (x s))
    (hye : ∀ t ∈ Icc (0 : ℝ) T, y t = F t + ∫ s in (0 : ℝ)..t, w s (y s)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤
      Real.exp ((K : ℝ) * T) * ∫ s in (0 : ℝ)..t, a s := by
  have hφ : Continuous (fun t ↦ ‖x t - y t‖) := (hx.sub hy).norm
  have hvx : Continuous (fun s ↦ v s (x s)) := hv.comp (continuous_id.prodMk hx)
  have hwy : Continuous (fun s ↦ w s (y s)) := hw.comp (continuous_id.prodMk hy)
  have hine (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖x s - y s‖ ≤ (∫ r in (0 : ℝ)..s, a r) +
        (K : ℝ) * ∫ r in (0 : ℝ)..s, ‖x r - y r‖ := by
    have heq : x s - y s = ∫ r in (0 : ℝ)..s, v r (x r) - w r (y r) := by
      rw [hxe s hs, hye s hs, add_sub_add_left_eq_sub,
        intervalIntegral.integral_sub (μ := volume) (hvx.intervalIntegrable _ _)
          (hwy.intervalIntegrable _ _)]
    rw [heq]
    calc _ ≤ ∫ r in (0 : ℝ)..s, ‖v r (x r) - w r (y r)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ ∫ r in (0 : ℝ)..s, a r + (K : ℝ) * ‖x r - y r‖ := by
        apply intervalIntegral.integral_mono_on hs.1
          ((hvx.sub hwy).norm.intervalIntegrable _ _)
          ((ha.add (hφ.const_mul _)).intervalIntegrable _ _)
        intro r hr
        have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hs.2⟩
        calc ‖v r (x r) - w r (y r)‖ ≤
              ‖v r (x r) - v r (y r)‖ + ‖v r (y r) - w r (y r)‖ := by simpa only [dist_eq_norm] using dist_triangle (v r (x r)) (v r (y r)) (w r (y r))
          _ ≤ (K : ℝ) * ‖x r - y r‖ + a r :=
            add_le_add ((hvK r).norm_sub_le _ _) (hvw r hrT (y r))
          _ = _ := add_comm _ _
      _ = _ := by
        rw [intervalIntegral.integral_add (ha.intervalIntegrable _ _)
          ((hφ.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  intro t ht
  let A := ∫ s in (0 : ℝ)..t, a s
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg ht.1
    (fun s hs ↦ ha0 s ⟨hs.1, hs.2.trans ht.2⟩)
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      ‖x s - y s‖ ≤ A + (K : ℝ) * ∫ r in (0 : ℝ)..s, ‖x r - y r‖ := by
    apply (hine s ⟨hs.1, hs.2.trans ht.2⟩).trans
    apply add_le_add_left
    apply intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) hs.1 hs.2
      _ (ha.intervalIntegrable _ _)
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun r hr ↦
      ha0 r ⟨hr.1.le, hr.2.trans ht.2⟩)
  have hgr := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn K.coe_nonneg hi t ⟨ht.1, le_rfl⟩
  simp only [sub_zero] at hgr
  calc _ ≤ A * Real.exp ((K : ℝ) * t) := hgr
    _ ≤ A * Real.exp ((K : ℝ) * T) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) hA
    _ = _ := mul_comm _ _
end CKSD
