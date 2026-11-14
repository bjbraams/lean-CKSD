module
public import CKSD.Bayes.MeanFieldPicard
/-!
# Factorial contraction from time-integrated distance estimates

A Volterra estimate for an auxiliary time-dependent distance gives factorial bounds for the
iterates of a map. If the full metric distance is controlled by the same endpoint integral, some
iterate is a contraction on every bounded time interval. This is the abstract metric form of the
Picard iteration argument, using Mathlib factorial integration and convergence of powers over
factorials.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Function
open scoped Nat NNReal ENNReal Topology BigOperators
namespace CKSD
variable {X : Type*} [MetricSpace X]
/-- Iterated Volterra estimates give a factorial bound for a time-dependent distance. -/
theorem auxiliary_distance_iterate_le_pow_div_factorial
    (G : X → X) (q : X → X → ℝ → ℝ) {a T : ℝ} (ha : 0 ≤ a)
    (hq : ∀ x y, Continuous (q x y))
    (hbase : ∀ x y t, t ∈ Icc (0 : ℝ) T → q x y t ≤ dist x y)
    (hstep : ∀ x y t, t ∈ Icc (0 : ℝ) T →
      q (G x) (G y) t ≤ a * ∫ s in (0 : ℝ)..t, q x y s)
    (n : ℕ) (x y : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    q (G^[n] x) (G^[n] y) t ≤ (a * t)^n / n ! * dist x y := by
  induction n generalizing t with
  | zero => simpa using hbase x y t ht
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    calc _ ≤ a * ∫ s in (0 : ℝ)..t, q (G^[n] x) (G^[n] y) s := hstep _ _ t ht
      _ ≤ a * ∫ s in (0 : ℝ)..t, (a * s)^n / n ! * dist x y := by
        apply mul_le_mul_of_nonneg_left _ ha
        apply intervalIntegral.integral_mono_on ht.1 ((hq _ _).intervalIntegrable _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro s hs
        exact ih s ⟨hs.1, hs.2.trans ht.2⟩
      _ = _ := by
        have heq : (∫ s in (0 : ℝ)..t, (a*s)^n / n ! * dist x y) =
            a^n * dist x y / n ! * ∫ s in (0 : ℝ)..t, s^n := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          ext s
          rw [mul_pow]
          ring
        rw [heq, integral_pow, zero_pow n.succ_ne_zero, sub_zero, Nat.factorial_succ, mul_pow]
        push_cast
        field_simp
        ring
/-- The endpoint integral estimate turns the auxiliary factorial bound into a metric bound. -/
theorem dist_iterate_le_pow_div_factorial_of_integral_estimates
    (G : X → X) (q : X → X → ℝ → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hq : ∀ x y, Continuous (q x y))
    (hbase : ∀ x y t, t ∈ Icc (0 : ℝ) T → q x y t ≤ dist x y)
    (hstep : ∀ x y t, t ∈ Icc (0 : ℝ) T →
      q (G x) (G y) t ≤ a * ∫ s in (0 : ℝ)..t, q x y s)
    (hdist : ∀ x y, dist (G x) (G y) ≤ a * ∫ s in (0 : ℝ)..T, q x y s)
    (n : ℕ) (x y : X) :
    dist (G^[n] x) (G^[n] y) ≤ (a * T)^n / n ! * dist x y := by
  cases n with
  | zero => simp
  | succ n =>
    rw [iterate_succ_apply', iterate_succ_apply']
    calc _ ≤ a * ∫ s in (0 : ℝ)..T, q (G^[n] x) (G^[n] y) s := hdist _ _
      _ ≤ a * ∫ s in (0 : ℝ)..T, (a*s)^n / n ! * dist x y := by
        apply mul_le_mul_of_nonneg_left _ ha
        apply intervalIntegral.integral_mono_on hT ((hq _ _).intervalIntegrable _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        intro s hs
        exact auxiliary_distance_iterate_le_pow_div_factorial G q ha hq hbase hstep n x y s hs
      _ = _ := by
        have heq : (∫ s in (0 : ℝ)..T, (a*s)^n / n ! * dist x y) =
            a^n * dist x y / n ! * ∫ s in (0 : ℝ)..T, s^n := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          ext s
          rw [mul_pow]
          ring
        rw [heq, integral_pow, zero_pow n.succ_ne_zero, sub_zero, Nat.factorial_succ, mul_pow]
        push_cast
        field_simp
        ring
/-- A Volterra estimate yields a contracting iterate on every finite time interval. -/
theorem exists_contractingWith_iterate_of_integral_estimates
    (G : X → X) (q : X → X → ℝ → ℝ) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hq : ∀ x y, Continuous (q x y))
    (hbase : ∀ x y t, t ∈ Icc (0 : ℝ) T → q x y t ≤ dist x y)
    (hstep : ∀ x y t, t ∈ Icc (0 : ℝ) T →
      q (G x) (G y) t ≤ a * ∫ s in (0 : ℝ)..t, q x y s)
    (hdist : ∀ x y, dist (G x) (G y) ≤ a * ∫ s in (0 : ℝ)..T, q x y s) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C G^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (a*T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h0 : 0 ≤ (a*T)^n / n ! := by positivity
  refine ⟨n, ⟨_, h0⟩, hn, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  exact dist_iterate_le_pow_div_factorial_of_integral_estimates G q ha hT hq hbase hstep hdist n x y
end CKSD
