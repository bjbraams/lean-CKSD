module
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-!
# Gamma quotients along positive real arguments

Log-convexity and the Gamma recurrence squeeze a fixed positive logarithmic Gamma increment
between finite sums of `log (1 + c/x)`. This gives the power asymptotic for arbitrary positive
real arguments, as needed for Beta distribution limits with growing shape parameters.

The proof uses Mathlib's log-convexity and recurrence, without a Stirling expansion.
-/

@[expose] public section
noncomputable section
open Filter Set Real
open scoped Topology BigOperators
namespace CKSD

/-- The logarithmic Gamma increment is asymptotic to the shift times the logarithm. -/
theorem tendsto_log_Gamma_add_sub_log_Gamma_sub_mul_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ Real.log (Real.Gamma (x + b)) - Real.log (Real.Gamma x) - b * Real.log x)
      atTop (𝓝 0) := by
  obtain ⟨N, hNb⟩ := exists_nat_gt b
  have hN : 0 < N := by exact_mod_cast (hb.trans hNb)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let θ := b / N
  have hθ0 : 0 ≤ θ := (div_pos hb hNR).le
  have hθ1 : θ ≤ 1 := (div_le_one hNR).2 hNb.le
  let F : ℝ → ℝ := fun x ↦ Real.log (Real.Gamma x)
  have hFadd {x : ℝ} (hx : 0 < x) : F (x + 1) = F x + Real.log x := by
    dsimp only [F]
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
    ring
  have hFNat {x : ℝ} (hx : 0 < x) : F (x + N) = F x + ∑ k ∈ Finset.range N, Real.log (x + k) :=
    Real.BohrMollerup.f_add_nat_eq (fun {_} hy ↦ hFadd hy) hx N
  let S : ℝ → ℝ → ℝ := fun x c ↦ ∑ k ∈ Finset.range N, Real.log (1 + (c + k) / x)
  have hsum (x c : ℝ) (hx : 0 < x) (hc : 0 ≤ c) :
      (∑ k ∈ Finset.range N, Real.log (x + c + k)) = N * Real.log x + S x c := by
    have hp (k : ℕ) : Real.log (x + c + k) = Real.log x + Real.log (1 + (c + k) / x) := by
      rw [← Real.log_mul hx.ne' (by have := Nat.cast_nonneg (α := ℝ) k; positivity)]
      congr 1
      field_simp
      ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, S]
  have hbds (x : ℝ) (hx : 0 < x) :
      S x 0 - (1 - θ) * S x b ≤ F (x + b) - F x - b * Real.log x ∧
      F (x + b) - F x - b * Real.log x ≤ θ * S x 0 := by
    have hu := Real.convexOn_log_Gamma.2 hx (show (0 : ℝ) < x + N by positivity)
      (sub_nonneg.2 hθ1) hθ0 (sub_add_cancel 1 θ)
    have he1 : (1 - θ) * x + θ * (x + N) = x + b := by dsimp [θ]; field_simp; ring
    simp only [Function.comp_apply, smul_eq_mul, he1] at hu
    change F (x + b) ≤ (1 - θ) * F x + θ * F (x + N) at hu
    rw [hFNat hx] at hu
    have hsum0 := hsum x 0 hx (le_refl 0)
    simp only [add_zero] at hsum0
    rw [hsum0] at hu
    have hl := Real.convexOn_log_Gamma.2 (show (0 : ℝ) < x + b by positivity)
      (show (0 : ℝ) < x + b + N by positivity) hθ0 (sub_nonneg.2 hθ1) (add_sub_cancel θ 1)
    have he2 : θ * (x + b) + (1 - θ) * (x + b + N) = x + N := by dsimp [θ]; field_simp; ring
    simp only [Function.comp_apply, smul_eq_mul, he2] at hl
    change F (x + N) ≤ θ * F (x + b) + (1 - θ) * F (x + b + N) at hl
    rw [hFNat hx, hFNat (show 0 < x + b by positivity), hsum0, hsum x b hx hb.le] at hl
    have hθN : θ * N = b := by dsimp [θ]; field_simp
    have hθlog : θ * N * Real.log x = b * Real.log x := by rw [hθN]
    constructor <;> nlinarith [hθlog]
  have hSlim (c : ℝ) : Tendsto (fun x : ℝ ↦ S x c) atTop (𝓝 0) := by
    have hterm (k : ℕ) : Tendsto (fun x : ℝ ↦ Real.log (1 + (c + k) / x)) atTop (𝓝 0) := by
      have hi : Tendsto (fun x : ℝ ↦ 1 + (c + k) / x) atTop (𝓝 1) := by
        simpa only [mul_zero, add_zero, div_eq_mul_inv] using
          tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul (c + k))
      simpa only [Real.log_one, Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hi
    simpa only [S, Finset.sum_const_zero] using tendsto_finsetSum (Finset.range N) (fun k _ ↦ hterm k)
  have hlo := (hSlim 0).sub ((hSlim b).const_mul (1 - θ))
  have hup := (hSlim 0).const_mul θ
  simp only [mul_zero, sub_zero] at hlo hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (hbds x hx).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (hbds x hx).2

/-- The Gamma ratio has its standard power asymptotic along arbitrary positive real arguments. -/
theorem tendsto_Gamma_add_div_mul_rpow {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ Real.Gamma (x + b) / (Real.Gamma x * x ^ b)) atTop (𝓝 1) := by
  have h := Real.continuous_exp.tendsto 0 |>.comp (tendsto_log_Gamma_add_sub_log_Gamma_sub_mul_log hb)
  simp only [Real.exp_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log (Real.Gamma_pos_of_pos (add_pos hx hb)),
    Real.exp_log (Real.Gamma_pos_of_pos hx), Real.rpow_def_of_pos hx]
  rw [mul_comm b (Real.log x)]
  ring

end CKSD
