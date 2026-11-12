module
public import CKSD.Bayes.ParticleSamplingMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
/-!
# Uniform real-order moments of iid empirical averages

A bounded iid empirical average has `Lᵖ` error at most a constant depending on the real order
`p ≥ 1`, times its absolute bound divided by square-root sample size. The zero-bound case is
included. The proof rescales the centered sum to the local sub-Gaussian moment theorem and
uses Mathlib's real-valued `lpNorm` identities.

This supplies the independent-sampling estimate of Del Moral, *Feynman–Kac Formulae*,
Lemma 7.3.3, printed pages 223–225 (PDF pages 236–238 of the local 2004 copy), with a coarse
explicit exponential-moment constant valid at arbitrary real order.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators Nat
namespace CKSD
/-- Real-power moments are the real-valued finite-exponent `Lᵖ` norm. -/
theorem lpNorm_ofReal_eq_integral_abs_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    lpNorm f (ENNReal.ofReal p) P = (∫ ω, |f ω|^p ∂P)^(1/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs,one_div]

/-- Bounded iid empirical averages have a uniform `Lᵖ` error of order the inverse square root
of sample size; the constant depends only on the real moment order. -/
theorem exists_iid_empirical_mean_lpNorm_bound
    {X : Type*} [MeasurableSpace X] [Nonempty X] (p : ℝ) (hp : 1 ≤ p) :
    ∃ K > 0, ∀ (ν : Measure X), IsProbabilityMeasure ν → ∀ {N : ℕ}, 0 < N →
      ∀ {f : X → ℝ}, Measurable f → ∀ {B : ℝ}, 0 ≤ B → (∀ x, |f x| ≤ B) →
        lpNorm (fun z : Fin N → X ↦ (∑ i, f (z i))/(N:ℝ)-∫ x,f x ∂ν)
          (ENNReal.ofReal p) (Measure.pi (fun _ : Fin N ↦ ν)) ≤ K*B/Real.sqrt N := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨m,hm⟩ := exists_nat_ge p
  let D : ℝ := 1+2*(m !:ℝ)*Real.exp (1/2)
  let K : ℝ := 2*D^(1/p)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K,by dsimp [K]; positivity,fun ν hν N hN f hf B hB hfb ↦ ?_⟩
  let _ : IsProbabilityMeasure ν := hν
  let π := Measure.pi (fun _ : Fin N ↦ ν)
  obtain hB0 | hB0 := eq_or_lt_of_le hB
  · have hf0 : f=fun _ ↦ 0 := by
      funext x
      apply abs_nonpos_iff.1
      simpa only [← hB0] using hfb x
    simp only [hf0,Finset.sum_const_zero,zero_div,integral_zero,sub_zero,lpNorm_fun_zero,
      ← hB0,mul_zero,zero_div,le_rfl]
  · let A : ℝ := 2*B
    let Y : (Fin N → X) → ℝ := fun z ↦ (A*Real.sqrt N)⁻¹ * ∑ i,(f (z i)-∫ x,f x ∂ν)
    have hA : 0 < A := by dsimp [A]; positivity
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (Nat.cast_pos.2 hN)
    have hsg : HasSubgaussianMGF Y 1 π :=
      hasSubgaussianMGF_normalized_iid_sum ν hN f hf hA (fun x y ↦ by
        exact (abs_sub _ _).trans (by dsimp [A]; linarith [hfb x,hfb y]))
    have hYm : Measurable Y := by
      exact measurable_const.mul (Finset.measurable_fun_sum _ fun i _ ↦
        (hf.comp (measurable_pi_apply i)).sub measurable_const)
    have hYmoment : (∫ z, |Y z|^p ∂π) ≤ D :=
      integral_abs_rpow_le_of_hasSubgaussianMGF_one π Y hsg hp0.le hm
    have hYnorm : lpNorm Y (ENNReal.ofReal p) π ≤ D^(1/p) := by
      rw [lpNorm_ofReal_eq_integral_abs_rpow π hp0 hYm.aestronglyMeasurable]
      exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
        hYmoment (by positivity)
    have hscale : (A/Real.sqrt N)*(A*Real.sqrt N)⁻¹ = 1/(N:ℝ) := by
      have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
      field_simp [hA.ne',hs.ne']
      nlinarith
    have heq : (fun z : Fin N → X ↦ (∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂ν) =
        (A/Real.sqrt N) • Y := by
      funext z
      change (∑ i,f (z i))/(N:ℝ)-(∫ x,f x ∂ν) =
        (A/Real.sqrt N)*((A*Real.sqrt N)⁻¹ * ∑ i,(f (z i)-∫ x,f x ∂ν))
      rw [← mul_assoc,hscale,Finset.sum_sub_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.2 hN.ne']
    rw [heq,lpNorm_const_smul]
    have hc : 0 ≤ A/Real.sqrt N := (div_pos hA hs).le
    have hcnorm : (‖A/Real.sqrt N‖₊:ℝ) = A/Real.sqrt N := by
      rw [coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg hc]
    rw [hcnorm]
    calc (A/Real.sqrt N)*lpNorm Y (ENNReal.ofReal p) π ≤ (A/Real.sqrt N)*D^(1/p) :=
          mul_le_mul_of_nonneg_left hYnorm hc
      _ = K*B/Real.sqrt N := by dsimp [K,A]; ring

end CKSD
