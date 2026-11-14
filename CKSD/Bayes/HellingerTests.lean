module

public import CKSD.Bayes.HellingerGeometry
public import TauCeti.Probability.Moments.Bernstein

/-!
# Robust Hellinger tests

For dominated probability laws `P` and `Q` with positive Hellinger distance `h`, the bounded score
`(√q - √p)/(√q + √p)` gives an `n`-sample test of `P` against every dominated law in the
Hellinger ball of radius `h/8` around `Q`. Both errors are at most `exp (-n h² / 256)`.

The mean and second-moment estimates are proved in `CKSD.Bayes.HellingerGeometry`.
Mathlib supplies the independence of product coordinates, and TauCeti supplies Bernstein's
inequality `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_of_ae_le`.

## Main results

* `CKSD.exists_hellinger_ball_test`: a test uniform over the whole Hellinger ball.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- A Bernstein bound for an iid bounded score with second moment at most `3h²`. -/
theorem measureReal_centered_hellingerScore_sum_ge_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (g : X → ℝ) (hg : Measurable g)
    (hgb : ∀ x, |g x| ≤ 1) (h : ℝ) (hh : 0 < h)
    (hsecond : ∫ x, g x ^ 2 ∂P ≤ 3 * h ^ 2) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ P).real
      {x | (n : ℝ) * h ^ 2 / 5 ≤ ∑ i, (g (x i) - ∫ z, g z ∂P)} ≤
      Real.exp (-((n : ℝ) * h ^ 2 / 256)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  let ν := Measure.pi fun _ : Fin n ↦ P
  let m := ∫ x, g x ∂P
  have hgmem : MemLp g 2 P := MemLp.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hgb x)
  have hgm : |m| ≤ 1 := by
    simpa [m, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
      (μ := P) (f := g) (C := (1 : ℝ)) (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hgb x)
  have hYmeas : Measurable fun x ↦ g x - m := hg.sub_const m
  have hYb : ∀ x, |g x - m| ≤ 2 := fun x ↦ (abs_sub _ _).trans (by linarith [hgb x])
  have hYmem : MemLp (fun x ↦ g x - m) 2 P := hgmem.sub (memLp_const m)
  have hmean : ∫ x, (g x - m) ∂P = 0 := by
    rw [integral_sub (hgmem.integrable (by norm_num)) (integrable_const _)]
    simp [m]
  let Y : Fin n → (Fin n → X) → ℝ := fun i x ↦ g (x i) - m
  have hYcoord (i : Fin n) : MemLp (Y i) 2 ν :=
    hYmem.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ P) i)
  have hInt (i : Fin n) (F : X → ℝ) (hF : Measurable F) :
      ∫ x : Fin n → X, F (x i) ∂ν = ∫ x, F x ∂P := by
    have hi := integral_map (measurePreserving_eval (fun _ : Fin n ↦ P) i).aemeasurable
      (f := F) (by rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq]; exact hF.aestronglyMeasurable)
    rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq] at hi
    exact hi.symm
  have hYmean (i : Fin n) : ∫ x, Y i x ∂ν = 0 := by
    rw [hInt i _ hYmeas, hmean]
  have hYsecond (i : Fin n) : ∫ x, Y i x ^ 2 ∂ν = variance g P := by
    rw [hInt i _ (hYmeas.pow_const 2)]
    exact (variance_eq_integral hg.aemeasurable).symm
  have hind : iIndepFun Y ν := iIndepFun_pi (fun _ : Fin n ↦ hYmeas.aemeasurable)
  have hbern := hind.measureReal_sum_ge_le_of_ae_le (s := Finset.univ) (b := 2)
    (fun i _ ↦ hYcoord i) (fun i _ ↦ hYmean i)
    (fun i _ ↦ ae_of_all _ fun x ↦ (le_abs_self _).trans (hYb (x i)))
    (ε := (n : ℝ) * h ^ 2 / 5) (by positivity)
  have hvariance : variance g P ≤ 3 * h ^ 2 :=
    (variance_le_expectation_sq hg.aestronglyMeasurable).trans hsecond
  simp_rw [hYsecond] at hbern
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbern
  refine hbern.trans ?_
  apply Real.exp_le_exp.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 2 * ((n : ℝ) * variance g P + 2 * (n * h ^ 2 / 5) / 3) := by
    have hv := variance_nonneg g P
    positivity
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden]
  have hvn : (n : ℝ) * variance g P ≤ n * (3 * h ^ 2) := mul_le_mul_of_nonneg_left hvariance hn0.le
  have hnh : 0 < (n : ℝ) * h ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hvn hnh.le, sq_nonneg ((n : ℝ) * h ^ 2)]

/-- Exponentially accurate tests of a law against a Hellinger ball around an alternative.
The score test is uniform over all dominated laws in the ball of radius `h(P,Q)/8`. -/
theorem exists_hellinger_ball_test {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p q : X → ℝ) (hP : HasDensity P μ p) (hQ : HasDensity Q μ q)
    (hpos : 0 < statisticalHellingerDistance P Q) (n : ℕ) :
    ∃ ψ : (Fin n → X) → ℝ, IsStatisticalTest ψ ∧
      (∫ x, ψ x ∂(Measure.pi fun _ : Fin n ↦ P)) ≤
        Real.exp (-((n : ℝ) * statisticalHellingerDistance P Q ^ 2 / 256)) ∧
      ∀ (R : Measure X) (r : X → ℝ), IsProbabilityMeasure R → HasDensity R μ r →
        statisticalHellingerDistance R Q ≤ statisticalHellingerDistance P Q / 8 →
          (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ R)) ≤
            Real.exp (-((n : ℝ) * statisticalHellingerDistance P Q ^ 2 / 256)) := by
  let h := statisticalHellingerDistance P Q
  let T := hellingerScore p q
  let mP := ∫ x, T x ∂P
  let mQ := ∫ x, T x ∂Q
  let A : Set (Fin n → X) := {x | (n : ℝ) * (mP + h ^ 2 / 2) ≤ ∑ i, T (x i)}
  have hTm : Measurable T := measurable_hellingerScore hP.1 hQ.1
  have hTb : ∀ x, |T x| ≤ 1 := abs_hellingerScore_le_one p q
  have hAm : MeasurableSet A := measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ ↦ hTm.comp (measurable_pi_apply i))
  have hmean : mQ - mP = h ^ 2 := integral_hellingerScore_sub_eq hP hQ
  have hsecondQ : ∫ x, T x ^ 2 ∂Q ≤ h ^ 2 := integral_hellingerScore_sq_le hP hQ
  have hsecondP : ∫ x, T x ^ 2 ∂P ≤ h ^ 2 := by
    have hv := integral_hellingerScore_sq_le hQ hP
    rw [hellingerScore_swap] at hv
    simp only [neg_sq] at hv
    simpa only [T, h, statisticalHellingerDistance, ProbabilityTheory.sqHellinger_comm Q P] using hv
  refine ⟨A.indicator 1, ⟨measurable_one.indicator hAm, fun x ↦ ?_⟩, ?_, ?_⟩
  · by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  · rw [integral_indicator_one hAm]
    refine (measureReal_mono (μ := Measure.pi fun _ : Fin n ↦ P) (s₁ := A) (s₂ := {x | (n : ℝ) * h ^ 2 / 5 ≤
      ∑ i, (T (x i) - ∫ z, T z ∂P)}) ?_).trans ?_
    · intro x hx
      change (n : ℝ) * (mP + h ^ 2 / 2) ≤ ∑ i, T (x i) at hx
      simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      change (n : ℝ) * h ^ 2 / 5 ≤ (∑ i, T (x i)) - n * mP
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg h)]
    · exact measureReal_centered_hellingerScore_sum_ge_le P T hTm hTb h hpos
        (by nlinarith [sq_nonneg h]) n
  intro R r hRprob hR hclose
  let : IsProbabilityMeasure R := hRprob
  let ρ := statisticalHellingerDistance R Q
  let mR := ∫ x, T x ∂R
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ : ρ ≤ h / 8 := hclose
  have hρ2 : ρ ^ 2 ≤ h ^ 2 / 64 := by
    have hsq := mul_self_le_mul_self hρ0 hρ
    nlinarith
  have hμdiff := abs_integral_sub_le_hellinger hQ hR T hTm hTb hpos.le hsecondQ
  have hcross : 2 * ρ * h ≤ h ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_right hρ hpos.le
    nlinarith
  have hmeanR : mP + 7 / 10 * h ^ 2 ≤ mR := by
    have hl := neg_abs_le (mR - mQ)
    change |mR - mQ| ≤ 2 * ρ * h + ρ ^ 2 at hμdiff
    nlinarith [sq_nonneg h]
  have hsecondR : ∫ x, T x ^ 2 ∂R ≤ 3 * h ^ 2 := by
    have hv := integral_sq_le_of_hellinger hQ hR T hTm hTb
    nlinarith [sq_nonneg h]
  rw [integral_sub (f := fun _ : Fin n → X ↦ (1 : ℝ)) (g := A.indicator 1)
      (integrable_const _) (Integrable.indicator (f := (1 : (Fin n → X) → ℝ)) (integrable_const _) hAm),
    integral_const, probReal_univ, smul_eq_mul, mul_one, integral_indicator_one hAm,
    ← probReal_compl_eq_one_sub hAm]
  refine (measureReal_mono (μ := Measure.pi fun _ : Fin n ↦ R) (s₁ := Aᶜ) (s₂ := {x | (n : ℝ) * h ^ 2 / 5 ≤
    ∑ i, (-T (x i) - ∫ z, -T z ∂R)}) ?_).trans ?_
  · intro x hx
    simp only [Set.mem_compl_iff, A, Set.mem_ofPred_eq, not_le] at hx
    simp only [Set.mem_ofPred_eq, integral_neg, sub_neg_eq_add, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (n : ℝ) * h ^ 2 / 5 ≤ -(∑ i, T (x i)) + n * mR
    have := mul_le_mul_of_nonneg_left hmeanR (Nat.cast_nonneg n)
    nlinarith
  · exact measureReal_centered_hellingerScore_sum_ge_le R (fun x ↦ -T x) hTm.neg
      (fun x ↦ by simpa only [abs_neg] using hTb x) h hpos
      (by simpa only [neg_sq] using hsecondR) n

end CKSD
