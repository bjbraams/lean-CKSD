module

public import CKSD.Learning.Generalization.Concentration

/-!
# Exponential weights for bounded losses

Hoeffding's lemma for finite probability vectors and the regret guarantee for the
exponential-weights (Hedge) forecaster.

## Main results

* `CKSD.sum_mul_exp_le`: Hoeffding's lemma for a finite probability vector.
* `CKSD.hedge_regret_le`: the Hedge regret bound `log K / η + η T / 8` (GAPS 107.5).
* `CKSD.sum_sum_mul_sub_le_of_exponential_weights`: the second-order regret bound for
  exponential weights with nonnegative (estimated) losses, used for Exp3.
* `CKSD.exponentialWeights_succ`: the multiplicative update form of exponential weights.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Integrals against a finite weighted sum of Dirac masses on `Fin K`. -/
theorem integral_finiteDiracSum {K : ℕ} (p : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (g : Fin K → ℝ) :
    ∫ x, g x ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac j) = ∑ j, p j * g j := by
  rw [integral_finsetSum_measure (fun j _ ↦
    (Integrable.of_finite (μ := Measure.dirac j)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp j), smul_eq_mul]

/-- Hoeffding's lemma for a finite probability vector and values in `[0,1]`, from Mathlib's
`hasSubgaussianMGF_of_mem_Icc`. -/
theorem sum_mul_exp_le {K : ℕ} (p ℓ : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hℓ : ∀ j, ℓ j ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    ∑ j, p j * Real.exp (t * ℓ j) ≤ Real.exp (t * ∑ j, p j * ℓ j + t ^ 2 / 8) := by
  set μ : Measure (Fin K) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac j
  have hμ1 : μ Set.univ = 1 := by
    simp only [μ, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hp j, hp1, ENNReal.ofReal_one]
  have : IsProbabilityMeasure μ := ⟨hμ1⟩
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := 0) (b := 1)
    (measurable_of_finite ℓ).aemeasurable (ae_of_all _ hℓ)
  have hm := hs.mgf_le t
  have hmean : μ[ℓ] = ∑ j, p j * ℓ j := integral_finiteDiracSum p hp ℓ
  rw [mgf, integral_finiteDiracSum p hp, hmean] at hm
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 / 4 : ℝ≥0) := by
    norm_num
  rw [hc] at hm
  have hpt : ∀ j, Real.exp (t * ℓ j) =
      Real.exp (t * (ℓ j - ∑ i, p i * ℓ i)) * Real.exp (t * ∑ i, p i * ℓ i) := by
    intro j; rw [← Real.exp_add]; ring_nf
  calc ∑ j, p j * Real.exp (t * ℓ j)
      = (∑ j, p j * Real.exp (t * (ℓ j - ∑ i, p i * ℓ i))) * Real.exp (t * ∑ i, p i * ℓ i) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [hpt]; ring
    _ ≤ Real.exp ((1 / 4 : ℝ≥0) * t ^ 2 / 2) * Real.exp (t * ∑ i, p i * ℓ i) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- GAPS 107.5: the exponential-weights regret bound, for any positive learning rate. For losses
`ℓₜ(i) ∈ [0,1]` on `K ≥ 1` experts, the Hedge forecaster with learning rate `η > 0` has
cumulative expected loss at most that of any fixed expert `i` plus `log K / η + η T / 8`. -/
theorem hedge_regret_le {K : ℕ} (hK : 0 < K) (loss : ℕ → Fin K → ℝ)
    (hloss : ∀ t i, loss t i ∈ Icc 0 1) (eta : ℝ) (he : 0 < eta)
    (T : ℕ) (i : Fin K) :
    (∑ t ∈ Finset.range T, ∑ j, hedgeWeight loss eta t j * loss t j) -
      (∑ t ∈ Finset.range T, loss t i) ≤ Real.log K / eta + eta * T / 8 := by
  set L : ℕ → Fin K → ℝ := fun t j ↦ ∑ s ∈ Finset.range t, loss s j
  set W : ℕ → ℝ := fun t ↦ ∑ j, Real.exp (-eta * L t j)
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hW : ∀ t, 0 < W t := fun t ↦ Finset.sum_pos (fun j _ ↦ Real.exp_pos _) hne
  have hp : ∀ t j, hedgeWeight loss eta t j = Real.exp (-eta * L t j) / W t := fun _ _ ↦ rfl
  have hp0 : ∀ t j, 0 ≤ hedgeWeight loss eta t j := fun t j ↦ by
    rw [hp]; exact div_nonneg (Real.exp_pos _).le (hW t).le
  have hp1 : ∀ t, ∑ j, hedgeWeight loss eta t j = 1 := fun t ↦ by
    simp_rw [hp]; rw [← Finset.sum_div, div_self (hW t).ne']
  have hstep : ∀ t, Real.log (W (t + 1)) ≤ Real.log (W t) -
      eta * (∑ j, hedgeWeight loss eta t j * loss t j) + eta ^ 2 / 8 := by
    intro t
    have hWt : W (t + 1) = W t * ∑ j, hedgeWeight loss eta t j * Real.exp (-eta * loss t j) := by
      have hWt0 := (hW t).ne'
      conv_lhs => simp only [W]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hp]
      have hL : L (t + 1) j = L t j + loss t j := Finset.sum_range_succ _ _
      rw [hL, mul_add, Real.exp_add]
      field_simp
    have hb := sum_mul_exp_le (fun j ↦ hedgeWeight loss eta t j) (loss t) (hp0 t) (hp1 t)
      (hloss t) (-eta)
    have hpos : 0 < ∑ j, hedgeWeight loss eta t j * Real.exp (-eta * loss t j) := by
      have := hW (t + 1); rw [hWt] at this; exact pos_of_mul_pos_right this (hW t).le
    rw [hWt, Real.log_mul (hW t).ne' hpos.ne']
    have := Real.log_le_log hpos hb
    rw [Real.log_exp] at this
    nlinarith
  have hind : ∀ n, Real.log (W n) ≤ Real.log K -
      eta * (∑ t ∈ Finset.range n, ∑ j, hedgeWeight loss eta t j * loss t j) + n * eta ^ 2 / 8 := by
    intro n
    induction n with
    | zero => simp [W, L]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      push_cast
      nlinarith
  have hlow : -eta * L T i ≤ Real.log (W T) := by
    rw [← Real.log_exp (-eta * L T i)]
    exact Real.log_le_log (Real.exp_pos _)
      (Finset.single_le_sum (f := fun j ↦ Real.exp (-eta * L T j))
        (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i))
  have h := (hlow.trans (hind T))
  have hfinal : eta * ((∑ t ∈ Finset.range T, ∑ j, hedgeWeight loss eta t j * loss t j) -
      (∑ t ∈ Finset.range T, loss t i)) ≤ eta * (Real.log K / eta + eta * T / 8) := by
    rw [mul_add, mul_div_cancel₀ _ he.ne']
    simp only [L] at h
    nlinarith
  exact le_of_mul_le_mul_left hfinal he

/-- Second-order bound `exp(-x) ≤ 1 - x + x²/2` for `x ≥ 0`. -/
private theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  set g : ℝ → ℝ := fun y ↦ 1 - y + y ^ 2 / 2 - Real.exp (-y) with hg
  have hd : ∀ y, HasDerivAt g (-1 + y + Real.exp (-y)) y := by
    intro y
    have h := (((hasDerivAt_id y).const_sub 1).add ((hasDerivAt_pow 2 y).div_const 2)).sub
      (hasDerivAt_neg y).exp
    convert h using 1
    · funext z; simp only [hg, Pi.add_apply, Pi.sub_apply, id]
    · simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun y ↦ (hd y).continuousAt
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
      (fun y _ ↦ (hd y).differentiableAt.differentiableWithinAt) fun y _ ↦ ?_
    rw [(hd y).deriv]
    linarith [Real.add_one_le_exp (-y)]
  have := hmono (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hx hx
  simp only [hg, neg_zero, Real.exp_zero] at this
  linarith

/-- Deterministic exponential-weights bound with nonnegative estimated losses `ℓ̂`: if
`p t i ∝ exp(-η ∑_{s<t} ℓ̂ s i)`, then
`∑_{t<T} ∑ᵢ p t i ℓ̂ t i - ∑_{t<T} ℓ̂ t i⋆ ≤ log K / η + (η/2) ∑_{t<T} ∑ᵢ p t i ℓ̂ t i²`. -/
theorem sum_sum_mul_sub_le_of_exponential_weights {K : ℕ} (hK : 0 < K) {η : ℝ} (hη : 0 < η)
    (lh : ℕ → Fin K → ℝ) (hlh : ∀ t i, 0 ≤ lh t i) (p : ℕ → Fin K → ℝ)
    (hp : ∀ t i, p t i = Real.exp (-η * ∑ s ∈ Finset.range t, lh s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j)) (T : ℕ) (istar : Fin K) :
    ∑ t ∈ Finset.range T, ∑ i, p t i * lh t i - ∑ t ∈ Finset.range T, lh t istar ≤
      Real.log K / η + η / 2 * ∑ t ∈ Finset.range T, ∑ i, p t i * lh t i ^ 2 := by
  set W : ℕ → ℝ := fun t ↦ ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j) with hW
  have hWpos : ∀ t, 0 < W t := fun t ↦
    Finset.sum_pos (fun j _ ↦ Real.exp_pos _) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hpsum : ∀ t, ∑ i, p t i = 1 := fun t ↦ by
    simp only [hp, ← Finset.sum_div]
    exact div_self (hWpos t).ne'
  have hppos : ∀ t i, 0 < p t i := fun t i ↦ by
    rw [hp]; exact div_pos (Real.exp_pos _) (hWpos t)
  have hpnn : ∀ t i, 0 ≤ p t i := fun t i ↦ (hppos t i).le
  have hratio : ∀ t, W (t + 1) = W t * ∑ i, p t i * Real.exp (-η * lh t i) := by
    intro t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hp, Finset.sum_range_succ, mul_add, Real.exp_add]
    have := (hWpos t).ne'
    simp only [hW] at this ⊢
    field_simp
  have hstep : ∀ t, Real.log (W (t + 1)) - Real.log (W t) ≤
      -η * ∑ i, p t i * lh t i + η ^ 2 / 2 * ∑ i, p t i * lh t i ^ 2 := by
    intro t
    have hZpos : 0 < ∑ i, p t i * Real.exp (-η * lh t i) :=
      Finset.sum_pos (fun i _ ↦ mul_pos (hppos t i) (Real.exp_pos _))
        ⟨⟨0, hK⟩, Finset.mem_univ _⟩
    rw [hratio, Real.log_mul (hWpos t).ne' hZpos.ne', add_sub_cancel_left]
    refine (Real.log_le_sub_one_of_pos hZpos).trans ?_
    have hb : ∀ i, p t i * Real.exp (-η * lh t i) ≤
        p t i * (1 - η * lh t i + (η * lh t i) ^ 2 / 2) := fun i ↦ by
      refine mul_le_mul_of_nonneg_left ?_ (hpnn t i)
      rw [neg_mul]
      exact exp_neg_le_one_sub_add_sq_div_two (mul_nonneg hη.le (hlh t i))
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hb i
    have hexp : ∑ i, p t i * (1 - η * lh t i + (η * lh t i) ^ 2 / 2) =
        ∑ i, p t i - η * ∑ i, p t i * lh t i + η ^ 2 / 2 * ∑ i, p t i * lh t i ^ 2 := by
      simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      · exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hexp, hpsum] at this
    linarith
  have htel : Real.log (W T) - Real.log (W 0) ≤ ∑ t ∈ Finset.range T,
      (-η * ∑ i, p t i * lh t i + η ^ 2 / 2 * ∑ i, p t i * lh t i ^ 2) := by
    rw [← Finset.sum_range_sub (fun t ↦ Real.log (W t))]
    exact Finset.sum_le_sum fun t _ ↦ hstep t
  have hW0 : W 0 = K := by simp [hW]
  have hWT : -η * ∑ s ∈ Finset.range T, lh s istar ≤ Real.log (W T) := by
    rw [← Real.log_exp (-η * _)]
    exact Real.log_le_log (Real.exp_pos _)
      (Finset.single_le_sum (f := fun j ↦ Real.exp (-η * ∑ s ∈ Finset.range T, lh s j))
        (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ istar))
  rw [hW0] at htel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at htel
  have hfinal : η * (∑ t ∈ Finset.range T, ∑ i, p t i * lh t i -
      ∑ t ∈ Finset.range T, lh t istar) ≤
      η * (Real.log K / η + η / 2 * ∑ t ∈ Finset.range T, ∑ i, p t i * lh t i ^ 2) := by
    have : η * (Real.log K / η) = Real.log K := by field_simp
    rw [mul_add, this]
    nlinarith
  exact le_of_mul_le_mul_left hfinal hη

/-- Multiplicative update form of exponential weights:
`p (t+1) i = p t i exp(-η ℓ̂ t i) / ∑ⱼ p t j exp(-η ℓ̂ t j)`. -/
theorem exponentialWeights_succ {K : ℕ} (hK : 0 < K) (η : ℝ) (lh : ℕ → Fin K → ℝ)
    (p : ℕ → Fin K → ℝ)
    (hp : ∀ t i, p t i = Real.exp (-η * ∑ s ∈ Finset.range t, lh s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j)) (t : ℕ) (i : Fin K) :
    p (t + 1) i = p t i * Real.exp (-η * lh t i) /
      ∑ j, p t j * Real.exp (-η * lh t j) := by
  have hWpos : ∀ t, 0 < ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j) := fun t ↦
    Finset.sum_pos (fun j _ ↦ Real.exp_pos _) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hsplit : ∀ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), lh s j) =
      Real.exp (-η * ∑ s ∈ Finset.range t, lh s j) * Real.exp (-η * lh t j) := fun j ↦ by
    rw [Finset.sum_range_succ, mul_add, Real.exp_add]
  have hZ : ∑ j, p t j * Real.exp (-η * lh t j) =
      (∑ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), lh s j)) /
        ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hp, hsplit]; ring
  rw [hZ, hp (t + 1), hp t, hsplit]
  have h0 := (hWpos t).ne'
  have h1 := (hWpos (t + 1)).ne'
  generalize (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j)) = W0 at *
  generalize (∑ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), lh s j)) = W1 at *
  field_simp

end CKSD
