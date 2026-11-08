module

public import CKSD.Learning.Generalization.Concentration

/-!
# Exponential weights for bounded losses

Finite exponential-moment bounds and the regret guarantee for the exponential-weights
algorithm. Source: GAPS 107.5.
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

/-- GAPS 107.5: the exponential-weights regret bound, for any positive learning rate. -/
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

end CKSD
