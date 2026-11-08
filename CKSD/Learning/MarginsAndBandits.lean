module

public import CKSD.Learning.Algorithms
public import CKSD.Learning.Generalization

/-!
# Margin generalization and adversarial bandits

The finite-class margin bound uses measurable bounded scores, symmetrization and the
Ledoux–Talagrand contraction. The Exp3 protocol specifies its conditional action probabilities
and importance-weighted cumulative losses, so the algorithmic hypotheses do not assume a regret
conclusion.

## Main definitions

* `CKSD.signedMargin`: the signed margin of a score for Boolean labels.
* `CKSD.exp3EstimatedCumulativeLoss`: Exp3's importance-weighted cumulative loss.
* `CKSD.exp3WeightLowerBound`: a deterministic lower bound for Exp3 probabilities.

## Main results

* `CKSD.measure_margin_generalization_error_le`: the margin bound (GAPS 107.10).
* `CKSD.integral_regret_le_of_exp3`: the Exp3 regret bound `√(2 T K log K)` (GAPS 107.52).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Signed classification margin for Boolean labels, with `true` representing `+1`. -/
def signedMargin {H X : Type*} (f : H → X → ℝ) (h : H) (z : X × Bool) : ℝ :=
  if z.2 then f h z.1 else -f h z.1

/-- The ramp margin loss `min(1, max(0, 1 - u/ρ))` is `1/ρ`-Lipschitz. -/
theorem abs_marginLoss_sub_le {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    |marginLoss ρ u - marginLoss ρ v| ≤ 1 / ρ * |u - v| := by
  unfold marginLoss
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ((abs_max_sub_max_le_max _ _ _ _).trans (max_le (by
    rw [sub_self, abs_zero]; positivity) ?_))
  rw [show 1 - u / ρ - (1 - v / ρ) = (v - u) / ρ by ring, abs_div, abs_of_pos hρ, abs_sub_comm]
  rw [div_eq_inv_mul, one_div]

/-- The ramp margin loss takes values in `[0,1]`. -/
theorem marginLoss_mem_Icc (ρ u : ℝ) : marginLoss ρ u ∈ Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The ramp margin loss dominates the zero-one loss of a nonpositive margin. -/
theorem marginLoss_eq_one_of_nonpos {ρ u : ℝ} (hρ : 0 < ρ) (hu : u ≤ 0) : marginLoss ρ u = 1 := by
  unfold marginLoss
  have : 1 ≤ 1 - u / ρ := by
    have : u / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hρ.le
    linarith
  rw [max_eq_right (by linarith), min_eq_left this]

/-- GAPS 107.10: uniform expected-Rademacher margin bound for a finite class. For real scores
`f h` bounded by `B`, margin scale `ρ > 0` and `δ ∈ (0,1)`, with probability at least `1 - δ`
every `h` has misclassification probability at most its empirical ramp margin risk plus
`2/ρ` times the expected Rademacher complexity of the margins plus `√(log(1/δ) / (2n))`. -/
theorem measure_margin_generalization_error_le {H X : Type*} [Fintype H] [Nonempty H]
    [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (f : H → X → ℝ) (hm : ∀ h, Measurable (f h)) (B : ℝ)
    (hb : ∀ h x, |f h x| ≤ B) (n : ℕ) (hn : 0 < n)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : δ ∈ Ioo 0 1) :
    let Pn := Measure.pi fun _ : Fin n ↦ P;
    let rad := ∫ x, empiricalRademacherComplexity n (signedMargin f) x ∂Pn;
    Pn.real {x | ∃ h,
      empiricalRisk (fun h z ↦ marginLoss ρ (signedMargin f h z)) h x +
        2 / ρ * rad + Real.sqrt (Real.log (1 / δ) / (2 * n)) <
          P.real {z | signedMargin f h z ≤ 0}} ≤ δ := by
  intro Pn rad
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 ≤ max B 0 := le_max_right _ _
  -- margins
  have hsm : ∀ h, Measurable (signedMargin f h) := fun h ↦ by
    unfold signedMargin
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      ((hm h).comp measurable_fst) ((hm h).comp measurable_fst).neg
  have hsb : ∀ h z, |signedMargin f h z| ≤ max B 0 := fun h z ↦ by
    refine le_max_of_le_left ?_
    unfold signedMargin; split_ifs <;> simp [hb]
  -- the negated loss class
  set F : H → X × Bool → ℝ := fun h z ↦ -marginLoss ρ (signedMargin f h z) with hF_def
  have hφm : ∀ h, Measurable fun z ↦ marginLoss ρ (signedMargin f h z) := fun h ↦ by
    have : Measurable (marginLoss ρ) := by unfold marginLoss; fun_prop
    exact this.comp (hsm h)
  have hFm : ∀ h, Measurable (F h) := fun h ↦ (hφm h).neg
  have hFb : ∀ h z, |F h z| ≤ 1 := fun h z ↦ by
    have := marginLoss_mem_Icc ρ (signedMargin f h z)
    simp only [F, abs_neg, abs_le]; constructor <;> linarith [this.1, this.2]
  have hFosc : ∀ h z w, |F h z - F h w| ≤ 1 := fun h z w ↦ by
    have h1 := marginLoss_mem_Icc ρ (signedMargin f h z)
    have h2 := marginLoss_mem_Icc ρ (signedMargin f h w)
    simp only [F, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- expected supremum via symmetrization and contraction
  have hsym := integral_sSup_sub_le_two_mul_rademacher P F hFm hFb n hn
  have hcontr : ∀ x, empiricalRademacherComplexity n F x ≤
      1 / ρ * empiricalRademacherComplexity n (signedMargin f) x := by
    intro x
    have hneg := empiricalRademacherComplexity_neg n
      (fun h z ↦ marginLoss ρ (signedMargin f h z)) x
    simp only [F]
    rw [hneg, empiricalRademacherComplexity_eq, empiricalRademacherComplexity_eq,
      mul_left_comm]
    exact mul_le_mul_of_nonneg_left (sum_sSup_rademacher_comp_le n
      (fun h i ↦ signedMargin f h (x i)) (marginLoss ρ) (by positivity)
      (abs_marginLoss_sub_le hρ)) (by positivity)
  have hRadF : ∫ x, empiricalRademacherComplexity n F x ∂Pn ≤ 1 / ρ * rad := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_abs_le _
      (measurable_empiricalRademacherComplexity n F hFm)
      (abs_empiricalRademacherComplexity_le n F zero_le_one hFb))
      ((integrable_of_abs_le _ (measurable_empiricalRademacherComplexity n _ hsm)
        (abs_empiricalRademacherComplexity_le n _ hB hsb)).const_mul _) hcontr
  -- tail
  set tt := Real.sqrt (Real.log (1 / δ) / (2 * n)) with htt
  have htail := measureReal_integral_add_le_sSup_le P F hFm hFosc n hn (Real.sqrt_nonneg _)
    (t := tt)
  have hexp : Real.exp (-2 * n * tt ^ 2) = δ := by
    have hlog : 0 ≤ Real.log (1 / δ) / (2 * n) := by
      refine div_nonneg (Real.log_nonneg ?_) (by positivity)
      rw [le_div_iff₀ hδ.1]; linarith [hδ.2]
    rw [htt, Real.sq_sqrt hlog]
    have : -2 * (n : ℝ) * (Real.log (1 / δ) / (2 * n)) = -Real.log (1 / δ) := by
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (div_pos one_pos hδ.1), inv_div, div_one]
  rw [hexp] at htail
  refine le_trans (measureReal_mono ?_) htail
  intro x hx
  obtain ⟨h, hh⟩ := hx
  simp only [mem_ofPred_eq]
  -- the zero-one risk is dominated by the ramp risk
  have hrisk : P.real {z | signedMargin f h z ≤ 0} ≤
      ∫ z, marginLoss ρ (signedMargin f h z) ∂P := by
    have hS : MeasurableSet {z | signedMargin f h z ≤ 0} :=
      measurableSet_le (hsm h) measurable_const
    rw [← integral_indicator_one hS]
    refine integral_mono ((integrable_const 1).indicator hS) (integrable_of_abs_le _
      (hφm h) (C := 1) fun z ↦ by simpa [F] using hFb h z) fun z ↦ ?_
    by_cases hz : z ∈ {z | signedMargin f h z ≤ 0}
    · rw [indicator_of_mem hz, Pi.one_apply, marginLoss_eq_one_of_nonpos hρ hz]
    · rw [indicator_of_notMem hz]; exact (marginLoss_mem_Icc _ _).1
  have hle := le_csSup (finite_range fun h ↦ (∑ i, F h (x i)) / n - ∫ z, F h z ∂P).bddAbove
    ⟨h, rfl⟩
  have heq : (∑ i, F h (x i)) / n - ∫ z, F h z ∂P =
      ∫ z, marginLoss ρ (signedMargin f h z) ∂P -
        empiricalRisk (fun h z ↦ marginLoss ρ (signedMargin f h z)) h x := by
    simp only [F, empiricalRisk, Finset.sum_neg_distrib, integral_neg]; ring
  simp only at hle
  rw [heq] at hle
  have : 2 / ρ * rad = 2 * (1 / ρ * rad) := by ring
  linarith


/-- Conditional-probability identity: if `P[1_{A = j} | 𝓕] = p` and `g` is bounded and
`𝓕`-measurable, then `∫ 1_{A = j} g = ∫ p g`. -/
theorem integral_indicator_mul_eq_of_condExp {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (A : Ω → Fin K) (hA : Measurable A) (j : Fin K)
    (q : Ω → ℝ) (hq : P[(fun ω ↦ if A ω = j then (1 : ℝ) else 0) | m] =ᵐ[P] q)
    (g : Ω → ℝ) (hg : StronglyMeasurable[m] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) :
    ∫ ω, (if A ω = j then (1 : ℝ) else 0) * g ω ∂P = ∫ ω, q ω * g ω ∂P := by
  have hXm : Measurable fun ω ↦ if A ω = j then (1 : ℝ) else 0 :=
    Measurable.ite (hA (measurableSet_singleton j)) measurable_const measurable_const
  have hX : Integrable (fun ω ↦ if A ω = j then (1 : ℝ) else 0) P :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      split_ifs <;> simp)
  have hgm : Measurable g := (hg.mono hm).measurable
  have hgX : Integrable (g * fun ω ↦ if A ω = j then (1 : ℝ) else 0) P :=
    Integrable.of_bound (hgm.mul hXm).aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      split_ifs <;> simp [hgb ω, (abs_nonneg _).trans (hgb ω)])
  have h1 := condExp_mul_of_stronglyMeasurable_left hg hgX hX
  calc ∫ ω, (if A ω = j then (1 : ℝ) else 0) * g ω ∂P
      = ∫ ω, (g * fun ω ↦ if A ω = j then (1 : ℝ) else 0) ω ∂P := by
        congr 1; funext ω; simp [mul_comm]
    _ = ∫ ω, (P[g * fun ω ↦ if A ω = j then (1 : ℝ) else 0 | m]) ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, q ω * g ω ∂P := by
        refine integral_congr_ae (h1.trans ?_)
        filter_upwards [hq] with ω hω
        simp only [Pi.mul_apply, hω, mul_comm]

/-- Exp3 importance-weighted cumulative estimated loss. -/
def exp3EstimatedCumulativeLoss {Ω : Type*} {K : ℕ} (loss : ℕ → Fin K → ℝ)
    (p : ℕ → Ω → Fin K → ℝ) (A : ℕ → Ω → Fin K) (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range t, if A s ω = i then loss s i / p s ω i else 0

/-- The deterministic lower bound for Exp3 probabilities: `c₀ = 1/K` and
`c_{t+1} = c_t exp(-η / c_t)`. -/
def exp3WeightLowerBound (K : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => (K : ℝ)⁻¹
  | t + 1 => exp3WeightLowerBound K η t * Real.exp (-η / exp3WeightLowerBound K η t)

/-- The Exp3 lower-bound sequence is positive. -/
theorem exp3WeightLowerBound_pos {K : ℕ} (hK : 0 < K) (η : ℝ) (t : ℕ) :
    0 < exp3WeightLowerBound K η t := by
  induction t with
  | zero => simp only [exp3WeightLowerBound]; positivity
  | succ t ih => exact mul_pos ih (Real.exp_pos _)

/-- Exponential weights with nonnegative estimated losses `ℓ̂ t j ≤ 1 / p t j` stay above the
positive sequence `exp3WeightLowerBound K η`. -/
theorem exp3WeightLowerBound_le {K : ℕ} (hK : 0 < K) {η : ℝ} (hη : 0 < η)
    (lh p : ℕ → Fin K → ℝ) (hlh0 : ∀ t j, 0 ≤ lh t j) (hlh1 : ∀ t j, lh t j ≤ 1 / p t j)
    (hp : ∀ t i, p t i = Real.exp (-η * ∑ s ∈ Finset.range t, lh s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j)) (t : ℕ) :
    ∀ j, exp3WeightLowerBound K η t ≤ p t j := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hW : ∀ t, 0 < ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, lh s j) := fun t ↦
    Finset.sum_pos (fun j _ ↦ Real.exp_pos _) hne
  have hpos : ∀ t i, 0 < p t i := fun t i ↦ by
    rw [hp]; exact div_pos (Real.exp_pos _) (hW t)
  have hsum : ∀ t, ∑ i, p t i = 1 := fun t ↦ by
    simp_rw [hp t]; rw [← Finset.sum_div, div_self (hW t).ne']
  induction t with
  | zero =>
    intro j
    rw [hp 0 j]
    simp [exp3WeightLowerBound]
  | succ t ih =>
    set c := exp3WeightLowerBound K η t
    have hc := exp3WeightLowerBound_pos hK η t
    intro j
    have hup := exponentialWeights_succ hK η lh p hp t j
    have hZpos : 0 < ∑ j', p t j' * Real.exp (-η * lh t j') :=
      Finset.sum_pos (fun j' _ ↦ mul_pos (hpos t j') (Real.exp_pos _)) hne
    have hZ1 : ∑ j', p t j' * Real.exp (-η * lh t j') ≤ 1 := by
      rw [← hsum t]
      refine Finset.sum_le_sum fun j' _ ↦ ?_
      calc p t j' * Real.exp (-η * lh t j') ≤ p t j' * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
              nlinarith [hlh0 t j'])) (hpos t j').le
        _ = p t j' := mul_one _
    have hge : p t j * Real.exp (-η * lh t j) ≤ p (t + 1) j := by
      rw [hup]
      exact (le_div_iff₀ hZpos).mpr (mul_le_of_le_one_right
        (mul_nonneg (hpos t j).le (Real.exp_pos _).le) hZ1)
    have hexp : Real.exp (-η / c) ≤ Real.exp (-η * lh t j) := by
      apply Real.exp_le_exp.mpr
      have h1 : lh t j ≤ 1 / c := (hlh1 t j).trans (one_div_le_one_div_of_le hc (ih j))
      rw [neg_div, neg_mul, neg_le_neg_iff, ← mul_one_div]
      exact mul_le_mul_of_nonneg_left h1 hη.le
    calc exp3WeightLowerBound K η (t + 1) = c * Real.exp (-η / c) := rfl
      _ ≤ p t j * Real.exp (-η * lh t j) :=
          mul_le_mul (ih j) hexp (Real.exp_pos _).le (hpos t j).le
      _ ≤ _ := hge

/-- GAPS 107.52: expected Exp3 regret against an oblivious loss sequence. The arm `A t` is
drawn with conditional probabilities `p t` given the past `F t`, and `p t` is the exponential-
weights distribution, with learning rate `η = √(2 log K / (T K))`, of the importance-weighted
cumulative estimated losses. Then the expected regret against every fixed arm over `T` rounds is
at most `√(2 T K log K)`. -/
theorem integral_regret_le_of_exp3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (K T : ℕ) (hK : 2 ≤ K) (hT : 0 < T)
    (loss : ℕ → Fin K → ℝ) (hloss : ∀ t i, loss t i ∈ Icc 0 1)
    (p : ℕ → Ω → Fin K → ℝ) (A : ℕ → Ω → Fin K)
    (hp : ∀ t, Measurable[F t] (p t)) (hA : ∀ t, Measurable[F (t + 1)] (A t))
    (hchoice : ∀ t i, P[(fun ω ↦ if A t ω = i then (1 : ℝ) else 0) | F t] =ᵐ[P]
      fun ω ↦ p t ω i)
    (hrec : ∀ t ω i,
      let η := Real.sqrt (2 * Real.log K / (T * K));
      p t ω i = Real.exp (-η * exp3EstimatedCumulativeLoss loss p A t i ω) /
        ∑ j, Real.exp (-η * exp3EstimatedCumulativeLoss loss p A t j ω)) (i : Fin K) :
    (∫ ω, ∑ t ∈ Finset.range T, loss t (A t ω) ∂P) - (∑ t ∈ Finset.range T, loss t i) ≤
      Real.sqrt (2 * T * K * Real.log K) := by
  set η := Real.sqrt (2 * Real.log K / (T * K)) with hη_def
  have hK0 : 0 < K := by omega
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hη : 0 < η := Real.sqrt_pos.mpr (by positivity)
  -- estimated losses
  set lh : ℕ → Ω → Fin K → ℝ := fun t ω j ↦ if A t ω = j then loss t j / p t ω j else 0
    with hlh_def
  have hrec' : ∀ ω t j, p t ω j = Real.exp (-η * ∑ s ∈ Finset.range t, lh s ω j) /
      ∑ j', Real.exp (-η * ∑ s ∈ Finset.range t, lh s ω j') := fun ω t j ↦ hrec t ω j
  have hW : ∀ ω t, 0 < ∑ j', Real.exp (-η * ∑ s ∈ Finset.range t, lh s ω j') := fun _ _ ↦
    Finset.sum_pos (fun j _ ↦ Real.exp_pos _) ⟨⟨0, hK0⟩, Finset.mem_univ _⟩
  have hpos : ∀ t ω i, 0 < p t ω i := fun t ω i ↦ by
    rw [hrec' ω t i]; exact div_pos (Real.exp_pos _) (hW ω t)
  have hsum : ∀ t ω, ∑ i, p t ω i = 1 := fun t ω ↦ by
    simp_rw [hrec' ω t]; rw [← Finset.sum_div, div_self (hW ω t).ne']
  have hlh0 : ∀ t ω j, 0 ≤ lh t ω j := fun t ω j ↦ by
    simp only [lh]; split_ifs
    · exact div_nonneg (hloss t j).1 (hpos t ω j).le
    · exact le_rfl
  have hlh1 : ∀ t ω j, lh t ω j ≤ 1 / p t ω j := fun t ω j ↦ by
    simp only [lh]; split_ifs
    · exact div_le_div_of_nonneg_right (hloss t j).2 (hpos t ω j).le
    · exact (one_div_pos.mpr (hpos t ω j)).le
  -- deterministic lower bounds on the probabilities
  set c := exp3WeightLowerBound K η
  have hc : ∀ t, 0 < c t ∧ ∀ ω j, c t ≤ p t ω j := fun t ↦
    ⟨exp3WeightLowerBound_pos hK0 η t, fun ω ↦ exp3WeightLowerBound_le hK0 hη (lh · ω)
      (fun t j ↦ p t ω j) (fun t j ↦ hlh0 t ω j) (fun t j ↦ hlh1 t ω j) (hrec' ω) t⟩
  -- measurability
  have hpm : ∀ t j, Measurable[F t] fun ω ↦ p t ω j := fun t j ↦
    (measurable_pi_apply j).comp (hp t)
  have hAm : ∀ t, Measurable (A t) := fun t ↦ (hA t).mono (F.le (t + 1)) le_rfl
  -- the conditional-probability identities
  have hg : ∀ t j (r : ℝ), r ∈ Icc (0 : ℝ) 1 →
      ∫ ω, (if A t ω = j then (1 : ℝ) else 0) * (r / p t ω j) ∂P = r := by
    intro t j r hr
    have hgm : StronglyMeasurable[F t] fun ω ↦ r / p t ω j :=
      (measurable_const.div (hpm t j)).stronglyMeasurable
    have hb : ∀ ω, |r / p t ω j| ≤ 1 / c t := fun ω ↦ by
      rw [abs_of_nonneg (div_nonneg hr.1 (hpos t ω j).le)]
      exact (div_le_div_of_nonneg_right hr.2 (hpos t ω j).le).trans
        (one_div_le_one_div_of_le (hc t).1 ((hc t).2 ω j))
    rw [integral_indicator_mul_eq_of_condExp (F.le t) P (A t) (hAm t) j _ (hchoice t j) _ hgm hb]
    have : ∀ ω, p t ω j * (r / p t ω j) = r := fun ω ↦ by
      field_simp [(hpos t ω j).ne']
    simp only [this, integral_const, probReal_univ, one_smul]
  -- pointwise identities
  have hplh : ∀ t ω, ∑ j, p t ω j * lh t ω j = loss t (A t ω) := fun t ω ↦ by
    rw [Finset.sum_eq_single (A t ω)]
    · simp only [lh, ↓reduceIte]; field_simp [(hpos t ω (A t ω)).ne']
    · intro j _ hj; simp [lh, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hplh2 : ∀ t ω j, p t ω j * lh t ω j ^ 2 =
      (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j) := fun t ω j ↦ by
    simp only [lh]; split_ifs
    · field_simp [(hpos t ω j).ne']
    · simp
  have hlhi : ∀ t ω j, lh t ω j =
      (if A t ω = j then (1 : ℝ) else 0) * (loss t j / p t ω j) := fun t ω j ↦ by
    simp only [lh]; split_ifs <;> simp
  have hpt : ∀ ω, ∑ t ∈ Finset.range T, loss t (A t ω) - ∑ t ∈ Finset.range T, lh t ω i ≤
      Real.log K / η + η / 2 * ∑ t ∈ Finset.range T, ∑ j,
        (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j) := fun ω ↦ by
    have h := sum_sum_mul_sub_le_of_exponential_weights hK0 hη (lh · ω) (fun t j ↦ hlh0 t ω j)
      (fun t j ↦ p t ω j) (hrec' ω) T i
    simp only [hplh, hplh2] at h
    exact h
  -- integrability of the bounded measurable pieces
  have hterm : ∀ t j (r : ℝ), r ∈ Icc (0 : ℝ) 1 →
      Integrable (fun ω ↦ (if A t ω = j then (1 : ℝ) else 0) * (r / p t ω j)) P := by
    intro t j r hr
    have hXm : Measurable fun ω ↦ if A t ω = j then (1 : ℝ) else 0 :=
      Measurable.ite ((hAm t) (measurableSet_singleton j)) measurable_const measurable_const
    have hgm : Measurable fun ω ↦ r / p t ω j :=
      measurable_const.div ((hpm t j).mono (F.le t) le_rfl)
    refine Integrable.of_bound (hXm.mul hgm).aestronglyMeasurable (1 / c t)
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |r / p t ω j| ≤ 1 / c t := by
      rw [abs_of_nonneg (div_nonneg hr.1 (hpos t ω j).le)]
      exact (div_le_div_of_nonneg_right hr.2 (hpos t ω j).le).trans
        (one_div_le_one_div_of_le (hc t).1 ((hc t).2 ω j))
    split_ifs
    · simpa using hb
    · simp only [abs_zero, zero_mul]; exact (one_div_pos.mpr (hc t).1).le
  have hsq : ∀ t j, loss t j ^ 2 ∈ Icc (0 : ℝ) 1 := fun t j ↦
    ⟨sq_nonneg _, by nlinarith [(hloss t j).1, (hloss t j).2]⟩
  have hXint : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, loss t (A t ω)) P := by
    refine integrable_finsetSum _ fun t _ ↦ ?_
    have : (fun ω ↦ loss t (A t ω)) = fun ω ↦ ∑ j,
        (if A t ω = j then (1 : ℝ) else 0) * (loss t j / p t ω j) * p t ω j := by
      funext ω
      rw [Finset.sum_eq_single (A t ω)]
      · simp only [↓reduceIte, one_mul]; field_simp [(hpos t ω (A t ω)).ne']
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]
    refine integrable_finsetSum _ fun j _ ↦ ?_
    refine (hterm t j _ (hloss t j)).mul_of_top_left ?_
    refine memLp_top_of_bound ((hpm t j).mono (F.le t) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hpos t ω j), ← hsum t ω]
    exact Finset.single_le_sum (fun j' _ ↦ (hpos t ω j').le) (Finset.mem_univ j)
  have hYint : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, lh t ω i) P := by
    simp only [hlhi]
    exact integrable_finsetSum _ fun t _ ↦ hterm t i _ (hloss t i)
  have hZint : Integrable (fun ω ↦ ∑ t ∈ Finset.range T, ∑ j,
      (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j)) P :=
    integrable_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun j _ ↦ hterm t j _ (hsq t j)
  have hY : ∫ ω, ∑ t ∈ Finset.range T, lh t ω i ∂P = ∑ t ∈ Finset.range T, loss t i := by
    simp only [hlhi]
    rw [integral_finsetSum _ fun t _ ↦ hterm t i _ (hloss t i)]
    exact Finset.sum_congr rfl fun t _ ↦ hg t i _ (hloss t i)
  have hZ : ∫ ω, ∑ t ∈ Finset.range T, ∑ j,
      (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j) ∂P ≤ T * K := by
    rw [integral_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun j _ ↦ hterm t j _ (hsq t j)]
    calc ∑ t ∈ Finset.range T, ∫ ω, ∑ j,
          (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j) ∂P
        = ∑ t ∈ Finset.range T, ∑ j : Fin K, loss t j ^ 2 := by
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          rw [integral_finsetSum _ fun j _ ↦ hterm t j _ (hsq t j)]
          exact Finset.sum_congr rfl fun j _ ↦ hg t j _ (hsq t j)
      _ ≤ ∑ t ∈ Finset.range T, ∑ j : Fin K, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ ↦ Finset.sum_le_sum fun j _ ↦ (hsq t j).2
      _ = T * K := by simp
  have hint : ∫ ω, (∑ t ∈ Finset.range T, loss t (A t ω) - ∑ t ∈ Finset.range T, lh t ω i) ∂P ≤
      ∫ ω, (Real.log K / η + η / 2 * ∑ t ∈ Finset.range T, ∑ j,
        (if A t ω = j then (1 : ℝ) else 0) * (loss t j ^ 2 / p t ω j)) ∂P :=
    integral_mono (hXint.sub hYint)
      ((integrable_const (Real.log K / η)).add (hZint.const_mul (η / 2))) hpt
  rw [integral_sub hXint hYint, integral_add (integrable_const _) (hZint.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul, hY] at hint
  have hη2 : η ^ 2 = 2 * Real.log K / (T * K) := Real.sq_sqrt (by positivity)
  have hTK : (0 : ℝ) < T * K := by positivity
  have hfinal : Real.log K / η + η / 2 * (T * K) = Real.sqrt (2 * T * K * Real.log K) := by
    have hs : Real.sqrt (2 * T * K * Real.log K) = η * (T * K) := by
      rw [show (2 : ℝ) * T * K * Real.log K = (η * (T * K)) ^ 2 by
        rw [mul_pow, hη2]; field_simp]
      exact Real.sqrt_sq (by positivity)
    have h2 : η ^ 2 * (T * K) = 2 * Real.log K := by rw [hη2]; field_simp
    rw [hs]
    field_simp
    linear_combination -h2
  calc _ ≤ Real.log K / η + η / 2 * (T * K) := by
        nlinarith [mul_le_mul_of_nonneg_left hZ (by positivity : (0 : ℝ) ≤ η / 2)]
    _ = _ := hfinal

end CKSD
