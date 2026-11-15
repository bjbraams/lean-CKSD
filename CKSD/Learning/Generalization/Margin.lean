module

public import CKSD.Learning.Algorithms
import CKSD.Learning.Generalization.Concentration
import CKSD.Learning.Generalization.Contraction
public import CKSD.Learning.Basic

/-!
# Margin generalization bound

The finite-class margin bound uses measurable bounded scores, symmetrization and the
Ledoux–Talagrand contraction.

## Main definitions

* `CKSD.signedMargin`: the signed margin of a score for Boolean labels.

## Main results

* `CKSD.abs_marginLoss_sub_le`, `CKSD.marginLoss_mem_Icc`, `CKSD.marginLoss_eq_one_of_nonpos`:
  the ramp margin loss is `1/ρ`-Lipschitz, `[0,1]`-valued, and dominates the zero-one loss.
* `CKSD.measure_margin_generalization_error_le`: the margin bound (GAPS 107.10).
-/

public section

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
  simp only [marginLoss_def]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ((abs_max_sub_max_le_max _ _ _ _).trans (max_le (by
    rw [sub_self, abs_zero]; positivity) ?_))
  rw [show 1 - u / ρ - (1 - v / ρ) = (v - u) / ρ by ring, abs_div, abs_of_pos hρ, abs_sub_comm]
  rw [div_eq_inv_mul, one_div]

/-- The ramp margin loss takes values in `[0,1]`. -/
theorem marginLoss_mem_Icc (ρ u : ℝ) : marginLoss ρ u ∈ Icc 0 1 := by
  rw [marginLoss_def]
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The ramp margin loss dominates the zero-one loss of a nonpositive margin. -/
theorem marginLoss_eq_one_of_nonpos {ρ u : ℝ} (hρ : 0 < ρ) (hu : u ≤ 0) : marginLoss ρ u = 1 := by
  simp only [marginLoss_def]
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
    have : Measurable (marginLoss ρ) := by rw [funext (marginLoss_def ρ)]; fun_prop
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
    refine integral_mono (Integrable.of_bound
      (measurable_empiricalRademacherComplexity n F hFm).aestronglyMeasurable 1
      (ae_of_all _ (abs_empiricalRademacherComplexity_le n F zero_le_one hFb)))
      ((Integrable.of_bound
        (measurable_empiricalRademacherComplexity n _ hsm).aestronglyMeasurable _
        (ae_of_all _ (abs_empiricalRademacherComplexity_le n _ hB hsb))).const_mul _) hcontr
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
    refine integral_mono ((integrable_const 1).indicator hS) (Integrable.of_bound
      (hφm h).aestronglyMeasurable 1 (ae_of_all _ fun z ↦ by simpa [F] using hFb h z)) fun z ↦ ?_
    by_cases hz : z ∈ {z | signedMargin f h z ≤ 0}
    · rw [indicator_of_mem hz, Pi.one_apply, marginLoss_eq_one_of_nonpos hρ hz]
    · rw [indicator_of_notMem hz]; exact (marginLoss_mem_Icc _ _).1
  have hle := le_csSup (finite_range fun h ↦ (∑ i, F h (x i)) / n - ∫ z, F h z ∂P).bddAbove
    ⟨h, rfl⟩
  have heq : (∑ i, F h (x i)) / n - ∫ z, F h z ∂P =
      ∫ z, marginLoss ρ (signedMargin f h z) ∂P -
        empiricalRisk (fun h z ↦ marginLoss ρ (signedMargin f h z)) h x := by
    simp only [F, empiricalRisk_def, Finset.sum_neg_distrib, integral_neg]; ring
  simp only at hle
  rw [heq] at hle
  have : 2 / ρ * rad = 2 * (1 / ρ * rad) := by ring
  linarith

end CKSD
