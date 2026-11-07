module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Learning: Privacy

Sources: `GAPS.md`, `SYNOPSIS107.md`, and `STRUCTURE107.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 107.65, basic composition of two adaptive private releases. The proof bounds the first
release through the layer-cake formula for the truncated second-stage probability. -/
theorem isDifferentiallyPrivate_compProd {D Y Z : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    [MeasurableSpace Z] (R : D → D → Prop) (hR : ∀ d d', R d d' → R d' d)
    (M : Kernel D Y) [IsMarkovKernel M] (N : Kernel (D × Y) Z) [IsMarkovKernel N]
    (e₁ e₂ d₁ d₂ : ℝ) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hM : IsDifferentiallyPrivate R e₁ d₁ M)
    (hN : ∀ y, ∀ d d', R d d' → ∀ A : Set Z, MeasurableSet A →
      N (d,y) A ≤ ENNReal.ofReal (Real.exp e₂) * N (d',y) A + ENNReal.ofReal d₂) :
    IsDifferentiallyPrivate R (e₁ + e₂) (d₁ + d₂) (M ⊗ₖ N) := by
  intro d d' hdd' A hA
  rw [Kernel.compProd_apply hA, Kernel.compProd_apply hA]
  set c₁ := ENNReal.ofReal (Real.exp e₁)
  set c₂ := ENNReal.ofReal (Real.exp e₂)
  set g : D → Y → ℝ≥0∞ := fun e y ↦ N (e, y) (Prod.mk y ⁻¹' A)
  have hAy : ∀ y : Y, MeasurableSet (Prod.mk y ⁻¹' A) := fun y ↦ measurable_prodMk_left hA
  have hg'm : Measurable (g d') := Kernel.measurable_kernel_prodMk_left' hA d'
  set h : Y → ℝ≥0∞ := fun y ↦ min 1 (c₂ * g d' y)
  have hhm : Measurable h := measurable_const.min (hg'm.const_mul _)
  have hh1 : ∀ y, h y ≤ 1 := fun y ↦ min_le_left _ _
  set hr : Y → ℝ := fun y ↦ (h y).toReal
  have hhr : ∀ y, h y = ENNReal.ofReal (hr y) := fun y ↦
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hh1 y))).symm
  have hr1 : ∀ y, hr y ≤ 1 := fun y ↦ by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hh1 y); simpa using this
  have hrm : Measurable hr := hhm.ennreal_toReal
  -- step 1
  have hstep1 : ∀ y, g d y ≤ h y + ENNReal.ofReal d₂ := by
    intro y
    have h1 : g d y ≤ 1 := prob_le_one
    have h2 : g d y ≤ c₂ * g d' y + ENNReal.ofReal d₂ := hN y d d' hdd' _ (hAy y)
    rcases le_total 1 (c₂ * g d' y) with hc | hc
    · simp only [h, min_eq_left hc]; exact h1.trans le_self_add
    · simp only [h, min_eq_right hc]; exact h2
  have hstep2 : ∫⁻ y, g d y ∂M d ≤ ∫⁻ y, h y ∂M d + ENNReal.ofReal d₂ := by
    calc ∫⁻ y, g d y ∂M d ≤ ∫⁻ y, (h y + ENNReal.ofReal d₂) ∂M d := lintegral_mono hstep1
      _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  -- layer cake
  have hcake : ∀ e : D, ∫⁻ y, h y ∂M e = ∫⁻ t in Ioi 0, M e {y | t < hr y} := by
    intro e
    simp_rw [hhr]
    exact lintegral_eq_lintegral_meas_lt _ (ae_of_all _ fun y ↦ ENNReal.toReal_nonneg)
      hrm.aemeasurable
  have hpt : ∀ t : ℝ, M d {y | t < hr y} ≤
      c₁ * M d' {y | t < hr y} + (Iio (1 : ℝ)).indicator (fun _ ↦ ENNReal.ofReal d₁) t := by
    intro t
    by_cases ht : t < 1
    · rw [indicator_of_mem ht]
      exact hM d d' hdd' _ (measurableSet_lt measurable_const hrm)
    · have hempty : {y | t < hr y} = ∅ := by
        ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hr1 y).trans (not_lt.mp ht)
      rw [hempty, measure_empty]; exact zero_le
  have hstep3 : ∫⁻ y, h y ∂M d ≤ c₁ * ∫⁻ y, h y ∂M d' + ENNReal.ofReal d₁ := by
    rw [hcake d, hcake d']
    calc ∫⁻ t in Ioi 0, M d {y | t < hr y}
        ≤ ∫⁻ t in Ioi 0, (c₁ * M d' {y | t < hr y} +
            (Iio (1 : ℝ)).indicator (fun _ ↦ ENNReal.ofReal d₁) t) := lintegral_mono hpt
      _ = (∫⁻ t in Ioi 0, c₁ * M d' {y | t < hr y}) +
            ∫⁻ t in Ioi 0, (Iio (1 : ℝ)).indicator (fun _ ↦ ENNReal.ofReal d₁) t :=
        lintegral_add_right _ (measurable_const.indicator measurableSet_Iio)
      _ = c₁ * (∫⁻ t in Ioi 0, M d' {y | t < hr y}) + ENNReal.ofReal d₁ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
        have : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by ext; simp [and_comm]
        rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
  have hstep4 : ∫⁻ y, h y ∂M d' ≤ c₂ * ∫⁻ y, g d' y ∂M d' := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun y ↦ min_le_right _ _
  have hc : ENNReal.ofReal (Real.exp (e₁ + e₂)) = c₁ * c₂ := by
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hc, ENNReal.ofReal_add hd₁ hd₂]
  calc ∫⁻ y, g d y ∂M d ≤ ∫⁻ y, h y ∂M d + ENNReal.ofReal d₂ := hstep2
    _ ≤ c₁ * ∫⁻ y, h y ∂M d' + ENNReal.ofReal d₁ + ENNReal.ofReal d₂ := by gcongr
    _ ≤ c₁ * (c₂ * ∫⁻ y, g d' y ∂M d') + ENNReal.ofReal d₁ + ENNReal.ofReal d₂ := by gcongr
    _ = _ := by rw [mul_assoc, add_assoc]

/-- GAPS 107.75, the single-release KL contraction under local privacy. -/
theorem klDiv_comp_le_of_local_differential_privacy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Kernel X Y) [IsMarkovKernel Q] (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hpriv : IsDifferentiallyPrivate (fun _ _ : X ↦ True) epsilon 0 Q)
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    InformationTheory.klDiv (Q ∘ₘ P₁) (Q ∘ₘ P₂) +
      InformationTheory.klDiv (Q ∘ₘ P₂) (Q ∘ₘ P₁) ≤
      ENNReal.ofReal (4 * (Real.exp epsilon - 1) ^ 2 * totalVariationDistance P₁ P₂ ^ 2) := by
  sorry


end CKSD
