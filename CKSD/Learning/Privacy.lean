module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import CKSD.Nonparametric.LowerBounds
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.Divergence.TotalVariation.Integral
public import Statlib.Divergence.TotalVariation.Event

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
release through the layer-cake formula for the truncated second-stage probability; it does not
use the symmetry of `R` or the signs of `e₁` and `e₂`. -/
theorem isDifferentiallyPrivate_compProd {D Y Z : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    [MeasurableSpace Z] (R : D → D → Prop) (_hR : ∀ d d', R d d' → R d' d)
    (M : Kernel D Y) [IsMarkovKernel M] (N : Kernel (D × Y) Z) [IsMarkovKernel N]
    (e₁ e₂ d₁ d₂ : ℝ) (_he₁ : 0 ≤ e₁) (_he₂ : 0 ≤ e₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
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

/-- Mathlib's total variation distance of probability measures (the `L¹` norm) is at most twice
the event discrepancy `totalVariationDistance`. -/
theorem tvDist_le_two_mul_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    tvDist P₁ P₂ ≤ 2 * totalVariationDistance P₁ P₂ := by
  have hT0 : 0 ≤ totalVariationDistance P₁ P₂ :=
    (abs_nonneg _).trans (abs_measureReal_sub_le_totalVariationDistance P₁ P₂ ∅ MeasurableSet.empty)
  have hE : etvDist P₁ P₂ ≤ 2 * ENNReal.ofReal (totalVariationDistance P₁ P₂) := by
    rw [etvDist_eq_two_mul_iSup_sub P₁ P₂ (by simp)]
    gcongr
    refine iSup₂_le fun E hE ↦ ?_
    rw [← ofReal_measureReal (μ := P₁) (s := E), ← ofReal_measureReal (μ := P₂) (s := E),
      ← ENNReal.ofReal_sub _ measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
      (abs_measureReal_sub_le_totalVariationDistance P₁ P₂ E hE))
  have := ENNReal.toReal_mono (by finiteness) hE
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT0] at this
  simpa [tvDist] using this

/-- A measurable function with values in `[0, c]` has expectations under two probability
measures differing by at most `c` times their total variation distance. -/
theorem abs_integral_sub_integral_le_mul_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {ψ : X → ℝ}
    {c : ℝ} (hψ : Measurable ψ) (h0 : ∀ x, 0 ≤ ψ x) (hc : ∀ x, ψ x ≤ c) :
    |∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂| ≤ c * totalVariationDistance P₁ P₂ := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P₁
  have hc0 : 0 ≤ c := (h0 x₀).trans (hc x₀)
  have htv := tvDist_le_two_mul_totalVariationDistance P₁ P₂
  rcases hc0.eq_or_lt with rfl | hcpos
  · have : ψ = fun _ ↦ 0 := funext fun x ↦ le_antisymm (hc x) (h0 x)
    simp [this]
  have hint : ∀ P : Measure X, [IsProbabilityMeasure P] → Integrable ψ P := fun P _ ↦
    Integrable.of_bound hψ.aestronglyMeasurable c (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hc x)
  set f : X → ℝ := fun x ↦ 2 / c * ψ x - 1
  have hf : ∀ x, |f x| ≤ 1 := fun x ↦ by
    have h1 := h0 x; have h2 := hc x
    rw [abs_le]; constructor
    · simp only [f]; have : 0 ≤ 2 / c * ψ x := by positivity
      linarith
    · simp only [f]; have : 2 / c * ψ x ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]; linarith
      linarith
  have hfi : ∀ P : Measure X, [IsProbabilityMeasure P] →
      ∫ x, f x ∂P = 2 / c * ∫ x, ψ x ∂P - 1 := fun P _ ↦ by
    simp only [f]
    rw [integral_sub ((hint P).const_mul _) (integrable_const _), integral_const_mul]
    simp
  have h1 := integral_sub_integral_le_tvDist (μ := P₁) (ν := P₂) (f := f)
    (by fun_prop) (ae_of_all _ hf)
  have h2 := integral_sub_integral_le_tvDist (μ := P₁) (ν := P₂) (f := fun x ↦ - f x)
    (by fun_prop) (ae_of_all _ fun x ↦ by rw [abs_neg]; exact hf x)
  rw [integral_neg, integral_neg, hfi, hfi] at h2
  rw [hfi, hfi] at h1
  have key : |2 / c * (∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂)| ≤ 2 * totalVariationDistance P₁ P₂ := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by positivity)] at key
  have : 2 / c * |∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂| * (c / 2) ≤
      2 * totalVariationDistance P₁ P₂ * (c / 2) := by gcongr
  field_simp at this
  linarith

/-- For a pure `ε`-locally private Markov kernel `Q`, the output laws `Q ∘ₘ P₁` and `Q ∘ₘ P₂`
differ on each event by at most `(e^ε - 1) · TV(P₁, P₂)` times the mass of that event under
either output law. -/
theorem abs_measureReal_comp_sub_le_of_local_privacy {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (Q : Kernel X Y) [IsMarkovKernel Q] {ε : ℝ} (he : 0 ≤ ε)
    (hpriv : IsDifferentiallyPrivate (fun _ _ : X ↦ True) ε 0 Q)
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {A : Set Y}
    (hA : MeasurableSet A) :
    |(Q ∘ₘ P₁).real A - (Q ∘ₘ P₂).real A| ≤
        (Real.exp ε - 1) * totalVariationDistance P₁ P₂ * (Q ∘ₘ P₂).real A ∧
      |(Q ∘ₘ P₁).real A - (Q ∘ₘ P₂).real A| ≤
        (Real.exp ε - 1) * totalVariationDistance P₁ P₂ * (Q ∘ₘ P₁).real A := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure P₁
  set q : X → ℝ := fun x ↦ (Q x A).toReal
  have hqm : Measurable q := (Q.measurable_coe hA).ennreal_toReal
  have hq0 : ∀ x, 0 ≤ q x := fun x ↦ ENNReal.toReal_nonneg
  have hq1 : ∀ x, q x ≤ 1 := fun x ↦ measureReal_le_one
  have hqq : ∀ x x', q x ≤ Real.exp ε * q x' := fun x x' ↦ by
    have h := hpriv x x' trivial A hA
    rw [ENNReal.ofReal_zero, add_zero] at h
    have := ENNReal.toReal_mono (by finiteness) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  set m : ℝ := ⨅ x, q x
  have hbdd : BddBelow (range q) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hq0 x⟩
  have hmq : ∀ x, m ≤ q x := fun x ↦ ciInf_le hbdd x
  have hqm' : ∀ x, q x ≤ Real.exp ε * m := fun x ↦ by
    have : q x / Real.exp ε ≤ m := le_ciInf fun x' ↦ by
      rw [div_le_iff₀ (Real.exp_pos _)]; linarith [hqq x x']
    rwa [div_le_iff₀ (Real.exp_pos _), mul_comm] at this
  have hreal : ∀ P : Measure X, [IsProbabilityMeasure P] → (Q ∘ₘ P).real A = ∫ x, q x ∂P := by
    intro P _
    rw [measureReal_def, Measure.bind_apply hA (Q.aemeasurable),
      integral_toReal (Q.measurable_coe hA).aemeasurable (ae_of_all _ fun x ↦ by finiteness)]
  have hint : ∀ P : Measure X, [IsProbabilityMeasure P] → Integrable q P := fun P _ ↦
    Integrable.of_bound hqm.aestronglyMeasurable 1 (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]; exact hq1 x)
  have hψ := abs_integral_sub_integral_le_mul_totalVariationDistance P₁ P₂ (ψ := fun x ↦ q x - m)
    (c := (Real.exp ε - 1) * m) (hqm.sub_const _) (fun x ↦ by linarith [hmq x])
    (fun x ↦ by linarith [hqm' x])
  have hsub : ∀ P : Measure X, [IsProbabilityMeasure P] → ∫ x, (q x - m) ∂P = ∫ x, q x ∂P - m :=
    fun P _ ↦ by rw [integral_sub (hint P) (integrable_const _)]; simp
  rw [hsub, hsub, sub_sub_sub_cancel_right] at hψ
  have hmP : ∀ P : Measure X, [IsProbabilityMeasure P] → m ≤ ∫ x, q x ∂P := fun P _ ↦ by
    have := integral_mono (integrable_const m) (hint P) hmq
    simpa using this
  have hT0 : 0 ≤ totalVariationDistance P₁ P₂ :=
    (abs_nonneg _).trans (abs_measureReal_sub_le_totalVariationDistance P₁ P₂ ∅ MeasurableSet.empty)
  have he1 : 0 ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
  rw [hreal, hreal]
  constructor
  · calc _ ≤ (Real.exp ε - 1) * m * totalVariationDistance P₁ P₂ := hψ
      _ = (Real.exp ε - 1) * totalVariationDistance P₁ P₂ * m := by ring
      _ ≤ _ := by gcongr; exact hmP P₂
  · calc _ ≤ (Real.exp ε - 1) * m * totalVariationDistance P₁ P₂ := hψ
      _ = (Real.exp ε - 1) * totalVariationDistance P₁ P₂ * m := by ring
      _ ≤ _ := by gcongr; exact hmP P₁

/-- The Kullback–Leibler function is dominated by the `χ²` integrand on `[0, ∞)`. -/
theorem klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) : InformationTheory.klFun x ≤ (x - 1) ^ 2 := by
  rw [InformationTheory.klFun_apply]
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

/-- If two probability measures satisfy `|μ A - ν A| ≤ δ ν A` for every event, then
`KL(μ ‖ ν) ≤ δ²`. -/
theorem klDiv_le_ofReal_sq_of_abs_measureReal_sub_le {Y : Type*} [MeasurableSpace Y]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ δ * ν.real A) :
    InformationTheory.klDiv μ ν ≤ ENNReal.ofReal (δ ^ 2) := by
  have hac : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_
    have h1 := h A hA
    rw [measureReal_def ν A, h0, ENNReal.toReal_zero, sub_zero, mul_zero] at h1
    have h2 : μ.real A = 0 := abs_nonpos_iff.mp h1
    exact (measureReal_eq_zero_iff).mp h2
  have hupA : ∀ A, MeasurableSet A → μ A ≤ ENNReal.ofReal (1 + δ) * ν A := fun A hA ↦ by
    have h1 := (abs_le.mp (h A hA)).2
    rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν),
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlowA : ∀ A, MeasurableSet A → ENNReal.ofReal (1 - δ) * ν A ≤ μ A := fun A hA ↦ by
    have h1 := (abs_le.mp (h A hA)).1
    rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν),
      ← ENNReal.ofReal_mul' measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hup : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ ENNReal.ofReal (1 + δ) :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
      fun A hA _ ↦ by
        rw [Measure.setLIntegral_rnDeriv' hac hA, setLIntegral_const]; exact hupA A hA
  have hlow : ∀ᵐ x ∂ν, ENNReal.ofReal (1 - δ) ≤ μ.rnDeriv ν x :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
      fun A hA _ ↦ by
        rw [Measure.setLIntegral_rnDeriv' hac hA, setLIntegral_const]; exact hlowA A hA
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  calc ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (μ.rnDeriv ν x).toReal) ∂ν
      ≤ ∫⁻ _x, ENNReal.ofReal (δ ^ 2) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hup, hlow] with x hx1 hx2
        refine ENNReal.ofReal_le_ofReal ?_
        have hne : μ.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx1
        have hu : (μ.rnDeriv ν x).toReal ≤ 1 + δ :=
          ENNReal.toReal_le_of_le_ofReal (by linarith) hx1
        have hl : 1 - δ ≤ (μ.rnDeriv ν x).toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hne).mp hx2
        refine (klFun_le_sq_sub_one ENNReal.toReal_nonneg).trans ?_
        nlinarith
    _ = ENNReal.ofReal (δ ^ 2) := by simp

/-- GAPS 107.75, the single-release KL contraction under local privacy. -/
theorem klDiv_comp_le_of_local_differential_privacy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Kernel X Y) [IsMarkovKernel Q] (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hpriv : IsDifferentiallyPrivate (fun _ _ : X ↦ True) epsilon 0 Q)
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    InformationTheory.klDiv (Q ∘ₘ P₁) (Q ∘ₘ P₂) +
      InformationTheory.klDiv (Q ∘ₘ P₂) (Q ∘ₘ P₁) ≤
      ENNReal.ofReal (4 * (Real.exp epsilon - 1) ^ 2 * totalVariationDistance P₁ P₂ ^ 2) := by
  have hT0 : 0 ≤ totalVariationDistance P₁ P₂ :=
    (abs_nonneg _).trans (abs_measureReal_sub_le_totalVariationDistance P₁ P₂ ∅ MeasurableSet.empty)
  have he1 : 0 ≤ Real.exp epsilon - 1 := by linarith [Real.add_one_le_exp epsilon]
  set δ := (Real.exp epsilon - 1) * totalVariationDistance P₁ P₂
  have hδ : 0 ≤ δ := mul_nonneg he1 hT0
  have h1 := klDiv_le_ofReal_sq_of_abs_measureReal_sub_le (Q ∘ₘ P₁) (Q ∘ₘ P₂) hδ fun A hA ↦
    (abs_measureReal_comp_sub_le_of_local_privacy Q he hpriv P₁ P₂ hA).1
  have h2 := klDiv_le_ofReal_sq_of_abs_measureReal_sub_le (Q ∘ₘ P₂) (Q ∘ₘ P₁) hδ fun A hA ↦ by
    rw [abs_sub_comm]
    exact (abs_measureReal_comp_sub_le_of_local_privacy Q he hpriv P₁ P₂ hA).2
  calc _ ≤ ENNReal.ofReal (δ ^ 2) + ENNReal.ofReal (δ ^ 2) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * δ ^ 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simp only [δ]
      nlinarith [sq_nonneg ((Real.exp epsilon - 1) * totalVariationDistance P₁ P₂)])



end CKSD
