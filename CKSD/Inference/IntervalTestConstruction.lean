module

public import TauCeti.Probability.Quantile
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic


/-!
# Construction of two-sided interval tests

Real-variable ingredients of the two-sided interval tests in one-parameter exponential families
(Lehmann–Romano, *Testing Statistical Hypotheses*, Section 3.7).

## Main results

* `CKSD.exists_interval_weight_integral_eq_set_integral_quantile`: for a real probability law `μ`
  and levels `0 < a < b < 1`, a randomized interval weight in the quantiles `Q a ≤ Q b`
  integrates every `μ`-integrable function like the window `(a, b)` of levels.
* `CKSD.exists_set_integral_comp_quantile_eq_mul`: for a nondecreasing integrable `f` that is not
  almost everywhere constant, some window `(a, a + α)` of levels has
  `∫_{(a, a + α)} f (Q v) dv = α ∫ f dμ` (intermediate value theorem).
* `CKSD.exists_mul_exp_add_mul_exp_le_one_iff`: for exponents `β₁ < 0 < β₂` and `c₁ ≤ c₂`, a
  positive combination `A e^{β₁ t} + B e^{β₂ t}` is at most `1` on `[c₁, c₂]` and at least `1`
  off `(c₁, c₂)`.

## Implementation notes

The window identities use inverse transform sampling for the quantile function
(TauCeti's `MeasureTheory.Measure.measurePreserving_quantile` and
`MeasureTheory.Measure.monotoneOn_quantile`). On a level set `{Q = c}` of the quantile function
the randomization `γ` is the fraction of the level set inside the window.
-/
@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

/-- On a level set `S = {v ∈ (0, 1) | Q v = c}` of the quantile function, the constant weight
`γ = |S ∩ (a, b)| / |S|` reproduces the integral over the window `(a, b)`. -/
private theorem set_integral_level_set_quantile (μ : Measure ℝ) (a b c : ℝ) (ψ : ℝ → ℝ) :
    ∫ v in Ioo 0 1 ∩ μ.quantile ⁻¹' {c},
        volume.real (Ioo 0 1 ∩ μ.quantile ⁻¹' {c} ∩ Ioo a b) /
          volume.real (Ioo 0 1 ∩ μ.quantile ⁻¹' {c}) * ψ (μ.quantile v) =
      ∫ v in Ioo 0 1 ∩ μ.quantile ⁻¹' {c}, (Ioo a b).indicator (fun v ↦ ψ (μ.quantile v)) v := by
  set S := Ioo 0 1 ∩ μ.quantile ⁻¹' {c}
  have hS : MeasurableSet S :=
    measurableSet_Ioo.inter (measurable_quantile μ (measurableSet_singleton c))
  have hSfin : volume S ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (by simp)).ne
  rw [setIntegral_indicator measurableSet_Ioo]
  rw [setIntegral_congr_fun hS (g := fun _ ↦ volume.real (S ∩ Ioo a b) / volume.real S * ψ c)
      (fun v hv ↦ by simp only [show μ.quantile v = c from hv.2]),
    setIntegral_congr_fun (hS.inter measurableSet_Ioo) (g := fun _ ↦ ψ c)
      (fun v hv ↦ by simp only [show μ.quantile v = c from hv.1.2]),
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]
  rcases eq_or_ne (volume.real S) 0 with h0 | h0
  · have : volume.real (S ∩ Ioo a b) = 0 := le_antisymm
      (h0 ▸ measureReal_mono inter_subset_left hSfin) measureReal_nonneg
    simp [h0, this]
  · field_simp

/-- **Window tests.** For a probability law `μ` on `ℝ` and levels `0 < a < b < 1`, there is an
interval weight `w` (equal to `1` strictly between `c₁ ≤ c₂`, to `γᵢ ∈ [0, 1]` at `cᵢ`, and to `0`
elsewhere) with `∫ w ψ dμ = ∫_{(a, b)} ψ (Q v) dv` for every `μ`-integrable `ψ`, where `Q` is the
quantile function of `μ`. The endpoints are `cᵢ = Q a, Q b`. -/
theorem exists_interval_weight_integral_eq_set_integral_quantile (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ c₁ c₂ γ₁ γ₂ : ℝ, c₁ ≤ c₂ ∧ γ₁ ∈ Icc 0 1 ∧ γ₂ ∈ Icc 0 1 ∧
      ∀ ψ : ℝ → ℝ, Integrable ψ μ →
        ∫ t, (if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ₁ else if t = c₂ then γ₂ else 0) *
          ψ t ∂μ = ∫ v in Ioo a b, ψ (μ.quantile v) := by
  set Q := μ.quantile with hQ
  have hQm : Measurable Q := measurable_quantile μ
  have ha1 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb1 : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  set c₁ := Q a with hc₁
  set c₂ := Q b with hc₂
  have hc : c₁ ≤ c₂ := monotoneOn_quantile μ ha1 hb1 hab.le
  set S : ℝ → Set ℝ := fun c ↦ Ioo 0 1 ∩ Q ⁻¹' {c} with hSdef
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    measurableSet_Ioo.inter (hQm (measurableSet_singleton c))
  set γ : ℝ → ℝ := fun c ↦ volume.real (S c ∩ Ioo a b) / volume.real (S c) with hγdef
  have hγ : ∀ c, γ c ∈ Icc 0 1 := fun c ↦ ⟨div_nonneg measureReal_nonneg measureReal_nonneg,
    div_le_one_of_le₀ (measureReal_mono inter_subset_left
      ((measure_mono inter_subset_left).trans_lt (by simp)).ne) measureReal_nonneg⟩
  refine ⟨c₁, c₂, γ c₁, γ c₂, hc, hγ _, hγ _, fun ψ hψ ↦ ?_⟩
  set I : ℝ → ℝ := fun t ↦
    if c₁ < t ∧ t < c₂ then 1 else if t = c₁ then γ c₁ else if t = c₂ then γ c₂ else 0 with hI
  have hIm : Measurable I := by
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const
      (Measurable.ite ?_ measurable_const measurable_const))
    · exact measurableSet_Ioo
    · exact measurableSet_singleton _
    · exact measurableSet_singleton _
  have hIb : ∀ t, ‖I t‖ ≤ 1 := fun t ↦ by
    simp only [I]
    split_ifs <;> simp [abs_of_nonneg (hγ _).1, (hγ _).2]
  have hψQ : IntegrableOn (fun v ↦ ψ (Q v)) (Ioo 0 1) :=
    ((measurePreserving_quantile μ).integrable_comp hψ.1).2 hψ
  have hmap : ∫ t, I t * ψ t ∂μ = ∫ v in Ioo 0 1, I (Q v) * ψ (Q v) := by
    have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1)) hQm.aemeasurable
      (f := fun t ↦ I t * ψ t)
      (by rw [map_quantile_volume_Ioo μ]; exact hIm.aestronglyMeasurable.mul hψ.1)
    rwa [map_quantile_volume_Ioo μ] at h
  have hwin : ∫ v in Ioo a b, ψ (Q v) =
      ∫ v in Ioo 0 1, (Ioo a b).indicator (fun v ↦ ψ (Q v)) v := by
    rw [setIntegral_indicator measurableSet_Ioo, Ioo_inter_Ioo, max_eq_right ha.le,
      min_eq_right hb.le]
  rw [hmap, hwin]
  have hint1 : IntegrableOn (fun v ↦ I (Q v) * ψ (Q v)) (Ioo 0 1) :=
    hψQ.bdd_mul (hIm.comp hQm).aestronglyMeasurable (ae_of_all _ fun v ↦ hIb (Q v))
  have hint2 : IntegrableOn ((Ioo a b).indicator fun v ↦ ψ (Q v)) (Ioo 0 1) :=
    hψQ.indicator measurableSet_Ioo
  have ht : MeasurableSet (Q ⁻¹' {c₁, c₂}) :=
    hQm (measurableSet_insert.2 (measurableSet_singleton _))
  rw [← integral_inter_add_sdiff ht hint1, ← integral_inter_add_sdiff ht hint2]
  congr 1
  · -- On the two level sets the weights `γᵢ` reproduce the window.
    have hIc₁ : I c₁ = γ c₁ := by simp [I]
    rcases hc.lt_or_eq with hlt | heq
    · have hIc₂ : I c₂ = γ c₂ := by simp [I, hlt.ne']
      have hsplit : Ioo 0 1 ∩ Q ⁻¹' {c₁, c₂} = S c₁ ∪ S c₂ := by
        ext v; simp only [S, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff,
          mem_union]; tauto
      have hdisj : Disjoint (S c₁) (S c₂) := Set.disjoint_left.2 fun v h1 h2 ↦
        hlt.ne (h1.2.symm.trans h2.2)
      rw [hsplit, setIntegral_union hdisj (hSm _) (hint1.mono_set (by simp [S]))
          (hint1.mono_set (by simp [S])),
        setIntegral_union hdisj (hSm _) (hint2.mono_set (by simp [S]))
          (hint2.mono_set (by simp [S]))]
      congr 1
      · rw [← set_integral_level_set_quantile μ a b c₁ ψ]
        refine setIntegral_congr_fun (hSm _) fun v hv ↦ ?_
        change I (Q v) * ψ (Q v) = γ c₁ * ψ (Q v)
        rw [show Q v = c₁ from hv.2, hIc₁]
      · rw [← set_integral_level_set_quantile μ a b c₂ ψ]
        refine setIntegral_congr_fun (hSm _) fun v hv ↦ ?_
        change I (Q v) * ψ (Q v) = γ c₂ * ψ (Q v)
        rw [show Q v = c₂ from hv.2, hIc₂]
    · have hsplit : Ioo 0 1 ∩ Q ⁻¹' {c₁, c₂} = S c₁ := by
        ext v; simp only [S, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, heq,
          or_self]
      rw [hsplit, ← set_integral_level_set_quantile μ a b c₁ ψ]
      refine setIntegral_congr_fun (hSm _) fun v hv ↦ ?_
      change I (Q v) * ψ (Q v) = γ c₁ * ψ (Q v)
      rw [show Q v = c₁ from hv.2, hIc₁]
  · -- Off the level sets the weight is the indicator of the window.
    refine setIntegral_congr_fun (measurableSet_Ioo.diff ht) fun v hv ↦ ?_
    obtain ⟨hv01, hvc⟩ := hv
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, not_or] at hvc
    simp only [I, hvc.1, hvc.2, ite_false, indicator]
    rcases le_or_gt v a with hva | hva
    · have : Q v ≤ c₁ := monotoneOn_quantile μ hv01 ha1 hva
      have h1 : ¬ (c₁ < Q v ∧ Q v < c₂) := fun h ↦ (lt_irrefl _ (h.1.trans_le this))
      simp [h1, hva.not_gt]
    rcases le_or_gt b v with hvb | hvb
    · have : c₂ ≤ Q v := monotoneOn_quantile μ hb1 hv01 hvb
      have h1 : ¬ (c₁ < Q v ∧ Q v < c₂) := fun h ↦ (lt_irrefl _ (h.2.trans_le this))
      simp [h1, hvb.not_gt]
    · have h1 : c₁ < Q v := lt_of_le_of_ne (monotoneOn_quantile μ ha1 hv01 hva.le)
        (Ne.symm hvc.1)
      have h2 : Q v < c₂ := lt_of_le_of_ne (monotoneOn_quantile μ hv01 hb1 hvb.le) hvc.2
      simp [h1, h2, hva, hvb]

/-- For `h` integrable on `(0, 1)` and `0 ≤ x ≤ y ≤ 1`, the interval integral of the extension
of `h` by zero over `[x, y]` is the integral of `h` over `(x, y)`. -/
private theorem interval_integral_indicator_ioo_eq {h : ℝ → ℝ} {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : y ≤ 1) :
    ∫ v in x..y, (Ioo 0 1).indicator h v = ∫ v in Ioo x y, h v := by
  rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo,
    setIntegral_indicator measurableSet_Ioo, inter_eq_left.2 (Ioo_subset_Ioo hx hy)]

/-- Splitting the integral over `(0, 1)` at a level `β ∈ [0, 1]`. -/
private theorem set_integral_ioo_split {h : ℝ → ℝ} (hh : IntegrableOn h (Ioo 0 1)) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∫ v in Ioo 0 1, h v = (∫ v in Ioo 0 β, h v) + ∫ v in Ioo β 1, h v := by
  have hi : ∀ x y, IntervalIntegrable ((Ioo 0 1).indicator h) volume x y := fun x y ↦
    ((integrable_indicator_iff measurableSet_Ioo).2 hh).intervalIntegrable
  rw [← interval_integral_indicator_ioo_eq le_rfl zero_le_one le_rfl,
    ← interval_integral_indicator_ioo_eq le_rfl hβ0 hβ1,
    ← interval_integral_indicator_ioo_eq hβ0 hβ1 le_rfl,
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]

/-- For `h` monotone on `(0, 1)` and not almost everywhere constant there, the average of `h`
over `(0, β)` is strictly below its average over `(0, 1)`. -/
private theorem set_integral_ioo_lt_mul {h : ℝ → ℝ} (hh : IntegrableOn h (Ioo 0 1))
    (hmono : MonotoneOn h (Ioo 0 1))
    (hnc : ¬ ∃ c, ∀ᵐ v ∂volume.restrict (Ioo (0 : ℝ) 1), h v = c) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∫ v in Ioo 0 β, h v < β * ∫ v in Ioo 0 1, h v := by
  set c := h β
  have h1 : IntegrableOn h (Ioo 0 β) := hh.mono_set (Ioo_subset_Ioo le_rfl hβ.2.le)
  have h2 : IntegrableOn h (Ioo β 1) := hh.mono_set (Ioo_subset_Ioo hβ.1.le le_rfl)
  set A := ∫ v in Ioo 0 β, (c - h v) with hAdef
  set B := ∫ v in Ioo β 1, (h v - c) with hBdef
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioo fun v hv ↦
    sub_nonneg.2 (hmono ⟨hv.1, hv.2.trans hβ.2⟩ hβ hv.2.le)
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo fun v hv ↦
    sub_nonneg.2 (hmono hβ ⟨hβ.1.trans hv.1, hv.2⟩ hv.1.le)
  have hA : A = β * c - ∫ v in Ioo 0 β, h v := by
    rw [hAdef, integral_sub (integrableOn_const (by simp)) h1, setIntegral_const]
    simp [Real.volume_real_Ioo_of_le hβ.1.le]
  have hB : B = (∫ v in Ioo β 1, h v) - (1 - β) * c := by
    rw [hBdef, integral_sub h2 (integrableOn_const (by simp)), setIntegral_const]
    simp [Real.volume_real_Ioo_of_le hβ.2.le]
  rw [set_integral_ioo_split hh hβ.1.le hβ.2.le]
  by_contra hle
  replace hle := not_lt.1 hle
  have hAB : β * B + (1 - β) * A = 0 := by
    have := hβ.1; have := hβ.2
    nlinarith
  have hA' : A = 0 := by nlinarith [hβ.1, hβ.2, mul_nonneg hβ.1.le hB0]
  have hB' : B = 0 := by nlinarith [hβ.1, hβ.2, mul_nonneg (sub_nonneg.2 hβ.2.le) hA0]
  have hae1 : ∀ᵐ v ∂volume.restrict (Ioo (0 : ℝ) β), h v = c := by
    have := (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun v hv ↦
        sub_nonneg.2 (hmono ⟨hv.1, hv.2.trans hβ.2⟩ hβ hv.2.le)))
      ((integrableOn_const (by simp)).sub h1)).1 hA'
    filter_upwards [this] with v hv
    simp only [Pi.zero_apply, sub_eq_zero] at hv
    exact hv.symm
  have hae2 : ∀ᵐ v ∂volume.restrict (Ioo β (1 : ℝ)), h v = c := by
    have := (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun v hv ↦
        sub_nonneg.2 (hmono hβ ⟨hβ.1.trans hv.1, hv.2⟩ hv.1.le)))
      (h2.sub (integrableOn_const (by simp)))).1 hB'
    filter_upwards [this] with v hv
    simp only [Pi.zero_apply, sub_eq_zero] at hv
    exact hv
  refine hnc ⟨c, ?_⟩
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo 0 β ∪ Ioo β 1 ∪ {β} := fun v hv ↦ by
    rcases lt_trichotomy v β with h | h | h
    · exact Or.inl (Or.inl ⟨hv.1, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨h, hv.2⟩)
  refine ae_restrict_of_ae_restrict_of_subset hsub ?_
  rw [ae_restrict_union_iff, ae_restrict_union_iff]
  exact ⟨⟨hae1, hae2⟩, by simp [c]⟩

/-- **Two-point size selection.** For a probability law `μ` on `ℝ`, a nondecreasing `μ`-integrable
`f` that is not `μ`-almost everywhere constant, and `α ∈ (0, 1)`, some window `(a, a + α)` of
levels inside `(0, 1)` satisfies `∫_{(a, a + α)} f (Q v) dv = α ∫ f dμ`, where `Q` is the quantile
function of `μ`. The proof is the intermediate value theorem: the window integral is continuous
in `a`, below `α ∫ f dμ` at `a = 0` and above it at `a = 1 - α`. -/
theorem exists_set_integral_comp_quantile_eq_mul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Monotone f) (hfi : Integrable f μ) (hnc : ¬ ∃ c, ∀ᵐ t ∂μ, f t = c)
    {α : ℝ} (hα : α ∈ Ioo 0 1) :
    ∃ a, 0 < a ∧ a + α < 1 ∧
      ∫ v in Ioo a (a + α), f (μ.quantile v) = α * ∫ t, f t ∂μ := by
  set Q := μ.quantile
  set h : ℝ → ℝ := fun v ↦ f (Q v) with hhdef
  have hmp := measurePreserving_quantile μ
  have hh : IntegrableOn h (Ioo 0 1) := (hmp.integrable_comp hfi.1).2 hfi
  have hmono : MonotoneOn h (Ioo 0 1) := hf.comp_monotoneOn (monotoneOn_quantile μ)
  have hm : ∫ t, f t ∂μ = ∫ v in Ioo 0 1, h v := by
    have := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1)) hmp.measurable.aemeasurable
      (f := f) (by rw [hmp.map_eq]; exact hfi.1)
    rwa [hmp.map_eq] at this
  have hnc' : ¬ ∃ c, ∀ᵐ v ∂volume.restrict (Ioo (0 : ℝ) 1), h v = c := by
    rintro ⟨c, hc⟩
    refine hnc ⟨c, ?_⟩
    rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable (p := fun t ↦ f t = c)
      (hf.measurable (measurableSet_singleton c))]
    exact hc
  set h' := (Ioo (0 : ℝ) 1).indicator h
  have hi : ∀ x y, IntervalIntegrable h' volume x y := fun x y ↦
    ((integrable_indicator_iff measurableSet_Ioo).2 hh).intervalIntegrable
  set H : ℝ → ℝ := fun u ↦ (∫ v in (0 : ℝ)..(u + α), h' v) - ∫ v in (0 : ℝ)..u, h' v
  have hHc : Continuous H :=
    ((intervalIntegral.continuous_primitive hi 0).comp (continuous_id.add continuous_const)).sub
      (intervalIntegral.continuous_primitive hi 0)
  have hHeq : ∀ u, 0 ≤ u → u + α ≤ 1 → H u = ∫ v in Ioo u (u + α), h v := fun u hu hu1 ↦ by
    simp only [H]
    rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _),
      interval_integral_indicator_ioo_eq hu (by linarith [hα.1]) hu1]
  have hH0 : H 0 < α * ∫ t, f t ∂μ := by
    rw [hHeq 0 le_rfl (by linarith [hα.2]), zero_add, hm]
    exact set_integral_ioo_lt_mul hh hmono hnc' hα
  have hH1 : α * ∫ t, f t ∂μ < H (1 - α) := by
    rw [hHeq (1 - α) (by linarith [hα.2]) (by linarith), sub_add_cancel, hm]
    have hβ : 1 - α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
    have h1 := set_integral_ioo_lt_mul hh hmono hnc' hβ
    have h2 := set_integral_ioo_split hh hβ.1.le hβ.2.le
    linarith
  obtain ⟨a, ha, hHa⟩ := intermediate_value_Ioo (by linarith [hα.2] : (0 : ℝ) ≤ 1 - α)
    hHc.continuousOn ⟨hH0, hH1⟩
  refine ⟨a, ha.1, by linarith [ha.2], ?_⟩
  rw [← hHeq a ha.1.le (by linarith [ha.2])]
  exact hHa

/-- Convexity of `t ↦ A e^{β₁ t} + B e^{β₂ t}` for `A, B ≥ 0`, in two-point form. -/
private theorem mul_exp_add_mul_exp_convex {A B β₁ β₂ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    A * Real.exp (β₁ * (a * x + b * y)) + B * Real.exp (β₂ * (a * x + b * y)) ≤
      a * (A * Real.exp (β₁ * x) + B * Real.exp (β₂ * x)) +
        b * (A * Real.exp (β₁ * y) + B * Real.exp (β₂ * y)) := by
  have key : ∀ β : ℝ, Real.exp (β * (a * x + b * y)) ≤
      a * Real.exp (β * x) + b * Real.exp (β * y) := fun β ↦ by
    have := convexOn_exp.2 (mem_univ (β * x)) (mem_univ (β * y)) ha hb hab
    simp only [smul_eq_mul] at this
    calc Real.exp (β * (a * x + b * y)) = Real.exp (a * (β * x) + b * (β * y)) := by ring_nf
      _ ≤ _ := this
  nlinarith [mul_le_mul_of_nonneg_left (key β₁) hA, mul_le_mul_of_nonneg_left (key β₂) hB]

/-- **Two-sided exponential thresholds.** For exponents `β₁ < 0 < β₂` and `c₁ ≤ c₂` there are
`A, B > 0` such that `g t = A e^{β₁ t} + B e^{β₂ t}` satisfies `g ≤ 1` on `[c₁, c₂]` and `g ≥ 1`
off `(c₁, c₂)`. For `c₁ < c₂` the constants solve `g c₁ = g c₂ = 1`; for `c₁ = c₂ = c` they make
`g` tangent to `1` at `c`. -/
theorem exists_mul_exp_add_mul_exp_le_one_iff {β₁ β₂ c₁ c₂ : ℝ} (hβ₁ : β₁ < 0) (hβ₂ : 0 < β₂)
    (hc : c₁ ≤ c₂) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t,
      (t ∈ Icc c₁ c₂ → A * Real.exp (β₁ * t) + B * Real.exp (β₂ * t) ≤ 1) ∧
      (t ∉ Ioo c₁ c₂ → 1 ≤ A * Real.exp (β₁ * t) + B * Real.exp (β₂ * t)) := by
  rcases hc.lt_or_eq with hlt | heq
  · set D := Real.exp (β₁ * c₁) * Real.exp (β₂ * c₂) - Real.exp (β₂ * c₁) * Real.exp (β₁ * c₂)
    have hD : 0 < D := by
      simp only [D, ← Real.exp_add, sub_pos, Real.exp_lt_exp]
      nlinarith
    set A := (Real.exp (β₂ * c₂) - Real.exp (β₂ * c₁)) / D
    set B := (Real.exp (β₁ * c₁) - Real.exp (β₁ * c₂)) / D
    have hA : 0 < A := div_pos (sub_pos.2 (Real.exp_lt_exp.2 (by nlinarith))) hD
    have hB : 0 < B := div_pos (sub_pos.2 (Real.exp_lt_exp.2 (by nlinarith))) hD
    set g : ℝ → ℝ := fun t ↦ A * Real.exp (β₁ * t) + B * Real.exp (β₂ * t)
    have hg₁ : g c₁ = 1 := by
      simp only [g, A, B]; field_simp; simp only [D]; ring_nf
    have hg₂ : g c₂ = 1 := by
      simp only [g, A, B]; field_simp; simp only [D]; ring_nf
    have hconv := mul_exp_add_mul_exp_convex (β₁ := β₁) (β₂ := β₂) hA.le hB.le
    have hd : 0 < c₂ - c₁ := sub_pos.2 hlt
    refine ⟨A, B, hA, hB, fun t ↦ ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩⟩
    · have h := hconv c₁ c₂ ((c₂ - t) / (c₂ - c₁)) ((t - c₁) / (c₂ - c₁))
        (div_nonneg (by linarith [ht.2]) hd.le) (div_nonneg (by linarith [ht.1]) hd.le)
        (by field_simp; ring)
      have ht' : (c₂ - t) / (c₂ - c₁) * c₁ + (t - c₁) / (c₂ - c₁) * c₂ = t := by
        field_simp; ring
      rw [ht'] at h
      change g t ≤ _ * g c₁ + _ * g c₂ at h
      rw [hg₁, hg₂] at h
      calc g t ≤ _ := h
        _ = 1 := by field_simp; ring
    · simp only [mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with ht | ht
      · rcases ht.lt_or_eq with ht | ht
        · have hd' : 0 < c₂ - t := by linarith
          have h := hconv t c₂ ((c₂ - c₁) / (c₂ - t)) ((c₁ - t) / (c₂ - t))
            (div_nonneg hd.le hd'.le) (div_nonneg (by linarith) hd'.le) (by field_simp; ring)
          have ht' : (c₂ - c₁) / (c₂ - t) * t + (c₁ - t) / (c₂ - t) * c₂ = c₁ := by
            field_simp; ring
          rw [ht'] at h
          change g c₁ ≤ _ * g t + _ * g c₂ at h
          rw [hg₁, hg₂] at h
          have ha : 0 < (c₂ - c₁) / (c₂ - t) := div_pos hd hd'
          have hsum : (c₂ - c₁) / (c₂ - t) + (c₁ - t) / (c₂ - t) = 1 := by field_simp; ring
          change 1 ≤ g t
          nlinarith
        · rw [ht]; exact hg₁.ge
      · rcases ht.lt_or_eq with ht | ht
        · have hd' : 0 < t - c₁ := by linarith
          have h := hconv c₁ t ((t - c₂) / (t - c₁)) ((c₂ - c₁) / (t - c₁))
            (div_nonneg (by linarith) hd'.le) (div_nonneg hd.le hd'.le) (by field_simp; ring)
          have ht' : (t - c₂) / (t - c₁) * c₁ + (c₂ - c₁) / (t - c₁) * t = c₂ := by
            field_simp; ring
          rw [ht'] at h
          change g c₂ ≤ _ * g c₁ + _ * g t at h
          rw [hg₁, hg₂] at h
          have hb : 0 < (c₂ - c₁) / (t - c₁) := div_pos hd hd'
          have hsum : (t - c₂) / (t - c₁) + (c₂ - c₁) / (t - c₁) = 1 := by field_simp; ring
          change 1 ≤ g t
          nlinarith
        · rw [← ht]; exact hg₂.ge
  · subst heq
    have hd : 0 < β₂ - β₁ := by linarith
    set p := β₂ / (β₂ - β₁)
    set q := -β₁ / (β₂ - β₁)
    have hp : 0 < p := div_pos hβ₂ hd
    have hq : 0 < q := div_pos (by linarith) hd
    have hpq : p + q = 1 := by simp only [p, q]; field_simp; ring
    have hpq0 : p * β₁ + q * β₂ = 0 := by simp only [p, q]; field_simp; ring
    refine ⟨p * Real.exp (-(β₁ * c₁)), q * Real.exp (-(β₂ * c₁)), by positivity, by positivity,
      fun t ↦ ⟨fun ht ↦ ?_, fun _ ↦ ?_⟩⟩
    · obtain rfl : t = c₁ := le_antisymm ht.2 ht.1
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      simp [hpq]
    · have := convexOn_exp.2 (mem_univ (β₁ * (t - c₁))) (mem_univ (β₂ * (t - c₁))) hp.le hq.le
        hpq
      simp only [smul_eq_mul] at this
      have h0 : p * (β₁ * (t - c₁)) + q * (β₂ * (t - c₁)) = 0 := by
        linear_combination (t - c₁) * hpq0
      rw [h0, Real.exp_zero] at this
      calc (1 : ℝ) ≤ _ := this
        _ = _ := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          ring_nf

end CKSD
