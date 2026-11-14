module

public import CKSD.Inference.Basic


/-!
# Integration identities for sufficient statistics

A sufficient statistic `T` comes with one Markov kernel `K` disintegrating every joint law of
`(T, X)`. This file records the resulting identity `E_θ[g(T) φ] = E_θ[g(T) ∫ φ dK(T)]` for bounded
measurable `g` and `φ`, the common step in the proofs of Basu's theorem (GAPS 101.9) and of Neyman
structure (GAPS 101.49).

## Main results

* `CKSD.integral_comp_mul_eq_integral_comp_mul_integral_kernel`, `CKSD.integral_indicator_comp_mul_eq`.
* `CKSD.integral_comp_eq_integral_integral`: integrals against a mixture `P ∘ₘ Λ`.
* `CKSD.ae_integral_kernel_eq_of_is_boundedly_complete_statistic`: under bounded completeness, a
  bounded function with constant mean has constant conditional mean `∫ φ dK(T)`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CKSD

variable {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]

/-- A bounded measurable real function is integrable for a finite measure. -/
theorem integrable_of_measurable_of_abs_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {f : Y → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound (C := C) hf.aestronglyMeasurable (ae_of_all _ fun y ↦ by
    rw [Real.norm_eq_abs]; exact hC y)

/-- If the joint law of `(T, X)` under `μ` is the law of `T` composed with the Markov kernel `K`,
then `∫ g(T) φ dμ = ∫ g(T) (∫ φ dK(T)) dμ` for bounded measurable `g` and `φ`. -/
theorem integral_comp_mul_eq_integral_comp_mul_integral_kernel (μ : Measure X)
    [IsFiniteMeasure μ] {T : X → S} (hT : Measurable T) (K : Kernel S X) [IsMarkovKernel K]
    (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K)
    {g : S → ℝ} (hg : Measurable g) {Cg : ℝ} (hgb : ∀ s, |g s| ≤ Cg)
    {φ : X → ℝ} (hφ : Measurable φ) {Cφ : ℝ} (hφb : ∀ x, |φ x| ≤ Cφ) :
    ∫ x, g (T x) * φ x ∂μ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ := by
  have hTX : Measurable (fun x ↦ (T x, x)) := hT.prodMk measurable_id
  have hprod : Measurable (fun p : S × X ↦ g p.1 * φ p.2) :=
    (hg.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hbound : ∀ p : S × X, |g p.1 * φ p.2| ≤ Cg * Cφ := fun p ↦ by
    rw [abs_mul]
    exact mul_le_mul (hgb _) (hφb _) (abs_nonneg _) ((abs_nonneg _).trans (hgb p.1))
  have hKint : Measurable (fun s ↦ ∫ y, φ y ∂K s) :=
    (hφ.stronglyMeasurable.integral_kernel (κ := K)).measurable
  calc ∫ x, g (T x) * φ x ∂μ = ∫ p, g p.1 * φ p.2 ∂(μ.map (fun x ↦ (T x, x))) := by
        rw [integral_map hTX.aemeasurable hprod.aestronglyMeasurable]
    _ = ∫ s, ∫ y, g s * φ y ∂K s ∂(μ.map T) := by
        rw [hK, Measure.integral_compProd]
        exact integrable_of_measurable_of_abs_le _ hprod hbound
    _ = ∫ s, g s * ∫ y, φ y ∂K s ∂(μ.map T) := by
        simp_rw [integral_const_mul]
    _ = ∫ x, g (T x) * ∫ y, φ y ∂K (T x) ∂μ := by
        exact integral_map (f := fun s ↦ g s * ∫ y, φ y ∂K s) hT.aemeasurable
          (hg.mul hKint).aestronglyMeasurable

/-- Integration against a mixture `P ∘ₘ Λ` of a Markov kernel: the integral is the average of the
component integrals. -/
theorem integral_comp_eq_integral_integral {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (P : Kernel Θ X) [IsMarkovKernel P] (Λ : Measure Θ) [IsProbabilityMeasure Λ]
    (f : X → ℝ) (hf : Integrable f (P ∘ₘ Λ)) :
    ∫ x, f x ∂(P ∘ₘ Λ) = ∫ θ, ∫ x, f x ∂P θ ∂Λ := by
  rw [← Measure.snd_compProd, Measure.snd, integral_map measurable_snd.aemeasurable]
  · rw [Measure.integral_compProd]
    exact (Measure.integrable_compProd_snd_iff hf.1).2 hf
  · rw [← Measure.snd, Measure.snd_compProd]
    exact hf.1

/-- If the joint law of `(T, X)` under `μ` is `μ.map T ⊗ₘ K`, then `μ` is the mixture of `K`
over the law of `T`. -/
theorem comp_map_eq_of_map_prod_mk_eq_comp_prod (μ : Measure X) [IsFiniteMeasure μ] {T : X → S}
    (hT : Measurable T) (K : Kernel S X) [IsMarkovKernel K]
    (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) : K ∘ₘ μ.map T = μ := by
  rw [← Measure.snd_compProd, ← hK, Measure.snd_map_prodMk hT]
  · exact Measure.map_id
  · exact measurable_id

/-- A real convex function on the line is bounded below by `L 0 - c |t|` for some constant `c`. -/
theorem exists_sub_mul_abs_le_of_convex_on {L : ℝ → ℝ} (hL : ConvexOn ℝ univ L) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t, L 0 - c * |t| ≤ L t := by
  refine ⟨|L 0 - L (-1)| + |L 1 - L 0|, by positivity, fun t ↦ ?_⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := hL.slope_mono_adjacent (mem_univ t) (mem_univ 1) ht zero_lt_one
    rw [div_le_iff₀ (by linarith), sub_zero, div_one] at h
    rw [abs_of_neg ht]
    nlinarith [le_abs_self (L 1 - L 0), abs_nonneg (L 0 - L (-1))]
  · simp
  · have h := hL.slope_mono_adjacent (mem_univ (-1)) (mem_univ t) (by norm_num : (-1 : ℝ) < 0) ht
    rw [le_div_iff₀ (by linarith), sub_zero, sub_neg_eq_add, zero_add, div_one] at h
    rw [abs_of_pos ht]
    nlinarith [neg_abs_le (L 0 - L (-1)), abs_nonneg (L 1 - L 0)]

/-- A set integral over a preimage `T⁻¹ B` as an integral against the indicator of `B` at `T`. -/
theorem set_integral_preimage_eq_integral_indicator_mul (μ : Measure X) {T : X → S}
    (hT : Measurable T) {B : Set S} (hB : MeasurableSet B) (f : X → ℝ) :
    ∫ x in T ⁻¹' B, f x ∂μ = ∫ x, B.indicator 1 (T x) * f x ∂μ := by
  rw [← integral_indicator (hT hB)]
  congr 1
  funext x
  by_cases h : T x ∈ B <;> simp [indicator, h]

/-- The indicator of a set is bounded by one in absolute value. -/
theorem abs_indicator_one_le_one {Y : Type*} (B : Set Y) (y : Y) :
    |B.indicator (1 : Y → ℝ) y| ≤ 1 := by
  by_cases h : y ∈ B
  · simp only [indicator_of_mem h, Pi.one_apply, abs_one, le_refl]
  · simp only [indicator_of_notMem h, abs_zero, zero_le_one]

/-- The bounded-function case of `integral_comp_mul_eq_integral_comp_mul_integral_kernel` with
the indicator of a measurable set of statistic values. -/
theorem integral_indicator_comp_mul_eq (μ : Measure X)
    [IsFiniteMeasure μ] {T : X → S} (hT : Measurable T) (K : Kernel S X) [IsMarkovKernel K]
    (hK : μ.map (fun x ↦ (T x, x)) = μ.map T ⊗ₘ K) {B : Set S} (hB : MeasurableSet B)
    {φ : X → ℝ} (hφ : Measurable φ) {Cφ : ℝ} (hφb : ∀ x, |φ x| ≤ Cφ) :
    ∫ x, B.indicator 1 (T x) * φ x ∂μ =
      ∫ x, B.indicator 1 (T x) * ∫ y, φ y ∂K (T x) ∂μ :=
  integral_comp_mul_eq_integral_comp_mul_integral_kernel μ hT K hK (g := B.indicator 1)
    (measurable_one.indicator hB) (Cg := 1) (abs_indicator_one_le_one B) hφ hφb

/-- For a boundedly complete sufficient statistic `T` with disintegrating kernel `K`, a bounded
measurable `φ` whose expectation is `α` under every parameter satisfies `∫ φ dK(T) = α` almost
surely under every parameter. -/
theorem ae_integral_kernel_eq_of_is_boundedly_complete_statistic {Θ : Type*}
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ)) {T : X → S}
    (hT : Measurable T) (hc : IsBoundedlyCompleteStatistic P T)
    (K : Kernel S X) [IsMarkovKernel K]
    (hK : ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K)
    {φ : X → ℝ} (hφ : Measurable φ) {C : ℝ} (hφb : ∀ x, |φ x| ≤ C) (α : ℝ)
    (hα : ∀ θ, (∫ x, φ x ∂P θ) = α) (θ : Θ) :
    ∀ᵐ x ∂P θ, ∫ y, φ y ∂K (T x) = α := by
  let r : S → ℝ := fun s ↦ ∫ y, φ y ∂K s
  have hr : Measurable r := (hφ.stronglyMeasurable.integral_kernel (κ := K)).measurable
  have hrb : ∀ s, |r s| ≤ C := fun s ↦ by
    have := norm_integral_le_of_norm_le_const (μ := K s) (C := C)
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hφb y)
    simpa [Real.norm_eq_abs, r] using this
  have hzero := hc (fun s ↦ r s - α) (hr.sub measurable_const) ⟨C + |α|, fun s ↦
    (abs_sub _ _).trans (by linarith [hrb s])⟩ (fun θ' ↦ by
      have := hP θ'
      have h1 := integral_indicator_comp_mul_eq (P θ') hT K (hK θ') MeasurableSet.univ hφ hφb
      simp only [indicator_univ, Pi.one_apply, one_mul] at h1
      rw [integral_sub (f := fun x ↦ r (T x))
        (integrable_of_measurable_of_abs_le _ (hr.comp hT) fun x ↦ hrb (T x))
        (integrable_const α), ← h1, hα, integral_const]
      simp) θ
  exact hzero.mono fun x hx ↦ sub_eq_zero.1 hx

end CKSD
