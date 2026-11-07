module

public import CKSD.Inference.Basic
public import CKSD.Inference.Sufficiency
public import CKSD.Inference.Density

/-!
# Inference: InvariantTesting

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.47: generalized Neyman–Pearson comparison, with signed multipliers. -/
theorem integral_le_of_generalized_neyman_pearson {m : ℕ} (μ : Measure X) (f₀ : X → ℝ)
    (f : Fin m → X → ℝ) (k : Fin m → ℝ) (hf₀ : Integrable f₀ μ)
    (hf : ∀ i, Integrable (f i) μ) (φ ψ : X → ℝ)
    (hφ : IsStatisticalTest φ) (hψ : IsStatisticalTest ψ)
    (hthreshold : ∀ᵐ x ∂μ, ((∑ i, k i * f i x) < f₀ x → φ x = 1) ∧
      (f₀ x < (∑ i, k i * f i x) → φ x = 0))
    (hconstraints : ∀ i, k i * (∫ x, ψ x * f i x ∂μ) ≤
      k i * (∫ x, φ x * f i x ∂μ)) :
    (∫ x, ψ x * f₀ x ∂μ) ≤ ∫ x, φ x * f₀ x ∂μ := by
  have hmul (g : X → ℝ) (hg : Integrable g μ) (a : X → ℝ)
      (ha : IsStatisticalTest a) : Integrable (fun x ↦ a x * g x) μ := by
    apply hg.bdd_mul (c := 1) ha.1.aestronglyMeasurable
    exact ae_of_all μ fun x ↦ by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(ha.2 x).1], (ha.2 x).2⟩
  have hiφ₀ := hmul f₀ hf₀ φ hφ
  have hiψ₀ := hmul f₀ hf₀ ψ hψ
  have hiφ (i : Fin m) := hmul (f i) (hf i) φ hφ
  have hiψ (i : Fin m) := hmul (f i) (hf i) ψ hψ
  have hi (i : Fin m) : Integrable (fun x ↦ k i * (ψ x * f i x - φ x * f i x)) μ :=
    ((hiψ i).sub (hiφ i)).const_mul (k i)
  have hpoint : ∀ᵐ x ∂μ, ψ x * f₀ x - φ x * f₀ x ≤
      ∑ i, k i * (ψ x * f i x - φ x * f i x) := by
    filter_upwards [hthreshold] with x ht
    have hprod : (ψ x - φ x) * (f₀ x - ∑ i, k i * f i x) ≤ 0 := by
      rcases lt_trichotomy (∑ i, k i * f i x) (f₀ x) with h | h | h
      · rw [ht.1 h]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hψ.2 x).2]) (by linarith)
      · simp [h]
      · rw [ht.2 h]
        exact mul_nonpos_of_nonneg_of_nonpos (by simpa using (hψ.2 x).1) (by linarith)
    have hsum : (∑ i, k i * (ψ x * f i x - φ x * f i x)) =
        (ψ x - φ x) * ∑ i, k i * f i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    nlinarith [hprod]
  have hmono := integral_mono_ae (hiψ₀.sub hiφ₀)
    (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)) hpoint
  have hleft : (∫ x, ψ x * f₀ x - φ x * f₀ x ∂μ) =
      (∫ x, ψ x * f₀ x ∂μ) - ∫ x, φ x * f₀ x ∂μ := by
    simpa only [Pi.sub_apply] using integral_sub hiψ₀ hiφ₀
  have hterm (i : Fin m) :
      (∫ x, k i * (ψ x * f i x - φ x * f i x) ∂μ) =
        k i * ((∫ x, ψ x * f i x ∂μ) - ∫ x, φ x * f i x ∂μ) := by
    rw [integral_const_mul]
    congr 1
    simpa only [Pi.sub_apply] using integral_sub (hiψ i) (hiφ i)
  have hright : (∫ x, ∑ i, k i * (ψ x * f i x - φ x * f i x) ∂μ) ≤ 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
    simp_rw [hterm]
    apply Finset.sum_nonpos
    intro i _
    nlinarith [hconstraints i]
  simp only [Pi.sub_apply] at hmono
  rw [hleft] at hmono
  linarith

/-- On `|η - η₀| < ε`, the derivative factor `|t| e^{η t}` is dominated by the two exponentials at
`η₀ ± 2ε`. -/
theorem abs_mul_exp_le_of_abs_sub_lt {η η₀ ε : ℝ} (hε : 0 < ε) (hη : |η - η₀| < ε) (t : ℝ) :
    |t| * Real.exp (η * t) ≤
      (Real.exp ((η₀ + 2 * ε) * t) + Real.exp ((η₀ - 2 * ε) * t)) / ε := by
  rw [le_div_iff₀ hε]
  have h1 : ε * |t| ≤ Real.exp (ε * |t|) := by
    linarith [Real.add_one_le_exp (ε * |t|)]
  have h2 : Real.exp (η * t) * Real.exp (ε * |t|) ≤
      Real.exp ((η₀ + 2 * ε) * t) + Real.exp ((η₀ - 2 * ε) * t) := by
    rw [← Real.exp_add]
    rw [abs_lt] at hη
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      have : η * t + ε * t ≤ (η₀ + 2 * ε) * t := by nlinarith
      exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_neg ht]
      have : η * t + ε * -t ≤ (η₀ - 2 * ε) * t := by nlinarith
      exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  calc |t| * Real.exp (η * t) * ε = Real.exp (η * t) * (ε * |t|) := by ring
    _ ≤ Real.exp (η * t) * Real.exp (ε * |t|) := by gcongr
    _ ≤ _ := h2

/-- Differentiation under the integral sign for a bounded multiple of an exponential family
integrand, at an interior point of the Laplace-integrability set. -/
theorem hasDerivAt_integral_mul_exp (μ : Measure X)
    (T h g : X → ℝ) (hT : Measurable T) (hh : Measurable h) (hpos : ∀ x, 0 ≤ h x)
    (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) (U : Set ℝ) (hU : IsOpen U)
    (hint : ∀ η ∈ U, Integrable (fun x ↦ h x * Real.exp (η * T x)) μ) (η₀ : ℝ) (hη₀ : η₀ ∈ U) :
    Integrable (fun x ↦ g x * h x * T x * Real.exp (η₀ * T x)) μ ∧
      HasDerivAt (fun η ↦ ∫ x, g x * h x * Real.exp (η * T x) ∂μ)
        (∫ x, g x * h x * T x * Real.exp (η₀ * T x) ∂μ) η₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU η₀ hη₀
  set ε := δ / 3 with hεdef
  have hε : 0 < ε := by positivity
  have hp : η₀ + 2 * ε ∈ U := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hm : η₀ - 2 * ε ∈ U := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hbint : Integrable (fun x ↦ (h x * Real.exp ((η₀ + 2 * ε) * T x) +
      h x * Real.exp ((η₀ - 2 * ε) * T x)) / ε) μ :=
    ((hint _ hp).add (hint _ hm)).div_const ε
  have hgx : ∀ η, AEStronglyMeasurable (fun x ↦ g x * h x * Real.exp (η * T x)) μ :=
    fun η ↦ (by fun_prop : Measurable fun x ↦ g x * h x * Real.exp (η * T x)).aestronglyMeasurable
  have hF0 : Integrable (fun x ↦ g x * h x * Real.exp (η₀ * T x)) μ := by
    refine (hint η₀ hη₀).mono' (hgx η₀) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hpos x), abs_of_pos (Real.exp_pos _),
      mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (hpos x) (Real.exp_pos _).le) (hgb x)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun η x ↦ g x * h x * T x * Real.exp (η * T x)) (Metric.ball_mem_nhds η₀ hε)
    (Eventually.of_forall hgx) hF0
    (by fun_prop : Measurable fun x ↦ g x * h x * T x * Real.exp (η₀ * T x)).aestronglyMeasurable
    (ae_of_all _ fun x η hη ↦ ?_) hbint (ae_of_all _ fun x η _ ↦ ?_)
  · rw [Metric.mem_ball, Real.dist_eq] at hη
    have hb := abs_mul_exp_le_of_abs_sub_lt hε hη (T x)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hpos x),
      abs_of_pos (Real.exp_pos _)]
    calc |g x| * h x * |T x| * Real.exp (η * T x) ≤ 1 * h x * (|T x| * Real.exp (η * T x)) := by
          rw [mul_assoc (|g x| * h x)]
          have := hpos x
          gcongr
          exact hgb x
      _ ≤ h x * ((Real.exp ((η₀ + 2 * ε) * T x) + Real.exp ((η₀ - 2 * ε) * T x)) / ε) := by
          rw [one_mul]; gcongr; exact hpos x
      _ = _ := by ring
  · have h1 : HasDerivAt (fun η ↦ η * T x) (T x) η := by
      simpa using (hasDerivAt_id η).mul_const (T x)
    convert h1.exp.const_mul (g x * h x) using 1
    ring


/-- A nonnegative multiple of `t ↦ exp (d t)` lies below its chord over `[c₁, c₂]` and above the
extension of that chord outside the open interval. -/
theorem exists_chord_of_const_mul_exp {a d c₁ c₂ : ℝ} (ha : 0 ≤ a) (hc : c₁ < c₂) :
    ∃ k₀ k₁ : ℝ, ∀ t : ℝ, (c₁ ≤ t → t ≤ c₂ → a * Real.exp (d * t) ≤ k₀ + k₁ * t) ∧
      (t ≤ c₁ ∨ c₂ ≤ t → k₀ + k₁ * t ≤ a * Real.exp (d * t)) := by
  set G : ℝ → ℝ := fun t ↦ a * Real.exp (d * t) with hG
  have hconv : ConvexOn ℝ univ G := by
    refine ⟨convex_univ, fun x _ y _ p q hp hq hpq ↦ ?_⟩
    have := convexOn_exp.2 (mem_univ (d * x)) (mem_univ (d * y)) hp hq hpq
    simp only [smul_eq_mul, G] at this ⊢
    rw [show d * (p * x + q * y) = p * (d * x) + q * (d * y) by ring]
    nlinarith [mul_le_mul_of_nonneg_left this ha]
  -- the three-point form of convexity
  have h3 : ∀ x y z : ℝ, x < y → y < z → (z - x) * G y ≤ (z - y) * G x + (y - x) * G z := by
    intro x y z hxy hyz
    have := hconv.slope_mono_adjacent (mem_univ x) (mem_univ z) hxy hyz
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at this
    nlinarith
  refine ⟨G c₁ - (G c₂ - G c₁) / (c₂ - c₁) * c₁, (G c₂ - G c₁) / (c₂ - c₁), fun t ↦ ⟨?_, ?_⟩⟩
  · intro h1 h2
    have hpos : 0 < c₂ - c₁ := by linarith
    rw [← sub_nonneg]
    have key : (c₂ - c₁) * G t ≤ (c₂ - t) * G c₁ + (t - c₁) * G c₂ := by
      rcases h1.lt_or_eq with h1 | rfl
      · rcases h2.lt_or_eq with h2 | rfl
        · exact h3 _ _ _ h1 h2
        · nlinarith
      · nlinarith
    have : G c₁ - (G c₂ - G c₁) / (c₂ - c₁) * c₁ + (G c₂ - G c₁) / (c₂ - c₁) * t - G t =
        ((c₂ - t) * G c₁ + (t - c₁) * G c₂ - (c₂ - c₁) * G t) / (c₂ - c₁) := by
      field_simp; ring
    change 0 ≤ G c₁ - (G c₂ - G c₁) / (c₂ - c₁) * c₁ + (G c₂ - G c₁) / (c₂ - c₁) * t - G t
    rw [this]
    exact div_nonneg (by linarith) hpos.le
  · intro ht
    have hpos : 0 < c₂ - c₁ := by linarith
    rw [← sub_nonneg]
    have key : (c₂ - t) * G c₁ + (t - c₁) * G c₂ ≤ (c₂ - c₁) * G t := by
      rcases ht with ht | ht
      · rcases ht.lt_or_eq with ht | rfl
        · have := h3 _ _ _ ht hc
          nlinarith
        · nlinarith
      · rcases ht.lt_or_eq with ht | rfl
        · have := h3 _ _ _ hc ht
          nlinarith
        · nlinarith
    have : G t - (G c₁ - (G c₂ - G c₁) / (c₂ - c₁) * c₁ + (G c₂ - G c₁) / (c₂ - c₁) * t) =
        ((c₂ - c₁) * G t - ((c₂ - t) * G c₁ + (t - c₁) * G c₂)) / (c₂ - c₁) := by
      field_simp; ring
    change 0 ≤ G t - (G c₁ - (G c₂ - G c₁) / (c₂ - c₁) * c₁ + (G c₂ - G c₁) / (c₂ - c₁) * t)
    rw [this]
    exact div_nonneg (by linarith) hpos.le


/-- GAPS 101.45: the two-tail exponential-family test satisfying the two moment constraints is
UMPU. The proof applies `integral_le_of_generalized_neyman_pearson` with the chord of the
likelihood ratio through the critical points; for a competing unbiased test, the two moment
constraints follow from the vanishing derivative of its power function at `η₀`. -/
theorem isUniformlyMostPowerfulUnbiasedTest_of_two_tail_moment_constraints
    (μ : Measure X) (T h : X → ℝ) (hT : Measurable T)
    (hh : Measurable h) (hpos : ∀ x, 0 ≤ h x) (A : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hc : Convex ℝ U)
    (P : U → Measure X) (hP : ∀ η, IsProbabilityMeasure (P η))
    (hf : ∀ η, HasDensity (P η) μ (fun x ↦ h x * Real.exp (η.val * T x - A η.val)))
    (η₀ : U) (α c₁ c₂ : ℝ) (hα : α ∈ Ioo 0 1) (hcrit : c₁ < c₂)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (htail : ∀ x, (T x < c₁ ∨ c₂ < T x → φ x = 1) ∧
      (c₁ < T x ∧ T x < c₂ → φ x = 0))
    (hmom : Integrable T (P η₀) ∧ (∫ x, φ x ∂P η₀) = α ∧
      (∫ x, T x * φ x ∂P η₀) = α * ∫ x, T x ∂P η₀) :
    IsUniformlyMostPowerfulUnbiasedTest P {η₀} {η | η ≠ η₀} α φ := by
  obtain ⟨hTint, hφsize, hφmom⟩ := hmom
  let f : ℝ → X → ℝ := fun η x ↦ h x * Real.exp (η * T x - A η)
  have hfnn : ∀ η x, 0 ≤ f η x := fun η x ↦ mul_nonneg (hpos x) (Real.exp_pos _).le
  have hfint : ∀ η : U, Integrable (f η) μ := fun η ↦ (hf η).integrable
  have hint_eq : ∀ (η : U) (g : X → ℝ), (∫ x, g x ∂P η) = ∫ x, g x * f η x ∂μ := by
    intro η g
    rw [(hf η).integral_eq]
    exact integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)
  -- the test of level `α` with the same two moments as `φ` at `η₀` is beaten by `φ`
  have hTf : Integrable (fun x ↦ T x * f η₀ x) μ := by
    have := (hf η₀).2.2 ▸ hTint
    rw [integrable_withDensity_iff_integrable_smul' (hf η₀).1.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at this
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hfnn _ x), smul_eq_mul, f]
    ring
  have hcomp : ∀ η : U, ∀ ψ : X → ℝ, IsStatisticalTest ψ → (∫ x, ψ x ∂P η₀) = α →
      (∫ x, T x * ψ x ∂P η₀) = α * ∫ x, T x ∂P η₀ →
      (∫ x, ψ x ∂P η) ≤ ∫ x, φ x ∂P η := by
    intro η ψ hψ hψsize hψmom
    obtain ⟨k₀, k₁, hk⟩ := exists_chord_of_const_mul_exp (a := Real.exp (A η₀ - A η))
      (d := η.val - η₀.val) (Real.exp_pos _).le hcrit
    have hratio : ∀ x, f η x = Real.exp (A η₀ - A η) * Real.exp ((η.val - η₀.val) * T x) *
        f η₀ x := by
      intro x
      simp only [f]
      rw [show η.val * T x - A η = (A η₀ - A η) + (η.val - η₀.val) * T x + (η₀.val * T x - A η₀)
        by ring, Real.exp_add, Real.exp_add]
      ring
    have hsize' : (∫ x, ψ x * f η₀ x ∂μ) = ∫ x, φ x * f η₀ x ∂μ := by
      rw [← hint_eq, ← hint_eq, hψsize, hφsize]
    have hmom' : (∫ x, ψ x * (T x * f η₀ x) ∂μ) = ∫ x, φ x * (T x * f η₀ x) ∂μ := by
      have h1 : ∀ g : X → ℝ, (∫ x, g x * (T x * f η₀ x) ∂μ) = ∫ x, T x * g x ∂P η₀ := by
        intro g
        rw [hint_eq]
        exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      rw [h1, h1, hψmom, hφmom]
    have hNP := integral_le_of_generalized_neyman_pearson μ (f η)
      ![f η₀, fun x ↦ T x * f η₀ x] ![k₀, k₁] (hfint η)
      (fun i ↦ by fin_cases i; exacts [hfint η₀, hTf]) φ ψ hφ hψ ?_ ?_
    · rw [hint_eq, hint_eq]
      exact hNP
    · refine ae_of_all _ fun x ↦ ⟨fun hlt ↦ ?_, fun hlt ↦ ?_⟩
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hlt
        rw [hratio x] at hlt
        have hfx : 0 < f η₀ x := by
          rcases (hfnn η₀ x).lt_or_eq with h' | h'
          · exact h'
          · rw [← h'] at hlt; simp at hlt
        have : k₀ + k₁ * T x < Real.exp (A η₀ - A η) * Real.exp ((η.val - η₀.val) * T x) := by
          nlinarith
        apply (htail x).1
        by_contra hcon
        rw [not_or, not_lt, not_lt] at hcon
        exact absurd ((hk (T x)).1 hcon.1 hcon.2) (not_le.2 this)
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hlt
        rw [hratio x] at hlt
        have hfx : 0 < f η₀ x := by
          rcases (hfnn η₀ x).lt_or_eq with h' | h'
          · exact h'
          · rw [← h'] at hlt; simp at hlt
        have : Real.exp (A η₀ - A η) * Real.exp ((η.val - η₀.val) * T x) < k₀ + k₁ * T x := by
          nlinarith
        apply (htail x).2
        by_contra hcon
        rw [not_and_or, not_lt, not_lt] at hcon
        exact absurd ((hk (T x)).2 hcon) (not_le.2 this)
    · intro i
      fin_cases i
      · change k₀ * (∫ x, ψ x * f η₀ x ∂μ) ≤ k₀ * ∫ x, φ x * f η₀ x ∂μ
        rw [hsize']
      · change k₁ * (∫ x, ψ x * (T x * f η₀ x) ∂μ) ≤ k₁ * ∫ x, φ x * (T x * f η₀ x) ∂μ
        rw [hmom']
  -- moments under `P η` in terms of the unnormalized Laplace integrals
  have hrel : ∀ (η : U) (g : X → ℝ), (∫ x, g x ∂P η) =
      Real.exp (-A η) * ∫ x, g x * h x * Real.exp (η.val * T x) ∂μ := by
    intro η g
    rw [hint_eq, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [f]
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have hexpint : ∀ η ∈ U, Integrable (fun x ↦ h x * Real.exp (η * T x)) μ := by
    intro η hη
    refine ((hfint ⟨η, hη⟩).const_mul (Real.exp (A η))).congr (ae_of_all _ fun x ↦ ?_)
    simp only [f]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    field_simp
  have hZ : ∀ η : U, (∫ x, 1 * h x * Real.exp (η.val * T x) ∂μ) = Real.exp (A η) := by
    intro η
    have h1 := hrel η (fun _ ↦ 1)
    have := hP η
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    rw [Real.exp_neg] at h1
    have hne := (Real.exp_pos (A η)).ne'
    field_simp at h1
    simp only [one_mul]
    exact h1.symm
  have hpow : ∀ (η : U) (ψ : X → ℝ), (∫ x, ψ x ∂P η) =
      (∫ x, ψ x * h x * Real.exp (η.val * T x) ∂μ) /
        ∫ x, 1 * h x * Real.exp (η.val * T x) ∂μ := by
    intro η ψ
    rw [hrel, hZ, Real.exp_neg]
    ring
  have hP0 := hP η₀
  refine ⟨hφ, ?_, ?_, ?_⟩
  · intro θ hθ
    rw [mem_singleton_iff] at hθ
    rw [hθ, hφsize]
  · intro θ _
    have hconst : IsStatisticalTest (fun _ : X ↦ α) :=
      ⟨measurable_const, fun _ ↦ ⟨hα.1.le, hα.2.le⟩⟩
    have := hcomp θ (fun _ ↦ α) hconst (by simp) (by rw [integral_mul_const, mul_comm])
    have hPθ := hP θ
    simpa using this
  · intro ψ hψ hlev hunb θ _
    have hψb : ∀ x, |ψ x| ≤ 1 := fun x ↦ abs_le.2 ⟨by linarith [(hψ.2 x).1], (hψ.2 x).2⟩
    obtain ⟨-, hM⟩ := hasDerivAt_integral_mul_exp μ T h ψ hT hh hpos hψ.1 hψb U hU hexpint
      η₀ η₀.2
    obtain ⟨-, hZd⟩ := hasDerivAt_integral_mul_exp μ T h (fun _ ↦ 1) hT hh hpos measurable_const
      (fun _ ↦ by simp) U hU hexpint η₀ η₀.2
    set M := fun η : ℝ ↦ ∫ x, ψ x * h x * Real.exp (η * T x) ∂μ with hMdef
    set Z := fun η : ℝ ↦ ∫ x, 1 * h x * Real.exp (η * T x) ∂μ with hZdef
    set M' := ∫ x, ψ x * h x * T x * Real.exp (η₀.val * T x) ∂μ with hM'def
    set Z' := ∫ x, 1 * h x * T x * Real.exp (η₀.val * T x) ∂μ with hZ'def
    have hZ0 : Z η₀ = Real.exp (A η₀) := hZ η₀
    have hZne : Z η₀ ≠ 0 := by rw [hZ0]; exact (Real.exp_pos _).ne'
    have hβ := hM.div hZd hZne
    have hβeq : ∀ η : U, (∫ x, ψ x ∂P η) = M η / Z η := fun η ↦ hpow η ψ
    have hge : ∀ η (hη : η ∈ U), η ≠ η₀.val → α ≤ M η / Z η := by
      intro η hη hne
      rw [← hβeq ⟨η, hη⟩]
      exact hunb ⟨η, hη⟩ (fun h' ↦ hne (congrArg Subtype.val h'))
    have hle : M η₀ / Z η₀ ≤ α := by
      rw [← hβeq η₀]; exact hlev η₀ rfl
    have hmin : IsLocalMin (fun η ↦ M η / Z η) η₀ := by
      filter_upwards [hU.mem_nhds η₀.2] with η hη
      by_cases hne : η = η₀.val
      · rw [hne]
      · exact hle.trans (hge η hη hne)
    have hzero := hmin.hasDerivAt_eq_zero hβ
    have hβ0 : M η₀ / Z η₀ = α := by
      refine le_antisymm hle (ge_of_tendsto (hβ.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {η₀.val}ᶜ))) ?_)
      filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds η₀.2), self_mem_nhdsWithin] with η hη hne
      exact hge η hη hne
    have hMα : M η₀ = α * Z η₀ := by
      rw [← hβ0]; field_simp
    have hM' : M' = α * Z' := by
      rw [div_eq_zero_iff] at hzero
      rcases hzero with hzero | hzero
      · rw [hMα] at hzero
        have : (M' - α * Z') * Z η₀ = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' hZne
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 hzero) hZne
    refine hcomp θ ψ hψ ?_ ?_
    · rw [hβeq η₀]; exact hβ0
    · rw [hrel, hrel]
      have e1 : (∫ x, T x * ψ x * h x * Real.exp (η₀.val * T x) ∂μ) = M' :=
        integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      have e2 : (∫ x, T x * h x * Real.exp (η₀.val * T x) ∂μ) = Z' :=
        integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      rw [e1, e2, hM']
      ring

/-- GAPS 101.49: similar tests have Neyman structure under bounded completeness. -/
theorem condExp_eq_const_of_similar_test (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (hs : IsSufficientStatistic P T) (hc : IsBoundedlyCompleteStatistic P T)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ) (α : ℝ)
    (hsim : ∀ θ, (∫ x, φ x ∂P θ) = α) (θ : Θ) :
    (P θ)[φ | (inferInstance : MeasurableSpace S).comap T] =ᵐ[P θ] fun _ ↦ α := by
  obtain ⟨hT, K, hKm, hK⟩ := hs
  have hφb : ∀ x, |φ x| ≤ 1 := fun x ↦ abs_le.2 ⟨by linarith [(hφ.2 x).1], (hφ.2 x).2⟩
  have hzero := ae_integral_kernel_eq_of_isBoundedlyCompleteStatistic P hP hT hc K hK hφ.1 hφb
    α hsim θ
  have := hP θ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hT.comap_le
    (integrable_of_measurable_of_abs_le _ hφ.1 hφb)
    (fun _ _ _ ↦ integrableOn_const) (fun s hs' _ ↦ ?_) aestronglyMeasurable_const).symm
  obtain ⟨B, hB, rfl⟩ := hs'
  rw [setIntegral_preimage_eq_integral_indicator_mul _ hT hB,
    setIntegral_preimage_eq_integral_indicator_mul _ hT hB,
    integral_indicator_comp_mul_eq _ hT K (hK θ) hB hφ.1 hφb]
  refine integral_congr_ae (hzero.mono fun x hx ↦ ?_)
  simp only
  rw [hx]

/-- GAPS 101.55, algebraic part: invariant functions factor through a maximal invariant.
No measurability of the factor is asserted without a measurable quotient hypothesis. -/
theorem invariant_iff_factors_through_maximal_invariant
    {G A B : Type*} [Group G] [MulAction G A] [Nonempty B]
    (M : A → B) (hM : ∀ (g : G) x, M (g • x) = M x)
    (hmax : ∀ x y, M x = M y → ∃ g : G, g • x = y) (f : A → ℝ) :
    (∀ (g : G) x, f (g • x) = f x) ↔ ∃ q : B → ℝ, f = q ∘ M := by
  constructor
  · intro hf
    classical
    let q : B → ℝ := fun b ↦ if h : ∃ x, M x = b then f h.choose else 0
    refine ⟨q, funext fun x ↦ ?_⟩
    dsimp [q]
    rw [dite_eq_left ⟨x, rfl⟩]
    obtain ⟨g, hg⟩ := hmax x (Exists.choose (show ∃ y, M y = M x from ⟨x, rfl⟩))
      (Exists.choose_spec (show ∃ y, M y = M x from ⟨x, rfl⟩)).symm
    rw [← hg, hf]
  · rintro ⟨q, rfl⟩ g x
    simp [hM]


end CKSD
