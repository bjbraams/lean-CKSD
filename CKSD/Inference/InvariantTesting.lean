module

public import CKSD.Inference.Basic
public import CKSD.Inference.Sufficiency

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

/-- GAPS 101.45: the two-tail exponential-family test satisfying the two moment constraints is
UMPU. -/
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
  sorry

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
