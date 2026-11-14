module

public import CKSD.Bayes.MeanFieldBackwardTest
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Endpoint
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniqueness of weak continuity-equation solutions

A bounded globally Lipschitz space-time velocity determines at most one narrowly continuous
probability solution with a prescribed initial law. Smooth backward tests with uniformly small
transport residual give equality of terminal integrals. Testing cosine and sine of linear
functionals then identifies the measures by their characteristic functions.

No moment condition on either curve is required. Pinned TauCeti supplies the endpoint weak
continuity-equation identity; the local backward-test construction uses its smooth ODE flows
and Lipschitz approximation. Mathlib supplies integral bounds and characteristic-function
uniqueness. This is the Eulerian comparison ingredient for GAPS 104.53.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology ContDiff
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
section WeakTransport
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Two narrowly continuous probability solutions for a bounded globally Lipschitz velocity
have the same terminal integrals against every smooth bounded Lipschitz scalar test. -/
theorem integral_eq_of_is_continuity_equation_of_bounded_lipschitz
    {T : ℝ} (hT : 0 ≤ T) (v : ℝ × E → E) {K M : ℝ≥0}
    (hv : LipschitzWith K v) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (μ ν : ℝ → FiniteMeasure E) (hμ : ContinuousOn μ (Icc (0 : ℝ) T))
    (hν : ContinuousOn ν (Icc (0 : ℝ) T))
    (hμp : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (μ t : Measure E))
    (hνp : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (ν t : Measure E))
    (hμce : TauCeti.IsContinuityEquation (fun t ↦ (μ t : Measure E)) (fun t x ↦ v (t, x)) 0 T)
    (hνce : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure E)) (fun t x ↦ v (t, x)) 0 T)
    (hinit : μ 0 = ν 0) (g : E → ℝ) (hg : ContDiff ℝ ∞ g) {G : ℝ≥0}
    (hgLip : LipschitzWith G g) (A : ℝ) (hgA : ∀ x, ‖g x‖ ≤ A) :
    ∫ x, g x ∂(μ T : Measure E) = ∫ x, g x ∂(ν T : Measure E) := by
  obtain ⟨C, hC, htest⟩ := exists_approximate_backward_test v hv hM g hg hgLip A hgA hT
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have herr (ε : ℝ) (hε : 0 < ε) :
      ‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ ≤ (2 * C * T) * ε := by
    obtain ⟨u, hu, huA, huD, huT, hres⟩ := htest ε hε
    have hbound (κ : ℝ → FiniteMeasure E) (hκ : ContinuousOn κ (Icc (0 : ℝ) T))
        (hκp : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (κ t : Measure E))
        (hκce : TauCeti.IsContinuityEquation (fun t ↦ (κ t : Measure E)) (fun t x ↦ v (t, x)) 0 T) :
        ‖(∫ x, g x ∂(κ T : Measure E)) - ∫ x, u (0, x) ∂(κ 0 : Measure E)‖ ≤ C * ε * T := by
      have hid := hκce.intervalIntegral_integral_fderiv_eq_sub hκ hu huA huD h0 hTT
      simp_rw [huT] at hid
      rw [← hid]
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
        (f := fun t ↦ ∫ x, fderiv ℝ u (t, x) (1, v (t, x)) ∂(κ t : Measure E))
        (C := C * ε) (fun t ht ↦ ?_)
      · simpa only [sub_zero, abs_of_nonneg hT] using hh
      · rw [uIoc_of_le hT] at ht
        let := hκp t ⟨ht.1.le, ht.2⟩
        simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
          (μ := (κ t : Measure E)) (ae_of_all _ fun x ↦ hres t ⟨ht.1.le, ht.2⟩ x)
    have hm := hbound μ hμ hμp hμce
    have hn := hbound ν hν hνp hνce
    have heq0 : (∫ x, u (0, x) ∂(μ 0 : Measure E)) = ∫ x, u (0, x) ∂(ν 0 : Measure E) := by rw [hinit]
    calc
      _ = ‖((∫ x, g x ∂(μ T : Measure E)) - ∫ x, u (0, x) ∂(μ 0 : Measure E)) -
          ((∫ x, g x ∂(ν T : Measure E)) - ∫ x, u (0, x) ∂(ν 0 : Measure E))‖ := by
        rw [heq0]
        congr 1
        ring
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hm hn)
      _ = _ := by ring
  have hz : ‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    have hd : 0 < ‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ := lt_of_not_ge hnot
    let D := 2 * C * T
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hDp : 0 < D + 1 := by linarith
    have hh := herr (‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ / (D + 1))
      (div_pos hd hDp)
    have hsmall : D * (‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ / (D + 1)) <
        ‖(∫ x, g x ∂(μ T : Measure E)) - ∫ x, g x ∂(ν T : Measure E)‖ := by
      rw [← mul_div_assoc, div_lt_iff₀ hDp]
      nlinarith
    exact (not_le_of_gt hsmall) hh
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)
end WeakTransport

section InnerProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
/-- Narrowly continuous probability solutions of a continuity equation with bounded globally
Lipschitz space-time velocity are unique without moment hypotheses. -/
theorem eq_of_is_continuity_equation_of_bounded_lipschitz
    {T : ℝ} (hT : 0 ≤ T) (v : ℝ × H → H) {K M : ℝ≥0}
    (hv : LipschitzWith K v) (hM : ∀ q, ‖v q‖₊ ≤ M)
    (μ ν : ℝ → FiniteMeasure H) (hμ : ContinuousOn μ (Icc (0 : ℝ) T))
    (hν : ContinuousOn ν (Icc (0 : ℝ) T))
    (hμp : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (μ t : Measure H))
    (hνp : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (ν t : Measure H))
    (hμce : TauCeti.IsContinuityEquation (fun t ↦ (μ t : Measure H)) (fun t x ↦ v (t, x)) 0 T)
    (hνce : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure H)) (fun t x ↦ v (t, x)) 0 T)
    (hinit : μ 0 = ν 0) : μ T = ν T := by
  let : IsFiniteMeasure (μ T : Measure H) := (μ T).property
  let : IsFiniteMeasure (ν T : Measure H) := (ν T).property
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext z
  let ℓ : H →L[ℝ] ℝ := innerSL ℝ z
  have hc := integral_eq_of_is_continuity_equation_of_bounded_lipschitz hT v hv hM
    μ ν hμ hν hμp hνp hμce hνce hinit (fun x ↦ Real.cos (ℓ x))
    (Real.contDiff_cos.comp ℓ.contDiff) (Real.lipschitzWith_cos.comp ℓ.lipschitzWith)
    1 (fun x ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ℓ x))
  have hs := integral_eq_of_is_continuity_equation_of_bounded_lipschitz hT v hv hM
    μ ν hμ hν hμp hνp hμce hνce hinit (fun x ↦ Real.sin (ℓ x))
    (Real.contDiff_sin.comp ℓ.contDiff) (Real.lipschitzWith_sin.comp ℓ.lipschitzWith)
    1 (fun x ↦ by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ℓ x))
  have hint (κ : FiniteMeasure H) : Integrable (fun x : H ↦ Complex.exp (inner ℝ x z * Complex.I)) (κ : Measure H) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x ↦ by simp
  rw [charFun_apply, charFun_apply]
  apply Complex.ext
  · change RCLike.re (∫ x : H, Complex.exp (inner ℝ x z * Complex.I) ∂(μ T : Measure H)) =
      RCLike.re (∫ x : H, Complex.exp (inner ℝ x z * Complex.I) ∂(ν T : Measure H))
    rw [← integral_re (hint (μ T)), ← integral_re (hint (ν T))]
    have heqRe (x : H) : RCLike.re (Complex.exp (inner ℝ x z * Complex.I)) = Real.cos (ℓ x) := by
      change (Complex.exp (inner ℝ x z * Complex.I)).re = Real.cos (ℓ x)
      simp [Complex.exp_re, ℓ, real_inner_comm]
    simp_rw [heqRe]
    exact hc
  · change RCLike.im (∫ x : H, Complex.exp (inner ℝ x z * Complex.I) ∂(μ T : Measure H)) =
      RCLike.im (∫ x : H, Complex.exp (inner ℝ x z * Complex.I) ∂(ν T : Measure H))
    rw [← integral_im (hint (μ T)), ← integral_im (hint (ν T))]
    have heqIm (x : H) : RCLike.im (Complex.exp (inner ℝ x z * Complex.I)) = Real.sin (ℓ x) := by
      change (Complex.exp (inner ℝ x z * Complex.I)).im = Real.sin (ℓ x)
      simp [Complex.exp_im, ℓ, real_inner_comm]
    simp_rw [heqIm]
    exact hs
end InnerProduct
end CKSD
