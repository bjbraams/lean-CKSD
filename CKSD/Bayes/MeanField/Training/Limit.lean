module

import CKSD.Bayes.MeanField.Training.Evolution
import CKSD.Bayes.MeanField.Training.Empirical
public import CKSD.Bayes.MeanField.Training.Drift
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Order.CompletePartialOrder
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
import CKSD.Bayes.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Mean-field limit of two-layer network training

The population risk of a two-layer network in mean-field parametrization is a quadratic
functional of the parameter law. The time-scaled gradient flow of `N` parameters is a system of
ordinary differential equations, and as `N → ∞` its empirical measures converge to the solution
of a nonlinear continuity equation in TauCeti's sense.

## Main definitions

* `CKSD.meanFieldRisk`, `CKSD.meanFieldPotential`: the population risk of a two-layer network in
  mean-field parametrization and its first variation.

The velocity field `CKSD.meanFieldVelocity` of the training flow is defined in
`CKSD.Bayes.MeanField.Training.Drift`.

## Main results

* `CKSD.meanFieldRisk_eq`, `CKSD.hasGradientAt_meanFieldPotential_empiricalMeasure`,
  `CKSD.exists_meanField_limit`: the quadratic expansion of the risk, the identification of the
  particle velocity with the gradient of its first variation, and the mean-field limit of
  network training.

Source: GAPS 104.53.

## References

* S. Mei, A. Montanari and P.-M. Nguyen, *A mean field view of the landscape of two-layer neural
  networks*, Proc. Natl. Acad. Sci. USA 115 (2018), E7665–E7671.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

universe u

attribute [local instance] Classical.propDecidable

/-- Correlation `V(θ) = 𝔼[Y φ(X, θ)]` of a feature with the response. -/
def meanFieldV {Z Θ : Type*} [MeasurableSpace Z] (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ)
    (θ : Θ) : ℝ :=
  ∫ w, w.2 * φ w.1 θ ∂ν

/-- Feature kernel `U(θ, θ') = 𝔼[φ(X, θ) φ(X, θ')]`. -/
def meanFieldU {Z Θ : Type*} [MeasurableSpace Z] (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ)
    (θ θ' : Θ) : ℝ :=
  ∫ w, φ w.1 θ * φ w.1 θ' ∂ν

/-- Population risk `½ 𝔼(Y - f_ρ(X))²` of the mean-field predictor `f_ρ = ∫ φ(·, θ) ρ(dθ)`. -/
def meanFieldRisk {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ) (ρ : Measure Θ) : ℝ :=
  (1 / 2 : ℝ) * ∫ w, (w.2 - ∫ θ, φ w.1 θ ∂ρ) ^ 2 ∂ν

/-- GAPS 104.53: the elementary expansion
`R(ρ) = ½𝔼Y² - ∫ V dρ + ½ ∫∫ U dρ dρ` for a bounded measurable feature map. -/
theorem meanFieldRisk_eq {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (ν : Measure (Z × ℝ)) [IsProbabilityMeasure ν] (φ : Z → Θ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (B : ℝ) (hB : ∀ z θ, |φ z θ| ≤ B)
    (hY : Integrable (fun w : Z × ℝ ↦ w.2 ^ 2) ν) (ρ : Measure Θ) [IsProbabilityMeasure ρ] :
    meanFieldRisk ν φ ρ = (1 / 2 : ℝ) * ∫ w, w.2 ^ 2 ∂ν - ∫ θ, meanFieldV ν φ θ ∂ρ +
      (1 / 2 : ℝ) * ∫ θ, ∫ θ', meanFieldU ν φ θ θ' ∂ρ ∂ρ := by
  set f : Z → ℝ := fun z ↦ ∫ θ, φ z θ ∂ρ with hfdef
  have hfm : Measurable f := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hfB (z : Z) : |f z| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun θ ↦ φ z θ) (C := B)
      (ae_of_all _ fun θ ↦ by simpa [Real.norm_eq_abs] using hB z θ)
    simpa [Real.norm_eq_abs] using this
  have hφm (z : Z) : Measurable (φ z) := hφ.comp (measurable_const.prodMk measurable_id)
  -- Integrability of the pieces.
  have hY1 : Integrable (fun w : Z × ℝ ↦ w.2) ν := by
    refine ((integrable_const (1 : ℝ)).add hY).div_const 2 |>.mono'
      measurable_snd.aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs]
    have : 0 ≤ (|w.2| - 1) ^ 2 := sq_nonneg _
    have hsq : |w.2| ^ 2 = w.2 ^ 2 := sq_abs _
    simp only [Pi.add_apply]
    nlinarith
  have hyf : Integrable (fun w : Z × ℝ ↦ w.2 * f w.1) ν := by
    refine (hY1.abs.const_mul B).mono'
      (measurable_snd.mul (hfm.comp measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hfB w.1) (abs_nonneg _)
  have hf2 : Integrable (fun w : Z × ℝ ↦ f w.1 ^ 2) ν := by
    refine Integrable.of_bound ((hfm.comp measurable_fst).pow_const 2).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hfB w.1) 2
  -- The cross term.
  have hcross : ∫ w, w.2 * f w.1 ∂ν = ∫ θ, meanFieldV ν φ θ ∂ρ := by
    have h1 : (fun w : Z × ℝ ↦ w.2 * f w.1) = fun w ↦ ∫ θ, w.2 * φ w.1 θ ∂ρ := by
      funext w; rw [integral_const_mul]
    rw [h1]
    refine integral_integral_swap ?_
    refine (((hY1.abs.const_mul B).comp_fst ρ)).mono' ?_ (ae_of_all _ fun q ↦ ?_)
    · exact (measurable_fst.snd.mul (hφ.comp (measurable_fst.fst.prodMk
        measurable_snd))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _ _) (abs_nonneg _)
  -- The quadratic term.
  have hquad : ∫ w, f w.1 ^ 2 ∂ν = ∫ θ, ∫ θ', meanFieldU ν φ θ θ' ∂ρ ∂ρ := by
    have h1 : (fun w : Z × ℝ ↦ f w.1 ^ 2) = fun w ↦ ∫ θ, φ w.1 θ * f w.1 ∂ρ := by
      funext w; rw [integral_mul_const, sq]
    rw [h1, integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
      have h2 : (fun w : Z × ℝ ↦ φ w.1 θ * f w.1) =
          fun w ↦ ∫ θ', φ w.1 θ * φ w.1 θ' ∂ρ := by
        funext w; rw [integral_const_mul]
      simp only
      rw [h2, integral_integral_swap]
      · rfl
      refine Integrable.of_bound ?_ (B * B) (ae_of_all _ fun q ↦ ?_)
      · exact ((hφ.comp (measurable_fst.fst.prodMk measurable_const)).mul
          (hφ.comp (measurable_fst.fst.prodMk measurable_snd))).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB _ _) (hB _ _) (abs_nonneg _) ((abs_nonneg _).trans (hB q.1.1 θ))
    · refine Integrable.of_bound ?_ (B * B) (ae_of_all _ fun q ↦ ?_)
      · exact ((hφ.comp (measurable_fst.fst.prodMk measurable_snd)).mul
          (hfm.comp measurable_fst.fst)).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB _ _) (hfB _) (abs_nonneg _) ((abs_nonneg _).trans (hB q.1.1 q.2))
  have hpt (w : Z × ℝ) : (w.2 - f w.1) ^ 2 = w.2 ^ 2 - 2 * (w.2 * f w.1) + f w.1 ^ 2 := by
    ring
  have hf (z : Z) : ∫ θ, φ z θ ∂ρ = f z := by rw [hfdef]
  rw [meanFieldRisk]
  simp_rw [hf, hpt]
  have hsum := integral_add (hY.sub (hyf.const_mul 2)) hf2
  have hdif := integral_sub hY (hyf.const_mul 2)
  simp only [Pi.sub_apply] at hsum hdif
  rw [hsum, hdif, integral_const_mul, hcross, hquad]
  ring

/-- First variation `Ψ(θ; ρ) = -V(θ) + ∫ U(θ, θ') ρ(dθ')` of the mean-field risk. -/
def meanFieldPotential {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ) (ρ : Measure Θ) (θ : Θ) : ℝ :=
  -meanFieldV ν φ θ + ∫ θ', meanFieldU ν φ θ θ' ∂ρ

/-- GAPS 104.53: for the empirical measure `ρ_N` of `N` parameters, if `gradV` and `gradU` are
the gradients of `V` and of `U` in its first argument, then the mean-field velocity is
`-∇_θ Ψ(θ; ρ_N)`, so the particle equation of `CKSD.exists_meanField_limit` is the
time-scaled gradient flow `θ̇ᵢ = -∇_θ Ψ(θᵢ; ρ_N)`. The further identity
`∇_θ Ψ(θᵢ; ρ_N) = N ∇_{θᵢ} R(ρ_N)` is not formalized. -/
theorem hasGradientAt_meanFieldPotential_empiricalMeasure {Z : Type*} [MeasurableSpace Z]
    {p : ℕ} (ν : Measure (Z × ℝ)) (φ : Z → EuclideanSpace ℝ (Fin p) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (gradU : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    {θ : EuclideanSpace ℝ (Fin p)} (hgV : HasGradientAt (meanFieldV ν φ) (gradV θ) θ)
    {N : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin p))
    (hgU : ∀ j, HasGradientAt (fun η ↦ meanFieldU ν φ η (x j)) (gradU θ (x j)) θ) :
    HasGradientAt (meanFieldPotential ν φ (empiricalMeasure N x))
      (-meanFieldVelocity gradV gradU (empiricalMeasure N x) θ) θ := by
  simp only [hasGradientAt_iff_hasFDerivAt] at hgV hgU ⊢
  have h := hgV.neg.add
    ((HasFDerivAt.fun_sum (u := Finset.univ) fun j _ ↦ hgU j).const_mul (N : ℝ)⁻¹)
  convert h using 1
  · funext η
    simp only [meanFieldPotential, integral_empiricalMeasure_vector, smul_eq_mul]
    rfl
  · rw [meanFieldVelocity_def, integral_empiricalMeasure_vector]
    ext v
    simp [map_sum, Finset.mul_sum]
    ring

/-- GAPS 104.53: mean-field limit of two-layer network training. With bounded Lipschitz fields
`gradV` and `gradU`, the nonlinear continuity equation `∂ₜρ = ∇·(ρ∇_θΨ(·; ρ))`, with
`-∇_θΨ(·; ρ)` the velocity `CKSD.meanFieldVelocity gradV gradU ρ`, has a unique narrowly
continuous probability solution with datum `ρ₀`, and the empirical measures of the time-scaled
gradient flow from independent `ρ₀`-distributed initial particles converge to it in `W₁`, almost
surely and uniformly on bounded time intervals. The statement uses only `gradV` and `gradU`;
when they are the gradients of `V` and `U`, the particle equation is the gradient flow of the
risk by `CKSD.hasGradientAt_meanFieldPotential_empiricalMeasure`. -/
theorem exists_meanField_limit {p : ℕ}
    (gradV : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (gradU : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (B L : ℝ) (hVb : ∀ θ, ‖gradV θ‖ ≤ B) (hUb : ∀ θ θ', ‖gradU θ θ'‖ ≤ B)
    (hVl : ∀ θ η, ‖gradV θ - gradV η‖ ≤ L * ‖θ - η‖)
    (hUl : ∀ θ θ' η η', ‖gradU θ θ' - gradU η η'‖ ≤ L * (‖θ - η‖ + ‖θ' - η'‖))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure ρ₀]
    (hρ₀ : Integrable (fun θ ↦ ‖θ‖) ρ₀) :
    let IsSolution := fun ρ : ℝ → Measure (EuclideanSpace ℝ (Fin p)) ↦
      (∀ t ≥ 0, IsProbabilityMeasure (ρ t)) ∧ ρ 0 = ρ₀ ∧
      (∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ,
        ContinuousOn (fun t ↦ ∫ θ, g θ ∂ρ t) (Ici 0)) ∧
      ∀ T > 0, TauCeti.IsContinuityEquation ρ
        (fun t θ ↦ meanFieldVelocity gradV gradU (ρ t) θ) 0 T
    ∃ ρ, IsSolution ρ ∧ (∀ σ, IsSolution σ → ∀ t ≥ 0, σ t = ρ t) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin p)), IsIndependentIdenticallyDistributed P ξ ρ₀ →
        ∀ θ : ℕ → ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin p),
          (∀ N, ∀ i < N, ∀ ω, θ N i 0 ω = ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
            (meanFieldVelocity gradV gradU
              (empiricalMeasure N fun j : Fin N ↦ θ N j t ω) (θ N i t ω)) t) →
          ∀ᵐ ω ∂P, ∀ T > 0, Tendsto (fun N ↦ ⨆ t ∈ Icc 0 T,
            TauCeti.wassersteinEDist 1 (empiricalMeasure N fun j : Fin N ↦ θ N j t ω) (ρ t))
            atTop (𝓝 0) := by
  let b := fun x μ ↦ meanFieldVelocity gradV gradU μ x
  have hb := isWassersteinLipschitzDrift_meanFieldVelocity gradV gradU B L hVb hUb hVl hUl
  have hL : 0 ≤ 2 * (Real.toNNReal L : ℝ) := mul_nonneg (by norm_num) (Real.toNNReal L).coe_nonneg
  let M := Real.toNNReal (2 * B)
  have hM (μ : Measure (EuclideanSpace ℝ (Fin p))) (hμ : IsProbabilityMeasure μ) (x) :
      ‖b x μ‖ ≤ (M : ℝ) := by
    have := hμ
    exact (norm_meanFieldVelocity_le gradV gradU B hVb hUb μ x).trans (Real.le_coe_toNNReal _)
  obtain ⟨ρ, v, K, γ, hρ, huniq, hv, hvM, hγ, hγ0, hγd, hρlaw, hvρ⟩ :=
    exists_unique_nonlinear_continuity_solution_of_bound ρ₀ hρ₀ b hb hL M hM
  refine ⟨ρ, hρ, huniq, ?_⟩
  intro Ω _ P _ ξ hiid θ hθ
  have hγL (x) : LipschitzWith M (γ x) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hγd x t).differentiableAt)
    intro t
    rw [(hγd x t).deriv]
    exact hvM _
  have hvEq (t : ℝ) (ht : 0 ≤ t) (x) : v (t, x) = b x (ρ₀.map (fun y ↦ γ y t)) := by
    rw [hvρ t ht x, hρlaw t ht]
  filter_upwards [ae_tendsto_iSup_empirical_training_laws P ρ₀ hρ₀ ξ hiid b hb γ hγ hγ0 hγL
    v hv.continuous hγd hvEq θ hθ] with ω hω
  intro T hT
  convert hω T hT using 1
  funext N
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  rw [hρlaw t ht.1]


end CKSD
