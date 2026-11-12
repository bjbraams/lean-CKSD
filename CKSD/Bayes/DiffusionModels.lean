module

public import CKSD.Bayes.MeanField
public import CKSD.Bayes.DiffusionPathRegularity
public import CKSD.Bayes.DiffusionIntegralRegularity
public import CKSD.Bayes.Diffusion
public import CKSD.Bayes.GaussianSmoothing
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Time reversal, diffusion sampling, and marginal-preserving dynamics

Results on score-based generative models. Laws of forward diffusions are weak solutions of their
Fokker–Planck equations (`IsFokkerPlanckSolution`), and the probability-flow statement uses
TauCeti's continuity equation; the reverse-time stochastic differential equation of Anderson and
Haussmann–Pardoux needs stochastic integration and is not stated. For the variance-exploding
process, the smoothed law `π * N(0, tI)` is an explicit push-forward and its score is written by
the Tweedie formula `∇ log πₜ(x) = 𝔼[(Y - x)/t | Y + √t ξ = x]` as a ratio of Gaussian integrals.
The DDPM sampler is iterated on laws through `ddpmStep`. Diffusions with prescribed marginals are
stated with a constant noise level, for which the equation is pathwise. Gaussian smoothing and
the conditional score identity use `CKSD.Bayes.GaussianSmoothing`, which averages TauCeti's
Schwartz Gaussian and applies the conditional-expectation identity for joint densities.

## Main definitions

* `CKSD.probabilityFlowVelocity`: the velocity field of the probability-flow ODE.
* `CKSD.varianceExplodingLaw`, `CKSD.varianceExplodingScore`: the law `π * N(0, tI)` and its score.
* `CKSD.ddpmLaw`, `CKSD.ddpmStepRatio`: the law of the DDPM sampler and the step-ratio parameter.

## Main results

* `CKSD.probabilityFlow_isContinuityEquation_and_map`: the probability flow transports the
  time-reversed marginals (GAPS 104.63).
* `CKSD.klDiv_ddpmLaw_le`: the KL bound for DDPM under a second-moment assumption (GAPS 104.75),
  with the step schedule `CKSD.exists_ddpm_geometric_schedule` and the parameter choice
  `CKSD.ddpmStepRatio_le_half`, `CKSD.div_two_mul_add_two_mul_ddpmStepRatio_eq`,
  `CKSD.one_add_inv_ddpmStepRatio_mul_log`.
* `CKSD.isFokkerPlanckSolution_add_score_of_continuityEquation`: adding `ε ∇ log μₜ` to the drift
  and noise of level `√(2ε)` preserves the marginals (GAPS 104.76).
* `CKSD.map_marginalPreservingDiffusion`: the pathwise version at a constant noise level
  (GAPS 104.76).
* `CKSD.stochasticInterpolant_score`,
  `CKSD.stochasticInterpolant_integral_sub_eq_integral_velocity`: score and velocity of stochastic
  interpolants (GAPS 104.76).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Velocity `-f(T-t,x) + ½ g gᵀ(T-t) ∇ log p_{T-t}(x)` of the probability flow on `[0, T)`,
and `0` outside. -/
def probabilityFlowVelocity {d : ℕ} (T : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (g : ℝ → Matrix (Fin d) (Fin d) ℝ) (p : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 0 ≤ t ∧ t < T then
    -f (T - t) x + (1 / 2 : ℝ) • Matrix.toEuclideanLin (g (T - t) * (g (T - t)).transpose)
      ((p (T - t) x)⁻¹ • gradient (p (T - t)) x)
  else 0

/-- GAPS 104.63, probability-flow part: the time-reversed marginals `qₜ = p_{T-t}` of a diffusion
with positive `C¹` densities solve the continuity equation with the probability-flow velocity on
every `(0, T')`, `T' < T`, and when that velocity is Lipschitz the continuous flow started from `p_T` has
law `p_{T-t}`. The forward marginals are a weak Fokker–Planck solution with a finite initial second
moment; the reverse-time stochastic equation is not part of this statement. -/
theorem probabilityFlow_isContinuityEquation_and_map {d : ℕ} (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : Continuous (Function.uncurry f)) (Lf : ℝ≥0) (hfL : ∀ t, LipschitzWith Lf (f t))
    (g : ℝ → Matrix (Fin d) (Fin d) ℝ) (hg : Continuous g) (hginv : ∀ t, (g t).det ≠ 0)
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) (hμm : Measurable μ)
    (hFP : IsFokkerPlanckSolution μ f (fun t _ ↦ g t * (g t).transpose) T)
    (hμ2 : Integrable (fun x ↦ ‖x‖ ^ 2) (μ 0))
    (p : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hp : ∀ t ∈ Ioc 0 T, μ t = volume.withDensity fun x ↦ ENNReal.ofReal (p t x))
    (hpos : ∀ t ∈ Ioc 0 T, ∀ x, 0 < p t x) (hpC1 : ∀ t ∈ Ioc 0 T, ContDiff ℝ 1 (p t))
    (hpcont : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ p z.1 z.2)
      (Ioc 0 T ×ˢ univ))
    (hgradcont : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ gradient (p z.1) z.2)
      (Ioc 0 T ×ˢ univ))
    (hloc : ∀ t₀ ∈ Ioo 0 T, ∀ r > 0, ∫⁻ t in Ioo t₀ T, ∫⁻ x in Metric.closedBall 0 r,
      ENNReal.ofReal (p t x ^ 2 + ‖gradient (p t) x‖ ^ 2) < ∞) :
    (∀ T' ∈ Ioo 0 T, TauCeti.IsContinuityEquation (fun t ↦ μ (T - t))
      (probabilityFlowVelocity T f g p) 0 T') ∧
    ((∀ T' ∈ Ioo 0 T, ∃ K : ℝ≥0, ∀ t ∈ Icc 0 T',
        LipschitzWith K (probabilityFlowVelocity T f g p t)) →
      ∀ Z : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ z, Z 0 z = z) →
        (∀ z, ContinuousOn (fun t ↦ Z t z) (Ico 0 T)) →
        (∀ z, ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s ↦ Z s z)
          (probabilityFlowVelocity T f g p t (Z t z)) (Ici t) t) →
        ∀ t ∈ Ico 0 T, (μ T).map (Z t) = μ (T - t)) := by
  sorry

/-- The law `π * N(0, tI)` of `Y + √t ξ` with `Y ∼ π` and independent standard normal `ξ`. -/
def varianceExplodingLaw {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map fun z ↦ z.1 + Real.sqrt t • z.2

/-- Score `∇ log (π * N(0, tI))(x)`, written by Tweedie's formula as the ratio
`∫ (y - x)/t · e^{-‖x-y‖²/2t} π(dy) / ∫ e^{-‖x-y‖²/2t} π(dy)`. -/
def varianceExplodingScore {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (∫ y, Real.exp (-‖x - y‖ ^ 2 / (2 * t)) ∂π)⁻¹ •
    ∫ y, Real.exp (-‖x - y‖ ^ 2 / (2 * t)) • (t⁻¹ • (y - x)) ∂π

/-- Law of the DDPM sampler after `n` steps along the times `τ`, started from `N(0, TI)`. -/
def ddpmLaw {d : ℕ} (T : ℝ) (τ : ℕ → ℝ)
    (score : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    ℕ → Measure (EuclideanSpace ℝ (Fin d))
  | 0 => (stdGaussian (EuclideanSpace ℝ (Fin d))).map fun z ↦ Real.sqrt T • z
  | n + 1 => ((ddpmLaw T τ score n).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
      fun w ↦ ddpmStep (score (T - τ n)) (T - τ n) (τ (n + 1) - τ n) w.1 w.2

/-- GAPS 104.75: relative-entropy bound for the DDPM sampler under only a finite second moment,
for steps `hₙ ≤ h̄(T - τₙ)` with `h̄ ≤ 1/2`, early stopping `δ = T - τ_N`, and the accumulated score
error `ε²_sc = ∑ hₙ 𝔼_{π_{T-τₙ}} ‖ŝ_{T-τₙ} - ∇ log π_{T-τₙ}‖²`. -/
theorem klDiv_ddpmLaw_le {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure π] (hπ : Integrable (fun x ↦ ‖x‖ ^ 2) π) (T : ℝ) (N : ℕ)
    (τ : ℕ → ℝ) (hτ0 : τ 0 = 0) (hτ : ∀ n < N, τ n < τ (n + 1)) (hτN : τ N < T)
    (hbar : ℝ) (hbar0 : 0 < hbar) (hbar1 : hbar ≤ 1 / 2)
    (hstep : ∀ n < N, τ (n + 1) - τ n ≤ hbar * (T - τ n))
    (score : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hscore : Measurable (Function.uncurry score)) :
    let δ := T - τ N
    let εsc := ∑ n ∈ Finset.range N, ENNReal.ofReal (τ (n + 1) - τ n) *
      ∫⁻ x, ‖score (T - τ n) x - varianceExplodingScore π (T - τ n) x‖ₑ ^ 2
        ∂varianceExplodingLaw π (T - τ n)
    klDiv (varianceExplodingLaw π δ) (ddpmLaw T τ score N) ≤
      ENNReal.ofReal ((∫ x, ‖x‖ ^ 2 ∂π) / (2 * T)) + 4 * εsc +
        ENNReal.ofReal (2 * hbar * d * (1 + Real.log (T / δ))) := by
  sorry

/-- GAPS 104.75: the geometric step schedule. With `N` least such that `(1 - h̄)ᴺ T ≤ δ`, the times
`τₙ = T - (1 - h̄)ⁿ T` for `n < N` and `τ_N = T - δ` satisfy the step hypothesis, and
`N ≤ 1 + h̄⁻¹ log(T/δ)`. -/
theorem exists_ddpm_geometric_schedule (T δ hbar : ℝ) (hδ : 0 < δ) (hδT : δ < T) (hbar0 : 0 < hbar)
    (hbar1 : hbar ≤ 1 / 2) :
    ∃ N : ℕ, (1 - hbar) ^ N * T ≤ δ ∧ (∀ m < N, δ < (1 - hbar) ^ m * T) ∧
      let τ := fun n : ℕ ↦ if n < N then T - (1 - hbar) ^ n * T else T - δ
      1 ≤ N ∧ τ 0 = 0 ∧ T - τ N = δ ∧
        (∀ n < N, 0 < τ (n + 1) - τ n ∧ τ (n + 1) - τ n ≤ hbar * (T - τ n)) ∧
        (N : ℝ) ≤ 1 + hbar⁻¹ * Real.log (T / δ) := by
  have hT : 0 < T := hδ.trans hδT
  set r := 1 - hbar with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 := by linarith
  have hex : ∃ n : ℕ, r ^ n * T ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hT) hr1
    exact ⟨n, ((lt_div_iff₀ hT).1 hn).le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ not_le.1 (Nat.find_min hex hm), ?_⟩
  set N := Nat.find hex with hN
  have hspec : r ^ N * T ≤ δ := Nat.find_spec hex
  have hmin (m : ℕ) (hm : m < N) : δ < r ^ m * T := not_le.1 (Nat.find_min hex hm)
  have hN1 : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    rw [h0, pow_zero, one_mul] at hspec
    linarith
  intro τ
  have hτ (n : ℕ) (hn : n < N) : τ n = T - r ^ n * T := by simp only [τ, hn, ↓reduceIte]
  have hτN : τ N = T - δ := by simp only [τ, lt_irrefl, ↓reduceIte]
  refine ⟨hN1, ?_, ?_, ?_, ?_⟩
  · rw [hτ 0 (by omega), pow_zero, one_mul, sub_self]
  · rw [hτN]; ring
  · intro n hn
    rw [hτ n hn]
    by_cases hn1 : n + 1 < N
    · rw [hτ (n + 1) hn1, pow_succ]
      have hpos : 0 < r ^ n * T := by positivity
      constructor
      · nlinarith
      · nlinarith
    · have he : n + 1 = N := by omega
      rw [he, hτN]
      have hmn := hmin n hn
      constructor
      · linarith
      · have : r ^ N * T = r * (r ^ n * T) := by rw [← he, pow_succ]; ring
        nlinarith
  · have hlast := hmin (N - 1) (by omega)
    have hlog : Real.log δ < (N - 1 : ℕ) * Real.log r + Real.log T := by
      have := Real.log_lt_log hδ hlast
      rwa [Real.log_mul (by positivity) hT.ne', Real.log_pow] at this
    have hlr : Real.log r ≤ -hbar := by
      have := Real.log_le_sub_one_of_pos hr0
      linarith
    have hcast : ((N - 1 : ℕ) : ℝ) = N - 1 := by
      rw [Nat.cast_sub hN1, Nat.cast_one]
    rw [hcast] at hlog
    have hN0 : (0 : ℝ) ≤ N - 1 := by
      rw [← hcast]; exact Nat.cast_nonneg _
    rw [Real.log_div hT.ne' hδ.ne']
    have key : (N - 1) * hbar < Real.log T - Real.log δ := by nlinarith
    have : (N : ℝ) - 1 < hbar⁻¹ * (Real.log T - Real.log δ) := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hbar0]
      linarith
    linarith

/-- Step ratio `h̄ = ε² / (2d(1 + log(T/δ)))` of the DDPM parameter choice of GAPS 104.75. -/
def ddpmStepRatio (d : ℕ) (ε T δ : ℝ) : ℝ := ε ^ 2 / (2 * d * (1 + Real.log (T / δ)))

/-- GAPS 104.75: the parameter choice `h̄ = ε²/(2d(1 + log(T/δ)))` is positive for
`0 < ε² ≤ d` and `0 < δ < T`. -/
theorem ddpmStepRatio_pos {d : ℕ} {ε T δ : ℝ} (hε : 0 < ε) (hεd : ε ^ 2 ≤ d) (hδ : 0 < δ)
    (hδT : δ < T) : 0 < ddpmStepRatio d ε T δ := by
  have hd : (0 : ℝ) < d := (pow_pos hε 2).trans_le hεd
  have hL : 0 < Real.log (T / δ) := Real.log_pos ((one_lt_div hδ).2 hδT)
  unfold ddpmStepRatio
  positivity

/-- GAPS 104.75: the parameter choice `h̄ = ε²/(2d(1 + log(T/δ)))` is admissible, `h̄ ≤ 1/2`, for
`0 < ε² ≤ d` and `0 < δ < T`. -/
theorem ddpmStepRatio_le_half {d : ℕ} {ε T δ : ℝ} (hε : 0 < ε) (hεd : ε ^ 2 ≤ d) (hδ : 0 < δ)
    (hδT : δ < T) : ddpmStepRatio d ε T δ ≤ 1 / 2 := by
  have hd : (0 : ℝ) < d := (pow_pos hε 2).trans_le hεd
  have hL : 0 < Real.log (T / δ) := Real.log_pos ((one_lt_div hδ).2 hδT)
  have hden : 0 < 2 * d * (1 + Real.log (T / δ)) := by positivity
  rw [ddpmStepRatio, div_le_iff₀ hden]
  nlinarith

/-- GAPS 104.75: with `T = m₂²/ε²` and `h̄ = ε²/(2d(1 + log(T/δ)))`, the deterministic part
`m₂²/(2T) + 2h̄d(1 + log(T/δ))` of the KL bound equals `3ε²/2`. -/
theorem div_two_mul_add_two_mul_ddpmStepRatio_eq {d : ℕ} {m₂ ε δ : ℝ} (hε : 0 < ε)
    (hεd : ε ^ 2 ≤ d) (hδ : 0 < δ) (hδT : δ < m₂ ^ 2 / ε ^ 2) :
    m₂ ^ 2 / (2 * (m₂ ^ 2 / ε ^ 2)) +
        2 * ddpmStepRatio d ε (m₂ ^ 2 / ε ^ 2) δ * d * (1 + Real.log (m₂ ^ 2 / ε ^ 2 / δ)) =
      3 / 2 * ε ^ 2 := by
  have hd : (0 : ℝ) < d := (pow_pos hε 2).trans_le hεd
  have hT : 0 < m₂ ^ 2 / ε ^ 2 := hδ.trans hδT
  have hm' : m₂ ≠ 0 := by
    rintro rfl
    simp at hT
  have hL : 0 < Real.log (m₂ ^ 2 / ε ^ 2 / δ) := Real.log_pos ((one_lt_div hδ).2 hδT)
  have h1 : m₂ ^ 2 / (2 * (m₂ ^ 2 / ε ^ 2)) = ε ^ 2 / 2 := by field_simp
  have h2 : 2 * ddpmStepRatio d ε (m₂ ^ 2 / ε ^ 2) δ * d *
      (1 + Real.log (m₂ ^ 2 / ε ^ 2 / δ)) = ε ^ 2 := by
    have h0 : 1 + Real.log (m₂ ^ 2 / ε ^ 2 / δ) ≠ 0 := by positivity
    simp only [ddpmStepRatio]
    generalize 1 + Real.log (m₂ ^ 2 / ε ^ 2 / δ) = L at h0 ⊢
    field_simp
  rw [h1, h2]
  ring

/-- GAPS 104.75: with `h̄ = ε²/(2d(1 + log(T/δ)))`, the schedule bound `1 + h̄⁻¹ log(T/δ)` on the
number of steps equals `1 + 2dε⁻²(1 + log(T/δ)) log(T/δ)`. -/
theorem one_add_inv_ddpmStepRatio_mul_log (d : ℕ) (ε T δ : ℝ) :
    1 + (ddpmStepRatio d ε T δ)⁻¹ * Real.log (T / δ) =
      1 + 2 * d / ε ^ 2 * (1 + Real.log (T / δ)) * Real.log (T / δ) := by
  simp only [ddpmStepRatio, inv_div]
  ring

/-- A linear functional applied to a gradient, in Euclidean coordinates. -/
theorem clm_apply_gradient_eq_sum {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    L (gradient h x) = ∑ i, L (EuclideanSpace.single i 1) *
      fderiv ℝ h x (EuclideanSpace.single i 1) := by
  have hx : gradient h x = ∑ i, (gradient h x) i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (gradient h x)]
    simp
  have hc (i : Fin d) : (gradient h x) i = fderiv ℝ h x (EuclideanSpace.single i 1) := by
    have h1 : inner ℝ (gradient h x) (EuclideanSpace.single i (1 : ℝ)) = (gradient h x) i := by
      rw [EuclideanSpace.inner_single_right]; simp
    rw [← h1, gradient, InnerProductSpace.toDual_symm_apply]
  rw [hx, map_sum]
  simp [hc, mul_comm]

/-- The gradient of `log m` is `∇m / m` where `m` is differentiable and nonzero. -/
theorem gradient_log_eq_inv_smul {d : ℕ} (m : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hm : DifferentiableAt ℝ m x) (hx : m x ≠ 0) :
    gradient (fun y ↦ Real.log (m y)) x = (m x)⁻¹ • gradient m x := by
  rw [gradient, (hm.hasFDerivAt.log hx).fderiv, gradient, map_smul]

/-- Integration by parts on `ℝᵈ`: `∫ (∇f · ∇m + m Δf) = 0` for compactly supported `f`. -/
theorem integral_fderiv_gradient_add_mul_laplacian_eq_zero {d : ℕ}
    (m f : EuclideanSpace ℝ (Fin d) → ℝ) (hm : ContDiff ℝ 2 m) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∫ x, (fderiv ℝ f x (gradient m x) + m x * ∑ i, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) = 0 := by
  set e : Fin d → EuclideanSpace ℝ (Fin d) := fun i ↦ EuclideanSpace.single i 1 with he
  show ∫ x, (fderiv ℝ f x (gradient m x) +
    m x * ∑ i, fderiv ℝ (fderiv ℝ f) x (e i) (e i)) = 0
  have hmd : Differentiable ℝ m := hm.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable one_ne_zero
  have hmc' : Continuous (fderiv ℝ m) := hm.continuous_fderiv (by norm_num)
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv one_ne_zero
  have hHc (i : Fin d) : HasCompactSupport fun y ↦ fderiv ℝ (fderiv ℝ f) y (e i) (e i) :=
    ((hfc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ ↦
        L (e i) (e i)) (by simp)
  -- Each coordinate term is a total derivative.
  have hterm (i : Fin d) : ∫ x, (fderiv ℝ f x (e i) * fderiv ℝ m x (e i) +
      m x * fderiv ℝ (fderiv ℝ f) x (e i) (e i)) = 0 := by
    set g : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ fderiv ℝ f y (e i) with hg
    have hgd : Differentiable ℝ g := fun y ↦ (hfd y).clm_apply (differentiableAt_const _)
    have hgder (y : EuclideanSpace ℝ (Fin d)) :
        fderiv ℝ g y (e i) = fderiv ℝ (fderiv ℝ f) y (e i) (e i) := by
      rw [hg, fderiv_clm_apply (hfd y) (differentiableAt_const _)]
      simp
    have hgc : HasCompactSupport g := hfc.fderiv_apply (𝕜 := ℝ) (e i)
    have hgcont : Continuous g :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hg'cont : Continuous fun y ↦ fderiv ℝ g y (e i) := by
      simp_rw [hgder]; exact (hf2c.clm_apply continuous_const).clm_apply continuous_const
    have hg'c : HasCompactSupport fun y ↦ fderiv ℝ g y (e i) :=
      hgc.fderiv_apply (𝕜 := ℝ) (e i)
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := m) (g := g) (v := e i)
      (((hmc'.clm_apply continuous_const).mul hgcont).integrable_of_hasCompactSupport
        hgc.mul_left)
      ((hm.continuous.mul hg'cont).integrable_of_hasCompactSupport hg'c.mul_left)
      ((hm.continuous.mul hgcont).integrable_of_hasCompactSupport hgc.mul_left)
      (fun y _ ↦ hmd y) (fun y _ ↦ hgd y)
    simp_rw [hgder] at hibp
    rw [integral_add, hibp]
    · have hc : ∫ x, fderiv ℝ f x (e i) * fderiv ℝ m x (e i) =
          ∫ x, fderiv ℝ m x (e i) * g x := by
        congr 1; funext x; simp only [hg]; ring
      rw [hc]; ring
    · exact ((hgcont).mul (hmc'.clm_apply continuous_const)).integrable_of_hasCompactSupport
        hgc.mul_right
    · exact (hm.continuous.mul ((hf2c.clm_apply continuous_const).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hHc i).mul_left
  have hsum (x : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ f x (gradient m x) + m x * ∑ i, fderiv ℝ (fderiv ℝ f) x (e i) (e i) =
        ∑ i, (fderiv ℝ f x (e i) * fderiv ℝ m x (e i) +
          m x * fderiv ℝ (fderiv ℝ f) x (e i) (e i)) := by
    rw [clm_apply_gradient_eq_sum, Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [hsum]
  rw [integral_finsetSum (Finset.univ : Finset (Fin d))]
  · exact Finset.sum_eq_zero fun i _ ↦ hterm i
  · intro i _
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        (hmc'.clm_apply continuous_const)).add
        (hm.continuous.mul ((hf2c.clm_apply continuous_const).clm_apply continuous_const))
    · exact ((hfc.fderiv_apply (𝕜 := ℝ) (e i)).mul_right).add (hHc i).mul_left

/-- GAPS 104.76: smooth positive densities solving the continuity equation with velocity `v` also
solve the Fokker–Planck equation of `dX = (v + ε∇ log μ)(X) dt + √(2ε) dW`, for every continuous
`ε ≥ 0`. Both equations are taken in the weak integral form on `[0, 1]`. -/
theorem isFokkerPlanckSolution_add_score_of_continuityEquation {d : ℕ}
    (m : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hm : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (m t))
    (hmpos : ∀ t x, 0 < m t x)
    (v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ε : ℝ → ℝ)

    (hCE : IsFokkerPlanckSolution (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (m t x))
      v (fun _ _ ↦ 0) 1) :
    IsFokkerPlanckSolution (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (m t x))
      (fun t x ↦ v t x + ε t • gradient (fun y ↦ Real.log (m t y)) x)
      (fun t _ ↦ (2 * ε t) • 1) 1 := by
  obtain ⟨hprob, hweak⟩ := hCE
  refine ⟨hprob, fun f hf hfc t ht ↦ ?_⟩
  obtain ⟨hint, hii, hid⟩ := hweak f hf hfc t ht
  set μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)) :=
    fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (m t x) with hμ
  set X : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun s x ↦ ε s *
    (fderiv ℝ f x (gradient (fun y ↦ Real.log (m s y)) x) + ∑ i, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) with hX
  -- The new generator is the old one plus a term of zero mean.
  have hgen (s : ℝ) : diffusionGenerator
      (fun t x ↦ v t x + ε t • gradient (fun y ↦ Real.log (m t y)) x)
      (fun t _ ↦ (2 * ε t) • 1) f s =
        fun x ↦ diffusionGenerator v (fun _ _ ↦ 0) f s x + X s x := by
    funext x
    simp only [diffusionGenerator, hX, map_add, map_smul, smul_eq_mul, Matrix.smul_apply,
      Matrix.one_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      mul_ite, mul_one, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
    rw [mul_add, Finset.mul_sum, add_assoc]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hXc (s : ℝ) : Continuous (X s) := by
    have hlog : ContDiff ℝ (⊤ : ℕ∞) fun y ↦ Real.log (m s y) :=
      (hm s).log fun y ↦ (hmpos s y).ne'
    have hgc : Continuous fun x ↦ gradient (fun y ↦ Real.log (m s y)) x := by
      simp only [gradient]
      exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp
        (hlog.continuous_fderiv (by simp))
    have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by simp)
    refine continuous_const.mul (((hf.continuous_fderiv (by simp)).clm_apply hgc).add ?_)
    exact continuous_finsetSum _ fun i _ ↦
      ((hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply
        continuous_const
  have hXsupp (s : ℝ) : HasCompactSupport (X s) := by
    refine hfc.mono' fun x hx ↦ ?_
    by_contra h
    apply hx
    have h1 : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ h
    have h2 : fderiv ℝ (fderiv ℝ f) x = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h' ↦ h (tsupport_fderiv_subset ℝ h')
    simp [hX, h1, h2]
  have hXint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : Integrable (X s) (μ s) := by
    have := hprob s hs
    obtain ⟨C, hC⟩ := (hXc s).bounded_above_of_compact_support (hXsupp s)
    exact Integrable.of_bound (hXc s).aestronglyMeasurable C (ae_of_all _ hC)
  have hX0 (s : ℝ) : ∫ x, X s x ∂μ s = 0 := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul
      (hm s).continuous.measurable.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    have hpt (x : EuclideanSpace ℝ (Fin d)) : (ENNReal.ofReal (m s x)).toReal • X s x =
        ε s * (fderiv ℝ f x (gradient (m s) x) + m s x * ∑ i, fderiv ℝ (fderiv ℝ f) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) := by
      have hne := (hmpos s x).ne'
      rw [ENNReal.toReal_ofReal (hmpos s x).le, smul_eq_mul, hX]
      simp only
      rw [gradient_log_eq_inv_smul (m s) x ((hm s).differentiable (by simp) x) hne, map_smul,
        smul_eq_mul]
      field_simp
    simp_rw [hpt]
    rw [integral_const_mul, integral_fderiv_gradient_add_mul_laplacian_eq_zero (m s) f
      ((hm s).of_le (by simp)) hf2 hfc, mul_zero]
  have hcongr (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ∫ x, diffusionGenerator (fun t x ↦ v t x + ε t • gradient (fun y ↦ Real.log (m t y)) x)
        (fun t _ ↦ (2 * ε t) • 1) f s x ∂μ s =
      ∫ x, diffusionGenerator v (fun _ _ ↦ 0) f s x ∂μ s := by
    rw [hgen, integral_add (hweak f hf hfc s hs).1 (hXint s hs), hX0, add_zero]
  have hsub : ∀ s ∈ uIcc 0 t, s ∈ Icc (0 : ℝ) 1 := by
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hgen]
    exact hint.add (hXint t ht)
  · refine hii.congr fun s hs ↦ ?_
    exact (hcongr s (hsub s (uIoc_subset_uIcc hs))).symm
  · rw [hid]
    congr 1
    exact intervalIntegral.integral_congr fun s hs ↦ (hcongr s (hsub s hs)).symm

/-- GAPS 104.76, constant noise level: if the jointly Borel drift `bₜ = vₜ + ε∇ log μₜ` is
Lipschitz uniformly in `t ∈ [0, 1]` and `∫₀¹ ∫ ‖bₜ‖ dμₜ dt < ∞`, a continuous solution with
interval-integrable pathwise drift of `Xₜ = X₀ + ∫₀ᵗ bₛ(Xₛ) ds + √(2ε) Wₜ`
with `X₀ ∼ μ₀` independent of the Brownian motion has law `μₜ` for every `t ∈ [0, 1]`. -/
theorem map_marginalPreservingDiffusion {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hm : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (m t))
    (hmpos : ∀ t x, 0 < m t x)
    (v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hε : 0 ≤ ε)
    (hCE : IsFokkerPlanckSolution (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (m t x))
      v (fun _ _ ↦ 0) 1)
    (hbm : Measurable (fun q : Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin d) ↦
      v q.1 q.2 + ε • gradient (fun y ↦ Real.log (m q.1 y)) q.2))
    (K : ℝ≥0) (hLip : ∀ t ∈ Icc (0 : ℝ) 1,
      LipschitzWith K fun x ↦ v t x + ε • gradient (fun y ↦ Real.log (m t y)) x)
    (hint : ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ x,
      ‖v t x + ε • gradient (fun y ↦ Real.log (m t y)) x‖ₑ * ENNReal.ofReal (m t x) < ∞)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hW : IsBrownianEuclidean W P)
    (X : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hXm : ∀ t, Measurable (X t))
    (hind : IndepFun (X 0) (fun ω t ↦ W t ω) P)
    (hX0 : P.map (X 0) = volume.withDensity fun x ↦ ENNReal.ofReal (m 0 x))
    (hXi : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (fun s ↦ v s (X s ω) +
        ε • gradient (fun y ↦ Real.log (m s y)) (X s ω)) volume 0 t)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧ ∀ t ∈ Icc (0 : ℝ) 1, X t ω = X 0 ω +
      (∫ s in (0 : ℝ)..t, v s (X s ω) + ε • gradient (fun y ↦ Real.log (m s y)) (X s ω)) +
        Real.sqrt (2 * ε) • W t.toNNReal ω) :
    ∀ t ∈ Icc (0 : ℝ) 1, P.map (X t) = volume.withDensity fun x ↦ ENNReal.ofReal (m t x) := by
  sorry

/-- GAPS 104.76: the score of a stochastic interpolant. For `Xₜ = Iₜ(X₀, X₁) + γₜ Z` with standard
normal `Z` independent of the coupling and `γₜ > 0`, the law of `Xₜ` has a smooth positive density
`mₜ` and `∇ log mₜ(Xₜ) = -γₜ⁻¹ 𝔼[Z | Xₜ]` almost surely. -/
theorem stochasticInterpolant_score {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ : ℝ → ℝ)
    (hIm : ∀ t, Measurable fun w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      I t w.1 w.2)
    (X₀ X₁ Z : Ω → EuclideanSpace ℝ (Fin d)) (hX₀ : Measurable X₀) (hX₁ : Measurable X₁)
    (hZ : Measurable Z) (hZlaw : P.map Z = stdGaussian (EuclideanSpace ℝ (Fin d)))
    (hind : IndepFun (fun ω ↦ (X₀ ω, X₁ ω)) Z P) (t : ℝ) (hγt : 0 < γ t) :
    let X := fun ω ↦ I t (X₀ ω) (X₁ ω) + γ t • Z ω
    ∃ mt : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) mt ∧ (∀ x, 0 < mt x) ∧
      P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (mt x)) ∧
      (fun ω ↦ gradient (fun y ↦ Real.log (mt y)) (X ω)) =ᵐ[P]
        fun ω ↦ -(γ t)⁻¹ • P[Z | MeasurableSpace.comap X inferInstance] ω := by
  intro X
  let Y := fun w ↦ I t (X₀ w) (X₁ w)
  let ν := P.map Y
  let σ := γ t
  have hσ : 0 < σ := hγt
  have hY : Measurable Y := (hIm t).comp (hX₀.prodMk hX₁)
  have hXm : Measurable X := hY.add (hZ.const_smul σ)
  have hind' : IndepFun Y Z P := by
    simpa [Y, Function.comp_def] using hind.comp (hIm t) measurable_id
  have hYZ : P.map (fun w ↦ (Y w, Z w)) = ν.prod (stdGaussian _) := by
    rw [hind'.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable, hZlaw]
  let m := fun x ↦ ∫ y, gaussianSmoothingKernel σ (x - y) ∂ν
  obtain ⟨hms, hmpos⟩ := smooth_positive_gaussianSmoothing ν hσ
  have hXmLaw : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (m x)) := by
    calc _ = (P.map (fun w ↦ (Y w, Z w))).map (fun p ↦ p.1 + σ • p.2) := by
            rw [Measure.map_map (by fun_prop) (hY.prodMk hZ)]
            rfl
      _ = _ := by rw [hYZ, map_add_gaussian_eq_withDensity ν hσ]
  refine ⟨m, hms, hmpos, hXmLaw, ?_⟩
  have hYX : P.map (fun w ↦ (Y w, X w)) = (ν.prod volume).withDensity
      (fun p ↦ ENNReal.ofReal (gaussianSmoothingKernel σ (p.2 - p.1))) := by
    calc _ = (P.map (fun w ↦ (Y w, Z w))).map (fun p ↦ (p.1, p.1 + σ • p.2)) := by
            rw [Measure.map_map (by fun_prop) (hY.prodMk hZ)]
            rfl
      _ = _ := by rw [hYZ, map_pair_add_gaussian_eq_withDensity ν hσ]
  let H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun p ↦ σ⁻¹ • (p.2 - p.1)
  have hH : Measurable H := by fun_prop
  have hHcomp : (fun w ↦ H (Y w, X w)) = Z := by
    funext w
    simp [H, X, Y, σ, smul_smul, hγt.ne']
  have hZi : Integrable Z P := by
    have hi : Integrable id (P.map Z) := by rw [hZlaw]; exact IsGaussian.integrable_id
    exact hi.comp_measurable hZ
  have hC := condExp_of_joint_density P ν volume Y X hY hXm
    (fun p ↦ gaussianSmoothingKernel σ (p.2 - p.1))
    ((contDiff_gaussianSmoothingKernel hσ).continuous.measurable.comp
      (measurable_snd.sub measurable_fst))
    (fun p ↦ (gaussianSmoothingKernel_pos hσ _).le) m hms.continuous.measurable hmpos
    hYX hXmLaw H hH (hHcomp ▸ hZi)
  rw [hHcomp] at hC
  filter_upwards [hC] with w hw
  rw [← hw, gradient_log_eq_inv_smul m (X w) (hms.differentiable (by simp) _) (hmpos _).ne',
    gradient_gaussianSmoothing ν hσ]
  change (m (X w))⁻¹ • (-(σ ^ 2)⁻¹ • ∫ y, gaussianSmoothingKernel σ (X w - y) • (X w - y) ∂ν) =
    -σ⁻¹ • ((m (X w))⁻¹ • ∫ y, gaussianSmoothingKernel σ (X w - y) • (σ⁻¹ • (X w-y)) ∂ν)
  simp_rw [smul_comm (gaussianSmoothingKernel σ _) σ⁻¹, integral_smul, smul_smul]
  congr 1
  field_simp

/-- GAPS 104.76: the velocity of a stochastic interpolant, in the weak form of the continuity
equation. Let `Xₜ = Iₜ(X₀, X₁) + γₜ Z` with `I` and `γ` continuously differentiable in `t`,
and `∫₀¹ 𝔼‖∂ₜIₜ(X₀, X₁)‖² dt < ∞` (continuity of `γ̇` makes a bound on `∫₀¹ γ̇ₜ² dt`
unnecessary), and let `vₜ(Xₜ)` be, for every
`t ∈ (0, 1)`, a version of `𝔼[∂ₜIₜ + γ̇ₜ Z | Xₜ]`. Then for every smooth compactly supported `φ`
and `0 < a ≤ b < 1`, `𝔼 φ(X_b) - 𝔼 φ(X_a) = ∫ₐᵇ 𝔼[∇φ(Xₜ) · vₜ(Xₜ)] dt`. The square-integrability
in `t` does not make `∂ₜIₜ` integrable at every fixed `t`, so the identity is stated in
integrated form. -/
theorem stochasticInterpolant_integral_sub_eq_integral_velocity {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (I dI : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ dγ : ℝ → ℝ)
    (hdI : ∀ t x₀ x₁, HasDerivAt (fun s ↦ I s x₀ x₁) (dI t x₀ x₁) t)
    (hdIc : ∀ x₀ x₁, Continuous fun t ↦ dI t x₀ x₁)
    (hIm : ∀ t, Measurable fun w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      I t w.1 w.2)
    (hdIm : ∀ t, Measurable fun w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      dI t w.1 w.2)
    (hdγ : ∀ t, HasDerivAt γ (dγ t) t) (hdγc : Continuous dγ)
    (X₀ X₁ Z : Ω → EuclideanSpace ℝ (Fin d)) (hX₀ : Measurable X₀) (hX₁ : Measurable X₁)
    (hZ : Measurable Z) (hZlaw : P.map Z = stdGaussian (EuclideanSpace ℝ (Fin d)))
    (hdI2 : ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ ω, ‖dI t (X₀ ω) (X₁ ω)‖ₑ ^ 2 ∂P < ∞) :
    let X := fun t ω ↦ I t (X₀ ω) (X₁ ω) + γ t • Z ω
    ∀ v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ t ∈ Ioo (0 : ℝ) 1, (fun ω ↦ v t (X t ω)) =ᵐ[P]
        P[fun ω ↦ dI t (X₀ ω) (X₁ ω) + dγ t • Z ω | MeasurableSpace.comap (X t) inferInstance]) →
      ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, a ≤ b →
          ∫ ω, φ (X b ω) ∂P - ∫ ω, φ (X a ω) ∂P =
            ∫ t in a..b, ∫ ω, fderiv ℝ φ (X t ω) (v t (X t ω)) ∂P := by
  intro X v hv φ hφ hφc a ha b hb hab
  set W : ℝ → Ω → EuclideanSpace ℝ (Fin d) := fun t ω ↦ dI t (X₀ ω) (X₁ ω) + dγ t • Z ω with hW
  set F : ℝ → Ω → ℝ := fun t ω ↦ fderiv ℝ φ (X t ω) (W t ω) with hF
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hφ'c.bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  -- pathwise calculus
  have hXd (ω : Ω) (t : ℝ) : HasDerivAt (fun s ↦ X s ω) (W t ω) t :=
    (hdI t _ _).add ((hdγ t).smul_const (Z ω))
  have hXc (ω : Ω) : Continuous fun t ↦ X t ω :=
    continuous_iff_continuousAt.2 fun t ↦ (hXd ω t).continuousAt
  have hWc (ω : Ω) : Continuous fun t ↦ W t ω := (hdIc _ _).add (hdγc.smul continuous_const)
  have hFc (ω : Ω) : Continuous fun t ↦ F t ω :=
    (hφ'c.comp (hXc ω)).clm_apply (hWc ω)
  have hFTC (ω : Ω) : φ (X b ω) - φ (X a ω) = ∫ t in a..b, F t ω := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s ↦ φ (X s ω))
      (fun t _ ↦ ?_) ((hFc ω).intervalIntegrable a b)).symm
    exact (hφd _).hasFDerivAt.comp_hasDerivAt t (hXd ω t)
  -- measurability
  have hXm (t : ℝ) : Measurable (X t) :=
    ((hIm t).comp (hX₀.prodMk hX₁)).add (hZ.const_smul (γ t))
  have hdIm' (t : ℝ) : Measurable fun ω ↦ dI t (X₀ ω) (X₁ ω) := (hdIm t).comp (hX₀.prodMk hX₁)
  have hWm (t : ℝ) : Measurable (W t) := (hdIm' t).add (hZ.const_smul (dγ t))
  have hFm (t : ℝ) : Measurable (F t) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hφ'c.measurable.comp (hXm t)).prodMk (hWm t))
  have hFjm : Measurable (Function.uncurry F) :=
    measurable_uncurry_of_continuous_of_measurable hFc hFm
  have hdIjm : Measurable (Function.uncurry fun t ω ↦ dI t (X₀ ω) (X₁ ω)) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω ↦ hdIc _ _) hdIm'
  -- integrability of the drift of the interpolation
  have hdIint : Integrable (fun p : ℝ × Ω ↦ dI p.1 (X₀ p.2) (X₁ p.2)) (μ.prod P) := by
    refine ⟨hdIjm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod (f := fun p : ℝ × Ω ↦ ‖dI p.1 (X₀ p.2) (X₁ p.2)‖ₑ)
      hdIjm.enorm.aemeasurable]
    have hpt (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ₑ ≤ 1 + ‖x‖ₑ ^ 2 := by
      by_cases h : ‖x‖ₑ ≤ 1
      · exact le_add_right h
      · exact (le_self_pow₀ (not_le.1 h).le two_ne_zero).trans le_add_self
    calc ∫⁻ t, ∫⁻ ω, ‖dI t (X₀ ω) (X₁ ω)‖ₑ ∂P ∂μ
        ≤ ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ ω, ‖dI t (X₀ ω) (X₁ ω)‖ₑ ∂P :=
          lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ha.1.le hb.2.le))
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, (1 + ∫⁻ ω, ‖dI t (X₀ ω) (X₁ ω)‖ₑ ^ 2 ∂P) := by
          refine lintegral_mono fun t ↦ ?_
          calc ∫⁻ ω, ‖dI t (X₀ ω) (X₁ ω)‖ₑ ∂P ≤ ∫⁻ ω, (1 + ‖dI t (X₀ ω) (X₁ ω)‖ₑ ^ 2) ∂P :=
                lintegral_mono fun ω ↦ hpt _
            _ = _ := by
                rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
      _ < ∞ := by
          rw [lintegral_add_left measurable_const, lintegral_const]
          exact ENNReal.add_lt_top.2 ⟨by simp, hdI2⟩
  have hZint : Integrable Z P := by
    have := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin d))) 1
      (by simp)).integrable le_rfl
    rw [← hZlaw, integrable_map_measure this.aestronglyMeasurable hZ.aemeasurable] at this
    exact this
  have hdγint : Integrable dγ μ :=
    (hdγc.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have hFint : Integrable (Function.uncurry F) (μ.prod P) := by
    refine Integrable.mono' ((hdIint.norm.add (hdγint.norm.mul_prod hZint.norm)).const_mul M)
      hFjm.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    simp only [Function.uncurry, hF, hW]
    calc ‖fderiv ℝ φ (X p.1 p.2) (dI p.1 (X₀ p.2) (X₁ p.2) + dγ p.1 • Z p.2)‖
        ≤ M * ‖dI p.1 (X₀ p.2) (X₁ p.2) + dγ p.1 • Z p.2‖ :=
          ((fderiv ℝ φ _).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      _ ≤ M * (‖dI p.1 (X₀ p.2) (X₁ p.2)‖ + ‖dγ p.1‖ * ‖Z p.2‖) := by
          have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
          gcongr
          exact (norm_add_le _ _).trans_eq (by rw [norm_smul])
  -- Fubini
  have hφint (t : ℝ) : Integrable (fun ω ↦ φ (X t ω)) P :=
    Integrable.of_bound (hφ.continuous.measurable.comp (hXm t)).aestronglyMeasurable Mφ
      (ae_of_all _ fun ω ↦ hMφ _)
  have hlhs : ∫ ω, φ (X b ω) ∂P - ∫ ω, φ (X a ω) ∂P = ∫ t in a..b, ∫ ω, F t ω ∂P := by
    rw [← integral_sub (hφint b) (hφint a)]
    simp_rw [hFTC, intervalIntegral.integral_of_le hab]
    exact integral_integral_swap (f := fun ω t ↦ F t ω) hFint.swap
  rw [hlhs]
  -- conditioning for almost every time
  refine intervalIntegral.integral_congr_ae ?_
  have hae : ∀ᵐ t ∂μ, Integrable (fun ω ↦ dI t (X₀ ω) (X₁ ω)) P := hdIint.prod_right_ae
  rw [hμ, ae_restrict_iff' measurableSet_Ioc] at hae
  filter_upwards [hae] with t ht htab
  rw [uIoc_of_le hab] at htab
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans htab.1, htab.2.trans_lt hb.2⟩
  have hWint : Integrable (W t) P := (ht htab).add (Integrable.smul (dγ t) hZint)
  have hmle : MeasurableSpace.comap (X t) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hXm t).comap_le
  have hDm : StronglyMeasurable[MeasurableSpace.comap (X t) inferInstance]
      fun ω ↦ fderiv ℝ φ (X t ω) :=
    (hφ'c.measurable.comp (comap_measurable (X t))).stronglyMeasurable
  have hpull := condExp_stronglyMeasurable_bilin_of_bound
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) hmle hDm hWint M
    (ae_of_all _ fun ω ↦ hM _)
  calc ∫ ω, F t ω ∂P = ∫ ω, (P[fun ω ↦
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (fderiv ℝ φ (X t ω))
          (W t ω) | MeasurableSpace.comap (X t) inferInstance]) ω ∂P :=
        (integral_condExp hmle).symm
    _ = ∫ ω, fderiv ℝ φ (X t ω) (v t (X t ω)) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hv t ht01] with ω h1 h2
        rw [h1, ← h2]
        rfl

end CKSD
