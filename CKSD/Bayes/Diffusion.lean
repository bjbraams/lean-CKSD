module

public import CKSD.Bayes.Basic

/-!
# Gibbs laws, diffusion generators, and discretized Langevin dynamics

Shared vocabulary for the diffusion-based sampling and generative-modelling files of Section 104.
A diffusion is represented through the weak (distributional) form of its Fokker–Planck equation on
smooth compactly supported test functions; no stochastic differential equation or stochastic
integral is constructed. Discretizations are given by explicit update maps, or by their action on
laws when the Gaussian increment is integrated out.

## Main definitions

* `CKSD.gibbsMeasure V`: the Gibbs law with Lebesgue density `e^{-V} / ∫ e^{-V}`.
* `CKSD.diffusionGenerator b A f t x`: the generator `⟨∇f, b⟩ + ½ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f` of a diffusion
  with drift `b` and infinitesimal covariance `A`.
* `CKSD.IsFokkerPlanckSolution μ b A T`: `t ↦ μ t` is a weak solution on `[0, T]` of the
  Fokker–Planck equation of that generator.
* `CKSD.eulerMaruyamaStep`, `CKSD.langevinStepLaw`, `CKSD.malaAcceptance`, `CKSD.ddpmStep`: the
  Euler–Maruyama update, the law of one step of the unadjusted Langevin algorithm, the acceptance
  probability of the Metropolis-adjusted Langevin algorithm, and the denoising update of a
  variance-exploding diffusion model.

## Main results

* `CKSD.isProbabilityMeasure_gibbsMeasure`: the Gibbs law is a probability measure when `e^{-V}`
  is integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Gibbs law `e^{-V(x)} dx / Z` with partition integral `Z = ∫ e^{-V}`. It is a probability
measure when `e^{-V}` is integrable (`isProbabilityMeasure_gibbsMeasure`); otherwise the Bochner
integral `Z` is zero and the definition carries no meaning. -/
def gibbsMeasure {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  let Z := ∫ x, Real.exp (-V x)
  volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x) / Z))

/-- If `e^{-V}` is integrable, the Gibbs law is a probability measure. -/
theorem isProbabilityMeasure_gibbsMeasure {d : ℕ} {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Integrable (fun x ↦ Real.exp (-V x))) : IsProbabilityMeasure (gibbsMeasure V) := by
  have hZ : 0 < ∫ x, Real.exp (-V x) :=
    integral_exp_pos (μ := volume) (f := fun x ↦ -V x) hV
  constructor
  rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hV.div_const _)
      (ae_of_all _ fun x ↦ div_nonneg (Real.exp_pos _).le hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

/-- Generator `L f(x) = ⟨∇f(x), b(t,x)⟩ + ½ ∑ᵢⱼ A(t,x)ᵢⱼ ∂ᵢ∂ⱼ f(x)` of a diffusion with drift `b`
and infinitesimal covariance `A`, in Euclidean coordinates. -/
def diffusionGenerator {d : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ f x (b t x) + (1 / 2 : ℝ) *
    ∑ i, ∑ j, A t x i j *
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Weak Fokker–Planck equation on `[0, T]`: every `μ t` is a probability measure and, for every
smooth compactly supported test function `f`, `∫ f dμₜ = ∫ f dμ₀ + ∫₀ᵗ ∫ L f dμₛ ds`, with the
integrability needed to make sense of the right side. -/
def IsFokkerPlanckSolution {d : ℕ}
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)))
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, IsProbabilityMeasure (μ t)) ∧
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ⊤ f → HasCompactSupport f →
      ∀ t ∈ Icc 0 T,
        Integrable (diffusionGenerator b A f t) (μ t) ∧
        IntervalIntegrable (fun s ↦ ∫ x, diffusionGenerator b A f s x ∂μ s) volume 0 t ∧
        (∫ x, f x ∂μ t) = (∫ x, f x ∂μ 0) +
          ∫ s in (0 : ℝ)..t, ∫ x, diffusionGenerator b A f s x ∂μ s

/-- Euler–Maruyama step `x + h b(x) + √h σ z` with an already sampled standard Gaussian
increment `z`. -/
def eulerMaruyamaStep {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • b x + Real.sqrt h • σ z

/-- Law after one step `x ↦ x - h ∇V(x) + √(2h) Z` of the unadjusted Langevin algorithm started
from the law `P`, with `Z` an independent standard Gaussian vector. -/
def langevinStepLaw {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
    (fun z ↦ z.1 - h • gradV z.1 + Real.sqrt (2 * h) • z.2)

/-- Acceptance probability of a move from `x` to `y` in the Metropolis-adjusted Langevin
algorithm with target `e^{-V}` and Gaussian proposal `N(x - h ∇V(x), 2h I)`. -/
def malaAcceptance {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  min 1 (Real.exp (V x - V y +
    (‖y - x + h • gradV x‖ ^ 2 - ‖x - y + h • gradV y‖ ^ 2) / (4 * h)))

/-- Denoising (DDPM) update `x + h s(x) + √((t - h) h / t) z` for variance-exploding Brownian
noising, with fitted score `s`, remaining time `t`, step `h`, and a standard Gaussian draw `z`. -/
def ddpmStep {d : ℕ} (score : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • score x + Real.sqrt ((t - h) * h / t) • z

end CKSD
