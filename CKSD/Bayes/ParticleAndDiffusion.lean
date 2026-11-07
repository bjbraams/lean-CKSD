module

public import CKSD.Bayes.Basic
public import CKSD.Asymptotics.Basic

/-!
# Particle filters and weak diffusion equations

A Feynman–Kac specification consists of Markov transitions and positive bounded potentials.
Its unnormalized laws and bootstrap proposal laws are explicit measure constructions. Weak
Fokker–Planck solutions are specified by their integral identity on smooth compactly supported tests;
this definition does not assert existence of an SDE solution or supply a stochastic integral.
Sources: GAPS 104.37–104.60, 104.63, and 104.75–104.76.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Feynman–Kac model with fixed observations encoded in its potentials. -/
structure FeynmanKacModel (X : Type*) [MeasurableSpace X] where
  /-- Initial probability law. -/
  initial : ProbabilityMeasure X
  /-- Transition kernel from generation `n` to generation `n+1`. -/
  transition : ℕ → Kernel X X
  /-- Each transition is Markov. -/
  isMarkov_transition : ∀ n, IsMarkovKernel (transition n)
  /-- Observation potential of each generation. -/
  potential : ℕ → X → ℝ
  /-- Measurability of each potential. -/
  measurable_potential : ∀ n, Measurable (potential n)
  /-- Strict positivity of each potential. -/
  potential_pos : ∀ n x, 0 < potential n x
  /-- Upper and positive lower bounds, allowed to depend on the time. -/
  potential_bounds : ∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ x, potential n x ∈ Icc a b

/-- Unnormalized Feynman–Kac measure at generation `n`. -/
def FeynmanKacModel.unnormalizedLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) : ℕ → Measure X
  | 0 => M.initial
  | n + 1 => M.transition n ∘ₘ (M.unnormalizedLaw n).withDensity
      (fun x ↦ ENNReal.ofReal (M.potential n x))

/-- Normalized filtering law. -/
def FeynmanKacModel.filterLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : Measure X :=
  (M.unnormalizedLaw n univ)⁻¹ • M.unnormalizedLaw n

/-- Bootstrap prediction law from the weighted particles at the current generation. -/
def FeynmanKacModel.particlePredictionLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (n : ℕ) (x : Fin N → X) : Measure X :=
  (∑ i, ENNReal.ofReal (M.potential n (x i)))⁻¹ •
    ∑ i, ENNReal.ofReal (M.potential n (x i)) • M.transition n (x i)

/-- Bootstrap-particle likelihood estimate as a product of mean potentials. -/
def FeynmanKacModel.particleLikelihood {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (particles : ℕ → Fin N → X) (n : ℕ) : ℝ :=
  ∏ p ∈ Finset.range n, (∑ i, M.potential p (particles p i)) / N

/-- Bootstrap sampling: conditional on the entire past, next particles are independent draws
from the weighted prediction law. This specifies a simulation protocol rather than its limits. -/
def IsBootstrapParticleSystem {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : FeynmanKacModel X) (N : ℕ) (ξ : ℕ → Ω → Fin N → X) : Prop :=
  (∀ n, Measurable (ξ n)) ∧
    P.map (ξ 0) = Measure.pi (fun _ : Fin N ↦ (M.initial : Measure X)) ∧
    ∀ n, ∀ᵐ ω ∂P,
      condDistrib (ξ (n + 1)) (fun (ω : Ω) (i : Fin (n + 1)) ↦ ξ i.val ω) P
        (fun i : Fin (n + 1) ↦ ξ i.val ω) =
          Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω))

/-- GAPS 104.55: fixed-time consistency of the multinomial bootstrap particle filter. -/
theorem tendstoInProbabilityConst_particle_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (n : ℕ) :
    TendstoInProbabilityConst P
      (fun N ω ↦ (∑ i, f (ξ N n ω i)) / (N + 1)) (∫ x, f x ∂M.filterLaw n) := by
  sorry

/-- GAPS 104.58: unbiased likelihood estimate for multinomial resampling. -/
theorem integral_particleLikelihood_eq {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X)
    (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ) :
    (∫ ω, M.particleLikelihood (fun p ↦ ξ p ω) n ∂P) = (M.unnormalizedLaw n).real univ := by
  sorry

/-- Gibbs law normalized by its partition integral. Use under finite positive normalizer
hypotheses. -/
def gibbsMeasure {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  let Z := ∫ x, Real.exp (-V x)
  volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x) / Z))

/-- Diffusion generator in Euclidean coordinates for drift `b` and infinitesimal covariance `A`. -/
def diffusionGenerator {d : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ f x (b t x) + (1 / 2 : ℝ) *
    ∑ i, ∑ j, A t x i j *
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Weak integral formulation of the Fokker–Planck equation on `[0,T]`. -/
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

/-- Euler–Maruyama step with an already sampled standard Gaussian increment. -/
def eulerMaruyamaStep {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • b x + Real.sqrt h • σ z

/-- Unadjusted Langevin one-step law, with noise variance `2h`. -/
def langevinStepLaw {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
    (fun z ↦ z.1 - h • gradV z.1 + Real.sqrt (2 * h) • z.2)

/-- Acceptance probability of Metropolis-adjusted Langevin with proposal variance `2h`. -/
def malaAcceptance {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  min 1 (Real.exp (V x - V y +
    (‖y - x + h • gradV x‖ ^ 2 - ‖x - y + h • gradV y‖ ^ 2) / (4 * h)))

/-- DDPM update for variance-exploding Brownian noising, using the remaining time `t`. -/
def ddpmStep {d : ℕ} (score : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • score x + Real.sqrt ((t - h) * h / t) • z

/-- Feynman–Kac normalization starts from the specified prior law. -/
@[simp] theorem FeynmanKacModel.unnormalizedLaw_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) : M.unnormalizedLaw 0 = (M.initial : Measure X) := rfl

/-- The particle likelihood of an empty observation sequence is one. -/
@[simp] theorem FeynmanKacModel.particleLikelihood_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (particles : ℕ → Fin N → X) :
    M.particleLikelihood particles 0 = 1 := by simp [particleLikelihood]

end CKSD
