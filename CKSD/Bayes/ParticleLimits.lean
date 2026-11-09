module

public import CKSD.Bayes.ParticleFilter

/-!
# Feynman–Kac semigroups and particle fluctuations

Central limit theorems and uniform-in-time error bounds for the bootstrap particle filter of a
Feynman–Kac model. The backwards operator over `m` transitions from time `p` includes the
potentials from time `p` through time `p + m - 1`, so that the zero-step operator is the identity,
matching the normalization of the filtering laws of `CKSD.FeynmanKacModel`.

## Main definitions

* `CKSD.FeynmanKacModel.backwardOperator`: the backwards Feynman–Kac operator.
* `CKSD.FeynmanKacModel.particleAverageAsymptoticVariance`,
  `CKSD.FeynmanKacModel.particleLikelihoodAsymptoticVariance`: the asymptotic variances of the
  particle average and of the normalized likelihood estimate.

## Main results

* `CKSD.tendstoInDistribution_particle_average`,
  `CKSD.tendstoInDistribution_particle_likelihood`: fixed-time central limit theorems.
* `CKSD.exists_uniform_particle_moment_bound`: a uniform-in-time `Lᵖ` bound under mixing.

Sources: GAPS 104.59 and GAPS 104.60.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Backwards Feynman–Kac operator over `m` transitions starting at time `p`. -/
def FeynmanKacModel.backwardOperator {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p : ℕ) : ℕ → (X → ℝ) → X → ℝ
  | 0, f => f
  | m + 1, f => fun x ↦ M.potential p x *
      ∫ y, M.backwardOperator (p + 1) m f y ∂M.transition p x

/-- Asymptotic variance of the bootstrap particle average of `f` at time `n`:
`∑_{p ≤ n} 𝛈ₚ((Q_{p,n}(f - 𝛈ₙ f))²) / 𝛈ₚ(Q_{p,n} 1)²`, with `𝛈ₚ` the filtering law and `Q_{p,n}`
the backwards operator over `n - p` transitions from time `p`. -/
def FeynmanKacModel.particleAverageAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) : ℝ :=
  let centered := fun x ↦ f x - ∫ y, f y ∂M.filterLaw n
  ∑ p ∈ Finset.range (n + 1),
    (∫ x, (M.backwardOperator p (n - p) centered x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2

/-- Asymptotic variance of the particle likelihood estimate at time `n`, normalized by the true
likelihood: `∑_{p ≤ n} (𝛈ₚ((Q_{p,n} 1)²) / 𝛈ₚ(Q_{p,n} 1)² - 1)`. -/
def FeynmanKacModel.particleLikelihoodAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1),
    ((∫ x, (M.backwardOperator p (n - p) (fun _ ↦ 1) x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2 - 1)

/-- With unit potentials, the backwards operator preserves the constant one function. -/
theorem FeynmanKacModel.backwardOperator_one_of_potential_eq_one
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    (hpotential : ∀ p x, M.potential p x = 1) (p m : ℕ) :
    M.backwardOperator p m (fun _ ↦ 1) = fun _ ↦ 1 := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    funext x
    have := M.isMarkov_transition p
    simp [FeynmanKacModel.backwardOperator, ih, hpotential]

/-- At time zero the likelihood estimate is deterministic and its asymptotic variance is zero. -/
@[simp] theorem FeynmanKacModel.particleLikelihoodAsymptoticVariance_zero
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) :
    M.particleLikelihoodAsymptoticVariance 0 = 0 := by
  simp [FeynmanKacModel.particleLikelihoodAsymptoticVariance, FeynmanKacModel.backwardOperator]

/-- Unit observation potentials give zero likelihood-estimation asymptotic variance. -/
theorem FeynmanKacModel.particleLikelihoodAsymptoticVariance_eq_zero_of_potential_eq_one
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    (hpotential : ∀ p x, M.potential p x = 1) (n : ℕ) :
    M.particleLikelihoodAsymptoticVariance n = 0 := by
  simp [FeynmanKacModel.particleLikelihoodAsymptoticVariance,
    M.backwardOperator_one_of_potential_eq_one hpotential]

/-- GAPS 104.59: central limit theorem for the bootstrap particle filter at a fixed time `n`.
For a bounded measurable `f`, `√N (N⁻¹ ∑ᵢ f(ξᵢ) - 𝛈ₙ f)` converges in distribution to the centred
normal law with variance `particleAverageAsymptoticVariance n f`. -/
theorem tendstoInDistribution_particle_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (n : ℕ) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ Real.sqrt (N + 1) *
        ((∑ i, f (ξ N n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n)) atTop id (fun _ ↦ P)
      (gaussianReal 0 (Real.toNNReal (M.particleAverageAsymptoticVariance n f))) := by
  sorry

/-- GAPS 104.59: central limit theorem for the particle likelihood estimate at a fixed time `n`.
The relative error `√N (Ẑₙ / Zₙ - 1)` converges in distribution to the centred normal law with
variance `particleLikelihoodAsymptoticVariance n`. -/
theorem tendstoInDistribution_particle_likelihood {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N)) (n : ℕ) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ Real.sqrt (N + 1) *
        (M.particleLikelihood (fun p ↦ ξ N p ω) n / (M.unnormalizedLaw n).real univ - 1))
      atTop id (fun _ ↦ P)
      (gaussianReal 0 (Real.toNNReal (M.particleLikelihoodAsymptoticVariance n))) := by
  sorry

/-- GAPS 104.60: uniform-in-time `Lᵖ` particle error bound for a fixed mixing model.
The bound is uniform in time, particle number, and test functions with oscillation at most one;
no model-independent value of the constant is claimed by this formulation. -/
theorem exists_uniform_particle_moment_bound {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (εG εM : ℝ) (hG : εG ∈ Ioc 0 1) (hM : εM ∈ Ioc 0 1)
    (hpotential : ∀ n x y, εG * M.potential n y ≤ M.potential n x)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal εM * M.transition n y A ≤ M.transition n x A)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ N : ℕ, ∀ ξ : ℕ → Ω → Fin (N + 1) → X,
      IsBootstrapParticleSystem P M (N + 1) ξ → ∀ n : ℕ, ∀ f : X → ℝ, Measurable f →
      (∀ x y, |f x - f y| ≤ 1) →
      Real.sqrt (N + 1) * Real.rpow
        (∫ ω, |(∑ i, f (ξ n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n| ^ p ∂P) (1 / p) ≤
          C / (εM ^ 2 * εG) := by
  sorry

/-- A zero-step backwards operator is the identity. -/
@[simp] theorem FeynmanKacModel.backwardOperator_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p : ℕ) (f : X → ℝ) : M.backwardOperator p 0 f = f := rfl

/-- Each particle-average asymptotic variance is nonnegative. -/
theorem FeynmanKacModel.particleAverageAsymptoticVariance_nonneg
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) :
    0 ≤ M.particleAverageAsymptoticVariance n f := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)) (sq_nonneg _)

end CKSD
