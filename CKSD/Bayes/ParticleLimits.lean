module

public import CKSD.Bayes.ParticleAndDiffusion

/-!
# Feynman–Kac semigroups and particle fluctuations

The backwards operator includes potentials from time `p` through time `p+m-1`.
Thus the terminal case is the identity, matching the normalization of the existing filtering laws.
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

/-- Asymptotic variance of a normalized bootstrap particle average. -/
def FeynmanKacModel.particleAverageAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) : ℝ :=
  let centered := fun x ↦ f x - ∫ y, f y ∂M.filterLaw n
  ∑ p ∈ Finset.range (n + 1),
    (∫ x, (M.backwardOperator p (n - p) centered x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2

/-- Asymptotic variance of the normalized likelihood estimate. -/
def FeynmanKacModel.particleLikelihoodAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1),
    (∫ x, (M.backwardOperator p (n - p) (fun _ ↦ 1) x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2 - 1

/-- GAPS 104.59: bootstrap-particle central limit theorem at a fixed time. -/
theorem tendstoInDistribution_particle_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (n : ℕ) :
    TendstoInDistribution P
      (fun N ω ↦ Real.sqrt (N + 1) *
        ((∑ i, f (ξ N n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n))
      (gaussianReal 0 (Real.toNNReal (M.particleAverageAsymptoticVariance n f))) := by
  sorry

/-- GAPS 104.59: bootstrap-particle likelihood central limit theorem at a fixed time. -/
theorem tendstoInDistribution_particle_likelihood {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N)) (n : ℕ) :
    TendstoInDistribution P
      (fun N ω ↦ Real.sqrt (N + 1) *
        (M.particleLikelihood (fun p ↦ ξ N p ω) n / (M.unnormalizedLaw n).real univ - 1))
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
