module

public import CKSD.Bayes.Nonparametric
public import CKSD.Asymptotics.Basic
public import Statlib.Divergence.Hellinger.Basic

/-!
# Dominated posteriors and posterior contraction

For a dominated model with densities `f θ`, the posterior after `n` observations is the prior
reweighted by the product likelihood and normalized. Its value at samples with zero evidence
follows the zero-measure normalization convention; the consistency theorems only control it
under the true sampling law. Hellinger distance reuses Statlib's `sqHellinger`, with a factor
two to obtain the convention `h² = ∫ (√p - √q)²` of `GAPS.md`.

## Main definitions

* `CKSD.dominatedPosterior`: the posterior of a dominated model.
* `CKSD.statisticalHellingerDistance`: Hellinger distance in the convention `h² = ∫ (√p - √q)²`.
* `CKSD.HasUniformlyConsistentTests`, `CKSD.HasHellingerSieveCover`: uniformly consistent tests
  and finite Hellinger covers of sieves with an entropy bound.

## Main results

* `CKSD.tendstoInProbabilityConst_posterior_compl_of_kl_support`: Schwartz's posterior
  consistency theorem (GAPS 104.18).
* `CKSD.exists_posterior_hellinger_contraction`: the Ghosal–Ghosh–van der Vaart contraction
  theorem in Hellinger distance (GAPS 104.19).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Posterior measure obtained by multiplying a prior by the finite-sample likelihood. -/
def dominatedPosterior {Θ X : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) (f : Θ → X → ℝ) {n : ℕ} (x : Fin n → X) : Measure Θ :=
  let unnormalized := π.withDensity (fun θ ↦ ENNReal.ofReal (∏ i, f θ (x i)))
  (unnormalized univ)⁻¹ • unnormalized

/-- Real Hellinger adapter in the convention `h² = integral (sqrt p - sqrt q)²`
for probability measures. For arbitrary measures an infinite squared divergence is totalized to
zero by `ENNReal.toReal`; distance interpretations require finite divergence. -/
def statisticalHellingerDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ := Real.sqrt (2 * (ProbabilityTheory.sqHellinger P Q).toReal)

/-- Existence of uniformly consistent tests against a fixed parameter set. -/
def HasUniformlyConsistentTests {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (θ₀ : Θ) (A : Set Θ) : Prop :=
  ∃ φ : ∀ n : ℕ, (Fin n → X) → ℝ,
    (∀ n : ℕ, IsStatisticalTest (φ n)) ∧
    Tendsto (fun n : ℕ ↦ ∫ x, φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ ∈ A,
      (∫ x, 1 - φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ ε

/-- GAPS 104.18: Schwartz's posterior consistency theorem. If the prior charges every
Kullback–Leibler neighbourhood `{θ | KL(P θ₀ ‖ P θ) < ε}` of the true parameter and there are
uniformly consistent tests of `θ₀` against `Uᶜ`, then the posterior mass of `Uᶜ` tends to zero in
probability under the true law. -/
theorem tendstoInProbabilityConst_posterior_compl_of_kl_support
    {Θ X : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ)
    (hKLmeas : ∀ ε > 0, MeasurableSet {θ | klDiv (P θ₀) (P θ) < ENNReal.ofReal ε})
    (hKL : ∀ ε > 0, 0 < π {θ | klDiv (P θ₀) (P θ) < ENNReal.ofReal ε})
    (U : Set Θ) (hU : MeasurableSet U)
    (htests : HasUniformlyConsistentTests P θ₀ Uᶜ) :
    TendstoInProbabilityConst (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun n x ↦ (dominatedPosterior π f (fun i : Fin n ↦ x i.val)).real Uᶜ) 0 := by
  sorry

/-- Finite internal Hellinger cover of a sieve, with an explicit entropy cardinality bound. -/
def HasHellingerSieveCover {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (sieve : Set Θ) (ε entropy : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ Real.exp entropy ∧ ∃ center : Fin m → Θ,
    (∀ i, center i ∈ sieve) ∧ ∀ θ ∈ sieve,
      ∃ i, statisticalHellingerDistance (P θ) (P (center i)) ≤ ε

/-- GAPS 104.19: the Ghosal–Ghosh–van der Vaart theorem. Suppose `εₙ → 0` with `n εₙ² → ∞`, the
sieves `Θₙ` have `εₙ/2`-Hellinger covers of cardinality at most `e^{n εₙ²}`, the prior mass outside
`Θₙ` is at most `e^{-(C+4) n εₙ²}`, and the prior mass of the Kullback–Leibler neighbourhood
`{KL ≤ εₙ², V₂ ≤ εₙ²}` is at least `e^{-C n εₙ²}`. Then the posterior contracts at rate `εₙ` in
Hellinger distance. The finite-cover condition spells out the entropy bound without imposing a
metric on parameter labels. -/
theorem exists_posterior_hellinger_contraction
    {Θ X : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ)
    (ε : ℕ → ℝ) (hε : ∀ n : ℕ, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hnε : Tendsto (fun n : ℕ ↦ (n : ℝ) * ε n ^ 2) atTop atTop)
    (C : ℝ) (hC : 0 < C) (sieve : ℕ → Set Θ) (hsieve : ∀ n : ℕ, MeasurableSet (sieve n))
    (hcover : ∀ n : ℕ, HasHellingerSieveCover P (sieve n) (ε n / 2) ((n : ℝ) * ε n ^ 2))
    (htail : ∀ n : ℕ, π (sieve n)ᶜ ≤ ENNReal.ofReal (Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2)))
    (hBmeas : ∀ n : ℕ, MeasurableSet {θ | klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2) ∧
      logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2)})
    (hprior : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-C * (n : ℝ) * ε n ^ 2)) ≤
      π {θ | klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2) ∧
        logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2)})
    (hHmeas : Measurable (fun θ ↦ statisticalHellingerDistance (P θ) (P θ₀))) :
    HasPosteriorContractionRate (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun n x ↦ dominatedPosterior π f (fun i : Fin n ↦ x i.val))
      (fun θ ↦ statisticalHellingerDistance (P θ) (P θ₀)) ε := by
  sorry

/-- Statistical Hellinger distance is nonnegative by its definition. -/
theorem statisticalHellingerDistance_nonneg {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : 0 ≤ statisticalHellingerDistance P Q := Real.sqrt_nonneg _

/-- The Hellinger adapter vanishes when its two laws agree, by Statlib. -/
@[simp] theorem statisticalHellingerDistance_self {X : Type*} [MeasurableSpace X]
    (P : Measure X) [SigmaFinite P] : statisticalHellingerDistance P P = 0 := by
  simp [statisticalHellingerDistance]

/-- Symmetry of the Hellinger adapter follows from Statlib's symmetry theorem. -/
theorem statisticalHellingerDistance_comm {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    statisticalHellingerDistance P Q = statisticalHellingerDistance Q P := by
  simp only [statisticalHellingerDistance, ProbabilityTheory.sqHellinger_comm P Q]

/-- Before any observations, a probability prior is its own dominated posterior. -/
@[simp] theorem dominatedPosterior_empty {Θ X : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (f : Θ → X → ℝ) (x : Fin 0 → X) :
    dominatedPosterior π f x = π := by
  simp [dominatedPosterior]

end CKSD
