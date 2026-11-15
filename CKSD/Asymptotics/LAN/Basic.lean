module

public import CKSD.Asymptotics.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Local experiments and local asymptotic normality

The interface definitions for limits of experiments: local experiments indexed by a local
parameter, local asymptotic normality, and regular estimator sequences.

## Main definitions

* `CKSD.LocalExperiment`: a sequence of experiments indexed by a local parameter in `ℝᵈ`.
* `CKSD.IsLocallyAsymptoticallyNormal`: a Gaussian central sequence and the quadratic
  log-likelihood expansion.
* `CKSD.IsRegularEstimator`: a locally scaled estimator whose centred limit law does not depend
  on the local parameter.

## Conventions

The local parameter `h` of an experiment denotes the displacement `h / √n` from its centre; an
estimator is already scaled by `√n`. Observation spaces may depend on `n`.

## References

van der Vaart, *Asymptotic Statistics*, Chapters 7 and 8.
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace CKSD

/-- A local experiment with observation space depending on sample size. -/
abbrev LocalExperiment (d : ℕ) (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] :=
  ∀ n, EuclideanSpace ℝ (Fin d) → ProbabilityMeasure (Ω n)

/-- Local asymptotic normality: Gaussian central sequence and log-likelihood expansion. -/
@[expose] def IsLocallyAsymptoticallyNormal {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) : Prop :=
  I.PosDef ∧ (∀ n, Measurable (Δ n)) ∧
    TendstoInDistribution Δ atTop id (fun n ↦ (P n 0 : Measure (Ω n)))
      (multivariateGaussian 0 I) ∧
    ∀ h, TendstoInProbabilityZero (fun n ↦ (P n 0 : Measure (Ω n)))
      (fun n ω ↦ Real.log (((P n h : Measure (Ω n)).rnDeriv (P n 0) ω).toReal) -
        inner ℝ h (Δ n ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2)

/-- Regularity of a locally scaled estimator: its centred limit law `L` is independent of the
local parameter. -/
@[expose] def IsRegularEstimator {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] : Prop :=
  (∀ n, Measurable (T n)) ∧ ∀ h,
    TendstoInDistribution (fun n ω ↦ T n ω - h) atTop id (fun n ↦ (P n h : Measure (Ω n))) L

end CKSD
