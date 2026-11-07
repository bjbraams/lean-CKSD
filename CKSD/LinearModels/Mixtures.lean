module

public import CKSD.LinearModels.Basic
public import TauCeti.Probability.Distributions.Gaussian.Mixture.Multivariate

/-!
# Identifiable finite Gaussian mixtures

The laws and densities are TauCeti's general finite multivariate Gaussian-mixture constructions.
This module restricts their parameters to distinct, nondegenerate, positive-weight components,
then states identifiability across different component counts and likelihood unboundedness.
Sources: GAPS 105.6 and SYNOPSIS105, item 6.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Convexity
open scoped NNReal ENNReal BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Parameters of a reduced finite Gaussian mixture: all components are nondegenerate, distinct,
and have positive weight. Laws and densities use the upstream TauCeti construction. -/
structure GaussianMixtureModel (d k : ℕ) where
  /-- Component weights on the finite simplex. -/
  weights : StdSimplex ℝ≥0 (Fin k)
  /-- Component means. -/
  mean : Fin k → EuclideanSpace ℝ (Fin d)
  /-- Component covariance matrices. -/
  covariance : Fin k → Matrix (Fin d) (Fin d) ℝ
  /-- Every covariance is positive definite. -/
  covariance_posDef : ∀ i, (covariance i).PosDef
  /-- No component has zero weight. -/
  weight_pos : ∀ i, 0 < weights.weights i
  /-- Equal component parameters have equal component indices. -/
  distinct : Function.Injective (fun i ↦ (mean i, covariance i))

/-- Probability law of a reduced Gaussian mixture, using TauCeti's finite mixture. -/
def GaussianMixtureModel.law {d k : ℕ} (M : GaussianMixtureModel d k) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  TauCeti.Probability.multivariateGaussianMixtureMeasure M.weights M.mean M.covariance

/-- Real Gaussian-mixture density, using TauCeti's canonical continuous density. -/
def GaussianMixtureModel.density {d k : ℕ} (M : GaussianMixtureModel d k) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  TauCeti.Probability.multivariateGaussianMixturePDFReal M.weights M.mean M.covariance

/-- Log likelihood of a reduced Gaussian mixture at a finite observed sample. -/
def GaussianMixtureModel.logLikelihood {d k n : ℕ} (M : GaussianMixtureModel d k)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, Real.log (M.density (x i))

/-- The mixture law is a probability measure by TauCeti's mixture instance. -/
instance GaussianMixtureModel.isProbabilityMeasure_law {d k : ℕ}
    (M : GaussianMixtureModel d k) : IsProbabilityMeasure M.law :=
  inferInstanceAs (IsProbabilityMeasure
    (TauCeti.Probability.multivariateGaussianMixtureMeasure M.weights M.mean M.covariance))

/-- The canonical mixture density is nonnegative, by TauCeti. -/
theorem GaussianMixtureModel.density_nonneg {d k : ℕ} (M : GaussianMixtureModel d k)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ M.density x :=
  TauCeti.Probability.multivariateGaussianMixturePDFReal_nonneg _ _ _ _

/-- The mixture's real density agrees with its law in CKSD's density interface, using TauCeti. -/
theorem GaussianMixtureModel.hasDensity {d k : ℕ} (M : GaussianMixtureModel d k) :
    HasDensity M.law volume M.density := by
  refine ⟨TauCeti.Probability.measurable_multivariateGaussianMixturePDFReal _ _ _,
    Filter.Eventually.of_forall M.density_nonneg, ?_⟩
  exact (TauCeti.Probability.multivariateGaussianMixtureMeasure_eq_withDensity
    (fun i _ ↦ M.covariance_posDef i)).trans (by
      congr 1
      funext x
      exact TauCeti.Probability.multivariateGaussianMixturePDF_eq_ofReal _ _ _ _)

/-- GAPS 105.6: finite nondegenerate Gaussian mixtures are identifiable up to relabeling,
including equality of the number of distinct positive-weight components. -/
theorem gaussianMixtureModel_identifiable {d k l : ℕ} (hd : 0 < d)
    (M : GaussianMixtureModel d k) (N : GaussianMixtureModel d l) (h : M.law = N.law) :
    ∃ e : Fin k ≃ Fin l, ∀ i,
      M.weights.weights i = N.weights.weights (e i) ∧
        M.mean i = N.mean (e i) ∧ M.covariance i = N.covariance (e i) := by
  sorry

/-- GAPS 105.6: two Gaussian components already give an unbounded likelihood when their
covariances are unconstrained. The sample and ambient dimension are both nonempty. -/
theorem gaussianMixtureModel_logLikelihood_unbounded {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∀ R : ℝ, ∃ M : GaussianMixtureModel d 2, R < M.logLikelihood x := by
  sorry

end CKSD
