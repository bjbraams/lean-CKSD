module

public import CKSD.Inference.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Inference: ExponentialFamily

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.1: factorization on standard Borel sample and statistic spaces. -/
theorem isSufficientStatistic_iff_exists_factorization
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace S]
    [Nonempty S] [Nonempty Θ] (P : Θ → Measure X) (μ : Measure X) [SigmaFinite μ]
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S) (hT : Measurable T) :
    IsSufficientStatistic P T ↔ ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  sorry

/-- GAPS 101.4, convexity part: the multivariate Laplace-integrability domain is convex. -/
theorem convex_laplace_integrability_domain {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Convex ℝ {η : EuclideanSpace ℝ (Fin d) |
      Integrable (fun t ↦ Real.exp (inner ℝ η t)) ν} := by
  intro η hη ζ hζ a b ha hb hab
  apply ((hη.const_mul a).add (hζ.const_mul b)).mono'
  · exact (by fun_prop : Continuous (fun t ↦ Real.exp (inner ℝ (a • η + b • ζ) t))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [inner_add_left, real_inner_smul_left, smul_eq_mul, Pi.add_apply] using
      convexOn_exp.2 (mem_univ (inner ℝ η t)) (mem_univ (inner ℝ ζ t)) ha hb hab

/-- GAPS 101.5: completeness of a natural statistic over a nonempty open parameter set. -/
theorem isCompleteStatistic_exponential_family {d : ℕ} (ν : Measure X) [SigmaFinite ν]
    (T : X → EuclideanSpace ℝ (Fin d)) (hT : Measurable T)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hne : U.Nonempty)
    (Z : EuclideanSpace ℝ (Fin d) → ℝ)
    (hZ : ∀ η ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ η (T x))) ν ∧
      Z η = ∫ x, Real.exp (inner ℝ η (T x)) ∂ν ∧ 0 < Z η) :
    IsCompleteStatistic (fun η : U ↦ ν.withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η.val (T x)) / Z η.val))) T := by
  sorry

/-- GAPS 101.2, minimal likelihood-ratio statistic for a countable parameter family. -/
theorem likelihood_ratio_statistic_minimal_sufficient
    [StandardBorelSpace X] [Nonempty X] [Countable Θ]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (mu : Measure X) [SigmaFinite mu] (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) mu (f θ)) (hpos : ∀ θ x, 0 < f θ x) (θ₀ : Θ) :
    let R := fun x θ ↦ f θ x / f θ₀ x;
    IsSufficientStatistic P R ∧ ∀ T : X → S, IsSufficientStatistic P T →
      ∃ phi : S → (Θ → ℝ), Measurable phi ∧ ∀ θ, R =ᵐ[P θ] phi ∘ T := by
  sorry

/-- GAPS 101.6: the monotone Pitman–Koopman–Darmois characterization. -/
theorem exists_exponential_family_of_monotone_sufficient_statistics
    (P : Θ → Measure X) (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (heq : ∀ θ, P θ ≪ P₀ ∧ P₀ ≪ P θ)
    (N : Set ℕ) (hN : N.Infinite) (h1 : 1 ∈ N)
    (hmon : ∀ n ∈ N, ∃ T : (Fin n → X) → ℝ, Measurable T ∧
      ∀ θ, ∃ H : ℝ → ℝ, Monotone H ∧
        HasDensity (Measure.pi fun _ : Fin n ↦ P θ)
          (Measure.pi fun _ : Fin n ↦ P₀) (H ∘ T)) :
    ∃ T : X → ℝ, Measurable T ∧ ∀ θ, ∃ C > 0, ∃ a : ℝ,
      HasDensity (P θ) P₀ (fun x ↦ C * Real.exp (a * T x)) := by
  sorry

/-- GAPS 101.4, multivariate analyticity and first/second cumulant derivatives. -/
theorem analyticOnNhd_cumulant_and_fderiv_eq_moments
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d)))
    [SigmaFinite nu] (hne : nu ≠ 0) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    let P := fun eta ↦ nu.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ eta x - A eta)));
    AnalyticOnNhd ℝ A (interior N) ∧ ∀ eta ∈ interior N,
      HasFDerivAt A (innerSL ℝ (∫ x, x ∂P eta)) eta ∧
      ∀ u v : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (fderiv ℝ A) eta u v =
          covariance (P eta) (fun x ↦ inner ℝ u x) (fun x ↦ inner ℝ v x) := by
  sorry


end CKSD
