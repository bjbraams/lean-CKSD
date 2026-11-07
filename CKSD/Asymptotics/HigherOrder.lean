module

public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Asymptotics: HigherOrder

Sources: `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 102.44, Hampel optimality part of the Huber statement. -/
theorem integral_huberScore_sq_le (k : ℝ) (hk : 0 < k) :
    let G := gaussianReal 0 1;
    let a := 2 * cdf G k - 1;
    ∀ (φ : ℝ → ℝ),
    ∀ (hm : Measurable φ),
    ∀ (hbound : ∀ x, |φ x| ≤ k / a),
    ∀ (h0 : (∫ x, φ x ∂G) = 0),
    ∀ (h1 : (∫ x, x * φ x ∂G) = 1),
    (∫ x, (huberScore k x / a) ^ 2 ∂G) ≤ ∫ x, φ x ^ 2 ∂G := by
  sorry

/-- GAPS 102.49: uniform one-term Edgeworth expansion under the stated nonlattice condition. -/
theorem uniform_edgeworth_expansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h3 : Integrable
      (fun x ↦ |x| ^ 3) P)
    (h0 : (∫ x, x ∂P) = 0) (h1 : (∫ x, x ^ 2 ∂P) = 1)
    (hnonlattice : ∀ a : ℝ, ∀ b > 0, P (range fun j : ℤ ↦ a + b * j) < 1) :
    let ρ := ∫ x, x ^ 3 ∂P;
    ∃ e : ℕ → ℝ, Tendsto (fun n : ℕ ↦ Real.sqrt n * e n) atTop (𝓝 0) ∧
      ∀ (n : ℕ), n ≥ 1 → ∀ t, |μ.real {ω | Real.sqrt n * sampleAverage X n ω ≤ t} -
        (cdf (gaussianReal 0 1) t - gaussianPDFReal 0 1 t * (t ^ 2 - 1) *
          ρ / (6 * Real.sqrt n))| ≤ e n := by
  sorry

/-- GAPS 102.51: conditional bootstrap consistency of the mean, for positive variance. -/
theorem tendstoInProbabilityConst_bootstrap_mean_kolmogorovDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) :
    TendstoInProbabilityConst μ (fun n ω ↦ kolmogorovDistance
      ((Measure.pi fun _ : Fin n ↦ empiricalMeasure n (fun i ↦ X i.val ω)).map
        (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - sampleAverage X n ω)))
      (gaussianReal 0 (Real.toNNReal (variance P id)))) 0 := by
  sorry


end CKSD
