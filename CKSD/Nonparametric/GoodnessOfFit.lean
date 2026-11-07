module

public import CKSD.Nonparametric.Models
public import TauCeti.Probability.Distributions.OrderStatistic.Joint

/-!
# Distribution-free goodness-of-fit statistics and residual eigenvector bounds

Sources: GAPS 103.17 and 103.54; the scopes are the finite-sample distribution-freeness and
deterministic residual-bound parts described in `GAPS_EASY.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical distribution function of a finite sample. -/
def finiteEmpiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun i ↦ x i ≤ t).card : ℝ) / n

/-- Cramér–von Mises statistic, with the factor `n` normalization. -/
def cramerVonMisesStatistic {n : ℕ} (P : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∫ t, (finiteEmpiricalCDF x t - cdf P t) ^ 2 ∂P

/-- Two-sample Kolmogorov–Smirnov statistic, without the asymptotic scaling factor. -/
def twoSampleKolmogorovSmirnovStatistic {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sSup (range fun t : ℚ ↦ |finiteEmpiricalCDF x t - finiteEmpiricalCDF y t|)

/-- GAPS 103.17: finite-sample distribution-freeness of the Cramér–von Mises statistic. -/
theorem map_cramerVonMisesStatistic_eq_uniform (P : Measure ℝ) [IsProbabilityMeasure P]
    [NullSingletonClass P] (n : ℕ) (hn : 0 < n) :
    let U := ProbabilityTheory.uniformOn (Icc (0 : ℝ) 1);
    (Measure.pi fun _ : Fin n ↦ P).map (cramerVonMisesStatistic P) =
      (Measure.pi fun _ : Fin n ↦ U).map (cramerVonMisesStatistic U) := by
  sorry

/-- GAPS 103.17: finite-sample distribution-freeness of the two-sample KS statistic. -/
theorem map_twoSampleKolmogorovSmirnovStatistic_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let U := ProbabilityTheory.uniformOn (Icc (0 : ℝ) 1);
    ((Measure.pi fun _ : Fin m ↦ P).prod (Measure.pi fun _ : Fin n ↦ P)).map
      (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) =
      ((Measure.pi fun _ : Fin m ↦ U).prod (Measure.pi fun _ : Fin n ↦ U)).map
        (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) := by
  sorry

/-- GAPS 103.54: residual perturbation bound, with the gap specified by a Rayleigh bound.
The probabilistic spiked-covariance bound is outside this deterministic statement. -/
theorem leading_eigenvector_residual_bound {p : ℕ}
    (A E : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : IsSelfAdjoint A) (hE : IsSelfAdjoint E)
    (v : EuclideanSpace ℝ (Fin p)) (hv : ‖v‖ = 1) (a gap : ℝ) (hgap : 0 < gap)
    (heig : A v = a • v)
    (hother : ∀ u, inner ℝ u v = 0 → inner ℝ u (A u) ≤ (a - gap) * ‖u‖ ^ 2)
    (hsmall : 2 * ‖E‖ < gap) :
    ∃ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v ∧
      (∃ b : ℝ, (A + E) w = b • w ∧
        (∀ u, inner ℝ u ((A + E) u) ≤ b * ‖u‖ ^ 2) ∧
        ∀ z, (A + E) z = b • z → z ∈ Submodule.span ℝ {w}) ∧
      ‖w - v‖ ≤ 2 * ‖E v - inner ℝ v (E v) • v‖ / (gap - 2 * ‖E‖) := by
  sorry

end CKSD
