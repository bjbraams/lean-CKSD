module

public import CKSD.Processes.Models

/-!
# The CUSUM bridge limit

The Brownian bridge is formed from Mathlib's continuous Brownian motion. The finite statistic
includes both endpoint partial sums, which are zero after bridge centering.
Source: GAPS 106.39.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Supremum of the absolute Brownian bridge on the unit interval. -/
def brownianBridgeSupremum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  sSup {r : ℝ | ∃ t ∈ Icc (0 : ℝ) 1, r = |brownianBridge B t ω|}

/-- Standardized maximum of a finite partial-sum bridge. -/
def cusumBridgeStatistic {Ω : Type*} (X : ℕ → Ω → ℝ) (σ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sSup (range fun k : Fin (n + 1) ↦
    |(∑ i ∈ Finset.range k.val, X i ω) - (k.val : ℝ) / n *
      (∑ i ∈ Finset.range n, X i ω)|) / (σ * Real.sqrt n)

/-- GAPS 106.39: the iid finite-variance CUSUM statistic converges to the Brownian-bridge supremum. -/
theorem tendstoInDistribution_cusumBridgeStatistic {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (h2 : MemLp id 2 P) (hv : 0 < variance P id)
    (ν : Measure Ω') [IsProbabilityMeasure ν] (B : ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianReal B ν) :
    TendstoInDistribution μ (fun n ω ↦ cusumBridgeStatistic X (Real.sqrt (variance P id)) n ω)
      (ν.map (brownianBridgeSupremum B)) := by
  sorry

/-- At sample size zero, the standardized CUSUM statistic uses division-by-zero value zero. -/
@[simp] theorem cusumBridgeStatistic_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (σ : ℝ) (ω : Ω) :
    cusumBridgeStatistic X σ 0 ω = 0 := by simp [cusumBridgeStatistic]

end CKSD
