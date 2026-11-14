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

/-- GAPS 106.39: the iid finite-variance CUSUM statistic converges to the Brownian-bridge
supremum: for iid observations with positive (hence finite) variance `σ²`,
`max_{k ≤ n} |S_k - (k / n) S_n| / (σ √n) ⇒ sup_{t ∈ [0, 1]} |B_t - t B_1|`. -/
theorem tendsto_in_distribution_cusum_bridge_statistic {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hv : 0 < Var[id; P])
    (ν : Measure Ω') [IsProbabilityMeasure ν] (B : ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianReal B ν) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ cusumBridgeStatistic X (Real.sqrt (Var[id; P])) n ω)
      atTop id (fun _ ↦ μ)
      (ν.map (brownianBridgeSupremum B)) := by
  sorry

/-- At sample size zero, the standardized CUSUM statistic uses division-by-zero value zero. -/
@[simp] theorem cusum_bridge_statistic_zero {Ω : Type*} (X : ℕ → Ω → ℝ) (σ : ℝ) (ω : Ω) :
    cusumBridgeStatistic X σ 0 ω = 0 := by simp [cusumBridgeStatistic]

end CKSD
