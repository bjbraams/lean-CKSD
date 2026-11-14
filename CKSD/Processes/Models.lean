module

public import CKSD.Processes.Basic
public import Mathlib.Probability.BrownianMotion.Basic


/-!
# Brownian bridge, hitting times and change-detection statistics

Pathwise definitions shared by the sequential and change-point results of Section 106.

## Main definitions

* `CKSD.brownianBridge`: the bridge `B(t) - t B(1)` of a process indexed by `ℝ≥0`; with
  Mathlib's Brownian motion this is the Brownian bridge on `[0, 1]`.
* `CKSD.thresholdHittingTime`: the first time `n` with `a ≤ V n`, as an element of `ℕ∞`; a path
  that never reaches the level has hitting time `⊤`.
* `CKSD.cusumStatistic`: Page's CUSUM likelihood-ratio statistic
  `W_{n+1} = max(1, W_n) L_n`, `W_0 = 0`.
* `CKSD.shiryaevRobertsStatistic`: the Shiryaev–Roberts statistic `R_{n+1} = (1 + R_n) L_n`,
  `R_0 = 0`.

## Main results

* `CKSD.cusum_statistic_le_shiryaev_roberts_statistic`: for nonnegative likelihood ratios the CUSUM
  statistic is dominated pathwise by the Shiryaev–Roberts statistic. Since `R_n - n` is a
  martingale under the pre-change law, this gives Lorden's bound `𝔼_∞ T_CS(A) ≥ A` (GAPS 106.44).
* `CKSD.brownian_bridge_one`: the bridge is pinned at `1`.

## Conventions

The likelihood-ratio observations `L n` are indexed from zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- The bridge `t ↦ B(t) - t B(1)` of a process `B` indexed by `ℝ≥0`, pinned at times zero and
one; for a Brownian motion `B` it is the Brownian bridge on `[0, 1]`. -/
def brownianBridge {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  B (Real.toNNReal t) ω - t * B 1 ω

/-- The first time `n` with `a ≤ V n ω`, with value `⊤` if the level is never reached. -/
def thresholdHittingTime {Ω : Type*} (V : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ n : {n : ℕ // a ≤ V n ω}, (n.val : ℕ∞)

/-- Page's CUSUM likelihood-ratio statistic `W_0 = 0`, `W_{n+1} = max(1, W_n) · L_n`, for
likelihood ratios `L 0, L 1, …`; the CUSUM procedure stops when `W_n ≥ A`. -/
def cusumStatistic {Ω : Type*} (L : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => max 1 (cusumStatistic L n ω) * L n ω

/-- The Shiryaev–Roberts statistic `R_0 = 0`, `R_{n+1} = (1 + R_n) · L_n`, for likelihood ratios
`L 0, L 1, …`. -/
def shiryaevRobertsStatistic {Ω : Type*} (L : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => (1 + shiryaevRobertsStatistic L n ω) * L n ω

/-- The Shiryaev–Roberts statistic of nonnegative likelihood ratios is nonnegative. -/
theorem shiryaev_roberts_statistic_nonneg {Ω : Type*} (L : ℕ → Ω → ℝ)
    (hL : ∀ n ω, 0 ≤ L n ω) (n : ℕ) (ω : Ω) : 0 ≤ shiryaevRobertsStatistic L n ω := by
  induction n with
  | zero => simp [shiryaevRobertsStatistic]
  | succ n ih => exact mul_nonneg (by linarith) (hL n ω)

/-- GAPS 106.44, pathwise comparison: for nonnegative likelihood ratios the CUSUM statistic is
at most the Shiryaev–Roberts statistic, `W_n ≤ R_n`. Hence the CUSUM stopping time is at least
the Shiryaev–Roberts stopping time for the same threshold, which underlies the false-alarm bound
`𝔼_∞ T_CS(A) ≥ A`. -/
theorem cusum_statistic_le_shiryaev_roberts_statistic {Ω : Type*} (L : ℕ → Ω → ℝ)
    (hL : ∀ n ω, 0 ≤ L n ω) (n : ℕ) (ω : Ω) :
    cusumStatistic L n ω ≤ shiryaevRobertsStatistic L n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply mul_le_mul_of_nonneg_right _ (hL n ω)
    exact max_le (by linarith [shiryaev_roberts_statistic_nonneg L hL n ω]) (by linarith)

/-- The bridge is pinned at its right endpoint. -/
@[simp] theorem brownian_bridge_one {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    brownianBridge B 1 ω = 0 := by simp [brownianBridge]

end CKSD
