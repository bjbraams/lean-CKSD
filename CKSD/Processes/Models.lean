module

public import CKSD.Processes.Basic
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Time-series and sequential models

First-exit times take values in `ℕ∞`, so a procedure that never stops has infinite stopping time.
The Brownian bridge uses Mathlib's Brownian process; counting-process compensators use ordinary
Lebesgue integrals and martingales, without postulating a stochastic integral.
Sources: GAPS 106.24, 106.30, 106.34, 106.37–106.44.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Brownian bridge pinned at times zero and one, on the time interval `[0,1]`. -/
def brownianBridge {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  B (Real.toNNReal t) ω - t * B 1 ω

/-- A two-sided Brownian process assembled from independent positive and negative halves. -/
def twoSidedBrownian {Ω : Type*} (Bplus Bminus : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if 0 ≤ t then Bplus (Real.toNNReal t) ω else Bminus (Real.toNNReal (-t)) ω

/-- Likelihood-ratio process with the empty product equal to one. -/
def likelihoodRatioProcess {Ω X : Type*} (Xn : ℕ → Ω → X) (f₀ f₁ : X → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := ∏ i ∈ Finset.range n, f₁ (Xn i ω) / f₀ (Xn i ω)

/-- First crossing of a threshold, including the value infinity if no crossing occurs. -/
def thresholdHittingTime {Ω : Type*} (V : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ n : {n : ℕ // a ≤ V n ω}, (n.val : ℕ∞)

/-- Sequential probability-ratio test's first exit from the open continuation interval. -/
def sprtStoppingTime {Ω : Type*} (L : ℕ → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ n : {n : ℕ // L n ω ≤ a ∨ b ≤ L n ω}, (n.val : ℕ∞)

/-- The rejection event of a sequential probability-ratio test. -/
def sprtRejectionEvent {Ω : Type*} (L : ℕ → Ω → ℝ) (a b : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, sprtStoppingTime L a b ω = n ∧ b ≤ L n ω}

/-- Page's CUSUM likelihood statistic, with observations indexed from zero. -/
def cusumStatistic {Ω : Type*} (L : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => max 1 (cusumStatistic L n ω) * L n ω

/-- The Shiryaev–Roberts statistic, used to bound the CUSUM false-alarm waiting time. -/
def shiryaevRobertsStatistic {Ω : Type*} (L : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => (1 + shiryaevRobertsStatistic L n ω) * L n ω

/-- CUSUM stopping time, excluding the initial time. -/
def cusumStoppingTime {Ω : Type*} (L : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ n : {n : ℕ // 0 < n ∧ a ≤ cusumStatistic L n ω}, (n.val : ℕ∞)

/-- Integrated hazard (compensator) of a counting process with an at-risk process. -/
def integratedIntensity {Ω : Type*} (Y intensity : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, Y s ω * intensity s ω

/-- A counting process with the specified multiplicative intensity has a martingale residual. -/
def HasMultiplicativeIntensity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (N Y intensity : ℝ → Ω → ℝ) : Prop :=
  (∀ ω, Monotone (fun t ↦ N t ω)) ∧
    (∀ t ω, 0 ≤ N t ω) ∧ (∀ t ω, 0 ≤ Y t ω) ∧ (∀ t ω, 0 ≤ intensity t ω) ∧
    Martingale (fun t ω ↦ N t ω - integratedIntensity Y intensity t ω) F P

/-- Cox's partial log-likelihood for a finite sample without simultaneous failures. -/
def coxPartialLogLikelihood {n d : ℕ} (time : Fin n → ℝ) (event : Fin n → Bool)
    (z : Fin n → EuclideanSpace ℝ (Fin d)) (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, if event i then inner ℝ β (z i) -
    Real.log (∑ j, if time i ≤ time j then Real.exp (inner ℝ β (z j)) else 0) else 0

/-- Nonnegativity of the Shiryaev–Roberts statistic for nonnegative likelihood ratios. -/
theorem shiryaevRobertsStatistic_nonneg {Ω : Type*} (L : ℕ → Ω → ℝ)
    (hL : ∀ n ω, 0 ≤ L n ω) (n : ℕ) (ω : Ω) : 0 ≤ shiryaevRobertsStatistic L n ω := by
  induction n with
  | zero => simp [shiryaevRobertsStatistic]
  | succ n ih => exact mul_nonneg (by linarith) (hL n ω)

/-- GAPS 106.44, the pathwise comparison underlying the false-alarm waiting-time bound. -/
theorem cusumStatistic_le_shiryaevRobertsStatistic {Ω : Type*} (L : ℕ → Ω → ℝ)
    (hL : ∀ n ω, 0 ≤ L n ω) (n : ℕ) (ω : Ω) :
    cusumStatistic L n ω ≤ shiryaevRobertsStatistic L n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply mul_le_mul_of_nonneg_right _ (hL n ω)
    exact max_le (by linarith [shiryaevRobertsStatistic_nonneg L hL n ω]) (by linarith)

/-- A likelihood-ratio process starts at one. -/
@[simp] theorem likelihoodRatioProcess_zero {Ω X : Type*} (Xn : ℕ → Ω → X)
    (f₀ f₁ : X → ℝ) (ω : Ω) : likelihoodRatioProcess Xn f₀ f₁ 0 ω = 1 := by
  simp [likelihoodRatioProcess]

/-- The bridge is pinned at its right endpoint. -/
@[simp] theorem brownianBridge_one {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    brownianBridge B 1 ω = 0 := by simp [brownianBridge]

end CKSD
