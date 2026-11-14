module

public import CKSD.Asymptotics.Expansions
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Bootstrap of the empirical distribution function and of the studentized mean

The conditional expectation given the sample of a function of a nonparametric resample is the
exact average over the `n^n` index maps `Fin n → Fin n`; this avoids measurability questions
for functions on the nonseparable space of bounded functions. The bounded Lipschitz metric is
taken over functions on `ℝ → ℝ` that are bounded by one and `1`-Lipschitz for the extended
supremum distance. The `F`-Brownian bridge is `t ↦ W(F t) - F t · W 1` for a Brownian motion
`W` in the sense of Mathlib's `IsBrownianReal`.

The second-order accuracy of the studentized bootstrap is stated for the studentized mean in
dimension one, with the convention of `studentizedStatistic` that the statistic is zero when
the estimated standard deviation vanishes. Sources: GAPS 102.52 and 102.60.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Empirical distribution function of a finite sample. -/
def sampleEmpiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Finset.univ.filter fun i ↦ x i ≤ t).card / n

/-- Mean of a finite sample. -/
def finiteSampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Standard deviation of a finite sample with divisor `n`. -/
def finiteSampleSD {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (x i - finiteSampleMean x) ^ 2) / n)

/-- Extended supremum distance between real functions on the line. -/
def supEDist (u v : ℝ → ℝ) : ℝ≥0∞ := ⨆ t, ENNReal.ofReal |u t - v t|

/-- Test functions of the bounded Lipschitz metric: bounded by one and `1`-Lipschitz for the
supremum distance. -/
def IsBoundedLipschitzOne (h : (ℝ → ℝ) → ℝ) : Prop :=
  (∀ u, |h u| ≤ 1) ∧ ∀ u v, ENNReal.ofReal |h u - h v| ≤ supEDist u v

/-- The bootstrap empirical process `√n (F*ₙ - Fₙ)` of the resample `x ∘ σ`. -/
def bootstrapEmpiricalProcess {n : ℕ} (x : Fin n → ℝ) (σ : Fin n → Fin n) (t : ℝ) : ℝ :=
  Real.sqrt n * (sampleEmpiricalCDF (x ∘ σ) t - sampleEmpiricalCDF x t)

/-- Bounded Lipschitz distance between the conditional law of the bootstrap empirical process
given the sample `x` and the law of a process `Z` on `(Ω', P')`. The conditional expectation is
the average over all `n^n` resampling index maps. -/
def bootstrapBoundedLipschitzDistance {Ω' : Type*} [MeasurableSpace Ω'] {n : ℕ}
    (x : Fin n → ℝ) (Z : Ω' → ℝ → ℝ) (P' : Measure Ω') : ℝ :=
  ⨆ h : {h : (ℝ → ℝ) → ℝ // IsBoundedLipschitzOne h},
    |((Fintype.card (Fin n → Fin n) : ℝ))⁻¹ * ∑ σ, h.1 (bootstrapEmpiricalProcess x σ) -
      ∫ ω', h.1 (Z ω') ∂P'|

/-- GAPS 102.52: conditional convergence of the bootstrap empirical process. For iid real
observations with distribution function `F`, the bounded Lipschitz distance between the
conditional law of `√n (F*ₙ - Fₙ)` and the law of the `F`-Brownian bridge `B⁰ ∘ F` tends to zero
in outer probability. -/
theorem tendstoInProbability_bootstrapBoundedLipschitzDistance
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (P' : Measure Ω')
    [IsProbabilityMeasure P'] (W : ℝ≥0 → Ω' → ℝ) (hW : IsBrownianReal W P') :
    let Z := fun (ω' : Ω') (t : ℝ) ↦ W (cdf P t).toNNReal ω' - cdf P t * W 1 ω';
    ∀ ε > 0, Tendsto (fun n ↦ μ.real {ω | ε <
      bootstrapBoundedLipschitzDistance (fun i : Fin n ↦ X i ω) Z P'}) atTop (𝓝 0) := by
  sorry

/-- GAPS 102.60, for the studentized mean in dimension one (`d = 1`, `g = id`). Assume all
moments are finite, the variance is positive, and Cramér's condition holds for `(X, X²)`.
With `T = √n (X̄ - μ)/σ̂` and its resampling analogue `T* = √n (X̄* - X̄)/σ̂*`:
the Kolmogorov distance between the conditional law of `T*` and the law of `T` is `O_P(n⁻¹)`;
the Kolmogorov distance between the law of `T` and `N(0,1)` is
`n^{-1/2} sup_x |p₁(x) φ(x)| + o(n^{-1/2})` with `p₁(x) = γ (2x² + 1)/6`, `γ` the skewness;
and the one-sided percentile-`t` interval `(-∞, X̄ - n^{-1/2} σ̂ v̂_α]` has coverage
`1 - α + O(n⁻¹)`. The coverage statements for the normal-theory, percentile, two-sided, and
symmetric intervals are outside this scope. -/
theorem studentized_bootstrap_mean_second_order_accuracy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hmom : ∀ k : ℕ, Integrable (fun x ↦ |x| ^ k) P) (hv : 0 < Var[id; P])
    (hcramer : SatisfiesCramerCondition
      (P.map fun x ↦ (WithLp.toLp 2 ![x, x ^ 2] : EuclideanSpace ℝ (Fin 2))))
    (α : ℝ) (hα : α ∈ Ioo 0 (1 / 2)) :
    let m := ∫ x, x ∂P;
    let γ := (∫ x, (x - m) ^ 3 ∂P) / Real.sqrt (Var[id; P]) ^ 3;
    let sample := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ X i ω;
    let T := fun (n : ℕ) (ω : Ω) ↦
      studentizedStatistic n (finiteSampleMean (sample n ω)) m (finiteSampleSD (sample n ω));
    let Tstar := fun (n : ℕ) (ω : Ω) ↦ bootstrapLaw (fun y : Fin n → ℝ ↦
      studentizedStatistic n (finiteSampleMean y) (finiteSampleMean (sample n ω))
        (finiteSampleSD y)) (sample n ω);
    let v := fun (n : ℕ) (ω : Ω) ↦ sInf {t : ℝ | α ≤ cdf (Tstar n ω) t};
    IsBoundedInProbability μ (fun n ω ↦ n * kolmogorovDistance (Tstar n ω) (μ.map (T n))) ∧
      Tendsto (fun n : ℕ ↦ Real.sqrt n *
          kolmogorovDistance (μ.map (T n)) (gaussianReal 0 1) -
            sSup (range fun x : ℝ ↦ |γ * (2 * x ^ 2 + 1) / 6 * gaussianPDFReal 0 1 x|))
        atTop (𝓝 0) ∧
      (fun n : ℕ ↦ μ.real {ω | m ≤ finiteSampleMean (sample n ω) -
          (Real.sqrt n)⁻¹ * finiteSampleSD (sample n ω) * v n ω} - (1 - α))
        =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  sorry

end CKSD
