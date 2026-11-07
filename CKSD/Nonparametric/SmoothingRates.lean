module

public import CKSD.Nonparametric.Models

/-!
# Regression smoothers and one-dimensional Hölder rates

The Hölder interfaces in this file have order in `(0,1]`. The fixed-design model samples at
`(i+1)/n`, so it uses the same endpoint convention as GAPS 103.22. All minimax risks are
nonnegative extended-real integrals over measurable estimators. Sources: GAPS 103.7, 103.22,
and 103.26. The higher-order local-polynomial and Sobolev parts are outside these statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The finite-sample Nadaraya–Watson predictor formed from paired observations. -/
def nadarayaWatsonSample {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ)
    (sample : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  nadarayaWatson K h (fun i ↦ (sample i).1) (fun i ↦ (sample i).2) x

/-- GAPS 103.7: universal prediction consistency of the Nadaraya–Watson estimator.
The regression mean is given as a version of conditional expectation, with its `L²` property
explicit. The kernel has upper and positive local lower ball bounds. -/
theorem tendsto_nadarayaWatson_prediction_error_probability
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d) × ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (hY : MemLp Prod.snd 2 P)
    (m : EuclideanSpace ℝ (Fin d) → ℝ) (hm : Measurable m)
    (hm2 : MemLp m 2 (P.map Prod.fst))
    (hmean : P[(fun z ↦ z.2) |
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))).comap Prod.fst] =ᵐ[P]
        fun z ↦ m z.1)
    (K : EuclideanSpace ℝ (Fin d) → ℝ) (hK : Measurable K)
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hR : r ≤ R)
    (hlower : ∀ x, ‖x‖ ≤ r → a ≤ K x)
    (hupper : ∀ x, 0 ≤ K x ∧ K x ≤ b)
    (hsupp : ∀ x, R < ‖x‖ → K x = 0)
    (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n ^ d) atTop atTop) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ μ.real {ω |
      ENNReal.ofReal ε < regressionPredictionError (P.map Prod.fst) m
        (nadarayaWatsonSample K (h n) (fun i : Fin n ↦ X i.val ω))}) atTop (𝓝 0) := by
  sorry

/-- Measurable functions on the line with a Hölder increment bound on the unit interval.
There is no bound on an additive constant. -/
def holderRegressionClass (β L : ℝ) : Set (ℝ → ℝ) :=
  {f | Measurable f ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |f x - f y| ≤ L * Real.rpow |x - y| β}

/-- Fixed-design Gaussian regression law with noise standard deviation `σ`. -/
def fixedDesignRegressionLaw (n : ℕ) (f : ℝ → ℝ) (σ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i ↦ gaussianReal (f (((i.val + 1 : ℕ) : ℝ) / n))
    (Real.toNNReal (σ ^ 2)))

/-- Mean integrated squared error of a predictor under the fixed-design Gaussian experiment. -/
def fixedDesignRegressionRisk {n : ℕ} (f : ℝ → ℝ) (σ : ℝ)
    (estimate : (Fin n → ℝ) → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ((estimate y t - f t) ^ 2))
    ∂fixedDesignRegressionLaw n f σ

/-- Fixed-design Hölder minimax mean integrated squared risk over jointly measurable estimators. -/
def holderRegressionMinimaxRisk (n : ℕ) (β L σ : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → ℝ → ℝ // Measurable (Function.uncurry T)},
    ⨆ f : holderRegressionClass β L, fixedDesignRegressionRisk f.val σ T.val

/-- Box-kernel local-constant regression on the fixed design. -/
def fixedDesignLocalConstant {n : ℕ} (h : ℝ) (y : Fin n → ℝ) (t : ℝ) : ℝ :=
  let w := fun i : Fin n ↦ if |t - ((i.val + 1 : ℕ) : ℝ) / n| ≤ h then (1 : ℝ) else 0
  (∑ i, w i * y i) / (∑ i, w i)

/-- GAPS 103.22: the fixed-design `L²` Hölder minimax rate for orders at most one.
This states both bounds; sup-norm risk and higher local-polynomial orders are not asserted. -/
theorem holderRegressionMinimaxRisk_bounds (β L σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderRegressionMinimaxRisk n β L σ ∧
      holderRegressionMinimaxRisk n β L σ ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  sorry

/-- GAPS 103.22: a box-kernel local-constant estimator attains the `L²` rate for `0<β≤1`. -/
theorem fixedDesignLocalConstant_risk_le (β L σ c : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hσ : 0 < σ) (hc : 1 ≤ c) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ f ∈ holderRegressionClass β L,
      fixedDesignRegressionRisk (n := n) f σ
        (fixedDesignLocalConstant (n := n) (c * Real.rpow (n : ℝ) (-1 / (2 * β + 1)))) ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  sorry

/-- Hölder probability density class on the line, for smoothness orders at most one. -/
def holderDensityClass (β L : ℝ) : Set (ℝ → ℝ) :=
  {f | Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ (∫ x, f x) = 1 ∧
    ∀ x y, |f x - f y| ≤ L * Real.rpow |x - y| β}

/-- The probability law represented by a real density. -/
def densityLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- A finite-sample kernel density estimator at a specified point. -/
def finiteKernelDensityEstimator {n : ℕ} (K : ℝ → ℝ) (h : ℝ)
    (sample : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, K ((t - sample i) / h)) / ((n : ℝ) * h)

/-- Pointwise minimax risk for density estimation on a Hölder class. -/
def holderDensityPointwiseMinimaxRisk (n : ℕ) (β L x : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → ℝ // Measurable T},
    ⨆ f : holderDensityClass β L,
      ∫⁻ sample, ENNReal.ofReal ((T.val sample - f.val x) ^ 2)
        ∂(Measure.pi fun _ : Fin n ↦ densityLaw f.val)

/-- GAPS 103.26: the kernel upper bound for pointwise Hölder density risk with `0<β≤1`.
The moment condition is the order-zero kernel condition appropriate in this range. -/
theorem finiteKernelDensityEstimator_risk_le (β L c : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) (hc : 0 < c)
    (K : ℝ → ℝ) (hK : Measurable K) (hKi : Integrable K volume)
    (hK1 : (∫ x, K x) = 1) (hK2 : MemLp K 2 volume)
    (hKm : Integrable (fun x ↦ Real.rpow |x| β * |K x|) volume) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ f ∈ holderDensityClass β L, ∀ x : ℝ,
      (∫⁻ sample, ENNReal.ofReal
        ((finiteKernelDensityEstimator K (c * Real.rpow (n : ℝ) (-1 / (2 * β + 1))) sample x -
          f x) ^ 2) ∂(Measure.pi fun _ : Fin n ↦ densityLaw f)) ≤
      ENNReal.ofReal (C * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) := by
  sorry

/-- GAPS 103.26: the matching pointwise minimax lower bound for Hölder orders at most one. -/
theorem holderDensityPointwiseMinimaxRisk_lower_bound (β L : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hL : 0 < L) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 * β / (2 * β + 1))) ≤
        holderDensityPointwiseMinimaxRisk n β L x := by
  sorry

/-- A Nadaraya–Watson predictor is nonnegative when observations and weights are nonnegative. -/
theorem nadarayaWatson_nonneg {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : ∀ x, 0 ≤ K x) (h : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (t : EuclideanSpace ℝ (Fin d)) :
    0 ≤ nadarayaWatson K h x y t := by
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hK _) (hy i))
    (Finset.sum_nonneg fun i _ ↦ hK _)

/-- A nonempty normalized set of kernel weights reproduces a constant response. -/
theorem nadarayaWatson_const {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (t : EuclideanSpace ℝ (Fin d))
    (hden : (∑ i, K (h⁻¹ • (x i - t))) ≠ 0) :
    nadarayaWatson K h x (fun _ ↦ c) t = c := by
  unfold nadarayaWatson
  rw [← Finset.sum_mul, mul_div_cancel_left₀ _ hden]

end CKSD
