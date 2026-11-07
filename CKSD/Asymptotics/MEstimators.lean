module

public import CKSD.Asymptotics.Statistics

/-!
# Consistency and local normality of extremum estimators

These formulations separate measurable sample criteria, deterministic local curvature, and the
quality of the empirical optimization. Sources: GAPS 102.2, 102.24, and 102.48. Wald consistency
is stated with continuous positive densities and an integrable envelope of their log likelihoods;
the more general upper-semicontinuous formulation is outside that scope.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Empirical average of a real criterion evaluated at a parameter. -/
def empiricalCriterion {Ω X Θ : Type*} (m : Θ → X → ℝ)
    (Xn : ℕ → Ω → X) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (∑ i ∈ Finset.range n, m θ (Xn i ω)) / n

/-- Population criterion under a fixed data-generating law. -/
def populationCriterion {X Θ : Type*} [MeasurableSpace X]
    (P : Measure X) (m : Θ → X → ℝ) (θ : Θ) : ℝ := ∫ x, m θ x ∂P

/-- GAPS 102.2: Wald consistency with continuous positive densities on a compact parameter space.
The log-likelihood envelope is integrable at the true law; identifiability concerns the laws,
so no irrelevant distinction between density versions is required. -/
theorem tendstoInProbabilityConst_mle_of_compact
    {Ω X Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Θ → Measure X)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (ν : Measure X) [SigmaFinite ν]
    (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hcont : ∀ x, Continuous (fun θ ↦ f θ x))
    (hid : Function.Injective P) (θ₀ : Θ) (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn (P θ₀))
    (B : X → ℝ) (hB : Integrable B (P θ₀))
    (henv : ∀ θ x, |Real.log (f θ x)| ≤ B x)
    (T : ℕ → Ω → Θ) (hT : ∀ n, Measurable (T n))
    (r : ℕ → Ω → ℝ) (hr : TendstoInProbabilityConst μ r 0)
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ,
      empiricalCriterion (fun θ x ↦ Real.log (f θ x)) Xn n ω θ₀ - r n ω ≤
        empiricalCriterion (fun θ x ↦ Real.log (f θ x)) Xn n ω (T n ω)) :
    TendstoInProbabilityConst μ T θ₀ := by
  sorry

/-- GAPS 102.24: local asymptotic linearity and normality of multivariate M-estimators.
The negative-definite matrix `V` is the Hessian of the population criterion through its
quadratic little-o expansion. The empirical optimization error is `o_P(1/n)`. -/
theorem m_estimator_asymptotic_linearization_and_normality
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (m : EuclideanSpace ℝ (Fin d) → X → ℝ) (hm : ∀ θ, Measurable (m θ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (score : X → EuclideanSpace ℝ (Fin d))
    (hs : MemLp score 2 P) (hs0 : (∫ x, score x ∂P) = 0)
    (hd : ∀ᵐ x ∂P, HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (score x)) θ₀)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (B : X → ℝ) (hB : MemLp B 2 P)
    (hlip : ∀ᵐ x ∂P, ∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀,
      |m a x - m b x| ≤ B x * ‖a - b‖)
    (hmi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (m θ) P)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : (-V).PosDef)
    (hquad : Asymptotics.IsLittleO (𝓝 0)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ populationCriterion P m (θ₀ + h) -
        populationCriterion P m θ₀ -
          inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ 2))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityConst μ T θ₀)
    (r : ℕ → Ω → ℝ)
    (hr : TendstoInProbabilityConst μ (fun n ω ↦ (n : ℝ) * r n ω) 0)
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ θ,
      empiricalCriterion m Xn n ω θ - r n ω ≤ empiricalCriterion m Xn n ω (T n ω)) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n • (T n ω - θ₀) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
        ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, score (Xn i ω))) 0 ∧
      TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (T n ω - θ₀))
        (multivariateGaussian 0
          (V⁻¹ * fisherInformationMatrix P score * (V⁻¹).transpose)) := by
  sorry

/-- Fixed-design convex regression objective. -/
def regressionMObjective {d : ℕ} (ρ : ℝ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (y : ℕ → ℝ) (n : ℕ) (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ Finset.range n, ρ (y i - inner ℝ (x i) β)

/-- Empirical Gram matrix of the first `n` fixed-design rows. -/
def fixedDesignGramMatrix {d : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin d))
    (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (∑ k ∈ Finset.range n, x k i * x k j) / n

/-- GAPS 102.48: asymptotic linearization and normality of fixed-design convex M-estimators.
The right derivative of `ρ` is `ψ`. The `L²` continuity of shifted scores is expressed by
nonnegative extended integrals, so nonintegrable remainders cannot be assigned value zero. -/
theorem regression_m_estimator_asymptotic_linearization_and_normality
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ ε P)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (hgram : Tendsto (fixedDesignGramMatrix x) atTop (𝓝 Q))
    (hleverage : Tendsto (fun n : ℕ ↦
      sSup (range fun i : Fin n ↦ ‖x i.val‖) / Real.sqrt n) atTop (𝓝 0))
    (ρ ψ : ℝ → ℝ) (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hder : ∀ u, HasDerivWithinAt ρ (ψ u) (Ici u) u)
    (hψ2 : MemLp ψ 2 P) (hψ0 : (∫ z, ψ z ∂P) = 0)
    (hcont : Tendsto (fun t : ℝ ↦ ∫⁻ z, ENNReal.ofReal ((ψ (z - t) - ψ z) ^ 2) ∂P)
      (𝓝 0) (𝓝 0))
    (γ : ℝ) (hγ : 0 < γ)
    (hmean : HasDerivAt (fun t ↦ ∫ z, ψ (z - t) ∂P) (-γ) 0)
    (β : EuclideanSpace ℝ (Fin d)) (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hT : ∀ n, Measurable (T n))
    (hmin : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ b,
      regressionMObjective ρ x (fun i ↦ inner ℝ (x i) β + ε i ω) n (T n ω) ≤
        regressionMObjective ρ x (fun i ↦ inner ℝ (x i) β + ε i ω) n b) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n • (T n ω - β) -
      (γ * Real.sqrt n)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹
        (∑ i ∈ Finset.range n, ψ (ε i ω) • x i)) 0 ∧
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (T n ω - β))
      (multivariateGaussian 0 (((∫ z, ψ z ^ 2 ∂P) / γ ^ 2) • Q⁻¹)) := by
  sorry

/-- An empirical criterion is unchanged if its per-observation criterion is translated. -/
theorem empiricalCriterion_add_const {Ω X Θ : Type*} (m : Θ → X → ℝ)
    (Xn : ℕ → Ω → X) (n : ℕ) (hn : n ≠ 0) (ω : Ω) (θ : Θ) (c : ℝ) :
    empiricalCriterion (fun θ x ↦ m θ x + c) Xn n ω θ =
      empiricalCriterion m Xn n ω θ + c := by
  simp only [empiricalCriterion, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The zero-sample convex regression objective has value zero. -/
@[simp] theorem regressionMObjective_zero {d : ℕ} (ρ : ℝ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin d)) :
    regressionMObjective ρ x y 0 β = 0 := by simp [regressionMObjective]

end CKSD
