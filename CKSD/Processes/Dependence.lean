module

public import CKSD.Processes.Independence


/-!
# Strong mixing, the moving-block bootstrap, and Stein's prediction theorem

The strong mixing coefficient of a real process on `ℤ` compares the past `σ(X_s : s ≤ 0)` with
the future `σ(X_s : s ≥ k)`. The moving-block bootstrap law is the exact conditional law given
the data: the uniform average over all `(n - b + 1)^ℓ` tuples of block starting indices, with
observations `X_0, …, X_{n-1}`.

For Stein's theorem the random variables `h_1, h_2, …` are the coordinates of `ℕ → ℝ`, carrying
two centred Gaussian laws with prescribed finite-dimensional marginals. The best linear predictor
of `ψ` from the first `n` coordinates computed under covariance `k` has coefficients
`K_n⁻¹ c`, with `K_n` the Gram matrix of `k` and `c` the covariances of `ψ` with the coordinates.

## Main definitions

* `CKSD.pastSigmaAlgebra`, `CKSD.futureSigmaAlgebra`: `σ(X_s : s ≤ t)` and `σ(X_s : s ≥ t)`.
* `CKSD.strongMixingCoefficient`: the strong mixing coefficients `α(k)`.
* `CKSD.blockMean`, `CKSD.movingBlockBootstrapLaw`: the moving-block bootstrap.
* `CKSD.kernelGram`, `CKSD.linearPredictionError`: Gram matrices and errors of linear predictors.

## Main results

* `CKSD.indep_fun_of_measurable_past_sigma_algebra`: for an independent sequence, a function of the
  strict past `σ(ε_s : s < t)` is independent of `ε_t`; with the monotonicity and measurability
  lemmas for `pastSigmaAlgebra`.
* `CKSD.tendsto_in_measure_kolmogorov_distance_moving_block_bootstrap_law` (GAPS 106.11):
  consistency of the moving-block bootstrap for the mean of a strongly mixing sequence.
* `CKSD.eventually_abs_linear_prediction_error_div_sub_one_le` (GAPS 106.21): Stein's theorem on
  asymptotically efficient prediction under equivalent Gaussian laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- The past σ-algebra `σ(X_s : s ≤ t)` of a real process on `ℤ`. -/
@[instance_reducible]
def pastSigmaAlgebra {Ω : Type*} (X : ℤ → Ω → ℝ) (t : ℤ) : MeasurableSpace Ω :=
  ⨆ s : ℤ, ⨆ _ : s ≤ t, MeasurableSpace.comap (X s) inferInstance

/-- The coordinate `ε_s` is measurable with respect to the past `σ(ε_r : r ≤ t)` when `s ≤ t`. -/
theorem measurable_past_sigma_algebra_of_le {Ω : Type*}
    {ε : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    Measurable[pastSigmaAlgebra ε t] (ε s) :=
  Measurable.of_comap_le (le_iSup₂_of_le s hst le_rfl)

/-- The past σ-algebras increase with time. -/
theorem past_sigma_algebra_mono {Ω : Type*} (ε : ℤ → Ω → ℝ) {s t : ℤ} (hst : s ≤ t) :
    pastSigmaAlgebra ε s ≤ pastSigmaAlgebra ε t :=
  iSup₂_le fun r hr ↦ le_iSup₂_of_le r (hr.trans hst) le_rfl

/-- The past σ-algebras of a measurable process are sub-σ-algebras. -/
theorem past_sigma_algebra_le {Ω : Type*} [MeasurableSpace Ω] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (t : ℤ) : pastSigmaAlgebra ε t ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun r _ ↦ (hm r).comap_le

/-- A function of the strict past `σ(ε_s : s < t)` of an independent sequence is independent
of `ε_t`. -/
theorem indep_fun_of_measurable_past_sigma_algebra {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (t : ℤ) {Y : Ω → ℝ} (hY : Measurable[pastSigmaAlgebra ε (t - 1)] Y) :
    IndepFun Y (ε t) μ :=
  indep_fun_of_measurable_bi_sup_of_not_mem hm hind (S := {s | s ≤ t - 1}) (by simp) hY

/-- The future σ-algebra `σ(X_s : s ≥ t)` of a real process on `ℤ`. -/
@[instance_reducible]
def futureSigmaAlgebra {Ω : Type*} (X : ℤ → Ω → ℝ) (t : ℤ) : MeasurableSpace Ω :=
  ⨆ s : ℤ, ⨆ _ : t ≤ s, MeasurableSpace.comap (X s) inferInstance

/-- The strong mixing coefficient
`α(k) = sup |P(A ∩ B) - P(A) P(B)|` over `A ∈ σ(X_s : s ≤ 0)`, `B ∈ σ(X_s : s ≥ k)`. -/
def strongMixingCoefficient {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℤ → Ω → ℝ) (k : ℕ) : ℝ :=
  sSup {r | ∃ A B : Set Ω, MeasurableSet[pastSigmaAlgebra X 0] A ∧
    MeasurableSet[futureSigmaAlgebra X k] B ∧ r = |μ.real (A ∩ B) - μ.real A * μ.real B|}

/-- The mean of the block `x_i, …, x_{i+b-1}`. -/
def blockMean (x : ℕ → ℝ) (b i : ℕ) : ℝ :=
  (b : ℝ)⁻¹ * ∑ k ∈ Finset.range b, x (i + k)

/-- The moving-block bootstrap law of `√(ℓb) (X̄*_n - 𝔼* X̄*_n)` given data `x_0, …, x_{n-1}`,
for block length `b` and `ℓ = ⌊n/b⌋` blocks with starting indices uniform on `n - b + 1`
positions. -/
def movingBlockBootstrapLaw (x : ℕ → ℝ) (n b : ℕ) : Measure ℝ :=
  ((((n - b + 1) ^ (n / b) : ℕ) : ℝ≥0∞))⁻¹ •
    ∑ I : Fin (n / b) → Fin (n - b + 1),
      Measure.dirac (Real.sqrt ((n / b : ℕ) * b) *
        ((((n / b : ℕ) : ℝ))⁻¹ * ∑ j, blockMean x b (I j) -
          (((n - b + 1 : ℕ) : ℝ))⁻¹ * ∑ i : Fin (n - b + 1), blockMean x b i))

/-- GAPS 106.11: consistency of the moving-block bootstrap for the mean of a strictly
stationary strongly mixing sequence with `𝔼|X|^{2+δ} < ∞` and `∑ α(k)^{δ/(2+δ)} < ∞`:
the autocovariances are absolutely summable, `√n (X̄_n - μ) ⇒ N(0, σ²_∞)`, and the Kolmogorov
distance between the bootstrap law and the law of `√n (X̄_n - μ)` tends to `0` in probability,
for block lengths `b → ∞` with `b/n → 0` (so that eventually `1 ≤ b ≤ n`). -/
theorem tendsto_in_measure_kolmogorov_distance_moving_block_bootstrap_law {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hstat : ∀ h : ℤ, μ.map (fun ω t ↦ X (t + h) ω) = μ.map (fun ω t ↦ X t ω))
    (δ : ℝ) (hδ : 0 < δ) (hmom : MemLp (X 0) (ENNReal.ofReal (2 + δ)) μ)
    (hmix : Summable fun k : ℕ ↦ strongMixingCoefficient μ X k ^ (δ / (2 + δ)))
    (hσ : 0 < ∑' k : ℤ, cov[X k, X 0; μ])
    (b : ℕ → ℕ) (hb : Tendsto b atTop atTop)
    (hb' : Tendsto (fun n ↦ (b n : ℝ) / n) atTop (𝓝 0)) :
    let σsq := ∑' k : ℤ, cov[X k, X 0; μ]
    let S : ℕ → Ω → ℝ := fun n ω ↦
      Real.sqrt n * (sampleAverage (fun t : ℕ ↦ X t) n ω - ∫ ω', X 0 ω' ∂μ)
    Summable (fun k : ℤ ↦ |cov[X k, X 0; μ]|) ∧
      TendstoInDistribution S atTop id (fun _ ↦ μ) (gaussianReal 0 (Real.toNNReal σsq)) ∧
      TendstoInMeasure μ (fun (n : ℕ) ω ↦
        kolmogorovDistance (movingBlockBootstrapLaw (fun t ↦ X t ω) n (b n)) (μ.map (S n)))
            atTop (fun _ ↦ 0) := by
  sorry

/-- The Gram matrix `(k i j)_{i,j<n}` of a covariance kernel on the first `n` indices. -/
def kernelGram (k : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ k i j

/-- The error `ψ - ∑_i a_i h_i` of the best linear predictor of `ψ` from the first `n`
coordinates, computed as if the covariance were `k`, with cross-covariances of `ψ` taken under
the law `Q` whose coordinate covariance is `k`. -/
def linearPredictionError (Q : Measure (ℕ → ℝ)) (k : ℕ → ℕ → ℝ) (n : ℕ)
    (ψ : (ℕ → ℝ) → ℝ) (x : ℕ → ℝ) : ℝ :=
  ψ x - ∑ i : Fin n,
    ((kernelGram k n)⁻¹.mulVec (fun j : Fin n ↦ ∫ y, y j * ψ y ∂Q)) i * x i

/-- GAPS 106.21: Stein's theorem on asymptotically efficient prediction under equivalent
Gaussian laws. The coordinates are linearly independent under `k₀`, the laws `P₀` and `P₁` are
centred Gaussian with covariances `k₀` and `k₁`, and `ψ` ranges over the closed linear span `H`
of the coordinates in `L²(P₀)`. Uniformly over `ψ ∈ H` with nonzero `P₀`-error, the relative
excess error of the `k₁`-predictor and the relative misstatement of its error tend to zero; the
exchanged roles are the same statement applied to `(k₁, P₁, k₀, P₀)`. The Gram matrices of
`k₁` are automatically positive semidefinite: otherwise the marginal of `P₁` is a Dirac mass,
which is not equivalent to the nondegenerate marginal of `P₀`. -/
theorem eventually_abs_linear_prediction_error_div_sub_one_le (k₀ k₁ : ℕ → ℕ → ℝ)
    (P₀ P₁ : Measure (ℕ → ℝ)) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (hk₀ : ∀ n, (kernelGram k₀ n).PosDef)
    (hP₀ : ∀ n, P₀.map (fun x ↦ WithLp.toLp 2 fun i : Fin n ↦ x i) =
      multivariateGaussian 0 (kernelGram k₀ n))
    (hP₁ : ∀ n, P₁.map (fun x ↦ WithLp.toLp 2 fun i : Fin n ↦ x i) =
      multivariateGaussian 0 (kernelGram k₁ n))
    (hequiv : P₀ ≪ P₁ ∧ P₁ ≪ P₀) :
    let H : Set ((ℕ → ℝ) → ℝ) := {ψ | MemLp ψ 2 P₀ ∧ ∀ ε > 0, ∃ (n : ℕ) (c : Fin n → ℝ),
      (∫ x, (ψ x - ∑ i, c i * x i) ^ 2 ∂P₀) < ε}
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ ψ ∈ H,
      0 < (∫ x, linearPredictionError P₀ k₀ n ψ x ^ 2 ∂P₀) →
        |(∫ x, linearPredictionError P₁ k₁ n ψ x ^ 2 ∂P₀) /
            (∫ x, linearPredictionError P₀ k₀ n ψ x ^ 2 ∂P₀) - 1| ≤ ε ∧
          |(∫ x, linearPredictionError P₀ k₀ n ψ x ^ 2 ∂P₁) /
            (∫ x, linearPredictionError P₀ k₀ n ψ x ^ 2 ∂P₀) - 1| ≤ ε := by
  sorry

end CKSD
