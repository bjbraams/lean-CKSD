module

public import CKSD.Processes.Basic
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Periodogram, lag-window estimation, linear prediction, and Whittle estimation

The periodogram of `X_0, …, X_{n-1}` is `I_n(x) = (2πn)⁻¹ |∑_t X_t e^{-itx}|²`, the
normalization under which `𝔼 I_n → f` for the spectral density `f`, with
`γ(h) = ∫ e^{ihx} f(x) dx`. Observations are indexed from zero. Lag-window estimators use the
mean-corrected sample autocovariances `sampleAutocovariance` with divisor `n`.

The prediction-error formula is stated for a centred weakly stationary sequence in a complex
inner-product space, the abstract form of a centred `L²` process; the one-step error from the
infinite past is the distance to the linear span of the past.

The ARMA polynomials are `φ(z) = 1 - ∑ φ_i z^i` and `θ(z) = 1 + ∑ θ_j z^j`, with the parameter
`β = (φ_1, …, φ_p, θ_1, …, θ_q)` indexed by `Fin p ⊕ Fin q`.

Sources: GAPS 106.6, 106.16, and 106.17.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The two-sided linear process `X_t = ∑_j ψ_j Z_{t-j}`, as a pointwise series. -/
def linearProcess {Ω : Type*} (ψ : ℤ → ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ∑' j : ℤ, ψ j * Z (t - j) ω

/-- The transfer function `∑_j ψ_j e^{-ijx}` of a two-sided filter. -/
def transferFunction (ψ : ℤ → ℝ) (x : ℝ) : ℂ :=
  ∑' j : ℤ, (ψ j : ℂ) * Complex.exp (-((j : ℝ) * x : ℝ) * Complex.I)

/-- The spectral density `σ² |∑_j ψ_j e^{-ijx}|² / (2π)` of a linear process with innovation
variance `σ²`. -/
def linearProcessSpectralDensity (σsq : ℝ) (ψ : ℤ → ℝ) (x : ℝ) : ℝ :=
  σsq / (2 * Real.pi) * ‖transferFunction ψ x‖ ^ 2

/-- The periodogram `I_n(x) = (2πn)⁻¹ |∑_{t<n} X_t e^{-itx}|²` of `X_0, …, X_{n-1}`. -/
def periodogram {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (2 * Real.pi * n)⁻¹ *
    ‖∑ t ∈ Finset.range n, (X t ω : ℂ) * Complex.exp (-((t : ℝ) * x : ℝ) * Complex.I)‖ ^ 2

/-- The Fourier frequency `2πk/n` nearest to `x`, with `k` the rounded value of `nx/(2π)`. -/
def nearestFourierFrequency (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.pi * (round ((n : ℝ) * x / (2 * Real.pi)) : ℝ) / n

/-- A lag window: an even function with `w 0 = 1`, `|w| ≤ 1`, vanishing outside `[-1,1]`,
continuous at `0` and continuous on `[-1,1]` off a finite set (this contains the piecewise
continuous windows). -/
def IsLagWindow (w : ℝ → ℝ) : Prop :=
  (∀ u, w (-u) = w u) ∧ w 0 = 1 ∧ (∀ u, |w u| ≤ 1) ∧ (∀ u, 1 < |u| → w u = 0) ∧
    ContinuousAt w 0 ∧ ∃ s : Finset ℝ, ContinuousOn w (Icc (-1) 1 \ (s : Set ℝ))

/-- The lag-window spectral estimator
`(2π)⁻¹ ∑_{|h| ≤ r} w(h/r) γ̂(h) e^{-ihx}`, written with `γ̂(-h) = γ̂(h)` as a cosine sum. -/
def lagWindowEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (w : ℝ → ℝ) (r n : ℕ) (ω : Ω) (x : ℝ) :
    ℝ :=
  (2 * Real.pi)⁻¹ * ∑ h ∈ Finset.Icc (-(r : ℤ)) r,
    w ((h : ℝ) / r) * sampleAutocovariance X h.natAbs n ω * Real.cos ((h : ℝ) * x)

/-- GAPS 106.6: periodogram ordinates at Fourier frequencies nearest to fixed frequencies in
`(0, π)`, divided by the spectral density, converge jointly in law to independent standard
exponential variables, for a linear process with absolutely summable coefficients and iid
innovations of finite positive variance. The non-consistency corollary is not restated. -/
theorem tendstoInDistribution_periodogram_div_spectralDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℤ → Ω → ℝ) (hZm : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z μ) (hlaw : ∀ t, μ.map (Z t) = μ.map (Z 0)) (h2 : MemLp (Z 0) 2 μ)
    (h0 : (∫ ω, Z 0 ω ∂μ) = 0) (σsq : ℝ) (hσ : 0 < σsq) (hvar : (∫ ω, Z 0 ω ^ 2 ∂μ) = σsq)
    (ψ : ℤ → ℝ) (hψ : Summable fun j ↦ |ψ j|)
    (hf : ∀ x, 0 < linearProcessSpectralDensity σsq ψ x)
    (m : ℕ) (x : Fin m → ℝ) (hx : StrictMono x) (hx0 : ∀ j, 0 < x j)
    (hxπ : ∀ j, x j < Real.pi) :
    TendstoInDistribution μ (fun n ω ↦ WithLp.toLp 2 fun j : Fin m ↦
      periodogram (fun t ↦ linearProcess ψ Z t) n ω (nearestFourierFrequency n (x j)) /
        linearProcessSpectralDensity σsq ψ (x j))
      ((Measure.pi fun _ : Fin m ↦ expMeasure 1).map (WithLp.toLp 2)) := by
  sorry

/-- GAPS 106.6: asymptotic mean and variance, and mean-square consistency, of a lag-window
spectral estimator for a linear process with `∑ |ψ_j| |j|^{1/2} < ∞` and iid innovations with
finite fourth moment, when the truncation point `r` satisfies `r → ∞` and `r/n → 0`.
The window is assumed continuous at `0` (see `IsLagWindow`). -/
theorem tendsto_lagWindowEstimator_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℤ → Ω → ℝ) (hZm : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z μ) (hlaw : ∀ t, μ.map (Z t) = μ.map (Z 0)) (h4 : MemLp (Z 0) 4 μ)
    (h0 : (∫ ω, Z 0 ω ∂μ) = 0) (σsq : ℝ) (hσ : 0 < σsq) (hvar : (∫ ω, Z 0 ω ^ 2 ∂μ) = σsq)
    (ψ : ℤ → ℝ) (hψ : Summable fun j ↦ |ψ j|)
    (hψ' : Summable fun j : ℤ ↦ |ψ j| * Real.sqrt |(j : ℝ)|)
    (hf : ∀ x, 0 < linearProcessSpectralDensity σsq ψ x)
    (w : ℝ → ℝ) (hw : IsLagWindow w) (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n ↦ (r n : ℝ) / n) atTop (𝓝 0)) (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
    let X : ℕ → Ω → ℝ := fun t ↦ linearProcess ψ Z t
    let f := linearProcessSpectralDensity σsq ψ x
    let c : ℝ := if x = 0 ∨ x = Real.pi then 2 else 1
    Tendsto (fun n ↦ ∫ ω, lagWindowEstimator X w (r n) n ω x ∂μ) atTop (𝓝 f) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) / r n * variance μ (fun ω ↦ lagWindowEstimator X w (r n) n ω x))
        atTop (𝓝 (c * f ^ 2 * ∫ u in (-1 : ℝ)..1, w u ^ 2)) ∧
      Tendsto (fun n ↦ ∫ ω, (lagWindowEstimator X w (r n) n ω x - f) ^ 2 ∂μ) atTop (𝓝 0) := by
  sorry

/-- GAPS 106.16: Kolmogorov's (Szegő's) formula for the one-step prediction error of a centred
weakly stationary sequence from its infinite past. Here `X` lies in a complex inner-product
space, `⟪X s, X t⟫ = γ(t - s)`, the spectral measure `F` lives on `(-π, π]`, and `f` is the
density of its absolutely continuous part. The value `0` is taken exactly when `log f` fails to
be integrable or `f` vanishes on a set of positive measure, i.e. when `∫ log f = -∞`. -/
theorem infDist_past_sq_eq_kolmogorov {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (X : ℤ → H)
    (hstat : ∀ s t, inner ℂ (X s) (X t) = inner ℂ (X 0) (X (t - s)))
    (F : Measure ℝ) [IsFiniteMeasure F] (hF : F (Ioc (-Real.pi) Real.pi)ᶜ = 0)
    (hγ : ∀ h : ℤ, inner ℂ (X 0) (X h) =
      ∫ ν, Complex.exp (((h : ℝ) * ν : ℝ) * Complex.I) ∂F) :
    let f : ℝ → ℝ := fun ν ↦ (F.rnDeriv volume ν).toReal
    Metric.infDist (X 0) (Submodule.span ℂ (X '' Iio 0) : Set H) ^ 2 =
      if (∀ᵐ ν ∂(volume.restrict (Ioc (-Real.pi) Real.pi)), 0 < f ν) ∧
          IntegrableOn (fun ν ↦ Real.log (f ν)) (Ioc (-Real.pi) Real.pi) then
        2 * Real.pi * Real.exp ((2 * Real.pi)⁻¹ *
          ∫ ν in Ioc (-Real.pi) Real.pi, Real.log (f ν))
      else 0 := by
  sorry

/-- The autoregressive polynomial `φ(z) = 1 - ∑_{i=1}^p φ_i z^i`. -/
def arPolynomial {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) (z : ℂ) : ℂ :=
  1 - ∑ i : Fin p, (β (Sum.inl i) : ℂ) * z ^ (i.val + 1)

/-- The moving-average polynomial `θ(z) = 1 + ∑_{j=1}^q θ_j z^j`. -/
def maPolynomial {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) (z : ℂ) : ℂ :=
  1 + ∑ j : Fin q, (β (Sum.inr j) : ℂ) * z ^ (j.val + 1)

/-- The ARMA spectral shape `g(x; β) = |θ(e^{-ix})|² / |φ(e^{-ix})|²`. -/
def armaSpectralShape {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) (x : ℝ) : ℝ :=
  ‖maPolynomial β (Complex.exp (-(x : ℂ) * Complex.I))‖ ^ 2 /
    ‖arPolynomial β (Complex.exp (-(x : ℂ) * Complex.I))‖ ^ 2

/-- The last autoregressive coefficient `φ_p`, read as `0` when `p = 0`. -/
def lastArCoefficient {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) : ℝ :=
  if h : 0 < p then β (Sum.inl ⟨p - 1, Nat.sub_lt h one_pos⟩) else 0

/-- The last moving-average coefficient `θ_q`, read as `0` when `q = 0`. -/
def lastMaCoefficient {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) : ℝ :=
  if h : 0 < q then β (Sum.inr ⟨q - 1, Nat.sub_lt h one_pos⟩) else 0

/-- Causal, invertible, identifiable ARMA(p,q) parameters: `φ(z) θ(z) ≠ 0` on the closed unit
disc, no common zeros, and `(φ_p, θ_q) ≠ (0,0)` (vacuous for `p = q = 0`). -/
def armaAdmissibleParameters (p q : ℕ) : Set (EuclideanSpace ℝ (Fin p ⊕ Fin q)) :=
  {β | (∀ z : ℂ, ‖z‖ ≤ 1 → arPolynomial β z * maPolynomial β z ≠ 0) ∧
    (∀ z : ℂ, ¬(arPolynomial β z = 0 ∧ maPolynomial β z = 0)) ∧
    (p + q = 0 ∨ (lastArCoefficient β, lastMaCoefficient β) ≠ (0, 0))}

/-- The Whittle objective `n⁻¹ ∑_j I_n(ω_j) / g(ω_j; β)` over the Fourier frequencies
`ω_j = 2πj/n`, `0 ≤ j < n`; by `2π`-periodicity this equals the sum over `(-π, π]`. -/
def whittleObjective {Ω : Type*} {p q : ℕ} (X : ℕ → Ω → ℝ) (n : ℕ)
    (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
    periodogram X n ω (2 * Real.pi * j / n) / armaSpectralShape β (2 * Real.pi * j / n)

/-- The asymptotic information matrix
`W(β) = (4π)⁻¹ ∫_{-π}^{π} ∇ log g ∇ log gᵀ` of ARMA estimation. -/
def armaAsymptoticInformation {p q : ℕ} (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.of fun i j ↦ (4 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi,
    gradient (fun b ↦ Real.log (armaSpectralShape b x)) β i *
      gradient (fun b ↦ Real.log (armaSpectralShape b x)) β j

/-- GAPS 106.17, Whittle-estimator case: for a causal invertible ARMA(p,q) process with iid,
not necessarily Gaussian, innovations of variance `σ² > 0`, every measurable approximate
minimizer of the Whittle objective over the admissible parameters (to within `(n+1)⁻²`) is
strongly consistent, the Whittle innovation-variance estimator `2π · min` converges almost surely
to `σ²`, and `√n (β̂ - β) ⇒ N(0, W(β)⁻¹)`. The process is any `L²`-bounded solution of the ARMA
equations, which is the stationary causal solution. The Gaussian maximum-likelihood and
least-squares estimators, and the autoregressive identity `W⁻¹ = σ² Γ_p⁻¹`, are not covered. -/
theorem whittleEstimator_asymptotics {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p q : ℕ} (Z : ℤ → Ω → ℝ)
    (hZm : ∀ t, Measurable (Z t)) (hind : iIndepFun Z μ)
    (hlaw : ∀ t, μ.map (Z t) = μ.map (Z 0)) (h2 : MemLp (Z 0) 2 μ)
    (h0 : (∫ ω, Z 0 ω ∂μ) = 0) (σsq : ℝ) (hσ : 0 < σsq) (hvar : (∫ ω, Z 0 ω ^ 2 ∂μ) = σsq)
    (β : EuclideanSpace ℝ (Fin p ⊕ Fin q)) (hβ : β ∈ armaAdmissibleParameters p q)
    (X : ℤ → Ω → ℝ) (hX2 : ∀ t, MemLp (X t) 2 μ)
    (hXbdd : ∃ C, ∀ t, (∫ ω, X t ω ^ 2 ∂μ) ≤ C)
    (harma : ∀ t, ∀ᵐ ω ∂μ, X t ω - ∑ i : Fin p, β (Sum.inl i) * X (t - (i.val + 1)) ω =
      Z t ω + ∑ j : Fin q, β (Sum.inr j) * Z (t - (j.val + 1)) ω)
    (βhat : ℕ → Ω → EuclideanSpace ℝ (Fin p ⊕ Fin q)) (hmeas : ∀ n, Measurable (βhat n))
    (hmin : ∀ n ω, βhat n ω ∈ armaAdmissibleParameters p q ∧
      ∀ b ∈ armaAdmissibleParameters p q,
        whittleObjective (fun t ↦ X t) n (βhat n ω) ω ≤
          whittleObjective (fun t ↦ X t) n b ω + ((n : ℝ) + 1)⁻¹ ^ 2) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ βhat n ω) atTop (𝓝 β)) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ 2 * Real.pi * whittleObjective (fun t ↦ X t) n (βhat n ω) ω)
        atTop (𝓝 σsq)) ∧
      TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (βhat n ω - β))
        (multivariateGaussian 0 (armaAsymptoticInformation β)⁻¹) := by
  sorry

end CKSD
