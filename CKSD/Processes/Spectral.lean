module

public import CKSD.Processes.Basic
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Spectral analysis of stationary processes

Periodogram and lag-window spectral estimation for linear processes, Kolmogorov's formula for
the one-step prediction error, Whittle estimation of ARMA parameters, and the random-phase
realization of a finite spectral measure as a stationary random field.

The periodogram of `X_0, …, X_{n-1}` is `I_n(x) = (2πn)⁻¹ |∑_t X_t e^{-itx}|²`, the
normalization under which `𝔼 I_n → f` for the spectral density `f`, with
`γ(h) = ∫ e^{ihx} f(x) dx`. Observations are indexed from zero. Lag-window estimators use the
mean-corrected sample autocovariances `sampleAutocovariance` with divisor `n`.

The prediction-error formula is stated for a centred weakly stationary sequence in a complex
inner-product space, the abstract form of a centred `L²` process; the one-step error from the
infinite past is the distance to the linear span of the past.

The ARMA polynomials are `φ(z) = 1 - ∑ φ_i z^i` and `θ(z) = 1 + ∑ θ_j z^j`, with the parameter
`β = (φ_1, …, φ_p, θ_1, …, θ_q)` indexed by `Fin p ⊕ Fin q`.

The random field `f(x) = √F(ℝᵈ) e^{i(⟨W, x⟩ + Φ)}` is built from a frequency `W` drawn from the
normalized spectral measure and an independent phase `Φ` uniform on `{0, π}`; its covariance is
the Fourier transform of `F`.

## Main definitions

* `CKSD.linearProcess`, `CKSD.transferFunction`, `CKSD.linearProcessSpectralDensity`.
* `CKSD.periodogram`, `CKSD.nearestFourierFrequency`, `CKSD.IsLagWindow`,
  `CKSD.lagWindowEstimator`.
* `CKSD.arPolynomial`, `CKSD.maPolynomial`, `CKSD.armaSpectralShape`,
  `CKSD.armaAdmissibleParameters`, `CKSD.whittleObjective`, `CKSD.armaAsymptoticInformation`.
* `CKSD.spectralRandomField`, `CKSD.twoPointPhaseLaw`, `CKSD.normalizedSpectralMeasure`.

## Main results

* `CKSD.tendstoInDistribution_periodogram_div_spectralDensity` and
  `CKSD.tendsto_lagWindowEstimator_moments` (GAPS 106.6).
* `CKSD.infDist_past_sq_eq_kolmogorov` (GAPS 106.16): Kolmogorov's (Szegő's) formula.
* `CKSD.tendsto_whittleEstimator` (GAPS 106.17).
* `CKSD.exists_stationary_field_of_spectral_measure` (GAPS 106.24): every finite spectral
  measure is the spectral measure of a mean-square continuous weakly stationary field.
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
innovations of finite positive variance. Positivity of the spectral density is needed only at
the fixed frequencies. The non-consistency corollary is not restated. -/
theorem tendstoInDistribution_periodogram_div_spectralDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℤ → Ω → ℝ) (σsq : ℝ)
    (hZ : IsIIDNoise μ Z σsq) (ψ : ℤ → ℝ) (hψ : Summable fun j ↦ |ψ j|)
    (m : ℕ) (x : Fin m → ℝ) (hx : StrictMono x) (hx0 : ∀ j, 0 < x j)
    (hxπ : ∀ j, x j < Real.pi) (hf : ∀ j, 0 < linearProcessSpectralDensity σsq ψ (x j)) :
    TendstoInDistribution μ (fun n ω ↦ WithLp.toLp 2 fun j : Fin m ↦
      periodogram (fun t ↦ linearProcess ψ Z t) n ω (nearestFourierFrequency n (x j)) /
        linearProcessSpectralDensity σsq ψ (x j))
      ((Measure.pi fun _ : Fin m ↦ expMeasure 1).map (WithLp.toLp 2)) := by
  sorry

/-- GAPS 106.6: asymptotic mean and variance, and mean-square consistency, of a lag-window
spectral estimator for a linear process with `∑ |ψ_j| |j|^{1/2} < ∞` and iid innovations with
finite fourth moment, when the truncation point `r` satisfies `r → ∞` and `r/n → 0`.
The window is assumed continuous at `0` (see `IsLagWindow`). The condition
`∑ |ψ_j| |j|^{1/2} < ∞` implies absolute summability of `ψ`, and positivity of the spectral
density is not needed. -/
theorem tendsto_lagWindowEstimator_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℤ → Ω → ℝ) (σsq : ℝ)
    (hZ : IsIIDNoise μ Z σsq) (h4 : MemLp (Z 0) 4 μ)
    (ψ : ℤ → ℝ) (hψ : Summable fun j : ℤ ↦ |ψ j| * Real.sqrt |(j : ℝ)|)
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
space, `⟪X s, X t⟫ = γ(t - s)` (`IsWeaklyStationary`), the spectral measure `F` lives on
`(-π, π]`, and `f` is the density of its absolutely continuous part. The value `0` is taken
exactly when `log f` fails to be integrable or `f` vanishes on a set of positive measure, i.e.
when `∫ log f = -∞`. -/
theorem infDist_past_sq_eq_kolmogorov {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (X : ℤ → H) (hstat : IsWeaklyStationary ℂ X)
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
theorem tendsto_whittleEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p q : ℕ} (Z : ℤ → Ω → ℝ) (σsq : ℝ)
    (hZ : IsIIDNoise μ Z σsq)
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

section RandomField

/-- The phase law of the random field, uniform on the two points `{0, π}`; its first circular
moment `𝔼 e^{iφ}` vanishes. -/
def twoPointPhaseLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac Real.pi)

/-- The two-point phase law is a probability measure. -/
instance : IsProbabilityMeasure twoPointPhaseLaw := by
  constructor
  simp only [twoPointPhaseLaw, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- The first circular moment of the two-point phase law vanishes. -/
theorem integral_exp_twoPointPhaseLaw :
    ∫ φ, Complex.exp ((φ : ℂ) * Complex.I) ∂twoPointPhaseLaw = 0 := by
  rw [twoPointPhaseLaw, integral_smul_measure, integral_add_measure]
  · simp [Complex.exp_pi_mul_I]
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

section Normalized

variable {E : Type*} [Zero E] [MeasurableSpace E]

/-- The spectral measure normalized to a probability measure, with the Dirac mass at the origin
for the zero measure. -/
def normalizedSpectralMeasure (F : Measure E) :
    Measure E :=
  if F univ = 0 then Measure.dirac 0 else (F univ)⁻¹ • F

/-- The normalized spectral measure is a probability measure. -/
instance (F : Measure E) [IsFiniteMeasure F] :
    IsProbabilityMeasure (normalizedSpectralMeasure F) := by
  unfold normalizedSpectralMeasure
  split_ifs with h
  · infer_instance
  · constructor
    simp [ENNReal.inv_mul_cancel h (measure_ne_top F univ)]

/-- Integrating against the spectral measure is the total mass times integrating against the
normalized spectral measure. -/
theorem real_mul_integral_normalizedSpectralMeasure
    (F : Measure E) [IsFiniteMeasure F]
    (g : E → ℂ) :
    (F.real univ : ℂ) * ∫ w, g w ∂normalizedSpectralMeasure F = ∫ w, g w ∂F := by
  unfold normalizedSpectralMeasure
  split_ifs with h
  · rw [Measure.measure_univ_eq_zero.1 h]; simp
  · rw [integral_smul_measure, Complex.real_smul, ← mul_assoc]
    have h' : (F univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h, measure_ne_top F univ⟩
    have : (F.real univ : ℂ) * ((F univ)⁻¹.toReal : ℂ) = 1 := by
      rw [ENNReal.toReal_inv, measureReal_def]
      push_cast
      exact div_self (by exact_mod_cast h')
    rw [this, one_mul]

end Normalized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The random-phase field `f(x)(w, φ) = √mass · e^{i(⟨w, x⟩ + φ)}` on a real inner-product space
`E`, as a function of a frequency `w` and a phase `φ`; with `mass` the total mass of a spectral
measure `F`, `w` drawn from `F` normalized and `φ` from `twoPointPhaseLaw`, its covariance is the
Fourier transform of `F`. -/
def spectralRandomField (mass : ℝ) (x : E)
    (ω : E × ℝ) : ℂ :=
  (Real.sqrt mass : ℂ) * Complex.exp ((inner ℝ ω.1 x + ω.2) * Complex.I)

/-- The random-phase field factors into a frequency part and a phase part. -/
theorem spectralRandomField_eq (m : ℝ) (x : E)
    (ω : E × ℝ) :
    spectralRandomField m x ω = (Real.sqrt m : ℂ) *
      (Complex.exp ((inner ℝ ω.1 x : ℝ) * Complex.I) * Complex.exp ((ω.2 : ℂ) * Complex.I)) := by
  rw [spectralRandomField, ← Complex.exp_add]
  congr 2
  ring

/-- The random-phase field has constant modulus `√mass`. -/
theorem norm_spectralRandomField (m : ℝ) (x : E)
    (ω : E × ℝ) :
    ‖spectralRandomField m x ω‖ = Real.sqrt m := by
  rw [spectralRandomField_eq, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- The random-phase field is jointly continuous in location and randomness. -/
theorem continuous_spectralRandomField (m : ℝ) :
    Continuous fun p : E × (E × ℝ) ↦
      spectralRandomField m p.1 p.2 := by
  unfold spectralRandomField
  fun_prop

/-- The product `f(x) f(y)^*` of the random-phase field depends only on the frequency and on
`x - y`. -/
theorem spectralRandomField_mul_star {m : ℝ} (hm : 0 ≤ m)
    (x y : E) (ω : E × ℝ) :
    spectralRandomField m x ω * star (spectralRandomField m y ω) =
      (m : ℂ) * Complex.exp ((inner ℝ ω.1 (x - y) : ℝ) * Complex.I) := by
  rw [spectralRandomField, spectralRandomField, Complex.star_def, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, map_mul, map_add, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    mul_mul_mul_comm, ← Complex.exp_add, ← Complex.ofReal_mul, Real.mul_self_sqrt hm,
    inner_sub_right]
  congr 2
  push_cast
  ring

/-- GAPS 106.24, realization part of Bochner's theorem for random fields: for a finite measure
`F` on a real inner-product space `E` there is a probability space carrying a square-integrable
centred complex field `f(x)`, `x ∈ E`, with covariance
`𝔼 f(x) f(y)^* = ∫ e^{i⟨w, x - y⟩} F(dw)` that is continuous in mean square. The mean-square
differentiability criterion and the Matérn family are not covered. -/
theorem exists_stationary_field_of_spectral_measure [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : Measure E) [IsFiniteMeasure F] :
    ∃ P : Measure (E × ℝ), IsProbabilityMeasure P ∧
      (∀ x, MemLp (spectralRandomField (F.real univ) x) 2 P) ∧
      (∀ x, (∫ ω, spectralRandomField (F.real univ) x ω ∂P) = 0) ∧
      (∀ x y, (∫ ω, spectralRandomField (F.real univ) x ω *
        star (spectralRandomField (F.real univ) y ω) ∂P) =
          ∫ w, Complex.exp ((inner ℝ w (x - y) : ℂ) * Complex.I) ∂F) ∧
      ∀ x, Tendsto (fun y ↦ ∫ ω, ‖spectralRandomField (F.real univ) y ω -
        spectralRandomField (F.real univ) x ω‖ ^ 2 ∂P) (𝓝 x) (𝓝 0) := by
  have hm : 0 ≤ F.real univ := measureReal_nonneg
  let P := (normalizedSpectralMeasure F).prod twoPointPhaseLaw
  have hcont : ∀ x, Continuous (spectralRandomField (E := E) (F.real univ) x) := fun x ↦ by
    unfold spectralRandomField; fun_prop
  refine ⟨P, inferInstance, fun x ↦ ?_, fun x ↦ ?_, fun x y ↦ ?_, fun x ↦ ?_⟩

  · exact MemLp.of_bound (hcont x).aestronglyMeasurable (Real.sqrt (F.real univ))
      (ae_of_all _ fun ω ↦ (norm_spectralRandomField _ x ω).le)
  · simp_rw [spectralRandomField_eq]
    rw [integral_const_mul]
    simp only [P]
    rw [integral_prod_mul (fun w ↦ Complex.exp ((inner ℝ w x : ℝ) * Complex.I))
      (fun φ : ℝ ↦ Complex.exp ((φ : ℂ) * Complex.I)), integral_exp_twoPointPhaseLaw]
    simp
  · simp_rw [spectralRandomField_mul_star hm]
    rw [integral_const_mul]
    simp only [P]
    rw [integral_fun_fst (fun w ↦ Complex.exp ((inner ℝ w (x - y) : ℝ) * Complex.I)),
      probReal_univ (μ := twoPointPhaseLaw), one_smul, real_mul_integral_normalizedSpectralMeasure]
  · have hlim : (0 : ℝ) = ∫ ω, ‖spectralRandomField (F.real univ) x ω -
        spectralRandomField (F.real univ) x ω‖ ^ 2 ∂P := by
      simp
    rw [hlim]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (2 * Real.sqrt (F.real univ)) ^ 2)
      (Eventually.of_forall fun y ↦ (((hcont y).sub (hcont x)).norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ ae_of_all _ fun ω ↦ ?_) (integrable_const _)
      (ae_of_all _ fun ω ↦ ?_)
    · rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      calc ‖spectralRandomField (F.real univ) y ω - spectralRandomField (F.real univ) x ω‖
          ≤ ‖spectralRandomField (F.real univ) y ω‖ +
              ‖spectralRandomField (F.real univ) x ω‖ := norm_sub_le _ _
        _ = 2 * Real.sqrt (F.real univ) := by
          rw [norm_spectralRandomField, norm_spectralRandomField]; ring
    · have : Continuous fun y ↦
          ‖spectralRandomField (F.real univ) y ω - spectralRandomField (F.real univ) x ω‖ ^ 2 := by
        unfold spectralRandomField; fun_prop
      exact this.tendsto x

end RandomField

end CKSD
