module

public import CKSD.Processes.Basic
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Cox regression and Rebolledo's martingale central limit theorem

Counting processes are described pathwise: a counting path starts at `0`, is nondecreasing,
right-continuous and integer-valued with unit jumps. Stochastic integrals against counting
processes are the pathwise Lebesgue–Stieltjes sums `∫_(0,t] H dN = ∑_{s ≤ t} ΔN(s) H(s)`, and
compensators are pathwise Lebesgue integrals of predictable intensities. Time is `ℝ≥0`.

The Cox model is specified by a disintegration of the law of `(Z, T, C)`: given the covariate
`Z = z`, the failure and censoring times are independent and the failure time has conditional
survival function `exp(-Λ₀(t) e^{β·z})` on `[0, τ]`.

## Main definitions

* `CKSD.coxPartialLogLikelihood`: Cox's partial log-likelihood of a finite sample.
* `CKSD.coxRiskMean`, `CKSD.coxInformation`: the population risk-set average `ē(u)` and the
  information matrix `𝓘` of the Cox model.
* `CKSD.jumpIntegral`, `CKSD.IsCountingPath`, `CKSD.IsCountingProcessWithIntensity`,
  `CKSD.countingMartingaleTransform`: counting processes with intensities and their martingale
  transforms `∑_h ∫ H_{jh} (dN_h - λ_h ds)`.

## Main results

* `CKSD.tendsto_coxPartialLikelihoodMaximizer` (GAPS 106.30): consistency and asymptotic
  normality of the maximum partial-likelihood estimator.
* `CKSD.tendstoInDistribution_countingMartingaleTransform` (GAPS 106.34): Rebolledo's central
  limit theorem, in finite-dimensional form.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Cox's partial log-likelihood
`∑_{i : δ_i = 1} (β·z_i - log ∑_{j : t_j ≥ t_i} e^{β·z_j})` of a finite sample with observed
times `t_i`, failure indicators `δ_i` and covariates `z_i` in a real inner-product space, without
correction for tied failure times. -/
def coxPartialLogLikelihood {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (time : Fin n → ℝ) (event : Fin n → Bool) (z : Fin n → E) (β : E) : ℝ :=
  ∑ i, if event i then ⟪β, z i⟫ -
    Real.log (∑ j, if time i ≤ time j then Real.exp ⟪β, z j⟫ else 0) else 0

/-- The Cox partial log-likelihood of the first `n` observations `D i = (Z_i, T_i, C_i)`, with
observed times `min (T_i) (C_i)` and failures counted only when observed in `[0, τ]`. -/
def coxSampleLogLikelihood {Ω : Type*} {d : ℕ} (τ : ℝ)
    (D : ℕ → Ω → EuclideanSpace ℝ (Fin d) × ℝ × ℝ) (n : ℕ) (ω : Ω)
    (b : EuclideanSpace ℝ (Fin d)) : ℝ :=
  coxPartialLogLikelihood (fun i : Fin n ↦ min (D i ω).2.1 (D i ω).2.2)
    (fun i : Fin n ↦ decide ((D i ω).2.1 ≤ (D i ω).2.2 ∧ (D i ω).2.1 ≤ τ))
    (fun i : Fin n ↦ (D i ω).1) b

/-- The Cox risk-set average
`ē(u) = 𝔼[Y(u) Z e^{β·Z}] / 𝔼[Y(u) e^{β·Z}]`, with `Y(u) = 1{min(T,C) ≥ u}`, for a law of
`(Z, T, C)`. -/
def coxRiskMean {d : ℕ} (L : Measure (EuclideanSpace ℝ (Fin d) × ℝ × ℝ))
    (β : EuclideanSpace ℝ (Fin d)) (u : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (∫ a, (if u ≤ min a.2.1 a.2.2 then Real.exp ⟪β, a.1⟫ else 0) ∂L)⁻¹ •
    ∫ a, (if u ≤ min a.2.1 a.2.2 then Real.exp ⟪β, a.1⟫ else 0) • a.1 ∂L

/-- The Cox information `𝓘 = 𝔼 ∫_0^τ (Z - ē(u))^{⊗2} dN(u)`, with `N` jumping at an observed
failure `T ≤ C`. -/
def coxInformation {d : ℕ} (L : Measure (EuclideanSpace ℝ (Fin d) × ℝ × ℝ))
    (β : EuclideanSpace ℝ (Fin d)) (τ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j ↦ ∫ a, (if a.2.1 ≤ a.2.2 ∧ a.2.1 ≤ τ then
    (a.1 - coxRiskMean L β a.2.1) i * (a.1 - coxRiskMean L β a.2.1) j else 0) ∂L

/-- GAPS 106.30: consistency and asymptotic normality of the maximum partial-likelihood
estimator in the Cox model, with the partial likelihood restricted to failures in `[0, τ]`,
bounded covariates, conditionally independent censoring, `P(min(T,C) ≥ τ) > 0`, and positive
definite information. The estimator is any measurable choice that maximizes the partial
likelihood whenever a maximizer exists. The efficiency and log-rank interpretations are not
restated. -/
theorem tendsto_coxPartialLikelihoodMaximizer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (L : Measure (EuclideanSpace ℝ (Fin d) × ℝ × ℝ)) [IsProbabilityMeasure L]
    (D : ℕ → Ω → EuclideanSpace ℝ (Fin d) × ℝ × ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ D L)
    (B : ℝ) (hB : ∀ᵐ a ∂L, ‖a.1‖ ≤ B)
    (κT κC : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κT] [IsMarkovKernel κC]
    (hL : L = L.map Prod.fst ⊗ₘ (κT ×ₖ κC))
    (β : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (hτ : 0 < τ) (baseHazard : ℝ → ℝ)
    (hbase : ∀ t, 0 ≤ baseHazard t) (hbaseInt : IntegrableOn baseHazard (Icc 0 τ))
    (hhaz : ∀ᵐ z ∂(L.map Prod.fst), ∀ t ∈ Icc 0 τ,
      (κT z).real (Ioi t) = Real.exp (-(∫ s in (0 : ℝ)..t, baseHazard s) * Real.exp ⟪β, z⟫))
    (hrisk : 0 < L.real {a | τ ≤ min a.2.1 a.2.2})
    (hI : (coxInformation L β τ).PosDef)
    (βhat : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hmeas : ∀ n, Measurable (βhat n))
    (hmax : ∀ n ω, (∃ b, ∀ b', coxSampleLogLikelihood τ D n ω b' ≤
        coxSampleLogLikelihood τ D n ω b) →
      ∀ b', coxSampleLogLikelihood τ D n ω b' ≤ coxSampleLogLikelihood τ D n ω (βhat n ω)) :
    TendstoInProbabilityConst μ βhat β ∧
      TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (βhat n ω - β))
        (multivariateGaussian 0 (coxInformation L β τ)⁻¹) := by
  sorry

/-- The pathwise Lebesgue–Stieltjes integral `∫_(0,t] H dN = ∑_{0 < s ≤ t} ΔN(s) H(s)` of a
pure-jump path with finitely many jumps on `(0, t]`. -/
def jumpIntegral (N H : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∑ᶠ (s : ℝ≥0) (_ : s ∈ Ioc 0 t), (N s - Function.leftLim N s) * H s

/-- A counting path: starts at `0`, nondecreasing, right-continuous, integer-valued, with jumps
of size at most one. -/
def IsCountingPath (N : ℝ≥0 → ℝ) : Prop :=
  N 0 = 0 ∧ Monotone N ∧ (∀ t, ContinuousWithinAt N (Ici t) t) ∧
    (∀ t, ∃ m : ℕ, N t = m) ∧ ∀ t, N t - Function.leftLim N t ≤ 1

/-- A `k`-variate counting process without simultaneous jumps, with nonnegative predictable
locally integrable intensities `λ_h` for which `N_h - ∫_0^· λ_h` are martingales. -/
def IsCountingProcessWithIntensity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) {k : ℕ}
    (N intensity : Fin k → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ h ω, IsCountingPath fun t ↦ N h t ω) ∧
    (∀ ω t h h', h ≠ h' → N h t ω = Function.leftLim (fun s ↦ N h s ω) t ∨
      N h' t ω = Function.leftLim (fun s ↦ N h' s ω) t) ∧
    (∀ h, Measurable[F.predictable] fun q : ℝ≥0 × Ω ↦ intensity h q.1 q.2) ∧
    (∀ h t ω, 0 ≤ intensity h t ω) ∧
    (∀ h ω (t : ℝ), IntervalIntegrable (fun s : ℝ ↦ intensity h (Real.toNNReal s) ω) volume 0 t) ∧
    ∀ h, Martingale (fun t ω ↦ N h t ω -
      ∫ s in (0 : ℝ)..(t : ℝ), intensity h (Real.toNNReal s) ω) F μ

/-- The counting-process martingale transform
`M_j(t) = ∑_h ∫_0^t H_{jh} (dN_h - λ_h ds)`. -/
def countingMartingaleTransform {Ω : Type*} {k m : ℕ} (N intensity : Fin m → ℝ≥0 → Ω → ℝ)
    (H : Fin k → Fin m → ℝ≥0 → Ω → ℝ) (j : Fin k) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ h, (jumpIntegral (fun s ↦ N h s ω) (fun s ↦ H j h s ω) t -
    ∫ s in (0 : ℝ)..(t : ℝ), H j h (Real.toNNReal s) ω * intensity h (Real.toNNReal s) ω)

/-- GAPS 106.34: Rebolledo's central limit theorem for counting-process martingale transforms,
in finite-dimensional form: under convergence in probability of the predictable variations to a
continuous deterministic `V` and the Lindeberg condition,
the values of `M^{(n)}` at finitely many times in `[0, τ]` converge jointly in law to those of
the continuous Gaussian martingale with covariance `V(s ∧ t)`. Restrictions: the compensated
counting processes are martingales rather than local martingales, all processes live on one
probability space, and weak convergence in `D[0,τ]^k` is replaced by convergence of the
finite-dimensional distributions. The limit `V` automatically satisfies `V 0 = 0` and has
positive-semidefinite increments on `[0, τ]`, as a limit in probability of predictable
variations with these properties. -/
theorem tendstoInDistribution_countingMartingaleTransform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (kn : ℕ → ℕ)
    (F : ℕ → Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (N intensity : (n : ℕ) → Fin (kn n) → ℝ≥0 → Ω → ℝ)
    (hN : ∀ n, IsCountingProcessWithIntensity μ (F n) (N n) (intensity n))
    (H : (n : ℕ) → Fin k → Fin (kn n) → ℝ≥0 → Ω → ℝ)
    (hHpred : ∀ n j h, Measurable[(F n).predictable] fun q : ℝ≥0 × Ω ↦ H n j h q.1 q.2)
    (hHbdd : ∀ n j h ω (t : ℝ≥0), BddAbove ((fun s ↦ |H n j h s ω|) '' Iic t))
    (τ : ℝ≥0) (V : ℝ≥0 → Matrix (Fin k) (Fin k) ℝ) (hVc : ContinuousOn V (Iic τ))
    (hvar : ∀ t ≤ τ, ∀ j j', TendstoInProbabilityConst μ (fun n ω ↦ ∑ h,
      ∫ s in (0 : ℝ)..(t : ℝ), H n j h (Real.toNNReal s) ω * H n j' h (Real.toNNReal s) ω *
        intensity n h (Real.toNNReal s) ω) (V t j j'))
    (hlind : ∀ t ≤ τ, ∀ j, ∀ ε > 0, TendstoInProbabilityConst μ (fun n ω ↦ ∑ h,
      ∫ s in (0 : ℝ)..(t : ℝ), (if ε < |H n j h (Real.toNNReal s) ω| then
        H n j h (Real.toNNReal s) ω ^ 2 else 0) * intensity n h (Real.toNNReal s) ω) 0)
    (m : ℕ) (t : Fin m → ℝ≥0) (ht : ∀ i, t i ≤ τ) :
    TendstoInDistribution μ
      (fun n ω ↦ WithLp.toLp 2 fun a : Fin m × Fin k ↦
        countingMartingaleTransform (N n) (intensity n) (H n) a.2 (t a.1) ω)
      (multivariateGaussian 0 (Matrix.of fun a b : Fin m × Fin k ↦
        V (min (t a.1) (t b.1)) a.2 b.2)) := by
  sorry

end CKSD
