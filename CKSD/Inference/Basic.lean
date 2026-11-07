module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.StrongLaw
public import Mathlib.Tactic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Inference: definitions

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Weak convergence of finite Borel measures, tested against bounded continuous functions. -/
def TendstoWeakly {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ, Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- Convergence in law of a sequence of random variables on one probability space. -/
def TendstoInDistribution {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (ν : Measure E) : Prop :=
  TendstoWeakly (fun n ↦ μ.map (X n)) ν

/-- Convergence in probability to a constant; applications assume a probability measure. -/
def TendstoInProbabilityConst {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ μ.real {ω | ε < dist (X n ω) x}) atTop (𝓝 0)

/-- Uniform tightness in probability of a real sequence. -/
def IsBoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < |X n ω|} ≤ ε

/-- The empirical measure; the empty sample gives the zero measure. -/
def empiricalMeasure {E : Type*} [MeasurableSpace E] (n : ℕ) (x : Fin n → E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The empirical average of the first `n` observations of a sequence. -/
def sampleAverage {Ω E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- A measurable independent sequence with common law `P`. -/
def IsIndependentIdenticallyDistributed {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (P : Measure E) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧ ∀ i, μ.map (X i) = P

/-- The distribution function of a finite measure on the line. -/
def cdf (P : Measure ℝ) (t : ℝ) : ℝ := P.real (Iic t)

/-- A real density, with measurability and nonnegativity made explicit. -/
def HasDensity {X : Type*} [MeasurableSpace X]
    (P μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧ P = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

/-- Centered second moment, used only with the stated second-moment hypotheses. -/
def variance {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → ℝ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P

/-- Mathlib covariance with the measure-first statistical adapter used in this project. -/
abbrev covariance {X : Type*} [MeasurableSpace X]
    (P : Measure X) (f g : X → ℝ) : ℝ :=
  ProbabilityTheory.covariance f g P

/-- A real-valued randomized test. -/
def IsStatisticalTest {X : Type*} [MeasurableSpace X] (φ : X → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1

/-- Unbiasedness includes integrability under every parameter law. -/
def IsUnbiasedEstimator {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (δ : X → ℝ) (g : Θ → ℝ) : Prop :=
  Measurable δ ∧ ∀ θ, Integrable δ (P θ) ∧ (∫ x, δ x ∂P θ) = g θ

/-- Sufficiency: a single Markov kernel disintegrates every joint law of `(T,X)`. -/
def IsSufficientStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
    ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K

/-- Completeness of the family of laws of a statistic. -/
def IsCompleteStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g →
    (∀ θ, Integrable (g ∘ T) (P θ) ∧ (∫ x, g (T x) ∂P θ) = 0) →
    ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- Bounded completeness, with a global bound on the test function. -/
def IsBoundedlyCompleteStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g → (∃ C, ∀ s, |g s| ≤ C) →
    (∀ θ, (∫ x, g (T x) ∂P θ) = 0) → ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- The level and power comparison defining a uniformly most powerful test. -/
def IsUniformlyMostPowerfulTest {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    ∀ ψ, IsStatisticalTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- The uniformly most powerful unbiased property. -/
def IsUniformlyMostPowerfulUnbiasedTest {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    (∀ θ ∈ H₁, α ≤ ∫ x, φ x ∂P θ) ∧
    ∀ ψ, IsStatisticalTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      (∀ θ ∈ H₁, α ≤ ∫ x, ψ x ∂P θ) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- A randomized decision rule, using Mathlib's Markov kernels. -/
abbrev RandomizedDecisionRule (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] :=
  {K : Kernel X A // IsMarkovKernel K}

/-- Real risk, used below only for integrable or bounded losses. -/
def risk {Θ X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Θ → Measure X) (L : Θ → A → ℝ) (δ : RandomizedDecisionRule X A) (θ : Θ) : ℝ :=
  ∫ x, ∫ a, L θ a ∂δ.val x ∂P θ



end CKSD
