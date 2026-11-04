module

public import Mathlib
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Suggested statements for Section 101

Source: `GAPS.md`, Section 101; mathematical conventions: `SYNOPSIS101.md`;
library scope: `STRUCTURE101.md`. The Lake manifest fixes the library baseline.
Every theorem below is deliberately admitted. Definitions have explicit mathematical
content and contain no admissions. A docstring identifies the source and any narrower
scope; a theorem for one part of an entry does not represent the entire entry.

The shared definitions in namespace `CKSD` also support Sections 102–108.

Not represented: the uncountable-parameter version of 101.2; 101.13 (the complete
nonparametric model and permutation sigma-algebra), 101.21 (joint sorting and
rank laws), the full generality of 101.37 (risk sets closed only from below),
101.39 (infinite compact groups), 101.40 (improper-prior minimax theory),
101.42 (nonregular steep families), 101.43 (conditional exponential families),
101.46 (nuisance-parameter conditional tests), 101.50 and 101.53
(extended critical points and complete classes), 101.54 (least favorable
mixtures), 101.58 (Blyth's method), 101.60 (rank-deficient simultaneous bands),
101.62 (the comparison category of experiments). These need additional choices
of statistical framework beyond the concrete formulations below.

101.56 is omitted as stated: under scalar rescaling of a sample, Student's
statistic is not a maximal invariant (the sample direction retains information).
For 101.69 the natural parameter space is explicitly the full domain of
Laplace integrability; its openness is the regularity assumption in the synopsis.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Weak convergence of finite Borel measures, tested against bounded continuous functions. -/
def Weakly {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ, Tendsto (fun n ↦ ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

/-- Convergence in law of a sequence of random variables on one probability space. -/
def InLaw {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (ν : Measure E) : Prop :=
  Weakly (fun n ↦ μ.map (X n)) ν

/-- Convergence in probability to a constant; applications assume a probability measure. -/
def InProbability {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (x : E) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ μ.real {ω | ε < dist (X n ω) x}) atTop (𝓝 0)

/-- Uniform tightness in probability of a real sequence. -/
def BoundedInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < |X n ω|} ≤ ε

/-- The empirical measure; the empty sample gives the zero measure. -/
def empirical {E : Type*} [MeasurableSpace E] (n : ℕ) (x : Fin n → E) : Measure E :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

/-- The empirical average of the first `n` observations of a sequence. -/
def average {Ω E : Type*} [AddCommMonoid E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω

/-- A measurable independent sequence with common law `P`. -/
def IID {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
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

/-- Centered cross moment. -/
def covariance {X : Type*} [MeasurableSpace X]
    (P : Measure X) (f g : X → ℝ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂P) * (g x - ∫ y, g y ∂P) ∂P

/-- A real-valued randomized test. -/
def IsTest {X : Type*} [MeasurableSpace X] (φ : X → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Icc 0 1

/-- Unbiasedness includes integrability under every parameter law. -/
def Unbiased {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (δ : X → ℝ) (g : Θ → ℝ) : Prop :=
  Measurable δ ∧ ∀ θ, Integrable δ (P θ) ∧ (∫ x, δ x ∂P θ) = g θ

/-- Sufficiency: a single Markov kernel disintegrates every joint law of `(T,X)`. -/
def Sufficient {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∃ K : Kernel S X, IsMarkovKernel K ∧
    ∀ θ, (P θ).map (fun x ↦ (T x, x)) = (P θ).map T ⊗ₘ K

/-- Completeness of the family of laws of a statistic. -/
def Complete {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g →
    (∀ θ, Integrable (g ∘ T) (P θ) ∧ (∫ x, g (T x) ∂P θ) = 0) →
    ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- Bounded completeness, with a global bound on the test function. -/
def BoundedlyComplete {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  ∀ g : S → ℝ, Measurable g → (∃ C, ∀ s, |g s| ≤ C) →
    (∀ θ, (∫ x, g (T x) ∂P θ) = 0) → ∀ θ, ∀ᵐ x ∂P θ, g (T x) = 0

/-- The level and power comparison defining a uniformly most powerful test. -/
def UMP {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    ∀ ψ, IsTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- The uniformly most powerful unbiased property. -/
def UMPU {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X)
    (H₀ H₁ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsTest φ ∧ (∀ θ ∈ H₀, (∫ x, φ x ∂P θ) ≤ α) ∧
    (∀ θ ∈ H₁, α ≤ ∫ x, φ x ∂P θ) ∧
    ∀ ψ, IsTest ψ → (∀ θ ∈ H₀, (∫ x, ψ x ∂P θ) ≤ α) →
      (∀ θ ∈ H₁, α ≤ ∫ x, ψ x ∂P θ) →
      ∀ θ ∈ H₁, (∫ x, ψ x ∂P θ) ≤ ∫ x, φ x ∂P θ

/-- A randomized decision rule, using Mathlib's Markov kernels. -/
abbrev Rule (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] :=
  {K : Kernel X A // IsMarkovKernel K}

/-- Real risk, used below only for integrable or bounded losses. -/
def risk {Θ X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Θ → Measure X) (L : Θ → A → ℝ) (δ : Rule X A) (θ : Θ) : ℝ :=
  ∫ x, ∫ a, L θ a ∂δ.val x ∂P θ

namespace Section101

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.1: factorization on standard Borel sample and statistic spaces. -/
theorem gap101_1 [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace S]
    [Nonempty S] [Nonempty Θ] (P : Θ → Measure X) (μ : Measure X) [SigmaFinite μ]
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S) (hT : Measurable T) :
    Sufficient P T ↔ ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  sorry

/-- GAPS 101.4, convexity part: the multivariate Laplace-integrability domain is convex. -/
theorem gap101_4_convex {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Convex ℝ {η : EuclideanSpace ℝ (Fin d) |
      Integrable (fun t ↦ Real.exp (inner ℝ η t)) ν} := by
  sorry

/-- GAPS 101.5: completeness of a natural statistic over a nonempty open parameter set. -/
theorem gap101_5 {d : ℕ} (ν : Measure X) [SigmaFinite ν]
    (T : X → EuclideanSpace ℝ (Fin d)) (hT : Measurable T)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hne : U.Nonempty)
    (Z : EuclideanSpace ℝ (Fin d) → ℝ)
    (hZ : ∀ η ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ η (T x))) ν ∧
      Z η = ∫ x, Real.exp (inner ℝ η (T x)) ∂ν ∧ 0 < Z η) :
    Complete (fun η : U ↦ ν.withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η.val (T x)) / Z η.val))) T := by
  sorry

/-- GAPS 101.7: one parameter-independent Rao–Blackwell rule, with convex risk reduction. -/
theorem gap101_7 (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (hT : Sufficient P T) (δ : X → ℝ) (hδ : Measurable δ)
    (hint : ∀ θ, Integrable δ (P θ)) :
    ∃ r : S → ℝ, Measurable r ∧ ∀ θ,
      Integrable (r ∘ T) (P θ) ∧ (∫ x, r (T x) ∂P θ) = ∫ x, δ x ∂P θ ∧
      ∀ L : ℝ → ℝ, ConvexOn ℝ univ L →
        Integrable (fun x ↦ L (δ x)) (P θ) →
        Integrable (fun x ↦ L (r (T x))) (P θ) ∧
        (∫ x, L (r (T x)) ∂P θ) ≤ ∫ x, L (δ x) ∂P θ := by
  sorry

/-- GAPS 101.8, uniqueness part: unbiased functions of a complete statistic agree. -/
theorem gap101_8_unique (P : Θ → Measure X) (T : X → S) (hc : Complete P T)
    (a b : S → ℝ) (ha : Measurable a) (hb : Measurable b) (g : Θ → ℝ)
    (hua : Unbiased P (a ∘ T) g) (hub : Unbiased P (b ∘ T) g) :
    ∀ θ, ∀ᵐ x ∂P θ, a (T x) = b (T x) := by
  sorry

/-- GAPS 101.9: Basu's theorem. -/
theorem gap101_9 (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (A : X → V) (hA : Measurable A)
    (hs : Sufficient P T) (hc : BoundedlyComplete P T)
    (ha : ∀ θ θ', (P θ).map A = (P θ').map A) (θ : Θ) :
    IndepFun T A (P θ) := by
  sorry

/-- GAPS 101.10, scalar score-moment form of the information inequality.
The derivative-under-integral assumptions give the displayed cross-moment identity. -/
theorem gap101_10 (P : Measure X) [IsProbabilityMeasure P]
    (W score : X → ℝ) (hW : MemLp W 2 P) (hs : MemLp score 2 P)
    (hs0 : (∫ x, score x ∂P) = 0) (g' : ℝ)
    (hcross : (∫ x, (W x - ∫ y, W y ∂P) * score x ∂P) = g')
    (hI : 0 < ∫ x, score x ^ 2 ∂P) :
    g' ^ 2 / (∫ x, score x ^ 2 ∂P) ≤ variance P W := by
  sorry

/-- GAPS 101.12: covariance characterization of uniformly minimum variance unbiasedness. -/
theorem gap101_12 (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (W : X → ℝ) (g : Θ → ℝ) (hW : Unbiased P W g)
    (hW2 : ∀ θ, MemLp W 2 (P θ)) :
    (∀ W', Unbiased P W' g → (∀ θ, MemLp W' 2 (P θ)) →
      ∀ θ, variance (P θ) W ≤ variance (P θ) W') ↔
    (∀ U, Unbiased P U (fun _ ↦ 0) → (∀ θ, MemLp U 2 (P θ)) →
      ∀ θ, covariance (P θ) W U = 0) := by
  sorry

/-- GAPS 101.14: existence and optimality of a Neyman–Pearson test. -/
theorem gap101_14 (P₀ P₁ μ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (f₀ f₁ : X → ℝ)
    (h₀ : HasDensity P₀ μ f₀) (h₁ : HasDensity P₁ μ f₁)
    (α : ℝ) (hα : α ∈ Ioo 0 1) :
    ∃ k : ℝ, 0 ≤ k ∧ ∃ φ : X → ℝ, IsTest φ ∧
      (∫ x, φ x ∂P₀) = α ∧
      (∀ᵐ x ∂μ, (k * f₀ x < f₁ x → φ x = 1) ∧
        (f₁ x < k * f₀ x → φ x = 0)) ∧
      ∀ ψ, IsTest ψ → (∫ x, ψ x ∂P₀) ≤ α →
        (∫ x, ψ x ∂P₁) ≤ ∫ x, φ x ∂P₁ := by
  sorry

/-- GAPS 101.15: Karlin–Rubin for strictly positive densities on a common support.
This scope avoids the convention for ratios with zero denominator. -/
theorem gap101_15 (P : ℝ → Measure X) (μ : Measure X)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : ℝ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (hpos : ∀ θ x, 0 < f θ x)
    (T : X → ℝ) (hT : Measurable T)
    (hmlr : ∀ a b, a < b → ∃ r : ℝ → ℝ, Monotone r ∧
      ∀ x, f b x / f a x = r (T x))
    (θ₀ c γ α : ℝ) (hγ : γ ∈ Icc 0 1) (hα : α ∈ Ioo 0 1)
    (hsize : (∫ x, (if c < T x then 1 else if T x = c then γ else 0) ∂P θ₀) = α) :
    UMP P (Iic θ₀) (Ioi θ₀) α
      (fun x ↦ if c < T x then 1 else if T x = c then γ else 0) := by
  sorry

/-- GAPS 101.17: chi-squared residual law and independence from the sample mean. -/
theorem gap101_17 (n : ℕ) (hn : 2 ≤ n) (m : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    let P := Measure.pi (fun _ : Fin n ↦ gaussianReal m v);
    let mean := fun x : Fin n → ℝ ↦ (∑ i, x i) / n;
    let ss := fun x : Fin n → ℝ ↦ ∑ i, (x i - mean x) ^ 2;
    P.map (fun x ↦ ss x / v) = TauCeti.Probability.chiSquaredMeasure (n - 1 : ℕ) ∧
      IndepFun mean ss P ∧
      P.map (fun x ↦ Real.sqrt n * (mean x - m) /
        Real.sqrt (ss x / (n - 1 : ℕ))) = TauCeti.Probability.studentTMeasure (n - 1 : ℕ) := by
  sorry

/-- GAPS 101.32: finite statistical games have a saddle point in rules and priors. -/
theorem gap101_32 [Fintype Θ] [Nonempty Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ)) (L : Θ → A → ℝ) :
    ∃ δ : Rule X A, ∃ π : ProbabilityMeasure Θ,
      (∀ δ', (∫ θ, risk P L δ θ ∂(π : Measure Θ)) ≤
        ∫ θ, risk P L δ' θ ∂(π : Measure Θ)) ∧
      ∀ θ, risk P L δ θ ≤ ∫ θ', risk P L δ θ' ∂(π : Measure Θ) := by
  sorry

/-- GAPS 101.45: the two-tail exponential-family test satisfying the two moment constraints is UMPU. -/
theorem gap101_45 (μ : Measure X) (T h : X → ℝ) (hT : Measurable T)
    (hh : Measurable h) (hpos : ∀ x, 0 ≤ h x) (A : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hc : Convex ℝ U)
    (P : U → Measure X) (hP : ∀ η, IsProbabilityMeasure (P η))
    (hf : ∀ η, HasDensity (P η) μ (fun x ↦ h x * Real.exp (η.val * T x - A η.val)))
    (η₀ : U) (α c₁ c₂ : ℝ) (hα : α ∈ Ioo 0 1) (hcrit : c₁ < c₂)
    (φ : X → ℝ) (hφ : IsTest φ)
    (htail : ∀ x, (T x < c₁ ∨ c₂ < T x → φ x = 1) ∧
      (c₁ < T x ∧ T x < c₂ → φ x = 0))
    (hmom : Integrable T (P η₀) ∧ (∫ x, φ x ∂P η₀) = α ∧
      (∫ x, T x * φ x ∂P η₀) = α * ∫ x, T x ∂P η₀) :
    UMPU P {η₀} {η | η ≠ η₀} α φ := by
  sorry

/-- GAPS 101.47: generalized Neyman–Pearson comparison, with signed multipliers. -/
theorem gap101_47 {m : ℕ} (μ : Measure X) (f₀ : X → ℝ)
    (f : Fin m → X → ℝ) (k : Fin m → ℝ) (hf₀ : Integrable f₀ μ)
    (hf : ∀ i, Integrable (f i) μ) (φ ψ : X → ℝ)
    (hφ : IsTest φ) (hψ : IsTest ψ)
    (hthreshold : ∀ᵐ x ∂μ, ((∑ i, k i * f i x) < f₀ x → φ x = 1) ∧
      (f₀ x < (∑ i, k i * f i x) → φ x = 0))
    (hconstraints : ∀ i, k i * (∫ x, ψ x * f i x ∂μ) ≤
      k i * (∫ x, φ x * f i x ∂μ)) :
    (∫ x, ψ x * f₀ x ∂μ) ≤ ∫ x, φ x * f₀ x ∂μ := by
  sorry

/-- GAPS 101.49: similar tests have Neyman structure under bounded completeness. -/
theorem gap101_49 (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (hs : Sufficient P T) (hc : BoundedlyComplete P T)
    (φ : X → ℝ) (hφ : IsTest φ) (α : ℝ)
    (hsim : ∀ θ, (∫ x, φ x ∂P θ) = α) (θ : Θ) :
    (P θ)[φ | (inferInstance : MeasurableSpace S).comap T] =ᵐ[P θ] fun _ ↦ α := by
  sorry

/-- GAPS 101.55, algebraic part: invariant functions factor through a maximal invariant.
No measurability of the factor is asserted without a measurable quotient hypothesis. -/
theorem gap101_55 {G A B : Type*} [Group G] [MulAction G A] [Nonempty B]
    (M : A → B) (hM : ∀ (g : G) x, M (g • x) = M x)
    (hmax : ∀ x y, M x = M y → ∃ g : G, g • x = y) (f : A → ℝ) :
    (∀ (g : G) x, f (g • x) = f x) ↔ ∃ q : B → ℝ, f = q ∘ M := by
  sorry

/-- GAPS 101.57, strict James–Stein improvement in dimension at least three. -/
theorem gap101_57 {p : ℕ} (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p)) :
    let P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ);
    let δ := fun x : EuclideanSpace ℝ (Fin p) ↦ (1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x;
    (∫ x, ‖δ x - θ‖ ^ 2 ∂P) = (p : ℝ) - ((p : ℝ) - 2) ^ 2 *
      (∫ x, (‖x‖ ^ 2)⁻¹ ∂P) ∧ (∫ x, ‖δ x - θ‖ ^ 2 ∂P) < p := by
  sorry

/-- GAPS 101.64: Gaussian integration by parts, in the continuously differentiable scope. -/
theorem gap101_64 {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ContDiff ℝ 1 g) :
    let P := multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ));
    ∀ (hL2 : MemLp g 2 P),
    ∀ (hder : ∀ i, Integrable
      (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i) P),
    ∀ (i : Fin p),
    (∫ x, (x i - θ i) * g x i ∂P) =
      (v : ℝ) * ∫ x, (fderiv ℝ g x (EuclideanSpace.single i 1)) i ∂P := by
  sorry

/-- GAPS 101.69: existence and uniqueness of a regular natural-exponential-family maximum.
The domain is the full Laplace-integrability domain, not an arbitrary open
subset of it. The criterion is the per-observation log likelihood. -/
theorem gap101_69 {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    ∀ (hNne : N.Nonempty),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t : EuclideanSpace ℝ (Fin d)),
    (∃ eta ∈ N, ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta) ↔
      t ∈ interior (convexHull ℝ nu.support) := by
  sorry

/-- GAPS 101.69: a natural-family maximizer is unique and solves the mean equation. -/
theorem gap101_69_unique {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t eta : EuclideanSpace ℝ (Fin d)),
    ∀ (heta : eta ∈ N),
    ∀ (hmax : ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta),
    HasFDerivAt A (innerSL ℝ t) eta ∧
      ∀ zeta ∈ N, inner ℝ zeta t - A zeta = inner ℝ eta t - A eta → zeta = eta := by
  sorry

/-- GAPS 101.2, minimal likelihood-ratio statistic for a countable parameter family. -/
theorem gap101_2 [StandardBorelSpace X] [Nonempty X] [Countable Θ]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (mu : Measure X) [SigmaFinite mu] (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) mu (f θ)) (hpos : ∀ θ x, 0 < f θ x) (θ₀ : Θ) :
    let R := fun x θ ↦ f θ x / f θ₀ x;
    Sufficient P R ∧ ∀ T : X → S, Sufficient P T →
      ∃ phi : S → (Θ → ℝ), Measurable phi ∧ ∀ θ, R =ᵐ[P θ] phi ∘ T := by
  sorry

/-- GAPS 101.6: the monotone Pitman–Koopman–Darmois characterization. -/
theorem gap101_6 (P : Θ → Measure X) (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (heq : ∀ θ, P θ ≪ P₀ ∧ P₀ ≪ P θ)
    (N : Set ℕ) (hN : N.Infinite) (h1 : 1 ∈ N)
    (hmon : ∀ n ∈ N, ∃ T : (Fin n → X) → ℝ, Measurable T ∧
      ∀ θ, ∃ H : ℝ → ℝ, Monotone H ∧
        HasDensity (Measure.pi fun _ : Fin n ↦ P θ)
          (Measure.pi fun _ : Fin n ↦ P₀) (H ∘ T)) :
    ∃ T : X → ℝ, Measurable T ∧ ∀ θ, ∃ C > 0, ∃ a : ℝ,
      HasDensity (P θ) P₀ (fun x ↦ C * Real.exp (a * T x)) := by
  sorry

/-- GAPS 101.4, multivariate analyticity and first/second cumulant derivatives. -/
theorem gap101_4_moments {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d)))
    [SigmaFinite nu] (hne : nu ≠ 0) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    let P := fun eta ↦ nu.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ eta x - A eta)));
    AnalyticOnNhd ℝ A (interior N) ∧ ∀ eta ∈ interior N,
      HasFDerivAt A (innerSL ℝ (∫ x, x ∂P eta)) eta ∧
      ∀ u v : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (fderiv ℝ A) eta u v =
          covariance (P eta) (fun x ↦ inner ℝ u x) (fun x ↦ inner ℝ v x) := by
  sorry

/-- GAPS 101.37, the closed-convex-risk-set form of the finite complete-class theorem. -/
theorem gap101_37 {d : ℕ} (hd : 0 < d) (C : Set (Fin d → ℝ))
    (hc : Convex ℝ C) (hclosed : IsClosed C) (hb : ∃ b : Fin d → ℝ, ∀ x ∈ C, ∀ i, b i ≤ x i) :
    ∀ x ∈ C, ∃ y ∈ C, (∀ i, y i ≤ x i) ∧
      (¬ ∃ z ∈ C, (∀ i, z i ≤ y i) ∧ ∃ i, z i < y i) ∧
      ∃ w : Fin d → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        ∀ z ∈ C, (∑ i, w i * y i) ≤ ∑ i, w i * z i := by
  sorry

/-- GAPS 101.39, the compact-group averaging theorem for a finite group. -/
theorem gap101_39 {G A : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Θ] [MulAction G A] [MeasurableSpace A]
    (hX : ∀ g : G, Measurable (fun x : X ↦ g • x))
    (hA : ∀ g : G, Measurable (fun a : A ↦ g • a))
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (hmodel : ∀ (g : G) θ, (P θ).map (fun x ↦ g • x) = P (g • θ))
    (L : Θ → A → ℝ) (hm : ∀ θ, Measurable (L θ))
    (C : ℝ) (hb : ∀ θ a, |L θ a| ≤ C)
    (hloss : ∀ (g : G) θ a, L (g • θ) (g • a) = L θ a) (delta : Rule X A) :
    ∃ bar : Rule X A,
      (∀ (g : G) x, bar.val (g • x) = (bar.val x).map (fun a ↦ g • a)) ∧
      ∀ θ, risk P L bar θ = (∑ g : G, risk P L delta (g • θ)) / Fintype.card G := by
  sorry

/-- GAPS 101.42, the mean diffeomorphism in a minimal regular family.
An analytic inverse is stated on the open convex-support interior. -/
theorem gap101_42 {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    let mean := fun eta : EuclideanSpace ℝ (Fin d) ↦
      (∫ x, Real.exp (inner ℝ eta x) ∂nu)⁻¹ •
        (∫ x, Real.exp (inner ℝ eta x) • x ∂nu);
    let K := interior (convexHull ℝ nu.support);
    IsOpen N → N.Nonempty →
      ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        AnalyticOnNhd ℝ mean N ∧ AnalyticOnNhd ℝ g K ∧
        (∀ eta ∈ N, mean eta ∈ K ∧ g (mean eta) = eta) ∧
        ∀ m ∈ K, g m ∈ N ∧ mean (g m) = m := by
  sorry

end Section101
end CKSD
