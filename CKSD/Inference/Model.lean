module

public import CKSD.Inference.Basic

/-!
# Statistical models, tests, confidence sets, and decision criteria

Definitions of the classical criteria of Section 101: ancillarity, minimum-variance unbiased
estimation, level, similarity and power of tests, confidence coverage, admissible, Bayes, and
minimax rules, garblings of experiments, Fisher information, and natural exponential families.
Statistical models are families of measures or Mathlib Markov kernels.

## Main definitions

* `CKSD.StatisticalModel`, `CKSD.StatisticalExperiment`.
* `CKSD.IsAncillaryStatistic`, `CKSD.IsMinimumVarianceUnbiasedEstimator`.
* `CKSD.testPower`, `CKSD.HasTestLevel`, `CKSD.IsSimilarTest`, `CKSD.HasConfidenceCoverage`,
  `CKSD.confidenceSetOfTests`.
* `CKSD.IsAdmissibleRisk`, `CKSD.IsBayesRule`, `CKSD.IsMinimaxRule`, for a family `R δ` of real
  risk functions indexed by rules `δ`.
* `CKSD.IsGarbling P Q`: `Q` is obtained from `P` by one Markov kernel.
* `CKSD.likelihoodScore`, `CKSD.fisherInformation`, `CKSD.fisherInformationMatrix`.
* `CKSD.naturalParameterSpace`, `CKSD.logPartition`, `CKSD.exponentialFamilyMeasure`,
  `CKSD.IsMinimalExponentialFamily`, for a natural exponential family with base measure `ν` and
  statistic `T` with values in Euclidean space.

## Main results

* `CKSD.hasConfidenceCoverage_confidenceSetOfTests`: inverting level-`α` tests gives confidence
  sets of coverage `1 - α`.
* `CKSD.IsGarbling.refl`, `CKSD.IsUniformlyMostPowerfulTest.hasTestLevel`.

## Conventions

Bayes and minimax rules are defined so that junk values of Bochner integrals and of real
suprema play no role: a Bayes rule has integrable risk and is compared with rules with integrable
risk, and a minimax rule has bounded risk and is compared with rules with bounded risk.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CKSD

/-- A measurably parametrized statistical model: a Markov kernel from the parameter space to the
sample space. -/
abbrev StatisticalModel (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] :=
  {P : Kernel Θ X // IsMarkovKernel P}

/-- A statistical experiment: a probability law on the sample space for each parameter, with no
measurable structure on the parameter space. -/
abbrev StatisticalExperiment (Θ X : Type*) [MeasurableSpace X] := Θ → ProbabilityMeasure X

/-- An ancillary statistic: a measurable `T` whose law `(P θ).map T` does not depend on `θ`. -/
def IsAncillaryStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∀ θ θ', (P θ).map T = (P θ').map T

/-- A uniformly minimum variance unbiased estimator of `g`: `W` is a square-integrable unbiased
estimator of `g` and, at every `θ`, its variance is at most that of every square-integrable
unbiased estimator of `g`. -/
def IsMinimumVarianceUnbiasedEstimator {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (W : X → ℝ) (g : Θ → ℝ) : Prop :=
  IsUnbiasedEstimator P W g ∧ (∀ θ, MemLp W 2 (P θ)) ∧
    ∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) →
      ∀ θ, Var[W; P θ] ≤ Var[W'; P θ]

/-- The power `θ ↦ ∫ φ dP θ` of a randomized test `φ`. -/
def testPower {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) : ℝ := ∫ x, φ x ∂P θ

/-- `φ` is a test of level `α` for the null hypothesis `H₀`: its power is at most `α` at every
`θ ∈ H₀`. This is stated pointwise, so no supremum over a possibly empty `H₀` is taken. -/
def HasTestLevel {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (H₀ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ H₀, testPower P φ θ ≤ α

/-- `φ` is similar of size `α` on `B`: its power equals `α` at every `θ ∈ B` (typically the
boundary of the null hypothesis). -/
def IsSimilarTest {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (B : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ B, testPower P φ θ = α

/-- The confidence set `C` has coverage at least `1 - α`: for every `θ`, the event `θ ∈ C x` is
measurable and has `P θ`-probability at least `1 - α`. -/
def HasConfidenceCoverage {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (C : X → Set Θ) (α : ℝ) : Prop :=
  ∀ θ, MeasurableSet {x | θ ∈ C x} ∧ 1 - α ≤ (P θ).real {x | θ ∈ C x}

/-- `δ` is admissible in the class `D` of rules with risk functions `R`: no `δ'` has risk at most
that of `δ` everywhere and strictly smaller somewhere. -/
def IsAdmissibleRisk {Θ D : Type*} (R : D → Θ → ℝ) (δ : D) : Prop :=
  ¬ ∃ δ', (∀ θ, R δ' θ ≤ R δ θ) ∧ ∃ θ, R δ' θ < R δ θ

/-- `δ` is a Bayes rule for the prior (or weight measure) `π` in the class `D` of rules with risk
functions `R`: the risk of `δ` is `π`-integrable, and its integrated risk `∫ R δ dπ` is at most
that of every rule whose risk is `π`-integrable. -/
def IsBayesRule {Θ D : Type*} [MeasurableSpace Θ]
    (R : D → Θ → ℝ) (π : Measure Θ) (δ : D) : Prop :=
  Integrable (R δ) π ∧ ∀ δ', Integrable (R δ') π → (∫ θ, R δ θ ∂π) ≤ ∫ θ, R δ' θ ∂π

/-- `δ` is a minimax rule in the class `D` of rules with risk functions `R`: the risk of `δ` is
bounded above, and its maximal risk `⨆ θ, R δ θ` is at most that of every rule with risk bounded
above. Rules with unbounded risk have infinite maximal risk and are never better. -/
def IsMinimaxRule {Θ D : Type*} (R : D → Θ → ℝ) (δ : D) : Prop :=
  BddAbove (range (R δ)) ∧
    ∀ δ', BddAbove (range (R δ')) → (⨆ θ, R δ θ) ≤ ⨆ θ, R δ' θ

/-- The experiment `Q` is a garbling of `P`: one Markov kernel `K` maps every `P θ` to `Q θ`,
`Q θ = K ∘ₘ P θ`. -/
def IsGarbling {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y) : Prop :=
  ∃ K : Kernel X Y, IsMarkovKernel K ∧ ∀ θ, Q θ = K ∘ₘ P θ

/-- The score `∂/∂θ log f(θ, x)` of a likelihood `f` in a real parameter `θ`. -/
def likelihoodScore {X : Type*} (f : ℝ → X → ℝ) (θ : ℝ) (x : X) : ℝ :=
  deriv (fun t ↦ Real.log (f t x)) θ

/-- The Fisher information `I(θ) = ∫ (∂/∂θ log f(θ, x)) ^ 2 dP θ(x)` of a real-parameter model,
as the second moment of the score; regularity hypotheses belong to the theorems using it. -/
def fisherInformation {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, likelihoodScore f θ x ^ 2 ∂P θ

/-- The information matrix `(∫ sᵢ sⱼ dP)ᵢⱼ` of a vector score `s`. -/
def fisherInformationMatrix {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure X) (score : X → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ ∫ x, score x i * score x j ∂P

/-- The natural parameter space `{η | ∫ exp ⟪η, T⟫ dν < ∞}` of the natural exponential family
with base measure `ν` and statistic `T`. -/
def naturalParameterSpace {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (ν : Measure X) (T : X → E) : Set E :=
  {η | Integrable (fun x ↦ Real.exp (inner ℝ η (T x))) ν}

/-- The log partition function `η ↦ log ∫ exp ⟪η, T⟫ dν` of a natural exponential family. -/
def logPartition {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (ν : Measure X) (T : X → E) (η : E) : ℝ :=
  Real.log (∫ x, Real.exp (inner ℝ η (T x)) ∂ν)

/-- The law `exp (⟪η, T⟫ - logPartition ν T η) · ν` of the natural exponential family at `η`;
it is a probability measure for `η` in `naturalParameterSpace ν T` when `ν ≠ 0`. -/
def exponentialFamilyMeasure {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (ν : Measure X) (T : X → E) (η : E) : Measure X :=
  ν.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η (T x) - logPartition ν T η)))

/-- A minimal natural exponential family: no nonzero linear functional `⟪u, T⟫` of the statistic
is `ν`-almost everywhere constant. -/
def IsMinimalExponentialFamily {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (ν : Measure X) (T : X → E) : Prop :=
  ∀ u : E, u ≠ 0 → ∀ c : ℝ, ¬ (∀ᵐ x ∂ν, inner ℝ u (T x) = c)

/-- The confidence set obtained by inverting tests: `θ` is in the set at `x` iff the test of the
point null hypothesis `θ` does not reject at `x`. -/
def confidenceSetOfTests {Θ X : Type*} (reject : Θ → Set X) (x : X) : Set Θ :=
  {θ | x ∉ reject θ}

/-- Test/confidence-set duality: inverting level-`α` tests with measurable rejection regions
gives confidence sets with coverage at least `1 - α`. -/
theorem hasConfidenceCoverage_confidenceSetOfTests {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (reject : Θ → Set X) (hm : ∀ θ, MeasurableSet (reject θ)) (α : ℝ)
    (hlevel : ∀ θ, (P θ).real (reject θ) ≤ α) :
    HasConfidenceCoverage P (confidenceSetOfTests reject) α := by
  intro θ
  refine ⟨(hm θ).compl, ?_⟩
  change 1 - α ≤ (P θ).real (reject θ)ᶜ
  rw [measureReal_compl (hm θ)]
  simpa using sub_le_sub_left (hlevel θ) 1

/-- The Fisher information is nonnegative. -/
theorem fisherInformation_nonneg {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) : 0 ≤ fisherInformation P f θ :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

/-- A uniformly most powerful level-`α` test has level `α`. -/
theorem IsUniformlyMostPowerfulTest.hasTestLevel {Θ X : Type*} [MeasurableSpace X]
    {P : Θ → Measure X} {H₀ H₁ : Set Θ} {α : ℝ} {φ : X → ℝ}
    (h : IsUniformlyMostPowerfulTest P H₀ H₁ α φ) : HasTestLevel P H₀ α φ :=
  ⟨h.1, h.2.1⟩

/-- Every experiment is a garbling of itself, by the identity kernel. -/
theorem IsGarbling.refl {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X) :
    IsGarbling P P := by
  exact ⟨Kernel.id, inferInstance, fun _ ↦ Measure.id_comp.symm⟩

end CKSD
