module

public import CKSD.Inference.Basic

/-!
# Models, testing, and decision criteria

Statistical models use Mathlib's Markov kernels and probability measures. Real risk is the
integrable-loss interface `CKSD.risk`; no new kernel or measure construction is introduced.
Sources: the conventions of Sections 101–108 of `GAPS.md` and `SYNOPSIS101.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CKSD

/-- A measurably parametrized statistical model, represented by a Markov kernel. -/
abbrev StatisticalModel (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] :=
  {P : Kernel Θ X // IsMarkovKernel P}

/-- An experiment without a measurable structure on the parameter space. -/
abbrev StatisticalExperiment (Θ X : Type*) [MeasurableSpace X] := Θ → ProbabilityMeasure X

/-- The law of an ancillary statistic is the same at every parameter value. -/
def IsAncillaryStatistic {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (P : Θ → Measure X) (T : X → S) : Prop :=
  Measurable T ∧ ∀ θ θ', (P θ).map T = (P θ').map T

/-- An unbiased estimator with uniformly minimum variance in the square-integrable class. -/
def IsMinimumVarianceUnbiasedEstimator {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (W : X → ℝ) (g : Θ → ℝ) : Prop :=
  IsUnbiasedEstimator P W g ∧ (∀ θ, MemLp W 2 (P θ)) ∧
    ∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) →
      ∀ θ, variance (P θ) W ≤ variance (P θ) W'

/-- Power at a parameter, for a real-valued randomized test. -/
def testPower {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (φ : X → ℝ) (θ : Θ) : ℝ := ∫ x, φ x ∂P θ

/-- Level of a test on a null parameter set, stated without a supremum of an empty set. -/
def HasTestLevel {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (H₀ : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ H₀, testPower P φ θ ≤ α

/-- Similarity means equality of power on the specified parameter set. -/
def IsSimilarTest {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (B : Set Θ) (α : ℝ) (φ : X → ℝ) : Prop :=
  IsStatisticalTest φ ∧ ∀ θ ∈ B, testPower P φ θ = α

/-- Coverage of a confidence set, represented by its membership relation. -/
def HasConfidenceCoverage {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (C : X → Set Θ) (α : ℝ) : Prop :=
  ∀ θ, MeasurableSet {x | θ ∈ C x} ∧ 1 - α ≤ (P θ).real {x | θ ∈ C x}

/-- A risk vector is admissible in a class if no risk vector dominates it strictly. -/
def IsAdmissibleRisk {Θ D : Type*} (R : D → Θ → ℝ) (δ : D) : Prop :=
  ¬ ∃ δ', (∀ θ, R δ' θ ≤ R δ θ) ∧ ∃ θ, R δ' θ < R δ θ

/-- A Bayes rule minimizes the integrated risk for the supplied finite prior. -/
def IsBayesRule {Θ D : Type*} [MeasurableSpace Θ]
    (R : D → Θ → ℝ) (π : Measure Θ) (δ : D) : Prop :=
  ∀ δ', (∫ θ, R δ θ ∂π) ≤ ∫ θ, R δ' θ ∂π

/-- A minimax rule minimizes worst-case risk. Applications require bounded risk vectors. -/
def IsMinimaxRule {Θ D : Type*} (R : D → Θ → ℝ) (δ : D) : Prop :=
  ∀ δ', (⨆ θ, R δ θ) ≤ ⨆ θ, R δ' θ

/-- An experiment is a garbling of another if a common Markov kernel produces its laws. -/
def IsGarbling {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y) : Prop :=
  ∃ K : Kernel X Y, IsMarkovKernel K ∧ ∀ θ, Q θ = K ∘ₘ P θ

/-- The scalar likelihood score for a real parameter at a specified observation. -/
def likelihoodScore {X : Type*} (f : ℝ → X → ℝ) (θ : ℝ) (x : X) : ℝ :=
  deriv (fun t ↦ Real.log (f t x)) θ

/-- Fisher information as the second score moment; regularity hypotheses belong to theorems. -/
def fisherInformation {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, likelihoodScore f θ x ^ 2 ∂P θ

/-- Information matrix for a specified vector score. -/
def fisherInformationMatrix {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure X) (score : X → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ ∫ x, score x i * score x j ∂P

/-- The full domain of Laplace integrability of a natural statistic. -/
def naturalParameterSpace {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) (T : X → EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {η | Integrable (fun x ↦ Real.exp (inner ℝ η (T x))) ν}

/-- Log partition function of a natural exponential family. -/
def logPartition {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) (T : X → EuclideanSpace ℝ (Fin d)) (η : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ x, Real.exp (inner ℝ η (T x)) ∂ν)

/-- A natural exponential law, used on `naturalParameterSpace` with a nonzero base measure. -/
def exponentialFamilyMeasure {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) (T : X → EuclideanSpace ℝ (Fin d)) (η : EuclideanSpace ℝ (Fin d)) : Measure X :=
  ν.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η (T x) - logPartition ν T η)))

/-- Minimality means that no nonzero linear functional of the statistic is almost surely constant. -/
def IsMinimalExponentialFamily {X : Type*} [MeasurableSpace X] {d : ℕ}
    (ν : Measure X) (T : X → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ, ¬ (∀ᵐ x ∂ν, inner ℝ u (T x) = c)

/-- A confidence set obtained by accepting the corresponding point-null test. -/
def confidenceSetOfTests {Θ X : Type*} (reject : Θ → Set X) (x : X) : Set Θ :=
  {θ | x ∉ reject θ}

/-- The elementary test/confidence-set duality, in probability rather than density form. -/
theorem hasConfidenceCoverage_confidenceSetOfTests {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (reject : Θ → Set X) (hm : ∀ θ, MeasurableSet (reject θ)) (α : ℝ)
    (hlevel : ∀ θ, (P θ).real (reject θ) ≤ α) :
    HasConfidenceCoverage P (confidenceSetOfTests reject) α := by
  intro θ
  let := hP θ
  refine ⟨(hm θ).compl, ?_⟩
  change 1 - α ≤ (P θ).real (reject θ)ᶜ
  rw [measureReal_compl (hm θ)]
  simpa using sub_le_sub_left (hlevel θ) 1

/-- Nonnegativity of the Fisher information. -/
theorem fisherInformation_nonneg {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) : 0 ≤ fisherInformation P f θ :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

/-- Every UMP test has the asserted level. -/
theorem IsUniformlyMostPowerfulTest.hasTestLevel {Θ X : Type*} [MeasurableSpace X]
    {P : Θ → Measure X} {H₀ H₁ : Set Θ} {α : ℝ} {φ : X → ℝ}
    (h : IsUniformlyMostPowerfulTest P H₀ H₁ α φ) : HasTestLevel P H₀ α φ :=
  ⟨h.1, h.2.1⟩

/-- Garbling is reflexive. -/
theorem isGarbling_refl {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X) :
    IsGarbling P P := by
  exact ⟨Kernel.id, inferInstance, fun _ ↦ Measure.id_comp.symm⟩

end CKSD
