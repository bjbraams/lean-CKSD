module

public import CKSD.Bayes.Basic
public import CKSD.Inference.Model
public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Random probability measures and posterior consistency

The finite-dimensional Dirichlet laws are those of TauCeti. Zero-parameter cells in a partition
are required to have random mass zero; the Dirichlet law is tested on positive-mass cells.
Posterior kernels are specified by disintegration, so statements apply to any chosen version.
Sources: GAPS 104.15–104.19.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Finite-dimensional partition characterization of a Dirichlet process.
`A` partitions a set of full base mass; this includes partitions with null cells after deleting them. -/
def IsDirichletProcess {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (P : Ω → ProbabilityMeasure X) (α : Measure X) : Prop :=
  (∀ A, MeasurableSet A → Measurable (fun ω ↦ (P ω : Measure X) A)) ∧
    (∀ A, MeasurableSet A → α A = 0 → ∀ᵐ ω ∂μ, (P ω : Measure X) A = 0) ∧
    ∀ k : ℕ, 0 < k → ∀ A : Fin k → Set X,
      (∀ i, MeasurableSet (A i)) → Pairwise (Disjoint on A) →
      α (⋃ i, A i)ᶜ = 0 → (∀ i, 0 < α (A i)) →
      μ.map (fun ω ↦ WithLp.toLp 2 (fun i ↦ (P ω : Measure X).real (A i))) =
        TauCeti.Probability.dirichletMeasure (fun i ↦ α.real (A i))

/-- Posterior base measure after a finite sample from a Dirichlet process. -/
def dirichletPosteriorBase {X : Type*} [MeasurableSpace X] {n : ℕ}
    (α : Measure X) (x : Fin n → X) : Measure X := α + ∑ i, Measure.dirac (x i)

/-- Blackwell–MacQueen one-step predictive law. -/
def polyaPredictiveLaw {X : Type*} [MeasurableSpace X] {n : ℕ}
    (α : Measure X) (x : Fin n → X) : Measure X :=
  (α univ + n)⁻¹ • dirichletPosteriorBase α x

/-- Infinite stick-breaking weights in their size-biased order. -/
def stickBreakingWeight (V : ℕ → ℝ) (k : ℕ) : ℝ :=
  V k * ∏ j ∈ Finset.range k, (1 - V j)

/-- Random atomic measure associated to a sequence of atoms and stick-breaking fractions. -/
def stickBreakingMeasure {X : Type*} [MeasurableSpace X]
    (V : ℕ → ℝ) (θ : ℕ → X) : Measure X :=
  Measure.sum (fun k ↦ ENNReal.ofReal (stickBreakingWeight V k) • Measure.dirac (θ k))

/-- A chosen posterior kernel is a disintegration of the joint parameter-data law. -/
def IsPosteriorKernel {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) (P : Kernel Θ X) (post : Kernel X Θ) : Prop :=
  IsMarkovKernel post ∧
    (π ⊗ₘ P).map Prod.swap = (P ∘ₘ π) ⊗ₘ post

/-- Posterior consistency at a parameter, with data given as an infinite sequence. -/
def IsPosteriorConsistent {Θ X : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [MeasurableSpace X]
    (law : Measure (ℕ → X)) (post : ∀ n, Kernel (Fin n → X) Θ) (θ : Θ) : Prop :=
  ∀ U ∈ 𝓝 θ, ∀ᵐ x ∂law, Tendsto (fun n ↦ (post n (fun i ↦ x i.val)).real U) atTop (𝓝 1)

/-- GAPS 104.17: Doob consistency for any posterior versions based on finite prefixes.
The `n`th posterior is conditioned on exactly the first `n` observations. -/
theorem ae_isPosteriorConsistent_of_identifiable
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    [TopologicalSpace Θ] [PolishSpace Θ] [BorelSpace Θ]
    [StandardBorelSpace X] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P]
    (hinj : Function.Injective P)
    (Q : ∀ n, Kernel Θ (Fin n → X)) (hMarkov : ∀ n, IsMarkovKernel (Q n))
    (hQ : ∀ n θ, Q n θ = Measure.pi (fun _ : Fin n ↦ P θ))
    (post : ∀ n, Kernel (Fin n → X) Θ)
    (hpost : ∀ n, IsPosteriorKernel π (Q n) (post n)) :
    ∀ᵐ θ ∂π, IsPosteriorConsistent (Measure.infinitePi (fun _ : ℕ ↦ P θ)) post θ := by
  sorry

/-- Second log-likelihood-ratio moment, used in posterior contraction neighborhoods. -/
def logLikelihoodRatioSecondMoment {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.log ((P.rnDeriv Q x).toReal) ^ 2) ∂P

/-- Posterior contraction at a specified deterministic rate in a metric on parameters. -/
def HasPosteriorContractionRate {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [PseudoMetricSpace Θ] (μ : Measure Ω) (post : ℕ → Kernel Ω Θ)
    (θ₀ : Θ) (ε : ℕ → ℝ) : Prop :=
  ∃ M₀ > 0, ∀ M ≥ M₀,
    TendstoInProbabilityConst μ (fun n ω ↦ (post n ω).real {θ | M * ε n ≤ dist θ θ₀}) 0

/-- The initial empty sample leaves the Dirichlet base measure unchanged. -/
@[simp] theorem dirichletPosteriorBase_empty {X : Type*} [MeasurableSpace X]
    (α : Measure X) (x : Fin 0 → X) : dirichletPosteriorBase α x = α := by
  simp [dirichletPosteriorBase]

/-- Zeroth stick-breaking weight. -/
@[simp] theorem stickBreakingWeight_zero (V : ℕ → ℝ) : stickBreakingWeight V 0 = V 0 := by
  simp [stickBreakingWeight]

end CKSD
