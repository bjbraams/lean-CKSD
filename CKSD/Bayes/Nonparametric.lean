module

public import CKSD.Bayes.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Random probability measures and posterior consistency

Vocabulary for Bayesian nonparametrics: Dirichlet processes through their finite-dimensional
partition laws, the Blackwell–MacQueen predictive law, stick breaking, posterior kernels given as
disintegrations, posterior consistency, and posterior contraction rates.

The finite-dimensional Dirichlet laws are those of TauCeti. Zero-parameter cells in a partition
are required to have random mass zero; the Dirichlet law is tested on positive-mass cells.
Posterior kernels are specified by disintegration, so statements apply to any chosen version.

## Main definitions

* `CKSD.IsDirichletProcess μ P α`: the random measure `P` is a Dirichlet process with base `α`.
* `CKSD.dirichletPosteriorBase`, `CKSD.polyaPredictiveLaw`: the posterior base `α + ∑ δ_{xᵢ}` and
  the predictive law `(α + ∑ δ_{xᵢ}) / (|α| + n)`.
* `CKSD.stickBreakingWeight`, `CKSD.stickBreakingMeasure`: Sethuraman's stick-breaking weights
  and random atomic measure.
* `CKSD.IsPosteriorKernel`, `CKSD.IsPosteriorConsistent`, `CKSD.HasPosteriorContractionRate`:
  posterior kernels, consistency, and contraction at a rate.

## Main results

* `CKSD.ae_isPosteriorConsistent_of_identifiable`: Doob's consistency theorem (GAPS 104.17).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Finite-dimensional partition characterization of a Dirichlet process.
`A` partitions a set of full base mass; this includes partitions with null cells after deleting
them. -/
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

/-- GAPS 104.17: Doob's consistency theorem. For an identifiable model (`P` injective) on standard
Borel spaces, any versions of the posteriors given the first `n` i.i.d. observations are
consistent at `π`-almost every parameter. -/
theorem ae_isPosteriorConsistent_of_identifiable
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    [TopologicalSpace Θ] [PolishSpace Θ] [BorelSpace Θ]
    [StandardBorelSpace X] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P]
    (hinj : Function.Injective P)
    (Q : ∀ n, Kernel Θ (Fin n → X))
    (hQ : ∀ n θ, Q n θ = Measure.pi (fun _ : Fin n ↦ P θ))
    (post : ∀ n, Kernel (Fin n → X) Θ)
    (hpost : ∀ n, IsPosteriorKernel π (Q n) (post n)) :
    ∀ᵐ θ ∂π, IsPosteriorConsistent (Measure.infinitePi (fun _ : ℕ ↦ P θ)) post θ := by
  sorry

/-- Second moment `∫ (log dP/dQ)² dP` of the log-likelihood ratio, used in the Kullback–Leibler
neighbourhoods of posterior contraction theory. -/
def logLikelihoodRatioSecondMoment {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.log ((P.rnDeriv Q x).toReal) ^ 2) ∂P

/-- Posterior contraction at the deterministic rate `ε` with respect to a loss `ρ` on parameters
(typically `ρ θ = d(θ, θ₀)` for a true parameter `θ₀`): there is `M₀ > 0` such that for every
`M ≥ M₀` the posterior mass `post n ω {θ | M εₙ ≤ ρ θ}` tends to zero in `μ`-probability. -/
def HasPosteriorContractionRate {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure Ω) (post : ℕ → Ω → Measure Θ) (ρ : Θ → ℝ) (ε : ℕ → ℝ) : Prop :=
  ∃ M₀ > 0, ∀ M ≥ M₀,
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (post n ω).real {θ | M * ε n ≤ ρ θ}) atTop (fun _ ↦ 0)

/-- The initial empty sample leaves the Dirichlet base measure unchanged. -/
@[simp] theorem dirichletPosteriorBase_empty {X : Type*} [MeasurableSpace X]
    (α : Measure X) (x : Fin 0 → X) : dirichletPosteriorBase α x = α := by
  simp [dirichletPosteriorBase]

/-- Zeroth stick-breaking weight. -/
@[simp] theorem stickBreakingWeight_zero (V : ℕ → ℝ) : stickBreakingWeight V 0 = V 0 := by
  simp [stickBreakingWeight]

end CKSD
