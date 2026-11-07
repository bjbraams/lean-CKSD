module

public import CKSD.Inference.Basic
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Inference: conditional exponential families and conditional tests

Natural exponential families whose natural statistic splits as a pair `(T, S)`, the
conditional law of `T` given `S` (GAPS 101.43), and the conditional UMPU tests in the presence
of a nuisance parameter (GAPS 101.46).

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Conditional laws are expressed by Mathlib's measure-kernel composition `⊗ₘ` and conditional
sizes by Mathlib's conditional expectation. The docstrings specify the scope of each result;
`sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Log partition function of a natural exponential family whose natural statistic is the pair
`(T, S)`, with natural parameter `(η, ζ)`. -/
def splitLogPartition (ν : Measure X) (T : X → E) (S : X → F) (η : E) (ζ : F) : ℝ :=
  Real.log (∫ x, Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x)) ∂ν)

/-- The natural exponential law with density `exp(η·T + ζ·S - A(η, ζ))` with respect to the
base measure `ν`; it is a probability measure on the natural parameter space when `ν ≠ 0`. -/
def splitExponentialFamilyMeasure (ν : Measure X) (T : X → E) (S : X → F) (η : E) (ζ : F) :
    Measure X :=
  ν.withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x) - splitLogPartition ν T S η ζ)))

/-- The exponential tilt of a family of measures `ν_s` by the parameter `η`, normalized in each
fibre: the kernel `s ↦ exp(η·t - A_s(η)) ν_s(dt)` with `A_s(η) = log ∫ exp(η·t) ν_s(dt)`. -/
def conditionalExponentialKernel [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) : Kernel F E :=
  Kernel.withDensity κ (fun s t ↦ ENNReal.ofReal
    (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s))))

/-- GAPS 101.43: conditional exponential families. For a natural exponential family with natural
statistic `(T, S)` with values in Euclidean spaces, there is one s-finite kernel `s ↦ ν_s`, free of
the parameter, such that at every natural parameter `(η, ζ)` the joint law of `(S, T)` is the law
of `S` composed with the kernel `s ↦ exp(η·t - A_s(η)) ν_s(dt)`; that is, the conditional law of
`T` given `S = s` has this density for almost every `s`, and it is free of `ζ`. -/
theorem exists_kernel_conditional_exponential_family {k l : ℕ} (ν : Measure X)
    (T : X → EuclideanSpace ℝ (Fin k)) (S : X → EuclideanSpace ℝ (Fin l))
    (hT : Measurable T) (hS : Measurable S) :
    ∃ κ : Kernel (EuclideanSpace ℝ (Fin l)) (EuclideanSpace ℝ (Fin k)), ∃ _ : IsSFiniteKernel κ,
      ∀ η ζ, Integrable (fun x ↦ Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x))) ν →
        (splitExponentialFamilyMeasure ν T S η ζ).map (fun x ↦ (S x, T x)) =
          (splitExponentialFamilyMeasure ν T S η ζ).map S ⊗ₘ
            conditionalExponentialKernel κ η := by
  sorry

/-- Minimality of a split natural statistic `(T, S)` with real `T`: no nontrivial affine function
`a T + b·S` is almost everywhere constant under the base measure. -/
def IsMinimalSplitStatistic {l : ℕ} (ν : Measure X) (T : X → ℝ)
    (S : X → EuclideanSpace ℝ (Fin l)) : Prop :=
  ∀ (a : ℝ) (b : EuclideanSpace ℝ (Fin l)), (a, b) ≠ 0 → ∀ c : ℝ,
    ¬ (∀ᵐ x ∂ν, a * T x + inner ℝ b (S x) = c)

/-- GAPS 101.46, two-sided part: conditional tests with a nuisance parameter. In a minimal
exponential family with real natural statistic `T`, nuisance statistic `S`, and natural parameter
`(η, ζ)` ranging over an open convex set `U` on which the family is defined and which meets the
hyperplane `η = η₀`, a test that rejects for values of `T` outside the conditional interval
`[c₁(S), c₂(S)]`, accepts inside it, and has conditional size `α` and conditional first-moment
constraint `E[Tφ | S] = α E[T | S]` at one point of the hyperplane, is UMPU of level `α` for
`η = η₀` against `η ≠ η₀`. The randomization at the conditional critical points is
unrestricted. -/
theorem isUniformlyMostPowerfulUnbiasedTest_conditional_two_sided {l : ℕ} (ν : Measure X)
    (T : X → ℝ) (S : X → EuclideanSpace ℝ (Fin l)) (hT : Measurable T) (hS : Measurable S)
    (hmin : IsMinimalSplitStatistic ν T S)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin l))) (hU : IsOpen U) (hc : Convex ℝ U)
    (hint : ∀ θ ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ θ.1 (T x) + inner ℝ θ.2 (S x))) ν)
    (η₀ : ℝ) (θ₀ : U) (hθ₀ : θ₀.val.1 = η₀) (α : ℝ) (hα : α ∈ Ioo 0 1)
    (c₁ c₂ : EuclideanSpace ℝ (Fin l) → ℝ) (hcrit : ∀ s, c₁ s ≤ c₂ s)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (htail : ∀ x, (T x < c₁ (S x) ∨ c₂ (S x) < T x → φ x = 1) ∧
      (c₁ (S x) < T x ∧ T x < c₂ (S x) → φ x = 0)) :
    let P := fun θ : U ↦ splitExponentialFamilyMeasure ν T S θ.val.1 θ.val.2;
    (P θ₀)[φ | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun _ ↦ α) →
    (P θ₀)[fun x ↦ T x * φ x | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun x ↦ α * (P θ₀)[T | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] x) →
    IsUniformlyMostPowerfulUnbiasedTest P {θ | θ.val.1 = η₀} {θ | θ.val.1 ≠ η₀} α φ := by
  sorry

/-- GAPS 101.46, one-sided part: in the setting of
`isUniformlyMostPowerfulUnbiasedTest_conditional_two_sided`, a test that rejects for
`T > c(S)`, accepts for `T < c(S)`, and has conditional size `α` at one point of the hyperplane
`η = η₀` is UMPU of level `α` for `η ≤ η₀` against `η > η₀`. -/
theorem isUniformlyMostPowerfulUnbiasedTest_conditional_one_sided {l : ℕ} (ν : Measure X)
    (T : X → ℝ) (S : X → EuclideanSpace ℝ (Fin l)) (hT : Measurable T) (hS : Measurable S)
    (hmin : IsMinimalSplitStatistic ν T S)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin l))) (hU : IsOpen U) (hc : Convex ℝ U)
    (hint : ∀ θ ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ θ.1 (T x) + inner ℝ θ.2 (S x))) ν)
    (η₀ : ℝ) (θ₀ : U) (hθ₀ : θ₀.val.1 = η₀) (α : ℝ) (hα : α ∈ Ioo 0 1)
    (c : EuclideanSpace ℝ (Fin l) → ℝ) (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (htail : ∀ x, (c (S x) < T x → φ x = 1) ∧ (T x < c (S x) → φ x = 0)) :
    let P := fun θ : U ↦ splitExponentialFamilyMeasure ν T S θ.val.1 θ.val.2;
    (P θ₀)[φ | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun _ ↦ α) →
    IsUniformlyMostPowerfulUnbiasedTest P {θ | θ.val.1 ≤ η₀} {θ | η₀ < θ.val.1} α φ := by
  sorry

end CKSD
