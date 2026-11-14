module

public import CKSD.Geometry.Persistence
public import Mathlib.Probability.StrongLaw


/-!
# Strong law for persistence landscapes

The strong law is a specialization of Mathlib's Banach-space strong law. A landscape is represented
as an element of `Lp` on counting measure times Lebesgue measure; the theorem applies to all random
`Lp` elements, and the geometric construction need not be repeated in its probabilistic proof.
The strong law covers the scope of GAPS_EASY 108.23; the identification of
`CKSD.persistenceLandscape` with an element of `CKSD.LandscapeLp p` is not formalized.

## Main definitions

* `CKSD.landscapeMeasure`: counting measure on levels times Lebesgue measure.
* `CKSD.LandscapeLp`: the Banach space `Lp` carrying landscapes.

## Main results

* `CKSD.LandscapeLp.ae_tendsto_sample_average`: the strong law (GAPS 108.23).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace CKSD

/-- Measure used for the `Lp` persistence landscape representation. -/
abbrev landscapeMeasure : Measure (ℕ × ℝ) := Measure.count.prod volume

/-- The Banach-space representation of persistence landscapes at exponent `p`. -/
abbrev LandscapeLp (p : ℝ≥0∞) := Lp ℝ p landscapeMeasure

/-- Borel measurable structure on the landscape Banach space. -/
local instance landscapeMeasurableSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MeasurableSpace (LandscapeLp p) := borel _

/-- The landscape measurable structure is its Borel structure. -/
local instance landscapeBorelSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BorelSpace (LandscapeLp p) := ⟨rfl⟩

/-- GAPS 108.23: strong law for integrable independent identically distributed landscapes: the
sample averages of pairwise independent, identically distributed, integrable random elements of
`LandscapeLp p` converge almost surely to the mean. Pairwise independence is sufficient, as in
Mathlib's Etemadi strong law. -/
theorem LandscapeLp.ae_tendsto_sample_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (X : ℕ → Ω → LandscapeLp p) (hint : Integrable (X 0) μ)
    (hind : Pairwise (fun i j ↦ IndepFun (X i) (X j) μ))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ sampleAverage X n ω) atTop (𝓝 (∫ ω, X 0 ω ∂μ)) :=
  ProbabilityTheory.strong_law_ae X hint hind hident

end CKSD
