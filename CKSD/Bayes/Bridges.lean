module

public import TauCeti.InformationTheory.KullbackLeibler.Projection

/-!
# Half-bridges and alternating marginal projections

The observations `start` and `finish` can be endpoint evaluations on a path space. Defining the
iteration on an arbitrary measurable space also covers its static endpoint coupling.
The entropy projection and its proofs are imported from TauCeti, without duplication.
Source: GAPS 104.77, in the scope of GAPS_EASY 104.77.
-/

@[expose] public section

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace CKSD

/-- Alternating terminal- and initial-law entropy projections, starting from `R`. -/
def bridgeIterate {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (R : Measure Ω) (start : Ω → X) (finish : Ω → Y)
    (μ : Measure X) (ν : Measure Y) : ℕ → Measure Ω
  | 0 => R
  | n + 1 => if Even n then (bridgeIterate R start finish μ ν n).fitLaw finish ν
      else (bridgeIterate R start finish μ ν n).fitLaw start μ

/-- The reference law is the zeroth iterate. -/
@[simp] theorem bridgeIterate_zero {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] (R : Measure Ω) (start : Ω → X)
    (finish : Ω → Y) (μ : Measure X) (ν : Measure Y) :
    bridgeIterate R start finish μ ν 0 = R := rfl

/-- GAPS 104.77: the half-bridge has the prescribed marginal, by TauCeti's entropy projection. -/
theorem map_half_bridge {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (R : Measure Ω) [IsFiniteMeasure R] (f : Ω → X) (hf : Measurable f)
    (μ : Measure X) [IsFiniteMeasure μ] (hac : μ ≪ R.map f) :
    (R.fitLaw f μ).map f = μ :=
  Measure.map_fitLaw_of_absolutelyContinuous hf hac

/-- GAPS 104.77: the half-bridge attains the marginal relative entropy, by TauCeti. -/
theorem klDiv_half_bridge {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (R : Measure Ω) [IsFiniteMeasure R] (f : Ω → X) (hf : Measurable f)
    (μ : Measure X) [IsFiniteMeasure μ] (hac : μ ≪ R.map f) :
    klDiv (R.fitLaw f μ) R = klDiv μ (R.map f) :=
  TauCeti.klDiv_fitLaw hf hac

/-- GAPS 104.77: finite-entropy uniqueness of the half-bridge, by TauCeti. -/
theorem eq_half_bridge_of_minimum_entropy {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (R σ : Measure Ω) [IsFiniteMeasure R] [IsFiniteMeasure σ]
    (f : Ω → X) (hf : Measurable f) (μ : Measure X) (hlaw : σ.map f = μ)
    (hmin : klDiv σ R ≤ klDiv (R.fitLaw f μ) R) (hfin : klDiv σ R ≠ ∞) :
    σ = R.fitLaw f μ :=
  TauCeti.eq_fitLaw_of_klDiv_le hf hlaw hmin hfin

/-- GAPS 104.77: the entropy Pythagorean identity for each step of the path-space iteration.
It holds for every feasible competitor, without assuming it minimizes entropy. -/
theorem klDiv_bridgeIterate_step {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] (R σ : Measure Ω) [IsFiniteMeasure σ]
    (start : Ω → X) (finish : Ω → Y) (hs : Measurable start) (hf : Measurable finish)
    (μ : Measure X) (ν : Measure Y) (hσs : σ.map start = μ) (hσf : σ.map finish = ν)
    (n : ℕ) [IsFiniteMeasure (bridgeIterate R start finish μ ν n)]
    (hac : σ ≪ bridgeIterate R start finish μ ν n) :
    klDiv σ (bridgeIterate R start finish μ ν n) =
      klDiv σ (bridgeIterate R start finish μ ν (n + 1)) +
        klDiv (bridgeIterate R start finish μ ν (n + 1)) (bridgeIterate R start finish μ ν n) := by
  have : IsFiniteMeasure μ := hσs ▸ (inferInstance : IsFiniteMeasure (σ.map start))
  have : IsFiniteMeasure ν := hσf ▸ (inferInstance : IsFiniteMeasure (σ.map finish))
  rw [bridgeIterate]
  split
  · rw [TauCeti.klDiv_fitLaw hf (hσf ▸ hac.map hf)]
    exact (TauCeti.klDiv_eq_klDiv_map_add_klDiv_fitLaw hf hσf).trans (add_comm _ _)
  · rw [TauCeti.klDiv_fitLaw hs (hσs ▸ hac.map hs)]
    exact (TauCeti.klDiv_eq_klDiv_map_add_klDiv_fitLaw hs hσs).trans (add_comm _ _)

end CKSD
