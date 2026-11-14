module

public import TauCeti.InformationTheory.KullbackLeibler.Projection


/-!
# Half-bridges and alternating marginal projections

The half-bridge of a reference law `R` with prescribed law `μ` of an observation `f` is TauCeti's
entropy projection `R.fitLaw f μ`. TauCeti proves that it has law `μ` under `f`
(`Measure.map_fitLaw_of_absolutelyContinuous`), that its relative entropy to `R` is
`KL(μ ‖ R ∘ f⁻¹)` (`TauCeti.klDiv_fitLaw`), and that it is the unique finite-entropy minimizer
(`TauCeti.eq_fitLaw_of_klDiv_le`). This file defines the alternating iteration of these
projections. The observations `start` and `finish` can be the endpoint evaluations on a path
space; on an arbitrary measurable space the same definition also covers the static endpoint
coupling.

## Main definitions

* `CKSD.bridgeIterate R start finish μ ν`: the iterates of iterative proportional fitting,
  alternately fitting the law `ν` of `finish` and the law `μ` of `start`, starting from `R`.

## Main results

* `CKSD.kl_div_bridge_iterate_step`: the entropy Pythagorean identity
  `KL(σ ‖ Pⁿ) = KL(σ ‖ Pⁿ⁺¹) + KL(Pⁿ⁺¹ ‖ Pⁿ)` for every law `σ` with both marginals.

Source: GAPS 104.77, in the scope of GAPS_EASY 104.77.
-/

@[expose] public section

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace CKSD

/-- Iterative proportional fitting from `R`: odd iterates fit the law `ν` of `finish`, even
iterates of positive index fit the law `μ` of `start`. -/
def bridgeIterate {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (R : Measure Ω) (start : Ω → X) (finish : Ω → Y)
    (μ : Measure X) (ν : Measure Y) : ℕ → Measure Ω
  | 0 => R
  | n + 1 => if Even n then (bridgeIterate R start finish μ ν n).fitLaw finish ν
      else (bridgeIterate R start finish μ ν n).fitLaw start μ

/-- The reference law is the zeroth iterate. -/
@[simp] theorem bridge_iterate_zero {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] (R : Measure Ω) (start : Ω → X)
    (finish : Ω → Y) (μ : Measure X) (ν : Measure Y) :
    bridgeIterate R start finish μ ν 0 = R := rfl

/-- GAPS 104.77: the entropy Pythagorean identity for each step of the path-space iteration.
It holds for every feasible competitor, without assuming it minimizes entropy. -/
theorem kl_div_bridge_iterate_step {Ω X Y : Type*} [MeasurableSpace Ω]
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
