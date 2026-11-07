module

public import CKSD.Learning.Algorithms

/-!
# Margin generalization and adversarial bandits

The finite-class margin bound uses measurable bounded scores. The Exp3 protocol specifies its
conditional action probabilities and importance-weighted cumulative losses, so the algorithmic
hypotheses do not assume a regret conclusion. Sources: GAPS 107.10 and 107.52.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Signed classification margin for Boolean labels, with `true` representing `+1`. -/
def signedMargin {H X : Type*} (f : H → X → ℝ) (h : H) (z : X × Bool) : ℝ :=
  if z.2 then f h z.1 else -f h z.1

/-- GAPS 107.10: uniform expected-Rademacher margin bound for a finite class. -/
theorem measure_margin_generalization_error_le {H X : Type*} [Fintype H] [Nonempty H]
    [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (f : H → X → ℝ) (hm : ∀ h, Measurable (f h)) (B : ℝ)
    (hb : ∀ h x, |f h x| ≤ B) (n : ℕ) (hn : 0 < n)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : δ ∈ Ioo 0 1) :
    let Pn := Measure.pi fun _ : Fin n ↦ P;
    let rad := ∫ x, empiricalRademacherComplexity n (signedMargin f) x ∂Pn;
    Pn.real {x | ∃ h,
      empiricalRisk (fun h z ↦ marginLoss ρ (signedMargin f h z)) h x +
        2 / ρ * rad + Real.sqrt (Real.log (1 / δ) / (2 * n)) <
          P.real {z | signedMargin f h z ≤ 0}} ≤ δ := by
  sorry

/-- Exp3 importance-weighted cumulative estimated loss. -/
def exp3EstimatedCumulativeLoss {Ω : Type*} {K : ℕ} (loss : ℕ → Fin K → ℝ)
    (p : ℕ → Ω → Fin K → ℝ) (A : ℕ → Ω → Fin K) (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range t, if A s ω = i then loss s i / p s ω i else 0

/-- GAPS 107.52: expected Exp3 regret against an oblivious loss sequence. -/
theorem exp3_expected_regret_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (K T : ℕ) (hK : 2 ≤ K) (hT : 0 < T)
    (loss : ℕ → Fin K → ℝ) (hloss : ∀ t i, loss t i ∈ Icc 0 1)
    (p : ℕ → Ω → Fin K → ℝ) (A : ℕ → Ω → Fin K)
    (hp : ∀ t, Measurable[F t] (p t)) (hA : ∀ t, Measurable[F (t + 1)] (A t))
    (hpos : ∀ t ω i, 0 < p t ω i) (hsum : ∀ t ω, ∑ i, p t ω i = 1)
    (hchoice : ∀ t i, P[(fun ω ↦ if A t ω = i then (1 : ℝ) else 0) | F t] =ᵐ[P]
      fun ω ↦ p t ω i)
    (hrec : ∀ t ω i,
      let η := Real.sqrt (2 * Real.log K / (T * K));
      p t ω i = Real.exp (-η * exp3EstimatedCumulativeLoss loss p A t i ω) /
        ∑ j, Real.exp (-η * exp3EstimatedCumulativeLoss loss p A t j ω)) (i : Fin K) :
    (∫ ω, ∑ t ∈ Finset.range T, loss t (A t ω) ∂P) - (∑ t ∈ Finset.range T, loss t i) ≤
      Real.sqrt (2 * T * K * Real.log K) := by
  sorry

end CKSD
