module

public import CKSD.Geometry.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.SinkhornDivergence


/-!
# Real-valued entropic costs

A real cost bounded below is shifted by a specified lower bound before conversion to TauCeti's
nonnegative extended-real cost; the debiasing of the Sinkhorn divergence cancels the shift.

## Main definitions

* `CKSD.shiftedEntropicCost`: the nonnegative cost `c - lower`.
* `CKSD.realSinkhornDivergence`: the debiased Sinkhorn divergence of a real cost.

## Main results

* `CKSD.real_sinkhorn_divergence_independent_lower_bound`: the divergence does not depend on the
  lower bound (GAPS 108.44).
* `CKSD.real_sinkhorn_divergence_nonneg`: nonnegativity for a positive semidefinite continuous Gibbs
  kernel on a compact space (GAPS 108.44).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace CKSD

/-- A lower-bounded real transport cost represented in TauCeti's nonnegative cost convention. -/
def shiftedEntropicCost {X : Type*} (c : X × X → ℝ) (lower : ℝ) : X × X → ℝ≥0∞ :=
  fun z ↦ ENNReal.ofReal (c z - lower)

/-- Debiased Sinkhorn divergence of a real cost, computed after a nonnegative shift. -/
def realSinkhornDivergence {X : Type*} [MeasurableSpace X] (c : X × X → ℝ)
    (lower : ℝ) (ε : ℝ≥0) (P Q : Measure X) : ℝ :=
  TauCeti.sinkhornDivergence (shiftedEntropicCost c lower) ε P Q

/-- Lowering the shift by `b - a` raises every entropic cost by `b - a`. -/
theorem entropic_transport_cost_shifted_entropic_cost_eq_add
    {X : Type*} [MeasurableSpace X] (c : X × X → ℝ)
    (a b : ℝ) (hab : a ≤ b) (hb : ∀ z, b ≤ c z) (ε : ℝ≥0) (P Q : Measure X)
    [IsProbabilityMeasure P] :
    TauCeti.entropicTransportCost (shiftedEntropicCost c a) ε P Q =
      TauCeti.entropicTransportCost (shiftedEntropicCost c b) ε P Q + ENNReal.ofReal (b - a) := by
  have hpt : ∀ z, shiftedEntropicCost c a z =
      shiftedEntropicCost c b z + ENNReal.ofReal (b - a) := by
    intro z
    unfold shiftedEntropicCost
    rw [← ENNReal.ofReal_add (by linarith [hb z]) (by linarith)]
    congr 1
    ring
  rw [TauCeti.entropicTransportCost_def, TauCeti.entropicTransportCost_def, ENNReal.iInf_add]
  refine iInf_congr fun π ↦ ?_
  rw [ENNReal.iInf_add]
  refine iInf_congr fun hπ ↦ ?_
  have := hπ.isProbabilityMeasure
  simp_rw [hpt]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  ring

/-- Entropic costs of a bounded shifted cost between probability measures are finite. -/
theorem entropic_transport_cost_shifted_entropic_cost_ne_top
    {X : Type*} [MeasurableSpace X] (c : X × X → ℝ)
    (b C : ℝ) (hC : ∀ z, c z ≤ C) (ε : ℝ≥0) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    TauCeti.entropicTransportCost (shiftedEntropicCost c b) ε P Q ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ z, shiftedEntropicCost c b z ∂P.prod Q +
    ε * InformationTheory.klDiv (P.prod Q) (P.prod Q)) ?_ ?_
  · rw [InformationTheory.klDiv_self, mul_zero, add_zero]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (C - b) ∂P.prod Q) ?_ ?_
    · rw [lintegral_const]; simp
    · exact lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal (by linarith [hC z])
  · rw [TauCeti.entropicTransportCost_def]
    exact iInf₂_le (P.prod Q) (TauCeti.isCoupling_prod P Q)

/-- GAPS 108.44: the debiased divergence does not depend on the chosen valid lower bound. For a
bounded real cost `c` with lower bounds `a` and `b`, the shifted Sinkhorn divergences agree for
probability measures `P, Q`. -/
theorem real_sinkhorn_divergence_independent_lower_bound
    {X : Type*} [MeasurableSpace X] (c : X × X → ℝ)
    (a b C : ℝ) (ha : ∀ z, a ≤ c z) (hb : ∀ z, b ≤ c z) (hC : ∀ z, c z ≤ C)
    (ε : ℝ≥0) (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    realSinkhornDivergence c a ε P Q = realSinkhornDivergence c b ε P Q := by
  have key : ∀ a b : ℝ, a ≤ b → (∀ z, b ≤ c z) →
      realSinkhornDivergence c a ε P Q = realSinkhornDivergence c b ε P Q := by
    intro a b hab hb
    unfold realSinkhornDivergence
    rw [TauCeti.sinkhornDivergence_def, TauCeti.sinkhornDivergence_def,
      entropic_transport_cost_shifted_entropic_cost_eq_add c a b hab hb ε P Q,
      entropic_transport_cost_shifted_entropic_cost_eq_add c a b hab hb ε P P,
      entropic_transport_cost_shifted_entropic_cost_eq_add c a b hab hb ε Q Q,
      ENNReal.toReal_add (entropic_transport_cost_shifted_entropic_cost_ne_top c b C hC ε P Q)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (entropic_transport_cost_shifted_entropic_cost_ne_top c b C hC ε P P)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (entropic_transport_cost_shifted_entropic_cost_ne_top c b C hC ε Q Q)
        ENNReal.ofReal_ne_top]
    ring
  rcases le_total a b with h | h
  · exact key a b h hb
  · exact (key b a h ha).symm

/-- GAPS 108.44: nonnegativity of a shifted real-cost Sinkhorn divergence, using TauCeti: on a
compact space, if the shifted cost is bounded and its Gibbs kernel `exp(-c/ε)` is positive
semidefinite and continuous, then the divergence is nonnegative for all probability laws. -/
theorem real_sinkhorn_divergence_nonneg {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] (c : X × X → ℝ) (lower : ℝ)
    (hc : Measurable c) (C : ℝ≥0) (hbound : ∀ z, shiftedEntropicCost c lower z ≤ C)
    (ε : ℝ≥0) (hε : ε ≠ 0)
    (hpd : Matrix.PosSemidef (TauCeti.entropicGibbsKernel (shiftedEntropicCost c lower) ε))
    (hcont : Continuous (Function.uncurry
      (TauCeti.entropicGibbsKernel (shiftedEntropicCost c lower) ε)))
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ realSinkhornDivergence c lower ε P Q := by
  exact TauCeti.sinkhornDivergence_nonneg
    (by unfold shiftedEntropicCost; fun_prop) hbound hε hpd hcont

end CKSD
