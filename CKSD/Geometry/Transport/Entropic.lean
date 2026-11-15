module

import TauCeti.MeasureTheory.OptimalTransport.Entropic.SinkhornDivergence
public import CKSD.Inference.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality

/-!
# Real-valued entropic costs

A real cost bounded below is shifted by a specified lower bound before conversion to TauCeti's
nonnegative extended-real cost; the debiasing of the Sinkhorn divergence cancels the shift. The
quadratic entropic cost carries sample-complexity bounds for empirical laws, which use
`CKSD.empiricalMeasure`.

## Main definitions

* `CKSD.shiftedEntropicCost`: the nonnegative cost `c - lower`.
* `CKSD.realSinkhornDivergence`: the debiased Sinkhorn divergence of a real cost.
* `CKSD.quadraticEntropicCost`, `CKSD.quadraticEntropicTransport`: the squared Euclidean cost and
  the real-valued entropic transport cost.
* `CKSD.entropicBarycentricMap`: the barycentric projection of a quadratic Gibbs coupling.

## Main results

* `CKSD.realSinkhornDivergence_independent_lower_bound`: the divergence does not depend on the
  lower bound (GAPS 108.44).
* `CKSD.realSinkhornDivergence_nonneg`: nonnegativity for a positive semidefinite continuous Gibbs
  kernel on a compact space (GAPS 108.44).
* `CKSD.quadraticEntropicTransport_empirical_bounds`: dimension-free mean-square and bias bounds
  (GAPS 108.55).

## References

* S. Chewi, J. Niles-Weed, P. Rigollet, *Statistical optimal transport*, École d'Été de
  Probabilités de Saint-Flour XLIX (2019), Lecture Notes in Mathematics 2364, Springer, 2025.
  Theorem 4.9 is the dimension-free bound of GAPS 108.55.
* P. Rigollet, A. J. Stromme, *On the sample complexity of entropic optimal transport*, preprint,
  arXiv:2206.13472 (2022).
-/

public section

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
theorem entropicTransportCost_shiftedEntropicCost_eq_add
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
theorem entropicTransportCost_shiftedEntropicCost_ne_top
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
theorem realSinkhornDivergence_independent_lower_bound
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
      entropicTransportCost_shiftedEntropicCost_eq_add c a b hab hb ε P Q,
      entropicTransportCost_shiftedEntropicCost_eq_add c a b hab hb ε P P,
      entropicTransportCost_shiftedEntropicCost_eq_add c a b hab hb ε Q Q,
      ENNReal.toReal_add (entropicTransportCost_shiftedEntropicCost_ne_top c b C hC ε P Q)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (entropicTransportCost_shiftedEntropicCost_ne_top c b C hC ε P P)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (entropicTransportCost_shiftedEntropicCost_ne_top c b C hC ε Q Q)
        ENNReal.ofReal_ne_top]
    ring
  rcases le_total a b with h | h
  · exact key a b h hb
  · exact (key b a h ha).symm

/-- GAPS 108.44: nonnegativity of a shifted real-cost Sinkhorn divergence: on a compact space, if
the shifted cost is bounded and its Gibbs kernel `exp(-c/ε)` is positive semidefinite and
continuous, then the divergence is nonnegative for all probability laws. This is TauCeti's
`TauCeti.sinkhornDivergence_nonneg` applied to the shifted cost. -/
theorem realSinkhornDivergence_nonneg {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] (c : X × X → ℝ) (lower : ℝ)
    (hc : Measurable c) (C : ℝ≥0) (hbound : ∀ z, shiftedEntropicCost c lower z ≤ C)
    (ε : ℝ≥0) (hε : ε ≠ 0)
    (hpd : Matrix.PosSemidef (TauCeti.entropicGibbsKernel (shiftedEntropicCost c lower) ε))
    (hcont : Continuous (Function.uncurry
      (TauCeti.entropicGibbsKernel (shiftedEntropicCost c lower) ε)))
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ realSinkhornDivergence c lower ε P Q :=
  TauCeti.sinkhornDivergence_nonneg (by unfold shiftedEntropicCost; fun_prop) hbound hε hpd hcont

/-- Squared Euclidean cost in TauCeti's nonnegative extended-real convention. -/
def quadraticEntropicCost {d : ℕ} (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ := ENNReal.ofReal (‖z.1 - z.2‖ ^ 2)

/-- Real entropic quadratic transport cost, used where the bounded-support cost is finite. -/
def quadraticEntropicTransport {d : ℕ} (ε : ℝ≥0)
    (P Q : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (TauCeti.entropicTransportCost quadraticEntropicCost ε P Q).toReal

/-- Barycentric projection of a quadratic Gibbs coupling represented by a target dual potential.
The denominator is explicit; applications supply a positive finite normalization integral. -/
def entropicBarycentricMap {d : ℕ} (ε : ℝ)
    (Q : Measure (EuclideanSpace ℝ (Fin d))) (potential : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  let weight := fun y ↦ Real.exp ((potential y - ‖x - y‖ ^ 2) / ε)
  (∫ y, weight y ∂Q)⁻¹ • ∫ y, weight y • y ∂Q

/-- GAPS 108.55: dimension-free mean-square and bias bounds for empirical entropic costs. For
`ε > 0` there is `C > 0`, independent of the dimension, such that for laws `P, Q` on the ball of
radius `1/2` and `n ≥ 1` samples the empirical entropic cost `S_n` satisfies
`E (S_n - S)² ≤ C / n` and `|E S_n - S| ≤ C / n`. The entropic-map estimation bound is not
asserted here. Constants may depend on `ε` only. -/
theorem quadraticEntropicTransport_empirical_bounds (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ d : ℕ,
      ∀ P Q : Measure (EuclideanSpace ℝ (Fin d)),
      IsProbabilityMeasure P → IsProbabilityMeasure Q →
      P (Metric.closedBall 0 (1 / 2 : ℝ)) = 1 →
      Q (Metric.closedBall 0 (1 / 2 : ℝ)) = 1 → ∀ n : ℕ, 0 < n →
      let sampleLaw := Measure.pi fun _ : Fin n ↦ P.prod Q;
      let cost := fun z : Fin n → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        quadraticEntropicTransport ε (empiricalMeasure n (fun i ↦ (z i).1))
          (empiricalMeasure n (fun i ↦ (z i).2));
      (∫ z, (cost z - quadraticEntropicTransport ε P Q) ^ 2 ∂sampleLaw) ≤ C / n ∧
      |(∫ z, cost z ∂sampleLaw) - quadraticEntropicTransport ε P Q| ≤ C / n := by
  sorry

end CKSD
