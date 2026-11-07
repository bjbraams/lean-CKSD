module

public import CKSD.Geometry.Entropic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Statistical entropic transport and Wasserstein barycenter gradients

Entropic and Wasserstein costs are TauCeti constructions. Empirical laws use the CKSD statistical
adapter. The barycenter differentiation statement is a directional derivative along a specified
square-integrable displacement; it does not claim the full Wasserstein Fréchet expansion.
Sources: GAPS 108.55 and 108.58.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

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

/-- GAPS 108.55: dimension-free mean-square and bias bounds for empirical entropic costs.
The entropic-map estimation bound is not asserted here. Constants may depend on `ε` only. -/
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

/-- Equal-weight Wasserstein barycenter energy, with the factor `1/2` normalization. -/
def wassersteinBarycenterEnergy {d k : ℕ}
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (P : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (∑ i, (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2) / (2 * k)

/-- Candidate barycenter gradient represented by residual optimal transport maps. -/
def wassersteinBarycenterGradient {d k : ℕ}
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x - (k : ℝ)⁻¹ • ∑ i, T i x

/-- Karcher equation for a specified collection of optimal transport maps. -/
def SatisfiesWassersteinKarcherEquation {d k : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  wassersteinBarycenterGradient T =ᵐ[P] 0

/-- Displacing a law by the vector field `v` for time `t`. -/
def displacementLaw {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) := P.map (fun x ↦ x + t • v x)

/-- GAPS 108.58, directional first variation of the equal-weight barycenter energy.
The source is absolutely continuous, and each supplied map is optimal with its stated target. -/
theorem hasDerivAt_wassersteinBarycenterEnergy_displacement {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP : P ≪ volume) (hP2 : MemLp id 2 P)
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (htarget : ∀ i, IsProbabilityMeasure (target i)) (h2 : ∀ i, MemLp id 2 (target i))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hlaw : ∀ i, P.map (T i) = target i)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2)
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hv : Measurable v) (hv2 : MemLp v 2 P) :
    HasDerivAt (fun t ↦ wassersteinBarycenterEnergy target (displacementLaw P v t))
      (∫ x, inner ℝ (wassersteinBarycenterGradient T x) (v x) ∂P) 0 := by
  sorry

/-- GAPS 108.58: an absolutely continuous minimizing barycenter satisfies the Karcher equation. -/
theorem satisfiesWassersteinKarcherEquation_of_minimizer {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP : P ≪ volume) (hP2 : MemLp id 2 P)
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (htarget : ∀ i, IsProbabilityMeasure (target i)) (h2 : ∀ i, MemLp id 2 (target i))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hlaw : ∀ i, P.map (T i) = target i)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2)
    (hmin : ∀ Q : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure Q → MemLp id 2 Q →
      wassersteinBarycenterEnergy target P ≤ wassersteinBarycenterEnergy target Q) :
    SatisfiesWassersteinKarcherEquation P T := by
  sorry

/-- The Karcher equation says exactly that the average optimal map is the identity almost surely. -/
theorem satisfiesWassersteinKarcherEquation_iff {d k : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    SatisfiesWassersteinKarcherEquation P T ↔
      ∀ᵐ x ∂P, (k : ℝ)⁻¹ • (∑ i, T i x) = x := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (sub_eq_zero.mp hx).symm
  · intro h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mpr hx.symm

end CKSD
