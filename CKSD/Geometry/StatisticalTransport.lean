module

public import CKSD.Geometry.Entropic
import CKSD.Geometry.TransportFirstVariation
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
public import CKSD.Geometry.Transport
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic


/-!
# Statistical entropic transport and Wasserstein barycenter gradients

Sample-complexity bounds for empirical entropic transport costs, and the first-order theory of the
equal-weight Wasserstein barycenter energy. Entropic and Wasserstein costs are TauCeti
constructions; empirical laws use `CKSD.empiricalMeasure`.

## Main definitions

* `CKSD.quadraticEntropicCost`, `CKSD.quadraticEntropicTransport`: the squared Euclidean cost and
  the real-valued entropic transport cost.
* `CKSD.entropicBarycentricMap`: the barycentric projection of a quadratic Gibbs coupling.
* `CKSD.SatisfiesWassersteinKarcherEquation`: the Karcher (first-order) equation for a barycenter.
* `CKSD.displacementLaw`: the law displaced along a vector field.

## Main results

* `CKSD.quadratic_entropic_transport_empirical_bounds`: dimension-free mean-square and bias bounds
  (GAPS 108.55).
* `CKSD.has_deriv_at_wasserstein_barycenter_energy_displacement`: the directional first variation of
  the barycenter energy (GAPS 108.58). It is a directional derivative along a specified
  square-integrable displacement, not the full Wasserstein Fréchet expansion.
* `CKSD.satisfies_wasserstein_karcher_equation_of_minimizer`: minimizers satisfy the Karcher equation
  (GAPS 108.58).
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

/-- GAPS 108.55: dimension-free mean-square and bias bounds for empirical entropic costs. For
`ε > 0` there is `C > 0`, independent of the dimension, such that for laws `P, Q` on the ball of
radius `1/2` and `n ≥ 1` samples the empirical entropic cost `S_n` satisfies
`E (S_n - S)² ≤ C / n` and `|E S_n - S| ≤ C / n`. The entropic-map estimation bound is not
asserted here. Constants may depend on `ε` only. -/
theorem quadratic_entropic_transport_empirical_bounds (ε : ℝ≥0) (hε : 0 < ε) :
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

/-- Karcher equation for a specified collection of optimal transport maps. -/
def SatisfiesWassersteinKarcherEquation {d k : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  wassersteinBarycenterGradient T =ᵐ[P] 0

/-- Displacing a law by the vector field `v` for time `t`. -/
def displacementLaw {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) := P.map (fun x ↦ x + t • v x)

/-- Finite sums of quadratic transport first variations give the equal - weight barycenter
  derivative. -/
theorem barycenter_derivative_of_component_derivatives {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP2 : MemLp id 2 P)
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT2 : ∀ i, MemLp (T i) 2 P)
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hv2 : MemLp v 2 P)
    (hder : ∀ i, HasDerivAt (fun t : ℝ ↦
        (TauCeti.wassersteinEDist 2 (P.map fun x ↦ x + t • v x) (target i)).toReal ^ 2)
      (2*∫ x, inner ℝ (x - T i x) (v x) ∂P) 0) :
    HasDerivAt (fun t ↦ wassersteinBarycenterEnergy target (displacementLaw P v t))
      (∫ x, inner ℝ (wassersteinBarycenterGradient T x) (v x) ∂P) 0 := by
  have hd := (HasDerivAt.sum (u := Finset.univ) (fun i _ ↦ hder i)).div_const (2 * (k:ℝ))
  have hi (i : Fin k) : Integrable (fun x ↦ inner ℝ (x - T i x) (v x)) P := by
    have hsub : MemLp (fun x ↦ x - T i x) 2 P := hP2.sub (hT2 i)
    refine ((hsub.integrable_norm_pow two_ne_zero).add
      (hv2.integrable_norm_pow two_ne_zero)).mono'
        (hsub.aestronglyMeasurable.inner hv2.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have hinner := abs_real_inner_le_norm (x - T i x) (v x)
    nlinarith [sq_nonneg (‖x - T i x‖-‖v x‖)]
  have he : (∑i : Fin k, 2*∫ x, inner ℝ (x - T i x) (v x) ∂P) / (2 * (k:ℝ)) =
      ∫ x, inner ℝ (wassersteinBarycenterGradient T x) (v x) ∂P := by
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ ↦ hi i)]
    have he (x : EuclideanSpace ℝ (Fin d)) :
        ∑i : Fin k, inner ℝ (x - T i x) (v x) =
          (k:ℝ) * inner ℝ (wassersteinBarycenterGradient T x) (v x) := by
      simp only [inner_sub_left, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, wassersteinBarycenterGradient, real_inner_smul_left,
        sum_inner]
      field_simp
    simp_rw [he]
    rw [integral_const_mul]
    have hk0 : (k:ℝ)≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  rw [he] at hd
  simpa only [wassersteinBarycenterEnergy, displacementLaw, Finset.sum_apply] using hd

/-- GAPS 108.58, directional first variation of the equal-weight barycenter energy. For an
absolutely continuous law `P` with finite second moment and square-integrable maps `T_i` that are
optimal from `P` to the targets, the energy along the displacement `x ↦ x + t v(x)` has derivative
`∫ ⟨x - k⁻¹ ∑ T_i x, v x⟩ dP` at `t = 0`. The targets are probability laws with finite second
moment because they are the images `(T_i)_# P`. -/
theorem has_deriv_at_wasserstein_barycenter_energy_displacement {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP : P ≪ volume) (hP2 : MemLp id 2 P)
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hlaw : ∀ i, P.map (T i) = target i)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2)
    (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hv : Measurable v) (hv2 : MemLp v 2 P) :
    HasDerivAt (fun t ↦ wassersteinBarycenterEnergy target (displacementLaw P v t))
      (∫ x, inner ℝ (wassersteinBarycenterGradient T x) (v x) ∂P) 0 := by
  let pp : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) := ⟨P, inferInstance⟩
  obtain ⟨μ, hμ⟩ := TauCeti.exists_coe_eq_map_of_memLp (ν := pp) hP2
  have hμ' : ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure _) = P :=
    hμ.trans Measure.map_id
  choose ν hν using fun i ↦ TauCeti.exists_coe_eq_map_of_memLp (ν := pp) (hT2 i)
  have hν' (i : Fin k) : ((ν i : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure _) =
    target i :=
    (hν i).trans (hlaw i)
  have hder (i : Fin k) : HasDerivAt (fun t : ℝ ↦
        (TauCeti.wassersteinEDist 2 (P.map fun x ↦ x + t • v x) (target i)).toReal ^ 2)
      (2*∫ x, inner ℝ (x - T i x) (v x) ∂P) 0 := by
    have hd := has_deriv_at_wasserstein_sq_displacement μ (ν i) (by simpa only [hμ'] using hP) (T i)
      (hT i)
      (by simpa only [hμ', hν'] using hlaw i)
      (by simpa only [hμ', hν'] using hopt i) v hv
      (by simpa only [hμ'] using hv2)
    simpa only [hμ', hν'] using hd
  exact barycenter_derivative_of_component_derivatives hk P hP2 target T hT2 v hv2 hder

/-- GAPS 108.58: a minimizing barycenter with the supplied optimal maps satisfies the
Karcher equation. -/
theorem satisfies_wasserstein_karcher_equation_of_minimizer {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP2 : MemLp id 2 P)
    (target : Fin k → Measure (EuclideanSpace ℝ (Fin d)))
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hlaw : ∀ i, P.map (T i) = target i)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2)
    (hmin : ∀ Q : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure Q → MemLp id 2 Q →
      wassersteinBarycenterEnergy target P ≤ wassersteinBarycenterEnergy target Q) :
    SatisfiesWassersteinKarcherEquation P T := by
  let g := wassersteinBarycenterGradient T
  have hsum : MemLp (fun x ↦ ∑ i, T i x) 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦ hT2 i
  have hg2 : MemLp g 2 P := hP2.sub (hsum.const_smul ((k : ℝ)⁻¹))
  have hgm : Measurable g := measurable_id.sub
    ((Finset.measurable_fun_sum Finset.univ fun i _ ↦ hT i).const_smul ((k : ℝ)⁻¹))
  have hstepm : Measurable (fun x ↦ x - (1 : ℝ) • g x) :=
    measurable_id.sub (hgm.const_smul (1 : ℝ))
  have hstep2 : MemLp (fun x ↦ x - (1 : ℝ) • g x) 2 P :=
    hP2.sub (hg2.const_smul (1 : ℝ))
  have hmap2 : MemLp id 2 (P.map (fun x ↦ x - (1 : ℝ) • g x)) := by
    rwa [memLp_map_measure_iff (by fun_prop) hstepm.aemeasurable]
  have hopt' : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (P.map (T i))).toReal ^ 2 := by
    intro i
    rw [hlaw]
    exact hopt i
  have hdescent := wasserstein_barycenter_energy_map_sub_le hk P hP2 T hT hT2 hopt' 1
  have hmin' := hmin (P.map (fun x ↦ x - (1 : ℝ) • g x))
    inferInstance hmap2
  simp only [wassersteinBarycenterEnergy, ← hlaw] at hmin'
  change _ ≤ -(1 - 1 ^ 2 / 2) * ∫ x, ‖g x‖ ^ 2 ∂P at hdescent
  have hzero : (∫ x, ‖g x‖ ^ 2 ∂P) = 0 := by
    have hnonneg : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    simp only [wassersteinBarycenterEnergy] at hdescent
    norm_num [g, wassersteinBarycenterGradient] at hmin' hdescent hnonneg
    change (∫ x, ‖x - (k : ℝ)⁻¹ • ∑ i, T i x‖ ^ 2 ∂P) = 0
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖g x‖)
    (hg2.integrable_norm_pow two_ne_zero)).mp hzero
  filter_upwards [hae] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- The Karcher equation says exactly that the average optimal map is the identity almost surely. -/
theorem satisfies_wasserstein_karcher_equation_iff {d k : ℕ}
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
