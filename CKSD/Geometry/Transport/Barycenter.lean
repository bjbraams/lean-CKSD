module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import CKSD.Geometry.Transport.FirstVariation
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import CKSD.Geometry.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Wasserstein barycenters: energy, descent, and first variation

The equal-weight Wasserstein barycenter energy `(2k)⁻¹ ∑_i W₂²(P, P_i)` and the barycenter
gradient `x - k⁻¹ ∑_i T_i x` defined by transport maps `T_i`, the energy-descent inequality for the
averaged-transport update, and the first-order theory of the energy. Wasserstein distances are
TauCeti's `TauCeti.wassersteinEDist`.

## Main definitions

* `CKSD.wassersteinBarycenterEnergy`: the equal-weight barycenter energy
  `(2k)⁻¹ ∑_i W₂²(P, target_i)`.
* `CKSD.wassersteinBarycenterGradient`: the displacement `x - k⁻¹ ∑_i T_i x` defined by transport
  maps `T_i`. Both are stated on a general real inner product space.
* `CKSD.SatisfiesWassersteinKarcherEquation`: the Karcher (first-order) equation for a barycenter.
* `CKSD.displacementLaw`: the law displaced along a vector field.

## Main results

* `CKSD.wassersteinBarycenterEnergy_map_sub_le`: the descent inequality for the averaged-transport
  update (GAPS 108.59).
* `CKSD.hasDerivAt_wassersteinBarycenterEnergy_displacement`: the directional first variation of
  the barycenter energy (GAPS 108.58). It is a directional derivative along a specified
  square-integrable displacement, not the full Wasserstein Fréchet expansion.
* `CKSD.satisfiesWassersteinKarcherEquation_of_minimizer`: minimizers satisfy the Karcher equation
  (GAPS 108.58).

## References

* S. Chewi, J. Niles-Weed, P. Rigollet, *Statistical optimal transport*, École d'Été de
  Probabilités de Saint-Flour XLIX (2019), Lecture Notes in Mathematics 2364, Springer, 2025.
* M. Agueh, G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924.
* Y. Zemel, V. M. Panaretos, *Fréchet means and Procrustes analysis in Wasserstein space*,
  Bernoulli 25 (2019), 932–976.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

section Barycenter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The equal-weight Wasserstein barycenter energy `(2k)⁻¹ ∑_i W₂²(P, target_i)`, with the factor
`1/2` normalization. -/
def wassersteinBarycenterEnergy {k : ℕ} (target : Fin k → Measure E) (P : Measure E) : ℝ :=
  (∑ i, (TauCeti.wassersteinEDist 2 P (target i)).toReal ^ 2) / (2 * k)

/-- The candidate barycenter gradient `x - k⁻¹ ∑_i T_i x` represented by transport maps `T_i`
(optimal maps from the current law to the targets). -/
def wassersteinBarycenterGradient {k : ℕ} (T : Fin k → E → E) (x : E) : E :=
  x - (k : ℝ)⁻¹ • ∑ i, T i x

omit [InnerProductSpace ℝ E] in
/-- The squared `2`-Wasserstein distance between the laws of `S` and `T` under `P` is at most
the mean squared distance `∫ ‖S x - T x‖² dP`, by the coupling `(S, T)_# P`. -/
theorem wassersteinEDist_two_map_toReal_sq_le (P : Measure E) {S T : E → E} (hS : Measurable S)
    (hT : Measurable T) (h : MemLp (fun x ↦ S x - T x) 2 P) :
    (TauCeti.wassersteinEDist 2 (P.map S) (P.map T)).toReal ^ 2 ≤ ∫ x, ‖S x - T x‖ ^ 2 ∂P := by
  have hc := TauCeti.isCoupling_map_prodMk_of_aemeasurable (γ := P) hS.aemeasurable
    hT.aemeasurable rfl rfl
  have hW := TauCeti.wassersteinEDist_le hc 2
  rw [eLpNorm_map_measure (by fun_prop) (by fun_prop)] at hW
  have he : eLpNorm ((fun z : E × E ↦ edist z.1 z.2) ∘ fun x ↦ (S x, T x)) 2 P =
      eLpNorm (fun x ↦ S x - T x) 2 P := by
    refine eLpNorm_congr_enorm_ae (by fun_prop) h.aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp [edist_eq_enorm_sub]
  rw [he, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hW
  have hI : 0 ≤ ∫ x, ‖S x - T x‖ ^ (2 : ℝ≥0∞).toReal ∂P :=
    integral_nonneg fun x ↦ by positivity
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
  refine hsq.trans_eq ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hI ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Pointwise form of the descent identity: with `g = x - k⁻¹ ∑ Tᵢ`, moving `x` by `-τ g` changes
the sum of squared distances to the `Tᵢ` by `-k (2τ - τ²) ‖g‖²`. -/
theorem sum_norm_sub_smul_sub_sq {k : ℕ} (hk : 0 < k) (x : E) (t : Fin k → E) (tau : ℝ) :
    ∑ i, ‖x - tau • (x - (k : ℝ)⁻¹ • ∑ j, t j) - t i‖ ^ 2 =
      ∑ i, ‖x - t i‖ ^ 2 - k * (2 * tau - tau ^ 2) * ‖x - (k : ℝ)⁻¹ • ∑ j, t j‖ ^ 2 := by
  set g := x - (k : ℝ)⁻¹ • ∑ j, t j
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsum : ∑ i, (x - t i) = (k : ℝ) • g := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_sub, smul_smul, mul_inv_cancel₀ hk', one_smul, Nat.cast_smul_eq_nsmul]
  have hpt : ∀ i, ‖x - tau • g - t i‖ ^ 2 =
      ‖x - t i‖ ^ 2 - 2 * tau * inner ℝ (x - t i) g + tau ^ 2 * ‖g‖ ^ 2 := by
    intro i
    rw [show x - tau • g - t i = (x - t i) - tau • g by abel, norm_sub_sq_real, inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- GAPS 108.59, the energy-descent inequality for the averaged-transport update. Let `P` have
finite second moment, let `T_i` be square-integrable maps that are optimal from `P` to
`P_i = (T_i)_# P`, and let `g = x - k⁻¹ ∑ T_i x` be the barycenter gradient. Then for every step
size `τ` the update `x ↦ x - τ g(x)` lowers the barycenter energy by at least
`(τ - τ²/2) ∫ ‖g‖² dP`. The usual descent interpretation uses `τ ∈ [0, 1]`; no convergence of the
iteration is asserted. -/
theorem wassersteinBarycenterEnergy_map_sub_le {k : ℕ} (hk : 0 < k) (P : Measure E)
    (hP2 : MemLp id 2 P) (T : Fin k → E → E) (hT : ∀ i, Measurable (T i))
    (hT2 : ∀ i, MemLp (T i) 2 P)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (P.map (T i))).toReal ^ 2) (tau : ℝ) :
    wassersteinBarycenterEnergy (fun i ↦ P.map (T i))
        (P.map fun x ↦ x - tau • wassersteinBarycenterGradient T x) -
      wassersteinBarycenterEnergy (fun i ↦ P.map (T i)) P ≤
      -(tau - tau ^ 2 / 2) * ∫ x, ‖wassersteinBarycenterGradient T x‖ ^ 2 ∂P := by
  set g := wassersteinBarycenterGradient T with hg_def
  set F := wassersteinBarycenterEnergy fun i ↦ P.map (T i) with hF_def
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsumT : MemLp (fun x ↦ ∑ i, T i x) 2 P := memLp_finsetSum Finset.univ fun i _ ↦ hT2 i
  have hg2 : MemLp g 2 P := hP2.sub (hsumT.const_smul ((k : ℝ)⁻¹))
  have hgm : Measurable g := measurable_id.sub
    ((Finset.measurable_fun_sum Finset.univ fun i _ ↦ hT i).const_smul ((k : ℝ)⁻¹))
  have hSm : Measurable fun x ↦ x - tau • g x := measurable_id.sub (hgm.const_smul tau)
  have hS2 : MemLp (fun x ↦ x - tau • g x) 2 P := hP2.sub (hg2.const_smul tau)
  have hdiff : ∀ i, MemLp (fun x ↦ x - tau • g x - T i x) 2 P := fun i ↦ hS2.sub (hT2 i)
  have hdiff0 : ∀ i, MemLp (fun x ↦ x - T i x) 2 P := fun i ↦ hP2.sub (hT2 i)
  have hint : ∀ {f : E → E}, MemLp f 2 P →
      Integrable (fun x ↦ ‖f x‖ ^ 2) P := fun hf ↦ hf.integrable_norm_pow two_ne_zero
  -- each new squared distance is bounded by the cost of the coupling through `P`
  have hbound : ∀ i, (TauCeti.wassersteinEDist 2 (P.map fun x ↦ x - tau • g x)
      (P.map (T i))).toReal ^ 2 ≤ ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P :=
    fun i ↦ wassersteinEDist_two_map_toReal_sq_le P hSm (hT i) (hdiff i)
  have hnew : F (P.map fun x ↦ x - tau • g x) ≤
      (∑ i, ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P) / (2 * k) := by
    simp only [F, wassersteinBarycenterEnergy]
    gcongr with i
    exact hbound i
  have hold : F P = (∑ i, ∫ x, ‖x - T i x‖ ^ 2 ∂P) / (2 * k) := by
    simp only [F, wassersteinBarycenterEnergy, hopt]
  have hid : (∑ i, ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P) =
      (∑ i, ∫ x, ‖x - T i x‖ ^ 2 ∂P) - k * (2 * tau - tau ^ 2) * ∫ x, ‖g x‖ ^ 2 ∂P := by
    rw [← integral_finsetSum _ fun i _ ↦ hint (hdiff i),
      ← integral_finsetSum _ fun i _ ↦ hint (hdiff0 i), ← integral_const_mul,
      ← integral_sub (integrable_finsetSum _ fun i _ ↦ hint (hdiff0 i))
        ((hint hg2).const_mul _)]
    congr 1
    ext x
    exact sum_norm_sub_smul_sub_sq hk x (fun i ↦ T i x) tau
  rw [hold]
  refine (sub_le_sub_right hnew _).trans_eq ?_
  rw [hid]
  field_simp
  ring

end Barycenter

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
theorem hasDerivAt_wassersteinBarycenterEnergy_displacement {d k : ℕ} (hk : 0 < k)
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
    have hd := hasDerivAt_wasserstein_sq_displacement μ (ν i) (by simpa only [hμ'] using hP) (T i)
      (hT i)
      (by simpa only [hμ', hν'] using hlaw i)
      (by simpa only [hμ', hν'] using hopt i) v hv
      (by simpa only [hμ'] using hv2)
    simpa only [hμ', hν'] using hd
  exact barycenter_derivative_of_component_derivatives hk P hP2 target T hT2 v hv2 hder

/-- GAPS 108.58: a minimizing barycenter with the supplied optimal maps satisfies the
Karcher equation. -/
theorem satisfiesWassersteinKarcherEquation_of_minimizer {d k : ℕ} (hk : 0 < k)
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
  have hdescent := wassersteinBarycenterEnergy_map_sub_le hk P hP2 T hT hT2 hopt' 1
  have hmin' := hmin (P.map (fun x ↦ x - (1 : ℝ) • g x))
    inferInstance hmap2
  simp only [wassersteinBarycenterEnergy, ← hlaw] at hmin'
  -- restate the descent bound through the local gradient `g`
  change _ ≤ -(1 - 1 ^ 2 / 2) * ∫ x, ‖g x‖ ^ 2 ∂P at hdescent
  have hzero : (∫ x, ‖g x‖ ^ 2 ∂P) = 0 := by
    have hnonneg : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    simp only [wassersteinBarycenterEnergy] at hdescent
    norm_num [g, wassersteinBarycenterGradient] at hmin' hdescent hnonneg
    -- unfold the local gradient `g` in the goal, as `norm_num` did in the hypotheses
    change (∫ x, ‖x - (k : ℝ)⁻¹ • ∑ i, T i x‖ ^ 2 ∂P) = 0
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖g x‖)
    (hg2.integrable_norm_pow two_ne_zero)).mp hzero
  filter_upwards [hae] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

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
