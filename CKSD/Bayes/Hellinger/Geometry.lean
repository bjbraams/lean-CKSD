/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli, Bastiaan J Braams
-/
module

import CKSD.Inference.Density
public import CKSD.Inference.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Hellinger geometry and bounded testing scores

Hellinger distance in the convention `h²(P,Q) = ∫ (√p - √q)² dμ` and the bounded score
`(√q - √p)/(√q + √p)` used to test a law against a Hellinger neighbourhood of an alternative.

The score has mean separation `h²(P,Q)` and second moments bounded by that separation. Its mean
under a perturbed law `R` differs from the mean under `Q` by at most `2 h(R,Q) h(P,Q) + h(R,Q)²`.
The square-root density representation also gives the triangle inequality
(`CKSD.statisticalHellingerDistance_triangle`), with densities relative to `P + Q + R`.

The Hellinger divergence and its mixture formula are specialized from Statlib's
`Divergence.Hellinger.Basic` and `Divergence.FDiv.Basic`. The proofs use Mathlib's
Radon–Nikodym chain rules and Hölder's inequality.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- The Hellinger divergence integrand at exponent one half. Its value at infinity is
the extended limit of the finite-argument formula. -/
private def hellingerIntegrand (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ∞ else ENNReal.ofReal ((1 - Real.sqrt r.toReal) ^ 2)

/-- The extended Hellinger integrand is measurable. -/
private theorem measurable_hellingerIntegrand : Measurable hellingerIntegrand := by
  unfold hellingerIntegrand
  exact (by
    apply Measurable.ite (measurableSet_singleton ∞)
    · exact measurable_const
    · fun_prop)

/-- Squared Hellinger distance, with the full singular mass of the first measure.
This uses the convention without a factor of one half. The decomposition follows
Statlib's square-root specialization of its Hellinger divergence. -/
def squaredStatisticalHellingerDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ≥0∞ :=
  (∫⁻ x, hellingerIntegrand (P.rnDeriv Q x) ∂Q) + P.singularPart Q univ

/-- Statistical Hellinger distance in the convention `h² = ∫ (√p - √q)²` for probability laws.
An infinite value of the squared divergence is sent to zero by `ENNReal.toReal`. -/
def statisticalHellingerDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ := Real.sqrt (squaredStatisticalHellingerDistance P Q).toReal

/-- Defining equation of `statisticalHellingerDistance`. -/
theorem statisticalHellingerDistance_def {X : Type*} [MeasurableSpace X] (P Q : Measure X) :
    statisticalHellingerDistance P Q =
      Real.sqrt (squaredStatisticalHellingerDistance P Q).toReal := by
  rw [statisticalHellingerDistance]

/-- The singular mass of `P` relative to `Q` is the `P`-mass where the `Q` density vanishes.
This argument follows Statlib's Radon–Nikodym decomposition lemma. -/
private theorem singularPart_univ_eq_rnDeriv_add_eq_zero {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    P.singularPart Q univ = P {x | Q.rnDeriv (P + Q) x = 0} := by
  let N := {x | Q.rnDeriv (P + Q) x = 0}
  have hN : MeasurableSet N := measurableSet_eq_fun (Q.measurable_rnDeriv _) measurable_const
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hQN : Q N = 0 := by
    rw [← Measure.setLIntegral_rnDeriv hQ,
      setLIntegral_congr_fun hN (g := 0) fun x hx ↦ hx]
    simp
  have hac : P.restrict Nᶜ ≪ Q := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hQA ↦ ?_
    rw [Measure.restrict_apply hA]
    refine Measure.AbsolutelyContinuous.rfl.add_right Q ?_
    rw [← Measure.setLIntegral_rnDeriv hQ,
      setLIntegral_eq_zero_iff hA (Q.measurable_rnDeriv _)] at hQA
    rw [← compl_compl (A ∩ Nᶜ), ← mem_ae_iff]
    filter_upwards [hQA] with x hx hxN
    exact hxN.2 (hx hxN.1)
  have hSing : P.singularPart Q = P.restrict N := by
    refine Measure.singularPart_eq_restrict ?_ hQN
    rw [← Measure.restrict_apply_univ, ← Measure.singularPart_restrict P Q hN.compl,
      Measure.singularPart_eq_zero_of_ac hac]
    simp
  rw [hSing, Measure.restrict_apply_univ]

/-- Pointwise square-root identity for a positive denominator in the Hellinger perspective. -/
private theorem mul_hellingerIntegrand_div {p q : ℝ≥0∞} (hp : p ≠ ∞)
    (hq : q ≠ ∞) (hq0 : q ≠ 0) :
    q * hellingerIntegrand (p / q) =
      ENNReal.ofReal ((Real.sqrt p.toReal - Real.sqrt q.toReal) ^ 2) := by
  have hdiv : p / q ≠ ∞ := ENNReal.div_ne_top hp hq0
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hid : Real.sqrt (p.toReal / q.toReal) * Real.sqrt q.toReal = Real.sqrt p.toReal := by
    rw [← Real.sqrt_mul (div_nonneg ENNReal.toReal_nonneg hqpos.le),
      div_mul_cancel₀ _ hqpos.ne']
  have hsq : Real.sqrt q.toReal * (1 - Real.sqrt (p.toReal / q.toReal)) =
      -(Real.sqrt p.toReal - Real.sqrt q.toReal) := by
    rw [mul_sub, mul_one, mul_comm (Real.sqrt q.toReal), hid]
    ring
  have heq := congrArg (fun t : ℝ ↦ t ^ 2) hsq
  rw [mul_pow, Real.sq_sqrt hqpos.le, neg_sq] at heq
  rw [hellingerIntegrand, ite_eq_right hdiv, ENNReal.toReal_div]
  conv_lhs => lhs; rw [← ENNReal.ofReal_toReal hq]
  rw [← ENNReal.ofReal_mul hqpos.le, heq]

/-- The squared Hellinger distance is the integral of the squared difference of the two
square-root densities with respect to `P + Q`. This is the Hellinger case of Statlib's
mixture formula for divergences. -/
theorem squaredStatisticalHellingerDistance_eq_lintegral {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    squaredStatisticalHellingerDistance P Q =
      ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((P.rnDeriv (P + Q) x).toReal) -
        Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)) ^ 2) ∂(P + Q) := by
  let N := {x | Q.rnDeriv (P + Q) x = 0}
  have hN : MeasurableSet N := measurableSet_eq_fun (Q.measurable_rnDeriv _) measurable_const
  have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hQN : Q N = 0 := by
    rw [← Measure.setLIntegral_rnDeriv hQ,
      setLIntegral_congr_fun hN (g := 0) fun x hx ↦ hx]
    simp
  have hmass : P N = ∫⁻ x, N.indicator (1 : X → ℝ≥0∞) x ∂(P + Q) := by
    rw [lintegral_indicator_one hN, add_apply, hQN, add_zero]
  have hdivmeas := (P.measurable_rnDeriv (P + Q)).div (Q.measurable_rnDeriv (P + Q))
  have hchange :
      (∫⁻ x, hellingerIntegrand (P.rnDeriv Q x) ∂Q) =
        ∫⁻ x, Q.rnDeriv (P + Q) x *
          hellingerIntegrand (P.rnDeriv (P + Q) x / Q.rnDeriv (P + Q) x) ∂(P + Q) := by
    have htransport :=
      lintegral_rnDeriv_mul hQ (measurable_hellingerIntegrand.comp hdivmeas).aemeasurable
    rw [show (∫⁻ x, Q.rnDeriv (P + Q) x *
      hellingerIntegrand (P.rnDeriv (P + Q) x / Q.rnDeriv (P + Q) x) ∂(P + Q)) =
        ∫⁻ x, hellingerIntegrand (P.rnDeriv (P + Q) x / Q.rnDeriv (P + Q) x) ∂Q by
      simpa only [Function.comp_apply, Pi.div_apply] using htransport]
    exact lintegral_congr_ae ((Measure.rnDeriv_eq_div_rnDeriv_add P Q).mono
      fun x hx ↦ congrArg hellingerIntegrand hx)
  have hNm : Measurable (N.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hN
  rw [squaredStatisticalHellingerDistance, singularPart_univ_eq_rnDeriv_add_eq_zero,
    hchange, hmass, ← lintegral_add_right _ hNm]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top P (P + Q), Measure.rnDeriv_lt_top Q (P + Q),
    P.rnDeriv_add' Q (P + Q), (P + Q).rnDeriv_self] with x hp hq hadd hsum
  have hpq : P.rnDeriv (P + Q) x + Q.rnDeriv (P + Q) x = 1 := by
    rw [← Pi.add_apply, ← hadd, hsum]
  by_cases hqx : Q.rnDeriv (P + Q) x = 0
  · have hpx : P.rnDeriv (P + Q) x = 1 := by simpa only [hqx, add_zero] using hpq
    have hxN : x ∈ N := hqx
    simp [hqx, hpx, indicator_of_mem hxN]
  · have hxN : x ∉ N := hqx
    rw [indicator_of_notMem hxN, add_zero, mul_hellingerIntegrand_div hp.ne hq.ne hqx]

/-- Statistical Hellinger distance is nonnegative. -/
theorem statisticalHellingerDistance_nonneg {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : 0 ≤ statisticalHellingerDistance P Q := Real.sqrt_nonneg _

/-- Statistical Hellinger distance vanishes on two copies of the same σ-finite measure. -/
@[simp] theorem statisticalHellingerDistance_self {X : Type*} [MeasurableSpace X]
    (P : Measure X) [SigmaFinite P] : statisticalHellingerDistance P P = 0 := by
  rw [statisticalHellingerDistance_def, squaredStatisticalHellingerDistance_eq_lintegral]
  simp

/-- Statistical Hellinger distance is symmetric for σ-finite measures. -/
theorem statisticalHellingerDistance_comm {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    statisticalHellingerDistance P Q = statisticalHellingerDistance Q P := by
  simp only [statisticalHellingerDistance_def, squaredStatisticalHellingerDistance_eq_lintegral]
  rw [add_comm Q P]
  congr 2
  apply lintegral_congr
  intro x
  rw [← neg_sub, neg_sq]

/-- Hellinger affinity in terms of densities relative to a common dominating measure. -/
theorem integral_sqrt_rnDeriv_eq_integral_sqrt_density_mul {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) :
    ∫ x, Real.sqrt ((P.rnDeriv Q x).toReal) ∂Q =
      ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ := by
  have hPμ : P ≪ μ := by rw [hP.2.2]; exact withDensity_absolutelyContinuous _ _
  have hQμ : Q ≪ μ := by rw [hQ.2.2]; exact withDensity_absolutelyContinuous _ _
  have hp : P.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (p x) := by
    rw [hP.2.2]; exact Measure.rnDeriv_withDensity μ hP.1.ennreal_ofReal
  have hq : Q.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (q x) := by
    rw [hQ.2.2]; exact Measure.rnDeriv_withDensity μ hQ.1.ennreal_ofReal
  have hchain : ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal * q x = p x := by
    filter_upwards [Measure.rnDeriv_mul_rnDeriv' (μ := P) hQμ,
      hQμ.ae_le hp, hQμ.ae_le hq, hQμ.ae_le hP.2.1, hQμ.ae_le hQ.2.1] with x hx hp hq hp0 hq0
    simp only [Pi.mul_apply] at hx
    rw [hp, hq] at hx
    have := congrArg ENNReal.toReal hx
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hq0] using this
  have hchain' : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) ≠ 0 →
      (P.rnDeriv Q x).toReal * q x = p x := by
    apply (ae_withDensity_iff hQ.1.ennreal_ofReal).1
    rw [← hQ.2.2]
    exact hchain
  rw [hQ.integral_eq]
  refine integral_congr_ae ?_
  filter_upwards [hP.2.1, hQ.2.1, hchain'] with x hp0 hq0 hx
  by_cases h0 : q x = 0
  · simp [h0]
  have hqpos : 0 < q x := lt_of_le_of_ne hq0 (Ne.symm h0)
  have heq := hx (by simp [hqpos])
  calc q x * Real.sqrt ((P.rnDeriv Q x).toReal) =
      Real.sqrt (q x) * (Real.sqrt ((P.rnDeriv Q x).toReal) * Real.sqrt (q x)) := by
        rw [show Real.sqrt (q x) * (Real.sqrt ((P.rnDeriv Q x).toReal) * Real.sqrt (q x)) =
          Real.sqrt (q x) ^ 2 * Real.sqrt ((P.rnDeriv Q x).toReal) by ring, Real.sq_sqrt hq0]
    _ = Real.sqrt (q x) * Real.sqrt ((P.rnDeriv Q x).toReal * q x) := by
      rw [Real.sqrt_mul ENNReal.toReal_nonneg]
    _ = Real.sqrt (p x) * Real.sqrt (q x) := by rw [heq]; ring

/-- The square root of an integrable nonnegative density belongs to `L²`. -/
theorem HasDensity.memLp_sqrt {X : Type*} [MeasurableSpace X]
    {P μ : Measure X} [IsFiniteMeasure P] {p : X → ℝ} (hP : HasDensity P μ p) :
    MemLp (fun x ↦ Real.sqrt (p x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq hP.1.sqrt.aestronglyMeasurable).2
  exact hP.integrable.congr (hP.2.1.mono fun x hx ↦ (Real.sq_sqrt hx).symm)

/-- A finite measure absolutely continuous with respect to a σ-finite measure has the real
Radon–Nikodym derivative as a density. -/
theorem hasDensity_toReal_rnDeriv {X : Type*} [MeasurableSpace X] {P μ : Measure X}
    [IsFiniteMeasure P] [SigmaFinite μ] (hPμ : P ≪ μ) :
    HasDensity P μ (fun x ↦ (P.rnDeriv μ x).toReal) := by
  refine ⟨(Measure.measurable_rnDeriv P μ).ennreal_toReal,
    ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq P μ hPμ]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top P μ] with x hx
  rw [ENNReal.ofReal_toReal hx.ne]

/-- The square-root density integral is expressed by a mass and affinity formula. -/
private theorem integral_sq_sub_sqrt_density_eq {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) :
    (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ) =
      2 - 2 * ∫ x, Real.sqrt ((P.rnDeriv Q x).toReal) ∂Q := by
  rw [integral_sqrt_rnDeriv_eq_integral_sqrt_density_mul hP hQ]
  have hprod : Integrable (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)) μ :=
    hP.memLp_sqrt.integrable_mul hQ.memLp_sqrt
  have hexpand : (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) =ᵐ[μ]
      fun x ↦ p x + q x - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
    filter_upwards [hP.2.1, hQ.2.1] with x hp hq
    nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]
  rw [integral_congr_ae hexpand,
    integral_sub (f := fun x ↦ p x + q x) (g := fun x ↦ 2 * (Real.sqrt (p x) * Real.sqrt (q x)))
      (hP.integrable.add hQ.integrable) (hprod.const_mul 2),
    integral_add (f := p) (g := q) hP.integrable hQ.integrable, integral_const_mul,
    hP.integral_eq_one, hQ.integral_eq_one]
  ring

/-- Hellinger distance is the `L²` distance between square roots of densities. -/
theorem statisticalHellingerDistance_sq_eq_integral {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) :
    statisticalHellingerDistance P Q ^ 2 =
      ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ := by
  have hP' := hasDensity_toReal_rnDeriv
    (Measure.AbsolutelyContinuous.rfl.add_right Q : P ≪ P + Q)
  have hQ' := hasDensity_toReal_rnDeriv
    (Measure.AbsolutelyContinuous.rfl.add_right' P : Q ≪ P + Q)
  have hInt : Integrable (fun x ↦ (Real.sqrt ((P.rnDeriv (P + Q) x).toReal) -
      Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)) ^ 2) (P + Q) :=
    (hP'.memLp_sqrt.sub hQ'.memLp_sqrt).integrable_sq
  rw [statisticalHellingerDistance_def, Real.sq_sqrt ENNReal.toReal_nonneg,
    squaredStatisticalHellingerDistance_eq_lintegral,
    ← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _),
    integral_sq_sub_sqrt_density_eq hP' hQ', integral_sq_sub_sqrt_density_eq hP hQ]

/-- Bounded Hellinger score separating a null density `p` from an alternative density `q`. -/
def hellingerScore {X : Type*} (p q : X → ℝ) (x : X) : ℝ :=
  (Real.sqrt (q x) - Real.sqrt (p x)) / (Real.sqrt (q x) + Real.sqrt (p x))

/-- The Hellinger score is measurable. -/
theorem measurable_hellingerScore {X : Type*} [MeasurableSpace X]
    {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q) : Measurable (hellingerScore p q) :=
  (hq.sqrt.sub hp.sqrt).div (hq.sqrt.add hp.sqrt)

/-- The Hellinger score takes values in `[-1,1]`, including points where both densities vanish. -/
theorem abs_hellingerScore_le_one {X : Type*} (p q : X → ℝ) (x : X) :
    |hellingerScore p q x| ≤ 1 := by
  have ha := Real.sqrt_nonneg (p x)
  have hb := Real.sqrt_nonneg (q x)
  by_cases hsum : Real.sqrt (q x) + Real.sqrt (p x) = 0
  · simp [hellingerScore, hsum]
  have hpos : 0 < Real.sqrt (q x) + Real.sqrt (p x) := lt_of_le_of_ne (by positivity) (Ne.symm hsum)
  rw [hellingerScore, abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
  constructor <;> linarith

/-- A density-weighted squared Hellinger score is at most the squared square-root difference. -/
theorem mul_hellingerScore_sq_le {X : Type*} {p q : X → ℝ} {x : X}
    (hq : 0 ≤ q x) :
    q x * hellingerScore p q x ^ 2 ≤ (Real.sqrt (q x) - Real.sqrt (p x)) ^ 2 := by
  have ha := Real.sqrt_nonneg (p x)
  have hb := Real.sqrt_nonneg (q x)
  by_cases hsum : Real.sqrt (q x) + Real.sqrt (p x) = 0
  · have hq0 : q x = 0 := by nlinarith [Real.sq_sqrt hq]
    simp [hq0, hellingerScore]
  have hpos : 0 < Real.sqrt (q x) + Real.sqrt (p x) := lt_of_le_of_ne (by positivity) (Ne.symm hsum)
  have hfrac : (Real.sqrt (q x) / (Real.sqrt (q x) + Real.sqrt (p x))) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.sqrt (q x) / (Real.sqrt (q x) + Real.sqrt (p x)) := by positivity
    have h1 : Real.sqrt (q x) / (Real.sqrt (q x) + Real.sqrt (p x)) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    nlinarith
  calc q x * hellingerScore p q x ^ 2 =
      (Real.sqrt (q x) / (Real.sqrt (q x) + Real.sqrt (p x))) ^ 2 *
        (Real.sqrt (q x) - Real.sqrt (p x)) ^ 2 := by
          rw [hellingerScore, div_pow, div_pow, Real.sq_sqrt hq]
          ring
    _ ≤ 1 * (Real.sqrt (q x) - Real.sqrt (p x)) ^ 2 :=
      mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
    _ = _ := one_mul _

/-- The mean separation identity for the Hellinger score. -/
theorem sub_mul_hellingerScore_eq {X : Type*} {p q : X → ℝ} {x : X}
    (hp : 0 ≤ p x) (hq : 0 ≤ q x) :
    (q x - p x) * hellingerScore p q x = (Real.sqrt (q x) - Real.sqrt (p x)) ^ 2 := by
  have ha := Real.sqrt_nonneg (p x)
  have hb := Real.sqrt_nonneg (q x)
  by_cases hsum : Real.sqrt (q x) + Real.sqrt (p x) = 0
  · have h1 : Real.sqrt (p x) = 0 := by linarith
    have h2 : Real.sqrt (q x) = 0 := by linarith
    simp [hellingerScore, h1, h2]
  have heq : q x - p x = (Real.sqrt (q x) - Real.sqrt (p x)) *
      (Real.sqrt (q x) + Real.sqrt (p x)) := by nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]
  rw [hellingerScore, heq]
  field_simp

/-- Cauchy–Schwarz for real `L²` functions, in square-root moment form. -/
theorem abs_integral_mul_le_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hc : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_norm_le_Lp_mul_Lq hc (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ _ := h

/-- The bounded Hellinger score belongs to every `Lᵖ` under a finite measure. -/
theorem memLp_hellingerScore {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] {p q : X → ℝ} (hp : Measurable p) (hq : Measurable q) (a : ℝ≥0∞) :
    MemLp (hellingerScore p q) a P :=
  MemLp.of_bound (measurable_hellingerScore hp hq).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using abs_hellingerScore_le_one p q x)

/-- The difference between the alternative and null score means is the squared Hellinger
distance. -/
theorem integral_hellingerScore_sub_eq {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) :
    (∫ x, hellingerScore p q x ∂Q) - (∫ x, hellingerScore p q x ∂P) =
      statisticalHellingerDistance P Q ^ 2 := by
  have hiP :=
    (hP.integrable_iff _).1 ((memLp_hellingerScore P hP.1 hQ.1 2).integrable (by norm_num))
  have hiQ :=
    (hQ.integrable_iff _).1 ((memLp_hellingerScore Q hP.1 hQ.1 2).integrable (by norm_num))
  rw [hP.integral_eq, hQ.integral_eq, ← integral_sub hiQ hiP,
    statisticalHellingerDistance_sq_eq_integral hP hQ]
  refine integral_congr_ae ?_
  filter_upwards [hP.2.1, hQ.2.1] with x hp hq
  have h := sub_mul_hellingerScore_eq hp hq
  nlinarith

/-- The squared score has expectation at most the squared Hellinger distance under its
alternative. -/
theorem integral_hellingerScore_sq_le {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) :
    (∫ x, hellingerScore p q x ^ 2 ∂Q) ≤ statisticalHellingerDistance P Q ^ 2 := by
  rw [hQ.integral_eq, statisticalHellingerDistance_sq_eq_integral hP hQ]
  apply integral_mono_ae
    ((hQ.integrable_iff _).1 (memLp_hellingerScore Q hP.1 hQ.1 2).integrable_sq)
    (by simpa only [Pi.sub_apply] using (hP.memLp_sqrt.sub hQ.memLp_sqrt).integrable_sq)
  filter_upwards [hQ.2.1] with x hq
  convert mul_hellingerScore_sq_le (p := p) hq using 1; ring

/-- Exchanging the densities negates the Hellinger score. -/
theorem hellingerScore_swap {X : Type*} (p q : X → ℝ) :
    hellingerScore q p = fun x ↦ -hellingerScore p q x := by
  funext x
  unfold hellingerScore
  rw [add_comm (Real.sqrt (p x))]
  ring

/-- Changing a law by Hellinger distance `ρ` changes the mean of a bounded score by at most
`2 ρ a + ρ²`, when the score's second moment under the reference law is at most `a²`. -/
theorem abs_integral_sub_le_hellinger {X : Type*} [MeasurableSpace X]
    {Q R μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {q r : X → ℝ} (hQ : HasDensity Q μ q) (hR : HasDensity R μ r)
    (T : X → ℝ) (hT : Measurable T) (hTb : ∀ x, |T x| ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (hsecond : ∫ x, T x ^ 2 ∂Q ≤ a ^ 2) :
    |(∫ x, T x ∂R) - (∫ x, T x ∂Q)| ≤
      2 * statisticalHellingerDistance R Q * a + statisticalHellingerDistance R Q ^ 2 := by
  let D : X → ℝ := fun x ↦ Real.sqrt (r x) - Real.sqrt (q x)
  let W : X → ℝ := fun x ↦ Real.sqrt (q x) * T x
  have hTmem (ν : Measure X) [IsFiniteMeasure ν] : MemLp T 2 ν :=
    MemLp.of_bound hT.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hTb x)
  have hD : MemLp D 2 μ := by simpa only [Pi.sub_def, D] using hR.memLp_sqrt.sub hQ.memLp_sqrt
  have hW : MemLp W 2 μ := by
    apply (memLp_two_iff_integrable_sq (hQ.1.sqrt.mul hT).aestronglyMeasurable).2
    refine ((hQ.integrable_iff _).1 (hTmem Q).integrable_sq).congr ?_
    filter_upwards [hQ.2.1] with x hx
    dsimp [W]
    rw [mul_pow, Real.sq_sqrt hx]
  have hDmoment : ∫ x, D x ^ 2 ∂μ = statisticalHellingerDistance R Q ^ 2 :=
    (statisticalHellingerDistance_sq_eq_integral hR hQ).symm
  have hWmoment : ∫ x, W x ^ 2 ∂μ = ∫ x, T x ^ 2 ∂Q := by
    rw [hQ.integral_eq]
    refine integral_congr_ae ?_
    filter_upwards [hQ.2.1] with x hx
    dsimp [W]
    rw [mul_pow, Real.sq_sqrt hx]
  have hDnonneg : 0 ≤ statisticalHellingerDistance R Q := Real.sqrt_nonneg _
  have hCS : |∫ x, D x * W x ∂μ| ≤ statisticalHellingerDistance R Q * a := by
    have h := abs_integral_mul_le_sqrt hD hW
    rw [hDmoment, hWmoment, Real.sqrt_sq_eq_abs, abs_of_nonneg hDnonneg] at h
    exact h.trans (mul_le_mul_of_nonneg_left ((Real.sqrt_le_left ha).2 hsecond) hDnonneg)
  have hrem : Integrable (fun x ↦ D x ^ 2 * T x) μ :=
    hD.integrable_sq.mul_bdd hT.aestronglyMeasurable (ae_of_all _ fun x ↦ by
      simpa [Real.norm_eq_abs] using hTb x)
  have hRemBound : |∫ x, D x ^ 2 * T x ∂μ| ≤ statisticalHellingerDistance R Q ^ 2 := by
    refine abs_integral_le_integral_abs.trans ?_
    rw [← hDmoment]
    apply integral_mono_ae hrem.abs hD.integrable_sq
    exact ae_of_all _ fun x ↦ by
      dsimp only
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (hTb x)
  have hexpand : (∫ x, T x ∂R) - (∫ x, T x ∂Q) =
      2 * (∫ x, D x * W x ∂μ) + ∫ x, D x ^ 2 * T x ∂μ := by
    rw [hR.integral_eq, hQ.integral_eq,
      ← integral_sub ((hR.integrable_iff _).1 ((hTmem R).integrable (by norm_num)))
        ((hQ.integrable_iff _).1 ((hTmem Q).integrable (by norm_num))),
      ← integral_const_mul, ← integral_add (f := fun x ↦ 2 * (D x * W x))
        (g := fun x ↦ D x ^ 2 * T x) (hD.integrable_mul hW |>.const_mul 2) hrem]
    refine integral_congr_ae ?_
    filter_upwards [hR.2.1, hQ.2.1] with x hr hq
    dsimp [D, W]
    have h1 := congrArg (fun z : ℝ ↦ z * T x) (Real.sq_sqrt hr)
    have h2 := congrArg (fun z : ℝ ↦ z * T x) (Real.sq_sqrt hq)
    nlinarith
  rw [hexpand]
  calc |2 * (∫ x, D x * W x ∂μ) + ∫ x, D x ^ 2 * T x ∂μ| ≤
      2 * |∫ x, D x * W x ∂μ| + |∫ x, D x ^ 2 * T x ∂μ| := by
        simpa only [abs_mul, abs_two] using abs_add_le
          (2 * (∫ x, D x * W x ∂μ)) (∫ x, D x ^ 2 * T x ∂μ)
    _ ≤ _ := by nlinarith

/-- A bounded score's second moment under a perturbed law is at most twice its reference second
moment plus twice the squared Hellinger distance. -/
theorem integral_sq_le_of_hellinger {X : Type*} [MeasurableSpace X]
    {Q R μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {q r : X → ℝ} (hQ : HasDensity Q μ q) (hR : HasDensity R μ r)
    (T : X → ℝ) (hT : Measurable T) (hTb : ∀ x, |T x| ≤ 1) :
    (∫ x, T x ^ 2 ∂R) ≤
      2 * statisticalHellingerDistance R Q ^ 2 + 2 * (∫ x, T x ^ 2 ∂Q) := by
  let D : X → ℝ := fun x ↦ Real.sqrt (r x) - Real.sqrt (q x)
  have hTmem (ν : Measure X) [IsFiniteMeasure ν] : MemLp T 2 ν :=
    MemLp.of_bound hT.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hTb x)
  have hD : MemLp D 2 μ := by simpa only [Pi.sub_def, D] using hR.memLp_sqrt.sub hQ.memLp_sqrt
  rw [hR.integral_eq, hQ.integral_eq, statisticalHellingerDistance_sq_eq_integral hR hQ,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hD.integrable_sq.const_mul 2)
      (((hQ.integrable_iff _).1 (hTmem Q).integrable_sq).const_mul 2)]
  apply integral_mono_ae ((hR.integrable_iff _).1 (hTmem R).integrable_sq)
    ((hD.integrable_sq.const_mul 2).add
      (((hQ.integrable_iff _).1 (hTmem Q).integrable_sq).const_mul 2))
  filter_upwards [hR.2.1, hQ.2.1] with x hr hq
  have ht : T x ^ 2 ≤ 1 := by nlinarith [sq_abs (T x), hTb x, abs_nonneg (T x)]
  have heq : r x * T x ^ 2 = (D x * T x + Real.sqrt (q x) * T x) ^ 2 := by
    dsimp [D]
    rw [show (Real.sqrt (r x) - Real.sqrt (q x)) * T x + Real.sqrt (q x) * T x =
      Real.sqrt (r x) * T x by ring, mul_pow, Real.sq_sqrt hr]
  have h1 : (D x * T x + Real.sqrt (q x) * T x) ^ 2 ≤
      2 * (D x * T x) ^ 2 + 2 * (Real.sqrt (q x) * T x) ^ 2 := by
    nlinarith [sq_nonneg (D x * T x - Real.sqrt (q x) * T x)]
  have h2 : (D x * T x) ^ 2 ≤ D x ^ 2 := by
    rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg _) ht
  -- Fold `D x` and apply the scalar multiplication, the form `rw [heq]` and `h1`, `h2` use.
  change r x * T x ^ 2 ≤ 2 * D x ^ 2 + 2 * (q x * T x ^ 2)
  rw [heq]
  simp only [mul_pow, Real.sq_sqrt hq] at h1
  nlinarith

/-- Triangle inequality for Hellinger distance among laws with a common dominating measure. -/
theorem statisticalHellingerDistance_triangle_of_hasDensity {X : Type*} [MeasurableSpace X]
    {P Q R μ : Measure X} [SigmaFinite μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {p q r : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q) (hR : HasDensity R μ r) :
    statisticalHellingerDistance P R ≤
      statisticalHellingerDistance P Q + statisticalHellingerDistance Q R := by
  let A : X → ℝ := fun x ↦ Real.sqrt (p x) - Real.sqrt (q x)
  let B : X → ℝ := fun x ↦ Real.sqrt (q x) - Real.sqrt (r x)
  have hA : MemLp A 2 μ := by simpa only [Pi.sub_def, A] using hP.memLp_sqrt.sub hQ.memLp_sqrt
  have hB : MemLp B 2 μ := by simpa only [Pi.sub_def, B] using hQ.memLp_sqrt.sub hR.memLp_sqrt
  have hcs := abs_integral_mul_le_sqrt hA hB
  rw [← statisticalHellingerDistance_sq_eq_integral hP hQ,
    ← statisticalHellingerDistance_sq_eq_integral hQ hR,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ statisticalHellingerDistance P Q from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ statisticalHellingerDistance Q R from Real.sqrt_nonneg _)] at hcs
  have heq : statisticalHellingerDistance P R ^ 2 = statisticalHellingerDistance P Q ^ 2 +
      2 * (∫ x, A x * B x ∂μ) + statisticalHellingerDistance Q R ^ 2 := by
    rw [statisticalHellingerDistance_sq_eq_integral hP hR,
      statisticalHellingerDistance_sq_eq_integral hP hQ,
      statisticalHellingerDistance_sq_eq_integral hQ hR,
      ← integral_const_mul,
      ← integral_add (f := fun x ↦ A x ^ 2) (g := fun x ↦ 2 * (A x * B x)) hA.integrable_sq
        (hA.integrable_mul hB |>.const_mul 2),
      ← integral_add (f := fun x ↦ A x ^ 2 + 2 * (A x * B x)) (g := fun x ↦ B x ^ 2)
        (hA.integrable_sq.add (hA.integrable_mul hB |>.const_mul 2)) hB.integrable_sq]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      dsimp [A, B]
      ring
  have hPR : 0 ≤ statisticalHellingerDistance P R := Real.sqrt_nonneg _
  have hPQ : 0 ≤ statisticalHellingerDistance P Q := Real.sqrt_nonneg _
  have hQR : 0 ≤ statisticalHellingerDistance Q R := Real.sqrt_nonneg _
  have hcs' := (le_abs_self (∫ x, A x * B x ∂μ)).trans hcs
  nlinarith

/-- Triangle inequality for Hellinger distance among probability measures. Densities are taken
with respect to the dominating measure `P + Q + R`. -/
theorem statisticalHellingerDistance_triangle {X : Type*} [MeasurableSpace X]
    (P Q R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] :
    statisticalHellingerDistance P R ≤
      statisticalHellingerDistance P Q + statisticalHellingerDistance Q R :=
  statisticalHellingerDistance_triangle_of_hasDensity (μ := P + Q + R)
    (hasDensity_toReal_rnDeriv (Measure.absolutelyContinuous_of_le
      (Measure.le_add_right (Measure.le_add_right le_rfl))))
    (hasDensity_toReal_rnDeriv (Measure.absolutelyContinuous_of_le
      (Measure.le_add_right (Measure.le_add_left le_rfl))))
    (hasDensity_toReal_rnDeriv (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)))

end CKSD
