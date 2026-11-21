/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli, Gaëtan Serré, Bastiaan J Braams
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import TauCeti.InformationTheory.KullbackLeibler.ChainRule

/-!
# Relative entropy of products and binary laws

Relative entropy is additive over finite products of probability measures. For a Bernoulli
law with parameter `p` relative to an interior parameter `q`, it is
`p log(p/q) + (1-p) log((1-p)/(1-q))`. We use Mathlib's convention `log 0 = 0`
for the real-valued binary formula.

The finite-product induction follows Statlib's `Divergence.KullbackLeibler.CondKL`, with
TauCeti's two-factor chain rule. The Bernoulli calculation follows Rémy Degenne's
`ForMathlib.InformationTheory.KullbackLeibler.Bernoulli` and the density calculation in
Statlib's `ForMathlib.Probability.Distributions.Bernoulli`.
-/

@[expose] public noncomputable section

open MeasureTheory InformationTheory ProbabilityTheory Real unitInterval
open scoped ENNReal NNReal

namespace CKSD

/-- Relative entropy is invariant under a measurable change of coordinates. -/
private theorem klDiv_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : X ≃ᵐ Y) :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q e.measurable)
  simpa only [e.map_symm_map] using klDiv_map_le (P.map e) (Q.map e) e.symm.measurable

/-- Relative entropy of two finite products of probability laws is the sum over coordinates. -/
theorem klDiv_pi {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {P Q : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {X : ι → Type _}
    [∀ i, MeasurableSpace (X i)] {P Q : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)],
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i)) ?_ ?_ ?_ ι
  · intro ι ι' hι' e ih X _ P Q _ _
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    have hp := Measure.pi_map_piCongrLeft e P
    have hq := Measure.pi_map_piCongrLeft e Q
    rw [← hp, ← hq, klDiv_map_equiv, ih]
    exact Fintype.sum_equiv e (fun i ↦ klDiv (P (e i)) (Q (e i)))
      (fun i ↦ klDiv (P i) (Q i)) (fun _ ↦ rfl)
  · intro X _ P Q _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, klDiv_self, Finset.univ_eq_empty,
      Finset.sum_empty]
  · intro ι _ ih X _ P Q _ _
    have hp := Measure.pi_map_piOptionEquivProd P
    have hq := Measure.pi_map_piOptionEquivProd Q
    rw [← hp, ← hq, klDiv_map_equiv, TauCeti.klDiv_prod_prod, ih,
      Fintype.sum_option, add_comm]

/-- For identical coordinates, product relative entropy is the coordinate value times the count. -/
theorem klDiv_pi_const {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {P Q : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv (Measure.pi fun _ : ι ↦ P) (Measure.pi fun _ : ι ↦ Q) =
      Fintype.card ι * klDiv P Q := by
  rw [klDiv_pi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The real-valued relative entropy formula for binary parameters, used for interior `q`. -/
def bernoulliKullbackLeibler (p q : ℝ) : ℝ :=
  p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Expand the ratio inside a logarithm multiplied by its numerator, including zero. -/
private theorem mul_log_div {a b : ℝ} (hb : b ≠ 0) :
    a * log (a / b) = a * (log a - log b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]

/-- The binary divergence in terms of binary entropy, for `q ≠ 0, 1`. -/
theorem bernoulliKullbackLeibler_eq_neg_binEntropy_sub {p q : ℝ} (hq0 : q ≠ 0)
    (hq1 : q ≠ 1) :
    bernoulliKullbackLeibler p q = -binEntropy p - p * log q - (1 - p) * log (1 - q) := by
  rw [bernoulliKullbackLeibler, mul_log_div hq0, mul_log_div (sub_ne_zero.mpr hq1.symm)]
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def]
  ring

/-- A unit-interval weight viewed as an extended nonnegative real. -/
private theorem coe_toNNReal_eq_ofReal (p : I) :
    (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal p := by
  rw [ENNReal.ofReal, show Real.toNNReal p = unitInterval.toNNReal p from
    Real.toNNReal_of_nonneg p.2.1]

/-- The density of one binary law relative to a law with positive mass at both outcomes. -/
private theorem bernoulliMeasure_eq_withDensity {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] {x y : X} (hxy : x ≠ y)
    (p : I) {q : I} (hq0 : (0 : ℝ) < q) (hq1 : (q : ℝ) < 1) :
    Ber(x, y, p) = Ber(x, y, q).withDensity
      (fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, withDensity_add_measure]
  simp_rw [ENNReal.smul_def]
  rw [withDensity_smul_measure, withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
    ite_eq_left rfl, ite_eq_right hxy.symm, smul_smul, smul_smul]
  simp only [coe_toNNReal_eq_ofReal, coe_symm_eq]
  congr 1 <;> congr 1
  · rw [← ENNReal.ofReal_mul hq0.le]
    congr 1
    field_simp
  · rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hq1.le)]
    congr 1
    field_simp

/-- Relative entropy of two binary laws with distinct outcomes and interior reference parameter. -/
theorem klDiv_bernoulliMeasure_eq_bernoulliKullbackLeibler {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {x y : X} (hxy : x ≠ y)
    (p : I) {q : I} (hq0 : (0 : ℝ) < q) (hq1 : (q : ℝ) < 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (bernoulliKullbackLeibler p q) := by
  classical
  have hD := bernoulliMeasure_eq_withDensity hxy p hq0 hq1
  have hac : Ber(x, y, p) ≪ Ber(x, y, q) := hD ▸ withDensity_absolutelyContinuous _ _
  have hr : Ber(x, y, p).rnDeriv Ber(x, y, q) =ᵐ[Ber(x, y, q)]
      fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q)) := by
    rw [hD]
    exact Measure.rnDeriv_withDensity _
      (Measurable.ite (measurableSet_singleton x) measurable_const measurable_const)
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.mpr p.2.2
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.mpr hq1
  rw [klDiv_eq_lintegral_klFun_of_ac hac, lintegral_congr_ae (hr.mono fun z hz ↦ by rw [hz])]
  rw [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.smul_def, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
    coe_toNNReal_eq_ofReal, coe_toNNReal_eq_ofReal, coe_symm_eq, smul_eq_mul, smul_eq_mul]
  simp only [ite_true, ite_eq_right hxy.symm, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg hp1 hq1'.le)]
  rw [← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_mul hq1'.le, ← ENNReal.ofReal_add
      (mul_nonneg hq0.le (klFun_nonneg (div_nonneg hp0 hq0.le)))
      (mul_nonneg hq1'.le (klFun_nonneg (div_nonneg hp1 hq1'.le)))]
  congr 1
  simp only [klFun, bernoulliKullbackLeibler]
  field_simp
  ring

/-- Nonnegativity of relative entropy for binary probabilities. -/
theorem bernoulliKullbackLeibler_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ bernoulliKullbackLeibler p q := by
  have lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * log (a / b) := by
    rcases ha.eq_or_lt with rfl | ha
    · simp [hb.le]
    calc
      a - b = a * (1 - (a / b)⁻¹) := by field_simp
      _ ≤ a * log (a / b) := mul_le_mul_of_nonneg_left
        (one_sub_inv_le_log_of_pos (div_pos ha hb)) ha.le
  exact (show 0 ≤ (p - q) + ((1 - p) - (1 - q)) by linarith).trans
    (add_le_add (lower hp0 hq0) (lower (sub_nonneg.mpr hp1) (sub_pos.mpr hq1)))

end CKSD
