module

public import CKSD.LinearModels.CausalEfficiency
public import Mathlib.Probability.Independence.Integration


/-!
# Identification of causal effects from observational and instrumental data

Potential outcomes `Y a` (for a binary treatment `a`) are ordinary random variables on the
sample space; the observed outcome is `Y (A ω) ω`. Covariates take finitely many values, so that
conditional means and probabilities given a covariate stratum are quotients of integrals.

## Main definitions

* `CKSD.instrumentStratumMean`: the mean of a variable on an instrument stratum `{Z = z}`.

## Main results

* `CKSD.integral_potential_outcome_eq_sum_stratum_outcome_mean`,
  `CKSD.integral_potential_outcome_eq_integral_div_propensity`: under mean ignorability and
  overlap, the mean potential outcome is given by the adjustment formula and by inverse
  propensity weighting (GAPS 105.47).
* `CKSD.integral_treatment_effect_influence_sub_eq_sum_mul`: the bias of the augmented inverse
  probability weighted functional is a product of the outcome-regression and propensity errors
  (double robustness, GAPS 105.49).
* `CKSD.wald_ratio_eq_complier_average_effect`: under instrument independence and
  monotonicity, the Wald ratio is the average treatment effect on compliers (Imbens–Angrist,
  GAPS 105.50). Its proof uses Mathlib's `IndepFun.integral_fun_mul_eq_mul_integral` for the
  instrument strata.

## References

* G. W. Imbens and J. D. Angrist, *Identification and estimation of local average treatment
  effects*, Econometrica 62 (1994).
* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, J. Amer. Statist. Assoc. 89 (1994).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CKSD

/-- Identification of a potential-outcome mean in finite strata, with the stratum masses,
propensities and outcome means as local definitions (both conclusions together). -/
private theorem integral_potential_outcome_aux
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure Ω) (X : Ω → ι) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Bool → Ω → ℝ)
    (hY : ∀ a, Integrable (Y a) P) (a : Bool) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e := fun x ↦ P.real {ω | X ω = x ∧ A ω = a} / p x;
    let m := fun x ↦ (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) / (p x * e x);
    (∀ x, 0 < p x) →
    (∀ x, 0 < e x) →
    (∀ x, (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) =
      e x * ∫ ω in {ω | X ω = x}, Y a ω ∂P) →
    (∫ ω, Y a ω ∂P) = ∑ x, p x * m x ∧
      (∫ ω, Y a ω ∂P) = ∫ ω, (if A ω = a then Y (A ω) ω else 0) / e (X ω) ∂P := by
  intro p e m hp he hign
  have hXs : ∀ x, MeasurableSet {ω | X ω = x} := fun x ↦ hX (measurableSet_singleton x)
  have hAs : MeasurableSet {ω | A ω = a} := hA (measurableSet_singleton a)
  have hU : (⋃ x, {ω | X ω = x}) = univ := by
    ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun x ↦ {ω | X ω = x}) := fun x y hxy ↦
    disjoint_left.2 fun ω (hx : X ω = x) (hy : X ω = y) ↦ hxy (hx.symm.trans hy)
  -- the partition of the mean of `Y a` by the strata
  have hpart : ∀ f : Ω → ℝ, (∀ x, IntegrableOn f {ω | X ω = x} P) →
      (∫ ω, f ω ∂P) = ∑ x, ∫ ω in {ω | X ω = x}, f ω ∂P := by
    intro f hf
    rw [← integral_iUnion_fintype hXs hdisj hf, hU, Measure.restrict_univ]
  have hstrat : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) / e x =
      ∫ ω in {ω | X ω = x}, Y a ω ∂P := by
    intro x
    rw [hign x]
    field_simp [(he x).ne']
  refine ⟨?_, ?_⟩
  · rw [hpart _ fun x ↦ (hY a).integrableOn]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← hstrat x]
    simp only [m]
    field_simp [(hp x).ne', (he x).ne']
  · -- on each stratum the weighted integrand is a multiple of an indicator
    have hloc : ∀ x, EqOn (fun ω ↦ (if A ω = a then Y (A ω) ω else 0) / e (X ω))
        (fun ω ↦ (e x)⁻¹ * Set.indicator {ω | A ω = a} (Y a) ω) {ω | X ω = x} := by
      intro x ω hω
      simp only [mem_ofPred_eq] at hω
      by_cases h : A ω = a
      · simp [h, hω, div_eq_inv_mul]
      · simp [h]
    have hint : ∀ x, IntegrableOn (fun ω ↦ (if A ω = a then Y (A ω) ω else 0) / e (X ω))
        {ω | X ω = x} P := by
      intro x
      refine IntegrableOn.congr_fun ?_ (hloc x).symm (hXs x)
      exact (((hY a).indicator hAs).const_mul _).integrableOn
    rw [hpart _ hint, hpart _ fun x ↦ (hY a).integrableOn]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [setIntegral_congr_fun (hXs x) (hloc x), integral_const_mul,
      setIntegral_indicator hAs, ← hstrat x, div_eq_inv_mul]
    rfl

/-- The double-robustness bias identity in finite strata, with the stratum masses and
propensities as local definitions. -/
private theorem integral_treatment_effect_influence_aux {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ι) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : Integrable Y P)
    (m₁ m₀ a₁ a₀ e : ι → ℝ) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e₀ := fun x ↦ P.real {ω | X ω = x ∧ A ω = true} / p x;
    (∀ x, 0 < p x) →
    (∀ x, e x ∈ Ioo 0 1) →
    (∀ x, (∫ ω in {ω | X ω = x ∧ A ω = true}, Y ω ∂P) = p x * e₀ x * m₁ x) →
    (∀ x, (∫ ω in {ω | X ω = x ∧ A ω = false}, Y ω ∂P) = p x * (1 - e₀ x) * m₀ x) →
    (∫ ω, a₁ (X ω) - a₀ (X ω) +
      (if A ω then (Y ω - a₁ (X ω)) / e (X ω)
        else -(Y ω - a₀ (X ω)) / (1 - e (X ω))) ∂P) -
      (∑ x, p x * (m₁ x - m₀ x)) =
      ∑ x, p x * (e x - e₀ x) * ((a₁ x - m₁ x) / e x + (a₀ x - m₀ x) / (1 - e x)) := by
  intro p e₀ hp he hcond₁ hcond₀
  have hXs : ∀ x, MeasurableSet {ω | X ω = x} := fun x ↦ hX (measurableSet_singleton x)
  have hAs : MeasurableSet {ω | A ω = true} := hA (measurableSet_singleton true)
  have hU : (⋃ x, {ω | X ω = x}) = univ := by
    ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun x ↦ {ω | X ω = x}) := fun x y hxy ↦
    disjoint_left.2 fun ω (hx : X ω = x) (hy : X ω = y) ↦ hxy (hx.symm.trans hy)
  have hpart : ∀ f : Ω → ℝ, (∀ x, IntegrableOn f {ω | X ω = x} P) →
      (∫ ω, f ω ∂P) = ∑ x, ∫ ω in {ω | X ω = x}, f ω ∂P := by
    intro f hf
    rw [← integral_iUnion_fintype hXs hdisj hf, hU, Measure.restrict_univ]
  set f : Ω → ℝ := fun ω ↦ a₁ (X ω) - a₀ (X ω) +
      (if A ω then (Y ω - a₁ (X ω)) / e (X ω) else -(Y ω - a₀ (X ω)) / (1 - e (X ω)))
  -- on a stratum the integrand is a constant plus two indicators
  have hloc : ∀ x, EqOn f (fun ω ↦ (a₁ x - a₀ x) +
      (Set.indicator {ω | A ω = true} (fun ω ↦ (Y ω - a₁ x) / e x) ω +
        Set.indicator {ω | A ω = true}ᶜ (fun ω ↦ -(Y ω - a₀ x) / (1 - e x)) ω))
      {ω | X ω = x} := by
    intro x ω hω
    simp only [mem_ofPred_eq] at hω
    by_cases h : A ω = true <;> simp [f, h, hω]
  have hg₁ : ∀ x, Integrable (fun ω ↦ (Y ω - a₁ x) / e x) P := fun x ↦
    (hY.sub (integrable_const _)).div_const _
  have hg₀ : ∀ x, Integrable (fun ω ↦ -(Y ω - a₀ x) / (1 - e x)) P := fun x ↦
    (hY.sub (integrable_const _)).neg.div_const _
  have hint : ∀ x, IntegrableOn f {ω | X ω = x} P := by
    intro x
    refine IntegrableOn.congr_fun ?_ (hloc x).symm (hXs x)
    exact ((integrable_const _).add (((hg₁ x).indicator hAs).add
      ((hg₀ x).indicator hAs.compl))).integrableOn
  -- the two treatment arms of a stratum
  have hset₁ : ∀ x, {ω | X ω = x} ∩ {ω | A ω = true} = {ω | X ω = x ∧ A ω = true} :=
    fun x ↦ rfl
  have hset₀ : ∀ x, {ω | X ω = x} ∩ {ω | A ω = true}ᶜ = {ω | X ω = x ∧ A ω = false} := by
    intro x; ext ω; simp
  have hmass₀ : ∀ x, P.real {ω | X ω = x ∧ A ω = false} = p x * (1 - e₀ x) := by
    intro x
    have h := measureReal_inter_add_sdiff (μ := P) (s := {ω | X ω = x}) hAs
    rw [Set.sdiff_eq, hset₁, hset₀] at h
    simp only [e₀]
    field_simp [(hp x).ne']
    simp only [p]
    linarith
  have hmass₁ : ∀ x, P.real {ω | X ω = x ∧ A ω = true} = p x * e₀ x := by
    intro x
    simp only [e₀]
    field_simp [(hp x).ne']
  have hstrat : ∀ x, (∫ ω in {ω | X ω = x}, f ω ∂P) =
      p x * (a₁ x - a₀ x) + (p x * e₀ x * m₁ x - a₁ x * (p x * e₀ x)) / e x -
        (p x * (1 - e₀ x) * m₀ x - a₀ x * (p x * (1 - e₀ x))) / (1 - e x) := by
    intro x
    have hi₁ : IntegrableOn (fun ω ↦ Set.indicator {ω | A ω = true}
        (fun ω ↦ (Y ω - a₁ x) / e x) ω) {ω | X ω = x} P :=
      ((hg₁ x).indicator hAs).integrableOn
    have hi₀ : IntegrableOn (fun ω ↦ Set.indicator {ω | A ω = true}ᶜ
        (fun ω ↦ -(Y ω - a₀ x) / (1 - e x)) ω) {ω | X ω = x} P :=
      ((hg₀ x).indicator hAs.compl).integrableOn
    have hi : IntegrableOn (fun ω ↦ Set.indicator {ω | A ω = true}
        (fun ω ↦ (Y ω - a₁ x) / e x) ω + Set.indicator {ω | A ω = true}ᶜ
        (fun ω ↦ -(Y ω - a₀ x) / (1 - e x)) ω) {ω | X ω = x} P := hi₁.add hi₀
    rw [setIntegral_congr_fun (hXs x) (hloc x), integral_add (integrable_const _) hi,
      integral_add hi₁ hi₀,
      setIntegral_indicator hAs, setIntegral_indicator hAs.compl, hset₁, hset₀,
      setIntegral_const, integral_div, integral_div, integral_neg,
      integral_sub hY.integrableOn (integrable_const _).integrableOn,
      integral_sub hY.integrableOn (integrable_const _).integrableOn,
      setIntegral_const, setIntegral_const, hcond₁, hcond₀, hmass₁, hmass₀]
    simp only [smul_eq_mul, p]
    ring
  rw [hpart f hint, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hstrat x]
  have h1 : e x ≠ 0 := (he x).1.ne'
  have h2 : 1 - e x ≠ 0 := by linarith [(he x).2]
  field_simp
  ring

/-- The Wald-ratio identity with the stratum means as local definitions. -/
private theorem wald_ratio_aux {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → Bool) (A : Bool → Ω → Bool)
    (Y : Bool → Ω → ℝ) (hZ : Measurable Z) (hA : ∀ z, Measurable (A z))
    (hY : ∀ a, Integrable (Y a) P)
    (hind : IndepFun (fun ω ↦ (Y false ω, Y true ω, A false ω, A true ω)) Z P)
    (hmon : ∀ᵐ ω ∂P, A false ω = true → A true ω = true)
    (hp : ∀ z : Bool, 0 < P {ω | Z ω = z}) :
    let obsA := fun ω ↦ if A (Z ω) ω then (1 : ℝ) else 0;
    let obsY := fun ω ↦ Y (A (Z ω) ω) ω;
    let mean := fun (f : Ω → ℝ) z ↦ (∫ ω in {ω | Z ω = z}, f ω ∂P) / P.real {ω | Z ω = z};
    let C := {ω | A false ω = false ∧ A true ω = true};
    (mean obsY true - mean obsY false) / (mean obsA true - mean obsA false) =
      (∫ ω in C, Y true ω - Y false ω ∂P) / P.real C := by
  intro obsA obsY mean C
  set W := fun ω ↦ (Y false ω, Y true ω, A false ω, A true ω)
  -- the potential treatment under instrument value `z`, read from `W`
  let sel : Bool → ℝ × ℝ × Bool × Bool → Bool := fun z w ↦ cond z w.2.2.2 w.2.2.1
  have hsel : ∀ z, Measurable (sel z) := by
    intro z; cases z
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hselW : ∀ z ω, sel z (W ω) = A z ω := by intro z ω; cases z <;> rfl
  have hZs : ∀ z, MeasurableSet {ω | Z ω = z} := fun z ↦ hZ (measurableSet_singleton z)
  -- independence turns a stratum integral of a function of `W` into a product
  have hstr : ∀ (z : Bool) (g : ℝ × ℝ × Bool × Bool → ℝ), Measurable g →
      AEStronglyMeasurable (fun ω ↦ g (W ω)) P →
      (∫ ω in {ω | Z ω = z}, g (W ω) ∂P) = P.real {ω | Z ω = z} * ∫ ω, g (W ω) ∂P := by
    intro z g hg hgW
    have hind' : IndepFun (fun ω ↦ g (W ω))
        (fun ω ↦ (fun b : Bool ↦ if b = z then (1 : ℝ) else 0) (Z ω)) P :=
      ProbabilityTheory.IndepFun.comp hind hg
        (measurable_of_countable (fun b : Bool ↦ if b = z then (1 : ℝ) else 0))
    have hind_eq : (fun ω ↦ (fun b : Bool ↦ if b = z then (1 : ℝ) else 0) (Z ω)) =
        Set.indicator {ω | Z ω = z} 1 := by
      ext ω; by_cases h : Z ω = z <;> simp [h]
    rw [hind_eq] at hind'
    have hmul := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind' hgW
      (measurable_const.indicator (hZs z)).aestronglyMeasurable
    rw [← integral_indicator (hZs z)]
    have : (fun ω ↦ Set.indicator {ω | Z ω = z} (fun ω ↦ g (W ω)) ω) =
        fun ω ↦ g (W ω) * Set.indicator {ω | Z ω = z} 1 ω := by
      ext ω; by_cases h : Z ω = z <;> simp [h]
    rw [this, hmul, integral_indicator_one (hZs z), mul_comm]
  have hAm : ∀ z, MeasurableSet {ω | A z ω = true} := fun z ↦ hA z (measurableSet_singleton _)
  -- outcome and treatment functions of `W` under instrument value `z`
  let g : Bool → ℝ × ℝ × Bool × Bool → ℝ := fun z w ↦ if sel z w = true then w.2.1 else w.1
  let h : Bool → ℝ × ℝ × Bool × Bool → ℝ := fun z w ↦ if sel z w = true then 1 else 0
  have hgm : ∀ z, Measurable (g z) := fun z ↦
    Measurable.ite ((hsel z) (measurableSet_singleton true)) measurable_snd.fst measurable_fst
  have hhm : ∀ z, Measurable (h z) := fun z ↦
    Measurable.ite ((hsel z) (measurableSet_singleton true)) measurable_const measurable_const
  have hgW : ∀ z, (fun ω ↦ g z (W ω)) = fun ω ↦ Set.indicator {ω | A z ω = true} (Y true) ω +
      Set.indicator {ω | A z ω = true}ᶜ (Y false) ω := by
    intro z; ext ω
    by_cases hz : A z ω = true <;> simp [g, hselW, hz, W]
  have hhW : ∀ z, (fun ω ↦ h z (W ω)) = Set.indicator {ω | A z ω = true} 1 := by
    intro z; ext ω
    by_cases hz : A z ω = true <;> simp [h, hselW, hz]
  have hgI : ∀ z, Integrable (fun ω ↦ g z (W ω)) P := by
    intro z; rw [hgW z]
    exact ((hY true).indicator (hAm z)).add ((hY false).indicator (hAm z).compl)
  have hhI : ∀ z, Integrable (fun ω ↦ h z (W ω)) P := by
    intro z; rw [hhW z]
    exact (integrable_const 1).indicator (hAm z)
  -- the stratum means are the means of the potential quantities
  have hmeanY : ∀ z, mean obsY z = ∫ ω, g z (W ω) ∂P := by
    intro z
    have hpos : 0 < P.real {ω | Z ω = z} := ENNReal.toReal_pos (hp z).ne' (measure_ne_top _ _)
    simp only [mean]
    rw [setIntegral_congr_fun (hZs z) (g := fun ω ↦ g z (W ω)) (fun ω hω ↦ by
      simp only [mem_ofPred_eq] at hω
      simp only [obsY, g, hselW, hω]
      by_cases hz : A z ω = true <;> simp [hz, W]), hstr z _ (hgm z) (hgI z).1]
    field_simp
  have hmeanA : ∀ z, mean obsA z = ∫ ω, h z (W ω) ∂P := by
    intro z
    have hpos : 0 < P.real {ω | Z ω = z} := ENNReal.toReal_pos (hp z).ne' (measure_ne_top _ _)
    simp only [mean]
    rw [setIntegral_congr_fun (hZs z) (g := fun ω ↦ h z (W ω)) (fun ω hω ↦ by
      simp only [mem_ofPred_eq] at hω
      simp only [obsA, h, hselW, hω]), hstr z _ (hhm z) (hhI z).1]
    field_simp
  have hCm : MeasurableSet C := (hA false (measurableSet_singleton false)).inter
    (hA true (measurableSet_singleton true))
  -- monotonicity removes the defiers
  have hnum : (∫ ω, g true (W ω) ∂P) - ∫ ω, g false (W ω) ∂P =
      ∫ ω in C, Y true ω - Y false ω ∂P := by
    rw [← integral_sub (hgI true) (hgI false), ← integral_indicator hCm]
    refine integral_congr_ae (hmon.mono fun ω hω ↦ ?_)
    simp only [g, hselW, C, Set.indicator, mem_ofPred_eq]
    cases h0 : A false ω <;> cases h1 : A true ω <;> simp_all [W]
  have hden : (∫ ω, h true (W ω) ∂P) - ∫ ω, h false (W ω) ∂P = P.real C := by
    rw [← integral_sub (hhI true) (hhI false), ← integral_indicator_one hCm]
    refine integral_congr_ae (hmon.mono fun ω hω ↦ ?_)
    simp only [h, hselW, C, Set.indicator, mem_ofPred_eq, Pi.one_apply]
    cases h0 : A false ω <;> cases h1 : A true ω <;> simp_all
  rw [hmeanY, hmeanY, hmeanA, hmeanA, hnum, hden]

/-- GAPS 105.47, finite-stratum potential-outcome identification under mean ignorability:
if every covariate stratum and every treatment stratum `{X = x, A = a}` has positive
probability and `E[Y(a) | X = x, A = a] = E[Y(a) | X = x]` (written without division), then
`E[Y(a)] = ∑ₓ P(X = x) E[Y(a) | X = x, A = a]` (the adjustment formula). -/
theorem integral_potential_outcome_eq_sum_stratum_outcome_mean
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure Ω) (X : Ω → ι) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Bool → Ω → ℝ)
    (hY : ∀ a, Integrable (Y a) P) (a : Bool)
    (hp : ∀ x, 0 < P.real {ω | X ω = x})
    (he : ∀ x, 0 < P.real (treatmentStratum X A x a))
    (hign : ∀ x, (∫ ω in treatmentStratum X A x a, Y a ω ∂P) =
      P.real (treatmentStratum X A x a) / P.real {ω | X ω = x} *
        ∫ ω in {ω | X ω = x}, Y a ω ∂P) :
    (∫ ω, Y a ω ∂P) = ∑ x, P.real {ω | X ω = x} * stratumOutcomeMean P X A (Y a) x a := by
  rw [(integral_potential_outcome_aux P X A hX hA Y hY a hp
    (fun x ↦ div_pos (he x) (hp x)) hign).1]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h₁ := (hp x).ne'
  have h₂ := (he x).ne'
  simp only [stratumOutcomeMean, treatmentStratum] at h₂ ⊢
  field_simp

/-- GAPS 105.47, inverse-propensity weighting: under the hypotheses of
`integral_potential_outcome_eq_sum_stratum_outcome_mean`, `E[Y(a)] = E[1{A = a} Y / e_a(X)]`
with the observed outcome `Y = Y(A)` and the stratum propensity
`e_a(x) = P(A = a | X = x)`. -/
theorem integral_potential_outcome_eq_integral_div_propensity
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure Ω) (X : Ω → ι) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Bool → Ω → ℝ)
    (hY : ∀ a, Integrable (Y a) P) (a : Bool)
    (hp : ∀ x, 0 < P.real {ω | X ω = x})
    (he : ∀ x, 0 < P.real (treatmentStratum X A x a))
    (hign : ∀ x, (∫ ω in treatmentStratum X A x a, Y a ω ∂P) =
      P.real (treatmentStratum X A x a) / P.real {ω | X ω = x} *
        ∫ ω in {ω | X ω = x}, Y a ω ∂P) :
    (∫ ω, Y a ω ∂P) = ∫ ω, (if A ω = a then Y (A ω) ω else 0) /
      (P.real (treatmentStratum X A (X ω) a) / P.real {ω' | X ω' = X ω}) ∂P :=
  (integral_potential_outcome_aux P X A hX hA Y hY a hp
    (fun x ↦ div_pos (he x) (hp x)) hign).2

/-- GAPS 105.49, finite-stratum double-robustness bias identity.
The causal identification and cross-fitting conclusions require the additional
frameworks described in the source; this is the observable-moment identity. For working
outcome regressions `a₁`, `a₀` and a working propensity `e` with values in `(0, 1)`, true
stratum outcome means `m₁`, `m₀` and true propensity `e₀ = stratumPropensity P X A`, the bias
of the augmented inverse-probability-weighted functional is
`∑ₓ P(X = x) (e(x) - e₀(x)) ((a₁ - m₁)(x) / e(x) + (a₀ - m₀)(x) / (1 - e(x)))`; it vanishes
when either the outcome regressions or the propensity are correct. -/
theorem integral_treatment_effect_influence_sub_eq_sum_mul
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ι) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : Integrable Y P)
    (m₁ m₀ a₁ a₀ e : ι → ℝ) (hp : ∀ x, 0 < P.real {ω | X ω = x})
    (he : ∀ x, e x ∈ Ioo 0 1)
    (hcond₁ : ∀ x, (∫ ω in treatmentStratum X A x true, Y ω ∂P) =
      P.real {ω | X ω = x} * stratumPropensity P X A x * m₁ x)
    (hcond₀ : ∀ x, (∫ ω in treatmentStratum X A x false, Y ω ∂P) =
      P.real {ω | X ω = x} * (1 - stratumPropensity P X A x) * m₀ x) :
    (∫ ω, treatmentEffectInfluence a₀ a₁ e 0 (X ω) (A ω) (Y ω) ∂P) -
        (∑ x, P.real {ω | X ω = x} * (m₁ x - m₀ x)) =
      ∑ x, P.real {ω | X ω = x} * (e x - stratumPropensity P X A x) *
        ((a₁ x - m₁ x) / e x + (a₀ x - m₀ x) / (1 - e x)) := by
  simpa only [treatmentEffectInfluence, sub_zero, stratumPropensity, treatmentStratum] using
    integral_treatment_effect_influence_aux P X A hX hA Y hY m₁ m₀ a₁ a₀ e hp he hcond₁ hcond₀

/-- The mean of `f` on the instrument stratum `{Z = z}`. -/
def instrumentStratumMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → Bool)
    (f : Ω → ℝ) (z : Bool) : ℝ :=
  (∫ ω in {ω | Z ω = z}, f ω ∂P) / P.real {ω | Z ω = z}

/-- GAPS 105.50: the Wald ratio identifies the complier average effect. For a binary
instrument `Z` independent of the potential treatments `A z` and potential outcomes `Y a`,
with monotonicity `A 0 ≤ A 1` and both instrument values of positive probability, the ratio of
the instrument-stratum contrasts of the observed outcome `Y(A(Z))` and of the observed
treatment `A(Z)` equals `E[Y 1 - Y 0 | A 0 = 0, A 1 = 1]`, the average effect on compliers.
When the first-stage contrast vanishes both sides are zero, by the convention `x / 0 = 0`. -/
theorem wald_ratio_eq_complier_average_effect {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → Bool) (A : Bool → Ω → Bool)
    (Y : Bool → Ω → ℝ) (hZ : Measurable Z) (hA : ∀ z, Measurable (A z))
    (hY : ∀ a, Integrable (Y a) P)
    (hind : IndepFun (fun ω ↦ (Y false ω, Y true ω, A false ω, A true ω)) Z P)
    (hmon : ∀ᵐ ω ∂P, A false ω = true → A true ω = true)
    (hp : ∀ z : Bool, 0 < P {ω | Z ω = z}) :
    (instrumentStratumMean P Z (fun ω ↦ Y (A (Z ω) ω) ω) true -
        instrumentStratumMean P Z (fun ω ↦ Y (A (Z ω) ω) ω) false) /
      (instrumentStratumMean P Z (fun ω ↦ if A (Z ω) ω then 1 else 0) true -
        instrumentStratumMean P Z (fun ω ↦ if A (Z ω) ω then 1 else 0) false) =
      (∫ ω in {ω | A false ω = false ∧ A true ω = true}, Y true ω - Y false ω ∂P) /
        P.real {ω | A false ω = false ∧ A true ω = true} :=
  wald_ratio_aux P Z A Y hZ hA hY hind hmon hp

end CKSD
