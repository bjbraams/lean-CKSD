module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import CKSD.Inference.Moments
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import Mathlib.Probability.Independence.Integration

/-!
# LinearModels: CausalAndSurvey

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
The finite-design moment identities use Mathlib's indicator and finite-sum integrals
and its second-moment formula for variance. The Wald-ratio identity uses Mathlib's
`IndepFun.integral_fun_mul_eq_mul_integral` for the instrument strata.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- Every real statistic on the finite sample space has finite moments under a finite design. -/
theorem memLp_finite_sample {N : ℕ} (P : Measure (Finset (Fin N))) [IsFiniteMeasure P]
    (f : Finset (Fin N) → ℝ) (p : ℝ≥0∞) : MemLp f p P := by
  exact eLpNorm_lt_top_of_finite (measurable_of_countable f).aestronglyMeasurable

/-- Integrating a sum over a random sample uses the first-order inclusion probabilities. -/
theorem integral_sample_sum {N : ℕ} (P : Measure (Finset (Fin N))) [IsFiniteMeasure P]
    (b : Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, b i ∂P) = ∑ i, P.real {s | i ∈ s} * b i := by
  classical
  have hfun : (fun s : Finset (Fin N) ↦ ∑ i ∈ s, b i) =
      (fun s ↦ ∑ i, if i ∈ s then b i else 0) := by
    funext s
    simp
  rw [hfun, integral_finsetSum _ (fun i _ ↦ (memLp_finite_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul] using
    (integral_indicator_const (μ := P) (b i)
      (Set.to_countable {s : Finset (Fin N) | i ∈ s}).measurableSet)

/-- Integrating a double sum over a random sample uses joint inclusion probabilities. -/
theorem integral_sample_pair_sum {N : ℕ} (P : Measure (Finset (Fin N))) [IsFiniteMeasure P]
    (b : Fin N → Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, ∑ j ∈ s, b i j ∂P) =
      ∑ i, ∑ j, P.real {s | i ∈ s ∧ j ∈ s} * b i j := by
  classical
  have hfun : (fun s : Finset (Fin N) ↦ ∑ i ∈ s, ∑ j ∈ s, b i j) =
      (fun s ↦ ∑ i, ∑ j, if i ∈ s ∧ j ∈ s then b i j else 0) := by
    funext s
    simp only [ite_and]
    simp
  rw [hfun, integral_finsetSum _ (fun i _ ↦ (memLp_finite_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ (memLp_finite_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul] using
    (integral_indicator_const (μ := P) (b i j)
      (Set.to_countable {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}).measurableSet)

/-- GAPS 105.46, Neyman's exact design variance in a completely randomized experiment. -/
theorem randomized_treatment_difference_mean_and_variance {N : ℕ} (n₁ n₀ : ℕ) (hn : n₁ + n₀ = N)
    (h₁ : 0 < n₁) (h₀ : 0 < n₀) (y₁ y₀ : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y₁ i) / n₁ - (∑ i ∈ sᶜ, y₀ i) / n₀;
    (∫ s, T s ∂simpleRandomSampleDesign N n₁) = populationMean (y₁ - y₀) ∧
      variance (simpleRandomSampleDesign N n₁) T = populationVariance y₁ / n₁ + populationVariance y₀ / n₀ -
        populationVariance (y₁ - y₀) / N := by
  sorry

/-- GAPS 105.47, finite-stratum potential-outcome identification under mean ignorability. -/
theorem treatment_effect_identification_of_conditional_independence
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Bool → Ω → ℝ)
    (hY : ∀ a, Integrable (Y a) P) (a : Bool) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e := fun x ↦ P.real {ω | X ω = x ∧ A ω = a} / p x;
    let m := fun x ↦ (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) / (p x * e x);
    ∀ (hp : ∀ x, 0 < p x),
    ∀ (he : ∀ x, 0 < e x),
    ∀ (hign : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) =
      e x * ∫ ω in {ω | X ω = x}, Y a ω ∂P),
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

/-- GAPS 105.49, finite-stratum double-robustness bias identity.
The causal identification and cross-fitting conclusions require the additional
frameworks described in the source; this is the observable-moment identity. -/
theorem doubly_robust_bias_identity {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : Integrable Y P)
    (m₁ m₀ a₁ a₀ e : Fin k → ℝ) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e₀ := fun x ↦ P.real {ω | X ω = x ∧ A ω = true} / p x;
    ∀ (hp : ∀ x, 0 < p x),
    ∀ (he : ∀ x, e x ∈ Ioo 0 1),
    ∀ (hcond₁ : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = true}, Y ω ∂P) = p x * e₀ x * m₁ x),
    ∀ (hcond₀ : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = false}, Y ω ∂P) = p x * (1 - e₀ x) * m₀ x),
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
    rw [Set.diff_eq, hset₁, hset₀] at h
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

/-- GAPS 105.50: the Wald ratio identifies the complier average effect. -/
theorem local_average_treatment_effect_eq_wald_ratio {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → Bool) (A : Bool → Ω → Bool)
    (Y : Bool → Ω → ℝ) (hZ : Measurable Z) (hA : ∀ z, Measurable (A z))
    (hY : ∀ a, Integrable (Y a) P)
    (hind : IndepFun (fun ω ↦ (Y false ω, Y true ω, A false ω, A true ω)) Z P)
    (hmon : ∀ᵐ ω ∂P, A false ω = true → A true ω = true)
    (hp : ∀ z : Bool, 0 < P {ω | Z ω = z}) :
    let obsA := fun ω ↦ if A (Z ω) ω then (1 : ℝ) else 0;
    let obsY := fun ω ↦ Y (A (Z ω) ω) ω;
    let mean := fun (f : Ω → ℝ) z ↦ (∫ ω in {ω | Z ω = z}, f ω ∂P) / P.real {ω | Z ω = z};
    ∀ (hstage : mean obsA true ≠ mean obsA false),
    let C := {ω | A false ω = false ∧ A true ω = true};
    (mean obsY true - mean obsY false) / (mean obsA true - mean obsA false) =
      (∫ ω in C, Y true ω - Y false ω ∂P) / P.real C := by
  intro obsA obsY mean _ C
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

/-- GAPS 105.72, Horvitz–Thompson unbiasedness and exact design variance. -/
theorem horvitz_thompson_mean_and_variance
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i, 0 < pi i),
    let T := fun s : Finset (Fin N) ↦ ∑ i ∈ s, y i / pi i;
    (∫ s, T s ∂P) = ∑ i, y i ∧
      variance P T = ∑ i, ∑ j, (pij i j - pi i * pi j) * y i * y j / (pi i * pi j) := by
  classical
  dsimp only
  intro hp
  let pi := fun i ↦ P.real {s : Finset (Fin N) | i ∈ s}
  let pij := fun i j ↦ P.real {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}
  have hpi0 : ∀ i, pi i ≠ 0 := fun i ↦ (hp i).ne'
  let T := fun s : Finset (Fin N) ↦ ∑ i ∈ s, y i / pi i
  have hmean : (∫ s, T s ∂P) = ∑ i, y i := by
    rw [integral_sample_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_cancel₀ (y i) (hp i).ne'
  refine ⟨hmean, ?_⟩
  rw [variance_eq_mathlib P T (measurable_of_countable _).aemeasurable,
    ProbabilityTheory.variance_eq_sub (memLp_finite_sample P T 2), hmean]
  have hsquare : T ^ 2 =
      (fun s ↦ ∑ i ∈ s, ∑ j ∈ s, y i / pi i * (y j / pi j)) := by
    funext s
    simp only [T, pow_two, Pi.mul_apply, Finset.sum_mul_sum]
  rw [hsquare, integral_sample_pair_sum]
  have hpop : (∑ i, y i) ^ 2 = ∑ i, ∑ j, y i * y j := by
    simp only [pow_two, Finset.sum_mul_sum]
  rw [hpop, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change pij i j * (y i / pi i * (y j / pi j)) - y i * y j = _
  change _ = (pij i j - pi i * pi j) * y i * y j / (pi i * pi j)
  field_simp [hpi0 i, hpi0 j]
  <;> ring

/-- GAPS 105.72, unbiased estimation of the Horvitz–Thompson design variance. -/
theorem horvitz_thompson_variance_estimator_unbiased
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i j, 0 < pij i j),
    (∫ s, ∑ i ∈ s, ∑ j ∈ s,
      (pij i j - pi i * pi j) / pij i j * y i * y j / (pi i * pi j) ∂P) =
      variance P (fun s ↦ ∑ i ∈ s, y i / pi i) := by
  classical
  dsimp only
  intro hp
  have hpi : ∀ i, 0 < P.real {s : Finset (Fin N) | i ∈ s} := by
    intro i
    simpa only [and_self] using hp i i
  rw [integral_sample_pair_sum, (horvitz_thompson_mean_and_variance P y hpi).2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(hp i j).ne']

/-- GAPS 105.72, Sen–Yates–Grundy identity for a fixed-size sampling design. -/
theorem horvitz_thompson_variance_eq_sen_yates_grundy
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (n : ℕ) (hn : ∀ᵐ s ∂P, s.card = n) (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i, 0 < pi i),
    variance P (fun s ↦ ∑ i ∈ s, y i / pi i) =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, (pij i j - pi i * pi j) * (y i / pi i - y j / pi j) ^ 2 := by
  classical
  dsimp only
  intro hp
  let pi := fun i ↦ P.real {s : Finset (Fin N) | i ∈ s}
  let pij := fun i j ↦ P.real {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}
  let c := fun i j ↦ pij i j - pi i * pi j
  let w := fun i ↦ y i / pi i
  have htotal : ∑ i, pi i = (n : ℝ) := by
    calc
      _ = ∫ s, ∑ i ∈ s, (1 : ℝ) ∂P := by
        simpa only [mul_one] using (integral_sample_sum P (fun _ ↦ (1 : ℝ))).symm
      _ = ∫ _, (n : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hn] with s hs
        simp [hs]
      _ = _ := by simp
  have hrow : ∀ i, ∑ j, pij i j = (n : ℝ) * pi i := by
    intro i
    calc
      _ = ∫ s, ∑ j : Fin N, if i ∈ s ∧ j ∈ s then (1 : ℝ) else 0 ∂P := by
        rw [integral_finsetSum _
          (fun j _ ↦ (memLp_finite_sample P _ 1).integrable le_rfl)]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul, mul_one] using
          (integral_indicator_const (μ := P) (1 : ℝ)
            (Set.to_countable {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}).measurableSet).symm
      _ = ∫ s, if i ∈ s then (n : ℝ) else 0 ∂P := by
        apply integral_congr_ae
        filter_upwards [hn] with s hs
        by_cases hi : i ∈ s <;> simp [hi, hs]
      _ = _ := by
        simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul, mul_comm] using
          (integral_indicator_const (μ := P) (n : ℝ)
            (Set.to_countable {s : Finset (Fin N) | i ∈ s}).measurableSet)
  have hrow0 : ∀ i, ∑ j, c i j = 0 := by
    intro i
    simp only [c, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, htotal]
    ring
  have hsym : ∀ i j, c i j = c j i := by
    intro i j
    simp only [c, pij, and_comm, mul_comm]
  have hcol0 : ∀ j, ∑ i, c i j = 0 := by
    intro j
    simp_rw [hsym _ j]
    exact hrow0 j
  have hfirst : (∑ i, ∑ j, w i ^ 2 * c i j) = 0 := by
    simp_rw [← Finset.mul_sum, hrow0, mul_zero]
    simp
  have hsecond : (∑ i, ∑ j, w j ^ 2 * c i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol0, mul_zero]
    simp
  have hdiff : (∑ i, ∑ j, c i j * (w i - w j) ^ 2) =
      -2 * ∑ i, ∑ j, c i j * w i * w j := by
    have hexpand : ∀ i j, c i j * (w i - w j) ^ 2 =
        w i ^ 2 * c i j + w j ^ 2 * c i j - 2 * (c i j * w i * w j) := by
      intro i j
      ring
    simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    simp_rw [← Finset.mul_sum]
    ring
  have hvar : variance P (fun s ↦ ∑ i ∈ s, y i / pi i) =
      ∑ i, ∑ j, c i j * w i * w j := by
    rw [(horvitz_thompson_mean_and_variance P y hp).2]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [c, w, pi, pij, div_eq_mul_inv, mul_inv_rev]
    ring
  change variance P (fun s ↦ ∑ i ∈ s, y i / pi i) =
    -(1 / 2 : ℝ) * ∑ i, ∑ j, c i j * (w i - w j) ^ 2
  rw [hvar, hdiff]
  ring

/-- GAPS 105.73, finite-population correction for a simple random sample mean. -/
theorem simple_random_sample_mean_and_variance
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (y : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y i) / n;
    (∫ s, T s ∂simpleRandomSampleDesign N n) = populationMean y ∧
      variance (simpleRandomSampleDesign N n) T = (1 - (n : ℝ) / N) * populationVariance y / n := by
  sorry

/-- GAPS 105.73, the continuous Neyman allocation optimization. -/
theorem neyman_allocation_optimal {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (n : ℝ) (hn : 0 < n) (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hxsum : ∑ i, x i = n) :
    (∑ i, a i) ^ 2 / n ≤ ∑ i, a i ^ 2 / x i ∧
      ((∑ i, a i) ^ 2 / n = ∑ i, a i ^ 2 / x i ↔
        ∀ i, x i = n * a i / ∑ j, a j) := by
  classical
  let S := ∑ i, a i
  have hn0 : n ≠ 0 := hn.ne'
  have hx0 : ∀ i, x i ≠ 0 := fun i ↦ (hx i).ne'
  have hS : 0 < S := by
    by_cases hk : k = 0
    · subst k
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hxsum
      linarith
    · letI : NeZero k := ⟨hk⟩
      exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hS0 : S ≠ 0 := hS.ne'
  let q := fun i ↦ (a i - (S / n) * x i) ^ 2 / x i
  have hq : ∀ i, 0 ≤ q i := fun i ↦ div_nonneg (sq_nonneg _) (hx i).le
  have hid : (∑ i, q i) = (∑ i, a i ^ 2 / x i) - S ^ 2 / n := by
    have hterm : ∀ i, q i = a i ^ 2 / x i - (2 * S / n) * a i +
        (S / n) ^ 2 * x i := by
      intro i
      dsimp [q]
      field_simp [hn0, hx0 i]
      <;> ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    change (∑ i, a i ^ 2 / x i) - (2 * S / n) * S + (S / n) ^ 2 *
      (∑ i, x i) = _
    rw [hxsum]
    field_simp
    <;> ring
  have hbound : S ^ 2 / n ≤ ∑ i, a i ^ 2 / x i := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hq i)
    rw [hid] at this
    linarith
  refine ⟨hbound, ?_⟩
  constructor
  · intro heq i
    have hz : ∑ j, q j = 0 := by rw [hid, ← heq]; ring
    have hqi : q i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hq j)).mp hz i (Finset.mem_univ i)
    have hi : a i - (S / n) * x i = 0 := by
      have : (a i - (S / n) * x i) ^ 2 = 0 :=
        (div_eq_zero_iff.mp hqi).resolve_right (hx0 i)
      exact sq_eq_zero_iff.mp this
    dsimp [S] at hS0 ⊢
    apply (eq_div_iff hS0).mpr
    have hi' : a i * n - S * x i = 0 := by
      have := (div_eq_zero_iff.mp (show (a i * n - S * x i) / n = 0 by
        convert hi using 1 <;> field_simp <;> ring)).resolve_right hn0
      exact this
    dsimp [S] at hi'
    nlinarith
  · intro heq
    have hz : ∑ i, q i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      dsimp [q]
      rw [heq i]
      change (a i - (S / n) * (n * a i / S)) ^ 2 / _ = 0
      have : a i - (S / n) * (n * a i / S) = 0 := by
        field_simp
        <;> ring
      rw [this]
      simp
    rw [hid] at hz
    linarith


end CKSD
