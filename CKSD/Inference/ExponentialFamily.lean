module

public import CKSD.Inference.Model
public import CKSD.Inference.Factorization
public import CKSD.Inference.LaplaceDeterminacy
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import CKSD.Inference.LogPartition

/-!
# Sufficiency and natural exponential families

## Main definitions

* `CKSD.RealExponentialFamily`: a regular scalar natural exponential family, with
  `RealExponentialFamily.cumulant` and `RealExponentialFamily.law`.

## Main results

* `CKSD.isSufficientStatistic_iff_exists_factorization`: the factorization theorem (GAPS 101.1).
* `CKSD.isSufficientStatistic_likelihoodRatio_and_ae_eq_comp`: the likelihood-ratio statistic is
  minimal sufficient (GAPS 101.2).
* `CKSD.convex_naturalParameterSpace` and `CKSD.analyticOnNhd_logPartition_and_fderiv_eq_moments`:
  convexity of the natural parameter space, and analyticity and cumulant identities of the log
  partition function (GAPS 101.4).
* `CKSD.isCompleteStatistic_withDensity_exp_inner`: completeness of the natural statistic on a
  parameter set with nonempty interior (GAPS 101.5).
* `CKSD.exists_exponential_family_of_monotone_sufficient_statistics`: the Pitman–Koopman–Darmois
  theorem with monotone sufficient statistics (GAPS 101.6).

## Implementation notes

The completeness proof uses Laplace determinacy (`CKSD.measure_eq_of_integral_exp_inner_eq`)
and Mathlib's density and pushforward operations.

The analyticity and moment identities of the log partition function are proved in
`CKSD.Inference.LogPartition`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.1: factorization on a standard Borel sample space and an arbitrary measurable
statistic space. -/
theorem isSufficientStatistic_iff_exists_factorization
    [StandardBorelSpace X] [Nonempty X] [Nonempty Θ] (P : Θ → Measure X) (μ : Measure X) [SigmaFinite μ]
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S) (hT : Measurable T) :
    IsSufficientStatistic P T ↔ ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  refine ⟨exists_factorization_of_isSufficientStatistic P μ hP f hf T, ?_⟩
  rintro ⟨g, h, hg, -, -, hfac⟩
  exact isSufficientStatistic_of_factorization P μ hP f hf hT g h hg hfac

/-- GAPS 101.4, convexity part: the natural parameter space `{η | ∫ exp ⟪η, t⟫ dν(t) < ∞}` of a
measure `ν` on a real inner product space is convex (Hölder's inequality, here through the
convexity of `exp`). -/
theorem convex_naturalParameterSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) :
    Convex ℝ (naturalParameterSpace ν id) := by
  intro η hη ζ hζ a b ha hb hab
  replace hη : Integrable (fun t ↦ Real.exp (inner ℝ η t)) ν := hη
  replace hζ : Integrable (fun t ↦ Real.exp (inner ℝ ζ t)) ν := hζ
  change Integrable (fun t ↦ Real.exp (inner ℝ (a • η + b • ζ) t)) ν
  apply ((hη.const_mul a).add (hζ.const_mul b)).mono'
  · exact (by fun_prop : Continuous (fun t ↦ Real.exp (inner ℝ (a • η + b • ζ) t))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [inner_add_left, real_inner_smul_left, smul_eq_mul, Pi.add_apply] using
      convexOn_exp.2 (mem_univ (inner ℝ η t)) (mem_univ (inner ℝ ζ t)) ha hb hab

/-- GAPS 101.5: completeness of the natural statistic. For the laws
`exp ⟪η, T⟫ / Z(η) · ν` with `η` ranging over a nonempty open set `U`, where `Z(η)` is the
(finite, positive) normalizer, the statistic `T` is complete. -/
theorem isCompleteStatistic_withDensity_exp_inner {d : ℕ} (ν : Measure X)
    (T : X → EuclideanSpace ℝ (Fin d)) (hT : Measurable T)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hne : U.Nonempty)
    (Z : EuclideanSpace ℝ (Fin d) → ℝ)
    (hZ : ∀ η ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ η (T x))) ν ∧
      Z η = ∫ x, Real.exp (inner ℝ η (T x)) ∂ν ∧ 0 < Z η) :
    IsCompleteStatistic (fun η : U ↦ ν.withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η.val (T x)) / Z η.val))) T := by
  intro g hg hzero θ
  have hgT : Measurable fun x ↦ g (T x) := hg.comp hT
  have hw : ∀ η : EuclideanSpace ℝ (Fin d), Measurable fun x ↦ Real.exp (inner ℝ η (T x)) :=
    fun η ↦ Real.measurable_exp.comp ((continuous_const.inner continuous_id).measurable.comp hT)
  -- Unnormalized moment identities on `U`.
  have key : ∀ η ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ η (T x)) * g (T x)) ν ∧
      ∫ x, Real.exp (inner ℝ η (T x)) * g (T x) ∂ν = 0 := by
    intro η hη
    obtain ⟨hi, hz⟩ := hzero ⟨η, hη⟩
    have hZ0 := (hZ η hη).2.2
    have hd : Measurable fun x ↦ Real.exp (inner ℝ η (T x)) / Z η := (hw η).div_const _
    have hd0 : ∀ x, 0 ≤ Real.exp (inner ℝ η (T x)) / Z η := fun x ↦ by positivity
    have hi' := (integrable_withDensity_ofReal_iff ν hd hd0 _).1 hi
    have hz' := integral_withDensity_ofReal ν hd hd0 (fun x ↦ g (T x))
    have heq : (fun x ↦ Real.exp (inner ℝ η (T x)) * g (T x)) =
        fun x ↦ Z η * (Real.exp (inner ℝ η (T x)) / Z η * g (T x)) := by
      funext x; field_simp
    refine ⟨heq ▸ hi'.const_mul (Z η), ?_⟩
    rw [heq, integral_const_mul, ← hz']
    rw [hz, mul_zero]
  obtain ⟨η₀, hη₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU η₀ hη₀
  have hmem : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ < r → η₀ + u ∈ U := fun u hu ↦
    hball (by rwa [Metric.mem_ball, dist_self_add_left])
  -- Positive and negative parts, tilted at `η₀`, pushed forward to the statistic space.
  let hp : X → ℝ := fun x ↦ max (g (T x)) 0 * Real.exp (inner ℝ η₀ (T x))
  let hm : X → ℝ := fun x ↦ max (-g (T x)) 0 * Real.exp (inner ℝ η₀ (T x))
  have hpm : Measurable hp := (hgT.max measurable_const).mul (hw η₀)
  have hmm : Measurable hm := (hgT.neg.max measurable_const).mul (hw η₀)
  have hp0 : ∀ x, 0 ≤ hp x := fun x ↦ by positivity
  have hm0 : ∀ x, 0 ≤ hm x := fun x ↦ by positivity
  let μp : Measure (EuclideanSpace ℝ (Fin d)) := (ν.withDensity fun x ↦ ENNReal.ofReal (hp x)).map T
  let μm : Measure (EuclideanSpace ℝ (Fin d)) := (ν.withDensity fun x ↦ ENNReal.ofReal (hm x)).map T
  -- Integrability of the tilted parts at `η₀ + u`.
  have hexp_add : ∀ (u : EuclideanSpace ℝ (Fin d)) (x : X),
      Real.exp (inner ℝ η₀ (T x)) * Real.exp (inner ℝ u (T x)) =
      Real.exp (inner ℝ (η₀ + u) (T x)) := fun u x ↦ by
    rw [← Real.exp_add, inner_add_left]
  have hpart : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ < r →
      Integrable (fun x ↦ hp x * Real.exp (inner ℝ u (T x))) ν ∧
      Integrable (fun x ↦ hm x * Real.exp (inner ℝ u (T x))) ν := by
    intro u hu
    have hI := (key _ (hmem u hu)).1
    have hmeas : ∀ k : X → ℝ, Measurable k →
        AEStronglyMeasurable (fun x ↦ k x * Real.exp (inner ℝ u (T x))) ν :=
      fun k hk ↦ (hk.mul (hw u)).aestronglyMeasurable
    constructor
    · refine hI.mono (hmeas _ hpm) (ae_of_all _ fun x ↦ ?_)
      have : hp x * Real.exp (inner ℝ u (T x)) =
          max (g (T x)) 0 * Real.exp (inner ℝ (η₀ + u) (T x)) := by
        simp only [hp]; rw [mul_assoc, hexp_add]
      rw [this, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp,
        abs_of_nonneg (le_max_right _ _), mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
        (Real.exp_pos _).le
    · refine hI.mono (hmeas _ hmm) (ae_of_all _ fun x ↦ ?_)
      have : hm x * Real.exp (inner ℝ u (T x)) =
          max (-g (T x)) 0 * Real.exp (inner ℝ (η₀ + u) (T x)) := by
        simp only [hm]; rw [mul_assoc, hexp_add]
      rw [this, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp,
        abs_of_nonneg (le_max_right _ _), mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _))
        (Real.exp_pos _).le
  have hfin : ∀ k : X → ℝ, Measurable k → (∀ x, 0 ≤ k x) →
      Integrable (fun x ↦ k x * Real.exp (inner ℝ (0 : EuclideanSpace ℝ (Fin d)) (T x))) ν →
      IsFiniteMeasure ((ν.withDensity fun x ↦ ENNReal.ofReal (k x)).map T) := by
    intro k hk hk0 hki
    simp only [inner_zero_left, Real.exp_zero, mul_one] at hki
    refine ⟨?_⟩
    rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hki.lintegral_lt_top
  have h0r : ‖(0 : EuclideanSpace ℝ (Fin d))‖ < r := by simpa using hr
  have := hfin hp hpm hp0 (hpart 0 h0r).1
  have := hfin hm hmm hm0 (hpart 0 h0r).2
  have hFm : ∀ u : EuclideanSpace ℝ (Fin d),
      Measurable fun t : EuclideanSpace ℝ (Fin d) ↦ Real.exp (inner ℝ u t) := fun u ↦ by
    fun_prop
  have hμ : μp = μm := by
    refine measure_eq_of_integral_exp_inner_eq μp μm hr (fun u hu ↦ ?_) (fun u hu ↦ ?_)
    · exact (integrable_map_withDensity_ofReal_iff ν hT hpm hp0 (hFm u)).2 (hpart u hu).1
    · rw [integral_map_withDensity_ofReal ν hT hpm hp0 (hFm u),
        integral_map_withDensity_ofReal ν hT hmm hm0 (hFm u), ← sub_eq_zero,
        ← integral_sub (hpart u hu).1 (hpart u hu).2]
      rw [← (key _ (hmem u hu)).2]
      congr 1
      funext x
      simp only [hp, hm, ← hexp_add]
      linear_combination (Real.exp (inner ℝ η₀ (T x)) * Real.exp (inner ℝ u (T x))) *
        max_zero_sub_eq_self (g (T x))
  -- The two parts vanish where the other is positive.
  have hnull : ∀ (k : X → ℝ), Measurable k → ∀ B : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet B →
      (∀ x, T x ∈ B → k x = 0) → ((ν.withDensity fun x ↦ ENNReal.ofReal (k x)).map T) B = 0 :=
    by
    intro k hk B hB hkB
    rw [Measure.map_apply hT hB, withDensity_apply_eq_zero hk.ennreal_ofReal]
    convert measure_empty (μ := ν)
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_empty_iff_false, iff_false,
      not_and]
    intro hx hxB
    exact hx (by rw [hkB x hxB, ENNReal.ofReal_zero])
  have hpos : MeasurableSet {t : EuclideanSpace ℝ (Fin d) | 0 < g t} :=
    measurableSet_lt measurable_const hg
  have hneg : MeasurableSet {t : EuclideanSpace ℝ (Fin d) | g t < 0} :=
    measurableSet_lt hg measurable_const
  have h1 : μp {t | 0 < g t} = 0 := by
    rw [hμ]
    refine hnull hm hmm _ hpos fun x hx ↦ ?_
    simp only [hm, mem_ofPred_eq] at hx ⊢
    rw [max_eq_right (by linarith), zero_mul]
  have h2 : μm {t | g t < 0} = 0 := by
    rw [← hμ]
    refine hnull hp hpm _ hneg fun x hx ↦ ?_
    simp only [hp, mem_ofPred_eq] at hx ⊢
    rw [max_eq_right hx.le, zero_mul]
  rw [Measure.map_apply hT hpos, withDensity_apply_eq_zero hpm.ennreal_ofReal] at h1
  rw [Measure.map_apply hT hneg, withDensity_apply_eq_zero hmm.ennreal_ofReal] at h2
  have hae : ∀ᵐ x ∂ν, g (T x) = 0 := by
    have h1' := measure_union_null h1 h2
    rw [ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) h1'
    simp only [mem_ofPred_eq] at hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · refine Or.inr ⟨?_, hlt⟩
      simp only [hm, mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (lt_max_of_lt_left (by linarith)) (Real.exp_pos _)
    · refine Or.inl ⟨?_, hgt⟩
      simp only [hp, mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (lt_max_of_lt_left hgt) (Real.exp_pos _)
  exact withDensity_absolutelyContinuous _ _ hae

/-- GAPS 101.2: for a countable family with everywhere positive densities `f θ`, the likelihood
ratio `R(x) = (f θ x / f θ₀ x)_θ` is sufficient, and it is minimal: for every sufficient statistic
`T` there is a measurable `φ` with `R = φ ∘ T` almost surely under every `P θ`. -/
theorem isSufficientStatistic_likelihoodRatio_and_ae_eq_comp
    [StandardBorelSpace X] [Nonempty X] [Countable Θ]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (mu : Measure X) [SigmaFinite mu] (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) mu (f θ)) (hpos : ∀ θ x, 0 < f θ x) (θ₀ : Θ) :
    let R := fun x θ ↦ f θ x / f θ₀ x;
    IsSufficientStatistic P R ∧ ∀ T : X → S, IsSufficientStatistic P T →
      ∃ phi : S → (Θ → ℝ), Measurable phi ∧ ∀ θ, R =ᵐ[P θ] phi ∘ T := by
  intro R
  have : Nonempty Θ := ⟨θ₀⟩
  have hR : Measurable R := Measurable.of_eval fun θ ↦ (hf θ).1.div (hf θ₀).1
  refine ⟨isSufficientStatistic_of_factorization P mu hP f hf hR (fun θ r ↦ max (r θ) 0)
    (f θ₀) (fun θ ↦ ⟨(measurable_pi_apply θ).max measurable_const, fun _ ↦ le_max_right _ _⟩)
    fun θ ↦ ae_of_all _ fun x ↦ ?_, fun T hT ↦ ?_⟩
  · simp only [R]
    rw [max_eq_left (div_nonneg (hpos θ x).le (hpos θ₀ x).le),
      div_mul_cancel₀ _ (hpos θ₀ x).ne']
  obtain ⟨g, h, hg, -, -, hfac⟩ := exists_factorization_of_isSufficientStatistic P mu hP f hf T hT
  refine ⟨fun s θ ↦ g θ s / g θ₀ s,
    Measurable.of_eval fun θ ↦ (hg θ).1.div (hg θ₀).1, fun θ ↦ ?_⟩
  have hac : P θ ≪ mu := (hf θ).2.2 ▸ withDensity_absolutelyContinuous _ _
  refine hac (ae_all_iff.2 hfac |>.mono fun x hx ↦ ?_)
  funext θ'
  have hh : h x ≠ 0 := fun h0 ↦ (hpos θ₀ x).ne' (by rw [hx θ₀, h0, mul_zero])
  simp only [R, Function.comp_apply, hx θ', hx θ₀]
  exact mul_div_mul_right _ _ hh

/-- GAPS 101.6: a Pitman–Koopman–Darmois theorem. Let the laws `P θ` be mutually absolutely
continuous with a reference probability `P₀`, and suppose that for infinitely many sample sizes
`n` (including `n = 1`) the product densities are nondecreasing functions of a real statistic
`Tₙ`. Then the family is a one-parameter exponential family: `dP θ / dP₀ = C(θ) exp (a(θ) T)` for
a real statistic `T`. -/
theorem exists_exponential_family_of_monotone_sufficient_statistics
    (P : Θ → Measure X) (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (heq : ∀ θ, P θ ≪ P₀ ∧ P₀ ≪ P θ)
    (N : Set ℕ) (hN : N.Infinite) (h1 : 1 ∈ N)
    (hmon : ∀ n ∈ N, ∃ T : (Fin n → X) → ℝ, Measurable T ∧
      ∀ θ, ∃ H : ℝ → ℝ, Monotone H ∧
        HasDensity (Measure.pi fun _ : Fin n ↦ P θ)
          (Measure.pi fun _ : Fin n ↦ P₀) (H ∘ T)) :
    ∃ T : X → ℝ, Measurable T ∧ ∀ θ, ∃ C > 0, ∃ a : ℝ,
      HasDensity (P θ) P₀ (fun x ↦ C * Real.exp (a * T x)) := by
  sorry

/-- GAPS 101.4: in the natural exponential family with base measure `ν` on a finite-dimensional
real inner product space `E` and statistic the identity, the log partition function `A` is real
analytic on the interior of the natural parameter space `N`; at every `η ∈ interior N` its
gradient is the mean of the law `P η` at `η` and its Hessian is the covariance of `P η`. -/
theorem analyticOnNhd_logPartition_and_fderiv_eq_moments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0) :
    AnalyticOnNhd ℝ (logPartition ν id) (interior (naturalParameterSpace ν id)) ∧
      ∀ η ∈ interior (naturalParameterSpace ν id),
        HasFDerivAt (logPartition ν id)
          (innerSL ℝ (∫ x, x ∂exponentialFamilyMeasure ν id η)) η ∧
        ∀ u v : E, fderiv ℝ (fderiv ℝ (logPartition ν id)) η u v =
          cov[fun x ↦ inner ℝ u x, fun x ↦ inner ℝ v x;
            exponentialFamilyMeasure ν id η] := by
  exact ⟨analyticOnNhd_logPartition ν hne, fun η hη ↦
    ⟨hasFDerivAt_logPartition ν hne hη, fderiv_fderiv_logPartition_apply ν hne hη⟩⟩

/-- A regular scalar natural exponential family: laws `exp (η T - A(η)) · base` for natural
parameters `η` in an open interval `domain` on which `exp (η T)` is `base`-integrable, with a
nonzero σ-finite base measure and a statistic `T` that is not almost everywhere constant. -/
structure RealExponentialFamily (X : Type*) [MeasurableSpace X] where
  /-- Base measure, including any parameter-free carrier density. -/
  base : Measure X
  /-- The base measure is sigma finite. -/
  sigmaFinite : SigmaFinite base
  /-- Real natural statistic. -/
  statistic : X → ℝ
  /-- Measurability of the statistic. -/
  measurable_statistic : Measurable statistic
  /-- Parameter domain. -/
  domain : Set ℝ
  /-- Regularity of the domain. -/
  isOpen_domain : IsOpen domain
  /-- Interval property of the domain. -/
  convex_domain : Convex ℝ domain
  /-- The parameter domain is nonempty. -/
  nonempty_domain : domain.Nonempty
  /-- Exponential integrability at each parameter. -/
  integrable_exp : ∀ η ∈ domain, Integrable (fun x ↦ Real.exp (η * statistic x)) base
  /-- The base measure is nonzero. -/
  base_ne_zero : base ≠ 0
  /-- Nondegeneracy of the statistic. -/
  nonconstant : ∀ c : ℝ, ¬ (∀ᵐ x ∂base, statistic x = c)

/-- The log normalizer `A(η) = log ∫ exp (η T) d base` of a scalar exponential family. -/
def RealExponentialFamily.cumulant {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η : ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (η * F.statistic x) ∂F.base)

/-- The law `exp (η T - A(η)) · base` of the family at a natural parameter `η ∈ domain`. -/
def RealExponentialFamily.law {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η : F.domain) : Measure X :=
  F.base.withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (η.val * F.statistic x - F.cumulant η.val)))

end CKSD
