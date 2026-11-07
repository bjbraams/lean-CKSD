module

public import CKSD.Inference.Basic
public import CKSD.Inference.Factorization
public import CKSD.Inference.LaplaceDeterminacy
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Inference: ExponentialFamily

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.1: factorization on standard Borel sample and statistic spaces. -/
theorem isSufficientStatistic_iff_exists_factorization
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace S]
    [Nonempty S] [Nonempty Θ] (P : Θ → Measure X) (μ : Measure X) [SigmaFinite μ]
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S) (hT : Measurable T) :
    IsSufficientStatistic P T ↔ ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  refine ⟨exists_factorization_of_isSufficientStatistic P μ hP f hf T, ?_⟩
  rintro ⟨g, h, hg, -, -, hfac⟩
  exact isSufficientStatistic_of_factorization P μ hP f hf hT g h hg hfac

/-- GAPS 101.4, convexity part: the multivariate Laplace-integrability domain is convex. -/
theorem convex_laplace_integrability_domain {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) :
    Convex ℝ {η : EuclideanSpace ℝ (Fin d) |
      Integrable (fun t ↦ Real.exp (inner ℝ η t)) ν} := by
  intro η hη ζ hζ a b ha hb hab
  apply ((hη.const_mul a).add (hζ.const_mul b)).mono'
  · exact (by fun_prop : Continuous (fun t ↦ Real.exp (inner ℝ (a • η + b • ζ) t))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [inner_add_left, real_inner_smul_left, smul_eq_mul, Pi.add_apply] using
      convexOn_exp.2 (mem_univ (inner ℝ η t)) (mem_univ (inner ℝ ζ t)) ha hb hab

/-- GAPS 101.5: completeness of a natural statistic over a nonempty open parameter set. -/
theorem isCompleteStatistic_exponential_family {d : ℕ} (ν : Measure X) [SigmaFinite ν]
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
    refine Measure.ext_of_integral_exp_inner_eq μp μm hr (fun u hu ↦ ?_) (fun u hu ↦ ?_)
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

/-- GAPS 101.2, minimal likelihood-ratio statistic for a countable parameter family. -/
theorem likelihood_ratio_statistic_minimal_sufficient
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

/-- GAPS 101.6: the monotone Pitman–Koopman–Darmois characterization. -/
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

/-- GAPS 101.4, multivariate analyticity and first/second cumulant derivatives. -/
theorem analyticOnNhd_cumulant_and_fderiv_eq_moments
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d)))
    [SigmaFinite nu] (hne : nu ≠ 0) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    let P := fun eta ↦ nu.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ eta x - A eta)));
    AnalyticOnNhd ℝ A (interior N) ∧ ∀ eta ∈ interior N,
      HasFDerivAt A (innerSL ℝ (∫ x, x ∂P eta)) eta ∧
      ∀ u v : EuclideanSpace ℝ (Fin d),
        fderiv ℝ (fderiv ℝ A) eta u v =
          covariance (P eta) (fun x ↦ inner ℝ u x) (fun x ↦ inner ℝ v x) := by
  sorry


end CKSD
