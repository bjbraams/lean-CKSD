module

public import CKSD.Bayes.BakryEmeryRegularization
/-!
# Bakry–Émery logarithmic Sobolev inequality

Expanding smooth radial cutoffs extend the compact-support entropy estimate to every
admissible smooth test. Their common Lipschitz bound dominates the derivative energies,
while their eventual local equality to one gives pointwise convergence of both the tests
and their derivatives. The resulting Gibbs logarithmic Sobolev constant is `1 / m`.

The cutoffs are imported from TauCeti; Mathlib supplies dominated convergence. The
compact-support estimate is the Prékopa–Leindler argument in the preceding local modules.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace CKSD

/-- Multiplication by a scalar in the unit interval preserves an integrable entropy bound. -/
theorem abs_sq_mul_log_sq_mul_le (a x : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    |(a * x) ^ 2 * Real.log ((a * x) ^ 2)| ≤ |x ^ 2 * Real.log (x ^ 2)| + x ^ 2 := by
  have ha2 : a ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [ha.1, ha.2]⟩
  have halog : |a ^ 2 * Real.log (a ^ 2)| ≤ 1 := by
    have h1 := Real.mul_log_nonpos ha2.1 ha2.2
    have h2 := Real.negMulLog_le_one_sub_self ha2.1
    rw [Real.negMulLog_eq_neg] at h2
    rw [abs_of_nonpos h1]
    linarith [ha2.1]
  have hid : (a ^ 2 * x ^ 2) * Real.log (a ^ 2 * x ^ 2) =
      x ^ 2 * (a ^ 2 * Real.log (a ^ 2)) + a ^ 2 * (x ^ 2 * Real.log (x ^ 2)) := by
    have h := Real.negMulLog_mul (a ^ 2) (x ^ 2)
    simp only [Real.negMulLog_eq_neg] at h
    nlinarith
  rw [mul_pow, hid]
  calc |x ^ 2 * (a ^ 2 * Real.log (a ^ 2)) + a ^ 2 * (x ^ 2 * Real.log (x ^ 2))| ≤
      |x ^ 2 * (a ^ 2 * Real.log (a ^ 2))| + |a ^ 2 * (x ^ 2 * Real.log (x ^ 2))| := abs_add_le _ _
    _ = x ^ 2 * |a ^ 2 * Real.log (a ^ 2)| + a ^ 2 * |x ^ 2 * Real.log (x ^ 2)| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (x : ℝ)), abs_of_nonneg (sq_nonneg (a : ℝ))]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left halog (sq_nonneg x)
      have h2 := mul_le_mul_of_nonneg_right ha2.2 (abs_nonneg (x ^ 2 * Real.log (x ^ 2)))
      nlinarith

/-- Smooth expanding radial cutoffs can be chosen with a common Lipschitz bound. -/
theorem exists_expanding_smooth_cutoffs (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ χ : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (χ n)) ∧ (∀ n x, χ n x ∈ Icc 0 1) ∧
      (∀ n, HasCompactSupport (χ n)) ∧ (∀ n, LipschitzWith 2 (χ n)) ∧
      ∀ x, ∀ᶠ n in atTop, (χ n) =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  have hex (n : ℕ) := TauCeti.exists_contDiff_cutoff_closedBall_lipschitzWith (0 : E)
    (r := (n : ℝ) + 1) (R := (n : ℝ) + 2) (K := 2)
    (by positivity) (by linarith) (by
      have h : (n : ℝ) + 2 - ((n : ℝ) + 1) = 1 := by ring
      rw [h]
      norm_num)
  choose χ hs hval heq hsupp hLip using hex
  refine ⟨χ, hs, (fun n x ↦ hval n (mem_range_self x)), ?_, hLip, ?_⟩
  · intro n
    change IsCompact (tsupport (χ n))
    exact (isCompact_closedBall (0 : E) ((n : ℝ) + 2)).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ((hsupp n).trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hxn : x ∈ Metric.ball (0 : E) ((n : ℝ) + 1) := by
      rw [mem_ball_iff_norm, sub_zero]
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [Metric.isOpen_ball.mem_nhds hxn] with y hy
    simpa only [Pi.one_apply] using heq n (Metric.ball_subset_closedBall hy)

/-- A logarithmic Sobolev bound on smooth compactly supported tests extends to all admissible tests. -/
theorem log_sobolev_inequality_of_has_compact_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (C : ℝ)
    (h : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      μ.entropy (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) :
    μ.LogSobolevInequality C := by
  rw [Measure.LogSobolevInequality_def]
  intro f hf hdf hf2 hflog
  obtain ⟨χ, hχs, hχval, hχcomp, hχLip, hχlim⟩ := exists_expanding_smooth_cutoffs E
  let F : ℕ → E → ℝ := fun n x ↦ χ n x * f x
  have hFs (n : ℕ) : ContDiff ℝ ∞ (F n) := (hχs n).mul hf
  have hFc (n : ℕ) : HasCompactSupport (F n) := by
    change HasCompactSupport (χ n * f)
    exact (hχcomp n).mul_right
  have hFnear (x : E) : ∀ᶠ n in atTop, F n =ᶠ[𝓝 x] f := by
    filter_upwards [hχlim x] with n hn
    filter_upwards [hn] with y hy
    dsimp [F]
    rw [hy, one_mul]
  have hFlim (x : E) : Tendsto (fun n ↦ F n x ^ 2) atTop (𝓝 (f x ^ 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hFnear x] with n hn
    rw [hn.eq_of_nhds]
  have hDlim (x : E) : Tendsto (fun n ↦ ‖fderiv ℝ (F n) x‖ ^ 2) atTop (𝓝 (‖fderiv ℝ f x‖ ^ 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hFnear x] with n hn
    rw [hn.fderiv_eq]
  have hF2 (n : ℕ) (x : E) : F n x ^ 2 ≤ f x ^ 2 := by
    dsimp [F]
    nlinarith [(hχval n x).1, (hχval n x).2, sq_nonneg (f x),
      mul_nonneg (sq_nonneg (f x)) (by nlinarith [(hχval n x).1, (hχval n x).2] : 0 ≤ 1 - χ n x ^ 2)]
  have hEntropy : Tendsto (fun n ↦ μ.entropy (fun x ↦ F n x ^ 2)) atTop
      (𝓝 (μ.entropy (fun x ↦ f x ^ 2))) := by
    apply tendsto_entropy_of_dominated_convergence μ _ _ (fun x ↦ f x ^ 2)
      (fun x ↦ |f x ^ 2 * Real.log (f x ^ 2)| + f x ^ 2)
      (fun n ↦ ((hFs n).continuous.pow 2).aestronglyMeasurable) hf2
      (by
        have hh : Integrable (fun x ↦ ‖f x ^ 2 * Real.log (f x ^ 2)‖ + f x ^ 2) μ := hflog.norm.add hf2
        simpa only [Real.norm_eq_abs] using hh)
    · intro n
      exact ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hF2 n x
    · intro n
      exact ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs]
        exact abs_sq_mul_log_sq_mul_le (χ n x) (f x) (hχval n x)
    · exact ae_of_all _ hFlim
  have hDi : Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ 2) μ := (memLp_two_iff_integrable_sq ((hf.continuous_fderiv (by simp)).norm.aestronglyMeasurable)).1 hdf
  have hDbound (n : ℕ) (x : E) : ‖fderiv ℝ (F n) x‖ ^ 2 ≤ 2 * ‖fderiv ℝ f x‖ ^ 2 + 8 * f x ^ 2 := by
    have hD : fderiv ℝ (F n) x = χ n x • fderiv ℝ f x + f x • fderiv ℝ (χ n) x := by
      exact (((hχs n).differentiable (by simp) x).hasFDerivAt.mul
        ((hf.differentiable (by simp) x).hasFDerivAt)).fderiv
    have hDχ : ‖fderiv ℝ (χ n) x‖ ≤ (2 : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hχLip n)
    have hD1 : ‖fderiv ℝ (F n) x‖ ≤ ‖fderiv ℝ f x‖ + 2 * |f x| := by
      rw [hD]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hχval n x).1]
      have h1 := mul_le_mul_of_nonneg_right (hχval n x).2 (norm_nonneg (fderiv ℝ f x))
      have h2 := mul_le_mul_of_nonneg_left hDχ (abs_nonneg (f x))
      nlinarith
    have hD2 := sq_le_sq₀ (norm_nonneg (fderiv ℝ (F n) x)) (by positivity) |>.2 hD1
    nlinarith [sq_nonneg (‖fderiv ℝ f x‖ - 2 * |f x|), sq_abs (f x)]
  have hEnergy := tendsto_integral_of_dominated_convergence
    (fun x ↦ 2 * ‖fderiv ℝ f x‖ ^ 2 + 8 * f x ^ 2)
    (fun n ↦ ((hFs n).continuous_fderiv (by simp)).norm.aestronglyMeasurable.pow 2)
    ((hDi.const_mul 2).add (hf2.const_mul 8))
    (fun n ↦ ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hDbound n x)
    (ae_of_all _ hDlim)
  exact le_of_tendsto_of_tendsto' hEntropy (hEnergy.const_mul (2 * C)) (fun n ↦ h (F n) (hFs n) (hFc n))

/-- Bakry–Émery: a strongly convex smooth potential has logarithmic Sobolev constant `1/m`. -/
theorem log_sobolev_inequality_gibbs_measure_of_strongly_monotone_gradient {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m : ℝ) (hm0 : 0 < m)
    (hG : ∀ x, HasGradientAt V (G x) x) (hm : IsStronglyMonotoneGradient G m)
    (hZ : Integrable (fun x ↦ Real.exp (-V x))) :
    (gibbsMeasure V).LogSobolevInequality (1 / m) := by
  have : IsProbabilityMeasure (gibbsMeasure V) := is_probability_measure_gibbs_measure hZ
  apply log_sobolev_inequality_of_has_compact_support
  intro f hf hfc
  convert entropy_gibbs_sq_le_of_has_compact_support V G m hm0 hG hm hZ f hf hfc using 1 <;> ring

end CKSD
