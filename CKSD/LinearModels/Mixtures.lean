module

public import CKSD.LinearModels.Basic
public import TauCeti.Probability.Distributions.Gaussian.Mixture.Multivariate

/-!
# Identifiable finite Gaussian mixtures

The laws and densities are TauCeti's general finite multivariate Gaussian-mixture constructions.
This module restricts their parameters to distinct, nondegenerate, positive-weight components,
then states identifiability across different component counts and likelihood unboundedness.
Sources: GAPS 105.6 and SYNOPSIS105, item 6.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Convexity
open scoped NNReal ENNReal BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Parameters of a reduced finite Gaussian mixture: all components are nondegenerate, distinct,
and have positive weight. Laws and densities use the upstream TauCeti construction. -/
structure GaussianMixtureModel (d k : ℕ) where
  /-- Component weights on the finite simplex. -/
  weights : StdSimplex ℝ≥0 (Fin k)
  /-- Component means. -/
  mean : Fin k → EuclideanSpace ℝ (Fin d)
  /-- Component covariance matrices. -/
  covariance : Fin k → Matrix (Fin d) (Fin d) ℝ
  /-- Every covariance is positive definite. -/
  covariance_posDef : ∀ i, (covariance i).PosDef
  /-- No component has zero weight. -/
  weight_pos : ∀ i, 0 < weights.weights i
  /-- Equal component parameters have equal component indices. -/
  distinct : Function.Injective (fun i ↦ (mean i, covariance i))

/-- Probability law of a reduced Gaussian mixture, using TauCeti's finite mixture. -/
def GaussianMixtureModel.law {d k : ℕ} (M : GaussianMixtureModel d k) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  TauCeti.Probability.multivariateGaussianMixtureMeasure M.weights M.mean M.covariance

/-- Real Gaussian-mixture density, using TauCeti's canonical continuous density. -/
def GaussianMixtureModel.density {d k : ℕ} (M : GaussianMixtureModel d k) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  TauCeti.Probability.multivariateGaussianMixturePDFReal M.weights M.mean M.covariance

/-- Log likelihood of a reduced Gaussian mixture at a finite observed sample. -/
def GaussianMixtureModel.logLikelihood {d k n : ℕ} (M : GaussianMixtureModel d k)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, Real.log (M.density (x i))

/-- The mixture law is a probability measure by TauCeti's mixture instance. -/
instance GaussianMixtureModel.isProbabilityMeasure_law {d k : ℕ}
    (M : GaussianMixtureModel d k) : IsProbabilityMeasure M.law :=
  inferInstanceAs (IsProbabilityMeasure
    (TauCeti.Probability.multivariateGaussianMixtureMeasure M.weights M.mean M.covariance))

/-- The canonical mixture density is nonnegative, by TauCeti. -/
theorem GaussianMixtureModel.density_nonneg {d k : ℕ} (M : GaussianMixtureModel d k)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ M.density x :=
  TauCeti.Probability.multivariateGaussianMixturePDFReal_nonneg _ _ _ _

/-- The mixture's real density agrees with its law in CKSD's density interface, using TauCeti. -/
theorem GaussianMixtureModel.hasDensity {d k : ℕ} (M : GaussianMixtureModel d k) :
    HasDensity M.law volume M.density := by
  refine ⟨TauCeti.Probability.measurable_multivariateGaussianMixturePDFReal _ _ _,
    Filter.Eventually.of_forall M.density_nonneg, ?_⟩
  exact (TauCeti.Probability.multivariateGaussianMixtureMeasure_eq_withDensity
    (fun i _ ↦ M.covariance_posDef i)).trans (by
      congr 1
      funext x
      exact TauCeti.Probability.multivariateGaussianMixturePDF_eq_ofReal _ _ _ _)

/-- GAPS 105.6: finite nondegenerate Gaussian mixtures are identifiable up to relabeling,
including equality of the number of distinct positive-weight components. -/
theorem gaussianMixtureModel_identifiable {d k l : ℕ} (hd : 0 < d)
    (M : GaussianMixtureModel d k) (N : GaussianMixtureModel d l) (h : M.law = N.law) :
    ∃ e : Fin k ≃ Fin l, ∀ i,
      M.weights.weights i = N.weights.weights (e i) ∧
        M.mean i = N.mean (e i) ∧ M.covariance i = N.covariance (e i) := by
  sorry

/-- GAPS 105.6: two Gaussian components already give an unbounded likelihood when their
covariances are unconstrained. The sample and ambient dimension are both nonempty. -/
theorem gaussianMixtureModel_logLikelihood_unbounded {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∀ R : ℝ, ∃ M : GaussianMixtureModel d 2, R < M.logLikelihood x := by
  intro R
  classical
  set i₀ : Fin n := ⟨0, hn⟩
  set μ := x i₀
  let φ := TauCeti.Probability.multivariateGaussianPDFReal (ι := Fin d)
  -- the lower bound contributed by the unit-covariance component
  let c : Fin n → ℝ := fun i ↦ Real.log (1 / 2 * φ μ 1 (x i))
  have hφpos : ∀ y, 0 < φ μ 1 y := fun y ↦
    TauCeti.Probability.multivariateGaussianPDFReal_pos (by simp) μ y
  let K₀ : ℝ := Real.log (1 / 2) + Real.log ((2 * Real.pi) ^ (-(d : ℝ) / 2))
  let s : ℝ := max 1 (2 * (R - ∑ i, c i + c i₀ - K₀) / d + 1)
  have hs : 0 < s := lt_of_lt_of_le one_pos (le_max_left _ _)
  set t : ℝ := Real.exp (-s)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≠ 1 := by
    intro h
    have : -s = 0 := by rw [← Real.exp_eq_one_iff]; exact h
    linarith
  let w : StdSimplex ℝ≥0 (Fin 2) :=
    StdSimplex.duple 0 1 (s := 1 / 2) (t := 1 / 2) (by positivity) (by positivity) (by rw [add_halves])
  have hw : ∀ i, (w.weights i : ℝ) = 1 / 2 := by
    intro i
    fin_cases i <;> simp [w, StdSimplex.duple]
  let S : Fin 2 → Matrix (Fin d) (Fin d) ℝ := ![t • 1, 1]
  have hS : ∀ i, (S i).PosDef := by
    intro i
    fin_cases i
    · exact Matrix.PosDef.one.smul ht
    · exact Matrix.PosDef.one
  let M : GaussianMixtureModel d 2 :=
    { weights := w
      mean := fun _ ↦ μ
      covariance := S
      covariance_posDef := hS
      weight_pos := fun i ↦ by
        have := hw i
        rw [← NNReal.coe_pos, this]
        norm_num
      distinct := by
        intro i j hij
        simp only [Prod.mk.injEq] at hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          have := congrFun (congrFun hij.2 ⟨0, hd⟩) ⟨0, hd⟩
          simp [S] at this
          exact ht1 this
        · exfalso
          have := congrFun (congrFun hij.2 ⟨0, hd⟩) ⟨0, hd⟩
          simp [S] at this
          exact ht1 this.symm
        · rfl }
  refine ⟨M, ?_⟩
  have hdens : ∀ y, M.density y = 1 / 2 * φ μ (t • 1) y + 1 / 2 * φ μ 1 y := by
    intro y
    simp only [GaussianMixtureModel.density, M,
      TauCeti.Probability.multivariateGaussianMixturePDFReal_def]
    rw [Finset.filter_true_of_mem (fun i _ ↦ hS i), Fin.sum_univ_two, hw, hw]
    rfl
  have hφt : ∀ y, 0 < φ μ (t • 1) y := fun y ↦
    TauCeti.Probability.multivariateGaussianPDFReal_pos ((Matrix.PosDef.one.smul ht).det_pos) μ y
  have hlow : ∀ i, c i ≤ Real.log (M.density (x i)) := by
    intro i
    rw [hdens]
    apply Real.log_le_log (by have := hφpos (x i); positivity)
    have := hφt (x i)
    linarith
  have hcenter : Real.log (1 / 2 * φ μ (t • 1) μ) ≤ Real.log (M.density μ) := by
    rw [hdens]
    apply Real.log_le_log (by have := hφt μ; positivity)
    have := hφpos μ
    linarith
  have hval : Real.log (1 / 2 * φ μ (t • 1) μ) = K₀ + d * s / 2 := by
    simp only [φ, TauCeti.Probability.multivariateGaussianPDFReal_def, sub_self, inner_zero_left,
      neg_zero, zero_div, Real.exp_zero, mul_one, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    have h2π : (0 : ℝ) < (2 * Real.pi) ^ (-(d : ℝ) / 2) := by positivity
    have htd : (0 : ℝ) < (t ^ d) ^ (-(1 : ℝ) / 2) := by positivity
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul h2π.ne' htd.ne',
      Real.log_rpow (pow_pos ht d), Real.log_pow, Real.log_exp]
    simp only [K₀]
    ring
  -- sum of the lower bounds, improved at the observation `x i₀`
  have hsum : ∑ i, c i - c i₀ + Real.log (M.density μ) ≤ M.logLikelihood x := by
    unfold GaussianMixtureModel.logLikelihood
    have h1 : ∑ i, c i ≤ ∑ i, Real.log (M.density (x i)) := Finset.sum_le_sum fun i _ ↦ hlow i
    have h2 := Finset.single_le_sum (f := fun i ↦ Real.log (M.density (x i)) - c i)
      (fun i _ ↦ sub_nonneg.2 (hlow i)) (Finset.mem_univ i₀)
    simp only [Finset.sum_sub_distrib] at h2
    linarith
  have hsd : 2 * (R - ∑ i, c i + c i₀ - K₀) / d < s := by
    have := le_max_right 1 (2 * (R - ∑ i, c i + c i₀ - K₀) / d + 1)
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have : R - ∑ i, c i + c i₀ - K₀ < d * s / 2 := by
    rw [div_lt_iff₀ hdpos] at hsd
    linarith
  linarith

end CKSD
