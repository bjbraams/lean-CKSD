module

public import CKSD.Geometry.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein


/-!
# Gaussian-smoothed empirical Wasserstein distance

For a law `P` on the cube `[-1, 1]^d`, Gaussian smoothing with `N(0, σ² I)` gives the empirical
`W₁` distance the parametric rate: `E W₁(μ_n * N_σ, P * N_σ) ≤ C / √n`. Both smoothings have
Lebesgue densities, `p_n(x) = n⁻¹ ∑ φ(x - X_i)` and `p(x) = ∫ φ(x - y) dP(y)`. By
Kantorovich–Rubinstein duality (TauCeti), `W₁` is at most `∫ ‖x‖ |p_n(x) - p(x)| dx`; for each `x`
the mean absolute deviation of the sample mean `p_n(x)` is at most `K φ_{2σ²}(x) / √n` by the
variance of i.i.d. sums, and the weighted integral of the Gaussian bound is finite.

## Main results

* `CKSD.wasserstein_e_dist_one_gaussian_smoothing_le`: the weighted total variation bound.
* `CKSD.integral_abs_sample_mean_sub_le`: `E |n⁻¹ ∑ g(X_i) - E g| ≤ B / √n` for `|g| ≤ B`.
* `CKSD.integral_wasserstein_e_dist_gaussian_smoothing_le`: the rate with an explicit constant.

## References

* Z. Goldfeld, K. Greenewald, J. Niles-Weed and Y. Polyanskiy, *Convergence of smoothed empirical
  measures with applications to entropy estimation*, IEEE Trans. Inform. Theory 66 (2020),
  4368–4391.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CKSD

variable {d : ℕ}


/-- The density of `N(0, s I)` is `c_s exp(-‖z‖² / (2 s))` with `c_s` its value at the origin. -/
theorem multivariate_gaussian_pdf_real_zero_smul_one {s : ℝ} (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin d)) :
    TauCeti.Probability.multivariateGaussianPDFReal 0 (s • (1 : Matrix (Fin d) (Fin d) ℝ)) z =
      TauCeti.Probability.multivariateGaussianPDFReal 0 (s • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 *
        Real.exp (-(‖z‖ ^ 2 / (2 * s))) := by
  have hinv : (s • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = s⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hs.ne', one_mul, one_smul]
  have key : ∀ w : EuclideanSpace ℝ (Fin d),
      ⟪w, (s • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹.toEuclideanLin w⟫ = s⁻¹ * ‖w‖ ^ 2 := by
    intro w
    have : (s⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).toEuclideanLin w = s⁻¹ • w := by
      rw [map_smul, Matrix.toLpLin_one]; rfl
    rw [hinv, this, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [TauCeti.Probability.multivariateGaussianPDFReal_def, sub_zero, key, norm_zero]
  rw [show -(s⁻¹ * 0 ^ 2) / 2 = 0 by ring, Real.exp_zero, mul_one]
  congr 2
  field_simp


/-- The density of `N(0, s I)` on `ℝ^d`. -/
noncomputable def isoGaussianPDF (d : ℕ) (s : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  TauCeti.Probability.multivariateGaussianPDFReal 0 (s • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- The density of `N(0, s I)` in the form `c_s exp(-‖z‖² / (2 s))`. -/
theorem iso_gaussian_pdf_eq {s : ℝ} (hs : 0 < s) (z : EuclideanSpace ℝ (Fin d)) :
    isoGaussianPDF d s z = isoGaussianPDF d s 0 * Real.exp (-(‖z‖ ^ 2 / (2 * s))) :=
  multivariate_gaussian_pdf_real_zero_smul_one hs z

/-- A positive multiple of the identity is positive definite. -/
private theorem pos_def_smul_one {s : ℝ} (hs : 0 < s) :
    (s • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
  Matrix.PosDef.one.smul hs

/-- The density of `N(0, s I)` is positive. -/
theorem iso_gaussian_pdf_pos {s : ℝ} (hs : 0 < s) (z : EuclideanSpace ℝ (Fin d)) :
    0 < isoGaussianPDF d s z :=
  TauCeti.Probability.multivariateGaussianPDFReal_pos (pos_def_smul_one hs).det_pos _ _

/-- The density of `N(0, s I)` is continuous. -/
theorem continuous_iso_gaussian_pdf {s : ℝ} (hs : 0 < s) : Continuous (isoGaussianPDF d s) := by
  have : isoGaussianPDF d s = fun z ↦ isoGaussianPDF d s 0 * Real.exp (-(‖z‖ ^ 2 / (2 * s))) :=
    funext (iso_gaussian_pdf_eq hs)
  rw [this]; fun_prop

/-- The density of `N(0, s I)` is maximal at the origin. -/
theorem iso_gaussian_pdf_le_iso_gaussian_pdf_zero {s : ℝ} (hs : 0 < s) (z : EuclideanSpace ℝ (Fin d)) :
    isoGaussianPDF d s z ≤ isoGaussianPDF d s 0 := by
  rw [iso_gaussian_pdf_eq hs z]
  refine mul_le_of_le_one_right (iso_gaussian_pdf_pos hs 0).le (Real.exp_le_one_iff.2 ?_)
  have : 0 ≤ ‖z‖ ^ 2 / (2 * s) := by positivity
  linarith

/-- Gaussian domination: if `‖y‖² ≤ R`, then the density of `N(0, s I)` at `x - y` is at most a
constant times the density of `N(0, 2 s I)` at `x`. -/
theorem iso_gaussian_pdf_sub_le {s R : ℝ} (hs : 0 < s) (x y : EuclideanSpace ℝ (Fin d))
    (hy : ‖y‖ ^ 2 ≤ R) :
    isoGaussianPDF d s (x - y) ≤ isoGaussianPDF d s 0 / isoGaussianPDF d (2 * s) 0 *
      Real.exp (R / (2 * s)) * isoGaussianPDF d (2 * s) x := by
  have h2 : 0 < 2 * s := by positivity
  rw [iso_gaussian_pdf_eq hs, iso_gaussian_pdf_eq h2 x]
  have hc := iso_gaussian_pdf_pos h2 (0 : EuclideanSpace ℝ (Fin d))
  have hc' := iso_gaussian_pdf_pos hs (0 : EuclideanSpace ℝ (Fin d))
  have hR : isoGaussianPDF d s 0 / isoGaussianPDF d (2 * s) 0 * Real.exp (R / (2 * s)) *
      (isoGaussianPDF d (2 * s) 0 * Real.exp (-(‖x‖ ^ 2 / (2 * (2 * s))))) =
      isoGaussianPDF d s 0 * Real.exp (R / (2 * s) + -(‖x‖ ^ 2 / (2 * (2 * s)))) := by
    rw [Real.exp_add]; field_simp
  rw [hR]
  refine mul_le_mul_of_nonneg_left ?_ hc'.le
  refine Real.exp_le_exp.2 ?_
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
  have hsq : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg x) htri 2
    nlinarith [sq_nonneg (‖x - y‖ - ‖y‖)]
  have e1 : -(‖x - y‖ ^ 2 / (2 * s)) = -(2 * ‖x - y‖ ^ 2) / (4 * s) := by field_simp; ring
  have e2 : R / (2 * s) + -(‖x‖ ^ 2 / (2 * (2 * s))) = (2 * R - ‖x‖ ^ 2) / (4 * s) := by
    field_simp; ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- The density of `N(0, s I)` is measurable. -/
theorem measurable_iso_gaussian_pdf {s : ℝ} (hs : 0 < s) : Measurable (isoGaussianPDF d s) :=
  (continuous_iso_gaussian_pdf hs).measurable

/-- `N(0, s I)` has density `isoGaussianPDF d s` with respect to Lebesgue measure. -/
theorem multivariate_gaussian_smul_one_eq_with_density {s : ℝ} (hs : 0 < s) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (s • 1) =
      volume.withDensity fun z ↦ ENNReal.ofReal (isoGaussianPDF d s z) :=
  (TauCeti.Probability.multivariateGaussian_eq_withDensity (pos_def_smul_one hs) 0).trans
    (by rw [TauCeti.Probability.multivariateGaussianPDF_def]; rfl)

/-- Integrals against `N(0, s I)` as Lebesgue integrals against its density. -/
theorem integral_multivariate_gaussian_smul_one {s : ℝ} (hs : 0 < s)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ z, g z ∂(multivariateGaussian 0 (s • 1)) = ∫ z, isoGaussianPDF d s z * g z := by
  rw [multivariate_gaussian_smul_one_eq_with_density hs, integral_withDensity_eq_integral_toReal_smul
    (measurable_iso_gaussian_pdf hs).ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp [ENNReal.toReal_ofReal (iso_gaussian_pdf_pos hs z).le]

/-- `‖x‖` times the density of `N(0, s I)` is Lebesgue integrable. -/
theorem integrable_norm_mul_iso_gaussian_pdf {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ * isoGaussianPDF d s x) := by
  have hG : Integrable (fun x ↦ ‖x‖)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (s • 1)) :=
    (IsGaussian.memLp_two_id.integrable one_le_two).norm
  rw [multivariate_gaussian_smul_one_eq_with_density hs, integrable_withDensity_iff_integrable_smul'
    (measurable_iso_gaussian_pdf hs).ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hG
  refine hG.congr (ae_of_all _ fun x ↦ ?_)
  simp [ENNReal.toReal_ofReal (iso_gaussian_pdf_pos hs x).le, mul_comm]

/-- The Gaussian smoothing of a probability measure is a probability measure. -/
theorem is_probability_measure_gaussian_smoothing (sigma : ℝ) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (gaussianSmoothing sigma ν) := by
  unfold gaussianSmoothing
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- The norm is integrable under a centred multivariate Gaussian law. -/
theorem integrable_norm_multivariate_gaussian (s : ℝ) :
    Integrable (fun x ↦ ‖x‖) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (s • 1)) :=
  (IsGaussian.memLp_two_id.integrable one_le_two).norm

/-- The Gaussian smoothing of a law with finite first moment has finite first moment. -/
theorem has_finite_moment_gaussian_smoothing (sigma : ℝ) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] (hν : Integrable (fun x ↦ ‖x‖) ν) :
    TauCeti.HasFiniteMoment 1 (gaussianSmoothing sigma ν) := by
  have := is_probability_measure_gaussian_smoothing sigma ν
  rw [TauCeti.hasFiniteMoment_iff_lintegral_edist_rpow_ne_top one_ne_zero ENNReal.one_ne_top 0]
  simp only [ENNReal.toReal_one, ENNReal.rpow_one]
  set G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (sigma ^ 2 • 1)
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      ‖z.1 + z.2‖) (ν.prod G) := by
    refine Integrable.mono' ((hν.comp_fst G).add
      ((integrable_norm_multivariate_gaussian (sigma ^ 2)).comp_snd ν)) (by fun_prop)
      (ae_of_all _ fun z ↦ ?_)
    simpa using norm_add_le z.1 z.2
  unfold gaussianSmoothing
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.hasFiniteIntegral)
  refine lintegral_congr fun z ↦ ?_
  simp [edist_zero_left, enorm_eq_nnnorm]

/-- Integrals against a Gaussian smoothing: for `f` continuous with `|f x| ≤ ‖x‖` and `ν` with
finite first moment, `∫ f d(ν * N(0, σ² I)) = ∫ (∫ f(x) φ(x - y) dx) dν(y)` with `φ` the Gaussian
density. -/
theorem integral_gaussian_smoothing_eq {sigma : ℝ} (hs : sigma ≠ 0)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (hν : Integrable (fun x ↦ ‖x‖) ν) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (hfb : ∀ x, |f x| ≤ ‖x‖) :
    ∫ x, f x ∂(gaussianSmoothing sigma ν) =
      ∫ y, (∫ x, f x * isoGaussianPDF d (sigma ^ 2) (x - y)) ∂ν := by
  have hs2 : 0 < sigma ^ 2 := by positivity
  set G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (sigma ^ 2 • 1)
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      f (z.1 + z.2)) (ν.prod G) := by
    refine Integrable.mono' ((hν.comp_fst G).add
      ((integrable_norm_multivariate_gaussian (sigma ^ 2)).comp_snd ν)) (by fun_prop)
      (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (hfb _).trans (norm_add_le z.1 z.2)
  unfold gaussianSmoothing
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable, integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only
  rw [integral_multivariate_gaussian_smul_one hs2]
  have := integral_add_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun x ↦ f x * isoGaussianPDF d (sigma ^ 2) (x - y)) y
  simp only [add_sub_cancel_left] at this
  rw [← this]
  exact integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)

/-- Mean absolute deviation of a sample mean: for `g` with `|g| ≤ B` almost surely and an i.i.d.
sample of size `n ≥ 1`, `E |n⁻¹ ∑ g(X_i) - E g| ≤ B / √n`. -/
theorem integral_abs_sample_mean_sub_le {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] {g : X → ℝ} (hg : Measurable g) {B : ℝ} (hB : 0 < B)
    (hgB : ∀ᵐ y ∂P, |g y| ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, |(n : ℝ)⁻¹ * ∑ i, g (ω i) - ∫ y, g y ∂P| ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      B / Real.sqrt n := by
  set μ := Measure.pi fun _ : Fin n ↦ P
  set m := ∫ y, g y ∂P
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hgL : MemLp g 2 P := MemLp.of_bound hg.aestronglyMeasurable B
    (hgB.mono fun y hy ↦ by rwa [Real.norm_eq_abs])
  have hgi : Integrable g P := hgL.integrable one_le_two
  have hcomp : ∀ i : Fin n, Integrable (fun ω : Fin n → X ↦ g (ω i)) μ := fun i ↦
    (measurePreserving_eval (fun _ : Fin n ↦ P) i).integrable_comp_of_integrable hgi
  set S : (Fin n → X) → ℝ := fun ω ↦ ∑ i, g (ω i)
  have hSm : Measurable S := Finset.measurable_sum _ fun i _ ↦ hg.comp (measurable_pi_apply i)
  have hES : ∫ ω, S ω ∂μ = n * m := by
    simp only [S]
    rw [integral_finsetSum _ fun i _ ↦ hcomp i]
    have : ∀ i : Fin n, ∫ ω, g (ω i) ∂μ = m := fun i ↦ by
      have h := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable
        hg.aestronglyMeasurable
      rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq] at h
      exact h.symm
    simp [this]
  have hvar : Var[S; μ] = n * Var[g; P] := by
    have h := variance_sum_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ g) (fun _ ↦ hgL)
    have hfun : (∑ i : Fin n, fun ω : Fin n → X ↦ g (ω i)) = S := by
      funext ω; simp [S]
    rw [hfun] at h
    rw [h]; simp
  have hvg : Var[g; P] ≤ B ^ 2 := by
    refine (variance_le_expectation_sq hg.aestronglyMeasurable).trans ?_
    calc ∫ y, (g ^ 2) y ∂P ≤ ∫ _y, B ^ 2 ∂P := integral_mono_ae (hgL.integrable_sq)
          (integrable_const _) (hgB.mono fun y hy ↦ by
            simp only [Pi.pow_apply]; nlinarith [abs_nonneg (g y), sq_abs (g y)])
      _ = B ^ 2 := by simp
  -- second moment of the centred sample mean
  set Z : (Fin n → X) → ℝ := fun ω ↦ (n : ℝ)⁻¹ * S ω - m
  have hZ2 : ∫ ω, Z ω ^ 2 ∂μ ≤ B ^ 2 / n := by
    have hv := variance_eq_integral (μ := μ) hSm.aemeasurable
    rw [hES] at hv
    have hZ : ∀ ω, Z ω ^ 2 = ((n : ℝ) ^ 2)⁻¹ * (S ω - n * m) ^ 2 := fun ω ↦ by
      simp only [Z]; field_simp
    simp_rw [hZ]
    rw [integral_const_mul, ← hv, hvar]
    calc ((n : ℝ) ^ 2)⁻¹ * (n * Var[g; P]) ≤ ((n : ℝ) ^ 2)⁻¹ * (n * B ^ 2) := by gcongr
      _ = B ^ 2 / n := by field_simp
  have hZm : Measurable Z := (hSm.const_mul _).sub_const _
  have hZb : ∀ᵐ ω ∂μ, |Z ω| ≤ 2 * B := by
    have hall : ∀ᵐ ω ∂μ, ∀ i, |g (ω i)| ≤ B := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin n ↦ P) i).quasiMeasurePreserving.ae
        (p := fun y ↦ |g y| ≤ B) hgB
    filter_upwards [hall] with ω hω
    have h1 : |(n : ℝ)⁻¹ * S ω| ≤ B := by
      rw [abs_mul, abs_inv, abs_of_pos hnR, inv_mul_le_iff₀ hnR]
      calc |S ω| ≤ ∑ i, |g (ω i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ hω i
        _ = n * B := by simp
    have h2 : |m| ≤ B := by
      calc |m| ≤ ∫ y, |g y| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _y, B ∂P := integral_mono_ae hgi.abs (integrable_const _) hgB
        _ = B := by simp
    calc |Z ω| ≤ |(n : ℝ)⁻¹ * S ω| + |m| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hZi : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable (2 * B)
    (hZb.mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hZ2i : Integrable (fun ω ↦ Z ω ^ 2) μ := by
    refine Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable ((2 * B) ^ 2)
      (hZb.mono fun ω h ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- `|Z| ≤ (Z² / t + t) / 2`
  set t := B / Real.sqrt n
  have ht : 0 < t := div_pos hB hsn
  have hpt : ∀ ω, |Z ω| ≤ (Z ω ^ 2 / t + t) / 2 := fun ω ↦ by
    have h := sq_nonneg (|Z ω| - t)
    have h2 : 2 * t * |Z ω| ≤ Z ω ^ 2 + t ^ 2 := by
      rw [← sq_abs (Z ω)]; linarith [h, show (|Z ω| - t) ^ 2 = |Z ω| ^ 2 - 2 * t * |Z ω| + t ^ 2
        by ring]
    have h3 : (Z ω ^ 2 / t + t) / 2 = (Z ω ^ 2 + t ^ 2) / (2 * t) := by field_simp
    rw [h3, le_div_iff₀ (by positivity)]
    linarith
  have hA : ∫ ω, |Z ω| ∂μ ≤ ∫ ω, (Z ω ^ 2 / t + t) / 2 ∂μ :=
    integral_mono hZi.abs (((hZ2i.div_const t).add (integrable_const t)).div_const 2) hpt
  have hB' : ∫ ω, (Z ω ^ 2 / t + t) / 2 ∂μ = ((∫ ω, Z ω ^ 2 ∂μ) / t + t) / 2 := by
    rw [integral_div, integral_add (hZ2i.div_const t) (integrable_const t), integral_div]
    simp
  have hC : ((∫ ω, Z ω ^ 2 ∂μ) / t + t) / 2 ≤ (B ^ 2 / n / t + t) / 2 := by
    have := div_le_div_of_nonneg_right hZ2 ht.le
    linarith
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnR.le
  have hD : B ^ 2 / n / t = t := by
    rw [div_eq_iff ht.ne']
    simp only [t]
    rw [div_mul_div_comm, ← sq, ← sq, hsq]
  have hE : ∫ ω, |Z ω| ∂μ ≤ t := by
    have := hA.trans (hB'.le.trans hC)
    rw [hD] at this
    linarith
  exact hE

/-- The cube `[-1, 1]^d` in `ℝ^d`. -/
def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Icc (-1 : ℝ) 1}

/-- The cube `[-1, 1]^d` is measurable. -/
theorem measurable_set_unit_cube : MeasurableSet (unitCube d) := by
  have : unitCube d = ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) ⁻¹' Icc (-1) 1 := by
    ext x; simp [unitCube]
  rw [this]
  exact MeasurableSet.iInter fun i ↦ measurableSet_Icc.preimage (by fun_prop)

/-- Points of the cube `[-1, 1]^d` have squared norm at most `d`. -/
theorem norm_sq_le_of_mem_unit_cube {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ unitCube d) :
    ‖y‖ ^ 2 ≤ d := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        rw [Real.norm_eq_abs, sq_abs]
        have := hy i
        nlinarith [this.1, this.2]
    _ = d := by simp

/-- Every real function is integrable for an empirical measure. -/
theorem integrable_empirical_measure {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Integrable f (empiricalMeasure n x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalMeasure]
  rw [empiricalMeasure]
  refine Integrable.smul_measure (integrable_finsetSum_measure.2 fun i _ ↦
    integrable_dirac (by simp)) (by simp [hn.ne'])

/-- The integral against an empirical measure is the sample average. -/
theorem integral_empirical_measure {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y, f y ∂(empiricalMeasure n x) = (n : ℝ)⁻¹ * ∑ i, f (x i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalMeasure]
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp
  · intro i _
    exact integrable_dirac (by simp)

section Smoothed

variable {sigma : ℝ}

/-- The constant `K` of the Gaussian domination bound `φ_{σ²}(x - y) ≤ K φ_{2σ²}(x)` for `y` in the
cube `[-1, 1]^d`. -/
noncomputable def smoothingConst (d : ℕ) (sigma : ℝ) : ℝ :=
  isoGaussianPDF d (sigma ^ 2) 0 / isoGaussianPDF d (2 * sigma ^ 2) 0 *
    Real.exp (d / (2 * sigma ^ 2))

/-- The Gaussian domination constant is positive. -/
theorem smoothing_const_pos (hs : sigma ≠ 0) : 0 < smoothingConst d sigma := by
  have hs2 : 0 < sigma ^ 2 := by positivity
  unfold smoothingConst
  have := iso_gaussian_pdf_pos hs2 (0 : EuclideanSpace ℝ (Fin d))
  have := iso_gaussian_pdf_pos (by positivity : 0 < 2 * sigma ^ 2) (0 : EuclideanSpace ℝ (Fin d))
  positivity

/-- Gaussian domination on the cube: for `y ∈ [-1, 1]^d`, `φ_{σ²}(x - y) ≤ K φ_{2σ²}(x)`. -/
theorem iso_gaussian_pdf_sub_le_of_mem_unit_cube (hs : sigma ≠ 0) (x : EuclideanSpace ℝ (Fin d))
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ unitCube d) :
    isoGaussianPDF d (sigma ^ 2) (x - y) ≤
      smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x :=
  iso_gaussian_pdf_sub_le (by positivity) x y (norm_sq_le_of_mem_unit_cube hy)

/-- The Lebesgue density `x ↦ ∫ φ_{σ²}(x - y) dP(y)` of the Gaussian smoothing of `P`. -/
noncomputable def smoothedDensity (d : ℕ) (sigma : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, isoGaussianPDF d (sigma ^ 2) (x - y) ∂P

/-- The smoothed density is measurable. -/
theorem measurable_smoothed_density (hs : sigma ≠ 0) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [SFinite P] : Measurable (smoothedDensity d sigma P) := by
  have hc : Continuous fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      isoGaussianPDF d (sigma ^ 2) (z.1 - z.2) :=
    (continuous_iso_gaussian_pdf (by positivity)).comp (by fun_prop)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- The smoothed density is nonnegative. -/
theorem smoothed_density_nonneg (P : Measure (EuclideanSpace ℝ (Fin d))) (hs : sigma ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ smoothedDensity d sigma P x :=
  integral_nonneg fun y ↦ (iso_gaussian_pdf_pos (by positivity) _).le

/-- For a law on the cube, the smoothed density is dominated by `K φ_{2σ²}`. -/
theorem smoothed_density_le (hs : sigma ≠ 0) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (hP : P (unitCube d) = 1) (x : EuclideanSpace ℝ (Fin d)) :
    smoothedDensity d sigma P x ≤ smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x := by
  have hae : ∀ᵐ y ∂P, y ∈ unitCube d :=
    (prob_compl_eq_zero_iff measurable_set_unit_cube).2 hP
  calc smoothedDensity d sigma P x ≤ ∫ _y, smoothingConst d sigma *
        isoGaussianPDF d (2 * sigma ^ 2) x ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y ↦ (iso_gaussian_pdf_pos
          (by positivity) _).le) (integrable_const _) (hae.mono fun y hy ↦ ?_)
        exact iso_gaussian_pdf_sub_le_of_mem_unit_cube hs x hy
    _ = _ := by simp

/-- `‖x‖` times the dominating function `K φ_{2σ²}(x)` is integrable. -/
private theorem integrable_norm_mul_dominant (hs : sigma ≠ 0) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      ‖x‖ * (smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x)) := by
  have := (integrable_norm_mul_iso_gaussian_pdf (d := d) (by positivity :
    0 < 2 * sigma ^ 2)).const_mul (smoothingConst d sigma)
  refine this.congr (ae_of_all _ fun x ↦ ?_)
  simp only; ring

/-- Weighted total variation bound: for a sample in the cube, `W₁` between the Gaussian smoothings
of its empirical measure and of `P` is at most `∫ ‖x‖ |p_n(x) - p(x)| dx`, by Kantorovich–Rubinstein
duality. -/
theorem wasserstein_e_dist_one_gaussian_smoothing_le (hs : sigma ≠ 0)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (hP : P (unitCube d) = 1)
    {n : ℕ} (hn : 1 ≤ n) (X : Fin n → EuclideanSpace ℝ (Fin d)) (hX : ∀ i, X i ∈ unitCube d) :
    TauCeti.wassersteinEDist 1 (gaussianSmoothing sigma (empiricalMeasure n X))
        (gaussianSmoothing sigma P) ≤
      ∫⁻ x, ENNReal.ofReal (‖x‖ * |(n : ℝ)⁻¹ * ∑ i, isoGaussianPDF d (sigma ^ 2) (x - X i) -
        smoothedDensity d sigma P x|) := by
  have := is_probability_measure_empirical_measure hn X
  have hae : ∀ᵐ y ∂P, y ∈ unitCube d := (prob_compl_eq_zero_iff measurable_set_unit_cube).2 hP
  have hPint : Integrable (fun x ↦ ‖x‖) P := by
    refine Integrable.of_bound (by fun_prop) (Real.sqrt d) (hae.mono fun y hy ↦ ?_)
    rw [Real.norm_eq_abs, abs_norm]
    simpa using Real.abs_le_sqrt (norm_sq_le_of_mem_unit_cube hy)
  have := is_probability_measure_gaussian_smoothing sigma P
  have := is_probability_measure_gaussian_smoothing sigma (empiricalMeasure n X)
  rw [TauCeti.wassersteinEDist_one_eq_iSup_apply_eq_zero
    (has_finite_moment_gaussian_smoothing sigma _ (integrable_empirical_measure X _))
    (has_finite_moment_gaussian_smoothing sigma P hPint) 0]
  refine iSup₂_le fun f hf ↦ iSup_le fun hf0 ↦ ?_
  have hfb : ∀ x, |f x| ≤ ‖x‖ := fun x ↦ by
    have := hf.dist_le_mul x 0
    simpa [hf0, Real.dist_eq] using this
  set φ := isoGaussianPDF d (sigma ^ 2)
  set B : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
    smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x
  have hφ0 : ∀ z, 0 ≤ φ z := fun z ↦ (iso_gaussian_pdf_pos (by positivity) z).le
  have hφm : Measurable φ := measurable_iso_gaussian_pdf (by positivity)
  have hIB := integrable_norm_mul_dominant (d := d) hs
  set pX : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ (n : ℝ)⁻¹ * ∑ i, φ (x - X i)
  set pP := smoothedDensity d sigma P
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpX0 : ∀ x, 0 ≤ pX x := fun x ↦ by
    simp only [pX]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ hφ0 _)
  have hpXB : ∀ x, pX x ≤ B x := fun x ↦ by
    simp only [pX]
    rw [inv_mul_le_iff₀ hnR]
    calc ∑ i, φ (x - X i) ≤ ∑ _i : Fin n, B x := Finset.sum_le_sum fun i _ ↦
          iso_gaussian_pdf_sub_le_of_mem_unit_cube hs x (hX i)
      _ = n * B x := by simp
  have hpP0 : ∀ x, 0 ≤ pP x := smoothed_density_nonneg P hs
  have hpPB : ∀ x, pP x ≤ B x := smoothed_density_le hs P hP
  have hpXm : Measurable pX := (Finset.measurable_sum _ fun i _ ↦
    hφm.comp (measurable_id.sub_const _)).const_mul _
  have hpPm : Measurable pP := measurable_smoothed_density hs P
  have hfm : Measurable f := hf.continuous.measurable
  have hint : ∀ q : EuclideanSpace ℝ (Fin d) → ℝ, Measurable q → (∀ x, |q x| ≤ B x) →
      Integrable (fun x ↦ f x * q x) := fun q hq hqB ↦ by
    refine hIB.mono' (hfm.mul hq).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb x) (hqB x) (abs_nonneg _) (norm_nonneg _)
  -- the empirical side
  have hemp : ∫ x, f x ∂(gaussianSmoothing sigma (empiricalMeasure n X)) =
      ∫ x, f x * pX x := by
    rw [integral_gaussian_smoothing_eq hs _ (integrable_empirical_measure X _) hf.continuous hfb,
      integral_empirical_measure]
    have hi : ∀ i, Integrable (fun x ↦ f x * φ (x - X i)) := fun i ↦
      hint _ (hφm.comp (measurable_id.sub_const _)) fun x ↦ by
        rw [abs_of_nonneg (hφ0 _)]; exact iso_gaussian_pdf_sub_le_of_mem_unit_cube hs x (hX i)
    have hfun : (fun x ↦ f x * pX x) =
        fun x : EuclideanSpace ℝ (Fin d) ↦ ∑ i : Fin n, (n : ℝ)⁻¹ * (f x * φ (x - X i)) := by
      funext x; simp only [pX, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hfun, integral_finsetSum _ fun i _ ↦ (hi i).const_mul _]
    simp only [integral_const_mul, φ, ← Finset.mul_sum]
  -- the population side
  have hpop : ∫ x, f x ∂(gaussianSmoothing sigma P) = ∫ x, f x * pP x := by
    rw [integral_gaussian_smoothing_eq hs _ hPint hf.continuous hfb]
    have hI2 : Integrable (Function.uncurry fun (y : EuclideanSpace ℝ (Fin d))
        (x : EuclideanSpace ℝ (Fin d)) ↦ f x * φ (x - y)) (P.prod volume) := by
      refine (hIB.comp_snd P).mono' ?_ ?_
      · exact (((hfm.comp measurable_snd).mul (hφm.comp (measurable_snd.sub measurable_fst))))
          |>.aestronglyMeasurable
      · have h1 : ∀ᵐ z ∂(P.prod (volume : Measure (EuclideanSpace ℝ (Fin d)))),
            z.1 ∈ unitCube d := Measure.quasiMeasurePreserving_fst.ae hae
        filter_upwards [h1] with z hz
        rcases z with ⟨y, x⟩
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (hφ0 _)]
        exact mul_le_mul (hfb _) (iso_gaussian_pdf_sub_le_of_mem_unit_cube hs _ hz)
          (hφ0 _) (norm_nonneg _)
    rw [integral_integral_swap hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [pP, smoothedDensity]
    rw [integral_const_mul]
  have hiX := hint pX hpXm fun x ↦ by rw [abs_of_nonneg (hpX0 x)]; exact hpXB x
  have hiP := hint pP hpPm fun x ↦ by rw [abs_of_nonneg (hpP0 x)]; exact hpPB x
  have hdiff : ∀ x, |pX x - pP x| ≤ B x := fun x ↦
    abs_sub_le_iff.2 ⟨by linarith [hpXB x, hpP0 x], by linarith [hpPB x, hpX0 x]⟩
  have hiT : Integrable (fun x ↦ ‖x‖ * |pX x - pP x|) := by
    refine hIB.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_abs]
    exact mul_le_mul_of_nonneg_left (hdiff x) (norm_nonneg _)
  rw [hemp, hpop, ← integral_sub hiX hiP, ← ofReal_integral_eq_lintegral_ofReal hiT
    (ae_of_all _ fun x ↦ by positivity)]
  refine ENNReal.ofReal_le_ofReal (integral_mono (hiX.sub hiP) hiT fun x ↦ ?_)
  simp only
  rw [← mul_sub]
  calc f x * (pX x - pP x) ≤ |f x * (pX x - pP x)| := le_abs_self _
    _ = |f x| * |pX x - pP x| := abs_mul _ _
    _ ≤ ‖x‖ * |pX x - pP x| := mul_le_mul_of_nonneg_right (hfb x) (abs_nonneg _)

/-- The constant `∫ ‖x‖ K φ_{2σ²}(x) dx` of the smoothed empirical `W₁` rate. -/
noncomputable def smoothingMoment (d : ℕ) (sigma : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin d),
    ‖x‖ * (smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x)

/-- The constant `smoothingMoment` is nonnegative. -/
theorem smoothing_moment_nonneg (hs : sigma ≠ 0) : 0 ≤ smoothingMoment d sigma :=
  integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (mul_nonneg (smoothing_const_pos hs).le
    (iso_gaussian_pdf_pos (by positivity) _).le)

/-- The expected weighted total variation between smoothed empirical and population densities is at
most `smoothingMoment d σ / √n`. -/
theorem lintegral_lintegral_smoothed_density_le (hs : sigma ≠ 0)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (hP : P (unitCube d) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ X, (∫⁻ x, ENNReal.ofReal (‖x‖ * |(n : ℝ)⁻¹ * ∑ i, isoGaussianPDF d (sigma ^ 2) (x - X i) -
        smoothedDensity d sigma P x|)) ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (smoothingMoment d sigma / Real.sqrt n) := by
  have hae : ∀ᵐ y ∂P, y ∈ unitCube d := (prob_compl_eq_zero_iff measurable_set_unit_cube).2 hP
  set φ := isoGaussianPDF d (sigma ^ 2)
  have hφm : Measurable φ := measurable_iso_gaussian_pdf (by positivity)
  have hφ0 : ∀ z, 0 ≤ φ z := fun z ↦ (iso_gaussian_pdf_pos (by positivity) z).le
  have hpPm : Measurable (smoothedDensity d sigma P) := measurable_smoothed_density hs P
  set B : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
    smoothingConst d sigma * isoGaussianPDF d (2 * sigma ^ 2) x
  have hBpos : ∀ x, 0 < B x := fun x ↦
    mul_pos (smoothing_const_pos hs) (iso_gaussian_pdf_pos (by positivity) x)
  have hF : Measurable fun z : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ↦
      ENNReal.ofReal (‖z.2‖ * |(n : ℝ)⁻¹ * ∑ i, φ (z.2 - z.1 i) -
        smoothedDensity d sigma P z.2|) := by
    refine ENNReal.measurable_ofReal.comp (measurable_snd.norm.mul ?_)
    refine (((Finset.measurable_sum _ fun i _ ↦ hφm.comp (measurable_snd.sub
      ((measurable_pi_apply i).comp measurable_fst))).const_mul _).sub
      (hpPm.comp measurable_snd)).abs
  rw [lintegral_lintegral_swap hF.aemeasurable]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  calc ∫⁻ x, ∫⁻ X, ENNReal.ofReal (‖x‖ * |(n : ℝ)⁻¹ * ∑ i, φ (x - X i) -
          smoothedDensity d sigma P x|) ∂(Measure.pi fun _ : Fin n ↦ P)
      ≤ ∫⁻ x, ENNReal.ofReal (‖x‖ * B x / Real.sqrt n) := by
        refine lintegral_mono fun x ↦ ?_
        set g : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ φ (x - y)
        have hgm : Measurable g := hφm.comp (measurable_const.sub measurable_id)
        have hgB : ∀ᵐ y ∂P, |g y| ≤ B x := hae.mono fun y hy ↦ by
          rw [abs_of_nonneg (hφ0 _)]; exact iso_gaussian_pdf_sub_le_of_mem_unit_cube hs x hy
        have key := integral_abs_sample_mean_sub_le P hgm (hBpos x) hgB hn
        change ∫⁻ X, ENNReal.ofReal (‖x‖ * |(n : ℝ)⁻¹ * ∑ i, g (X i) - ∫ y, g y ∂P|)
          ∂(Measure.pi fun _ : Fin n ↦ P) ≤ _
        have hZi : Integrable (fun X : Fin n → EuclideanSpace ℝ (Fin d) ↦
            ‖x‖ * |(n : ℝ)⁻¹ * ∑ i, g (X i) - ∫ y, g y ∂P|) (Measure.pi fun _ : Fin n ↦ P) := by
          refine Integrable.const_mul ?_ _
          refine Integrable.of_bound ((((Finset.measurable_sum _ fun i _ ↦
            hgm.comp (measurable_pi_apply i)).const_mul _).sub_const _).abs.aestronglyMeasurable)
            ((φ 0) + |∫ y, g y ∂P|) (ae_of_all _ fun X ↦ ?_)
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn
          have ha0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i, g (X i) :=
            mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ hφ0 _)
          have ha1 : (n : ℝ)⁻¹ * ∑ i, g (X i) ≤ φ 0 := by
            rw [inv_mul_le_iff₀ hnR]
            calc ∑ i, g (X i) ≤ ∑ _i : Fin n, φ 0 := Finset.sum_le_sum fun i _ ↦
                  iso_gaussian_pdf_le_iso_gaussian_pdf_zero (by positivity) _
              _ = n * φ 0 := by simp
          rw [Real.norm_eq_abs, abs_abs]
          calc |(n : ℝ)⁻¹ * ∑ i, g (X i) - ∫ y, g y ∂P| ≤
              |(n : ℝ)⁻¹ * ∑ i, g (X i)| + |∫ y, g y ∂P| := abs_sub _ _
            _ ≤ φ 0 + |∫ y, g y ∂P| := by rw [abs_of_nonneg ha0]; linarith
        rw [← ofReal_integral_eq_lintegral_ofReal hZi (ae_of_all _ fun X ↦ by positivity),
          integral_const_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = ENNReal.ofReal (smoothingMoment d sigma / Real.sqrt n) := by
        rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_norm_mul_dominant hs).div_const _)
          (ae_of_all _ fun x ↦ by have := hBpos x; positivity), integral_div]
        rfl

/-- The parametric rate of Gaussian-smoothed empirical `W₁` with an explicit constant: for a law `P`
on `[-1, 1]^d` and `n ≥ 1`, `E W₁(μ_n * N_σ, P * N_σ) ≤ smoothingMoment d σ / √n`. -/
theorem integral_wasserstein_e_dist_gaussian_smoothing_le (hs : sigma ≠ 0)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (hP : P (unitCube d) = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ X, (TauCeti.wassersteinEDist 1 (gaussianSmoothing sigma (empiricalMeasure n X))
        (gaussianSmoothing sigma P)).toReal ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      smoothingMoment d sigma / Real.sqrt n := by
  set μ := Measure.pi fun _ : Fin n ↦ P
  have hae : ∀ᵐ y ∂P, y ∈ unitCube d := (prob_compl_eq_zero_iff measurable_set_unit_cube).2 hP
  have haeX : ∀ᵐ X ∂μ, ∀ i, X i ∈ unitCube d := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n ↦ P) i).quasiMeasurePreserving.ae
      (p := fun y ↦ y ∈ unitCube d) hae
  set φ := isoGaussianPDF d (sigma ^ 2)
  have hφm : Measurable φ := measurable_iso_gaussian_pdf (by positivity)
  have hpPm : Measurable (smoothedDensity d sigma P) := measurable_smoothed_density hs P
  set T : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ := fun X ↦
    ∫⁻ x, ENNReal.ofReal (‖x‖ * |(n : ℝ)⁻¹ * ∑ i, φ (x - X i) - smoothedDensity d sigma P x|)
  have hF : Measurable fun z : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ↦
      ENNReal.ofReal (‖z.2‖ * |(n : ℝ)⁻¹ * ∑ i, φ (z.2 - z.1 i) -
        smoothedDensity d sigma P z.2|) := by
    refine ENNReal.measurable_ofReal.comp (measurable_snd.norm.mul ?_)
    refine (((Finset.measurable_sum _ fun i _ ↦ hφm.comp (measurable_snd.sub
      ((measurable_pi_apply i).comp measurable_fst))).const_mul _).sub
      (hpPm.comp measurable_snd)).abs
  have hTm : Measurable T := hF.lintegral_prod_right'
  have hTle : ∫⁻ X, T X ∂μ ≤ ENNReal.ofReal (smoothingMoment d sigma / Real.sqrt n) :=
    lintegral_lintegral_smoothed_density_le hs P hP hn
  have hTne : ∫⁻ X, T X ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTle
  have hTfin : ∀ᵐ X ∂μ, T X < ⊤ := ae_lt_top hTm hTne
  calc ∫ X, (TauCeti.wassersteinEDist 1 (gaussianSmoothing sigma (empiricalMeasure n X))
        (gaussianSmoothing sigma P)).toReal ∂μ ≤ ∫ X, (T X).toReal ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
          (integrable_toReal_of_lintegral_ne_top hTm.aemeasurable hTne) ?_
        filter_upwards [haeX, hTfin] with X hX hXT
        exact ENNReal.toReal_mono hXT.ne
          (wasserstein_e_dist_one_gaussian_smoothing_le hs P hP hn X hX)
    _ = (∫⁻ X, T X ∂μ).toReal := integral_toReal hTm.aemeasurable hTfin
    _ ≤ smoothingMoment d sigma / Real.sqrt n :=
        ENNReal.toReal_le_of_le_ofReal (div_nonneg (smoothing_moment_nonneg hs)
          (Real.sqrt_nonneg _)) hTle

end Smoothed

end CKSD
