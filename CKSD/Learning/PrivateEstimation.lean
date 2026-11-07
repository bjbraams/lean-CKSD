module

public import CKSD.Learning.Basic
public import CKSD.Learning.Privacy
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Distributions.Laplace.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Statlib.Divergence.BretagnolleHuber
public import Statlib.Divergence.TotalVariation.Integral
public import Statlib.Divergence.KullbackLeibler.CondKL
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Private estimation of a bounded mean

Data sets are vectors in `ℝⁿ`, neighbouring when they differ in at most one coordinate. A
central mechanism is a Markov kernel from data sets to real releases. The clipped Laplace
mechanism releases the mean of the data clipped to `[-1,1]` plus Laplace noise of scale
`2 / (n ε)`. Local mechanisms are noninteractive: individual `i` releases `Zᵢ ∼ Qᵢ(· | Xᵢ)`
through an `ε`-locally private kernel to the real line, and an estimator is a measurable
function of the releases. The target is the mean of an unknown law on `[-1,1]` and the risk is
the mean squared error.

The Laplace law and its moments are TauCeti's (`TauCeti.Probability.laplaceMeasure`).
Source: GAPS 107.66.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Data sets in `ℝⁿ` are neighbouring when they differ in at most one coordinate. -/
def IsHammingNeighbor {n : ℕ} (d d' : Fin n → ℝ) : Prop :=
  (Finset.univ.filter fun i ↦ d i ≠ d' i).card ≤ 1

/-- Clipping to `[-1,1]`. -/
def clipUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- Mean of a data set clipped to `[-1,1]`. -/
def clippedMean {n : ℕ} (d : Fin n → ℝ) : ℝ := (∑ i, clipUnit (d i)) / n

/-- The clipped Laplace mean mechanism with noise scale `2 / (n ε)`. -/
def laplaceMeanMechanism (n : ℕ) (ε : ℝ) : Kernel (Fin n → ℝ) ℝ where
  toFun d := TauCeti.Probability.laplaceMeasure (clippedMean d) (2 / (n * ε))
  measurable' := by
    have hc : Measurable fun d : Fin n → ℝ ↦ clippedMean d := by
      unfold clippedMean clipUnit
      fun_prop
    exact TauCeti.Probability.measurable_laplaceMeasure.comp (hc.prodMk measurable_const)

/-- Mean squared error of a central mechanism for the mean of `P`, from `n` observations.
It is a lower Lebesgue integral in `ℝ≥0∞`, so a mechanism with infinite error has risk `∞`
rather than the junk value `0` of a non-integrable Bochner integral. -/
def centralMeanRisk {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ) (P : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ∫⁻ y, ENNReal.ofReal ((y - ∫ x, x ∂P) ^ 2) ∂M d ∂Measure.pi fun _ : Fin n ↦ P

/-- Mean squared error of a noninteractive local protocol with release kernels `Q` and
estimator `est`, for the mean of `P`, as a lower Lebesgue integral in `ℝ≥0∞`. -/
def localMeanRisk {n : ℕ} (Q : Fin n → Kernel ℝ ℝ) (est : (Fin n → ℝ) → ℝ) (P : Measure ℝ) :
    ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((est z - ∫ x, x ∂P) ^ 2) ∂Measure.pi fun i ↦ Q i ∘ₘ P

/-- Changing one coordinate moves the clipped mean by at most `2 / n`. -/
theorem abs_clippedMean_sub_le {n : ℕ} {d d' : Fin n → ℝ} (h : IsHammingNeighbor d d') :
    |clippedMean d - clippedMean d'| ≤ 2 / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [clippedMean]
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : |∑ i, (clipUnit (d i) - clipUnit (d' i))| ≤ 2 := by
    let S := Finset.univ.filter fun i ↦ d i ≠ d' i
    calc |∑ i, (clipUnit (d i) - clipUnit (d' i))|
        ≤ ∑ i, |clipUnit (d i) - clipUnit (d' i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |clipUnit (d i) - clipUnit (d' i)| := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_).symm
        have : d i = d' i := by simpa [S] using hi
        simp [this]
      _ ≤ ∑ _i ∈ S, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        have h1 := hclip (d i); have h2 := hclip (d' i)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      _ = 2 * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * 1 := by
        have : (S.card : ℝ) ≤ 1 := by exact_mod_cast h
        linarith
      _ = 2 := by norm_num
  unfold clippedMean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnr]
  exact div_le_div_of_nonneg_right hsum hnr.le

/-- Shifting the location of a Laplace density by `δ` changes it by at most `e^{|δ|/b}`. -/
theorem laplacePDF_le_exp_mul {b : ℝ} (hb : 0 < b) (m m' x : ℝ) :
    TauCeti.Probability.laplacePDF m b x ≤
      ENNReal.ofReal (Real.exp (|m - m'| / b)) * TauCeti.Probability.laplacePDF m' b x := by
  rw [TauCeti.Probability.laplacePDF_of_pos hb, TauCeti.Probability.laplacePDF_of_pos hb,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have htri : |x - m'| ≤ |x - m| + |m - m'| := by
    calc |x - m'| = |(x - m) + (m - m')| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hexp : Real.exp (-|x - m| / b) ≤ Real.exp (|m - m'| / b) * Real.exp (-|x - m'| / b) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [← add_div, div_le_div_iff_of_pos_right hb]
    linarith
  have h2b : 0 ≤ (2 * b)⁻¹ := by positivity
  calc (2 * b)⁻¹ * Real.exp (-|x - m| / b)
      ≤ (2 * b)⁻¹ * (Real.exp (|m - m'| / b) * Real.exp (-|x - m'| / b)) :=
        mul_le_mul_of_nonneg_left hexp h2b
    _ = _ := by ring

/-- GAPS 107.66: the clipped Laplace mean mechanism is `ε`-differentially private. -/
theorem isDifferentiallyPrivate_laplaceMeanMechanism (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε : 0 < ε) :
    IsDifferentiallyPrivate IsHammingNeighbor ε 0 (laplaceMeanMechanism n ε) := by
  intro d d' hdd' A _
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set b : ℝ := 2 / (n * ε) with hb_def
  have hb : 0 < b := by positivity
  have hratio : |clippedMean d - clippedMean d'| / b ≤ ε := by
    rw [div_le_iff₀ hb, hb_def]
    calc |clippedMean d - clippedMean d'| ≤ 2 / n := abs_clippedMean_sub_le hdd'
      _ = ε * (2 / (n * ε)) := by field_simp
  have hk : ∀ e : Fin n → ℝ, laplaceMeanMechanism n ε e =
      volume.withDensity (TauCeti.Probability.laplacePDF (clippedMean e) b) := fun e ↦
    TauCeti.Probability.laplaceMeasure_eq_withDensity _ _
  rw [ENNReal.ofReal_zero, add_zero, hk, hk, withDensity_apply' _ A, withDensity_apply' _ A,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x ↦ ?_
  calc TauCeti.Probability.laplacePDF (clippedMean d) b x
      ≤ ENNReal.ofReal (Real.exp (|clippedMean d - clippedMean d'| / b)) *
          TauCeti.Probability.laplacePDF (clippedMean d') b x := laplacePDF_le_exp_mul hb _ _ x
    _ ≤ ENNReal.ofReal (Real.exp ε) * TauCeti.Probability.laplacePDF (clippedMean d') b x := by
      gcongr

/-- Mean squared deviation of a Laplace law from a point: squared bias plus variance `2b²`. -/
theorem integral_sq_sub_laplaceMeasure {b : ℝ} (hb : 0 < b) (m θ : ℝ) :
    ∫ y, (y - θ) ^ 2 ∂TauCeti.Probability.laplaceMeasure m b = (m - θ) ^ 2 + 2 * b ^ 2 := by
  have := TauCeti.Probability.isProbabilityMeasure_laplaceMeasure hb m
  have h2 := TauCeti.Probability.integral_pow_abs_sub_laplaceMeasure hb m 2
  have hi2 := TauCeti.Probability.integrable_pow_abs_sub_laplaceMeasure (b := b) m 2
  have hi1 := TauCeti.Probability.integrable_sub_const_laplaceMeasure (b := b) m
  have h1 := TauCeti.Probability.integral_sub_const_laplaceMeasure (b := b) m
  simp only [sq_abs] at h2 hi2
  have hpt : ∀ y : ℝ, (y - θ) ^ 2 = ((y - m) ^ 2 + 2 * (m - θ) * (y - m)) + (m - θ) ^ 2 := by
    intro y; ring
  rw [show (fun y : ℝ ↦ (y - θ) ^ 2) = fun y ↦
    ((y - m) ^ 2 + 2 * (m - θ) * (y - m)) + (m - θ) ^ 2 from funext hpt]
  rw [integral_add (f := fun y ↦ (y - m) ^ 2 + 2 * (m - θ) * (y - m))
      (g := fun _ ↦ (m - θ) ^ 2) (hi2.add (hi1.const_mul _)) (integrable_const _),
    integral_add (f := fun y ↦ (y - m) ^ 2) (g := fun y ↦ 2 * (m - θ) * (y - m)) hi2
      (hi1.const_mul _), integral_const_mul, h1, h2, integral_const]
  simp only [probReal_univ, one_smul, Nat.factorial_two, Nat.cast_ofNat, mul_zero, add_zero]
  ring

/-- The squared deviation from a point is integrable under a Laplace law. -/
theorem integrable_sq_sub_laplaceMeasure {b : ℝ} (hb : 0 < b) (m θ : ℝ) :
    Integrable (fun y ↦ (y - θ) ^ 2) (TauCeti.Probability.laplaceMeasure m b) := by
  have := TauCeti.Probability.isProbabilityMeasure_laplaceMeasure hb m
  have hi2 := TauCeti.Probability.integrable_pow_abs_sub_laplaceMeasure (b := b) m 2
  have hi1 := TauCeti.Probability.integrable_sub_const_laplaceMeasure (b := b) m
  simp only [sq_abs] at hi2
  rw [show (fun y : ℝ ↦ (y - θ) ^ 2) = fun y ↦
    ((y - m) ^ 2 + 2 * (m - θ) * (y - m)) + (m - θ) ^ 2 from funext fun y ↦ by ring]
  exact (hi2.add (hi1.const_mul _)).add (integrable_const _)

/-- On laws supported by `[-1,1]` the clipped sample mean has mean squared error at most
`1/n`. -/
theorem integral_clippedMean_sub_sq_le (n : ℕ) (hn : 0 < n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂Measure.pi (fun _ : Fin n ↦ P) ≤ 1 / n := by
  set π : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hclipm : Measurable clipUnit := by unfold clipUnit; fun_prop
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hae : ∀ᵐ x ∂P, clipUnit x = x := by
    have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
      fun x hx ↦ by simpa using hx
    filter_upwards [hmem] with x hx
    simp only [clipUnit, min_eq_right hx.2, max_eq_right hx.1]
  have hθ : ∫ x, clipUnit x ∂P = ∫ x, x ∂P := integral_congr_ae hae
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i d ↦ clipUnit (d i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ hclipm.comp (measurable_pi_apply i)
  have hYb : ∀ i d, ‖Y i d‖ ≤ 1 := fun i d ↦ by
    rw [Real.norm_eq_abs, abs_le]; exact ⟨(hclip _).1, (hclip _).2⟩
  have hYL : ∀ i, MemLp (Y i) 2 π := fun i ↦
    MemLp.of_bound (hYm i).aestronglyMeasurable 1 (Eventually.of_forall (hYb i))
  have hYint : ∀ i, ∫ d, Y i d ∂π = ∫ x, x ∂P := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin n ↦ P) i
    have := integral_map (μ := π) hp.measurable.aemeasurable (f := clipUnit)
      hclipm.aestronglyMeasurable
    rw [hp.map_eq] at this
    rw [← hθ, this]
  have hmean_eq : (fun d ↦ clippedMean d) = fun d ↦ (n : ℝ)⁻¹ * (∑ i, Y i) d := by
    funext d
    simp only [clippedMean, Finset.sum_apply, Y]
    rw [div_eq_inv_mul]
  have hsumL : MemLp (∑ i, Y i) 2 π := memLp_finsetSum' _ fun i _ ↦ hYL i
  have hEmean : ∫ d, clippedMean d ∂π = ∫ x, x ∂P := by
    rw [hmean_eq, integral_const_mul]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hYL i).integrable one_le_two]
    simp only [hYint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hvar_eq : ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂π = ProbabilityTheory.variance (fun d ↦ clippedMean d) π := by
    rw [variance_eq_integral (by rw [hmean_eq]; exact (hsumL.aemeasurable.const_mul _)), hEmean]
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j ↦ Y i ⟂ᵢ[π] Y j := by
    intro i _ j _ hij
    exact (iIndepFun_pi (X := fun _ : Fin n ↦ clipUnit)
      (fun _ ↦ hclipm.aemeasurable)).indepFun hij
  have hvsum : ProbabilityTheory.variance (∑ i, Y i) π = ∑ i, ProbabilityTheory.variance (Y i) π :=
    IndepFun.variance_sum (fun i _ ↦ hYL i) hindep
  have hvY : ∀ i, ProbabilityTheory.variance (Y i) π ≤ 1 := by
    intro i
    have := variance_le_sq_of_bounded (μ := π) (a := -1) (b := 1)
      (Eventually.of_forall fun d ↦ hclip (d i)) (hYm i).aemeasurable
    norm_num at this
    exact this
  rw [hvar_eq, hmean_eq, variance_const_mul, hvsum]
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, ProbabilityTheory.variance (Y i) π ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvY i) (by positivity)
    _ = 1 / n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp

/-- GAPS 107.66: on laws supported by `[-1,1]`, the clipped Laplace mean mechanism has mean
squared error at most `1/n + 8/(n ε)²`. -/
theorem centralMeanRisk_laplaceMeanMechanism_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    centralMeanRisk (laplaceMeanMechanism n ε) P ≤ ENNReal.ofReal (1 / n + 8 / (n * ε) ^ 2) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set b : ℝ := 2 / (n * ε) with hb_def
  have hb : 0 < b := by positivity
  have hinner : ∀ d : Fin n → ℝ, ∫ y, (y - ∫ x, x ∂P) ^ 2 ∂laplaceMeanMechanism n ε d =
      (clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2 := fun d ↦
    integral_sq_sub_laplaceMeasure hb _ _
  have hclipm : Measurable clipUnit := by unfold clipUnit; fun_prop
  have hcm : Measurable fun d : Fin n → ℝ ↦ clippedMean d := by
    unfold clippedMean; fun_prop
  have hbdd : ∀ d : Fin n → ℝ, ‖(clippedMean d - ∫ x, x ∂P) ^ 2‖ ≤ (1 + |∫ x, x ∂P|) ^ 2 := by
    intro d
    have hc : |clippedMean d| ≤ 1 := by
      unfold clippedMean
      rw [abs_div, abs_of_pos hnr, div_le_one hnr]
      calc |∑ i, clipUnit (d i)| ≤ ∑ i, |clipUnit (d i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
          rw [abs_le]
          exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
        _ = n := by simp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := abs_sub (clippedMean d) (∫ x, x ∂P)
    nlinarith [abs_nonneg (clippedMean d - ∫ x, x ∂P), sq_abs (clippedMean d - ∫ x, x ∂P)]
  have hint : Integrable (fun d : Fin n → ℝ ↦ (clippedMean d - ∫ x, x ∂P) ^ 2)
      (Measure.pi fun _ : Fin n ↦ P) :=
    Integrable.of_bound ((hcm.sub_const _).pow_const 2).aestronglyMeasurable _
      (Eventually.of_forall hbdd)
  have hinner' : ∀ d : Fin n → ℝ,
      ∫⁻ y, ENNReal.ofReal ((y - ∫ x, x ∂P) ^ 2) ∂laplaceMeanMechanism n ε d =
        ENNReal.ofReal ((clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2) := fun d ↦ by
    have hI : Integrable (fun y ↦ (y - ∫ x, x ∂P) ^ 2) (laplaceMeanMechanism n ε d) :=
      integrable_sq_sub_laplaceMeasure hb _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ ↦ sq_nonneg _), hinner d]
  unfold centralMeanRisk
  simp_rw [hinner']
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun d ↦ (clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2)
    (hint.add (integrable_const _)) (ae_of_all _ fun _ ↦ by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_add hint (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  have h1 := integral_clippedMean_sub_sq_le n hn P hP
  have h2 : 2 * b ^ 2 = 8 / (n * ε) ^ 2 := by rw [hb_def]; field_simp; ring
  linarith

/-- The clipped Laplace mean mechanism is a Markov kernel for positive `n` and `ε`. -/
theorem isMarkovKernel_laplaceMeanMechanism (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    IsMarkovKernel (laplaceMeanMechanism n ε) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨fun d ↦ ?_⟩
  exact TauCeti.Probability.isProbabilityMeasure_laplaceMeasure (by positivity) _

/-- The mean of a law supported by `[-1,1]` lies in `[-1,1]`. -/
theorem abs_integral_le_one_of_support (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Icc (-1) 1)ᶜ = 0) : |∫ x, x ∂P| ≤ 1 := by
  have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
    fun x hx ↦ by simpa using hx
  have h := norm_integral_le_of_norm_le_const (C := 1) (hmem.mono fun x hx ↦ by
    rw [Real.norm_eq_abs, abs_le]; exact hx)
  simpa [Real.norm_eq_abs] using h

/-- GAPS 107.66, central minimax upper bound: for `0 < ε ≤ 1` some `ε`-differentially private
mechanism (the clipped Laplace mean, or the constant release `0` when `1` is the smaller
rate) has mean squared error at most `8 min(1, 1/n + 1/(nε)²)` for every law on `[-1,1]`. -/
theorem exists_centralMeanRisk_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) :
    ∃ M : Kernel (Fin n → ℝ) ℝ, IsMarkovKernel M ∧
      IsDifferentiallyPrivate IsHammingNeighbor ε 0 M ∧
      ∀ P : Measure ℝ, IsProbabilityMeasure P → P (Icc (-1) 1)ᶜ = 0 →
        centralMeanRisk M P ≤ ENNReal.ofReal (8 * min 1 (1 / n + 1 / (n * ε) ^ 2)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hsmall : 1 ≤ 1 / n + 1 / (n * ε) ^ 2
  · refine ⟨Kernel.const _ (Measure.dirac 0), inferInstance, ?_, fun P hP1 hP ↦ ?_⟩
    · intro d d' _ A _
      simp only [Kernel.const_apply, ENNReal.ofReal_zero, add_zero]
      calc (Measure.dirac (0 : ℝ)) A = 1 * (Measure.dirac (0 : ℝ)) A := (one_mul _).symm
        _ ≤ ENNReal.ofReal (Real.exp ε) * (Measure.dirac (0 : ℝ)) A := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.1.le)
    · rw [min_eq_left hsmall]
      unfold centralMeanRisk
      simp only [Kernel.const_apply, lintegral_dirac, zero_sub, even_two, Even.neg_pow,
        lintegral_const, measure_univ, mul_one]
      apply ENNReal.ofReal_le_ofReal
      have := abs_integral_le_one_of_support P hP
      nlinarith [abs_nonneg (∫ x, x ∂P), sq_abs (∫ x, x ∂P)]
  · push Not at hsmall
    refine ⟨laplaceMeanMechanism n ε, isMarkovKernel_laplaceMeanMechanism n hn ε hε.1,
      isDifferentiallyPrivate_laplaceMeanMechanism n hn ε hε.1, fun P hP1 hP ↦ ?_⟩
    rw [min_eq_right hsmall.le]
    refine (centralMeanRisk_laplaceMeanMechanism_le n hn ε hε.1 P hP).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h8 : 8 / (n * ε) ^ 2 = 8 * (1 / (n * ε) ^ 2) := by ring
    have hpos : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith

/-! ### Two-point lower bounds for the central mean risk -/

/-- Integrals against the Bernoulli law `Ber(1, 0, p)` on the real line. -/
theorem integral_bernoulliMeasure_one_zero (p : unitInterval) (f : ℝ → ℝ) :
    ∫ x, f x ∂(Ber((1 : ℝ), 0, p)) = p * f 1 + (1 - p) * f 0 := by
  rw [bernoulliMeasure_def, integral_add_measure, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac]
  · simp [NNReal.smul_def, unitInterval.coe_symm_eq]
  · exact (integrable_dirac (by simp)).smul_measure_nnreal
  · exact (integrable_dirac (by simp)).smul_measure_nnreal

/-- The Bernoulli law `Ber(1, 0, p)` has mean `p`. -/
theorem integral_id_bernoulliMeasure_one_zero (p : unitInterval) :
    ∫ x, x ∂(Ber((1 : ℝ), 0, p)) = p := by
  rw [integral_bernoulliMeasure_one_zero p fun x ↦ x]
  ring

/-- The Bernoulli law `Ber(1, 0, p)` is supported by `[-1,1]`. -/
theorem bernoulliMeasure_one_zero_compl_Icc (p : unitInterval) :
    (Ber((1 : ℝ), 0, p)) (Icc (-1) 1)ᶜ = 0 :=
  bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_Icc.compl
    (by simp) (by simp)

/-- Group privacy: a mechanism that is `ε`-differentially private for Hamming neighbours
changes the probability of an event by at most the factor `exp(ε k)` between data sets that
differ in at most `k` coordinates. -/
theorem kernel_apply_le_exp_mul_card {n : ℕ} {M : Kernel (Fin n → ℝ) ℝ} {ε : ℝ}
    (hM : IsDifferentiallyPrivate IsHammingNeighbor ε 0 M) {B : Set ℝ} (hB : MeasurableSet B) :
    ∀ (s : Finset (Fin n)) (d d' : Fin n → ℝ), (∀ i ∉ s, d i = d' i) →
      M d B ≤ ENNReal.ofReal (Real.exp (ε * s.card)) * M d' B := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro d d' h
    have : d = d' := funext fun i ↦ h i (Finset.notMem_empty i)
    simp [this]
  | insert a s ha ih =>
    intro d d' h
    set d'' := Function.update d a (d' a)
    have hnb : IsHammingNeighbor d d'' := by
      unfold IsHammingNeighbor
      refine (Finset.card_le_card (t := {a}) fun i hi ↦ ?_).trans (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hia
      rw [Finset.mem_singleton] at hia
      exact hi (by simp [d'', Function.update_of_ne hia])
    have h1 := hM d d'' hnb B hB
    have h2 := ih d'' d' fun i hi ↦ by
      by_cases hia : i = a
      · subst hia; simp [d'']
      · simp only [d'', Function.update_of_ne hia]
        exact h i (by simp [hia, hi])
    rw [ENNReal.ofReal_zero, add_zero] at h1
    calc M d B ≤ ENNReal.ofReal (Real.exp ε) * M d'' B := h1
      _ ≤ ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (Real.exp (ε * s.card)) * M d' B) := by
        gcongr
      _ = ENNReal.ofReal (Real.exp (ε * (insert a s).card)) * M d' B := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          Finset.card_insert_of_notMem ha]
        push_cast
        ring_nf

/-- A lower bound for the central mean risk on a set of releases far from the mean. -/
theorem ofReal_mul_comp_le_centralMeanRisk {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ)
    (P : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) {r : ℝ}
    (hr : ∀ y ∈ B, r ≤ (y - ∫ x, x ∂P) ^ 2) :
    ENNReal.ofReal r * (M ∘ₘ Measure.pi fun _ : Fin n ↦ P) B ≤ centralMeanRisk M P := by
  rw [Measure.bind_apply hB M.aemeasurable, ← lintegral_const_mul _ (M.measurable_coe hB)]
  unfold centralMeanRisk
  refine lintegral_mono fun d ↦ ?_
  rw [← lintegral_indicator_const hB]
  refine lintegral_mono fun y ↦ ?_
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (hr y hy)
  · rw [indicator_of_notMem hy]
    exact zero_le

/-- Le Cam's two-point bound for Bernoulli laws `Ber(1, 0, a)` and `Ber(1, 0, b)` with
`a < b`: the sum of the two risks is at least `((b - a)/2)²` times the sum of the error
probabilities of the test that rejects `a` when the release exceeds `(a + b)/2`. -/
theorem centralMeanRisk_add_centralMeanRisk_ge {n : ℕ} (M : Kernel (Fin n → ℝ) ℝ)
    {a b : unitInterval} (hab : (a : ℝ) < b) :
    ENNReal.ofReal (((b - a : ℝ) / 2) ^ 2) *
        ((M ∘ₘ Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)) {y | ((a + b : ℝ)) / 2 ≤ y} +
          (M ∘ₘ Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)) {y | ((a + b : ℝ)) / 2 ≤ y}ᶜ) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
  have hA : MeasurableSet {y : ℝ | ((a + b : ℝ)) / 2 ≤ y} := measurableSet_Ici
  rw [mul_add]
  gcongr
  · refine ofReal_mul_comp_le_centralMeanRisk M _ hA fun y hy ↦ ?_
    rw [integral_id_bernoulliMeasure_one_zero]
    simp only [Set.mem_ofPred_eq] at hy
    nlinarith
  · refine ofReal_mul_comp_le_centralMeanRisk M _ hA.compl fun y hy ↦ ?_
    rw [integral_id_bernoulliMeasure_one_zero]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
    nlinarith

/-- The binary Kullback–Leibler divergence is at most the χ² divergence
`(p - q)² / (q (1 - q))`. -/
theorem klBerReal_le_sq_div {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    InformationTheory.klBerReal p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  rw [InformationTheory.klBerReal_apply]
  have h1 : p * Real.log (p / q) ≤ p * (p / q - 1) := by
    rcases eq_or_lt_of_le hp0 with rfl | hp
    · simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hp hq0)) hp0
  have h2 : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ (1 - p) * ((1 - p) / (1 - q) - 1) := by
    rcases eq_or_lt_of_le (sub_nonneg.mpr hp1) with h | hp
    · rw [← h]; simp
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hp (by linarith))) hp.le
  have hq1' : 0 < 1 - q := by linarith
  have h3 : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) =
      (p - q) ^ 2 / (q * (1 - q)) := by
    field_simp
    ring
  linarith

/-- If a sum is at least `r`, one of the two terms is at least `r / 2`. -/
theorem ofReal_half_le_or_of_ofReal_le_add {x y : ℝ≥0∞} {r : ℝ} (h : ENNReal.ofReal r ≤ x + y) :
    ENNReal.ofReal (r / 2) ≤ x ∨ ENNReal.ofReal (r / 2) ≤ y := by
  rcases le_or_gt r 0 with hr | hr
  · left
    rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact zero_le
  by_contra hc
  push Not at hc
  have := ENNReal.add_lt_add hc.1 hc.2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at this
  exact absurd h (not_le.mpr this)

/-- The event bound from the total variation distance: `2 (Q A - Q' A) ≤ tvDist Q Q'`. -/
theorem two_mul_measureReal_sub_le_tvDist {Q Q' : Measure ℝ} [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] {A : Set ℝ} (hA : MeasurableSet A) :
    2 * (Q.real A - Q'.real A) ≤ tvDist Q Q' := by
  have hf : ∀ (ξ : Measure ℝ) [IsProbabilityMeasure ξ],
      ∫ y, (2 * A.indicator (1 : ℝ → ℝ) y - 1) ∂ξ = 2 * ξ.real A - 1 := by
    intro ξ _
    have hI : Integrable (A.indicator (1 : ℝ → ℝ)) ξ := (integrable_const (1 : ℝ)).indicator hA
    rw [integral_sub (hI.const_mul 2) (integrable_const 1), integral_const_mul,
      integral_indicator_one hA]
    simp
  have h := integral_sub_integral_le_tvDist (μ := Q) (ν := Q')
    (f := fun y ↦ 2 * A.indicator (1 : ℝ → ℝ) y - 1)
    ((((measurable_const.indicator hA).const_mul 2).sub_const 1).aestronglyMeasurable)
    (ae_of_all _ fun y ↦ by
      by_cases hy : y ∈ A
      · simp [indicator_of_mem hy]; norm_num
      · simp [indicator_of_notMem hy])
  rw [hf Q, hf Q'] at h
  linarith

/-- The non-private part of the central lower bound: for every mechanism some Bernoulli law
`Ber(1, 0, p)` has mean squared error at least `1 / (192 n)`. The two laws `Ber(1/2)` and
`Ber(1/2 + δ)` with `δ = 1/(2√n)` have product laws at Kullback–Leibler divergence at most `1`
(Statlib's `klDiv_pi_const` and `klDiv_bernoulliMeasure_eq_klBerReal`), so by the
Bretagnolle–Huber inequality (Statlib's `exp_neg_klDiv_le_two_sub_tvDist`) and data processing
(`tvDist_comp_le`) no test separates them well. -/
theorem exists_bernoulli_centralMeanRisk_ge_inv {n : ℕ} (hn : 0 < n)
    (M : Kernel (Fin n → ℝ) ℝ) [IsMarkovKernel M] :
    ∃ p : unitInterval,
      ENNReal.ofReal (1 / (192 * n)) ≤ centralMeanRisk M (Ber((1 : ℝ), 0, p)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set δ : ℝ := 1 / (2 * Real.sqrt n) with hδ_def
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnr
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ2 : δ ^ 2 = 1 / (4 * n) := by
    rw [hδ_def, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  set a : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  set b : unitInterval := ⟨1 / 2 + δ, by positivity, by linarith⟩
  have ha : (a : ℝ) = 1 / 2 := rfl
  have hb : (b : ℝ) = 1 / 2 + δ := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; linarith
  set μa := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- Kullback–Leibler divergence of the product laws
  have hkl : InformationTheory.klBerReal b a ≤ 1 / n := by
    refine (klBerReal_le_sq_div b.2.1 b.2.2 (by rw [ha]; norm_num) (by rw [ha]; norm_num)).trans
      (le_of_eq ?_)
    rw [ha, hb, show ((1 / 2 + δ - 1 / 2 : ℝ)) ^ 2 / (1 / 2 * (1 - 1 / 2)) = 4 * δ ^ 2 by ring,
      hδ2]
    field_simp
  have hKL : InformationTheory.klDiv μb μa =
      n * ENNReal.ofReal (InformationTheory.klBerReal b a) := by
    rw [klDiv_pi_const, Fintype.card_fin,
      InformationTheory.klDiv_bernoulliMeasure_eq_klBerReal (by norm_num : (1 : ℝ) ≠ 0) b]
    · intro h; have := congrArg Subtype.val h; rw [ha] at this; norm_num at this
    · intro h; have := congrArg Subtype.val h; rw [ha] at this; norm_num at this
  have hKLne : InformationTheory.klDiv μb μa ≠ ⊤ := by
    rw [hKL]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top
  have hKLr : (InformationTheory.klDiv μb μa).toReal ≤ 1 := by
    rw [hKL, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (InformationTheory.klBerReal_nonneg b.2.1 b.2.2
        (by rw [ha]; norm_num) (by rw [ha]; norm_num))]
    calc (n : ℝ) * InformationTheory.klBerReal b a ≤ n * (1 / n) :=
          mul_le_mul_of_nonneg_left hkl (by positivity)
      _ = 1 := by field_simp
  have hBH := exp_neg_klDiv_le_two_sub_tvDist μb μa hKLne
  have hexp : Real.exp (-1) ≤ Real.exp (-(InformationTheory.klDiv μb μa).toReal) :=
    Real.exp_le_exp.mpr (by linarith)
  have hTV := tvDist_comp_le μb μa M
  have hev := two_mul_measureReal_sub_le_tvDist (Q := M ∘ₘ μb) (Q' := M ∘ₘ μa) hA
  have he3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hcompl : (M ∘ₘ μb).real Aᶜ = 1 - (M ∘ₘ μb).real A := by
    rw [measureReal_compl hA, probReal_univ]
  have htest : 1 / 6 ≤ (M ∘ₘ μa).real A + (M ∘ₘ μb).real Aᶜ := by
    rw [hcompl]; linarith
  have hLC := centralMeanRisk_add_centralMeanRisk_ge M hab (n := n)
  have hsum : ENNReal.ofReal (1 / (96 * n)) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ hLC
    rw [← ofReal_measureReal (measure_ne_top (M ∘ₘ μa) A),
      ← ofReal_measureReal (measure_ne_top (M ∘ₘ μb) Aᶜ),
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hsq' : ((b - a : ℝ) / 2) ^ 2 = 1 / (16 * n) := by
      rw [ha, hb, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, div_pow, hδ2]; ring
    rw [hsq']
    calc 1 / (96 * (n : ℝ)) = 1 / (16 * n) * (1 / 6) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (by positivity)
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, by convert h using 2; field_simp; ring⟩
  · exact ⟨b, by convert h using 2; field_simp; ring⟩

/-- The exponential moment of the number of nonzero coordinates under the product of
Bernoulli laws: `∫ exp(ε #{i | dᵢ ≠ 0}) = (1 + q (e^ε - 1))ⁿ`, written as a lower integral. -/
theorem lintegral_exp_mul_card_ne_zero {n : ℕ} (q : unitInterval) (ε : ℝ) :
    ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ)))
        ∂(Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, q)) =
      ENNReal.ofReal ((1 + q * (Real.exp ε - 1)) ^ n) := by
  set g : ℝ → ℝ := fun x ↦ Real.exp (ε * if x ≠ 0 then 1 else 0)
  have hg : Measurable g :=
    Real.measurable_exp.comp (measurable_const.mul (Measurable.ite
      (measurableSet_singleton 0).compl measurable_const measurable_const))
  have hprod : ∀ d : Fin n → ℝ,
      Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ)) = ∏ i, g (d i) := by
    intro d
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp only [g]
    split_ifs <;> simp
  simp_rw [hprod]
  have hgb : ∀ x, ‖g x‖ ≤ Real.exp |ε| := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    split_ifs <;> simp [le_abs_self, abs_nonneg]
  have hint : Integrable (fun d : Fin n → ℝ ↦ ∏ i, g (d i))
      (Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, q)) := by
    refine Integrable.of_bound (C := Real.exp |ε| ^ n)
      ((Finset.measurable_prod _ fun i _ ↦ hg.comp (measurable_pi_apply i)).aestronglyMeasurable)
      (ae_of_all _ fun d ↦ ?_)
    rw [norm_prod]
    calc ∏ i, ‖g (d i)‖ ≤ ∏ _i : Fin n, Real.exp |ε| :=
          Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦ hgb _
      _ = _ := by simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun d ↦ Finset.prod_nonneg fun i _ ↦ (Real.exp_pos _).le),
    integral_fintype_prod_eq_pow, integral_bernoulliMeasure_one_zero]
  simp only [g, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, mul_one, not_true_eq_false,
    mul_zero, Real.exp_zero, Fintype.card_fin]
  congr 2
  ring

/-- The exponential moment bound `(1 + q (e^ε - 1))ⁿ ≤ 9` when `q ε ≤ 1/n` and `ε ≤ 1`. -/
theorem one_add_mul_exp_sub_one_pow_le_nine {n : ℕ} (hn : 0 < n) {ε q : ℝ} (hε : ε ∈ Ioc 0 1)
    (hq0 : 0 ≤ q) (hq : q * ε ≤ 1 / n) : (1 + q * (Real.exp ε - 1)) ^ n ≤ 9 := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : Real.exp ε - 1 ≤ 2 * ε := by
    have := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε.1]; exact hε.2)
    rw [abs_of_pos hε.1] at this
    exact (le_abs_self _).trans this
  have hx0 : 0 ≤ q * (Real.exp ε - 1) :=
    mul_nonneg hq0 (by linarith [Real.add_one_le_exp ε, hε.1])
  have hx : n * (q * (Real.exp ε - 1)) ≤ 2 := by
    have : q * (Real.exp ε - 1) ≤ 2 * (q * ε) := by nlinarith
    calc (n : ℝ) * (q * (Real.exp ε - 1)) ≤ n * (2 * (q * ε)) :=
          mul_le_mul_of_nonneg_left this hnr.le
      _ ≤ n * (2 * (1 / n)) := by gcongr
      _ = 2 := by field_simp
  calc (1 + q * (Real.exp ε - 1)) ^ n ≤ Real.exp (q * (Real.exp ε - 1)) ^ n := by
        gcongr
        linarith [Real.add_one_le_exp (q * (Real.exp ε - 1))]
    _ = Real.exp (n * (q * (Real.exp ε - 1))) := (Real.exp_nat_mul _ n).symm
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hx
    _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 9 := by
        have := Real.exp_one_lt_d9
        have h0 := Real.exp_pos 1
        nlinarith

/-- The private part of the central lower bound: for an `ε`-differentially private mechanism
some Bernoulli law `Ber(1, 0, p)` has mean squared error at least `min(1, 1/(nε))² / 72`. The
two laws are `Ber(1, 0, 0) = δ₀` and `Ber(1, 0, q)` with `q = min(1, 1/(nε))`; by group
privacy the release law under the second is at most `(1 + q(e^ε - 1))ⁿ ≤ 9` times the release
law under the first. -/
theorem exists_bernoulli_centralMeanRisk_ge_private {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1) (M : Kernel (Fin n → ℝ) ℝ) [IsMarkovKernel M]
    (hM : IsDifferentiallyPrivate IsHammingNeighbor ε 0 M) :
    ∃ p : unitInterval, ENNReal.ofReal (min 1 (1 / (n * ε)) ^ 2 / 72) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, p)) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set q : ℝ := min 1 (1 / (n * ε)) with hq_def
  have hq0 : 0 < q := lt_min one_pos (by have := hε.1; positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqε : q * ε ≤ 1 / n := by
    calc q * ε ≤ 1 / (n * ε) * ε := mul_le_mul_of_nonneg_right (min_le_right _ _) hε.1.le
      _ = 1 / n := by field_simp [hε.1.ne']
  set a : unitInterval := 0
  set b : unitInterval := ⟨q, hq0.le, hq1⟩
  have ha : (a : ℝ) = 0 := rfl
  have hb : (b : ℝ) = q := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; exact hq0
  set μa := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- the release law under `δ₀`
  have hae : ∀ᵐ d ∂μa, d = 0 := by
    have h : ∀ i, ∀ᵐ d ∂μa, d i = 0 := by
      intro i
      have hmap := (measurePreserving_eval (fun _ : Fin n ↦ Ber((1 : ℝ), 0, a)) i).map_eq
      have h0 : ∀ᵐ x ∂(Ber((1 : ℝ), 0, a)), x = 0 := by
        rw [show a = 0 from rfl, bernoulliMeasure_zero]
        exact (ae_dirac_iff (measurableSet_singleton 0)).mpr rfl
      rw [← hmap] at h0
      exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h0
    exact (ae_all_iff.mpr h).mono fun d hd ↦ funext hd
  have hQa : (M ∘ₘ μa) A = M 0 A := by
    rw [Measure.bind_apply hA M.aemeasurable,
      lintegral_congr_ae (g := fun _ ↦ M 0 A) (hae.mono fun d hd ↦ by rw [hd]), lintegral_const,
      measure_univ,
      mul_one]
  -- group privacy
  have hgroup : ∀ d, M d A ≤
      ENNReal.ofReal (Real.exp (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ))) *
        M 0 A := fun d ↦
    kernel_apply_le_exp_mul_card hM hA _ d 0 fun i hi ↦ by simpa using hi
  have hQb : (M ∘ₘ μb) A ≤ 9 * M 0 A := by
    rw [Measure.bind_apply hA M.aemeasurable]
    calc ∫⁻ d, M d A ∂μb ≤ ∫⁻ d, ENNReal.ofReal (Real.exp
          (ε * ((Finset.univ.filter fun i ↦ d i ≠ 0).card : ℝ))) * M 0 A ∂μb :=
          lintegral_mono hgroup
      _ = ENNReal.ofReal ((1 + q * (Real.exp ε - 1)) ^ n) * M 0 A := by
          rw [lintegral_mul_const' _ _ (measure_ne_top _ _), lintegral_exp_mul_card_ne_zero]
      _ ≤ 9 * M 0 A := by
          gcongr
          rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num]
          exact ENNReal.ofReal_le_ofReal
            (one_add_mul_exp_sub_one_pow_le_nine hn hε hq0.le hqε)
  have htest : ENNReal.ofReal (1 / 9) ≤ (M ∘ₘ μa) A + (M ∘ₘ μb) Aᶜ := by
    have h1 : (M ∘ₘ μb) A + (M ∘ₘ μb) Aᶜ = 1 := by
      rw [measure_add_measure_compl hA, measure_univ]
    have h2 : 1 ≤ 9 * ((M ∘ₘ μa) A + (M ∘ₘ μb) Aᶜ) := by
      rw [← h1, hQa, mul_add]
      gcongr
      calc (M ∘ₘ μb) Aᶜ = 1 * (M ∘ₘ μb) Aᶜ := (one_mul _).symm
        _ ≤ 9 * (M ∘ₘ μb) Aᶜ := by gcongr; norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
      show ENNReal.ofReal 9 = 9 by norm_num]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm]
    exact h2
  have hLC := centralMeanRisk_add_centralMeanRisk_ge M hab (n := n)
  have hsum : ENNReal.ofReal (q ^ 2 / 36) ≤
      centralMeanRisk M (Ber((1 : ℝ), 0, a)) + centralMeanRisk M (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ hLC
    calc ENNReal.ofReal (q ^ 2 / 36) = ENNReal.ofReal (((b - a : ℝ) / 2) ^ 2) *
          ENNReal.ofReal (1 / 9) := by
          rw [← ENNReal.ofReal_mul (by positivity), ha, hb]; congr 1; ring
      _ ≤ _ := by gcongr
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, by convert h using 2; ring⟩
  · exact ⟨b, by convert h using 2; ring⟩

/-- GAPS 107.66, central minimax lower bound: there is an absolute `c > 0` such that for
`0 < ε ≤ 1` every `ε`-differentially private mechanism has mean squared error at least
`c min(1, 1/n + 1/(nε)²)` for the mean of some law on `[-1,1]`. -/
theorem exists_centralMeanRisk_ge :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ M : Kernel (Fin n → ℝ) ℝ,
      IsMarkovKernel M → IsDifferentiallyPrivate IsHammingNeighbor ε 0 M →
      ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
        ENNReal.ofReal (c * min 1 (1 / n + 1 / (n * ε) ^ 2)) ≤ centralMeanRisk M P := by
  refine ⟨1 / 400, by norm_num, ?_⟩
  intro n hn ε hε M hMk hM
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set q : ℝ := min 1 (1 / (n * ε)) with hq_def
  have hz : 0 ≤ 1 / (n * ε) := by have := hε.1; positivity
  have hq0 : 0 ≤ q := le_min zero_le_one hz
  have hqsq : min 1 (1 / (n * ε) ^ 2) = q ^ 2 := by
    rw [hq_def, ← one_div_pow]
    rcases le_total (1 / (n * ε)) 1 with h | h
    · rw [min_eq_right h, min_eq_right (pow_le_one₀ hz h)]
    · rw [min_eq_left h, min_eq_left (one_le_pow₀ h), one_pow]
  have hmin : min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / n + q ^ 2 := by
    rw [← hqsq]
    have h1 : 0 ≤ 1 / (n : ℝ) := by positivity
    have h2 : 0 ≤ 1 / (n * ε) ^ 2 := by positivity
    rcases le_total (1 / (n * ε) ^ 2) 1 with h | h
    · rw [min_eq_right h]; exact min_le_right _ _
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
  by_cases h : q ^ 2 ≤ 1 / n
  · obtain ⟨p, hp⟩ := exists_bernoulli_centralMeanRisk_ge_inv hn M
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p,
      le_trans (ENNReal.ofReal_le_ofReal ?_) hp⟩
    calc 1 / 400 * min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / 400 * (1 / (n : ℝ) + 1 / n) := by
          gcongr; linarith
      _ ≤ 1 / (192 * n) := by
          rw [show 1 / 400 * (1 / (n : ℝ) + 1 / n) = 1 / (200 * n) by field_simp; ring]
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · push Not at h
    obtain ⟨p, hp⟩ := exists_bernoulli_centralMeanRisk_ge_private hn hε M hM
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p,
      le_trans (ENNReal.ofReal_le_ofReal ?_) hp⟩
    rw [← hq_def]
    calc 1 / 400 * min 1 (1 / n + 1 / (n * ε) ^ 2) ≤ 1 / 400 * (q ^ 2 + q ^ 2) := by
          gcongr; linarith
      _ ≤ q ^ 2 / 72 := by nlinarith [sq_nonneg q]

/-! ### Two-point lower bounds for the local mean risk -/

/-- The total variation distance between `Ber(1, 0, a)` and `Ber(1, 0, b)` is at most
`|a - b|`. -/
theorem totalVariationDistance_bernoulliMeasure_le (a b : unitInterval) :
    totalVariationDistance (Ber((1 : ℝ), 0, a)) (Ber((1 : ℝ), 0, b)) ≤ |(a : ℝ) - b| := by
  unfold totalVariationDistance
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  rw [bernoulliMeasure_real_apply a hA, bernoulliMeasure_real_apply b hA]
  split_ifs
  · simp
  · simp
  · simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    rw [abs_sub_comm]
    ring_nf
    exact le_refl _
  · simp

/-- A lower bound for the local mean risk on a set of estimates far from the mean. -/
theorem ofReal_mul_map_le_localMeanRisk {n : ℕ} (Q : Fin n → Kernel ℝ ℝ)
    {est : (Fin n → ℝ) → ℝ} (hest : Measurable est) (P : Measure ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) {r : ℝ} (hr : ∀ y ∈ B, r ≤ (y - ∫ x, x ∂P) ^ 2) :
    ENNReal.ofReal r * ((Measure.pi fun i ↦ Q i ∘ₘ P).map est) B ≤ localMeanRisk Q est P := by
  rw [Measure.map_apply hest hB, ← lintegral_indicator_const (hest hB)]
  unfold localMeanRisk
  refine lintegral_mono fun z ↦ ?_
  by_cases hz : z ∈ est ⁻¹' B
  · rw [indicator_of_mem hz]
    exact ENNReal.ofReal_le_ofReal (hr _ hz)
  · rw [indicator_of_notMem hz]
    exact zero_le

/-- The lower half of the local minimax rate: for `ε`-locally private release kernels and a
measurable estimator, some Bernoulli law `Ber(1, 0, p)` has mean squared error at least
`min(1, 1/(nε²)) / 768`. The two laws are `Ber(1/2)` and `Ber(1/2 + δ)` with
`δ = min(1/2, 1/(4ε√n))`; the release laws of one individual are at Kullback–Leibler
divergence at most `16 ε² δ²` by the contraction under local privacy (GAPS 107.75,
`klDiv_comp_le_of_local_differential_privacy`), and Le Cam's method concludes as in the
central case. -/
theorem exists_bernoulli_localMeanRisk_ge {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (Q : Fin n → Kernel ℝ ℝ) (hQ : ∀ i, IsMarkovKernel (Q i))
    (hpriv : ∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i))
    (est : (Fin n → ℝ) → ℝ) (hest : Measurable est) :
    ∃ p : unitInterval, ENNReal.ofReal (min 1 (1 / (n * ε ^ 2)) / 768) ≤
      localMeanRisk Q est (Ber((1 : ℝ), 0, p)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hε0 := hε.1
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnr
  set δ : ℝ := min (1 / 2) (1 / (4 * ε * Real.sqrt n)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : 16 * n * ε ^ 2 * δ ^ 2 ≤ 1 := by
    have h1 : δ ≤ 1 / (4 * ε * Real.sqrt n) := min_le_right _ _
    have h2 : δ ^ 2 ≤ (1 / (4 * ε * Real.sqrt n)) ^ 2 := pow_le_pow_left₀ hδ0.le h1 2
    have h3 : (1 / (4 * ε * Real.sqrt n)) ^ 2 = 1 / (16 * n * ε ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le]; ring
    rw [h3] at h2
    calc 16 * n * ε ^ 2 * δ ^ 2 ≤ 16 * n * ε ^ 2 * (1 / (16 * n * ε ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by field_simp
  have hδm : min 1 (1 / (n * ε ^ 2)) / 16 ≤ δ ^ 2 := by
    rcases min_choice (1 / 2 : ℝ) (1 / (4 * ε * Real.sqrt n)) with h | h
    · rw [← hδ_def] at h; rw [h]
      have := min_le_left (1 : ℝ) (1 / (n * ε ^ 2)); linarith
    · rw [← hδ_def] at h; rw [h, div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le]
      have := min_le_right (1 : ℝ) (1 / (n * ε ^ 2))
      calc min 1 (1 / (n * ε ^ 2)) / 16 ≤ 1 / (n * ε ^ 2) / 16 := by linarith
        _ = 1 ^ 2 / (4 ^ 2 * ε ^ 2 * n) := by field_simp; ring
  set a : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  set b : unitInterval := ⟨1 / 2 + δ, by positivity, by linarith⟩
  have ha : (a : ℝ) = 1 / 2 := rfl
  have hb : (b : ℝ) = 1 / 2 + δ := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; linarith
  have : ∀ i, IsMarkovKernel (Q i) := hQ
  set μa := Measure.pi fun i ↦ Q i ∘ₘ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun i ↦ Q i ∘ₘ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- divergence of one release
  have hKLi : ∀ i, InformationTheory.klDiv (Q i ∘ₘ Ber((1 : ℝ), 0, b))
      (Q i ∘ₘ Ber((1 : ℝ), 0, a)) ≤ ENNReal.ofReal (16 * ε ^ 2 * δ ^ 2) := by
    intro i
    have h := klDiv_comp_le_of_local_differential_privacy (Q i) ε hε0.le (hpriv i)
      (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a))
    refine le_trans le_self_add (h.trans (ENNReal.ofReal_le_ofReal ?_))
    have hTV := totalVariationDistance_bernoulliMeasure_le b a
    have hTV0 : 0 ≤ totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) :=
      Real.sSup_nonneg (by rintro _ ⟨A, -, rfl⟩; exact abs_nonneg _)
    rw [hb, ha, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, abs_of_pos hδ0] at hTV
    have he : Real.exp ε - 1 ≤ 2 * ε := by
      have := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε0]; exact hε.2)
      rw [abs_of_pos hε0] at this
      exact (le_abs_self _).trans this
    have he0 : 0 ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
    have h1 : (Real.exp ε - 1) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ he0 he 2
    have h2 : totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) ^ 2 ≤ δ ^ 2 :=
      pow_le_pow_left₀ hTV0 hTV 2
    calc 4 * (Real.exp ε - 1) ^ 2 *
          totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) ^ 2
        ≤ 4 * (2 * ε) ^ 2 * δ ^ 2 := by gcongr
      _ = 16 * ε ^ 2 * δ ^ 2 := by ring
  have hKL : InformationTheory.klDiv μb μa ≤ ENNReal.ofReal 1 := by
    rw [klDiv_pi]
    calc ∑ i, InformationTheory.klDiv (Q i ∘ₘ Ber((1 : ℝ), 0, b)) (Q i ∘ₘ Ber((1 : ℝ), 0, a))
        ≤ ∑ _i : Fin n, ENNReal.ofReal (16 * ε ^ 2 * δ ^ 2) := Finset.sum_le_sum fun i _ ↦ hKLi i
      _ = ENNReal.ofReal (n * (16 * ε ^ 2 * δ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hKLne : InformationTheory.klDiv μb μa ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hKLr : (InformationTheory.klDiv μb μa).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    rwa [ENNReal.toReal_ofReal zero_le_one] at this
  have hBH := exp_neg_klDiv_le_two_sub_tvDist μb μa hKLne
  have hexp : Real.exp (-1) ≤ Real.exp (-(InformationTheory.klDiv μb μa).toReal) :=
    Real.exp_le_exp.mpr (by linarith)
  have hTV := tvDist_map_le μb μa hest
  have hev := two_mul_measureReal_sub_le_tvDist (Q := μb.map est) (Q' := μa.map est) hA
  have he3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hcompl : (μb.map est).real Aᶜ = 1 - (μb.map est).real A := by
    rw [measureReal_compl hA, probReal_univ]
  have htest : 1 / 6 ≤ (μa.map est).real A + (μb.map est).real Aᶜ := by
    rw [hcompl]; linarith
  have hLa := ofReal_mul_map_le_localMeanRisk Q hest (Ber((1 : ℝ), 0, a)) hA
    (r := ((b - a : ℝ) / 2) ^ 2) fun y hy ↦ by
      rw [integral_id_bernoulliMeasure_one_zero]
      simp only [A, Set.mem_ofPred_eq] at hy
      nlinarith
  have hLb := ofReal_mul_map_le_localMeanRisk Q hest (Ber((1 : ℝ), 0, b)) hA.compl
    (r := ((b - a : ℝ) / 2) ^ 2) fun y hy ↦ by
      rw [integral_id_bernoulliMeasure_one_zero]
      simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
      nlinarith
  have hsum : ENNReal.ofReal (δ ^ 2 / 24) ≤
      localMeanRisk Q est (Ber((1 : ℝ), 0, a)) + localMeanRisk Q est (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ (add_le_add hLa hLb)
    rw [← mul_add, ← ofReal_measureReal (measure_ne_top (μa.map est) A),
      ← ofReal_measureReal (measure_ne_top (μb.map est) Aᶜ),
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [ha, hb, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring]
    calc δ ^ 2 / 24 = (δ / 2) ^ 2 * (1 / 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (by positivity)
  have hfin : ∀ x : ℝ≥0∞, ENNReal.ofReal (δ ^ 2 / 24 / 2) ≤ x →
      ENNReal.ofReal (min 1 (1 / (n * ε ^ 2)) / 768) ≤ x := fun x hx ↦
    le_trans (ENNReal.ofReal_le_ofReal (by nlinarith)) hx
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, hfin _ h⟩
  · exact ⟨b, hfin _ h⟩

/-- The local Laplace release kernel: clip to `[-1,1]` and add Laplace noise of scale `2/ε`. -/
def localLaplaceKernel (ε : ℝ) : Kernel ℝ ℝ where
  toFun x := TauCeti.Probability.laplaceMeasure (clipUnit x) (2 / ε : ℝ)
  measurable' := by
    have hc : Measurable fun x : ℝ ↦ clipUnit x := by unfold clipUnit; fun_prop
    exact TauCeti.Probability.measurable_laplaceMeasure.comp
      (f := fun x : ℝ ↦ (clipUnit x, (2 / ε : ℝ))) (hc.prodMk measurable_const)

/-- The local Laplace release kernel is a Markov kernel for positive `ε`. -/
theorem isMarkovKernel_localLaplaceKernel {ε : ℝ} (hε : 0 < ε) :
    IsMarkovKernel (localLaplaceKernel ε) :=
  ⟨fun _ ↦ TauCeti.Probability.isProbabilityMeasure_laplaceMeasure (by positivity) _⟩

/-- GAPS 107.66: the local Laplace release kernel is `ε`-locally differentially private. -/
theorem isDifferentiallyPrivate_localLaplaceKernel {ε : ℝ} (hε : 0 < ε) :
    IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (localLaplaceKernel ε) := by
  intro x x' _ A _
  set b : ℝ := 2 / ε with hb_def
  have hb : 0 < b := by positivity
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hratio : |clipUnit x - clipUnit x'| / b ≤ ε := by
    rw [div_le_iff₀ hb, hb_def]
    have h1 := hclip x; have h2 := hclip x'
    calc |clipUnit x - clipUnit x'| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      _ = ε * (2 / ε) := by field_simp
  have hk : ∀ e : ℝ, localLaplaceKernel ε e =
      volume.withDensity (TauCeti.Probability.laplacePDF (clipUnit e) b) := fun e ↦
    TauCeti.Probability.laplaceMeasure_eq_withDensity _ _
  rw [ENNReal.ofReal_zero, add_zero, hk, hk, withDensity_apply' _ A, withDensity_apply' _ A,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y ↦ ?_
  calc TauCeti.Probability.laplacePDF (clipUnit x) b y
      ≤ ENNReal.ofReal (Real.exp (|clipUnit x - clipUnit x'| / b)) *
          TauCeti.Probability.laplacePDF (clipUnit x') b y := laplacePDF_le_exp_mul hb _ _ y
    _ ≤ ENNReal.ofReal (Real.exp ε) * TauCeti.Probability.laplacePDF (clipUnit x') b y := by
      gcongr

/-- Under a law supported by `[-1,1]`, the squared deviation of a local Laplace release from
the mean has lower integral at most `4 + 8/ε²`. -/
theorem lintegral_sq_sub_localLaplace_le {ε : ℝ} (hε : 0 < ε) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    ∫⁻ y, ENNReal.ofReal ((y - ∫ x, x ∂P) ^ 2) ∂(localLaplaceKernel ε ∘ₘ P) ≤
      ENNReal.ofReal (4 + 8 / ε ^ 2) := by
  set θ := ∫ x, x ∂P
  set b : ℝ := 2 / ε with hb_def
  have hb : 0 < b := by positivity
  have hθ := abs_integral_le_one_of_support P hP
  rw [abs_le] at hθ
  have hclip : ∀ x, clipUnit x ∈ Icc (-1 : ℝ) 1 := fun x ↦
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) (by fun_prop)]
  have hinner : ∀ x, ∫⁻ y, ENNReal.ofReal ((y - θ) ^ 2) ∂localLaplaceKernel ε x =
      ENNReal.ofReal ((clipUnit x - θ) ^ 2 + 2 * b ^ 2) := fun x ↦ by
    have hI : Integrable (fun y ↦ (y - θ) ^ 2) (localLaplaceKernel ε x) :=
      integrable_sq_sub_laplaceMeasure hb _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact congrArg _ (integral_sq_sub_laplaceMeasure hb _ _)
  simp_rw [hinner]
  calc ∫⁻ x, ENNReal.ofReal ((clipUnit x - θ) ^ 2 + 2 * b ^ 2) ∂P
      ≤ ∫⁻ _x, ENNReal.ofReal (4 + 8 / ε ^ 2) ∂P := by
        refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
        have h := hclip x
        have h2 : 2 * b ^ 2 = 8 / ε ^ 2 := by rw [hb_def]; field_simp; ring
        nlinarith [h.1, h.2]
    _ = ENNReal.ofReal (4 + 8 / ε ^ 2) := by simp

/-- Under a law supported by `[-1,1]`, a local Laplace release has mean equal to the mean of
the law. -/
theorem integral_id_localLaplace {ε : ℝ} (hε : 0 < ε) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0)
    (hint : Integrable (fun y : ℝ ↦ y) (localLaplaceKernel ε ∘ₘ P)) :
    ∫ y, y ∂(localLaplaceKernel ε ∘ₘ P) = ∫ x, x ∂P := by
  have hb : 0 < 2 / ε := by positivity
  have hae : ∀ᵐ x ∂P, clipUnit x = x := by
    have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
      fun x hx ↦ by simpa using hx
    filter_upwards [hmem] with x hx
    simp only [clipUnit, min_eq_right hx.2, max_eq_right hx.1]
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint]
  simp only [Kernel.const_apply]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  change ∫ y, y ∂TauCeti.Probability.laplaceMeasure (clipUnit x) (2 / ε) = x
  rw [TauCeti.Probability.integral_id_laplaceMeasure, hx]
  exact hb

/-- GAPS 107.66: on laws supported by `[-1,1]`, the sample mean of local Laplace releases has
mean squared error at most `(4 + 8/ε²)/n`. -/
theorem localMeanRisk_localLaplace_mean_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    localMeanRisk (fun _ : Fin n ↦ localLaplaceKernel ε) (fun z ↦ (∑ i, z i) / n) P ≤
      ENNReal.ofReal ((4 + 8 / ε ^ 2) / n) := by
  have := isMarkovKernel_localLaplaceKernel hε
  set L : Measure ℝ := localLaplaceKernel ε ∘ₘ P with hL
  set θ := ∫ x, x ∂P
  set π : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ L
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlin := lintegral_sq_sub_localLaplace_le hε P hP
  have hsqI : Integrable (fun y : ℝ ↦ (y - θ) ^ 2) L := by
    refine ⟨(by fun_prop : Measurable fun y : ℝ ↦ (y - θ) ^ 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hL2 : MemLp (fun y : ℝ ↦ y - θ) 2 L :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hsqI
  have hid2 : MemLp (fun y : ℝ ↦ y) 2 L := by
    convert hL2.add (memLp_const θ) using 1
    funext y; simp
  have hmeanL : ∫ y, y ∂L = θ := integral_id_localLaplace hε P hP (hid2.integrable one_le_two)
  have hsqle : ∫ y, (y - θ) ^ 2 ∂L ≤ 4 + 8 / ε ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _) (by fun_prop)]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have hvarL : Var[fun y : ℝ ↦ y; L] ≤ 4 + 8 / ε ^ 2 := by
    rw [variance_eq_integral (by fun_prop), hmeanL]; exact hsqle
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i z ↦ z i
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_pi_apply i
  have hmap : ∀ i, π.map (Y i) = L := fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ L) i).map_eq
  have hYL : ∀ i, MemLp (Y i) 2 π := fun i ↦ by
    exact hid2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ L) i)
  have hYint : ∀ i, ∫ z, Y i z ∂π = θ := by
    intro i
    rw [← hmeanL, ← hmap i, integral_map (hYm i).aemeasurable (by fun_prop)]
  have hvY : ∀ i, Var[Y i; π] ≤ 4 + 8 / ε ^ 2 := by
    intro i
    have h := variance_map (μ := π) (X := fun y : ℝ ↦ y) (Y := Y i)
      (by rw [hmap i]; fun_prop) (hYm i).aemeasurable
    rw [hmap i] at h
    rw [show Y i = (fun y : ℝ ↦ y) ∘ Y i from rfl, ← h]; exact hvarL
  have hmean_eq : (fun z : Fin n → ℝ ↦ (∑ i, z i) / n) = fun z ↦ (n : ℝ)⁻¹ * (∑ i, Y i) z := by
    funext z
    simp only [Finset.sum_apply, Y]
    rw [div_eq_inv_mul]
  have hsumL : MemLp (∑ i, Y i) 2 π := memLp_finsetSum' _ fun i _ ↦ hYL i
  have hmL : MemLp (fun z : Fin n → ℝ ↦ (∑ i, z i) / n) 2 π := by
    rw [hmean_eq]; exact hsumL.const_mul _
  have hEmean : ∫ z, (∑ i, z i) / n ∂π = θ := by
    rw [hmean_eq, integral_const_mul]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hYL i).integrable one_le_two]
    simp only [hYint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j ↦ Y i ⟂ᵢ[π] Y j := by
    intro i _ j _ hij
    exact (iIndepFun_pi (X := fun _ : Fin n ↦ fun y : ℝ ↦ y)
      (fun _ ↦ aemeasurable_id)).indepFun hij
  have hvsum : Var[∑ i, Y i; π] = ∑ i, Var[Y i; π] :=
    IndepFun.variance_sum (fun i _ ↦ hYL i) hindep
  have hsqint : Integrable (fun z : Fin n → ℝ ↦ ((∑ i, z i) / n - θ) ^ 2) π :=
    (hmL.sub (memLp_const θ)).integrable_sq
  unfold localMeanRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hsqint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hvar_eq : ∫ z, ((∑ i, z i) / n - θ) ^ 2 ∂π =
      Var[fun z : Fin n → ℝ ↦ (∑ i, z i) / n; π] := by
    rw [variance_eq_integral hmL.aemeasurable, hEmean]
  rw [hvar_eq, hmean_eq, variance_const_mul, hvsum]
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[Y i; π] ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, (4 + 8 / ε ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvY i) (by positivity)
    _ = (4 + 8 / ε ^ 2) / n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- GAPS 107.66, local minimax rate: there are absolute `c, C > 0` such that for `0 < ε ≤ 1`
every noninteractive protocol with `ε`-locally private release kernels and every measurable
estimator has mean squared error at least `c min(1, 1/(nε²))` for some law on `[-1,1]`, and some
such protocol has error at most `C min(1, 1/(nε²))` for every law on `[-1,1]`. -/
theorem localMeanRisk_minimax_order :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1,
      (∀ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) →
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) →
        ∀ est : (Fin n → ℝ) → ℝ, Measurable est →
        ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
          ENNReal.ofReal (c * min 1 (1 / (n * ε ^ 2))) ≤ localMeanRisk Q est P) ∧
      ∃ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) ∧
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) ∧
        ∃ est : (Fin n → ℝ) → ℝ, Measurable est ∧
          ∀ P : Measure ℝ, IsProbabilityMeasure P → P (Icc (-1) 1)ᶜ = 0 →
            localMeanRisk Q est P ≤ ENNReal.ofReal (C * min 1 (1 / (n * ε ^ 2))) := by
  refine ⟨1 / 768, by norm_num, 12, by norm_num, fun n hn ε hε ↦ ⟨?_, ?_⟩⟩
  · intro Q hQ hpriv est hest
    obtain ⟨p, hp⟩ := exists_bernoulli_localMeanRisk_ge hn hε Q hQ hpriv est hest
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p, ?_⟩
    rw [one_div_mul_eq_div]; exact hp
  have hε0 := hε.1
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have := isMarkovKernel_localLaplaceKernel hε0
  refine ⟨fun _ ↦ localLaplaceKernel ε, fun _ ↦ this,
    fun _ ↦ isDifferentiallyPrivate_localLaplaceKernel hε0,
    fun z ↦ if (n : ℝ) * ε ^ 2 < 1 then 0 else (∑ i, z i) / n, ?_, ?_⟩
  · split_ifs <;> fun_prop
  intro P hP hsupp
  by_cases hsmall : (n : ℝ) * ε ^ 2 < 1
  · simp only [hsmall, ↓reduceIte]
    have hθ := abs_integral_le_one_of_support P hsupp
    have hmin : min 1 (1 / (n * ε ^ 2)) = 1 :=
      min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith)
    unfold localMeanRisk
    rw [lintegral_const, measure_univ, mul_one, hmin]
    apply ENNReal.ofReal_le_ofReal
    have : (0 - ∫ x, x ∂P) ^ 2 ≤ 1 := by
      rw [zero_sub, neg_sq, ← sq_abs]; nlinarith [abs_nonneg (∫ x, x ∂P)]
    linarith
  · simp only [hsmall, ↓reduceIte]
    push Not at hsmall
    have hmin : min 1 (1 / (n * ε ^ 2)) = 1 / (n * ε ^ 2) :=
      min_eq_right (by rw [div_le_iff₀ (by positivity)]; linarith)
    refine (localMeanRisk_localLaplace_mean_le hn hε0 P hsupp).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hmin]
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith [hε.2]
    have h4 : 4 ≤ 4 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    calc (4 + 8 / ε ^ 2) / n ≤ (4 / ε ^ 2 + 8 / ε ^ 2) / n := by gcongr
      _ = 12 * (1 / (n * ε ^ 2)) := by field_simp; ring


end CKSD
