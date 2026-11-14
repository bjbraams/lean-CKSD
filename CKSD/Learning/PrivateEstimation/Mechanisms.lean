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
# Central and local mechanisms for a bounded mean

Neighbouring data sets differ in at most one coordinate. Clipping and Laplace perturbation
yield central and noninteractive local mechanisms for laws supported on `[-1,1]`.
Laplace laws and moments use TauCeti.

## Main definitions

* `CKSD.IsHammingNeighbor`: data sets at Hamming distance at most one.
* `CKSD.clipUnit`, `CKSD.clippedMean`: clipping to `[-1,1]` and the clipped sample mean.
* `CKSD.laplaceMeanMechanism`: the clipped Laplace mean mechanism.
* `CKSD.centralMeanRisk`, `CKSD.localMeanRisk`: mean squared errors as lower integrals.

## Main results

* `CKSD.is_differentially_private_of_eq_laplace_measure`: privacy of Laplace mechanisms.
* `CKSD.is_differentially_private_laplace_mean_mechanism`: privacy of the clipped Laplace mean
  (GAPS 107.66).
* `CKSD.central_mean_risk_laplace_mean_mechanism_le`: its risk bound `1/n + 8/(nε)²` (GAPS 107.66).
* `CKSD.exists_central_mean_risk_le`: the central minimax upper bound (GAPS 107.66).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Data sets in `ℝⁿ` are neighbouring when they differ in at most one coordinate, that is,
when their Hamming distance is at most `1`. -/
def IsHammingNeighbor {n : ℕ} (d d' : Fin n → ℝ) : Prop :=
  hammingDist d d' ≤ 1

/-- Clipping to `[-1,1]`: the projection `Set.projIcc` onto the interval, as a real number. -/
def clipUnit (x : ℝ) : ℝ := Set.projIcc (-1 : ℝ) 1 (by norm_num) x

/-- Clipped values lie in `[-1,1]`. -/
theorem clip_unit_mem_icc (x : ℝ) : clipUnit x ∈ Icc (-1 : ℝ) 1 :=
  (Set.projIcc (-1 : ℝ) 1 (by norm_num) x).2

/-- Clipping is the identity on `[-1,1]`. -/
theorem clip_unit_of_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : clipUnit x = x :=
  congrArg Subtype.val (Set.projIcc_of_mem _ hx)

/-- Clipping is continuous. -/
theorem continuous_clip_unit : Continuous clipUnit :=
  continuous_subtype_val.comp continuous_projIcc

/-- Clipping is measurable. -/
theorem measurable_clip_unit : Measurable clipUnit :=
  continuous_clip_unit.measurable

/-- Mean of a data set clipped to `[-1,1]`. -/
def clippedMean {n : ℕ} (d : Fin n → ℝ) : ℝ := (∑ i, clipUnit (d i)) / n

/-- The clipped Laplace mean mechanism with noise scale `2 / (n ε)`. -/
def laplaceMeanMechanism (n : ℕ) (ε : ℝ) : Kernel (Fin n → ℝ) ℝ where
  toFun d := TauCeti.Probability.laplaceMeasure (clippedMean d) (2 / (n * ε))
  measurable' := by
    have hc : Measurable fun d : Fin n → ℝ ↦ clippedMean d :=
      (Finset.measurable_sum _ fun i _ ↦
        measurable_clip_unit.comp (measurable_pi_apply i)).div_const _
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
theorem abs_clipped_mean_sub_le {n : ℕ} {d d' : Fin n → ℝ} (h : IsHammingNeighbor d d') :
    |clippedMean d - clippedMean d'| ≤ 2 / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [clippedMean]
  have hclip := clip_unit_mem_icc
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
        have : (S.card : ℝ) ≤ 1 := by exact_mod_cast (show S.card ≤ 1 from h)
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

/-- A Laplace mechanism `d ↦ Laplace(f d, b)` is `ε`-differentially private for a relation `R`
along which `f` moves by at most `ε b`. -/
theorem is_differentially_private_of_eq_laplace_measure {D : Type*} [MeasurableSpace D]
    (R : D → D → Prop) (M : Kernel D ℝ) (f : D → ℝ) {b ε : ℝ} (hb : 0 < b)
    (hM : ∀ d, M d = TauCeti.Probability.laplaceMeasure (f d) b)
    (hf : ∀ d d', R d d' → |f d - f d'| ≤ ε * b) : IsDifferentiallyPrivate R ε 0 M := by
  intro d d' hdd' A _
  have hk : ∀ e, M e = volume.withDensity (TauCeti.Probability.laplacePDF (f e) b) := fun e ↦
    (hM e).trans (TauCeti.Probability.laplaceMeasure_eq_withDensity _ _)
  rw [ENNReal.ofReal_zero, add_zero, hk, hk, withDensity_apply' _ A, withDensity_apply' _ A,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x ↦ (laplacePDF_le_exp_mul hb (f d) (f d') x).trans ?_
  gcongr
  rw [div_le_iff₀ hb]
  exact hf d d' hdd'

/-- GAPS 107.66: the clipped Laplace mean mechanism is `ε`-differentially private. -/
theorem is_differentially_private_laplace_mean_mechanism (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε : 0 < ε) :
    IsDifferentiallyPrivate IsHammingNeighbor ε 0 (laplaceMeanMechanism n ε) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine is_differentially_private_of_eq_laplace_measure _ _ clippedMean (by positivity)
    (fun _ ↦ rfl) fun d d' hdd' ↦ (abs_clipped_mean_sub_le hdd').trans_eq ?_
  field_simp

/-- Mean squared deviation of a Laplace law from a point: squared bias plus variance `2b²`. -/
theorem integral_sq_sub_laplace_measure {b : ℝ} (hb : 0 < b) (m θ : ℝ) :
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
theorem integrable_sq_sub_laplace_measure {b : ℝ} (hb : 0 < b) (m θ : ℝ) :
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
theorem integral_clipped_mean_sub_sq_le (n : ℕ) (hn : 0 < n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂Measure.pi (fun _ : Fin n ↦ P) ≤ 1 / n := by
  set π : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hclipm := measurable_clip_unit
  have hclip := clip_unit_mem_icc
  have hae : ∀ᵐ x ∂P, clipUnit x = x := by
    have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
      fun x hx ↦ by simpa using hx
    filter_upwards [hmem] with x hx
    exact clip_unit_of_mem hx
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
  have hvar_eq : ∫ d, (clippedMean d - ∫ x, x ∂P) ^ 2 ∂π =
      ProbabilityTheory.variance (fun d ↦ clippedMean d) π := by
    rw [variance_eq_integral (by rw [hmean_eq]; exact (hsumL.aemeasurable.const_mul _)), hEmean]
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j ↦ Y i ⟂ᵢ[π] Y j := by
    intro i _ j _ hij
    exact (iIndepFun_pi (X := fun _ : Fin n ↦ clipUnit)
      (fun _ ↦ hclipm.aemeasurable)).indepFun hij
  have hvsum : ProbabilityTheory.variance (∑ i, Y i) π =
      ∑ i, ProbabilityTheory.variance (Y i) π :=
    IndepFun.variance_sum (fun i _ ↦ hYL i) hindep
  have hvY : ∀ i, ProbabilityTheory.variance (Y i) π ≤ 1 := by
    intro i
    have := variance_le_sq_of_bounded (μ := π) (a := -1) (b := 1)
      (Eventually.of_forall fun d ↦ hclip (d i)) (hYm i).aemeasurable
    norm_num at this
    exact this
  rw [hvar_eq, hmean_eq, variance_const_mul, hvsum]
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, ProbabilityTheory.variance (Y i) π ≤
        ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvY i) (by positivity)
    _ = 1 / n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp

/-- GAPS 107.66: on laws supported by `[-1,1]`, the clipped Laplace mean mechanism has mean
squared error at most `1/n + 8/(n ε)²`. -/
theorem central_mean_risk_laplace_mean_mechanism_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    centralMeanRisk (laplaceMeanMechanism n ε) P ≤ ENNReal.ofReal (1 / n + 8 / (n * ε) ^ 2) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set b : ℝ := 2 / (n * ε) with hb_def
  have hb : 0 < b := by positivity
  have hinner : ∀ d : Fin n → ℝ, ∫ y, (y - ∫ x, x ∂P) ^ 2 ∂laplaceMeanMechanism n ε d =
      (clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2 := fun d ↦
    integral_sq_sub_laplace_measure hb _ _
  have hcm : Measurable fun d : Fin n → ℝ ↦ clippedMean d :=
    (Finset.measurable_sum _ fun i _ ↦ measurable_clip_unit.comp (measurable_pi_apply i)).div_const _
  have hbdd : ∀ d : Fin n → ℝ, ‖(clippedMean d - ∫ x, x ∂P) ^ 2‖ ≤ (1 + |∫ x, x ∂P|) ^ 2 := by
    intro d
    have hc : |clippedMean d| ≤ 1 := by
      unfold clippedMean
      rw [abs_div, abs_of_pos hnr, div_le_one hnr]
      calc |∑ i, clipUnit (d i)| ≤ ∑ i, |clipUnit (d i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ abs_le.mpr (clip_unit_mem_icc _)
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
      integrable_sq_sub_laplace_measure hb _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ ↦ sq_nonneg _), hinner d]
  unfold centralMeanRisk
  simp_rw [hinner']
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun d ↦ (clippedMean d - ∫ x, x ∂P) ^ 2 + 2 * b ^ 2)
    (hint.add (integrable_const _)) (ae_of_all _ fun _ ↦ by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_add hint (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  have h1 := integral_clipped_mean_sub_sq_le n hn P hP
  have h2 : 2 * b ^ 2 = 8 / (n * ε) ^ 2 := by rw [hb_def]; field_simp; ring
  linarith

/-- The clipped Laplace mean mechanism is a Markov kernel for positive `n` and `ε`. -/
theorem is_markov_kernel_laplace_mean_mechanism (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
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

/-- GAPS 107.66, central minimax upper bound: for every `ε > 0` (in particular `0 < ε ≤ 1`)
some `ε`-differentially private mechanism (the clipped Laplace mean, or the constant release
`0` when `1` is the smaller rate) has mean squared error at most `8 min(1, 1/n + 1/(nε)²)` for
every law on `[-1,1]`. -/
theorem exists_central_mean_risk_le (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
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
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε.le)
    · rw [min_eq_left hsmall]
      unfold centralMeanRisk
      simp only [Kernel.const_apply, lintegral_dirac, zero_sub, even_two, Even.neg_pow,
        lintegral_const, measure_univ, mul_one]
      apply ENNReal.ofReal_le_ofReal
      have := abs_integral_le_one_of_support P hP
      nlinarith [abs_nonneg (∫ x, x ∂P), sq_abs (∫ x, x ∂P)]
  · push Not at hsmall
    refine ⟨laplaceMeanMechanism n ε, is_markov_kernel_laplace_mean_mechanism n hn ε hε,
      is_differentially_private_laplace_mean_mechanism n hn ε hε, fun P hP1 hP ↦ ?_⟩
    rw [min_eq_right hsmall.le]
    refine (central_mean_risk_laplace_mean_mechanism_le n hn ε hε P hP).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h8 : 8 / (n * ε) ^ 2 = 8 * (1 / (n * ε) ^ 2) := by ring
    have hpos : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith

end CKSD
