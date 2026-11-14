module

public import CKSD.Geometry.Basic
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.MeasureTheory.Integral.LayerCake
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Energy distance and distance-induced maximum mean discrepancy

For real probability laws with finite first moments, the energy distance is twice the integral
of the squared difference of their distribution functions. The proof uses the layer-cake formula
for expected absolute differences and identifies right-continuous distribution functions that
agree almost everywhere.

Gaussian averaging of absolute projections recovers the norm on a finite-dimensional real
inner product space. Averaging the real-law identity therefore proves that Euclidean energy
distance is nonnegative and vanishes exactly for equal laws. The squared maximum mean
discrepancy of the distance-induced kernel is half the energy distance, by first-moment
cancellation. These statements include zero-dimensional spaces.

TauCeti supplies the layer-cake identity, Gaussian absolute first moment, and standard Gaussian
density. Mathlib supplies Fubini, Gaussian projection laws, and characteristic-function uniqueness.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators symmDiff
namespace CKSD

/-- First moments imply integrability of the distance between two independent observations. -/
theorem integrable_norm_sub_prod {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    Integrable (fun z : E × E ↦ ‖z.1 - z.2‖) (P.prod Q) := by
  refine ((hP.comp_fst Q).add (hQ.comp_snd P)).mono' (by fun_prop) (ae_of_all _ fun z ↦ ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply] using norm_sub_le z.1 z.2

/-- The probability that two independent real observations lie on opposite sides of a cutoff. -/
theorem measure_symm_diff_real_prod_eq_cdf (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (t : ℝ) :
    (P.prod Q) ({z : ℝ × ℝ | z.1 ≤ t} ∆ {z : ℝ × ℝ | z.2 ≤ t}) =
      ENNReal.ofReal (cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) := by
  have hfst : {z : ℝ × ℝ | z.1 ≤ t} = Iic t ×ˢ univ := by ext z; simp
  have hsnd : {z : ℝ × ℝ | z.2 ≤ t} = univ ×ˢ Iic t := by ext z; simp
  have hdiff1 : (Iic t ×ˢ (univ : Set ℝ)) \ (univ ×ˢ Iic t) = Iic t ×ˢ Ioi t := by
    ext z; simp
  have hdiff2 : ((univ : Set ℝ) ×ˢ Iic t) \ (Iic t ×ˢ univ) = Ioi t ×ˢ Iic t := by
    ext z; simp [and_comm]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P.prod Q) _)]
  congr 1
  rw [← measureReal_def, measureReal_symmDiff_eq (by measurability) (by measurability),
    hfst, hsnd, hdiff1, hdiff2, measureReal_prod_prod, measureReal_prod_prod]
  have hPcompl : P.real (Ioi t) = 1 - cdf P t := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
  have hQcompl : Q.real (Ioi t) = 1 - cdf Q t := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
  rw [hPcompl, hQcompl, cdf_eq_real, cdf_eq_real]

/-- The expected distance of real observations is the area of their cutoff disagreement
probabilities. -/
theorem integral_abs_sub_prod_eq_integral_cdf (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ |x|) P) (hQ : Integrable (fun x ↦ |x|) Q) :
    Integrable (fun t ↦ cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) ∧
      (∫ z : ℝ × ℝ, |z.1 - z.2| ∂P.prod Q) =
        ∫ t, cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t := by
  have hi : Integrable (fun z : ℝ × ℝ ↦ |z.1 - z.2|) (P.prod Q) :=
    integrable_norm_sub_prod P Q hP hQ
  have hnon (t : ℝ) : 0 ≤ cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t :=
    add_nonneg (mul_nonneg (cdf_nonneg P t) (sub_nonneg.2 (cdf_le_one Q t)))
      (mul_nonneg (sub_nonneg.2 (cdf_le_one P t)) (cdf_nonneg Q t))
  have hm : Measurable (fun t ↦ cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) :=
    (cdf P).mono.measurable.mul (measurable_const.sub (cdf Q).mono.measurable) |>.add
      ((measurable_const.sub (cdf P).mono.measurable).mul (cdf Q).mono.measurable)
  have hl := TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff (P.prod Q)
    measurable_fst.aemeasurable measurable_snd.aemeasurable
  simp_rw [Real.enorm_eq_ofReal_abs, measure_symm_diff_real_prod_eq_cdf] at hl
  have hfi : Integrable (fun t ↦ cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnon)).2 ?_⟩
    rw [← hl]
    exact hi.lintegral_lt_top
  refine ⟨hfi, ?_⟩
  have hreal := congrArg ENNReal.toReal hl
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z ↦ abs_nonneg _) hi.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnon) hfi.aestronglyMeasurable] at hreal
  exact hreal

/-- Right-continuous monotone real functions which agree almost everywhere agree everywhere. -/
theorem stieltjes_function_eq_of_ae_eq (f g : StieltjesFunction ℝ)
    (hae : (f : ℝ → ℝ) =ᵐ[volume] (g : ℝ → ℝ)) : f = g := by
  have hle (f g : StieltjesFunction ℝ)
      (hae : (f : ℝ → ℝ) =ᵐ[volume] (g : ℝ → ℝ)) (x : ℝ) : f x ≤ g x := by
    by_contra hnot
    have hx : g x < f x := lt_of_not_ge hnot
    let m := (f x + g x) / 2
    have hgm : g x < m := by dsimp [m]; linarith
    have hmf : m < f x := by dsimp [m]; linarith
    have hright : ∀ᶠ y in 𝓝[Set.Ici x] x, g y < m :=
      (g.right_continuous x).eventually (gt_mem_nhds hgm)
    obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhdsWithin_iff.1 hright
    obtain ⟨y, hyeq, hy⟩ := (Measure.dense_of_ae hae).exists_mem_open isOpen_Ioo
      (show (Ioo x (x + ε)).Nonempty by exact nonempty_Ioo.2 (by linarith))
    have hyg : g y < m := hεg ⟨?_, hy.1.le⟩
    · have hfy : f x ≤ f y := f.mono hy.1.le
      rw [hyeq] at hfy
      linarith
    · rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 hy.1)]
      linarith [hy.2]
  ext x
  exact le_antisymm (hle f g hae x) (hle g f hae.symm x)

/-- Real energy distance is twice the integrated squared difference of distribution functions. -/
theorem real_energy_distance_eq_integral_cdf_sq (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ |x|) P) (hQ : Integrable (fun x ↦ |x|) Q) :
    Integrable (fun t ↦ (cdf P t - cdf Q t) ^ 2) ∧
      2 * (∫ z : ℝ × ℝ, |z.1 - z.2| ∂P.prod Q) -
        (∫ z : ℝ × ℝ, |z.1 - z.2| ∂P.prod P) -
          (∫ z : ℝ × ℝ, |z.1 - z.2| ∂Q.prod Q) =
        2 * ∫ t, (cdf P t - cdf Q t) ^ 2 := by
  obtain ⟨hPQ, ePQ⟩ := integral_abs_sub_prod_eq_integral_cdf P Q hP hQ
  obtain ⟨hPP, ePP⟩ := integral_abs_sub_prod_eq_integral_cdf P P hP hP
  obtain ⟨hQQ, eQQ⟩ := integral_abs_sub_prod_eq_integral_cdf Q Q hQ hQ
  have heq (t : ℝ) : 2 * (cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) -
      (cdf P t * (1 - cdf P t) + (1 - cdf P t) * cdf P t) -
      (cdf Q t * (1 - cdf Q t) + (1 - cdf Q t) * cdf Q t) =
        2 * (cdf P t - cdf Q t) ^ 2 := by ring
  have hsum := ((hPQ.const_mul 2).sub hPP).sub hQQ
  have htwo : Integrable (fun t ↦ 2 * (cdf P t - cdf Q t) ^ 2) :=
    hsum.congr (ae_of_all _ heq)
  have hdiff : Integrable (fun t ↦ (cdf P t - cdf Q t) ^ 2) := by
    exact (htwo.const_mul (1 / 2 : ℝ)).congr (ae_of_all _ fun t ↦ by dsimp only; ring)
  refine ⟨hdiff, ?_⟩
  have hmid : Integrable (fun t ↦
      2 * (cdf P t * (1 - cdf Q t) + (1 - cdf P t) * cdf Q t) -
      (cdf P t * (1 - cdf P t) + (1 - cdf P t) * cdf P t)) := (hPQ.const_mul 2).sub hPP
  rw [ePQ, ePP, eQQ, ← integral_const_mul, ← integral_sub (hPQ.const_mul 2) hPP,
    ← integral_sub hmid hQQ, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ heq)

/-- Real energy distance is nonnegative and vanishes precisely for equal laws. -/
theorem real_energy_distance_nonneg_eq_zero_iff (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ |x|) P) (hQ : Integrable (fun x ↦ |x|) Q) :
    let D := 2 * (∫ z : ℝ × ℝ, |z.1 - z.2| ∂P.prod Q) -
      (∫ z : ℝ × ℝ, |z.1 - z.2| ∂P.prod P) -
        (∫ z : ℝ × ℝ, |z.1 - z.2| ∂Q.prod Q)
    0 ≤ D ∧ (D = 0 ↔ P = Q) := by
  obtain ⟨hint, heq⟩ := real_energy_distance_eq_integral_cdf_sq P Q hP hQ
  dsimp only
  rw [heq]
  refine ⟨mul_nonneg (by norm_num) (integral_nonneg fun t ↦ sq_nonneg _), ?_⟩
  constructor
  · intro hzero
    have h0 : (∫ t, (cdf P t - cdf Q t) ^ 2) = 0 := by linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun t ↦ sq_nonneg _) hint).1 h0
    apply Measure.eq_of_cdf
    apply stieltjes_function_eq_of_ae_eq
    filter_upwards [hae] with t ht
    exact sub_eq_zero.1 (sq_eq_zero_iff.1 ht)
  · intro hPQ
    subst Q
    simp

/-- The energy distance of two laws on a normed space, written through independent copies. -/
def energyDistance {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P Q : Measure E) : ℝ :=
  2 * (∫ z : E × E, ‖z.1 - z.2‖ ∂P.prod Q) -
    (∫ z : E × E, ‖z.1 - z.2‖ ∂P.prod P) - (∫ z : E × E, ‖z.1 - z.2‖ ∂Q.prod Q)

/-- Gaussian averaging of absolute projections recovers the Euclidean norm. -/
theorem integral_abs_inner_std_gaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    (∫ w, |inner ℝ w v| ∂stdGaussian E) = Real.sqrt (2 / Real.pi) * ‖v‖ := by
  have hmap : (stdGaussian E).map (innerSL ℝ v) = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
    rw [(inferInstance : IsGaussian ((stdGaussian E).map (innerSL ℝ v))).eq_gaussianReal,
      integral_map (by fun_prop) (by fun_prop), variance_map (by fun_prop) (by fun_prop)]
    simp only [id_eq, Function.id_comp, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm]
  have heq : (∫ w, |inner ℝ w v| ∂stdGaussian E) =
      ∫ t, |t| ∂((stdGaussian E).map (innerSL ℝ v)) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    exact ae_of_all _ fun w ↦ by simp [real_inner_comm]
  rw [heq, hmap, TauCeti.Probability.integral_abs_gaussianReal,
    Real.toNNReal_of_nonneg (sq_nonneg _)]
  change Real.sqrt (2 * ‖v‖ ^ 2 / Real.pi) = Real.sqrt (2 / Real.pi) * ‖v‖
  rw [show 2 * ‖v‖ ^ 2 / Real.pi = (2 / Real.pi) * ‖v‖ ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The Gaussian average of the expected absolute projected distance is a positive constant
times the expected Euclidean distance. -/
theorem integral_gaussian_projected_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    Integrable (fun w ↦ ∫ z : E × E, |inner ℝ w (z.1 - z.2)| ∂P.prod Q) (stdGaussian E) ∧
      (∫ w, ∫ z : E × E, |inner ℝ w (z.1 - z.2)| ∂P.prod Q ∂stdGaussian E) =
        Real.sqrt (2 / Real.pi) * ∫ z : E × E, ‖z.1 - z.2‖ ∂P.prod Q := by
  have hdist := integrable_norm_sub_prod P Q hP hQ
  have hG : Integrable (fun w : E ↦ ‖w‖) (stdGaussian E) := (IsGaussian.integrable_id : Integrable id (stdGaussian E)).norm
  have hint : Integrable (fun p : E × (E × E) ↦ |inner ℝ p.1 (p.2.1 - p.2.2)|)
      ((stdGaussian E).prod (P.prod Q)) := by
    refine (hG.mul_prod hdist).mono' (by fun_prop) (ae_of_all _ fun p ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_abs] using abs_real_inner_le_norm p.1 (p.2.1 - p.2.2)
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  simp_rw [integral_abs_inner_std_gaussian]
  rw [integral_const_mul]

/-- The standard Gaussian has positive mass on every nonempty open subset. -/
theorem is_open_pos_measure_std_gaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (stdGaussian E).IsOpenPosMeasure := by
  rw [TauCeti.Probability.stdGaussian_eq_withDensity_norm E]
  refine (withDensity_absolutelyContinuous' (by fun_prop) (ae_of_all _ fun x ↦ ?_)).isOpenPosMeasure
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

/-- Projecting a finite-first-moment law gives a real law with finite first moment. -/
theorem integrable_abs_map_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) (hP : Integrable (fun x ↦ ‖x‖) P) (w : E) :
    Integrable (fun t : ℝ ↦ |t|) (P.map (fun x ↦ inner ℝ w x)) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  refine (hP.const_mul ‖w‖).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using abs_real_inner_le_norm w x

/-- Expected distance under two projected laws is the corresponding projected product integral. -/
theorem integral_abs_sub_map_inner_prod {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (w : E) :
    (∫ z : ℝ × ℝ, |z.1 - z.2| ∂(P.map (fun x ↦ inner ℝ w x)).prod
      (Q.map (fun x ↦ inner ℝ w x))) =
      ∫ z : E × E, |inner ℝ w (z.1 - z.2)| ∂P.prod Q := by
  rw [Measure.map_prod_map P Q (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by simp only [Prod.map_fst, Prod.map_snd, inner_sub_right]

/-- Energy distance on a finite-dimensional real inner product space is nonnegative and
vanishes only for equal probability laws with finite first moments. -/
theorem energy_distance_nonneg_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    0 ≤ energyDistance P Q ∧ (energyDistance P Q = 0 ↔ P = Q) := by
  let J (μ ν : Measure E) (w : E) := ∫ z : E × E, |inner ℝ w (z.1 - z.2)| ∂μ.prod ν
  let D (w : E) := 2 * J P Q w - J P P w - J Q Q w
  obtain ⟨hPQ, ePQ⟩ := integral_gaussian_projected_distance P Q hP hQ
  obtain ⟨hPP, ePP⟩ := integral_gaussian_projected_distance P P hP hP
  obtain ⟨hQQ, eQQ⟩ := integral_gaussian_projected_distance Q Q hQ hQ
  have hmid : Integrable (fun w ↦ 2 * J P Q w - J P P w) (stdGaussian E) :=
    (hPQ.const_mul 2).sub hPP
  have hD : Integrable D (stdGaussian E) := hmid.sub hQQ
  have hmean : (∫ w, D w ∂stdGaussian E) = Real.sqrt (2 / Real.pi) * energyDistance P Q := by
    change (∫ w, (2 * J P Q w - J P P w) - J Q Q w ∂stdGaussian E) = _
    rw [integral_sub hmid hQQ, integral_sub (hPQ.const_mul 2) hPP, integral_const_mul]
    change 2 * (∫ w, J P Q w ∂stdGaussian E) - (∫ w, J P P w ∂stdGaussian E) -
      (∫ w, J Q Q w ∂stdGaussian E) = _
    rw [show (∫ w, J P Q w ∂stdGaussian E) = _ from ePQ,
      show (∫ w, J P P w ∂stdGaussian E) = _ from ePP,
      show (∫ w, J Q Q w ∂stdGaussian E) = _ from eQQ]
    unfold energyDistance
    ring
  have hreal (w : E) : 0 ≤ D w ∧
      (D w = 0 ↔ P.map (fun x ↦ inner ℝ w x) = Q.map (fun x ↦ inner ℝ w x)) := by
    have h := real_energy_distance_nonneg_eq_zero_iff
      (P.map (fun x ↦ inner ℝ w x)) (Q.map (fun x ↦ inner ℝ w x))
      (integrable_abs_map_inner P hP w) (integrable_abs_map_inner Q hQ w)
    dsimp only at h
    simp_rw [integral_abs_sub_map_inner_prod] at h
    exact h
  have hK : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (div_pos two_pos Real.pi_pos)
  refine ⟨?_, ?_⟩
  · have hn : 0 ≤ ∫ w, D w ∂stdGaussian E := integral_nonneg fun w ↦ (hreal w).1
    rw [hmean] at hn
    exact nonneg_of_mul_nonneg_right hn hK
  constructor
  · intro hzero
    have h0 : (∫ w, D w ∂stdGaussian E) = 0 := by rw [hmean, hzero, mul_zero]
    have hae := (integral_eq_zero_iff_of_nonneg (fun w ↦ (hreal w).1) hD).1 h0
    have hchar (μ : Measure E) (w : E) :
        charFun (μ.map (fun x ↦ inner ℝ w x)) (1 : ℝ) = charFun μ w := by
      rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), charFun_apply]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp [real_inner_comm]
    have hcf : charFun P =ᵐ[stdGaussian E] charFun Q := by
      filter_upwards [hae] with w hw
      have heq := congrArg (fun ν : Measure ℝ ↦ charFun ν (1 : ℝ)) ((hreal w).2.1 hw)
      simpa only [hchar] using heq
    have := is_open_pos_measure_std_gaussian (E := E)
    exact Measure.ext_of_charFun (Measure.eq_of_ae_eq hcf continuous_charFun continuous_charFun)
  · intro hPQ
    subst Q
    unfold energyDistance
    ring

/-- The mean of a distance-induced kernel is expressed by the first moments and mean distance. -/
theorem integral_distance_kernel_prod {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    (∫ z : E × E, distanceKernel z.1 z.2 ∂P.prod Q) =
      ((∫ x, ‖x‖ ∂P) + (∫ y, ‖y‖ ∂Q) - (∫ z : E × E, ‖z.1 - z.2‖ ∂P.prod Q)) / 2 := by
  change (∫ z : E × E, (‖z.1‖ + ‖z.2‖ - ‖z.1 - z.2‖) / 2 ∂P.prod Q) = _
  have hsum : Integrable (fun z : E × E ↦ ‖z.1‖ + ‖z.2‖) (P.prod Q) :=
    (hP.comp_fst Q).add (hQ.comp_snd P)
  rw [integral_div, integral_sub hsum (integrable_norm_sub_prod P Q hP hQ),
    integral_add (hP.comp_fst Q) (hQ.comp_snd P), integral_fun_fst, integral_fun_snd]
  simp

/-- The energy distance is twice the squared maximum mean discrepancy of the distance kernel. -/
theorem energy_distance_eq_two_mul_squared_mmd {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    energyDistance P Q = 2 * squaredMMD distanceKernel P Q := by
  rw [squaredMMD, integral_distance_kernel_prod P P hP hP,
    integral_distance_kernel_prod Q Q hQ hQ, integral_distance_kernel_prod P Q hP hQ]
  unfold energyDistance
  ring

end CKSD
