module

public import CKSD.Geometry.Kernels
public import Mathlib.Algebra.Order.Chebyshev
public import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Random Fourier features

For a shift-invariant kernel `k(x, y) = ∫ cos ⟪ω, x - y⟫ dΛ(ω)` with spectral probability measure
`Λ`, the random Fourier feature kernel averages `2 cos(⟪ωᵢ, x⟫ + bᵢ) cos(⟪ωᵢ, y⟫ + bᵢ)` over
independent frequencies `ωᵢ ∼ Λ` and uniform phases `bᵢ` on `[0, 2π]`. It is an unbiased
estimator of `k`, it concentrates pointwise by Hoeffding's inequality, and a uniform kernel
error controls the error of the squared maximum mean discrepancy.

## Main results

* `CKSD.integral_randomFourierFeatureKernel`: unbiasedness of the random feature kernel.
* `CKSD.measureReal_abs_randomFourierFeatureKernel_sub_ge_le`: pointwise Hoeffding bound.
* `CKSD.measure_uniform_randomFourierFeatureKernel_error_le`: the uniform error bound over a
  compact set (GAPS 108.74).
* `CKSD.abs_squaredMMD_sub_le_of_uniform_kernel_error`: a uniform kernel error bounds the error
  of the squared MMD (GAPS 108.74).

## References

* A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Over a uniformly distributed phase on `[0, 2π]`, `cos (c + 2b)` has mean zero. -/
theorem integral_cos_add_two_mul_uniformPhase (phase : Measure ℝ)
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (c : ℝ) : ∫ b, Real.cos (c + 2 * b) ∂phase = 0 := by
  rw [hphase, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]
  have hderiv : ∀ b ∈ uIcc 0 (2 * Real.pi),
      HasDerivAt (fun b ↦ Real.sin (c + 2 * b) / 2) (Real.cos (c + 2 * b)) b := by
    intro b _
    have := ((hasDerivAt_id' b).const_mul 2).const_add c |>.sin
    convert this.div_const 2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : Real.sin (c + 2 * (2 * Real.pi)) = Real.sin c := by
    rw [show c + 2 * (2 * Real.pi) = c + ((2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_nat_mul_two_pi c 2
  rw [this]
  simp

/-- The random-feature summand is continuous in the frequency and phase. -/
theorem continuous_randomFourierFeatureTerm {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    Continuous (randomFourierFeatureTerm x y) := by
  unfold randomFourierFeatureTerm; fun_prop

/-- The random-feature summand takes values in `[-2, 2]`. -/
theorem randomFourierFeatureTerm_mem_Icc {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) : randomFourierFeatureTerm x y s ∈ Icc (-2 : ℝ) 2 := by
  unfold randomFourierFeatureTerm
  have h1 := Real.abs_cos_le_one (inner ℝ s.1 x + s.2)
  have h2 := Real.abs_cos_le_one (inner ℝ s.1 y + s.2)
  have : |2 * Real.cos (inner ℝ s.1 x + s.2) * Real.cos (inner ℝ s.1 y + s.2)| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (Real.cos (inner ℝ s.1 x + s.2)),
      abs_nonneg (Real.cos (inner ℝ s.1 y + s.2))]
  exact abs_le.mp this

/-- The random-feature summand is unbiased for the translation-invariant kernel. -/
theorem integral_randomFourierFeatureTerm {d : ℕ}
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ s, randomFourierFeatureTerm x y s ∂L.prod phase = ∫ w, Real.cos (inner ℝ w (x - y)) ∂L := by
  have hint : Integrable (randomFourierFeatureTerm x y) (L.prod phase) := by
    refine Integrable.of_bound (C := 2)
      (continuous_randomFourierFeatureTerm x y).measurable.aestronglyMeasurable
      (ae_of_all _ fun s ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact randomFourierFeatureTerm_mem_Icc x y s
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  have hpt : ∀ b, randomFourierFeatureTerm x y (w, b) =
      Real.cos (inner ℝ w (x - y)) + Real.cos ((inner ℝ w x + inner ℝ w y) + 2 * b) := by
    intro b
    have e1 : inner ℝ w (x - y) = (inner ℝ w x + b) - (inner ℝ w y + b) := by
      rw [inner_sub_right]; ring
    have e2 : inner ℝ w x + inner ℝ w y + 2 * b = (inner ℝ w x + b) + (inner ℝ w y + b) := by
      ring
    rw [e1, e2, Real.cos_sub (inner ℝ w x + b), Real.cos_add (inner ℝ w x + b) (inner ℝ w y + b)]
    simp only [randomFourierFeatureTerm]
    ring
  simp_rw [hpt]
  rw [integral_add (integrable_const _) ?_, integral_const, probReal_univ, one_smul,
    integral_cos_add_two_mul_uniformPhase phase hphase, add_zero]
  exact Integrable.of_bound (C := 1) (by fun_prop) (ae_of_all _ fun b ↦ by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- Hoeffding's inequality for a sample of `D` independent copies of a variable with values in
`[a, b]`: the sum of the centered copies exceeds `D ε` with probability at most
`exp (-2 D ε² / (b - a)²)`. -/
theorem measureReal_pi_sum_sub_integral_ge_le {Y : Type*} [MeasurableSpace Y] (D : ℕ)
    (μ : Measure Y) [IsProbabilityMeasure μ] {g : Y → ℝ} (hg : Measurable g) {a b : ℝ}
    (hb : ∀ s, g s ∈ Icc a b) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin D ↦ μ).real
        {s | D * ε ≤ ∑ j, (g (s j) - ∫ t, g t ∂μ)} ≤
      Real.exp (-2 * (D : ℝ) * ε ^ 2 / (b - a) ^ 2) := by
  set P := Measure.pi fun _ : Fin D ↦ μ
  have hindep : iIndepFun (fun (j : Fin D) (s : Fin D → Y) ↦ g (s j) - ∫ t, g t ∂μ) P :=
    iIndepFun_pi (X := fun _ t ↦ g t - ∫ t, g t ∂μ) fun _ ↦ (hg.sub_const _).aemeasurable
  have hsub : ∀ j : Fin D, HasSubgaussianMGF (fun s : Fin D → Y ↦ g (s j) - ∫ t, g t ∂μ)
      ((‖b - a‖₊ / 2) ^ 2) P := by
    intro j
    have hm : AEMeasurable (fun s : Fin D → Y ↦ g (s j)) P :=
      (hg.comp (measurable_pi_apply j)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc hm (ae_of_all _ fun s ↦ hb (s j))
    have hint : ∫ s, g (s j) ∂P = ∫ t, g t ∂μ :=
      integral_comp_eval (μ := fun _ : Fin D ↦ μ) hg.aestronglyMeasurable
    simpa only [hint] using h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep (s := Finset.univ)
    (fun j _ ↦ hsub j) (ε := D * ε) (by positivity)
  refine h.trans_eq ?_
  congr 1
  have hc : (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (b - a) ^ 2 / 4 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [div_pow, sq_abs]
    norm_num
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, hc]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  rcases eq_or_ne (b - a) 0 with hab | hab
  · simp [hab]
  · have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
    ring

/-- GAPS 108.74: random Fourier features are unbiased. The random Fourier feature kernel of an
independent sample of frequencies `w_j ∼ L` and uniform phases `b_j ∈ [0, 2π]` has mean
`k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)`. -/
theorem integral_randomFourierFeatureKernel {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∫ sample, randomFourierFeatureKernel sample x y ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) =
      ∫ w, Real.cos (inner ℝ w (x - y)) ∂L := by
  have hmeas : Measurable (randomFourierFeatureTerm x y) :=
    (continuous_randomFourierFeatureTerm x y).measurable
  have hcoord : ∀ j : Fin D, ∫ s, randomFourierFeatureTerm x y (s j)
      ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) = ∫ w, Real.cos (inner ℝ w (x - y)) ∂L :=
    fun j ↦ by
      rw [← integral_randomFourierFeatureTerm L phase hphase x y]
      exact integral_comp_eval (μ := fun _ : Fin D ↦ L.prod phase) hmeas.aestronglyMeasurable
  have hintj : ∀ j : Fin D, Integrable (fun s : Fin D → _ ↦ randomFourierFeatureTerm x y (s j))
      (Measure.pi fun _ : Fin D ↦ L.prod phase) :=
    fun j ↦ Integrable.of_bound (C := 2)
      (hmeas.comp (measurable_pi_apply j)).aestronglyMeasurable
      (ae_of_all _ fun s ↦ by
        rw [Real.norm_eq_abs, abs_le]; exact randomFourierFeatureTerm_mem_Icc x y (s j))
  have hDpos : (D : ℝ) ≠ 0 := by exact_mod_cast (show 0 < D by omega).ne'
  simp only [randomFourierFeatureKernel]
  rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hintj j]
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- GAPS 108.74: the pointwise Hoeffding bound for random Fourier features. For an independent
sample of `D ≥ 1` frequencies `w_j ∼ L` and uniform phases, the random-feature kernel deviates from
`k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)` by at least `ε > 0` with probability at most
`2 exp(-D ε² / 8)`. Its unbiasedness is `CKSD.integral_randomFourierFeatureKernel`. -/
theorem measureReal_abs_randomFourierFeatureKernel_sub_ge_le {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) (epsilon : ℝ) (he : 0 < epsilon) :
    (Measure.pi fun _ : Fin D ↦ L.prod phase).real
        {sample | epsilon ≤ |randomFourierFeatureKernel sample x y -
          ∫ w, Real.cos (inner ℝ w (x - y)) ∂L|} ≤
      2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
  set P := Measure.pi fun _ : Fin D ↦ L.prod phase
  set k := ∫ w, Real.cos (inner ℝ w (x - y)) ∂L
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hmeas : Measurable (randomFourierFeatureTerm x y) :=
    (continuous_randomFourierFeatureTerm x y).measurable
  have hk : ∫ s, randomFourierFeatureTerm x y s ∂L.prod phase = k :=
    integral_randomFourierFeatureTerm L phase hphase x y
  have hcenter : ∀ s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ,
      randomFourierFeatureKernel s x y - k =
        (D : ℝ)⁻¹ * ∑ j, (randomFourierFeatureTerm x y (s j) - k) := by
    intro s
    rw [randomFourierFeatureKernel, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hexp : Real.exp (-2 * (D : ℝ) * epsilon ^ 2 / (2 - -2) ^ 2) =
      Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
    congr 1; ring
  have hup := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas
    (randomFourierFeatureTerm_mem_Icc x y) he.le
  have hlo := measureReal_pi_sum_sub_integral_ge_le D (L.prod phase) hmeas.neg (a := -2) (b := 2)
    (fun s ↦ by
      have := randomFourierFeatureTerm_mem_Icc x y s
      exact ⟨by simp only [Pi.neg_apply]; linarith [this.2],
        by simp only [Pi.neg_apply]; linarith [this.1]⟩) he.le
  rw [hk, hexp] at hup
  simp only [Pi.neg_apply, integral_neg, hk] at hlo
  rw [hexp] at hlo
  set A := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ |
    (D : ℝ) * epsilon ≤ ∑ j, (randomFourierFeatureTerm x y (s j) - k)}
  set B := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ |
    (D : ℝ) * epsilon ≤ ∑ j, (-randomFourierFeatureTerm x y (s j) - -k)}
  have hsub : {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|} ⊆ A ∪ B := by
    intro s hs
    simp only [mem_ofPred_eq, hcenter] at hs
    simp only [A, B, mem_union, mem_ofPred_eq]
    have hsum : ∑ j, (-randomFourierFeatureTerm x y (s j) - -k) =
        -∑ j, (randomFourierFeatureTerm x y (s j) - k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsum]
    rcases le_abs'.mp hs with h | h
    · right
      have := mul_le_mul_of_nonneg_left h hDpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hDpos.ne', one_mul] at this
      linarith
    · left
      have := mul_le_mul_of_nonneg_left h hDpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hDpos.ne', one_mul] at this
  calc P.real {sample | epsilon ≤ |randomFourierFeatureKernel sample x y - k|}
      ≤ P.real (A ∪ B) := measureReal_mono hsub
    _ ≤ P.real A + P.real B := measureReal_union_le _ _
    _ ≤ Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) + Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) :=
        add_le_add hup hlo
    _ = 2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by ring

/-- The random-feature summand is Lipschitz in the pair of points: at the frequency-phase pair
`(w, b)` it moves by at most `2 ‖w‖ (‖x - x'‖ + ‖y - y'‖)`. -/
theorem abs_randomFourierFeatureTerm_sub_le {d : ℕ} (x y x' y' : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) :
    |randomFourierFeatureTerm x y s - randomFourierFeatureTerm x' y' s| ≤
      2 * ‖s.1‖ * (‖x - x'‖ + ‖y - y'‖) := by
  unfold randomFourierFeatureTerm
  have hcos : ∀ u v : EuclideanSpace ℝ (Fin d),
      |Real.cos (inner ℝ s.1 u + s.2) - Real.cos (inner ℝ s.1 v + s.2)| ≤ ‖s.1‖ * ‖u - v‖ := by
    intro u v
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [add_sub_add_right_eq_sub, ← inner_sub_right]
    exact abs_real_inner_le_norm _ _
  have h1 := hcos x x'
  have h2 := hcos y y'
  have hc1 := Real.abs_cos_le_one (inner ℝ s.1 y + s.2)
  have hc2 := Real.abs_cos_le_one (inner ℝ s.1 x' + s.2)
  set a := Real.cos (inner ℝ s.1 x + s.2)
  set a' := Real.cos (inner ℝ s.1 x' + s.2)
  set c := Real.cos (inner ℝ s.1 y + s.2)
  set c' := Real.cos (inner ℝ s.1 y' + s.2)
  have he : 2 * a * c - 2 * a' * c' = 2 * ((a - a') * c + a' * (c - c')) := by ring
  rw [he, abs_mul, abs_two]
  have hw := norm_nonneg s.1
  calc 2 * |(a - a') * c + a' * (c - c')| ≤ 2 * (|a - a'| * |c| + |a'| * |c - c'|) := by
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
    _ ≤ 2 * (‖s.1‖ * ‖x - x'‖ * 1 + 1 * (‖s.1‖ * ‖y - y'‖)) := by
        gcongr
    _ = 2 * ‖s.1‖ * (‖x - x'‖ + ‖y - y'‖) := by ring

/-- For a law with finite second moment, `E ‖w‖ ≤ √(E ‖w‖²)`, provided the right side is
positive. -/
private theorem integral_norm_le_sqrt_integral_norm_sq {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] (L : Measure E) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (hσ : 0 < Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)) :
    ∫ w, ‖w‖ ∂L ≤ Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) := by
  set σ := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)
  have h2 : Integrable (fun w : E ↦ ‖w‖ ^ 2) L := by
    simpa using hL2.integrable_norm_pow (by norm_num)
  have h1 : Integrable (fun w : E ↦ ‖w‖) L := (hL2.integrable one_le_two).norm
  have hσ2 : σ ^ 2 = ∫ w, ‖w‖ ^ 2 ∂L := Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)
  have hpt : ∀ w : E, ‖w‖ ≤ (‖w‖ ^ 2 + σ ^ 2) / (2 * σ) := fun w ↦ by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖w‖ - σ)]
  calc ∫ w, ‖w‖ ∂L ≤ ∫ w, (‖w‖ ^ 2 + σ ^ 2) / (2 * σ) ∂L :=
        integral_mono h1 ((h2.add (integrable_const _)).div_const _) hpt
    _ = σ := by
        rw [integral_div, integral_add h2 (integrable_const _), integral_const, probReal_univ,
          one_smul, ← hσ2]
        field_simp
        ring

/-- The shift-invariant kernel `k(x, y) = ∫ cos ⟨w, x - y⟩ dL(w)` is Lipschitz in the pair of
points, with constant `σ = √(E ‖w‖²)`. -/
theorem abs_integral_cos_inner_sub_le {d : ℕ} (L : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (hσ : 0 < Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)) (x y x' y' : EuclideanSpace ℝ (Fin d)) :
    |(∫ w, Real.cos (inner ℝ w (x - y)) ∂L) - ∫ w, Real.cos (inner ℝ w (x' - y')) ∂L| ≤
      Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) * (‖x - x'‖ + ‖y - y'‖) := by
  have hcosint : ∀ u : EuclideanSpace ℝ (Fin d),
      Integrable (fun w ↦ Real.cos (inner ℝ w u)) L := fun u ↦
    Integrable.of_bound (C := 1) (by fun_prop) (ae_of_all _ fun w ↦ by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have h1 : Integrable (fun w : EuclideanSpace ℝ (Fin d) ↦ ‖w‖) L :=
    (hL2.integrable one_le_two).norm
  rw [← integral_sub (hcosint _) (hcosint _)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ w, |Real.cos (inner ℝ w (x - y)) - Real.cos (inner ℝ w (x' - y'))| ∂L
      ≤ ∫ w, ‖w‖ * (‖x - x'‖ + ‖y - y'‖) ∂L := by
        refine integral_mono ((hcosint _).sub (hcosint _)).abs (h1.mul_const _) fun w ↦ ?_
        refine (Real.abs_cos_sub_cos_le _ _).trans ?_
        rw [← inner_sub_right]
        refine (abs_real_inner_le_norm _ _).trans ?_
        gcongr
        rw [show x - y - (x' - y') = (x - x') - (y - y') by abel]
        exact norm_sub_le _ _
    _ ≤ Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) * (‖x - x'‖ + ‖y - y'‖) := by
        rw [integral_mul_const]
        gcongr
        exact integral_norm_le_sqrt_integral_norm_sq L hL2 hσ

/-- The random-feature error `D⁻¹ ∑ⱼ 2 cos(⟨wⱼ, x⟩ + bⱼ) cos(⟨wⱼ, y⟩ + bⱼ) - k(x, y)` is
Lipschitz in the pair of points with the random constant `2 D⁻¹ ∑ⱼ ‖wⱼ‖ + σ`. -/
theorem abs_randomFourierFeatureError_sub_le {d D : ℕ} (L : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (hσ : 0 < Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L))
    (sample : Fin D → EuclideanSpace ℝ (Fin d) × ℝ) (x y x' y' : EuclideanSpace ℝ (Fin d)) :
    |(randomFourierFeatureKernel sample x y - ∫ w, Real.cos (inner ℝ w (x - y)) ∂L) -
        (randomFourierFeatureKernel sample x' y' - ∫ w, Real.cos (inner ℝ w (x' - y')) ∂L)| ≤
      (2 * ((D : ℝ)⁻¹ * ∑ j, ‖(sample j).1‖) + Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)) *
        (‖x - x'‖ + ‖y - y'‖) := by
  have hk := abs_integral_cos_inner_sub_le L hL2 hσ x y x' y'
  have hs : |randomFourierFeatureKernel sample x y - randomFourierFeatureKernel sample x' y'| ≤
      2 * ((D : ℝ)⁻¹ * ∑ j, ‖(sample j).1‖) * (‖x - x'‖ + ‖y - y'‖) := by
    unfold randomFourierFeatureKernel
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_inv, Nat.abs_cast]
    calc (D : ℝ)⁻¹ * |∑ j, (randomFourierFeatureTerm x y (sample j) -
          randomFourierFeatureTerm x' y' (sample j))|
        ≤ (D : ℝ)⁻¹ * ∑ j, 2 * ‖(sample j).1‖ * (‖x - x'‖ + ‖y - y'‖) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ ↦ abs_randomFourierFeatureTerm_sub_le x y x' y' _)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  calc _ = |(randomFourierFeatureKernel sample x y - randomFourierFeatureKernel sample x' y') -
        ((∫ w, Real.cos (inner ℝ w (x - y)) ∂L) - ∫ w, Real.cos (inner ℝ w (x' - y')) ∂L)| := by
        ring_nf
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-- The empirical second moment `Q = D⁻¹ ∑ⱼ ‖wⱼ‖²` of the frequencies of a random-feature sample is
integrable, with mean `E ‖w‖²`. -/
private theorem integrable_and_integral_average_norm_sq_sample {d D : ℕ} (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase] :
    Integrable (fun s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ ↦ (D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖ ^ 2)
        (Measure.pi fun _ ↦ L.prod phase) ∧
      ∫ s, (D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖ ^ 2 ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) =
        ∫ w, ‖w‖ ^ 2 ∂L := by
  have h2 : Integrable (fun w : EuclideanSpace ℝ (Fin d) ↦ ‖w‖ ^ 2) L := by
    simpa using hL2.integrable_norm_pow (by norm_num)
  have hg : Integrable (fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ ‖p.1‖ ^ 2) (L.prod phase) :=
    h2.comp_fst phase
  have hj : ∀ j : Fin D, Integrable (fun s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ ↦
      ‖(s j).1‖ ^ 2) (Measure.pi fun _ ↦ L.prod phase) := fun j ↦
    integrable_comp_eval (μ := fun _ : Fin D ↦ L.prod phase) hg
  refine ⟨(integrable_finsetSum _ fun j _ ↦ hj j).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hj j]
  have hcoord : ∀ j : Fin D, ∫ s, ‖(s j).1‖ ^ 2 ∂(Measure.pi fun _ : Fin D ↦ L.prod phase) =
      ∫ w, ‖w‖ ^ 2 ∂L := fun j ↦ by
    rw [integral_comp_eval (μ := fun _ : Fin D ↦ L.prod phase)
      (f := fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ ‖p.1‖ ^ 2) hg.aestronglyMeasurable,
      integral_fun_fst (fun w : EuclideanSpace ℝ (Fin d) ↦ ‖w‖ ^ 2)]
    simp
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (D : ℝ) ≠ 0 := by exact_mod_cast (show 0 < D by omega).ne'
  field_simp

/-- A set of diameter `Δ > 0` in `ℝ^d` has an `r / 2`-net, `r = (F / 2)^{1/2} Δ`, whose
cardinality squared is at most `(50 / F)^d`, for `0 < F ≤ 2`. -/
private theorem exists_finset_cover_card_sq_le {d : ℕ} {M : Set (EuclideanSpace ℝ (Fin d))}
    {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ M) (hMb : Bornology.IsBounded M)
    (hΔ : 0 < Metric.diam M) {F : ℝ} (hF0 : 0 < F) (hF2 : F ≤ 2) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin d)),
      (∀ x ∈ M, ∃ c ∈ N, ‖x - c‖ ≤ Real.sqrt (F / 2) * Metric.diam M / 2) ∧
        (N.card : ℝ) ^ 2 ≤ (50 / F) ^ d := by
  set Δ := Metric.diam M
  have hΔ0 : 0 ≤ Δ := hΔ.le
  set ρ := Real.sqrt (F / 2) with hρdef
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρ2 : ρ ^ 2 = F / 2 := Real.sq_sqrt (by positivity)
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  set r := ρ * Δ with hrdef
  have hr : 0 < r := mul_pos hρ0 hΔ
  have hMball : M ⊆ Metric.closedBall x0 ((⟨Δ, hΔ0⟩ : ℝ≥0) : ℝ) := fun x hx ↦ by
    rw [Metric.mem_closedBall]
    exact Metric.dist_le_diam_of_mem hMb hx hx0
  set ε' : ℝ≥0 := ⟨r / 2, by positivity⟩ with hε'def
  have hε'r : (ε' : ℝ) = r / 2 := rfl
  have hε'0 : ε' ≠ 0 := fun h ↦ by
    have := congrArg NNReal.toReal h
    rw [hε'r, NNReal.coe_zero] at this
    linarith
  obtain ⟨N, -, hNcov, hNcard⟩ := TauCeti.exists_finset_isCover_of_subset_closedBall hε'0 hMball
  simp only [hε'r, finrank_euclideanSpace_fin] at hNcard
  refine ⟨N, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨c, hc, hxc⟩ := hNcov hx
    refine ⟨c, hc, ?_⟩
    change edist x c ≤ (ε' : ℝ≥0∞) at hxc
    rw [edist_nndist, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nndist, hε'r] at hxc
    rwa [← dist_eq_norm]
  · have h5 : 1 + 2 * Δ / (r / 2) ≤ 5 / ρ := by
      rw [hrdef, show 2 * Δ / (ρ * Δ / 2) = 4 / ρ by field_simp; ring]
      rw [show (5 : ℝ) / ρ = 1 / ρ + 4 / ρ by ring]
      gcongr
      exact one_le_one_div hρ0 hρ1
    calc (N.card : ℝ) ^ 2 ≤ ((5 / ρ) ^ d) ^ 2 := by
          gcongr
          exact hNcard.trans (pow_le_pow_left₀ (by positivity) h5 d)
      _ = (50 / F) ^ d := by
          rw [← pow_mul, mul_comm, pow_mul, div_pow, hρ2]
          congr 1
          field_simp
          norm_num

/-- The Lipschitz-bad event of the random-feature error: by Markov's inequality for the empirical
second moment `D⁻¹ ∑ⱼ ‖wⱼ‖²` of the frequencies, the probability that the random Lipschitz
constant `2 D⁻¹ ∑ⱼ ‖wⱼ‖ + σ` times `r` reaches `ε / 4` is at most `80 u`, when
`ε² / (16 r²) = σ² / (8 u)` and `u < 1 / 98`. -/
private theorem measureReal_lipschitz_bad_le {d D : ℕ} (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase] {epsilon r u : ℝ} (he : 0 < epsilon)
    (hr : 0 < r) (hu0 : 0 < u) (hu : u < 1 / 98) (hσ : 0 < Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L))
    (hq : epsilon ^ 2 / (16 * r ^ 2) = Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) ^ 2 / (8 * u)) :
    (Measure.pi fun _ : Fin D ↦ L.prod phase).real
      {s | epsilon / 4 ≤ (2 * ((D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖) +
        Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)) * r} ≤ 80 * u := by
  set sigma := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L)
  set P := Measure.pi fun _ : Fin D ↦ L.prod phase
  have hσ2 : sigma ^ 2 = ∫ w, ‖w‖ ^ 2 ∂L := Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)
  set S : (Fin D → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ := fun s ↦ (D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖
  set Q : (Fin D → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ := fun s ↦ (D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖ ^ 2
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hSQ : ∀ s, S s ^ 2 ≤ Q s := fun s ↦ by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j ↦ ‖(s j).1‖)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    simp only [S, Q, mul_pow]
    rw [show ((D : ℝ)⁻¹) ^ 2 = (D : ℝ)⁻¹ * (D : ℝ)⁻¹ by ring, mul_assoc]
    gcongr
    rw [inv_mul_le_iff₀ hDpos]
    exact h
  have hS0 : ∀ s, 0 ≤ S s := fun s ↦ by positivity
  obtain ⟨hQint, hQmean⟩ := integrable_and_integral_average_norm_sq_sample hD L hL2 phase
  set c₀ := (epsilon ^ 2 / (16 * r ^ 2) - 2 * sigma ^ 2) / 8 with hc₀def
  have hc₀ : c₀ = sigma ^ 2 * (1 - 16 * u) / (64 * u) := by
    rw [hc₀def, hq]
    field_simp
    ring
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    have : 0 < 1 - 16 * u := by linarith
    positivity
  set Bad := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | epsilon / 4 ≤ (2 * S s + sigma) * r}
  show P.real Bad ≤ 80 * u
  have hBadsub : Bad ⊆ {s | c₀ ≤ Q s} := by
    intro s hs
    simp only [Bad, mem_ofPred_eq] at hs ⊢
    have h1 : (epsilon / 4) ^ 2 ≤ ((2 * S s + sigma) * r) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    have h2 : (2 * S s + sigma) ^ 2 ≤ 8 * Q s + 2 * sigma ^ 2 := by
      have e : (2 * S s + sigma) ^ 2 = 8 * S s ^ 2 + 2 * sigma ^ 2 - (2 * S s - sigma) ^ 2 := by
        ring
      linarith [hSQ s, sq_nonneg (2 * S s - sigma)]
    have h3 : epsilon ^ 2 / (16 * r ^ 2) ≤ 8 * Q s + 2 * sigma ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg r)
      rw [mul_pow] at h1
      have e : epsilon ^ 2 = 16 * (epsilon / 4) ^ 2 := by ring
      linarith
    rw [hc₀def]
    linarith
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := P) (ae_of_all _ fun s ↦ by positivity)
    hQint c₀
  rw [hQmean, ← hσ2] at hM
  have hp0 : 0 ≤ P.real Bad := measureReal_nonneg
  have h1 : c₀ * P.real Bad ≤ sigma ^ 2 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hBadsub) hc₀pos.le).trans hM
  rw [hc₀] at h1
  have hs2 : 0 < sigma ^ 2 := by positivity
  have h2 : (1 - 16 * u) * P.real Bad ≤ 64 * u := by
    have h3 : sigma ^ 2 * ((1 - 16 * u) * P.real Bad) ≤ sigma ^ 2 * (64 * u) := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 64 * u by positivity)
      rw [show 64 * u * (sigma ^ 2 * (1 - 16 * u) / (64 * u) * P.real Bad) =
        sigma ^ 2 * ((1 - 16 * u) * P.real Bad) by field_simp] at this
      linarith
    exact le_of_mul_le_mul_left h3 hs2
  have h4 : (4 / 5) * P.real Bad ≤ (1 - 16 * u) * P.real Bad :=
    mul_le_mul_of_nonneg_right (by linarith) hp0
  linarith

/-- The union bound over the pairs of centres of the net: with `n² ≤ (50 / F)^d`,
`e ≤ (F^{d+1})²` and `98 F < 1`, the total `n · n · 2e` is at most `F`. -/
private theorem card_mul_card_mul_two_mul_le {n d : ℕ} {F e : ℝ} (hF0 : 0 < F)
    (hF98 : 98 * F < 1) (hcard : (n : ℝ) ^ 2 ≤ (50 / F) ^ d) (he0 : 0 ≤ e)
    (hexp : e ≤ (F ^ (d + 1)) ^ 2) : (n : ℝ) * n * (2 * e) ≤ F := by
  have h50 : (50 * F) ^ d ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  calc (n : ℝ) * n * (2 * e) ≤ (50 / F) ^ d * (2 * (F ^ (d + 1)) ^ 2) := by
        rw [← sq]
        gcongr
    _ = 2 * (50 * F) ^ d * F ^ 2 := by
        rw [div_pow, mul_pow, ← pow_mul]
        field_simp
        ring
    _ ≤ 2 * 1 * F ^ 2 := by gcongr
    _ ≤ F := by
        have : F * F ≤ (1 / 2) * F := mul_le_mul_of_nonneg_right (by linarith) hF0.le
        rw [sq]
        linarith

/-- If `ε ≤ |e₁|` and `|e₁ - e₂| ≤ t < ε / 4`, then `3 ε / 4 ≤ |e₂|`. -/
private theorem le_abs_of_le_abs_of_abs_sub_le {e₁ e₂ t ε : ℝ} (h₁ : ε ≤ |e₁|)
    (h₂ : |e₁ - e₂| ≤ t) (h₃ : t < ε / 4) : 3 * ε / 4 ≤ |e₂| := by
  have := abs_sub_abs_le_abs_sub e₁ e₂
  linarith

/-- GAPS 108.74: the uniform compact-set random-feature bound. For a compact set `M ⊆ ℝ^d`, a
frequency law `L` with finite second moment `σ² = E ‖w‖²`, and `ε ≤ σ diam M`, the probability that
the random-feature kernel of `D` features deviates from `k` by at least `ε` somewhere on `M × M` is
at most `98 (σ diam M / ε)² exp(-D ε² / (32 (d + 1)))`. -/
theorem measure_uniform_randomFourierFeatureKernel_error_le {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (M : Set (EuclideanSpace ℝ (Fin d))) (hM : IsCompact M)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hscale : epsilon ≤ Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L) * Metric.diam M) :
    let sigma := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L);
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    let P := Measure.pi (fun _ : Fin D ↦ L.prod phase);
    P.real {sample | ∃ x ∈ M, ∃ y ∈ M, epsilon ≤ |randomFourierFeatureKernel sample x y - k x y|} ≤
      98 * (sigma * Metric.diam M / epsilon) ^ 2 *
        Real.exp (-(D : ℝ) * epsilon ^ 2 / (32 * (d + 1))) := by
  intro sigma k P
  set Δ := Metric.diam M with hΔdef
  have hΔ0 : 0 ≤ Δ := Metric.diam_nonneg
  have hσ0 : 0 ≤ sigma := Real.sqrt_nonneg _
  have hσΔ : 0 < sigma * Δ := he.trans_le hscale
  have hσ : 0 < sigma := lt_of_le_of_ne hσ0 fun h ↦ by rw [← h, zero_mul] at hσΔ; exact hσΔ.false
  have hΔ : 0 < Δ := lt_of_le_of_ne hΔ0 fun h ↦ by rw [← h, mul_zero] at hσΔ; exact hσΔ.false
  obtain ⟨x0, hx0⟩ : M.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [Δ, h] at hΔ
  have hσ2 : sigma ^ 2 = ∫ w, ‖w‖ ^ 2 ∂L := Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)
  set A := sigma * Δ / epsilon with hAdef
  have hA : 1 ≤ A := (one_le_div he).mpr hscale
  set F := Real.exp (-(D : ℝ) * epsilon ^ 2 / (32 * (d + 1))) with hFdef
  have hF0 : 0 < F := Real.exp_pos _
  have hexp : Real.exp (-(D : ℝ) * (3 * epsilon / 4) ^ 2 / 8) ≤ (F ^ (d + 1)) ^ 2 := by
    rw [← pow_mul, hFdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have he2 : (((d + 1) * 2 : ℕ) : ℝ) * (-(D : ℝ) * epsilon ^ 2 / (32 * (d + 1))) =
        -(D : ℝ) * epsilon ^ 2 / 16 := by
      push_cast
      field_simp
      ring
    rw [he2]
    have : 0 ≤ (D : ℝ) * epsilon ^ 2 := by positivity
    linarith
  have hPle1 : P.real {sample | ∃ x ∈ M, ∃ y ∈ M,
      epsilon ≤ |randomFourierFeatureKernel sample x y - k x y|} ≤ 1 := measureReal_le_one
  rcases le_or_gt 1 (98 * A ^ 2 * F) with hbig | hsmall
  · exact hPle1.trans hbig
  set u := A ^ 2 * F with hudef
  have hu : u < 1 / 98 := by rw [hudef]; linarith
  have hFu : F ≤ u := le_mul_of_one_le_left hF0.le (one_le_pow₀ hA)
  have hu0 : 0 < u := hF0.trans_le hFu
  -- the radius of the net
  set ρ := Real.sqrt (F / 2) with hρdef
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hρ2 : ρ ^ 2 = F / 2 := Real.sq_sqrt (by positivity)
  set r := ρ * Δ with hrdef
  have hr : 0 < r := mul_pos hρ0 hΔ
  -- an `r / 2`-net of `M` with at most `(50 / F)^(d / 2)` points
  obtain ⟨N, hcov, hcard⟩ := exists_finset_cover_card_sq_le hx0 hM.isBounded hΔ hF0
    (by linarith)
  -- the random Lipschitz constant
  set S : (Fin D → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ := fun s ↦ (D : ℝ)⁻¹ * ∑ j, ‖(s j).1‖
  have hS0 : ∀ s, 0 ≤ S s := fun s ↦ by positivity
  -- the event that the Lipschitz constant is large
  have hq : epsilon ^ 2 / (16 * r ^ 2) = sigma ^ 2 / (8 * u) := by
    rw [hudef, hAdef, hrdef, mul_pow, hρ2]
    field_simp
    ring
  set Bad := {s : Fin D → EuclideanSpace ℝ (Fin d) × ℝ | epsilon / 4 ≤ (2 * S s + sigma) * r}
  have hBad : P.real Bad ≤ 80 * u :=
    measureReal_lipschitz_bad_le hD L hL2 phase he hr hu0 hu hσ hq
  -- the events at the pairs of centres of the net
  set Ctr : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) →
      Set (Fin D → EuclideanSpace ℝ (Fin d) × ℝ) := fun c ↦
    {s | 3 * epsilon / 4 ≤ |randomFourierFeatureKernel s c.1 c.2 - k c.1 c.2|}
  have hCtr : ∀ c, P.real (Ctr c) ≤ 2 * Real.exp (-(D : ℝ) * (3 * epsilon / 4) ^ 2 / 8) :=
    fun c ↦ measureReal_abs_randomFourierFeatureKernel_sub_ge_le D hD L phase hphase c.1 c.2 _
      (by positivity)
  have hsub : {sample | ∃ x ∈ M, ∃ y ∈ M,
      epsilon ≤ |randomFourierFeatureKernel sample x y - k x y|} ⊆
      Bad ∪ ⋃ c ∈ N ×ˢ N, Ctr c := by
    rintro s ⟨x, hx, y, hy, hxy⟩
    by_cases hs : s ∈ Bad
    · exact Or.inl hs
    right
    obtain ⟨a, ha, hxa⟩ := hcov x hx
    obtain ⟨b, hb, hyb⟩ := hcov y hy
    simp only [mem_iUnion]
    refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    simp only [Bad, mem_ofPred_eq, not_le] at hs
    have hlip := abs_randomFourierFeatureError_sub_le L hL2 hσ s x y a b
    have hδ : ‖x - a‖ + ‖y - b‖ ≤ r := by
      have := add_le_add hxa hyb
      rwa [add_halves] at this
    have h1 : (2 * S s + sigma) * (‖x - a‖ + ‖y - b‖) ≤ (2 * S s + sigma) * r :=
      mul_le_mul_of_nonneg_left hδ (add_nonneg (mul_nonneg zero_le_two (hS0 s)) hσ0)
    have hxy' : epsilon ≤
        |randomFourierFeatureKernel s x y - ∫ w, Real.cos (inner ℝ w (x - y)) ∂L| := hxy
    show 3 * epsilon / 4 ≤
      |randomFourierFeatureKernel s a b - ∫ w, Real.cos (inner ℝ w (a - b)) ∂L|
    have h2 := hlip.trans h1
    exact le_abs_of_le_abs_of_abs_sub_le hxy' h2 hs
  have hU : P.real (⋃ c ∈ N ×ˢ N, Ctr c) ≤ F := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ ↦ hCtr c).trans ?_
    rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    exact card_mul_card_mul_two_mul_le hF0 (by linarith) hcard (by positivity) hexp
  calc P.real {sample | ∃ x ∈ M, ∃ y ∈ M,
        epsilon ≤ |randomFourierFeatureKernel sample x y - k x y|}
      ≤ P.real (Bad ∪ ⋃ c ∈ N ×ˢ N, Ctr c) := measureReal_mono hsub
    _ ≤ P.real Bad + P.real (⋃ c ∈ N ×ˢ N, Ctr c) := measureReal_union_le _ _
    _ ≤ 80 * u + F := add_le_add hBad hU
    _ ≤ 98 * (sigma * Δ / epsilon) ^ 2 * F := by
        rw [← hAdef]
        linarith

/-- A function continuous on `M × M`, for a compact `M`, is integrable for every finite measure
concentrated on `M × M`. No second countability of the ambient space is needed. -/
theorem integrable_of_continuousOn_compact_prod
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {M : Set X} (hM : IsCompact M) (ρ : Measure (X × X)) [IsFiniteMeasure ρ]
    (hρ : ρ (M ×ˢ M)ᶜ = 0) {g : X × X → ℝ} (hg : ContinuousOn g (M ×ˢ M)) :
    Integrable g ρ := by
  have hMm : MeasurableSet M := hM.isClosed.measurableSet
  have hs : MeasurableSet (M ×ˢ M) := hMm.prod hMm
  have hρs : ρ.restrict (M ×ˢ M) = ρ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hρ)
  rw [← hρs, ← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).integrable_map_iff]
  have : CompactSpace M := isCompact_iff_compactSpace.mp hM
  let G : M × M → ℝ := fun p ↦ g (p.1, p.2)
  have hG : Continuous G := by
    have : Continuous (fun p : M × M ↦ ((p.1 : X), (p.2 : X))) := by fun_prop
    exact hg.comp_continuous this fun p ↦ ⟨p.1.2, p.2.2⟩
  have hmeas : Measurable (g ∘ ((↑) : ↥(M ×ˢ M) → X × X)) :=
    hG.measurable.comp (MeasurableEquiv.Set.prod M M).measurable
  obtain ⟨C, hC⟩ := hM.prod hM |>.exists_bound_of_continuousOn hg
  have : IsFiniteMeasure (Measure.comap ((↑) : ↥(M ×ˢ M) → X × X) ρ) := by
    constructor
    rw [(MeasurableEmbedding.subtype_coe hs).comap_apply]
    simp
  exact Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ fun z ↦ hC z z.2)

/-- GAPS 108.74, deterministic transfer of a uniform kernel error to squared MMD: if two continuous
kernels differ by at most `ε` on `M × M` for a compact `M` carrying both laws, their squared MMDs
differ by at most `4 ε`. -/
theorem abs_squaredMMD_sub_le_of_uniform_kernel_error
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (M : Set X) (hM : IsCompact M) (hP : P M = 1) (hQ : Q M = 1)
    (k l : X → X → ℝ) (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (epsilon : ℝ)  (herr : ∀ x ∈ M, ∀ y ∈ M, |k x y - l x y| ≤ epsilon) :
    |squaredMMD k P Q - squaredMMD l P Q| ≤ 4 * epsilon := by
  have hMm : MeasurableSet M := hM.isClosed.measurableSet
  have hconc : ∀ (R S : Measure X) [IsProbabilityMeasure R] [IsProbabilityMeasure S],
      R M = 1 → S M = 1 → (R.prod S) (M ×ˢ M)ᶜ = 0 := by
    intro R S _ _ hR hS
    rw [prob_compl_eq_zero_iff (hMm.prod hMm), Measure.prod_prod, hR, hS, one_mul]
  have hk' := hk.continuousOn (s := M ×ˢ M)
  have hl' := hl.continuousOn (s := M ×ˢ M)
  -- each of the three double integrals moves by at most `epsilon`
  have hpiece : ∀ (R S : Measure X) [IsProbabilityMeasure R] [IsProbabilityMeasure S],
      R M = 1 → S M = 1 →
      |(∫ z, k z.1 z.2 ∂R.prod S) - ∫ z, l z.1 z.2 ∂R.prod S| ≤ epsilon := by
    intro R S _ _ hR hS
    have hρ := hconc R S hR hS
    rw [← integral_sub
      (integrable_of_continuousOn_compact_prod (g := fun z : X × X ↦ k z.1 z.2) hM _ hρ hk')
      (integrable_of_continuousOn_compact_prod (g := fun z : X × X ↦ l z.1 z.2) hM _ hρ hl')]
    have hb := norm_integral_le_of_norm_le_const (μ := R.prod S)
      (f := fun z : X × X ↦ k z.1 z.2 - l z.1 z.2) (C := epsilon)
      (Filter.Eventually.mono (p := fun z ↦ z ∈ M ×ˢ M) (mem_ae_iff.mpr hρ)
        fun z hz ↦ herr z.1 hz.1 z.2 hz.2)
    simpa using hb
  have h1 := hpiece P P hP hP
  have h2 := hpiece Q Q hQ hQ
  have h3 := hpiece P Q hP hQ
  unfold squaredMMD
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end CKSD
