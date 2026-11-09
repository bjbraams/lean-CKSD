module

public import CKSD.Geometry.Kernels

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
  sorry

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
