module
import CKSD.LinearModels.GLMAsymptotics.Basic
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder InnerProductSpace RealInnerProductSpace
namespace CKSD
variable {p : ℕ}

/-- The rescaled negative log-likelihood process of a canonical-link model,
`h ↦ ∑_{i<n} (b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - yᵢ ⟪xᵢ, h/√n⟫)`, is convex when `b` is. -/
private theorem convex_on_canonical_glm_process {b : ℝ → ℝ} (hbconv : ConvexOn ℝ univ b)
    (β : EuclideanSpace ℝ (Fin p)) (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) (n : ℕ) :
    ConvexOn ℝ univ fun h : EuclideanSpace ℝ (Fin p) ↦ ∑ i ∈ Finset.range n,
      (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (x i) β) -
        y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • h)) := by
  refine ⟨convex_univ, fun u _ v _ a a' ha ha' hab ↦ ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  set s := (Real.sqrt n)⁻¹
  have key : inner ℝ (x i) (β + s • (a • u + a' • v)) =
      a • inner ℝ (x i) (β + s • u) + a' • inner ℝ (x i) (β + s • v) := by
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    linear_combination (-(inner ℝ (x i) β)) * hab
  have hlin : inner ℝ (x i) (s • (a • u + a' • v)) =
      a * inner ℝ (x i) (s • u) + a' * inner ℝ (x i) (s • v) := by
    simp only [inner_add_right, inner_smul_right]
    ring
  have hρ := hbconv.2 (mem_univ (inner ℝ (x i) (β + s • u)))
    (mem_univ (inner ℝ (x i) (β + s • v))) ha ha' hab
  rw [key, hlin]
  simp only [smul_eq_mul] at hρ ⊢
  have : (a + a') * b (inner ℝ (x i) β) = b (inner ℝ (x i) β) := by rw [hab, one_mul]
  nlinarith

/-- A root `β̂` of the canonical-link likelihood equations minimizes the rescaled process
`h ↦ ∑_{i<n} (b(⟪xᵢ, β + h/√n⟫) - b(⟪xᵢ, β⟫) - yᵢ ⟪xᵢ, h/√n⟫)` at `h = √n (β̂ - β)`. -/
private theorem canonical_glm_process_le_of_is_canonical_glm_root {b : ℝ → ℝ}
    (hdiff : Differentiable ℝ b) (hbconv : ConvexOn ℝ univ b) (β : EuclideanSpace ℝ (Fin p))
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (y : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {βh : EuclideanSpace ℝ (Fin p)} (hω : IsCanonicalGLMRoot b n x y βh)
    (h : EuclideanSpace ℝ (Fin p)) :
    ∑ i ∈ Finset.range n,
      (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • (Real.sqrt n • (βh - β)))) -
        b (inner ℝ (x i) β) - y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • (Real.sqrt n • (βh - β)))) ≤
      ∑ i ∈ Finset.range n, (b (inner ℝ (x i) (β + (Real.sqrt n)⁻¹ • h)) -
        b (inner ℝ (x i) β) - y i * inner ℝ (x i) ((Real.sqrt n)⁻¹ • h)) := by
  set s := (Real.sqrt n)⁻¹ with hs_def
  set a := Real.sqrt n • (βh - β) with ha_def
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
  have hβ' : β + s • a = βh := by
    rw [ha_def, smul_smul, hs_def, inv_mul_cancel₀ hs, one_smul, add_sub_cancel]
  rw [IsCanonicalGLMRoot, ← hβ'] at hω
  have hsum : ∑ i ∈ Finset.range n, (y i - deriv b (inner ℝ (x i) (β + s • a))) *
      (inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a)) = 0 := by
    have := congrArg (fun w ↦ ⟪w, s • h - s • a⟫_ℝ) hω
    simp only [sum_inner] at this
    simpa only [real_inner_smul_left, inner_zero_left, inner_sub_right, mul_sub, sub_self]
      using this
  calc _ = ∑ i ∈ Finset.range n,
        ((b (inner ℝ (x i) (β + s • a)) - b (inner ℝ (x i) β) -
          y i * inner ℝ (x i) (s • a)) -
        (y i - deriv b (inner ℝ (x i) (β + s • a))) *
          (inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a))) := by
        symm
        rw [Finset.sum_sub_distrib, hsum, sub_zero]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have htan := add_mul_sub_le_of_convex_on_of_has_deriv_within_at hbconv
          (hdiff (inner ℝ (x i) (β + s • a))).hasDerivAt.hasDerivWithinAt
          (inner ℝ (x i) (β + s • h))
        have hvu : inner ℝ (x i) (β + s • h) - inner ℝ (x i) (β + s • a) =
            inner ℝ (x i) (s • h) - inner ℝ (x i) (s • a) := by
          simp only [inner_add_right]; ring
        rw [hvu] at htan
        linarith

/-- Studentization of a Gaussian limit: if `αₙ ⇒ N(0, φ J⁻¹)` with `J` positive definite and
`φ̂ₙ → φ > 0` in probability, then `φ̂ₙ^{-1/2} J^{1/2} αₙ ⇒ N(0, I)`. -/
private theorem tendsto_in_distribution_studentized_glm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {J : Matrix (Fin p) (Fin p) ℝ} (hJ : J.PosDef)
    {φ : ℝ} (hφ : 0 < φ) (α : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hαm : ∀ n, Measurable (α n))
    (hlim1 : TendstoInDistribution α atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J⁻¹)))
    (φhat : ℕ → Ω → ℝ) (hφm : ∀ n, Measurable (φhat n))
    (hφcons : TendstoInMeasure P φhat atTop (fun _ ↦ φ)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ •
        Matrix.toEuclideanLin (CFC.sqrt J) (α n ω)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 1) := by
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit
  set S := CFC.sqrt J with hS_def
  have hJ0 : 0 ≤ J := Matrix.nonneg_iff_posSemidef.2 hJ.posSemidef
  have hSS : S * S = J := CFC.sqrt_mul_sqrt_self J hJ0
  have hS0 : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg J)
  have hSt : S.transpose = S := (Matrix.isHermitian_iff_isSymm.1 hS0.isHermitian).eq
  have hSdet : IsUnit S.det := by
    rw [← hSS, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_left hdet
  have hSJS : S * J⁻¹ * S = 1 := by
    rw [← hSS, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSdet,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hSdet]
  set k := (Real.sqrt φ)⁻¹ with hk_def
  have hk : k * k * φ = 1 := by
    rw [hk_def, ← mul_inv, Real.mul_self_sqrt hφ.le, inv_mul_cancel₀ hφ.ne']
  set Mk := k • S with hMk
  have hS1 : (φ • J⁻¹).PosSemidef := hJ.inv.posSemidef.smul hφ.le
  have hT : TendstoInDistribution (fun (n : ℕ) ω ↦ Mk.toEuclideanLin (α n ω)) atTop id
      (fun _ ↦ P) (multivariateGaussian 0 1) := by
    have hm := TauCeti.Probability.map_affine_multivariateGaussian 0 hS1 Mk 0
    simp only [add_zero, map_zero] at hm
    refine tendsto_in_distribution_of_map_eq (hlim1.continuous_comp
      (LinearMap.continuous_of_finiteDimensional Mk.toEuclideanLin)) aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, hm]
    have hM : Mk * (φ • J⁻¹) * Mk.transpose = 1 := by
      rw [hMk, Matrix.transpose_smul, hSt, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, hSJS, smul_smul, smul_smul]
      rw [hk, one_smul]
    rw [hM]
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ S.toEuclideanLin (α n ω) with hV
  have hVd : TendstoInDistribution V atTop id (fun _ ↦ P)
      ((multivariateGaussian 0 (φ • J⁻¹)).map S.toEuclideanLin) := by
    have := hlim1.continuous_comp (LinearMap.continuous_of_finiteDimensional S.toEuclideanLin)
    refine tendsto_in_distribution_of_map_eq this (by fun_prop) ?_
    rw [Function.comp_id, Measure.map_id]
  have hc : TendstoInMeasure P (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ - k) atTop
      (fun _ ↦ 0) := by
    have hcont : ContinuousAt (fun x ↦ (Real.sqrt x)⁻¹ - k) φ :=
      (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_ne_zero'.2 hφ)).sub continuousAt_const
    simpa [hk_def] using tendsto_in_measure_comp_of_continuous_at P φhat φ _ hcont hφcons
  have hsm := tendsto_in_measure_smul_zero P _ V hc hVd
  refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable P _ _
    (fun n ↦ (LinearMap.continuous_of_finiteDimensional _).measurable.comp (hαm n))
    (fun n ↦ ((Real.continuous_sqrt.measurable.comp (hφm n)).inv).smul
      ((LinearMap.continuous_of_finiteDimensional _).measurable.comp (hαm n))) hT ?_
  refine hsm.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
  simp only [hV, hMk, map_smul, LinearMap.smul_apply, sub_smul, Function.comp_apply]

/-- The normalized canonical GLM score converges to its Gaussian information limit. -/
private theorem tendsto_in_distribution_canonical_glm_score {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (β : EuclideanSpace ℝ (Fin p))
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid' : IsIndependentIdenticallyDistributed P (fun i w ↦ (X i w,Y i w)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef) :
    let U := fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
      (Y i w-deriv b (inner ℝ (X i w) β)) • X i w
    (∀ n, Measurable (U n)) ∧ TendstoInDistribution U atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (φ • canonicalGLMInformation Px b β)) := by
  intro U
  let J := canonicalGLMInformation Px b β
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hiid'.1 i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hiid'.1 i)
  have hd1 : Continuous (deriv b) := hb.continuous_deriv (by norm_num)
  have hUm : ∀ n, Measurable (U n) := fun n ↦ by
    have := hXm; have := hYm
    dsimp only [U]
    fun_prop
  have hS : (φ • J).PosSemidef := hJ.posSemidef.smul hφ.le
  refine ⟨hUm,?_⟩
  refine TendstoInDistribution.of_inner aemeasurable_id (fun n ↦ (hUm n).aemeasurable)
    fun v ↦ ?_
  obtain ⟨h2, h0, hsq⟩ := mem_lp_score_and_integral hb hφ hlaw hR hκ v
  have key := tendsto_in_distribution_inv_sqrt_mul_sum_of_iid P (Px ⊗ₘ κ) _ hiid'
    (fun z ↦ (z.2 - deriv b (inner ℝ z.1 β)) * inner ℝ z.1 v) (by fun_prop) h2 h0
  have hfun : (fun (n : ℕ) ω ↦ ⟪U n ω, v⟫_ℝ) = fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, (Y i ω - deriv b (inner ℝ (X i ω) β)) * inner ℝ (X i ω) v := by
    funext n ω
    simp only [U, real_inner_smul_left, sum_inner]
  rw [hfun]
  refine tendsto_in_distribution_of_map_eq key (by fun_prop) ?_
  have hW : (fun z : EuclideanSpace ℝ (Fin p) ↦ ⟪id z, v⟫_ℝ) = fun z ↦ ⟪v, z⟫_ℝ :=
    funext fun z ↦ real_inner_comm _ _
  rw [hW, TauCeti.Probability.map_inner_multivariateGaussian 0 v hS, Measure.map_id,
    inner_zero_right, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, hsq]
  congr 2
  change ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (φ • J) v⟫_ℝ = _
  rw [Matrix.inner_toEuclideanCLM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- GAPS 105.3, canonical-link form: for independent and identically distributed pairs
`(xᵢ, Yᵢ)` whose response given the covariate is exponential-dispersion with natural parameter
`⟪x, β⟫`, with covariates bounded by `R`, smooth cumulant function, natural parameter space all
of `ℝ`, and nonsingular `J = E[x xᵀ b''(⟪x, β⟫)]`, every measurable root `β̂` of the likelihood
equations satisfies `√n (β̂ - β) ⇒ N(0, φ J⁻¹)`, and
`φ̂^{-1/2} J^{1/2} √n (β̂ - β) ⇒ N(0, I_p)` for every consistent `φ̂`. Restrictions of scope:
canonical link (`g = (b')⁻¹`), bounded covariates, and natural parameter space `ℝ`; the
general twice-differentiable link is not covered. Consistency of `β̂` is not assumed: the log
likelihood is concave, so every root is a maximizer, and the argument goes through the
convexity lemma `CKSD.tendsto_in_measure_sub_of_convex_on_of_is_min_on`. -/
theorem tendsto_in_distribution_canonical_glm_root {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (β : EuclideanSpace ℝ (Fin p))
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef)
    (βhat : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (hβm : ∀ n, Measurable (βhat n))
    (hroot : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P,
      IsCanonicalGLMRoot b n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω))
    (φhat : ℕ → Ω → ℝ) (hφm : ∀ n, Measurable (φhat n))
    (hφcons : TendstoInMeasure P φhat atTop (fun _ ↦ φ)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (βhat n ω - β)) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 (φ • (canonicalGLMInformation Px b β)⁻¹)) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt (φhat n ω))⁻¹ •
          Matrix.toEuclideanLin (CFC.sqrt (canonicalGLMInformation Px b β))
            (Real.sqrt n • (βhat n ω - β))) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 1) := by
  classical
  set J := canonicalGLMInformation Px b β with hJ_def
  obtain ⟨hZm, hind, hlawZ⟩ := hiid
  have hiid' : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ) :=
    ⟨hZm, hind, hlawZ⟩
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hZm i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hZm i)
  have hd1 : Continuous (deriv b) := hb.continuous_deriv (by norm_num)
  have hb2 : Continuous (iteratedDeriv 2 b) := hb.continuous_iteratedDeriv 2 (by norm_num)
  have hdiff : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hbconv : ConvexOn ℝ univ b := by
    refine convexOn_univ_of_deriv2_nonneg hdiff ?_ fun x ↦ ?_
    · have := hb.differentiable_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    · rw [← iteratedDeriv_eq_iterate]
      exact iterated_deriv_two_nonneg hφ hlaw x
  -- covariates are bounded almost surely
  set R0 := max R 0 with hR0
  have haeR : ∀ᵐ ω ∂P, ∀ i, ‖X i ω‖ ≤ R0 := by
    refine ae_all_iff.2 fun i ↦ ?_
    have h1 : ∀ᵐ z ∂(Px ⊗ₘ κ), ‖z.1‖ ≤ R0 := by
      have := hR
      rw [← map_fst_comp_prod (Px := Px) (κ := κ)] at this
      exact (ae_of_ae_map measurable_fst.aemeasurable this).mono fun z hz ↦
        hz.trans (le_max_left _ _)
    rw [← hlawZ i] at h1
    exact ae_of_ae_map (hZm i).aemeasurable h1
  -- the information operator
  set A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J with hA_def
  set B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hB_def
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit
  have hAB : ∀ u, A (B u) = u := fun u ↦ by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) J * Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹) u = u
    rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
    rfl
  have hAsymm : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    fun u v ↦ (Matrix.isSymmetric_toEuclideanLin_iff.2 hJ.isHermitian) u v
  obtain ⟨c, hc, hA⟩ := exists_pos_mul_sq_le_inner_to_euclidean_clm hJ
  -- the normalized score and its central limit theorem
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (Y i ω - deriv b (inner ℝ (X i ω) β)) • X i ω
    with hU
  have hUm : ∀ n, Measurable (U n) := fun n ↦ by
    have := hXm; have := hYm
    fun_prop
  have hS : (φ • J).PosSemidef := hJ.posSemidef.smul hφ.le
  have hclt : TendstoInDistribution U atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J)) := by
    have hh := (tendsto_in_distribution_canonical_glm_score P ν b hb φ hφ hlaw Px κ β
      hκ R hR X Y hiid' hJ).2
    simpa only [hU,hJ_def] using hh
  have htight : ∀ η > (0 : ℝ≥0∞), ∃ M : ℝ, ∀ᶠ n in atTop, P {ω | M < ‖U n ω‖} ≤ η := by
    intro η hη
    rcases eq_or_ne η ⊤ with rfl | hηt
    · exact ⟨0, Eventually.of_forall fun _ ↦ le_top⟩
    obtain ⟨M, -, hM⟩ := exists_measure_real_lt_norm_le_of_tendsto_in_distribution P U hclt
      (ENNReal.toReal_pos hη.ne' hηt)
    refine ⟨M, hM.mono fun n hn ↦ ?_⟩
    rw [← ofReal_measureReal]
    exact (ENNReal.ofReal_le_iff_le_toReal hηt).2 hn
  -- the convex process
  set Z : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ := fun n ω h ↦ ∑ i ∈ Finset.range n,
    (b (inner ℝ (X i ω) (β + (Real.sqrt n)⁻¹ • h)) - b (inner ℝ (X i ω) β) -
      Y i ω * inner ℝ (X i ω) ((Real.sqrt n)⁻¹ • h)) with hZ
  have hZc : ∀ n ω, ConvexOn ℝ univ (Z n ω) := fun n ω ↦
    convex_on_canonical_glm_process hbconv β (fun i ↦ X i ω) (fun i ↦ Y i ω) n
  -- roots are minimizers
  set α : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ Real.sqrt n • (βhat n ω - β) with hα
  have hmin' : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ h, Z n ω (α n ω) ≤ Z n ω h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hroot n hn] with ω hω h
    exact canonical_glm_process_le_of_is_canonical_glm_root hdiff hbconv β _ _ hn hω h
  -- pointwise convergence of the convex process
  have hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {ω | ε ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|}) atTop (𝓝 0) := by
    intro h ε hε
    have H : TendstoInMeasure P (fun (n : ℕ) ω ↦ Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2)
        atTop (fun _ ↦ 0) := by
      exact tendsto_in_measure_glm_process P hb hR β X Y hiid' haeR h
    simpa [Real.dist_eq] using tendstoInMeasure_iff_dist.1 H ε hε
  have hlin := tendsto_in_measure_sub_of_convex_on_of_is_min_on Z hZc U A B hAB hAsymm hc hA hpt
    htight α hmin'
  -- the limit law of `√n (β̂ₙ - β)`
  have hsymm : J⁻¹.transpose = J⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, (Matrix.isHermitian_iff_isSymm.1 hJ.isHermitian).eq]
  have hlim1 : TendstoInDistribution α atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (φ • J⁻¹)) := by
    set g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
      fun y ↦ (J⁻¹).toEuclideanLin y + 0 with hg
    have hgc : Continuous g := (LinearMap.continuous_of_finiteDimensional _).add continuous_const
    have hmap := TauCeti.Probability.map_affine_multivariateGaussian 0 hS J⁻¹ 0
    have hlimU : TendstoInDistribution (fun (n : ℕ) ↦ g ∘ U n) atTop id (fun _ ↦ P)
        (multivariateGaussian 0 (φ • J⁻¹)) := by
      refine tendsto_in_distribution_of_map_eq (hclt.continuous_comp hgc) aemeasurable_id ?_
      rw [Measure.map_id, Function.comp_id, hmap, hsymm, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      simp
    refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable P _ _
      (fun n ↦ hgc.measurable.comp (hUm n)) (fun n ↦ by have := hβm n; fun_prop) hlimU ?_
    refine hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
    simp only [hα, hg, Function.comp_apply, add_zero, hB_def,
      ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  refine ⟨hlim1, ?_⟩
  convert tendsto_in_distribution_studentized_glm P hJ hφ α
    (fun n ↦ by have := hβm n; fun_prop) hlim1 φhat hφm hφcons

/-- GAPS 105.3, deviance test for nested canonical-link models with known dispersion: if the
true coefficient lies in a subspace `L`, `β̂` is a consistent root of the full likelihood
equations and `β̃` a consistent maximizer of the likelihood over `L`, then the scaled deviance
difference `2 (ℓₙ(β̂) - ℓₙ(β̃))` converges in distribution to chi-squared on
`p - dim L` degrees of freedom. Hypotheses as in `tendsto_in_distribution_canonical_glm_root`. -/
theorem tendsto_in_distribution_canonical_glm_deviance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) (b : ℝ → ℝ) (hb : ContDiff ℝ 3 b)
    (φ : ℝ) (hφ : 0 < φ)
    (hlaw : ∀ θ, IsProbabilityMeasure (exponentialDispersionLaw ν b φ θ))
    (Px : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure Px]
    (κ : Kernel (EuclideanSpace ℝ (Fin p)) ℝ) [IsMarkovKernel κ]
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (β : EuclideanSpace ℝ (Fin p)) (hβL : β ∈ L)
    (hκ : ∀ x, κ x = exponentialDispersionLaw ν b φ (inner ℝ x β))
    (R : ℝ) (hR : ∀ᵐ x ∂Px, ‖x‖ ≤ R)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (Y : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed P (fun i ω ↦ (X i ω, Y i ω)) (Px ⊗ₘ κ))
    (hJ : (canonicalGLMInformation Px b β).PosDef)
    (βhat βtilde : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hβm : ∀ n, Measurable (βhat n)) (hβm' : ∀ n, Measurable (βtilde n))
    (hcons : TendstoInMeasure P βhat atTop (fun _ ↦ β))
    (hcons' : TendstoInMeasure P βtilde atTop (fun _ ↦ β))
    (hroot : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P,
      IsCanonicalGLMRoot b n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω))
    (hmax : ∀ n, ∀ᵐ ω ∂P, βtilde n ω ∈ L ∧ ∀ γ ∈ L,
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) γ ≤
        canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βtilde n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦
        2 * (canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βhat n ω) -
          canonicalGLMLogLikelihood b φ n (fun i ↦ X i ω) (fun i ↦ Y i ω) (βtilde n ω)))
      atTop id (fun _ ↦ P)
      (TauCeti.Probability.chiSquaredMeasure (p - Module.finrank ℝ L : ℕ)) := by
  classical
  -- Convexity controls the minimizers without needing the stated consistency assumptions.
  clear hcons hcons'
  let J := canonicalGLMInformation Px b β
  let S := CFC.sqrt J⁻¹
  obtain ⟨F,hF,hFlinear,hFquad⟩ := exists_glm_whitening hJ hφ
  let K := L.map F.symm.toLinearMap
  let U := fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
    (Y i w-deriv b (inner ℝ (X i w) β)) • X i w
  obtain ⟨hUm,hclt⟩ := tendsto_in_distribution_canonical_glm_score P ν b hb φ hφ hlaw Px κ β
    hκ R hR X Y hiid hJ
  change (∀ n, Measurable (U n)) at hUm
  change TendstoInDistribution U atTop id (fun _ ↦ P) (multivariateGaussian 0 (φ • J)) at hclt
  let W := fun (n : ℕ) w ↦ (Real.sqrt φ)⁻¹ • S.toEuclideanLin (U n w)
  have hWm : ∀ n, Measurable (W n) := fun n ↦ by
    change Measurable ((fun x : EuclideanSpace ℝ (Fin p) ↦
      (Real.sqrt φ)⁻¹ • S.toEuclideanLin x) ∘ U n)
    exact ((LinearMap.continuous_of_finiteDimensional S.toEuclideanLin).const_smul
      (Real.sqrt φ)⁻¹).measurable.comp (hUm n)
  have hWclt : TendstoInDistribution W atTop id (fun _ ↦ P)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) := by
    have hJJ : J⁻¹⁻¹=J := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit)
    have hc : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) ↦ φ) atTop (fun _ ↦ φ) := by
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      simp [hε.not_ge]
    have hJlocal : J.PosDef := hJ
    have hh := tendsto_in_distribution_studentized_glm P hJlocal.inv hφ U hUm
      (by simpa only [hJJ] using hclt) (fun _ _ ↦ φ) (fun _ ↦ measurable_const) hc
    simpa only [multivariateGaussian_zero_one] using hh
  have hXm : ∀ i, Measurable (X i) := fun i ↦ measurable_fst.comp (hiid.1 i)
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_snd.comp (hiid.1 i)
  have hdiff : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hbconv : ConvexOn ℝ univ b := by
    refine convexOn_univ_of_deriv2_nonneg hdiff ?_ fun x ↦ ?_
    · have := hb.differentiable_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    · rw [← iteratedDeriv_eq_iterate]
      exact iterated_deriv_two_nonneg hφ hlaw x
  have haeR : ∀ᵐ w ∂P, ∀ i, ‖X i w‖ ≤ max R 0 := by
    refine ae_all_iff.2 fun i ↦ ?_
    have h1 : ∀ᵐ z ∂(Px ⊗ₘ κ), ‖z.1‖ ≤ max R 0 := by
      have hh := hR
      rw [← map_fst_comp_prod (Px := Px) (κ := κ)] at hh
      exact (ae_of_ae_map measurable_fst.aemeasurable hh).mono fun z hz ↦
        hz.trans (le_max_left _ _)
    rw [← hiid.2.2 i] at h1
    exact ae_of_ae_map (hiid.1 i).aemeasurable h1
  let Z0 := fun (n : ℕ) w h ↦ ∑ i ∈ Finset.range n,
    (b (inner ℝ (X i w) (β+(Real.sqrt n)⁻¹ • h))-b (inner ℝ (X i w) β)-
      Y i w * inner ℝ (X i w) ((Real.sqrt n)⁻¹ • h))
  let Z := fun (n : ℕ) w h ↦ Z0 n w (F h)/φ
  have hZc : ∀ n w, ConvexOn ℝ univ (Z n w) := by
    intro n w
    have hh := convex_on_canonical_glm_process hbconv β (fun i ↦ X i w) (fun i ↦ Y i w) n
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    have hxy := hh.2 (mem_univ (F x)) (mem_univ (F y)) ha hb hab
    have hscaled := div_le_div_of_nonneg_right hxy hφ.le
    simpa only [Z,Z0,map_add,map_smul,smul_eq_mul,add_div,mul_div_assoc] using hscaled
  have hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {w | ε ≤ |Z n w h+inner ℝ (W n w) h-‖h‖^2/2|}) atTop (𝓝 0) := by
    intro h ε hε
    have hh := tendsto_in_measure_glm_process P hb hR β X Y hiid haeR (F h)
    have hscaled := tendsto_in_measure_const_mul_zero P _ φ⁻¹ hh
    have heq (n) (w) : φ⁻¹ * (Z0 n w (F h)+inner ℝ (U n w) (F h)-
        inner ℝ (F h) (J.toEuclideanLin (F h))/2) =
        Z n w h+inner ℝ (W n w) h-‖h‖^2/2 := by
      rw [← hFlinear,← hFquad]
      dsimp only [Z]
      ring
    have hscaled' : TendstoInMeasure P (fun n w ↦ Z n w h+inner ℝ (W n w) h-‖h‖^2/2)
        atTop (fun _ ↦ 0) := by
      refine hscaled.congr (fun n ↦ ae_of_all _ fun w ↦ ?_) EventuallyEq.rfl
      simpa only [Z0,U,J,← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe] using heq n w
    simpa only [Real.dist_eq,sub_zero] using (tendstoInMeasure_iff_dist.1 hscaled') ε hε
  let α := fun (n : ℕ) w ↦ F.symm (Real.sqrt n • (βhat n w-β))
  let β0 := fun (n : ℕ) w ↦ F.symm (Real.sqrt n • (βtilde n w-β))
  have hβ0mem (n) (w) (hw : βtilde n w ∈ L) : β0 n w ∈ K := by
    exact Submodule.mem_map.2 ⟨Real.sqrt n • (βtilde n w-β),
      L.smul_mem _ (L.sub_mem hw hβL),rfl⟩
  let βK := fun (n : ℕ) w ↦ if hh : β0 n w ∈ K then (⟨β0 n w,hh⟩ : K) else 0
  have hβKcoe (n) (w) (hw : βtilde n w ∈ L) : (βK n w : EuclideanSpace ℝ (Fin p)) = β0 n w := by
    simp only [βK,dite_eq_left (hβ0mem n w hw)]
  have hZLL (n) (w) (h) : Z n w h =
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i w) (fun i ↦ Y i w) β-
      canonicalGLMLogLikelihood b φ n (fun i ↦ X i w) (fun i ↦ Y i w)
        (β+(Real.sqrt n)⁻¹ • F h) := by
    simp only [Z,Z0,canonicalGLMLogLikelihood,← Finset.sum_div]
    rw [← sub_div,← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_add_right]
    ring
  have hαcenter (n : ℕ) (hn : 0 < n) (w) : β+(Real.sqrt n)⁻¹ • F (α n w)=βhat n w := by
    simp only [α,F.apply_symm_apply,smul_smul,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 hn)),one_smul,add_sub_cancel]
  have hβcenter (n : ℕ) (hn : 0 < n) (w) (hw : βtilde n w ∈ L) :
      β+(Real.sqrt n)⁻¹ • F (βK n w)=βtilde n w := by
    rw [hβKcoe n w hw]
    simp only [β0,F.apply_symm_apply,smul_smul,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 hn)),one_smul,add_sub_cancel]
  have hminα : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h, Z n w (α n w) ≤ Z n w h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hroot n hn] with w hw h
    have hle := canonical_glm_process_le_of_is_canonical_glm_root hdiff hbconv β _ _ hn hw (F h)
    have hdiv := div_le_div_of_nonneg_right hle hφ.le
    simpa only [Z,Z0,α,F.apply_symm_apply] using hdiv
  have hminβ : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h : K, Z n w (βK n w) ≤ Z n w h := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hmax n] with w hw h
    have hFh : F (h : EuclideanSpace ℝ (Fin p)) ∈ L := by
      obtain ⟨v,hv,he⟩ := Submodule.mem_map.1 h.property
      rw [← he]
      change F (F.symm v) ∈ L
      simpa only [F.apply_symm_apply] using hv
    have hnew : β+(Real.sqrt n)⁻¹ • F (h : EuclideanSpace ℝ (Fin p)) ∈ L :=
      L.add_mem hβL (L.smul_mem _ hFh)
    have hh := hw.2 _ hnew
    rw [hZLL,hZLL,hβcenter n (by omega) w hw.1]
    linarith
  let D := fun (n : ℕ) w ↦ 2*(canonicalGLMLogLikelihood b φ n (fun i ↦ X i w)
    (fun i ↦ Y i w) (βhat n w)-canonicalGLMLogLikelihood b φ n (fun i ↦ X i w)
      (fun i ↦ Y i w) (βtilde n w))
  have hDm : ∀ n, Measurable (D n) := by
    intro n
    have hβ := hβm n
    have hβ' := hβm' n
    have hm_b := hb.continuous.measurable
    dsimp only [D,canonicalGLMLogLikelihood]
    fun_prop
  have hDeq (n : ℕ) : D n =ᵐ[P] fun w ↦ -2*(Z n w (α n w)-Z n w (βK n w)) := by
    filter_upwards [hmax n] with w hw
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [D,Z,Z0,canonicalGLMLogLikelihood]
    · rw [hZLL,hZLL,hαcenter n hn w,hβcenter n hn w hw.1]
      dsimp only [D]
      ring
  have hdim : Module.finrank ℝ Kᗮ = p-Module.finrank ℝ L := by
    have hdim1 := K.finrank_add_finrank_orthogonal
    have hdim2 : Module.finrank ℝ K = Module.finrank ℝ L := F.symm.finrank_map_eq L
    simp only [finrank_euclideanSpace,Fintype.card_fin,hdim2] at hdim1
    omega
  have hlimit := tendsto_in_distribution_convex_deviance P Z hZc W hWm hWclt hpt K α βK
    hminα hminβ D hDm hDeq
  rw [hdim] at hlimit; exact hlimit

end CKSD
