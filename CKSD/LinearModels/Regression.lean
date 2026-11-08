module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import TauCeti.Probability.Distributions.Gaussian.Projection
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared

/-!
# LinearModels: Regression

Sources: `GAPS.md`, `SYNOPSIS105.md`, and `STRUCTURE105.md`.
Declarations adapted from this project's section drafts.
The residual law uses TauCeti's standard Gaussian projection and affine-image results.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- With uncorrelated coordinates of common variance `v`, the variance of `⟪b, Y⟫` is
`v ‖b‖²`. -/
theorem variance_inner_of_covariance_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (b : EuclideanSpace ℝ (Fin n)) :
    variance μ (fun ω ↦ inner ℝ b (Y ω)) = v * ‖b‖ ^ 2 := by
  have hYi : ∀ i, MemLp (fun ω ↦ Y ω i) 2 μ := fun i ↦
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hY
  have hbY : ∀ i, MemLp (fun ω ↦ b i * Y ω i) 2 μ := fun i ↦ (hYi i).const_mul (b i)
  have hinner : (fun ω ↦ inner ℝ b (Y ω)) = fun ω ↦ ∑ i, b i * Y ω i := by
    funext ω
    simp [PiLp.inner_apply, mul_comm]
  have hmeas : AEMeasurable (fun ω ↦ inner ℝ b (Y ω)) μ := by
    exact (aestronglyMeasurable_const.inner hY.aestronglyMeasurable).aemeasurable
  have hvar : variance μ (fun ω ↦ inner ℝ b (Y ω)) =
      ProbabilityTheory.variance (fun ω ↦ inner ℝ b (Y ω)) μ :=
    (ProbabilityTheory.variance_eq_integral hmeas).symm
  rw [hvar, ← covariance_self hmeas, hinner,
    covariance_fun_sum_fun_sum hbY hbY]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  have := hcov
  simp only [covariance] at this
  simp_rw [this, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- GAPS 105.1, scalar Gauss–Markov comparison by projecting an unbiased coefficient. -/
theorem variance_projection_le_of_unbiased {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ) (hv : 0 ≤ v)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hm : P (∫ ω, Y ω ∂μ) = ∫ ω, Y ω ∂μ) (a : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (P a) (Y ω) ∂μ) = ∫ ω, inner ℝ a (Y ω) ∂μ ∧
      variance μ (fun ω ↦ inner ℝ (P a) (Y ω)) ≤
        variance μ (fun ω ↦ inner ℝ a (Y ω)) := by
  have hint : Integrable Y μ := hY.integrable one_le_two
  refine ⟨?_, ?_⟩
  · rw [integral_inner hint, integral_inner hint, hPsym, hm]
  · rw [variance_inner_of_covariance_eq μ Y hY v hcov, variance_inner_of_covariance_eq μ Y hY v hcov]
    refine mul_le_mul_of_nonneg_left ?_ hv
    have horth : inner ℝ (P a) (a - P a) = 0 := by
      rw [inner_sub_right, hPsym a (P a), hPid, real_inner_comm, sub_self]
    have : ‖a‖ ^ 2 = ‖P a‖ ^ 2 + ‖a - P a‖ ^ 2 := by
      have h := norm_add_sq_real (P a) (a - P a)
      rw [horth, mul_zero, add_zero, add_sub_cancel] at h
      exact h
    rw [this]
    nlinarith [sq_nonneg ‖a - P a‖]

/-- GAPS 105.2, residual chi-squared law and projection independence. -/
theorem gaussian_projection_residual_law_and_indepFun
    {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (hm : P m = m) :
    let r := Module.finrank ℝ (LinearMap.range P.toLinearMap);
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ ‖x - P x‖ ^ 2 / v) = TauCeti.Probability.chiSquaredMeasure (n - r : ℕ) ∧
      IndepFun P (fun x ↦ ‖x - P x‖ ^ 2) G := by
  intro r G
  let K := LinearMap.range P.toLinearMap
  have hproj : ∀ x, K.starProjection x = P x := by
    intro x
    refine K.eq_starProjection_of_mem_of_inner_eq_zero ⟨x, rfl⟩ ?_
    rintro _ ⟨y, rfl⟩
    change inner ℝ (x - P x) (P y) = 0
    rw [inner_sub_left, hPsym x (P y), hPid, sub_self]
  have hcomp : ∀ x, Kᗮ.starProjection x = x - P x := by
    intro x
    rw [K.starProjection_orthogonal_val, hproj]
  have hdim : Module.finrank ℝ Kᗮ = n - r := by
    have h := K.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace_fin] at h
    change Module.finrank ℝ Kᗮ = n - Module.finrank ℝ K
    omega
  set s := Real.sqrt (v : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  have hs2 : s ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have hG : G = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun z ↦ m + s • z) := by
    have h := TauCeti.Probability.map_add_smul_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin n)) (Matrix.PosSemidef.one) m s
    simpa only [multivariateGaussian_zero_one, smul_zero, add_zero, hs2] using h.symm
  let Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x ↦ s⁻¹ • (x - m)
  have hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))) G := by
    refine ⟨by fun_prop, ?_⟩
    rw [hG, Measure.map_map (by fun_prop) (by fun_prop)]
    have hid : Z ∘ (fun z ↦ m + s • z) = id := by
      funext z
      simp [Z, smul_smul, hs.ne']
    rw [hid, Measure.map_id]
  have hres : ∀ x, Kᗮ.starProjection (Z x) = s⁻¹ • (x - P x) := by
    intro x
    rw [hcomp]
    simp only [Z, map_smul, map_sub, hm]
    module
  have hnorm : ∀ x, ‖Kᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2 = ‖x - P x‖ ^ 2 / v := by
    intro x
    change ‖Kᗮ.starProjection (Z x)‖ ^ 2 = _
    rw [hres, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs2, div_eq_inv_mul]
  constructor
  · simpa only [hnorm, hdim] using (hZ.norm_sq_orthogonalProjectionOnto_stdGaussian Kᗮ).map_eq
  · let Ks : Bool → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun b ↦ if b then K else Kᗮ
    have horth : Pairwise fun i j ↦ (Ks i).IsOrtho (Ks j) := by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact K.isOrtho_orthogonal_left
      · exact K.isOrtho_orthogonal_right
      · exact (hij rfl).elim
    have hi := (hZ.iIndepFun_orthogonalProjectionOnto_stdGaussian Ks horth).indepFun
      (show true ≠ false by decide)
    have hfit : ∀ x, m + s • (K.orthogonalProjectionOnto (Z x) : EuclideanSpace ℝ (Fin n)) = P x := by
      intro x
      change m + s • K.starProjection (Z x) = P x
      rw [hproj]
      simp [Z, map_smul, map_sub, hm, smul_smul, hs.ne']
    have hres' : ∀ x, s ^ 2 * ‖Kᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2 = ‖x - P x‖ ^ 2 := by
      intro x
      rw [hnorm, hs2, mul_div_cancel₀ _ (by exact_mod_cast hv.ne' : (v : ℝ) ≠ 0)]
    have h := hi.comp (φ := fun z : K ↦ m + s • (z : EuclideanSpace ℝ (Fin n)))
      (ψ := fun z : Kᗮ ↦ s ^ 2 * ‖z‖ ^ 2) (by fun_prop) (by fun_prop)
    change IndepFun (fun x ↦ m + s • (K.orthogonalProjectionOnto (Z x) : EuclideanSpace ℝ (Fin n)))
      (fun x ↦ s ^ 2 * ‖Kᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2) G at h
    simpa only [hfit, hres'] using h

/-- GAPS 105.10, exact null F law for nested Gaussian projection models. -/
theorem nested_gaussian_projection_fisher_law
    {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hid : ∀ x, P₀ (P₀ x) = P₀ x ∧ P₁ (P₁ x) = P₁ x)
    (hsym : ∀ x y, inner ℝ (P₀ x) y = inner ℝ x (P₀ y) ∧
      inner ℝ (P₁ x) y = inner ℝ x (P₁ y))
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x) (hm : P₀ m = m) :
    let r₀ := Module.finrank ℝ (LinearMap.range P₀.toLinearMap);
    let r₁ := Module.finrank ℝ (LinearMap.range P₁.toLinearMap);
    ∀ (hr : r₀ < r₁),
    ∀ (hrn : r₁ < n),
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ (‖P₁ x - P₀ x‖ ^ 2 / (r₁ - r₀ : ℕ)) /
      (‖x - P₁ x‖ ^ 2 / (n - r₁ : ℕ))) =
      TauCeti.Probability.fisherSnedecorMeasure (r₁ - r₀ : ℕ) (n - r₁ : ℕ) := by
  intro r₀ r₁ hr hrn G
  have hcomm : ∀ x, P₀ (P₁ x) = P₀ x := by
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [(hsym (P₁ x) y).1, (hsym x (P₀ y)).2, hnest, ← (hsym x y).1]
  have hm₁ : P₁ m = m := by rw [← hm, hnest, hm]
  let K₀ := LinearMap.range P₀.toLinearMap
  let K₁ := LinearMap.range P₁.toLinearMap
  let S := K₀ᗮ ⊓ K₁
  have hle : K₀ ≤ K₁ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨P₀ x, hnest x⟩
  have hSdim : Module.finrank ℝ S = r₁ - r₀ := by
    have h := Submodule.finrank_add_inf_finrank_orthogonal hle
    change r₀ + Module.finrank ℝ S = r₁ at h
    omega
  have hP₁ : ∀ x, K₁.starProjection x = P₁ x := by
    intro x
    refine K₁.eq_starProjection_of_mem_of_inner_eq_zero ⟨x, rfl⟩ ?_
    rintro _ ⟨y, rfl⟩
    change inner ℝ (x - P₁ x) (P₁ y) = 0
    rw [inner_sub_left, (hsym x (P₁ y)).2, (hid y).2, sub_self]
  have hS : ∀ x, S.starProjection x = P₁ x - P₀ x := by
    intro x
    refine S.eq_starProjection_of_mem_of_inner_eq_zero ⟨?_, ?_⟩ ?_
    · refine (Submodule.mem_orthogonal' K₀ _).mpr ?_
      rintro _ ⟨y, rfl⟩
      change inner ℝ (P₁ x - P₀ x) (P₀ y) = 0
      rw [inner_sub_left, ← (hsym (P₁ x) y).1, ← (hsym (P₀ x) y).1, hcomm, (hid x).1, sub_self]
    · refine ⟨x - P₀ x, ?_⟩
      change P₁ (x - P₀ x) = P₁ x - P₀ x
      rw [map_sub, hnest]
    · intro y hy
      have hy₀ := (Submodule.mem_orthogonal' K₀ y).mp hy.1 (P₀ x) ⟨x, rfl⟩
      have hy₁ := K₁.starProjection_inner_eq_zero x y hy.2
      rw [hP₁] at hy₁
      rw [inner_sub_left, inner_sub_left]
      have hy₀' : inner ℝ (P₀ x) y = 0 := by
        rw [real_inner_comm]
        exact hy₀
      rw [hy₀']
      simpa only [inner_sub_left, sub_zero] using hy₁
  have hR : ∀ x, K₁ᗮ.starProjection x = x - P₁ x := by
    intro x
    rw [K₁.starProjection_orthogonal_val, hP₁]
  have hRdim : Module.finrank ℝ K₁ᗮ = n - r₁ := by
    have h := K₁.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace_fin] at h
    change r₁ + Module.finrank ℝ K₁ᗮ = n at h
    omega
  set s := Real.sqrt (v : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hv)
  have hs2 : s ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hG : G = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun z ↦ m + s • z) := by
    have h := TauCeti.Probability.map_add_smul_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin n)) (Matrix.PosSemidef.one) m s
    simpa only [multivariateGaussian_zero_one, smul_zero, add_zero, hs2] using h.symm
  let Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x ↦ s⁻¹ • (x - m)
  have hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))) G := by
    refine ⟨by fun_prop, ?_⟩
    rw [hG, Measure.map_map (by fun_prop) (by fun_prop)]
    have hidZ : Z ∘ (fun z ↦ m + s • z) = id := by
      funext z
      simp [Z, smul_smul, hs.ne']
    rw [hidZ, Measure.map_id]
  have hNS : ∀ x, ‖S.orthogonalProjectionOnto (Z x)‖ ^ 2 = ‖P₁ x - P₀ x‖ ^ 2 / v := by
    intro x
    change ‖S.starProjection (Z x)‖ ^ 2 = _
    rw [hS]
    have hpt : P₁ (Z x) - P₀ (Z x) = s⁻¹ • (P₁ x - P₀ x) := by
      simp only [Z, map_smul, map_sub, hm, hm₁]
      module
    rw [hpt, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs2, div_eq_inv_mul]
  have hNR : ∀ x, ‖K₁ᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2 = ‖x - P₁ x‖ ^ 2 / v := by
    intro x
    change ‖K₁ᗮ.starProjection (Z x)‖ ^ 2 = _
    rw [hR]
    have hpt : Z x - P₁ (Z x) = s⁻¹ • (x - P₁ x) := by
      simp only [Z, map_smul, map_sub, hm₁]
      module
    rw [hpt, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs2, div_eq_inv_mul]
  let Ks : Bool → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun b ↦ if b then S else K₁ᗮ
  have horth : Pairwise fun i j ↦ (Ks i).IsOrtho (Ks j) := by
    intro i j hij
    have hSR : S.IsOrtho K₁ᗮ := K₁.isOrtho_orthogonal_right.mono_left inf_le_right
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hSR.symm
    · exact hSR
    · exact (hij rfl).elim
  have hi := (hZ.iIndepFun_orthogonalProjectionOnto_stdGaussian Ks horth).indepFun
    (show true ≠ false by decide)
  have hi' := hi.comp (φ := fun z : S ↦ ‖z‖ ^ 2)
    (ψ := fun z : K₁ᗮ ↦ ‖z‖ ^ 2) (by fun_prop) (by fun_prop)
  change IndepFun (fun x ↦ ‖S.orthogonalProjectionOnto (Z x)‖ ^ 2)
    (fun x ↦ ‖K₁ᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2) G at hi'
  have hnum := hZ.norm_sq_orthogonalProjectionOnto_stdGaussian S
  have hden := hZ.norm_sq_orthogonalProjectionOnto_stdGaussian K₁ᗮ
  rw [hSdim] at hnum
  rw [hRdim] at hden
  have h := TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared
    (by exact_mod_cast Nat.sub_pos_of_lt hr) (by exact_mod_cast Nat.sub_pos_of_lt hrn)
    hi' hnum hden
  have hpt : (fun x ↦ ‖S.orthogonalProjectionOnto (Z x)‖ ^ 2 / (r₁ - r₀ : ℕ) /
      (‖K₁ᗮ.orthogonalProjectionOnto (Z x)‖ ^ 2 / (n - r₁ : ℕ))) =
      (fun x ↦ (‖P₁ x - P₀ x‖ ^ 2 / (r₁ - r₀ : ℕ)) /
        (‖x - P₁ x‖ ^ 2 / (n - r₁ : ℕ))) := by
    funext x
    rw [hNS, hNR]
    rw [div_right_comm (‖P₁ x - P₀ x‖ ^ 2) (v : ℝ) (r₁ - r₀ : ℕ),
      div_right_comm (‖x - P₁ x‖ ^ 2) (v : ℝ) (n - r₁ : ℕ), div_div_div_cancel_right₀ hv']
  rw [hpt] at h
  exact h.map_eq

/-- GAPS 105.15, Craig–Sakamoto criterion for centered quadratic forms. -/
theorem indepFun_matrixQuadraticForm_iff {n : ℕ} (Sigma A B : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm) :
    IndepFun (matrixQuadraticForm A) (matrixQuadraticForm B)
      (multivariateGaussian 0 Sigma) ↔ A * Sigma * B = 0 := by
  sorry


end CKSD
