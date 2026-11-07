module

public import CKSD.Inference.Density
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Inference: Gaussian

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.57, strict James–Stein improvement in dimension at least three. -/
theorem james_stein_risk_eq_and_lt {p : ℕ} (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p)) :
    let P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ);
    let δ := fun x : EuclideanSpace ℝ (Fin p) ↦ (1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x;
    (∫ x, ‖δ x - θ‖ ^ 2 ∂P) = (p : ℝ) - ((p : ℝ) - 2) ^ 2 *
      (∫ x, (‖x‖ ^ 2)⁻¹ ∂P) ∧ (∫ x, ‖δ x - θ‖ ^ 2 ∂P) < p := by
  sorry

/-- The isotropic Gaussian density `N(θ, v I)` in closed form: its value at `θ` times
`exp (-‖x - θ‖² / (2v))`. Stated for TauCeti's `multivariateGaussianPDFReal`. -/
theorem multivariateGaussianPDFReal_smul_one {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (x : EuclideanSpace ℝ (Fin p)) :
    TauCeti.Probability.multivariateGaussianPDFReal θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) x =
      TauCeti.Probability.multivariateGaussianPDFReal θ
        ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) θ *
        Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) := by
  have hv' : (v : ℝ) ≠ 0 := (NNReal.coe_pos.2 hv).ne'
  have hinv : ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))⁻¹ = (v : ℝ)⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hv', one_smul]
  simp only [TauCeti.Probability.multivariateGaussianPDFReal_def, hinv, sub_self, map_zero,
    inner_zero_left, neg_zero, zero_div, Real.exp_zero, mul_one]
  congr 2
  rw [map_smul, LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]


/-- GAPS 101.64: Gaussian integration by parts, in the continuously differentiable scope.
The proof writes the law as a density against Lebesgue measure
(TauCeti's `multivariateGaussian_eq_withDensity`) and applies Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. -/
theorem gaussian_integration_by_parts {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ContDiff ℝ 1 g) :
    let P := multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ));
    ∀ (hL2 : MemLp g 2 P),
    ∀ (hder : ∀ i, Integrable
      (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i) P),
    ∀ (i : Fin p),
    (∫ x, (x i - θ i) * g x i ∂P) =
      (v : ℝ) * ∫ x, (fderiv ℝ g x (EuclideanSpace.single i 1)) i ∂P := by
  intro P hL2 hder i
  have hv' : (v : ℝ) ≠ 0 := (NNReal.coe_pos.2 hv).ne'
  have hS : ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (NNReal.coe_pos.2 hv)
  let φ := TauCeti.Probability.multivariateGaussianPDFReal θ
    ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))
  let e : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single i 1
  have hφm : Measurable φ := TauCeti.Probability.measurable_multivariateGaussianPDFReal _ _
  have hφnn : ∀ x, 0 ≤ φ x := TauCeti.Probability.multivariateGaussianPDFReal_nonneg _ _
  have hden : HasDensity P volume φ :=
    ⟨hφm, ae_of_all _ hφnn, by
      show multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) = _
      rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS θ,
        TauCeti.Probability.multivariateGaussianPDF_def]⟩
  have hint : ∀ h : EuclideanSpace ℝ (Fin p) → ℝ,
      Integrable h P ↔ Integrable (fun x ↦ φ x * h x) volume := by
    intro h
    rw [hden.2.2, integrable_withDensity_iff_integrable_smul' hφm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hφnn _), smul_eq_mul]
  -- the coordinate function `g i` and its partial derivative
  let gi : EuclideanSpace ℝ (Fin p) → ℝ := fun x ↦ g x i
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgi : ∀ x, HasFDerivAt gi ((EuclideanSpace.proj i).comp (fderiv ℝ g x)) x :=
    fun x ↦ (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) i).hasFDerivAt.comp x (hgd x).hasFDerivAt
  have hgi_fd : ∀ x, fderiv ℝ gi x e = fderiv ℝ g x e i := fun x ↦ by
    rw [(hgi x).fderiv]; rfl
  -- the derivative of the density
  let c := φ θ
  have hφeq : φ = fun x ↦ c * Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) :=
    funext fun x ↦ multivariateGaussianPDFReal_smul_one θ v hv x
  have hφd : ∀ x, HasFDerivAt φ (c • (Real.exp (-((v : ℝ)⁻¹ * ‖x - θ‖ ^ 2) / 2) •
      ((-(v : ℝ)⁻¹ / 2) • (2 • (innerSL ℝ (x - θ)).comp (ContinuousLinearMap.id ℝ _))))) x := by
    intro x
    rw [hφeq]
    have h1 := HasFDerivAt.norm_sq ((hasFDerivAt_id x).sub_const θ)
    have h2 := (h1.const_mul (-(v : ℝ)⁻¹ / 2)).exp.const_mul c
    convert h2 using 2
    · simp only [id]; congr 1; ring_nf
    · simp only [id]; congr 2; ring_nf
  have hφ_fd : ∀ x, fderiv ℝ φ x e = -((v : ℝ)⁻¹ * (x i - θ i)) * φ x := fun x ↦ by
    rw [(hφd x).fderiv, hφeq]
    simp [e, EuclideanSpace.inner_single_right]
    ring_nf
  -- integrability under `P`
  have hmemLp_gi : MemLp gi 2 P :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p) i).comp_memLp' hL2
  have hmemLp_x : MemLp (fun x : EuclideanSpace ℝ (Fin p) ↦ x i - θ i) 2 P :=
    (IsGaussian.memLp_dual (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)))
      (EuclideanSpace.proj i) 2 (by simp)).sub (memLp_const _)
  have hxg : Integrable (fun x ↦ (x i - θ i) * gi x) P := hmemLp_x.integrable_mul hmemLp_gi
  have hgP : Integrable gi P := hmemLp_gi.integrable one_le_two
  have hf'g : Integrable (fun x ↦ fderiv ℝ φ x e * gi x) volume := by
    simp_rw [hφ_fd]
    refine (((hint _).1 hxg).const_mul (-(v : ℝ)⁻¹)).congr (ae_of_all _ fun x ↦ ?_)
    simp only
    ring
  have hfg' : Integrable (fun x ↦ φ x * fderiv ℝ gi x e) volume := by
    simp_rw [hgi_fd]
    exact (hint _).1 (hder i)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' ((hint _).1 hgP)
    (fun x _ ↦ (hφd x).differentiableAt) (fun x _ ↦ (hgi x).differentiableAt)
  rw [hden.integral_eq, hden.integral_eq]
  have hrw : (∫ x, φ x * (fderiv ℝ g x (EuclideanSpace.single i 1)) i) =
      ∫ x, φ x * fderiv ℝ gi x e := by
    simp_rw [hgi_fd]; rfl
  rw [hrw, hibp]
  simp_rw [hφ_fd]
  rw [← integral_neg, ← integral_const_mul]
  congr 1
  funext x
  field_simp
  ring

/-- GAPS 101.69: existence and uniqueness of a regular natural-exponential-family maximum.
The domain is the full Laplace-integrability domain, not an arbitrary open
subset of it. The criterion is the per-observation log likelihood. -/
theorem exists_exponential_family_mle_iff_mem_interior_convex_support
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    ∀ (hNne : N.Nonempty),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t : EuclideanSpace ℝ (Fin d)),
    (∃ eta ∈ N, ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta) ↔
      t ∈ interior (convexHull ℝ nu.support) := by
  sorry

/-- GAPS 101.69: a natural-family maximizer is unique and solves the mean equation. -/
theorem exponential_family_mle_unique_and_mean_eq
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t eta : EuclideanSpace ℝ (Fin d)),
    ∀ (heta : eta ∈ N),
    ∀ (hmax : ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta),
    HasFDerivAt A (innerSL ℝ t) eta ∧
      ∀ zeta ∈ N, inner ℝ zeta t - A zeta = inner ℝ eta t - A eta → zeta = eta := by
  sorry


/-- GAPS 101.60: the simultaneous-contrast supremum underlying Scheffé's method.
This is the geometric identity; its Gaussian pivot uses the projection sampling laws. -/
theorem scheffe_contrast_supremum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Submodule ℝ H) (v : H) (hv : v ∈ S) (s : ℝ) (hs : 0 < s) :
    sSup {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} =
      ‖v‖ ^ 2 / s ^ 2 := by
  by_cases hv0 : v = 0
  · subst v
    by_cases hS : ∃ u ∈ S, u ≠ (0 : H)
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = {0} := by
        ext r
        simp only [inner_zero_right, zero_pow two_ne_zero, zero_div, mem_ofPred_eq,
          mem_singleton_iff]
        exact ⟨fun ⟨_, _, _, hr⟩ ↦ hr, fun hr ↦ by
          obtain ⟨u, hu, hune⟩ := hS
          exact ⟨u, hu, hune, hr⟩⟩
      rw [hset]
      simp
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro r ⟨u, hu, hune, _⟩
        exact hS ⟨u, hu, hune⟩
      rw [hset]
      simp
  · let R := {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)}
    have hupper : ∀ r ∈ R, r ≤ ‖v‖ ^ 2 / s ^ 2 := by
      rintro r ⟨u, hu, hune, rfl⟩
      have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hune
      have hcs := real_inner_mul_inner_self_le u v
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos hu0))
        (sq_pos_of_pos hs)).mpr
      nlinarith [mul_nonneg (sq_nonneg s)
        (show 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 by nlinarith)]
    have hmem : ‖v‖ ^ 2 / s ^ 2 ∈ R := by
      refine ⟨v, hv, hv0, ?_⟩
      rw [real_inner_self_eq_norm_sq]
      field_simp [ne_of_gt hs, norm_ne_zero_iff.mpr hv0]
    exact le_antisymm (csSup_le ⟨_, hmem⟩ hupper) (le_csSup ⟨_, hupper⟩ hmem)

end CKSD
