module

public import CKSD.Inference.Density
public import CKSD.Inference.Model
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gaussian models: Stein's identity, James–Stein, exponential-family MLE, Scheffé

Results of Section 101 on Gaussian and natural exponential families.

## Main results

* `CKSD.gaussian_integration_by_parts`: Stein's identity for `N(θ, v I)` (GAPS 101.64).
* `CKSD.james_stein_risk_eq_and_lt`: the risk of the James–Stein estimator (GAPS 101.57).
* `CKSD.exists_isMaxOn_logLikelihood_iff_mem_interior_convexHull_support` and
  `CKSD.hasFDerivAt_logPartition_and_eq_of_isMaxOn`: existence, the likelihood equation, and
  uniqueness of the maximum likelihood estimator in a regular minimal natural exponential family
  (GAPS 101.69).
* `CKSD.scheffe_contrast_supremum`: the contrast supremum behind Scheffé's method (GAPS 101.60).

## References

The integration by parts writes the Gaussian law as a density against Lebesgue measure
(TauCeti's `multivariateGaussian_eq_withDensity`) and uses Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.57: the James–Stein estimator `δ(x) = (1 - (p - 2) / ‖x‖²) x` for `X ~ N(θ, I)` in
dimension `p ≥ 3` has risk `p - (p - 2)² E‖X‖⁻²`, strictly smaller than the risk `p` of `X`. -/
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


/-- GAPS 101.64: Gaussian integration by parts (Stein's identity) for `X ~ N(θ, v I)` and a
continuously differentiable `g` with `g ∈ L²` and integrable partial derivatives:
`E[(Xᵢ - θᵢ) gᵢ(X)] = v E[∂ᵢ gᵢ(X)]`.
The proof writes the law as a density against Lebesgue measure
(TauCeti's `multivariateGaussian_eq_withDensity`) and applies Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. -/
theorem gaussian_integration_by_parts {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ContDiff ℝ 1 g)
    (hL2 : MemLp g 2 (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))))
    (hder : ∀ i, Integrable (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i)
      (multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)))) (i : Fin p) :
    (∫ x, (x i - θ i) * g x i
        ∂multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ))) =
      (v : ℝ) * ∫ x, (fderiv ℝ g x (EuclideanSpace.single i 1)) i
        ∂multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) := by
  set P := multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ)) with hPdef
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

/-- GAPS 101.69: existence of the maximum likelihood estimator in a regular minimal natural
exponential family. For the family with base measure `ν` on `E` and statistic the identity,
whose natural parameter space `N` is open and nonempty, the log likelihood
`η ↦ ⟪η, t⟫ - logPartition ν id η` of an observation `t` attains its maximum on `N` if and only
if `t` lies in the interior of the convex hull of the support of `ν`. -/
theorem exists_isMaxOn_logLikelihood_iff_mem_interior_convexHull_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    (hNne : (naturalParameterSpace ν id).Nonempty) (t : E) :
    (∃ η ∈ naturalParameterSpace ν id,
        IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id) η) ↔
      t ∈ interior (convexHull ℝ ν.support) := by
  sorry

/-- GAPS 101.69: in a regular minimal natural exponential family with open natural parameter
space `N`, a maximizer `η ∈ N` of the log likelihood `ζ ↦ ⟪ζ, t⟫ - logPartition ν id ζ` solves the
likelihood equation `∇ logPartition ν id η = t` (the mean of the law at `η` is `t`), and it is the
unique maximizer on `N`. -/
theorem hasFDerivAt_logPartition_and_eq_of_isMaxOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    {t η : E} (hη : η ∈ naturalParameterSpace ν id)
    (hmax : IsMaxOn (fun ζ ↦ inner ℝ ζ t - logPartition ν id ζ) (naturalParameterSpace ν id) η) :
    HasFDerivAt (logPartition ν id) (innerSL ℝ t) η ∧
      ∀ ζ ∈ naturalParameterSpace ν id,
        inner ℝ ζ t - logPartition ν id ζ = inner ℝ η t - logPartition ν id η → ζ = η := by
  sorry


/-- GAPS 101.60: the simultaneous-contrast supremum underlying Scheffé's method: for `v` in a
subspace `S`, `sup_{u ∈ S, u ≠ 0} ⟪u, v⟫² / (s² ‖u‖²) = ‖v‖² / s²` (the supremum is attained at
`u = v`; for `v = 0` it is `0`). The Gaussian pivot of the method is not included. -/
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
