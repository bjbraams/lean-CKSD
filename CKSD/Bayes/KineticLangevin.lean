module

public import CKSD.Bayes.LangevinSampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CKSD.Inference.Density
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Probability.Distributions.Gaussian.Density


/-!
# Kinetic Langevin dynamics

The kinetic Langevin diffusion `dX = P dt`, `dP = -∇V(X) dt - γP dt + √(2γ) dW` on `ℝᵈ × ℝᵈ` is
represented through its generator and the weak form of its Fokker–Planck equation, as in
`IsFokkerPlanckSolution`. Synchronous coupling is stated pathwise: two copies driven by the same
Brownian motion have differences solving the noiseless integral equations below, because the
additive noise cancels. Partial gradients in position and momentum are gradients of the sections
of a function on `ℝᵈ × ℝᵈ`.

The Gibbs law has a smooth phase-space density. Invariance follows by writing the kinetic
generator in weighted divergence form and using TauCeti
`integral_fderiv_apply_eq_zero_of_hasCompactSupport` for each coordinate. The Gaussian density
is TauCeti's `stdGaussian_eq_withDensity`. The contraction of synchronous coupling combines the
Baillon–Haddad co-coercivity of `∇V - α id`, derived from two-sided quadratic bounds on the
Bregman divergence of `V`, with a Grönwall argument for the twisted norm.

## Main definitions

* `CKSD.kineticGenerator`, `CKSD.kineticGibbsMeasure`: the kinetic Langevin generator and its
  invariant law `π ⊗ N(0, I)` on phase space.
* `CKSD.IsKineticFokkerPlanckSolution`: a weak solution of the kinetic Fokker–Planck equation.
* `CKSD.kineticCouplingNorm`, `CKSD.kineticH1Energy`: the twisted norm and the twisted `H¹`
  energy of hypocoercivity.

## Main results

* `CKSD.integral_kinetic_generator_eq_zero`: invariance of the Gibbs law.
* `CKSD.exists_kinetic_generator_not_symmetric`: the dynamics is not reversible.
* `CKSD.kinetic_coupling_norm_synchronous_le`: contraction of synchronous coupling.
* `CKSD.exists_kinetic_hypocoercive_decay_of_poincare`,
  `CKSD.exists_kinetic_entropic_hypocoercive_decay`: `L²` and entropic hypocoercivity.

Source: GAPS 104.48.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace ContDiff

namespace CKSD

/-- Generator `p·∇ₓf - (∇V(x) + γp)·∇ₚf + γΔₚf` of the kinetic Langevin diffusion. -/
def kineticGenerator {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ : ℝ) (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ f z (z.2, -gradV z.1 - γ • z.2) +
    γ * ∑ i, fderiv ℝ (fderiv ℝ f) z (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1)

/-- The invariant law `π ⊗ N(0, I)` of the kinetic Langevin diffusion. -/
def kineticGibbsMeasure {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  (gibbsMeasure V).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- Weak form of the kinetic Fokker–Planck equation on `[0, ∞)`, tested on smooth compactly
supported functions. -/
def IsKineticFokkerPlanckSolution {d : ℕ}
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (ν : ℝ → Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ t ≥ 0, IsProbabilityMeasure (ν t)) ∧
    ∀ f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      HasCompactSupport f → ∀ t ≥ 0,
        Integrable (kineticGenerator gradV γ f) (ν t) ∧
        IntervalIntegrable (fun s ↦ ∫ z, kineticGenerator gradV γ f z ∂ν s) volume 0 t ∧
        (∫ z, f z ∂ν t) = (∫ z, f z ∂ν 0) +
          ∫ s in (0 : ℝ)..t, ∫ z, kineticGenerator gradV γ f z ∂ν s

/-- Position gradient of a function on phase space. -/
def gradX {d : ℕ} (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  gradient (fun x ↦ f (x, z.2)) z.1

/-- Momentum gradient of a function on phase space. -/
def gradP {d : ℕ} (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  gradient (fun p ↦ f (z.1, p)) z.2

/-- The twisted norm `|||(x,p)|||² = ‖x‖² + ‖x + 2p/γ‖²` of synchronous coupling. -/
def kineticCouplingNorm {d : ℕ} (γ : ℝ) (x p : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + ‖x + (2 / γ) • p‖ ^ 2)

/-- Weighted `H¹(𝛑)` energy `‖f‖² + β⁻¹‖∇ₓf‖² + ‖∇ₚf‖²` for `β > 0`,
possibly infinite. Outside this temperature domain the integrand uses the totalized real inverse
and `ENNReal.ofReal`, without an energy interpretation. -/
def kineticH1Energy {d : ℕ} (β : ℝ)
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (f z ^ 2 + β⁻¹ * ‖gradX f z‖ ^ 2 + ‖gradP f z‖ ^ 2) ∂π

section Invariance

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A smooth density and its logarithmic derivative for the kinetic Gibbs measure. -/
theorem exists_has_density_kinetic_gibbs_measure (V : E → ℝ) (gradV : E → E) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) :
    ∃ ρ : E × E → ℝ,
      HasDensity (kineticGibbsMeasure V) (volume.prod volume) ρ ∧
      ContDiff ℝ 1 ρ ∧
      ∀ z v, fderiv ℝ ρ z v = -(inner ℝ (gradV z.1) v.1 + inner ℝ z.2 v.2) * ρ z := by
  let Z : ℝ := ∫ x, Real.exp (-V x)
  let c : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2)
  let ρ : E × E → ℝ := fun z ↦ (c / Z) * Real.exp (-V z.1 - ‖z.2‖ ^ 2 / 2)
  have hc : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hZ : 0 ≤ Z := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hρ : ContDiff ℝ 2 ρ := by
    dsimp [ρ]
    exact contDiff_const.mul (((hV.contDiff.comp contDiff_fst).neg.sub
      ((contDiff_snd : ContDiff ℝ 2 (fun z : E × E ↦ z.2)).norm_sq (𝕜 := ℝ) |>.div_const 2)).exp)
  refine ⟨ρ, ⟨hρ.continuous.measurable, ae_of_all _ (fun z ↦ ?_), ?_⟩,
    hρ.of_le (by norm_num), ?_⟩
  · exact mul_nonneg (div_nonneg hc hZ) (Real.exp_pos _).le
  · rw [kineticGibbsMeasure, gibbsMeasure, TauCeti.Probability.stdGaussian_eq_withDensity,
      prod_withDensity]
    · congr 1
      funext z
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ)]
      congr 1
      dsimp [ρ, Z, c]
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [Fintype.card_fin, neg_div]
      ring
    · exact (Real.continuous_exp.comp hV.contDiff.continuous.neg |>.div_const _).measurable
        |>.ennreal_ofReal
    · fun_prop
  · intro z v
    have hs : HasFDerivAt (fun z : E × E ↦ z.2) (ContinuousLinearMap.snd ℝ E E) z := hasFDerivAt_snd
    have hD := ((hV.hasGradientAt z.1).hasFDerivAt.comp z hasFDerivAt_fst).neg.sub
      (hs.norm_sq.mul_const (1 / 2))
    have h := hD.exp.const_mul (c / Z)
    dsimp [ρ]
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    simp only [Pi.sub_apply, Pi.neg_apply, Function.comp_apply] at h
    rw [h.fderiv]
    simp only [smul_apply, sub_apply,
      neg_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst,
      ContinuousLinearMap.snd, innerSL_apply_apply, smul_eq_mul]
    dsimp [ρ]
    ring

/-- Weighted divergence form of the kinetic generator has zero integral. -/
theorem integral_mul_kinetic_generator_eq_zero_of_fderiv_density
    (b : E → E) (hb : ContDiff ℝ 1 b) (γ : ℝ)
    (ρ : E × E → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (hρder : ∀ z v, fderiv ℝ ρ z v = -(inner ℝ (b z.1) v.1 + inner ℝ z.2 v.2) * ρ z)
    (f : E × E → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ z, ρ z * kineticGenerator b γ f z ∂(volume.prod volume) = 0 := by
  let ex (i : Fin d) : E × E := (EuclideanSpace.single i 1, 0)
  let ep (i : Fin d) : E × E := (0, EuclideanSpace.single i 1)
  let A (i : Fin d) : E × E → ℝ := fun z ↦ ρ z * z.2 i * f z
  let B (i : Fin d) : E × E → ℝ := fun z ↦ ρ z * b z.1 i * f z
  let C (i : Fin d) : E × E → ℝ := fun z ↦ ρ z * fderiv ℝ f z (ep i)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hA (i : Fin d) : ContDiff ℝ 1 (A i) :=
    (hρ.mul ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.comp
      contDiff_snd)).mul hf1
  have hB (i : Fin d) : ContDiff ℝ 1 (B i) :=
    (hρ.mul ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).contDiff.comp
      (hb.comp contDiff_fst))).mul hf1
  have hC (i : Fin d) : ContDiff ℝ 1 (C i) := by
    exact hρ.mul (hfd.clm_apply contDiff_const)
  have hAc (i : Fin d) : HasCompactSupport (A i) := hfc.mul_left
  have hBc (i : Fin d) : HasCompactSupport (B i) := hfc.mul_left
  have hCc (i : Fin d) : HasCompactSupport (C i) :=
    (hfc.fderiv_apply (𝕜 := ℝ) (ep i)).mul_left
  have hdA (i : Fin d) (z : E × E) : fderiv ℝ (A i) z (ex i) =
      ρ z * (z.2 i * fderiv ℝ f z (ex i) - b z.1 i * z.2 i * f z) := by
    have hcoord : HasFDerivAt (fun z : E × E ↦ z.2 i)
        ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ E E)) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt.comp z
        ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt)
    change fderiv ℝ ((ρ * fun z ↦ z.2 i) * f) z (ex i) = _
    rw [(((hρ.differentiable one_ne_zero z).hasFDerivAt.mul hcoord).mul
        (hf1.differentiable one_ne_zero z).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.snd, smul_eq_mul]
    rw [hρder]
    simp [ex, EuclideanSpace.inner_single_right]
    ring
  have hdB (i : Fin d) (z : E × E) : fderiv ℝ (B i) z (ep i) =
      ρ z * (b z.1 i * fderiv ℝ f z (ep i) - b z.1 i * z.2 i * f z) := by
    have hcoord : HasFDerivAt (fun z : E × E ↦ b z.1 i)
        ((EuclideanSpace.proj i).comp ((fderiv ℝ b z.1).comp
          (ContinuousLinearMap.fst ℝ E E))) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i).hasFDerivAt.comp z
        ((hb.differentiable one_ne_zero z.1).hasFDerivAt.comp z hasFDerivAt_fst)
    change fderiv ℝ ((ρ * fun z ↦ b z.1 i) * f) z (ep i) = _
    rw [(((hρ.differentiable one_ne_zero z).hasFDerivAt.mul hcoord).mul
        (hf1.differentiable one_ne_zero z).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst, smul_eq_mul]
    rw [hρder]
    simp [ep, EuclideanSpace.inner_single_right]
    ring
  have hdC (i : Fin d) (z : E × E) : fderiv ℝ (C i) z (ep i) =
      ρ z * (fderiv ℝ (fderiv ℝ f) z (ep i) (ep i) -
        z.2 i * fderiv ℝ f z (ep i)) := by
    have hd : HasFDerivAt (fun z ↦ fderiv ℝ f z (ep i))
        (((ContinuousLinearMap.apply ℝ ℝ (ep i))).comp
          (fderiv ℝ (fderiv ℝ f) z)) z :=
      ((ContinuousLinearMap.apply ℝ ℝ (ep i))).hasFDerivAt.comp z
        (hfd.differentiable one_ne_zero z).hasFDerivAt
    change fderiv ℝ (ρ * fun z ↦ fderiv ℝ f z (ep i)) z (ep i) = _
    rw [(((hρ.differentiable one_ne_zero z).hasFDerivAt).mul hd).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
    rw [hρder]
    simp [ep, EuclideanSpace.inner_single_right]
    ring
  have hvec (a b : E) : (a, b) = ∑ i, (a i • ex i + b i • ep i) := by
    have he (a : E) : (∑ i, a i • EuclideanSpace.single i 1) = a := by
      ext j
      change (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) j)
        (∑ i, a i • EuclideanSpace.single i 1) = _
      simp [map_sum, PiLp.single_apply]
    apply Prod.ext <;> simp [ex, ep, Prod.fst_sum, Prod.snd_sum, he]
  have hpoint (z : E × E) : ρ z * kineticGenerator b γ f z =
      ∑ i, (fderiv ℝ (A i) z (ex i) - fderiv ℝ (B i) z (ep i) +
        γ * fderiv ℝ (C i) z (ep i)) := by
    simp_rw [hdA, hdB, hdC]
    rw [kineticGenerator, hvec z.2 (-b z.1 - γ • z.2)]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    dsimp [ep]
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    have hAi : Integrable (fun z ↦ fderiv ℝ (A i) z (ex i)) (volume.prod volume) :=
      ((hA i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hAc i).fderiv_apply (𝕜 := ℝ) (ex i))
    have hBi : Integrable (fun z ↦ fderiv ℝ (B i) z (ep i)) (volume.prod volume) :=
      ((hB i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hBc i).fderiv_apply (𝕜 := ℝ) (ep i))
    have hCi : Integrable (fun z ↦ fderiv ℝ (C i) z (ep i)) (volume.prod volume) :=
      ((hC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.integrable_of_hasCompactSupport ((hCc i).fderiv_apply (𝕜 := ℝ) (ep i))
    have hAB : Integrable (fun z ↦ fderiv ℝ (A i) z (ex i) - fderiv ℝ (B i) z (ep i))
        (volume.prod volume) := hAi.sub hBi
    rw [integral_add hAB (hCi.const_mul γ), integral_sub hAi hBi,
      integral_const_mul, TauCeti.integral_fderiv_apply_eq_zero_of_hasCompactSupport (hA i) (hAc i),
      TauCeti.integral_fderiv_apply_eq_zero_of_hasCompactSupport (hB i) (hBc i),
      TauCeti.integral_fderiv_apply_eq_zero_of_hasCompactSupport (hC i) (hCc i)]
    ring
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport
    · exact (((hA i).continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
        (((hB i).continuous_fderiv one_ne_zero).clm_apply continuous_const) |>.add
          (continuous_const.mul (((hC i).continuous_fderiv one_ne_zero).clm_apply continuous_const))
    · exact (((hAc i).fderiv_apply (𝕜 := ℝ) (ex i)).sub
        ((hBc i).fderiv_apply (𝕜 := ℝ) (ep i))).add
          (((hCc i).fderiv_apply (𝕜 := ℝ) (ep i)).mul_left)
end Invariance

/-- GAPS 104.48: invariance of `π ⊗ N(0, I)`, in the weak form `∫ Lf d𝛑 = 0` for smooth compactly
supported `f`. -/
theorem integral_kinetic_generator_eq_zero {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β γ : ℝ)
    (hV : IsSamplingPotential V gradV β)
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∫ z, kineticGenerator gradV γ f z ∂kineticGibbsMeasure V = 0 := by
  obtain ⟨ρ, hden, hρ, hρder⟩ := exists_has_density_kinetic_gibbs_measure V gradV β hV
  have hb : ContDiff ℝ 1 gradV := by
    have heq : gradV = gradient V := funext fun x ↦ (hV.hasGradientAt x).gradient.symm
    rw [heq]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.contDiff.comp
      (hV.contDiff.fderiv_right (by norm_num))
  rw [hden.integral_eq]
  exact integral_mul_kinetic_generator_eq_zero_of_fderiv_density gradV hb γ ρ hρ hρder f
    (hf.of_le (by simp)) hfc

section Irreversibility

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- For a differentiable family of linear forms, `DF(z) w v = D(F(·) v)(z) w`. -/
private theorem fderiv_apply_comm {F : E × E → (E × E →L[ℝ] ℝ)} {z : E × E}
    (hF : DifferentiableAt ℝ F z) (v w : E × E) :
    fderiv ℝ F z w v = fderiv ℝ (fun y ↦ F y v) z w := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

/-- The derivative of a function of position only, `D(c ∘ fst)(y) v = Dc(y₁) v₁`. -/
private theorem fderiv_comp_fst_apply {c : E → ℝ} (hc : Differentiable ℝ c) (y v : E × E) :
    fderiv ℝ (fun z : E × E ↦ c z.1) y v = fderiv ℝ c y.1 v.1 := by
  rw [show (fun z : E × E ↦ c z.1) = c ∘ Prod.fst from rfl,
    ((hc y.1).hasFDerivAt.comp y hasFDerivAt_fst).fderiv]
  rfl

/-- Product rule for the kinetic generator with a factor depending on position only:
`L(f·(c ∘ fst)) = f·(p·∇c) + c·Lf`, since the factor has no momentum derivatives. -/
private theorem kinetic_generator_mul_comp_fst (gradV : E → E) (γ : ℝ) {c : E → ℝ}
    (hc : ContDiff ℝ 2 c) {f : E × E → ℝ} (hf : ContDiff ℝ 2 f) (z : E × E) :
    kineticGenerator gradV γ (fun z ↦ f z * c z.1) z =
      f z * fderiv ℝ c z.1 z.2 + c z.1 * kineticGenerator gradV γ f z := by
  have hc1 : Differentiable ℝ c := hc.differentiable two_ne_zero
  have hg : ContDiff ℝ 2 (fun z : E × E ↦ c z.1) := hc.comp contDiff_fst
  have hf1 : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hg1 : Differentiable ℝ (fun z : E × E ↦ c z.1) := hg.differentiable two_ne_zero
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hD : ∀ y, fderiv ℝ (fun z ↦ f z * c z.1) y =
      f y • fderiv ℝ (fun z : E × E ↦ c z.1) y + c y.1 • fderiv ℝ f y := fun y ↦
    fderiv_fun_mul (hf1 y) (hg1 y)
  have hDD : Differentiable ℝ (fderiv ℝ (fun z ↦ f z * c z.1)) :=
    ((hf.mul hg).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h2 : ∀ i : Fin d, fderiv ℝ (fderiv ℝ (fun z ↦ f z * c z.1)) z
      (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) =
      c z.1 * fderiv ℝ (fderiv ℝ f) z
      (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) := by
    intro i
    set v : E × E := (0, EuclideanSpace.single i 1)
    rw [fderiv_apply_comm (hDD z), fderiv_apply_comm (hDf z)]
    have : (fun y ↦ fderiv ℝ (fun z ↦ f z * c z.1) y v) =
        fun y ↦ c y.1 * fderiv ℝ f y v := by
      funext y
      rw [hD y]
      simp [fderiv_comp_fst_apply hc1, v]
    rw [this, fderiv_fun_mul (hg1 z) ((hDf z).clm_apply (differentiableAt_const v))]
    simp [fderiv_comp_fst_apply hc1, v]
  simp only [kineticGenerator, hD, h2, ← Finset.mul_sum]
  simp [fderiv_comp_fst_apply hc1]
  ring


/-- The kinetic generator is a local operator. -/
private theorem kinetic_generator_congr {gradV : E → E} {γ : ℝ} {f₁ f₂ : E × E → ℝ} {z : E × E}
    (h : f₁ =ᶠ[nhds z] f₂) : kineticGenerator gradV γ f₁ z = kineticGenerator gradV γ f₂ z := by
  simp only [kineticGenerator, h.fderiv_eq, h.fderiv.fderiv_eq]

/-- The kinetic generator of a `C²` function is continuous when `∇V` is continuous. -/
private theorem continuous_kinetic_generator {gradV : E → E} (hb : Continuous gradV) (γ : ℝ)
    {f : E × E → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (kineticGenerator gradV γ f) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hs : Continuous fun z ↦ ∑ i : Fin d, fderiv ℝ (fderiv ℝ f) z
      (0, EuclideanSpace.single i 1) (0, EuclideanSpace.single i 1) :=
    continuous_finsetSum _ fun i _ ↦ (h2.clm_apply continuous_const).clm_apply continuous_const
  exact (h1.clm_apply (by fun_prop)).add (continuous_const.mul hs)

/-- The kinetic Gibbs law charges every nonempty open set: both factors have everywhere positive
densities. -/
private theorem is_open_pos_measure_kinetic_gibbs_measure {V : E → ℝ}
    (hV : Continuous V) (hint : Integrable (fun x ↦ Real.exp (-V x))) :
    (kineticGibbsMeasure V).IsOpenPosMeasure := by
  have hZ : 0 < ∫ x, Real.exp (-V x) :=
    integral_exp_pos hint
  have h1 : (gibbsMeasure V).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun x ↦ ?_)).isOpenPosMeasure
    · exact ((Real.continuous_exp.comp hV.neg).div_const _).measurable.ennreal_ofReal.aemeasurable
    · simpa using div_pos (Real.exp_pos (-V x)) hZ
  have h2 : (stdGaussian E).IsOpenPosMeasure := by
    rw [TauCeti.Probability.stdGaussian_eq_withDensity]
    refine (withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun x ↦ ?_)).isOpenPosMeasure
    · exact (by fun_prop : Measurable fun x : E ↦
        (2 * Real.pi) ^ (-(Fintype.card (Fin d) : ℝ) / 2) *
          Real.exp (-‖x‖ ^ 2 / 2)).ennreal_ofReal.aemeasurable
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  unfold kineticGibbsMeasure
  infer_instance

/-- Non-reversibility of the kinetic generator, with explicit test functions: for a bump `c` in
position, `g ≈ c(x)` and `f = (p·∇c(x)) χ` with a bump `χ`, the product rule and invariance give
`∫ g Lf = -∫ f Lg`, while `∫ f Lg = ∫ (p·∇c)² χ > 0`. -/
private theorem exists_kinetic_generator_not_symmetric_aux (hd : 0 < d) (V : E → ℝ)
    (gradV : E → E) (β γ : ℝ) (hV : IsSamplingPotential V gradV β) :
    ∃ f g : E × E → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∫ z, f z * kineticGenerator gradV γ g z ∂kineticGibbsMeasure V ≠
        ∫ z, g z * kineticGenerator gradV γ f z ∂kineticGibbsMeasure V := by
  have hb : Continuous gradV := by
    have heq : gradV = gradient V := funext fun x ↦ (hV.hasGradientAt x).gradient.symm
    rw [heq]
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hV.contDiff.continuous_fderiv two_ne_zero)
  have := is_probability_measure_gibbs_measure hV.integrable
  have : IsProbabilityMeasure (kineticGibbsMeasure V) := by
    unfold kineticGibbsMeasure
    infer_instance
  have := is_open_pos_measure_kinetic_gibbs_measure hV.contDiff.continuous hV.integrable
  -- the position bump `c` and a point where its derivative does not vanish
  let bc : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set c : E → ℝ := ⇑bc with hc_def
  have hc : ContDiff ℝ ∞ c := bc.contDiff
  have hc2 : ContDiff ℝ 2 c := bc.contDiff
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, fderiv ℝ c x₀ ≠ 0 := by
    by_contra! h
    have h1 := is_const_of_fderiv_eq_zero (hc2.differentiable two_ne_zero) h 0
      (EuclideanSpace.single ⟨0, hd⟩ 3)
    rw [hc_def, bc.one_of_mem_closedBall (by simp [bc]),
      bc.zero_of_le_dist (by simp [bc]; norm_num)] at h1
    exact one_ne_zero h1
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, fderiv ℝ c x₀ p₀ ≠ 0 := by
    by_contra! h
    exact hx₀ (ContinuousLinearMap.ext h)
  -- the phase-space bumps
  let bχ : ContDiffBump ((x₀, p₀) : E × E) := ⟨1, 2, one_pos, one_lt_two⟩
  let bη : ContDiffBump p₀ := ⟨3, 4, by norm_num, by norm_num⟩
  let G : E × E → ℝ := fun z ↦ c z.1
  let f : E × E → ℝ := fun z ↦ fderiv ℝ c z.1 z.2 * bχ z
  let g : E × E → ℝ := fun z ↦ c z.1 * bη z.2
  have hf : ContDiff ℝ ∞ f :=
    (((hc.fderiv_right (m := ∞) le_rfl).comp contDiff_fst).clm_apply contDiff_snd).mul bχ.contDiff
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hfc : HasCompactSupport f := bχ.hasCompactSupport.mul_left
  have hg : ContDiff ℝ ∞ g := (hc.comp contDiff_fst).mul (bη.contDiff.comp contDiff_snd)
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : E) 2).prod
      (isCompact_closedBall p₀ 4)) fun z hz ↦ ?_
    rw [Set.mem_prod, not_and_or, Metric.mem_closedBall, Metric.mem_closedBall] at hz
    rcases hz with hz | hz
    · have : c z.1 = 0 := bc.zero_of_le_dist (show (2 : ℝ) ≤ _ from (not_le.mp hz).le)
      simp only [g, this, zero_mul]
    · have : bη z.2 = 0 := bη.zero_of_le_dist (show (4 : ℝ) ≤ _ from (not_le.mp hz).le)
      simp only [g, this, mul_zero]
  -- `g` agrees with `G` near the support of `f`
  have hU : ∀ z ∈ tsupport f, g =ᶠ[nhds z] G := by
    intro z hz
    have hz' : z ∈ Metric.closedBall ((x₀, p₀) : E × E) 2 := by
      rw [← show bχ.rOut = 2 from rfl, ← bχ.tsupport_eq]
      exact tsupport_mul_subset_right hz
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball ((x₀, p₀) : E × E) 3 from
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz') (by norm_num : (2 : ℝ) < 3))] with y hy
    have hy2 : dist y.2 p₀ ≤ 3 := by
      rw [Metric.mem_ball, Prod.dist_eq] at hy
      exact (le_max_right _ _).trans hy.le
    simp only [g, G, bη.one_of_mem_closedBall (Metric.mem_closedBall.mpr hy2), mul_one]
  have hfz : ∀ z ∉ tsupport f, f =ᶠ[nhds z] 0 := fun z hz ↦
    notMem_tsupport_iff_eventuallyEq.mp hz
  have hLG : ∀ z, kineticGenerator gradV γ G z = fderiv ℝ c z.1 z.2 := by
    intro z
    have := kinetic_generator_mul_comp_fst gradV γ hc2 (contDiff_const (c := (1 : ℝ))) z
    simpa [G, kineticGenerator] using this
  have hfLg : ∀ z, f z * kineticGenerator gradV γ g z = fderiv ℝ c z.1 z.2 ^ 2 * bχ z := by
    intro z
    by_cases hz : z ∈ tsupport f
    · rw [kinetic_generator_congr (hU z hz), hLG]
      simp only [f]
      ring
    · have h0 : f z = 0 := (hfz z hz).eq_of_nhds
      rw [h0, zero_mul]
      simp only [f, mul_eq_zero] at h0
      rcases h0 with h0 | h0 <;> simp [h0]
  have hkey : ∀ z, f z * kineticGenerator gradV γ g z + g z * kineticGenerator gradV γ f z =
      kineticGenerator gradV γ (fun z ↦ f z * c z.1) z := by
    intro z
    by_cases hz : z ∈ tsupport f
    · rw [kinetic_generator_congr (hU z hz), (hU z hz).eq_of_nhds, hLG,
        kinetic_generator_mul_comp_fst gradV γ hc2 hf2]
    · have e := hfz z hz
      have e2 : (fun z ↦ f z * c z.1) =ᶠ[nhds z] 0 := e.mono fun y hy ↦ by simp [hy]
      rw [kinetic_generator_congr e, kinetic_generator_congr e2, e.eq_of_nhds]
      simp [kineticGenerator]
  have hFc : Continuous fun z : E × E ↦ fderiv ℝ c z.1 z.2 ^ 2 * bχ z :=
    ((((hc2.continuous_fderiv two_ne_zero).comp continuous_fst).clm_apply continuous_snd).pow 2).mul
      bχ.continuous
  have hFs : HasCompactSupport fun z : E × E ↦ fderiv ℝ c z.1 z.2 ^ 2 * bχ z :=
    bχ.hasCompactSupport.mul_left
  have hpos : 0 < ∫ z, f z * kineticGenerator gradV γ g z ∂kineticGibbsMeasure V := by
    simp_rw [hfLg]
    refine hFc.integral_pos_of_hasCompactSupport_nonneg_ne_zero hFs
      (fun z ↦ mul_nonneg (sq_nonneg _) (bχ.nonneg' z)) (x := (x₀, p₀)) ?_
    simp [bχ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), hp₀]
  have hint1 : Integrable (fun z ↦ f z * kineticGenerator gradV γ g z) (kineticGibbsMeasure V) := by
    simp_rw [hfLg]
    exact hFc.integrable_of_hasCompactSupport hFs
  have hint2 : Integrable (fun z ↦ g z * kineticGenerator gradV γ f z) (kineticGibbsMeasure V) :=
    (hg.continuous.mul (continuous_kinetic_generator hb γ hf2)).integrable_of_hasCompactSupport
      hgc.mul_right
  have hsum := integral_add hint1 hint2
  simp_rw [hkey] at hsum
  rw [integral_kinetic_generator_eq_zero V gradV β γ hV (fun z ↦ f z * c z.1)
    (hf.mul (hc.comp contDiff_fst)) hfc.mul_right] at hsum
  refine ⟨f, g, hf, hfc, hg, hgc, ?_⟩
  linarith

end Irreversibility

/-- GAPS 104.48: the kinetic Langevin diffusion is not reversible: its generator is not symmetric
in `L²(𝛑)` on smooth compactly supported functions, in every positive dimension. -/
theorem exists_kinetic_generator_not_symmetric {d : ℕ} (hd : 0 < d)
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β γ : ℝ)
    (hV : IsSamplingPotential V gradV β) :
    ∃ f g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∫ z, f z * kineticGenerator gradV γ g z ∂kineticGibbsMeasure V ≠
        ∫ z, g z * kineticGenerator gradV γ f z ∂kineticGibbsMeasure V :=
  exists_kinetic_generator_not_symmetric_aux hd V gradV β γ hV

section Coupling

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Derivative of a potential along the segment `t ↦ x + t • u`. -/
private theorem has_deriv_at_comp_add_smul {V : E → ℝ} {gradV : E → E}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x) (x u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ V (x + s • u)) ⟪gradV (x + t • u), u⟫ t := by
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  have := (hgrad (x + t • u)).hasFDerivAt.comp_hasDerivAt t hl
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

/-- Two-sided quadratic bounds on the Bregman divergence of a potential with a `β`-Lipschitz,
`α`-strongly monotone gradient:
`(α/2)‖y - x‖² ≤ V y - V x - ⟪∇V(x), y - x⟫ ≤ (β/2)‖y - x‖²`. -/
private theorem bregman_bounds {V : E → ℝ} {gradV : E → E} {α β : ℝ}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x)
    (hlip : ∀ x y, ‖gradV x - gradV y‖ ≤ β * ‖x - y‖)
    (hmono : IsStronglyMonotoneGradient gradV α) (x y : E) :
    α / 2 * ‖y - x‖ ^ 2 ≤ V y - V x - ⟪gradV x, y - x⟫ ∧
      V y - V x - ⟪gradV x, y - x⟫ ≤ β / 2 * ‖y - x‖ ^ 2 := by
  set u := y - x with hu
  have hy : x + (1 : ℝ) • u = y := by simp [hu]
  have hx : x + (0 : ℝ) • u = x := by simp
  set φ : ℝ → ℝ := fun t ↦ V (x + t • u) - t * ⟪gradV x, u⟫ with hφ
  have hd (t : ℝ) : HasDerivAt φ (⟪gradV (x + t • u), u⟫ - ⟪gradV x, u⟫) t := by
    have := (has_deriv_at_comp_add_smul hgrad x u t).sub ((hasDerivAt_id t).mul_const ⟪gradV x, u⟫)
    simp only [id, one_mul] at this
    exact this
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun t ↦ (hd t).continuousAt
  constructor
  · set ψ : ℝ → ℝ := fun t ↦ φ t - α / 2 * t ^ 2 * ‖u‖ ^ 2
    have hψ (t : ℝ) : HasDerivAt ψ (⟪gradV (x + t • u), u⟫ - ⟪gradV x, u⟫ - α * t * ‖u‖ ^ 2) t := by
      have := (hd t).sub (((hasDerivAt_pow 2 t).const_mul (α / 2)).mul_const (‖u‖ ^ 2))
      convert this using 1
      simp only [Nat.cast_ofNat]
      ring
    have hmon : MonotoneOn ψ (Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun t _ ↦ (hψ t).continuousAt.continuousWithinAt) (fun t _ ↦ (hψ t).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Ici, mem_Ioi] at ht
      have h := hmono (x + t • u) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht, real_inner_smul_right,
        inner_sub_left] at h
      have : α * t * ‖u‖ ^ 2 ≤ ⟪gradV (x + t • u), u⟫ - ⟪gradV x, u⟫ := by
        refine le_of_mul_le_mul_left ?_ ht
        nlinarith
      linarith
    have h01 := hmon (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_le_one
    simp only [ψ, hφ, hx, hy] at h01
    norm_num at h01
    linarith
  · set ψ : ℝ → ℝ := fun t ↦ φ t - β / 2 * t ^ 2 * ‖u‖ ^ 2
    have hψ (t : ℝ) : HasDerivAt ψ (⟪gradV (x + t • u), u⟫ - ⟪gradV x, u⟫ - β * t * ‖u‖ ^ 2) t := by
      have := (hd t).sub (((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖u‖ ^ 2))
      convert this using 1
      simp only [Nat.cast_ofNat]
      ring
    have hant : AntitoneOn ψ (Ici 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
        (fun t _ ↦ (hψ t).continuousAt.continuousWithinAt) (fun t _ ↦ (hψ t).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Ici, mem_Ioi] at ht
      have h := hlip (x + t • u) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
      have h2 : ⟪gradV (x + t • u), u⟫ - ⟪gradV x, u⟫ ≤ ‖gradV (x + t • u) - gradV x‖ * ‖u‖ := by
        rw [← inner_sub_left]; exact real_inner_le_norm _ _
      have h3 := mul_le_mul_of_nonneg_right h (norm_nonneg u)
      nlinarith
    have h01 := hant (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_le_one
    simp only [ψ, hφ, hx, hy] at h01
    norm_num at h01
    linarith


/-- Baillon–Haddad co-coercivity for the convex part `V - (α/2)‖·‖²` of a potential with a
`β`-Lipschitz, `α`-strongly monotone gradient: with `F z = ∇V(z) - α z` and `L ≥ β - α`, `L > 0`,
`‖F y - F x‖² ≤ L ⟪F y - F x, y - x⟫`. -/
private theorem norm_sq_le_mul_inner_of_bregman {V : E → ℝ} {gradV : E → E} {α β : ℝ}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x)
    (hlip : ∀ x y, ‖gradV x - gradV y‖ ≤ β * ‖x - y‖)
    (hmono : IsStronglyMonotoneGradient gradV α) {L : ℝ} (hL : 0 < L) (hβL : β ≤ L + α)
    (x y : E) :
    ‖(gradV y - α • y) - (gradV x - α • x)‖ ^ 2 ≤
      L * ⟪(gradV y - α • y) - (gradV x - α • x), y - x⟫ := by
  set f : E → ℝ := fun z ↦ V z - α / 2 * ‖z‖ ^ 2 with hf
  set F : E → E := fun z ↦ gradV z - α • z with hF
  have hid (z w : E) : f w - f z - ⟪F z, w - z⟫ =
      (V w - V z - ⟪gradV z, w - z⟫) - α / 2 * ‖w - z‖ ^ 2 := by
    simp only [hf, hF]
    rw [inner_sub_left, real_inner_smul_left, norm_sub_sq_real]
    simp only [inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm z w]
    ring
  have hlow (z w : E) : f z + ⟪F z, w - z⟫ ≤ f w := by
    have := (bregman_bounds hgrad hlip hmono z w).1
    linarith [hid z w]
  have hup (z w : E) : f w ≤ f z + ⟪F z, w - z⟫ + L / 2 * ‖w - z‖ ^ 2 := by
    have := (bregman_bounds hgrad hlip hmono z w).2
    have h2 : β / 2 * ‖w - z‖ ^ 2 ≤ (L + α) / 2 * ‖w - z‖ ^ 2 := by gcongr
    linarith [hid z w]
  set a : E := F y - F x with ha
  set u : E := y - x with hu
  have h1 := hlow x (y - L⁻¹ • a)
  have h2 := hup y (y - L⁻¹ • a)
  have h3 := hlow y (x + L⁻¹ • a)
  have h4 := hup x (x + L⁻¹ • a)
  have e1 : y - L⁻¹ • a - x = u - L⁻¹ • a := by rw [hu]; abel
  have e2 : y - L⁻¹ • a - y = -(L⁻¹ • a) := by abel
  have e3 : x + L⁻¹ • a - y = -u + L⁻¹ • a := by rw [hu]; abel
  have e4 : x + L⁻¹ • a - x = L⁻¹ • a := by abel
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  simp only [inner_sub_right, inner_add_right, inner_neg_right, real_inner_smul_right,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, mul_pow] at h1 h2 h3 h4
  have hFa : ⟪F y, a⟫ - ⟪F x, a⟫ = ‖a‖ ^ 2 := by
    rw [← inner_sub_left, ← ha, real_inner_self_eq_norm_sq]
  have hFu : ⟪F y, u⟫ - ⟪F x, u⟫ = ⟪a, u⟫ := by rw [← inner_sub_left]
  have key : L⁻¹ * ‖a‖ ^ 2 ≤ ⟪a, u⟫ := by
    have hsum := add_le_add (h1.trans h2) (h3.trans h4)
    have : L / 2 * (L⁻¹ ^ 2 * ‖a‖ ^ 2) = L⁻¹ * ‖a‖ ^ 2 / 2 := by field_simp
    have hFa' : L⁻¹ * ⟪F y, a⟫ - L⁻¹ * ⟪F x, a⟫ = L⁻¹ * ‖a‖ ^ 2 := by
      rw [← mul_sub, hFa]
    linarith
  have := mul_le_mul_of_nonneg_left key hL.le
  rwa [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at this


/-- The key estimate of synchronous coupling: for `γ² ≥ 2β`,
`‖γ (y - x) - (2/γ)(∇V(y) - ∇V(x))‖ ≤ (γ - 2α/γ) ‖y - x‖`. -/
private theorem norm_smul_sub_smul_gradV_sub_le {V : E → ℝ} {gradV : E → E} {α β γ : ℝ}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x)
    (hlip : ∀ x y, ‖gradV x - gradV y‖ ≤ β * ‖x - y‖)
    (hmono : IsStronglyMonotoneGradient gradV α) (hα : 0 < α) (hγ : 0 < γ)
    (hγβ : 2 * β ≤ γ ^ 2) (x y : E) :
    ‖γ • (y - x) - (2 / γ) • (gradV y - gradV x)‖ ≤ (γ - 2 * α / γ) * ‖y - x‖ := by
  set u := y - x with hu
  set g := gradV y - gradV x with hg
  have hP : α * ‖u‖ ^ 2 ≤ ⟪g, u⟫ := hmono y x
  have hG : ‖g‖ ≤ β * ‖u‖ := hlip y x
  by_cases hu0 : u = 0
  · have : g = 0 := by
      rw [hu0, norm_zero, mul_zero] at hG
      exact norm_le_zero_iff.1 hG
    simp [hu0, this]
  have hU : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hαβ : α ≤ β := by
    have h1 : ⟪g, u⟫ ≤ ‖g‖ * ‖u‖ := real_inner_le_norm _ _
    have h2 := mul_le_mul_of_nonneg_right hG hU.le
    have : α * ‖u‖ ^ 2 ≤ β * ‖u‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  -- Co-coercivity of `∇V - α id` in the form `‖g - α u‖² ≤ L (⟪g, u⟫ - α ‖u‖²)`.
  obtain ⟨L, hL0, hLγ, hco⟩ : ∃ L : ℝ, 0 ≤ L ∧ L + 2 * α ≤ γ ^ 2 ∧
      ‖g - α • u‖ ^ 2 ≤ L * (⟪g, u⟫ - α * ‖u‖ ^ 2) := by
    rcases hαβ.eq_or_lt with heq | hlt
    · refine ⟨0, le_rfl, by linarith, ?_⟩
      rw [zero_mul, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hα]
      have : ‖g‖ ^ 2 ≤ (β * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
      rw [← heq] at this
      nlinarith
    · refine ⟨2 * (β - α), by linarith, by linarith, ?_⟩
      have h := norm_sq_le_mul_inner_of_bregman hgrad hlip hmono (L := 2 * (β - α))
        (by linarith) (by linarith) x y
      have e : (gradV y - α • y) - (gradV x - α • x) = g - α • u := by
        rw [hg, hu, smul_sub]; abel
      rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
      exact h
  have hc : 0 ≤ γ - 2 * α / γ := by
    rw [sub_nonneg, div_le_iff₀ hγ]
    nlinarith
  rw [← abs_of_nonneg (norm_nonneg _), ← abs_of_nonneg (mul_nonneg hc (norm_nonneg u))]
  refine sq_le_sq.1 ?_
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hγ, abs_of_pos (by positivity : 0 < 2 / γ),
    mul_pow]
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
    at hco
  have hgu : ⟪u, g⟫ = ⟪g, u⟫ := real_inner_comm _ _
  rw [hgu]
  have key : α * (γ ^ 2 - α) * ‖u‖ ^ 2 ≤ γ ^ 2 * ⟪g, u⟫ - ‖g‖ ^ 2 := by
    nlinarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  rw [← sub_nonneg]
  have : ((γ - 2 * α / γ) * ‖u‖) ^ 2 -
      (γ ^ 2 * ‖u‖ ^ 2 - 2 * (γ * (2 / γ * ⟪g, u⟫)) + (2 / γ * ‖g‖) ^ 2) =
      4 / γ ^ 2 * (γ ^ 2 * ⟪g, u⟫ - ‖g‖ ^ 2 - α * (γ ^ 2 - α) * ‖u‖ ^ 2) := by
    field_simp
    ring
  rw [this]
  exact mul_nonneg (by positivity) (by linarith)


/-- Pointwise derivative bound for the squared twisted norm along the noiseless difference
dynamics `u' = w`, `w' = -(g + γ w)`, given `‖γ u - (2/γ) g‖ ≤ c ‖u‖`. -/
private theorem coupling_deriv_le (u w g : E) {γ c : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c)
    (hb : ‖γ • u - (2 / γ) • g‖ ≤ c * ‖u‖) :
    2 * ⟪u, w⟫ + 2 * ⟪u + (2 / γ) • w, w + (2 / γ) • -(g + γ • w)⟫ ≤
      (c - γ) * (‖u‖ ^ 2 + ‖u + (2 / γ) • w‖ ^ 2) := by
  set z := u + (2 / γ) • w with hz
  set v := γ • u - (2 / γ) • g with hv
  have hzv : ⟪z, v⟫ ≤ c / 2 * (‖z‖ ^ 2 + ‖u‖ ^ 2) := by
    have h1 : ⟪z, v⟫ ≤ ‖z‖ * ‖v‖ := real_inner_le_norm _ _
    have h2 := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
    nlinarith [sq_nonneg (‖z‖ - ‖u‖), mul_nonneg hc (sq_nonneg (‖z‖ - ‖u‖))]
  have hid : 2 * ⟪u, w⟫ + 2 * ⟪z, w + (2 / γ) • -(g + γ • w)⟫ =
      -γ * (‖u‖ ^ 2 + ‖z‖ ^ 2) + 2 * ⟪z, v⟫ := by
    have hz2 : ‖z‖ ^ 2 = ‖u‖ ^ 2 + 2 * ((2 / γ) * ⟪u, w⟫) + (2 / γ) ^ 2 * ‖w‖ ^ 2 := by
      rw [hz, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2 / γ), mul_pow]
    rw [hz2, hz, hv]
    simp only [inner_add_left, inner_add_right, inner_sub_right, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm w u, real_inner_comm g w, real_inner_comm g u]
    field_simp
    ring
  rw [hid]
  nlinarith


/-- Exponential decay of the squared twisted norm along the noiseless difference dynamics
`u' = w`, `w' = -(g + γ w)` (in integral form on `[0, ∞)`), given the pointwise estimate
`‖γ u - (2/γ) g‖ ≤ c ‖u‖` with `c ≥ 0`. -/
private theorem twisted_norm_sq_le_of_integral_eq {u w g : ℝ → E} {γ c : ℝ} (hγ : 0 < γ)
    (hc : 0 ≤ c) (huc : Continuous u) (hwc : Continuous w) (hgc : Continuous g)
    (hu : ∀ t ≥ 0, u t = u 0 + ∫ s in (0 : ℝ)..t, w s)
    (hw : ∀ t ≥ 0, w t = w 0 - ∫ s in (0 : ℝ)..t, g s + γ • w s)
    (hb : ∀ t, ‖γ • u t - (2 / γ) • g t‖ ≤ c * ‖u t‖) :
    ∀ t ≥ 0, ‖u t‖ ^ 2 + ‖u t + (2 / γ) • w t‖ ^ 2 ≤
      Real.exp ((c - γ) * t) * (‖u 0‖ ^ 2 + ‖u 0 + (2 / γ) • w 0‖ ^ 2) := by
  have hFc : Continuous fun s ↦ g s + γ • w s := hgc.add (hwc.const_smul γ)
  have hu' (t : ℝ) (ht : 0 < t) : HasDerivAt u (w t) t := by
    have h1 : HasDerivAt (fun s ↦ u 0 + ∫ r in (0 : ℝ)..s, w r) (w t) t :=
      ((hwc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hu s hs.le
  have hw' (t : ℝ) (ht : 0 < t) : HasDerivAt w (-(g t + γ • w t)) t := by
    have h1 : HasDerivAt (fun s ↦ w 0 - ∫ r in (0 : ℝ)..s, g r + γ • w r)
        (-(g t + γ • w t)) t := by
      have := ((hFc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_sub (w 0)
      exact this
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hw s hs.le
  set N2 : ℝ → ℝ := fun t ↦ ‖u t‖ ^ 2 + ‖u t + (2 / γ) • w t‖ ^ 2 with hN2
  have hN2c : Continuous N2 := by
    simp only [hN2]
    fun_prop
  have hN2' (t : ℝ) (ht : 0 < t) : HasDerivAt N2
      (2 * ⟪u t, w t⟫ + 2 * ⟪u t + (2 / γ) • w t, w t + (2 / γ) • -(g t + γ • w t)⟫) t :=
    (hu' t ht).norm_sq.add (((hu' t ht).add ((hw' t ht).const_smul (2 / γ))).norm_sq)
  set Φ : ℝ → ℝ := fun t ↦ Real.exp (-((c - γ) * t)) * N2 t with hΦ
  have hΦc : Continuous Φ := (Real.continuous_exp.comp (by fun_prop)).mul hN2c
  have hΦ' (t : ℝ) (ht : 0 < t) : HasDerivAt Φ (Real.exp (-((c - γ) * t)) * (-(c - γ)) * N2 t +
      Real.exp (-((c - γ) * t)) *
        (2 * ⟪u t, w t⟫ + 2 * ⟪u t + (2 / γ) • w t, w t + (2 / γ) • -(g t + γ • w t)⟫)) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ Real.exp (-((c - γ) * s)))
        (Real.exp (-((c - γ) * t)) * (-(c - γ))) t := by
      have := ((hasDerivAt_id t).const_mul (c - γ)).neg.exp
      simpa using this
    exact h1.mul (hN2' t ht)
  have hanti : AntitoneOn Φ (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hΦc.continuousOn
      (f' := fun t ↦ Real.exp (-((c - γ) * t)) * (-(c - γ)) * N2 t +
        Real.exp (-((c - γ) * t)) *
          (2 * ⟪u t, w t⟫ + 2 * ⟪u t + (2 / γ) • w t, w t + (2 / γ) • -(g t + γ • w t)⟫))
      (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [interior_Ici, mem_Ioi] at ht
      exact (hΦ' t ht).hasDerivWithinAt
    · rw [interior_Ici, mem_Ioi] at ht
      have hd := coupling_deriv_le (u t) (w t) (g t) hγ hc (hb t)
      have he := Real.exp_pos (-((c - γ) * t))
      have : Real.exp (-((c - γ) * t)) * (-(c - γ)) * N2 t +
          Real.exp (-((c - γ) * t)) *
            (2 * ⟪u t, w t⟫ + 2 * ⟪u t + (2 / γ) • w t, w t + (2 / γ) • -(g t + γ • w t)⟫) =
          Real.exp (-((c - γ) * t)) *
            ((2 * ⟪u t, w t⟫ + 2 * ⟪u t + (2 / γ) • w t, w t + (2 / γ) • -(g t + γ • w t)⟫) -
              (c - γ) * N2 t) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos he.le (by simp only [hN2]; linarith)
  intro t ht
  have h := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simp only [hΦ, mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  have hexp : Real.exp ((c - γ) * t) * Real.exp (-((c - γ) * t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc N2 t = Real.exp ((c - γ) * t) * (Real.exp (-((c - γ) * t)) * N2 t) := by
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp ((c - γ) * t) * N2 0 :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end Coupling

/-- GAPS 104.48: contraction of synchronous coupling in the twisted norm at rate `α/γ`, for
`αI ⪯ ∇²V ⪯ βI` and `γ ≥ √(2β)`. The differences of two copies driven by one Brownian motion
solve the noiseless integral equations given as hypotheses. -/
theorem kinetic_coupling_norm_synchronous_le {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β γ : ℝ) (hα : 0 < α)
    (hV : IsSamplingPotential V gradV β) (hmono : IsStronglyMonotoneGradient gradV α)
    (hγ : 0 < γ) (hγβ : Real.sqrt (2 * β) ≤ γ)
    (x p y q : ℝ → EuclideanSpace ℝ (Fin d))
    (hx : Continuous x) (hp : Continuous p) (hy : Continuous y) (hq : Continuous q)
    (hdx : ∀ t ≥ 0, x t - y t = x 0 - y 0 + ∫ s in (0 : ℝ)..t, p s - q s)
    (hdp : ∀ t ≥ 0, p t - q t = p 0 - q 0 -
      ∫ s in (0 : ℝ)..t, (gradV (x s) - gradV (y s)) + γ • (p s - q s)) :
    ∀ t ≥ 0, kineticCouplingNorm γ (x t - y t) (p t - q t) ≤
      Real.exp (-(α * t / γ)) * kineticCouplingNorm γ (x 0 - y 0) (p 0 - q 0) := by
  have hγ2 : 2 * β ≤ γ ^ 2 := by
    by_cases hβ0 : 0 ≤ 2 * β
    · have h := Real.sq_sqrt hβ0
      nlinarith [Real.sqrt_nonneg (2 * β)]
    · nlinarith [sq_nonneg γ]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro t _
    have h0 (v : EuclideanSpace ℝ (Fin 0)) : v = 0 := Subsingleton.elim _ _
    rw [h0 (x t - y t), h0 (p t - q t), h0 (x 0 - y 0), h0 (p 0 - q 0)]
    simp [kineticCouplingNorm]
  have hαβ : α ≤ β := by
    set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1
    have he : ‖e‖ = 1 := by simp [e]
    have h1 := hmono e 0
    have h2 := hV.lipschitz e 0
    have h3 := real_inner_le_norm (gradV e - gradV 0) (e - 0)
    rw [sub_zero, he] at h1 h2 h3
    nlinarith
  have hgc : Continuous gradV := by
    have heq : gradV = gradient V := funext fun z ↦ (hV.hasGradientAt z).gradient.symm
    have hb : ContDiff ℝ 1 gradV := by
      rw [heq]
      exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.contDiff.comp
        (hV.contDiff.fderiv_right (by norm_num))
    exact hb.continuous
  have hc : 0 ≤ γ - 2 * α / γ := by
    rw [sub_nonneg, div_le_iff₀ hγ]
    nlinarith
  have key := twisted_norm_sq_le_of_integral_eq (u := fun t ↦ x t - y t) (w := fun t ↦ p t - q t)
    (g := fun t ↦ gradV (x t) - gradV (y t)) hγ hc (hx.sub hy) (hp.sub hq)
    ((hgc.comp hx).sub (hgc.comp hy)) hdx hdp
    (fun t ↦ norm_smul_sub_smul_gradV_sub_le hV.hasGradientAt hV.lipschitz hmono hα hγ hγ2
      (y t) (x t))
  intro t ht
  have h := key t ht
  have hexp : Real.exp ((γ - 2 * α / γ - γ) * t) = Real.exp (-(α * t / γ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  rw [hexp] at h
  unfold kineticCouplingNorm
  rw [← Real.sqrt_sq (Real.exp_pos _).le, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- GAPS 104.48: `L²` hypocoercivity under a Poincaré inequality with constant `1/α` and
`β`-smoothness, with friction `γ = c₀√β`. The relative density `fₜ = d𝛑ₜ/d𝛑 - 1` is assumed
continuously differentiable; the constants depend only on `c₀`. -/
theorem exists_kinetic_hypocoercive_decay_of_poincare (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → 0 < β → IsSamplingPotential V gradV β →
        (gibbsMeasure V).PoincareInequality (1 / α) →
        ∀ (ν : ℝ → Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
          (f : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ),
          (∀ t ≥ 0, ContDiff ℝ 1 (f t)) → (∀ t ≥ 0, ∀ z, 0 ≤ 1 + f t z) →
          (∀ t ≥ 0, ν t = (kineticGibbsMeasure V).withDensity
            fun z ↦ ENNReal.ofReal (1 + f t z)) →
          IsKineticFokkerPlanckSolution gradV (c₀ * Real.sqrt β) ν →
          ∀ t ≥ 0, kineticH1Energy β (kineticGibbsMeasure V) (f t) ≤
            ENNReal.ofReal (C * Real.exp (-(c * α * t / Real.sqrt β))) *
              kineticH1Energy β (kineticGibbsMeasure V) (f 0) := by
  sorry

/-- GAPS 104.48: entropic hypocoercivity under a logarithmic Sobolev inequality with constant
`1/α`, with friction `γ = c₀√β`. The Lyapunov functional is the relative entropy plus a positive
definite twisted Fisher information of the log-density `hₜ = log(d𝛑ₜ/d𝛑)`, assumed continuously
differentiable. Here the rate constant `c'` may depend on `c₀`. -/
theorem exists_kinetic_entropic_hypocoercive_decay (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ a b c₁ c' : ℝ, 0 < a ∧ 0 < c₁ ∧ b ^ 2 < a * c₁ ∧ 0 < c' ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → 0 < β → IsSamplingPotential V gradV β →
        (gibbsMeasure V).LogSobolevInequality (1 / α) →
        ∀ (ν : ℝ → Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
          (h : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ),
          (∀ t ≥ 0, ContDiff ℝ 1 (h t)) →
          (∀ t ≥ 0, ν t = (kineticGibbsMeasure V).withDensity
            fun z ↦ ENNReal.ofReal (Real.exp (h t z))) →
          IsKineticFokkerPlanckSolution gradV (c₀ * Real.sqrt β) ν →
          let L := fun t : ℝ ↦ klDiv (ν t) (kineticGibbsMeasure V) +
            ∫⁻ z, ENNReal.ofReal (a / β * ‖gradX (h t) z‖ ^ 2 +
              2 * (b / Real.sqrt β) * ⟪gradX (h t) z, gradP (h t) z⟫ +
                c₁ * ‖gradP (h t) z‖ ^ 2) ∂ν t
          ∀ t ≥ 0, L t ≤ ENNReal.ofReal (Real.exp (-(c' * α * t / Real.sqrt β))) * L 0 := by
  sorry

end CKSD
