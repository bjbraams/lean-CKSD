module

public import CKSD.Bayes.LangevinSampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CKSD.Inference.Density
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
is TauCeti's `stdGaussian_eq_withDensity`.

## Main definitions

* `CKSD.kineticGenerator`, `CKSD.kineticGibbsMeasure`: the kinetic Langevin generator and its
  invariant law `π ⊗ N(0, I)` on phase space.
* `CKSD.IsKineticFokkerPlanckSolution`: a weak solution of the kinetic Fokker–Planck equation.
* `CKSD.kineticCouplingNorm`, `CKSD.kineticH1Energy`: the twisted norm and the twisted `H¹`
  energy of hypocoercivity.

## Main results

* `CKSD.integral_kineticGenerator_eq_zero`: invariance of the Gibbs law.
* `CKSD.exists_kineticGenerator_not_symmetric`: the dynamics is not reversible.
* `CKSD.kineticCouplingNorm_synchronous_le`: contraction of synchronous coupling.
* `CKSD.exists_kinetic_hypocoercive_decay_of_poincare`,
  `CKSD.exists_kinetic_entropic_hypocoercive_decay`: `L²` and entropic hypocoercivity.

Source: GAPS 104.48.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace

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
    ∀ f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ⊤ f →
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
theorem exists_hasDensity_kineticGibbsMeasure (V : E → ℝ) (gradV : E → E) (β : ℝ)
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
theorem integral_mul_kineticGenerator_eq_zero_of_fderiv_density
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
theorem integral_kineticGenerator_eq_zero {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β γ : ℝ)
    (hV : IsSamplingPotential V gradV β)
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ ⊤ f)
    (hfc : HasCompactSupport f) :
    ∫ z, kineticGenerator gradV γ f z ∂kineticGibbsMeasure V = 0 := by
  obtain ⟨ρ, hden, hρ, hρder⟩ := exists_hasDensity_kineticGibbsMeasure V gradV β hV
  have hb : ContDiff ℝ 1 gradV := by
    have heq : gradV = gradient V := funext fun x ↦ (hV.hasGradientAt x).gradient.symm
    rw [heq]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.contDiff.comp
      (hV.contDiff.fderiv_right (by norm_num))
  rw [hden.integral_eq]
  exact integral_mul_kineticGenerator_eq_zero_of_fderiv_density gradV hb γ ρ hρ hρder f
    (hf.of_le (by simp)) hfc

/-- GAPS 104.48: the kinetic Langevin diffusion is not reversible: its generator is not symmetric
in `L²(𝛑)` on smooth compactly supported functions, in every positive dimension. -/
theorem exists_kineticGenerator_not_symmetric {d : ℕ} (hd : 0 < d)
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β γ : ℝ)
    (hV : IsSamplingPotential V gradV β) :
    ∃ f g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ⊤ f ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ g ∧ HasCompactSupport g ∧
      ∫ z, f z * kineticGenerator gradV γ g z ∂kineticGibbsMeasure V ≠
        ∫ z, g z * kineticGenerator gradV γ f z ∂kineticGibbsMeasure V := by
  sorry

/-- GAPS 104.48: contraction of synchronous coupling in the twisted norm at rate `α/γ`, for
`αI ⪯ ∇²V ⪯ βI` and `γ ≥ √(2β)`. The differences of two copies driven by one Brownian motion
solve the noiseless integral equations given as hypotheses. -/
theorem kineticCouplingNorm_synchronous_le {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
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
  sorry

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
