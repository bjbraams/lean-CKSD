module

public import CKSD.Bayes.LangevinSampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Kinetic Langevin dynamics

The kinetic Langevin diffusion `dX = P dt`, `dP = -∇V(X) dt - γP dt + √(2γ) dW` on `ℝᵈ × ℝᵈ` is
represented through its generator and the weak form of its Fokker–Planck equation, as in
`IsFokkerPlanckSolution`. Synchronous coupling is stated pathwise: two copies driven by the same
Brownian motion have differences solving the noiseless integral equations below, because the
additive noise cancels. Partial gradients in position and momentum are gradients of the sections
of a function on `ℝᵈ × ℝᵈ`. Sources: GAPS 104.48.
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

/-- Weighted `H¹(𝛑)` energy `‖f‖² + β⁻¹‖∇ₓf‖² + ‖∇ₚf‖²`, possibly infinite. -/
def kineticH1Energy {d : ℕ} (β : ℝ)
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (f z ^ 2 + β⁻¹ * ‖gradX f z‖ ^ 2 + ‖gradP f z‖ ^ 2) ∂π

/-- GAPS 104.48: invariance of `π ⊗ N(0, I)`, in the weak form `∫ Lf d𝛑 = 0` for smooth compactly
supported `f`. -/
theorem integral_kineticGenerator_eq_zero {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β γ : ℝ)
    (hV : IsSamplingPotential V gradV β)
    (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ ⊤ f)
    (hfc : HasCompactSupport f) :
    ∫ z, kineticGenerator gradV γ f z ∂kineticGibbsMeasure V = 0 := by
  sorry

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
