module

public import CKSD.Bayes.Diffusion
public import CKSD.Nonparametric.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Probability.Concentration.PoincareLogSobolev
public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Unadjusted and Metropolis-adjusted Langevin algorithms

Non-asymptotic guarantees for Langevin Monte Carlo targeting a Gibbs law `π ∝ e^{-V}` on `ℝᵈ`.
The unadjusted Langevin algorithm (ULA) `x ↦ x - h ∇V(x) + √(2h) Z` is iterated on laws through
`langevinStepLaw`. The `1/2`-lazy Metropolis-adjusted algorithm (MALA) is given by a
random-mapping representation: from the current state `x`, a uniform variable compared with `1/2`
decides laziness, a standard Gaussian draw gives the Langevin proposal `y`, and a second uniform
variable accepts `y` with probability `malaAcceptance`.

## Conventions

* The Hessian bounds `αI ⪯ ∇²V ⪯ βI` with `α > 0` for a `C²` potential are expressed by strong
  monotonicity of the gradient (`IsStronglyMonotoneGradient`) and `β`-Lipschitz continuity of
  the gradient (`IsSamplingPotential`), which are equivalent to them. The condition number is
  `κ = β / α`.
* The Wasserstein distance is TauCeti's `wassersteinEDist`, relative entropy is Mathlib's
  `klDiv`, and the logarithmic Sobolev inequality is TauCeti's, whose constant `C` corresponds to
  `KL ≤ (C/2) I`; "LSI with constant `1/α`" in the sense of Vempala–Wibisono is
  `LogSobolevInequality (1 / α)`.
* Uniform random variables have TauCeti's law `uniformMeasure 0 1`.

## Main definitions

* `CKSD.IsSamplingPotential`, `CKSD.IsStronglyMonotoneGradient`: smoothness and strong
  convexity hypotheses on the potential.
* `CKSD.ulaLaw`, `CKSD.malaStepLaw`: the law of the ULA iterates and one MALA step on laws.

## Main results

* `CKSD.exists_ula_iteration_complexity`: ULA iteration complexity in `W₂` and in KL under strong
  convexity (GAPS 104.39).
* `CKSD.exists_klDiv_ula_le_of_logSobolev`: the Vempala–Wibisono KL bound for ULA under a
  logarithmic Sobolev inequality, for step sizes `h ≤ α / (4β²)` (GAPS 104.45).
* `CKSD.exists_wasserstein_ula_le_of_stronglyConvex`: geometric `W₂` convergence of ULA up to a
  bias of order `β √(dh) / α` (GAPS 104.45).
* `CKSD.exists_mala_mixing_time_le`, `CKSD.exists_mala_mixing_time_ge`: matching upper and lower
  bounds `κ √d` (up to logarithms) for the mixing time of MALA from a warm start (GAPS 104.47).

## References

* S. Vempala and A. Wibisono, *Rapid convergence of the unadjusted Langevin algorithm: isoperimetry
  suffices*, NeurIPS 2019, Theorem 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Standing sampling hypotheses on a potential: twice continuously differentiable, with gradient
`gradV`, the gradient `β`-Lipschitz, and `e^{-V}` integrable. -/
structure IsSamplingPotential {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ) : Prop where
  /-- The potential is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 V
  /-- `gradV` is the gradient of `V`. -/
  hasGradientAt : ∀ x, HasGradientAt V (gradV x) x
  /-- The gradient is `β`-Lipschitz, that is, `V` is `β`-smooth. -/
  lipschitz : ∀ x y, ‖gradV x - gradV y‖ ≤ β * ‖x - y‖
  /-- The Gibbs density `e^{-V}` is integrable. -/
  integrable : Integrable (fun x ↦ Real.exp (-V x))

/-- Strong monotonicity of the gradient, equivalent to `∇²V ⪰ αI` for a `C²` potential. -/
def IsStronglyMonotoneGradient {d : ℕ}
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α : ℝ) : Prop :=
  ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (gradV x - gradV y) (x - y)

/-- Law of the unadjusted Langevin algorithm after `n` steps of size `h` from the initial law
`μ₀`. -/
def ulaLaw {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (n : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (langevinStepLaw gradV h)^[n] μ₀

/-- One step of the `1/2`-lazy Metropolis-adjusted Langevin algorithm acting on laws: the image
of `μ ⊗ N(0, I) ⊗ U(0,1) ⊗ U(0,1)` under the lazy accept–reject map. -/
def malaStepLaw {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).prod
      (TauCeti.Probability.uniformMeasure 0 1)).prod (TauCeti.Probability.uniformMeasure 0 1)).map
    fun w ↦
      let x := w.1.1.1
      let y := x - h • gradV x + Real.sqrt (2 * h) • w.1.1.2
      if w.2 ≤ 1 / 2 then x else if w.1.2 ≤ malaAcceptance V gradV h x y then y else x

/-- GAPS 104.39: iteration complexity of the unadjusted Langevin algorithm under
`αI ⪯ ∇²V ⪯ βI`, both in `W₂` at the last iterate and in relative entropy for the average of the
laws of iterates `N+1, …, 2N`. The initial law has a finite second moment. -/
theorem exists_ula_iteration_complexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ → MemLp id 2 μ₀ →
        ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt d →
          let h := c * ε ^ 2 / (β * d)
          let W₀ := (TauCeti.wassersteinEDist 2 μ₀ (gibbsMeasure V)).toReal
          ∀ N : ℕ, C * (β / α) * d / ε ^ 2 * Real.log (Real.exp 1 + α * W₀ ^ 2 / ε ^ 2) ≤ N →
            TauCeti.wassersteinEDist 2 (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
                ENNReal.ofReal (ε / Real.sqrt α) ∧
              klDiv ((N : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.Ioc N (2 * N), ulaLaw gradV h μ₀ j)
                  (gibbsMeasure V) ≤ ENNReal.ofReal (ε ^ 2) := by
  sorry

/-- GAPS 104.45: Vempala–Wibisono bound for the unadjusted Langevin algorithm. If the Gibbs law
`π` satisfies a logarithmic Sobolev inequality with constant `1/α` and `V` is `β`-smooth (not
necessarily convex), there is a universal `C` such that for `0 < h ≤ α / (4β²)` and all `N`,
`KL(μ_N ‖ π) ≤ e^{-α N h} KL(μ₀ ‖ π) + C β² d h / α`. -/
theorem exists_klDiv_ula_le_of_logSobolev :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → 0 < β → IsSamplingPotential V gradV β →
        (gibbsMeasure V).LogSobolevInequality (1 / α) →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ →
        ∀ h : ℝ, 0 < h → h ≤ α / (4 * β ^ 2) → ∀ N : ℕ,
          klDiv (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
            ENNReal.ofReal (Real.exp (-(α * N * h))) * klDiv μ₀ (gibbsMeasure V) +
              ENNReal.ofReal (C * β ^ 2 * d * h / α) := by
  sorry

/-- GAPS 104.45: geometric `W₂` convergence of the unadjusted Langevin algorithm under
`αI ⪯ ∇²V ⪯ βI`: there are universal `c, C` such that for `0 < h ≤ c / (βκ)` and all `N`,
`W₂(μ_N, π) ≤ e^{-α N h / 2} W₂(μ₀, π) + C β √(d h) / α`. -/
theorem exists_wasserstein_ula_le_of_stronglyConvex :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ →
        ∀ h : ℝ, 0 < h → h ≤ c / (β * (β / α)) → ∀ N : ℕ,
          TauCeti.wassersteinEDist 2 (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
            ENNReal.ofReal (Real.exp (-(α * N * h / 2))) *
                TauCeti.wassersteinEDist 2 μ₀ (gibbsMeasure V) +
              ENNReal.ofReal (C * β * Real.sqrt (d * h) / α) := by
  sorry

/-- GAPS 104.47: mixing-time upper bound for the `1/2`-lazy Metropolis-adjusted Langevin
algorithm from an `M`-warm start (`μ₀ ≤ Mπ`), with `Λ = log max {κ, d, M/ε, c₂}`. -/
theorem exists_mala_mixing_time_le :
    ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < d → 0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ M : ℝ, ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)),
          IsProbabilityMeasure μ₀ → μ₀ ≤ ENNReal.ofReal M • gibbsMeasure V →
          let κ := β / α
          let Λ := Real.log (max (max κ d) (max (M / ε) c₂))
          let h := c₀ / (β * Real.sqrt d * Λ ^ 2)
          ∃ n : ℕ, (n : ℝ) ≤ c₁ * κ * Real.sqrt d * Λ ^ 3 ∧
            totalVariationDistance ((malaStepLaw V gradV h)^[n] μ₀) (gibbsMeasure V) ≤ ε := by
  sorry

/-- GAPS 104.47: matching lower bound for the `1/2`-lazy Metropolis-adjusted Langevin algorithm:
in high dimension, for every step size some target of condition number `κ` and some `M`-warm
start need `c₃ κ √d (max {log κ, log d})⁻³ log(c₄/ε)` steps. -/
theorem exists_mala_mixing_time_ge :
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ a b : ℝ, 0 < a → 0 < b → ∃ N₀ : ℕ,
      ∀ d : ℕ, N₀ < d → ∀ κ : ℝ, 3 ≤ κ → κ ≤ a * (d : ℝ) ^ b → ∀ M : ℝ, 12 ≤ M →
      ∀ h : ℝ, 0 < h → ∀ ε ∈ Ioo (0 : ℝ) 1,
        ∃ (V : EuclideanSpace ℝ (Fin d) → ℝ)
          (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α : ℝ),
          0 < α ∧ IsSamplingPotential V gradV (κ * α) ∧ IsStronglyMonotoneGradient gradV α ∧
          ∃ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ ∧
            μ₀ ≤ ENNReal.ofReal M • gibbsMeasure V ∧
            ∀ n : ℕ, (n : ℝ) < c₃ * κ * Real.sqrt d *
                (max (Real.log κ) (Real.log d)) ^ (-3 : ℤ) * Real.log (c₄ / ε) →
              ε < totalVariationDistance ((malaStepLaw V gradV h)^[n] μ₀) (gibbsMeasure V) := by
  sorry

end CKSD
