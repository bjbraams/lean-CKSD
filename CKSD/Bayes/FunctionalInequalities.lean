module

public import CKSD.Bayes.LangevinSampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Resolvent
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic

/-!
# Langevin flows, functional inequalities, and the JKO scheme

The law of the overdamped Langevin diffusion `dX = -∇V(X) dt + √2 dW` is represented by a weak
solution of its Fokker–Planck equation (`IsFokkerPlanckSolution` with drift `-∇V` and
infinitesimal covariance `2I`) on every bounded time interval; no stochastic differential equation
is constructed. The Poincaré and logarithmic Sobolev inequalities are TauCeti's. The JKO step is a
point of TauCeti's Moreau–Yosida resolvent on the Wasserstein space `P₂(ℝᵈ)`, for the free energy
built from TauCeti's Boltzmann entropy relative to Lebesgue measure and potential energy.
Sources: GAPS 104.43 and 104.44.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The flow of laws of the overdamped Langevin diffusion: a weak Fokker–Planck solution with
drift `-gradV` and covariance `2I` on `[0, T]` for every `T ≥ 0`. -/
def IsLangevinFlow {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ T ≥ 0, IsFokkerPlanckSolution μ (fun _ x ↦ -gradV x) (fun _ _ ↦ (2 : ℝ) • 1) T

/-- Chi-squared divergence `∫ (dμ/dν - 1)² dν` for `μ ≪ ν`, and `∞` otherwise. -/
def chiSqDiv {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν else ∞

/-- GAPS 104.44: the Poincaré inequality with constant `C` is equivalent to exponential decay at
rate `2/C` of the chi-squared divergence along every Langevin flow. -/
theorem poincareInequality_iff_chiSqDiv_langevin_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C) :
    (gibbsMeasure V).PoincareInequality C ↔
      ∀ μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)), IsLangevinFlow gradV μ → ∀ t ≥ 0,
        chiSqDiv (μ t) (gibbsMeasure V) ≤
          ENNReal.ofReal (Real.exp (-2 * t / C)) * chiSqDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- GAPS 104.44: the logarithmic Sobolev inequality with constant `C` is equivalent to exponential
decay at rate `2/C` of the relative entropy along every Langevin flow. -/
theorem logSobolevInequality_iff_klDiv_langevin_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C) :
    (gibbsMeasure V).LogSobolevInequality C ↔
      ∀ μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)), IsLangevinFlow gradV μ → ∀ t ≥ 0,
        klDiv (μ t) (gibbsMeasure V) ≤
          ENNReal.ofReal (Real.exp (-2 * t / C)) * klDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- GAPS 104.44: under a logarithmic Sobolev inequality, the Otto–Villani inequality gives
`W₂²(μₜ, π) ≤ 2C e^{-2t/C} KL(μ₀‖π)` along every Langevin flow. -/
theorem wasserstein_sq_langevin_le_of_logSobolev {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C)
    (hLS : (gibbsMeasure V).LogSobolevInequality C)
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) (hμ : IsLangevinFlow gradV μ) (t : ℝ)
    (ht : 0 ≤ t) :
    TauCeti.wassersteinEDist 2 (μ t) (gibbsMeasure V) ^ 2 ≤
      ENNReal.ofReal (2 * C * Real.exp (-2 * t / C)) * klDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- GAPS 104.44: a logarithmic Sobolev inequality implies the Poincaré inequality with the same
constant, for every probability measure on `ℝᵈ`. -/
theorem poincareInequality_of_logSobolevInequality {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (C : ℝ)
    (h : μ.LogSobolevInequality C) : μ.PoincareInequality C := by
  sorry

/-- GAPS 104.44: Bakry–Émery and Holley–Stroock. If `V = V₀ + ψ` with `∇²V₀ ⪰ mI`, `m > 0`, and
`a ≤ ψ ≤ b`, then the Gibbs law satisfies the Poincaré and logarithmic Sobolev inequalities with
constant `e^{b-a}/m`. -/
theorem poincare_and_logSobolev_of_bounded_perturbation {d : ℕ}
    (V₀ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m a b : ℝ) (hm : 0 < m)
    (hV₀ : ContDiff ℝ 2 V₀) (hgrad : ∀ x, HasGradientAt V₀ (gradV₀ x) x)
    (hconv : IsStronglyMonotoneGradient gradV₀ m) (hψ : Measurable ψ)
    (hab : ∀ x, ψ x ∈ Icc a b) :
    (gibbsMeasure (V₀ + ψ)).PoincareInequality (Real.exp (b - a) / m) ∧
      (gibbsMeasure (V₀ + ψ)).LogSobolevInequality (Real.exp (b - a) / m) := by
  sorry

/-- The underlying measure of a law in the Wasserstein space `P₂(ℝᵈ)`. -/
def wassersteinLaw {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))

/-- Free energy `∫ ρ log ρ + ∫ V dρ` on the Wasserstein space, with the entropy relative to
Lebesgue measure; it is `⊤` for laws without a density. -/
def jkoFreeEnergy {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) : EReal :=
  TauCeti.boltzmannEntropy volume (wassersteinLaw ν) + TauCeti.potentialEnergy V (wassersteinLaw ν)

/-- Lebesgue density of a law in the Wasserstein space, as a real function. -/
def wassersteinDensity {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((wassersteinLaw ν).rnDeriv volume x).toReal

/-- GAPS 104.43: the Jordan–Kinderlehrer–Otto theorem. Every JKO step for the free energy has a
unique minimizer, and the piecewise-constant interpolations converge, weakly in `L¹` at every time
and strongly in `L¹((0,T) × ℝᵈ)`, to a weak solution of `∂ₜρ = Δρ + ∇·(ρ∇V)` with datum `ρ₀`.
Uniqueness of the limiting weak solution is not part of this statement. -/
theorem jko_scheme_tendsto_fokkerPlanck {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hV : ContDiff ℝ ⊤ V) (hV0 : ∀ x, 0 ≤ V x) (C : ℝ)
    (hgrowth : ∀ x, ‖gradient V x‖ ≤ C * (V x + 1))
    (ρ₀ : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (hF : jkoFreeEnergy V ρ₀ ≠ ⊤) :
    (∀ τ : ℝ≥0, 0 < τ → ∀ μ, ∃! ν, ν ∈ TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ μ) ∧
      ∃ ρ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ T ≥ 0, IsFokkerPlanckSolution
          (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (ρ t x))
          (fun _ x ↦ -gradient V x) (fun _ _ ↦ (2 : ℝ) • 1) T) ∧
        (∀ᵐ x, ρ 0 x = wassersteinDensity ρ₀ x) ∧
        ∀ seq : ℝ≥0 → ℕ → TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)),
          (∀ τ, 0 < τ → seq τ 0 = ρ₀ ∧
            ∀ k, seq τ (k + 1) ∈ TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ (seq τ k)) →
          (∀ t : ℝ, 0 ≤ t → ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g →
            (∃ M, ∀ x, |g x| ≤ M) →
            Tendsto (fun τ : ℝ≥0 ↦ ∫ x, g x ∂wassersteinLaw (seq τ ⌊t / (τ : ℝ)⌋₊))
              (𝓝[>] 0) (𝓝 (∫ x, g x * ρ t x))) ∧
          ∀ T : ℝ, 0 < T → Tendsto (fun τ : ℝ≥0 ↦ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x,
              ENNReal.ofReal |wassersteinDensity (seq τ ⌊t / (τ : ℝ)⌋₊) x - ρ t x|)
            (𝓝[>] 0) (𝓝 0) := by
  sorry

end CKSD
