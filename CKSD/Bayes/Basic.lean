module

public import CKSD.Inference.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Bayes: definitions

Sources: `GAPS.md`, `SYNOPSIS104.md`, and `STRUCTURE104.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Poisson likelihood as a real nonnegative mass, for a nonnegative intensity. -/
def poissonMass (θ : ℝ) (x : ℕ) : ℝ := Real.exp (-θ) * θ ^ x / Nat.factorial x

/-- Finite-state Metropolis acceptance, with acceptance one for a zero denominator. -/
def metropolisAcceptance {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ)
    (x y : Fin s) : ℝ :=
  if π x * q x y = 0 then 1 else min 1 (π y * q y x / (π x * q x y))

/-- Finite-state Metropolis transition, including rejected proposals on the diagonal. -/
def metropolisTransition {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  fun x y ↦ q x y * metropolisAcceptance π q x y +
    if x = y then 1 - ∑ z, q x z * metropolisAcceptance π q x z else 0

/-- One leapfrog step with identity mass matrix and a specified force. -/
def leapfrogStep {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  let p := z.2 - (h / 2) • g z.1
  let x := z.1 + h • p
  (x, p - (h / 2) • g x)

/-- Posterior of a normal location with known variance, given a proper prior density.
Likelihood factors independent of the parameter cancel in this normalization. -/
def normalPosterior (prior : ℝ → ℝ) (v : ℝ≥0) (n : ℕ) (mean : ℝ) : Measure ℝ :=
  let density := fun theta ↦ prior theta * Real.exp (-(n : ℝ) * (theta - mean) ^ 2 / (2 * v))
  (ENNReal.ofReal (∫ theta, density theta))⁻¹ • volume.withDensity (fun theta ↦ ENNReal.ofReal
    (density theta))


end CKSD
