module

public import CKSD.Processes.Models
public import TauCeti.Analysis.Bochner.BochnerTheorem

/-!
# Spectral random fields and stopped likelihood identities

The random-field construction uses a random frequency and a random uniform phase. The stopped
exponential identity uses an explicitly specified first-exit time of an iid random walk.
Sources: GAPS 106.24 and 106.41, in the scopes of `GAPS_EASY.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Spectral random-phase field for a spectral measure of total real mass `mass`. -/
def spectralRandomField {d : ℕ} (mass : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (ω : EuclideanSpace ℝ (Fin d) × ℝ) : ℂ :=
  (Real.sqrt mass : ℂ) * Complex.exp ((inner ℝ ω.1 x + ω.2) * Complex.I)

/-- GAPS 106.24: a finite spectral measure is realized by a mean-square continuous stationary field.
This concerns the Fourier/random-field assertion, not Matérn differentiability. -/
theorem exists_stationary_field_of_spectral_measure {d : ℕ}
    (F : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure F] :
    ∃ P : Measure (EuclideanSpace ℝ (Fin d) × ℝ), IsProbabilityMeasure P ∧
      (∀ x, MemLp (spectralRandomField (F.real univ) x) 2 P) ∧
      (∀ x, (∫ ω, spectralRandomField (F.real univ) x ω ∂P) = 0) ∧
      (∀ x y, (∫ ω, spectralRandomField (F.real univ) x ω *
        star (spectralRandomField (F.real univ) y ω) ∂P) =
          ∫ w, Complex.exp ((inner ℝ w (x - y) : ℂ) * Complex.I) ∂F) ∧
      ∀ x, Tendsto (fun y ↦ ∫ ω, ‖spectralRandomField (F.real univ) y ω -
        spectralRandomField (F.real univ) x ω‖ ^ 2 ∂P) (𝓝 x) (𝓝 0) := by
  sorry

/-- Partial sums of iid log-likelihood increments. -/
def logLikelihoodPartialSum {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, Z i ω

/-- GAPS 106.41: Wald's fundamental stopped exponential identity at a first exit time.
The finite-valued time `N` is a version of the almost surely finite first exit. -/
theorem integral_stopped_exponential_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (law : Measure ℝ) [IsProbabilityMeasure law]
    (Z : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed P Z law)
    (hpos : 0 < law (Ioi 0)) (hneg : 0 < law (Iio 0))
    (hexp : ∀ t : ℝ, Integrable (fun z ↦ Real.exp (t * z)) law)
    (a b : ℝ) (ha : a < 0) (hb : 0 < b) (N : Ω → ℕ) (hN : Measurable N)
    (hstop : ∀ᵐ ω ∂P,
      (logLikelihoodPartialSum Z (N ω) ω ≤ a ∨ b ≤ logLikelihoodPartialSum Z (N ω) ω) ∧
        ∀ k < N ω, a < logLikelihoodPartialSum Z k ω ∧ logLikelihoodPartialSum Z k ω < b)
    (t : ℝ) (hmgf : 1 ≤ ∫ z, Real.exp (t * z) ∂law) :
    Integrable (fun ω ↦ Real.exp (t * logLikelihoodPartialSum Z (N ω) ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ N ω) P ∧
    (∫ ω, Real.exp (t * logLikelihoodPartialSum Z (N ω) ω) /
      (∫ z, Real.exp (t * z) ∂law) ^ N ω ∂P) = 1 := by
  sorry

end CKSD
