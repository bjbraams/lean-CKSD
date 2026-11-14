module

public import CKSD.Asymptotics.Statistics
public import Mathlib.Probability.Moments.ComplexMGF


/-!
# Edgeworth and saddlepoint expansions

The Edgeworth expansion for smooth functions of means uses `edgeworthApproximation` with
correction polynomials of the stated degrees and parities, and Cramér's condition on the
characteristic function (`MeasureTheory.charFun`). The saddlepoint approximation uses Mathlib's
cumulant generating function `ProbabilityTheory.cgf`, moment generating function `mgf`, and
complex moment generating function `complexMGF`, together with `saddlepointDensity`.
Sources: GAPS 102.50 and 102.55.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Cramér's condition `limsup_{‖t‖→∞} |E e^{i⟨t,X⟩}| < 1`, in the equivalent form of a uniform
bound by a constant `c < 1` outside a ball. -/
def SatisfiesCramerCondition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) : Prop :=
  ∃ c < 1, ∃ R : ℝ, ∀ t : E, R ≤ ‖t‖ → ‖charFun P t‖ ≤ c

/-- GAPS 102.50: Edgeworth expansion of order `j` for a smooth function of a vector mean.
Here `A` has `j+2` continuous derivatives on a neighbourhood of the mean `m`, `A m = 0`, and
`σ² = ∇A(m)ᵀ Σ ∇A(m)` is written as the variance of the linear statistic `DA(m) X`. Under a
moment of order `j+2` and Cramér's condition, there are polynomials `p_r`, `1 ≤ r ≤ j`, of
degree at most `3r-1` and of parity opposite to `r`, such that the distribution function of
`√n A(X̄)/σ` equals `Φ + Σ_r n^{-r/2} p_r φ` up to `o(n^{-j/2})` uniformly. The identification of
the coefficients of `p_r` through the moments of order at most `r+2` and the derivatives of `A`
is outside this scope. -/
theorem exists_edgeworth_expansion_smooth_function_of_means
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (j : ℕ) (hj : 1 ≤ j) (hmom : Integrable (fun x ↦ ‖x‖ ^ (j + 2)) P)
    (hcramer : SatisfiesCramerCondition P)
    (A : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : ∃ U ∈ 𝓝 (∫ x, x ∂P), ContDiffOn ℝ (j + 2 : ℕ) A U)
    (hA0 : A (∫ x, x ∂P) = 0)
    (hσ : 0 < Var[fun x ↦ fderiv ℝ A (∫ y, y ∂P) x; P]) :
    let σ := Real.sqrt (Var[fun x ↦ fderiv ℝ A (∫ y, y ∂P) x; P]);
    ∃ p : ℕ → Polynomial ℝ,
      (∀ r, 1 ≤ r → r ≤ j → (p r).natDegree ≤ 3 * r - 1 ∧
        ∀ x, (p r).eval (-x) = (-1) ^ (r + 1) * (p r).eval x) ∧
      ∃ e : ℕ → ℝ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((j : ℝ) / 2) * e n) atTop (𝓝 0) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
          |μ.real {ω | Real.sqrt n * A (sampleAverage X n ω) / σ ≤ x} -
            edgeworthApproximation p j n x| ≤ e n := by
  sorry

/-- GAPS 102.55: the saddlepoint approximation to the density of a sample mean. The cumulant
generating function `K = cgf id P` is finite near the origin, `ŝ` lies in the interior of its
domain with `K'(ŝ) = x`, `P` has a density, and the normalized tilted characteristic function
`t ↦ |E e^{(ŝ+it)X}| / E e^{ŝX}` is in `L^ν` for some `ν ≥ 1`. Then for `n > ν` the mean of `n`
observations has a continuous density `fₙ`, bounded when the characteristic function of `X` is
also in `L^ν`, and `fₙ(x) = (n/(2π K''(ŝ)))^{1/2} e^{n(K(ŝ)-ŝx)} (1 + O(1/n))`. -/
theorem saddlepoint_approximation_sample_average_density
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (hac : P ≪ volume)
    (ε : ℝ) (hε : 0 < ε) (hK : ∀ s ∈ Ioo (-ε) ε, Integrable (fun y ↦ Real.exp (s * y)) P)
    (s x : ℝ) (hs : s ∈ interior {s | Integrable (fun y ↦ Real.exp (s * y)) P})
    (hsx : deriv (cgf id P) s = x) (ν : ℝ) (hν : 1 ≤ ν)
    (hint : Integrable fun t : ℝ ↦
      ‖complexMGF id P (s + t * Complex.I) / (mgf id P s : ℂ)‖ ^ ν) :
    ∃ f : ℕ → ℝ → ℝ,
      (∀ n : ℕ, ν < n → Continuous (f n) ∧
        ((Integrable fun t : ℝ ↦ ‖complexMGF id P (t * Complex.I)‖ ^ ν) →
          ∃ C, ∀ y, |f n y| ≤ C) ∧
        μ.map (sampleAverage X n) = volume.withDensity fun y ↦ ENNReal.ofReal (f n y)) ∧
      (fun n : ℕ ↦ f n x / saddlepointDensity (cgf id P) n s x - 1) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  sorry

end CKSD
