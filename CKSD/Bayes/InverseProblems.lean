module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Linear inverse problems in sequence space

The white-noise model `Y = Af + εW` for a compact injective operator with singular system
`A eⱼ = κⱼ gⱼ` is written in its equivalent sequence form `Yⱼ = κⱼ fⱼ + ε Zⱼ`. Coordinates are
indexed from `0`, the coordinate `j` standing for the index `j + 1` of the singular system.
Squared `ℓ²` distances are taken in `ℝ≥0∞`, so that the risks and the Sobolev ellipsoid are
meaningful for arbitrary sequences. The Gaussian-prior posterior is written in its conjugate
closed form, coordinatewise independent normal. Sources: GAPS 104.20.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Squared `ℓ²` distance between real sequences, possibly infinite. -/
def seqDistSq (f g : ℕ → ℝ) : ℝ≥0∞ := ∑' j, ENNReal.ofReal ((f j - g j) ^ 2)

/-- The Sobolev ellipsoid `S^β(R) = {f : ∑ⱼ j^{2β} fⱼ² ≤ R²}`, with `j` running from `1`. -/
def inverseProblemSobolevBall (β R : ℝ) : Set (ℕ → ℝ) :=
  {f | ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) ^ (2 * β) * f j ^ 2) ≤ ENNReal.ofReal (R ^ 2)}

/-- Law of the observations `Yⱼ = κⱼ fⱼ + ε Zⱼ` with independent standard normal `Zⱼ`. -/
def inverseProblemLaw (κ : ℕ → ℝ) (ε : ℝ) (f : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j ↦ gaussianReal (κ j * f j) (ε ^ 2).toNNReal

/-- Mean squared `ℓ²` risk of an estimator at the truth `f`. -/
def inverseProblemRisk (κ : ℕ → ℝ) (ε : ℝ) (fhat : (ℕ → ℝ) → ℕ → ℝ) (f : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, seqDistSq (fhat y) f ∂inverseProblemLaw κ ε f

/-- Posterior under the prior with independent `fⱼ ∼ N(0, j^{-1-2β})`, in conjugate form:
coordinate `j` is normal with mean `λⱼκⱼYⱼ / (κⱼ²λⱼ + ε²)` and variance `λⱼε² / (κⱼ²λⱼ + ε²)`. -/
def gaussianSeqPosterior (κ : ℕ → ℝ) (β ε : ℝ) (y : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j ↦
    gaussianReal ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * κ j * y j /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2))
      ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * ε ^ 2 /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)).toNNReal

/-- Polynomially decaying singular values: `c₀⁻¹ j^{-a} ≤ κⱼ ≤ c₀ j^{-a}`, `j ≥ 1`. -/
def HasPolynomialSingularValues (κ : ℕ → ℝ) (a c₀ : ℝ) : Prop :=
  ∀ j : ℕ, c₀⁻¹ * ((j : ℝ) + 1) ^ (-a) ≤ κ j ∧ κ j ≤ c₀ * ((j : ℝ) + 1) ^ (-a)

/-- GAPS 104.20: the minimax `ℓ²` rate `ε^r`, `r = 2β/(2β+2a+1)`, over a Sobolev ellipsoid in the
sequence form of a mildly ill-posed linear inverse problem. Estimators are measurable maps of the
whole observation sequence, and the constants depend only on `a`, `β`, `R`, and `c₀`. -/
theorem minimax_rate_inverseProblem (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) (hR : 0 < R)
    (hc₀ : 1 ≤ c₀) :
    let r := 2 * β / (2 * β + 2 * a + 1)
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ κ : ℕ → ℝ, HasPolynomialSingularValues κ a c₀ →
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        (∃ fhat : (ℕ → ℝ) → ℕ → ℝ, Measurable fhat ∧
          ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f ≤
            ENNReal.ofReal ((C * ε ^ r) ^ 2)) ∧
        ∀ fhat : (ℕ → ℝ) → ℕ → ℝ, Measurable fhat →
          ENNReal.ofReal ((c * ε ^ r) ^ 2) ≤
            ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f := by
  sorry

/-- GAPS 104.20: uniform posterior contraction at the minimax rate for the Gaussian prior
`fⱼ ∼ N(0, j^{-1-2β})` matched to the Sobolev smoothness, for every `M_ε → ∞`. -/
theorem tendsto_gaussianSeqPosterior_contraction (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (hR : 0 < R) (hc₀ : 1 ≤ c₀) (κ : ℕ → ℝ) (hκ : HasPolynomialSingularValues κ a c₀)
    (M : ℝ → ℝ) (hM : Tendsto M (𝓝[>] 0) atTop) :
    let r := 2 * β / (2 * β + 2 * a + 1)
    Tendsto (fun ε ↦ ⨆ f₀ ∈ inverseProblemSobolevBall β R,
        ∫⁻ y, gaussianSeqPosterior κ β ε y
          {f | ENNReal.ofReal ((M ε * ε ^ r) ^ 2) ≤ seqDistSq f f₀} ∂inverseProblemLaw κ ε f₀)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

end CKSD
