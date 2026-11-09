module

public import CKSD.Nonparametric.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Convex.Topology

/-!
# Log-concave maximum likelihood

The class `𝓕_d` consists of upper semicontinuous log-concave probability densities on
`ℝ^d`, with log-concavity expressed multiplicatively so that zero values need no extended
logarithm. The log-likelihood functional `∫ log f dP` takes values in `EReal`: it is `⊥` when
`f` is not almost surely positive or `log f` is not `P`-integrable, which for the bounded
densities of `𝓕_d` is exactly the case `∫ log f dP = -∞`. The squared Hellinger distance is
`H²(f, g) = ∫ (√f - √g) ^ 2`, without the factor `1/2`.
Source: GAPS 103.28.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- An upper semicontinuous log-concave probability density on `ℝ^d`. -/
def IsLogConcaveDensity {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ UpperSemicontinuous f ∧
    (∀ x y (t : ℝ), 0 ≤ t → t ≤ 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) ∧
    ∫ x, f x = 1

/-- The log-likelihood functional `∫ log f dP`, with value `⊥` when it equals `-∞`; it is
intended for densities bounded above, such as log-concave densities. -/
def logLikelihoodFunctional {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : EReal :=
  if (∀ᵐ x ∂P, 0 < f x) ∧ Integrable (fun x ↦ Real.log (f x)) P then
    ((∫ x, Real.log (f x) ∂P : ℝ) : EReal) else ⊥

/-- `f` is a log-concave projection of `P`: it maximizes `∫ log f dP` over `𝓕_d`. -/
def IsLogConcaveProjection {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IsLogConcaveDensity f ∧
    ∀ g, IsLogConcaveDensity g → logLikelihoodFunctional P g ≤ logLikelihoodFunctional P f

/-- The tent function with heights `y` at the points `x`: the least concave function on the
convex hull of the points with value at least `y i` at `x i`. -/
def tentFunction {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) (y : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup {r : ℝ | ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • x i = z ∧
    r = ∑ i, w i * y i}

/-- Squared Hellinger distance `∫ (√f - √g) ^ 2` between two densities on `ℝ^d`. -/
def densityHellingerSq {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((Real.sqrt (f z) - Real.sqrt (g z)) ^ 2)

/-- Expected squared Hellinger loss of a density estimator from `n` independent observations
with density `f₀`. -/
def densityHellingerRisk {d : ℕ} (n : ℕ)
    (T : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) → ℝ)
    (f₀ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, densityHellingerSq (T x) f₀
    ∂(Measure.pi fun _ : Fin n ↦ volume.withDensity fun z ↦ ENNReal.ofReal (f₀ z))

/-- The log-concave rate: `n ^ (-4/5)` for `d = 1` and `n ^ (-2/(d+1)) log n` for `d ≥ 2`. -/
def logConcaveUpperRate (d n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ (-4 / 5 : ℝ) else (n : ℝ) ^ (-2 / (d + 1 : ℝ)) * Real.log n

/-- The log-concave minimax lower rate: `n ^ (-4/5)` for `d = 1` and `n ^ (-2/(d+1))` for
`d ≥ 2`. -/
def logConcaveLowerRate (d n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ (-4 / 5 : ℝ) else (n : ℝ) ^ (-2 / (d + 1 : ℝ))

/-- GAPS 103.28: existence and uniqueness of the log-concave projection, with its positivity
set between the interior of the convex support of `P` and that support. The convex support is
the closed convex hull of the support of `P`. -/
theorem existsUnique_isLogConcaveProjection {d : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP1 : Integrable (fun x ↦ ‖x‖) P)
    (hhyp : ∀ (a : EuclideanSpace ℝ (Fin d)) (b : ℝ), a ≠ 0 →
      P {x | inner ℝ a x = b} < 1) :
    ∃ f, (IsLogConcaveProjection P f ∧ ⊥ < logLikelihoodFunctional P f) ∧
      (∀ g, IsLogConcaveProjection P g → g = f) ∧
      interior (closedConvexHull ℝ P.support) ⊆ {x | 0 < f x} ∧
      {x | 0 < f x} ⊆ closedConvexHull ℝ P.support := by
  sorry

/-- GAPS 103.28: the log-concave maximum likelihood estimator of affinely spanning data is
unique, vanishes outside the convex hull `C_n` of the data, and its logarithm is a tent
function on `C_n`. Affine spanning of `ℝ^d` forces `n ≥ d + 1`. -/
theorem existsUnique_logConcaveMLE_tent {d n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (hspan : affineSpan ℝ (range x) = ⊤) :
    ∃ f, IsLogConcaveProjection (empiricalMeasure n x) f ∧
      (∀ g, IsLogConcaveProjection (empiricalMeasure n x) g → g = f) ∧
      (∀ z ∉ convexHull ℝ (range x), f z = 0) ∧
      ∃ y : Fin n → ℝ, ∀ z ∈ convexHull ℝ (range x), f z = Real.exp (tentFunction x y z) := by
  sorry

/-- GAPS 103.28: the worst-case squared Hellinger risk of the log-concave maximum likelihood
estimator. The estimator `T` is required to be the maximum likelihood estimator on affinely
spanning samples, which have probability one; the constant depends only on `d`. -/
theorem logConcaveMLE_hellingerRisk_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, d + 1 ≤ n →
      ∀ T : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x, affineSpan ℝ (range x) = ⊤ → IsLogConcaveProjection (empiricalMeasure n x) (T x)) →
      ∀ f₀, IsLogConcaveDensity f₀ →
        densityHellingerRisk n T f₀ ≤ ENNReal.ofReal (C * logConcaveUpperRate d n) := by
  sorry

/-- GAPS 103.28: the minimax lower bound for log-concave density estimation in squared
Hellinger distance, with a constant `c_d` depending only on the dimension (Kim and Samworth,
2016, Theorem 1). Estimators are jointly measurable functions of the sample and the evaluation
point. -/
theorem logConcave_minimax_hellingerRisk_lower_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, d + 1 ≤ n →
      ∀ T : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) → ℝ,
      Measurable (fun q : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ↦
        T q.1 q.2) →
      ENNReal.ofReal (c * logConcaveLowerRate d n) ≤
        ⨆ f₀ : {f₀ // IsLogConcaveDensity f₀}, densityHellingerRisk n T f₀.val := by
  sorry

end CKSD
