module

public import CKSD.Learning.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Nearest-neighbour rules and local averaging estimates

A binary classification law is described by the feature law `μ` and the regression function
`η(x) = P(Y = 1 | X = x)`. Labels are realized as `Y = 1{V < η(X)}` with `V` uniform on `[0,1]`
and independent of `X`, so every law of `(X, Y)` arises. Each sample point carries an
independent uniform tie-breaking variable: neighbours are ranked by distance, then by the
tie-breaking variable, then by index (the last step is needed only on a null event).
The `k`-nearest-neighbour rule predicts `1` when more than half of the `k` nearest labels are
`1`. The expected error `𝔼 Lₙ` is the probability that the rule misclassifies an independent
test pair.

Sources: GAPS 107.14 and 107.20.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The uniform law on `[0,1]`. -/
abbrev labelUniform : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- Labelled sample from features, label variables, and tie-breaking variables. -/
def labelledSample {E : Type*} {n : ℕ} (η : E → ℝ) (data : Fin n → E × ℝ × ℝ) :
    Fin n → E × Bool × ℝ :=
  fun i ↦ ((data i).1, decide ((data i).2.1 < η (data i).1), (data i).2.2)

/-- The `k`-nearest-neighbour rule on a labelled sample with tie-breaking variables. -/
def knnRule {E : Type*} [PseudoMetricSpace E] {n : ℕ} (k : ℕ)
    (sample : Fin n → E × Bool × ℝ) (x : E) : Bool :=
  let key := fun i ↦ toLex (dist x (sample i).1, (sample i).2.2)
  let before := fun j i ↦ key j < key i ∨ (key j = key i ∧ j < i)
  let nbrs := Finset.univ.filter fun i ↦ (Finset.univ.filter fun j ↦ before j i).card < k
  decide (k < 2 * (nbrs.filter fun i ↦ (sample i).2.1 = true).card)

/-- Expected error `𝔼 Lₙ` of the `k`-nearest-neighbour rule built from `n` observations. -/
def knnExpectedError {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] (μ : Measure E)
    (η : E → ℝ) (k n : ℕ) : ℝ :=
  ∫ data, ∫ z, (if knnRule k (labelledSample η data) z.1 = decide (z.2 < η z.1) then 0 else 1)
    ∂μ.prod labelUniform ∂Measure.pi fun _ : Fin n ↦ μ.prod (labelUniform.prod labelUniform)

/-- Bayes risk `R* = 𝔼 min(η(X), 1 - η(X))`. -/
def bayesClassificationRisk {E : Type*} [MeasurableSpace E] (μ : Measure E) (η : E → ℝ) : ℝ :=
  ∫ x, min (η x) (1 - η x) ∂μ

/-- Asymptotic `1`-nearest-neighbour risk `L_NN = 𝔼[2η(X)(1 - η(X))]`. -/
def nearestNeighborAsymptoticRisk {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (η : E → ℝ) : ℝ :=
  ∫ x, 2 * η x * (1 - η x) ∂μ

/-- GAPS 107.14 (Cover–Hart): for every distribution on `ℝ^d × {0,1}`, the expected error of the
`1`-nearest-neighbour rule converges to `L_NN = 𝔼[2η(X)(1 - η(X))]`. -/
theorem tendsto_oneNN_expectedError {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η)
    (h01 : ∀ x, η x ∈ Icc 0 1) :
    Tendsto (fun n ↦ knnExpectedError μ η 1 n) atTop
      (𝓝 (nearestNeighborAsymptoticRisk μ η)) := by
  sorry

/-- GAPS 107.14, Cover–Hart inequalities `R* ≤ L_NN ≤ 2R*(1 - R*)`. -/
theorem bayesRisk_le_nnRisk_le {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (η : E → ℝ) (hη : Measurable η) (h01 : ∀ x, η x ∈ Icc 0 1) :
    bayesClassificationRisk μ η ≤ nearestNeighborAsymptoticRisk μ η ∧
      nearestNeighborAsymptoticRisk μ η ≤
        2 * bayesClassificationRisk μ η * (1 - bayesClassificationRisk μ η) := by
  set m : E → ℝ := fun x ↦ min (η x) (1 - η x) with hm_def
  have hmm : Measurable m := hη.min (measurable_const.sub hη)
  have hm0 : ∀ x, 0 ≤ m x := fun x ↦ le_min (h01 x).1 (by linarith [(h01 x).2])
  have hm1 : ∀ x, m x ≤ 1 / 2 := fun x ↦ by
    rcases le_total (η x) (1 - η x) with h | h
    · simp only [hm_def, min_eq_left h]; linarith
    · simp only [hm_def, min_eq_right h]; linarith
  have hkey : ∀ x, 2 * η x * (1 - η x) = 2 * m x * (1 - m x) := fun x ↦ by
    rcases le_total (η x) (1 - η x) with h | h
    · simp only [hm_def, min_eq_left h]
    · simp only [hm_def, min_eq_right h]; ring
  have hbdd : ∀ x, ‖m x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hm0 x)]; linarith [hm1 x]
  have hint : Integrable m μ := Integrable.of_bound hmm.aestronglyMeasurable 1
    (Eventually.of_forall hbdd)
  have hmem : MemLp m 2 μ := MemLp.of_bound hmm.aestronglyMeasurable 1
    (Eventually.of_forall hbdd)
  have hint2 : Integrable (fun x ↦ m x ^ 2) μ := hmem.integrable_sq
  have hNN : nearestNeighborAsymptoticRisk μ η = 2 * (∫ x, m x ∂μ) - 2 * ∫ x, m x ^ 2 ∂μ := by
    unfold nearestNeighborAsymptoticRisk
    simp_rw [hkey]
    have : (fun x ↦ 2 * m x * (1 - m x)) = fun x ↦ 2 * m x - 2 * m x ^ 2 := by
      funext x; ring
    rw [this, integral_sub (hint.const_mul 2) (hint2.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hR : bayesClassificationRisk μ η = ∫ x, m x ∂μ := rfl
  constructor
  · rw [hNN, hR, ← integral_const_mul, ← integral_const_mul, ← integral_sub (hint.const_mul 2)
      (hint2.const_mul 2)]
    refine integral_mono hint ((hint.const_mul 2).sub (hint2.const_mul 2)) fun x ↦ ?_
    nlinarith [hm0 x, hm1 x]
  · have hvar := variance_nonneg m μ
    rw [variance_eq_sub hmem] at hvar
    simp only [Pi.pow_apply] at hvar
    rw [hNN, hR]
    nlinarith [hvar]

/-- GAPS 107.14, fixed odd `k`: the limits `L_kNN` of the expected errors exist, are
nonincreasing over odd `k`, and satisfy `R* ≤ L_kNN ≤ R* + 1/√(k e)`. -/
theorem exists_tendsto_knn_expectedError {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η)
    (h01 : ∀ x, η x ∈ Icc 0 1) :
    ∃ L : ℕ → ℝ, (∀ k, Odd k → Tendsto (fun n ↦ knnExpectedError μ η k n) atTop (𝓝 (L k))) ∧
      (∀ k k', Odd k → Odd k' → k ≤ k' → L k' ≤ L k) ∧
      ∀ k, Odd k → bayesClassificationRisk μ η ≤ L k ∧
        L k ≤ bayesClassificationRisk μ η + 1 / Real.sqrt (k * Real.exp 1) := by
  sorry

/-- GAPS 107.14, universal consistency (Stone): if `kₙ → ∞` and `kₙ / n → 0`, the expected
error of the `kₙ`-nearest-neighbour rule tends to the Bayes risk for every distribution. -/
theorem tendsto_knn_expectedError_bayesRisk {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (η : EuclideanSpace ℝ (Fin d) → ℝ) (hη : Measurable η)
    (h01 : ∀ x, η x ∈ Icc 0 1) (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ knnExpectedError μ η (k n) n) atTop
      (𝓝 (bayesClassificationRisk μ η)) := by
  sorry

/-- GAPS 107.20, Stone's theorem for response-independent local averaging (forests). The
weights `w n i x xs u` are nonnegative, sum to one, and are jointly measurable functions of
the query point `x`, the sample features `xs`, and independent randomness `u ∼ ν`, but not of
the responses. Under the domination, localization, and vanishing-maximum conditions the
estimate `mₙ(x) = ∑ᵢ wₙᵢ(x) Yᵢ` is consistent in `L²(P_X)` for the regression function `m`,
characterized by `∫_{X ∈ s} Y = ∫_s m dP_X`. -/
theorem tendsto_localAveraging_sq_error {d : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure P]
    (hY : Integrable (fun z ↦ z.2 ^ 2) P) (m : EuclideanSpace ℝ (Fin d) → ℝ)
    (hm : Measurable m)
    (hreg : ∀ s, MeasurableSet s → ∫ z in Prod.fst ⁻¹' s, z.2 ∂P = ∫ x in s, m x ∂P.map Prod.fst)
    {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (w : ∀ n : ℕ, Fin n → EuclideanSpace ℝ (Fin d) → (Fin n → EuclideanSpace ℝ (Fin d)) → U → ℝ)
    (hwm : ∀ n i, Measurable fun p : EuclideanSpace ℝ (Fin d) ×
      (Fin n → EuclideanSpace ℝ (Fin d)) × U ↦ w n i p.1 p.2.1 p.2.2)
    (hw0 : ∀ n i x xs u, 0 ≤ w n i x xs u) (hw1 : ∀ n, 0 < n → ∀ x xs u, ∑ i, w n i x xs u = 1)
    (C : ℝ)
    (hdom : ∀ n, ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g → (∀ x, 0 ≤ g x) →
      (∃ B, ∀ x, g x ≤ B) →
      ∫ p, ∑ i, w n i p.1 (fun j ↦ (p.2.1 j).1) p.2.2 * g (p.2.1 i).1
          ∂(P.map Prod.fst).prod ((Measure.pi fun _ : Fin n ↦ P).prod ν) ≤
        C * ∫ x, g x ∂P.map Prod.fst)
    (hloc : ∀ r > (0 : ℝ), Tendsto (fun n ↦
      ∫ p, ∑ i, w n i p.1 (fun j ↦ (p.2.1 j).1) p.2.2 *
          (if r < dist (p.2.1 i).1 p.1 then 1 else 0)
        ∂(P.map Prod.fst).prod ((Measure.pi fun _ : Fin n ↦ P).prod ν)) atTop (𝓝 0))
    (hmax : Tendsto (fun n ↦
      ∫ p, ⨆ i, w n i p.1 (fun j ↦ (p.2.1 j).1) p.2.2
        ∂(P.map Prod.fst).prod ((Measure.pi fun _ : Fin n ↦ P).prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n ↦
      ∫ p, ((∑ i, w n i p.1 (fun j ↦ (p.2.1 j).1) p.2.2 * (p.2.1 i).2) - m p.1) ^ 2
        ∂(P.map Prod.fst).prod ((Measure.pi fun _ : Fin n ↦ P).prod ν)) atTop (𝓝 0) := by
  sorry

end CKSD
