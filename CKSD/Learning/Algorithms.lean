module

public import CKSD.Processes.Models
public import TauCeti.Probability.Distributions.Laplace.Basic

/-!
# Learning objectives, boosting, and private threshold queries

Basic objects of empirical risk minimization, margin-based classification and boosting, simple
neural predictors, `k`-means, and the AboveThreshold mechanism.

## Main definitions

* `CKSD.empiricalRisk`, `CKSD.IsEmpiricalRiskMinimizer`: empirical risk on a finite sample.
* `CKSD.marginLoss`, `CKSD.exponentialLoss`: ramp and exponential margin losses.
* `CKSD.boostingScore`, `CKSD.boostingWeight`, `CKSD.boostingWeightedError`,
  `CKSD.boostingNormalizer`: AdaBoost.
* `CKSD.relu`, `CKSD.twoLayerPredictor`: one-hidden-layer predictors.
* `CKSD.kmeansRisk`: the population `k`-means distortion.
* `CKSD.HasQuerySensitivity`, `CKSD.aboveThresholdTime`: the AboveThreshold mechanism.

## Main results

* `CKSD.training_error_le_exponential_loss`: the exponential loss dominates the training error
  (GAPS 107.24).
* `CKSD.prod_boostingNormalizer`, `CKSD.boostingNormalizer_eq`,
  `CKSD.boosting_training_error_le`: the AdaBoost training-error bound
  `∏ₜ 2 √(εₜ (1 - εₜ)) ≤ exp (-2 ∑ₜ (½ - εₜ)²)` (GAPS 107.24).
* `CKSD.sub_le_of_threshold_add_le_add`, `CKSD.le_add_of_add_lt_threshold_add`: the
  deterministic accuracy step of AboveThreshold on the bounded-noise event.
* `CKSD.measureReal_lt_abs_le_of_hasLaw_laplaceMeasure`: the two-sided Laplace tail.
* `CKSD.one_sub_le_measureReal_aboveThreshold_accurate`: the accuracy of AboveThreshold
  (GAPS 107.74); its privacy is not formalized.

Sources: Sections 107A–107D of `GAPS.md`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical risk on a finite sample. -/
def empiricalRisk {H X : Type*} {n : ℕ} (loss : H → X → ℝ) (h : H) (x : Fin n → X) : ℝ :=
  (∑ i, loss h (x i)) / n

/-- The defining formula of `CKSD.empiricalRisk`. -/
theorem empiricalRisk_def {H X : Type*} {n : ℕ} (loss : H → X → ℝ) (h : H) (x : Fin n → X) :
    empiricalRisk loss h x = (∑ i, loss h (x i)) / n := by
  rw [empiricalRisk]

/-- An empirical risk minimizer; existence is a separate assertion. -/
@[expose] def IsEmpiricalRiskMinimizer {H X : Type*} {n : ℕ}
    (loss : H → X → ℝ) (x : Fin n → X) (h : H) : Prop :=
  ∀ g, empiricalRisk loss h x ≤ empiricalRisk loss g x

/-- Ramp margin loss at a positive margin scale. -/
def marginLoss (ρ margin : ℝ) : ℝ := min 1 (max 0 (1 - margin / ρ))

/-- The defining formula of `CKSD.marginLoss`. -/
theorem marginLoss_def (ρ margin : ℝ) :
    marginLoss ρ margin = min 1 (max 0 (1 - margin / ρ)) := by
  rw [marginLoss]

/-- Exponential loss of a signed binary margin. -/
def exponentialLoss (margin : ℝ) : ℝ := Real.exp (-margin)

/-- The defining formula of `CKSD.exponentialLoss`. -/
theorem exponentialLoss_def (margin : ℝ) :
    exponentialLoss margin = Real.exp (-margin) := by
  rw [exponentialLoss]

/-- AdaBoost's accumulated score from a sequence of weak binary predictors. -/
def boostingScore {X : Type*} (h : ℕ → X → ℝ) (α : ℕ → ℝ) (T : ℕ) (x : X) : ℝ :=
  ∑ t ∈ Finset.range T, α t * h t x

/-- The defining formula of `CKSD.boostingScore`. -/
theorem boostingScore_def {X : Type*} (h : ℕ → X → ℝ) (α : ℕ → ℝ) (T : ℕ) (x : X) :
    boostingScore h α T x = ∑ t ∈ Finset.range T, α t * h t x := by
  rw [boostingScore]

/-- AdaBoost's normalized observation weights before round `t`. -/
def boostingWeight {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) (i : Fin n) : ℝ :=
  Real.exp (-y i * boostingScore h α t (x i)) /
    ∑ j, Real.exp (-y j * boostingScore h α t (x j))

/-- The defining formula of `CKSD.boostingWeight`. -/
theorem boostingWeight_def {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) (i : Fin n) :
    boostingWeight x y h α t i =
      Real.exp (-y i * boostingScore h α t (x i)) /
        ∑ j, Real.exp (-y j * boostingScore h α t (x j)) := by
  rw [boostingWeight]

/-- Weighted misclassification error of a weak predictor. -/
def boostingWeightedError {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i, if h t (x i) ≠ y i then boostingWeight x y h α t i else 0

/-- The defining formula of `CKSD.boostingWeightedError`. -/
theorem boostingWeightedError_def {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) :
    boostingWeightedError x y h α t =
      ∑ i, if h t (x i) ≠ y i then boostingWeight x y h α t i else 0 := by
  rw [boostingWeightedError]

/-- AdaBoost's normalizer `Zₜ = ∑ᵢ Dₜ(i) exp(-αₜ yᵢ hₜ(xᵢ))` in round `t`. -/
def boostingNormalizer {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i, boostingWeight x y h α t i * Real.exp (-(α t * y i * h t (x i)))

/-- The defining formula of `CKSD.boostingNormalizer`. -/
theorem boostingNormalizer_def {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) :
    boostingNormalizer x y h α t =
      ∑ i, boostingWeight x y h α t i * Real.exp (-(α t * y i * h t (x i))) := by
  rw [boostingNormalizer]

/-- Scalar ReLU activation `x ↦ max 0 x` (the scalar form of TauCeti's vector-valued
`reluActivation`). -/
def relu (x : ℝ) : ℝ := max 0 x

/-- The defining formula of `CKSD.relu`. -/
theorem relu_def (x : ℝ) :
    relu x = max 0 x := by
  rw [relu]

/-- A one-hidden-layer real predictor `x ↦ ∑ⱼ aⱼ σ(⟪wⱼ, x⟫ + bⱼ)` with `N` hidden units on a
real inner product space. -/
def twoLayerPredictor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (σ : ℝ → ℝ) (a : Fin N → ℝ) (w : Fin N → E) (b : Fin N → ℝ) (x : E) : ℝ :=
  ∑ j, a j * σ (inner ℝ (w j) x + b j)

/-- The defining formula of `CKSD.twoLayerPredictor`. -/
theorem twoLayerPredictor_def {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (σ : ℝ → ℝ) (a : Fin N → ℝ) (w : Fin N → E) (b : Fin N → ℝ) (x : E) :
    twoLayerPredictor σ a w b x = ∑ j, a j * σ (inner ℝ (w j) x + b j) := by
  rw [twoLayerPredictor]

/-- Population `k`-means distortion `∫ minⱼ d(x, cⱼ)² dP` for an ordered list of `k` centers.
The minimum is the real `sInf` of a finite set; for `k = 0` it is `sInf ∅ = 0`. -/
def kmeansRisk {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {k : ℕ}
    (P : Measure X) (centers : Fin k → X) : ℝ :=
  ∫ x, sInf (range fun j ↦ dist x (centers j) ^ 2) ∂P

/-- The defining formula of `CKSD.kmeansRisk`. -/
theorem kmeansRisk_def {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {k : ℕ}
    (P : Measure X) (centers : Fin k → X) :
    kmeansRisk P centers = ∫ x, sInf (range fun j ↦ dist x (centers j) ^ 2) ∂P := by
  rw [kmeansRisk]

/-- A query has sensitivity at most `c` for the supplied neighboring-data relation. -/
@[expose] def HasQuerySensitivity {D : Type*} (R : D → D → Prop) (c : ℝ) (f : D → ℝ) : Prop :=
  ∀ d d', R d d' → |f d - f d'| ≤ c

/-- AboveThreshold's first crossing, for fixed threshold noise and a noise stream. -/
def aboveThresholdTime {D : Type*} (query : ℕ → D → ℝ) (T z : ℝ)
    (noise : ℕ → ℝ) (d : D) : ℕ∞ :=
  thresholdHittingTime (fun n (_ : Unit) ↦ query n d + noise n) (T + z) ()

/-- The defining formula of `CKSD.aboveThresholdTime`. -/
theorem aboveThresholdTime_def {D : Type*} (query : ℕ → D → ℝ) (T z : ℝ)
    (noise : ℕ → ℝ) (d : D) :
    aboveThresholdTime query T z noise d =
      thresholdHittingTime (fun n (_ : Unit) ↦ query n d + noise n) (T + z) () := by
  rw [aboveThresholdTime]

/-- GAPS 107.24, exponential loss dominates empirical training error, including zero margins. -/
theorem training_error_le_exponential_loss {n : ℕ} (margin : Fin n → ℝ) :
    (((Finset.univ.filter fun i ↦ margin i ≤ 0).card : ℝ) / n) ≤
      (∑ i, exponentialLoss (margin i)) / n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ((Finset.univ.filter fun i ↦ margin i ≤ 0).card : ℝ) =
        ∑ i, if margin i ≤ 0 then (1 : ℝ) else 0 := by simp
    _ ≤ ∑ i, exponentialLoss (margin i) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · exact (Real.one_le_exp_iff).mpr (neg_nonneg.mpr h)
      · exact (Real.exp_pos _).le

/-- GAPS 107.74, deterministic accuracy on the simultaneous bounded-noise event, crossing case:
if the threshold noise `z` and the query noise are at most `α / 2` in absolute value, a noisy
query value at or above the noisy threshold `T + z` has true value at least `T - α`. -/
theorem sub_le_of_threshold_add_le_add {value T z noise α : ℝ}
    (hz : |z| ≤ α / 2) (hnoise : |noise| ≤ α / 2) (h : T + z ≤ value + noise) :
    T - α ≤ value := by
  linarith [abs_le.mp hz, abs_le.mp hnoise]

/-- GAPS 107.74, deterministic accuracy on the simultaneous bounded-noise event, non-crossing
case: if the threshold noise `z` and the query noise are at most `α / 2` in absolute value, a
noisy query value below the noisy threshold `T + z` has true value at most `T + α`. -/
theorem le_add_of_add_lt_threshold_add {value T z noise α : ℝ}
    (hz : |z| ≤ α / 2) (hnoise : |noise| ≤ α / 2) (h : value + noise < T + z) :
    value ≤ T + α := by
  linarith [abs_le.mp hz, abs_le.mp hnoise]

/-- Two-sided tail of a centered Laplace law: if `ν` has law `Lap(0, b)` and `t ≥ 0`, then
`P(|ν| > t) ≤ e^{-t/b}` (with equality, since the law has no atoms). -/
theorem measureReal_lt_abs_le_of_hasLaw_laplaceMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ν : Ω → ℝ} {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (hν : HasLaw ν (TauCeti.Probability.laplaceMeasure 0 b) P) :
    P.real {ω | t < |ν ω|} ≤ Real.exp (-t / b) := by
  have := TauCeti.Probability.isProbabilityMeasure_laplaceMeasure hb 0
  rw [hν.measureReal_eq (p := fun x ↦ t < |x|) (measurableSet_lt measurable_const
    continuous_abs.measurable)]
  have hsub : {x : ℝ | t < |x|} ⊆ Ioi t ∪ Iic (-t) := fun x (hx : t < |x|) ↦ by
    rcases lt_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [mem_Iic]; linarith)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  rw [TauCeti.Probability.measureReal_Ioi_laplaceMeasure hb ht,
    TauCeti.Probability.measureReal_Iic_laplaceMeasure_of_le hb (by linarith)]
  rw [sub_zero, sub_zero, neg_div]
  linarith

/-- GAPS 107.74, accuracy of AboveThreshold. Let the threshold noise `Z` have law
`Lap(0, 2/ε)` and the query noises `ν i` have law `Lap(0, 4/ε)`, let `0 < β ≤ 1`, `k ≥ 1`, and
`α = 8 (log k + log (2/β)) / ε`. If among the first `k` queries `0, …, k - 1` only the last can
have value at least `T - α`, then with probability at least `1 - β` the mechanism does not halt
before query `k - 1`, every query `i < k` reported "above" (`T + Z ≤ fᵢ(d) + νᵢ`) has
`fᵢ(d) ≥ T - α`, and every query `i < k` reported "below" has `fᵢ(d) ≤ T + α`.

The queries are fixed functions of the data: before the mechanism halts every report is
"below", so adaptively chosen queries are determined by the data along the run. Only the
marginal laws of the noises enter (by a union bound), not their independence. The privacy of
AboveThreshold is not formalized here. -/
theorem one_sub_le_measureReal_aboveThreshold_accurate {Ω D : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ε β α : ℝ} (hε : 0 < ε) (hβ : 0 < β)
    (hβ1 : β ≤ 1) {k : ℕ} (hk : 0 < k) (hα : α = 8 * (Real.log k + Real.log (2 / β)) / ε)
    (query : ℕ → D → ℝ) (d : D) (T : ℝ) (Z : Ω → ℝ) (ν : ℕ → Ω → ℝ)
    (hZ : HasLaw Z (TauCeti.Probability.laplaceMeasure 0 (2 / ε)) P)
    (hν : ∀ i, HasLaw (ν i) (TauCeti.Probability.laplaceMeasure 0 (4 / ε)) P)
    (hlow : ∀ i < k - 1, query i d < T - α) :
    1 - β ≤ P.real {ω | ((k - 1 : ℕ) : ℕ∞) ≤ aboveThresholdTime query T (Z ω) (fun i ↦ ν i ω) d ∧
      (∀ i < k, T + Z ω ≤ query i d + ν i ω → T - α ≤ query i d) ∧
      (∀ i < k, query i d + ν i ω < T + Z ω → query i d ≤ T + α)} := by
  set L := Real.log k + Real.log (2 / β) with hL
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hlogβ : 0 ≤ Real.log (2 / β) :=
    Real.log_nonneg (by rw [le_div_iff₀ hβ]; linarith)
  have hL0 : 0 ≤ L := by linarith
  have hα2 : 0 ≤ α / 2 := by rw [hα]; positivity
  have hexpL : Real.exp (-L) = β / (2 * k) := by
    rw [hL, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    field_simp
  -- the good event and its probability
  set G : Set Ω := {ω | |Z ω| ≤ α / 2 ∧ ∀ i < k, |ν i ω| ≤ α / 2} with hG
  have hbad : Gᶜ ⊆ {ω | α / 2 < |Z ω|} ∪ ⋃ i ∈ Finset.range k, {ω | α / 2 < |ν i ω|} := by
    intro ω hω
    simp only [hG, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le, not_forall, exists_prop]
      at hω
    rcases hω with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr (mem_biUnion (Finset.mem_range.mpr hi) h)
  have hZbad : P.real {ω | α / 2 < |Z ω|} ≤ β / (2 * k) := by
    refine (measureReal_lt_abs_le_of_hasLaw_laplaceMeasure (by positivity) hα2 hZ).trans ?_
    rw [← hexpL]
    refine Real.exp_le_exp.mpr ?_
    rw [hα]
    field_simp
    linarith
  have hνbad : ∀ i, P.real {ω | α / 2 < |ν i ω|} ≤ β / (2 * k) := fun i ↦ by
    refine (measureReal_lt_abs_le_of_hasLaw_laplaceMeasure (by positivity) hα2 (hν i)).trans ?_
    rw [← hexpL]
    refine le_of_eq (congrArg Real.exp ?_)
    rw [hα]
    field_simp
    ring
  have hGc : P.real Gᶜ ≤ β := by
    refine (measureReal_mono hbad).trans ((measureReal_union_le _ _).trans ?_)
    refine (add_le_add hZbad (measureReal_biUnion_finset_le _ _)).trans ?_
    refine (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ hνbad i)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hk0 : (0 : ℝ) < k := by linarith
    have : β / (2 * k) ≤ β / 2 := div_le_div_of_nonneg_left hβ.le (by norm_num) (by linarith)
    have hkβ : (k : ℝ) * (β / (2 * k)) = β / 2 := by field_simp
    linarith
  have hGr : 1 - β ≤ P.real G := by
    have h := measureReal_union_le (μ := P) G Gᶜ
    rw [union_compl_self, probReal_univ] at h
    linarith
  refine hGr.trans (measureReal_mono fun ω ⟨hz, hn⟩ ↦ ⟨?_, fun i hi h ↦ ?_, fun i hi h ↦ ?_⟩)
  · rw [aboveThresholdTime, thresholdHittingTime_def]
    refine le_iInf fun n ↦ Nat.cast_le.mpr (not_lt.mp fun hlt ↦ ?_)
    have h1 := hlow n.val hlt
    have h2 := abs_le.mp (hn n.val (by omega))
    have h3 := abs_le.mp hz
    have h4 := n.2
    linarith
  · exact sub_le_of_threshold_add_le_add hz (hn i hi) h
  · exact le_add_of_add_lt_threshold_add hz (hn i hi) h

/-- The product of AdaBoost's normalizers over the first `T` rounds is the average exponential
loss `n⁻¹ ∑ᵢ exp(-yᵢ f(xᵢ))` of the score `f` after `T` rounds, for any weak predictors and
any coefficients. -/
theorem prod_boostingNormalizer {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (y : Fin n → ℝ) (h : ℕ → X → ℝ) (α : ℕ → ℝ) (T : ℕ) :
    ∏ t ∈ Finset.range T, boostingNormalizer x y h α t =
      (∑ i, exponentialLoss (y i * boostingScore h α T (x i))) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℕ → ℝ := fun t ↦ ∑ j, Real.exp (-y j * boostingScore h α t (x j)) with hS
  have hSpos : ∀ t, 0 < S t := fun t ↦
    Finset.sum_pos (fun j _ ↦ Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hloss : ∀ t, ∑ i, exponentialLoss (y i * boostingScore h α t (x i)) = S t := fun t ↦
    Finset.sum_congr rfl fun i _ ↦ by rw [exponentialLoss, neg_mul]
  have hZ : ∀ t, boostingNormalizer x y h α t = S (t + 1) / S t := by
    intro t
    simp only [boostingNormalizer, boostingWeight, hS, div_mul_eq_mul_div, ← Finset.sum_div,
      ← Real.exp_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ congrArg Real.exp ?_
    simp only [boostingScore, Finset.sum_range_succ]
    ring
  simp only [hloss]
  induction T with
  | zero => simp [hS, boostingScore, hn'.ne']
  | succ T ih =>
    rw [Finset.prod_range_succ, ih, hZ]
    field_simp [(hSpos T).ne']

/-- In a round with weighted error `ε ∈ (0, 1)`, labels and predictions in `{-1, 1}`, and
AdaBoost's coefficient `α = ½ log ((1 - ε) / ε)`, the normalizer is `2 √(ε (1 - ε))`. -/
theorem boostingNormalizer_eq {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (t : ℕ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ i, h t (x i) = 1 ∨ h t (x i) = -1)
    (hε : boostingWeightedError x y h α t ∈ Ioo 0 1)
    (hα : α t = Real.log ((1 - boostingWeightedError x y h α t) /
      boostingWeightedError x y h α t) / 2) :
    boostingNormalizer x y h α t =
      2 * Real.sqrt (boostingWeightedError x y h α t * (1 - boostingWeightedError x y h α t)) := by
  set ε := boostingWeightedError x y h α t with hεdef
  obtain ⟨hε0, hε1⟩ := hε
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hεdef, boostingWeightedError] at hε0
    · exact hn
  -- the weights sum to one
  have hD1 : ∑ i, boostingWeight x y h α t i = 1 := by
    simp only [boostingWeight, ← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun j _ ↦ Real.exp_pos _)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩).ne'
  set u := Real.exp (α t) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu2 : u ^ 2 = (1 - ε) / ε := by
    rw [hu, ← Real.exp_nat_mul, hα]
    push_cast
    rw [show 2 * (Real.log ((1 - ε) / ε) / 2) = Real.log ((1 - ε) / ε) by ring,
      Real.exp_log (div_pos (by linarith) hε0)]
  have hterm : ∀ i, boostingWeight x y h α t i * Real.exp (-(α t * y i * h t (x i))) =
      u⁻¹ * boostingWeight x y h α t i +
        (u - u⁻¹) * (if h t (x i) ≠ y i then boostingWeight x y h α t i else 0) := by
    intro i
    rw [hu, ← Real.exp_neg]
    rcases hy i with hyi | hyi <;> rcases hh i with hhi | hhi <;>
      simp only [hyi, hhi, ne_eq, not_true_eq_false, ite_false, mul_one, mul_neg, neg_neg,
        mul_zero, add_zero] <;> norm_num <;> ring
  have hZ : boostingNormalizer x y h α t = u⁻¹ + (u - u⁻¹) * ε := by
    simp only [boostingNormalizer, hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hD1,
      mul_one, hεdef, boostingWeightedError]
  have hsq : ε * (1 - ε) = (ε * u) ^ 2 := by
    rw [mul_pow, hu2]
    field_simp
  rw [hZ, hsq, Real.sqrt_sq (by positivity)]
  have : (1 - ε) = ε * u ^ 2 := by rw [hu2]; field_simp
  field_simp
  nlinarith [this]

/-- GAPS 107.24, the AdaBoost training-error bound. Let the labels `yᵢ` and the weak predictions
`hₜ(xᵢ)` lie in `{-1, 1}`, let every weighted error `εₜ`, `t < T`, lie in `(0, 1)`, and let
`αₜ = ½ log ((1 - εₜ) / εₜ)`. Then the fraction of sample points with `yᵢ f(xᵢ) ≤ 0` for the
score `f = ∑_{t<T} αₜ hₜ` (the training error of `sign f`, whatever the value of `sign 0`) is at
most `∏ₜ 2 √(εₜ (1 - εₜ)) ≤ exp (-2 ∑ₜ (½ - εₜ)²)`. Since the coefficients are determined
recursively by the errors, they are given as a sequence satisfying the defining equations.
The margin bound and the convex-hull Rademacher identity of GAPS 107.24 are not formalized. -/
theorem boosting_training_error_le {X : Type*} {n : ℕ} (x : Fin n → X) (y : Fin n → ℝ)
    (h : ℕ → X → ℝ) (α : ℕ → ℝ) (T : ℕ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t < T, ∀ i, h t (x i) = 1 ∨ h t (x i) = -1)
    (hε : ∀ t < T, boostingWeightedError x y h α t ∈ Ioo 0 1)
    (hα : ∀ t < T, α t = Real.log ((1 - boostingWeightedError x y h α t) /
      boostingWeightedError x y h α t) / 2) :
    (((Finset.univ.filter fun i ↦ y i * boostingScore h α T (x i) ≤ 0).card : ℝ) / n) ≤
        ∏ t ∈ Finset.range T, 2 * Real.sqrt (boostingWeightedError x y h α t *
          (1 - boostingWeightedError x y h α t)) ∧
      ∏ t ∈ Finset.range T, 2 * Real.sqrt (boostingWeightedError x y h α t *
          (1 - boostingWeightedError x y h α t)) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - boostingWeightedError x y h α t) ^ 2) := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]
      exact Finset.prod_nonneg fun t _ ↦ by positivity
    rw [Finset.prod_congr rfl fun t ht ↦ (boostingNormalizer_eq x y h α t hy
      (hh t (Finset.mem_range.mp ht)) (hε t (Finset.mem_range.mp ht))
      (hα t (Finset.mem_range.mp ht))).symm, prod_boostingNormalizer hn]
    exact training_error_le_exponential_loss _
  · rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun t _ ↦ by positivity) fun t _ ↦ ?_
    set ε := boostingWeightedError x y h α t
    have hpow : (2 * Real.sqrt (ε * (1 - ε))) ^ 2 ≤ Real.exp (-2 * (1 / 2 - ε) ^ 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt', ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (-2 * (1 / 2 - ε) ^ 2) = -(4 * (1 / 2 - ε) ^ 2) by ring]
      have h1 := Real.add_one_le_exp (-(4 * (1 / 2 - ε) ^ 2))
      have h2 := Real.exp_pos (-(4 * (1 / 2 - ε) ^ 2))
      rcases le_total (ε * (1 - ε)) 0 with hle | hle
      · rw [max_eq_right hle]; linarith
      · rw [max_eq_left hle]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hpow

/-- The ReLU activation is nonnegative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_left _ _

/-- ReLU is the identity on the nonnegative half-line. -/
@[simp] theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_right hx

end CKSD
