module

public import CKSD.Asymptotics.CrossFitting.FoldBounds

/-!
# Cross-fitted estimation of a missing mean

Asymptotic linearity of the cross-fitted augmented inverse-probability estimator of the mean of
a response that is missing at random (GAPS 102.39).

Cross-fitting uses `SampleSplit`, `crossFittedAverage`, and `missingMeanScore`. Rate
conditions on norms are expressed for `ℝ≥0∞`-valued `L²` norms (`eLpNorm`), so that an
infinite norm cannot be replaced by a junk real value.

The definitions `CKSD.TendstoInProbabilityZeroENNReal` and `CKSD.missingDataObservation`, the
fold Chebyshev inequality and the bias bound are in `CKSD.Asymptotics.CrossFitting.FoldBounds`.

## Main results

* `CKSD.crossFittedAverage_missingMean_asymptotically_linear`: asymptotic linearity of the
  cross-fitted estimator (GAPS 102.39).

## Implementation notes

The proof splits each fold sum into a centred part, bounded by Chebyshev's inequality given the
independent training data, and a bias part. Missingness at random makes the bias equal to
`E[(m - m₀)(π - π₀)/π]`, which the Cauchy–Schwarz inequality bounds by the product of the
nuisance errors. No lower bound on the fold sizes is needed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

section CrossFitting

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The augmented inverse-probability score only uses the response when it is observed. -/
private theorem missingMeanScore_missingDataObservation (h : (X → ℝ) × (X → ℝ))
    (w : Bool × X × ℝ) :
    missingMeanScore h.1 h.2 (missingDataObservation w).2.1 (missingDataObservation w).1
        (missingDataObservation w).2.2 = missingMeanScore h.1 h.2 w.2.1 w.1 w.2.2 := by
  rcases w with ⟨_ | _, x, y⟩ <;> simp [missingDataObservation_def, missingMeanScore_def]

/-- **Cross-fitting decomposition.** For `n ≥ 1`, the centred and scaled cross-fitted average
minus the linear term is the sum over folds of the scaled fold sums of score differences. -/
private theorem sqrt_mul_crossFittedAverage_sub_eq {Y H : Type*} {n K : ℕ} (hn : 0 < n)
    (split : SampleSplit n K) (train : ∀ k : Fin K, (split.trainingIndices k → Y) → H)
    (score : H → Y → ℝ) (s₀ : Y → ℝ) (x y : Fin n → Y)
    (hxy : ∀ h i, score h (x i) = score h (y i)) (c : ℝ) :
    Real.sqrt n * (crossFittedAverage split train score x - c) -
        (Real.sqrt n)⁻¹ * ∑ i, (s₀ (y i) - c) =
      ∑ k, (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.univ.filter fun i ↦ split.fold i = k,
        (score (train k fun j ↦ x j.val) (y i) - s₀ (y i)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  rw [← Finset.mul_sum]
  have hfib : ∑ k, ∑ i ∈ Finset.univ.filter (fun i ↦ split.fold i = k),
      (score (train k fun j ↦ x j.val) (y i) - s₀ (y i)) =
      ∑ i, (score (train (split.fold i) fun j ↦ x j.val) (y i) - s₀ (y i)) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := split.fold)]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(Finset.mem_filter.1 hi).2]
  rw [hfib, crossFittedAverage_def, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hxy]
  field_simp
  rw [Real.sq_sqrt hn'.le]
  ring

/-- Measurability of the augmented inverse-probability score with measurably estimated
nuisance functions. -/
private theorem measurable_missingMeanScore_comp {Z : Type*} [MeasurableSpace Z]
    {h : Z → (X → ℝ) × (X → ℝ)} (h₁ : Measurable fun p : Z × X ↦ (h p.1).1 p.2)
    (h₂ : Measurable fun p : Z × X ↦ (h p.1).2 p.2) :
    Measurable fun p : Z × (Bool × X × ℝ) ↦
      missingMeanScore (h p.1).1 (h p.1).2 p.2.2.1 p.2.1 p.2.2.2 := by
  have hS : MeasurableSet {p : Z × (Bool × X × ℝ) | p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hm : Measurable fun p : Z × (Bool × X × ℝ) ↦ (h p.1).1 p.2.2.1 :=
    h₁.comp (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hπ : Measurable fun p : Z × (Bool × X × ℝ) ↦ (h p.1).2 p.2.2.1 :=
    h₂.comp (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  simp only [missingMeanScore_def]
  exact hm.add (Measurable.ite hS (((measurable_snd.comp (measurable_snd.comp
    measurable_snd)).sub hm).div hπ) measurable_const)

/-- Measurability of the difference of two augmented inverse-probability scores, one with
measurably estimated nuisance functions. -/
private theorem measurable_missingMeanScore_sub {Z : Type*} [MeasurableSpace Z]
    {h : Z → (X → ℝ) × (X → ℝ)} (h₁ : Measurable fun p : Z × X ↦ (h p.1).1 p.2)
    (h₂ : Measurable fun p : Z × X ↦ (h p.1).2 p.2) {m₀ π₀ : X → ℝ} (hm₀m : Measurable m₀)
    (hπ₀m : Measurable π₀) :
    Measurable fun p : Z × (Bool × X × ℝ) ↦
      missingMeanScore (h p.1).1 (h p.1).2 p.2.2.1 p.2.1 p.2.2.2 -
        missingMeanScore m₀ π₀ p.2.2.1 p.2.1 p.2.2.2 :=
  (measurable_missingMeanScore_comp h₁ h₂).sub
    (measurable_missingMeanScore_comp (h := fun _ ↦ (m₀, π₀)) (hm₀m.comp measurable_snd)
      (hπ₀m.comp measurable_snd))

/-- Measurability of the observed-data map `(R, X, Y) ↦ (R, X, R Y)`. -/
private theorem measurable_missingDataObservation :
    Measurable (missingDataObservation : Bool × X × ℝ → Bool × X × ℝ) := by
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  rw [funext (missingDataObservation_def (X := X))]
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (Measurable.ite hS (measurable_snd.comp measurable_snd) measurable_const))

/-- Deterministic step for one fold: if `√n |c| ≤ ε / 2`, `|A| ≤ n` and the scaled fold sum
`n^{-1/2} (S + |A| c)` exceeds `ε`, then the centred sum `S` exceeds `ε √n / 2`. -/
private theorem lt_abs_of_lt_abs_inv_mul_add {s a S c ε : ℝ} (hs : 0 < s) (ha0 : 0 ≤ a)
    (ha : a ≤ s * s) (hc : s * |c| ≤ ε / 2) (h : ε < |s⁻¹ * (S + a * c)|) :
    ε / 2 * s < |S| := by
  rw [abs_mul, abs_inv, abs_of_pos hs] at h
  have h1 : |S + a * c| ≤ |S| + a * |c| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ha0]
  have h2 : a * |c| ≤ s * (s * |c|) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have h3 : ε * s < |S + a * c| := by
    rwa [inv_mul_eq_div, lt_div_iff₀ hs] at h
  nlinarith

/-- Bias step for one fold: from `‖c‖ₑ ≤ δ⁻¹ eᵤ eᵥ` and `√n eᵤ eᵥ ≤ ε δ / 2` follows
`√n |c| ≤ ε / 2`. -/
private theorem sqrt_mul_abs_le_of_enorm_le {s c δ ε : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ)
    (hε : 0 ≤ ε) {eu ev : ℝ≥0∞} (hc : ‖c‖ₑ ≤ ENNReal.ofReal δ⁻¹ * eu * ev)
    (hp : ENNReal.ofReal s * eu * ev ≤ ENNReal.ofReal (ε * δ / 2)) :
    s * |c| ≤ ε / 2 := by
  have h : ENNReal.ofReal (s * |c|) ≤ ENNReal.ofReal (ε / 2) := by
    rw [ENNReal.ofReal_mul hs, ← Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal s * ‖c‖ₑ ≤ ENNReal.ofReal s * (ENNReal.ofReal δ⁻¹ * eu * ev) := by
          gcongr
      _ = ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal s * eu * ev) := by ring
      _ ≤ ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (ε * δ / 2) := by gcongr
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le)]
        congr 1; field_simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- Measurability of the difference between the augmented inverse-probability score with
nuisance values trained on the observed data `(Rⱼ, Xⱼ, Rⱼ Yⱼ)` of a training sample and the
score with the true nuisance functions, jointly in the training sample and the new point. -/
private theorem measurable_missingMeanScore_observed_sub {T : Type*}
    (tr : (T → Bool × X × ℝ) → (X → ℝ) × (X → ℝ))
    (h₁ : Measurable fun p : (T → Bool × X × ℝ) × X ↦ (tr p.1).1 p.2)
    (h₂ : Measurable fun p : (T → Bool × X × ℝ) × X ↦ (tr p.1).2 p.2) {m₀ π₀ : X → ℝ}
    (hm₀m : Measurable m₀) (hπ₀m : Measurable π₀) :
    Measurable fun p : (T → Bool × X × ℝ) × (Bool × X × ℝ) ↦
      missingMeanScore (tr fun j ↦ missingDataObservation (p.1 j)).1
        (tr fun j ↦ missingDataObservation (p.1 j)).2 p.2.2.1 p.2.1 p.2.2.2 -
      missingMeanScore m₀ π₀ p.2.2.1 p.2.1 p.2.2.2 := by
  have hΦ : Measurable fun z : T → Bool × X × ℝ ↦ fun j ↦ missingDataObservation (z j) :=
    measurable_pi_iff.2 fun j ↦ measurable_missingDataObservation.comp (measurable_pi_apply j)
  exact measurable_missingMeanScore_sub
    (h := fun z : T → Bool × X × ℝ ↦ tr fun j ↦ missingDataObservation (z j))
    (h₁.comp ((hΦ.comp measurable_fst).prodMk measurable_snd))
    (h₂.comp ((hΦ.comp measurable_fst).prodMk measurable_snd)) hm₀m hπ₀m

/-- Choice of the Chebyshev threshold for one fold: given `ε > 0` and `e > 0` there are `r` and
`η > 0` with `r ≤ e / 2` and `|A| η² / (ε √n / 2)² ≤ r` whenever `|A| ≤ n`, `n ≥ 1`. -/
theorem exists_ofReal_mul_sq_div_sq_le {ε : ℝ} (hε : 0 < ε) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r η : ℝ, 0 < η ∧ ENNReal.ofReal r ≤ e / 2 ∧ ∀ (n : ℕ) (a : ℝ), 1 ≤ n → a ≤ n →
      ENNReal.ofReal (a * η ^ 2 / (ε / 2 * Real.sqrt n) ^ 2) ≤ ENNReal.ofReal r := by
  set e₁ : ℝ≥0∞ := min e 1 with he₁def
  have he₁ : 0 < e₁ := lt_min he one_pos
  have he₁t : e₁ ≠ ∞ := ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
  set r : ℝ := e₁.toReal / 2 with hrdef
  have hr : 0 < r := div_pos (ENNReal.toReal_pos he₁.ne' he₁t) two_pos
  set η : ℝ := ε / 2 * Real.sqrt r with hηdef
  have hη : 0 < η := by positivity
  have hηr : η ^ 2 / (ε / 2) ^ 2 = r := by
    rw [hηdef, mul_pow, Real.sq_sqrt hr.le]; field_simp
  refine ⟨r, η, hη, ?_, fun n a hn ha ↦ ENNReal.ofReal_le_ofReal ?_⟩
  · rw [hrdef, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal he₁t,
      ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_right (min_le_left _ _) 2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (ε / 2 * Real.sqrt n) ^ 2 = (ε / 2) ^ 2 * n := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [e, ← hηr, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ η ^ 2 * (ε / 2) ^ 2 := by positivity
  nlinarith

/-- Deterministic step for one fold with fixed nuisance values `(m, π)`, `π ≥ δ`: if
`‖m - m₀‖₂ ≤ 1`, `√n ‖m - m₀‖₂ ‖π - π₀‖₂ ≤ ε δ / 2` and `|A| ≤ n`, and the scaled fold sum of
score differences `D` exceeds `ε`, then the centred fold sum `∑_{i ∈ A} (D(wᵢ) - E D)` exceeds
`ε √n / 2`. -/
private theorem lt_abs_sum_sub_integral_of_lt_abs_inv_mul_sum {ι : Type*}
    (P : Measure (Bool × X × ℝ)) [IsProbabilityMeasure P]
    (hY : MemLp (fun w : Bool × X × ℝ ↦ w.2.2) 2 P)
    (π₀ m₀ : X → ℝ) (hπ₀m : Measurable π₀) (hm₀m : Measurable m₀) {δ : ℝ} (hδ : 0 < δ)
    (hπ₀ : ∀ x, δ ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P)
    (m π : X → ℝ) (hm : Measurable m) (hπ : Measurable π) (hπδ : ∀ x, δ ≤ π x)
    {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) (A : Finset ι) (hA : (A.card : ℝ) ≤ s * s)
    (w : ι → Bool × X × ℝ)
    (hu1 : eLpNorm (fun x ↦ m x - m₀ x) 2 (P.map fun w ↦ w.2.1) ≤ ENNReal.ofReal 1)
    (hp : ENNReal.ofReal s * eLpNorm (fun x ↦ m x - m₀ x) 2 (P.map fun w ↦ w.2.1) *
      eLpNorm (fun x ↦ π x - π₀ x) 2 (P.map fun w ↦ w.2.1) ≤ ENNReal.ofReal (ε * δ / 2))
    (h : ε < |s⁻¹ * ∑ i ∈ A, (missingMeanScore m π (w i).2.1 (w i).1 (w i).2.2 -
      missingMeanScore m₀ π₀ (w i).2.1 (w i).1 (w i).2.2)|) :
    ε / 2 * s < |∑ i ∈ A, ((missingMeanScore m π (w i).2.1 (w i).1 (w i).2.2 -
      missingMeanScore m₀ π₀ (w i).2.1 (w i).1 (w i).2.2) -
        ∫ y, (missingMeanScore m π y.2.1 y.1 y.2.2 -
          missingMeanScore m₀ π₀ y.2.1 y.1 y.2.2) ∂P)| := by
  have hbias := enorm_integral_missingMeanScore_sub_le P hY π₀ m₀ hπ₀m hm₀m hδ hπ₀ hmar hreg
    _ _ hm hπ hπδ (hu1.trans_lt ENNReal.ofReal_lt_top)
  have hc := sqrt_mul_abs_le_of_enorm_le hs.le hδ hε hbias hp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  refine lt_abs_of_lt_abs_inv_mul_add hs (Nat.cast_nonneg _) hA hc ?_
  rwa [sub_add_cancel]

/-- **One fold of the cross-fitted estimator.** For a fold `k`, the scaled fold sum of the
differences between the scores with estimated and with true nuisance functions tends to zero
in probability. The centred part is controlled by Chebyshev's inequality given the training
data, the bias part by the product of the nuisance errors. -/
private theorem tendsto_measure_lt_abs_fold_term {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (Bool × X × ℝ))
    [IsProbabilityMeasure P] (W : ℕ → Ω → Bool × X × ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ W P)
    (hY : MemLp (fun w : Bool × X × ℝ ↦ w.2.2) 2 P)
    (π₀ m₀ : X → ℝ) (hπ₀m : Measurable π₀) (hm₀m : Measurable m₀) {δ : ℝ} (hδ : 0 < δ)
    (hπ₀ : ∀ x, δ ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P)
    {K : ℕ} (split : ∀ n, SampleSplit n K)
    (train : ∀ n (k : Fin K), ((split n).trainingIndices k → Bool × X × ℝ) → (X → ℝ) × (X → ℝ))
    (htrain₁ : ∀ n k, Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k p.1).1 p.2)
    (htrain₂ : ∀ n k, Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k p.1).2 p.2)
    (hπhat : ∀ n k z x, δ ≤ (train n k z).2 x) (k : Fin K)
    (h1 : TendstoInProbabilityZeroENNReal μ fun n ω ↦
      eLpNorm (fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).1 x - m₀ x) 2
        (P.map fun w ↦ w.2.1))
    (h2 : TendstoInProbabilityZeroENNReal μ fun n ω ↦
      eLpNorm (fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).2 x - π₀ x) 2
        (P.map fun w ↦ w.2.1))
    (h3 : TendstoInProbabilityZeroENNReal μ fun n ω ↦
      ENNReal.ofReal (Real.sqrt n) *
        eLpNorm (fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).1 x - m₀ x) 2
          (P.map fun w ↦ w.2.1) *
        eLpNorm (fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).2 x - π₀ x) 2
          (P.map fun w ↦ w.2.1))
    (h4 : TendstoInProbabilityZeroENNReal μ fun n ω ↦
      eLpNorm (fun w ↦ missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
        (train n k fun j ↦ missingDataObservation (W j.val ω)).2 w.2.1 w.1 w.2.2 -
          missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2) 2 P)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ {ω | ε < |(Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.univ.filter (fun i ↦ (split n).fold i = k),
        (missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
          (train n k fun j ↦ missingDataObservation (W j.val ω)).2 (W i ω).2.1 (W i ω).1
            (W i ω).2.2 - missingMeanScore m₀ π₀ (W i ω).2.1 (W i ω).1 (W i ω).2.2)|})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨r, η, hη, hrle, hrem⟩ := exists_ofReal_mul_sq_div_sq_le hε he
  have hlim := (h4 η hη).add (((h1 1 one_pos).add (h2 1 one_pos)).add
    (h3 (ε * δ / 2) (by positivity)))
  simp only [add_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds (ENNReal.half_pos he.ne')),
    eventually_ge_atTop 1] with n hlimn hn
  clear h1 h2 h3 h4 hlim
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), A = Finset.univ.filter fun i ↦ (split n).fold i = k :=
    ⟨_, rfl⟩
  have hdisj : ∀ i ∈ A, i ∉ (split n).trainingIndices k := fun i hi hiT ↦ by
    subst hA; exact hiT (Finset.mem_filter.1 hi).2
  obtain ⟨G, hGdef⟩ : ∃ G : ((split n).trainingIndices k → Bool × X × ℝ) × (Bool × X × ℝ) → ℝ,
      G = fun p ↦ missingMeanScore (train n k fun j ↦ missingDataObservation (p.1 j)).1
        (train n k fun j ↦ missingDataObservation (p.1 j)).2 p.2.2.1 p.2.1 p.2.2.2 -
      missingMeanScore m₀ π₀ p.2.2.1 p.2.1 p.2.2.2 := ⟨_, rfl⟩
  have hG : Measurable G :=
    hGdef ▸ measurable_missingMeanScore_observed_sub (train n k) (htrain₁ n k) (htrain₂ n k)
      hm₀m hπ₀m
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hcard : (A.card : ℝ) ≤ Real.sqrt n * Real.sqrt n := by
    rw [hsq, hA]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨D, hD⟩ : ∃ D : Ω → Bool × X × ℝ → ℝ, D = fun ω w ↦
      missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
        (train n k fun j ↦ missingDataObservation (W j.val ω)).2 w.2.1 w.1 w.2.2 -
      missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2 := ⟨_, rfl⟩
  have hGD : ∀ ω w, G ((fun j : (split n).trainingIndices k ↦ W j.val.val ω), w) = D ω w := by
    intro ω w; rw [hGdef, hD]
  have hDm : ∀ ω, Measurable (D ω) := fun ω ↦ by
    have : D ω = fun w ↦ G ((fun j : (split n).trainingIndices k ↦ W j.val.val ω), w) := by
      ext w; rw [hGD]
    rw [this]; exact hG.comp measurable_prodMk_left
  have hF := measure_lt_abs_fold_sum_sub_integral_le μ P W hiid A _ hdisj G hG
    (ε := ε / 2 * Real.sqrt n) (by positivity) η
  simp only [hGD] at hF
  have hbad : {ω | ENNReal.ofReal (η ^ 2) < ∫⁻ y, ENNReal.ofReal (D ω y ^ 2) ∂P} ⊆
      {ω | ENNReal.ofReal η < eLpNorm (D ω) 2 P} := fun ω hω ↦ by
    by_contra h
    exact (not_lt.2 (lintegral_ofReal_sq_le_of_eLpNorm_le (hDm ω).aestronglyMeasurable hη.le
      (not_lt.1 h))) hω
  obtain ⟨eu, heu⟩ : ∃ eu : Ω → ℝ≥0∞, ∀ ω, eLpNorm (fun x ↦
      (train n k fun j ↦ missingDataObservation (W j.val ω)).1 x - m₀ x) 2
        (P.map fun w ↦ w.2.1) = eu ω := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨ev, hev⟩ : ∃ ev : Ω → ℝ≥0∞, ∀ ω, eLpNorm (fun x ↦
      (train n k fun j ↦ missingDataObservation (W j.val ω)).2 x - π₀ x) 2
        (P.map fun w ↦ w.2.1) = ev ω := ⟨_, fun _ ↦ rfl⟩
  have hDω : ∀ ω, (fun w : Bool × X × ℝ ↦
      missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
        (train n k fun j ↦ missingDataObservation (W j.val ω)).2 w.2.1 w.1 w.2.2 -
      missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2) = D ω := fun ω ↦ by rw [hD]
  simp only [heu, hev, hDω] at hlimn
  have hsub : {ω | ε < |(Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.univ.filter (fun i ↦ (split n).fold i = k),
        (missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
          (train n k fun j ↦ missingDataObservation (W j.val ω)).2 (W i ω).2.1 (W i ω).1
            (W i ω).2.2 - missingMeanScore m₀ π₀ (W i ω).2.1 (W i ω).1 (W i ω).2.2)|} ⊆
      {ω | ε / 2 * Real.sqrt n < |∑ i ∈ A, (D ω (W i ω) - ∫ y, D ω y ∂P)|} ∪
        ({ω | ENNReal.ofReal 1 < eu ω} ∪ {ω | ENNReal.ofReal 1 < ev ω} ∪
          {ω | ENNReal.ofReal (ε * δ / 2) < ENNReal.ofReal (Real.sqrt n) * eu ω * ev ω}) := by
    intro ω hω
    by_cases hB : ENNReal.ofReal 1 < eu ω ∨ ENNReal.ofReal 1 < ev ω ∨
        ENNReal.ofReal (ε * δ / 2) < ENNReal.ofReal (Real.sqrt n) * eu ω * ev ω
    · rcases hB with h | h | h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
    left
    simp only [not_or, not_lt] at hB
    obtain ⟨hu1, hv1, hp⟩ := hB
    have hm : Measurable fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).1 x :=
      (htrain₁ n k).comp (measurable_const.prodMk measurable_id)
    have hπ : Measurable fun x ↦ (train n k fun j ↦ missingDataObservation (W j.val ω)).2 x :=
      (htrain₂ n k).comp (measurable_const.prodMk measurable_id)
    simp only [mem_ofPred_eq] at hω ⊢
    rw [← heu, ← hev] at hp
    rw [← heu] at hu1
    rw [← hA] at hω
    rw [hD]
    exact lt_abs_sum_sub_integral_of_lt_abs_inv_mul_sum P hY π₀ m₀ hπ₀m hm₀m hδ hπ₀ hmar hreg
      _ _ hm hπ (hπhat n k _) hsn hε.le A hcard (fun i ↦ W i ω) hu1 hp hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (μ {ω | ENNReal.ofReal η < eLpNorm (D ω) 2 P} + ENNReal.ofReal r) +
        (μ {ω | ENNReal.ofReal 1 < eu ω} + μ {ω | ENNReal.ofReal 1 < ev ω} +
          μ {ω | ENNReal.ofReal (ε * δ / 2) < ENNReal.ofReal (Real.sqrt n) * eu ω * ev ω}) := by
      gcongr
      · exact hF.trans (add_le_add (measure_mono hbad) (hrem n _ hn (hsq ▸ hcard)))
      · exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = (μ {ω | ENNReal.ofReal η < eLpNorm (D ω) 2 P} +
        (μ {ω | ENNReal.ofReal 1 < eu ω} + μ {ω | ENNReal.ofReal 1 < ev ω} +
          μ {ω | ENNReal.ofReal (ε * δ / 2) < ENNReal.ofReal (Real.sqrt n) * eu ω * ev ω})) +
        ENNReal.ofReal r := by ring
    _ ≤ e / 2 + e / 2 := add_le_add hlimn hrle
    _ = e := ENNReal.add_halves e

end CrossFitting

/-- GAPS 102.39: asymptotic linearity of the cross-fitted augmented inverse-probability
estimator of a missing mean. The full-data triples `(R, X, Y)` are iid with law `P`, the
response is missing at random with propensity `π₀`, and `m₀` is the regression of `Y` on `X`,
both expressed by their defining integral identities. The estimators `(m̂, π̂)` on fold `k`
are computed from the observed data `(R, X, RY)` outside fold `k`. On each fold the `L²(P_X)`
errors of `m̂` and `π̂` tend to zero in probability, their product is `o_P(n^{-1/2})`, and the
`L²(P)` distance between the estimated and true scores, with the nuisance estimates held fixed,
tends to zero in probability. -/
theorem crossFittedAverage_missingMean_asymptotically_linear
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (Bool × X × ℝ))
    [IsProbabilityMeasure P] (W : ℕ → Ω → Bool × X × ℝ)
    (hiid : IsIndependentIdenticallyDistributed μ W P)
    (hY : MemLp (fun w : Bool × X × ℝ ↦ w.2.2) 2 P)
    (π₀ m₀ : X → ℝ) (hπ₀m : Measurable π₀) (hm₀m : Measurable m₀) (δ : ℝ) (hδ : 0 < δ)
    (hπ₀ : ∀ x, δ ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P)
    (K : ℕ) (split : ∀ n, SampleSplit n K)
    (train : ∀ n (k : Fin K), ((split n).trainingIndices k → Bool × X × ℝ) → (X → ℝ) × (X → ℝ))
    (htrain₁ : ∀ n k, Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k p.1).1 p.2)
    (htrain₂ : ∀ n k, Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k p.1).2 p.2)
    (hπhat : ∀ n k z x, δ ≤ (train n k z).2 x) :
    let PX := P.map fun w ↦ w.2.1;
    let mean := ∫ w, w.2.2 ∂P;
    let fit := fun n (k : Fin K) (ω : Ω) ↦
      train n k fun j ↦ missingDataObservation (W j.val ω);
    let score := fun (h : (X → ℝ) × (X → ℝ)) (w : Bool × X × ℝ) ↦
      missingMeanScore h.1 h.2 w.2.1 w.1 w.2.2;
    (∀ k : Fin K, TendstoInProbabilityZeroENNReal μ fun n ω ↦
        eLpNorm (fun x ↦ (fit n k ω).1 x - m₀ x) 2 PX) →
    (∀ k : Fin K, TendstoInProbabilityZeroENNReal μ fun n ω ↦
        eLpNorm (fun x ↦ (fit n k ω).2 x - π₀ x) 2 PX) →
    (∀ k : Fin K, TendstoInProbabilityZeroENNReal μ fun n ω ↦
        ENNReal.ofReal (Real.sqrt n) * eLpNorm (fun x ↦ (fit n k ω).1 x - m₀ x) 2 PX *
          eLpNorm (fun x ↦ (fit n k ω).2 x - π₀ x) 2 PX) →
    (∀ k : Fin K, TendstoInProbabilityZeroENNReal μ fun n ω ↦
        eLpNorm (fun w ↦ score (fit n k ω) w - score (m₀, π₀) w) 2 P) →
    TendstoInMeasure μ (fun (n : ℕ) ω ↦
      Real.sqrt n * (crossFittedAverage (split n) (train n) score
        (fun i ↦ missingDataObservation (W i ω)) - mean) -
      (Real.sqrt n)⁻¹ * ∑ i : Fin n, (score (m₀, π₀) (W i ω) - mean)) atTop (fun _ ↦ 0) := by
  intro PX mean fit score h1 h2 h3 h4
  have hK : 0 < K := Fin.pos ((split 1).fold 0)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hfold := fun k : Fin K ↦ tendsto_measure_lt_abs_fold_term μ P W hiid hY π₀ m₀ hπ₀m hm₀m
    hδ hπ₀ hmar hreg split train htrain₁ htrain₂ hπhat k (h1 k) (h2 k) (h3 k) (h4 k) hε'
  have hsum := tendsto_finsetSum Finset.univ fun k _ ↦ hfold k
  simp only [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine (measure_mono ?_).trans (measure_biUnion_finset_le Finset.univ _)
  intro ω hω
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
  rw [sqrt_mul_crossFittedAverage_sub_eq hn (split n) (train n) score (score (m₀, π₀))
    (fun i ↦ missingDataObservation (W i ω)) (fun i ↦ W i ω)
    (fun h i ↦ missingMeanScore_missingDataObservation h _) mean] at hω
  by_contra hcon
  simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_univ, exists_true_left, not_exists,
    not_lt] at hcon
  refine absurd hω (not_le.2 ?_)
  calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin K, ε / (2 * K) := Finset.sum_le_sum fun k _ ↦ hcon k
    _ = ε / 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ < ε := half_lt_self hε

end CKSD
