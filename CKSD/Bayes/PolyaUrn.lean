module

public import CKSD.Bayes.Nonparametric
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.PSeries


/-!
# Pólya urn predictive laws and distinct values

The urn is specified by its conditional next-observation law given the complete finite past.
For an atomless base measure, the distinct-count theorems describe the Chinese restaurant
counting process.

## Main definitions

* `CKSD.IsPolyaUrnProcess P α Xn`: `Xn` follows the Pólya urn with base measure `α`.
* `CKSD.distinctObservationCount Xn n ω`: the number of distinct values among the first `n`
  observations.

## Main results

* `CKSD.integral_distinct_observation_count_polya`: the expected number of distinct values is
  `∑_{i<n} θ / (θ + i)`, with `θ = α(X)`.
* `CKSD.integral_sq_distinct_observation_count_sub_le_polya`: its variance is at most its mean.
* `CKSD.ae_tendsto_distinct_observation_count_div_log_polya`: the number of distinct values grows
  like `θ log n` almost surely.

Sources: GAPS 104.16.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Pólya urn protocol, with predictive law conditional on the first `n` observations. -/
def IsPolyaUrnProcess {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X)
    (Xn : ℕ → Ω → X) : Prop :=
  (∀ n, Measurable (Xn n)) ∧ ∀ n, ∀ᵐ ω ∂P,
    condDistrib (Xn n) (fun (ω : Ω) (i : Fin n) ↦ Xn i.val ω) P
      (fun i : Fin n ↦ Xn i.val ω) = polyaPredictiveLaw α (fun i : Fin n ↦ Xn i.val ω)

/-- Number of distinct values among the first `n` observations. -/
def distinctObservationCount {Ω X : Type*} (Xn : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).image fun i ↦ Xn i ω).card

/-- The distinct count increases by one exactly when the next observation is new. -/
theorem distinct_observation_count_succ {Ω X : Type*} (Xn : ℕ → Ω → X) (n : ℕ) (ω : Ω) :
    distinctObservationCount Xn (n + 1) ω = distinctObservationCount Xn n ω +
      if ∀ i < n, Xn n ω ≠ Xn i ω then 1 else 0 := by
  unfold distinctObservationCount
  rw [Finset.range_add_one, Finset.image_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun i hi heq ↦ h i hi heq.symm
  · push Not at h
    obtain ⟨i, hi, heq⟩ := h
    rw [Finset.insert_eq_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, heq.symm⟩)]
    simp

/-- For an atomless base, the Pólya predictive law gives the complement of the observed values
the mass `|α| / (|α| + n)`. -/
theorem polya_predictive_law_compl_range {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (α : Measure X) [IsFiniteMeasure α] [NullSingletonClass α]
    {n : ℕ}
    (y : Fin n → X) : polyaPredictiveLaw α y (range y)ᶜ = (α univ + n)⁻¹ * α univ := by
  have hmc : MeasurableSet (range y)ᶜ := (Set.finite_range y).measurableSet.compl
  rw [polyaPredictiveLaw, smul_apply, smul_eq_mul, dirichletPosteriorBase,
    add_apply, FunLike.coe_sum, Finset.sum_apply]
  congr 1
  rw [measure_compl (Set.finite_range y).measurableSet (measure_ne_top _ _),
    (Set.finite_range y).measure_zero α, tsub_zero]
  simp only [Measure.dirac_apply' _ hmc, Set.indicator, mem_compl_iff, mem_range,
    exists_apply_eq_apply, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero, add_zero]

/-- Under a Pólya urn with atomless base `α`, the `n`-th observation is new with probability
`|α| / (|α| + n)`: the predictive law gives the finitely many past values the mass of their
atoms only, and `α` charges no finite set. -/
theorem measure_real_new_observation_polya {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) (n : ℕ) :
    P.real {ω | ∀ i < n, Xn n ω ≠ Xn i ω} = α.real univ / (α.real univ + n) := by
  obtain ⟨hmeas, hcond⟩ := hurn
  set Y : Ω → Fin n → X := fun ω i ↦ Xn i.val ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  set S : Set ((Fin n → X) × X) := {p | ∀ i : Fin n, p.2 ≠ p.1 i} with hS
  have hSm : MeasurableSet S := by
    rw [hS, ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ (measurableSet_eq_fun measurable_snd
      ((measurable_pi_apply i).comp measurable_fst)).compl
  have hset : {ω | ∀ i < n, Xn n ω ≠ Xn i ω} = (fun ω ↦ (Y ω, Xn n ω)) ⁻¹' S := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hS, hYdef]
    exact ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩
  have hval (y : Fin n → X) : polyaPredictiveLaw α y (Prod.mk y ⁻¹' S) =
      (α univ + n)⁻¹ * α univ := by
    have hpre : Prod.mk y ⁻¹' S = (range y)ᶜ := by
      ext x
      simp [hS, eq_comm]
    rw [hpre, polya_predictive_law_compl_range]
  have hmain : P {ω | ∀ i < n, Xn n ω ≠ Xn i ω} = (α univ + n)⁻¹ * α univ := by
    rw [hset, ← Measure.map_apply (hY.prodMk (hmeas n)) hSm,
      ← compProd_map_condDistrib hY.aemeasurable (hmeas n).aemeasurable,
      Measure.compProd_apply hSm, lintegral_map _ hY]
    · rw [lintegral_congr_ae (g := fun _ ↦ (α univ + n)⁻¹ * α univ)]
      · simp
      · filter_upwards [hcond n] with ω hω
        simp only [hYdef] at hω ⊢
        rw [hω, hval]
    · exact Kernel.measurable_kernel_prodMk_left hSm
  rw [measureReal_def, hmain, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add
    (measure_ne_top _ _) (ENNReal.natCast_ne_top n), measureReal_def, div_eq_inv_mul]
  simp

/-- The distinct count is the number of indices at which a new value is observed. -/
theorem distinct_observation_count_eq_sum_indicator {Ω X : Type*} (Xn : ℕ → Ω → X) (n : ℕ)
    (ω : Ω) : (distinctObservationCount Xn n ω : ℝ) = ∑ i ∈ Finset.range n,
      {ω | ∀ j < i, Xn i ω ≠ Xn j ω}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  induction n with
  | zero => simp [distinctObservationCount]
  | succ n ih =>
    rw [distinct_observation_count_succ, Finset.sum_range_succ, ← ih, Nat.cast_add]
    congr 1
    by_cases h : ∀ j < n, Xn n ω ≠ Xn j ω <;> simp [h, Set.indicator]

/-- GAPS 104.16: expected number of distinct observations under an atomless Pólya base. -/
theorem integral_distinct_observation_count_polya {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) (n : ℕ) :
    (∫ ω, (distinctObservationCount Xn n ω : ℝ) ∂P) =
      ∑ i ∈ Finset.range n, α.real univ / (α.real univ + i) := by
  have hm (i : ℕ) : MeasurableSet {ω | ∀ j < i, Xn i ω ≠ Xn j ω} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_eq_fun (hurn.1 i) (hurn.1 j)).compl
  simp_rw [distinct_observation_count_eq_sum_indicator]
  rw [integral_finsetSum _ fun i _ ↦ (integrable_const 1).indicator (hm i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_indicator_const (1 : ℝ) (hm i), smul_eq_mul, mul_one,
    measure_real_new_observation_polya P α Xn hurn i]

/-- Conditionally on the first `n` observations of a Pólya urn with atomless base, the `n`-th
observation is new with probability `|α| / (|α| + n)`: for a bounded measurable function `F` of
the past, `𝔼[F · 1{new}] = |α| / (|α| + n) · 𝔼[F]`. -/
theorem integral_mul_indicator_new_observation_polya {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) (n : ℕ) (F : (Fin n → X) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ y, |F y| ≤ C) :
    ∫ ω, F (fun i : Fin n ↦ Xn i ω) *
        {ω | ∀ i < n, Xn n ω ≠ Xn i ω}.indicator (fun _ ↦ (1 : ℝ)) ω ∂P =
      α.real univ / (α.real univ + n) * ∫ ω, F (fun i : Fin n ↦ Xn i ω) ∂P := by
  obtain ⟨hmeas, hcond⟩ := hurn
  set Y : Ω → Fin n → X := fun ω i ↦ Xn i.val ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  set S : Set ((Fin n → X) × X) := {p | ∀ i : Fin n, p.2 ≠ p.1 i} with hS
  have hSm : MeasurableSet S := by
    rw [hS, ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ (measurableSet_eq_fun measurable_snd
      ((measurable_pi_apply i).comp measurable_fst)).compl
  set H : (Fin n → X) × X → ℝ := fun p ↦ F p.1 * S.indicator (fun _ ↦ (1 : ℝ)) p with hH
  have hHm : Measurable H :=
    (hF.comp measurable_fst).mul (measurable_const.indicator hSm)
  have hpt (ω : Ω) : F (Y ω) * {ω | ∀ i < n, Xn n ω ≠ Xn i ω}.indicator (fun _ ↦ (1 : ℝ)) ω =
      H (Y ω, Xn n ω) := by
    simp only [hH, hS, Set.indicator, mem_ofPred_eq, hYdef]
    congr 1
    congr 1
    exact propext ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩
  have hpre (y : Fin n → X) : Prod.mk y ⁻¹' S = (range y)ᶜ := by
    ext x; simp [hS, eq_comm]
  set κ := condDistrib (Xn n) Y P with hκ
  have hinner (y : Fin n → X) : ∫ x, H (y, x) ∂κ y = F y * (κ y).real (range y)ᶜ := by
    simp only [hH]
    rw [integral_const_mul]
    congr 1
    have : (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) (y, x)) =
        (range y)ᶜ.indicator (fun _ ↦ (1 : ℝ)) := by
      funext x
      rw [← hpre y]
      rfl
    rw [this, integral_indicator_const _ (Set.finite_range y).measurableSet.compl,
      smul_eq_mul, mul_one]
  have hHint : Integrable H ((P.map Y) ⊗ₘ κ) := by
    refine Integrable.of_bound hHm.aestronglyMeasurable C (ae_of_all _ fun p ↦ ?_)
    simp only [hH, Real.norm_eq_abs, abs_mul]
    refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (hC _)
    by_cases hp : p ∈ S <;> simp [Set.indicator, hp]
  have hG : StronglyMeasurable fun y ↦ ∫ x, H (y, x) ∂κ y :=
    StronglyMeasurable.integral_kernel_prod_right (f := fun y x ↦ H (y, x))
      hHm.stronglyMeasurable
  change ∫ ω, F (Y ω) * {ω | ∀ i < n, Xn n ω ≠ Xn i ω}.indicator (fun _ ↦ (1 : ℝ)) ω ∂P = _
  simp_rw [hpt]
  rw [← integral_map (hY.prodMk (hmeas n)).aemeasurable hHm.aestronglyMeasurable,
    ← compProd_map_condDistrib hY.aemeasurable (hmeas n).aemeasurable,
    Measure.integral_compProd hHint, integral_map hY.aemeasurable hG.aestronglyMeasurable,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcond n] with ω hω
  rw [hinner]
  simp only [hYdef] at hω ⊢
  rw [hω, measureReal_def, polya_predictive_law_compl_range, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.natCast_ne_top n),
    ← measureReal_def]
  simp only [ENNReal.toReal_natCast]
  ring

/-- Second moment of the centred distinct count of a Pólya urn: the increments of
`Kₙ - ∑_{i<n} |α|/(|α|+i)` are orthogonal Bernoulli residuals, so its second moment is at most
`∑_{i<n} |α|/(|α|+i)`. -/
theorem integral_sq_distinct_observation_count_sub_le_polya {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) (n : ℕ) :
    ∫ ω, ((distinctObservationCount Xn n ω : ℝ) -
        ∑ i ∈ Finset.range n, α.real univ / (α.real univ + i)) ^ 2 ∂P ≤
      ∑ i ∈ Finset.range n, α.real univ / (α.real univ + i) := by
  set θ := α.real univ with hθ
  set p : ℕ → ℝ := fun i ↦ θ / (θ + i) with hp
  have hp0 (i : ℕ) : 0 ≤ p i := div_nonneg measureReal_nonneg (by positivity)
  set A : ℕ → Set Ω := fun i ↦ {ω | ∀ j < i, Xn i ω ≠ Xn j ω} with hA
  have hAm (i : ℕ) : MeasurableSet (A i) := by
    simp only [hA, ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_eq_fun (hurn.1 i) (hurn.1 j)).compl
  set I : ℕ → Ω → ℝ := fun i ↦ (A i).indicator fun _ ↦ 1 with hI
  have hIm (i : ℕ) : Measurable (I i) := measurable_const.indicator (hAm i)
  have hI01 (i : ℕ) (ω : Ω) : I i ω = 0 ∨ I i ω = 1 := by
    by_cases h : ω ∈ A i <;> simp [hI, h]
  have hIint (i : ℕ) : Integrable (I i) P := (integrable_const 1).indicator (hAm i)
  have hEI (i : ℕ) : ∫ ω, I i ω ∂P = p i := by
    rw [integral_indicator_const (1 : ℝ) (hAm i), smul_eq_mul, mul_one]
    exact measure_real_new_observation_polya P α Xn hurn i
  induction n with
  | zero => simp [distinctObservationCount]
  | succ n ih =>
    set c := ∑ i ∈ Finset.range n, p i with hc
    -- `Kₙ - cₙ` as a bounded measurable function of the first `n` observations.
    set B : Fin n → Set (Fin n → X) := fun i ↦ {y | ∀ j : Fin n, j < i → y i ≠ y j} with hB
    have hBm (i : Fin n) : MeasurableSet (B i) := by
      simp only [hB, ofPred_forall]
      exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
    set F : (Fin n → X) → ℝ := fun y ↦ (∑ i, (B i).indicator (fun _ ↦ (1 : ℝ)) y) - c with hF
    have hFm : Measurable F :=
      (Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator (hBm i)).sub_const _
    have hFb (y : Fin n → X) : |F y| ≤ n + c := by
      simp only [hF]
      refine (abs_sub _ _).trans (add_le_add ?_ (le_of_eq (abs_of_nonneg
        (Finset.sum_nonneg fun i _ ↦ hp0 i))))
      rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦
        zero_le_one) _)]
      calc ∑ i, (B i).indicator (fun _ ↦ (1 : ℝ)) y ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) _
        _ = n := by simp
    have hMF (ω : Ω) : (distinctObservationCount Xn n ω : ℝ) - c =
        F (fun i : Fin n ↦ Xn i ω) := by
      rw [distinct_observation_count_eq_sum_indicator, hF, ← Fin.sum_univ_eq_sum_range]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Set.indicator, hB, mem_ofPred_eq]
      congr 1
      exact propext ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h ⟨j, hj.trans i.2⟩ hj⟩
    have hY : Measurable fun ω (i : Fin n) ↦ Xn i ω := measurable_pi_iff.2 fun i ↦ hurn.1 i
    have hFY : Integrable (fun ω ↦ F (fun i : Fin n ↦ Xn i ω)) P :=
      Integrable.of_bound (hFm.comp hY).aestronglyMeasurable (n + c)
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hFb _)
    have hFI : Integrable (fun ω ↦ F (fun i : Fin n ↦ Xn i ω) * I n ω) P :=
      Integrable.of_bound ((hFm.comp hY).mul (hIm n)).aestronglyMeasurable (n + c)
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (hFb _)
          rcases hI01 n ω with h | h <;> simp [h])
    have horth : ∫ ω, F (fun i : Fin n ↦ Xn i ω) * (I n ω - p n) ∂P = 0 := by
      simp_rw [mul_sub]
      rw [integral_sub hFI (hFY.mul_const _), integral_mul_const,
        integral_mul_indicator_new_observation_polya P α Xn hurn n F hFm (n + c) hFb]
      simp only [hp, hθ]
      ring
    have hD2 : ∫ ω, (I n ω - p n) ^ 2 ∂P ≤ p n := by
      have hpt (ω : Ω) : (I n ω - p n) ^ 2 = (1 - 2 * p n) * I n ω + p n ^ 2 := by
        rcases hI01 n ω with h | h <;> rw [h] <;> ring
      simp_rw [hpt]
      rw [integral_add ((hIint n).const_mul _) (integrable_const _), integral_const_mul, hEI,
        integral_const]
      simp only [probReal_univ, one_smul]
      nlinarith [hp0 n]
    have hexp (ω : Ω) : ((distinctObservationCount Xn (n + 1) ω : ℝ) -
        ∑ i ∈ Finset.range (n + 1), p i) ^ 2 =
        F (fun i : Fin n ↦ Xn i ω) ^ 2 + 2 * (F (fun i : Fin n ↦ Xn i ω) * (I n ω - p n)) +
          (I n ω - p n) ^ 2 := by
      rw [distinct_observation_count_eq_sum_indicator, Finset.sum_range_succ,
        Finset.sum_range_succ, ← distinct_observation_count_eq_sum_indicator]
      have := hMF ω
      simp only [hI, hA] at this ⊢
      rw [← this]
      ring
    have i1 : Integrable (fun ω ↦ F (fun i : Fin n ↦ Xn i ω) ^ 2) P :=
      Integrable.of_bound ((hFm.comp hY).pow_const 2).aestronglyMeasurable ((n + c) ^ 2)
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hFb _) 2)
    have i2 : Integrable (fun ω ↦ 2 * (F (fun i : Fin n ↦ Xn i ω) * (I n ω - p n))) P :=
      ((hFI.sub (hFY.mul_const (p n))).const_mul 2).congr (ae_of_all _ fun ω ↦ by
        simp only [Pi.sub_apply]; ring)
    have i3 : Integrable (fun ω ↦ (I n ω - p n) ^ 2) P :=
      Integrable.of_bound (((hIm n).sub_const _).pow_const 2).aestronglyMeasurable
        ((1 + p n) ^ 2) (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs, abs_pow]
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          rcases hI01 n ω with h | h <;> rw [h, abs_le] <;> constructor <;> linarith [hp0 n])
    simp_rw [hexp]
    have e1 := integral_add (i1.add i2) i3
    simp only [Pi.add_apply] at e1
    rw [e1, integral_add i1 i2, integral_const_mul, horth, mul_zero, add_zero,
      Finset.sum_range_succ]
    have ih' : ∫ ω, F (fun i : Fin n ↦ Xn i ω) ^ 2 ∂P ≤ c := by
      simpa only [hMF] using ih
    have := hD2
    simp only [hp] at this ih' ⊢
    linarith

/-- Monotone interpolation: if `u ≥ 0` and `L` are monotone, `u / L → l` along a strictly
increasing sequence `sₖ`, and `L(sₖ₊₁) / L(sₖ) → 1`, then `u / L → l`. -/
theorem tendsto_div_of_monotone_of_tendsto_subseq {u L : ℕ → ℝ} {l : ℝ} (hu : Monotone u)
    (hu0 : ∀ m, 0 ≤ u m) (hL : Monotone L) (s : ℕ → ℕ) (hs : StrictMono s)
    (hLpos : ∀ m, s 0 ≤ m → 0 < L m)
    (hsub : Tendsto (fun k ↦ u (s k) / L (s k)) atTop (𝓝 l))
    (hratio : Tendsto (fun k ↦ L (s (k + 1)) / L (s k)) atTop (𝓝 1)) :
    Tendsto (fun m ↦ u m / L m) atTop (𝓝 l) := by
  set κ : ℕ → ℕ := fun m ↦ Nat.findGreatest (fun k ↦ s k ≤ m) m with hκ
  have hsk (k : ℕ) : k ≤ s k := hs.le_apply
  have hκle (m : ℕ) (hm : s 0 ≤ m) : s (κ m) ≤ m :=
    Nat.findGreatest_spec (P := fun k ↦ s k ≤ m) (Nat.zero_le m) hm
  have hκlt (m : ℕ) : m < s (κ m + 1) := by
    by_contra h
    push Not at h
    have h1 : κ m + 1 ≤ m := (hsk _).trans h
    exact Nat.findGreatest_is_greatest (P := fun k ↦ s k ≤ m) (Nat.lt_succ_self _) h1 h
  have hκtop : Tendsto κ atTop atTop := by
    refine tendsto_atTop_atTop.2 fun K ↦ ⟨s K, fun m hm ↦ ?_⟩
    exact Nat.le_findGreatest ((hsk K).trans hm) hm
  have hlo : Tendsto (fun k ↦ u (s k) / L (s (k + 1))) atTop (𝓝 l) := by
    have := hsub.div hratio one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards with k
    have h1 := hLpos (s k) (hs.monotone (Nat.zero_le _)) |>.ne'
    have h2 := hLpos (s (k + 1)) (hs.monotone (Nat.zero_le _)) |>.ne'
    simp only [Pi.div_apply]
    field_simp
  have hhi : Tendsto (fun k ↦ u (s (k + 1)) / L (s k)) atTop (𝓝 l) := by
    have := ((hsub.comp (tendsto_add_atTop_nat 1)).mul hratio)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards with k
    have h1 := hLpos (s k) (hs.monotone (Nat.zero_le _)) |>.ne'
    have h2 := hLpos (s (k + 1)) (hs.monotone (Nat.zero_le _)) |>.ne'
    simp only [Function.comp_apply]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlo.comp hκtop) (hhi.comp hκtop) ?_ ?_
  · filter_upwards [eventually_ge_atTop (s 0)] with m hm
    simp only [Function.comp_apply]
    have hLm := hLpos m hm
    have hLk := hLpos (s (κ m + 1)) (hs.monotone (Nat.zero_le _))
    calc u (s (κ m)) / L (s (κ m + 1)) ≤ u m / L (s (κ m + 1)) :=
          div_le_div_of_nonneg_right (hu (hκle m hm)) hLk.le
      _ ≤ u m / L m := div_le_div_of_nonneg_left (hu0 m) hLm (hL (hκlt m).le)
  · filter_upwards [eventually_ge_atTop (s 0)] with m hm
    simp only [Function.comp_apply]
    have hLm := hLpos m hm
    have hLk := hLpos (s (κ m)) (hs.monotone (Nat.zero_le _))
    calc u m / L m ≤ u (s (κ m + 1)) / L m :=
          div_le_div_of_nonneg_right (hu (hκlt m).le) hLm.le
      _ ≤ u (s (κ m + 1)) / L (s (κ m)) :=
          div_le_div_of_nonneg_left (hu0 _) hLk (hL (hκle m hm))

/-- The sums `∑_{i<n} θ/(θ+i)` are `θ log(n+1)` up to a bounded error, by comparison with the
harmonic numbers. -/
theorem exists_bounds_sum_div_add_log {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      θ * Real.log (n + 1) - D ≤ ∑ i ∈ Finset.range n, θ / (θ + i) ∧
        ∑ i ∈ Finset.range n, θ / (θ + i) ≤ θ * (1 + Real.log (n + 1)) + D := by
  set d : ℕ → ℝ := fun i ↦ θ / (θ + i) - θ / ((i : ℝ) + 1) with hd
  set m := min θ 1 with hm
  have hm0 : 0 < m := lt_min hθ one_pos
  have hdb (i : ℕ) : |d i| ≤ θ * |1 - θ| / m * (1 / (((i + 1 : ℕ) : ℝ)) ^ 2) := by
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h1 : 0 < θ + i := by positivity
    have h2 : (0 : ℝ) < i + 1 := by positivity
    have hge : m * ((i : ℝ) + 1) ≤ θ + i := by
      have := min_le_left θ 1
      have := min_le_right θ 1
      nlinarith
    have heq : d i = θ * (1 - θ) / ((θ + i) * ((i : ℝ) + 1)) := by
      simp only [hd]; field_simp; ring
    rw [heq, abs_div, abs_mul, abs_of_pos hθ, abs_of_pos (mul_pos h1 h2)]
    push_cast
    rw [div_le_iff₀ (mul_pos h1 h2)]
    have : θ * |1 - θ| / m * (1 / ((i : ℝ) + 1) ^ 2) * ((θ + i) * ((i : ℝ) + 1)) ≥
        θ * |1 - θ| / m * (1 / ((i : ℝ) + 1) ^ 2) * (m * ((i : ℝ) + 1) * ((i : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hge h2.le) (by positivity)
    refine le_trans (le_of_eq ?_) this
    field_simp
  have hsum : Summable fun i ↦ |d i| := by
    refine Summable.of_nonneg_of_le (fun i ↦ abs_nonneg _) hdb ?_
    exact ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left _
  refine ⟨∑' i, |d i|, tsum_nonneg fun i ↦ abs_nonneg _, fun n ↦ ?_⟩
  have hdiff : |∑ i ∈ Finset.range n, θ / (θ + i) -
      θ * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)| ≤ ∑' i, |d i| := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_)
      (hsum.sum_le_tsum (Finset.range n) fun i _ ↦ abs_nonneg _))
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hd, mul_one_div]
  have hH : (∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)) = (harmonic n : ℝ) := by
    simp [harmonic, one_div]
  have hlo := log_add_one_le_harmonic n
  have hhi := harmonic_le_one_add_log n
  have hlogn : Real.log n ≤ Real.log (n + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_le_log (by exact_mod_cast hn) (by linarith)
  push_cast at hlo
  rw [hH] at hdiff
  rw [abs_le] at hdiff
  constructor <;> nlinarith

/-- GAPS 104.16: logarithmic almost-sure growth of the number of distinct values.
The logarithm uses `n+1`, which has the same asymptotics and avoids its initial zero argument. -/
theorem ae_tendsto_distinct_observation_count_div_log_polya
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (α : Measure X) [IsFiniteMeasure α]
    [NullSingletonClass α] (hα : α ≠ 0) (Xn : ℕ → Ω → X)
    (hurn : IsPolyaUrnProcess P α Xn) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (distinctObservationCount Xn n ω : ℝ) /
      Real.log (n + 1)) atTop (𝓝 (α.real univ)) := by
  set θ := α.real univ with hθdef
  have hθ : 0 < θ := ENNReal.toReal_pos ((Measure.measure_univ_ne_zero).2 hα) (measure_ne_top _ _)
  obtain ⟨D, hD0, hDb⟩ := exists_bounds_sum_div_add_log hθ
  set c : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, θ / (θ + i) with hc
  set L : ℕ → ℝ := fun n ↦ Real.log (n + 1) with hL
  have hLtop : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hLinv : Tendsto (fun n ↦ (L n)⁻¹) atTop (𝓝 0) := hLtop.inv_tendsto_atTop
  have hLpos1 (n : ℕ) (hn : 1 ≤ n) : 0 < L n := by
    simp only [hL]
    exact Real.log_pos (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith)
  have hclim : Tendsto (fun n ↦ c n / L n) atTop (𝓝 θ) := by
    have hlo : Tendsto (fun n ↦ θ - D * (L n)⁻¹) atTop (𝓝 θ) := by
      simpa using tendsto_const_nhds.sub (hLinv.const_mul D)
    have hhi : Tendsto (fun n ↦ θ + (θ + D) * (L n)⁻¹) atTop (𝓝 θ) := by
      simpa using tendsto_const_nhds.add (hLinv.const_mul (θ + D))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hLn := hLpos1 n hn
      rw [le_div_iff₀ hLn]
      have := (hDb n).1
      have h1 : (θ - D * (L n)⁻¹) * L n = θ * L n - D := by field_simp
      rw [h1]
      exact this
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hLn := hLpos1 n hn
      rw [div_le_iff₀ hLn]
      have := (hDb n).2
      have h1 : (θ + (θ + D) * (L n)⁻¹) * L n = θ * L n + (θ + D) := by field_simp
      rw [h1]
      simp only [hc, hL] at this ⊢
      linarith
  -- The subsequence `s k = 2^((k+1)²)`.
  set s : ℕ → ℕ := fun k ↦ 2 ^ ((k + 1) ^ 2) with hs
  have hsm : StrictMono s := fun a b hab ↦
    Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_left (by omega) (by norm_num))
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hLs (k : ℕ) : ((k : ℝ) + 1) ^ 2 * Real.log 2 ≤ L (s k) ∧
      L (s k) ≤ (((k : ℝ) + 1) ^ 2 + 1) * Real.log 2 := by
    simp only [hL, hs]
    push_cast
    have hp : (1 : ℝ) ≤ 2 ^ ((k + 1) ^ 2) := one_le_pow₀ one_le_two
    have e1 : Real.log ((2 : ℝ) ^ ((k + 1) ^ 2)) = ((k : ℝ) + 1) ^ 2 * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have e2 : Real.log ((2 : ℝ) ^ ((k + 1) ^ 2 + 1)) =
        (((k : ℝ) + 1) ^ 2 + 1) * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    constructor
    · rw [← e1]
      exact Real.log_le_log (by positivity) (by linarith)
    · rw [← e2]
      exact Real.log_le_log (by positivity) (by rw [pow_succ (2 : ℝ) ((k + 1) ^ 2)]; linarith)
  have hLspos (k : ℕ) : 0 < L (s k) :=
    lt_of_lt_of_le (by positivity) (hLs k).1
  -- Chebyshev and Borel–Cantelli along the subsequence.
  set Z : ℕ → Ω → ℝ := fun k ω ↦ (distinctObservationCount Xn (s k) ω : ℝ) - c (s k) with hZ
  have hKm (n : ℕ) : Measurable fun ω ↦ (distinctObservationCount Xn n ω : ℝ) := by
    simp_rw [distinct_observation_count_eq_sum_indicator]
    refine Finset.measurable_sum _ fun i _ ↦ measurable_const.indicator ?_
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_eq_fun (hurn.1 i) (hurn.1 j)).compl
  have hKle (n : ℕ) (ω : Ω) : (distinctObservationCount Xn n ω : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_image_le).trans (by simp)
  have hc0 (n : ℕ) : 0 ≤ c n := Finset.sum_nonneg fun i _ ↦ by positivity
  have hint (k : ℕ) : Integrable (fun ω ↦ Z k ω ^ 2) P := by
    refine Integrable.of_bound (((hKm _).sub_const _).pow_const 2).aestronglyMeasurable
      ((s k + c (s k)) ^ 2) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    simp only [hZ]
    have h1 := hKle (s k) ω
    have h2 := hc0 (s k)
    have h3 : (0 : ℝ) ≤ (distinctObservationCount Xn (s k) ω : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (s k : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hsum : Summable fun k ↦ (∫ ω, Z k ω ^ 2 ∂P) / L (s k) ^ 2 := by
    set B := (θ + D) / Real.log 2 ^ 2 + θ / Real.log 2 with hB
    refine Summable.of_nonneg_of_le (fun k ↦ div_nonneg (integral_nonneg fun ω ↦ sq_nonneg _)
      (sq_nonneg _)) (fun k ↦ ?_) (((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left B)
    have hvar := integral_sq_distinct_observation_count_sub_le_polya P α Xn hurn (s k)
    have hLk := hLspos k
    have ha : 0 < ((k : ℝ) + 1) ^ 2 * Real.log 2 := by positivity
    have hck := (hDb (s k)).2
    simp only [hZ]
    calc (∫ ω, ((distinctObservationCount Xn (s k) ω : ℝ) - c (s k)) ^ 2 ∂P) / L (s k) ^ 2
        ≤ c (s k) / L (s k) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
      _ ≤ (θ * (1 + L (s k)) + D) / L (s k) ^ 2 :=
          div_le_div_of_nonneg_right hck (sq_nonneg _)
      _ = (θ + D) / L (s k) ^ 2 + θ / L (s k) := by field_simp; ring
      _ ≤ (θ + D) / (((k : ℝ) + 1) ^ 2 * Real.log 2) ^ 2 +
            θ / (((k : ℝ) + 1) ^ 2 * Real.log 2) := by
          gcongr
          · exact (hLs k).1
          · exact (hLs k).1
      _ ≤ B * (1 / (((k + 1 : ℕ) : ℝ)) ^ 2) := by
          have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 :=
            one_le_pow₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
          have hk0 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
          have t1 : (θ + D) / (((k : ℝ) + 1) ^ 2 * Real.log 2) ^ 2 ≤
              (θ + D) / Real.log 2 ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
            rw [div_mul_div_comm, mul_one]
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have h5 : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2 :=
              le_mul_of_one_le_right hk0.le hk1
            calc Real.log 2 ^ 2 * ((k : ℝ) + 1) ^ 2
                ≤ Real.log 2 ^ 2 * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2) :=
                  mul_le_mul_of_nonneg_left h5 (by positivity)
              _ = (((k : ℝ) + 1) ^ 2 * Real.log 2) ^ 2 := by ring
          have t2 : θ / (((k : ℝ) + 1) ^ 2 * Real.log 2) =
              θ / Real.log 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
            field_simp
          push_cast
          rw [hB, add_mul]
          linarith
  have hae := ae_tendsto_div_of_summable_integral_sq_div P Z (fun k ↦ L (s k)) hLspos hint hsum
  filter_upwards [hae] with ω hω
  have hsub : Tendsto (fun k ↦ (distinctObservationCount Xn (s k) ω : ℝ) / L (s k)) atTop
      (𝓝 θ) := by
    have := hω.add (hclim.comp hsm.tendsto_atTop)
    rw [zero_add] at this
    refine this.congr fun k ↦ ?_
    simp only [hZ, Function.comp_apply]
    ring
  have hratio : Tendsto (fun k ↦ L (s (k + 1)) / L (s k)) atTop (𝓝 1) := by
    have hq : Tendsto (fun k : ℕ ↦ (1 + 1 / ((k : ℝ) + 1)) ^ 2 + (1 / ((k : ℝ) + 1)) ^ 2)
        atTop (𝓝 ((1 + 0) ^ 2 + 0 ^ 2)) :=
      ((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).pow 2).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2)
    rw [show ((1 : ℝ) + 0) ^ 2 + 0 ^ 2 = 1 by norm_num] at hq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hq (fun k ↦ ?_)
      (fun k ↦ ?_)
    · rw [le_div_iff₀ (hLspos k), one_mul]
      have := hsm.monotone (Nat.le_succ k)
      simp only [hL]
      exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right this 1)
    · rw [div_le_iff₀ (hLspos k)]
      have h1 := (hLs (k + 1)).2
      have h2 := (hLs k).1
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      calc L (s (k + 1)) ≤ ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 + 1) * Real.log 2 := h1
        _ = ((1 + 1 / ((k : ℝ) + 1)) ^ 2 + (1 / ((k : ℝ) + 1)) ^ 2) *
            (((k : ℝ) + 1) ^ 2 * Real.log 2) := by push_cast; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine tendsto_div_of_monotone_of_tendsto_subseq (u := fun n ↦
    (distinctObservationCount Xn n ω : ℝ)) ?_ (fun m ↦ Nat.cast_nonneg _) ?_ s hsm
    (fun m hm ↦ hLpos1 m (le_trans (Nat.one_le_two_pow) hm)) hsub hratio
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    simp only [distinct_observation_count_succ, Nat.cast_add]
    split_ifs <;> simp
  · intro a b hab
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)

/-- No values have been observed before the first sample. -/
@[simp] theorem distinct_observation_count_zero {Ω X : Type*} (Xn : ℕ → Ω → X) (ω : Ω) :
    distinctObservationCount Xn 0 ω = 0 := by simp [distinctObservationCount]

end CKSD
