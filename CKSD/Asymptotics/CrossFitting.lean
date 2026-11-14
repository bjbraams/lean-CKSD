module

public import CKSD.Asymptotics.Statistics

/-!
# Cross-fitted estimation of a missing mean

Asymptotic linearity of the cross-fitted augmented inverse-probability estimator of the mean of
a response that is missing at random (GAPS 102.39).

Cross-fitting uses `SampleSplit`, `crossFittedAverage`, and `missingMeanScore`. Rate
conditions on norms are expressed for `ℝ≥0∞`-valued `L²` norms (`eLpNorm`), so that an
infinite norm cannot be replaced by a junk real value.

## Main definitions

* `CKSD.TendstoInProbabilityZeroENNReal`: convergence to zero in probability of
  `ℝ≥0∞`-valued random quantities.
* `CKSD.missingDataObservation`: the observed part `(R, X, R Y)` of a full-data triple.

## Main results

* `CKSD.crossFittedAverage_missingMean_asymptotically_linear`: asymptotic linearity of the
  cross-fitted estimator (GAPS 102.39).

## Implementation notes

The proof splits each fold sum into a centred part, bounded by Chebyshev's inequality given the
independent training data, and a bias part. Missingness at random makes the bias equal to
`E[(m - m₀)(π - π₀)/π]`, which the Cauchy–Schwarz inequality bounds by the product of the
nuisance errors. No lower bound on the fold sizes is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Convergence to zero in (outer) probability of nonnegative extended-real random quantities.
An infinite value counts as exceeding every threshold. -/
def TendstoInProbabilityZeroENNReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ENNReal.ofReal ε < Y n ω}) atTop (𝓝 0)

/-- Observed part `(R, X, R Y)` of a full-data triple `(R, X, Y)`. -/
def missingDataObservation {X : Type*} (w : Bool × X × ℝ) : Bool × X × ℝ :=
  (w.1, w.2.1, if w.1 then w.2.2 else 0)

section CrossFitting

/-- **Chebyshev's inequality for an i.i.d. fold, given a fixed statistic.** Under a product law
`ν ⊗ Pᶥ`, the centred fold sum `∑ᵢ (G(z, uᵢ) - ∫ G(z, ·) dP)` exceeds `ε` with probability at most
`|ι| η² / ε²` plus the `ν`-probability that `∫ G(z, ·)² dP > η²`. -/
private theorem prod_pi_measure_lt_abs_sum_sub_integral_le {𝒵 Y ι : Type*} [MeasurableSpace 𝒵]
    [MeasurableSpace Y] [Fintype ι] (ν : Measure 𝒵) [IsProbabilityMeasure ν] (P : Measure Y)
    [IsProbabilityMeasure P] (G : 𝒵 × Y → ℝ) (hG : Measurable G) {ε η : ℝ} (hε : 0 < ε) :
    (ν.prod (Measure.pi fun _ : ι ↦ P))
        {p | ∫⁻ y, ENNReal.ofReal (G (p.1, y) ^ 2) ∂P ≤ ENNReal.ofReal (η ^ 2) ∧
          ε < |∑ i, (G (p.1, p.2 i) - ∫ y, G (p.1, y) ∂P)|} ≤
      ENNReal.ofReal (Fintype.card ι * η ^ 2 / ε ^ 2) := by
  set π := Measure.pi fun _ : ι ↦ P with hπ
  have hc : Measurable fun z ↦ ∫ y, G (z, y) ∂P :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  have hq : Measurable fun z ↦ ∫⁻ y, ENNReal.ofReal (G (z, y) ^ 2) ∂P :=
    Measurable.lintegral_prod_right' (f := fun p : 𝒵 × Y ↦ ENNReal.ofReal (G p ^ 2)) (by fun_prop)
  have hE : MeasurableSet {p : 𝒵 × (ι → Y) |
      ∫⁻ y, ENNReal.ofReal (G (p.1, y) ^ 2) ∂P ≤ ENNReal.ofReal (η ^ 2) ∧
        ε < |∑ i, (G (p.1, p.2 i) - ∫ y, G (p.1, y) ∂P)|} := by
    refine (measurableSet_le (hq.comp measurable_fst) measurable_const).inter
      (measurableSet_lt (measurable_const (a := ε)) ?_)
    have : ∀ i : ι, Measurable fun p : 𝒵 × (ι → Y) ↦ G (p.1, p.2 i) - ∫ y, G (p.1, y) ∂P :=
      fun i ↦ (hG.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp
        measurable_snd))).sub (hc.comp measurable_fst)
    exact continuous_abs.measurable.comp (Finset.measurable_fun_sum _ fun i _ ↦ this i)
  rw [Measure.prod_apply hE]
  calc ∫⁻ z, π (Prod.mk z ⁻¹' _) ∂ν ≤ ∫⁻ _, ENNReal.ofReal (Fintype.card ι * η ^ 2 / ε ^ 2) ∂ν :=
        lintegral_mono fun z ↦ ?_
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  by_cases hz : ∫⁻ y, ENNReal.ofReal (G (z, y) ^ 2) ∂P ≤ ENNReal.ofReal (η ^ 2)
  swap
  · have : Prod.mk z ⁻¹' {p : 𝒵 × (ι → Y) |
        ∫⁻ y, ENNReal.ofReal (G (p.1, y) ^ 2) ∂P ≤ ENNReal.ofReal (η ^ 2) ∧
          ε < |∑ i, (G (p.1, p.2 i) - ∫ y, G (p.1, y) ∂P)|} = ∅ := by
      ext u; simp [hz]
    rw [this, measure_empty]; exact bot_le
  set g : Y → ℝ := fun y ↦ G (z, y) with hg
  have hgm : Measurable g := hG.comp measurable_prodMk_left
  have hfin : ∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂P < ∞ := hz.trans_lt ENNReal.ofReal_lt_top
  have hg2 : MemLp g 2 P := by
    rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable]
    refine ⟨(hgm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y ↦ sq_nonneg (g y))]
    exact hfin
  have hgsq : ∫ y, g y ^ 2 ∂P ≤ η ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ sq_nonneg (g y))
      (hgm.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg η) hz
  set X : ι → (ι → Y) → ℝ := fun i u ↦ g (u i) with hX
  have hev : ∀ i, MeasurePreserving (Function.eval i) π P := fun i ↦
    measurePreserving_eval (fun _ ↦ P) i
  have hX2 : ∀ i, MemLp (X i) 2 π := fun i ↦ hg2.comp_measurePreserving (hev i)
  have hXint : ∀ i, ∫ u, X i u ∂π = ∫ y, g y ∂P := fun i ↦ by
    rw [← (hev i).map_eq]
    exact (integral_map (hev i).measurable.aemeasurable
      (by rw [(hev i).map_eq]; exact hgm.aestronglyMeasurable)).symm
  have hXsq : ∀ i, ∫ u, X i u ^ 2 ∂π = ∫ y, g y ^ 2 ∂P := fun i ↦ by
    rw [← (hev i).map_eq]
    exact (integral_map (hev i).measurable.aemeasurable
      (by rw [(hev i).map_eq]; exact (hgm.pow_const 2).aestronglyMeasurable)).symm
  have hind : iIndepFun X π := iIndepFun_pi (fun _ ↦ hgm.aemeasurable)
  have hvar : variance (∑ i, X i) π ≤ Fintype.card ι * η ^ 2 := by
    rw [IndepFun.variance_sum (fun i _ ↦ hX2 i) (fun i _ j _ hij ↦ hind.indepFun hij)]
    calc ∑ i, variance (X i) π ≤ ∑ _i : ι, η ^ 2 := Finset.sum_le_sum fun i _ ↦ by
          refine (variance_le_expectation_sq (hX2 i).aestronglyMeasurable).trans ?_
          simp only [Pi.pow_apply]
          rw [hXsq i]; exact hgsq
      _ = _ := by simp
  have hmean : ∫ u, (∑ i, X i) u ∂π = Fintype.card ι * ∫ y, g y ∂P := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hX2 i).integrable one_le_two]
    simp [hXint]
  have hsum2 : MemLp (∑ i, X i) 2 π := memLp_finsetSum' _ fun i _ ↦ hX2 i
  refine (measure_mono fun u hu ↦ ?_).trans ((meas_ge_le_variance_div_sq hsum2 hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε))))
  simp only [mem_preimage, mem_ofPred_eq] at hu ⊢
  rw [hmean, Finset.sum_apply]
  refine hu.2.le.trans_eq ?_
  simp [hX, hg, Finset.sum_sub_distrib]

/-- **Chebyshev's inequality for a cross-fitting fold.** For an i.i.d. sequence, a fold `A` of
`Fin n` and a training set `Tr` disjoint from it, let `Z` be the training data. For a jointly
measurable `G`, the centred fold sum `∑_{i ∈ A} (G(Z, Wᵢ) - ∫ G(Z, ·) dP)` exceeds `ε` with
probability at most `|A| η² / ε²` plus the probability that `∫ G(Z, ·)² dP > η²`. -/
private theorem measure_lt_abs_fold_sum_sub_integral_le {Ω Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Y)
    [IsProbabilityMeasure P] (W : ℕ → Ω → Y) (hiid : IsIndependentIdenticallyDistributed μ W P)
    {n : ℕ} (A : Finset (Fin n)) (Tr : Set (Fin n)) (hdisj : ∀ i ∈ A, i ∉ Tr)
    (G : (Tr → Y) × Y → ℝ) (hG : Measurable G) {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    μ {ω | ε < |∑ i ∈ A, (G ((fun j : Tr ↦ W j.val.val ω), W i.val ω) -
        ∫ y, G ((fun j : Tr ↦ W j.val.val ω), y) ∂P)|} ≤
      μ {ω | ENNReal.ofReal (η ^ 2) <
          ∫⁻ y, ENNReal.ofReal (G ((fun j : Tr ↦ W j.val.val ω), y) ^ 2) ∂P} +
        ENNReal.ofReal (A.card * η ^ 2 / ε ^ 2) := by
  classical
  obtain ⟨hWm, hind, hlaw⟩ := hiid
  set S : Finset ℕ := (Finset.univ.filter (· ∈ Tr)).map Fin.valEmbedding with hSdef
  set T : Finset ℕ := A.map Fin.valEmbedding with hTdef
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a haS haT
    simp only [hSdef, hTdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at haS haT
    obtain ⟨i, hi, rfl⟩ := haS
    obtain ⟨j, hj, hji⟩ := haT
    exact hdisj j hj (Fin.ext hji ▸ hi)
  have hmemS : ∀ j : Tr, j.val.val ∈ S := fun j ↦ by
    simp only [hSdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    exact ⟨j.val, j.prop, rfl⟩
  set ZS : Ω → (S → Y) := fun ω s ↦ W s ω with hZS
  set UT : Ω → (T → Y) := fun ω t ↦ W t ω with hUT
  have hZSm : Measurable ZS := measurable_pi_iff.2 fun s ↦ hWm s
  have hUTm : Measurable UT := measurable_pi_iff.2 fun t ↦ hWm t
  set Ψ : (S → Y) → (Tr → Y) := fun z j ↦ z ⟨j.val.val, hmemS j⟩ with hΨ
  have hΨm : Measurable Ψ := measurable_pi_iff.2 fun j ↦ measurable_pi_apply _
  set G' : (S → Y) × Y → ℝ := fun p ↦ G (Ψ p.1, p.2) with hG'
  have hG'm : Measurable G' := hG.comp ((hΨm.comp measurable_fst).prodMk measurable_snd)
  -- The joint law of training data and fold data is a product.
  have hindST : IndepFun ZS UT μ := hind.indepFun_finset S T hST hWm
  have hUind : iIndepFun (fun t : T ↦ W t) μ := hind.precomp Subtype.val_injective
  have hUlaw : μ.map UT = Measure.pi fun _ : T ↦ P := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun t : T ↦ (hWm t).aemeasurable)).1 hUind]
    simp only [hlaw]
  have hjoint : μ.map (fun ω ↦ (ZS ω, UT ω)) = (μ.map ZS).prod (Measure.pi fun _ : T ↦ P) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZSm.aemeasurable hUTm.aemeasurable).1 hindST,
      hUlaw]
  set E : Set ((S → Y) × (T → Y)) := {p | ∫⁻ y, ENNReal.ofReal (G' (p.1, y) ^ 2) ∂P ≤
      ENNReal.ofReal (η ^ 2) ∧ ε < |∑ t, (G' (p.1, p.2 t) - ∫ y, G' (p.1, y) ∂P)|} with hEdef
  have hbound := prod_pi_measure_lt_abs_sum_sub_integral_le (ι := T) (μ.map ZS) P G' hG'm hε
    (η := η)
  have hEm : MeasurableSet E := by
    have hc : Measurable fun z ↦ ∫ y, G' (z, y) ∂P :=
      hG'm.stronglyMeasurable.integral_prod_right'.measurable
    have hq : Measurable fun z ↦ ∫⁻ y, ENNReal.ofReal (G' (z, y) ^ 2) ∂P :=
      Measurable.lintegral_prod_right' (f := fun p ↦ ENNReal.ofReal (G' p ^ 2)) (by fun_prop)
    refine (measurableSet_le (hq.comp measurable_fst) measurable_const).inter
      (measurableSet_lt (measurable_const (a := ε)) ?_)
    have : ∀ t : T, Measurable fun p : (S → Y) × (T → Y) ↦
        G' (p.1, p.2 t) - ∫ y, G' (p.1, y) ∂P :=
      fun t ↦ (hG'm.comp (measurable_fst.prodMk ((measurable_pi_apply t).comp
        measurable_snd))).sub (hc.comp measurable_fst)
    exact continuous_abs.measurable.comp (Finset.measurable_fun_sum _ fun t _ ↦ this t)
  have hZ : ∀ ω, (fun j : Tr ↦ W j.val.val ω) = Ψ (ZS ω) := fun ω ↦ rfl
  have hsum : ∀ ω, ∑ i ∈ A, (G ((fun j : Tr ↦ W j.val.val ω), W i.val ω) -
      ∫ y, G ((fun j : Tr ↦ W j.val.val ω), y) ∂P) =
      ∑ t : T, (G' (ZS ω, UT ω t) - ∫ y, G' (ZS ω, y) ∂P) := fun ω ↦ by
    rw [Finset.sum_coe_sort T (fun t ↦ G' (ZS ω, W t ω) - ∫ y, G' (ZS ω, y) ∂P), hTdef,
      Finset.sum_map]
    rfl
  have hsub : {ω | ε < |∑ i ∈ A, (G ((fun j : Tr ↦ W j.val.val ω), W i.val ω) -
        ∫ y, G ((fun j : Tr ↦ W j.val.val ω), y) ∂P)|} ⊆
      {ω | ENNReal.ofReal (η ^ 2) <
          ∫⁻ y, ENNReal.ofReal (G ((fun j : Tr ↦ W j.val.val ω), y) ^ 2) ∂P} ∪
        (fun ω ↦ (ZS ω, UT ω)) ⁻¹' E := by
    intro ω hω
    by_cases h : ENNReal.ofReal (η ^ 2) <
        ∫⁻ y, ENNReal.ofReal (G ((fun j : Tr ↦ W j.val.val ω), y) ^ 2) ∂P
    · exact Or.inl h
    · refine Or.inr ⟨not_lt.1 h, ?_⟩
      simp only [mem_ofPred_eq] at hω
      rw [hsum ω] at hω
      exact hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := by
      gcongr
      rw [← Measure.map_apply (hZSm.prodMk hUTm) hEm, hjoint]
      have hcard : (Fintype.card T : ℝ) = A.card := by
        rw [Fintype.card_coe, hTdef, Finset.card_map]
      rw [← hcard]
      exact hbound


variable {X : Type*} [MeasurableSpace X]

/-- **Missing at random as a density identity.** If the response is missing at random with
propensity `π₀ ≥ 0`, the law of `(X, Y)` on the event `R = 1` has density `π₀(x)` with respect to
the law of `(X, Y)`. -/
private theorem map_restrict_observed_eq_withDensity (P : Measure (Bool × X × ℝ))
    [IsProbabilityMeasure P] (π₀ : X → ℝ) (hπ₀m : Measurable π₀) (hπ₀0 : ∀ x, 0 ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P) :
    (P.restrict {w | w.1 = true}).map (fun w ↦ (w.2.1, w.2.2)) =
      (P.map fun w ↦ (w.2.1, w.2.2)).withDensity fun p ↦ ENNReal.ofReal (π₀ p.1) := by
  set q : Bool × X × ℝ → X × ℝ := fun w ↦ (w.2.1, w.2.2) with hq
  have hqm : Measurable q := by fun_prop
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  have hdm : Measurable fun p : X × ℝ ↦ ENNReal.ofReal (π₀ p.1) := by fun_prop
  set C : ℕ → Set X := fun M ↦ {x | π₀ x ≤ M} with hC
  have hCm : ∀ M, MeasurableSet (C M) := fun M ↦ measurableSet_le hπ₀m measurable_const
  -- Agreement on rectangles inside a truncation set.
  have hrect : ∀ M A B, MeasurableSet A → MeasurableSet B → A ⊆ C M →
      (P.restrict {w | w.1 = true}).map q (A ×ˢ B) =
        ((P.map q).withDensity fun p ↦ ENNReal.ofReal (π₀ p.1)) (A ×ˢ B) := by
    intro M A B hA hB hAC
    have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
    have hpre : q ⁻¹' (A ×ˢ B) = {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B} := rfl
    rw [Measure.map_apply hqm hAB, Measure.restrict_apply (hqm hAB), withDensity_apply _ hAB,
      setLIntegral_map hAB hdm hqm, hpre]
    have hint : IntegrableOn (fun w : Bool × X × ℝ ↦ π₀ w.2.1)
        {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B} P := by
      refine Measure.integrableOn_of_bounded (M := M) (measure_ne_top _ _)
        (hπ₀m.comp (by fun_prop)).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem (hpre ▸ hqm hAB) fun w hw ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ₀0 _)]
      exact hAC hw.1
    have hset : {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B} ∩ {w | w.1 = true} =
        {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} := by
      ext w; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
    rw [hset, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun w ↦ hπ₀0 _), ← hmar A B hA hB, ofReal_measureReal]
  -- Agreement after truncation.
  have htrunc : ∀ M, ((P.restrict {w | w.1 = true}).map q).restrict (C M ×ˢ univ) =
      ((P.map q).withDensity fun p ↦ ENNReal.ofReal (π₀ p.1)).restrict (C M ×ˢ univ) := by
    intro M
    have hCM : MeasurableSet (C M ×ˢ (univ : Set ℝ)) := (hCm M).prod MeasurableSet.univ
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [Measure.restrict_apply ((show MeasurableSet A from hA).prod hB),
        Measure.restrict_apply ((show MeasurableSet A from hA).prod hB),
        prod_inter_prod, inter_univ]
      exact hrect M _ _ ((show MeasurableSet A from hA).inter (hCm M)) hB inter_subset_right
    · rw [Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
        univ_inter]
      exact hrect M _ _ (hCm M) MeasurableSet.univ subset_rfl
  ext E hE
  have hmono : Monotone fun M : ℕ ↦ E ∩ (C M ×ˢ univ) := fun a b hab ↦
    inter_subset_inter_right _ (prod_mono (fun x hx ↦ (hx.trans (by exact_mod_cast hab) :
      π₀ x ≤ b)) subset_rfl)
  have hU : (⋃ M : ℕ, E ∩ (C M ×ˢ univ)) = E := by
    refine Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_left) fun p hp ↦ ?_
    obtain ⟨M, hM⟩ := exists_nat_ge (π₀ p.1)
    exact mem_iUnion.2 ⟨M, hp, hM, mem_univ _⟩
  have h1 := tendsto_measure_iUnion_atTop
    (μ := (P.restrict {w | w.1 = true}).map q) hmono
  have h2 := tendsto_measure_iUnion_atTop
    (μ := (P.map q).withDensity fun p ↦ ENNReal.ofReal (π₀ p.1)) hmono
  rw [hU] at h1 h2
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun M ↦ ?_
  have := congrArg (fun ν : Measure (X × ℝ) ↦ ν E) (htrunc M)
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE] at this
  exact this.symm

/-- **Transfer from the observed event to the propensity.** Under missingness at random,
`E[1{R = 1} F(X, Y)] = E[π₀(X) F(X, Y)]` for every measurable `F`, and either side is integrable
exactly when the other one is. -/
private theorem integral_ite_observed_eq (P : Measure (Bool × X × ℝ))
    [IsProbabilityMeasure P] (π₀ : X → ℝ) (hπ₀m : Measurable π₀) (hπ₀0 : ∀ x, 0 ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P)
    (F : X × ℝ → ℝ) (hF : Measurable F) :
    (∫ w, (if w.1 = true then F (w.2.1, w.2.2) else 0) ∂P) =
        ∫ w, π₀ w.2.1 * F (w.2.1, w.2.2) ∂P ∧
      (Integrable (fun w ↦ if w.1 = true then F (w.2.1, w.2.2) else 0) P ↔
        Integrable (fun w ↦ π₀ w.2.1 * F (w.2.1, w.2.2)) P) := by
  set q : Bool × X × ℝ → X × ℝ := fun w ↦ (w.2.1, w.2.2) with hq
  have hqm : Measurable q := by fun_prop
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  have heq : (P.restrict {w | w.1 = true}).map q =
      (P.map q).withDensity fun p ↦ (((π₀ p.1).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    map_restrict_observed_eq_withDensity P π₀ hπ₀m hπ₀0 hmar
  have hdm : Measurable fun p : X × ℝ ↦ (π₀ p.1).toNNReal := by fun_prop
  have hind : (fun w : Bool × X × ℝ ↦ if w.1 = true then F (w.2.1, w.2.2) else 0) =
      {w | w.1 = true}.indicator (F ∘ q) := by
    ext w; by_cases h : w.1 = true <;> simp [h, hq]
  have hsm : (fun w : Bool × X × ℝ ↦ π₀ w.2.1 * F (w.2.1, w.2.2)) =
      (fun p : X × ℝ ↦ (π₀ p.1).toNNReal • F p) ∘ q := by
    ext w; simp [hq, NNReal.smul_def, Real.coe_toNNReal _ (hπ₀0 _)]
  rw [hind, hsm]
  constructor
  · rw [integral_indicator hS]
    calc ∫ w in {w | w.1 = true}, (F ∘ q) w ∂P = ∫ p, F p ∂((P.restrict _).map q) :=
          (integral_map hqm.aemeasurable hF.aestronglyMeasurable).symm
      _ = ∫ p, (π₀ p.1).toNNReal • F p ∂(P.map q) := by
          rw [heq, integral_withDensity_eq_integral_smul hdm]
      _ = _ := integral_map hqm.aemeasurable (by fun_prop)
  · rw [integrable_indicator_iff hS, IntegrableOn,
      ← integrable_map_measure hF.aestronglyMeasurable hqm.aemeasurable, heq,
      integrable_withDensity_iff_integrable_smul hdm,
      integrable_map_measure (by fun_prop) hqm.aemeasurable]

/-- A truncation bound for a positive part: if `∫_{0 ≤ g ≤ M} g ≤ C` for every `M`, then
`∫⁻ g⁺ ≤ C`. -/
private theorem lintegral_ofReal_le_of_setIntegral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ M : ℕ, ∫ w in {w | 0 ≤ g w ∧ g w ≤ M}, g w ∂μ ≤ C) :
    ∫⁻ w, ENNReal.ofReal (g w) ∂μ ≤ ENNReal.ofReal C := by
  set s : ℕ → Set Ω := fun M ↦ {w | 0 ≤ g w ∧ g w ≤ M} with hsdef
  have hs : ∀ M, MeasurableSet (s M) := fun M ↦
    (measurableSet_le measurable_const hg).inter (measurableSet_le hg measurable_const)
  have hsup : ∀ w, ENNReal.ofReal (g w) =
      ⨆ M : ℕ, (s M).indicator (fun w ↦ ENNReal.ofReal (g w)) w := by
    intro w
    refine le_antisymm ?_ (iSup_le fun M ↦ indicator_le_self _ _ w)
    by_cases h0 : 0 ≤ g w
    · obtain ⟨M, hM⟩ := exists_nat_ge (g w)
      exact le_iSup_of_le M (by rw [indicator_of_mem (show w ∈ s M from ⟨h0, hM⟩)])
    · rw [ENNReal.ofReal_of_nonpos (not_le.1 h0).le]; exact bot_le
  have hmono : Monotone fun M : ℕ ↦ (s M).indicator (fun w ↦ ENNReal.ofReal (g w)) := by
    intro a b hab w
    refine indicator_le_indicator_of_subset ?_ (fun _ ↦ bot_le) w
    intro x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast hab)⟩
  rw [lintegral_congr hsup, lintegral_iSup (fun M ↦ (by fun_prop : Measurable fun w ↦
      ENNReal.ofReal (g w)).indicator (hs M)) hmono]
  refine iSup_le fun M ↦ ?_
  rw [lintegral_indicator (hs M), ← ofReal_integral_eq_lintegral_ofReal ?_
    (ae_restrict_of_forall_mem (hs M) fun w hw ↦ hw.1)]
  · exact ENNReal.ofReal_le_ofReal (hC M)
  · refine Measure.integrableOn_of_bounded (M := M) (measure_ne_top _ _) hg.aestronglyMeasurable
      (ae_restrict_of_forall_mem (hs M) fun w hw ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2

/-- A function `m₀` satisfying the regression identities `∫_{X ∈ A} Y = ∫_{X ∈ A} m₀(X)` for an
integrable response is itself integrable. -/
private theorem integrable_of_regression (P : Measure (Bool × X × ℝ)) [IsProbabilityMeasure P]
    (hYi : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) P) (m₀ : X → ℝ) (hm₀m : Measurable m₀)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P) :
    Integrable (fun w : Bool × X × ℝ ↦ m₀ w.2.1) P := by
  have hgm : Measurable fun w : Bool × X × ℝ ↦ m₀ w.2.1 := by fun_prop
  have hbound : ∀ A, MeasurableSet A → |∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P| ≤
      ∫ w, |w.2.2| ∂P := fun A _ ↦
    (abs_integral_le_integral_abs).trans (setIntegral_le_integral hYi.abs
      (Eventually.of_forall fun _ ↦ abs_nonneg _))
  have hpos : ∫⁻ w, ENNReal.ofReal (m₀ w.2.1) ∂P ≤ ENNReal.ofReal (∫ w, |w.2.2| ∂P) := by
    refine lintegral_ofReal_le_of_setIntegral_le hgm fun M ↦ ?_
    have hA : MeasurableSet {x | 0 ≤ m₀ x ∧ m₀ x ≤ M} :=
      (measurableSet_le measurable_const hm₀m).inter (measurableSet_le hm₀m measurable_const)
    have hset : {w : Bool × X × ℝ | w.2.1 ∈ {x | 0 ≤ m₀ x ∧ m₀ x ≤ M}} =
        {w | 0 ≤ m₀ w.2.1 ∧ m₀ w.2.1 ≤ M} := rfl
    rw [← hset, ← hreg _ hA]
    exact (le_abs_self _).trans (hbound _ hA)
  have hneg : ∫⁻ w, ENNReal.ofReal (-m₀ w.2.1) ∂P ≤ ENNReal.ofReal (∫ w, |w.2.2| ∂P) := by
    have hnm : Measurable fun w : Bool × X × ℝ ↦ -m₀ w.2.1 := by fun_prop
    refine lintegral_ofReal_le_of_setIntegral_le hnm fun M ↦ ?_
    have hA : MeasurableSet {x | 0 ≤ -m₀ x ∧ -m₀ x ≤ M} :=
      (measurableSet_le measurable_const hm₀m.neg).inter
        (measurableSet_le hm₀m.neg measurable_const)
    have hset : {w : Bool × X × ℝ | w.2.1 ∈ {x | 0 ≤ -m₀ x ∧ -m₀ x ≤ M}} =
        {w | 0 ≤ -m₀ w.2.1 ∧ -m₀ w.2.1 ≤ M} := rfl
    rw [← hset, integral_neg, ← hreg _ hA]
    exact (neg_le_abs _).trans (hbound _ hA)
  refine ⟨hgm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hsplit : ∀ w : Bool × X × ℝ, ‖m₀ w.2.1‖ₑ =
      ENNReal.ofReal (m₀ w.2.1) + ENNReal.ofReal (-m₀ w.2.1) := by
    intro w
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (m₀ w.2.1) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  rw [lintegral_congr hsplit, lintegral_add_left (by fun_prop)]
  exact ENNReal.add_lt_top.2 ⟨hpos.trans_lt ENNReal.ofReal_lt_top,
    hneg.trans_lt ENNReal.ofReal_lt_top⟩

/-- **Regression identity for a function of the covariate.** If `m₀(X)` satisfies the
regression identities on all covariate events, then `E[f(X) Y] = E[f(X) m₀(X)]` whenever
`f(X) Y` is integrable. -/
private theorem integral_mul_response_eq (P : Measure (Bool × X × ℝ)) [IsProbabilityMeasure P]
    (hYi : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) P) (m₀ : X → ℝ) (hm₀m : Measurable m₀)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P)
    (f : X → ℝ) (hf : Measurable f)
    (hfY : Integrable (fun w : Bool × X × ℝ ↦ f w.2.1 * w.2.2) P) :
    ∫ w, f w.2.1 * w.2.2 ∂P = ∫ w, f w.2.1 * m₀ w.2.1 ∂P := by
  have hX : Measurable fun w : Bool × X × ℝ ↦ w.2.1 := by fun_prop
  have hm₀i := integrable_of_regression P hYi m₀ hm₀m hreg
  have hmX := hX.comap_le
  have hXm : Measurable[MeasurableSpace.comap (fun w : Bool × X × ℝ ↦ w.2.1)
      (inferInstance : MeasurableSpace X)] fun w : Bool × X × ℝ ↦ w.2.1 := comap_measurable _
  have hce : (fun w : Bool × X × ℝ ↦ m₀ w.2.1) =ᵐ[P]
      P[fun w ↦ w.2.2 | MeasurableSpace.comap (fun w : Bool × X × ℝ ↦ w.2.1)
        (inferInstance : MeasurableSpace X)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (g := fun w ↦ m₀ w.2.1) hmX hYi
      (fun s _ _ ↦ hm₀i.integrableOn) (fun s hs _ ↦ ?_)
      (hm₀m.comp hXm).stronglyMeasurable.aestronglyMeasurable
    obtain ⟨A, hA, rfl⟩ := hs
    exact (hreg A hA).symm
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := MeasurableSpace.comap (fun w : Bool × X × ℝ ↦ w.2.1)
      (inferInstance : MeasurableSpace X)) (μ := P)
    (f := fun w : Bool × X × ℝ ↦ f w.2.1) (g := fun w ↦ w.2.2)
    (hf.comp hXm).stronglyMeasurable (by exact hfY) hYi
  rw [← integral_condExp hmX]
  calc _ = ∫ w, ((fun w : Bool × X × ℝ ↦ f w.2.1) * P[fun w ↦ w.2.2 |
        MeasurableSpace.comap (fun w : Bool × X × ℝ ↦ w.2.1)
          (inferInstance : MeasurableSpace X)]) w ∂P := integral_congr_ae hpull
    _ = _ := integral_congr_ae (by filter_upwards [hce] with w h; simp [← h])

/-- Hölder's inequality for a weighted product of covariate functions: if `π ≥ δ > 0`, then
`‖E[u(X) v(X)/π(X)]‖ ≤ δ⁻¹ ‖u‖_{L²(P_X)} ‖v‖_{L²(P_X)}`. -/
private theorem enorm_integral_comp_mul_div_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Xv : Ω → X} (hX : Measurable Xv) {u v π : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hπ : Measurable π) {δ : ℝ} (hδ : 0 < δ) (hπδ : ∀ x, δ ≤ π x) :
    ‖∫ w, u (Xv w) * (v (Xv w) / π (Xv w)) ∂P‖ₑ ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm u 2 (P.map Xv) * eLpNorm v 2 (P.map Xv) := by
  have hπ0 : ∀ x, 0 < π x := fun x ↦ hδ.trans_le (hπδ x)
  calc ‖∫ w, u (Xv w) * (v (Xv w) / π (Xv w)) ∂P‖ₑ
      ≤ ∫⁻ w, ‖u (Xv w) * (v (Xv w) / π (Xv w))‖ₑ ∂P := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x, ‖u x * (v x / π x)‖ₑ ∂(P.map Xv) :=
        (lintegral_map (f := fun x ↦ ‖u x * (v x / π x)‖ₑ) (by fun_prop) hX).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal δ⁻¹ * ‖u x * v x‖ₑ ∂(P.map Xv) := by
        refine lintegral_mono fun x ↦ ?_
        rw [mul_div_assoc', div_eq_mul_one_div, enorm_mul (u x * v x), mul_comm]
        gcongr
        rw [Real.enorm_eq_ofReal_abs, abs_of_pos (one_div_pos.2 (hπ0 x)), one_div]
        exact ENNReal.ofReal_le_ofReal (inv_anti₀ hδ (hπδ x))
    _ = ENNReal.ofReal δ⁻¹ * eLpNorm (fun x ↦ u x * v x) 1 (P.map Xv) := by
        rw [lintegral_const_mul _ (by fun_prop),
          eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
    _ ≤ ENNReal.ofReal δ⁻¹ * (eLpNorm u 2 (P.map Xv) * eLpNorm v 2 (P.map Xv)) := by
        gcongr
        have := eLpNorm_le_eLpNorm_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := P.map Xv)
          (fun a b : ℝ ↦ a * b) 1 continuous_mul hu.aestronglyMeasurable
          hv.aestronglyMeasurable (Eventually.of_forall fun x ↦ by simp [nnnorm_mul])
        simpa using this
    _ = _ := by rw [mul_assoc]

/-- **Bias of the augmented inverse-probability score.** Under missingness at random, for
nuisance values `(m, π)` with `π ≥ δ` and `m - m₀, π - π₀ ∈ L²(P_X)`, the mean of the difference
of the scores at `(m, π)` and `(m₀, π₀)` is `E[(m - m₀)(π - π₀)/π](X)`, so it is bounded by
`δ⁻¹ ‖m - m₀‖₂ ‖π - π₀‖₂`. -/
private theorem enorm_integral_missingMeanScore_sub_le (P : Measure (Bool × X × ℝ))
    [IsProbabilityMeasure P] (hY : MemLp (fun w : Bool × X × ℝ ↦ w.2.2) 2 P)
    (π₀ m₀ : X → ℝ) (hπ₀m : Measurable π₀) (hm₀m : Measurable m₀) {δ : ℝ} (hδ : 0 < δ)
    (hπ₀ : ∀ x, δ ≤ π₀ x)
    (hmar : ∀ A B, MeasurableSet A → MeasurableSet B →
      P.real {w | w.1 = true ∧ w.2.1 ∈ A ∧ w.2.2 ∈ B} =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A ∧ w.2.2 ∈ B}, π₀ w.2.1 ∂P)
    (hreg : ∀ A, MeasurableSet A →
      (∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, w.2.2 ∂P) =
        ∫ w in {w : Bool × X × ℝ | w.2.1 ∈ A}, m₀ w.2.1 ∂P)
    (m π : X → ℝ) (hm : Measurable m) (hπ : Measurable π) (hπδ : ∀ x, δ ≤ π x)
    (hu : eLpNorm (fun x ↦ m x - m₀ x) 2 (P.map fun w ↦ w.2.1) < ∞) :
    ‖∫ w, (missingMeanScore m π w.2.1 w.1 w.2.2 - missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2) ∂P‖ₑ ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm (fun x ↦ m x - m₀ x) 2 (P.map fun w ↦ w.2.1) *
        eLpNorm (fun x ↦ π x - π₀ x) 2 (P.map fun w ↦ w.2.1) := by
  have hX : Measurable fun w : Bool × X × ℝ ↦ w.2.1 := by fun_prop
  have hYi : Integrable (fun w : Bool × X × ℝ ↦ w.2.2) P := hY.integrable one_le_two
  have hπ₀0 : ∀ x, 0 ≤ π₀ x := fun x ↦ hδ.le.trans (hπ₀ x)
  have hπ0 : ∀ x, 0 < π x := fun x ↦ hδ.trans_le (hπδ x)
  have hπ₀p : ∀ x, 0 < π₀ x := fun x ↦ hδ.trans_le (hπ₀ x)
  set u : X → ℝ := fun x ↦ m x - m₀ x with hudef
  set k : X → ℝ := fun x ↦ 1 / π x - 1 / π₀ x with hkdef
  have hum : Measurable u := hm.sub hm₀m
  have hkm : Measurable k := (measurable_const.div hπ).sub (measurable_const.div hπ₀m)
  have hinv : ∀ x, 1 / π x ≤ δ⁻¹ := fun x ↦ by
    rw [one_div]; exact inv_anti₀ hδ (hπδ x)
  have hinv₀ : ∀ x, 1 / π₀ x ≤ δ⁻¹ := fun x ↦ by
    rw [one_div]; exact inv_anti₀ hδ (hπ₀ x)
  have hkb : ∀ x, ‖k x‖ ≤ δ⁻¹ := fun x ↦ by
    have h1 : 0 < 1 / π x := one_div_pos.2 (hπ0 x)
    have h2 : 0 < 1 / π₀ x := one_div_pos.2 (hπ₀p x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hinv x, hinv₀ x]
  have huX : MemLp u 2 (P.map fun w ↦ w.2.1) := hu
  have huL : MemLp (fun w : Bool × X × ℝ ↦ u w.2.1) 2 P :=
    (memLp_map_measure_iff hum.aestronglyMeasurable hX.aemeasurable).1 huX
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  have hui : Integrable (fun w : Bool × X × ℝ ↦ u w.2.1) P := huL.integrable one_le_two
  have hm₀i := integrable_of_regression P hYi m₀ hm₀m hreg
  have htr := integral_ite_observed_eq P π₀ hπ₀m hπ₀0 hmar
  -- The first part: `u(X) (1 - R/π(X))`.
  have hF1 : Measurable fun p : X × ℝ ↦ u p.1 / π p.1 := by fun_prop
  have hA1 : Integrable (fun w : Bool × X × ℝ ↦ if w.1 = true then u w.2.1 / π w.2.1 else 0)
      P := by
    refine (hui.norm.const_mul δ⁻¹).mono'
      ((Measurable.ite hS (by fun_prop) measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun w ↦ ?_)
    split_ifs
    · rw [norm_div, Real.norm_eq_abs (π _), abs_of_pos (hπ0 _), div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (hinv _) (norm_nonneg _)
    · rw [norm_zero]; positivity
  have hA1' := (htr _ hF1).2.1 hA1
  -- The second part: `R (Y - m₀(X)) k(X)`.
  have hF2 : Measurable fun p : X × ℝ ↦ (p.2 - m₀ p.1) * k p.1 := by fun_prop
  have hA2 : Integrable (fun w : Bool × X × ℝ ↦
      if w.1 = true then (w.2.2 - m₀ w.2.1) * k w.2.1 else 0) P := by
    refine ((hYi.sub hm₀i).norm.const_mul δ⁻¹).mono'
      ((Measurable.ite hS (by fun_prop) measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.sub_apply]
    split_ifs
    · rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hkb _) (norm_nonneg _)
    · rw [norm_zero]; positivity
  have hA2' := (htr _ hF2).2.1 hA2
  have hF3 : Measurable fun p : X × ℝ ↦ m₀ p.1 * k p.1 := by fun_prop
  have hA3 : Integrable (fun w : Bool × X × ℝ ↦ if w.1 = true then m₀ w.2.1 * k w.2.1 else 0)
      P := by
    refine (hm₀i.norm.const_mul δ⁻¹).mono'
      ((Measurable.ite hS (by fun_prop) measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun w ↦ ?_)
    split_ifs
    · rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hkb _) (norm_nonneg _)
    · rw [norm_zero]; positivity
  have hA3' := (htr _ hF3).2.1 hA3
  have hkY : Integrable (fun w : Bool × X × ℝ ↦ (π₀ w.2.1 * k w.2.1) * w.2.2) P := by
    refine (hA2'.add hA3').congr (Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.add_apply]; ring
  have hB : ∫ w, π₀ w.2.1 * ((w.2.2 - m₀ w.2.1) * k w.2.1) ∂P = 0 := by
    have h1 := integral_mul_response_eq P hYi m₀ hm₀m hreg (fun x ↦ π₀ x * k x)
      (hπ₀m.mul hkm) hkY
    have h2 : ∫ w, π₀ w.2.1 * ((w.2.2 - m₀ w.2.1) * k w.2.1) ∂P =
        ∫ w, (π₀ w.2.1 * k w.2.1) * w.2.2 ∂P - ∫ w, (π₀ w.2.1 * k w.2.1) * m₀ w.2.1 ∂P := by
      rw [← integral_sub hkY (hA3'.congr (Eventually.of_forall fun w ↦ by dsimp only; ring))]
      congr 1; ext w; ring
    rw [h2, h1, sub_self]
  -- The mean of the score difference.
  have hD : ∫ w, (missingMeanScore m π w.2.1 w.1 w.2.2 -
      missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2) ∂P =
      ∫ w, u w.2.1 * ((π w.2.1 - π₀ w.2.1) / π w.2.1) ∂P := by
    have hsplit : (fun w : Bool × X × ℝ ↦ missingMeanScore m π w.2.1 w.1 w.2.2 -
        missingMeanScore m₀ π₀ w.2.1 w.1 w.2.2) = fun w ↦
        (u w.2.1 - (if w.1 = true then u w.2.1 / π w.2.1 else 0)) +
          (if w.1 = true then (w.2.2 - m₀ w.2.1) * k w.2.1 else 0) := by
      ext w
      simp only [missingMeanScore, hudef, hkdef]
      split_ifs
      · field_simp [(hπ0 w.2.1).ne', (hπ₀p w.2.1).ne']; ring
      · ring
    have e1 := integral_add (hui.sub hA1) hA2
    have e2 := integral_sub hui hA1
    have e3 := integral_sub hui hA1'
    simp only [Pi.sub_apply] at e1
    rw [hsplit, e1, e2, (htr _ hF2).1, (htr _ hF1).1, hB, add_zero, ← e3]
    congr 1; ext w
    field_simp [(hπ0 w.2.1).ne']
  rw [hD]
  exact enorm_integral_comp_mul_div_le P hX hum (hπ.sub hπ₀m) hπ hδ hπδ

/-- The squared `L²` seminorm bound `‖f‖₂ ≤ η` gives `∫⁻ f² ≤ η²`. -/
private theorem lintegral_ofReal_sq_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hfm : AEStronglyMeasurable f μ) {η : ℝ} (hη : 0 ≤ η)
    (hf : eLpNorm f 2 μ ≤ ENNReal.ofReal η) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal (η ^ 2) := by
  have h1 : ∀ x, ENNReal.ofReal (f x ^ 2) = ‖f x‖ₑ ^ (2 : ℝ) := fun x ↦ by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
  have h2 : eLpNorm f 2 μ = eLpNorm' f 2 μ := by
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hfm]; norm_num
  rw [lintegral_congr h1, lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos, ← h2]
  calc eLpNorm f 2 μ ^ (2 : ℝ) ≤ ENNReal.ofReal η ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hf (by norm_num)
    _ = ENNReal.ofReal (η ^ 2) := by rw [ENNReal.rpow_two, ENNReal.ofReal_pow hη]

omit [MeasurableSpace X] in
/-- The augmented inverse-probability score only uses the response when it is observed. -/
private theorem missingMeanScore_missingDataObservation (h : (X → ℝ) × (X → ℝ))
    (w : Bool × X × ℝ) :
    missingMeanScore h.1 h.2 (missingDataObservation w).2.1 (missingDataObservation w).1
        (missingDataObservation w).2.2 = missingMeanScore h.1 h.2 w.2.1 w.1 w.2.2 := by
  rcases w with ⟨_ | _, x, y⟩ <;> rfl

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
  rw [hfib, crossFittedAverage, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hxy]
  field_simp
  rw [Real.sq_sqrt hn'.le]
  ring

omit [MeasurableSpace X] in
/-- Unfolding of the augmented inverse-probability score. -/
private theorem missingMeanScore_def (m π : X → ℝ) (x : X) (r : Bool) (y : ℝ) :
    missingMeanScore m π x r y = m x + if r = true then (y - m x) / π x else 0 := rfl

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
  set e₁ : ℝ≥0∞ := min e 1 with he₁def
  have he₁ : 0 < e₁ := lt_min he one_pos
  have he₁t : e₁ ≠ ∞ := ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
  set r : ℝ := e₁.toReal / 2 with hrdef
  have hr : 0 < r := div_pos (ENNReal.toReal_pos he₁.ne' he₁t) two_pos
  set η : ℝ := ε / 2 * Real.sqrt r with hηdef
  have hη : 0 < η := by positivity
  have hηr : η ^ 2 / (ε / 2) ^ 2 = r := by
    rw [hηdef, mul_pow, Real.sq_sqrt hr.le]; field_simp
  have hrle : ENNReal.ofReal r ≤ e / 2 := by
    rw [hrdef, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal he₁t,
      ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_right (min_le_left _ _) 2
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
  have hΦ : Measurable fun z : (split n).trainingIndices k → Bool × X × ℝ ↦
      fun j ↦ missingDataObservation (z j) :=
    measurable_pi_iff.2 fun j ↦ measurable_missingDataObservation.comp (measurable_pi_apply j)
  obtain ⟨G, hGdef⟩ : ∃ G : ((split n).trainingIndices k → Bool × X × ℝ) × (Bool × X × ℝ) → ℝ,
      G = fun p ↦ missingMeanScore (train n k fun j ↦ missingDataObservation (p.1 j)).1
        (train n k fun j ↦ missingDataObservation (p.1 j)).2 p.2.2.1 p.2.1 p.2.2.2 -
      missingMeanScore m₀ π₀ p.2.2.1 p.2.1 p.2.2.2 := ⟨_, rfl⟩
  have hg₁ : Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k fun j ↦ missingDataObservation (p.1 j)).1 p.2 :=
    (htrain₁ n k).comp ((hΦ.comp measurable_fst).prodMk measurable_snd)
  have hg₂ : Measurable fun p : ((split n).trainingIndices k → Bool × X × ℝ) × X ↦
      (train n k fun j ↦ missingDataObservation (p.1 j)).2 p.2 :=
    (htrain₂ n k).comp ((hΦ.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable G := by
    rw [hGdef]
    exact measurable_missingMeanScore_sub
      (h := fun z : (split n).trainingIndices k → Bool × X × ℝ ↦
        train n k fun j ↦ missingDataObservation (z j)) hg₁ hg₂ hm₀m hπ₀m
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
  have hrem : ENNReal.ofReal (A.card * η ^ 2 / (ε / 2 * Real.sqrt n) ^ 2) ≤
      ENNReal.ofReal r := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hcn : (A.card : ℝ) ≤ n := hsq ▸ hcard
    have e : (ε / 2 * Real.sqrt n) ^ 2 = (ε / 2) ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [e, ← hηr, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ η ^ 2 * (ε / 2) ^ 2 := by positivity
    nlinarith
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
    have hbias := enorm_integral_missingMeanScore_sub_le P hY π₀ m₀ hπ₀m hm₀m hδ hπ₀ hmar hreg
      _ _ hm hπ (hπhat n k _) ((heu ω).trans_le hu1 |>.trans_lt ENNReal.ofReal_lt_top)
    rw [heu, hev, hDω] at hbias
    have hc := sqrt_mul_abs_le_of_enorm_le hsn.le hδ hε.le hbias hp
    simp only [mem_ofPred_eq] at hω ⊢
    have hsplit : ∑ i ∈ Finset.univ.filter (fun i ↦ (split n).fold i = k),
        (missingMeanScore (train n k fun j ↦ missingDataObservation (W j.val ω)).1
          (train n k fun j ↦ missingDataObservation (W j.val ω)).2 (W i ω).2.1 (W i ω).1
            (W i ω).2.2 - missingMeanScore m₀ π₀ (W i ω).2.1 (W i ω).1 (W i ω).2.2) =
        ∑ i ∈ A, (D ω (W i ω) - ∫ y, D ω y ∂P) + A.card * ∫ y, D ω y ∂P := by
      have e : ∑ i ∈ A, (D ω (W i ω) - ∫ y, D ω y ∂P) + A.card * ∫ y, D ω y ∂P =
          ∑ i ∈ A, D ω (W i ω) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_add_cancel]
      rw [e, hA, hD]
    rw [hsplit] at hω
    exact lt_abs_of_lt_abs_inv_mul_add hsn (Nat.cast_nonneg _) hcard hc hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (μ {ω | ENNReal.ofReal η < eLpNorm (D ω) 2 P} + ENNReal.ofReal r) +
        (μ {ω | ENNReal.ofReal 1 < eu ω} + μ {ω | ENNReal.ofReal 1 < ev ω} +
          μ {ω | ENNReal.ofReal (ε * δ / 2) < ENNReal.ofReal (Real.sqrt n) * eu ω * ev ω}) := by
      gcongr
      · exact hF.trans (add_le_add (measure_mono hbad) hrem)
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
