module

public import CKSD.Asymptotics.Statistics
public import CKSD.Inference.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Fold and bias bounds for cross-fitted estimation of a missing mean

The two estimates behind the asymptotic linearity of the cross-fitted augmented
inverse-probability estimator (`CKSD.Asymptotics.CrossFitting`, GAPS 102.39): Chebyshev's
inequality for the centred sum over a fold, given independent training data, and the bias bound
for the augmented inverse-probability score under missingness at random. Rate conditions on norms
are expressed for `ℝ≥0∞`-valued `L²` norms (`eLpNorm`), so that an infinite norm cannot be
replaced by a junk real value.

## Main definitions

* `CKSD.TendstoInProbabilityZeroENNReal`: convergence to zero in probability of
  `ℝ≥0∞`-valued random quantities.
* `CKSD.missingDataObservation`: the observed part `(R, X, R Y)` of a full-data triple.

## Main results

* `CKSD.measure_lt_abs_fold_sum_sub_integral_le`: Chebyshev's inequality for a cross-fitting
  fold.
* `CKSD.enorm_integral_missingMeanScore_sub_le`: missingness at random makes the bias of the
  score equal to `E[(m - m₀)(π - π₀)/π]`, bounded by the product of the nuisance errors.
* `CKSD.lintegral_ofReal_sq_le_of_eLpNorm_le`: an `L²` seminorm bound bounds the integral of
  the square.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Convergence to zero in (outer) probability of nonnegative extended-real random quantities.
An infinite value counts as exceeding every threshold. -/
@[expose] def TendstoInProbabilityZeroENNReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ENNReal.ofReal ε < Y n ω}) atTop (𝓝 0)

/-- Observed part `(R, X, R Y)` of a full-data triple `(R, X, Y)`. -/
def missingDataObservation {X : Type*} (w : Bool × X × ℝ) : Bool × X × ℝ :=
  (w.1, w.2.1, if w.1 then w.2.2 else 0)

/-- The observed part of `(R, X, Y)` is `(R, X, R Y)`. -/
theorem missingDataObservation_def {X : Type*} (w : Bool × X × ℝ) :
    missingDataObservation w = (w.1, w.2.1, if w.1 then w.2.2 else 0) := by
  rw [missingDataObservation]

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
theorem measure_lt_abs_fold_sum_sub_integral_le {Ω Y : Type*} [MeasurableSpace Ω]
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
`‖E[u(X) v(X) / π(X)]‖ ≤ δ⁻¹ ‖u‖_{L²(P_X)} ‖v‖_{L²(P_X)}`. -/
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

/-- A function supported on the observed records `R = 1` and dominated there by a multiple
of an integrable function is integrable. -/
private theorem integrable_ite_observed_of_norm_le {P : Measure (Bool × X × ℝ)}
    {f g : Bool × X × ℝ → ℝ} {c : ℝ} (hg : Integrable g P) (hf : Measurable f)
    (hfg : ∀ w, ‖f w‖ ≤ c * ‖g w‖) :
    Integrable (fun w ↦ if w.1 = true then f w else 0) P := by
  have hS : MeasurableSet {w : Bool × X × ℝ | w.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  refine (hg.norm.const_mul c).mono' ((Measurable.ite hS hf measurable_const).aestronglyMeasurable)
    (Eventually.of_forall fun w ↦ ?_)
  split_ifs
  · exact hfg w
  · rw [norm_zero]; exact (norm_nonneg _).trans (hfg w)

/-- **Bias of the augmented inverse-probability score.** Under missingness at random, for
nuisance values `(m, π)` with `π ≥ δ` and `m - m₀, π - π₀ ∈ L²(P_X)`, the mean of the difference
of the scores at `(m, π)` and `(m₀, π₀)` is `E[(m - m₀)(π - π₀) / π](X)`, so it is bounded by
`δ⁻¹ ‖m - m₀‖₂ ‖π - π₀‖₂`. -/
theorem enorm_integral_missingMeanScore_sub_le (P : Measure (Bool × X × ℝ))
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
  have hui : Integrable (fun w : Bool × X × ℝ ↦ u w.2.1) P := huL.integrable one_le_two
  have hm₀i := integrable_of_regression P hYi m₀ hm₀m hreg
  have htr := integral_ite_observed_eq P π₀ hπ₀m hπ₀0 hmar
  -- The first part: `u(X) (1 - R/π(X))`.
  have hF1 : Measurable fun p : X × ℝ ↦ u p.1 / π p.1 := by fun_prop
  have hA1 : Integrable (fun w : Bool × X × ℝ ↦ if w.1 = true then u w.2.1 / π w.2.1 else 0)
      P := integrable_ite_observed_of_norm_le hui (by fun_prop) fun w ↦ by
    rw [norm_div, Real.norm_eq_abs (π _), abs_of_pos (hπ0 _), div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (hinv _) (norm_nonneg _)
  have hA1' := (htr _ hF1).2.1 hA1
  -- The second part: `R (Y - m₀(X)) k(X)`.
  have hF2 : Measurable fun p : X × ℝ ↦ (p.2 - m₀ p.1) * k p.1 := by fun_prop
  have hA2 : Integrable (fun w : Bool × X × ℝ ↦
      if w.1 = true then (w.2.2 - m₀ w.2.1) * k w.2.1 else 0) P :=
    integrable_ite_observed_of_norm_le (hYi.sub hm₀i) (by fun_prop) fun w ↦ by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hkb _) (norm_nonneg _)
  have hA2' := (htr _ hF2).2.1 hA2
  have hF3 : Measurable fun p : X × ℝ ↦ m₀ p.1 * k p.1 := by fun_prop
  have hA3 : Integrable (fun w : Bool × X × ℝ ↦ if w.1 = true then m₀ w.2.1 * k w.2.1 else 0)
      P := integrable_ite_observed_of_norm_le hm₀i (by fun_prop) fun w ↦ by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hkb _) (norm_nonneg _)
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
      simp only [missingMeanScore_def, hudef, hkdef]
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
theorem lintegral_ofReal_sq_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
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

end CrossFitting

end CKSD
