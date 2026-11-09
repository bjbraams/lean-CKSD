module

public import CKSD.Inference.Basic
public import Mathlib.Probability.CDF
public import CKSD.Inference.Sufficiency
public import TauCeti.Probability.Distributions.OrderStatistic.Joint
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
public import TauCeti.Probability.Distributions.Beta.Cdf
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Independence.InfinitePi
public import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Symmetric completeness, order statistics, and the Pitman estimator

## Main definitions

* `CKSD.IsSymmetricStatistic`, `CKSD.IsSymmetricallyComplete`: permutation-invariant sample
  statistics and completeness restricted to them.
* `CKSD.IsLocationEquivariant`, `CKSD.pitmanEstimator`: location-equivariant estimators and the
  Pitman estimator `∫ u ∏ f(xᵢ - u) du / ∫ ∏ f(xᵢ - u) du`.

## Main results

* `CKSD.isSymmetricallyComplete_of_complete_convex_family`: the order statistic is complete in a
  convex complete family (GAPS 101.13).
* `CKSD.map_orderStatistics_eq_withDensity`, `CKSD.map_orderStatistic_eq_withDensity`: joint and
  marginal densities of order statistics (GAPS 101.21).
* `CKSD.map_sort_eq_and_indepFun_orderStatistics`: the ranks of an atomless i.i.d. sample are
  uniform and independent of the order statistics (GAPS 101.21).
* `CKSD.pitmanEstimator_minimum_equivariant_risk`: the Pitman estimator minimizes the
  squared-error risk among location-equivariant estimators (GAPS 101.40).

## Implementation notes

Order statistics and sorting are TauCeti's `TauCeti.orderStatistic` and Mathlib's `Tuple.sort`;
the densities use TauCeti's chamber formula `TauCeti.Probability.map_orderStatistics_pi`, its
beta-law computation of the distribution function of an order statistic, and the probability
integral transform `MeasureTheory.Measure.cdf_map_eq_volume_restrict`.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A statistic on a finite sample is symmetric under all coordinate permutations. -/
def IsSymmetricStatistic {X Y : Type*} {n : ℕ} (T : (Fin n → X) → Y) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) x, T (x ∘ σ) = T x

/-- Completeness restricted to the symmetric sample statistics. -/
def IsSymmetricallyComplete {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (n : ℕ) : Prop :=
  ∀ g : (Fin n → X) → ℝ, Measurable g → IsSymmetricStatistic g →
    (∀ θ, Integrable g (Measure.pi fun _ : Fin n ↦ P θ) ∧
      (∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ P θ)) = 0) →
    ∀ θ, g =ᵐ[Measure.pi fun _ : Fin n ↦ P θ] 0

/-- GAPS 101.13: completeness of permutation-invariant statistics in a convex complete model. -/
theorem isSymmetricallyComplete_of_complete_convex_family
    {X : Type*} [MeasurableSpace X] (C : Set (ProbabilityMeasure X))
    (hc : IsCompleteStatistic (fun P : C ↦ (P.val : Measure X)) id)
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X)) (n : ℕ) :
    IsSymmetricallyComplete (fun P : C ↦ (P.val : Measure X)) n := by
  sorry

/-- GAPS 101.21: joint order-statistic density for an absolutely continuous law.
The proof combines TauCeti's chamber formula `TauCeti.Probability.map_orderStatistics_pi` with
TauCeti's product-density identity `TauCeti.pi_withDensity`. -/
theorem map_orderStatistics_eq_withDensity {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f) :
    (Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ TauCeti.orderStatistic i x) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x ↦
        if StrictMono x then ENNReal.ofReal ((n.factorial : ℝ) * ∏ i, f (x i)) else 0) := by
  have hPeq := hf.2.2
  have hns : NullSingletonClass P := by rw [hPeq]; infer_instance
  have hsf : SigmaFinite (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) := by
    rw [← hPeq]; infer_instance
  have hC : MeasurableSet {x : Fin n → ℝ | StrictMono x} :=
    TauCeti.measurableSet_setOf_strictMono
  rw [TauCeti.Probability.map_orderStatistics_pi, hPeq,
    TauCeti.pi_withDensity (fun _ ↦ (volume : Measure ℝ)) (fun _ ↦ hf.1.ennreal_ofReal),
    ← volume_pi, restrict_withDensity hC, ← withDensity_indicator hC, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    ← withDensity_smul]
  swap
  · exact (Finset.measurable_prod _ fun i _ ↦
      hf.1.ennreal_ofReal.comp (measurable_pi_apply i)).indicator hC
  refine withDensity_congr_ae ?_
  have hnn : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ∀ i, 0 ≤ f (x i) := by
    rw [volume_pi, ae_all_iff]
    exact fun i ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ (volume : Measure ℝ))
      (i := i)).eventually (p := fun t ↦ 0 ≤ f t) hf.2.1
  filter_upwards [hnn] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, indicator, mem_ofPred_eq]
  split_ifs
  · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hx i,
      ENNReal.ofReal_natCast]
  · simp

/-- On the unit interval the beta density with integer shapes `j + 1` and `n - j` is the
polynomial `n! / (j! (n - j - 1)!) u ^ j (1 - u) ^ (n - j - 1)`. -/
theorem betaMeasure_nat_eq_withDensity {n : ℕ} (j : Fin n) :
    betaMeasure ((j : ℝ) + 1) ((n : ℝ) - j) =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity (fun u ↦ ENNReal.ofReal
        ((n.factorial : ℝ) / (j.val.factorial * (n - j.val - 1).factorial) *
          u ^ j.val * (1 - u) ^ (n - j.val - 1))) := by
  have hjn : j.val < n := j.2
  rw [TauCeti.Probability.betaMeasure_eq_withDensity_restrict_Ioo,
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hk : (n : ℝ) - j = ((n - j.val - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hbeta : ProbabilityTheory.beta ((j : ℝ) + 1) ((n : ℝ) - j) =
      (j.val.factorial * (n - j.val - 1).factorial) / n.factorial := by
    rw [ProbabilityTheory.beta, show (j : ℝ) + 1 + ((n : ℝ) - j) = (n : ℝ) + 1 by ring, hk,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  simp only [betaPDF, betaPDFReal, hu.1, hu.2, and_self, ite_true, hbeta, one_div, inv_div]
  congr 1
  rw [hk, add_sub_cancel_right, add_sub_cancel_right, Real.rpow_natCast, Real.rpow_natCast]


/-- GAPS 101.21: the marginal density of the zero-indexed `j`th order statistic.
The proof compares distribution functions: TauCeti's
`TauCeti.Probability.cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta` and
`TauCeti.Probability.cdf_betaMeasure_eq` give the beta law of `F(X₍ⱼ₎)`, and TauCeti's
probability integral transform `MeasureTheory.Measure.cdf_map_eq_volume_restrict` moves the
beta density back along `F`. -/
theorem map_orderStatistic_eq_withDensity {n : ℕ} (j : Fin n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f) :
    (Measure.pi fun _ : Fin n ↦ P).map (TauCeti.orderStatistic j) =
      volume.withDensity (fun x ↦ ENNReal.ofReal
        ((n.factorial : ℝ) / (j.val.factorial * (n - j.val - 1).factorial) *
          cdf P x ^ j.val * (1 - cdf P x) ^ (n - j.val - 1) * f x)) := by
  have hjn : j.val < n := j.2
  have hPeq := hf.2.2
  have hns : NullSingletonClass P := by rw [hPeq]; infer_instance
  let c : ℝ := (n.factorial : ℝ) / (j.val.factorial * (n - j.val - 1).factorial)
  let h : ℝ → ℝ := fun u ↦ c * u ^ j.val * (1 - u) ^ (n - j.val - 1)
  let F : ℝ → ℝ := fun x ↦ ProbabilityTheory.cdf P x
  have hFeq : ∀ x, cdf P x = F x := fun x ↦ rfl
  have hFm : Measurable F := (ProbabilityTheory.cdf P).mono.measurable
  have hhm : Measurable h := by fun_prop
  have hc : 0 ≤ c := by positivity
  have hhF : ∀ x, 0 ≤ h (F x) := fun x ↦ by
    have h0 := ProbabilityTheory.cdf_nonneg P x
    have h1 := ProbabilityTheory.cdf_le_one P x
    have : 0 ≤ 1 - F x := by simp only [F]; linarith
    positivity
  -- the right side is `P` reweighted by `h ∘ F`
  have hrhs : volume.withDensity (fun x ↦ ENNReal.ofReal
        (c * cdf P x ^ j.val * (1 - cdf P x) ^ (n - j.val - 1) * f x)) =
      P.withDensity (fun x ↦ ENNReal.ofReal (h (F x))) := by
    simp_rw [hFeq]
    conv_rhs => rw [hPeq]
    rw [← withDensity_mul volume (f := fun x ↦ ENNReal.ofReal (f x))
      (g := fun x ↦ ENNReal.ofReal (h (F x))) hf.1.ennreal_ofReal (hhm.comp hFm).ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [mul_comm (ENNReal.ofReal (f x)), ← ENNReal.ofReal_mul (hhF x)]
  -- the law of the order statistic, computed by its distribution function
  have hfin : IsFiniteMeasure (P.withDensity (fun x ↦ ENNReal.ofReal (h (F x)))) := by
    refine isFiniteMeasure_withDensity_ofReal ?_
    refine (integrable_of_measurable_of_abs_le P (C := c) (hhm.comp hFm) fun x ↦ ?_).2
    have h0 := ProbabilityTheory.cdf_nonneg P x
    have h1 := ProbabilityTheory.cdf_le_one P x
    rw [Function.comp_apply, abs_of_nonneg (hhF x)]
    simp only [h, F]
    calc c * (ProbabilityTheory.cdf P x) ^ j.val * (1 - ProbabilityTheory.cdf P x) ^ (n - j.val - 1)
        ≤ c * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ h0 h1
          · exact pow_le_one₀ (by linarith) (by linarith)
      _ = c := by ring
  have ha : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) - j := by
    have : (j.val : ℝ) < n := by exact_mod_cast hjn
    linarith
  have hpit : P.map F = volume.restrict (Icc (0 : ℝ) 1) :=
    MeasureTheory.Measure.cdf_map_eq_volume_restrict P
  -- the level sets of `F` are `P`-null, by the probability integral transform
  have hlevel : ∀ s : ℝ, P (F ⁻¹' {s}) = 0 := by
    intro s
    rw [← Measure.map_apply hFm (measurableSet_singleton s), hpit,
      Measure.restrict_apply (measurableSet_singleton s)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)
  have := isProbabilityMeasureBeta ha hb
  have hFmono : Monotone F := (ProbabilityTheory.cdf P).mono
  rw [hrhs]
  refine Measure.ext_of_Iic _ _ fun t ↦ ?_
  rw [← ProbabilityTheory.ofReal_cdf,
    TauCeti.Probability.cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta,
    ← TauCeti.Probability.cdf_betaMeasure_eq ha hb, ProbabilityTheory.ofReal_cdf,
    betaMeasure_nat_eq_withDensity j, ← hpit, withDensity_apply _ measurableSet_Iic,
    setLIntegral_map measurableSet_Iic (by fun_prop) hFm, withDensity_apply _ measurableSet_Iic]
  refine setLIntegral_congr (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun x hx ↦ ?_) (hlevel (F t))
    simp only [Set.mem_sdiff, mem_preimage, mem_Iic, not_le] at hx
    exact le_antisymm hx.1 (hFmono hx.2.le)
  · refine measure_mono_null (fun x hx ↦ ?_) (measure_empty (μ := P))
    simp only [Set.mem_sdiff, mem_preimage, mem_Iic] at hx
    exact hx.2 (hFmono hx.1)

/-- The set of samples with a prescribed sorting permutation is measurable. -/
theorem measurableSet_setOf_sort_eq {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | Tuple.sort x = τ} := by
  classical
  have h : {x : Fin n → ℝ | Tuple.sort x = τ} =
      (⋂ i, ⋂ j, {x : Fin n → ℝ | i ≤ j → x (τ i) ≤ x (τ j)}) ∩
        ⋂ i, ⋂ j, {x : Fin n → ℝ | i ≤ j → x (τ i) = x (τ j) → τ i ≤ τ j} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_)
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp [hij]
  · by_cases hij : i ≤ j
    · by_cases hτ : τ i ≤ τ j
      · simp [hij, hτ]
      · simp only [hij, hτ, true_implies, imp_false]
        exact (measurableSet_eq_fun (measurable_pi_apply (τ i)) (measurable_pi_apply (τ j))).compl
    · simp [hij]


/-- GAPS 101.21: for an i.i.d. sample from an atomless law on `ℝ`, the sorting permutation (the
ranks) is uniformly distributed on the `n!` permutations and independent of the vector of order
statistics. The permutation group carries its discrete σ-algebra.
The proof refines the chamber decomposition of TauCeti's
`TauCeti.Probability.map_orderStatistics_pi`: ties are null
(`TauCeti.Probability.ae_eval_ne_eval_infinitePi`), and coordinate permutations preserve the
product law and the order statistics (`TauCeti.orderStatistic_comp_perm`). -/
theorem map_sort_eq_and_indepFun_orderStatistics {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] [NullSingletonClass P]
    [MeasurableSpace (Equiv.Perm (Fin n))] [DiscreteMeasurableSpace (Equiv.Perm (Fin n))] :
    (Measure.pi fun _ : Fin n ↦ P).map Tuple.sort = (n.factorial : ℝ≥0∞)⁻¹ • Measure.count ∧
      IndepFun Tuple.sort (fun x i ↦ TauCeti.orderStatistic i x)
        (Measure.pi fun _ : Fin n ↦ P) := by
  classical
  set μ := Measure.pi fun _ : Fin n ↦ P
  let S : (Fin n → ℝ) → (Fin n → ℝ) := fun x i ↦ TauCeti.orderStatistic i x
  let M : Set (Fin n → ℝ) := {x | StrictMono x}
  have hM : MeasurableSet M := TauCeti.measurableSet_setOf_strictMono
  have hS : Measurable S := by fun_prop
  have hsort : Measurable (Tuple.sort : (Fin n → ℝ) → Equiv.Perm (Fin n)) :=
    measurable_to_countable' fun τ ↦ measurableSet_setOf_sort_eq τ
  have hSperm : ∀ x (σ : Equiv.Perm (Fin n)), S (x ∘ σ) = S x := fun x σ ↦ by
    funext i; exact TauCeti.orderStatistic_comp_perm i x σ
  have hperm (σ : Equiv.Perm (Fin n)) : MeasurePreserving (fun x : Fin n → ℝ ↦ x ∘ σ) μ μ := by
    convert measurePreserving_piCongrLeft (fun _ : Fin n ↦ P) σ.symm using 1
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  -- ties are null, and away from ties the sorting permutation is the one making the sample
  -- strictly increasing
  have hne : ∀ᵐ x ∂μ, Function.Injective x := by
    have h : ∀ᵐ x ∂μ, ∀ i j : Fin n, i ≠ j → x i ≠ x j := by
      refine ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ ?_
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h ↦ (h hij).elim
      · simpa only [Measure.infinitePi_eq_pi] using
          (TauCeti.Probability.ae_eval_ne_eval_infinitePi (fun _ : Fin n ↦ P) hij).mono
            fun _ hx _ ↦ hx
    filter_upwards [h] with x hx
    exact Function.injective_iff_pairwise_ne.mpr hx
  have hae : ∀ τ : Equiv.Perm (Fin n),
      {x : Fin n → ℝ | Tuple.sort x = τ} =ᵐ[μ] (fun x : Fin n → ℝ ↦ x ∘ τ) ⁻¹' M := by
    intro τ
    filter_upwards [hne] with x hx
    apply propext
    constructor
    · intro h
      change Tuple.sort x = τ at h
      change StrictMono (x ∘ τ)
      rw [← h]
      exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
    · intro h
      change StrictMono (x ∘ τ) at h
      have heq := Tuple.unique_monotone (Tuple.monotone_sort x) h.monotone
      exact DFunLike.ext _ _ fun i ↦ hx (congrFun heq i)
  -- each sorting permutation carries the same part of the law of the order statistics
  have hkey : ∀ (τ : Equiv.Perm (Fin n)) (t : Set (Fin n → ℝ)), MeasurableSet t →
      μ ({x | Tuple.sort x = τ} ∩ S ⁻¹' t) = μ (M ∩ S ⁻¹' t) := by
    intro τ t ht
    rw [measure_congr ((hae τ).inter (ae_eq_refl _))]
    have : (fun x : Fin n → ℝ ↦ x ∘ τ) ⁻¹' M ∩ S ⁻¹' t =
        (fun x : Fin n → ℝ ↦ x ∘ τ) ⁻¹' (M ∩ S ⁻¹' t) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, hSperm]
    rw [this, (hperm τ).measure_preimage (hM.inter (hS ht)).nullMeasurableSet]
  have hsum : ∀ t : Set (Fin n → ℝ), MeasurableSet t →
      μ (S ⁻¹' t) = (n.factorial : ℝ≥0∞) * μ (M ∩ S ⁻¹' t) := by
    intro t ht
    have hU : S ⁻¹' t = ⋃ τ : Equiv.Perm (Fin n), ({x | Tuple.sort x = τ} ∩ S ⁻¹' t) := by
      ext x; simp
    nth_rw 1 [hU]
    rw [measure_iUnion (fun τ τ' hττ' ↦ ?_)
      (fun τ ↦ (measurableSet_setOf_sort_eq τ).inter (hS ht)), tsum_fintype]
    · simp_rw [hkey _ t ht]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    · refine Set.disjoint_left.2 fun x hx hx' ↦ hττ' ?_
      exact hx.1.symm.trans hx'.1
  have hfac0 : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfacT : (n.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hval : ∀ (τ : Equiv.Perm (Fin n)) (t : Set (Fin n → ℝ)), MeasurableSet t →
      μ ({x | Tuple.sort x = τ} ∩ S ⁻¹' t) = (n.factorial : ℝ≥0∞)⁻¹ * μ (S ⁻¹' t) := by
    intro τ t ht
    rw [hkey τ t ht, hsum t ht, ← mul_assoc, ENNReal.inv_mul_cancel hfac0 hfacT, one_mul]
  have hval1 : ∀ τ : Equiv.Perm (Fin n),
      μ {x | Tuple.sort x = τ} = (n.factorial : ℝ≥0∞)⁻¹ := by
    intro τ
    have := hval τ univ MeasurableSet.univ
    simpa using this
  -- preimages of sets of permutations
  have hpre : ∀ s : Set (Equiv.Perm (Fin n)), (Tuple.sort : (Fin n → ℝ) → _) ⁻¹' s =
      ⋃ τ ∈ s.toFinset, {x | Tuple.sort x = τ} := by
    intro s; ext x; simp
  have hdisj : ∀ s : Set (Equiv.Perm (Fin n)),
      (s.toFinset : Set (Equiv.Perm (Fin n))).PairwiseDisjoint
      (fun τ ↦ {x : Fin n → ℝ | Tuple.sort x = τ}) := by
    intro s τ _ τ' _ hττ'
    exact Set.disjoint_left.2 fun x hx hx' ↦ hττ' (hx.symm.trans hx')
  refine ⟨?_, ?_⟩
  · ext s hs
    rw [Measure.map_apply hsort hs, hpre, measure_biUnion_finset (hdisj s)
      (fun τ _ ↦ measurableSet_setOf_sort_eq τ)]
    simp_rw [hval1]
    rw [smul_apply, Measure.count_apply_finite s (Set.toFinite s), Finset.sum_const,
      nsmul_eq_mul, smul_eq_mul, mul_comm, Set.Finite.toFinset_eq_toFinset]
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t _ ht
    have hpre' : Tuple.sort ⁻¹' s ∩ S ⁻¹' t =
        ⋃ τ ∈ s.toFinset, ({x | Tuple.sort x = τ} ∩ S ⁻¹' t) := by
      rw [hpre, Set.iUnion₂_inter]
    change μ (Tuple.sort ⁻¹' s ∩ S ⁻¹' t) = μ (Tuple.sort ⁻¹' s) * μ (S ⁻¹' t)
    rw [hpre', hpre, measure_biUnion_finset (fun τ _ τ' _ hττ' ↦ ?_)
      (fun τ _ ↦ (measurableSet_setOf_sort_eq τ).inter (hS ht)),
      measure_biUnion_finset (hdisj s) (fun τ _ ↦ measurableSet_setOf_sort_eq τ),
      Finset.sum_mul]
    · refine Finset.sum_congr rfl fun τ _ ↦ ?_
      rw [hval τ t ht, hval1]
    · exact Set.disjoint_left.2 fun x hx hx' ↦ hττ' (hx.1.symm.trans hx'.1)

/-- Location-equivariance of a real estimator on a finite sample. -/
def IsLocationEquivariant {n : ℕ} (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x a, δ (fun i ↦ x i + a) = δ x + a

/-- The Pitman location estimator, using an improper Lebesgue prior. -/
def pitmanEstimator {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ u, u * ∏ i, f (x i - u)) / (∫ u, ∏ i, f (x i - u))

/-- Orbit decomposition of Lebesgue integrals on `Fin n → ℝ` along the diagonal direction: the
integral of `H` is the integral over `z`, weighted by the indicator of `z i₀ ∈ [0, 1]`, of the
integral of `H` along the line `u ↦ z - u • 1`. -/
theorem lintegral_eq_lintegral_indicator_mul_lintegral_sub_const {n : ℕ} (i₀ : Fin n)
    {H : (Fin n → ℝ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H x = ∫⁻ z, (Icc (0 : ℝ) 1).indicator 1 (z i₀) * ∫⁻ u : ℝ, H (z - fun _ ↦ u) := by
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ → ℝ≥0∞, k = (Icc (0 : ℝ) 1).indicator 1 := ⟨_, rfl⟩
  rw [← hkdef]
  have hk : Measurable k := by rw [hkdef]; exact measurable_one.indicator measurableSet_Icc
  have hc : Measurable fun p : (Fin n → ℝ) × ℝ ↦ (fun _ : Fin n ↦ p.2) :=
    measurable_pi_iff.2 fun _ ↦ measurable_snd
  have hjoint : Measurable fun p : (Fin n → ℝ) × ℝ ↦ k (p.1 i₀) * H (p.1 - fun _ ↦ p.2) :=
    (hk.comp ((measurable_pi_apply i₀).comp measurable_fst)).mul
      (hH.comp (measurable_fst.sub hc))
  have hjoint' : Measurable fun p : ℝ × (Fin n → ℝ) ↦ k (p.2 i₀ + p.1) * H p.2 :=
    (hk.comp (((measurable_pi_apply i₀).comp measurable_snd).add measurable_fst :
      Measurable fun p : ℝ × (Fin n → ℝ) ↦ p.2 i₀ + p.1)).mul
      (hH.comp measurable_snd)
  have hk1 : ∀ t : ℝ, ∫⁻ u, k (t + u) = 1 := fun t ↦ by
    rw [lintegral_add_left_eq_self k t, hkdef, lintegral_indicator_one measurableSet_Icc,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have e1 : ∫⁻ z, k (z i₀) * ∫⁻ u : ℝ, H (z - fun _ ↦ u)
      = ∫⁻ z, ∫⁻ u : ℝ, k (z i₀) * H (z - fun _ ↦ u) := by
    refine lintegral_congr fun z ↦ (lintegral_const_mul _ ?_).symm
    exact hH.comp (measurable_const.sub (measurable_pi_iff.2 fun _ ↦ measurable_id))
  have e2 : ∫⁻ u : ℝ, ∫⁻ z, k (z i₀) * H (z - fun _ ↦ u) =
      ∫⁻ u : ℝ, ∫⁻ x, k (x i₀ + u) * H x := by
    refine lintegral_congr fun u ↦ ?_
    have := lintegral_sub_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
      (fun x ↦ k (x i₀ + u) * H x) (fun _ ↦ u)
    rw [← this]
    refine lintegral_congr fun z ↦ ?_
    rw [Pi.sub_apply, sub_add_cancel]
  have e3 : ∫⁻ x, ∫⁻ u : ℝ, k (x i₀ + u) * H x = ∫⁻ x, H x := by
    refine lintegral_congr fun x ↦ ?_
    rw [lintegral_mul_const (f := fun u ↦ k (x i₀ + u)) _
      (hk.comp (measurable_const_add (x i₀))), hk1, one_mul]
  rw [e1, lintegral_lintegral_swap hjoint.aemeasurable, e2,
    lintegral_lintegral_swap hjoint'.aemeasurable, e3]

/-- Minimization of a weighted quadratic: for an integrable weight `w ≥ 0` with integrable first
moment and positive mass, the weighted second moment `∫ (c - u)² w(u) du` is minimal at the
weighted mean `c = ∫ u w / ∫ w`. -/
theorem lintegral_ofReal_sq_sub_mul_le {w : ℝ → ℝ} (hw : Measurable w) (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) (hmi : Integrable fun u ↦ u * w u) (hpos : 0 < ∫ u, w u) (c : ℝ) :
    ∫⁻ u, ENNReal.ofReal (((∫ u, u * w u) / (∫ u, w u) - u) ^ 2 * w u) ≤
      ∫⁻ u, ENNReal.ofReal ((c - u) ^ 2 * w u) := by
  obtain ⟨W, hW⟩ : ∃ W, W = ∫ u, w u := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ u, u * w u := ⟨_, rfl⟩
  rw [← hW, ← hM]
  rw [← hW] at hpos
  by_cases hfin : ∫⁻ u, ENNReal.ofReal ((c - u) ^ 2 * w u) = ∞
  · rw [hfin]; exact le_top
  have hm : ∀ d : ℝ, Measurable fun u ↦ (d - u) ^ 2 * w u := fun d ↦
    ((measurable_const.sub measurable_id).pow_const 2).mul hw
  have hci : Integrable fun u ↦ (c - u) ^ 2 * w u := by
    refine ⟨(hm c).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u ↦ mul_nonneg (sq_nonneg _) (hw0 u))]
    exact lt_top_iff_ne_top.2 hfin
  have hsq : Integrable fun u ↦ u ^ 2 * w u := by
    have := (hci.sub (hmi.const_mul (-2 * c))).sub (hwi.const_mul (c ^ 2))
    refine this.congr (ae_of_all _ fun u ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  have hexp : ∀ d : ℝ, Integrable (fun u ↦ (d - u) ^ 2 * w u) ∧
      ∫ u, (d - u) ^ 2 * w u = d ^ 2 * W - 2 * d * M + ∫ u, u ^ 2 * w u := by
    intro d
    have hsplit : (fun u ↦ (d - u) ^ 2 * w u) =
        fun u ↦ d ^ 2 * w u - 2 * d * (u * w u) + u ^ 2 * w u := by
      funext u; ring
    have h1 := hwi.const_mul (d ^ 2)
    have h2 := hmi.const_mul (2 * d)
    refine ⟨by rw [hsplit]; exact (h1.sub h2).add hsq, ?_⟩
    have h12 : Integrable (fun u ↦ d ^ 2 * w u - 2 * d * (u * w u)) := h1.sub h2
    have i1 : ∫ u, (d ^ 2 * w u - 2 * d * (u * w u) + u ^ 2 * w u) =
        (∫ u, (d ^ 2 * w u - 2 * d * (u * w u))) + ∫ u, u ^ 2 * w u := integral_add h12 hsq
    have i2 : ∫ u, (d ^ 2 * w u - 2 * d * (u * w u)) =
        (∫ u, d ^ 2 * w u) - ∫ u, 2 * d * (u * w u) := integral_sub h1 h2
    have i3 : ∫ u, d ^ 2 * w u = d ^ 2 * ∫ u, w u := integral_const_mul _ _
    have i4 : ∫ u, 2 * d * (u * w u) = 2 * d * ∫ u, u * w u := integral_const_mul _ _
    rw [hsplit, i1, i2, i3, i4, hW, hM]
  have hnn : ∀ d : ℝ, 0 ≤ᵐ[volume] fun u ↦ (d - u) ^ 2 * w u :=
    fun d ↦ ae_of_all _ fun u ↦ mul_nonneg (sq_nonneg _) (hw0 u)
  rw [← ofReal_integral_eq_lintegral_ofReal (hexp (M / W)).1 (hnn _),
    ← ofReal_integral_eq_lintegral_ofReal (hexp c).1 (hnn c), (hexp _).2, (hexp c).2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hW : W ≠ 0 := hpos.ne'
  have key : c ^ 2 * W - 2 * c * M - ((M / W) ^ 2 * W - 2 * (M / W) * M) =
      W * (c - M / W) ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg hpos.le (sq_nonneg (c - M / W))]

/-- The samples at which the Pitman estimator is well defined: the normalizing and first-moment
integrals exist and the normalizing integral is positive. -/
def pitmanGoodSet {n : ℕ} (f : ℝ → ℝ) : Set (Fin n → ℝ) :=
  {x | Integrable (fun u ↦ ∏ i, f (x i - u)) ∧ Integrable (fun u ↦ u * ∏ i, f (x i - u)) ∧
    0 < ∫ u, ∏ i, f (x i - u)}

/-- Joint measurability of the location likelihood `(x, u) ↦ ∏ f (x i - u)`. -/
theorem measurable_prod_sub {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun p : (Fin n → ℝ) × ℝ ↦ ∏ i, f (p.1 i - p.2) :=
  Finset.measurable_prod _ fun i _ ↦
    hf.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)

/-- The Pitman estimator is measurable for a measurable density. -/
theorem measurable_pitmanEstimator {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (pitmanEstimator (n := n) f) := by
  have h0 := measurable_prod_sub (n := n) hf
  have h1 : Measurable fun p : (Fin n → ℝ) × ℝ ↦ p.2 * ∏ i, f (p.1 i - p.2) :=
    measurable_snd.mul h0
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.div
    (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The Pitman good set is measurable. -/
theorem measurableSet_pitmanGoodSet {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet (pitmanGoodSet (n := n) f) := by
  have h0 := measurable_prod_sub (n := n) hf
  have h1 : Measurable fun p : (Fin n → ℝ) × ℝ ↦ p.2 * ∏ i, f (p.1 i - p.2) :=
    measurable_snd.mul h0
  have hI : ∀ {F : (Fin n → ℝ) × ℝ → ℝ}, Measurable F →
      MeasurableSet {x | Integrable (fun u ↦ F (x, u))} := by
    intro F hF
    have : {x | Integrable (fun u ↦ F (x, u))} = {x | ∫⁻ u, ‖F (x, u)‖ₑ < ∞} := by
      ext x
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hF.comp measurable_prodMk_left).aestronglyMeasurable, h⟩⟩
    rw [this]
    exact (hF.enorm.lintegral_prod_right' (ν := (volume : Measure ℝ))) measurableSet_Iio
  exact (hI h0).inter ((hI h1).inter (measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const
    (h0.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable))

/-- The Pitman good set is invariant under diagonal translations. -/
theorem sub_const_mem_pitmanGoodSet {n : ℕ} {f : ℝ → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ pitmanGoodSet f) (t : ℝ) : (x - fun _ : Fin n ↦ t) ∈ pitmanGoodSet f := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hv' : ∀ u, ∏ i, f ((x - fun _ : Fin n ↦ t) i - u) = ∏ i, f (x i - (u + t)) := by
    intro u; congr 1; funext i; rw [Pi.sub_apply]; ring_nf
  have hv : (fun u ↦ ∏ i, f ((x - fun _ : Fin n ↦ t) i - u)) = fun u ↦ ∏ i, f (x i - (u + t)) :=
    funext hv'
  have h2' : Integrable fun u ↦ (u + t) * ∏ i, f (x i - (u + t)) := h2.comp_add_right t
  have h1' : Integrable fun u ↦ ∏ i, f (x i - (u + t)) := h1.comp_add_right t
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]; exact h1'
  · simp only [hv']
    refine (h2'.sub (h1'.const_mul t)).congr (ae_of_all _ fun u ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  · rw [hv, integral_add_right_eq_self (fun u ↦ ∏ i, f (x i - u)) t]
    exact h3

/-- Membership in the Pitman good set is invariant under diagonal translations. -/
theorem sub_const_mem_pitmanGoodSet_iff {n : ℕ} {f : ℝ → ℝ} {x : Fin n → ℝ} (t : ℝ) :
    (x - fun _ : Fin n ↦ t) ∈ pitmanGoodSet f ↔ x ∈ pitmanGoodSet f := by
  refine ⟨fun h ↦ ?_, fun h ↦ sub_const_mem_pitmanGoodSet h t⟩
  have := sub_const_mem_pitmanGoodSet h (-t)
  have hx : ((x - fun _ : Fin n ↦ t) - fun _ ↦ -t) = x := by funext i; simp
  rwa [hx] at this

/-- On the good set, the Pitman estimator is location-equivariant. -/
theorem pitmanEstimator_sub_const {n : ℕ} {f : ℝ → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ pitmanGoodSet f) (t : ℝ) :
    pitmanEstimator f (x - fun _ : Fin n ↦ t) = pitmanEstimator f x - t := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hv' : ∀ u, ∏ i, f ((x - fun _ : Fin n ↦ t) i - u) = ∏ i, f (x i - (u + t)) := by
    intro u; congr 1; funext i; rw [Pi.sub_apply]; ring_nf
  have hv : (fun u ↦ ∏ i, f ((x - fun _ : Fin n ↦ t) i - u)) = fun u ↦ ∏ i, f (x i - (u + t)) :=
    funext hv'
  have hW : ∫ u, ∏ i, f ((x - fun _ : Fin n ↦ t) i - u) = ∫ u, ∏ i, f (x i - u) := by
    rw [hv, integral_add_right_eq_self (fun u ↦ ∏ i, f (x i - u)) t]
  have hM : ∫ u, u * ∏ i, f ((x - fun _ : Fin n ↦ t) i - u) =
      (∫ u, u * ∏ i, f (x i - u)) - t * ∫ u, ∏ i, f (x i - u) := by
    have e : (fun u ↦ u * ∏ i, f ((x - fun _ : Fin n ↦ t) i - u)) =
        fun u ↦ (fun s ↦ s * ∏ i, f (x i - s) - t * ∏ i, f (x i - s)) (u + t) := by
      funext u; rw [hv']; ring
    rw [e, integral_add_right_eq_self (fun s ↦ s * ∏ i, f (x i - s) - t * ∏ i, f (x i - s)) t,
      integral_sub h2 (h1.const_mul t), integral_const_mul]
  unfold pitmanEstimator
  rw [hM, hW]
  field_simp

/-- GAPS 101.40 for a nonnegative density: on the good set the Pitman estimator minimizes the
equivariant squared-error risk. -/
theorem pitmanEstimator_minimum_equivariant_risk_of_nonneg {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f)
    (hf0 : ∀ t, 0 ≤ f t)
    (δ : (Fin n → ℝ) → ℝ) (hm : Measurable δ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : Fin n ↦ P))
    (hint : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P), x ∈ pitmanGoodSet f) :
    (∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P)) ≤
      ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) := by
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨D, hD⟩ : ∃ D : (Fin n → ℝ) → ℝ≥0∞, D = fun x ↦ ∏ i, ENNReal.ofReal (f (x i)) :=
    ⟨_, rfl⟩
  have hDm : Measurable D := by
    rw [hD]
    exact Finset.measurable_prod _ fun i _ ↦ (hf.1.comp (measurable_pi_apply i)).ennreal_ofReal
  have hPn : Measure.pi (fun _ : Fin n ↦ P) = volume.withDensity D := by
    have : SigmaFinite (volume.withDensity fun t ↦ ENNReal.ofReal (f t)) := by
      rw [← hf.2.2]; infer_instance
    rw [hf.2.2, TauCeti.pi_withDensity (fun _ : Fin n ↦ (volume : Measure ℝ))
      (fun _ ↦ hf.1.ennreal_ofReal), hD, volume_pi]
  set G := pitmanGoodSet (n := n) f
  have hG : MeasurableSet G := measurableSet_pitmanGoodSet hf.1
  have hpm := measurable_pitmanEstimator (n := n) hf.1
  have hshift : ∀ (z : Fin n → ℝ) (u : ℝ), (z - fun _ : Fin n ↦ u) = fun i ↦ z i + -u := by
    intro z u; funext i; simp [sub_eq_add_neg]
  have hDz : ∀ (z : Fin n → ℝ) (u : ℝ),
      D (z - fun _ : Fin n ↦ u) = ENNReal.ofReal (∏ i, f (z i - u)) := by
    intro z u
    rw [hD, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hf0 _]
    rfl
  -- The risk of a measurable rule as an orbit integral.
  let Φ : ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ≥0∞ := fun g z ↦
    ∫⁻ u : ℝ, (G.indicator (fun y ↦ ENNReal.ofReal (g y ^ 2)) (z - fun _ ↦ u) *
      D (z - fun _ ↦ u))
  have hrisk : ∀ g : (Fin n → ℝ) → ℝ, Measurable g →
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) =
        ∫⁻ z, (Icc (0 : ℝ) 1).indicator 1 (z i₀) * Φ g z := by
    intro g hg
    have hgm : Measurable fun y ↦ ENNReal.ofReal (g y ^ 2) := (hg.pow_const 2).ennreal_ofReal
    have hIm : Measurable (G.indicator fun y ↦ ENNReal.ofReal (g y ^ 2)) := hgm.indicator hG
    calc ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P)
        = ∫⁻ x, G.indicator (fun y ↦ ENNReal.ofReal (g y ^ 2)) x
            ∂(Measure.pi fun _ : Fin n ↦ P) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hint] with x hx
          rw [indicator_of_mem hx]
      _ = ∫⁻ x, G.indicator (fun y ↦ ENNReal.ofReal (g y ^ 2)) x * D x := by
          rw [hPn, lintegral_withDensity_eq_lintegral_mul _ hDm hIm]
          refine lintegral_congr fun x ↦ ?_
          simp only [Pi.mul_apply]
          rw [mul_comm]
      _ = ∫⁻ z, (Icc (0 : ℝ) 1).indicator 1 (z i₀) * Φ g z :=
          lintegral_eq_lintegral_indicator_mul_lintegral_sub_const i₀ (hIm.mul hDm)
  -- Pointwise comparison of the orbit integrals.
  have hcomp : ∀ z, Φ (pitmanEstimator f) z ≤ Φ δ z := by
    intro z
    by_cases hz : z ∈ G
    · have hmem : ∀ u : ℝ, (z - fun _ : Fin n ↦ u) ∈ G := fun u ↦
        (sub_const_mem_pitmanGoodSet_iff u).2 hz
      have hform : ∀ g : (Fin n → ℝ) → ℝ, ∀ c : ℝ,
          (∀ u : ℝ, g (z - fun _ : Fin n ↦ u) = c - u) →
          Φ g z = ∫⁻ u : ℝ, ENNReal.ofReal ((c - u) ^ 2 * ∏ i, f (z i - u)) := by
        intro g c hgc
        refine lintegral_congr fun u ↦ ?_
        rw [indicator_of_mem (hmem u), hDz, hgc, ← ENNReal.ofReal_mul (sq_nonneg _)]
      have ⟨h1, h2', h3⟩ := hz
      rw [hform _ (pitmanEstimator f z) fun u ↦ pitmanEstimator_sub_const hz u,
        hform δ (δ z) fun u ↦ by rw [hshift, heq, sub_eq_add_neg]]
      exact lintegral_ofReal_sq_sub_mul_le (measurable_prod_sub hf.1 |>.comp
        (measurable_const.prodMk measurable_id)) (fun u ↦ Finset.prod_nonneg fun i _ ↦ hf0 _)
        h1 h2' h3 (δ z)
    · have hzero : ∀ g : (Fin n → ℝ) → ℝ, Φ g z = 0 := by
        intro g
        refine (lintegral_congr fun u ↦ ?_).trans lintegral_zero
        rw [indicator_of_notMem (fun h ↦ hz ((sub_const_mem_pitmanGoodSet_iff u).1 h)),
          zero_mul]
      rw [hzero, hzero]
  have hle : ∫⁻ x, ENNReal.ofReal (pitmanEstimator f x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ∫⁻ x, ENNReal.ofReal (δ x ^ 2) ∂(Measure.pi fun _ : Fin n ↦ P) := by
    rw [hrisk _ hpm, hrisk _ hm]
    exact lintegral_mono fun z ↦ by gcongr; exact hcomp z
  have hδi : Integrable (fun x ↦ δ x ^ 2) (Measure.pi fun _ : Fin n ↦ P) := h2.integrable_sq
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (hpm.pow_const 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (hm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hδi.lintegral_lt_top.ne hle

/-- GAPS 101.40: the Pitman estimator minimizes equivariant squared-error risk.
The normalizing and first-moment integrals are assumed to exist almost surely explicitly. -/
theorem pitmanEstimator_minimum_equivariant_risk {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f)
    (δ : (Fin n → ℝ) → ℝ) (hm : Measurable δ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : Fin n ↦ P))
    (hint : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P),
      Integrable (fun u ↦ ∏ i, f (x i - u)) volume ∧
      Integrable (fun u ↦ u * ∏ i, f (x i - u)) volume ∧
      0 < ∫ u, ∏ i, f (x i - u)) :
    (∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P)) ≤
      ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) := by
  -- Replace `f` by its positive part, which agrees with it almost everywhere.
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun t ↦ max (f t) 0 := ⟨_, rfl⟩
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ by rw [hgdef]; exact le_max_right _ _
  have hg : HasDensity P volume g := by
    refine ⟨by rw [hgdef]; exact hf.1.max measurable_const, ae_of_all _ hg0, ?_⟩
    rw [hf.2.2]
    congr 1
    funext t
    simp only [hgdef, ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact (max_eq_left bot_le).symm
  have hfg : ∀ᵐ t ∂(volume : Measure ℝ), f t = g t :=
    hf.2.1.mono fun t ht ↦ by rw [hgdef]; exact (max_eq_left ht).symm
  have hae : ∀ x : Fin n → ℝ,
      (fun u ↦ ∏ i, f (x i - u)) =ᵐ[volume] fun u ↦ ∏ i, g (x i - u) := by
    intro x
    have : ∀ i, ∀ᵐ u ∂(volume : Measure ℝ), f (x i - u) = g (x i - u) := fun i ↦
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) (x i)).quasiMeasurePreserving.ae
        (p := fun t ↦ f t = g t) hfg
    filter_upwards [ae_all_iff.2 this] with u hu
    exact Finset.prod_congr rfl fun i _ ↦ hu i
  have hae' : ∀ x : Fin n → ℝ,
      (fun u ↦ u * ∏ i, f (x i - u)) =ᵐ[volume] fun u ↦ u * ∏ i, g (x i - u) := by
    intro x
    filter_upwards [hae x] with u hu
    rw [hu]
  have hpit : pitmanEstimator (n := n) f = pitmanEstimator g := by
    funext x
    unfold pitmanEstimator
    rw [integral_congr_ae (hae x), integral_congr_ae (hae' x)]
  rw [hpit]
  refine pitmanEstimator_minimum_equivariant_risk_of_nonneg hn P g hg hg0 δ hm heq h2 ?_
  filter_upwards [hint] with x hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1.congr (hae x), h2.congr (hae' x), ?_⟩
  rw [← integral_congr_ae (hae x)]
  exact h3

end CKSD
