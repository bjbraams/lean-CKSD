module

import CKSD.Bayes.DirichletConjugacy.Multinomial
public import CKSD.Bayes.StickBreaking
public import TauCeti.Probability.Distributions.Dirichlet.Measurability
public import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Title

## Main definitions

## Main results

## Notation
-/


namespace CKSD

section PosteriorCells

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
open TauCeti TauCeti.Probability
open MeasurableSpace

variable {X : Type*} [MeasurableSpace X]

/-- The number of the observations `x l` lying in a set `A`, as a real number. -/
def sampleCount {n : ℕ} (x : Fin n → X) (A : Set X) : ℝ :=
  ∑ l, A.indicator (fun _ ↦ (1 : ℝ)) (x l)

omit [MeasurableSpace X] in
/-- Sample counts are nonnegative. -/
theorem sample_count_nonneg {n : ℕ} (x : Fin n → X) (A : Set X) : 0 ≤ sampleCount x A :=
  Finset.sum_nonneg fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

/-- The sample count of a measurable set is a measurable function of the sample. -/
theorem measurable_sample_count {n : ℕ} {A : Set X} (hA : MeasurableSet A) :
    Measurable fun x : Fin n → X ↦ sampleCount x A :=
  Finset.measurable_sum _ fun l _ ↦ (measurable_const.indicator hA).comp (measurable_pi_apply l)

omit [MeasurableSpace X] in
/-- If each observation `x l` lies in the cell `A (c l)` of a disjoint family, the sample counts
of the cells are the cell counts of `c`. -/
theorem sample_count_eq_cell_count {ι : Type*} [DecidableEq ι] {A : ι → Set X}
    (hAd : Pairwise (Disjoint on A)) {n : ℕ} {c : Fin n → ι} {x : Fin n → X}
    (hx : ∀ l, x l ∈ A (c l)) (i : ι) : sampleCount x (A i) = cellCount c i := by
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  by_cases h : c l = i
  · subst h
    simp [Set.indicator_of_mem (hx l)]
  · simp [h, Set.indicator_of_notMem (Set.disjoint_left.mp (hAd h) (hx l))]

/-- The measurable sets contained in a cell of `A` or in the complement of its union. -/
def subcellSets {ι : Type*} (A : ι → Set X) : Set (Set X) :=
  {B | MeasurableSet B ∧ ((∃ i, B ⊆ A i) ∨ B ⊆ (⋃ i, A i)ᶜ)}

/-- The sets contained in a cell form a π-system. -/
theorem is_pi_system_subcell_sets {ι : Type*} (A : ι → Set X) : IsPiSystem (subcellSets A) := by
  rintro B ⟨hB, hB'⟩ B' ⟨hB'm, -⟩ -
  refine ⟨hB.inter hB'm, ?_⟩
  rcases hB' with ⟨i, hi⟩ | h
  · exact Or.inl ⟨i, inter_subset_left.trans hi⟩
  · exact Or.inr (inter_subset_left.trans h)

/-- The sets contained in a cell of a measurable family generate the σ-algebra. -/
theorem generate_from_subcell_sets {ι : Type*} [Finite ι] {A : ι → Set X}
    (hAm : ∀ i, MeasurableSet (A i)) : generateFrom (subcellSets A) = ‹MeasurableSpace X› := by
  refine le_antisymm (generateFrom_le fun B hB ↦ hB.1) fun S hS ↦ ?_
  have hU : S = (⋃ i, S ∩ A i) ∪ (S ∩ (⋃ i, A i)ᶜ) := by
    ext x
    by_cases hx : x ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      simp only [mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff]
      exact ⟨fun h ↦ Or.inl ⟨i, h, hi⟩, fun h ↦ h.elim (fun ⟨_, h, _⟩ ↦ h) And.left⟩
    · simp only [mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff]
      exact ⟨fun h ↦ Or.inr ⟨h, by simpa using hx⟩, fun h ↦ h.elim (fun ⟨_, h, _⟩ ↦ h) And.left⟩
  rw [hU]
  refine MeasurableSet.union (MeasurableSet.iUnion fun i ↦ measurableSet_generateFrom
    ⟨hS.inter (hAm i), Or.inl ⟨i, inter_subset_right⟩⟩) (measurableSet_generateFrom
    ⟨hS.inter (MeasurableSet.iUnion hAm).compl, Or.inr inter_subset_right⟩)

/-- The sets contained in a cell of a finite family are countably spanning. -/
theorem is_countably_spanning_subcell_sets {ι : Type*} [Fintype ι] {A : ι → Set X}
    (hAm : ∀ i, MeasurableSet (A i)) : IsCountablySpanning (subcellSets A) := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨fun k ↦ if h : k < Fintype.card ι then A (e.symm ⟨k, h⟩) else (⋃ i, A i)ᶜ,
    fun k ↦ ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨hAm _, Or.inl ⟨_, subset_rfl⟩⟩
    · exact ⟨(MeasurableSet.iUnion hAm).compl, Or.inr subset_rfl⟩
  · refine eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨e i, ?_⟩
      split_ifs with h
      · simpa using hi
      · exact absurd (e i).2 h
    · refine mem_iUnion.mpr ⟨Fintype.card ι, ?_⟩
      split_ifs with h
      · exact absurd h (lt_irrefl _)
      · exact hx

/-- **Posterior cell masses of a Dirichlet process.** Let the prior be the law of a Dirichlet
process with base `α`, let the data be an i.i.d. sample of size `n` from the random measure, and
let `post` be a posterior kernel. For a partition `A` into cells of positive `α`-mass whose
union has `α`-null complement, for almost every sample `x` the posterior law of the cell masses
is the Dirichlet law with parameters `α(A i)` plus the number of observations in `A i`. -/
theorem ae_map_posterior_eq_dirichlet_measure (α : Measure X) [IsFiniteMeasure α]
    (prior : Measure (ProbabilityMeasure X)) [IsProbabilityMeasure prior]
    (hprior : IsDirichletProcess prior id α) {n : ℕ}
    (Q : Kernel (ProbabilityMeasure X) (Fin n → X))
    (hQ : ∀ θ, Q θ = Measure.pi fun _ : Fin n ↦ (θ : Measure X))
    (post : Kernel (Fin n → X) (ProbabilityMeasure X)) (hpost : IsPosteriorKernel prior Q post)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : ι → Set X}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAc : α (⋃ i, A i)ᶜ = 0) (hApos : ∀ i, 0 < α (A i)) :
    ∀ᵐ x ∂(Q ∘ₘ prior), (post x).map (fun θ : ProbabilityMeasure X ↦
        WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) =
      dirichletMeasure fun i ↦ α.real (A i) + sampleCount x (A i) := by
  have : IsMarkovKernel Q := ⟨fun θ ↦ by rw [hQ]; infer_instance⟩
  have := hpost.1
  have hpA : Measurable fun θ : ProbabilityMeasure X ↦
      WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i) :=
    measurable_to_lp_measure_real (P := id) hprior.1 hAm
  have hb : ∀ (x : Fin n → X) i, 0 < α.real (A i) + sampleCount x (A i) := fun x i ↦
    add_pos_of_pos_of_nonneg (ENNReal.toReal_pos (hApos i).ne' (measure_ne_top _ _))
      (sample_count_nonneg x _)
  let K : Kernel (Fin n → X) (EuclideanSpace ℝ ι) :=
    ⟨fun x ↦ dirichletMeasure fun i ↦ α.real (A i) + sampleCount x (A i),
      measurable_dirichletMeasure.comp
        (measurable_pi_iff.mpr fun i ↦ (measurable_sample_count (hAm i)).const_add _)⟩
  have : IsMarkovKernel K := ⟨fun x ↦ isProbabilityMeasure_dirichletMeasure (hb x)⟩
  have := Kernel.IsMarkovKernel.map post hpA
  have hQS : ∀ (θ : ProbabilityMeasure X) (B : Fin n → Set X),
      Q θ (univ.pi B) = ∏ l, (θ : Measure X) (B l) := fun θ B ↦ by rw [hQ, Measure.pi_pi]
  have hνS : ∀ B : Fin n → Set X, (∀ l, MeasurableSet (B l)) →
      (Q ∘ₘ prior) (univ.pi B) = ∫⁻ θ, ∏ l, (θ : Measure X) (B l) ∂prior := fun B hB ↦ by
    rw [Measure.bind_apply (MeasurableSet.univ_pi hB) Q.measurable.aemeasurable]
    simp_rw [hQS]
  have hL : ∀ B : Fin n → Set X, (∀ l, MeasurableSet (B l)) → ∀ U, MeasurableSet U →
      ((Q ∘ₘ prior) ⊗ₘ post.map fun θ : ProbabilityMeasure X ↦
        WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) (univ.pi B ×ˢ U) =
      ∫⁻ θ in (fun θ : ProbabilityMeasure X ↦
        WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ⁻¹' U,
        ∏ l, (θ : Measure X) (B l) ∂prior := by
    intro B hB U hU
    have hS := MeasurableSet.univ_pi hB
    rw [Measure.compProd_apply_prod hS hU]
    simp_rw [Kernel.map_apply _ hpA, Measure.map_apply hpA hU]
    rw [← Measure.compProd_apply_prod hS (hpA hU), ← hpost.2,
      Measure.map_apply measurable_swap (hS.prod (hpA hU)), preimage_swap_prod,
      Measure.compProd_apply_prod (hpA hU) hS]
    simp_rw [hQS]
  have hgen : (inferInstance : MeasurableSpace ((Fin n → X) × EuclideanSpace ℝ ι)) =
      generateFrom (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : Fin n ↦ subcellSets A)
        {U : Set (EuclideanSpace ℝ ι) | MeasurableSet U}) := by
    rw [← generateFrom_prod_eq (IsCountablySpanning.pi fun _ ↦ is_countably_spanning_subcell_sets hAm)
      isCountablySpanning_measurableSet, ← generateFrom_pi_eq fun _ ↦
      is_countably_spanning_subcell_sets hAm, generate_from_subcell_sets hAm, generateFrom_measurableSet]
  have hpi : IsPiSystem (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : Fin n ↦ subcellSets A)
      {U : Set (EuclideanSpace ℝ ι) | MeasurableSet U}) :=
    (IsPiSystem.pi fun _ ↦ is_pi_system_subcell_sets A).prod isPiSystem_measurableSet
  have heq : (Q ∘ₘ prior) ⊗ₘ (post.map fun θ : ProbabilityMeasure X ↦
      WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) = (Q ∘ₘ prior) ⊗ₘ K := by
    refine ext_of_generate_finite _ hgen hpi ?_ (by rw [measure_univ, measure_univ])
    rintro _ ⟨_, ⟨B, hB, rfl⟩, U, hU, rfl⟩
    have hBm : ∀ l, MeasurableSet (B l) := fun l ↦ (hB l (mem_univ l)).1
    have hS := MeasurableSet.univ_pi hBm
    rw [hL B hBm U hU, Measure.compProd_apply_prod hS hU]
    by_cases hc : ∀ l, ∃ i, B l ⊆ A i
    · choose c hc using hc
      have hbc : ∀ i, 0 < α.real (A i) + cellCount c i := fun i ↦
        add_pos_of_pos_of_nonneg (ENNReal.toReal_pos (hApos i).ne' (measure_ne_top _ _))
          (cell_count_nonneg c i)
      have := isProbabilityMeasure_dirichletMeasure hbc
      have hK : ∀ x ∈ univ.pi B,
          K x U = dirichletMeasure (fun i ↦ α.real (A i) + cellCount c i) U := by
        intro x hx
        have hcnt : (fun i ↦ α.real (A i) + sampleCount x (A i)) =
            fun i ↦ α.real (A i) + cellCount c i := funext fun i ↦ by
          rw [sample_count_eq_cell_count hAd (fun l ↦ hc l (hx l (mem_univ l))) i]
        show dirichletMeasure _ U = _
        rw [hcnt]
      rw [setLIntegral_congr_fun hS hK, setLIntegral_const, hνS B hBm]
      have hgm : Measurable fun θ : ProbabilityMeasure X ↦ ∏ l, (θ : Measure X).real (B l) :=
        Finset.measurable_prod _ fun l _ ↦ (hprior.1 _ (hBm l)).ennreal_toReal
      have hg01 : ∀ θ : ProbabilityMeasure X, 0 ≤ ∏ l, (θ : Measure X).real (B l) ∧
          ∏ l, (θ : Measure X).real (B l) ≤ 1 := fun θ ↦
        ⟨Finset.prod_nonneg fun _ _ ↦ measureReal_nonneg,
          Finset.prod_le_one₀ (fun _ _ ↦ measureReal_nonneg) fun _ _ ↦ measureReal_le_one⟩
      have hg : ∀ θ : ProbabilityMeasure X, ∏ l, (θ : Measure X) (B l) =
          ENNReal.ofReal (∏ l, (θ : Measure X).real (B l)) := fun θ ↦ by
        rw [ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ measureReal_nonneg]
        exact Finset.prod_congr rfl fun l _ ↦ by rw [ofReal_measureReal]
      simp_rw [hg]
      rw [← lintegral_indicator (hpA hU)]
      have hind : ∀ θ : ProbabilityMeasure X, ((fun θ : ProbabilityMeasure X ↦
          WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ⁻¹' U).indicator
          (fun θ ↦ ENNReal.ofReal (∏ l, (θ : Measure X).real (B l))) θ =
          ENNReal.ofReal (U.indicator 1 (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) *
            ∏ l, (θ : Measure X).real (B l)) := fun θ ↦ by
        by_cases h : (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ∈ U
        · have hθ : θ ∈ (fun θ : ProbabilityMeasure X ↦
              WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ⁻¹' U := h
          rw [indicator_of_mem hθ, indicator_of_mem h, Pi.one_apply, one_mul]
        · have hθ : θ ∉ (fun θ : ProbabilityMeasure X ↦
              WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ⁻¹' U := h
          rw [indicator_of_notMem hθ, indicator_of_notMem h, zero_mul, ENNReal.ofReal_zero]
      simp_rw [hind]
      have hint : Integrable (fun θ : ProbabilityMeasure X ↦ ∏ l, (θ : Measure X).real (B l))
          prior :=
        Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun θ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg01 θ).1]; exact (hg01 θ).2)
      have hint' : Integrable (fun θ : ProbabilityMeasure X ↦
          U.indicator 1 (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) *
            ∏ l, (θ : Measure X).real (B l)) prior := by
        refine Integrable.of_bound (((measurable_one.indicator hU).comp hpA).mul
          hgm).aestronglyMeasurable 1 (Eventually.of_forall fun θ ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg01 θ).1]
        have h1 : |U.indicator (1 : EuclideanSpace ℝ ι → ℝ)
            (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i))| ≤ 1 := by
          by_cases h : (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) ∈ U
          · rw [indicator_of_mem h, Pi.one_apply, abs_one]
          · rw [indicator_of_notMem h, abs_zero]
            exact zero_le_one
        calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 (hg01 θ).2 (hg01 θ).1 zero_le_one
          _ = 1 := one_mul 1
      rw [← ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall fun θ ↦
          mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hg01 θ).1),
        ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun θ ↦ (hg01 θ).1)]
      have hW := integral_mul_prod_measure_real_of_subset (P := id) hprior hAm hAd hAc hApos hBm hc
        (H := U.indicator 1) (measurable_one.indicator hU) (C := 1) fun y ↦ by
          by_cases h : y ∈ U
          · rw [indicator_of_mem h, Pi.one_apply, abs_one]
          · rw [indicator_of_notMem h, abs_zero]
            exact zero_le_one
      rw [integral_indicator_one hU] at hW
      simp only [id_eq] at hW
      rw [show ∫ θ, U.indicator 1 (WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i)) *
          ∏ l, (θ : Measure X).real (B l) ∂prior = _ from hW,
        ENNReal.ofReal_mul (integral_nonneg fun θ ↦ (hg01 θ).1), ofReal_measureReal, mul_comm]
    · push Not at hc
      obtain ⟨l₀, hl₀⟩ := hc
      have hB0 : B l₀ ⊆ (⋃ i, A i)ᶜ :=
        (hB l₀ (mem_univ _)).2.resolve_left fun ⟨i, hi⟩ ↦ hl₀ i hi
      have hnull : ∀ᵐ θ : ProbabilityMeasure X ∂prior, (θ : Measure X) (B l₀) = 0 :=
        hprior.2.1 _ (hBm l₀) (measure_mono_null hB0 hAc)
      have h0 : ∫⁻ θ, ∏ l, (θ : Measure X) (B l) ∂prior = 0 :=
        (lintegral_congr_ae (hnull.mono fun θ h ↦ Finset.prod_eq_zero (Finset.mem_univ l₀) h)).trans
          lintegral_zero
      rw [le_antisymm ((setLIntegral_le_lintegral _ _).trans h0.le) zero_le, eq_comm]
      refine le_antisymm ?_ zero_le
      calc ∫⁻ x in univ.pi B, K x U ∂(Q ∘ₘ prior) ≤ ∫⁻ _ in univ.pi B, 1 ∂(Q ∘ₘ prior) :=
            lintegral_mono fun x ↦ prob_le_one
        _ = 0 := by rw [setLIntegral_one, hνS B hBm, h0]
  filter_upwards [Kernel.ae_eq_of_compProd_eq heq] with x hx
  rw [← Kernel.map_apply _ hpA, hx]
  rfl

end PosteriorCells

section Uniqueness

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
open TauCeti TauCeti.Probability
open MeasurableSpace

variable {X : Type*} [MeasurableSpace X]

/-- The masses that a probability measure gives to the cells of the `m`-th finite partition
generated by a sequence of sets `t`. -/
def memPartitionMasses (t : ℕ → Set X) (m : ℕ) (θ : ProbabilityMeasure X) :
    memPartition t m → ℝ≥0∞ :=
  fun u ↦ (θ : Measure X) u

/-- The σ-algebra on probability measures generated by the cell masses of the `m`-th partition
generated by `t`. -/
abbrev memPartitionMassesSpace (t : ℕ → Set X) (m : ℕ) : MeasurableSpace (ProbabilityMeasure X) :=
  MeasurableSpace.comap (memPartitionMasses t m) inferInstance

/-- The cell masses of a finite partition into measurable cells depend measurably on the
probability measure. -/
theorem measurable_mem_partition_masses {t : ℕ → Set X} (ht : ∀ n, MeasurableSet (t n)) (m : ℕ) :
    Measurable (memPartitionMasses t m) :=
  measurable_pi_iff.mpr fun u ↦
    (Measure.measurable_coe (measurableSet_memPartition ht m u.2)).comp measurable_subtype_coe

/-- The mass of a union of cells of the `m`-th partition is a measurable function of the cell
masses. -/
private theorem measurable_comap_mem_partition_masses {t : ℕ → Set X}
    (ht : ∀ n, MeasurableSet (t n)) (m : ℕ) {s : Set X}
    (hs : MeasurableSet[generateFrom (memPartition t m)] s) :
    Measurable[memPartitionMassesSpace t m]
      fun θ : ProbabilityMeasure X ↦ (θ : Measure X) s := by
  obtain ⟨F, hF, rfl⟩ := (measurableSet_generateFrom_memPartition_iff t m s).mp hs
  have hsum : (fun θ : ProbabilityMeasure X ↦ (θ : Measure X) (⋃₀ ↑F)) =
      fun θ ↦ ∑ u ∈ F.attach, memPartitionMasses t m θ ⟨u.1, hF u.2⟩ := by
    funext θ
    have hU : ⋃₀ (↑F : Set (Set X)) = ⋃ u ∈ F, u := by
      ext x
      simp
    rw [hU, measure_biUnion_finset
      (fun u hu v hv huv ↦ disjoint_memPartition t m (hF hu) (hF hv) huv)
      fun u hu ↦ measurableSet_memPartition ht m (hF hu)]
    exact (Finset.sum_attach F fun u ↦ (θ : Measure X) u).symm
  rw [hsum]
  refine Finset.measurable_sum _ fun u _ ↦ ?_
  have := (measurable_pi_apply (⟨u.1, hF u.2⟩ : memPartition t m)).comp
    (comap_measurable (m := (inferInstance : MeasurableSpace (memPartition t m → ℝ≥0∞)))
      (memPartitionMasses t m))
  exact this

/-- **Uniqueness of laws of random measures.** Two laws of random probability measures on a
space whose σ-algebra is generated by a sequence of measurable sets `t` agree as soon as they
give the same laws to the cell masses of every finite partition `memPartition t m`. -/
theorem ext_of_map_mem_partition_masses {t : ℕ → Set X} (ht : ∀ n, MeasurableSet (t n))
    (htgen : generateFrom (range t) = ‹MeasurableSpace X›)
    {Q₁ Q₂ : Measure (ProbabilityMeasure X)} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    (h : ∀ m, Q₁.map (memPartitionMasses t m) = Q₂.map (memPartitionMasses t m)) :
    Q₁ = Q₂ := by
  have hmono : Monotone fun m ↦ generateFrom (memPartition t m) :=
    monotone_nat_of_le_succ (generateFrom_memPartition_le_succ t)
  have hcomap_mono : Monotone fun m ↦
      memPartitionMassesSpace t m := by
    intro k m hkm
    refine Measurable.comap_le ?_
    exact @measurable_pi_iff _ _ _ (memPartitionMassesSpace t m) _ _ |>.mpr fun u ↦
      measurable_comap_mem_partition_masses ht m (hmono hkm _ (measurableSet_generateFrom u.2))
  let T : Set (Set (ProbabilityMeasure X)) := ⋃ m,
    {E | MeasurableSet[memPartitionMassesSpace t m] E}
  have hT : IsPiSystem T := isPiSystem_iUnion_of_monotone _
    (fun m ↦ @isPiSystem_measurableSet _ (memPartitionMassesSpace t m))
    fun k m hkm E hE ↦ hcomap_mono hkm E hE
  have hgen : (inferInstance : MeasurableSpace (ProbabilityMeasure X)) = generateFrom T := by
    refine le_antisymm ?_ (generateFrom_le fun E hE ↦ ?_)
    · have hS : ‹MeasurableSpace X› =
          generateFrom (⋃ m, {s | MeasurableSet[generateFrom (memPartition t m)] s}) := by
        refine le_antisymm ?_ (generateFrom_le fun s hs ↦ ?_)
        · rw [← htgen, ← generateFrom_iUnion_memPartition]
          exact generateFrom_mono (iUnion_mono fun m u hu ↦ measurableSet_generateFrom hu)
        · obtain ⟨m, hm⟩ := mem_iUnion.mp hs
          exact generateFrom_memPartition_le ht m s hm
      have hpiS : IsPiSystem (⋃ m, {s | MeasurableSet[generateFrom (memPartition t m)] s}) :=
        isPiSystem_iUnion_of_monotone _
          (fun m ↦ @isPiSystem_measurableSet X (generateFrom (memPartition t m)))
          fun k m hkm s hs ↦ hmono hkm s hs
      have hmeas : Measurable[generateFrom T] fun θ : ProbabilityMeasure X ↦ (θ : Measure X) :=
        Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hS hpiS fun s hs ↦ by
          obtain ⟨m, hm⟩ := mem_iUnion.mp hs
          exact (measurable_comap_mem_partition_masses ht m hm).mono
            (fun E hE ↦ measurableSet_generateFrom (mem_iUnion.mpr ⟨m, hE⟩)) le_rfl
      exact hmeas.comap_le
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hE
      exact (measurable_mem_partition_masses ht m).comap_le E hm
  refine ext_of_generate_finite T hgen hT (fun E hE ↦ ?_) (by rw [measure_univ, measure_univ])
  obtain ⟨m, V, hV, rfl⟩ := mem_iUnion.mp hE
  rw [← Measure.map_apply (measurable_mem_partition_masses ht m) hV, h m,
    Measure.map_apply (measurable_mem_partition_masses ht m) hV]

end Uniqueness

section Conjugacy

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
open TauCeti TauCeti.Probability
open MeasurableSpace

variable {X : Type*} [MeasurableSpace X]

/-- The posterior base measure of a measurable set is its prior mass plus its sample count. -/
theorem measure_real_dirichlet_posterior_base (α : Measure X) [IsFiniteMeasure α] {n : ℕ}
    (x : Fin n → X) {A : Set X} (hA : MeasurableSet A) :
    (dirichletPosteriorBase α x).real A = α.real A + sampleCount x A := by
  have hδ : ∀ l, Measure.dirac (x l) A = ENNReal.ofReal (A.indicator (fun _ ↦ (1 : ℝ)) (x l)) :=
    fun l ↦ by
      rw [Measure.dirac_apply' _ hA]
      by_cases h : x l ∈ A
      · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, ENNReal.ofReal_one]
      · rw [indicator_of_notMem h, indicator_of_notMem h, ENNReal.ofReal_zero]
  simp only [Measure.real, dirichletPosteriorBase, add_apply, sum_apply, hδ]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.sum_ne_top.mpr fun _ _ ↦
    ENNReal.ofReal_ne_top), ENNReal.toReal_sum fun _ _ ↦ ENNReal.ofReal_ne_top]
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ ENNReal.toReal_ofReal
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

/-- A law of random measures whose cell masses on the null cells of a finite partition vanish
and whose cell masses on the remaining cells are Dirichlet-distributed has an explicit law of
the vector of all cell masses. -/
private theorem map_mem_partition_masses_eq {t : ℕ → Set X} (ht : ∀ n, MeasurableSet (t n))
    (m : ℕ) (p : memPartition t m → Prop) [DecidablePred p]
    {Q' : Measure (ProbabilityMeasure X)}
    (hnull : ∀ u, ¬ p u → ∀ᵐ θ : ProbabilityMeasure X ∂Q', (θ : Measure X) (u : Set X) = 0)
    (b : {u // p u} → ℝ)
    (hpos : Q'.map (fun θ : ProbabilityMeasure X ↦
      WithLp.toLp 2 fun u : {u // p u} ↦ (θ : Measure X).real u.1) = dirichletMeasure b) :
    Q'.map (memPartitionMasses t m) = (dirichletMeasure b).map
      fun y u ↦ if h : p u then ENNReal.ofReal (y ⟨u, h⟩) else 0 := by
  have hΦ : Measurable fun (y : EuclideanSpace ℝ {u // p u}) (u : memPartition t m) ↦
      if h : p u then ENNReal.ofReal (y ⟨u, h⟩) else 0 := by
    refine measurable_pi_iff.mpr fun u ↦ ?_
    by_cases h : p u
    · simp only [h, dite_true]
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · simp only [h, dite_false]
      exact measurable_const
  have hv : Measurable fun θ : ProbabilityMeasure X ↦
      WithLp.toLp 2 fun u : {u // p u} ↦ (θ : Measure X).real u.1 :=
    measurable_to_lp_measure_real (P := id)
    (fun A hA ↦ (Measure.measurable_coe hA).comp measurable_subtype_coe)
    (R := fun u : {u // p u} ↦ (u.1 : Set X)) fun u ↦ measurableSet_memPartition ht m u.1.2
  rw [← hpos, Measure.map_map hΦ hv]
  refine Measure.map_congr ?_
  have hall : ∀ᵐ θ : ProbabilityMeasure X ∂Q', ∀ u, ¬ p u → (θ : Measure X) (u : Set X) = 0 := by
    rw [ae_all_iff]
    intro u
    by_cases hu : p u
    · exact Eventually.of_forall fun _ h ↦ absurd hu h
    · filter_upwards [hnull u hu] with θ hθ _ using hθ
  filter_upwards [hall] with θ hθ
  funext u
  by_cases h : p u
  · simp only [memPartitionMasses, Function.comp_apply, h, dite_true]
    rw [ofReal_measureReal]
  · simp only [memPartitionMasses, Function.comp_apply, h, dite_false]
    exact hθ u h

/-- **Conjugacy of the Dirichlet process.** Let the prior be the law of a Dirichlet process with
base `α ≠ 0` on a countably generated space, let the data be an i.i.d. sample of size `n` from
the random measure, and let `post` be a posterior kernel. If a Dirichlet process law exists for
each posterior base measure `α + ∑ₗ δ_{x l}`, then for almost every sample the posterior is the
Dirichlet process law with that base measure. -/
theorem ae_is_dirichlet_process_posterior [CountablyGenerated X] (α : Measure X)
    [IsFiniteMeasure α] (hα : α ≠ 0)
    (prior : Measure (ProbabilityMeasure X)) [IsProbabilityMeasure prior]
    (hprior : IsDirichletProcess prior id α) {n : ℕ}
    (Q : Kernel (ProbabilityMeasure X) (Fin n → X))
    (hQ : ∀ θ, Q θ = Measure.pi fun _ : Fin n ↦ (θ : Measure X))
    (post : Kernel (Fin n → X) (ProbabilityMeasure X)) (hpost : IsPosteriorKernel prior Q post)
    (hex : ∀ x : Fin n → X, ∃ D : Measure (ProbabilityMeasure X), IsProbabilityMeasure D ∧
      IsDirichletProcess D id (dirichletPosteriorBase α x)) :
    ∀ᵐ x ∂(Q ∘ₘ prior), IsDirichletProcess (post x) id (dirichletPosteriorBase α x) := by
  classical
  have : IsMarkovKernel Q := ⟨fun θ ↦ by rw [hQ]; infer_instance⟩
  have := hpost.1
  set t := natGeneratingSequence X
  have ht : ∀ k, MeasurableSet (t k) := measurableSet_natGeneratingSequence
  have htgen : generateFrom (range t) = ‹MeasurableSpace X› := generateFrom_natGeneratingSequence X
  have hcell : ∀ m (u : memPartition t m), MeasurableSet (u : Set X) := fun m u ↦
    measurableSet_memPartition ht m u.2
  have hmθ : ∀ {A : Set X}, MeasurableSet A →
      Measurable fun θ : ProbabilityMeasure X ↦ (θ : Measure X) A := fun hA ↦
    (Measure.measurable_coe hA).comp measurable_subtype_coe
  have hnot : ∀ {c : ℝ≥0∞}, ¬ 0 < c → c = 0 := fun h ↦ le_antisymm (not_lt.mp h) zero_le
  -- the sets of `α`-null cells and of the cells of positive `α`-mass
  have hcompl : ∀ m (β : Measure X), (∀ u : memPartition t m, ¬ 0 < α u.1 → β u.1 = 0) →
      β (⋃ u : {u : memPartition t m // 0 < α u.1}, (u.1 : Set X))ᶜ = 0 := by
    intro m β hβ
    refine measure_mono_null (t := ⋃ u : {u : memPartition t m // ¬ 0 < α u.1}, (u.1 : Set X))
      (fun x hx ↦ ?_) (measure_iUnion_null fun u ↦ hβ u.1 u.2)
    have hxu : x ∈ ⋃₀ memPartition t m := by
      rw [sUnion_memPartition]
      trivial
    obtain ⟨v, hv, hxv⟩ := hxu
    by_cases hp : 0 < α v
    · exact absurd (mem_iUnion.mpr ⟨⟨⟨v, hv⟩, hp⟩, hxv⟩) hx
    · exact mem_iUnion.mpr ⟨⟨⟨v, hv⟩, hp⟩, hxv⟩
  have hdisj : ∀ m, Pairwise (Disjoint on fun u : {u : memPartition t m // 0 < α u.1} ↦
      (u.1 : Set X)) := fun m u v huv ↦
    disjoint_memPartition t m u.1.2 v.1.2 fun h ↦ huv (Subtype.ext (Subtype.ext h))
  -- almost surely, no observation lies in an `α`-null cell
  have hG1 : ∀ᵐ x ∂(Q ∘ₘ prior), ∀ m (u : memPartition t m), α u.1 = 0 →
      ∀ l, x l ∉ (u : Set X) := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro u
    by_cases hu : α u.1 = 0
    swap
    · exact Eventually.of_forall fun _ h ↦ absurd h hu
    have hx : ∀ᵐ x ∂(Q ∘ₘ prior), ∀ l, x l ∉ (u : Set X) := by
      rw [ae_all_iff]
      intro l
      rw [ae_iff]
      simp only [not_not]
      rw [Measure.bind_apply (s := {x : Fin n → X | x l ∈ (u : Set X)})
        (measurable_pi_apply l (hcell m u)) Q.measurable.aemeasurable]
      have h0 : (fun θ ↦ Q θ {x : Fin n → X | x l ∈ (u : Set X)}) =ᵐ[prior] fun _ ↦ 0 := by
        filter_upwards [hprior.2.1 _ (hcell m u) hu] with θ hθ
        rw [hQ]
        exact Measure.pi_eval_preimage_null _ hθ
      exact (lintegral_congr_ae h0).trans lintegral_zero
    filter_upwards [hx] with x hx _ using hx
  -- almost surely, the posterior gives no mass to `α`-null cells
  have hG2 : ∀ᵐ x ∂(Q ∘ₘ prior), ∀ m (u : memPartition t m), α u.1 = 0 →
      ∀ᵐ θ : ProbabilityMeasure X ∂(post x), (θ : Measure X) (u : Set X) = 0 := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro u
    by_cases hu : α u.1 = 0
    swap
    · exact Eventually.of_forall fun _ h ↦ absurd h hu
    have hj : ∀ᵐ w ∂((Q ∘ₘ prior) ⊗ₘ post), (w.2 : Measure X) (u : Set X) = 0 := by
      rw [← hpost.2, ae_map_iff (p := fun w : (Fin n → X) × ProbabilityMeasure X ↦
        (w.2 : Measure X) (u : Set X) = 0) measurable_swap.aemeasurable
        (measurableSet_eq_fun ((hmθ (hcell m u)).comp measurable_snd) measurable_const)]
      have h1 : ∀ᵐ θ : ProbabilityMeasure X ∂(prior ⊗ₘ Q).fst, (θ : Measure X) (u : Set X) = 0 := by
        rw [Measure.fst_compProd]
        exact hprior.2.1 _ (hcell m u) hu
      exact ae_of_ae_map measurable_fst.aemeasurable h1
    filter_upwards [Measure.ae_ae_of_ae_compProd hj] with x hx _ using hx
  have hne : ∀ m, Nonempty {u : memPartition t m // 0 < α u.1} := by
    intro m
    by_contra h
    rw [not_nonempty_iff] at h
    apply hα
    refine Measure.measure_univ_eq_zero.mp ?_
    have := hcompl m α fun u hu ↦ hnot hu
    rwa [iUnion_of_empty, compl_empty] at this
  -- almost surely, the posterior law of the masses of the positive cells is Dirichlet
  have hG3 : ∀ᵐ x ∂(Q ∘ₘ prior), ∀ m, (post x).map (fun θ : ProbabilityMeasure X ↦
      WithLp.toLp 2 fun u : {u : memPartition t m // 0 < α u.1} ↦ (θ : Measure X).real u.1) =
      dirichletMeasure fun u ↦ α.real u.1 + sampleCount x u.1 := by
    rw [ae_all_iff]
    intro m
    have := hne m
    exact ae_map_posterior_eq_dirichlet_measure α prior hprior Q hQ post hpost
      (A := fun u : {u : memPartition t m // 0 < α u.1} ↦ (u.1 : Set X)) (fun u ↦ hcell m u.1)
      (hdisj m) (hcompl m α fun u hu ↦ hnot hu) fun u ↦ u.2
  filter_upwards [hG1, hG2, hG3] with x h1 h2 h3
  obtain ⟨D, hDprob, hD⟩ := hex x
  have : IsFiniteMeasure (dirichletPosteriorBase α x) := by
    unfold dirichletPosteriorBase
    infer_instance
  have hβnull : ∀ m (u : memPartition t m), α u.1 = 0 → dirichletPosteriorBase α x u.1 = 0 := by
    intro m u hu
    simp only [dirichletPosteriorBase, add_apply, hu, zero_add, sum_apply]
    exact Finset.sum_eq_zero fun l _ ↦ by
      rw [Measure.dirac_apply' _ (hcell m u), indicator_of_notMem (h1 m u hu l)]
  have hpost_eq : post x = D := by
    refine ext_of_map_mem_partition_masses ht htgen fun m ↦ ?_
    have := hne m
    have hL := map_mem_partition_masses_eq ht m (fun u ↦ 0 < α u.1) (Q' := post x)
      (fun u hu ↦ h2 m u (hnot hu)) _ (h3 m)
    have hDpos : D.map (fun θ : ProbabilityMeasure X ↦
        WithLp.toLp 2 fun u : {u : memPartition t m // 0 < α u.1} ↦ (θ : Measure X).real u.1) =
        dirichletMeasure fun u ↦ α.real u.1 + sampleCount x u.1 := by
      have := map_cells_eq_dirichlet_measure hD
        (A := fun u : {u : memPartition t m // 0 < α u.1} ↦ (u.1 : Set X)) (fun u ↦ hcell m u.1)
        (hdisj m) (hcompl m _ fun u hu ↦ hβnull m u (hnot hu)) fun u ↦
          lt_of_lt_of_le u.2 (by simp only [dirichletPosteriorBase, add_apply]; exact le_self_add)
      simp only [id_eq] at this
      rw [this]
      congr 1
      funext u
      exact measure_real_dirichlet_posterior_base α x (hcell m u.1)
    have hR := map_mem_partition_masses_eq ht m (fun u ↦ 0 < α u.1) (Q' := D)
      (fun u hu ↦ hD.2.1 _ (hcell m u) (hβnull m u (hnot hu))) _ hDpos
    rw [hL, hR]
  rw [hpost_eq]
  exact hD

end Conjugacy


end CKSD
