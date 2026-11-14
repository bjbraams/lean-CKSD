module

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


open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
open TauCeti TauCeti.Probability
open MeasurableSpace

section MultinomialDirichlet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cell counts `#{l | jₗ = i}` of an assignment of `n` observations to cells, as reals. -/
def cellCount {n : ℕ} (j : Fin n → ι) (i : ι) : ℝ :=
  ∑ l, if j l = i then 1 else 0

omit [Fintype ι] in
/-- Cell counts are nonnegative. -/
theorem cell_count_nonneg {n : ℕ} (j : Fin n → ι) (i : ι) : 0 ≤ cellCount j i :=
  Finset.sum_nonneg fun l _ ↦ by split_ifs <;> norm_num

omit [Fintype ι] in
/-- Splitting off the first observation adds one to the count of its cell. -/
theorem cell_count_succ {n : ℕ} (j : Fin (n + 1) → ι) :
    cellCount j = Pi.single (j 0) 1 + cellCount (fun l : Fin n ↦ j l.succ) := by
  funext i
  simp only [cellCount, Fin.sum_univ_succ, Pi.add_apply, Pi.single_apply, eq_comm]

/-- **Multinomial–Dirichlet conjugacy.** Weighting the Dirichlet law `Dir(a)` by the likelihood
`∏ₗ y_{jₗ}` of an assignment `j` of `n` observations to cells gives, after normalization, the
Dirichlet law `Dir(a + counts(j))`. -/
theorem integral_prod_mul_dirichlet_measure [Nonempty ι] {n : ℕ} (j : Fin n → ι) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {g : EuclideanSpace ℝ ι → ℝ} (hg : Measurable g) :
    ∫ y, (∏ l, y (j l)) * g y ∂dirichletMeasure a =
      (∫ y, ∏ l, y (j l) ∂dirichletMeasure a) *
        ∫ y, g y ∂dirichletMeasure (a + cellCount j) := by
  induction n generalizing a with
  | zero =>
    have := isProbabilityMeasure_dirichletMeasure ha
    have h0 : cellCount j = 0 := funext fun i ↦ by simp [cellCount]
    simp [h0]
  | succ n ih =>
    have hs : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
    have ha' : ∀ i, 0 < (a + Pi.single (j 0) 1 : ι → ℝ) i := fun i ↦ by
      by_cases h : i = j 0
      · rw [h]; simp; linarith [ha (j 0)]
      · simp [Pi.single_eq_of_ne h, ha i]
    have htilt : ∀ {f : EuclideanSpace ℝ ι → ℝ}, Measurable f →
        ∫ y, y (j 0) * f y ∂dirichletMeasure a =
          a (j 0) / (∑ i, a i) * ∫ y, f y ∂dirichletMeasure (a + Pi.single (j 0) 1 : ι → ℝ) := by
      intro f hf
      rw [integral_dirichlet_measure_add_single ha (j 0) hf]
      have := ha (j 0)
      field_simp
    have hP : Measurable fun y : EuclideanSpace ℝ ι ↦ ∏ l : Fin n, y (j l.succ) :=
      Finset.measurable_prod _ fun l _ ↦ by fun_prop
    simp only [Fin.prod_univ_succ]
    have e1 : ∫ y, (y (j 0) * ∏ l : Fin n, y (j l.succ)) * g y ∂dirichletMeasure a =
        ∫ y, y (j 0) * ((∏ l : Fin n, y (j l.succ)) * g y) ∂dirichletMeasure a := by
      congr 1
      funext y
      ring
    rw [e1, htilt (f := fun y ↦ (∏ l : Fin n, y (j l.succ)) * g y) (hP.mul hg), htilt hP,
      ih (fun l ↦ j l.succ) ha', cell_count_succ, add_assoc]
    ring

end MultinomialDirichlet

section PartitionMarginals

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The Dirichlet marginal of a Dirichlet process on a partition indexed by any finite type:
`IsDirichletProcess` states it for partitions indexed by `Fin k`, and the Dirichlet laws are
compatible with reindexing (TauCeti's aggregation law along a bijection). -/
theorem map_cells_eq_dirichlet_measure {ι : Type*} [Fintype ι] [Nonempty ι] {μ : Measure Ω}
    {P : Ω → ProbabilityMeasure X} {α : Measure X} [IsFiniteMeasure α]
    (hP : IsDirichletProcess μ P α)
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAc : α (⋃ i, A i)ᶜ = 0) (hApos : ∀ i, 0 < α (A i)) :
    μ.map (fun ω ↦ WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i)) =
      dirichletMeasure fun i ↦ α.real (A i) := by
  classical
  set e := Fintype.equivFin ι
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  have hd : Pairwise (Disjoint on (A ∘ e.symm)) := fun i j hij ↦
    hAd (e.symm.injective.ne hij)
  have hu : (⋃ i, (A ∘ e.symm) i) = ⋃ i, A i := e.symm.surjective.iUnion_comp A
  have hmap := hP.2.2 _ hk (A ∘ e.symm) (fun i ↦ hAm _) hd (by rw [hu]; exact hAc)
    (fun i ↦ hApos _)
  have hmeas : Measurable fun ω ↦ WithLp.toLp 2 fun i ↦ (P ω : Measure X).real ((A ∘ e.symm) i) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦
      (hP.1 _ (hAm _)).ennreal_toReal)
  have hpos : ∀ i, 0 < α.real ((A ∘ e.symm) i) := fun i ↦
    ENNReal.toReal_pos (hApos _).ne' (measure_ne_top _ _)
  have hagg := map_euclideanFiberSum_dirichletMeasure e.symm.surjective hpos
  have hfib : ∀ (v : Fin (Fintype.card ι) → ℝ) (i : ι),
      ∑ j with e.symm j = i, v j = v (e i) := fun v i ↦ by
    rw [Finset.sum_eq_single (e i) (fun b hb hbi ↦ absurd (by simpa using hb) (by
      intro h; exact hbi (by rw [← h, Equiv.apply_symm_apply])))
      (fun h ↦ absurd (by simp) h)]
  have hcomp : (euclideanFiberSum e.symm ∘ fun ω ↦
      WithLp.toLp 2 fun i ↦ (P ω : Measure X).real ((A ∘ e.symm) i)) =
      fun ω ↦ WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i) := by
    funext ω
    ext i
    simp only [comp_apply, euclideanFiberSum_apply]
    rw [hfib (fun j ↦ (P ω : Measure X).real (A (e.symm j))) i, Equiv.symm_apply_apply]
  have hparam : (fun i ↦ ∑ j with e.symm j = i, α.real ((A ∘ e.symm) j)) =
      fun i ↦ α.real (A i) := by
    funext i
    rw [hfib (fun j ↦ α.real ((A ∘ e.symm) j)) i]
    simp
  rw [← hcomp, ← Measure.map_map (measurable_euclideanFiberSum _) hmeas, hmap, hagg, hparam]

end PartitionMarginals

section Refinement

variable {X : Type*} [MeasurableSpace X] {ι : Type*} {n : ℕ}

/-- The cells of the common refinement of a partition `A` and the sets `B₁, …, Bₙ`. -/
private def refineCell (A : ι → Set X) (B : Fin n → Set X) (k : ι × (Fin n → Bool)) : Set X :=
  A k.1 ∩ ⋂ l, if k.2 l then B l else (B l)ᶜ

omit [MeasurableSpace X] in
/-- Membership in a refined cell. -/
private theorem mem_refine_cell {A : ι → Set X} {B : Fin n → Set X} {k : ι × (Fin n → Bool)}
    {x : X} : x ∈ refineCell A B k ↔ x ∈ A k.1 ∧ ∀ l, (x ∈ B l ↔ k.2 l = true) := by
  simp only [refineCell, mem_inter_iff, mem_iInter]
  refine and_congr_right fun _ ↦ forall_congr' fun l ↦ ?_
  cases k.2 l <;> simp

/-- Refined cells are measurable. -/
private theorem measurable_set_refine_cell {A : ι → Set X} {B : Fin n → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ l, MeasurableSet (B l)) (k : ι × (Fin n → Bool)) :
    MeasurableSet (refineCell A B k) :=
  (hA _).inter (MeasurableSet.iInter fun l ↦ by
    split_ifs
    exacts [hB l, (hB l).compl])

omit [MeasurableSpace X] in
/-- Refined cells of a disjoint family are disjoint. -/
private theorem pairwise_disjoint_refine_cell {A : ι → Set X} (hA : Pairwise (Disjoint on A))
    (B : Fin n → Set X) : Pairwise (Disjoint on refineCell A B) := by
  rintro ⟨i, σ⟩ ⟨i', σ'⟩ hne
  refine Set.disjoint_left.mpr fun x hx hx' ↦ ?_
  rw [mem_refine_cell] at hx hx'
  by_cases hi : i = i'
  · subst hi
    have : σ ≠ σ' := fun h ↦ hne (by rw [h])
    obtain ⟨l, hl⟩ := Function.ne_iff.mp this
    exact hl (Bool.eq_iff_iff.mpr ((hx.2 l).symm.trans (hx'.2 l)))
  · exact (hA hi).le_bot ⟨hx.1, hx'.1⟩

omit [MeasurableSpace X] in
/-- The refined cells of `A i` cover it. -/
private theorem exists_mem_refine_cell {A : ι → Set X} (B : Fin n → Set X) {i : ι} {x : X}
    (hx : x ∈ A i) : ∃ σ, x ∈ refineCell A B (i, σ) := by
  classical
  exact ⟨fun l ↦ decide (x ∈ B l), mem_refine_cell.mpr ⟨hx, fun l ↦ by simp⟩⟩

/-- The measure of a union of refined cells is the sum of their measures. -/
private theorem measure_real_bi_union_refine_cell [Fintype ι] (ν : Measure X) [IsFiniteMeasure ν]
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    {B : Fin n → Set X} (hBm : ∀ l, MeasurableSet (B l)) (q : ι × (Fin n → Bool) → Prop)
    [DecidablePred q] :
    ν.real (⋃ k ∈ Finset.univ.filter q, refineCell A B k) =
      ∑ k with q k, ν.real (refineCell A B k) :=
  measureReal_biUnion_finset (fun _ _ _ _ h ↦ pairwise_disjoint_refine_cell hAd B h)
    fun k _ ↦ measurable_set_refine_cell hAm hBm k

omit [MeasurableSpace X] in
/-- A cell of `A` is the union of its refined cells. -/
private theorem bi_union_refine_cell_fst [Fintype ι] [DecidableEq ι] (A : ι → Set X)
    (B : Fin n → Set X) (i : ι) :
    ⋃ k ∈ Finset.univ.filter (fun k : ι × (Fin n → Bool) ↦ k.1 = i), refineCell A B k = A i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion, exists_prop]
  refine ⟨fun ⟨k, hk, hx⟩ ↦ hk ▸ (mem_refine_cell.mp hx).1, fun hx ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := exists_mem_refine_cell B hx
  exact ⟨(i, σ), rfl, hσ⟩

omit [MeasurableSpace X] in
/-- A set `B l` inside the cell `A (c l)` is the union of the refined cells of `A (c l)` lying
in `B l`. -/
private theorem bi_union_refine_cell_of_subset [Fintype ι] [DecidableEq ι] {A : ι → Set X}
    {B : Fin n → Set X} {c : Fin n → ι} (hBc : ∀ l, B l ⊆ A (c l)) (l : Fin n) :
    ⋃ k ∈ Finset.univ.filter (fun k : ι × (Fin n → Bool) ↦ k.1 = c l ∧ k.2 l = true),
      refineCell A B k = B l := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion, exists_prop]
  refine ⟨fun ⟨k, hk, hx⟩ ↦ ((mem_refine_cell.mp hx).2 l).mpr hk.2, fun hx ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := exists_mem_refine_cell B (hBc l hx)
  exact ⟨(c l, σ), ⟨rfl, ((mem_refine_cell.mp hσ).2 l).mp hx⟩, hσ⟩

end Refinement

section Expansion

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The vector of cell masses of a measurable random measure is measurable. -/
theorem measurable_to_lp_measure_real {κ : Type*} [Fintype κ] {P : Ω → ProbabilityMeasure X}
    (hP : ∀ A, MeasurableSet A → Measurable fun ω ↦ (P ω : Measure X) A)
    {R : κ → Set X} (hR : ∀ k, MeasurableSet (R k)) :
    Measurable fun ω ↦ WithLp.toLp 2 fun k ↦ (P ω : Measure X).real (R k) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun k ↦ (hP _ (hR k)).ennreal_toReal)

/-- **Size-biased expansion over a partition.** For a Dirichlet process `P` with base `α`, a
partition `R` into cells of positive mass, and an assignment `p` of `n` observations to cells,
weighting by the likelihood `∏ₗ P(R (p l))` turns the law of the cell masses into the Dirichlet
law with parameters `α(R k)` plus the counts of `p`. -/
theorem integral_mul_prod_measure_real_of_is_dirichlet_process {κ : Type*} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] {μ : Measure Ω} {P : Ω → ProbabilityMeasure X}
    {α : Measure X} [IsFiniteMeasure α] (hP : IsDirichletProcess μ P α)
    {R : κ → Set X} (hRm : ∀ k, MeasurableSet (R k)) (hRd : Pairwise (Disjoint on R))
    (hRc : α (⋃ k, R k)ᶜ = 0) (hRpos : ∀ k, 0 < α (R k)) {n : ℕ} (p : Fin n → κ)
    {H : EuclideanSpace ℝ κ → ℝ} (hH : Measurable H) :
    ∫ ω, H (WithLp.toLp 2 fun k ↦ (P ω : Measure X).real (R k)) *
        ∏ l, (P ω : Measure X).real (R (p l)) ∂μ =
      (∫ ω, ∏ l, (P ω : Measure X).real (R (p l)) ∂μ) *
        ∫ y, H y ∂dirichletMeasure (fun k ↦ α.real (R k) + cellCount p k) := by
  have hmap := map_cells_eq_dirichlet_measure hP hRm hRd hRc hRpos
  have hm := measurable_to_lp_measure_real hP.1 hRm
  have hpos : ∀ k, 0 < α.real (R k) := fun k ↦
    ENNReal.toReal_pos (hRpos k).ne' (measure_ne_top _ _)
  have hprod : Measurable fun y : EuclideanSpace ℝ κ ↦ ∏ l, y (p l) :=
    Finset.measurable_prod _ fun l _ ↦ by fun_prop
  have e1 : ∫ ω, H (WithLp.toLp 2 fun k ↦ (P ω : Measure X).real (R k)) *
      ∏ l, (P ω : Measure X).real (R (p l)) ∂μ =
      ∫ y, (∏ l, y (p l)) * H y ∂(μ.map fun ω ↦ WithLp.toLp 2 fun k ↦
        (P ω : Measure X).real (R k)) := by
    rw [integral_map (f := fun y : EuclideanSpace ℝ κ ↦ (∏ l, y (p l)) * H y) hm.aemeasurable
      (hprod.mul hH).aestronglyMeasurable]
    simp only [mul_comm]
  have e2 : ∫ ω, ∏ l, (P ω : Measure X).real (R (p l)) ∂μ =
      ∫ y, ∏ l, y (p l) ∂(μ.map fun ω ↦ WithLp.toLp 2 fun k ↦
        (P ω : Measure X).real (R k)) := by
    rw [integral_map hm.aemeasurable hprod.aestronglyMeasurable]
  rw [e1, e2, hmap, integral_prod_mul_dirichlet_measure p hpos hH]
  rfl

end Expansion

section RefinedExpansion

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- A sum over a filter of a function vanishing off a predicate `pos` is a sum over the subtype
of `pos`. -/
private theorem sum_filter_eq_sum_subtype {κ₀ : Type*} [Fintype κ₀] (pos : κ₀ → Prop)
    [DecidablePred pos] (q : κ₀ → Prop) [DecidablePred q] (G : κ₀ → ℝ)
    (hG : ∀ k, ¬ pos k → G k = 0) :
    ∑ k with q k, G k = ∑ k : {k // pos k}, if q k.1 then G k.1 else 0 := by
  rw [Finset.sum_filter, ← Fintype.sum_subtype_add_sum_subtype pos
    (fun k ↦ if q k then G k else 0)]
  rw [Finset.sum_eq_zero (s := Finset.univ)
    (f := fun k : {k // ¬ pos k} ↦ if q k.1 then G k.1 else 0) (fun k _ ↦ by simp [hG k.1 k.2]),
    add_zero]

/-- **Expansion over a refined partition.** For a Dirichlet process `P` with base `α`, a
partition `A` into cells of positive mass, and sets `B l ⊆ A (c l)`, weighting by the likelihood
`∏ₗ P(B l)` turns the law of the cell masses of `A` into the Dirichlet law with parameters
`α(A i)` plus the counts of `c`. -/
theorem integral_mul_prod_measure_real_of_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Ω → ProbabilityMeasure X}
    {α : Measure X} [IsFiniteMeasure α] (hP : IsDirichletProcess μ P α)
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAc : α (⋃ i, A i)ᶜ = 0) (hApos : ∀ i, 0 < α (A i))
    {n : ℕ} {B : Fin n → Set X} (hBm : ∀ l, MeasurableSet (B l)) {c : Fin n → ι}
    (hBc : ∀ l, B l ⊆ A (c l)) {H : EuclideanSpace ℝ ι → ℝ} (hH : Measurable H) {C : ℝ}
    (hHC : ∀ y, |H y| ≤ C) :
    ∫ ω, H (WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i)) *
        ∏ l, (P ω : Measure X).real (B l) ∂μ =
      (∫ ω, ∏ l, (P ω : Measure X).real (B l) ∂μ) *
        ∫ y, H y ∂dirichletMeasure (fun i ↦ α.real (A i) + cellCount c i) := by
  let κ := {k : ι × (Fin n → Bool) // 0 < α (refineCell A B k)}
  have hRm : ∀ k : κ, MeasurableSet (refineCell A B k.1) := fun k ↦
    measurable_set_refine_cell hAm hBm k.1
  have hRd : Pairwise (Disjoint on fun k : κ ↦ refineCell A B k.1) := fun k k' h ↦
    pairwise_disjoint_refine_cell hAd B (Subtype.val_injective.ne h)
  have hnull : ∀ k, ¬ 0 < α (refineCell A B k) → α (refineCell A B k) = 0 := fun k hk ↦
    le_antisymm (not_lt.mp hk) zero_le
  have hRc : α (⋃ k : κ, refineCell A B k.1)ᶜ = 0 := by
    refine measure_mono_null (t := (⋃ i, A i)ᶜ ∪
      ⋃ k : {k // ¬ 0 < α (refineCell A B k)}, refineCell A B k.1) ?_ ?_
    · intro x hx
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hx
      by_cases hxA : x ∈ ⋃ i, A i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
        obtain ⟨σ, hσ⟩ := exists_mem_refine_cell B hi
        by_cases hp : 0 < α (refineCell A B (i, σ))
        · exact absurd hσ (hx ⟨_, hp⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨⟨_, hp⟩, hσ⟩)
      · exact Or.inl hxA
    · exact measure_union_null hAc (measure_iUnion_null fun k ↦ hnull k.1 k.2)
  have hsum : ∀ (ν : Measure X) [IsFiniteMeasure ν],
      (∀ k, ¬ 0 < α (refineCell A B k) → ν (refineCell A B k) = 0) →
      (∀ i, ν.real (A i) = ∑ k : κ, if k.1.1 = i then ν.real (refineCell A B k.1) else 0) ∧
      (∀ l, ν.real (B l) = ∑ k : κ,
        if k.1.1 = c l ∧ k.1.2 l = true then ν.real (refineCell A B k.1) else 0) := by
    intro ν _ hν
    have hG : ∀ k, ¬ 0 < α (refineCell A B k) → ν.real (refineCell A B k) = 0 := fun k hk ↦ by
      simp [Measure.real, hν k hk]
    refine ⟨fun i ↦ ?_, fun l ↦ ?_⟩
    · conv_lhs => rw [← bi_union_refine_cell_fst A B i]
      rw [measure_real_bi_union_refine_cell ν hAm hAd hBm, sum_filter_eq_sum_subtype _ _ _ hG]
    · conv_lhs => rw [← bi_union_refine_cell_of_subset hBc l]
      rw [measure_real_bi_union_refine_cell ν hAm hAd hBm, sum_filter_eq_sum_subtype _ _ _ hG]
  have hf : Surjective fun k : κ ↦ k.1.1 := by
    intro i
    by_contra hne
    push Not at hne
    have h := (hsum α hnull).1 i
    rw [Finset.sum_eq_zero fun k _ ↦ by simp [hne k]] at h
    exact (ENNReal.toReal_pos (hApos i).ne' (measure_ne_top _ _)).ne' h
  have : Nonempty κ := ⟨(hf (Classical.arbitrary ι)).choose⟩
  have hae : ∀ᵐ ω ∂μ, ∀ k, ¬ 0 < α (refineCell A B k) →
      (P ω : Measure X) (refineCell A B k) = 0 := by
    rw [ae_all_iff]
    intro k
    by_cases hk : 0 < α (refineCell A B k)
    · exact Eventually.of_forall fun _ h ↦ absurd hk h
    · filter_upwards [hP.2.1 _ (measurable_set_refine_cell hAm hBm k) (hnull k hk)] with ω hω _
      exact hω
  let w : (Fin n → κ) → ℝ := fun p ↦
    ∏ l, if (p l).1.1 = c l ∧ (p l).1.2 l = true then 1 else 0
  have hexp : ∀ ω, (∀ k, ¬ 0 < α (refineCell A B k) → (P ω : Measure X) (refineCell A B k) = 0) →
      ∀ H' : EuclideanSpace ℝ ι → ℝ,
      H' (WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i)) *
        ∏ l, (P ω : Measure X).real (B l) =
      ∑ p, w p * (H' (euclideanFiberSum (fun k : κ ↦ k.1.1)
        (WithLp.toLp 2 fun k : κ ↦ (P ω : Measure X).real (refineCell A B k.1))) *
          ∏ l, (P ω : Measure X).real (refineCell A B (p l).1)) := by
    intro ω hω H'
    obtain ⟨h1, h2⟩ := hsum (P ω : Measure X) hω
    have hpA : (WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i)) =
        euclideanFiberSum (fun k : κ ↦ k.1.1)
          (WithLp.toLp 2 fun k : κ ↦ (P ω : Measure X).real (refineCell A B k.1)) := by
      ext i
      rw [euclideanFiberSum_apply, Finset.sum_filter, PiLp.toLp_apply, h1 i]
    rw [hpA]
    simp_rw [h2]
    rw [Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have : ∏ l, (if (p l).1.1 = c l ∧ (p l).1.2 l = true then
        (P ω : Measure X).real (refineCell A B (p l).1) else 0) =
        w p * ∏ l, (P ω : Measure X).real (refineCell A B (p l).1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun l _ ↦ ?_
      split_ifs <;> simp
    rw [this]
    ring
  have hRvec := measurable_to_lp_measure_real hP.1 hRm
  have key : ∀ H' : EuclideanSpace ℝ ι → ℝ, Measurable H' → ∀ C' : ℝ, (∀ y, |H' y| ≤ C') →
      ∫ ω, H' (WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i)) *
        ∏ l, (P ω : Measure X).real (B l) ∂μ =
      ∑ p, w p * ∫ ω, H' (euclideanFiberSum (fun k : κ ↦ k.1.1)
        (WithLp.toLp 2 fun k : κ ↦ (P ω : Measure X).real (refineCell A B k.1))) *
          ∏ l, (P ω : Measure X).real (refineCell A B (p l).1) ∂μ := by
    intro H' hH' C' hC'
    rw [integral_congr_ae (hae.mono fun ω hω ↦ hexp ω hω H'), integral_finsetSum]
    · exact Finset.sum_congr rfl fun p _ ↦ integral_const_mul _ _
    intro p _
    refine Integrable.const_mul (Integrable.of_bound ?_ C' (Eventually.of_forall fun ω ↦ ?_)) _
    · exact ((hH'.comp ((measurable_euclideanFiberSum _).comp hRvec)).mul
        (Finset.measurable_prod _ fun l _ ↦
          (hP.1 _ (hRm (p l))).ennreal_toReal)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod]
      refine (mul_le_of_le_one_right (abs_nonneg _) (Finset.prod_le_one₀ (fun l _ ↦ abs_nonneg _)
        fun l _ ↦ ?_)).trans (hC' _)
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hJ : ∀ p : Fin n → κ, w p ≠ 0 →
      ∫ y, H (euclideanFiberSum (fun k : κ ↦ k.1.1) y) ∂dirichletMeasure
        (fun k ↦ α.real (refineCell A B k.1) + cellCount p k) =
      ∫ y, H y ∂dirichletMeasure (fun i ↦ α.real (A i) + cellCount c i) := by
    intro p hp
    have hcond : ∀ l, (p l).1.1 = c l := fun l ↦ by
      by_contra h
      exact hp (Finset.prod_eq_zero (Finset.mem_univ l) (by simp [h]))
    have hb : ∀ k : κ, 0 < α.real (refineCell A B k.1) + cellCount p k := fun k ↦
      add_pos_of_pos_of_nonneg (ENNReal.toReal_pos k.2.ne' (measure_ne_top _ _))
        (cell_count_nonneg p k)
    rw [← integral_map (measurable_euclideanFiberSum _).aemeasurable hH.aestronglyMeasurable,
      map_euclideanFiberSum_dirichletMeasure hf hb]
    congr 2
    funext i
    rw [Finset.sum_add_distrib, Finset.sum_filter, ← (hsum α hnull).1 i]
    congr 1
    simp only [cellCount]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp [hcond l]
  have h1 := key (fun _ ↦ 1) measurable_const 1 (fun _ ↦ by simp)
  simp only [one_mul] at h1
  rw [key H hH C hHC, h1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : w p = 0
  · simp [hp]
  rw [integral_mul_prod_measure_real_of_is_dirichlet_process hP hRm hRd hRc (fun k ↦ k.2) p
    (H := fun y ↦ H (euclideanFiberSum _ y)) (hH.comp (measurable_euclideanFiberSum _)), hJ p hp]
  ring

end RefinedExpansion


end CKSD
