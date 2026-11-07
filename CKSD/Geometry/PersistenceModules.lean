module

public import CKSD.Geometry.SimplicialPersistence
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Interval decompositions and the isometry theorem

An interval basis of a persistence module `V` indexed by a preorder `P` is a family of nonempty
order-convex supports `I_j ⊆ P` together with bases of every `V_t` indexed by the `j` with
`t ∈ I_j`, such that each structure map `V_s → V_t` sends the basis vector `j` to the basis vector
`j` when `t ∈ I_j` and to zero otherwise. Such a basis is exactly an isomorphism of `V` with the
direct sum of the interval modules `𝕜_{I_j}`; the multiset of supports is the barcode.

A partial matching of bars whose matched supports are `ε`-close, and whose unmatched supports are
`2ε`-short, gives an `ε`-interleaving bar by bar. For closed-open bars this proves that the
interleaving distance is at most the bottleneck distance.

Sources: GAPS 108.18 and 108.20.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set
open scoped ENNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- An interval basis of a persistence module over a preorder: a decomposition of `V` as a direct
sum of interval modules, with supports `support j`. -/
structure IntervalBasis {P : Type*} [Preorder P] {K : Type*} [Field K] (V : P ⥤ ModuleCat K)
    (ι : Type*) where
  /-- Support interval of the `j`th summand. -/
  support : ι → Set P
  /-- Supports are nonempty. -/
  support_nonempty : ∀ j, (support j).Nonempty
  /-- Supports are intervals of the index order. -/
  support_ordConnected : ∀ j, (support j).OrdConnected
  /-- A basis of `V_t` indexed by the summands alive at `t`. -/
  basis : ∀ t, Module.Basis {j // t ∈ support j} K (V.obj t)
  /-- Structure maps send each basis vector to its continuation, or to zero after its death. -/
  map_basis : ∀ s t (h : s ≤ t) (j : {j // s ∈ support j}),
    (V.map (homOfLE h)).hom (basis s j) =
      if ht : t ∈ support j.1 then basis t ⟨j.1, ht⟩ else 0

/-- GAPS 108.18, existence (Crawley-Boevey's theorem): every pointwise finite-dimensional
persistence module over `ℝ` with coefficients in a field is a direct sum of interval modules.
The finite totally ordered case is Gabriel's theorem in type `A_n`. -/
theorem exists_intervalBasis_of_isPointwiseFiniteDimensional {K : Type*} [Field K]
    (V : PersistenceModule K) (hV : IsPointwiseFiniteDimensional V) :
    ∃ ι : Type, Nonempty (IntervalBasis V ι) := by
  sorry

/-- GAPS 108.18, uniqueness: the multiset of intervals of an interval decomposition of a
pointwise finite-dimensional persistence module over `ℝ` is unique, that is, any two interval
bases are related by a support-preserving bijection of their index sets. -/
theorem IntervalBasis.exists_equiv_support_eq {K : Type*} [Field K] {V : PersistenceModule K}
    (hV : IsPointwiseFiniteDimensional V) {ι ι' : Type*} (B : IntervalBasis V ι)
    (B' : IntervalBasis V ι') : ∃ e : ι ≃ ι', ∀ j, B'.support (e j) = B.support j := by
  sorry

namespace IntervalBasis

variable {K : Type*} [Field K] {U V : PersistenceModule K} {ι ι' : Type*}

/-- The comparison map `U_t → V_{t+ε}` attached to a partial matching `R` of the bars of two
interval bases: a bar is sent to its partner when the partner is alive at `t + ε`, and to zero
otherwise. -/
def barMap (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop) (ε t : ℝ) :
    U.obj t →ₗ[K] V.obj (t + ε) :=
  (BU.basis t).constr K fun j ↦
    if h : ∃ j', R j.1 j' ∧ t + ε ∈ BV.support j' then BV.basis (t + ε) ⟨h.choose, h.choose_spec.2⟩
    else 0

/-- Value of the comparison map on a basis vector. -/
theorem barMap_basis (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop)
    (ε t : ℝ) (j : {j // t ∈ BU.support j}) :
    barMap BU BV R ε t (BU.basis t j) =
      if h : ∃ j', R j.1 j' ∧ t + ε ∈ BV.support j' then
        BV.basis (t + ε) ⟨h.choose, h.choose_spec.2⟩ else 0 := by
  rw [barMap, Module.Basis.constr_basis]

/-- The comparison map sends a matched bar to its partner, or to zero once the partner is dead. -/
theorem barMap_basis_of_rel (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop)
    (hR : ∀ i j k, R i j → R i k → j = k) (ε t : ℝ) (j : {j // t ∈ BU.support j}) {j' : ι'}
    (hj : R j.1 j') :
    barMap BU BV R ε t (BU.basis t j) =
      if ht : t + ε ∈ BV.support j' then BV.basis (t + ε) ⟨j', ht⟩ else 0 := by
  rw [barMap_basis BU BV R]
  by_cases ht : t + ε ∈ BV.support j'
  · have hex : ∃ j', R j.1 j' ∧ t + ε ∈ BV.support j' := ⟨j', hj, ht⟩
    have hc : hex.choose = j' := hR _ _ _ hex.choose_spec.1 hj
    rw [dite_eq_left hex, dite_eq_left ht]
    congr 2
  · have hex : ¬ ∃ j', R j.1 j' ∧ t + ε ∈ BV.support j' := by
      rintro ⟨k, hk, hkt⟩
      exact ht (hR _ _ _ hk hj ▸ hkt)
    rw [dite_eq_right hex, dite_eq_right ht]

/-- The comparison map kills unmatched bars. -/
theorem barMap_basis_of_not (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop)
    (ε t : ℝ) (j : {j // t ∈ BU.support j})
    (hj : ¬ ∃ j', R j.1 j') : barMap BU BV R ε t (BU.basis t j) = 0 := by
  rw [barMap_basis BU BV R, dite_eq_right]
  rintro ⟨k, hk, -⟩
  exact hj ⟨k, hk⟩

/-- Structure maps on basis vectors of an interval basis. -/
theorem map_basis_apply (BU : IntervalBasis U ι) {s t : ℝ} (h : s ≤ t)
    (j : {j // s ∈ BU.support j}) :
    (U.map (homOfLE h)).hom (BU.basis s j) =
      if ht : t ∈ BU.support j.1 then BU.basis t ⟨j.1, ht⟩ else 0 := BU.map_basis s t h j

/-- Naturality of the comparison maps, under the compatibility condition `h1` on supports. -/
theorem barMap_natural (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop)
    (hR : ∀ i j k, R i j → R i k → j = k) (ε : ℝ)
    (h1 : ∀ j j', R j j' → ∀ s t, s ≤ t → s ∈ BU.support j → t + ε ∈ BV.support j' →
      s + ε ∈ BV.support j' ∧ t ∈ BU.support j)
    (s t : ℝ) (h : s ≤ t) :
    (V.map (homOfLE (show s + ε ≤ t + ε by linarith))).hom.comp (barMap BU BV R ε s) =
      (barMap BU BV R ε t).comp (U.map (homOfLE h)).hom := by
  refine (BU.basis s).ext fun j ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [map_basis_apply BU h j]
  by_cases hex : ∃ j', R j.1 j'
  · obtain ⟨j', hj'⟩ := hex
    rw [barMap_basis_of_rel BU BV R hR ε s j hj']
    by_cases hte : t + ε ∈ BV.support j'
    · obtain ⟨hse, ht⟩ := h1 _ _ hj' s t h j.2 hte
      rw [dite_eq_left hse, dite_eq_left ht, map_basis_apply BV _ ⟨j', hse⟩, dite_eq_left hte,
        barMap_basis_of_rel BU BV R hR ε t ⟨j.1, ht⟩ hj', dite_eq_left hte]
    · have hl : (V.map (homOfLE (show s + ε ≤ t + ε by linarith))).hom
          (if ht : s + ε ∈ BV.support j' then BV.basis (s + ε) ⟨j', ht⟩ else 0) = 0 := by
        by_cases hse : s + ε ∈ BV.support j'
        · rw [dite_eq_left hse, map_basis_apply BV _ ⟨j', hse⟩, dite_eq_right hte]
        · rw [dite_eq_right hse, map_zero]
      rw [hl]
      by_cases ht : t ∈ BU.support j.1
      · rw [dite_eq_left ht, barMap_basis_of_rel BU BV R hR ε t ⟨j.1, ht⟩ hj', dite_eq_right hte]
      · rw [dite_eq_right ht, map_zero]
  · rw [barMap_basis_of_not BU BV R ε s j hex, map_zero]
    split_ifs with ht
    · rw [barMap_basis_of_not BU BV R ε t ⟨j.1, ht⟩ hex]
    · rw [map_zero]

/-- Composite of the comparison maps for a matching and its transpose. -/
theorem barMap_comp_barMap (BU : IntervalBasis U ι) (BV : IntervalBasis V ι') (R : ι → ι' → Prop)
    (hR : ∀ i j k, R i j → R i k → j = k) (hR' : ∀ i j k, R i k → R j k → i = j) (ε : ℝ)
    (hε : 0 ≤ ε)
    (h3 : ∀ j j', R j j' → ∀ t, t ∈ BU.support j → (t + ε) + ε ∈ BU.support j →
      t + ε ∈ BV.support j')
    (h5 : ∀ j, (¬ ∃ j', R j j') → ∀ t, t ∈ BU.support j → (t + ε) + ε ∉ BU.support j) (t : ℝ) :
    (barMap BV BU (fun j' j ↦ R j j') ε (t + ε)).comp (barMap BU BV R ε t) =
      (U.map (homOfLE (show t ≤ (t + ε) + ε by linarith))).hom := by
  have hRt : ∀ i j k, (fun j' j ↦ R j j') i j → (fun j' j ↦ R j j') i k → j = k :=
    fun i j k h h' ↦ hR' _ _ _ h h'
  refine (BU.basis t).ext fun j ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [map_basis_apply BU _ j]
  by_cases hex : ∃ j', R j.1 j'
  · obtain ⟨j', hj'⟩ := hex
    rw [barMap_basis_of_rel BU BV R hR ε t j hj']
    by_cases hte : t + ε ∈ BV.support j'
    · rw [dite_eq_left hte, barMap_basis_of_rel BV BU _ hRt ε (t + ε) ⟨j', hte⟩ (j' := j.1) hj']
    · rw [dite_eq_right hte, map_zero, dite_eq_right fun h ↦ hte (h3 _ _ hj' t j.2 h)]
  · rw [barMap_basis_of_not BU BV R ε t j hex, map_zero, dite_eq_right (h5 _ hex t j.2)]

/-- An `ε`-interleaving from an `ε`-compatible partial matching of the bars of two interval
bases. -/
theorem nonempty_interleaving_of_matching (BU : IntervalBasis U ι) (BV : IntervalBasis V ι')
    (R : ι → ι' → Prop) (hR : ∀ i j k, R i j → R i k → j = k)
    (hR' : ∀ i j k, R i k → R j k → i = j) (ε : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ j j', R j j' → ∀ s t, s ≤ t → s ∈ BU.support j → t + ε ∈ BV.support j' →
      s + ε ∈ BV.support j' ∧ t ∈ BU.support j)
    (h2 : ∀ j j', R j j' → ∀ s t, s ≤ t → s ∈ BV.support j' → t + ε ∈ BU.support j →
      s + ε ∈ BU.support j ∧ t ∈ BV.support j')
    (h3 : ∀ j j', R j j' → ∀ t, t ∈ BU.support j → (t + ε) + ε ∈ BU.support j →
      t + ε ∈ BV.support j')
    (h4 : ∀ j j', R j j' → ∀ t, t ∈ BV.support j' → (t + ε) + ε ∈ BV.support j' →
      t + ε ∈ BU.support j)
    (h5 : ∀ j, (¬ ∃ j', R j j') → ∀ t, t ∈ BU.support j → (t + ε) + ε ∉ BU.support j)
    (h6 : ∀ j', (¬ ∃ j, R j j') → ∀ t, t ∈ BV.support j' → (t + ε) + ε ∉ BV.support j') :
    Nonempty (PersistenceInterleaving U V ε) := by
  let Rt : ι' → ι → Prop := fun j' j ↦ R j j'
  have hRt : ∀ i j k, Rt i j → Rt i k → j = k := fun i j k h h' ↦ hR' _ _ _ h h'
  have hRt' : ∀ i j k, Rt i k → Rt j k → i = j := fun i j k h h' ↦ hR _ _ _ h h'
  refine ⟨⟨hε, barMap BU BV R ε, barMap BV BU Rt ε, ?_, ?_, ?_, ?_⟩⟩
  · exact barMap_natural BU BV R hR ε h1
  · exact barMap_natural BV BU Rt hRt ε fun j' j h ↦ h2 j j' h
  · exact barMap_comp_barMap BU BV R hR hR' ε hε h3 h5
  · exact barMap_comp_barMap BV BU Rt hRt hRt' ε hε (fun j' j h ↦ h4 j j' h) h6

end IntervalBasis

/-- The partial matching of the bars of two full diagrams that combines a matching of finite parts
with a bijection of essential parts. -/
def DiagramMatching.sumRel {α β κ κ' : Type*} (M : DiagramMatching α β) (σ : κ ≃ κ') :
    α ⊕ κ → β ⊕ κ' → Prop
  | .inl i, .inl j => M.relates i j
  | .inr k, .inr k' => σ k = k'
  | _, _ => False

/-- GAPS 108.20, the easy half of the isometry theorem: for persistence modules with finite
closed-open interval bases, the interleaving distance is at most the bottleneck distance of the
diagrams. A matching of cost `ε` gives an `ε`-interleaving bar by bar. -/
theorem interleavingEDist_le_fullBottleneckEDist {K : Type*} [Field K]
    (U V : PersistenceModule K) {α β κ κ' : Type*} (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (BU : IntervalBasis U (α ⊕ κ)) (BV : IntervalBasis V (β ⊕ κ'))
    (hBU : ∀ i, BU.support (.inl i) = Ico (D.birth i) (D.death i))
    (hBU' : ∀ k, BU.support (.inr k) = Ici (e k))
    (hBV : ∀ i, BV.support (.inl i) = Ico (E.birth i) (E.death i))
    (hBV' : ∀ k, BV.support (.inr k) = Ici (e' k)) :
    interleavingEDist U V ≤ fullBottleneckEDist D e E e' := by
  unfold fullBottleneckEDist bottleneckEDist essentialBottleneckEDist
  rw [iInf_sup_eq]
  refine le_iInf fun M ↦ ?_
  rw [sup_iInf_eq]
  refine le_iInf fun σ ↦ ?_
  set c := max (M.cost D E) (⨆ k, ENNReal.ofReal |e k - e' (σ k)|) with hc
  rcases eq_top_or_lt_top c with htop | hlt
  · exact htop ▸ le_top
  set ε := c.toReal
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg
  have hcε : c = ENNReal.ofReal ε := (ENNReal.ofReal_toReal hlt.ne).symm
  have hle : ∀ x : ℝ, ENNReal.ofReal x ≤ c → x ≤ ε := fun x hx ↦ by
    rw [hcε] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp hx
  have hm : ∀ i j, M.relates i j → |D.birth i - E.birth j| ≤ ε ∧ |D.death i - E.death j| ≤ ε :=
    fun i j h ↦ max_le_iff.mp (hle _ ((M.ofReal_le_cost_of_relates D E h).trans (le_max_left _ _)))
  have hl : ∀ i, (¬ ∃ j, M.relates i j) → (D.death i - D.birth i) / 2 ≤ ε :=
    fun i h ↦ hle _ ((M.ofReal_le_cost_of_not_left D E h).trans (le_max_left _ _))
  have hr : ∀ j, (¬ ∃ i, M.relates i j) → (E.death j - E.birth j) / 2 ≤ ε :=
    fun j h ↦ hle _ ((M.ofReal_le_cost_of_not_right D E h).trans (le_max_left _ _))
  have hs : ∀ k, |e k - e' (σ k)| ≤ ε :=
    fun k ↦ hle _ ((le_iSup (fun k ↦ ENNReal.ofReal |e k - e' (σ k)|) k).trans (le_max_right _ _))
  have hI : Nonempty (PersistenceInterleaving U V ε) := by
    refine IntervalBasis.nonempty_interleaving_of_matching BU BV (M.sumRel σ) ?_ ?_ ε hε
      ?_ ?_ ?_ ?_ ?_ ?_
    · rintro (i | k) (j | k') (j' | k'') h h' <;> simp only [DiagramMatching.sumRel] at h h' ⊢
      · exact congrArg _ (M.left_unique _ _ _ h h')
      · exact congrArg _ (h ▸ h')
    · rintro (i | k) (j | k') (j' | k'') h h' <;> simp only [DiagramMatching.sumRel] at h h' ⊢
      · exact congrArg _ (M.right_unique _ _ _ h h')
      · exact congrArg _ (σ.injective (h.trans h'.symm))
    · rintro (i | k) (j | k') h s t hst hs1 ht1 <;> simp only [DiagramMatching.sumRel] at h
      · obtain ⟨hb, hd⟩ := hm i j h
        rw [abs_le] at hb hd
        simp only [hBU, hBV, mem_Ico] at hs1 ht1 ⊢
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      · subst h
        have := abs_le.mp (hs k)
        simp only [hBU', hBV', mem_Ici] at hs1 ht1 ⊢
        constructor <;> linarith
    · rintro (i | k) (j | k') h s t hst hs1 ht1 <;> simp only [DiagramMatching.sumRel] at h
      · obtain ⟨hb, hd⟩ := hm i j h
        rw [abs_le] at hb hd
        simp only [hBU, hBV, mem_Ico] at hs1 ht1 ⊢
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      · subst h
        have := abs_le.mp (hs k)
        simp only [hBU', hBV', mem_Ici] at hs1 ht1 ⊢
        constructor <;> linarith
    · rintro (i | k) (j | k') h t ht1 ht2 <;> simp only [DiagramMatching.sumRel] at h
      · obtain ⟨hb, hd⟩ := hm i j h
        rw [abs_le] at hb hd
        simp only [hBU, hBV, mem_Ico] at ht1 ht2 ⊢
        constructor <;> linarith
      · subst h
        have := abs_le.mp (hs k)
        simp only [hBU', hBV', mem_Ici] at ht1 ht2 ⊢
        linarith
    · rintro (i | k) (j | k') h t ht1 ht2 <;> simp only [DiagramMatching.sumRel] at h
      · obtain ⟨hb, hd⟩ := hm i j h
        rw [abs_le] at hb hd
        simp only [hBU, hBV, mem_Ico] at ht1 ht2 ⊢
        constructor <;> linarith
      · subst h
        have := abs_le.mp (hs k)
        simp only [hBU', hBV', mem_Ici] at ht1 ht2 ⊢
        linarith
    · rintro (i | k) h t ht1 ht2
      · have hn : ¬ ∃ j, M.relates i j := fun ⟨j, hj⟩ ↦ h ⟨.inl j, hj⟩
        have := hl i hn
        simp only [hBU, mem_Ico] at ht1 ht2
        linarith
      · exact h ⟨.inr (σ k), rfl⟩
    · rintro (j | k') h t ht1 ht2
      · have hn : ¬ ∃ i, M.relates i j := fun ⟨i, hi⟩ ↦ h ⟨.inl i, hi⟩
        have := hr j hn
        simp only [hBV, mem_Ico] at ht1 ht2
        linarith
      · exact h ⟨.inr (σ.symm k'), by simp [DiagramMatching.sumRel]⟩
  rw [hcε]
  exact iInf_le_of_le ⟨ε, hI⟩ le_rfl

/-- GAPS 108.20, the isometry theorem, for persistence modules of finite type with closed-open
bars: if `U` and `V` decompose into finitely many interval modules over `[b, d)` and `[b, ∞)`,
their interleaving distance equals the bottleneck distance of their diagrams (both are `∞`
exactly when the numbers of essential bars differ). The general `q`-tame case, with diagrams
defined from rank functions and intervals with arbitrary endpoint types, is not formalized. -/
theorem interleavingEDist_eq_fullBottleneckEDist {K : Type*} [Field K]
    (U V : PersistenceModule K) {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [Fintype κ'] (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (BU : IntervalBasis U (α ⊕ κ)) (BV : IntervalBasis V (β ⊕ κ'))
    (hBU : ∀ i, BU.support (.inl i) = Ico (D.birth i) (D.death i))
    (hBU' : ∀ k, BU.support (.inr k) = Ici (e k))
    (hBV : ∀ i, BV.support (.inl i) = Ico (E.birth i) (E.death i))
    (hBV' : ∀ k, BV.support (.inr k) = Ici (e' k)) :
    interleavingEDist U V = fullBottleneckEDist D e E e' := by
  refine le_antisymm (interleavingEDist_le_fullBottleneckEDist U V D e E e' BU BV hBU hBU' hBV hBV')
    ?_
  -- Remaining: algebraic stability, `d_B ≤ d_I`.
  sorry

end CKSD
