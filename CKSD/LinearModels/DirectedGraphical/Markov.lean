module

public import CKSD.LinearModels.DirectedGraphical.Interventions

/-!
# Directed Markov properties and back-door and front-door identification

For a mass function on the configurations of the vertices of a directed acyclic graph, the
recursive factorization, the local directed Markov property, and the global directed Markov
property are equivalent; an interventional mass is identified by the back-door and front-door
adjustment formulas.

## Main results

* `CKSD.CausalGraph.recursivelyFactorizes_tfae`: equivalence of recursive factorization, the
  local directed Markov property, and the global directed Markov property.
* `CKSD.doMarginalMass_eq_backdoor`: the back-door adjustment formula
  `P(y | do(x)) = ∑_z P(y | x, z) P(z)` for a set `Z` satisfying the back-door criterion.
* `CKSD.doMarginalMass_eq_frontdoor`: the front-door adjustment formula.

## References

* S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996, §3.2.
* J. Pearl, *Causality*, 2nd ed., Cambridge University Press, 2009, §3.3.

Sources: GAPS 105.62 and 105.63.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

/-! ### Directed Markov properties -/

/-- The marginal mass on all variables is the mass itself. -/
theorem marginalMass_univ [Fintype V] [Fintype S] (p : (V → S) → ℝ) (x : V → S) :
    marginalMass p Finset.univ x = p x := by
  unfold marginalMass
  have : ∀ y : V → S, (∀ v ∈ Finset.univ, y v = x v) ↔ y = x := fun y ↦ by simp [funext_iff]
  simp only [this]
  simp

/-- The decomposition property of conditional independence: `A ⊥ B | C` implies
`A ⊥ B' | C` for `B' ⊆ B`. -/
theorem CondIndepMass.mono_right [Fintype V] [Fintype S] {p : (V → S) → ℝ}
    {A B B' C : Finset V} (h : CondIndepMass p A B C) (hB' : B' ⊆ B) (hAB : Disjoint A B)
    (hBC : Disjoint B C) : CondIndepMass p A B' C := by
  intro x
  have hZ1 : Disjoint (A ∪ B' ∪ C) (B \ B') := by
    refine Finset.disjoint_left.2 fun v hv hvZ ↦ ?_
    obtain ⟨hvB, hvB'⟩ := Finset.mem_sdiff.1 hvZ
    rcases Finset.mem_union.1 hv with hv | hv
    · rcases Finset.mem_union.1 hv with hv | hv
      · exact Finset.disjoint_left.1 hAB hv hvB
      · exact hvB' hv
    · exact Finset.disjoint_left.1 hBC hvB hv
  have hZ2 : Disjoint (B' ∪ C) (B \ B') := by
    refine Finset.disjoint_left.2 fun v hv hvZ ↦ ?_
    obtain ⟨hvB, hvB'⟩ := Finset.mem_sdiff.1 hvZ
    rcases Finset.mem_union.1 hv with hv | hv
    · exact hvB' hv
    · exact Finset.disjoint_left.1 hBC hvB hv
  have e1 : A ∪ B' ∪ C ∪ B \ B' = A ∪ B ∪ C := by
    ext v
    have := @hB' v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have e2 : B' ∪ C ∪ B \ B' = B ∪ C := by
    ext v
    have := @hB' v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [marginalMass_eq_sum_overwriteOn p hZ1 x, marginalMass_eq_sum_overwriteOn p hZ2 x, e1, e2,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hC : marginalMass p C (overwriteOn (B \ B') z x) = marginalMass p C x :=
    marginalMass_congr_point p C fun v hv ↦ overwriteOn_of_notMem _ _ fun hvZ ↦
      Finset.disjoint_left.1 hZ2 (Finset.mem_union_right _ hv) hvZ
  have hAC : marginalMass p (A ∪ C) (overwriteOn (B \ B') z x) = marginalMass p (A ∪ C) x :=
    marginalMass_congr_point p _ fun v hv ↦ overwriteOn_of_notMem _ _ fun hvZ ↦ by
      rcases Finset.mem_union.1 hv with hv | hv
      · exact Finset.disjoint_left.1 hZ1 (by simp [hv]) hvZ
      · exact Finset.disjoint_left.1 hZ1 (by simp [hv]) hvZ
  have := h (overwriteOn (B \ B') z x)
  rw [hC, hAC] at this
  exact this

/-- Summing the marginal mass of `insert v C` over the values of `v`. -/
theorem sum_marginalMass_insert_update [Fintype V] [Fintype S] (p : (V → S) → ℝ) {v : V}
    {C : Finset V} (hv : v ∉ C) (y : V → S) :
    ∑ s, marginalMass p (insert v C) (Function.update y v s) = marginalMass p C y := by
  unfold marginalMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have key : ∀ s, (∀ u ∈ insert v C, w u = Function.update y v s u) ↔
      (w v = s ∧ ∀ u ∈ C, w u = y u) := by
    intro s
    simp only [Finset.mem_insert, forall_eq_or_imp, Function.update_self]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u hu ↦ ?_⟩
      rw [h2 u hu, Function.update_of_ne (show u ≠ v by rintro rfl; exact hv hu)]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u hu ↦ ?_⟩
      rw [Function.update_of_ne (show u ≠ v by rintro rfl; exact hv hu)]
      exact h2 u hu
  simp only [key, ite_and]
  rw [Finset.sum_ite_eq]
  simp

/-- Under the local directed Markov property, the marginal mass of an ancestral set is the
product of the conditional masses of its vertices given their parents. -/
theorem CausalGraph.marginalMass_eq_prod_condMass_of_isLocalDirectedMarkov [Fintype V]
    [Fintype S] (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hLM : G.IsLocalDirectedMarkov p) :
    ∀ D : Finset V, (∀ v ∈ D, ∀ u, G.edge u v → u ∈ D) → ∀ x,
      marginalMass p D x = ∏ v ∈ D, condMass p {v} (G.parentFinset v) x := by
  intro D
  induction D using Finset.strongInduction with
  | H D ih =>
  intro hD x
  rcases D.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.prod_empty]
    unfold marginalMass
    simpa using hp.2
  -- a vertex of `D` without descendants in `D`
  have : IsTrans V (flip (Relation.TransGen G.edge)) :=
    ⟨fun _ _ _ h₁ h₂ ↦ Relation.TransGen.trans h₂ h₁⟩
  have : Std.Irrefl (flip (Relation.TransGen G.edge)) := ⟨G.acyclic⟩
  obtain ⟨v, hvD, hmax⟩ := (Finite.wellFounded_of_trans_of_irrefl
    (flip (Relation.TransGen G.edge))).has_min (D : Set V) hne
  set D' := D.erase v with hD'
  have hD'cl : ∀ w ∈ D', ∀ u, G.edge u w → u ∈ D' := by
    intro w hw u huw
    refine Finset.mem_erase.2 ⟨?_, hD w (Finset.mem_of_mem_erase hw) u huw⟩
    rintro rfl
    exact hmax w (Finset.mem_of_mem_erase hw) (Relation.TransGen.single huw)
  set pa := G.parentFinset v with hpa
  have hmem_pa : ∀ u, u ∈ pa ↔ G.edge u v := fun u ↦ by
    simp [hpa, CausalGraph.parentFinset]
  have hpaD' : pa ⊆ D' := fun u hu ↦ by
    have hu' := (hmem_pa u).1 hu
    exact Finset.mem_erase.2 ⟨fun h ↦ G.not_edge_self v (h ▸ hu'), hD v hvD u hu'⟩
  set B' := D'.filter (fun w ↦ w ∉ pa) with hB'
  have hB'nd : B' ⊆ G.nonDescendantFinset v := by
    intro w hw
    obtain ⟨hwD', hwpa⟩ := Finset.mem_filter.1 hw
    simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.ne_of_mem_erase hwD', fun h ↦ hmax w (Finset.mem_of_mem_erase hwD') h,
      fun h ↦ hwpa ((hmem_pa w).2 h)⟩
  have hdisj1 : Disjoint ({v} : Finset V) (G.nonDescendantFinset v) := by
    simp [CausalGraph.nonDescendantFinset]
  have hdisj2 : Disjoint (G.nonDescendantFinset v) pa := by
    refine Finset.disjoint_left.2 fun u hu hu' ↦ ?_
    simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu
    exact hu.2.2 ((hmem_pa u).1 hu')
  have hci := ((hLM v).mono_right hB'nd hdisj1 hdisj2) x
  have e1 : {v} ∪ B' ∪ pa = D := by
    ext w
    simp only [Finset.mem_union, Finset.mem_singleton, hB', Finset.mem_filter]
    constructor
    · rintro ((rfl | ⟨hw, -⟩) | hw)
      · exact hvD
      · exact Finset.mem_of_mem_erase hw
      · exact Finset.mem_of_mem_erase (hpaD' hw)
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl (Or.inl hwv)
      by_cases hwp : w ∈ pa
      · exact Or.inr hwp
      · exact Or.inl (Or.inr ⟨Finset.mem_erase.2 ⟨hwv, hw⟩, hwp⟩)
  have e2 : B' ∪ pa = D' := by
    ext w
    simp only [Finset.mem_union, hB', Finset.mem_filter]
    constructor
    · rintro (⟨hw, -⟩ | hw)
      · exact hw
      · exact hpaD' hw
    · intro hw
      by_cases hwp : w ∈ pa
      · exact Or.inr hwp
      · exact Or.inl ⟨hw, hwp⟩
  rw [e1, e2] at hci
  have hstep : marginalMass p D x = condMass p {v} pa x * marginalMass p D' x := by
    unfold condMass
    by_cases hz : marginalMass p pa x = 0
    · have h0 : marginalMass p D x = 0 := by
        refine le_antisymm ?_ (marginalMass_nonneg hp.1 D x)
        calc marginalMass p D x ≤ marginalMass p pa x :=
              marginalMass_anti hp.1 (hpaD'.trans (Finset.erase_subset _ _)) x
          _ = 0 := hz
      rw [h0, hz, div_zero, zero_mul]
    · rw [div_mul_eq_mul_div, eq_div_iff hz, ← hci]
  rw [hstep, ih D' (Finset.erase_ssubset hvD) hD'cl x, ← Finset.mul_prod_erase D _ hvD]

/-- The local directed Markov property implies recursive factorization. -/
theorem CausalGraph.recursivelyFactorizes_of_isLocalDirectedMarkov [Fintype V] [Fintype S]
    (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hLM : G.IsLocalDirectedMarkov p) : G.RecursivelyFactorizes p := by
  intro x
  rw [← marginalMass_univ p x]
  exact G.marginalMass_eq_prod_condMass_of_isLocalDirectedMarkov hp hLM Finset.univ
    (fun _ _ _ _ ↦ Finset.mem_univ _) x

/-- A recursively factorizing probability mass function is the recursive product of a local
mass family respecting the parents. -/
theorem CausalGraph.exists_localMass_of_recursivelyFactorizes [Fintype V] [Fintype S]
    (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hRF : G.RecursivelyFactorizes p) :
    ∃ localMass : V → (V → S) → S → ℝ, IsLocalMassFamily localMass ∧
      G.RespectsParents localMass ∧ p = directedFactorizationMass localMass := by
  let loc : V → (V → S) → S → ℝ := fun v y s ↦
    if 0 < marginalMass p (G.parentFinset v) y
    then condMass p {v} (G.parentFinset v) (Function.update y v s)
    else (Fintype.card S : ℝ)⁻¹
  have hvpa : ∀ v, v ∉ G.parentFinset v := fun v h ↦ G.not_edge_self v (by
    simpa [CausalGraph.parentFinset] using h)
  have hloc : IsLocalMassFamily loc := by
    refine ⟨fun v y s ↦ ?_, fun v y ↦ ?_⟩
    · simp only [loc]
      split_ifs
      · exact div_nonneg (marginalMass_nonneg hp.1 _ _) (marginalMass_nonneg hp.1 _ _)
      · positivity
    · simp only [loc]
      split_ifs with hpos
      · unfold condMass
        have hden : ∀ s, marginalMass p (G.parentFinset v) (Function.update y v s) =
            marginalMass p (G.parentFinset v) y := fun s ↦
          marginalMass_congr_point p _ fun u hu ↦
            Function.update_of_ne (show u ≠ v by rintro rfl; exact hvpa u hu) _ _
        simp only [hden, ← Finset.sum_div]
        rw [show ({v} : Finset V) ∪ G.parentFinset v = insert v (G.parentFinset v) from
          (Finset.insert_eq _ _).symm, sum_marginalMass_insert_update p (hvpa v) y,
          div_self hpos.ne']
      · have : 0 < Fintype.card S := Fintype.card_pos_iff.2 ⟨y v⟩
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hpar : G.RespectsParents loc := by
    intro v y y' h
    have hpa : ∀ u ∈ G.parentFinset v, y u = y' u := fun u hu ↦
      h u (by simpa [CausalGraph.parentFinset, CausalGraph.parents] using hu)
    funext s
    have hupd : ∀ u ∈ ({v} : Finset V) ∪ G.parentFinset v,
        Function.update y v s u = Function.update y' v s u := by
      intro u hu
      by_cases huv : u = v
      · subst huv
        simp
      · rw [Function.update_of_ne huv, Function.update_of_ne huv]
        exact hpa u ((Finset.mem_union.1 hu).resolve_left (by simpa using huv))
    have hc : condMass p {v} (G.parentFinset v) (Function.update y v s) =
        condMass p {v} (G.parentFinset v) (Function.update y' v s) := by
      unfold condMass
      rw [marginalMass_congr_point p _ hupd,
        marginalMass_congr_point p _ fun u hu ↦ hupd u (Finset.mem_union_right _ hu)]
    simp only [loc, marginalMass_congr_point p _ hpa, hc]
  refine ⟨loc, hloc, hpar, funext fun x ↦ ?_⟩
  have hle : ∀ y, p y ≤ directedFactorizationMass loc y := by
    intro y
    by_cases hy : p y = 0
    · rw [hy]
      exact directedFactorizationMass_nonneg hloc y
    · have hpos : 0 < p y := lt_of_le_of_ne (hp.1 y) (Ne.symm hy)
      refine le_of_eq ?_
      rw [hRF y]
      unfold directedFactorizationMass
      refine Finset.prod_congr rfl fun v _ ↦ ?_
      have : 0 < marginalMass p (G.parentFinset v) y := lt_of_lt_of_le hpos (by
        rw [← marginalMass_univ p y]
        exact marginalMass_anti hp.1 (Finset.subset_univ _) y)
      simp only [loc, ite_eq_left this, Function.update_eq_self]
  have h1 : ∑ y, directedFactorizationMass loc y = 1 := by
    have := marginalMass_empty_directedFactorizationMass G hloc hpar x
    unfold marginalMass at this
    simpa using this
  have hsum : ∑ y, (directedFactorizationMass loc y - p y) = 0 := by
    rw [Finset.sum_sub_distrib, h1, hp.2, sub_self]
  have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ sub_nonneg.2 (hle y)).1 hsum x
    (Finset.mem_univ _)
  linarith

/-- GAPS 105.62: for a probability mass function on finitely many finite-valued variables,
recursive factorization along a directed acyclic graph, the local directed Markov property, and
the global (d-separation) Markov property are equivalent. Discrete-variable form: densities
with respect to counting measure on a finite product. -/
theorem CausalGraph.recursivelyFactorizes_tfae [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) (hp : IsProbabilityMass p) :
    [G.RecursivelyFactorizes p, G.IsLocalDirectedMarkov p, G.IsGlobalDirectedMarkov p].TFAE := by
  have hRF_GM : G.RecursivelyFactorizes p → G.IsGlobalDirectedMarkov p := by
    intro hRF A B C hAB hAC hBC hsep
    obtain ⟨loc, hloc, hpar, rfl⟩ := G.exists_localMass_of_recursivelyFactorizes hp hRF
    exact condIndepMass_directedFactorizationMass_of_dSeparated G loc hloc hpar A B C hAC
      hBC hsep
  have hGM_LM : G.IsGlobalDirectedMarkov p → G.IsLocalDirectedMarkov p := by
    intro hGM v
    have hvpa : v ∉ G.parentFinset v := fun h ↦ G.not_edge_self v (by
      simpa [CausalGraph.parentFinset] using h)
    refine hGM _ _ _ (by simp [CausalGraph.nonDescendantFinset])
      (Finset.disjoint_singleton_left.2 hvpa) ?_ ?_
    · refine Finset.disjoint_left.2 fun u hu hu' ↦ ?_
      simp only [CausalGraph.nonDescendantFinset, CausalGraph.parentFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at hu hu'
      exact hu.2.2 hu'
    · intro n q h0 hn hq
      have hq0 : q 0 = v := by simpa using h0
      have hnd : q (Fin.last n) ∈ G.nonDescendantFinset v := by simpa using hn
      simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hnd
      have hcoe : ((G.parentFinset v : Finset V) : Set V) = G.parents v := by
        ext u
        simp [CausalGraph.parentFinset, CausalGraph.parents]
      rw [hcoe] at hq
      exact G.dSeparated_parents_of_not_isDescendant (Ne.symm hnd.1) hnd.2.2 hnd.2.1 n q
        (by simp [hq0]) (by simp) hq
  have hLM_RF : G.IsLocalDirectedMarkov p → G.RecursivelyFactorizes p :=
    G.recursivelyFactorizes_of_isLocalDirectedMarkov hp
  tfae_have 1 → 3 := hRF_GM
  tfae_have 3 → 2 := hGM_LM
  tfae_have 2 → 1 := hLM_RF
  tfae_finish

/-- GAPS 105.63, back-door formula for discrete variables: if `Z` satisfies the back-door
criterion relative to `(X, Y)`, then `P(y | do(x)) = ∑_z P(y | x, z) P(z)` for the law
factorizing recursively along `G` with local masses `localMass`. The conditioning events
`{X = x, Z = z}` are assumed to have positive probability. -/
theorem doMarginalMass_eq_backdoor [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hbd : G.IsBackdoorSet X Y Z) (b : V → S)
    (hposZ : ∀ z : Z → S,
      0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z) (overwriteOn Z z b)) :
    doMarginalMass localMass X b Y b =
      ∑ z : Z → S,
        condMass (directedFactorizationMass localMass) Y (X ∪ Z) (overwriteOn Z z b) *
          marginalMass (directedFactorizationMass localMass) Z (overwriteOn Z z b) := by
  have hX : ∀ v ∈ Z, v ∉ X ∧ ∀ u ∈ X, ¬ G.IsDescendant u v := fun v hv ↦
    ⟨fun h ↦ Finset.disjoint_left.1 hXZ h hv, fun u hu ↦ hbd.1 u hu v hv⟩
  have hsep : ((G.removeIncoming ↑(∅ : Finset V)).removeOutgoing ↑X).DSeparated ↑Y ↑X
      ↑((∅ : Finset V) ∪ Z) := by
    rw [Finset.empty_union]
    exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths (G.removeIncoming ↑(∅ : Finset V))
      (fun u v h ↦ h.1)
      (Finset.disjoint_coe.2 hXY) hbd.2
  have hp0 : ∀ y, 0 ≤ directedFactorizationMass localMass y :=
    directedFactorizationMass_nonneg hloc
  change marginalMass (interventionMass localMass X b) Y b = _
  rw [marginalMass_eq_sum_overwriteOn _ hYZ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  set c := overwriteOn Z z b with hc
  have hcX : ∀ v ∈ X, c v = b v := fun v hv ↦
    overwriteOn_of_notMem _ _ (Finset.disjoint_left.1 hXZ hv)
  have hZm : marginalMass (interventionMass localMass X b) Z c =
      marginalMass (directedFactorizationMass localMass) Z c :=
    doMarginalMass_eq_marginalMass_of_nonDescendant G localMass hloc hpar X Z b c hX
  have hposZm : 0 < marginalMass (directedFactorizationMass localMass) Z c :=
    lt_of_lt_of_le (hposZ z) (marginalMass_anti hp0 Finset.subset_union_right c)
  have hrule := condDoMass_rule_two G localMass hloc hpar ∅ Y X Z
    ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Finset.disjoint_empty_left _,
      hXY.symm, hYZ, hXZ⟩ hsep c (by
      change 0 < marginalMass (interventionMass localMass ∅ c) (X ∪ Z) c
      rw [interventionMass_empty]
      exact hposZ z)
  unfold condDoMass at hrule
  change marginalMass (interventionMass localMass (∅ ∪ X) c) (Y ∪ Z) c /
      marginalMass (interventionMass localMass (∅ ∪ X) c) Z c =
    marginalMass (interventionMass localMass ∅ c) (Y ∪ (X ∪ Z)) c /
      marginalMass (interventionMass localMass ∅ c) (X ∪ Z) c at hrule
  rw [Finset.empty_union, interventionMass_empty, interventionMass_congr localMass X hcX,
    hZm] at hrule
  unfold condMass
  rw [← hrule, div_mul_cancel₀ _ hposZm.ne']

/-- GAPS 105.63, front-door formula for discrete variables: if `Z` satisfies the front-door
criterion relative to `(X, Y)`, then
`P(y | do(x)) = ∑_z P(z | x) ∑_{x'} P(y | x', z) P(x')`. The conditioning events `{X = x}` and
`{X = x', Z = z}` are assumed to have positive probability. -/
theorem doMarginalMass_eq_frontdoor [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hfd : G.IsFrontdoorSet X Y Z) (b : V → S)
    (hposX : 0 < marginalMass (directedFactorizationMass localMass) X b)
    (hposXZ : ∀ (x' : X → S) (z : Z → S),
      0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z)
        (overwriteOn X x' (overwriteOn Z z b))) :
    doMarginalMass localMass X b Y b =
      ∑ z : Z → S,
        condMass (directedFactorizationMass localMass) Z X (overwriteOn Z z b) *
          ∑ x' : X → S,
            condMass (directedFactorizationMass localMass) Y (X ∪ Z)
                (overwriteOn X x' (overwriteOn Z z b)) *
              marginalMass (directedFactorizationMass localMass) X
                (overwriteOn X x' (overwriteOn Z z b)) := by
  obtain ⟨hint, hbXZ, hbZY⟩ := hfd
  have hp0 : ∀ y, 0 ≤ directedFactorizationMass localMass y :=
    directedFactorizationMass_nonneg hloc
  change marginalMass (interventionMass localMass X b) Y b = _
  rw [marginalMass_eq_sum_overwriteOn _ hYZ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  set c := overwriteOn Z z b with hc
  have hcX : ∀ v ∈ X, c v = b v := fun v hv ↦
    overwriteOn_of_notMem _ _ (Finset.disjoint_left.1 hXZ hv)
  have hposXc : 0 < marginalMass (directedFactorizationMass localMass) X c := by
    rw [marginalMass_congr_point _ X hcX]
    exact hposX
  have hposXZc : 0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z) c := by
    have := hposXZ (fun v ↦ c v) z
    rwa [← hc, overwriteOn_self] at this
  -- `P(z | do(x)) = P(z | x)`
  have h1 : marginalMass (interventionMass localMass X b) Z c =
      condMass (directedFactorizationMass localMass) Z X c := by
    have hsep1 : ((G.removeIncoming ↑(∅ : Finset V)).removeOutgoing ↑X).DSeparated ↑Z ↑X
        ↑((∅ : Finset V) ∪ ∅) := by
      rw [Finset.empty_union, Finset.coe_empty]
      exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths
        (G.removeIncoming ∅) (fun u v h ↦ h.1)
        (Finset.disjoint_coe.2 hXZ) hbXZ
    have hrule := condDoMass_rule_two G localMass hloc hpar ∅ Z X ∅
      ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _,
        Finset.disjoint_empty_left _, hXZ.symm, Finset.disjoint_empty_right _,
        Finset.disjoint_empty_right _⟩ hsep1 c (by
        change 0 < marginalMass (interventionMass localMass ∅ c) (X ∪ ∅) c
        rw [interventionMass_empty, Finset.union_empty]
        exact hposXc)
    unfold condDoMass at hrule
    change marginalMass (interventionMass localMass (∅ ∪ X) c) (Z ∪ ∅) c /
        marginalMass (interventionMass localMass (∅ ∪ X) c) ∅ c =
      marginalMass (interventionMass localMass ∅ c) (Z ∪ (X ∪ ∅)) c /
        marginalMass (interventionMass localMass ∅ c) (X ∪ ∅) c at hrule
    simp only [Finset.empty_union, Finset.union_empty] at hrule
    rw [marginalMass_empty_interventionMass G hloc hpar, div_one, interventionMass_empty,
      interventionMass_congr localMass X hcX] at hrule
    rw [hrule]
    rfl
  have hposZdo : 0 < marginalMass (interventionMass localMass X b) Z c := by
    rw [h1]
    unfold condMass
    exact div_pos (by rw [Finset.union_comm]; exact hposXZc) hposXc
  -- `P(y | do(x), z) = P(y | do(x), do(z))`
  have h2 : marginalMass (interventionMass localMass X b) (Y ∪ Z) c /
      marginalMass (interventionMass localMass X b) Z c =
        marginalMass (interventionMass localMass (X ∪ Z) c) Y c := by
    have hsep2 : ((G.removeIncoming ↑X).removeOutgoing ↑Z).DSeparated ↑Y ↑Z ↑(X ∪ ∅) := by
      rw [Finset.union_empty]
      exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths (G.removeIncoming ↑X)
        (fun u v h ↦ h.1)
        (Finset.disjoint_coe.2 hYZ.symm) hbZY
    have hrule := condDoMass_rule_two G localMass hloc hpar X Y Z ∅
      ⟨hXY, hXZ, Finset.disjoint_empty_right _, hYZ, Finset.disjoint_empty_right _,
        Finset.disjoint_empty_right _⟩ hsep2 c (by
        change 0 < marginalMass (interventionMass localMass X c) (Z ∪ ∅) c
        rw [Finset.union_empty, interventionMass_congr localMass X hcX]
        exact hposZdo)
    unfold condDoMass at hrule
    change marginalMass (interventionMass localMass (X ∪ Z) c) (Y ∪ ∅) c /
        marginalMass (interventionMass localMass (X ∪ Z) c) ∅ c =
      marginalMass (interventionMass localMass X c) (Y ∪ (Z ∪ ∅)) c /
        marginalMass (interventionMass localMass X c) (Z ∪ ∅) c at hrule
    simp only [Finset.union_empty] at hrule
    rw [marginalMass_empty_interventionMass G hloc hpar, div_one,
      interventionMass_congr localMass X hcX] at hrule
    exact hrule.symm
  -- `P(y | do(x), do(z)) = P(y | do(z))`
  have h3 : marginalMass (interventionMass localMass (X ∪ Z) c) Y c =
      doMarginalMass localMass Z c Y c := by
    have := doMarginalMass_eq_marginalMass_of_nonDescendant (G.removeIncoming ↑Z)
      (intervenedLocalMass localMass Z c) (isLocalMassFamily_intervenedLocalMass hloc Z c)
      (respectsParents_intervenedLocalMass G hpar Z c) X Y c c fun v hv ↦
        ⟨fun h ↦ Finset.disjoint_left.1 hXY h hv, fun u hu ↦
          G.not_isDescendant_removeIncoming_of_intercepts (Finset.disjoint_coe.2 hXZ) hint
            v hv u hu⟩
    change marginalMass (interventionMass (intervenedLocalMass localMass Z c) X c) Y c =
      marginalMass (directedFactorizationMass (intervenedLocalMass localMass Z c)) Y c at this
    rw [interventionMass_intervenedLocalMass, directedFactorizationMass_intervenedLocalMass]
      at this
    exact this
  -- back-door adjustment for the effect of `Z` on `Y`, adjusting for `X`
  have hbd : G.IsBackdoorSet ↑Z ↑Y ↑X :=
    ⟨fun z hz x hx ↦ G.not_isDescendant_of_blocksBackdoorPaths hbXZ z hz x hx, hbZY⟩
  have h4 := doMarginalMass_eq_backdoor G localMass hloc hpar Z Y X hYZ.symm hXZ.symm
    hXY.symm hbd c fun x' ↦ by
      rw [Finset.union_comm]
      exact hposXZ x' z
  rw [← h1, ← div_mul_cancel₀ (marginalMass (interventionMass localMass X b) (Y ∪ Z) c)
    hposZdo.ne', h2, h3, h4, mul_comm, Finset.union_comm Z X]

end CKSD
