module

public import CKSD.LinearModels.DirectedGraphical.Basic

/-!
# D-separation and collider identification

Separating sets identify unshielded colliders and hence the graph skeleton and collider
structure within a Markov equivalence class. Source: GAPS 105.70.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

/-- GAPS 105.70: two nonadjacent distinct vertices of a directed acyclic graph are d-separated
by the parents of one of them. -/
theorem CausalGraph.dSeparated_parents_of_not_adjacent (G : CausalGraph V)
    {u v : V} (huv : u ≠ v) (h : ¬ G.Adjacent u v) :
    G.DSeparated {u} {v} (G.parents u) ∨ G.DSeparated {u} {v} (G.parents v) := by
  by_cases hd : G.IsDescendant u v
  · right
    refine (G.dSeparated_parents_of_not_isDescendant huv.symm (fun e ↦ h (Or.inl e))
      fun hd' ↦ G.acyclic u (hd.trans hd')).symm
  · exact Or.inl (G.dSeparated_parents_of_not_isDescendant huv (fun e ↦ h (Or.inr e)) hd)

/-- GAPS 105.70: two distinct vertices are adjacent if and only if no set of other vertices
d-separates them. -/
theorem CausalGraph.adjacent_iff_forall_not_dSeparated [Fintype V] (G : CausalGraph V)
    {u v : V} (huv : u ≠ v) :
    G.Adjacent u v ↔ ∀ S : Finset V, u ∉ S → v ∉ S → ¬ G.DSeparated {u} {v} S := by
  refine ⟨fun h S _ _ ↦ h.not_dSeparated _, fun h ↦ ?_⟩
  by_contra hadj
  have hnu : ∀ w, G.edge w u → w ≠ u ∧ w ≠ v := fun w hw ↦
    ⟨fun hwu ↦ G.not_adjacent_self u (by subst hwu; exact Or.inl hw),
      fun hwv ↦ hadj (by subst hwv; exact Or.inr hw)⟩
  have hnv : ∀ w, G.edge w v → w ≠ u ∧ w ≠ v := fun w hw ↦
    ⟨fun hwu ↦ hadj (by subst hwu; exact Or.inl hw),
      fun hwv ↦ G.not_adjacent_self v (by subst hwv; exact Or.inl hw)⟩
  rcases G.dSeparated_parents_of_not_adjacent huv hadj with hs | hs
  · refine h (G.parentFinset u) ?_ ?_ ?_
    · simp only [CausalGraph.parentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hw ↦ (hnu u hw).1 rfl
    · simp only [CausalGraph.parentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hw ↦ (hnu v hw).2 rfl
    · simpa [CausalGraph.parentFinset, CausalGraph.parents] using hs
  · refine h (G.parentFinset v) ?_ ?_ ?_
    · simp only [CausalGraph.parentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hw ↦ (hnv u hw).1 rfl
    · simp only [CausalGraph.parentFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hw ↦ (hnv v hw).2 rfl
    · simpa [CausalGraph.parentFinset, CausalGraph.parents] using hs

/-- GAPS 105.70: in a skeleton path `u - v - w` with distinct endpoints, if `S`
d-separates `u` and `w`, then `u → v ← w` exactly when `v ∉ S`. -/
theorem CausalGraph.isCollider_iff_not_mem_of_dSeparated (G : CausalGraph V)
    {u v w : V} (huv : G.Adjacent u v) (hvw : G.Adjacent v w)
    (hne : u ≠ w) (S : Set V) (hsep : G.DSeparated {u} {w} S) :
    (G.edge u v ∧ G.edge w v) ↔ v ∉ S := by
  have hinj : Function.Injective ![u, v, w] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [huv.ne, hvw.ne, huv.ne.symm, hvw.ne.symm, hne.symm]
  have hedge : ∀ i : Fin 2, G.edge (![u, v, w] i.castSucc) (![u, v, w] i.succ) ∨
      G.edge (![u, v, w] i.succ) (![u, v, w] i.castSucc) := by
    intro i
    fin_cases i
    · exact huv
    · exact hvw
  have hact := hsep 2 ![u, v, w] rfl rfl
  constructor
  · rintro hc hv
    refine hact ⟨hinj, hedge, fun i ↦ ?_⟩
    fin_cases i
    simp only
    split_ifs with h
    · exact ⟨v, hv, Or.inl rfl⟩
    · exact absurd hc h
  · intro hv
    by_contra hc
    refine hact ⟨hinj, hedge, fun i ↦ ?_⟩
    fin_cases i
    simp only
    split_ifs with h
    · exact absurd h hc
    · exact hv

/-- GAPS 105.70: the conditional independences of a mass function faithful to two directed
acyclic graphs determine the skeleton and the unshielded colliders; hence (by GAPS 105.67) the
Markov equivalence class. The statement on the PC algorithm is not formalized. -/
theorem CausalGraph.skeleton_and_colliders_eq_of_isFaithful [Fintype V] [Fintype S]
    (G H : CausalGraph V) (p : (V → S) → ℝ) (hG : G.IsFaithful p) (hH : H.IsFaithful p) :
    (∀ u v, G.Adjacent u v ↔ H.Adjacent u v) ∧
      ∀ u v w, G.IsUnshieldedCollider u v w ↔ H.IsUnshieldedCollider u v w := by
  -- d-separation of two distinct vertices by a set avoiding them is graph-independent
  have hsep : ∀ (u v : V) (Z : Finset V), u ≠ v → u ∉ Z → v ∉ Z →
      (G.DSeparated {u} {v} Z ↔ H.DSeparated {u} {v} Z) := by
    intro u v Z huv hu hv
    have h₁ : Disjoint ({u} : Finset V) {v} := Finset.disjoint_singleton.2 huv
    have h₂ : Disjoint ({u} : Finset V) Z := Finset.disjoint_singleton_left.2 hu
    have h₃ : Disjoint ({v} : Finset V) Z := Finset.disjoint_singleton_left.2 hv
    have := (hG {u} {v} Z h₁ h₂ h₃).trans (hH {u} {v} Z h₁ h₂ h₃).symm
    simpa using this
  have hadj : ∀ u v, G.Adjacent u v ↔ H.Adjacent u v := by
    intro u v
    by_cases huv : u = v
    · subst huv
      exact iff_of_false (G.not_adjacent_self u) (H.not_adjacent_self u)
    rw [G.adjacent_iff_forall_not_dSeparated huv, H.adjacent_iff_forall_not_dSeparated huv]
    exact forall_congr' fun Z ↦ forall_congr' fun hu ↦ forall_congr' fun hv ↦
      not_congr (hsep u v Z huv hu hv)
  refine ⟨hadj, ?_⟩
  -- an unshielded collider in one graph is one in the other
  have key : ∀ G H : CausalGraph V, (∀ u v, G.Adjacent u v ↔ H.Adjacent u v) →
      (∀ (u v : V) (Z : Finset V), u ≠ v → u ∉ Z → v ∉ Z →
        (G.DSeparated {u} {v} Z ↔ H.DSeparated {u} {v} Z)) →
      ∀ u v w, G.IsUnshieldedCollider u v w → H.IsUnshieldedCollider u v w := by
    intro G H hadj hsep u v w ⟨hne, huv, hwv, huw⟩
    have huv' : G.Adjacent u v := Or.inl huv
    have hvw' : G.Adjacent v w := Or.inr hwv
    obtain ⟨Z, hu, hw, hZ⟩ : ∃ Z : Finset V, u ∉ Z ∧ w ∉ Z ∧ G.DSeparated {u} {w} Z := by
      by_contra hcon
      exact huw ((G.adjacent_iff_forall_not_dSeparated hne).2 fun Z hu hw hZ ↦
        hcon ⟨Z, hu, hw, hZ⟩)
    have hv : v ∉ (Z : Set V) :=
      (G.isCollider_iff_not_mem_of_dSeparated huv' hvw' hne Z hZ).1 ⟨huv, hwv⟩
    have huwH : ¬ H.Adjacent u w := fun h ↦ huw ((hadj u w).2 h)
    have hZH : H.DSeparated {u} {w} Z := (hsep u w Z hne hu hw).1 hZ
    exact ⟨hne, (H.isCollider_iff_not_mem_of_dSeparated ((hadj u v).1 huv')
      ((hadj v w).1 hvw') hne Z hZH).2 hv |>.1,
      (H.isCollider_iff_not_mem_of_dSeparated ((hadj u v).1 huv')
      ((hadj v w).1 hvw') hne Z hZH).2 hv |>.2, huwH⟩
  intro u v w
  exact ⟨key G H hadj hsep u v w,
    key H G (fun u v ↦ (hadj u v).symm) (fun u v Z h₁ h₂ h₃ ↦ (hsep u v Z h₁ h₂ h₃).symm) u v w⟩

end CKSD
