module

public import CKSD.LinearModels.DirectedGraphical.Basic

/-!
# D-separation and the identification of skeleton and colliders

Two distinct vertices of a directed acyclic graph are adjacent exactly when no set of other
vertices d-separates them, and, for a skeleton path `u - v - w` with `u`, `w` d-separated by
`S`, the vertex `v` is a collider exactly when `v ∉ S`. Hence a mass function faithful to two
graphs forces them to have the same skeleton and the same unshielded colliders, the
graph-theoretic basis of constraint-based causal discovery (PC algorithm).

## Main results

* `CKSD.CausalGraph.adjacent_iff_forall_not_dSeparated`
* `CKSD.CausalGraph.isCollider_iff_notMem_of_dSeparated`
* `CKSD.CausalGraph.dSeparated_parents_of_not_adjacent`
* `CKSD.CausalGraph.adjacent_iff_of_isFaithful`,
  `CKSD.CausalGraph.isUnshieldedCollider_iff_of_isFaithful`

Source: GAPS 105.70.
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
theorem CausalGraph.isCollider_iff_notMem_of_dSeparated (G : CausalGraph V)
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

/-- For a mass function faithful to `G` and to `H`, d-separation of two distinct vertices by a
set avoiding them is the same in both graphs. -/
theorem CausalGraph.dSeparated_singleton_iff_of_isFaithful [Fintype V] [Fintype S]
    {G H : CausalGraph V} {p : (V → S) → ℝ} (hG : G.IsFaithful p) (hH : H.IsFaithful p)
    {u v : V} {Z : Finset V} (huv : u ≠ v) (hu : u ∉ Z) (hv : v ∉ Z) :
    G.DSeparated {u} {v} Z ↔ H.DSeparated {u} {v} Z := by
  have h₁ : Disjoint ({u} : Finset V) {v} := Finset.disjoint_singleton.2 huv
  have h₂ : Disjoint ({u} : Finset V) Z := Finset.disjoint_singleton_left.2 hu
  have h₃ : Disjoint ({v} : Finset V) Z := Finset.disjoint_singleton_left.2 hv
  have := (hG {u} {v} Z h₁ h₂ h₃).trans (hH {u} {v} Z h₁ h₂ h₃).symm
  simpa using this

/-- GAPS 105.70: the conditional independences of a mass function faithful to two directed
acyclic graphs determine the skeleton: the two graphs have the same adjacencies. -/
theorem CausalGraph.adjacent_iff_of_isFaithful [Fintype V] [Fintype S]
    {G H : CausalGraph V} {p : (V → S) → ℝ} (hG : G.IsFaithful p) (hH : H.IsFaithful p)
    (u v : V) : G.Adjacent u v ↔ H.Adjacent u v := by
  by_cases huv : u = v
  · subst huv
    exact iff_of_false (G.not_adjacent_self u) (H.not_adjacent_self u)
  rw [G.adjacent_iff_forall_not_dSeparated huv, H.adjacent_iff_forall_not_dSeparated huv]
  exact forall_congr' fun Z ↦ forall_congr' fun hu ↦ forall_congr' fun hv ↦
    not_congr (dSeparated_singleton_iff_of_isFaithful hG hH huv hu hv)

/-- An unshielded collider of `G` is an unshielded collider of `H` when the mass function is
faithful to both graphs. -/
theorem CausalGraph.IsUnshieldedCollider.of_isFaithful [Fintype V] [Fintype S]
    {G H : CausalGraph V} {p : (V → S) → ℝ} (hG : G.IsFaithful p) (hH : H.IsFaithful p)
    {u v w : V} (h : G.IsUnshieldedCollider u v w) : H.IsUnshieldedCollider u v w := by
  obtain ⟨hne, huv, hwv, huw⟩ := h
  have hadj := adjacent_iff_of_isFaithful hG hH
  have huv' : G.Adjacent u v := Or.inl huv
  have hvw' : G.Adjacent v w := Or.inr hwv
  obtain ⟨Z, hu, hw, hZ⟩ : ∃ Z : Finset V, u ∉ Z ∧ w ∉ Z ∧ G.DSeparated {u} {w} Z := by
    by_contra hcon
    exact huw ((G.adjacent_iff_forall_not_dSeparated hne).2 fun Z hu hw hZ ↦
      hcon ⟨Z, hu, hw, hZ⟩)
  have hv : v ∉ (Z : Set V) :=
    (G.isCollider_iff_notMem_of_dSeparated huv' hvw' hne Z hZ).1 ⟨huv, hwv⟩
  have hZH : H.DSeparated {u} {w} Z :=
    (dSeparated_singleton_iff_of_isFaithful hG hH hne hu hw).1 hZ
  have hcol := (H.isCollider_iff_notMem_of_dSeparated ((hadj u v).1 huv')
    ((hadj v w).1 hvw') hne Z hZH).2 hv
  exact ⟨hne, hcol.1, hcol.2, fun h ↦ huw ((hadj u w).2 h)⟩

/-- GAPS 105.70: the conditional independences of a mass function faithful to two directed
acyclic graphs determine the unshielded colliders; together with
`CKSD.CausalGraph.adjacent_iff_of_isFaithful` and the Verma–Pearl theorem (GAPS 105.67) they
determine the Markov equivalence class. The statement on the PC algorithm is not formalized. -/
theorem CausalGraph.isUnshieldedCollider_iff_of_isFaithful [Fintype V] [Fintype S]
    {G H : CausalGraph V} {p : (V → S) → ℝ} (hG : G.IsFaithful p) (hH : H.IsFaithful p)
    (u v w : V) : G.IsUnshieldedCollider u v w ↔ H.IsUnshieldedCollider u v w :=
  ⟨fun h ↦ h.of_isFaithful hG hH, fun h ↦ h.of_isFaithful hH hG⟩

end CKSD
