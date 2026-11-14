module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique


/-!
# Chordal graphs and junction trees

A finite simple graph is chordal (triangulated) when every cycle of length at least four has a
chord, an edge of the graph between two vertices of the cycle that is not an edge of the cycle.
A junction tree of a finite graph is a tree on an enumeration of its maximal cliques in which
every clique on the path between two cliques contains their intersection. This file proves that
a finite graph has a junction tree if and only if it is chordal. The statements are phrased
directly in terms of Mathlib's `SimpleGraph` walks, cliques and trees, without auxiliary
definitions.

The direction from junction trees to chordality uses that the cliques containing a vertex form a
path-convex set of tree nodes, that unions of intersecting path-convex sets of a tree are
path-convex, and a separation argument at a tree edge. The converse direction proves Dirac's
lemma (a chordal graph that is not complete has two nonadjacent simplicial vertices) for the
subgraphs induced on finite vertex sets, and then builds the junction tree by eliminating a
simplicial vertex and attaching its closed neighbourhood as a leaf clique.

## Main results

* `CKSD.chordal_of_junction_tree`: a graph with a junction tree is chordal.
* `CKSD.exists_junction_tree_of_chordal`: a finite chordal graph has a junction tree.

## References

* G. A. Dirac, *On rigid circuit graphs*, Abh. Math. Sem. Univ. Hamburg 25 (1961), 71–76.
* S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996, Chapter 2.
-/

@[expose] public section

open Finset

namespace CKSD

section Maximal

variable {α : Type*} [Fintype α]

/-- In a finite type, every element satisfying a predicate on finite sets lies below a maximal
one. -/
private theorem exists_subset_maximal (P : Finset α → Prop) {D : Finset α} (hD : P D) :
    ∃ C, D ⊆ C ∧ Maximal P C := by
  classical
  obtain ⟨b, hab, hb⟩ := Finset.exists_le_maximal (Finset.univ.filter P) (by simpa using hD)
  refine ⟨b, hab, (Finset.mem_filter.mp hb.1).2, fun y hy hby ↦ ?_⟩
  exact hb.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩) hby

end Maximal

section PathConvex

variable {ι : Type*} {T : SimpleGraph ι}

/-- A set of vertices of a graph is path-convex when it contains every vertex on every path
between two of its vertices. -/
private def IsPathConvex (T : SimpleGraph ι) (A : Set ι) : Prop :=
  ∀ ⦃i j : ι⦄ (p : T.Walk i j), p.IsPath → i ∈ A → j ∈ A → ∀ k ∈ p.support, k ∈ A

/-- In a tree, the union of two intersecting path-convex sets is path-convex. -/
private theorem IsPathConvex.union (hT : T.IsTree) {A B : Set ι} (hA : IsPathConvex T A)
    (hB : IsPathConvex T B) (hAB : (A ∩ B).Nonempty) : IsPathConvex T (A ∪ B) := by
  have key : ∀ ⦃i j : ι⦄ (p : T.Walk i j), p.IsPath → i ∈ A → j ∈ B →
      ∀ k ∈ p.support, k ∈ A ∪ B := by
    classical
    intro i j p hp hi hj k hk
    obtain ⟨c, hcA, hcB⟩ := hAB
    obtain ⟨w₁, hw₁⟩ : ∃ w : T.Walk i c, w.IsPath :=
      ⟨_, SimpleGraph.Walk.bypass_isPath (hT.connected i c).some⟩
    obtain ⟨w₂, hw₂⟩ : ∃ w : T.Walk c j, w.IsPath :=
      ⟨_, SimpleGraph.Walk.bypass_isPath (hT.connected c j).some⟩
    have h₁ := hA w₁ hw₁ hi hcA
    have h₂ := hB w₂ hw₂ hcB hj
    have hw : (w₁.append w₂).bypass = p := congrArg Subtype.val
      ((hT.isAcyclic.subsingleton_path _ _).elim ⟨_, SimpleGraph.Walk.bypass_isPath _⟩ ⟨p, hp⟩)
    rw [← hw] at hk
    have hk' := SimpleGraph.Walk.support_bypass_subset_support _ hk
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hk'
    rcases hk' with hk' | hk'
    · exact Or.inl (h₁ k hk')
    · exact Or.inr (h₂ k (List.mem_of_mem_tail hk'))
  intro i j p hp hi hj k hk
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact Or.inl (hA p hp hi hj k hk)
  · exact key p hp hi hj k hk
  · exact key p.reverse hp.reverse hj hi k (by simpa using hk)
  · exact Or.inr (hB p hp hi hj k hk)

/-- A walk from `A` to a disjoint set `B` inside `A ∪ B` has an edge from `A` to `B`. -/
private theorem exists_adj_of_walk {A B : Set ι} (hAB : Disjoint A B) :
    ∀ {i j : ι} (p : T.Walk i j), (∀ k ∈ p.support, k ∈ A ∪ B) → i ∈ A → j ∈ B →
      ∃ x y, T.Adj x y ∧ x ∈ A ∧ y ∈ B ∧ x ∈ p.support ∧ y ∈ p.support
  | _, _, .nil, _, hi, hj => absurd hj (Set.disjoint_left.mp hAB hi)
  | _, _, .cons (v := z) h p, hp, hi, hj => by
    have hz : z ∈ A ∪ B := hp z (by simp)
    rcases hz with hz | hz
    · obtain ⟨x, y, hxy, hx, hy, hxs, hys⟩ :=
        exists_adj_of_walk hAB p (fun k hk ↦ hp k (by simp [hk])) hz hj
      exact ⟨x, y, hxy, hx, hy, by simp [hxs], by simp [hys]⟩
    · exact ⟨_, z, h, hi, hz, by simp, by simp⟩

/-- In a tree, two path-convex sets meeting in `w` cannot separate the ends of an edge `xy` with
`x ∈ A \ B` and `y ∈ B \ A`. -/
private theorem not_separated (hT : T.IsTree) {A B : Set ι} (hA : IsPathConvex T A)
    (hB : IsPathConvex T B) {x y w : ι} (hxy : T.Adj x y) (hxA : x ∈ A) (hxB : x ∉ B)
    (hyA : y ∉ A) (hyB : y ∈ B) (hwA : w ∈ A) (hwB : w ∈ B) : False := by
  classical
  obtain ⟨px, hpx⟩ : ∃ w' : T.Walk x w, w'.IsPath :=
    ⟨_, SimpleGraph.Walk.bypass_isPath (hT.connected x w).some⟩
  obtain ⟨py, hpy⟩ : ∃ w' : T.Walk y w, w'.IsPath :=
    ⟨_, SimpleGraph.Walk.bypass_isPath (hT.connected y w).some⟩
  have hxs : x ∉ py.support := fun h ↦ hxB (hB py hpy hyB hwB x h)
  have hys : y ∉ px.support := fun h ↦ hyA (hA px hpx hxA hwA y h)
  have hc : (SimpleGraph.Walk.cons hxy.symm px).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hpx, hys⟩
  have he : SimpleGraph.Walk.cons hxy.symm px = py := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path _ _).elim ⟨_, hc⟩ ⟨py, hpy⟩)
  exact hxs (he ▸ by simp)

end PathConvex

section JunctionTreeToChordal

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {m : ℕ}
  {c : Fin m → Finset V} {T : SimpleGraph (Fin m)}

/-- The tree nodes whose clique contains a vertex of a walk. -/
private def walkNodes (c : Fin m → Finset V) {a b : V} (W : G.Walk a b) : Set (Fin m) :=
  {i | ∃ v ∈ W.support, v ∈ c i}

omit [Fintype V] in
/-- Under the running-intersection property, the nodes whose clique contains a vertex form a
path-convex set. -/
private theorem is_path_convex_nodes
    (hrip : ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k) (v : V) :
    IsPathConvex T {i | v ∈ c i} := fun i j p hp hi hj k hk ↦
  hrip i j p hp k hk (Finset.mem_inter.mpr ⟨hi, hj⟩)

omit [DecidableEq V] in
/-- Every clique lies in the clique of some node. -/
private theorem exists_node_of_is_clique
    (hcov : ∀ C, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C → ∃ i, c i = C)
    {D : Finset V} (hD : G.IsClique (D : Set V)) : ∃ i, D ⊆ c i := by
  obtain ⟨C, hDC, hC⟩ := exists_subset_maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) hD
  obtain ⟨i, rfl⟩ := hcov C hC
  exact ⟨i, hDC⟩

/-- The nodes whose clique meets a walk form a path-convex set. -/
private theorem is_path_convex_walk_nodes (hT : T.IsTree)
    (hcov : ∀ C, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C → ∃ i, c i = C)
    (hrip : ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k) :
    ∀ {a b : V} (W : G.Walk a b), IsPathConvex T (walkNodes c W)
  | a, _, .nil => by
    have : walkNodes c (SimpleGraph.Walk.nil : G.Walk a a) = {i | a ∈ c i} := by
      ext i; simp [walkNodes]
    rw [this]
    exact is_path_convex_nodes hrip a
  | a, _, .cons (v := z) h W => by
    have : walkNodes c (SimpleGraph.Walk.cons h W) = {i | a ∈ c i} ∪ walkNodes c W := by
      ext i; simp [walkNodes]
    rw [this]
    refine (is_path_convex_nodes hrip a).union hT (is_path_convex_walk_nodes hT hcov hrip W) ?_
    obtain ⟨i, hi⟩ := exists_node_of_is_clique hcov (D := {a, z}) (by
      rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr fun _ ↦ h)
    exact ⟨i, hi (by simp), z, by simp, hi (by simp)⟩

omit [Fintype V] [DecidableEq V] in
/-- Two distinct nonadjacent vertices lie in no common clique of the enumeration. -/
private theorem not_mem_both (hmax : ∀ i, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) (c i))
    {a b : V} (hab : a ≠ b) (hnadj : ¬ G.Adj a b) (i : Fin m) : ¬ (a ∈ c i ∧ b ∈ c i) :=
  fun h ↦ hnadj ((hmax i).1 h.1 h.2 hab)

omit [Fintype V] [DecidableEq V] in
/-- An edge `s(a, b)` between the endpoints of a path of length at least two is not an edge of
the path. -/
private theorem not_mem_edges_of_is_path {a b : V} (W : G.Walk a b) (hW : W.IsPath)
    (hl : 2 ≤ W.length) : s(a, b) ∉ W.edges := by
  cases W with
  | nil => simp at hl
  | cons h W' =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hW
    intro he
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · cases W' with
        | nil => simp at hl
        | cons h' _ =>
          exact ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hW.1).2
            (SimpleGraph.Walk.end_mem_support _)
      · exact h.ne rfl
    · exact hW.2 (SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he)

/-- **Graphs with junction trees are chordal.** If the cliques `c i` enumerate the maximal
cliques of `G` and a tree `T` on them has the running-intersection property, then every cycle of
`G` of length at least four has a chord. -/
theorem chordal_of_junction_tree (G : SimpleGraph V) (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m))
    (hmax : ∀ i, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) (c i))
    (hcov : ∀ C, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C → ∃ i, c i = C)
    (hT : T.IsTree)
    (hrip : ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k) :
    ∀ (u : V) (p : G.Walk u u), p.IsCycle → 4 ≤ p.length →
      ∃ a ∈ p.support, ∃ b ∈ p.support, G.Adj a b ∧ s(a, b) ∉ p.edges := by
  intro u p hp hl
  by_contra hcon
  push Not at hcon
  cases p with
  | nil => simp at hl
  | cons h q =>
  rename_i v₁
  rw [SimpleGraph.Walk.cons_isCycle_iff] at hp
  obtain ⟨hq, -⟩ := hp
  cases q with
  | nil => simp at hl
  | cons h₂ q₂ =>
  obtain ⟨w, q₃, h₃, hq₃⟩ := SimpleGraph.Walk.exists_cons_eq_concat h₂ q₂
  rw [hq₃] at hq hcon hl
  cases q₃ with
  | nil => simp at hl
  | cons h₄ q₄ =>
  rename_i z
  cases q₄ with
  | nil => simp at hl
  | cons h₅ q₅ =>
  obtain ⟨t, q₆, h₆, hq₆⟩ := SimpleGraph.Walk.exists_cons_eq_concat h₅ q₅
  rw [hq₆] at hq hcon hl
  -- the cycle is `u, v₁, z, …, t, w, u`, with `q₆ : z ⟶ t`
  set q₃ := SimpleGraph.Walk.cons h₄ (q₆.concat h₆)
  rw [SimpleGraph.Walk.isPath_concat] at hq
  obtain ⟨hq₃p, hu₃⟩ := hq
  have hq₃p' := hq₃p
  rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.isPath_concat] at hq₃p'
  obtain ⟨⟨hq₆p, hw₆⟩, hv₁⟩ := hq₃p'
  have hs₃ : q₃.support = v₁ :: (q₆.support ++ [w]) := by
    simp [q₃, SimpleGraph.Walk.support_concat]
  have hsp : ∀ x ∈ q₃.support, x ∈ (SimpleGraph.Walk.cons h (q₃.concat h₃)).support := by
    intro x hx
    simp [SimpleGraph.Walk.support_concat, hx]
  have hep : (SimpleGraph.Walk.cons h (q₃.concat h₃)).edges =
      s(u, v₁) :: (q₃.edges ++ [s(w, u)]) := by
    simp [SimpleGraph.Walk.edges_concat]
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton, not_or] at hv₁
  have hv₁w : v₁ ≠ w := hv₁.2
  have hv₁₃ : v₁ ∈ q₃.support := by simp [hs₃]
  have hw₃ : w ∈ q₃.support := by simp [hs₃]
  have hz₆ : ∀ x ∈ q₆.support, x ∈ q₃.support := fun x hx ↦ by simp [hs₃, hx]
  -- `v₁` and `w` are not adjacent
  have hnv₁w : ¬ G.Adj v₁ w := by
    intro hadj
    have he := hcon v₁ (hsp _ hv₁₃) w (hsp _ hw₃) hadj
    rw [hep, List.mem_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hu₃ hv₁₃
      · exact hu₃ hw₃
    · exact not_mem_edges_of_is_path q₃ hq₃p (by simp [q₃]) he
    · rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hv₁w rfl
      · exact hu₃ hv₁₃
  -- `u` is adjacent to no vertex strictly inside the path `q₆`
  have hnu : ∀ x ∈ q₆.support, u ≠ x ∧ ¬ G.Adj u x := by
    intro x hx
    refine ⟨fun hux ↦ hu₃ (hux ▸ hz₆ x hx), fun hadj ↦ ?_⟩
    have he := hcon u (by simp) x (hsp _ (hz₆ x hx)) hadj
    rw [hep, List.mem_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨h', -⟩
      · exact hv₁.1 hx
      · exact hu₃ (h' ▸ hv₁₃)
    · exact hu₃ (SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he)
    · rcases Sym2.eq_iff.mp he with ⟨h', -⟩ | ⟨-, rfl⟩
      · exact hu₃ (h' ▸ hw₃)
      · exact hw₆ hx
  -- translate to the tree
  set N : V → Set (Fin m) := fun v ↦ {i | v ∈ c i}
  have hpair : ∀ a b, G.Adj a b → ∃ i, a ∈ c i ∧ b ∈ c i := by
    intro a b hab
    obtain ⟨i, hi⟩ := exists_node_of_is_clique hcov (D := {a, b}) (by
      rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr fun _ ↦ hab)
    exact ⟨i, hi (by simp), hi (by simp)⟩
  have hdisj : Disjoint (N v₁) (N w) := Set.disjoint_left.mpr fun i h₁ h₂ ↦
    not_mem_both hmax hv₁w hnv₁w i ⟨h₁, h₂⟩
  have hdisju : ∀ x ∈ q₆.support, ∀ i, i ∈ N u → i ∉ N x := fun x hx i h₁ h₂ ↦
    not_mem_both hmax (hnu x hx).1 (hnu x hx).2 i ⟨h₁, h₂⟩
  obtain ⟨a, hua, hva⟩ := hpair u v₁ h
  obtain ⟨b, hwb, hub⟩ := hpair w u h₃
  obtain ⟨P, hP⟩ : ∃ P : T.Walk a b, P.IsPath :=
    ⟨_, SimpleGraph.Walk.bypass_isPath (hT.connected a b).some⟩
  have hPu := is_path_convex_nodes hrip u P hP hua hub
  have hPq := is_path_convex_walk_nodes hT hcov hrip q₃ P hP ⟨v₁, hv₁₃, hva⟩ ⟨w, hw₃, hwb⟩
  have hPsplit : ∀ k ∈ P.support, k ∈ N v₁ ∪ N w := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hPq k hk
    rw [hs₃, List.mem_cons, List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | hx | rfl
    · exact Or.inl hxk
    · exact absurd hxk (hdisju x hx k (hPu k hk))
    · exact Or.inr hxk
  obtain ⟨x, y, hxy, hx, hy, hxP, hyP⟩ := exists_adj_of_walk hdisj P hPsplit hva hwb
  obtain ⟨i₀, hi₀⟩ : ∃ i, z ∈ c i := by
    obtain ⟨i, hi⟩ := exists_node_of_is_clique hcov (D := {z}) (by simp)
    exact ⟨i, hi (by simp)⟩
  have hA := is_path_convex_walk_nodes hT hcov hrip (SimpleGraph.Walk.cons h₄ q₆)
  have hB := is_path_convex_walk_nodes hT hcov hrip (q₆.concat h₆)
  refine not_separated hT hA hB hxy ⟨v₁, by simp, hx⟩ ?_ ?_ ⟨w, by
    simp [SimpleGraph.Walk.support_concat], hy⟩ ⟨z, by simp, hi₀⟩
    ⟨z, by simp [SimpleGraph.Walk.support_concat], hi₀⟩
  · rintro ⟨v, hv, hvx⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hdisju v hv x (hPu x hxP) hvx
    · exact Set.disjoint_left.mp hdisj hx hvx
  · rintro ⟨v, hv, hvy⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Set.disjoint_left.mp hdisj hvy hy
    · exact hdisju v hv y (hPu y hyP) hvy

end JunctionTreeToChordal

section Dirac

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `G` is chordal on the vertex set `U`: every cycle of length at least four with all vertices in
`U` has a chord. -/
private def IsChordalOn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.IsCycle → 4 ≤ p.length → (∀ v ∈ p.support, v ∈ U) →
    ∃ a ∈ p.support, ∃ b ∈ p.support, G.Adj a b ∧ s(a, b) ∉ p.edges

omit [DecidableEq V] in
/-- Chordality passes to subsets. -/
private theorem IsChordalOn.mono {U U' : Finset V} (h : IsChordalOn G U) (hU : U' ⊆ U) :
    IsChordalOn G U' := fun u p hp hl hs ↦ h u p hp hl fun v hv ↦ hU (hs v hv)

/-- `v` is simplicial in the subgraph induced on `U`: its neighbours in `U` are pairwise
adjacent. -/
private def IsSimplicialIn (G : SimpleGraph V) (U : Finset V) (v : V) : Prop :=
  v ∈ U ∧ ∀ a ∈ U, ∀ b ∈ U, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b

omit [DecidableEq V] in
/-- A walk between distinct vertices whose edge `s(a, b)` it avoids has length at least two. -/
private theorem two_le_length_of_not_mem_edges {a b : V} (W : G.Walk a b) (hab : a ≠ b)
    (he : s(a, b) ∉ W.edges) : 2 ≤ W.length := by
  cases W with
  | nil => exact absurd rfl hab
  | cons h W' =>
    cases W' with
    | nil => simp at he
    | cons _ _ => simp

/-- **Shortcut.** A chord `s(a, b)` of a walk between two of its vertices that is not an edge of
the walk gives a strictly shorter walk with the same ends through vertices of the walk. -/
private theorem exists_shorter_walk {s t a b : V} (P : G.Walk s t) (ha : a ∈ P.support)
    (hb : b ∈ P.support) (hab : G.Adj a b) (he : s(a, b) ∉ P.edges) :
    ∃ P' : G.Walk s t, P'.length < P.length ∧ ∀ x ∈ P'.support, x ∈ P.support := by
  have hP := congrArg SimpleGraph.Walk.length (P.take_spec ha)
  rw [SimpleGraph.Walk.length_append] at hP
  have hb' : b ∈ (P.takeUntil a ha).support ∨ b ∈ (P.dropUntil a ha).support := by
    rw [← SimpleGraph.Walk.mem_support_append_iff, P.take_spec ha]
    exact hb
  rcases hb' with hb' | hb'
  · set R := P.takeUntil a ha
    have hR := congrArg SimpleGraph.Walk.length (R.take_spec hb')
    rw [SimpleGraph.Walk.length_append] at hR
    have h2 : 2 ≤ (R.dropUntil b hb').length := by
      refine two_le_length_of_not_mem_edges _ hab.ne.symm fun h ↦ he ?_
      rw [Sym2.eq_swap]
      exact P.edges_takeUntil_subset_edges ha (R.edges_dropUntil_subset_edges hb' h)
    refine ⟨(R.takeUntil b hb').append (SimpleGraph.Walk.cons hab.symm (P.dropUntil a ha)),
      ?_, fun x hx ↦ ?_⟩
    · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      omega
    · rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
        List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact P.support_takeUntil_subset_support ha (R.support_takeUntil_subset_support hb' hx)
      · exact hb
      · exact P.support_dropUntil_subset_support ha hx
  · set Q := P.dropUntil a ha
    have hQ := congrArg SimpleGraph.Walk.length (Q.take_spec hb')
    rw [SimpleGraph.Walk.length_append] at hQ
    have h2 : 2 ≤ (Q.takeUntil b hb').length :=
      two_le_length_of_not_mem_edges _ hab.ne fun h ↦
        he (P.edges_dropUntil_subset_edges ha (Q.edges_takeUntil_subset_edges hb' h))
    refine ⟨(P.takeUntil a ha).append (SimpleGraph.Walk.cons hab (Q.dropUntil b hb')),
      ?_, fun x hx ↦ ?_⟩
    · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      omega
    · rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
        List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact P.support_takeUntil_subset_support ha hx
      · exact ha
      · exact P.support_dropUntil_subset_support ha (Q.support_dropUntil_subset_support hb' hx)

/-- **The neighbourhood of a component is a clique.** Let `G` be chordal on `U`, `x ∈ U`, and let
`C ⊆ U` be a connected set of vertices outside the closed neighbourhood of `x`. Then the
neighbours of `x` adjacent to `C` are pairwise adjacent: otherwise a shortest path between two
nonadjacent ones through `C`, closed up through `x`, is a chordless cycle of length at least
four. -/
private theorem adj_of_mem_neighbors {U C S : Finset V} (hU : IsChordalOn G U) {x : V}
    (hx : x ∈ U) (hCU : C ⊆ U) (hSU : S ⊆ U) (hxC : ∀ c ∈ C, c ≠ x ∧ ¬ G.Adj x c)
    (hS : ∀ s ∈ S, G.Adj x s ∧ ∃ c ∈ C, G.Adj s c)
    (hconn : ∀ c ∈ C, ∀ c' ∈ C, ∃ W : G.Walk c c', ∀ v ∈ W.support, v ∈ C)
    {s t : V} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) : G.Adj s t := by
  classical
  by_contra hnadj
  have hxs : G.Adj x s := (hS s hs).1
  have hxt : G.Adj x t := (hS t ht).1
  -- every walk from `s` to `t` through `C` yields a contradiction, by induction on its length
  have key : ∀ n, ∀ P : G.Walk s t, P.length = n → (∀ v ∈ P.support, v = s ∨ v = t ∨ v ∈ C) →
      False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hPn hPC
    set P₀ := P.bypass
    have hP₀ : P₀.IsPath := P.bypass_isPath
    have hP₀s : ∀ v ∈ P₀.support, v ∈ P.support := fun v hv ↦
      P.support_bypass_subset_support hv
    have hP₀C : ∀ v ∈ P₀.support, v = s ∨ v = t ∨ v ∈ C := fun v hv ↦ hPC v (hP₀s v hv)
    have hxP₀ : x ∉ P₀.support := by
      intro hv
      rcases hP₀C x hv with h | h | h
      · exact hxs.ne h
      · exact hxt.ne h
      · exact (hxC x h).1 rfl
    have hl₀ : 2 ≤ P₀.length :=
      two_le_length_of_not_mem_edges _ hst fun h ↦ hnadj (P₀.adj_of_mem_edges h)
    set Z := SimpleGraph.Walk.cons hxs (P₀.concat hxt.symm)
    have hZ : Z.IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_concat,
        SimpleGraph.Walk.edges_concat, List.concat_eq_append]
      refine ⟨⟨hP₀, hxP₀⟩, fun h ↦ ?_⟩
      rw [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact hxP₀ (P₀.fst_mem_support_of_mem_edges h)
      · rcases Sym2.eq_iff.mp h with ⟨h', -⟩ | ⟨-, h'⟩
        · exact hxt.ne h'
        · exact hst h'
    have hZl : 4 ≤ Z.length := by simp [Z]; omega
    have hZs : ∀ v, v ∈ Z.support ↔ v = x ∨ v ∈ P₀.support := by
      intro v
      simp only [Z, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      tauto
    have hZU : ∀ v ∈ Z.support, v ∈ U := by
      intro v hv
      rcases (hZs v).mp hv with rfl | hv
      · exact hx
      · rcases hP₀C v hv with rfl | rfl | h
        · exact hSU hs
        · exact hSU ht
        · exact hCU h
    obtain ⟨a, ha, b, hb, hab, he⟩ := hU x Z hZ hZl hZU
    have hZe : Z.edges = s(x, s) :: (P₀.edges ++ [s(t, x)]) := by
      simp [Z, SimpleGraph.Walk.edges_concat]
    -- an edge from `x` into the path ends at `s` or `t`, so it is an edge of `Z`
    have hxe : ∀ v ∈ P₀.support, G.Adj x v → s(x, v) ∈ Z.edges := by
      intro v hv hadj
      rw [hZe]
      rcases hP₀C v hv with rfl | rfl | h
      · exact List.mem_cons_self
      · simp [Sym2.eq_swap]
      · exact absurd hadj (hxC v h).2
    rw [hZs] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact hab.ne rfl
      · exact he (hxe b hb hab)
    · rcases hb with rfl | hb
      · exact he (Sym2.eq_swap ▸ hxe a ha hab.symm)
      · have he' : s(a, b) ∉ P₀.edges := fun h ↦ he (by rw [hZe]; simp [h])
        obtain ⟨P', hP'l, hP's⟩ := exists_shorter_walk P₀ ha hb hab he'
        have hle : P₀.length ≤ P.length := P.length_bypass_le_length
        exact ih P'.length (by omega) P' rfl
          fun v hv ↦ hP₀C v (hP's v hv)
  obtain ⟨c₁, hc₁, hsc₁⟩ := (hS s hs).2
  obtain ⟨c₂, hc₂, htc₂⟩ := (hS t ht).2
  obtain ⟨W, hW⟩ := hconn c₁ hc₁ c₂ hc₂
  refine key _ (SimpleGraph.Walk.cons hsc₁ (W.concat htc₂.symm)) rfl fun v hv ↦ ?_
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat, List.mem_cons,
    List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (hW v h))
  · exact Or.inr (Or.inl h)

/-- **Dirac's lemma, local form.** If `G` is chordal on `U` and `x, y ∈ U` are distinct and
nonadjacent, then `U` has a simplicial vertex different from and nonadjacent to `x`. The proof is
by strong induction on `#U`: a simplicial vertex is found in the subgraph induced on the
component `C` of `y` outside the closed neighbourhood of `x` together with its neighbourhood
`S`, which is a clique. -/
private theorem exists_is_simplicial_in_not_adj (n : ℕ) :
    ∀ U : Finset V, U.card = n → IsChordalOn G U → ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ G.Adj x y →
      ∃ v, IsSimplicialIn G U v ∧ v ≠ x ∧ ¬ G.Adj x v := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hUn hU x hx y hy hxy hnxy
  set D := U.filter fun c ↦ c ≠ x ∧ ¬ G.Adj x c
  set C := D.filter fun c ↦ ∃ W : G.Walk y c, ∀ v ∈ W.support, v ∈ D
  set S := U.filter fun s ↦ G.Adj x s ∧ ∃ c ∈ C, G.Adj s c
  have hyD : y ∈ D := Finset.mem_filter.mpr ⟨hy, hxy.symm, hnxy⟩
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hDU : D ⊆ U := Finset.filter_subset _ _
  have hyC : y ∈ C := Finset.mem_filter.mpr ⟨hyD, SimpleGraph.Walk.nil, by simpa using hyD⟩
  -- every vertex on a walk from `y` inside `D` lies in `C`
  have hwalkC : ∀ {c : V} (W : G.Walk y c), (∀ v ∈ W.support, v ∈ D) → ∀ v ∈ W.support, v ∈ C := by
    intro c W hW v hv
    exact Finset.mem_filter.mpr ⟨hW v hv, W.takeUntil v hv, fun u hu ↦
      hW u (W.support_takeUntil_subset_support hv hu)⟩
  have hconn : ∀ c ∈ C, ∀ c' ∈ C, ∃ W : G.Walk c c', ∀ v ∈ W.support, v ∈ C := by
    intro c hc c' hc'
    obtain ⟨-, W, hW⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, W', hW'⟩ := Finset.mem_filter.mp hc'
    refine ⟨W.reverse.append W', fun v hv ↦ ?_⟩
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hv
    rcases hv with hv | hv
    · exact hwalkC W hW v hv
    · exact hwalkC W' hW' v hv
  have hxC : ∀ c ∈ C, c ≠ x ∧ ¬ G.Adj x c := fun c hc ↦ (Finset.mem_filter.mp (hCD hc)).2
  have hSprop : ∀ s ∈ S, G.Adj x s ∧ ∃ c ∈ C, G.Adj s c := fun s hs ↦
    (Finset.mem_filter.mp hs).2
  have hCU : C ⊆ U := hCD.trans hDU
  have hSU : S ⊆ U := Finset.filter_subset _ _
  have hScl : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → G.Adj s t := fun s hs t ht hst ↦
    adj_of_mem_neighbors hU hx hCU hSU hxC hSprop hconn hs ht hst
  set W' := C ∪ S
  have hW'U : W' ⊆ U := Finset.union_subset hCU hSU
  have hxW' : x ∉ W' := by
    rw [Finset.mem_union, not_or]
    exact ⟨fun h ↦ (hxC x h).1 rfl, fun h ↦ (hSprop x h).1.ne rfl⟩
  have hcard : W'.card < n := hUn ▸ Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hW'U, fun h ↦ hxW' (h ▸ hx)⟩)
  have hW'ch : IsChordalOn G W' := hU.mono hW'U
  -- a vertex of `C` that is simplicial in `W'`
  obtain ⟨v, hvC, hv⟩ : ∃ v ∈ C, IsSimplicialIn G W' v := by
    by_cases hcomp : ∀ a ∈ W', ∀ b ∈ W', a ≠ b → G.Adj a b
    · exact ⟨y, hyC, Finset.mem_union_left _ hyC, fun a ha b hb _ _ hab ↦ hcomp a ha b hb hab⟩
    · push Not at hcomp
      obtain ⟨p, hp, q, hq, hpq, hnpq⟩ := hcomp
      obtain ⟨v₁, hv₁, hv₁p, hnv₁⟩ := ih _ hcard W' rfl hW'ch p hp q hq hpq hnpq
      obtain ⟨v₂, hv₂, hv₂₁, hnv₂⟩ := ih _ hcard W' rfl hW'ch v₁ hv₁.1 p hp hv₁p
        fun h ↦ hnv₁ h.symm
      rcases Finset.mem_union.mp hv₁.1 with h₁ | h₁
      · exact ⟨v₁, h₁, hv₁⟩
      · rcases Finset.mem_union.mp hv₂.1 with h₂ | h₂
        · exact ⟨v₂, h₂, hv₂⟩
        · exact absurd (hScl v₁ h₁ v₂ h₂ hv₂₁.symm) hnv₂
  have hvx := hxC v hvC
  -- its neighbours in `U` lie in `W'`
  have hnbr : ∀ a ∈ U, G.Adj v a → a ∈ W' := by
    intro a ha hva
    have hax : a ≠ x := fun h ↦ hvx.2 (h ▸ hva.symm)
    by_cases hxa : G.Adj x a
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, hxa, v, hvC, hva.symm⟩)
    · refine Finset.mem_union_left _ ?_
      have haD : a ∈ D := Finset.mem_filter.mpr ⟨ha, hax, hxa⟩
      obtain ⟨-, W, hW⟩ := Finset.mem_filter.mp hvC
      refine hwalkC (W.concat hva) (fun u hu ↦ ?_) a (by simp [SimpleGraph.Walk.support_concat])
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hW u hu
      · exact haD
  refine ⟨v, ⟨hCU hvC, fun a ha b hb hva hvb hab ↦
    hv.2 a (hnbr a ha hva) b (hnbr b hb hvb) hva hvb hab⟩, hvx.1, hvx.2⟩

/-- A nonempty vertex set on which `G` is chordal has a simplicial vertex. -/
private theorem exists_is_simplicial_in {U : Finset V} (hU : IsChordalOn G U) (hne : U.Nonempty) :
    ∃ v, IsSimplicialIn G U v := by
  by_cases hcomp : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b
  · obtain ⟨v, hv⟩ := hne
    exact ⟨v, hv, fun a ha b hb _ _ hab ↦ hcomp a ha b hb hab⟩
  · push Not at hcomp
    obtain ⟨p, hp, q, hq, hpq, hnpq⟩ := hcomp
    obtain ⟨v, hv, -⟩ := exists_is_simplicial_in_not_adj _ U rfl hU p hp q hq hpq hnpq
    exact ⟨v, hv⟩

end Dirac

section LeafGraph

variable {m : ℕ} {T : SimpleGraph (Fin m)} {i₀ : Fin m}

/-- The tree `T` on `Fin m` with a new leaf `Fin.last m` attached to the node `i₀`. -/
private def leafGraph (T : SimpleGraph (Fin m)) (i₀ : Fin m) : SimpleGraph (Fin (m + 1)) where
  Adj x y := (∃ a b, T.Adj a b ∧ x = a.castSucc ∧ y = b.castSucc) ∨
    (x = Fin.last m ∧ y = i₀.castSucc) ∨ (y = Fin.last m ∧ x = i₀.castSucc)
  symm := ⟨by
    rintro x y (⟨a, b, h, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨b, a, h.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨by
    rintro x (⟨a, b, h, rfl, hb⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact h.ne (Fin.castSucc_injective _ hb)
    · exact Fin.castSucc_ne_last _ h.symm
    · exact Fin.castSucc_ne_last _ h.symm⟩

/-- Old nodes are adjacent in the leaf graph exactly when they are adjacent in `T`. -/
private theorem leaf_graph_adj_cast_succ {a b : Fin m} :
    (leafGraph T i₀).Adj a.castSucc b.castSucc ↔ T.Adj a b := by
  constructor
  · rintro (⟨a', b', h, ha, hb⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · rwa [Fin.castSucc_injective _ ha, Fin.castSucc_injective _ hb]
    · exact absurd h (Fin.castSucc_ne_last _)
    · exact absurd h (Fin.castSucc_ne_last _)
  · exact fun h ↦ Or.inl ⟨a, b, h, rfl, rfl⟩

/-- The only neighbour of the new leaf is `i₀`. -/
private theorem leaf_graph_adj_last {y : Fin (m + 1)} :
    (leafGraph T i₀).Adj (Fin.last m) y ↔ y = i₀.castSucc := by
  constructor
  · rintro (⟨a', b', -, ha, -⟩ | ⟨-, h⟩ | ⟨-, h⟩)
    · exact absurd ha.symm (Fin.castSucc_ne_last _)
    · exact h
    · exact absurd h.symm (Fin.castSucc_ne_last _)
  · rintro rfl
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- A walk of the leaf graph between old nodes that avoids the leaf comes from a walk of `T`. -/
private theorem leaf_graph_walk_transfer {x y : Fin (m + 1)} (p : (leafGraph T i₀).Walk x y)
    (hp : Fin.last m ∉ p.support) (a b : Fin m) (hx : x = a.castSucc) (hy : y = b.castSucc) :
    ∃ q : T.Walk a b, q.support.map Fin.castSucc = p.support := by
  induction p generalizing a with
  | nil =>
    obtain rfl := Fin.castSucc_injective _ (hx.symm.trans hy)
    exact ⟨.nil, by simp [hx]⟩
  | @cons x' z y' h p ih =>
    have hz : z ≠ Fin.last m := fun hz ↦ hp (by subst hz; simp)
    obtain ⟨c, rfl⟩ : ∃ c : Fin m, z = c.castSucc :=
      (Fin.eq_castSucc_or_eq_last z).resolve_right hz
    subst hx
    obtain ⟨q, hq⟩ := ih (fun h' ↦ hp (by simp [h'])) c rfl hy
    exact ⟨.cons (leaf_graph_adj_cast_succ.mp h) q, by simp [hq]⟩

/-- A path of the leaf graph between old nodes avoids the leaf. -/
private theorem leaf_graph_last_not_mem {a b : Fin m}
    (p : (leafGraph T i₀).Walk a.castSucc b.castSucc) (hp : p.IsPath) :
    Fin.last m ∉ p.support := by
  intro h
  have hsupp := congrArg SimpleGraph.Walk.support (p.take_spec h)
  rw [SimpleGraph.Walk.support_append] at hsupp
  have hnd := hp.support_nodup
  rw [← hsupp, List.nodup_append] at hnd
  have h₁ : i₀.castSucc ∈ (p.takeUntil _ h).support := by
    have hn : ¬ (p.takeUntil _ h).Nil :=
      SimpleGraph.Walk.not_nil_of_ne (Fin.castSucc_ne_last a)
    have hadj := (SimpleGraph.Walk.adj_penultimate hn).symm
    rw [leaf_graph_adj_last] at hadj
    rw [← hadj]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have h₂ : i₀.castSucc ∈ (p.dropUntil _ h).support.tail := by
    have hn : ¬ (p.dropUntil _ h).Nil :=
      SimpleGraph.Walk.not_nil_of_ne (Fin.castSucc_ne_last b).symm
    have hadj := SimpleGraph.Walk.adj_snd hn
    rw [leaf_graph_adj_last] at hadj
    rw [← hadj]
    exact SimpleGraph.Walk.snd_mem_tail_support hn
  exact hnd.2.2 _ h₁ _ h₂ rfl

/-- The edges of the leaf graph: the edges of `T` and the new edge to the leaf. -/
private theorem edge_set_leaf_graph :
    (leafGraph T i₀).edgeSet =
      Sym2.map Fin.castSucc '' T.edgeSet ∪ {s(Fin.last m, i₀.castSucc)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
  rw [SimpleGraph.mem_edgeSet, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨a, b, h, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨s(a, b), h, rfl⟩
    · exact Or.inr rfl
    · exact Or.inr (Sym2.eq_swap)
  · rintro (⟨e', he', hxy⟩ | hxy)
    · induction e' using Sym2.ind with
      | _ a b =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leaf_graph_adj_cast_succ.mpr he'
      · exact leaf_graph_adj_cast_succ.mpr (T.adj_symm he')
    · rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leaf_graph_adj_last.mpr rfl
      · exact (leaf_graph_adj_last.mpr rfl).symm

/-- Attaching a leaf to a tree gives a tree. -/
private theorem is_tree_leaf_graph (hT : T.IsTree) : (leafGraph T i₀).IsTree := by
  have hcard := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · have hφ : ∀ a b : Fin m, T.Reachable a b → (leafGraph T i₀).Reachable a.castSucc b.castSucc :=
      fun a b h ↦ h.map ⟨Fin.castSucc, fun h' ↦ leaf_graph_adj_cast_succ.mpr h'⟩
    have hroot : ∀ x, (leafGraph T i₀).Reachable x i₀.castSucc := by
      intro x
      rcases Fin.eq_castSucc_or_eq_last x with ⟨a, rfl⟩ | rfl
      · exact hφ a i₀ (hT.connected a i₀)
      · exact (leaf_graph_adj_last.mpr rfl).reachable
    exact ⟨fun x y ↦ (hroot x).trans (hroot y).symm⟩
  · rw [edge_set_leaf_graph, Nat.card_coe_set_eq, Set.ncard_union_eq, Set.ncard_singleton,
      Set.ncard_image_of_injective _ (Sym2.map.injective (Fin.castSucc_injective m)),
      ← Nat.card_coe_set_eq, Nat.card_fin]
    · rw [Nat.card_fin] at hcard
      omega
    rw [Set.disjoint_singleton_right]
    rintro ⟨e', -, he'⟩
    induction e' using Sym2.ind with
    | _ a b =>
    rw [Sym2.map_mk, Sym2.eq_iff] at he'
    rcases he' with ⟨h, -⟩ | ⟨-, h⟩ <;> exact Fin.castSucc_ne_last _ h

end LeafGraph

section ChordalToJunctionTree

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `C` is a maximal clique of the subgraph induced on `U`. -/
private def IsMaxCliqueIn (G : SimpleGraph V) (U C : Finset V) : Prop :=
  Maximal (fun D : Finset V ↦ D ⊆ U ∧ G.IsClique (D : Set V)) C

/-- `T` on the enumeration `c` is a junction tree of the subgraph induced on `U`. -/
private def IsJunctionTreeOn (G : SimpleGraph V) (U : Finset V) {m : ℕ} (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) : Prop :=
  Function.Injective c ∧ (∀ i, IsMaxCliqueIn G U (c i)) ∧
    (∀ C, IsMaxCliqueIn G U C → ∃ i, c i = C) ∧ T.IsTree ∧
    ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k

omit [DecidableRel G.Adj] in
/-- The empty vertex set has a junction tree with the single clique `∅`. -/
private theorem is_junction_tree_on_empty :
    IsJunctionTreeOn G ∅ (fun _ : Fin 1 ↦ (∅ : Finset V)) ⊥ := by
  refine ⟨fun i j _ ↦ Subsingleton.elim i j, fun _ ↦ ?_, fun C hC ↦ ⟨0, ?_⟩,
    SimpleGraph.IsTree.of_subsingleton, fun _ _ _ _ _ _ ↦ by simp⟩
  · exact ⟨⟨subset_refl _, by simp⟩, fun D hD _ ↦ hD.1⟩
  · exact (Finset.subset_empty.mp hC.1.1).symm

/-- A clique in `U` containing `v` lies in the closed neighbourhood of `v` in `U`. -/
private theorem subset_insert_of_mem {U D : Finset V} {v : V} (hDU : D ⊆ U)
    (hD : G.IsClique (D : Set V)) (hvD : v ∈ D) :
    D ⊆ insert v ((U.erase v).filter (G.Adj v)) := by
  intro x hx
  by_cases hxv : x = v
  · exact hxv ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hxv, hDU hx⟩, hD hvD hx (Ne.symm hxv)⟩)

/-- The closed neighbourhood in `U` of a simplicial vertex is a clique. -/
private theorem is_clique_insert_neighbors {U : Finset V} {v : V} (hv : IsSimplicialIn G U v) :
    G.IsClique ((insert v ((U.erase v).filter (G.Adj v)) : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_filter, Finset.mem_erase,
    Set.mem_ofPred_eq] at ha hb
  rcases ha with rfl | ⟨⟨-, haU⟩, hva⟩ <;> rcases hb with rfl | ⟨⟨-, hbU⟩, hvb⟩
  · exact absurd rfl hab
  · exact hvb
  · exact hva.symm
  · exact hv.2 a haU b hbU hva hvb hab

/-- The closed neighbourhood in `U` of a simplicial vertex is a maximal clique of `U`. -/
private theorem is_max_clique_in_insert {U : Finset V} {v : V} (hv : IsSimplicialIn G U v) :
    IsMaxCliqueIn G U (insert v ((U.erase v).filter (G.Adj v))) :=
  ⟨⟨Finset.insert_subset hv.1 fun _ hx ↦ Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1,
    is_clique_insert_neighbors hv⟩,
    fun _ hD hND ↦ subset_insert_of_mem hD.1 hD.2 (hND (Finset.mem_insert_self _ _))⟩

/-- The open neighbourhood of `v` in `U` is not a maximal clique of `U`. -/
private theorem ne_filter_of_is_max_clique_in {U C : Finset V} {v : V} (hv : IsSimplicialIn G U v)
    (hC : IsMaxCliqueIn G U C) : C ≠ (U.erase v).filter (G.Adj v) := by
  rintro rfl
  have h := hC.2 (is_max_clique_in_insert hv).1 (Finset.subset_insert _ _)
    (Finset.mem_insert_self v _)
  simp at h

/-- A maximal clique of `U` other than the closed neighbourhood of `v` is a maximal clique of
`U.erase v`. -/
private theorem is_max_clique_in_erase {U C : Finset V} {v : V} (hv : IsSimplicialIn G U v)
    (hC : IsMaxCliqueIn G U C) (hCN : C ≠ insert v ((U.erase v).filter (G.Adj v))) :
    IsMaxCliqueIn G (U.erase v) C := by
  have hvC : v ∉ C := fun hvC ↦ hCN (Finset.Subset.antisymm
    (subset_insert_of_mem hC.1.1 hC.1.2 hvC)
    (hC.2 (is_max_clique_in_insert hv).1 (subset_insert_of_mem hC.1.1 hC.1.2 hvC)))
  exact ⟨⟨fun x hx ↦ Finset.mem_erase.mpr ⟨fun h ↦ hvC (h ▸ hx), hC.1.1 hx⟩, hC.1.2⟩,
    fun D hD hCD ↦ hC.2 ⟨hD.1.trans (Finset.erase_subset _ _), hD.2⟩ hCD⟩

/-- A maximal clique of `U.erase v` other than the open neighbourhood of `v` is a maximal clique
of `U`. -/
private theorem is_max_clique_in_of_erase {U C : Finset V} {v : V} (hv : IsSimplicialIn G U v)
    (hC : IsMaxCliqueIn G (U.erase v) C) (hCK : C ≠ (U.erase v).filter (G.Adj v)) :
    IsMaxCliqueIn G U C := by
  refine ⟨⟨hC.1.1.trans (Finset.erase_subset _ _), hC.1.2⟩, fun D hD hCD ↦ ?_⟩
  by_cases hvD : v ∈ D
  · have hK : C ⊆ (U.erase v).filter (G.Adj v) := fun x hx ↦ Finset.mem_filter.mpr
      ⟨hC.1.1 hx, hD.2 hvD (hCD hx) (Finset.mem_erase.mp (hC.1.1 hx)).1.symm⟩
    have hKcl : G.IsClique (((U.erase v).filter (G.Adj v) : Finset V) : Set V) :=
      (is_clique_insert_neighbors hv).subset (Finset.coe_subset.mpr (Finset.subset_insert _ _))
    exact absurd (Finset.Subset.antisymm hK (hC.2 ⟨Finset.filter_subset _ _, hKcl⟩ hK)) hCK
  · exact hC.2 ⟨fun x hx ↦ Finset.mem_erase.mpr ⟨fun h ↦ hvD (h ▸ hx), hD.1 hx⟩, hD.2⟩ hCD

/-- Elimination step when the open neighbourhood of `v` is the clique `c i₀`: replace it by the
closed neighbourhood. -/
private theorem is_junction_tree_on_update {U : Finset V} {v : V} (hv : IsSimplicialIn G U v)
    {m : ℕ} {c : Fin m → Finset V} {T : SimpleGraph (Fin m)}
    (h : IsJunctionTreeOn G (U.erase v) c T) {i₀ : Fin m}
    (hi₀ : c i₀ = (U.erase v).filter (G.Adj v)) :
    IsJunctionTreeOn G U (Function.update c i₀ (insert v (c i₀))) T := by
  obtain ⟨hinj, hmax, hcov, hT, hrip⟩ := h
  have hvc : ∀ i, v ∉ c i := fun i hi ↦ by simpa using (hmax i).1.1 hi
  have hmem : ∀ i x, x ∈ Function.update c i₀ (insert v (c i₀)) i ↔
      x ∈ c i ∨ (i = i₀ ∧ x = v) := by
    intro i x
    by_cases hi : i = i₀
    · subst hi
      simp [or_comm]
    · simp [hi]
  have hvmem : ∀ i, v ∈ Function.update c i₀ (insert v (c i₀)) i ↔ i = i₀ := fun i ↦ by
    rw [hmem]
    simp [hvc i]
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun C hC ↦ ?_, hT, fun i j p hp k hk x hx ↦ ?_⟩
  · have hiff : i = i₀ ↔ j = i₀ := by rw [← hvmem, ← hvmem, hij]
    by_cases hi : i = i₀
    · exact hi.trans (hiff.mp hi).symm
    · have hj : j ≠ i₀ := fun hj ↦ hi (hiff.mpr hj)
      rw [Function.update_of_ne hi, Function.update_of_ne hj] at hij
      exact hinj hij
  · by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self, hi₀]
      exact is_max_clique_in_insert hv
    · rw [Function.update_of_ne hi]
      exact is_max_clique_in_of_erase hv (hmax i) fun h ↦ hi (hinj (h.trans hi₀.symm))
  · by_cases hCN : C = insert v ((U.erase v).filter (G.Adj v))
    · exact ⟨i₀, by rw [Function.update_self, hi₀, hCN]⟩
    · obtain ⟨i, hi⟩ := hcov C (is_max_clique_in_erase hv hC hCN)
      have hne : i ≠ i₀ := fun h ↦
        ne_filter_of_is_max_clique_in hv hC (hi.symm.trans (h ▸ hi₀))
      exact ⟨i, by rw [Function.update_of_ne hne, hi]⟩
  · rw [Finset.mem_inter, hmem, hmem] at hx
    rw [hmem]
    rcases hx with ⟨hxi | ⟨hi, hxv⟩, hxj | ⟨hj, hxv'⟩⟩
    · exact Or.inl (hrip i j p hp k hk (Finset.mem_inter.mpr ⟨hxi, hxj⟩))
    · exact absurd (hxv' ▸ hxi) (hvc i)
    · exact absurd (hxv ▸ hxj) (hvc j)
    · subst hi hj
      rw [SimpleGraph.Walk.nil_iff_support_eq.mp (SimpleGraph.Walk.isPath_iff_nil.mp hp),
        List.mem_singleton] at hk
      exact Or.inr ⟨hk, hxv⟩

/-- Elimination step when the open neighbourhood of `v` is strictly contained in the clique
`c i₀`: attach the closed neighbourhood as a new leaf at `i₀`. -/
private theorem is_junction_tree_on_snoc {U : Finset V} {v : V} (hv : IsSimplicialIn G U v)
    {m : ℕ} {c : Fin m → Finset V} {T : SimpleGraph (Fin m)}
    (h : IsJunctionTreeOn G (U.erase v) c T) {i₀ : Fin m}
    (hK : (U.erase v).filter (G.Adj v) ⊆ c i₀) (hne : c i₀ ≠ (U.erase v).filter (G.Adj v)) :
    IsJunctionTreeOn G U
      (Fin.snoc (α := fun _ ↦ Finset V) c (insert v ((U.erase v).filter (G.Adj v))))
      (leafGraph T i₀) := by
  obtain ⟨hinj, hmax, hcov, hT, hrip⟩ := h
  set K := (U.erase v).filter (G.Adj v) with hKdef
  have hvc : ∀ i, v ∉ c i := fun i hi ↦ by simpa using (hmax i).1.1 hi
  have hcK : ∀ i, c i ≠ K := by
    intro i hi
    have h₁ : c i ⊆ c i₀ := hi ▸ hK
    exact hne (Finset.Subset.antisymm (hi ▸ (hmax i).2 (hmax i₀).1 h₁) hK)
  have hold : ∀ (a b : Fin m) (p : (leafGraph T i₀).Walk a.castSucc b.castSucc), p.IsPath →
      ∀ k ∈ p.support, ∃ k' : Fin m, k = k'.castSucc ∧ c a ∩ c b ⊆ c k' := by
    intro a b p hp k hk
    obtain ⟨q, hq⟩ := leaf_graph_walk_transfer p (leaf_graph_last_not_mem p hp) a b rfl rfl
    have hqp : q.IsPath :=
      SimpleGraph.Walk.IsPath.mk' (List.Nodup.of_map _ (hq ▸ hp.support_nodup))
    rw [← hq, List.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact ⟨k', rfl, hrip a b q hqp k' hk'⟩
  have hmix : ∀ (x y : Fin (m + 1)) (p : (leafGraph T i₀).Walk x y) (b : Fin m),
      x = Fin.last m → y = b.castSucc → p.IsPath → ∀ k ∈ p.support,
      insert v K ∩ c b ⊆ Fin.snoc (α := fun _ ↦ Finset V) c (insert v K) k := by
    intro x y p b hx hy hp k hk z hz
    cases p with
    | nil => exact absurd (hx.symm.trans hy) (Fin.castSucc_ne_last b).symm
    | @cons _ w _ h p' =>
      subst hx hy
      have hz' : z ∈ c i₀ ∩ c b := by
        rw [Finset.mem_inter] at hz ⊢
        rcases Finset.mem_insert.mp hz.1 with rfl | hzK
        · exact absurd hz.2 (hvc b)
        · exact ⟨hK hzK, hz.2⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · rw [Fin.snoc_last]
        exact (Finset.mem_inter.mp hz).1
      · obtain rfl := leaf_graph_adj_last.mp h
        obtain ⟨k', rfl, hk'⟩ := hold i₀ b p' hp.of_cons k hk
        rw [Fin.snoc_castSucc]
        exact hk' hz'
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun C hC ↦ ?_, is_tree_leaf_graph hT,
    fun i j p hp k hk ↦ ?_⟩
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc] at hij
      rw [hinj hij]
    · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
      exact absurd (hij ▸ Finset.mem_insert_self v K) (hvc a)
    · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
      exact absurd (hij.symm ▸ Finset.mem_insert_self v K) (hvc b)
    · rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact is_max_clique_in_of_erase hv (hmax a) (hcK a)
    · rw [Fin.snoc_last]
      exact is_max_clique_in_insert hv
  · by_cases hCN : C = insert v K
    · exact ⟨Fin.last m, by rw [Fin.snoc_last, hCN]⟩
    · obtain ⟨i, hi⟩ := hcov C (is_max_clique_in_erase hv hC hCN)
      exact ⟨i.castSucc, by rw [Fin.snoc_castSucc, hi]⟩
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
    · obtain ⟨k', rfl, hk'⟩ := hold a b p hp k hk
      simpa only [Fin.snoc_castSucc] using hk'
    · rw [Fin.snoc_castSucc, Fin.snoc_last, Finset.inter_comm]
      exact hmix _ _ p.reverse a rfl rfl hp.reverse k (by simpa using hk)
    · rw [Fin.snoc_castSucc, Fin.snoc_last]
      exact hmix _ _ p b rfl rfl hp k hk
    · rw [SimpleGraph.Walk.nil_iff_support_eq.mp (SimpleGraph.Walk.isPath_iff_nil.mp hp),
        List.mem_singleton] at hk
      subst hk
      exact Finset.inter_subset_left

/-- Every finite vertex set on which `G` is chordal carries a junction tree of the induced
subgraph, by induction on the number of vertices. -/
private theorem exists_is_junction_tree_on [Fintype V] (n : ℕ) :
    ∀ U : Finset V, U.card = n → IsChordalOn G U →
      ∃ (m : ℕ) (c : Fin m → Finset V) (T : SimpleGraph (Fin m)), IsJunctionTreeOn G U c T := by
  induction n with
  | zero =>
    intro U hU _
    rw [Finset.card_eq_zero.mp hU]
    exact ⟨1, _, _, is_junction_tree_on_empty⟩
  | succ n ih =>
    intro U hU hch
    obtain ⟨v, hv⟩ := exists_is_simplicial_in hch (Finset.card_pos.mp (by omega))
    obtain ⟨m, c, T, h⟩ := ih (U.erase v) (by rw [Finset.card_erase_of_mem hv.1, hU]; rfl)
      (hch.mono (Finset.erase_subset _ _))
    obtain ⟨C, hKC, hC⟩ := exists_subset_maximal
      (fun D : Finset V ↦ D ⊆ U.erase v ∧ G.IsClique (D : Set V))
      (D := (U.erase v).filter (G.Adj v)) ⟨Finset.filter_subset _ _,
        (is_clique_insert_neighbors hv).subset (Finset.coe_subset.mpr (Finset.subset_insert _ _))⟩
    obtain ⟨i₀, hi₀⟩ := h.2.2.1 C hC
    by_cases hne : c i₀ = (U.erase v).filter (G.Adj v)
    · exact ⟨m, _, T, is_junction_tree_on_update hv h hne⟩
    · exact ⟨m + 1, _, _, is_junction_tree_on_snoc hv h (hi₀ ▸ hKC) hne⟩

end ChordalToJunctionTree

/-- **Chordal graphs have junction trees.** A finite graph in which every cycle of length at
least four has a chord admits an injective enumeration `c` of its maximal cliques and a tree `T`
on the indices in which every clique on the path between two cliques contains their
intersection. -/
theorem exists_junction_tree_of_chordal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : ∀ (u : V) (p : G.Walk u u), p.IsCycle → 4 ≤ p.length →
      ∃ a ∈ p.support, ∃ b ∈ p.support, G.Adj a b ∧ s(a, b) ∉ p.edges) :
    ∃ (m : ℕ) (c : Fin m → Finset V) (T : SimpleGraph (Fin m)), Function.Injective c ∧
      (∀ i, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) (c i)) ∧
      (∀ C, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C → ∃ i, c i = C) ∧
      T.IsTree ∧ ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k := by
  classical
  obtain ⟨m, c, T, hinj, hmax, hcov, hT, hrip⟩ :=
    exists_is_junction_tree_on (G := G) _ Finset.univ rfl fun u p hp hl _ ↦ h u p hp hl
  have hiff : ∀ C : Finset V, IsMaxCliqueIn G Finset.univ C ↔
      Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C := by
    intro C
    simp only [IsMaxCliqueIn, Finset.subset_univ, true_and]
  exact ⟨m, c, T, hinj, fun i ↦ (hiff _).mp (hmax i), fun C hC ↦ hcov C ((hiff C).mpr hC), hT,
    hrip⟩

end CKSD
