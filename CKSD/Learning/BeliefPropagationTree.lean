module

public import CKSD.Learning.GraphicalModels

/-!
# Belief propagation on trees

For a positive pairwise graphical model whose graph is a tree, belief propagation has a fixed
point whose beliefs are the exact marginals, and every fixed point has the same messages up to
positive scale (GAPS 107.23).

## Main results

* `CKSD.exists_beliefPropagation_exact_on_tree`: existence of an exact BP fixed point on a tree.
* `CKSD.beliefPropagation_tree_unique_up_to_scale`: uniqueness of BP messages up to scale.

## Implementation notes

The branch of a directed edge `(i, j)` is the set of vertices closer to `i` than to `j`. Rooting
the tree writes the weight as a product of branch weights, and the tree messages are partial
sums of branch weights over the branch; uniqueness is proved by strong induction on the size of
the branch.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

section TreeBranch

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
/-- In a tree, two neighbours of `i` that are both one step closer to `u` coincide. -/
private theorem tree_eq_of_dist_add_one (hG : G.IsTree)
    {u i j k : V} (hj : G.Adj i j) (hk : G.Adj i k) (hdj : G.dist u j + 1 = G.dist u i)
    (hdk : G.dist u k + 1 = G.dist u i) : j = k := by
  obtain ⟨P, hP, hPl⟩ := (hG.connected u i).exists_path_of_dist
  have key : ∀ x, G.Adj i x → G.dist u x + 1 = G.dist u i → x = P.penultimate := by
    intro x hx hdx
    obtain ⟨Q, hQ, hQl⟩ := (hG.connected u x).exists_path_of_dist
    have hiQ : i ∉ Q.support := by
      intro hi
      have h1 := SimpleGraph.dist_le (Q.takeUntil i hi)
      have h2 := Q.length_takeUntil_le_length hi
      omega
    have hxP := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hP hQ hx hiQ
    exact hG.isAcyclic.eq_penultimate_of_adj_end hP hx hxP
  rw [key j hj hdj, key k hk hdk]

omit [Fintype V] in
/-- Distances from the two ends of an edge differ by one, in the root-first convention. -/
private theorem tree_dist_adj (hG : G.IsTree) (u : V) {v w : V} (h : G.Adj v w) :
    G.dist v u = G.dist w u + 1 ∨ G.dist w u = G.dist v u + 1 := by
  have := hG.dist_eq_dist_add_one_of_adj u h
  rw [SimpleGraph.dist_comm (u := u), SimpleGraph.dist_comm (u := u) (v := w)] at this
  exact this

/-- The neighbour of `u` one step closer to the root `r` (and `u` itself if there is none). -/
private def treeParent (G : SimpleGraph V) (r u : V) : V :=
  if h : ∃ p, G.Adj u p ∧ G.dist r p + 1 = G.dist r u then h.choose else u

/-- Every vertex other than the root of a tree is adjacent to its parent, which is one step
closer to the root. -/
private theorem treeParent_spec (hG : G.IsTree) (r : V) {u : V} (hu : u ≠ r) :
    G.Adj u (treeParent G r u) ∧ G.dist r (treeParent G r u) + 1 = G.dist r u := by
  have hex : ∃ p, G.Adj u p ∧ G.dist r p + 1 = G.dist r u := by
    obtain ⟨W, -, hWl⟩ := (hG.connected u r).exists_path_of_dist
    cases W with
    | nil => exact absurd rfl hu
    | @cons _ p _ hup W' =>
      refine ⟨p, hup, ?_⟩
      have h1 := SimpleGraph.dist_le W'
      rw [SimpleGraph.Walk.length_cons] at hWl
      have e1 : G.dist r p = G.dist p r := SimpleGraph.dist_comm
      have e2 : G.dist r u = G.dist u r := SimpleGraph.dist_comm
      rcases hG.dist_eq_dist_add_one_of_adj r hup with h | h <;> omega
  unfold treeParent
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- The parent of a vertex adjacent to the root is the root. -/
private theorem treeParent_of_adj (hG : G.IsTree) {r u : V} (h : G.Adj u r) :
    treeParent G r u = r := by
  have hu : u ≠ r := h.ne
  obtain ⟨h1, h2⟩ := treeParent_spec hG r hu
  refine tree_eq_of_dist_add_one hG (u := r) h1 h h2 ?_
  rw [SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr h.symm]

/-- The branch of the directed edge `(i, j)`: the vertices closer to `i` than to `j`. -/
private def treeBranch (G : SimpleGraph V) (i j : V) : Finset V :=
  Finset.univ.filter fun u ↦ G.dist i u < G.dist j u

/-- Membership in a branch. -/
private theorem mem_treeBranch {i j u : V} :
    u ∈ treeBranch G i j ↔ G.dist i u < G.dist j u := by
  simp [treeBranch]

/-- The tail of a directed edge lies in its branch. -/
private theorem self_mem_treeBranch {i j : V} (h : G.Adj i j) : i ∈ treeBranch G i j := by
  rw [mem_treeBranch, SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr h.symm]
  exact Nat.zero_lt_one

/-- The head of a directed edge does not lie in its branch. -/
private theorem not_mem_treeBranch {i j : V} : j ∉ treeBranch G i j := by
  rw [mem_treeBranch, SimpleGraph.dist_self]
  exact Nat.not_lt_zero _

/-- On the branch of `(i, j)` the distance to `j` exceeds the distance to `i` by one. -/
private theorem dist_of_mem_treeBranch (hG : G.IsTree) {i j u : V} (h : G.Adj i j)
    (hu : u ∈ treeBranch G i j) : G.dist j u = G.dist i u + 1 := by
  rw [mem_treeBranch] at hu
  rcases tree_dist_adj hG u h with h' | h' <;> omega

/-- Branches behind the other neighbours of `i` lie in the branch of `(i, j)`. -/
private theorem treeBranch_subset (hG : G.IsTree) {i j k : V} (hij : G.Adj i j)
    (hki : G.Adj k i) (hkj : k ≠ j) : treeBranch G k i ⊆ treeBranch G i j := by
  intro u hu
  have hu' := dist_of_mem_treeBranch hG hki hu
  rw [mem_treeBranch]
  rcases tree_dist_adj hG u hij with h | h
  · exfalso
    refine hkj (tree_eq_of_dist_add_one hG (u := u) hki.symm hij ?_ ?_)
    · rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := u) (v := i)]; omega
    · rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := u) (v := i)]; omega
  · omega

/-- Branches behind distinct neighbours of `i` are disjoint. -/
private theorem treeBranch_disjoint (hG : G.IsTree) {i k k' : V} (hk : G.Adj k i)
    (hk' : G.Adj k' i) (hne : k ≠ k') : Disjoint (treeBranch G k i) (treeBranch G k' i) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  have h1 := dist_of_mem_treeBranch hG hk hu
  have h2 := dist_of_mem_treeBranch hG hk' hu'
  refine hne (tree_eq_of_dist_add_one hG (u := u) hk.symm hk'.symm ?_ ?_)
  · rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := u) (v := i)]; omega
  · rw [SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := u) (v := i)]; omega

/-- A vertex `u ≠ i` lies in the branch behind the neighbour of `i` on the way to `u`. -/
private theorem exists_mem_treeBranch (hG : G.IsTree) {i u : V} (hu : u ≠ i) :
    ∃ k, G.Adj k i ∧ u ∈ treeBranch G k i := by
  obtain ⟨h1, h2⟩ := treeParent_spec hG u hu.symm
  refine ⟨treeParent G u i, h1.symm, ?_⟩
  rw [mem_treeBranch, SimpleGraph.dist_comm, SimpleGraph.dist_comm (u := i)]
  omega

/-- The other vertices of a tree are partitioned by the branches behind the neighbours of `i`. -/
private theorem erase_eq_biUnion_treeBranch [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsTree) (i : V) :
    Finset.univ.erase i = (G.neighborFinset i).biUnion fun k ↦ treeBranch G k i := by
  ext u
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
    SimpleGraph.mem_neighborFinset]
  constructor
  · intro hu
    obtain ⟨k, hk, hku⟩ := exists_mem_treeBranch hG hu
    exact ⟨k, hk.symm, hku⟩
  · rintro ⟨k, hk, hku⟩ rfl
    exact not_mem_treeBranch hku

/-- The branch of `(i, j)` is `i` together with the branches behind the other neighbours. -/
private theorem treeBranch_eq_insert [DecidableEq V] [DecidableRel G.Adj] (hG : G.IsTree)
    {i j : V} (hij : G.Adj i j) :
    treeBranch G i j = insert i (((G.neighborFinset i).erase j).biUnion
      fun k ↦ treeBranch G k i) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_erase,
    SimpleGraph.mem_neighborFinset]
  constructor
  · intro hu
    by_cases hui : u = i
    · exact Or.inl hui
    · right
      obtain ⟨k, hk, hku⟩ := exists_mem_treeBranch hG hui
      refine ⟨k, ⟨fun hkj ↦ ?_, hk.symm⟩, hku⟩
      subst hkj
      have := dist_of_mem_treeBranch hG hij hu
      rw [mem_treeBranch] at hku
      omega
  · rintro (rfl | ⟨k, ⟨hkj, hk⟩, hku⟩)
    · exact self_mem_treeBranch hij
    · exact treeBranch_subset hG hij hk.symm hkj hku

/-- On the branch of `(i, j)`, away from `i`, parents towards `i` and towards `j` agree. -/
private theorem treeParent_eq_of_mem_treeBranch (hG : G.IsTree) {i j u : V} (hij : G.Adj i j)
    (hu : u ∈ treeBranch G i j) (hui : u ≠ i) : treeParent G j u = treeParent G i u := by
  have huj : u ≠ j := fun h ↦ not_mem_treeBranch (h ▸ hu)
  obtain ⟨hw, hdw⟩ := treeParent_spec hG i hui
  obtain ⟨hw', hdw'⟩ := treeParent_spec hG j huj
  have hdu := dist_of_mem_treeBranch hG hij hu
  set w := treeParent G i u
  have h1 := tree_dist_adj hG w hij
  have h2 := tree_dist_adj hG j hw
  rw [SimpleGraph.dist_comm (u := u) (v := j), SimpleGraph.dist_comm (u := w) (v := j)] at h2
  refine tree_eq_of_dist_add_one hG (u := j) hw' hw hdw' ?_
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

/-- The parent of a vertex in the branch of `(i, j)` towards `j` is `j` or lies in the branch. -/
private theorem treeParent_mem_insert_treeBranch (hG : G.IsTree) {i j u : V} (hij : G.Adj i j)
    (hu : u ∈ treeBranch G i j) : treeParent G j u ∈ insert j (treeBranch G i j) := by
  by_cases hui : u = i
  · subst hui
    rw [treeParent_of_adj hG hij]
    exact Finset.mem_insert_self _ _
  · rw [treeParent_eq_of_mem_treeBranch hG hij hu hui]
    refine Finset.mem_insert_of_mem ?_
    obtain ⟨hw, hdw⟩ := treeParent_spec hG i hui
    have hdu := dist_of_mem_treeBranch hG hij hu
    have h1 := tree_dist_adj hG (treeParent G i u) hij
    have h2 := tree_dist_adj hG j hw
    rw [SimpleGraph.dist_comm (u := u) (v := j),
      SimpleGraph.dist_comm (u := treeParent G i u) (v := j)] at h2
    rw [mem_treeBranch]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

end TreeBranch

variable {V S : Type*} [Fintype V] [LinearOrder V] [Fintype S]

/-- The factor of vertex `u` in the weight of a tree model rooted at `r`: its vertex potential
and the potential of the edge to its parent. -/
private def bpFactor (M : PairwiseGraphicalModel V S) (r u : V) (x : V → S) : ℝ :=
  M.vertexPotential u (x u) *
    M.edgePotential u (treeParent M.graph r u) (x u) (x (treeParent M.graph r u))

omit [Fintype S] in
/-- The weight of a tree model as a product of the root potential and the rooted vertex
factors. -/
private theorem weight_eq_rooted (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    (r : V) (x : V → S) :
    M.weight x = M.vertexPotential r (x r) * ∏ u ∈ Finset.univ.erase r, bpFactor M r u x := by
  set par := treeParent M.graph r
  have hpar : ∀ u, u ≠ r → M.graph.Adj u (par u) ∧ M.graph.dist r (par u) + 1 =
      M.graph.dist r u := fun u hu ↦ treeParent_spec htree r hu
  have hE : ∏ e ∈ M.orderedEdges, M.edgePotential e.1 e.2 (x e.1) (x e.2) =
      ∏ u ∈ Finset.univ.erase r, M.edgePotential u (par u) (x u) (x (par u)) := by
    symm
    refine Finset.prod_bij (fun k _ ↦ if k < par k then (k, par k) else (par k, k)) ?_ ?_ ?_ ?_
    · intro k hk
      have hadj := (hpar k (Finset.ne_of_mem_erase hk)).1
      simp only [PairwiseGraphicalModel.orderedEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      split_ifs with h
      · exact ⟨h, hadj⟩
      · exact ⟨lt_of_le_of_ne (not_lt.mp h) hadj.ne.symm, hadj.symm⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      have h₁ := (hpar k₁ (Finset.ne_of_mem_erase hk₁)).2
      have h₂ := (hpar k₂ (Finset.ne_of_mem_erase hk₂)).2
      split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> obtain ⟨e₁, e₂⟩ := heq
      · exact e₁
      · have := congrArg (M.graph.dist r) e₁; have := congrArg (M.graph.dist r) e₂; omega
      · have := congrArg (M.graph.dist r) e₁; have := congrArg (M.graph.dist r) e₂; omega
      · exact e₂
    · rintro ⟨e₁, e₂⟩ he
      simp only [PairwiseGraphicalModel.orderedEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at he
      obtain ⟨hlt, hadj⟩ := he
      rcases htree.dist_eq_dist_add_one_of_adj r hadj with h | h
      · have hr : e₁ ≠ r := by rintro rfl; simp at h
        have hp := tree_eq_of_dist_add_one htree (hpar e₁ hr).1 hadj (hpar e₁ hr).2 h.symm
        refine ⟨e₁, Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
        simp [hp, hlt]
      · have hr : e₂ ≠ r := by rintro rfl; simp at h
        have hp := tree_eq_of_dist_add_one htree (hpar e₂ hr).1 hadj.symm (hpar e₂ hr).2 h.symm
        refine ⟨e₂, Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
        simp [hp, not_lt.mpr hlt.le]
    · intro k _
      split_ifs
      · rfl
      · exact M.edgePotential_symm _ _ _ _
  unfold PairwiseGraphicalModel.weight bpFactor
  rw [hE, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), Finset.prod_mul_distrib]
  ring

/-- The product of the rooted factors over the branch of `(i, j)`, rooted at `j`. -/
private def bpBranchWeight (M : PairwiseGraphicalModel V S) (i j : V) (x : V → S) : ℝ :=
  ∏ u ∈ treeBranch M.graph i j, bpFactor M j u x

/-- The exact message from `i` to `j` of a tree model: the branch weight of `(i, j)` summed
over the branch, with the state of `j` equal to `b`. -/
private def bpTreeMessage (M : PairwiseGraphicalModel V S) (i j : V) (b : S) : ℝ :=
  coordSum (treeBranch M.graph i j) (bpBranchWeight M i j) fun _ ↦ b

omit [LinearOrder V] [Fintype S] in
/-- Branch weights are positive. -/
private theorem bpBranchWeight_pos (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    {i j : V} (x : V → S) : 0 < bpBranchWeight M i j x := by
  refine Finset.prod_pos fun u hu ↦ ?_
  have huj : u ≠ j := fun h ↦ not_mem_treeBranch (h ▸ hu)
  exact mul_pos (M.vertexPotential_pos _ _)
    (M.edgePotential_pos _ _ (treeParent_spec htree j huj).1 _ _)

omit [LinearOrder V] [Fintype S] in
/-- The branch weight of `(i, j)` reads only the coordinates of the branch and of `j`. -/
private theorem dependsOn_bpBranchWeight (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree) {i j : V} (hij : M.graph.Adj i j) :
    DependsOn (bpBranchWeight M i j) ↑(insert j (treeBranch M.graph i j)) := by
  intro z z' hz
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  unfold bpFactor
  rw [hz u (Finset.mem_insert_of_mem hu),
    hz _ (treeParent_mem_insert_treeBranch htree hij hu)]

omit [LinearOrder V] [Fintype S] in
/-- Recursion of branch weights along the tree. -/
private theorem bpBranchWeight_eq (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    {i j : V} (hij : M.graph.Adj i j) (x : V → S) :
    bpBranchWeight M i j x = bpFactor M j i x *
      ∏ k ∈ (M.graph.neighborFinset i).erase j, bpBranchWeight M k i x := by
  unfold bpBranchWeight
  have hi : i ∉ ((M.graph.neighborFinset i).erase j).biUnion fun k ↦ treeBranch M.graph k i := by
    simp only [Finset.mem_biUnion, not_exists, not_and]
    intro k _ hk
    exact not_mem_treeBranch hk
  rw [treeBranch_eq_insert htree hij, Finset.prod_insert hi, Finset.prod_biUnion]
  · congr 1
    refine Finset.prod_congr rfl fun k hk ↦ Finset.prod_congr rfl fun u hu ↦ ?_
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hk
    have hui : u ≠ i := fun h ↦ not_mem_treeBranch (h ▸ hu)
    have huij := treeBranch_subset htree hij hk.2.symm hk.1 hu
    unfold bpFactor
    rw [treeParent_eq_of_mem_treeBranch htree hij huij hui]
  · intro k hk k' hk' hne
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
      SimpleGraph.mem_neighborFinset] at hk hk'
    exact treeBranch_disjoint htree hk.1.symm hk'.1.symm hne

omit [LinearOrder V] in
/-- Summing a product of branch weights behind neighbours of `i` gives the product of the
messages. -/
private theorem coordSum_prod_bpBranchWeight (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree) (i : V) (K : Finset V) (hK : K ⊆ M.graph.neighborFinset i)
    (y : V → S) :
    coordSum (K.biUnion fun k ↦ treeBranch M.graph k i)
        (fun y' ↦ ∏ k ∈ K, bpBranchWeight M k i y') y =
      ∏ k ∈ K, bpTreeMessage M k i (y i) := by
  have hadj : ∀ k ∈ K, M.graph.Adj k i := fun k hk ↦
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (hK hk)).symm
  rw [coordSum_biUnion_prod]
  · refine Finset.prod_congr rfl fun k hk ↦ ?_
    unfold bpTreeMessage
    refine dependsOn_coordSum (dependsOn_bpBranchWeight M htree (hadj k hk)) fun v hv ↦ ?_
    obtain ⟨hv₁, hv₂⟩ := hv
    rcases Finset.mem_insert.mp hv₁ with hvi | hvb
    · rw [hvi]
    · exact absurd hvb hv₂
  · intro k hk k' hk' hne
    exact treeBranch_disjoint htree (hadj k hk) (hadj k' hk') hne
  · intro k hk
    refine (dependsOn_bpBranchWeight M htree (hadj k hk)).mono fun v hv hv' ↦ ?_
    rw [Finset.mem_coe, Finset.mem_biUnion] at hv'
    obtain ⟨k', hk'mem, hv'⟩ := hv'
    obtain ⟨hne, hk'⟩ := Finset.mem_erase.mp hk'mem
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hv) with h | h
    · exact not_mem_treeBranch (h ▸ hv')
    · exact Finset.disjoint_left.mp (treeBranch_disjoint htree (hadj k hk) (hadj k' hk')
      (Ne.symm hne)) h hv'


omit [LinearOrder V] in
/-- Summing over all coordinates but `i` at a constant configuration. -/
private theorem coordSum_erase_const (i : V) (f : (V → S) → ℝ) (a : S) :
    coordSum (Finset.univ.erase i) f (fun _ ↦ a) = ∑ x, if x i = a then f x else 0 := by
  unfold coordSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr (Finset.filter_congr fun x _ ↦ ?_) fun _ _ ↦ rfl
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_not]
  exact ⟨fun h ↦ h i rfl, fun h v hv ↦ hv ▸ h⟩

/-- Summing over all coordinates but `i` and `j`. -/
private theorem coordSum_erase_erase (i j : V) (hij : i ≠ j) (f : (V → S) → ℝ) (a b : S) :
    coordSum ((Finset.univ.erase i).erase j) f (Function.update (fun _ ↦ a) j b) =
      ∑ x, if x i = a ∧ x j = b then f x else 0 := by
  unfold coordSum
  rw [← Finset.sum_filter]
  refine Finset.sum_congr (Finset.filter_congr fun x _ ↦ ?_) fun _ _ ↦ rfl
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h i fun _ ↦ rfl
      rwa [Function.update_of_ne hij] at this
    · have := h j fun h' ↦ absurd rfl h'
      rwa [Function.update_self] at this
  · rintro ⟨ha, hb⟩ v hv
    by_cases hvj : v = j
    · subst hvj; rw [Function.update_self, hb]
    · rw [Function.update_of_ne hvj, hv hvj, ha]

omit [Fintype S] in
/-- The weight of a tree model rooted at `i`, as a product of branch weights. -/
private theorem weight_eq_prod_bpBranchWeight (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree) (i : V) (x : V → S) :
    M.weight x = M.vertexPotential i (x i) *
      ∏ k ∈ M.graph.neighborFinset i, bpBranchWeight M k i x := by
  rw [weight_eq_rooted M htree i, erase_eq_biUnion_treeBranch htree i, Finset.prod_biUnion]
  · rfl
  · intro k hk k' hk' hne
    exact treeBranch_disjoint htree ((SimpleGraph.mem_neighborFinset _ _ _).mp hk).symm
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hk').symm hne

omit [LinearOrder V] [Fintype S] in
/-- A neighbour `k ≠ j` of `i` has no branch containing `j`. -/
private theorem not_mem_treeBranch_of_ne {M : PairwiseGraphicalModel V S}
    (htree : M.graph.IsTree) {i j k : V} (hij : M.graph.Adj i j) (hkj : k ≠ j) :
    j ∉ treeBranch M.graph k i := by
  rw [mem_treeBranch, SimpleGraph.dist_eq_one_iff_adj.mpr hij]
  intro h
  exact hkj (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp (Nat.lt_one_iff.mp h)
    |>.resolve_right fun h' ↦ h' (htree.connected k j))

omit [LinearOrder V] in
/-- The exact tree messages satisfy the belief-propagation equations with unit scale. -/
private theorem bpTreeMessage_eq (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    {i j : V} (hij : M.graph.Adj i j) (b : S) :
    bpTreeMessage M i j b = ∑ a, M.vertexPotential i a * M.edgePotential i j a b *
      incomingMessageProduct M (bpTreeMessage M) i j a := by
  set U := ((M.graph.neighborFinset i).erase j).biUnion fun k ↦ treeBranch M.graph k i
  have hiU : i ∉ U := by
    simp only [U, Finset.mem_biUnion, not_exists, not_and]
    exact fun k _ hk ↦ not_mem_treeBranch hk
  have hjU : j ∉ U := by
    simp only [U, Finset.mem_biUnion, Finset.mem_erase, not_exists, not_and]
    exact fun k hk ↦ not_mem_treeBranch_of_ne htree hij hk.1
  show coordSum (treeBranch M.graph i j) (bpBranchWeight M i j) (fun _ ↦ b) = _
  rw [treeBranch_eq_insert htree hij, Finset.insert_eq,
    coordSum_union (Finset.disjoint_singleton_left.mpr hiU), coordSum_singleton]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  set y := Function.update (fun _ : V ↦ b) i a
  rw [coordSum_congr (g := fun y' ↦ bpFactor M j i y' *
      ∏ k ∈ (M.graph.neighborFinset i).erase j, bpBranchWeight M k i y')
      fun y' _ ↦ bpBranchWeight_eq M htree hij y']
  rw [coordSum_mul_left _ _ fun y' hy' ↦ ?_, coordSum_prod_bpBranchWeight M htree i _
    (Finset.erase_subset _ _)]
  · unfold bpFactor incomingMessageProduct
    rw [treeParent_of_adj htree hij]
    simp [y, Function.update_of_ne hij.ne.symm]
  · unfold bpFactor
    rw [treeParent_of_adj htree hij, hy' i hiU, hy' j hjU]

/-- The unnormalized node belief of the exact tree messages is the unnormalized marginal. -/
private theorem bpTreeMessage_node (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    (i : V) (a : S) :
    M.vertexPotential i a * ∏ k ∈ M.graph.neighborFinset i, bpTreeMessage M k i a =
      ∑ x, if x i = a then M.weight x else 0 := by
  rw [← coordSum_erase_const, coordSum_congr (g := fun y ↦ M.vertexPotential i (y i) *
      ∏ k ∈ M.graph.neighborFinset i, bpBranchWeight M k i y)
      fun y _ ↦ weight_eq_prod_bpBranchWeight M htree i y,
    coordSum_mul_left _ _ fun y' hy' ↦ by rw [hy' i (by simp)]]
  rw [erase_eq_biUnion_treeBranch htree i, coordSum_prod_bpBranchWeight M htree i _ le_rfl]

/-- The unnormalized edge belief of the exact tree messages is the unnormalized pair
marginal. -/
private theorem bpTreeMessage_edge (M : PairwiseGraphicalModel V S) (htree : M.graph.IsTree)
    {i j : V} (hij : M.graph.Adj i j) (a b : S) :
    M.vertexPotential i a * M.vertexPotential j b * M.edgePotential i j a b *
        incomingMessageProduct M (bpTreeMessage M) i j a *
        incomingMessageProduct M (bpTreeMessage M) j i b =
      ∑ x, if x i = a ∧ x j = b then M.weight x else 0 := by
  set Ui := ((M.graph.neighborFinset i).erase j).biUnion fun k ↦ treeBranch M.graph k i
  set Uj := ((M.graph.neighborFinset j).erase i).biUnion fun l ↦ treeBranch M.graph l j
  have hmemUi : ∀ v, v ∈ Ui ↔ ∃ k, (k ≠ j ∧ M.graph.Adj i k) ∧ v ∈ treeBranch M.graph k i := by
    intro v; simp [Ui]
  have hmemUj : ∀ v, v ∈ Uj ↔ ∃ l, (l ≠ i ∧ M.graph.Adj j l) ∧ v ∈ treeBranch M.graph l j := by
    intro v; simp [Uj]
  have hUjsub : ∀ l, l ≠ i → M.graph.Adj j l →
      treeBranch M.graph l j ⊆ treeBranch M.graph j i := fun l hli hl ↦
    treeBranch_subset htree hij.symm hl.symm hli
  have hiUi : i ∉ Ui := by
    rw [hmemUi]; rintro ⟨k, -, hk⟩; exact not_mem_treeBranch hk
  have hjUi : j ∉ Ui := by
    rw [hmemUi]; rintro ⟨k, ⟨hkj, -⟩, hk⟩; exact not_mem_treeBranch_of_ne htree hij hkj hk
  have hjUj : j ∉ Uj := by
    rw [hmemUj]; rintro ⟨l, -, hl⟩; exact not_mem_treeBranch hl
  have hiUj : i ∉ Uj := by
    rw [hmemUj]; rintro ⟨l, ⟨hli, -⟩, hl⟩
    exact not_mem_treeBranch_of_ne htree hij.symm hli hl
  -- the branches behind `j` avoid the coordinates read by the factors behind `i`
  have hUjk : ∀ k, k ≠ j → M.graph.Adj i k →
      Uj ⊆ Finset.univ \ insert i (treeBranch M.graph k i) := by
    intro k hkj hk v hv
    have hvi : v ≠ i := fun h ↦ hiUj (h ▸ hv)
    obtain ⟨l, ⟨hli, hl⟩, hvl⟩ := (hmemUj v).mp hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
    exact ⟨hvi, fun h ↦ Finset.disjoint_left.mp (treeBranch_disjoint htree hk.symm hij.symm hkj)
      h (hUjsub l hli hl hvl)⟩
  have hdisj : Disjoint Ui Uj := by
    rw [Finset.disjoint_left]
    intro v hvi hvj
    obtain ⟨k, ⟨hkj, hk⟩, hvk⟩ := (hmemUi v).mp hvi
    exact (Finset.mem_sdiff.mp (hUjk k hkj hk hvj)).2 (Finset.mem_insert_of_mem hvk)
  have hU : (Finset.univ.erase i).erase j = Ui ∪ Uj := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union]
    constructor
    · rintro ⟨hvj, hvi⟩
      obtain ⟨k, hk, hvk⟩ := exists_mem_treeBranch htree hvi
      by_cases hkj : k = j
      · subst hkj
        obtain ⟨l, hl, hvl⟩ := exists_mem_treeBranch htree hvj
        refine Or.inr ((hmemUj v).mpr ⟨l, ⟨fun hli ↦ ?_, hl.symm⟩, hvl⟩)
        subst hli
        have h1 := (mem_treeBranch.mp hvk)
        have h2 := (mem_treeBranch.mp hvl)
        omega
      · exact Or.inl ((hmemUi v).mpr ⟨k, ⟨hkj, hk.symm⟩, hvk⟩)
    · rintro (hv | hv)
      · exact ⟨fun h ↦ hjUi (h ▸ hv), fun h ↦ hiUi (h ▸ hv)⟩
      · exact ⟨fun h ↦ hjUj (h ▸ hv), fun h ↦ hiUj (h ▸ hv)⟩
  have hjN : j ∈ M.graph.neighborFinset i := (SimpleGraph.mem_neighborFinset _ _ _).mpr hij
  set A : (V → S) → ℝ := fun x ↦ M.vertexPotential i (x i) * M.vertexPotential j (x j) *
    M.edgePotential i j (x i) (x j) *
      ∏ k ∈ (M.graph.neighborFinset i).erase j, bpBranchWeight M k i x
  have hw : ∀ x, M.weight x =
      A x * ∏ l ∈ (M.graph.neighborFinset j).erase i, bpBranchWeight M l j x := by
    intro x
    rw [weight_eq_prod_bpBranchWeight M htree i, ← Finset.mul_prod_erase _ _ hjN,
      bpBranchWeight_eq M htree hij.symm]
    unfold bpFactor
    rw [treeParent_of_adj htree hij.symm, M.edgePotential_symm j i]
    ring
  rw [← coordSum_erase_erase i j hij.ne, hU, coordSum_union hdisj,
    coordSum_congr (g := fun y ↦ A y * ∏ l ∈ (M.graph.neighborFinset j).erase i,
      bpTreeMessage M l j (y j)) fun y _ ↦ ?_]
  · rw [coordSum_congr (g := fun y ↦ (M.vertexPotential i (y i) * M.vertexPotential j (y j) *
        M.edgePotential i j (y i) (y j) * ∏ l ∈ (M.graph.neighborFinset j).erase i,
          bpTreeMessage M l j (y j)) *
        ∏ k ∈ (M.graph.neighborFinset i).erase j, bpBranchWeight M k i y) fun y _ ↦ by
          simp only [A]; ring]
    rw [coordSum_mul_left _ _ fun y' hy' ↦ by rw [hy' i hiUi, hy' j hjUi],
      coordSum_prod_bpBranchWeight M htree i _ (Finset.erase_subset _ _)]
    unfold incomingMessageProduct
    simp only [Function.update_self, Function.update_of_ne hij.ne]
    ring
  · rw [coordSum_congr (g := fun y' ↦ A y' * ∏ l ∈ (M.graph.neighborFinset j).erase i,
        bpBranchWeight M l j y') fun y' _ ↦ hw y',
      coordSum_mul_left _ _ fun y' hy' ↦ ?_,
      coordSum_prod_bpBranchWeight M htree j _ (Finset.erase_subset _ _)]
    simp only [A]
    rw [hy' i hiUj, hy' j hjUj]
    congr 1
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hk
    exact dependsOn_bpBranchWeight M htree hk.2.symm fun v hv ↦
      hy' v fun hvU ↦ (Finset.mem_sdiff.mp (hUjk k hk.1 hk.2 hvU)).2 hv

/-- GAPS 107.23: positive tree models have BP fixed points giving the exact node and edge marginals.
The leaf-to-root implementation and the reconstruction theorem for arbitrary boundary beliefs
are separate parts of the catalogue entry. -/
theorem exists_beliefPropagation_exact_on_tree (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree) :
    ∃ m, IsBeliefPropagationFixedPoint M m ∧
      (∀ i a, beliefPropagationNode M m i a =
        ∑ x : V → S, if x i = a then M.mass x else 0) ∧
      ∀ i j, M.graph.Adj i j → ∀ a b,
        beliefPropagationEdge M m i j a b =
          ∑ x : V → S, if x i = a ∧ x j = b then M.mass x else 0 := by
  have hZ : ∀ f : (V → S) → ℝ, ∀ i : V, ∑ a, (∑ x, if x i = a then f x else 0) = ∑ x, f x := by
    intro f i
    rw [Finset.sum_comm]
    simp
  refine ⟨bpTreeMessage M, ⟨fun i j hij a ↦ ?_, fun i j hij ↦ ⟨1, one_pos, fun b ↦ ?_⟩⟩,
    fun i a ↦ ?_, fun i j hij a b ↦ ?_⟩
  · unfold bpTreeMessage coordSum
    exact Finset.sum_pos (fun x _ ↦ bpBranchWeight_pos M htree x)
      ⟨fun _ ↦ a, by simp⟩
  · rw [one_mul]; exact bpTreeMessage_eq M htree hij b
  · unfold beliefPropagationNode
    dsimp only
    simp_rw [bpTreeMessage_node M htree i]
    rw [hZ, Finset.sum_div]
    unfold PairwiseGraphicalModel.mass PairwiseGraphicalModel.partitionFunction
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  · unfold beliefPropagationEdge
    dsimp only
    simp_rw [bpTreeMessage_edge M htree hij]
    have hZ2 : ∑ z : S × S, (∑ x, if x i = z.1 ∧ x j = z.2 then M.weight x else 0) =
        ∑ x, M.weight x := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Finset.sum_eq_single (x i, x j)]
      · simp
      · rintro ⟨a', b'⟩ _ hne
        refine ite_eq_right_iff.mpr fun h ↦ absurd ?_ hne
        obtain ⟨h1, h2⟩ := h
        rw [h1, h2]
      · simp
    rw [hZ2, Finset.sum_div]
    unfold PairwiseGraphicalModel.mass PairwiseGraphicalModel.partitionFunction
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp

/-- In a tree, the branch of a directed edge `(k, i)` behind `k` is strictly contained in the
branch of `(i, j)` behind `i` when `k ≠ j`. -/
private theorem tree_branch_card_lt {V : Type*} [Fintype V] {G : SimpleGraph V} (hG : G.IsTree)
    {i j k : V} (hij : G.Adj i j) (hki : G.Adj k i) (hkj : k ≠ j) :
    (Finset.univ.filter fun u ↦ G.dist u k < G.dist u i).card <
      (Finset.univ.filter fun u ↦ G.dist u i < G.dist u j).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, ?_, ?_⟩
    · simp [SimpleGraph.dist_eq_one_iff_adj.mpr hij]
    · simp [SimpleGraph.dist_eq_one_iff_adj.mpr hki.symm]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have h1 := hG.dist_eq_dist_add_one_of_adj u hki
    have h2 := hG.dist_eq_dist_add_one_of_adj u hij
    rcases h2 with h2 | h2
    · exfalso
      exact hkj (tree_eq_of_dist_add_one hG hki.symm hij (by omega) h2.symm)
    · omega

set_option linter.unusedSectionVars false in
/-- GAPS 107.23: each directed-edge message in a positive tree model is unique up to positive
scale. The proof is by strong induction on the size of the branch behind the sending vertex. -/
theorem beliefPropagation_tree_unique_up_to_scale (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree)
    (m m' : V → V → S → ℝ)
    (hm : IsBeliefPropagationFixedPoint M m) (hm' : IsBeliefPropagationFixedPoint M m') :
    ∀ i j, M.graph.Adj i j → ∃ c > 0, ∀ a, m' i j a = c * m i j a := by
  intro i j hij
  induction hN : (Finset.univ.filter fun u ↦ M.graph.dist u i < M.graph.dist u j).card
    using Nat.strong_induction_on generalizing i j with
  | _ N ih =>
  have hin : ∀ k ∈ (M.graph.neighborFinset i).erase j, ∃ c > 0, ∀ a, m' k i a = c * m k i a := by
    intro k hk
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hk
    exact ih _ (hN ▸ tree_branch_card_lt htree hij hk.2.symm hk.1) k i hk.2.symm rfl
  choose! c hc0 hc using hin
  have hprod : ∀ a, incomingMessageProduct M m' i j a =
      (∏ k ∈ (M.graph.neighborFinset i).erase j, c k) * incomingMessageProduct M m i j a := by
    intro a
    unfold incomingMessageProduct
    rw [Finset.prod_congr rfl fun k hk ↦ hc k hk a]
    exact Finset.prod_mul_distrib
  have hC : 0 < ∏ k ∈ (M.graph.neighborFinset i).erase j, c k :=
    Finset.prod_pos fun k hk ↦ hc0 k hk
  obtain ⟨d, hd0, hd⟩ := hm.2 i j hij
  obtain ⟨d', hd0', hd'⟩ := hm'.2 i j hij
  refine ⟨d' * (∏ k ∈ (M.graph.neighborFinset i).erase j, c k) / d, by positivity, fun b ↦ ?_⟩
  rw [hd' b, hd b]
  simp_rw [hprod, mul_left_comm _ (∏ k ∈ (M.graph.neighborFinset i).erase j, c k),
    ← Finset.mul_sum]
  field_simp

end CKSD
