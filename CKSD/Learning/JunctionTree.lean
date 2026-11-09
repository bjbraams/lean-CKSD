module

public import CKSD.Learning.Basic
public import CKSD.Learning.ChordalGraphs
public import CKSD.Learning.CoordinateSum
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Junction trees and triangulated graphs

A graph is triangulated (chordal) when every cycle of length at least four has a chord. A
junction tree of a finite graph is a tree on an enumeration of its maximal cliques in which
every clique on the path between two cliques contains their intersection. Clique tables are
real functions on the configurations of the clique's vertices; marginalization to a separator
sums over the remaining coordinates. Ratios use Lean's convention `x / 0 = 0`, which is the
`0/0 = 0` convention of the catalogue since a zero separator entry forces zero clique entries
under local consistency.

Graphs, walks, paths, cliques, and trees are Mathlib's `SimpleGraph` API; configurations take
values in a finite alphabet `S`.

## Main definitions

* `CKSD.IsTriangulatedGraph`, `CKSD.IsJunctionTree`, `CKSD.HasJunctionTree`.
* `CKSD.jointMarginal`, `CKSD.tableMarginal`, `CKSD.junctionTreeProduct`.

## Main results

* `CKSD.hasJunctionTree_iff_isTriangulated`: junction trees exist exactly for triangulated
  graphs (GAPS 107.27).
* `CKSD.sum_eq_one_and_tableMarginal_eq_of_jointMarginal`,
  `CKSD.junctionTreeProduct_isJointLaw`, `CKSD.exists_joint_with_clique_marginals_iff`: the
  marginal problem on a junction tree (GAPS 107.27).
-/

@[expose] public section

noncomputable section

open Finset
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A graph is triangulated: every cycle of length at least four has a chord, an edge of the
graph between two of its vertices that is not an edge of the cycle. -/
def IsTriangulatedGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.IsCycle → 4 ≤ p.length →
    ∃ a ∈ p.support, ∃ b ∈ p.support, G.Adj a b ∧ s(a, b) ∉ p.edges

/-- `T` on the enumeration `c` of cliques is a junction tree of `G`: `c` lists every maximal
clique exactly once, `T` is a tree, and every clique on the path between two cliques contains
their intersection. Maximal cliques are the finite vertex sets that are maximal (Mathlib's
`Maximal`) among the cliques. -/
def IsJunctionTree {V : Type*} (G : SimpleGraph V) {m : ℕ} (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) : Prop :=
  Function.Injective c ∧ (∀ i, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) (c i)) ∧
    (∀ C, Maximal (fun D : Finset V ↦ G.IsClique (D : Set V)) C → ∃ i, c i = C) ∧ T.IsTree ∧
    ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k

/-- A graph has a junction tree. -/
def HasJunctionTree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (c : Fin m → Finset V) (T : SimpleGraph (Fin m)), IsJunctionTree G c T

/-- GAPS 107.27: a finite graph has a junction tree if and only if it is triangulated. -/
theorem hasJunctionTree_iff_isTriangulated {V : Type*} [Fintype V] (G : SimpleGraph V) :
    HasJunctionTree G ↔ IsTriangulatedGraph G :=
  ⟨fun ⟨_, c, T, _, hmax, hcov, hT, hrip⟩ ↦ chordal_of_junctionTree G c T hmax hcov hT hrip,
    fun h ↦ exists_junctionTree_of_chordal G h⟩

/-- Marginal table of a joint configuration mass on a finite set of vertices. -/
def jointMarginal {V S : Type*} [Fintype V] [Fintype S] (p : (V → S) → ℝ) (C : Finset V)
    (y : C → S) : ℝ :=
  ∑ x : V → S, if ∀ v : C, x v = y v then p x else 0

/-- Marginal of a table on `C` to the subset `D`, given by its membership proof. -/
def tableMarginal {V S : Type*} [Fintype S] {C D : Finset V} (hD : D ⊆ C) (b : (C → S) → ℝ)
    (z : D → S) : ℝ :=
  ∑ y : C → S, if ∀ v : D, y ⟨v, hD v.2⟩ = z v then b y else 0

/-- Junction-tree product formula: clique tables divided by separator tables, one separator
factor per tree edge, the separator table being the marginal of the lower-indexed clique. -/
def junctionTreeProduct {V S : Type*} [Fintype S] {m : ℕ} (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) (b : ∀ i, (c i → S) → ℝ) (x : V → S) : ℝ :=
  (∏ i, b i fun v ↦ x v) /
    ∏ e ∈ univ.filter (fun e : Fin m × Fin m ↦ e.1 < e.2 ∧ T.Adj e.1 e.2),
      tableMarginal (inter_subset_left (s₁ := c e.1) (s₂ := c e.2)) (b e.1) fun v ↦ x v

section CoordSum

variable {V S : Type*} [Fintype V] [Fintype S]

/-- Summing a clique table over coordinates `D ⊆ C` is a table sum with the coordinates of
`C \ D` frozen. -/
private theorem coordSum_table {C D : Finset V} (hD : D ⊆ C) (g : (C → S) → ℝ) (x : V → S) :
    coordSum D (fun x' ↦ g fun v : C ↦ x' v) x =
      ∑ y : C → S, if ∀ v : C, (v : V) ∉ D → y v = x v then g y else 0 := by
  unfold coordSum
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun x' _ ↦ fun v : C ↦ x' v)
    (fun y _ ↦ fun v ↦ if h : v ∈ C then y ⟨v, h⟩ else x v) ?_ ?_ ?_ ?_ ?_
  · intro x' hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' ⊢
    exact fun v hv ↦ hx' v hv
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro v hv
    by_cases hvC : v ∈ C
    · rw [dite_eq_left hvC]
      exact hy ⟨v, hvC⟩ hv
    · simp [hvC]
  · intro x' hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    funext v
    by_cases hvC : v ∈ C
    · simp [hvC]
    · rw [dite_eq_right hvC]
      exact (hx' v fun h ↦ hvC (hD h)).symm
  · intro y _
    funext v
    simp
  · intro x' _
    rfl

end CoordSum


section TreeDist

variable {ι : Type*} {T : SimpleGraph ι}

/-- In a tree, two neighbours of `i` that are both one step closer to `u` coincide. -/
private theorem jt_eq_of_dist_add_one (hT : T.IsTree) {u i j k : ι} (hj : T.Adj i j)
    (hk : T.Adj i k) (hdj : T.dist u j + 1 = T.dist u i) (hdk : T.dist u k + 1 = T.dist u i) :
    j = k := by
  classical
  obtain ⟨P, hP, hPl⟩ := (hT.connected u i).exists_path_of_dist
  have key : ∀ x, T.Adj i x → T.dist u x + 1 = T.dist u i → x = P.penultimate := by
    intro x hx hdx
    obtain ⟨Q, hQ, hQl⟩ := (hT.connected u x).exists_path_of_dist
    have hiQ : i ∉ Q.support := by
      intro hi
      have h1 := SimpleGraph.dist_le (Q.takeUntil i hi)
      have h2 := Q.length_takeUntil_le_length hi
      omega
    have hxP := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hP hQ hx hiQ
    exact hT.isAcyclic.eq_penultimate_of_adj_end hP hx hxP
  rw [key j hj hdj, key k hk hdk]

/-- In a tree every vertex other than the root has a neighbour one step closer to the root. -/
private theorem jt_exists_parent (hT : T.IsTree) (r : ι) {k : ι} (hk : k ≠ r) :
    ∃ p, T.Adj k p ∧ T.dist r p + 1 = T.dist r k := by
  obtain ⟨W, -, hWl⟩ := (hT.connected k r).exists_path_of_dist
  cases W with
  | nil => exact absurd rfl hk
  | @cons _ p _ hkp W' =>
    refine ⟨p, hkp, ?_⟩
    have h1 := SimpleGraph.dist_le W'
    rw [SimpleGraph.Walk.length_cons] at hWl
    have e1 : T.dist r p = T.dist p r := SimpleGraph.dist_comm
    have e2 : T.dist r k = T.dist k r := SimpleGraph.dist_comm
    rcases hT.dist_eq_dist_add_one_of_adj r hkp with h | h <;> omega

/-- Along a path that leaves `a` away from its neighbour `a'` closer to the root, the distance
to the root increases by one at each step. -/
private theorem jt_dist_of_isPath_away (hT : T.IsTree) (r : ι) {a k : ι} (W : T.Walk a k)
    (hW : W.IsPath) {a' : ι} (haa' : T.Adj a a') (hd : T.dist r a' + 1 = T.dist r a)
    (ha' : a' ∉ W.support) : T.dist r k = T.dist r a + W.length := by
  induction W generalizing a' with
  | nil => simp
  | @cons a b k hab W' ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hW
    have hba' : b ≠ a' := fun h ↦ ha' (by simp [← h])
    have hdb : T.dist r b = T.dist r a + 1 := by
      rcases hT.dist_eq_dist_add_one_of_adj r hab with h | h
      · exact absurd (jt_eq_of_dist_add_one hT hab haa' h.symm hd) hba'
      · exact h
    rw [ih hW.1 hab.symm hdb.symm hW.2, hdb, SimpleGraph.Walk.length_cons]
    ring

/-- In a tree with root `r`, the path from `i` to a vertex `k ≠ i` no farther from the root
passes through the parent `p` of `i`. -/
private theorem jt_parent_mem_support (hT : T.IsTree) (r : ι) {i p k : ι} (hip : T.Adj i p)
    (hd : T.dist r p + 1 = T.dist r i) (hki : k ≠ i) (hk : T.dist r k ≤ T.dist r i)
    (W : T.Walk i k) (hW : W.IsPath) : p ∈ W.support := by
  by_contra hp
  have h := jt_dist_of_isPath_away hT r W hW hip hd hp
  have hl : W.length ≠ 0 := fun h0 ↦ hki (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
  omega

end TreeDist

section JunctionProduct

variable {V S : Type*} [Fintype V] [Fintype S] {m : ℕ}

/-- Separator value at `x` of the table of clique `k` on its intersection with clique `l`. -/
private def jtSep (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ) (k l : Fin m)
    (x : V → S) : ℝ :=
  ∑ y : c k → S, if ∀ v : c k, (v : V) ∈ c l → y v = x v then b k y else 0

omit [Fintype V] in
/-- A separator value depends only on the coordinates in the intersection of the cliques. -/
private theorem jtSep_congr (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ) (k l : Fin m)
    {x x' : V → S} (h : ∀ v ∈ c k, v ∈ c l → x' v = x v) :
    jtSep c b k l x' = jtSep c b k l x := by
  unfold jtSep
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v : c k, (v : V) ∈ c l → y v = x' v) ↔ ∀ v : c k, (v : V) ∈ c l → y v = x v :=
    forall_congr' fun v ↦ imp_congr_right fun hv ↦ by rw [h v v.2 hv]
  rw [if_congr this rfl rfl]

/-- Summing a clique table over the coordinates outside the separator gives the separator
value. -/
private theorem coordSum_eq_jtSep (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ) (k l : Fin m)
    (x : V → S) : coordSum (c k \ c l) (fun x' ↦ b k fun v ↦ x' v) x = jtSep c b k l x := by
  rw [coordSum_table sdiff_subset]
  unfold jtSep
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v : c k, (v : V) ∉ c k \ c l → y v = x v) ↔
      ∀ v : c k, (v : V) ∈ c l → y v = x v :=
    forall_congr' fun v ↦ by simp [v.2]
  rw [if_congr this rfl rfl]

omit [Fintype V] in
/-- A vanishing separator value of a nonnegative table forces the clique entry to vanish. -/
private theorem jtSep_eq_zero (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ)
    (hb : ∀ i y, 0 ≤ b i y) (k l : Fin m) (x : V → S) (h : jtSep c b k l x = 0) :
    b k (fun v ↦ x v) = 0 := by
  unfold jtSep at h
  rw [Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ by split_ifs <;> simp [hb]] at h
  simpa using h (fun v ↦ x v) (Finset.mem_univ _)

omit [Fintype V] in
/-- The separator marginal of the left clique of a pair, evaluated at `x`. -/
private theorem tableMarginal_eq_jtSep (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ)
    (k l : Fin m) (x : V → S) :
    tableMarginal (inter_subset_left (s₁ := c k) (s₂ := c l)) (b k) (fun v ↦ x v) =
      jtSep c b k l x := by
  unfold tableMarginal jtSep
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v : (c k ∩ c l : Finset V), y ⟨v, inter_subset_left v.2⟩ = x v) ↔
      ∀ v : c k, (v : V) ∈ c l → y v = x v :=
    ⟨fun h v hv ↦ h ⟨v, mem_inter.mpr ⟨v.2, hv⟩⟩, fun h v ↦ h _ (mem_inter.mp v.2).2⟩
  rw [if_congr this rfl rfl]

omit [Fintype V] in
/-- The separator marginal of the right clique of a pair, evaluated at `x`. -/
private theorem tableMarginal_right_eq_jtSep (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ)
    (k l : Fin m) (x : V → S) :
    tableMarginal (inter_subset_right (s₁ := c k) (s₂ := c l)) (b l) (fun v ↦ x v) =
      jtSep c b l k x := by
  unfold tableMarginal jtSep
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v : (c k ∩ c l : Finset V), y ⟨v, inter_subset_right v.2⟩ = x v) ↔
      ∀ v : c l, (v : V) ∈ c k → y v = x v :=
    ⟨fun h v hv ↦ h ⟨v, mem_inter.mpr ⟨hv, v.2⟩⟩, fun h v ↦ h _ (mem_inter.mp v.2).1⟩
  rw [if_congr this rfl rfl]

/-- Partial junction-tree product over a parent-closed set `A` of cliques. -/
private def jtPartial (c : Fin m → Finset V) (b : ∀ i, (c i → S) → ℝ) (r : Fin m)
    (par : Fin m → Fin m) (A : Finset (Fin m)) (x : V → S) : ℝ :=
  (∏ k ∈ A, b k fun v ↦ x v) / ∏ k ∈ A.erase r, jtSep c b k (par k) x

/-- Leaf elimination on a junction tree rooted at `r`: summing the partial product over a
parent-closed set `A` over the coordinates of its cliques outside `c r` gives the root table. -/
private theorem coordSum_jtPartial (c : Fin m → Finset V) (T : SimpleGraph (Fin m))
    (hT : T.IsTree)
    (hrip : ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k)
    (b : ∀ i, (c i → S) → ℝ) (hb : ∀ i y, 0 ≤ b i y)
    (hsymm : ∀ i j, T.Adj i j → ∀ x, jtSep c b i j x = jtSep c b j i x)
    (r : Fin m) (par : Fin m → Fin m)
    (hpar : ∀ k, k ≠ r → T.Adj k (par k) ∧ T.dist r (par k) + 1 = T.dist r k)
    (A : Finset (Fin m)) (hr : r ∈ A) (hA : ∀ k ∈ A, k ≠ r → par k ∈ A) (x : V → S) :
    coordSum (A.biUnion c \ c r) (jtPartial c b r par A) x = b r fun v ↦ x v := by
  induction A using Finset.strongInduction generalizing x with
  | H A ih =>
  by_cases hne : (A.erase r).Nonempty
  · obtain ⟨i, hiA, himax⟩ := Finset.exists_max_image (A.erase r) (fun k ↦ T.dist r k) hne
    have hir : i ≠ r := Finset.ne_of_mem_erase hiA
    have hiA' : i ∈ A := Finset.mem_of_mem_erase hiA
    set p := par i with hp_def
    obtain ⟨hip, hdp⟩ := hpar i hir
    set A' := A.erase i with hA'_def
    have hpA' : p ∈ A' := Finset.mem_erase.mpr ⟨hip.ne.symm, hA i hiA' hir⟩
    have hrA' : r ∈ A' := Finset.mem_erase.mpr ⟨hir.symm, hr⟩
    have hA'cl : ∀ k ∈ A', k ≠ r → par k ∈ A' := by
      intro k hk hkr
      have hkA := Finset.mem_of_mem_erase hk
      refine Finset.mem_erase.mpr ⟨fun hki ↦ ?_, hA k hkA hkr⟩
      have h1 := (hpar k hkr).2
      have h2 := himax k (Finset.mem_erase.mpr ⟨hkr, hkA⟩)
      rw [hki] at h1
      omega
    -- the running intersection property at the leaf `i`
    have hsep : ∀ k ∈ A', c i ∩ c k ⊆ c p := by
      intro k hk
      by_cases hkp : k = p
      · rw [hkp]; exact inter_subset_right
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      have hdk : T.dist r k ≤ T.dist r i := by
        by_cases hkr : k = r
        · rw [hkr, SimpleGraph.dist_self]; exact Nat.zero_le _
        · exact himax k (Finset.mem_erase.mpr ⟨hkr, Finset.mem_of_mem_erase hk⟩)
      obtain ⟨W, hW, -⟩ := (hT.connected i k).exists_path_of_dist
      exact hrip i k W hW p (jt_parent_mem_support hT r hip hdp hki hdk W hW)
    set D := c i \ c p with hD_def
    set E := A'.biUnion c \ c r with hE_def
    have hDk : ∀ k ∈ A', ∀ v ∈ D, v ∉ c k := by
      intro k hk v hv hvk
      rw [hD_def, Finset.mem_sdiff] at hv
      exact hv.2 (hsep k hk (Finset.mem_inter.mpr ⟨hv.1, hvk⟩))
    have hdisj : Disjoint E D := by
      rw [Finset.disjoint_left]
      intro v hvE hvD
      rw [hE_def, Finset.mem_sdiff, Finset.mem_biUnion] at hvE
      obtain ⟨k, hk, hvk⟩ := hvE.1
      exact hDk k hk v hvD hvk
    have hunion : A.biUnion c \ c r = E ∪ D := by
      have hAi : A = insert i A' := (Finset.insert_erase hiA').symm
      ext v
      rw [hAi, Finset.biUnion_insert]
      simp only [hE_def, hD_def, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ⟨hv | ⟨k, hk, hvk⟩, hvr⟩
        · by_cases hvp : v ∈ c p
          · exact Or.inl ⟨⟨p, hpA', hvp⟩, hvr⟩
          · exact Or.inr ⟨hv, hvp⟩
        · exact Or.inl ⟨⟨k, hk, hvk⟩, hvr⟩
      · rintro (⟨⟨k, hk, hvk⟩, hvr⟩ | ⟨hvi, hvp⟩)
        · exact ⟨Or.inr ⟨k, hk, hvk⟩, hvr⟩
        · exact ⟨Or.inl hvi, fun hvr ↦ hvp (hsep r hrA' (Finset.mem_inter.mpr ⟨hvi, hvr⟩))⟩
    -- one elimination step
    have hstep : ∀ y, coordSum D (jtPartial c b r par A) y = jtPartial c b r par A' y := by
      intro y
      have hsplit : ∀ y', jtPartial c b r par A y' =
          jtPartial c b r par A' y' * ((jtSep c b i p y')⁻¹ * b i fun v ↦ y' v) := by
        intro y'
        unfold jtPartial
        rw [← Finset.mul_prod_erase A _ hiA', ← Finset.mul_prod_erase (A.erase r) _ hiA,
          Finset.erase_right_comm]
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      have hA'const : ∀ y', (∀ v ∉ D, y' v = y v) →
          jtPartial c b r par A' y' = jtPartial c b r par A' y := by
        intro y' hy'
        unfold jtPartial
        congr 1
        · refine Finset.prod_congr rfl fun k hk ↦ ?_
          congr 1
          funext v
          exact hy' v fun hvD ↦ hDk k hk v hvD v.2
        · refine Finset.prod_congr rfl fun k hk ↦ ?_
          exact jtSep_congr c b k (par k) fun v hv _ ↦
            hy' v fun hvD ↦ hDk k (Finset.mem_of_mem_erase hk) v hvD hv
      have hsconst : ∀ y', (∀ v ∉ D, y' v = y v) →
          (jtSep c b i p y')⁻¹ = (jtSep c b i p y)⁻¹ := by
        intro y' hy'
        rw [jtSep_congr c b i p (x := y) (x' := y') fun v _ hvp ↦
          hy' v fun hvD ↦ (Finset.mem_sdiff.mp hvD).2 hvp]
      rw [coordSum_congr (g := fun y' ↦ jtPartial c b r par A' y' *
        ((jtSep c b i p y')⁻¹ * b i fun v ↦ y' v)) fun y' _ ↦ hsplit y']
      rw [coordSum_mul_left _ _ (hA'const), coordSum_mul_left _ _ hsconst,
        hD_def, coordSum_eq_jtSep]
      by_cases hs : jtSep c b i p y = 0
      · rw [hs, inv_zero, zero_mul, mul_zero]
        have hbp : b p (fun v ↦ y v) = 0 :=
          jtSep_eq_zero c b hb p i y ((hsymm i p hip y).symm.trans hs)
        unfold jtPartial
        rw [Finset.prod_eq_zero hpA' hbp, zero_div]
      · rw [inv_mul_cancel₀ hs, mul_one]
    rw [hunion, coordSum_union hdisj]
    rw [coordSum_congr (g := jtPartial c b r par A') fun y _ ↦ hstep y]
    exact ih A' (Finset.erase_ssubset hiA') hrA' hA'cl x
  · have hAr : A = {r} := by
      ext k
      simp only [Finset.mem_singleton]
      refine ⟨fun hk ↦ by_contra fun hkr ↦ hne ⟨k, Finset.mem_erase.mpr ⟨hkr, hk⟩⟩,
        fun hk ↦ hk ▸ hr⟩
    subst hAr
    simp [jtPartial, coordSum_empty]

end JunctionProduct

section Marginals

variable {V S : Type*} [Fintype V] [Fintype S]

/-- A marginal table has the total mass of the joint table. -/
theorem sum_jointMarginal (p : (V → S) → ℝ) (C : Finset V) :
    ∑ y, jointMarginal p C y = ∑ x, p x := by
  simp only [jointMarginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_eq_single (fun v : C ↦ x v)]
  · simp
  · intro y _ hy
    have : ¬ ∀ v : C, x v = y v := fun h ↦ hy (funext fun v ↦ (h v).symm)
    rw [ite_eq_right this]
  · simp

/-- Marginalizing the marginal on `C` to `D ⊆ C` gives the marginal on `D`. -/
theorem tableMarginal_jointMarginal (p : (V → S) → ℝ) {C D : Finset V} (hD : D ⊆ C) :
    tableMarginal hD (jointMarginal p C) = jointMarginal p D := by
  funext z
  simp only [tableMarginal, jointMarginal]
  have hite : ∀ y : C → S, (if ∀ v : D, y ⟨v, hD v.2⟩ = z v then
      ∑ x : V → S, (if ∀ v : C, x v = y v then p x else 0) else 0) =
      ∑ x : V → S, if ∀ v : D, y ⟨v, hD v.2⟩ = z v then
        (if ∀ v : C, x v = y v then p x else 0) else 0 := fun y ↦ by
    split_ifs <;> simp
  simp_rw [hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_eq_single (fun v : C ↦ x v)]
  · simp
  · intro y _ hy
    have : ¬ ∀ v : C, x v = y v := fun h ↦ hy (funext fun v ↦ (h v).symm)
    simp only [ite_eq_right this, ite_self]
  · simp

/-- GAPS 107.27, necessity in the marginal problem: the clique marginals of a joint probability
table are normalized and agree on separators. No junction-tree hypothesis is needed. -/
theorem sum_eq_one_and_tableMarginal_eq_of_jointMarginal {m : ℕ} (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) (b : ∀ i, (c i → S) → ℝ)
    (h : ∃ p : (V → S) → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧ ∀ i, jointMarginal p (c i) = b i) :
    (∀ i, ∑ y, b i y = 1) ∧ ∀ i j, T.Adj i j →
      tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
        tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j) := by
  obtain ⟨p, -, hp1, hpb⟩ := h
  refine ⟨fun i ↦ by rw [← hpb i, sum_jointMarginal, hp1], fun i j _ ↦ ?_⟩
  rw [← hpb i, ← hpb j, tableMarginal_jointMarginal, tableMarginal_jointMarginal]

/-- GAPS 107.27, sufficiency in the marginal problem: on a junction tree, normalized nonnegative
clique tables that agree on separators are the clique marginals of the junction-tree product,
which is a probability table. -/
theorem junctionTreeProduct_isJointLaw {m : ℕ} (G : SimpleGraph V) (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) (hJ : IsJunctionTree G c T) (b : ∀ i, (c i → S) → ℝ)
    (hb : ∀ i y, 0 ≤ b i y) (hsum : ∀ i, ∑ y, b i y = 1)
    (hcons : ∀ i j, T.Adj i j →
      tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
        tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j)) :
    (∀ x, 0 ≤ junctionTreeProduct c T b x) ∧ ∑ x, junctionTreeProduct c T b x = 1 ∧
      ∀ i, jointMarginal (junctionTreeProduct c T b) (c i) = b i := by
  obtain ⟨-, -, hcov, hT, hrip⟩ := hJ
  have hcover : ∀ v, ∃ i, v ∈ c i := by
    intro v
    obtain ⟨C, hvC, hC⟩ := Finite.exists_le_maximal
      (p := fun D : Finset V ↦ G.IsClique (D : Set V)) (a := {v}) (by simp)
    obtain ⟨i, hi⟩ := hcov C hC
    exact ⟨i, hi ▸ hvC (Finset.mem_singleton_self v)⟩
  have hsymm : ∀ i j, T.Adj i j → ∀ x, jtSep c b i j x = jtSep c b j i x := by
    intro i j hij x
    have := congrFun (hcons i j hij) (fun v ↦ x v)
    rwa [tableMarginal_eq_jtSep, tableMarginal_right_eq_jtSep] at this
  have hne : Nonempty (V → S) := by
    by_cases hS : Nonempty S
    · infer_instance
    · have : IsEmpty V := ⟨fun v ↦ by
        obtain ⟨i, hi⟩ := hcover v
        have hemp : IsEmpty (c i → S) := ⟨fun y ↦ hS ⟨y ⟨v, hi⟩⟩⟩
        have := hsum i
        rw [Finset.univ_eq_empty, Finset.sum_empty] at this
        exact zero_ne_one this⟩
      infer_instance
  have hprod : ∀ r : Fin m, ∀ par : Fin m → Fin m,
      (∀ k, k ≠ r → T.Adj k (par k) ∧ T.dist r (par k) + 1 = T.dist r k) →
      ∀ x, junctionTreeProduct c T b x = jtPartial c b r par univ x := by
    intro r par hpar x
    unfold junctionTreeProduct jtPartial
    congr 1
    symm
    refine Finset.prod_bij (fun k _ ↦ if k < par k then (k, par k) else (par k, k)) ?_ ?_ ?_ ?_
    · intro k hk
      have hkr := Finset.ne_of_mem_erase hk
      have hadj := (hpar k hkr).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · exact ⟨h, hadj⟩
      · exact ⟨lt_of_le_of_ne (not_lt.mp h) hadj.ne.symm, hadj.symm⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      have h₁ := (hpar k₁ (Finset.ne_of_mem_erase hk₁)).2
      have h₂ := (hpar k₂ (Finset.ne_of_mem_erase hk₂)).2
      split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> obtain ⟨e₁, e₂⟩ := heq
      · exact e₁
      · have := congrArg (T.dist r) e₁; have := congrArg (T.dist r) e₂; omega
      · have := congrArg (T.dist r) e₁; have := congrArg (T.dist r) e₂; omega
      · exact e₂
    · rintro ⟨e₁, e₂⟩ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨hlt, hadj⟩ := he
      rcases hT.dist_eq_dist_add_one_of_adj r hadj with h | h
      · have hr : e₁ ≠ r := by rintro rfl; simp at h
        have hp := jt_eq_of_dist_add_one hT (hpar e₁ hr).1 hadj (hpar e₁ hr).2 h.symm
        refine ⟨e₁, Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
        simp [hp, hlt]
      · have hr : e₂ ≠ r := by rintro rfl; simp at h
        have hp := jt_eq_of_dist_add_one hT (hpar e₂ hr).1 hadj.symm (hpar e₂ hr).2 h.symm
        refine ⟨e₂, Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
        simp [hp, not_lt.mpr hlt.le]
    · intro k hk
      rw [tableMarginal_eq_jtSep]
      split_ifs
      · rfl
      · exact hsymm _ _ (hpar k (Finset.ne_of_mem_erase hk)).1 x
  have hmarg : ∀ r : Fin m, ∀ x : V → S,
      jointMarginal (junctionTreeProduct c T b) (c r) (fun v ↦ x v) = b r (fun v ↦ x v) := by
    intro r x
    obtain ⟨par, hpar⟩ : ∃ par : Fin m → Fin m,
        ∀ k, k ≠ r → T.Adj k (par k) ∧ T.dist r (par k) + 1 = T.dist r k := by
      choose! par hpar using fun k (hk : k ≠ r) ↦ jt_exists_parent hT r hk
      exact ⟨par, hpar⟩
    have h1 := coordSum_jtPartial c T hT hrip b hb hsymm r par hpar univ (Finset.mem_univ _)
      (fun k _ _ ↦ Finset.mem_univ _) x
    have hU : univ.biUnion c = univ := Finset.eq_univ_of_forall fun v ↦ by
      obtain ⟨i, hi⟩ := hcover v
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    rw [hU] at h1
    rw [← h1]
    unfold jointMarginal coordSum
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.filter_congr fun x' _ ↦ ?_) fun x' _ ↦ hprod r par hpar x'
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    exact ⟨fun h v hv ↦ h ⟨v, hv⟩, fun h v ↦ h v v.2⟩
  have hmarg' : ∀ i, jointMarginal (junctionTreeProduct c T b) (c i) = b i := by
    intro i
    funext y
    set x0 : V → S := fun v ↦ if h : v ∈ c i then y ⟨v, h⟩ else hne.some v
    have hy : (fun v : c i ↦ x0 v) = y := funext fun v ↦ by simp [x0, v.2]
    rw [← hy]
    exact hmarg i x0
  refine ⟨fun x ↦ ?_, ?_, hmarg'⟩
  · unfold junctionTreeProduct
    refine div_nonneg (Finset.prod_nonneg fun i _ ↦ hb _ _) (Finset.prod_nonneg fun e _ ↦ ?_)
    exact Finset.sum_nonneg fun y _ ↦ by split_ifs <;> simp [hb]
  · obtain ⟨r⟩ := hT.connected.nonempty
    rw [← sum_jointMarginal _ (c r), hmarg' r, hsum r]

/-- GAPS 107.27, marginal problem on a junction tree: nonnegative clique tables are the clique
marginals of a joint probability law exactly when every table is normalized and adjacent
tables agree on their separator; in that case the junction-tree product formula is such a law.
The uniqueness of the Markov law is not formalized here. -/
theorem exists_joint_with_clique_marginals_iff {m : ℕ}
    (G : SimpleGraph V) (c : Fin m → Finset V) (T : SimpleGraph (Fin m))
    (hJ : IsJunctionTree G c T) (b : ∀ i, (c i → S) → ℝ) (hb : ∀ i y, 0 ≤ b i y) :
    ((∃ p : (V → S) → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
        ∀ i, jointMarginal p (c i) = b i) ↔
      (∀ i, ∑ y, b i y = 1) ∧ ∀ i j, T.Adj i j →
        tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
          tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j)) ∧
    ((∀ i, ∑ y, b i y = 1) → (∀ i j, T.Adj i j →
        tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
          tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j)) →
      (∀ x, 0 ≤ junctionTreeProduct c T b x) ∧ ∑ x, junctionTreeProduct c T b x = 1 ∧
        ∀ i, jointMarginal (junctionTreeProduct c T b) (c i) = b i) := by
  have hsuff := junctionTreeProduct_isJointLaw G c T hJ b hb
  refine ⟨⟨sum_eq_one_and_tableMarginal_eq_of_jointMarginal c T b, fun h ↦ ?_⟩, hsuff⟩
  obtain ⟨h0, h1, h2⟩ := hsuff h.1 h.2
  exact ⟨_, h0, h1, h2⟩

end Marginals

end CKSD
