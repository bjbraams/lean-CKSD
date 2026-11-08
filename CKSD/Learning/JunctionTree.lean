module

public import CKSD.Learning.Basic
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
    HasJunctionTree G ↔ IsTriangulatedGraph G := by
  sorry

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
  sorry

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
