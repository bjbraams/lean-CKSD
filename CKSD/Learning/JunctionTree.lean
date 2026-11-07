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

Source: GAPS 107.27. Graphs, walks, paths, cliques, and trees are Mathlib's `SimpleGraph` API.
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

/-- A finite set of vertices is a maximal clique. -/
def IsMaximalCliqueFinset {V : Type*} (G : SimpleGraph V) (C : Finset V) : Prop :=
  G.IsClique (C : Set V) ∧ ∀ D : Finset V, G.IsClique (D : Set V) → C ⊆ D → D = C

/-- `T` on the enumeration `c` of cliques is a junction tree of `G`: `c` lists every maximal
clique exactly once, `T` is a tree, and every clique on the path between two cliques contains
their intersection. -/
def IsJunctionTree {V : Type*} (G : SimpleGraph V) {m : ℕ} (c : Fin m → Finset V)
    (T : SimpleGraph (Fin m)) : Prop :=
  Function.Injective c ∧ (∀ i, IsMaximalCliqueFinset G (c i)) ∧
    (∀ C, IsMaximalCliqueFinset G C → ∃ i, c i = C) ∧ T.IsTree ∧
    ∀ i j (p : T.Walk i j), p.IsPath → ∀ k ∈ p.support, c i ∩ c j ⊆ c k

/-- A graph has a junction tree. -/
def HasJunctionTree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (c : Fin m → Finset V) (T : SimpleGraph (Fin m)), IsJunctionTree G c T

/-- GAPS 107.27: a finite graph has a junction tree if and only if it is triangulated. -/
theorem hasJunctionTree_iff_isTriangulated {V : Type*} [Fintype V] (G : SimpleGraph V) :
    HasJunctionTree G ↔ IsTriangulatedGraph G := by
  sorry

/-- Marginal table of a joint configuration mass on a finite set of vertices. -/
def jointMarginal {V : Type*} [Fintype V] {q : ℕ} (p : (V → Fin q) → ℝ) (C : Finset V)
    (y : C → Fin q) : ℝ :=
  ∑ x : V → Fin q, if ∀ v : C, x v = y v then p x else 0

/-- Marginal of a table on `C` to the subset `S`, given by its membership proof. -/
def tableMarginal {V : Type*} {q : ℕ} {C S : Finset V} (hS : S ⊆ C) (b : (C → Fin q) → ℝ)
    (z : S → Fin q) : ℝ :=
  ∑ y : C → Fin q, if ∀ v : S, y ⟨v, hS v.2⟩ = z v then b y else 0

/-- Junction-tree product formula: clique tables divided by separator tables, one separator
factor per tree edge, the separator table being the marginal of the lower-indexed clique. -/
def junctionTreeProduct {V : Type*} {q m : ℕ} (c : Fin m → Finset V) (T : SimpleGraph (Fin m))
    (b : ∀ i, (c i → Fin q) → ℝ) (x : V → Fin q) : ℝ :=
  (∏ i, b i fun v ↦ x v) /
    ∏ e ∈ univ.filter (fun e : Fin m × Fin m ↦ e.1 < e.2 ∧ T.Adj e.1 e.2),
      tableMarginal (inter_subset_left (s₁ := c e.1) (s₂ := c e.2)) (b e.1) fun v ↦ x v

/-- GAPS 107.27, marginal problem on a junction tree: nonnegative clique tables are the clique
marginals of a joint probability law exactly when every table is normalized and adjacent
tables agree on their separator; in that case the junction-tree product formula is such a law.
The uniqueness of the Markov law is not formalized here. -/
theorem exists_joint_with_clique_marginals_iff {V : Type*} [Fintype V] {q m : ℕ}
    (G : SimpleGraph V) (c : Fin m → Finset V) (T : SimpleGraph (Fin m))
    (hJ : IsJunctionTree G c T) (b : ∀ i, (c i → Fin q) → ℝ) (hb : ∀ i y, 0 ≤ b i y) :
    ((∃ p : (V → Fin q) → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
        ∀ i, jointMarginal p (c i) = b i) ↔
      (∀ i, ∑ y, b i y = 1) ∧ ∀ i j, T.Adj i j →
        tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
          tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j)) ∧
    ((∀ i, ∑ y, b i y = 1) → (∀ i j, T.Adj i j →
        tableMarginal (inter_subset_left (s₁ := c i) (s₂ := c j)) (b i) =
          tableMarginal (inter_subset_right (s₁ := c i) (s₂ := c j)) (b j)) →
      (∀ x, 0 ≤ junctionTreeProduct c T b x) ∧ ∑ x, junctionTreeProduct c T b x = 1 ∧
        ∀ i, jointMarginal (junctionTreeProduct c T b) (c i) = b i) := by
  sorry

end CKSD
