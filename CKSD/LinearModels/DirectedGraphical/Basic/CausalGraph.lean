module

public import CKSD.LinearModels.Basic


/-!
# Finite causal graphs and d-separation

A causal graph on a vertex type `V` is a directed acyclic graph, given by an edge relation whose
transitive closure is irreflexive. This file sets up the graph-theoretic vocabulary of directed
graphical models: parents, descendants, active paths, d-separation, Markov equivalence, skeleton
adjacency and unshielded colliders, together with the recursive product of local conditional
masses and its truncated version for interventions.

## Main definitions

* `CKSD.CausalGraph`: a directed acyclic graph.
* `CKSD.CausalGraph.IsActivePath`: a path (injective sequence of adjacent vertices) on which
  every interior collider has a descendant in the conditioning set (or lies in it) and every
  interior noncollider lies outside it.
* `CKSD.CausalGraph.DSeparated`: no active path joins the two sets.
* `CKSD.CausalGraph.MarkovEquivalent`: the two graphs have the same d-separation statements.
* `CKSD.CausalGraph.IsUnshieldedCollider`: `u → v ← w` with `u` and `w` nonadjacent.
* `CKSD.directedFactorizationMass`, `CKSD.interventionMass`: the recursive product of local
  masses and the truncated product under an intervention.

## Main results

* `CKSD.markov_equivalent_iff_skeleton_and_colliders`: the Verma–Pearl theorem, two directed
  acyclic graphs on a finite vertex set are Markov equivalent if and only if they have the same
  skeleton and the same unshielded colliders.

## Conventions

The conditions of an active path constrain only its interior vertices, and `DSeparated A B Z`
is defined for arbitrary sets, not only for pairwise disjoint ones. Hence `A` and `B` are never
d-separated when they meet (a path of length zero is active), and an endpoint lying in `Z` does
not block a path. For pairwise disjoint `A`, `B`, `Z` this is the usual d-separation. The
d-separation statements with overlapping sets reduce to disjoint ones on a larger graph: for
`a ∈ Z`, the paths from `a` that are active given `Z` in `G` are exactly the paths from `a` that
are active given `(Z \ {a}) ∪ {a'}` in the graph obtained from `G` by adding a new vertex `a'`
with the single edge `a → a'`, and adding such a child to two graphs preserves the equality of
their skeletons and of their unshielded colliders. Consequently, by the classical Verma–Pearl
theorem for disjoint triples applied to the enlarged graphs, `MarkovEquivalent`, which
quantifies over all triples, agrees with Markov equivalence in the usual sense (agreement on
pairwise disjoint triples), and `markov_equivalent_iff_skeleton_and_colliders` holds as stated.

## References

* T. Verma and J. Pearl, *Equivalence and synthesis of causal models*, UAI 1990.
* S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Finite directed acyclic causal graph; acyclicity excludes every nonempty directed cycle. -/
structure CausalGraph (V : Type*) where
  /-- Directed edge relation. -/
  edge : V → V → Prop
  /-- No nonempty directed path returns to its initial vertex. -/
  acyclic : ∀ v, ¬ Relation.TransGen edge v v

/-- Parents of a vertex in a causal graph. -/
def CausalGraph.parents {V : Type*} (G : CausalGraph V) (v : V) : Set V :=
  {u | G.edge u v}

/-- Proper descendant relation in a causal graph. -/
def CausalGraph.IsDescendant {V : Type*} (G : CausalGraph V) (u v : V) : Prop :=
  Relation.TransGen G.edge u v

/-- A path `p 0, …, p n` (pairwise distinct vertices, consecutive ones adjacent) is active given
`Z` when every interior collider `p (i-1) → p i ← p (i+1)` lies in `Z` or has a descendant in
`Z`, and every interior noncollider lies outside `Z`. The endpoints are not constrained. -/
def CausalGraph.IsActivePath {V : Type*} (G : CausalGraph V) (Z : Set V)
    {n : ℕ} (p : Fin (n + 1) → V) : Prop :=
  Function.Injective p ∧
    (∀ i : Fin n, G.edge (p i.castSucc) (p i.succ) ∨ G.edge (p i.succ) (p i.castSucc)) ∧
    ∀ i : Fin (n - 1),
      let a : Fin (n + 1) := ⟨i.val, by omega⟩;
      let b : Fin (n + 1) := ⟨i.val + 1, by omega⟩;
      let c : Fin (n + 1) := ⟨i.val + 2, by omega⟩;
      if G.edge (p a) (p b) ∧ G.edge (p c) (p b)
      then ∃ z ∈ Z, z = p b ∨ G.IsDescendant (p b) z
      else p b ∉ Z

/-- `Z` d-separates `A` from `B` when no path from a vertex of `A` to a vertex of `B` is active
given `Z`. The sets need not be disjoint; see the module docstring for the resulting
conventions (`A ∩ B ≠ ∅` excludes d-separation, endpoints in `Z` do not block). -/
def CausalGraph.DSeparated {V : Type*} (G : CausalGraph V) (A B Z : Set V) : Prop :=
  ∀ n : ℕ, ∀ p : Fin (n + 1) → V, p 0 ∈ A → p (Fin.last n) ∈ B → ¬ G.IsActivePath Z p

/-- Two causal graphs are Markov equivalent if all their d-separation statements agree. The
quantification is over all triples of vertex sets; by the reduction described in the module
docstring this is equivalent to agreement on pairwise disjoint triples. -/
def CausalGraph.MarkovEquivalent {V : Type*} (G H : CausalGraph V) : Prop :=
  ∀ A B Z, G.DSeparated A B Z ↔ H.DSeparated A B Z

/-- Undirected skeleton adjacency. -/
def CausalGraph.Adjacent {V : Type*} (G : CausalGraph V) (u v : V) : Prop :=
  G.edge u v ∨ G.edge v u

/-- An unshielded collider is an inward-facing triple with nonadjacent endpoints. -/
def CausalGraph.IsUnshieldedCollider {V : Type*} (G : CausalGraph V) (u v w : V) : Prop :=
  u ≠ w ∧ G.edge u v ∧ G.edge w v ∧ ¬ G.Adjacent u w

/-- Local mass functions respect the parents of `G`: the local mass of `v` depends on the
configuration only through its values at the parents of `v`. -/
def CausalGraph.RespectsParents {V S : Type*} (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) : Prop :=
  ∀ v x y, (∀ u ∈ G.parents v, x u = y u) → localMass v x = localMass v y

/-- Recursive product mass `∏_v k_v(x_v | x)` from local conditional masses `k_v`. -/
def directedFactorizationMass {V S : Type*} [Fintype V]
    (localMass : V → (V → S) → S → ℝ) (x : V → S) : ℝ :=
  ∏ v, localMass v x (x v)

/-- Truncated factorization for the intervention `do(X_A = a_A)`: zero unless `x` agrees with
`a` on `A`, and otherwise the product of the local masses over the vertices outside `A`. -/
def interventionMass {V S : Type*} [Fintype V] [DecidableEq V] [DecidableEq S]
    (localMass : V → (V → S) → S → ℝ) (A : Finset V) (a x : V → S) : ℝ :=
  if ∀ v ∈ A, x v = a v then ∏ v ∈ Aᶜ, localMass v x (x v) else 0

/-- GAPS 105.67 (Verma–Pearl): two directed acyclic graphs on a finite vertex set are Markov
equivalent if and only if they have the same skeleton (adjacency relation) and the same
unshielded colliders. -/
theorem markov_equivalent_iff_skeleton_and_colliders {V : Type*} [Fintype V]
    (G H : CausalGraph V) :
    G.MarkovEquivalent H ↔
      (∀ u v, G.Adjacent u v ↔ H.Adjacent u v) ∧
        ∀ u v w, G.IsUnshieldedCollider u v w ↔ H.IsUnshieldedCollider u v w := by
  sorry

/-- Graphical Markov equivalence is reflexive. -/
theorem CausalGraph.markov_equivalent_refl {V : Type*} (G : CausalGraph V) :
    G.MarkovEquivalent G := fun _ _ _ ↦ Iff.rfl

end CKSD
