module

public import CKSD.Learning.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Pairwise graphical models and belief propagation

The vertex set `V` and the state alphabet `S` are finite types. Finite state spaces retain all
normalization constants. Edges are counted once using a linear order on `V`; messages use both
orientations. Local consistency and Bethe stationarity are explicit finite-dimensional
conditions, and no convergence or exactness property enters their definitions. The graph API is
Mathlib's `SimpleGraph`.

## Main definitions

* `CKSD.PairwiseGraphicalModel`: a positive pairwise model, with its weights, partition function
  and normalized masses.
* `CKSD.IsLocallyConsistentBelief`, `CKSD.betheFreeEnergy`, `CKSD.IsBetheStationary`: the local
  polytope and the Bethe variational problem.
* `CKSD.IsBeliefPropagationFixedPoint`, `CKSD.beliefPropagationNode`,
  `CKSD.beliefPropagationEdge`: belief propagation and its beliefs.

## Main results

* `CKSD.isBetheStationary_iff_exists_beliefPropagationFixedPoint`: Bethe stationary points are
  BP beliefs (GAPS 107.19).
* `CKSD.exists_beliefPropagation_exact_on_tree`,
  `CKSD.beliefPropagation_tree_unique_up_to_scale`: exactness and uniqueness of BP on trees
  (GAPS 107.23).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A positive pairwise model on a finite graph with a common finite state alphabet. -/
structure PairwiseGraphicalModel (V S : Type*) where
  /-- Underlying undirected graph. -/
  graph : SimpleGraph (V)
  /-- Vertex potentials. -/
  vertexPotential : V → S → ℝ
  /-- Edge potentials, represented in both orientations. -/
  edgePotential : V → V → S → S → ℝ
  /-- Vertex potentials are strictly positive. -/
  vertexPotential_pos : ∀ i a, 0 < vertexPotential i a
  /-- Edge potentials are strictly positive on edges. -/
  edgePotential_pos : ∀ i j, graph.Adj i j → ∀ a b, 0 < edgePotential i j a b
  /-- Changing edge orientation exchanges the endpoint states. -/
  edgePotential_symm : ∀ i j a b, edgePotential i j a b = edgePotential j i b a

variable {V S : Type*} [Fintype V] [LinearOrder V] [Fintype S]

/-- The oriented edge set with the smaller vertex listed first. -/
def PairwiseGraphicalModel.orderedEdges (M : PairwiseGraphicalModel V S) :
    Finset (V × V) := Finset.univ.filter fun e ↦ e.1 < e.2 ∧ M.graph.Adj e.1 e.2

/-- Unnormalized configuration weight. -/
def PairwiseGraphicalModel.weight (M : PairwiseGraphicalModel V S)
    (x : V → S) : ℝ :=
  (∏ i, M.vertexPotential i (x i)) *
    ∏ e ∈ M.orderedEdges, M.edgePotential e.1 e.2 (x e.1) (x e.2)

/-- Partition function of a finite pairwise model. -/
def PairwiseGraphicalModel.partitionFunction (M : PairwiseGraphicalModel V S) : ℝ :=
  ∑ x : V → S, M.weight x

/-- Normalized configuration mass. -/
def PairwiseGraphicalModel.mass (M : PairwiseGraphicalModel V S)
    (x : V → S) : ℝ := M.weight x / M.partitionFunction

/-- Arrays of node and oriented-edge beliefs. Nonedges are unused coordinates. -/
abbrev LocalBeliefTables (V S : Type*) :=
  (V → S → ℝ) × (V → V → S → S → ℝ)

/-- The local polytope of a finite pairwise model. -/
def IsLocallyConsistentBelief (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) : Prop :=
  (∀ i a, 0 ≤ B.1 i a) ∧ (∀ i, ∑ a, B.1 i a = 1) ∧
    ∀ i j, M.graph.Adj i j →
      (∀ a b, 0 ≤ B.2 i j a b) ∧
      (∀ a, ∑ b, B.2 i j a b = B.1 i a) ∧
      (∀ b, ∑ a, B.2 i j a b = B.1 j b) ∧
      ∀ a b, B.2 i j a b = B.2 j i b a

/-- Strict positivity in the coordinates constrained by the local polytope. -/
def IsInteriorLocalBelief (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) : Prop :=
  IsLocallyConsistentBelief M B ∧ (∀ i a, 0 < B.1 i a) ∧
    ∀ i j, M.graph.Adj i j → ∀ a b, 0 < B.2 i j a b

/-- Homogeneous local-polytope constraints describing its tangent directions. -/
def IsLocalBeliefDirection (M : PairwiseGraphicalModel V S)
    (D : LocalBeliefTables V S) : Prop :=
  (∀ i, ∑ a, D.1 i a = 0) ∧ ∀ i j, M.graph.Adj i j →
    (∀ a, ∑ b, D.2 i j a b = D.1 i a) ∧
    (∀ b, ∑ a, D.2 i j a b = D.1 j b) ∧
    ∀ a b, D.2 i j a b = D.2 j i b a

/-- Shannon entropy `∑ᵢ -pᵢ log pᵢ` of a real table, with `0 log 0 = 0` (Mathlib's
`Real.negMulLog`). -/
def finiteTableEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Bethe entropy of local node and edge tables. -/
def betheEntropy (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) : ℝ :=
  (∑ e ∈ M.orderedEdges, finiteTableEntropy (fun z : S × S ↦ B.2 e.1 e.2 z.1 z.2)) -
    ∑ i, ((M.graph.neighborFinset i).card - (1 : ℝ)) * finiteTableEntropy (B.1 i)

/-- Bethe free energy, including the vertex and edge potential terms. -/
def betheFreeEnergy (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) : ℝ :=
  -(∑ i, ∑ a, B.1 i a * Real.log (M.vertexPotential i a)) -
    (∑ e ∈ M.orderedEdges, ∑ a, ∑ b,
      B.2 e.1 e.2 a b * Real.log (M.edgePotential e.1 e.2 a b)) - betheEntropy M B

/-- Stationarity of the Bethe energy along every direction preserving the local constraints. -/
def IsBetheStationary (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) : Prop :=
  ∀ D, IsLocalBeliefDirection M D →
    HasDerivAt (fun t : ℝ ↦ betheFreeEnergy M (B + t • D)) 0 0

/-- Product of incoming messages at `i`, omitting the possible recipient `j`. -/
def incomingMessageProduct (M : PairwiseGraphicalModel V S)
    (m : V → V → S → ℝ) (i j : V) (a : S) : ℝ :=
  ∏ k ∈ (M.graph.neighborFinset i).erase j, m k i a

/-- Belief-propagation fixed-point equations, allowing one positive scale for each message. -/
def IsBeliefPropagationFixedPoint (M : PairwiseGraphicalModel V S)
    (m : V → V → S → ℝ) : Prop :=
  (∀ i j, M.graph.Adj i j → ∀ a, 0 < m i j a) ∧
    ∀ i j, M.graph.Adj i j → ∃ c > 0, ∀ b,
      m i j b = c * ∑ a, M.vertexPotential i a * M.edgePotential i j a b *
        incomingMessageProduct M m i j a

/-- Normalized node belief induced by incoming messages. -/
def beliefPropagationNode (M : PairwiseGraphicalModel V S)
    (m : V → V → S → ℝ) (i : V) (a : S) : ℝ :=
  let w := fun a ↦ M.vertexPotential i a * ∏ k ∈ M.graph.neighborFinset i, m k i a
  w a / ∑ b, w b

/-- Normalized edge belief induced by messages entering its endpoints. -/
def beliefPropagationEdge (M : PairwiseGraphicalModel V S)
    (m : V → V → S → ℝ) (i j : V) (a b : S) : ℝ :=
  let w := fun a b ↦ M.vertexPotential i a * M.vertexPotential j b *
    M.edgePotential i j a b * incomingMessageProduct M m i j a *
      incomingMessageProduct M m j i b
  w a b / ∑ z : S × S, w z.1 z.2

/-- GAPS 107.19: Bethe stationary points in the positive local polytope are exactly BP beliefs. -/
theorem isBetheStationary_iff_exists_beliefPropagationFixedPoint
    (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) :
    IsBetheStationary M B ↔ ∃ m, IsBeliefPropagationFixedPoint M m ∧
      (∀ i a, B.1 i a = beliefPropagationNode M m i a) ∧
      ∀ i j, M.graph.Adj i j → ∀ a b, B.2 i j a b = beliefPropagationEdge M m i j a b := by
  sorry

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
  sorry

/-- GAPS 107.23: each directed-edge message in a positive tree model is unique up to positive
scale. -/
theorem beliefPropagation_tree_unique_up_to_scale (M : PairwiseGraphicalModel V S)
    (htree : M.graph.IsTree)
    (m m' : V → V → S → ℝ)
    (hm : IsBeliefPropagationFixedPoint M m) (hm' : IsBeliefPropagationFixedPoint M m') :
    ∀ i j, M.graph.Adj i j → ∃ c > 0, ∀ a, m' i j a = c * m i j a := by
  sorry

omit [Fintype S] in
/-- Every finite positive graphical-model configuration has positive weight. -/
theorem PairwiseGraphicalModel.weight_pos (M : PairwiseGraphicalModel V S)
    (x : V → S) : 0 < M.weight x := by
  unfold weight
  apply mul_pos
  · exact Finset.prod_pos fun i _ ↦ M.vertexPotential_pos i (x i)
  · apply Finset.prod_pos
    intro e he
    exact M.edgePotential_pos e.1 e.2 (Finset.mem_filter.mp he).2.2 (x e.1) (x e.2)

end CKSD
