module

public import CKSD.Learning.Basic
public import CKSD.Learning.CoordinateSum
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

Exactness and uniqueness of belief propagation on trees are in
`CKSD.Learning.BeliefPropagationTree`.
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

/-- The partial derivative of the Bethe free energy in an edge coordinate. -/
private def betheEdgeGrad (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (i j : V) (a b : S) : ℝ :=
  Real.log (B.2 i j a b) - Real.log (M.edgePotential i j a b) + 1

/-- The partial derivative of the Bethe free energy in a node coordinate. -/
private def betheNodeGrad (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (i : V) (a : S) : ℝ :=
  -Real.log (M.vertexPotential i a) -
    ((M.graph.neighborFinset i).card - (1 : ℝ)) * (Real.log (B.1 i a) + 1)

/-- The directional derivative of the Bethe free energy. -/
private def betheDirDeriv (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (D : LocalBeliefTables V S) : ℝ :=
  ∑ i, ∑ a, betheNodeGrad M B i a * D.1 i a +
    ∑ e ∈ M.orderedEdges, ∑ a, ∑ b, betheEdgeGrad M B e.1 e.2 a b * D.2 e.1 e.2 a b

/-- Derivative of `t ↦ negMulLog (x + t d)` at `0`, for `x ≠ 0`. -/
private theorem hasDerivAt_negMulLog_affine {x : ℝ} (hx : x ≠ 0) (d : ℝ) :
    HasDerivAt (fun t ↦ Real.negMulLog (x + t * d)) ((-Real.log x - 1) * d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ ↦ x + t * d) d 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add x
    rwa [one_mul] at this
  have h2 : HasDerivAt Real.negMulLog (-Real.log x - 1) (x + 0 * d) := by
    rw [zero_mul, add_zero]; exact Real.hasDerivAt_negMulLog hx
  exact h2.comp (0 : ℝ) h1

/-- Derivative of `t ↦ (x + t d) c` at `0`. -/
private theorem hasDerivAt_affine_mul (x d c : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (x + t * d) * c) (d * c) 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).mul_const d).const_add x).mul_const c
  rwa [one_mul] at this

/-- At an interior point of the local polytope, the Bethe free energy is differentiable along
every line, with derivative given by the node and edge gradients. -/
private theorem hasDerivAt_betheFreeEnergy (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) (hB : IsInteriorLocalBelief M B) (D : LocalBeliefTables V S) :
    HasDerivAt (fun t : ℝ ↦ betheFreeEnergy M (B + t • D)) (betheDirDeriv M B D) 0 := by
  unfold betheFreeEnergy betheEntropy finiteTableEntropy
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hE : ∀ e ∈ M.orderedEdges, M.graph.Adj e.1 e.2 := fun e he ↦ (Finset.mem_filter.mp he).2.2
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦
      hasDerivAt_affine_mul (B.1 i a) (D.1 i a) (Real.log (M.vertexPotential i a))
  have h2 := HasDerivAt.fun_sum (u := M.orderedEdges) fun (e : V × V) _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦
      HasDerivAt.fun_sum (u := Finset.univ) fun b _ ↦
        hasDerivAt_affine_mul (B.2 e.1 e.2 a b) (D.2 e.1 e.2 a b)
          (Real.log (M.edgePotential e.1 e.2 a b))
  have h3 := HasDerivAt.fun_sum (u := M.orderedEdges) fun (e : V × V) he ↦
    HasDerivAt.fun_sum (u := Finset.univ) fun (z : S × S) _ ↦
      hasDerivAt_negMulLog_affine (hB.2.2 _ _ (hE e he) z.1 z.2).ne' (D.2 e.1 e.2 z.1 z.2)
  have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    (HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦
      hasDerivAt_negMulLog_affine (hB.2.1 i a).ne' (D.1 i a)).const_mul
        ((M.graph.neighborFinset i).card - (1 : ℝ))
  have h := (h1.neg.sub h2).sub (h3.sub h4)
  convert h using 1
  unfold betheDirDeriv betheNodeGrad betheEdgeGrad
  simp only [Fintype.sum_prod_type]
  have h1 : ∑ i, ∑ a, (-Real.log (M.vertexPotential i a) - ((M.graph.neighborFinset i).card -
      (1 : ℝ)) * (Real.log (B.1 i a) + 1)) * D.1 i a =
      -∑ i, ∑ a, D.1 i a * Real.log (M.vertexPotential i a) + ∑ i,
        ((M.graph.neighborFinset i).card - (1 : ℝ)) * ∑ a, (-Real.log (B.1 i a) - 1) * D.1 i a := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have h2 : ∑ e ∈ M.orderedEdges, ∑ a, ∑ b, (Real.log (B.2 e.1 e.2 a b) -
      Real.log (M.edgePotential e.1 e.2 a b) + 1) * D.2 e.1 e.2 a b =
      -∑ e ∈ M.orderedEdges, ∑ a, ∑ b, D.2 e.1 e.2 a b * Real.log (M.edgePotential e.1 e.2 a b) -
        ∑ e ∈ M.orderedEdges, ∑ a, ∑ b, (-Real.log (B.2 e.1 e.2 a b) - 1) * D.2 e.1 e.2 a b := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  rw [h1, h2]
  ring

omit [Fintype S] in
/-- Summing over the edges counted once is half the sum over both orientations, for a function
that is symmetric on edges. -/
private theorem sum_orderedEdges_eq_half (M : PairwiseGraphicalModel V S) (Φ : V → V → ℝ)
    (hΦ : ∀ i j, M.graph.Adj i j → Φ i j = Φ j i) :
    ∑ e ∈ M.orderedEdges, Φ e.1 e.2 =
      (1 / 2) * ∑ i, ∑ j ∈ M.graph.neighborFinset i, Φ i j := by
  have hN : ∑ i, ∑ j ∈ M.graph.neighborFinset i, Φ i j =
      ∑ p : V × V, if M.graph.Adj p.1 p.2 then Φ p.1 p.2 else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hsplit : ∀ p : V × V, (if M.graph.Adj p.1 p.2 then Φ p.1 p.2 else 0) =
      (if p.1 < p.2 ∧ M.graph.Adj p.1 p.2 then Φ p.1 p.2 else 0) +
        (if p.2 < p.1 ∧ M.graph.Adj p.2 p.1 then Φ p.2 p.1 else 0) := by
    intro p
    by_cases h : M.graph.Adj p.1 p.2
    · rcases lt_trichotomy p.1 p.2 with h' | h' | h'
      · simp [h, h', not_lt.mpr h'.le]
      · exact absurd h' h.ne
      · simp [h, h', not_lt.mpr h'.le, h.symm, hΦ _ _ h]
    · have h2 : ¬ M.graph.Adj p.2 p.1 := fun h' ↦ h h'.symm
      simp [h, h2]
  have hswap : ∑ p : V × V, (if p.2 < p.1 ∧ M.graph.Adj p.2 p.1 then Φ p.2 p.1 else 0) =
      ∑ p : V × V, (if p.1 < p.2 ∧ M.graph.Adj p.1 p.2 then Φ p.1 p.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm V V) _ _ fun p ↦ rfl
  have hE : ∑ e ∈ M.orderedEdges, Φ e.1 e.2 =
      ∑ p : V × V, (if p.1 < p.2 ∧ M.graph.Adj p.1 p.2 then Φ p.1 p.2 else 0) := by
    unfold PairwiseGraphicalModel.orderedEdges
    rw [Finset.sum_filter]
  rw [hN, Finset.sum_congr rfl fun p _ ↦ hsplit p, Finset.sum_add_distrib, hswap, hE]
  ring

omit [LinearOrder V] [Fintype S] in
/-- Exchanging the roles of the two endpoints in a sum over oriented edges. -/
private theorem sum_neighborFinset_swap (M : PairwiseGraphicalModel V S) (Φ : V → V → ℝ) :
    ∑ i, ∑ j ∈ M.graph.neighborFinset i, Φ j i = ∑ i, ∑ j ∈ M.graph.neighborFinset i, Φ i j := by
  have h : ∀ Ψ : V → V → ℝ, ∑ i, ∑ j ∈ M.graph.neighborFinset i, Ψ i j =
      ∑ p : V × V, if M.graph.Adj p.1 p.2 then Ψ p.1 p.2 else 0 := by
    intro Ψ
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  rw [h (fun i j ↦ Φ j i), h]
  exact Fintype.sum_equiv (Equiv.prodComm V V) _ _ fun p ↦ by
    simp [M.graph.adj_comm]

omit [Fintype V] [LinearOrder V] in
/-- Edge gradients are symmetric under reversing the edge. -/
private theorem betheEdgeGrad_symm (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) {i j : V} (h : M.graph.Adj i j) (a b : S) :
    betheEdgeGrad M B j i b a = betheEdgeGrad M B i j a b := by
  unfold betheEdgeGrad
  rw [← (hB.1.2.2 i j h).2.2.2 a b, ← M.edgePotential_symm i j a b]

/-- The directional derivative of the Bethe free energy along a direction that is symmetric on
edges, written with both orientations of each edge. -/
private theorem betheDirDeriv_eq (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) (D : LocalBeliefTables V S)
    (hD : ∀ i j, M.graph.Adj i j → ∀ a b, D.2 i j a b = D.2 j i b a) :
    betheDirDeriv M B D = ∑ i, ∑ a, betheNodeGrad M B i a * D.1 i a +
      (1 / 2) * ∑ i, ∑ j ∈ M.graph.neighborFinset i, ∑ a, ∑ b,
        betheEdgeGrad M B i j a b * D.2 i j a b := by
  unfold betheDirDeriv
  congr 1
  refine sum_orderedEdges_eq_half M (fun i j ↦ ∑ a, ∑ b, betheEdgeGrad M B i j a b * D.2 i j a b)
    fun i j h ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  rw [betheEdgeGrad_symm M B hB h a b, ← hD i j h a b]

/-- The directional derivative along a symmetrized rank-one direction on the edges. -/
private theorem betheDirDeriv_test (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) (D₁ : V → S → ℝ) (c : V → V → ℝ) (f g : S → ℝ) :
    betheDirDeriv M B (D₁, fun k l x y ↦ c k l * f x * g y + c l k * g x * f y) =
      ∑ i, ∑ a, betheNodeGrad M B i a * D₁ i a + ∑ i, ∑ j ∈ M.graph.neighborFinset i,
        c i j * ∑ x, ∑ y, betheEdgeGrad M B i j x y * (f x * g y) := by
  rw [betheDirDeriv_eq M B hB _ fun i j _ a b ↦ by simp only; ring]
  congr 1
  set Ψ : V → V → ℝ := fun i j ↦ c i j * ∑ x, ∑ y, betheEdgeGrad M B i j x y * (f x * g y)
  have h : ∀ i, ∀ j ∈ M.graph.neighborFinset i, ∑ x, ∑ y, betheEdgeGrad M B i j x y *
      (c i j * f x * g y + c j i * g x * f y) = Ψ i j + Ψ j i := by
    intro i j hj
    have hij : M.graph.Adj i j := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
    simp only [Ψ, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
      rw [betheEdgeGrad_symm M B hB hij]
      ring
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl (h i), Finset.sum_congr rfl
    fun i _ ↦ Finset.sum_add_distrib, Finset.sum_add_distrib, sum_neighborFinset_swap]
  ring

omit [Fintype V] [LinearOrder V] in
/-- Symmetrized rank-one directions satisfy the homogeneous local constraints. -/
private theorem isLocalBeliefDirection_test (M : PairwiseGraphicalModel V S)
    (D₁ : V → S → ℝ) (c : V → V → ℝ) (f g : S → ℝ) (hD₁ : ∀ i, ∑ a, D₁ i a = 0)
    (hf : ∑ x, f x = 0) (hc : ∀ k l, M.graph.Adj k l → ∀ x, D₁ k x = c k l * f x * ∑ y, g y) :
    IsLocalBeliefDirection M (D₁, fun k l x y ↦ c k l * f x * g y + c l k * g x * f y) := by
  refine ⟨hD₁, fun k l hkl ↦ ⟨fun x ↦ ?_, fun y ↦ ?_, fun x y ↦ by ring⟩⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hf, mul_zero, add_zero]
    exact (hc k l hkl x).symm
  · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, hf]
    show _ = D₁ l y
    rw [hc l k hkl.symm y]
    ring

/-- At a Bethe stationary point the directional derivative vanishes along every admissible
direction. -/
private theorem betheDirDeriv_eq_zero (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B) (D : LocalBeliefTables V S)
    (hD : IsLocalBeliefDirection M D) : betheDirDeriv M B D = 0 :=
  (hasDerivAt_betheFreeEnergy M B hB D).unique (hstat D hD)

/-- The ratio of an edge belief to the edge potential. -/
private def betheRatio (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (i j : V) (a b : S) : ℝ :=
  B.2 i j a b / M.edgePotential i j a b

omit [Fintype V] [LinearOrder V] in
/-- Edge ratios are positive at interior beliefs. -/
private theorem betheRatio_pos (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) {i j : V} (h : M.graph.Adj i j) (a b : S) :
    0 < betheRatio M B i j a b :=
  div_pos (hB.2.2 i j h a b) (M.edgePotential_pos i j h a b)

omit [Fintype V] [LinearOrder V] in
/-- Edge ratios are symmetric under reversing the edge. -/
private theorem betheRatio_symm (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) {i j : V} (h : M.graph.Adj i j) (a b : S) :
    betheRatio M B j i b a = betheRatio M B i j a b := by
  unfold betheRatio
  rw [← (hB.1.2.2 i j h).2.2.2 a b, ← M.edgePotential_symm i j a b]

omit [Fintype V] [LinearOrder V] in
/-- The edge gradient is the logarithm of the edge ratio plus one. -/
private theorem betheEdgeGrad_eq (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) {i j : V} (h : M.graph.Adj i j) (a b : S) :
    betheEdgeGrad M B i j a b = Real.log (betheRatio M B i j a b) + 1 := by
  unfold betheEdgeGrad betheRatio
  rw [Real.log_div (hB.2.2 i j h a b).ne' (M.edgePotential_pos i j h a b).ne']

/-- At a Bethe stationary point each edge belief is the edge potential times a product of
functions of the two endpoint states. -/
private theorem betheRatio_mul_of_stationary (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B)
    {i j : V} (h : M.graph.Adj i j) (s₀ a b : S) :
    betheRatio M B i j a b * betheRatio M B i j s₀ s₀ =
      betheRatio M B i j a s₀ * betheRatio M B i j s₀ b := by
  have h0 := betheDirDeriv_eq_zero M B hB hstat _ (isLocalBeliefDirection_test M
    (fun _ _ ↦ 0) (fun k l ↦ if k = i ∧ l = j then 1 else 0)
    (fun x ↦ (if x = a then 1 else 0) - if x = s₀ then 1 else 0)
    (fun y ↦ (if y = b then 1 else 0) - if y = s₀ then 1 else 0) (fun _ ↦ by simp)
    (by simp [Finset.sum_sub_distrib]) (fun k l _ x ↦ by simp [Finset.sum_sub_distrib]))
  rw [betheDirDeriv_test M B hB] at h0
  simp [ite_and, mul_sub, Finset.sum_sub_distrib, h] at h0
  simp only [betheEdgeGrad_eq M B hB h] at h0
  have hR := betheRatio_pos M B hB h
  rw [← Real.exp_log (mul_pos (hR a b) (hR s₀ s₀)), ← Real.exp_log (mul_pos (hR a s₀) (hR s₀ b)),
    Real.log_mul (hR a b).ne' (hR s₀ s₀).ne', Real.log_mul (hR a s₀).ne' (hR s₀ b).ne']
  congr 1
  linarith

/-- At a Bethe stationary point the node gradient plus the edge ratios at a reference state does
not depend on the node state. -/
private theorem betheNodeGrad_add_of_stationary (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B)
    (i : V) (s₀ a : S) :
    betheNodeGrad M B i a + ∑ j ∈ M.graph.neighborFinset i, Real.log (betheRatio M B i j a s₀) =
      betheNodeGrad M B i s₀ +
        ∑ j ∈ M.graph.neighborFinset i, Real.log (betheRatio M B i j s₀ s₀) := by
  have h0 := betheDirDeriv_eq_zero M B hB hstat _ (isLocalBeliefDirection_test M
    (fun k x ↦ if k = i then (if x = a then 1 else 0) - (if x = s₀ then 1 else 0) else 0)
    (fun k _ ↦ if k = i then 1 else 0)
    (fun x ↦ (if x = a then 1 else 0) - if x = s₀ then 1 else 0)
    (fun y ↦ if y = s₀ then 1 else 0) (fun k ↦ by split_ifs <;> simp [Finset.sum_sub_distrib])
    (by simp [Finset.sum_sub_distrib]) (fun k l _ x ↦ by split_ifs <;> simp))
  rw [betheDirDeriv_test M B hB] at h0
  simp [mul_sub, Finset.sum_sub_distrib] at h0
  have hG : ∀ s, ∑ j ∈ M.graph.neighborFinset i, betheEdgeGrad M B i j s s₀ =
      ∑ j ∈ M.graph.neighborFinset i, Real.log (betheRatio M B i j s s₀) +
        (M.graph.neighborFinset i).card := by
    intro s
    rw [Finset.sum_congr rfl fun j hj ↦ betheEdgeGrad_eq M B hB
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hj) s s₀, Finset.sum_add_distrib]
    simp
  rw [hG, hG] at h0
  linarith

/-- The messages reconstructed from Bethe beliefs, with reference state `s₀`: the node belief at
the recipient divided by the edge ratio at `s₀`. -/
private def betheMessage (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S) (s₀ : S)
    (k i : V) (a : S) : ℝ :=
  B.1 i a / betheRatio M B i k a s₀

/-- The logarithmic normalizing constant of the reconstructed node belief at `i`. -/
private def betheNodeConst (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (s₀ : S) (i : V) : ℝ :=
  -(betheNodeGrad M B i s₀ +
    ∑ j ∈ M.graph.neighborFinset i, Real.log (betheRatio M B i j s₀ s₀)) -
      ((M.graph.neighborFinset i).card - (1 : ℝ))

/-- At a Bethe stationary point the reconstructed messages give the node beliefs up to a
positive factor. -/
private theorem betheMessage_node (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B) (s₀ : S) (i : V) (a : S) :
    M.vertexPotential i a * ∏ k ∈ M.graph.neighborFinset i, betheMessage M B s₀ k i a =
      Real.exp (betheNodeConst M B s₀ i) * B.1 i a := by
  have hadj : ∀ k ∈ M.graph.neighborFinset i, M.graph.Adj i k := fun k hk ↦
    (SimpleGraph.mem_neighborFinset _ _ _).mp hk
  have hb := hB.2.1 i a
  have hm : ∀ k ∈ M.graph.neighborFinset i, 0 < betheMessage M B s₀ k i a := fun k hk ↦
    div_pos hb (betheRatio_pos M B hB (hadj k hk) a s₀)
  have hψ := M.vertexPotential_pos i a
  rw [← Real.exp_log (mul_pos hψ (Finset.prod_pos hm)), ← Real.exp_log hb, ← Real.exp_add,
    Real.log_mul hψ.ne' (Finset.prod_pos hm).ne', Real.log_prod fun k hk ↦ (hm k hk).ne']
  congr 1
  unfold betheMessage
  rw [Finset.sum_congr rfl fun k hk ↦ Real.log_div hb.ne'
    (betheRatio_pos M B hB (hadj k hk) a s₀).ne', Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have hn := betheNodeGrad_add_of_stationary M B hB hstat i s₀ a
  unfold betheNodeConst
  unfold betheNodeGrad at hn ⊢
  linear_combination (-1 : ℝ) * hn

/-- At a Bethe stationary point, the vertex potential times the messages entering `i` from
neighbours other than `j` is proportional to the edge ratio at the reference state. -/
private theorem betheMessage_incoming (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B)
    (s₀ : S) {i j : V} (h : M.graph.Adj i j) (a : S) :
    M.vertexPotential i a * incomingMessageProduct M (betheMessage M B s₀) i j a =
      Real.exp (betheNodeConst M B s₀ i) * betheRatio M B i j a s₀ := by
  have hN := betheMessage_node M B hB hstat s₀ i a
  rw [← Finset.mul_prod_erase _ _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)] at hN
  have hb := (hB.2.1 i a).ne'
  have hR := (betheRatio_pos M B hB h a s₀).ne'
  unfold incomingMessageProduct
  unfold betheMessage at hN ⊢
  field_simp at hN ⊢
  linear_combination hN

/-- A table proportional to a probability vector normalizes to it. -/
private theorem eq_div_sum_of_eq_mul {ι : Type*} [Fintype ι] {p w : ι → ℝ} {C : ℝ}
    (hC : C ≠ 0) (hp : ∑ x, p x = 1) (hw : ∀ x, w x = C * p x) (x : ι) :
    p x = w x / ∑ y, w y := by
  simp only [hw, ← Finset.mul_sum, hp, mul_one]
  field_simp

/-- Bethe stationary points in the interior of the local polytope are BP beliefs. -/
private theorem exists_beliefPropagationFixedPoint_of_isBetheStationary
    (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) (hstat : IsBetheStationary M B) :
    ∃ m, IsBeliefPropagationFixedPoint M m ∧
      (∀ i a, B.1 i a = beliefPropagationNode M m i a) ∧
      ∀ i j, M.graph.Adj i j → ∀ a b, B.2 i j a b = beliefPropagationEdge M m i j a b := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · have hV : ∀ i : V, False := fun i ↦ by simpa using hB.1.2.1 i
    exact ⟨fun _ _ _ ↦ 1, ⟨fun i _ _ _ ↦ (hV i).elim, fun i _ _ ↦ (hV i).elim⟩,
      fun i _ ↦ (hV i).elim, fun i _ _ _ _ ↦ (hV i).elim⟩
  set m := betheMessage M B s₀
  set K := betheNodeConst M B s₀
  have hR := fun {i j : V} (h : M.graph.Adj i j) ↦ betheRatio_pos M B hB h
  -- the edge beliefs in terms of the edge ratios at the reference state
  have hedge : ∀ i j, M.graph.Adj i j → ∀ a b, B.2 i j a b * betheRatio M B i j s₀ s₀ =
      M.edgePotential i j a b * betheRatio M B i j a s₀ * betheRatio M B i j s₀ b := by
    intro i j h a b
    have := betheRatio_mul_of_stationary M B hB hstat h s₀ a b
    have hψ := (M.edgePotential_pos i j h a b).ne'
    unfold betheRatio at this ⊢
    field_simp at this ⊢
    linear_combination this
  refine ⟨m, ⟨fun i j h a ↦ div_pos (hB.2.1 j a) (hR h.symm a s₀), fun i j h ↦ ?_⟩,
    fun i a ↦ ?_, fun i j h a b ↦ ?_⟩
  · refine ⟨1 / (Real.exp (K i) * betheRatio M B i j s₀ s₀), by have := hR h s₀ s₀; positivity,
      fun b ↦ ?_⟩
    have hterm : ∀ a, M.vertexPotential i a * M.edgePotential i j a b *
        incomingMessageProduct M m i j a =
          Real.exp (K i) * betheRatio M B i j s₀ s₀ / betheRatio M B i j s₀ b * B.2 i j a b := by
      intro a
      have h1 := betheMessage_incoming M B hB hstat s₀ h a
      have h2 := hedge i j h a b
      have := hR h s₀ b
      field_simp
      linear_combination M.edgePotential i j a b * betheRatio M B i j s₀ b * h1 -
        Real.exp (K i) * h2
    rw [Finset.sum_congr rfl fun a _ ↦ hterm a, ← Finset.mul_sum,
      (hB.1.2.2 i j h).2.2.1 b]
    show B.1 j b / betheRatio M B j i b s₀ = _
    rw [betheRatio_symm M B hB h]
    have := hR h s₀ s₀
    have := hR h s₀ b
    field_simp
  · unfold beliefPropagationNode
    exact eq_div_sum_of_eq_mul (Real.exp_pos (K i)).ne' (hB.1.2.1 i)
      (fun a ↦ betheMessage_node M B hB hstat s₀ i a) a
  · unfold beliefPropagationEdge
    dsimp only
    have hsum : ∑ z : S × S, B.2 i j z.1 z.2 = 1 := by
      rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ ↦ (hB.1.2.2 i j h).2.1 a]
      exact hB.1.2.1 i
    refine eq_div_sum_of_eq_mul (p := fun z : S × S ↦ B.2 i j z.1 z.2)
      (w := fun z : S × S ↦ M.vertexPotential i z.1 * M.vertexPotential j z.2 *
        M.edgePotential i j z.1 z.2 * incomingMessageProduct M m i j z.1 *
          incomingMessageProduct M m j i z.2)
      (C := Real.exp (K i) * Real.exp (K j) * betheRatio M B i j s₀ s₀)
      (by have := hR h s₀ s₀; positivity) hsum (fun z ↦ ?_) (a, b)
    have h1 := betheMessage_incoming M B hB hstat s₀ h z.1
    have h2 := betheMessage_incoming M B hB hstat s₀ h.symm z.2
    rw [betheRatio_symm M B hB h] at h2
    have h3 := hedge i j h z.1 z.2
    linear_combination M.edgePotential i j z.1 z.2 * M.vertexPotential j z.2 *
      incomingMessageProduct M m j i z.2 * h1 +
      M.edgePotential i j z.1 z.2 * Real.exp (K i) * betheRatio M B i j z.1 s₀ * h2 -
      Real.exp (K i) * Real.exp (K j) * h3

omit [LinearOrder V] [Fintype S] in
/-- Products of positive incoming messages are positive. -/
private theorem incomingMessageProduct_pos (M : PairwiseGraphicalModel V S) {m : V → V → S → ℝ}
    (hm : ∀ i j, M.graph.Adj i j → ∀ a, 0 < m i j a) (i j : V) (a : S) :
    0 < incomingMessageProduct M m i j a :=
  Finset.prod_pos fun k hk ↦ hm k i ((SimpleGraph.mem_neighborFinset _ _ _).mp
    (Finset.mem_of_mem_erase hk)).symm a

/-- BP beliefs from positive messages are Bethe stationary points. -/
private theorem isBetheStationary_of_beliefPropagation (M : PairwiseGraphicalModel V S)
    (B : LocalBeliefTables V S) (hB : IsInteriorLocalBelief M B) (m : V → V → S → ℝ)
    (hm : ∀ i j, M.graph.Adj i j → ∀ a, 0 < m i j a)
    (hnode : ∀ i a, B.1 i a = beliefPropagationNode M m i a)
    (hedge : ∀ i j, M.graph.Adj i j → ∀ a b, B.2 i j a b = beliefPropagationEdge M m i j a b) :
    IsBetheStationary M B := by
  intro D hD
  convert hasDerivAt_betheFreeEnergy M B hB D using 1
  rw [betheDirDeriv_eq M B hB D fun i j h ↦ (hD.2 i j h).2.2]
  have hI := incomingMessageProduct_pos M hm
  set P : V → V → S → ℝ := fun i j a ↦
    Real.log (M.vertexPotential i a) + Real.log (incomingMessageProduct M m i j a)
  set w : V → V → S → S → ℝ := fun i j a b ↦ M.vertexPotential i a * M.vertexPotential j b *
    M.edgePotential i j a b * incomingMessageProduct M m i j a *
      incomingMessageProduct M m j i b
  have hw : ∀ i j, M.graph.Adj i j → ∀ a b, 0 < w i j a b := fun i j h a b ↦ by
    have := M.vertexPotential_pos i a
    have := M.vertexPotential_pos j b
    have := M.edgePotential_pos i j h a b
    have := hI i j a
    have := hI j i b
    positivity
  have hG : ∀ i j, M.graph.Adj i j → ∀ a b, betheEdgeGrad M B i j a b =
      P i j a + P j i b + (1 - Real.log (∑ z : S × S, w i j z.1 z.2)) := by
    intro i j h a b
    have hZ : 0 < ∑ z : S × S, w i j z.1 z.2 :=
      Finset.sum_pos (fun z _ ↦ hw i j h z.1 z.2) ⟨(a, b), Finset.mem_univ _⟩
    unfold betheEdgeGrad
    rw [hedge i j h a b]
    unfold beliefPropagationEdge
    dsimp only
    have := M.vertexPotential_pos i a
    have := M.vertexPotential_pos j b
    have := M.edgePotential_pos i j h a b
    have := hI i j a
    have := hI j i b
    rw [Real.log_div (hw i j h a b).ne' hZ.ne']
    simp only [w, P]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  have hrow : ∀ i, ∀ j ∈ M.graph.neighborFinset i,
      ∑ a, ∑ b, betheEdgeGrad M B i j a b * D.2 i j a b =
        ∑ a, P i j a * D.1 i a + ∑ b, P j i b * D.1 j b := by
    intro i j hj
    have h := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
    obtain ⟨hr, hc, -⟩ := hD.2 i j h
    simp only [hG i j h, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b ↦ P j i b * D.2 i j a b)]
    simp only [← Finset.mul_sum, hr, hc, hD.1 i, mul_zero, add_zero]
  have hnodeG : ∀ i a, betheNodeGrad M B i a + ∑ j ∈ M.graph.neighborFinset i, P i j a =
      -((M.graph.neighborFinset i).card - (1 : ℝ)) * (1 - Real.log (∑ b,
        M.vertexPotential i b * ∏ k ∈ M.graph.neighborFinset i, m k i b)) := by
    intro i a
    have hmi : ∀ b, ∀ k ∈ M.graph.neighborFinset i, 0 < m k i b := fun b k hk ↦
      hm k i ((SimpleGraph.mem_neighborFinset _ _ _).mp hk).symm b
    have hwi : ∀ b, 0 < M.vertexPotential i b * ∏ k ∈ M.graph.neighborFinset i, m k i b :=
      fun b ↦ mul_pos (M.vertexPotential_pos i b) (Finset.prod_pos (hmi b))
    have hZ := Finset.sum_pos (fun b _ ↦ hwi b) ⟨a, Finset.mem_univ a⟩
    have hlog : Real.log (B.1 i a) = Real.log (M.vertexPotential i a) +
        ∑ k ∈ M.graph.neighborFinset i, Real.log (m k i a) - Real.log (∑ b,
          M.vertexPotential i b * ∏ k ∈ M.graph.neighborFinset i, m k i b) := by
      rw [hnode i a]
      unfold beliefPropagationNode
      dsimp only
      rw [Real.log_div (hwi a).ne' hZ.ne', Real.log_mul (M.vertexPotential_pos i a).ne'
        (Finset.prod_pos (hmi a)).ne', Real.log_prod fun k hk ↦ (hmi a k hk).ne']
    have hP : ∑ j ∈ M.graph.neighborFinset i, P i j a =
        (M.graph.neighborFinset i).card * Real.log (M.vertexPotential i a) +
          ((M.graph.neighborFinset i).card - (1 : ℝ)) *
            ∑ k ∈ M.graph.neighborFinset i, Real.log (m k i a) := by
      simp only [P]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_congr rfl fun j hj ↦ by
        unfold incomingMessageProduct
        rw [Real.log_prod fun k hk ↦ (hmi a k (Finset.mem_of_mem_erase hk)).ne',
          Finset.sum_erase_eq_sub hj]]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    unfold betheNodeGrad
    rw [hP, hlog]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl (hrow i)]
  simp only [Finset.sum_add_distrib]
  rw [sum_neighborFinset_swap M (fun i j ↦ ∑ a, P i j a * D.1 i a)]
  have hfin : ∀ i, ∑ a, betheNodeGrad M B i a * D.1 i a +
      ∑ j ∈ M.graph.neighborFinset i, ∑ a, P i j a * D.1 i a = 0 := by
    intro i
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun a _ ↦ by rw [← add_mul, hnodeG], ← Finset.mul_sum, hD.1 i,
      mul_zero]
  have := Finset.sum_eq_zero fun i (_ : i ∈ Finset.univ) ↦ hfin i
  rw [Finset.sum_add_distrib] at this
  linarith

/-- GAPS 107.19: Bethe stationary points in the positive local polytope are exactly BP beliefs. -/
theorem isBetheStationary_iff_exists_beliefPropagationFixedPoint
    (M : PairwiseGraphicalModel V S) (B : LocalBeliefTables V S)
    (hB : IsInteriorLocalBelief M B) :
    IsBetheStationary M B ↔ ∃ m, IsBeliefPropagationFixedPoint M m ∧
      (∀ i a, B.1 i a = beliefPropagationNode M m i a) ∧
      ∀ i j, M.graph.Adj i j → ∀ a b, B.2 i j a b = beliefPropagationEdge M m i j a b :=
  ⟨exists_beliefPropagationFixedPoint_of_isBetheStationary M B hB,
    fun ⟨m, hm, hnode, hedge⟩ ↦ isBetheStationary_of_beliefPropagation M B hB m hm.1 hnode hedge⟩

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
