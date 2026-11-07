module

public import CKSD.LinearModels.Causal

/-!
# Directed Markov properties, interventions, and causal discovery for discrete variables

All variables take values in one finite state type `S`, and a law on the configurations
`V → S` is given by a probability mass function. Marginal and conditional probabilities are
finite sums and quotients, with Lean's convention `x / 0 = 0`; whenever a conditional
probability appears in a formula, the conditioning event is assumed to have positive
probability. The graph-theoretic notions (`CausalGraph`, active paths, d-separation, skeleton,
unshielded colliders, truncated factorization) are those of `CKSD.LinearModels.Causal`.

A single configuration `b : V → S` carries the values of all variables that appear in a query;
for disjoint vertex sets `X`, `Y`, `Z` the values `x`, `y`, `z` are its restrictions.
Sums over the values of a set `B` of variables run over `B → S` and overwrite `b` on `B`.

Sources: GAPS 105.62, 105.63, 105.64, and 105.70 (discrete-variable forms).
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

/-- Parents of a vertex, as a finite set. -/
def CausalGraph.parentFinset [Fintype V] (G : CausalGraph V) (v : V) : Finset V :=
  Finset.univ.filter fun u ↦ G.edge u v

/-- Nondescendants of a vertex other than the vertex itself and its parents. -/
def CausalGraph.nonDescendantFinset [Fintype V] (G : CausalGraph V) (v : V) : Finset V :=
  Finset.univ.filter fun u ↦ u ≠ v ∧ ¬ G.IsDescendant v u ∧ ¬ G.edge u v

/-- The graph with all arrows into `X` removed (`G_{\bar X}`). -/
def CausalGraph.removeIncoming (G : CausalGraph V) (X : Set V) : CausalGraph V where
  edge u v := G.edge u v ∧ v ∉ X
  acyclic v h := G.acyclic v (Relation.TransGen.mono (fun _ _ h ↦ h.1) _ _ h)

/-- The graph with all arrows out of `Z` removed (`G_{\underline Z}`). -/
def CausalGraph.removeOutgoing (G : CausalGraph V) (Z : Set V) : CausalGraph V where
  edge u v := G.edge u v ∧ u ∉ Z
  acyclic v h := G.acyclic v (Relation.TransGen.mono (fun _ _ h ↦ h.1) _ _ h)

/-- A directed path from a vertex of `X` to a vertex of `Y` has some vertex in `Z`. -/
def CausalGraph.InterceptsDirectedPaths (G : CausalGraph V) (X Y Z : Set V) : Prop :=
  ∀ n : ℕ, ∀ p : Fin (n + 1) → V, p 0 ∈ X → p (Fin.last n) ∈ Y →
    (∀ i : Fin n, G.edge (p i.castSucc) (p i.succ)) → ∃ i, p i ∈ Z

/-- Every back-door path from `X` to `Y`, that is, every path whose first arrow points into
its initial vertex in `X`, is blocked by `W`. -/
def CausalGraph.BlocksBackdoorPaths (G : CausalGraph V) (X Y W : Set V) : Prop :=
  ∀ n : ℕ, ∀ p : Fin (n + 2) → V, p 0 ∈ X → p (Fin.last (n + 1)) ∈ Y → G.edge (p 1) (p 0) →
    ¬ G.IsActivePath W p

/-- The back-door criterion for `Z` relative to `(X, Y)`: no vertex of `Z` is a descendant of
a vertex of `X`, and `Z` blocks every back-door path from `X` to `Y`. -/
def CausalGraph.IsBackdoorSet (G : CausalGraph V) (X Y Z : Set V) : Prop :=
  (∀ x ∈ X, ∀ z ∈ Z, ¬ G.IsDescendant x z) ∧ G.BlocksBackdoorPaths X Y Z

/-- The front-door criterion for `Z` relative to `(X, Y)`. -/
def CausalGraph.IsFrontdoorSet (G : CausalGraph V) (X Y Z : Set V) : Prop :=
  G.InterceptsDirectedPaths X Y Z ∧ G.BlocksBackdoorPaths X Z ∅ ∧ G.BlocksBackdoorPaths Z Y X

/-- A probability mass function on configurations. -/
def IsProbabilityMass [Fintype V] [Fintype S] (p : (V → S) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Local conditional mass functions: each is a probability mass function in the state of its
vertex, for every configuration of the other variables. -/
def IsLocalMassFamily [Fintype S] (localMass : V → (V → S) → S → ℝ) : Prop :=
  (∀ v x s, 0 ≤ localMass v x s) ∧ ∀ v x, ∑ s, localMass v x s = 1

/-- Probability that the variables in `B` take the values of `x`. -/
def marginalMass [Fintype V] [Fintype S] (p : (V → S) → ℝ) (B : Finset V) (x : V → S) : ℝ :=
  ∑ y, if ∀ v ∈ B, y v = x v then p y else 0

/-- Conditional probability that the variables in `B` take the values of `x`, given that the
variables in `C` take the values of `x`. -/
def condMass [Fintype V] [Fintype S] (p : (V → S) → ℝ) (B C : Finset V) (x : V → S) : ℝ :=
  marginalMass p (B ∪ C) x / marginalMass p C x

/-- Conditional independence of `X_A` and `X_B` given `X_C` for a mass function, in product
form (no division). -/
def CondIndepMass [Fintype V] [Fintype S] (p : (V → S) → ℝ) (A B C : Finset V) : Prop :=
  ∀ x, marginalMass p (A ∪ B ∪ C) x * marginalMass p C x =
    marginalMass p (A ∪ C) x * marginalMass p (B ∪ C) x

/-- Recursive factorization `p(x) = ∏_v p(x_v | x_{pa(v)})`, with the conditional masses of
`p` itself. -/
def CausalGraph.RecursivelyFactorizes [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) : Prop :=
  ∀ x, p x = ∏ v, condMass p {v} (G.parentFinset v) x

/-- The local directed Markov property: each variable is conditionally independent of its
nondescendants given its parents. -/
def CausalGraph.IsLocalDirectedMarkov [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) : Prop :=
  ∀ v, CondIndepMass p {v} (G.nonDescendantFinset v) (G.parentFinset v)

/-- The global directed Markov property: d-separation of disjoint sets implies conditional
independence. -/
def CausalGraph.IsGlobalDirectedMarkov [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) : Prop :=
  ∀ A B C : Finset V, Disjoint A B → Disjoint A C → Disjoint B C →
    G.DSeparated A B C → CondIndepMass p A B C

/-- A mass function is faithful to `G` when its conditional independences among disjoint sets
are exactly the d-separations of `G`. -/
def CausalGraph.IsFaithful [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) : Prop :=
  ∀ A B C : Finset V, Disjoint A B → Disjoint A C → Disjoint B C →
    (G.DSeparated A B C ↔ CondIndepMass p A B C)

/-- Overwrite a configuration on `B` by values indexed by `B`. -/
def overwriteOn (B : Finset V) (b : B → S) (x : V → S) : V → S :=
  fun v ↦ if h : v ∈ B then b ⟨v, h⟩ else x v

/-- Interventional probability that the variables in `B` take the values of `y`, under
`do(X = x)` given by the truncated factorization. -/
def doMarginalMass [Fintype V] [Fintype S] (localMass : V → (V → S) → S → ℝ) (X : Finset V)
    (x : V → S) (B : Finset V) (y : V → S) : ℝ :=
  ∑ w, if ∀ v ∈ B, w v = y v then interventionMass localMass X x w else 0

/-- Interventional conditional probability `P(y | do(x), w)`, all values read from `b`. -/
def condDoMass [Fintype V] [Fintype S] (localMass : V → (V → S) → S → ℝ) (X Y W : Finset V)
    (b : V → S) : ℝ :=
  doMarginalMass localMass X b (Y ∪ W) b / doMarginalMass localMass X b W b

/-- GAPS 105.62: for a probability mass function on finitely many finite-valued variables,
recursive factorization along a directed acyclic graph, the local directed Markov property, and
the global (d-separation) Markov property are equivalent. Discrete-variable form: densities
with respect to counting measure on a finite product. -/
theorem CausalGraph.recursivelyFactorizes_tfae [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) (hp : IsProbabilityMass p) :
    (G.RecursivelyFactorizes p ↔ G.IsLocalDirectedMarkov p) ∧
      (G.IsLocalDirectedMarkov p ↔ G.IsGlobalDirectedMarkov p) := by
  sorry

/-- GAPS 105.63, back-door formula for discrete variables: if `Z` satisfies the back-door
criterion relative to `(X, Y)`, then `P(y | do(x)) = ∑_z P(y | x, z) P(z)` for the law
factorizing recursively along `G` with local masses `localMass`. The conditioning events
`{X = x, Z = z}` are assumed to have positive probability. -/
theorem doMarginalMass_eq_backdoor [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hbd : G.IsBackdoorSet X Y Z) (b : V → S)
    (hposZ : ∀ z : Z → S,
      0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z) (overwriteOn Z z b)) :
    doMarginalMass localMass X b Y b =
      ∑ z : Z → S,
        condMass (directedFactorizationMass localMass) Y (X ∪ Z) (overwriteOn Z z b) *
          marginalMass (directedFactorizationMass localMass) Z (overwriteOn Z z b) := by
  sorry

/-- GAPS 105.63, front-door formula for discrete variables: if `Z` satisfies the front-door
criterion relative to `(X, Y)`, then
`P(y | do(x)) = ∑_z P(z | x) ∑_{x'} P(y | x', z) P(x')`. The conditioning events `{X = x}` and
`{X = x', Z = z}` are assumed to have positive probability. -/
theorem doMarginalMass_eq_frontdoor [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z : Finset V) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hfd : G.IsFrontdoorSet X Y Z) (b : V → S)
    (hposX : 0 < marginalMass (directedFactorizationMass localMass) X b)
    (hposXZ : ∀ (x' : X → S) (z : Z → S),
      0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z)
        (overwriteOn X x' (overwriteOn Z z b))) :
    doMarginalMass localMass X b Y b =
      ∑ z : Z → S,
        condMass (directedFactorizationMass localMass) Z X (overwriteOn Z z b) *
          ∑ x' : X → S,
            condMass (directedFactorizationMass localMass) Y (X ∪ Z)
                (overwriteOn X x' (overwriteOn Z z b)) *
              marginalMass (directedFactorizationMass localMass) X
                (overwriteOn X x' (overwriteOn Z z b)) := by
  sorry

/-- GAPS 105.64, rule 1 of the do-calculus (insertion and deletion of observations):
if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X}`, then
`P(y | do(x), z, w) = P(y | do(x), w)`. The conditioning event `{Z = z, W = w}` has positive
interventional probability. -/
theorem condDoMass_rule_one [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z W : Finset V)
    (hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint X W ∧ Disjoint Y Z ∧ Disjoint Y W ∧
      Disjoint Z W)
    (hsep : (G.removeIncoming X).DSeparated Y Z ↑(X ∪ W)) (b : V → S)
    (hpos : 0 < doMarginalMass localMass X b (Z ∪ W) b) :
    condDoMass localMass X Y (Z ∪ W) b = condDoMass localMass X Y W b := by
  sorry

/-- GAPS 105.64, rule 2 of the do-calculus (action/observation exchange):
if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X \underline Z}`, then
`P(y | do(x), do(z), w) = P(y | do(x), z, w)`. The conditioning events have positive
interventional probability. -/
theorem condDoMass_rule_two [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z W : Finset V)
    (hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint X W ∧ Disjoint Y Z ∧ Disjoint Y W ∧
      Disjoint Z W)
    (hsep : ((G.removeIncoming X).removeOutgoing Z).DSeparated Y Z ↑(X ∪ W)) (b : V → S)
    (hpos : 0 < doMarginalMass localMass X b (Z ∪ W) b)
    (hpos' : 0 < doMarginalMass localMass (X ∪ Z) b W b) :
    condDoMass localMass (X ∪ Z) Y W b = condDoMass localMass X Y (Z ∪ W) b := by
  sorry

/-- The vertices of `Z` that are not ancestors of any vertex of `W` in `G_{\bar X}`. -/
def CausalGraph.nonAncestorPart (G : CausalGraph V) (X Z W : Set V) : Set V :=
  {z | z ∈ Z ∧ ∀ w ∈ W, ¬ (G.removeIncoming X).IsDescendant z w}

/-- GAPS 105.64, rule 3 of the do-calculus (insertion and deletion of actions):
if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X, \overline{Z(W)}}`, then
`P(y | do(x), do(z), w) = P(y | do(x), w)`. The conditioning events have positive
interventional probability. The completeness of the three rules for identifiability is not
stated. -/
theorem condDoMass_rule_three [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z W : Finset V)
    (hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint X W ∧ Disjoint Y Z ∧ Disjoint Y W ∧
      Disjoint Z W)
    (hsep : (G.removeIncoming (↑X ∪ G.nonAncestorPart X Z W)).DSeparated Y Z ↑(X ∪ W))
    (b : V → S) (hpos : 0 < doMarginalMass localMass X b W b)
    (hpos' : 0 < doMarginalMass localMass (X ∪ Z) b W b) :
    condDoMass localMass (X ∪ Z) Y W b = condDoMass localMass X Y W b := by
  sorry

/-- No vertex is adjacent to itself in a directed acyclic graph. -/
theorem CausalGraph.not_adjacent_self (G : CausalGraph V) (v : V) : ¬ G.Adjacent v v := by
  rintro (h | h) <;> exact G.acyclic v (Relation.TransGen.single h)

/-- Adjacent vertices are distinct. -/
theorem CausalGraph.Adjacent.ne {G : CausalGraph V} {u v : V} (h : G.Adjacent u v) : u ≠ v := by
  rintro rfl
  exact G.not_adjacent_self u h

/-- Adjacency is symmetric. -/
theorem CausalGraph.Adjacent.symm {G : CausalGraph V} {u v : V} (h : G.Adjacent u v) :
    G.Adjacent v u :=
  Or.symm h

/-- Adjacent vertices are joined by an active path of length one, whatever is conditioned on. -/
theorem CausalGraph.Adjacent.not_dSeparated {G : CausalGraph V} {u v : V} (h : G.Adjacent u v)
    (Z : Set V) : ¬ G.DSeparated {u} {v} Z := by
  intro hsep
  refine hsep 1 ![u, v] rfl rfl ⟨?_, ?_, fun i ↦ i.elim0⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | simp_all [h.ne, h.ne.symm]
  · intro i
    fin_cases i
    exact h

/-- GAPS 105.70: two nonadjacent distinct vertices of a directed acyclic graph are d-separated
by the parents of one of them. -/
theorem CausalGraph.dSeparated_parents_of_not_adjacent [Fintype V] (G : CausalGraph V)
    {u v : V} (huv : u ≠ v) (h : ¬ G.Adjacent u v) :
    G.DSeparated {u} {v} (G.parents u) ∨ G.DSeparated {u} {v} (G.parents v) := by
  sorry

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

/-- GAPS 105.70: in a skeleton path `u - v - w` with `u`, `w` nonadjacent, if `S` (not
containing `u`, `w`) d-separates `u` and `w`, then `u → v ← w` exactly when `v ∉ S`. -/
theorem CausalGraph.isCollider_iff_not_mem_of_dSeparated [Fintype V] (G : CausalGraph V)
    {u v w : V} (huv : G.Adjacent u v) (hvw : G.Adjacent v w) (huw : ¬ G.Adjacent u w)
    (hne : u ≠ w) (S : Set V) (hu : u ∉ S) (hw : w ∉ S) (hsep : G.DSeparated {u} {w} S) :
    (G.edge u v ∧ G.edge w v) ↔ v ∉ S := by
  sorry

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
      (G.isCollider_iff_not_mem_of_dSeparated huv' hvw' huw hne Z hu hw hZ).1 ⟨huv, hwv⟩
    have huwH : ¬ H.Adjacent u w := fun h ↦ huw ((hadj u w).2 h)
    have hZH : H.DSeparated {u} {w} Z := (hsep u w Z hne hu hw).1 hZ
    exact ⟨hne, (H.isCollider_iff_not_mem_of_dSeparated ((hadj u v).1 huv')
      ((hadj v w).1 hvw') huwH hne Z hu hw hZH).2 hv |>.1,
      (H.isCollider_iff_not_mem_of_dSeparated ((hadj u v).1 huv')
      ((hadj v w).1 hvw') huwH hne Z hu hw hZH).2 hv |>.2, huwH⟩
  intro u v w
  exact ⟨key G H hadj hsep u v w,
    key H G (fun u v ↦ (hadj u v).symm) (fun u v Z h₁ h₂ h₃ ↦ (hsep u v Z h₁ h₂ h₃).symm) u v w⟩

end CKSD
