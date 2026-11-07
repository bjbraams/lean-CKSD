module

public import CKSD.LinearModels.ActiveTrails

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

The central step is `condIndepMass_directedFactorizationMass_of_dSeparated`: a recursive product
of local masses satisfies the global directed Markov property. Its proof follows Lauritzen
(*Graphical Models*, 1996, §3.2): the coordinates outside the ancestral closure of
`A ∪ B ∪ C` are summed out, and the remaining product splits into a factor depending on the
vertices reachable from `A` by trails whose noncolliders avoid `C` and whose colliders lie in
that ancestral closure, and a factor depending on the other vertices; the graph-theoretic
steps are in `CKSD.LinearModels.ActiveTrails`. The rules of the do-calculus are derived from it:
rule 1 directly, rule 2 by comparing with the mass in which the children of `Z` read fixed
values of `Z`, and rule 3 by Pearl's augmentation of the graph with an intervention indicator
(Pearl, *Causality*, 2009, §3.4). The back-door and front-door formulae follow from rule 2 and
the invariance of the marginal law of nondescendants under intervention.
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

/-- The reverse of an active path is active. -/
theorem CausalGraph.IsActivePath.rev {G : CausalGraph V} {Z : Set V} {n : ℕ}
    {p : Fin (n + 1) → V} (h : G.IsActivePath Z p) : G.IsActivePath Z (p ∘ Fin.rev) := by
  obtain ⟨hinj, hedge, htri⟩ := h
  refine ⟨hinj.comp Fin.rev_injective, fun i ↦ ?_, fun i ↦ ?_⟩
  · have := hedge i.rev
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ]
    exact this.symm
  · have hi := i.isLt
    have := htri ⟨n - 2 - i.val, by omega⟩
    have e1 : (Fin.rev (⟨i.val, by omega⟩ : Fin (n + 1))) = ⟨n - 2 - i.val + 2, by omega⟩ := by
      ext; simp; omega
    have e2 : (Fin.rev (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = ⟨n - 2 - i.val + 1, by omega⟩ := by
      ext; simp; omega
    have e3 : (Fin.rev (⟨i.val + 2, by omega⟩ : Fin (n + 1))) = ⟨n - 2 - i.val, by omega⟩ := by
      ext; simp; omega
    simp only [Function.comp_apply, e1, e2, e3] at this ⊢
    split_ifs at this ⊢ <;> tauto

/-- d-separation is symmetric. -/
theorem CausalGraph.DSeparated.symm {G : CausalGraph V} {A B Z : Set V}
    (h : G.DSeparated A B Z) : G.DSeparated B A Z := by
  intro n p h0 hn hp
  refine h n (p ∘ Fin.rev) ?_ ?_ hp.rev
  · simpa using hn
  · simpa using h0

/-- A path leaving `u` along an outgoing arrow and active given the parents of `u` is a
directed path out of `u`. -/
theorem CausalGraph.isDescendant_of_isActivePath_parents (G : CausalGraph V) {u : V}
    {n : ℕ} {p : Fin (n + 1) → V} (hp : G.IsActivePath (G.parents u) p) (h0 : p 0 = u)
    (hn : 0 < n) (hlast : ¬ G.edge (p (Fin.last n)) u) :
    G.IsDescendant u (p (Fin.last n)) := by
  obtain ⟨hinj, hedge, htri⟩ := hp
  -- by induction: for `1 ≤ k ≤ n`, the edge into `p k` is forward and `u ⇝ p k`
  have key : ∀ k (hk : k + 1 ≤ n),
      G.edge (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩) ∧ G.IsDescendant u (p ⟨k + 1, by omega⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have he := hedge ⟨0, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk, zero_add] at he
      have hf : G.edge (p 0) (p ⟨1, by omega⟩) := by
        rcases he with he | he
        · exact he
        · exfalso
          rw [Fin.mk_zero] at he
          rw [h0] at he
          by_cases hn1 : n = 1
          · subst hn1; exact hlast he
          · have ht := htri ⟨0, by omega⟩
            simp only at ht
            split_ifs at ht with hc
            · rw [Fin.mk_zero, h0] at hc
              exact G.acyclic u (Relation.TransGen.tail (Relation.TransGen.single hc.1) he)
            · exact ht he
      refine ⟨by simpa using hf, ?_⟩
      have : G.edge u (p ⟨1, by omega⟩) := by rw [← h0]; exact hf
      exact Relation.TransGen.single this
    | succ k ih =>
      intro hk
      obtain ⟨hprev, hdesc⟩ := ih (by omega)
      have he := hedge ⟨k + 1, hk⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at he
      have hf : G.edge (p ⟨k + 1, by omega⟩) (p ⟨k + 2, by omega⟩) := by
        rcases he with he | he
        · exact he
        · exfalso
          have ht := htri ⟨k, by omega⟩
          simp only at ht
          split_ifs at ht with hc
          swap
          · exact hc ⟨hprev, he⟩
          obtain ⟨z, hz, hz'⟩ := ht
          have hzd : G.IsDescendant u z := by
            rcases hz' with rfl | hz'
            · exact hdesc
            · exact hdesc.trans hz'
          exact G.acyclic u (Relation.TransGen.tail hzd hz)
      exact ⟨hf, Relation.TransGen.tail hdesc hf⟩
  have := (key (n - 1) (by omega)).2
  have e : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by ext; simp; omega
  rwa [e] at this

/-- A vertex `u` is d-separated by its parents from every other vertex that is neither a parent
nor a descendant of `u`. -/
theorem CausalGraph.dSeparated_parents_of_not_isDescendant (G : CausalGraph V) {u v : V}
    (huv : u ≠ v) (hpar : ¬ G.edge v u) (hdesc : ¬ G.IsDescendant u v) :
    G.DSeparated {u} {v} (G.parents u) := by
  intro n p h0 hn hp
  rw [mem_singleton_iff] at h0 hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact huv (h0.symm.trans hn)
  · exact hdesc (hn ▸ G.isDescendant_of_isActivePath_parents hp h0 hpos (hn ▸ hpar))


/-- Splitting a sum over configurations according to the value at one coordinate. -/
theorem sum_eq_sum_ite_sum_update [Fintype V] [Fintype S] [DecidableEq V] (u : V) (c : S)
    (Φ : (V → S) → ℝ) :
    ∑ y, Φ y = ∑ y, if y u = c then ∑ s, Φ (Function.update y u s) else 0 := by
  calc ∑ y, Φ y = ∑ s, ∑ y, if y u = s then Φ y else 0 := by
        rw [Finset.sum_comm]
        simp
    _ = ∑ s, ∑ y, if y u = c then Φ (Function.update y u s) else 0 := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        let e : (V → S) ≃ (V → S) :=
          { toFun := fun y ↦ Function.update y u (Equiv.swap s c (y u))
            invFun := fun y ↦ Function.update y u (Equiv.swap s c (y u))
            left_inv := fun y ↦ by simp
            right_inv := fun y ↦ by simp }
        refine (Fintype.sum_equiv e _ _ fun y ↦ ?_).symm
        simp only [e, Equiv.coe_fn_mk, Function.update_self]
        by_cases hy : y u = c
        · simp [hy]
        · have : Equiv.swap s c (y u) ≠ s := by
            intro h
            apply hy
            simpa using congrArg (Equiv.swap s c) h
          simp [hy, this]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        split_ifs <;> simp

/-- Summing out the coordinates of a set closed under children: the factors of the summed
vertices disappear, the coordinates are frozen at those of `x`. -/
theorem sum_ite_prod_eq_sum_ite_prod_compl [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (x : V → S) (E : Finset V) :
    ∀ U : Finset V, (∀ w ∈ U, ∀ c, G.edge w c → c ∈ U) → Disjoint E U →
      (∑ y, if ∀ v ∈ E, y v = x v then ∏ v, localMass v y (y v) else 0) =
        ∑ y, if (∀ v ∈ E, y v = x v) ∧ ∀ v ∈ U, y v = x v
          then ∏ v ∈ Uᶜ, localMass v y (y v) else 0 := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hU hEU
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  -- a vertex of `U` without parents in `U`
  have : IsTrans V (Relation.TransGen G.edge) := ⟨fun _ _ _ ↦ Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen G.edge) := ⟨G.acyclic⟩
  obtain ⟨u, huU, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl
    (Relation.TransGen G.edge)).has_min (U : Set V) hne
  set U' := U.erase u with hU'
  have hU'U : U' ⊂ U := Finset.erase_ssubset huU
  have hU'cl : ∀ w ∈ U', ∀ c, G.edge w c → c ∈ U' := by
    intro w hw c hc
    refine Finset.mem_erase.2 ⟨?_, hU w (Finset.mem_of_mem_erase hw) c hc⟩
    rintro rfl
    exact hmin w (Finset.mem_of_mem_erase hw) (Relation.TransGen.single hc)
  rw [ih U' hU'U hU'cl (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hEU),
    sum_eq_sum_ite_sum_update u (x u)]
  have huE : u ∉ E := fun h ↦ Finset.disjoint_left.1 hEU h huU
  have hchild : ∀ c, G.edge u c → c ∈ U := fun c hc ↦ hU u huU c hc
  have hcompl : U'ᶜ = insert u Uᶜ := by
    ext v
    simp only [hU', Finset.mem_compl, Finset.mem_erase, Finset.mem_insert]
    by_cases hv : v = u <;> simp [hv]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hyu : y u = x u
  swap
  · rw [ite_eq_right hyu, ite_eq_right fun h ↦ hyu (h.2 u huU)]
  rw [ite_eq_left hyu]
  have hind : ∀ s, ((∀ v ∈ E, Function.update y u s v = x v) ∧
      ∀ v ∈ U', Function.update y u s v = x v) ↔
      ((∀ v ∈ E, y v = x v) ∧ ∀ v ∈ U', y v = x v) := by
    intro s
    have h1 : ∀ v ∈ E, Function.update y u s v = y v := fun v hv ↦
      Function.update_of_ne (by rintro rfl; exact huE hv) _ _
    have h2 : ∀ v ∈ U', Function.update y u s v = y v := fun v hv ↦
      Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨fun v hv ↦ (h1 v hv) ▸ ha v hv, fun v hv ↦ (h2 v hv) ▸ hb v hv⟩
    · rintro ⟨ha, hb⟩
      exact ⟨fun v hv ↦ (h1 v hv).symm ▸ ha v hv, fun v hv ↦ (h2 v hv).symm ▸ hb v hv⟩
  have hfac : ∀ s, ∏ v ∈ U'ᶜ, localMass v (Function.update y u s) (Function.update y u s v) =
      localMass u y s * ∏ v ∈ Uᶜ, localMass v y (y v) := by
    intro s
    rw [hcompl, Finset.prod_insert (by simp only [Finset.mem_compl, not_not]; exact huU)]
    congr 1
    · rw [Function.update_self, hpar u (Function.update y u s) y fun w hw ↦ Function.update_of_ne
        (show w ≠ u by rintro rfl; exact G.not_edge_self _ hw) _ _]
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      have hvu : v ≠ u := fun h ↦ (Finset.mem_compl.1 hv) (h ▸ huU)
      rw [Function.update_of_ne hvu, hpar v (Function.update y u s) y fun w hw ↦
        Function.update_of_ne
          (show w ≠ u by rintro rfl; exact (Finset.mem_compl.1 hv) (hchild v hw)) _ _]
  simp_rw [hind, hfac]
  have hU_iff : (∀ v ∈ U, y v = x v) ↔ ∀ v ∈ U', y v = x v := by
    constructor
    · exact fun h v hv ↦ h v (Finset.mem_of_mem_erase hv)
    · intro h v hv
      by_cases hvu : v = u
      · exact hvu ▸ hyu
      · exact h v (Finset.mem_erase.2 ⟨hvu, hv⟩)
  simp only [hU_iff]
  split_ifs
  · rw [← Finset.sum_mul, hloc.2 u y, one_mul]
  · simp

/-- Conditional independence from a factorization `g = F * H` with `F` depending only on the
coordinates in `R ∪ C` and `H` only on those outside `R`. -/
theorem sum_ite_mul_sum_ite_of_factor [Fintype V] [Fintype S] (g F H : (V → S) → ℝ)
    (A B C R : Finset V) (x : V → S) (hg : ∀ y, g y = F y * H y)
    (hF : ∀ y y', (∀ v, v ∈ R ∨ v ∈ C → y v = y' v) → F y = F y')
    (hH : ∀ y y', (∀ v, v ∉ R → y v = y' v) → H y = H y')
    (hAR : A ⊆ R) (hBR : Disjoint B R) (hCR : Disjoint C R) :
    (∑ y, if ∀ v ∈ A ∪ B ∪ C, y v = x v then g y else 0) *
        (∑ y, if ∀ v ∈ C, y v = x v then g y else 0) =
      (∑ y, if ∀ v ∈ A ∪ C, y v = x v then g y else 0) *
        (∑ y, if ∀ v ∈ B ∪ C, y v = x v then g y else 0) := by
  let mix : (V → S) → (V → S) → V → S := fun a b v ↦ if v ∈ R then a v else b v
  let σ : (V → S) × (V → S) ≃ (V → S) × (V → S) :=
    { toFun := fun p ↦ (mix p.1 p.2, mix p.2 p.1)
      invFun := fun p ↦ (mix p.1 p.2, mix p.2 p.1)
      left_inv := fun p ↦ by
        ext v <;> simp only [mix] <;> split_ifs <;> rfl
      right_inv := fun p ↦ by
        ext v <;> simp only [mix] <;> split_ifs <;> rfl }
  rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum, ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv σ _ _ fun p ↦ ?_
  obtain ⟨y, y'⟩ := p
  simp only [σ, Equiv.coe_fn_mk]
  have hmA : ∀ v ∈ A, mix y y' v = y v := fun v hv ↦ ite_eq_left (hAR hv)
  have hmC : ∀ v ∈ C, mix y y' v = y' v := fun v hv ↦
    ite_eq_right (Finset.disjoint_left.1 hCR hv)
  have hmB' : ∀ v ∈ B, mix y' y v = y v := fun v hv ↦
    ite_eq_right (Finset.disjoint_left.1 hBR hv)
  have hmC' : ∀ v ∈ C, mix y' y v = y v := fun v hv ↦
    ite_eq_right (Finset.disjoint_left.1 hCR hv)
  have hiff : ((∀ v ∈ A ∪ B ∪ C, y v = x v) ∧ ∀ v ∈ C, y' v = x v) ↔
      ((∀ v ∈ A ∪ C, mix y y' v = x v) ∧ ∀ v ∈ B ∪ C, mix y' y v = x v) := by
    simp only [Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
      · rcases hv with hv | hv
        · rw [hmA v hv]; exact h1 v (Or.inl (Or.inl hv))
        · rw [hmC v hv]; exact h2 v hv
      · rcases hv with hv | hv
        · rw [hmB' v hv]; exact h1 v (Or.inl (Or.inr hv))
        · rw [hmC' v hv]; exact h1 v (Or.inr hv)
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
      · rcases hv with (hv | hv) | hv
        · rw [← hmA v hv]; exact h1 v (Or.inl hv)
        · rw [← hmB' v hv]; exact h2 v (Or.inl hv)
        · rw [← hmC' v hv]; exact h2 v (Or.inr hv)
      · rw [← hmC v hv]; exact h1 v (Or.inr hv)
  by_cases hc : (∀ v ∈ A ∪ B ∪ C, y v = x v) ∧ ∀ v ∈ C, y' v = x v
  · have hc' := hiff.1 hc
    rw [ite_eq_left hc.1, ite_eq_left hc.2, ite_eq_left hc'.1, ite_eq_left hc'.2]
    have hyy : ∀ v ∈ C, y v = y' v := fun v hv ↦
      (hc.1 v (Finset.mem_union_right _ hv)).trans (hc.2 v hv).symm
    have e1 : F (mix y y') = F y := hF _ _ fun v hv ↦ by
      rcases hv with hv | hv
      · exact ite_eq_left hv
      · rw [hmC v hv, hyy v hv]
    have e2 : H (mix y y') = H y' := hH _ _ fun v hv ↦ ite_eq_right hv
    have e3 : F (mix y' y) = F y' := hF _ _ fun v hv ↦ by
      rcases hv with hv | hv
      · exact ite_eq_left hv
      · rw [hmC' v hv, hyy v hv]
    have e4 : H (mix y' y) = H y := hH _ _ fun v hv ↦ ite_eq_right hv
    rw [hg, hg, hg, hg, e1, e2, e3, e4]
    ring
  · have hc' := mt hiff.2 hc
    have l0 : (if ∀ v ∈ A ∪ B ∪ C, y v = x v then g y else 0) *
        (if ∀ v ∈ C, y' v = x v then g y' else 0) = 0 := by
      by_cases h1 : ∀ v ∈ A ∪ B ∪ C, y v = x v
      · rw [ite_eq_right fun h2 ↦ hc ⟨h1, h2⟩, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    have r0 : (if ∀ v ∈ A ∪ C, mix y y' v = x v then g (mix y y') else 0) *
        (if ∀ v ∈ B ∪ C, mix y' y v = x v then g (mix y' y) else 0) = 0 := by
      by_cases h1 : ∀ v ∈ A ∪ C, mix y y' v = x v
      · rw [ite_eq_right fun h2 ↦ hc' ⟨h1, h2⟩, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    rw [l0, r0]




/-- GAPS 105.62 (core step): a mass function that factorizes recursively along a directed
acyclic graph, with local masses respecting the parents, satisfies the global directed Markov
property: d-separation of disjoint sets implies conditional independence. -/
theorem condIndepMass_directedFactorizationMass_of_dSeparated [Fintype V] [Fintype S]
    (G : CausalGraph V) (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (A B C : Finset V) (_hAB : Disjoint A B)
    (hAC : Disjoint A C) (hBC : Disjoint B C) (hsep : G.DSeparated ↑A ↑B ↑C) :
    CondIndepMass (directedFactorizationMass localMass) A B C := by
  intro x
  -- the ancestral closure of `A ∪ B ∪ C`
  let D : Finset V := Finset.univ.filter fun v ↦ ∃ t ∈ A ∪ B ∪ C, t = v ∨ G.IsDescendant v t
  have hDpar : ∀ v ∈ D, ∀ u, G.edge u v → u ∈ D := by
    intro v hv u huv
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨t, ht, rfl | hvt⟩ := hv
    · exact ⟨t, ht, Or.inr (Relation.TransGen.single huv)⟩
    · exact ⟨t, ht, Or.inr (Relation.TransGen.head huv hvt)⟩
  have hUcl : ∀ w ∈ Dᶜ, ∀ c, G.edge w c → c ∈ Dᶜ := by
    intro w hw c hc
    exact Finset.mem_compl.2 fun hcD ↦ (Finset.mem_compl.1 hw) (hDpar c hcD w hc)
  have hABCD : A ∪ B ∪ C ⊆ D := fun t ht ↦ by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, ht, Or.inl rfl⟩
  let g : (V → S) → ℝ := fun y ↦
    if ∀ v ∈ Dᶜ, y v = x v then ∏ v ∈ Dᶜᶜ, localMass v y (y v) else 0
  have hmarg : ∀ E, E ⊆ A ∪ B ∪ C →
      marginalMass (directedFactorizationMass localMass) E x =
        ∑ y, if ∀ v ∈ E, y v = x v then g y else 0 := by
    intro E hE
    unfold marginalMass directedFactorizationMass
    rw [sum_ite_prod_eq_sum_ite_prod_compl G localMass hloc hpar x E Dᶜ hUcl
      (Finset.disjoint_left.2 fun v hv hv' ↦ (Finset.mem_compl.1 hv') (hABCD (hE hv)))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [g]
    rw [ite_and]
  -- the vertices reachable from `A` by trails with noncolliders outside `C`, colliders in `D`
  let R : Finset V := Finset.univ.filter fun w ↦ w ∈ D ∧ w ∉ C ∧
    ∃ (n : ℕ) (q : ℕ → V), G.IsTrailWith (fun v ↦ v ∈ D) (fun v ↦ v ∉ C) n q ∧ q 0 ∈ A ∧
      q n = w
  have hRD : ∀ w ∈ R, w ∈ D := fun w hw ↦ (Finset.mem_filter.1 hw).2.1
  have hRC : ∀ w ∈ R, w ∉ C := fun w hw ↦ (Finset.mem_filter.1 hw).2.2.1
  have hext : ∀ u w, u ∈ R → w ∈ D → w ∉ C → G.Adjacent u w → w ∈ R := by
    intro u w hu hwD hwC hadj
    obtain ⟨huD, huC, n, q, hq, h0, rfl⟩ := (Finset.mem_filter.1 hu).2
    obtain ⟨q', hq', hq'q, hq'n⟩ := hq.snoc hadj fun _ ↦ by
      unfold CausalGraph.TripleStatus
      split_ifs
      exacts [huD, huC]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hwD, hwC, n + 1, q', hq',
      (hq'q 0 (Nat.zero_le _)).symm ▸ h0, hq'n⟩
  have hext2 : ∀ u v w, u ∈ R → v ∈ D → w ∈ D → w ∉ C → G.edge u v → G.edge w v → w ∈ R := by
    intro u v w hu hvD hwD hwC huv hwv
    obtain ⟨huD, huC, n, q, hq, h0, rfl⟩ := (Finset.mem_filter.1 hu).2
    obtain ⟨q', hq', hq'q, hq'n⟩ := hq.snoc (Or.inl huv) fun _ ↦ by
      unfold CausalGraph.TripleStatus
      split_ifs
      exacts [huD, huC]
    obtain ⟨q'', hq'', hq''q, hq''n⟩ := hq'.snoc (w := w) (by rw [hq'n]; exact Or.inr hwv)
      fun _ ↦ by
        unfold CausalGraph.TripleStatus
        rw [Nat.add_sub_cancel, hq'q n le_rfl, hq'n, ite_eq_left ⟨huv, hwv⟩]
        exact hvD
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hwD, hwC, n + 1 + 1, q'', hq'', ?_, hq''n⟩
    rw [hq''q 0 (Nat.zero_le _), hq'q 0 (Nat.zero_le _)]
    exact h0
  -- families split between `R ∪ C` and the complement of `R`
  let famOK : V → Prop := fun v ↦ (v ∈ R ∨ v ∈ C) ∧ ∀ u, G.edge u v → u ∈ R ∨ u ∈ C
  have hfam : ∀ v ∈ D, ¬ famOK v → v ∉ R ∧ ∀ u, G.edge u v → u ∉ R := by
    intro v hv hnot
    simp only [famOK, not_and_or, not_or, not_forall] at hnot
    rcases hnot with ⟨hvR, hvC⟩ | ⟨w, hwv, hwR, hwC⟩
    · exact ⟨hvR, fun u huv huR ↦ hvR (hext u v huR hv hvC (Or.inl huv))⟩
    · have hwD := hDpar v hv w hwv
      exact ⟨fun hvR ↦ hwR (hext v w hvR hwD hwC (Or.inr hwv)),
        fun u huv huR ↦ hwR (hext2 u v w huR hv hwD hwC huv hwv)⟩
  let F : (V → S) → ℝ := fun y ↦ ∏ v ∈ D.filter famOK, localMass v y (y v)
  let H : (V → S) → ℝ := fun y ↦ (if ∀ v ∈ Dᶜ, y v = x v then 1 else 0) *
    ∏ v ∈ D.filter (fun v ↦ ¬ famOK v), localMass v y (y v)
  have hg : ∀ y, g y = F y * H y := by
    intro y
    simp only [g, F, H, compl_compl]
    rw [← Finset.prod_filter_mul_prod_filter_not D famOK]
    split_ifs <;> ring
  have hF : ∀ y y', (∀ v, v ∈ R ∨ v ∈ C → y v = y' v) → F y = F y' := by
    intro y y' hyy
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    have hv' := (Finset.mem_filter.1 hv).2
    rw [hyy v hv'.1, hpar v y y' fun u hu ↦ hyy u (hv'.2 u hu)]
  have hH : ∀ y y', (∀ v, v ∉ R → y v = y' v) → H y = H y' := by
    intro y y' hyy
    simp only [H]
    congr 1
    · have : (∀ v ∈ Dᶜ, y v = x v) ↔ ∀ v ∈ Dᶜ, y' v = x v := by
        refine forall₂_congr fun v hv ↦ ?_
        rw [hyy v fun hR ↦ (Finset.mem_compl.1 hv) (hRD v hR)]
      simp only [this]
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      obtain ⟨hvD, hv'⟩ := Finset.mem_filter.1 hv
      obtain ⟨hvR, hpR⟩ := hfam v hvD hv'
      rw [hyy v hvR, hpar v y y' fun u hu ↦ hyy u (hpR u hu)]
  have hAR : A ⊆ R := by
    intro a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hABCD (by simp [ha]),
      Finset.disjoint_left.1 hAC ha, 0, fun _ ↦ a, ⟨fun k hk ↦ absurd hk (Nat.not_lt_zero _),
        fun k hk ↦ by omega⟩, ha, rfl⟩
  have hBR : Disjoint B R := by
    refine Finset.disjoint_left.2 fun b hb hbR ↦ ?_
    obtain ⟨-, -, n, q, hq, h0, hn⟩ := (Finset.mem_filter.1 hbR).2
    refine G.false_of_dSeparated_of_semiActiveTrail (A := ↑A) (B := ↑B) (C := ↑C) (D := ↑D)
      hsep (fun a ha ↦ Finset.disjoint_left.1 hAC ha) (fun b hb ↦ Finset.disjoint_left.1 hBC hb)
      ?_ hq h0 (by rw [hn]; exact hb)
    intro v hv hcl
    simp only [D, Finset.coe_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨t, ht, ht'⟩ := hv
    rcases Finset.mem_union.1 ht with ht | ht
    · exact ⟨t, by simpa using ht, ht'⟩
    · exact absurd ⟨t, ht, ht'.imp (fun h ↦ h) fun h ↦ h⟩ hcl
  have hCR : Disjoint C R := Finset.disjoint_left.2 fun c hc hcR ↦ hRC c hcR hc
  have sub : ∀ v, v ∈ A ∪ B ∪ C ↔ v ∈ A ∨ v ∈ B ∨ v ∈ C := by simp
  rw [hmarg _ le_rfl, hmarg C (fun v hv ↦ (sub v).2 (by tauto)),
    hmarg (A ∪ C) (fun v hv ↦ (sub v).2 (by simp only [Finset.mem_union] at hv; tauto)),
    hmarg (B ∪ C) (fun v hv ↦ (sub v).2 (by simp only [Finset.mem_union] at hv; tauto))]
  exact sum_ite_mul_sum_ite_of_factor g F H A B C R x hg hF hH hAR hBR hCR

/-! ### Marginal and interventional masses -/

/-- A marginal mass depends only on the values of the point at the fixed coordinates. -/
theorem marginalMass_congr_point [Fintype V] [Fintype S] (p : (V → S) → ℝ) (E : Finset V)
    {x x' : V → S} (h : ∀ v ∈ E, x v = x' v) : marginalMass p E x = marginalMass p E x' := by
  unfold marginalMass
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v ∈ E, y v = x v) ↔ ∀ v ∈ E, y v = x' v :=
    forall₂_congr fun v hv ↦ by rw [h v hv]
  simp only [this]

/-- Marginal masses of a nonnegative mass function are nonnegative. -/
theorem marginalMass_nonneg [Fintype V] [Fintype S] {p : (V → S) → ℝ} (hp : ∀ y, 0 ≤ p y)
    (E : Finset V) (x : V → S) : 0 ≤ marginalMass p E x :=
  Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact hp y
    · exact le_rfl

/-- Marginal masses decrease when more coordinates are fixed. -/
theorem marginalMass_anti [Fintype V] [Fintype S] {p : (V → S) → ℝ} (hp : ∀ y, 0 ≤ p y)
    {E F : Finset V} (hEF : E ⊆ F) (x : V → S) : marginalMass p F x ≤ marginalMass p E x := by
  unfold marginalMass
  refine Finset.sum_le_sum fun y _ ↦ ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (fun v hv ↦ h1 v (hEF hv)) h2
  · exact hp y
  · exact le_rfl

/-- Fixing coordinates on which the mass is concentrated does not change a marginal mass. -/
theorem marginalMass_union_of_support [Fintype V] [Fintype S] {p : (V → S) → ℝ}
    {X : Finset V} {x : V → S} (hsupp : ∀ y, p y ≠ 0 → ∀ v ∈ X, y v = x v) (E : Finset V) :
    marginalMass p (E ∪ X) x = marginalMass p E x := by
  unfold marginalMass
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : p y = 0
  · simp [hy]
  · have hX := hsupp y hy
    have : (∀ v ∈ E ∪ X, y v = x v) ↔ ∀ v ∈ E, y v = x v :=
      ⟨fun h v hv ↦ h v (Finset.mem_union_left _ hv),
        fun h v hv ↦ (Finset.mem_union.1 hv).elim (h v) (hX v)⟩
    simp only [this]

/-- `overwriteOn` leaves the coordinates outside the overwritten set unchanged. -/
theorem overwriteOn_of_notMem {B : Finset V} (b : B → S) (x : V → S) {v : V} (hv : v ∉ B) :
    overwriteOn B b x v = x v := by
  simp [overwriteOn, hv]

/-- `overwriteOn` with the values of the configuration itself does nothing. -/
theorem overwriteOn_self (B : Finset V) (x : V → S) : overwriteOn B (fun v ↦ x v) x = x := by
  funext v
  unfold overwriteOn
  split_ifs <;> rfl

/-- The law of total probability: a marginal mass is the sum, over the values of a disjoint
set `Z` of variables, of the marginal masses with `Z` fixed as well. -/
theorem marginalMass_eq_sum_overwriteOn [Fintype V] [Fintype S] (p : (V → S) → ℝ)
    {E Z : Finset V} (hEZ : Disjoint E Z) (x : V → S) :
    marginalMass p E x = ∑ z : Z → S, marginalMass p (E ∪ Z) (overwriteOn Z z x) := by
  unfold marginalMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have key : ∀ z : Z → S, (∀ v ∈ E ∪ Z, y v = overwriteOn Z z x v) ↔
      ((∀ v ∈ E, y v = x v) ∧ z = fun v : Z ↦ y v) := by
    intro z
    constructor
    · intro h
      refine ⟨fun v hv ↦ ?_, funext fun v ↦ ?_⟩
      · have := h v (Finset.mem_union_left _ hv)
        rwa [overwriteOn_of_notMem _ _ (Finset.disjoint_left.1 hEZ hv)] at this
      · have := h v (Finset.mem_union_right _ v.2)
        simp only [overwriteOn, v.2, dite_true] at this
        exact this.symm
    · rintro ⟨h, rfl⟩ v hv
      unfold overwriteOn
      split_ifs with hvZ
      · rfl
      · exact h v ((Finset.mem_union.1 hv).resolve_right hvZ)
  simp only [key, ite_and]
  split_ifs with hE
  · simp
  · simp

/-- Interventional masses depend only on the intervention values on the intervened set. -/
theorem interventionMass_congr [Fintype V] (localMass : V → (V → S) → S → ℝ) (A : Finset V)
    {a a' : V → S} (h : ∀ v ∈ A, a v = a' v) :
    interventionMass localMass A a = interventionMass localMass A a' := by
  funext y
  unfold interventionMass
  have : (∀ v ∈ A, y v = a v) ↔ ∀ v ∈ A, y v = a' v :=
    forall₂_congr fun v hv ↦ by rw [h v hv]
  simp only [this]

/-- The empty intervention leaves the recursive product mass unchanged. -/
theorem interventionMass_empty [Fintype V] (localMass : V → (V → S) → S → ℝ) (a : V → S) :
    interventionMass localMass ∅ a = directedFactorizationMass localMass := by
  funext y
  simp [interventionMass, directedFactorizationMass]

/-- Local masses after the intervention `do(X = b)`: point masses at the values of `b` on `X`,
the original local masses elsewhere. -/
def intervenedLocalMass (localMass : V → (V → S) → S → ℝ) (X : Finset V) (b : V → S) :
    V → (V → S) → S → ℝ :=
  fun v y s ↦ if v ∈ X then (if s = b v then 1 else 0) else localMass v y s

/-- Intervened local masses form a local mass family. -/
theorem isLocalMassFamily_intervenedLocalMass [Fintype S] {localMass : V → (V → S) → S → ℝ}
    (hloc : IsLocalMassFamily localMass) (X : Finset V) (b : V → S) :
    IsLocalMassFamily (intervenedLocalMass localMass X b) := by
  refine ⟨fun v y s ↦ ?_, fun v y ↦ ?_⟩
  · unfold intervenedLocalMass
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact hloc.1 v y s
  · unfold intervenedLocalMass
    split_ifs
    · simp
    · exact hloc.2 v y

/-- Intervened local masses respect the parents in the graph with the arrows into `X`
removed. -/
theorem respectsParents_intervenedLocalMass (G : CausalGraph V)
    {localMass : V → (V → S) → S → ℝ} (hpar : G.RespectsParents localMass) (X : Finset V)
    (b : V → S) : (G.removeIncoming ↑X).RespectsParents (intervenedLocalMass localMass X b) := by
  intro v x y h
  unfold intervenedLocalMass
  by_cases hv : v ∈ X
  · simp [hv]
  · have : localMass v x = localMass v y := hpar v x y fun u hu ↦ h u ⟨hu, hv⟩
    funext s
    simp [hv, this]

/-- The truncated factorization is the recursive product of the intervened local masses. -/
theorem directedFactorizationMass_intervenedLocalMass [Fintype V]
    (localMass : V → (V → S) → S → ℝ) (X : Finset V) (b : V → S) :
    directedFactorizationMass (intervenedLocalMass localMass X b) =
      interventionMass localMass X b := by
  funext y
  unfold directedFactorizationMass interventionMass intervenedLocalMass
  have h1 : ∏ v ∈ X, (if v ∈ X then (if y v = b v then (1 : ℝ) else 0)
      else localMass v y (y v)) = if ∀ v ∈ X, y v = b v then 1 else 0 := by
    calc ∏ v ∈ X, (if v ∈ X then (if y v = b v then (1 : ℝ) else 0) else localMass v y (y v))
        = ∏ v ∈ X, (if y v = b v then (1 : ℝ) else 0) :=
          Finset.prod_congr rfl fun v hv ↦ ite_eq_left hv
      _ = _ := by convert Finset.prod_boole ..
  have h2 : ∏ v ∈ Xᶜ, (if v ∈ X then (if y v = b v then (1 : ℝ) else 0)
      else localMass v y (y v)) = ∏ v ∈ Xᶜ, localMass v y (y v) :=
    Finset.prod_congr rfl fun v hv ↦ ite_eq_right (Finset.mem_compl.1 hv)
  rw [← Finset.prod_mul_prod_compl X, h1, h2]
  split_ifs <;> simp

/-- Intervening on `X` after intervening on `Z` is intervening on `X ∪ Z`. -/
theorem interventionMass_intervenedLocalMass [Fintype V] (localMass : V → (V → S) → S → ℝ)
    (X Z : Finset V) (b : V → S) :
    interventionMass (intervenedLocalMass localMass Z b) X b =
      interventionMass localMass (X ∪ Z) b := by
  rw [← directedFactorizationMass_intervenedLocalMass,
    ← directedFactorizationMass_intervenedLocalMass]
  congr 1
  funext v y s
  by_cases h1 : v ∈ X <;> by_cases h2 : v ∈ Z <;> simp [intervenedLocalMass, h1, h2]

/-- Interventional masses are nonnegative. -/
theorem interventionMass_nonneg [Fintype V] [Fintype S] {localMass : V → (V → S) → S → ℝ}
    (hloc : IsLocalMassFamily localMass) (X : Finset V) (a y : V → S) :
    0 ≤ interventionMass localMass X a y := by
  unfold interventionMass
  split_ifs
  · exact Finset.prod_nonneg fun v _ ↦ hloc.1 v y (y v)
  · exact le_rfl

/-- The interventional mass under `do(X = a)` is concentrated on the configurations that agree
with `a` on `X`. -/
theorem interventionMass_support [Fintype V] {localMass : V → (V → S) → S → ℝ}
    {X : Finset V} {a y : V → S} (h : interventionMass localMass X a y ≠ 0) :
    ∀ v ∈ X, y v = a v := by
  unfold interventionMass at h
  by_contra hc
  rw [ite_eq_right hc] at h
  exact h rfl

/-- Recursive product masses are nonnegative. -/
theorem directedFactorizationMass_nonneg [Fintype V] [Fintype S]
    {localMass : V → (V → S) → S → ℝ} (hloc : IsLocalMassFamily localMass) (y : V → S) :
    0 ≤ directedFactorizationMass localMass y :=
  Finset.prod_nonneg fun v _ ↦ hloc.1 v y (y v)

/-- A recursive product of local masses has total mass one. -/
theorem marginalMass_empty_directedFactorizationMass [Fintype V] [Fintype S]
    (G : CausalGraph V) {localMass : V → (V → S) → S → ℝ} (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (x : V → S) :
    marginalMass (directedFactorizationMass localMass) ∅ x = 1 := by
  unfold marginalMass directedFactorizationMass
  rw [sum_ite_prod_eq_sum_ite_prod_compl G localMass hloc hpar x ∅ Finset.univ
    (fun _ _ _ _ ↦ Finset.mem_univ _) (Finset.disjoint_empty_left _)]
  have : ∀ y : V → S, ((∀ v ∈ (∅ : Finset V), y v = x v) ∧ ∀ v ∈ Finset.univ, y v = x v) ↔
      y = x := by
    intro y
    simp [funext_iff]
  simp only [this]
  simp

/-- An interventional mass has total mass one. -/
theorem marginalMass_empty_interventionMass [Fintype V] [Fintype S] (G : CausalGraph V)
    {localMass : V → (V → S) → S → ℝ} (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X : Finset V) (a x : V → S) :
    marginalMass (interventionMass localMass X a) ∅ x = 1 := by
  rw [← directedFactorizationMass_intervenedLocalMass]
  exact marginalMass_empty_directedFactorizationMass (G.removeIncoming ↑X)
    (isLocalMassFamily_intervenedLocalMass hloc X a) (respectsParents_intervenedLocalMass G hpar X a) x

/-- Conditional independence `Y ⊥ Z | X ∪ W`, for a mass concentrated on one value of `X`,
in quotient form: `P(y | z, w) = P(y | w)`. -/
theorem div_eq_div_of_condIndepMass [Fintype V] [Fintype S] {p : (V → S) → ℝ}
    (hp : ∀ y, 0 ≤ p y) {X Y Z W : Finset V} {b : V → S}
    (hsupp : ∀ y, p y ≠ 0 → ∀ v ∈ X, y v = b v) (hci : CondIndepMass p Y Z (X ∪ W))
    (hpos : 0 < marginalMass p (Z ∪ W) b) :
    marginalMass p (Y ∪ (Z ∪ W)) b / marginalMass p (Z ∪ W) b =
      marginalMass p (Y ∪ W) b / marginalMass p W b := by
  have h := hci b
  have e1 : Y ∪ Z ∪ (X ∪ W) = (Y ∪ (Z ∪ W)) ∪ X := by
    ext v; simp only [Finset.mem_union]; tauto
  have e3 : Y ∪ (X ∪ W) = (Y ∪ W) ∪ X := by
    ext v; simp only [Finset.mem_union]; tauto
  have e4 : Z ∪ (X ∪ W) = (Z ∪ W) ∪ X := by
    ext v; simp only [Finset.mem_union]; tauto
  have e2 : X ∪ W = W ∪ X := Finset.union_comm _ _
  rw [e1, e3, e4, e2, marginalMass_union_of_support hsupp, marginalMass_union_of_support hsupp,
    marginalMass_union_of_support hsupp, marginalMass_union_of_support hsupp] at h
  have hW : 0 < marginalMass p W b :=
    lt_of_lt_of_le hpos (marginalMass_anti hp Finset.subset_union_right b)
  rw [div_eq_div_iff hpos.ne' hW.ne']
  exact h

/-- The interventional marginal of variables that are neither in `X` nor descendants of `X`
equals their observational marginal. -/
theorem doMarginalMass_eq_marginalMass_of_nonDescendant [Fintype V] [Fintype S]
    (G : CausalGraph V) (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X E : Finset V) (a x : V → S)
    (hE : ∀ v ∈ E, v ∉ X ∧ ∀ u ∈ X, ¬ G.IsDescendant u v) :
    doMarginalMass localMass X a E x = marginalMass (directedFactorizationMass localMass) E x := by
  let U : Finset V := Finset.univ.filter fun v ↦ ∃ u ∈ X, u = v ∨ G.IsDescendant u v
  have hclG : ∀ w ∈ U, ∀ c, G.edge w c → c ∈ U := by
    intro w hw c hc
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨u, hu, rfl | huw⟩ := hw
    · exact ⟨u, hu, Or.inr (Relation.TransGen.single hc)⟩
    · exact ⟨u, hu, Or.inr (Relation.TransGen.tail huw hc)⟩
  have hclX : ∀ w ∈ U, ∀ c, (G.removeIncoming ↑X).edge w c → c ∈ U :=
    fun w hw c hc ↦ hclG w hw c hc.1
  have hEU : Disjoint E U := Finset.disjoint_left.2 fun v hv hvU ↦ by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hvU
    obtain ⟨u, hu, rfl | huv⟩ := hvU
    · exact (hE u hv).1 hu
    · exact (hE v hv).2 u hu huv
  change marginalMass (interventionMass localMass X a) E x = _
  rw [← directedFactorizationMass_intervenedLocalMass]
  unfold marginalMass directedFactorizationMass
  rw [sum_ite_prod_eq_sum_ite_prod_compl (G.removeIncoming ↑X) _
      (isLocalMassFamily_intervenedLocalMass hloc X a)
      (respectsParents_intervenedLocalMass G hpar X a) x E U hclX hEU,
    sum_ite_prod_eq_sum_ite_prod_compl G localMass hloc hpar x E U hclG hEU]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    have hvX : v ∉ X := fun h ↦ (Finset.mem_compl.1 hv)
      (by simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨v, h, Or.inl rfl⟩)
    simp only [intervenedLocalMass, hvX, ite_false]
  · rfl

/-! ### Graph surgery and d-separation -/

/-- An active path in a subgraph is active in the graph. -/
theorem CausalGraph.IsActivePath.mono {G H : CausalGraph V} (hle : ∀ u v, H.edge u v → G.edge u v)
    {Z : Set V} {n : ℕ} {p : Fin (n + 1) → V} (h : H.IsActivePath Z p) : G.IsActivePath Z p := by
  obtain ⟨hinj, hadj, htri⟩ := h
  refine ⟨hinj, fun i ↦ (hadj i).imp (hle _ _) (hle _ _), fun i ↦ ?_⟩
  have ht := htri i
  have hab := hadj ⟨i.val, by omega⟩
  have hbc := hadj ⟨i.val + 1, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at ht hab hbc ⊢
  by_cases hH : H.edge (p ⟨i.val, by omega⟩) (p ⟨i.val + 1, by omega⟩) ∧
      H.edge (p ⟨i.val + 2, by omega⟩) (p ⟨i.val + 1, by omega⟩)
  · rw [ite_eq_left hH] at ht
    rw [ite_eq_left ⟨hle _ _ hH.1, hle _ _ hH.2⟩]
    obtain ⟨z, hz, hz'⟩ := ht
    exact ⟨z, hz, hz'.imp id fun h ↦ Relation.TransGen.mono hle _ _ h⟩
  · rw [ite_eq_right hH] at ht
    rw [ite_eq_right]
    · exact ht
    rintro ⟨h1, h2⟩
    apply hH
    constructor
    · rcases hab with h | h
      · exact h
      · exact absurd (hle _ _ h) (G.not_edge_of_edge h1)
    · rcases hbc with h | h
      · exact absurd (hle _ _ h) (G.not_edge_of_edge h2)
      · exact h

/-- If every back-door path from `X` to `Y` is blocked by `W`, then in any subgraph with the
arrows out of `X` removed, `Y` and `X` are d-separated by `W`. -/
theorem CausalGraph.dSeparated_removeOutgoing_of_blocksBackdoorPaths (G H : CausalGraph V)
    (hle : ∀ u v, H.edge u v → G.edge u v) {X Y W : Set V} (hXY : Disjoint X Y)
    (hb : G.BlocksBackdoorPaths X Y W) : (H.removeOutgoing X).DSeparated Y X W := by
  intro n p h0 hn hp
  rcases n with _ | n
  · have : p 0 ∈ X := by simpa using hn
    exact Set.disjoint_left.1 hXY this h0
  · have hrev := hp.rev
    have hG := hrev.mono (G := G) (H := H.removeOutgoing X) fun u v h ↦ hle u v h.1
    refine hb n (p ∘ Fin.rev) (by simpa using hn) (by simpa using h0) ?_ hG
    have hadj := hrev.2.1 0
    simp only [Function.comp_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one] at hadj
    rcases hadj with h | h
    · exact absurd (by simpa using hn) h.2
    · simpa using hle _ _ h.1

/-- If every back-door path from `X` to `Z` is blocked by the empty set, then no vertex of `X`
is a descendant of a vertex of `Z`. -/
theorem CausalGraph.not_isDescendant_of_blocksBackdoorPaths (G : CausalGraph V)
    {X Z : Set V} (hb : G.BlocksBackdoorPaths X Z ∅) :
    ∀ z ∈ Z, ∀ x ∈ X, ¬ G.IsDescendant z x := by
  intro z hz x hx hd
  obtain ⟨m, r, hm, h0, hmx, hf⟩ := G.exists_forward_of_isDescendant hd
  have htr : G.IsTrailWith (G.MemAncestorClosure ∅) (· ∉ (∅ : Set V)) m (fun k ↦ r (m - k)) :=
    (G.isTrailWith_of_forward hf fun i _ _ ↦ Set.notMem_empty _).rev
  have hc : ∀ i j, i < j → j ≤ m → r i ≠ r j := by
    intro i j hij hjm heq
    have := G.isDescendant_of_forward (r := fun k ↦ r (k + i)) (m := m - i)
      (fun k hk ↦ by simpa [Nat.add_right_comm k 1 i] using hf (k + i) (by omega))
      (j - i) (by omega) (by omega)
    simp only [zero_add, Nat.sub_add_cancel hij.le] at this
    rw [heq] at this
    exact G.acyclic _ this
  have hinj : ∀ i ≤ m, ∀ j ≤ m, r (m - i) = r (m - j) → i = j := by
    intro i hi j hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hc (m - j) (m - i) (by omega) (by omega) h.symm
    · exact hc (m - i) (m - j) (by omega) (by omega) h
  have hpath := G.isActivePath_of_isTrailWith htr hinj
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine hb n (fun i ↦ r (n + 1 - i)) (by simpa [hmx] using hx) (by simpa [h0] using hz) ?_ hpath
  simpa using hf n (by omega)

/-- If `Z` intercepts all directed paths from `X` to `Y`, then in the graph with the arrows
into `Z` removed no vertex of `Y` is a descendant of a vertex of `X`. -/
theorem CausalGraph.not_isDescendant_removeIncoming_of_intercepts (G : CausalGraph V)
    {X Y Z : Set V} (hXZ : Disjoint X Z) (hi : G.InterceptsDirectedPaths X Y Z) :
    ∀ v ∈ Y, ∀ u ∈ X, ¬ (G.removeIncoming Z).IsDescendant u v := by
  intro v hv u hu hd
  obtain ⟨m, r, hm, h0, hmv, hf⟩ := (G.removeIncoming Z).exists_forward_of_isDescendant hd
  obtain ⟨i, hi'⟩ := hi m (fun i ↦ r i) (by simpa [h0] using hu) (by simpa [hmv] using hv)
    fun i ↦ by simpa using (hf i i.isLt).1
  rcases Nat.eq_zero_or_pos i.val with h | h
  · simp only [h, h0] at hi'
    exact Set.disjoint_left.1 hXZ hu hi'
  · have := (hf (i.val - 1) (by omega)).2
    rw [Nat.sub_add_cancel h] at this
    exact this hi'

/-! ### The global Markov property and the rules of the do-calculus -/


/-- Action/observation exchange (rule 2 of the do-calculus) under the single positivity
condition `P(z, w | do(x)) > 0`: if `Y` and `Z` are d-separated by `X ∪ W` in
`G_{\bar X \underline Z}`, then `P(y | do(x), do(z), w) = P(y | do(x), z, w)`.

The proof compares both sides with the mass in which the children of `Z` read the fixed values
of `b` on `Z`; that mass factorizes along `G_{\bar X \underline Z}`. -/
theorem condDoMass_union_eq_of_dSeparated [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z W : Finset V)
    (hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint X W ∧ Disjoint Y Z ∧ Disjoint Y W ∧
      Disjoint Z W)
    (hsep : ((G.removeIncoming X).removeOutgoing Z).DSeparated Y Z ↑(X ∪ W)) (b : V → S)
    (hpos : 0 < doMarginalMass localMass X b (Z ∪ W) b) :
    condDoMass localMass (X ∪ Z) Y W b = condDoMass localMass X Y (Z ∪ W) b := by
  obtain ⟨hXY, hXZ, hXW, hYZ, hYW, hZW⟩ := hdisj
  set G2 := (G.removeIncoming ↑X).removeOutgoing ↑Z with hG2
  let ow : (V → S) → V → S := fun y u ↦ if u ∈ Z then b u else y u
  let rloc : V → (V → S) → S → ℝ := fun v y s ↦ intervenedLocalMass localMass X b v (ow y) s
  have hloc' := isLocalMassFamily_intervenedLocalMass hloc X b
  have hrloc : IsLocalMassFamily rloc :=
    ⟨fun v y s ↦ hloc'.1 v _ s, fun v y ↦ hloc'.2 v _⟩
  have hrpar : G2.RespectsParents rloc := by
    intro v y y' h
    show intervenedLocalMass localMass X b v (ow y) = intervenedLocalMass localMass X b v (ow y')
    apply respectsParents_intervenedLocalMass G hpar X b v
    intro u hu
    simp only [ow]
    split_ifs with huZ
    · rfl
    · exact h u ⟨hu, huZ⟩
  let r := directedFactorizationMass rloc
  let q := interventionMass localMass X b
  have how : ∀ y, (∀ v ∈ Z, y v = b v) → ow y = y := fun y hy ↦ funext fun u ↦ by
    simp only [ow]
    split_ifs with hu
    · exact (hy u hu).symm
    · rfl
  have hr_eq : ∀ y, (∀ v ∈ Z, y v = b v) → r y = q y := by
    intro y hy
    simp only [r, q, ← directedFactorizationMass_intervenedLocalMass]
    unfold directedFactorizationMass
    simp only [rloc, how y hy]
  have hmargA : ∀ E, Z ⊆ E → marginalMass r E b = marginalMass q E b := by
    intro E hZE
    unfold marginalMass
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    split_ifs with hy
    · exact hr_eq y fun v hv ↦ hy v (hZE hv)
    · rfl
  have hmargB : ∀ E, Disjoint E Z →
      marginalMass r E b = doMarginalMass localMass (X ∪ Z) b E b := by
    intro E hEZ
    have hcl : ∀ w ∈ Z, ∀ c, G2.edge w c → c ∈ Z := fun w hw c hc ↦ absurd hw hc.2
    unfold marginalMass doMarginalMass
    simp only [r]
    unfold directedFactorizationMass
    rw [sum_ite_prod_eq_sum_ite_prod_compl G2 rloc hrloc hrpar b E Z hcl hEZ]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases hyZ : ∀ v ∈ Z, y v = b v
    · have hprod : ∏ v ∈ Zᶜ, rloc v y (y v) = interventionMass localMass (X ∪ Z) b y := by
        rw [← directedFactorizationMass_intervenedLocalMass]
        unfold directedFactorizationMass
        rw [← Finset.prod_subset (Finset.subset_univ Zᶜ)]
        · refine Finset.prod_congr rfl fun v hv ↦ ?_
          have hvZ : v ∉ Z := Finset.mem_compl.1 hv
          simp only [rloc, how y hyZ, intervenedLocalMass, Finset.mem_union, hvZ, or_false]
        · intro v _ hv
          have hvZ : v ∈ Z := by simpa using hv
          simp [intervenedLocalMass, hvZ, hyZ v hvZ]
      rw [hprod]
      by_cases hE : ∀ v ∈ E, y v = b v
      · rw [ite_eq_left ⟨hE, hyZ⟩, ite_eq_left hE]
      · rw [ite_eq_right fun h ↦ hE h.1, ite_eq_right hE]
    · have h0 : interventionMass localMass (X ∪ Z) b y = 0 := by
        unfold interventionMass
        rw [ite_eq_right]
        intro h
        exact hyZ fun v hv ↦ h v (Finset.mem_union_right _ hv)
      simp only [hyZ, and_false, ite_false, h0, ite_self]
  have hci := condIndepMass_directedFactorizationMass_of_dSeparated G2 rloc hrloc hrpar Y Z
    (X ∪ W) hYZ (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩)
    (Finset.disjoint_union_right.2 ⟨hXZ.symm, hZW⟩) hsep
  have hr0 : ∀ y, 0 ≤ r y := fun y ↦ directedFactorizationMass_nonneg hrloc y
  have hrsupp : ∀ y, r y ≠ 0 → ∀ v ∈ X, y v = b v := by
    intro y hy v hv
    by_contra hne
    apply hy
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simp only [rloc, intervenedLocalMass, hv, ite_true, hne, ite_false]
  have hposr : 0 < marginalMass r (Z ∪ W) b := by
    rw [hmargA _ Finset.subset_union_left]
    exact hpos
  have key := div_eq_div_of_condIndepMass hr0 hrsupp hci hposr
  unfold condDoMass
  rw [← hmargB _ (Finset.disjoint_union_left.2 ⟨hYZ, hZW.symm⟩), ← hmargB _ hZW.symm]
  change _ = marginalMass q (Y ∪ (Z ∪ W)) b / marginalMass q (Z ∪ W) b
  rw [← hmargA _ (fun v hv ↦ by simp [hv]), ← hmargA _ Finset.subset_union_left]
  exact key.symm

/-! ### Directed Markov properties -/

/-- The marginal mass on all variables is the mass itself. -/
theorem marginalMass_univ [Fintype V] [Fintype S] (p : (V → S) → ℝ) (x : V → S) :
    marginalMass p Finset.univ x = p x := by
  unfold marginalMass
  have : ∀ y : V → S, (∀ v ∈ Finset.univ, y v = x v) ↔ y = x := fun y ↦ by simp [funext_iff]
  simp only [this]
  simp

/-- The decomposition property of conditional independence: `A ⊥ B | C` implies
`A ⊥ B' | C` for `B' ⊆ B`. -/
theorem CondIndepMass.mono_right [Fintype V] [Fintype S] {p : (V → S) → ℝ}
    {A B B' C : Finset V} (h : CondIndepMass p A B C) (hB' : B' ⊆ B) (hAB : Disjoint A B)
    (hBC : Disjoint B C) : CondIndepMass p A B' C := by
  intro x
  have hZ1 : Disjoint (A ∪ B' ∪ C) (B \ B') := by
    refine Finset.disjoint_left.2 fun v hv hvZ ↦ ?_
    obtain ⟨hvB, hvB'⟩ := Finset.mem_sdiff.1 hvZ
    rcases Finset.mem_union.1 hv with hv | hv
    · rcases Finset.mem_union.1 hv with hv | hv
      · exact Finset.disjoint_left.1 hAB hv hvB
      · exact hvB' hv
    · exact Finset.disjoint_left.1 hBC hvB hv
  have hZ2 : Disjoint (B' ∪ C) (B \ B') := by
    refine Finset.disjoint_left.2 fun v hv hvZ ↦ ?_
    obtain ⟨hvB, hvB'⟩ := Finset.mem_sdiff.1 hvZ
    rcases Finset.mem_union.1 hv with hv | hv
    · exact hvB' hv
    · exact Finset.disjoint_left.1 hBC hvB hv
  have e1 : A ∪ B' ∪ C ∪ B \ B' = A ∪ B ∪ C := by
    ext v
    have := @hB' v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have e2 : B' ∪ C ∪ B \ B' = B ∪ C := by
    ext v
    have := @hB' v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [marginalMass_eq_sum_overwriteOn p hZ1 x, marginalMass_eq_sum_overwriteOn p hZ2 x, e1, e2,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hC : marginalMass p C (overwriteOn (B \ B') z x) = marginalMass p C x :=
    marginalMass_congr_point p C fun v hv ↦ overwriteOn_of_notMem _ _ fun hvZ ↦
      Finset.disjoint_left.1 hZ2 (Finset.mem_union_right _ hv) hvZ
  have hAC : marginalMass p (A ∪ C) (overwriteOn (B \ B') z x) = marginalMass p (A ∪ C) x :=
    marginalMass_congr_point p _ fun v hv ↦ overwriteOn_of_notMem _ _ fun hvZ ↦ by
      rcases Finset.mem_union.1 hv with hv | hv
      · exact Finset.disjoint_left.1 hZ1 (by simp [hv]) hvZ
      · exact Finset.disjoint_left.1 hZ1 (by simp [hv]) hvZ
  have := h (overwriteOn (B \ B') z x)
  rw [hC, hAC] at this
  exact this

/-- Summing the marginal mass of `insert v C` over the values of `v`. -/
theorem sum_marginalMass_insert_update [Fintype V] [Fintype S] (p : (V → S) → ℝ) {v : V}
    {C : Finset V} (hv : v ∉ C) (y : V → S) :
    ∑ s, marginalMass p (insert v C) (Function.update y v s) = marginalMass p C y := by
  unfold marginalMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have key : ∀ s, (∀ u ∈ insert v C, w u = Function.update y v s u) ↔
      (w v = s ∧ ∀ u ∈ C, w u = y u) := by
    intro s
    simp only [Finset.mem_insert, forall_eq_or_imp, Function.update_self]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u hu ↦ ?_⟩
      rw [h2 u hu, Function.update_of_ne (show u ≠ v by rintro rfl; exact hv hu)]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u hu ↦ ?_⟩
      rw [Function.update_of_ne (show u ≠ v by rintro rfl; exact hv hu)]
      exact h2 u hu
  simp only [key, ite_and]
  rw [Finset.sum_ite_eq]
  simp

/-- Under the local directed Markov property, the marginal mass of an ancestral set is the
product of the conditional masses of its vertices given their parents. -/
theorem CausalGraph.marginalMass_eq_prod_condMass_of_isLocalDirectedMarkov [Fintype V]
    [Fintype S] (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hLM : G.IsLocalDirectedMarkov p) :
    ∀ D : Finset V, (∀ v ∈ D, ∀ u, G.edge u v → u ∈ D) → ∀ x,
      marginalMass p D x = ∏ v ∈ D, condMass p {v} (G.parentFinset v) x := by
  intro D
  induction D using Finset.strongInduction with
  | H D ih =>
  intro hD x
  rcases D.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.prod_empty]
    unfold marginalMass
    simpa using hp.2
  -- a vertex of `D` without descendants in `D`
  have : IsTrans V (flip (Relation.TransGen G.edge)) :=
    ⟨fun _ _ _ h₁ h₂ ↦ Relation.TransGen.trans h₂ h₁⟩
  have : Std.Irrefl (flip (Relation.TransGen G.edge)) := ⟨G.acyclic⟩
  obtain ⟨v, hvD, hmax⟩ := (Finite.wellFounded_of_trans_of_irrefl
    (flip (Relation.TransGen G.edge))).has_min (D : Set V) hne
  set D' := D.erase v with hD'
  have hD'cl : ∀ w ∈ D', ∀ u, G.edge u w → u ∈ D' := by
    intro w hw u huw
    refine Finset.mem_erase.2 ⟨?_, hD w (Finset.mem_of_mem_erase hw) u huw⟩
    rintro rfl
    exact hmax w (Finset.mem_of_mem_erase hw) (Relation.TransGen.single huw)
  set pa := G.parentFinset v with hpa
  have hmem_pa : ∀ u, u ∈ pa ↔ G.edge u v := fun u ↦ by
    simp [hpa, CausalGraph.parentFinset]
  have hpaD' : pa ⊆ D' := fun u hu ↦ by
    have hu' := (hmem_pa u).1 hu
    exact Finset.mem_erase.2 ⟨fun h ↦ G.not_edge_self v (h ▸ hu'), hD v hvD u hu'⟩
  set B' := D'.filter (fun w ↦ w ∉ pa) with hB'
  have hB'nd : B' ⊆ G.nonDescendantFinset v := by
    intro w hw
    obtain ⟨hwD', hwpa⟩ := Finset.mem_filter.1 hw
    simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.ne_of_mem_erase hwD', fun h ↦ hmax w (Finset.mem_of_mem_erase hwD') h,
      fun h ↦ hwpa ((hmem_pa w).2 h)⟩
  have hdisj1 : Disjoint ({v} : Finset V) (G.nonDescendantFinset v) := by
    simp [CausalGraph.nonDescendantFinset]
  have hdisj2 : Disjoint (G.nonDescendantFinset v) pa := by
    refine Finset.disjoint_left.2 fun u hu hu' ↦ ?_
    simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu
    exact hu.2.2 ((hmem_pa u).1 hu')
  have hci := ((hLM v).mono_right hB'nd hdisj1 hdisj2) x
  have e1 : {v} ∪ B' ∪ pa = D := by
    ext w
    simp only [Finset.mem_union, Finset.mem_singleton, hB', Finset.mem_filter]
    constructor
    · rintro ((rfl | ⟨hw, -⟩) | hw)
      · exact hvD
      · exact Finset.mem_of_mem_erase hw
      · exact Finset.mem_of_mem_erase (hpaD' hw)
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl (Or.inl hwv)
      by_cases hwp : w ∈ pa
      · exact Or.inr hwp
      · exact Or.inl (Or.inr ⟨Finset.mem_erase.2 ⟨hwv, hw⟩, hwp⟩)
  have e2 : B' ∪ pa = D' := by
    ext w
    simp only [Finset.mem_union, hB', Finset.mem_filter]
    constructor
    · rintro (⟨hw, -⟩ | hw)
      · exact hw
      · exact hpaD' hw
    · intro hw
      by_cases hwp : w ∈ pa
      · exact Or.inr hwp
      · exact Or.inl ⟨hw, hwp⟩
  rw [e1, e2] at hci
  have hstep : marginalMass p D x = condMass p {v} pa x * marginalMass p D' x := by
    unfold condMass
    by_cases hz : marginalMass p pa x = 0
    · have h0 : marginalMass p D x = 0 := by
        refine le_antisymm ?_ (marginalMass_nonneg hp.1 D x)
        calc marginalMass p D x ≤ marginalMass p pa x :=
              marginalMass_anti hp.1 (hpaD'.trans (Finset.erase_subset _ _)) x
          _ = 0 := hz
      rw [h0, hz, div_zero, zero_mul]
    · rw [div_mul_eq_mul_div, eq_div_iff hz, ← hci]
  rw [hstep, ih D' (Finset.erase_ssubset hvD) hD'cl x, ← Finset.mul_prod_erase D _ hvD]

/-- The local directed Markov property implies recursive factorization. -/
theorem CausalGraph.recursivelyFactorizes_of_isLocalDirectedMarkov [Fintype V] [Fintype S]
    (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hLM : G.IsLocalDirectedMarkov p) : G.RecursivelyFactorizes p := by
  intro x
  rw [← marginalMass_univ p x]
  exact G.marginalMass_eq_prod_condMass_of_isLocalDirectedMarkov hp hLM Finset.univ
    (fun _ _ _ _ ↦ Finset.mem_univ _) x

/-- A recursively factorizing probability mass function is the recursive product of a local
mass family respecting the parents. -/
theorem CausalGraph.exists_localMass_of_recursivelyFactorizes [Fintype V] [Fintype S]
    (G : CausalGraph V) {p : (V → S) → ℝ} (hp : IsProbabilityMass p)
    (hRF : G.RecursivelyFactorizes p) :
    ∃ localMass : V → (V → S) → S → ℝ, IsLocalMassFamily localMass ∧
      G.RespectsParents localMass ∧ p = directedFactorizationMass localMass := by
  let loc : V → (V → S) → S → ℝ := fun v y s ↦
    if 0 < marginalMass p (G.parentFinset v) y
    then condMass p {v} (G.parentFinset v) (Function.update y v s)
    else (Fintype.card S : ℝ)⁻¹
  have hvpa : ∀ v, v ∉ G.parentFinset v := fun v h ↦ G.not_edge_self v (by
    simpa [CausalGraph.parentFinset] using h)
  have hloc : IsLocalMassFamily loc := by
    refine ⟨fun v y s ↦ ?_, fun v y ↦ ?_⟩
    · simp only [loc]
      split_ifs
      · exact div_nonneg (marginalMass_nonneg hp.1 _ _) (marginalMass_nonneg hp.1 _ _)
      · positivity
    · simp only [loc]
      split_ifs with hpos
      · unfold condMass
        have hden : ∀ s, marginalMass p (G.parentFinset v) (Function.update y v s) =
            marginalMass p (G.parentFinset v) y := fun s ↦
          marginalMass_congr_point p _ fun u hu ↦
            Function.update_of_ne (show u ≠ v by rintro rfl; exact hvpa u hu) _ _
        simp only [hden, ← Finset.sum_div]
        rw [show ({v} : Finset V) ∪ G.parentFinset v = insert v (G.parentFinset v) from
          (Finset.insert_eq _ _).symm, sum_marginalMass_insert_update p (hvpa v) y,
          div_self hpos.ne']
      · have : 0 < Fintype.card S := Fintype.card_pos_iff.2 ⟨y v⟩
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hpar : G.RespectsParents loc := by
    intro v y y' h
    have hpa : ∀ u ∈ G.parentFinset v, y u = y' u := fun u hu ↦
      h u (by simpa [CausalGraph.parentFinset, CausalGraph.parents] using hu)
    funext s
    have hupd : ∀ u ∈ ({v} : Finset V) ∪ G.parentFinset v,
        Function.update y v s u = Function.update y' v s u := by
      intro u hu
      by_cases huv : u = v
      · subst huv
        simp
      · rw [Function.update_of_ne huv, Function.update_of_ne huv]
        exact hpa u ((Finset.mem_union.1 hu).resolve_left (by simpa using huv))
    have hc : condMass p {v} (G.parentFinset v) (Function.update y v s) =
        condMass p {v} (G.parentFinset v) (Function.update y' v s) := by
      unfold condMass
      rw [marginalMass_congr_point p _ hupd,
        marginalMass_congr_point p _ fun u hu ↦ hupd u (Finset.mem_union_right _ hu)]
    simp only [loc, marginalMass_congr_point p _ hpa, hc]
  refine ⟨loc, hloc, hpar, funext fun x ↦ ?_⟩
  have hle : ∀ y, p y ≤ directedFactorizationMass loc y := by
    intro y
    by_cases hy : p y = 0
    · rw [hy]
      exact directedFactorizationMass_nonneg hloc y
    · have hpos : 0 < p y := lt_of_le_of_ne (hp.1 y) (Ne.symm hy)
      refine le_of_eq ?_
      rw [hRF y]
      unfold directedFactorizationMass
      refine Finset.prod_congr rfl fun v _ ↦ ?_
      have : 0 < marginalMass p (G.parentFinset v) y := lt_of_lt_of_le hpos (by
        rw [← marginalMass_univ p y]
        exact marginalMass_anti hp.1 (Finset.subset_univ _) y)
      simp only [loc, ite_eq_left this, Function.update_eq_self]
  have h1 : ∑ y, directedFactorizationMass loc y = 1 := by
    have := marginalMass_empty_directedFactorizationMass G hloc hpar x
    unfold marginalMass at this
    simpa using this
  have hsum : ∑ y, (directedFactorizationMass loc y - p y) = 0 := by
    rw [Finset.sum_sub_distrib, h1, hp.2, sub_self]
  have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ sub_nonneg.2 (hle y)).1 hsum x
    (Finset.mem_univ _)
  linarith

/-- GAPS 105.62: for a probability mass function on finitely many finite-valued variables,
recursive factorization along a directed acyclic graph, the local directed Markov property, and
the global (d-separation) Markov property are equivalent. Discrete-variable form: densities
with respect to counting measure on a finite product. -/
theorem CausalGraph.recursivelyFactorizes_tfae [Fintype V] [Fintype S] (G : CausalGraph V)
    (p : (V → S) → ℝ) (hp : IsProbabilityMass p) :
    (G.RecursivelyFactorizes p ↔ G.IsLocalDirectedMarkov p) ∧
      (G.IsLocalDirectedMarkov p ↔ G.IsGlobalDirectedMarkov p) := by
  have hRF_GM : G.RecursivelyFactorizes p → G.IsGlobalDirectedMarkov p := by
    intro hRF A B C hAB hAC hBC hsep
    obtain ⟨loc, hloc, hpar, rfl⟩ := G.exists_localMass_of_recursivelyFactorizes hp hRF
    exact condIndepMass_directedFactorizationMass_of_dSeparated G loc hloc hpar A B C hAB hAC
      hBC hsep
  have hGM_LM : G.IsGlobalDirectedMarkov p → G.IsLocalDirectedMarkov p := by
    intro hGM v
    have hvpa : v ∉ G.parentFinset v := fun h ↦ G.not_edge_self v (by
      simpa [CausalGraph.parentFinset] using h)
    refine hGM _ _ _ (by simp [CausalGraph.nonDescendantFinset])
      (Finset.disjoint_singleton_left.2 hvpa) ?_ ?_
    · refine Finset.disjoint_left.2 fun u hu hu' ↦ ?_
      simp only [CausalGraph.nonDescendantFinset, CausalGraph.parentFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at hu hu'
      exact hu.2.2 hu'
    · intro n q h0 hn hq
      have hq0 : q 0 = v := by simpa using h0
      have hnd : q (Fin.last n) ∈ G.nonDescendantFinset v := by simpa using hn
      simp only [CausalGraph.nonDescendantFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hnd
      have hcoe : ((G.parentFinset v : Finset V) : Set V) = G.parents v := by
        ext u
        simp [CausalGraph.parentFinset, CausalGraph.parents]
      rw [hcoe] at hq
      exact G.dSeparated_parents_of_not_isDescendant (Ne.symm hnd.1) hnd.2.2 hnd.2.1 n q
        (by simp [hq0]) (by simp) hq
  have hLM_RF : G.IsLocalDirectedMarkov p → G.RecursivelyFactorizes p :=
    G.recursivelyFactorizes_of_isLocalDirectedMarkov hp
  exact ⟨⟨fun h ↦ hGM_LM (hRF_GM h), hLM_RF⟩, ⟨fun h ↦ hRF_GM (hLM_RF h), hGM_LM⟩⟩

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
  have hX : ∀ v ∈ Z, v ∉ X ∧ ∀ u ∈ X, ¬ G.IsDescendant u v := fun v hv ↦
    ⟨fun h ↦ Finset.disjoint_left.1 hXZ h hv, fun u hu ↦ hbd.1 u hu v hv⟩
  have hsep : ((G.removeIncoming ↑(∅ : Finset V)).removeOutgoing ↑X).DSeparated ↑Y ↑X
      ↑((∅ : Finset V) ∪ Z) := by
    rw [Finset.empty_union]
    exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths (G.removeIncoming ↑(∅ : Finset V))
      (fun u v h ↦ h.1)
      (Finset.disjoint_coe.2 hXY) hbd.2
  have hp0 : ∀ y, 0 ≤ directedFactorizationMass localMass y :=
    directedFactorizationMass_nonneg hloc
  change marginalMass (interventionMass localMass X b) Y b = _
  rw [marginalMass_eq_sum_overwriteOn _ hYZ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  set c := overwriteOn Z z b with hc
  have hcX : ∀ v ∈ X, c v = b v := fun v hv ↦
    overwriteOn_of_notMem _ _ (Finset.disjoint_left.1 hXZ hv)
  have hZm : marginalMass (interventionMass localMass X b) Z c =
      marginalMass (directedFactorizationMass localMass) Z c :=
    doMarginalMass_eq_marginalMass_of_nonDescendant G localMass hloc hpar X Z b c hX
  have hposZm : 0 < marginalMass (directedFactorizationMass localMass) Z c :=
    lt_of_lt_of_le (hposZ z) (marginalMass_anti hp0 Finset.subset_union_right c)
  have hrule := condDoMass_union_eq_of_dSeparated G localMass hloc hpar ∅ Y X Z
    ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Finset.disjoint_empty_left _,
      hXY.symm, hYZ, hXZ⟩ hsep c (by
      change 0 < marginalMass (interventionMass localMass ∅ c) (X ∪ Z) c
      rw [interventionMass_empty]
      exact hposZ z)
  unfold condDoMass at hrule
  change marginalMass (interventionMass localMass (∅ ∪ X) c) (Y ∪ Z) c /
      marginalMass (interventionMass localMass (∅ ∪ X) c) Z c =
    marginalMass (interventionMass localMass ∅ c) (Y ∪ (X ∪ Z)) c /
      marginalMass (interventionMass localMass ∅ c) (X ∪ Z) c at hrule
  rw [Finset.empty_union, interventionMass_empty, interventionMass_congr localMass X hcX,
    hZm] at hrule
  unfold condMass
  rw [← hrule, div_mul_cancel₀ _ hposZm.ne']

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
  obtain ⟨hint, hbXZ, hbZY⟩ := hfd
  have hp0 : ∀ y, 0 ≤ directedFactorizationMass localMass y :=
    directedFactorizationMass_nonneg hloc
  change marginalMass (interventionMass localMass X b) Y b = _
  rw [marginalMass_eq_sum_overwriteOn _ hYZ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  set c := overwriteOn Z z b with hc
  have hcX : ∀ v ∈ X, c v = b v := fun v hv ↦
    overwriteOn_of_notMem _ _ (Finset.disjoint_left.1 hXZ hv)
  have hposXc : 0 < marginalMass (directedFactorizationMass localMass) X c := by
    rw [marginalMass_congr_point _ X hcX]
    exact hposX
  have hposXZc : 0 < marginalMass (directedFactorizationMass localMass) (X ∪ Z) c := by
    have := hposXZ (fun v ↦ c v) z
    rwa [← hc, overwriteOn_self] at this
  -- `P(z | do(x)) = P(z | x)`
  have h1 : marginalMass (interventionMass localMass X b) Z c =
      condMass (directedFactorizationMass localMass) Z X c := by
    have hsep1 : ((G.removeIncoming ↑(∅ : Finset V)).removeOutgoing ↑X).DSeparated ↑Z ↑X
        ↑((∅ : Finset V) ∪ ∅) := by
      rw [Finset.empty_union, Finset.coe_empty]
      exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths
        (G.removeIncoming ∅) (fun u v h ↦ h.1)
        (Finset.disjoint_coe.2 hXZ) hbXZ
    have hrule := condDoMass_union_eq_of_dSeparated G localMass hloc hpar ∅ Z X ∅
      ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _,
        Finset.disjoint_empty_left _, hXZ.symm, Finset.disjoint_empty_right _,
        Finset.disjoint_empty_right _⟩ hsep1 c (by
        change 0 < marginalMass (interventionMass localMass ∅ c) (X ∪ ∅) c
        rw [interventionMass_empty, Finset.union_empty]
        exact hposXc)
    unfold condDoMass at hrule
    change marginalMass (interventionMass localMass (∅ ∪ X) c) (Z ∪ ∅) c /
        marginalMass (interventionMass localMass (∅ ∪ X) c) ∅ c =
      marginalMass (interventionMass localMass ∅ c) (Z ∪ (X ∪ ∅)) c /
        marginalMass (interventionMass localMass ∅ c) (X ∪ ∅) c at hrule
    simp only [Finset.empty_union, Finset.union_empty] at hrule
    rw [marginalMass_empty_interventionMass G hloc hpar, div_one, interventionMass_empty,
      interventionMass_congr localMass X hcX] at hrule
    rw [hrule]
    rfl
  have hposZdo : 0 < marginalMass (interventionMass localMass X b) Z c := by
    rw [h1]
    unfold condMass
    exact div_pos (by rw [Finset.union_comm]; exact hposXZc) hposXc
  -- `P(y | do(x), z) = P(y | do(x), do(z))`
  have h2 : marginalMass (interventionMass localMass X b) (Y ∪ Z) c /
      marginalMass (interventionMass localMass X b) Z c =
        marginalMass (interventionMass localMass (X ∪ Z) c) Y c := by
    have hsep2 : ((G.removeIncoming ↑X).removeOutgoing ↑Z).DSeparated ↑Y ↑Z ↑(X ∪ ∅) := by
      rw [Finset.union_empty]
      exact G.dSeparated_removeOutgoing_of_blocksBackdoorPaths (G.removeIncoming ↑X)
        (fun u v h ↦ h.1)
        (Finset.disjoint_coe.2 hYZ.symm) hbZY
    have hrule := condDoMass_union_eq_of_dSeparated G localMass hloc hpar X Y Z ∅
      ⟨hXY, hXZ, Finset.disjoint_empty_right _, hYZ, Finset.disjoint_empty_right _,
        Finset.disjoint_empty_right _⟩ hsep2 c (by
        change 0 < marginalMass (interventionMass localMass X c) (Z ∪ ∅) c
        rw [Finset.union_empty, interventionMass_congr localMass X hcX]
        exact hposZdo)
    unfold condDoMass at hrule
    change marginalMass (interventionMass localMass (X ∪ Z) c) (Y ∪ ∅) c /
        marginalMass (interventionMass localMass (X ∪ Z) c) ∅ c =
      marginalMass (interventionMass localMass X c) (Y ∪ (Z ∪ ∅)) c /
        marginalMass (interventionMass localMass X c) (Z ∪ ∅) c at hrule
    simp only [Finset.union_empty] at hrule
    rw [marginalMass_empty_interventionMass G hloc hpar, div_one,
      interventionMass_congr localMass X hcX] at hrule
    exact hrule.symm
  -- `P(y | do(x), do(z)) = P(y | do(z))`
  have h3 : marginalMass (interventionMass localMass (X ∪ Z) c) Y c =
      doMarginalMass localMass Z c Y c := by
    have := doMarginalMass_eq_marginalMass_of_nonDescendant (G.removeIncoming ↑Z)
      (intervenedLocalMass localMass Z c) (isLocalMassFamily_intervenedLocalMass hloc Z c)
      (respectsParents_intervenedLocalMass G hpar Z c) X Y c c fun v hv ↦
        ⟨fun h ↦ Finset.disjoint_left.1 hXY h hv, fun u hu ↦
          G.not_isDescendant_removeIncoming_of_intercepts (Finset.disjoint_coe.2 hXZ) hint
            v hv u hu⟩
    change marginalMass (interventionMass (intervenedLocalMass localMass Z c) X c) Y c =
      marginalMass (directedFactorizationMass (intervenedLocalMass localMass Z c)) Y c at this
    rw [interventionMass_intervenedLocalMass, directedFactorizationMass_intervenedLocalMass]
      at this
    exact this
  -- back-door adjustment for the effect of `Z` on `Y`, adjusting for `X`
  have hbd : G.IsBackdoorSet ↑Z ↑Y ↑X :=
    ⟨fun z hz x hx ↦ G.not_isDescendant_of_blocksBackdoorPaths hbXZ z hz x hx, hbZY⟩
  have h4 := doMarginalMass_eq_backdoor G localMass hloc hpar Z Y X hYZ.symm hXZ.symm
    hXY.symm hbd c fun x' ↦ by
      rw [Finset.union_comm]
      exact hposXZ x' z
  rw [← h1, ← div_mul_cancel₀ (marginalMass (interventionMass localMass X b) (Y ∪ Z) c)
    hposZdo.ne', h2, h3, h4, mul_comm, Finset.union_comm Z X]

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
  obtain ⟨hXY, hXZ, hXW, hYZ, hYW, hZW⟩ := hdisj
  have hci := condIndepMass_directedFactorizationMass_of_dSeparated (G.removeIncoming ↑X)
    (intervenedLocalMass localMass X b) (isLocalMassFamily_intervenedLocalMass hloc X b)
    (respectsParents_intervenedLocalMass G hpar X b) Y Z (X ∪ W) hYZ
    (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩)
    (Finset.disjoint_union_right.2 ⟨hXZ.symm, hZW⟩) hsep
  rw [directedFactorizationMass_intervenedLocalMass] at hci
  exact div_eq_div_of_condIndepMass (interventionMass_nonneg hloc X b)
    (fun y hy ↦ interventionMass_support hy) hci hpos

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
  exact condDoMass_union_eq_of_dSeparated G localMass hloc hpar X Y Z W hdisj hsep b hpos

/-- The vertices of `Z` that are not ancestors of any vertex of `W` in `G_{\bar X}`. -/
def CausalGraph.nonAncestorPart (G : CausalGraph V) (X Z W : Set V) : Set V :=
  {z | z ∈ Z ∧ ∀ w ∈ W, ¬ (G.removeIncoming X).IsDescendant z w}

/-- The graph augmented by an intervention indicator `none` with an arrow into each vertex of
`Z`; the original vertices are `some v`. -/
def CausalGraph.augment (G : CausalGraph V) (Z : Finset V) : CausalGraph (Option V) where
  edge a c := ∃ v, c = some v ∧ (a = none ∧ v ∈ Z ∨ ∃ u, a = some u ∧ G.edge u v)
  acyclic := by
    have hnone : ∀ a, ¬ Relation.TransGen
        (fun a c : Option V ↦ ∃ v, c = some v ∧ (a = none ∧ v ∈ Z ∨ ∃ u, a = some u ∧ G.edge u v))
        a none := by
      intro a h
      obtain ⟨c, -, v, hv, -⟩ := Relation.TransGen.tail'_iff.1 h
      exact absurd hv (by simp)
    have hsome : ∀ a c, Relation.TransGen
        (fun a c : Option V ↦ ∃ v, c = some v ∧ (a = none ∧ v ∈ Z ∨ ∃ u, a = some u ∧ G.edge u v))
        a c → ∀ u v, a = some u → c = some v → Relation.TransGen G.edge u v := by
      intro a c h
      induction h with
      | @single c hac =>
        rintro u v rfl rfl
        obtain ⟨w, hw, (⟨h1, -⟩ | ⟨u', hu', he⟩)⟩ := hac
        · exact absurd h1 (by simp)
        · cases Option.some_injective _ hw
          cases Option.some_injective _ hu'
          exact Relation.TransGen.single he
      | @tail b c hab hbc ih =>
        rintro u v rfl rfl
        obtain ⟨w, hw, (⟨h1, -⟩ | ⟨u', hu', he⟩)⟩ := hbc
        · subst h1
          exact absurd hab (hnone _)
        · cases Option.some_injective _ hw
          exact Relation.TransGen.tail (ih u u' rfl hu') he
    intro a h
    cases a with
    | none => exact hnone _ h
    | some u => exact G.acyclic u (hsome _ _ h u u rfl rfl)

/-- Arrows between original vertices of the augmented graph are the arrows of the graph. -/
theorem CausalGraph.augment_edge_some (G : CausalGraph V) (Z : Finset V) (u v : V) :
    (G.augment Z).edge (some u) (some v) ↔ G.edge u v := by
  simp [CausalGraph.augment]

/-- The intervention indicator points exactly into the vertices of `Z`. -/
theorem CausalGraph.augment_edge_none (G : CausalGraph V) (Z : Finset V) (v : V) :
    (G.augment Z).edge none (some v) ↔ v ∈ Z := by
  simp [CausalGraph.augment]

/-- No arrow points into the intervention indicator. -/
theorem CausalGraph.augment_not_edge_to_none (G : CausalGraph V) (Z : Finset V)
    (a : Option V) : ¬ (G.augment Z).edge a none := by
  simp [CausalGraph.augment]

/-- Descendants among the original vertices of the augmented graph are descendants in the
graph. -/
theorem CausalGraph.isDescendant_of_augment (G : CausalGraph V) (Z : Finset V) {u v : V}
    (h : (G.augment Z).IsDescendant (some u) (some v)) : G.IsDescendant u v := by
  have key : ∀ a c, (G.augment Z).IsDescendant a c → ∀ u v, a = some u → c = some v →
      G.IsDescendant u v := by
    intro a c h
    induction h with
    | @single c hac =>
      rintro u v rfl rfl
      exact Relation.TransGen.single ((G.augment_edge_some Z u v).1 hac)
    | @tail b c hab hbc ih =>
      rintro u v rfl rfl
      cases b with
      | none =>
        obtain ⟨c, -, hc⟩ := Relation.TransGen.tail'_iff.1 hab
        exact absurd hc (G.augment_not_edge_to_none Z c)
      | some w => exact Relation.TransGen.tail (ih u w rfl rfl) ((G.augment_edge_some Z w v).1 hbc)
  exact key _ _ h u v rfl rfl

/-- Local masses on the augmented graph: the indicator `none` is uniform on `{s₀, s₁}`; when it
equals `s₁` the vertices of `Z` are set to the values of `b`, otherwise all vertices follow the
local masses after `do(X = b)`. -/
def augmentedLocalMass [Fintype S] (localMass : V → (V → S) → S → ℝ) (X Z : Finset V)
    (b : V → S) (s₀ s₁ : S) : Option V → (Option V → S) → S → ℝ :=
  fun o y s ↦ o.elim (if s = s₀ ∨ s = s₁ then 1 / 2 else 0) fun v ↦
    if v ∈ Z ∧ y none = s₁ then (if s = b v then 1 else 0)
    else intervenedLocalMass localMass X b v (fun u ↦ y (some u)) s

/-- The augmented local masses form a local mass family. -/
theorem isLocalMassFamily_augmentedLocalMass [Fintype S] {localMass : V → (V → S) → S → ℝ}
    (hloc : IsLocalMassFamily localMass) (X Z : Finset V) (b : V → S) {s₀ s₁ : S}
    (hs : s₀ ≠ s₁) : IsLocalMassFamily (augmentedLocalMass localMass X Z b s₀ s₁) := by
  have hl := isLocalMassFamily_intervenedLocalMass hloc X b
  refine ⟨fun o y s ↦ ?_, fun o y ↦ ?_⟩
  · cases o with
    | none =>
      simp only [augmentedLocalMass, Option.elim]
      split_ifs <;> norm_num
    | some v =>
      simp only [augmentedLocalMass, Option.elim]
      split_ifs
      · exact zero_le_one
      · exact le_rfl
      · exact hl.1 v _ s
  · cases o with
    | none =>
      simp only [augmentedLocalMass, Option.elim]
      rw [Fintype.sum_eq_add s₀ s₁ hs fun s hs' ↦ by simp [hs'.1, hs'.2]]
      simp [hs.symm]
      norm_num
    | some v =>
      simp only [augmentedLocalMass, Option.elim]
      split_ifs
      · simp
      · exact hl.2 v _

/-- The augmented local masses respect the parents of the augmented graph of `G_{\bar X}`. -/
theorem respectsParents_augmentedLocalMass [Fintype S] (G : CausalGraph V)
    {localMass : V → (V → S) → S → ℝ} (hpar : G.RespectsParents localMass) (X Z : Finset V)
    (b : V → S) (s₀ s₁ : S) :
    ((G.removeIncoming ↑X).augment Z).RespectsParents
      (augmentedLocalMass localMass X Z b s₀ s₁) := by
  intro o y y' h
  cases o with
  | none => rfl
  | some v =>
    have hi := respectsParents_intervenedLocalMass G hpar X b v (fun u ↦ y (some u))
      (fun u ↦ y' (some u)) fun u hu ↦ h (some u) ((CausalGraph.augment_edge_some _ Z u v).2 hu)
    funext s
    simp only [augmentedLocalMass, Option.elim]
    by_cases hvZ : v ∈ Z
    · have hn : y none = y' none := h none ((CausalGraph.augment_edge_none _ Z v).2 hvZ)
      rw [hn, hi]
    · simp only [hvZ, false_and, ite_false]
      rw [hi]

/-- The recursive product of the augmented local masses: the indicator mass times the law
under `do(X ∪ Z)` (indicator `s₁`) or under `do(X)` (any other value). -/
theorem directedFactorizationMass_augmentedLocalMass [Fintype V] [Fintype S]
    (localMass : V → (V → S) → S → ℝ) (X Z : Finset V) (b : V → S) (s₀ s₁ : S)
    (y : Option V → S) :
    directedFactorizationMass (augmentedLocalMass localMass X Z b s₀ s₁) y =
      (if y none = s₀ ∨ y none = s₁ then 1 / 2 else 0) *
        (if y none = s₁ then interventionMass localMass (X ∪ Z) b (fun u ↦ y (some u))
          else interventionMass localMass X b (fun u ↦ y (some u))) := by
  unfold directedFactorizationMass
  rw [Fintype.prod_option]
  congr 1
  split_ifs with h1
  · rw [← directedFactorizationMass_intervenedLocalMass]
    unfold directedFactorizationMass
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    simp only [augmentedLocalMass, Option.elim, h1, and_true, intervenedLocalMass,
      Finset.mem_union]
    by_cases hvZ : v ∈ Z <;> by_cases hvX : v ∈ X <;> simp [hvZ, hvX]
  · rw [← directedFactorizationMass_intervenedLocalMass]
    unfold directedFactorizationMass
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    simp [augmentedLocalMass, Option.elim, h1]

/-- Splitting a sum over configurations of `Option V` into the value at `none` and the
configuration on `V`. -/
theorem sum_option_pi [Fintype V] [Fintype S]
    (F : (Option V → S) → ℝ) :
    ∑ y, F y = ∑ s, ∑ y : V → S, F (fun o ↦ Option.elim o s y) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.piOptionEquivProd (β := fun _ ↦ S)) _ _ fun y ↦ ?_
  congr 1
  funext o
  cases o <;> rfl

/-- Marginal masses of the augmented mass, at a point with indicator value `s`. -/
theorem marginalMass_augmented [Fintype V] [Fintype S] (localMass : V → (V → S) → S → ℝ)
    (X Z : Finset V) (b : V → S) (s₀ s₁ : S) (T : Finset (Option V)) (s : S) (x : V → S) :
    marginalMass (directedFactorizationMass (augmentedLocalMass localMass X Z b s₀ s₁)) T
        (fun o ↦ o.elim s x) =
      ∑ s', if none ∈ T → s' = s then
        (if s' = s₀ ∨ s' = s₁ then 1 / 2 else 0) *
          marginalMass (if s' = s₁ then interventionMass localMass (X ∪ Z) b
            else interventionMass localMass X b) (Finset.univ.filter fun v ↦ some v ∈ T) x
      else 0 := by
  unfold marginalMass
  have key := sum_option_pi (V := V) (S := S) fun y : Option V → S ↦
    if ∀ o ∈ T, y o = Option.elim o s x then
      directedFactorizationMass (augmentedLocalMass localMass X Z b s₀ s₁) y else 0
  trans ∑ s', ∑ y : V → S, if ∀ o ∈ T, Option.elim o s' y = Option.elim o s x then
    directedFactorizationMass (augmentedLocalMass localMass X Z b s₀ s₁)
      (fun o ↦ Option.elim o s' y) else 0
  · convert key using 3
  refine Finset.sum_congr rfl fun s' _ ↦ ?_
  have hcond : ∀ y : V → S, (∀ o ∈ T, Option.elim o s' y = Option.elim o s x) ↔
      ((none ∈ T → s' = s) ∧ ∀ v ∈ Finset.univ.filter fun v ↦ some v ∈ T, y v = x v) := by
    intro y
    constructor
    · intro h
      exact ⟨fun hn ↦ h none hn, fun v hv ↦ h (some v) (Finset.mem_filter.1 hv).2⟩
    · rintro ⟨h1, h2⟩ o ho
      cases o with
      | none => exact h1 ho
      | some v => exact h2 v (Finset.mem_filter.2 ⟨Finset.mem_univ _, ho⟩)
  have hd : ∀ y : V → S,
      directedFactorizationMass (augmentedLocalMass localMass X Z b s₀ s₁)
          (fun o ↦ Option.elim o s' y) =
        (if s' = s₀ ∨ s' = s₁ then 1 / 2 else 0) *
          (if s' = s₁ then interventionMass localMass (X ∪ Z) b
            else interventionMass localMass X b) y := by
    intro y
    rw [directedFactorizationMass_augmentedLocalMass]
    by_cases h1 : s' = s₁ <;> simp [Option.elim, h1]
  by_cases hT : none ∈ T → s' = s
  · rw [ite_eq_left hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hd]
    by_cases hy : ∀ v ∈ Finset.univ.filter fun v ↦ some v ∈ T, y v = x v
    · rw [ite_eq_left ((hcond y).2 ⟨hT, hy⟩), ite_eq_left hy]
    · rw [ite_eq_right fun h ↦ hy ((hcond y).1 h).2, ite_eq_right hy, mul_zero]
  · rw [ite_eq_right hT]
    exact Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦ hT ((hcond y).1 h).1

/-- A directed path of `G_{\bar X}` ending in `W` survives the removal of the arrows into the
vertices of `Z` that are not ancestors of `W` in `G_{\bar X}`. -/
theorem CausalGraph.transGen_removeIncoming_nonAncestorPart (G : CausalGraph V)
    {X Z W : Set V} (hZW : Disjoint Z W) :
    ∀ u w, (G.removeIncoming X).IsDescendant u w → w ∈ W →
      (G.removeIncoming (X ∪ G.nonAncestorPart X Z W)).IsDescendant u w := by
  intro u w h hw
  induction h using Relation.TransGen.head_induction_on with
  | single h =>
    refine Relation.TransGen.single ⟨h.1, ?_⟩
    rintro (hX | ⟨hZ, -⟩)
    · exact h.2 hX
    · exact Set.disjoint_left.1 hZW hZ hw
  | head h _ ih =>
    refine Relation.TransGen.head ⟨h.1, ?_⟩ ih
    rintro (hX | ⟨-, hZ⟩)
    · exact h.2 hX
    · rename_i b _ hbw
      exact hZ w hw hbw

/-- In `G_{\bar X}` no vertex is a proper ancestor of a vertex of `X`. -/
theorem CausalGraph.not_isDescendant_removeIncoming_mem (G : CausalGraph V) {X : Set V}
    {u x : V} (hx : x ∈ X) : ¬ (G.removeIncoming X).IsDescendant u x := by
  intro h
  obtain ⟨c, -, hc⟩ := Relation.TransGen.tail'_iff.1 h
  exact hc.2 hx

/-- The graph-theoretic step of rule 3: if `Y` and `Z` are d-separated by `X ∪ W` in
`G_{\bar X, \overline{Z(W)}}`, then `Y` and the intervention indicator are d-separated by
`X ∪ W` in the augmented graph of `G_{\bar X}`. -/
theorem CausalGraph.dSeparated_augment_of_rule_three [Fintype V] (G : CausalGraph V)
    (X Y Z W : Finset V) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hZW : Disjoint Z W)
    (hsep : (G.removeIncoming (↑X ∪ G.nonAncestorPart ↑X ↑Z ↑W)).DSeparated ↑Y ↑Z ↑(X ∪ W)) :
    ((G.removeIncoming ↑X).augment Z).DSeparated (some '' ↑Y) {none} (some '' ↑(X ∪ W)) := by
  set G' := G.removeIncoming ↑X with hG'
  set G3 := G.removeIncoming (↑X ∪ G.nonAncestorPart ↑X ↑Z ↑W) with hG3
  set A := G'.augment Z with hA
  set Cp : Set (Option V) := some '' ↑(X ∪ W) with hCp
  have hZ1 : ∀ z, z ∈ G.nonAncestorPart ↑X ↑Z ↑W ↔
      z ∈ Z ∧ ∀ w ∈ W, ¬ G'.IsDescendant z w := fun z ↦ Iff.rfl
  -- closures in the augmented graph
  have hclos : ∀ c : V, A.MemAncestorClosure Cp (some c) →
      c ∈ X ∪ W ∨ ∃ w ∈ W, G'.IsDescendant c w := by
    rintro c ⟨z, ⟨z', hz', rfl⟩, h⟩
    rcases h with h | h
    · exact Or.inl (Option.some_injective _ h ▸ hz')
    · have hd := G'.isDescendant_of_augment Z h
      rcases Finset.mem_union.1 hz' with hx | hw
      · exact absurd hd (G.not_isDescendant_removeIncoming_mem (by simpa using hx))
      · exact Or.inr ⟨z', hw, hd⟩
  have hnotZ1 : ∀ c : V, A.MemAncestorClosure Cp (some c) →
      c ∉ G.nonAncestorPart ↑X ↑Z ↑W := by
    intro c hc hcZ
    rcases hclos c hc with h | ⟨w, hw, hd⟩
    · rcases Finset.mem_union.1 h with h | h
      · exact Finset.disjoint_left.1 hXZ h hcZ.1
      · exact Finset.disjoint_left.1 hZW hcZ.1 h
    · exact hcZ.2 w hw hd
  have hG3edge : ∀ u v, G'.edge u v → v ∉ G.nonAncestorPart ↑X ↑Z ↑W → G3.edge u v :=
    fun u v h hv ↦ ⟨h.1, fun h' ↦ h'.elim h.2 hv⟩
  intro n p h0 hn hp
  -- read the reversed path as a trail starting at the indicator
  obtain ⟨htr, hinj⟩ := A.isTrailWith_of_isActivePath hp.rev
  set q : ℕ → Option V := fun k ↦ (p ∘ Fin.rev) ⟨min k n, by omega⟩ with hq
  have hq0 : q 0 = none := by simpa [hq] using hn
  obtain ⟨yv, hyv, hqn⟩ : ∃ yv ∈ Y, q n = some yv := by
    obtain ⟨yv, hyv, h⟩ := h0
    refine ⟨yv, hyv, ?_⟩
    show p (Fin.rev ⟨min n n, by omega⟩) = some yv
    rw [show Fin.rev (⟨min n n, by omega⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp)]
    exact h.symm
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hqn
      rw [hqn] at hq0
      exact absurd hq0 (Option.some_ne_none _)
    · exact h
  have hq1 : ∃ z ∈ Z, q 1 = some z := by
    rcases htr.1 0 hn0 with h | h
    · rw [hq0] at h
      obtain ⟨v, hv, (⟨-, hvZ⟩ | ⟨u, hu, -⟩)⟩ := h
      · exact ⟨v, hvZ, hv⟩
      · exact absurd hu (by simp)
    · rw [hq0] at h
      exact absurd h (G'.augment_not_edge_to_none Z _)
  let PZ : ℕ → Prop := fun i ↦ ∃ z ∈ Z, q i = some z
  set k := Nat.findGreatest PZ n with hk
  have hk1 : 1 ≤ k := Nat.le_findGreatest (P := PZ) hn0 hq1
  have hkZ : PZ k := Nat.findGreatest_spec (P := PZ) hn0 hq1
  have hkn : k < n := by
    refine lt_of_le_of_ne (Nat.findGreatest_le n) fun hkn ↦ ?_
    obtain ⟨z, hz, hqz⟩ := hkZ
    rw [hkn, hqn] at hqz
    exact Finset.disjoint_left.1 hYZ (Option.some_injective _ hqz ▸ hyv) hz
  have hafter : ∀ i, k < i → i ≤ n → ∃ v, q i = some v ∧ v ∉ Z := by
    intro i hki hin
    cases hqi : q i with
    | none =>
      have := hinj i hin 0 (Nat.zero_le _) (by
        show q i = q 0
        rw [hqi, hq0])
      omega
    | some v =>
      refine ⟨v, rfl, fun hvZ ↦ ?_⟩
      exact Nat.findGreatest_is_greatest (P := PZ) hki hin ⟨v, hvZ, hqi⟩
  -- the part of the trail after the last vertex of `Z`
  let r : ℕ → V := fun i ↦ (q (i + k)).getD yv
  have hr : ∀ i, i ≤ n - k → q (i + k) = some (r i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · obtain ⟨z, -, hz⟩ := hkZ
      simp [r, hz]
    · obtain ⟨v, hv, -⟩ := hafter (i + k) (by omega) (by omega)
      simp [r, hv]
  have hrZ : ∀ i, 0 < i → i ≤ n - k → r i ∉ Z := by
    intro i hi hin
    obtain ⟨v, hv, hvZ⟩ := hafter (i + k) (by omega) (by omega)
    rw [hr i hin] at hv
    exact Option.some_injective _ hv ▸ hvZ
  have hr0 : r 0 ∈ Z := by
    obtain ⟨z, hz, hqz⟩ := hkZ
    have := hr 0 (Nat.zero_le _)
    rw [zero_add, hqz] at this
    exact Option.some_injective _ this ▸ hz
  have hrn : r (n - k) ∈ Y := by
    have := hr (n - k) le_rfl
    rw [Nat.sub_add_cancel hkn.le, hqn] at this
    exact Option.some_injective _ this ▸ hyv
  -- the arrow at the last vertex of `Z` does not point into a vertex of `Z(W)`
  have hfirst : G'.edge (r 1) (r 0) → r 0 ∉ G.nonAncestorPart ↑X ↑Z ↑W := by
    intro hback hZ1'
    have hqk : q k = some (r 0) := by simpa using hr 0 (Nat.zero_le _)
    have hqk1 : q (k + 1) = some (r 1) := by simpa [add_comm] using hr 1 (by omega)
    have hs := htr.2 (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at hs
    unfold CausalGraph.TripleStatus at hs
    have hin : A.edge (q (k + 1)) (q k) := by
      rw [hqk, hqk1]
      exact (G'.augment_edge_some Z _ _).2 hback
    by_cases hcol : A.edge (q (k - 1)) (q k)
    · rw [ite_eq_left ⟨hcol, hin⟩, hqk] at hs
      exact hnotZ1 _ hs hZ1'
    · have hout : A.edge (q k) (q (k - 1)) := by
        rcases htr.1 (k - 1) (by omega) with h | h
        · rw [show k - 1 + 1 = k by omega] at h
          exact absurd h hcol
        · rwa [show k - 1 + 1 = k by omega] at h
      have htk := (htr.trunc hkn.le).rev
      obtain ⟨m, hm0, hmk, hP, hdesc⟩ := A.exists_collider_of_forward_backward htk hk1 le_rfl
        (by simpa [show k - (0 + 1) = k - 1 by omega] using hout)
        (by
          simp only [Nat.sub_self, show k - (k - 1) = 1 by omega]
          obtain ⟨z, hz, hqz⟩ := hq1
          rw [hq0, hqz]
          exact (G'.augment_edge_none Z z).2 hz)
      simp only [Nat.sub_zero] at hP hdesc
      rw [hqk] at hdesc
      obtain ⟨c, hc, hc'⟩ := hP
      obtain ⟨c', hc'C, rfl⟩ := hc
      have hd : A.IsDescendant (some (r 0)) (some c') := by
        rcases hc' with h | h
        · rw [h]; exact hdesc
        · exact hdesc.trans h
      exact hnotZ1 _ ⟨some c', ⟨c', hc'C, rfl⟩, Or.inr hd⟩ hZ1'
  -- the remaining trail is active in `G_{\bar X, \overline{Z(W)}}`
  have hrtr : G3.IsTrailWith (G3.MemAncestorClosure ↑(X ∪ W)) (· ∉ (↑(X ∪ W) : Set V))
      (n - k) r := by
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · have ha := htr.1 (i + k) (by omega)
      rw [hr i (by omega), show i + k + 1 = i + 1 + k by omega, hr (i + 1) (by omega)] at ha
      rcases ha with h | h
      · exact Or.inl (hG3edge _ _ ((G'.augment_edge_some Z _ _).1 h)
          fun h' ↦ hrZ (i + 1) (by omega) (by omega) h'.1)
      · refine Or.inr (hG3edge _ _ ((G'.augment_edge_some Z _ _).1 h) fun h' ↦ ?_)
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exact hfirst ((G'.augment_edge_some Z _ _).1 h) h'
        · exact hrZ i hpos (by omega) h'.1
    · have hs := htr.2 (i + k) (by omega)
      rw [hr i (by omega), show i + k + 1 = i + 1 + k by omega, hr (i + 1) (by omega),
        show i + k + 2 = i + 2 + k by omega, hr (i + 2) (by omega)] at hs
      have hcZ : r (i + 1) ∉ G.nonAncestorPart ↑X ↑Z ↑W :=
        fun h' ↦ hrZ (i + 1) (by omega) (by omega) h'.1
      have e1 : A.edge (some (r i)) (some (r (i + 1))) ↔ G3.edge (r i) (r (i + 1)) := by
        rw [G'.augment_edge_some]
        exact ⟨fun h ↦ hG3edge _ _ h hcZ, fun h ↦ ⟨h.1, fun hx ↦ h.2 (Or.inl hx)⟩⟩
      have e2 : A.edge (some (r (i + 2))) (some (r (i + 1))) ↔
          G3.edge (r (i + 2)) (r (i + 1)) := by
        rw [G'.augment_edge_some]
        exact ⟨fun h ↦ hG3edge _ _ h hcZ, fun h ↦ ⟨h.1, fun hx ↦ h.2 (Or.inl hx)⟩⟩
      unfold CausalGraph.TripleStatus at hs ⊢
      rw [e1, e2] at hs
      split_ifs at hs ⊢ with hcol
      · rcases hclos _ hs with h | ⟨w, hw, hd⟩
        · exact ⟨_, h, Or.inl rfl⟩
        · exact ⟨w, Finset.mem_union_right _ hw, Or.inr
            (G.transGen_removeIncoming_nonAncestorPart (Finset.disjoint_coe.2 hZW) _ _ hd hw)⟩
      · exact fun h ↦ hs ⟨_, h, rfl⟩
  obtain ⟨m, r', hr', hr'0, hr'm, hinj'⟩ := G3.exists_injective_activeTrail _ _ _ hrtr
  exact hsep.symm m (fun i ↦ r' i) (by simpa [hr'0] using hr0) (by simpa [hr'm] using hrn)
    (G3.isActivePath_of_isTrailWith hr' hinj')

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
  obtain ⟨hXY, hXZ, hXW, hYZ, hYW, hZW⟩ := hdisj
  by_cases hS : ∃ s₀ s₁ : S, s₀ ≠ s₁
  swap
  · -- a single state: every configuration equals `b`
    push Not at hS
    have hsub : ∀ y : V → S, y = b := fun y ↦ funext fun v ↦ hS _ _
    have hM : ∀ A E : Finset V, doMarginalMass localMass A b E b =
        interventionMass localMass A b b := by
      intro A E
      unfold doMarginalMass
      rw [Finset.sum_eq_single b (fun y _ hy ↦ absurd (hsub y) hy) (by simp)]
      simp
    have h1 := hpos
    have h2 := hpos'
    rw [hM] at h1 h2
    unfold condDoMass
    rw [hM, hM, hM, hM, div_self h2.ne', div_self h1.ne']
  obtain ⟨s₀, s₁, hs⟩ := hS
  set e : V ↪ Option V := Function.Embedding.some
  have hsep' := G.dSeparated_augment_of_rule_three X Y Z W hXZ hYZ hZW hsep
  have hci := condIndepMass_directedFactorizationMass_of_dSeparated
    ((G.removeIncoming ↑X).augment Z) (augmentedLocalMass localMass X Z b s₀ s₁)
    (isLocalMassFamily_augmentedLocalMass hloc X Z b hs)
    (respectsParents_augmentedLocalMass G hpar X Z b s₀ s₁) (Y.map e) {none} ((X ∪ W).map e)
    (by simp [e]) ((Finset.disjoint_map e).2 (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩))
    (by simp [e]) (by simpa [e] using hsep') (fun o ↦ o.elim s₀ b)
  have hfilt : ∀ (T : Finset (Option V)) (E : Finset V), (∀ v, some v ∈ T ↔ v ∈ E) →
      Finset.univ.filter (fun v ↦ some v ∈ T) = E := fun T E h ↦ by
    ext v
    simp [h v]
  have hw : ∀ f : S → ℝ, (∑ s', (if s' = s₀ ∨ s' = s₁ then (1 : ℝ) / 2 else 0) * f s') =
      f s₀ / 2 + f s₁ / 2 := by
    intro f
    rw [Fintype.sum_eq_add s₀ s₁ hs fun s h ↦ by simp [h.1, h.2]]
    simp
    ring
  simp only [marginalMass_augmented] at hci
  rw [hfilt _ (Y ∪ (X ∪ W)) (fun v ↦ by simp [e]),
    hfilt _ (X ∪ W) (fun v ↦ by simp [e]),
    hfilt _ (Y ∪ (X ∪ W)) (fun v ↦ by simp [e]),
    hfilt _ (X ∪ W) (fun v ↦ by simp [e])] at hci
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_map, e,
    Function.Embedding.some_apply, reduceCtorEq, and_false, exists_false, or_false, or_true,
    true_implies, false_implies, ite_true, Finset.sum_ite_eq', Finset.mem_univ] at hci
  rw [hw, hw] at hci
  simp only [hs, ite_false, ite_true, true_or] at hci
  have hsX : ∀ y, interventionMass localMass X b y ≠ 0 → ∀ v ∈ X, y v = b v :=
    fun y hy ↦ interventionMass_support hy
  have hsXZ : ∀ y, interventionMass localMass (X ∪ Z) b y ≠ 0 → ∀ v ∈ X, y v = b v :=
    fun y hy v hv ↦ interventionMass_support hy v (Finset.mem_union_left _ hv)
  have e1 : Y ∪ (X ∪ W) = (Y ∪ W) ∪ X := by
    ext v; simp only [Finset.mem_union]; tauto
  have e2 : X ∪ W = W ∪ X := Finset.union_comm _ _
  rw [e1, e2, marginalMass_union_of_support hsX, marginalMass_union_of_support hsX,
    marginalMass_union_of_support hsXZ, marginalMass_union_of_support hsXZ] at hci
  unfold condDoMass
  change marginalMass (interventionMass localMass (X ∪ Z) b) (Y ∪ W) b /
      marginalMass (interventionMass localMass (X ∪ Z) b) W b =
    marginalMass (interventionMass localMass X b) (Y ∪ W) b /
      marginalMass (interventionMass localMass X b) W b
  have hp0 : 0 < marginalMass (interventionMass localMass X b) W b := hpos
  have hp1 : 0 < marginalMass (interventionMass localMass (X ∪ Z) b) W b := hpos'
  rw [div_eq_div_iff hp1.ne' hp0.ne']
  nlinarith [hci]

/-- GAPS 105.70: two nonadjacent distinct vertices of a directed acyclic graph are d-separated
by the parents of one of them. -/
theorem CausalGraph.dSeparated_parents_of_not_adjacent [Fintype V] (G : CausalGraph V)
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

/-- GAPS 105.70: in a skeleton path `u - v - w` with `u`, `w` nonadjacent, if `S` (not
containing `u`, `w`) d-separates `u` and `w`, then `u → v ← w` exactly when `v ∉ S`. -/
theorem CausalGraph.isCollider_iff_not_mem_of_dSeparated [Fintype V] (G : CausalGraph V)
    {u v w : V} (huv : G.Adjacent u v) (hvw : G.Adjacent v w) (huw : ¬ G.Adjacent u w)
    (hne : u ≠ w) (S : Set V) (hu : u ∉ S) (hw : w ∉ S) (hsep : G.DSeparated {u} {w} S) :
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
