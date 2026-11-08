module

public import CKSD.LinearModels.ActiveTrails

/-!
# Discrete directed factorization and the global Markov property

Finite probability masses factorizing along an acyclic graph satisfy the global Markov
property. The proof sums outside the ancestral closure and splits factors according to
active-trail reachability, following Lauritzen, *Graphical Models* (1996), §3.2.
Source: GAPS 105.62; graph-theoretic steps use `CKSD.LinearModels.ActiveTrails`.
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
    (hpar : G.RespectsParents localMass) (A B C : Finset V)
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

end CKSD
