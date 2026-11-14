module

public import CKSD.LinearModels.DirectedGraphical.Basic


/-!
# Marginal and interventional masses; rules 1 and 2 of the do-calculus

For a law on the configurations `V → S` given by a mass function, marginal probabilities are
finite sums. An intervention `do(X = x)` replaces the local masses of the vertices of `X` by
point masses at `x` (`CKSD.intervenedLocalMass`); its joint mass is the truncated
factorization `CKSD.interventionMass`, and its marginals are `CKSD.doMarginalMass`. A single
configuration `b` supplies all values occurring in a query.

## Main results

* `CKSD.do_marginal_mass_eq_marginal_mass_of_non_descendant`: an intervention does not change the
  marginal law of the nondescendants of the intervened set.
* Graph surgery lemmas relating back-door blocking, interception of directed paths, and
  d-separation in `G_{\bar X}` and `G_{\underline X}`.
* `CKSD.cond_do_mass_rule_one`, `CKSD.cond_do_mass_rule_two`: rules 1 (insertion and deletion of
  observations) and 2 (action/observation exchange) of Pearl's do-calculus. Rule 3 is
  `CKSD.cond_do_mass_rule_three` in `CKSD.LinearModels.DirectedGraphical.DoCalculus`.

## References

* J. Pearl, *Causality*, 2nd ed., Cambridge University Press, 2009, §3.4.

Sources: GAPS 105.63 and 105.64.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

/-! ### Marginal and interventional masses -/

/-- A marginal mass depends only on the values of the point at the fixed coordinates. -/
theorem marginal_mass_congr_point [Fintype V] [Fintype S] (p : (V → S) → ℝ) (E : Finset V)
    {x x' : V → S} (h : ∀ v ∈ E, x v = x' v) : marginalMass p E x = marginalMass p E x' := by
  unfold marginalMass
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : (∀ v ∈ E, y v = x v) ↔ ∀ v ∈ E, y v = x' v :=
    forall₂_congr fun v hv ↦ by rw [h v hv]
  simp only [this]

/-- Marginal masses of a nonnegative mass function are nonnegative. -/
theorem marginal_mass_nonneg [Fintype V] [Fintype S] {p : (V → S) → ℝ} (hp : ∀ y, 0 ≤ p y)
    (E : Finset V) (x : V → S) : 0 ≤ marginalMass p E x :=
  Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact hp y
    · exact le_rfl

/-- Marginal masses decrease when more coordinates are fixed. -/
theorem marginal_mass_anti [Fintype V] [Fintype S] {p : (V → S) → ℝ} (hp : ∀ y, 0 ≤ p y)
    {E F : Finset V} (hEF : E ⊆ F) (x : V → S) : marginalMass p F x ≤ marginalMass p E x := by
  unfold marginalMass
  refine Finset.sum_le_sum fun y _ ↦ ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (fun v hv ↦ h1 v (hEF hv)) h2
  · exact hp y
  · exact le_rfl

/-- Fixing coordinates on which the mass is concentrated does not change a marginal mass. -/
theorem marginal_mass_union_of_support [Fintype V] [Fintype S] {p : (V → S) → ℝ}
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
theorem overwrite_on_of_not_mem {B : Finset V} (b : B → S) (x : V → S) {v : V} (hv : v ∉ B) :
    overwriteOn B b x v = x v := by
  simp [overwriteOn, hv]

/-- `overwriteOn` with the values of the configuration itself does nothing. -/
theorem overwrite_on_self (B : Finset V) (x : V → S) : overwriteOn B (fun v ↦ x v) x = x := by
  funext v
  unfold overwriteOn
  split_ifs <;> rfl

/-- The law of total probability: a marginal mass is the sum, over the values of a disjoint
set `Z` of variables, of the marginal masses with `Z` fixed as well. -/
theorem marginal_mass_eq_sum_overwrite_on [Fintype V] [Fintype S] (p : (V → S) → ℝ)
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
        rwa [overwrite_on_of_not_mem _ _ (Finset.disjoint_left.1 hEZ hv)] at this
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
theorem intervention_mass_congr [Fintype V] (localMass : V → (V → S) → S → ℝ) (A : Finset V)
    {a a' : V → S} (h : ∀ v ∈ A, a v = a' v) :
    interventionMass localMass A a = interventionMass localMass A a' := by
  funext y
  unfold interventionMass
  have : (∀ v ∈ A, y v = a v) ↔ ∀ v ∈ A, y v = a' v :=
    forall₂_congr fun v hv ↦ by rw [h v hv]
  simp only [this]

/-- The empty intervention leaves the recursive product mass unchanged. -/
theorem intervention_mass_empty [Fintype V] (localMass : V → (V → S) → S → ℝ) (a : V → S) :
    interventionMass localMass ∅ a = directedFactorizationMass localMass := by
  funext y
  simp [interventionMass, directedFactorizationMass]

/-- Local masses after the intervention `do(X = b)`: point masses at the values of `b` on `X`,
the original local masses elsewhere. -/
def intervenedLocalMass (localMass : V → (V → S) → S → ℝ) (X : Finset V) (b : V → S) :
    V → (V → S) → S → ℝ :=
  fun v y s ↦ if v ∈ X then (if s = b v then 1 else 0) else localMass v y s

/-- Intervened local masses form a local mass family. -/
theorem is_local_mass_family_intervened_local_mass [Fintype S] {localMass : V → (V → S) → S → ℝ}
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
theorem respects_parents_intervened_local_mass (G : CausalGraph V)
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
theorem directed_factorization_mass_intervened_local_mass [Fintype V]
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
theorem intervention_mass_intervened_local_mass [Fintype V] (localMass : V → (V → S) → S → ℝ)
    (X Z : Finset V) (b : V → S) :
    interventionMass (intervenedLocalMass localMass Z b) X b =
      interventionMass localMass (X ∪ Z) b := by
  rw [← directed_factorization_mass_intervened_local_mass,
    ← directed_factorization_mass_intervened_local_mass]
  congr 1
  funext v y s
  by_cases h1 : v ∈ X <;> by_cases h2 : v ∈ Z <;> simp [intervenedLocalMass, h1, h2]

/-- Interventional masses are nonnegative. -/
theorem intervention_mass_nonneg [Fintype V] [Fintype S] {localMass : V → (V → S) → S → ℝ}
    (hloc : IsLocalMassFamily localMass) (X : Finset V) (a y : V → S) :
    0 ≤ interventionMass localMass X a y := by
  unfold interventionMass
  split_ifs
  · exact Finset.prod_nonneg fun v _ ↦ hloc.1 v y (y v)
  · exact le_rfl

/-- The interventional mass under `do(X = a)` is concentrated on the configurations that agree
with `a` on `X`. -/
theorem intervention_mass_support [Fintype V] {localMass : V → (V → S) → S → ℝ}
    {X : Finset V} {a y : V → S} (h : interventionMass localMass X a y ≠ 0) :
    ∀ v ∈ X, y v = a v := by
  unfold interventionMass at h
  by_contra hc
  rw [ite_eq_right hc] at h
  exact h rfl

/-- Recursive product masses are nonnegative. -/
theorem directed_factorization_mass_nonneg [Fintype V] [Fintype S]
    {localMass : V → (V → S) → S → ℝ} (hloc : IsLocalMassFamily localMass) (y : V → S) :
    0 ≤ directedFactorizationMass localMass y :=
  Finset.prod_nonneg fun v _ ↦ hloc.1 v y (y v)

/-- A recursive product of local masses has total mass one. -/
theorem marginal_mass_empty_directed_factorization_mass [Fintype V] [Fintype S]
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
theorem marginal_mass_empty_intervention_mass [Fintype V] [Fintype S] (G : CausalGraph V)
    {localMass : V → (V → S) → S → ℝ} (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X : Finset V) (a x : V → S) :
    marginalMass (interventionMass localMass X a) ∅ x = 1 := by
  rw [← directed_factorization_mass_intervened_local_mass]
  exact marginal_mass_empty_directed_factorization_mass (G.removeIncoming ↑X)
    (is_local_mass_family_intervened_local_mass hloc X a) (respects_parents_intervened_local_mass G hpar X a) x

/-- Conditional independence `Y ⊥ Z | X ∪ W`, for a mass concentrated on one value of `X`,
in quotient form: `P(y | z, w) = P(y | w)`. -/
theorem div_eq_div_of_cond_indep_mass [Fintype V] [Fintype S] {p : (V → S) → ℝ}
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
  rw [e1, e3, e4, e2, marginal_mass_union_of_support hsupp, marginal_mass_union_of_support hsupp,
    marginal_mass_union_of_support hsupp, marginal_mass_union_of_support hsupp] at h
  have hW : 0 < marginalMass p W b :=
    lt_of_lt_of_le hpos (marginal_mass_anti hp Finset.subset_union_right b)
  rw [div_eq_div_iff hpos.ne' hW.ne']
  exact h

/-- The interventional marginal of variables that are neither in `X` nor descendants of `X`
equals their observational marginal. -/
theorem do_marginal_mass_eq_marginal_mass_of_non_descendant [Fintype V] [Fintype S]
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
  rw [← directed_factorization_mass_intervened_local_mass]
  unfold marginalMass directedFactorizationMass
  rw [sum_ite_prod_eq_sum_ite_prod_compl (G.removeIncoming ↑X) _
      (is_local_mass_family_intervened_local_mass hloc X a)
      (respects_parents_intervened_local_mass G hpar X a) x E U hclX hEU,
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
theorem CausalGraph.d_separated_remove_outgoing_of_blocks_backdoor_paths (G H : CausalGraph V)
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
theorem CausalGraph.not_is_descendant_of_blocks_backdoor_paths (G : CausalGraph V)
    {X Z : Set V} (hb : G.BlocksBackdoorPaths X Z ∅) :
    ∀ z ∈ Z, ∀ x ∈ X, ¬ G.IsDescendant z x := by
  intro z hz x hx hd
  obtain ⟨m, r, hm, h0, hmx, hf⟩ := G.exists_forward_of_is_descendant hd
  have htr : G.IsTrailWith (G.MemAncestorClosure ∅) (· ∉ (∅ : Set V)) m (fun k ↦ r (m - k)) :=
    (G.is_trail_with_of_forward hf fun i _ _ ↦ Set.notMem_empty _).rev
  have hc : ∀ i j, i < j → j ≤ m → r i ≠ r j := by
    intro i j hij hjm heq
    have := G.is_descendant_of_forward (r := fun k ↦ r (k + i)) (m := m - i)
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
  have hpath := G.is_active_path_of_is_trail_with htr hinj
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine hb n (fun i ↦ r (n + 1 - i)) (by simpa [hmx] using hx) (by simpa [h0] using hz) ?_ hpath
  simpa using hf n (by omega)

/-- If `Z` intercepts all directed paths from `X` to `Y`, then in the graph with the arrows
into `Z` removed no vertex of `Y` is a descendant of a vertex of `X`. -/
theorem CausalGraph.not_is_descendant_remove_incoming_of_intercepts (G : CausalGraph V)
    {X Y Z : Set V} (hXZ : Disjoint X Z) (hi : G.InterceptsDirectedPaths X Y Z) :
    ∀ v ∈ Y, ∀ u ∈ X, ¬ (G.removeIncoming Z).IsDescendant u v := by
  intro v hv u hu hd
  obtain ⟨m, r, hm, h0, hmv, hf⟩ := (G.removeIncoming Z).exists_forward_of_is_descendant hd
  obtain ⟨i, hi'⟩ := hi m (fun i ↦ r i) (by simpa [h0] using hu) (by simpa [hmv] using hv)
    fun i ↦ by simpa using (hf i i.isLt).1
  rcases Nat.eq_zero_or_pos i.val with h | h
  · simp only [h, h0] at hi'
    exact Set.disjoint_left.1 hXZ hu hi'
  · have := (hf (i.val - 1) (by omega)).2
    rw [Nat.sub_add_cancel h] at this
    exact this hi'

/-! ### Rules 1 and 2 of the do-calculus -/

/-- GAPS 105.64, rule 1 of the do-calculus (insertion and deletion of observations):
if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X}`, then
`P(y | do(x), z, w) = P(y | do(x), w)`. The conditioning event `{Z = z, W = w}` has positive
interventional probability. -/
theorem cond_do_mass_rule_one [Fintype V] [Fintype S] (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) (hloc : IsLocalMassFamily localMass)
    (hpar : G.RespectsParents localMass) (X Y Z W : Finset V)
    (hdisj : Disjoint X Y ∧ Disjoint X Z ∧ Disjoint X W ∧ Disjoint Y Z ∧ Disjoint Y W ∧
      Disjoint Z W)
    (hsep : (G.removeIncoming X).DSeparated Y Z ↑(X ∪ W)) (b : V → S)
    (hpos : 0 < doMarginalMass localMass X b (Z ∪ W) b) :
    condDoMass localMass X Y (Z ∪ W) b = condDoMass localMass X Y W b := by
  obtain ⟨hXY, hXZ, hXW, hYZ, hYW, hZW⟩ := hdisj
  have hci := cond_indep_mass_directed_factorization_mass_of_d_separated (G.removeIncoming ↑X)
    (intervenedLocalMass localMass X b) (is_local_mass_family_intervened_local_mass hloc X b)
    (respects_parents_intervened_local_mass G hpar X b) Y Z (X ∪ W)
    (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩)
    (Finset.disjoint_union_right.2 ⟨hXZ.symm, hZW⟩) hsep
  rw [directed_factorization_mass_intervened_local_mass] at hci
  exact div_eq_div_of_cond_indep_mass (intervention_mass_nonneg hloc X b)
    (fun y hy ↦ intervention_mass_support hy) hci hpos

/-- GAPS 105.64, rule 2 of the do-calculus (action/observation exchange):
if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X \underline Z}`, then
`P(y | do(x), do(z), w) = P(y | do(x), z, w)`. The event `(z,w)` has positive
probability under `do(x)`.

The proof compares both sides with the mass in which the children of `Z` read the fixed values
of `b` on `Z`; that mass factorizes along `G_{\bar X \underline Z}`. -/
theorem cond_do_mass_rule_two [Fintype V] [Fintype S] (G : CausalGraph V)
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
  have hloc' := is_local_mass_family_intervened_local_mass hloc X b
  have hrloc : IsLocalMassFamily rloc :=
    ⟨fun v y s ↦ hloc'.1 v _ s, fun v y ↦ hloc'.2 v _⟩
  have hrpar : G2.RespectsParents rloc := by
    intro v y y' h
    show intervenedLocalMass localMass X b v (ow y) = intervenedLocalMass localMass X b v (ow y')
    apply respects_parents_intervened_local_mass G hpar X b v
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
    simp only [r, q, ← directed_factorization_mass_intervened_local_mass]
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
        rw [← directed_factorization_mass_intervened_local_mass]
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
  have hci := cond_indep_mass_directed_factorization_mass_of_d_separated G2 rloc hrloc hrpar Y Z
    (X ∪ W) (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩)
    (Finset.disjoint_union_right.2 ⟨hXZ.symm, hZW⟩) hsep
  have hr0 : ∀ y, 0 ≤ r y := fun y ↦ directed_factorization_mass_nonneg hrloc y
  have hrsupp : ∀ y, r y ≠ 0 → ∀ v ∈ X, y v = b v := by
    intro y hy v hv
    by_contra hne
    apply hy
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simp only [rloc, intervenedLocalMass, hv, ite_true, hne, ite_false]
  have hposr : 0 < marginalMass r (Z ∪ W) b := by
    rw [hmargA _ Finset.subset_union_left]
    exact hpos
  have key := div_eq_div_of_cond_indep_mass hr0 hrsupp hci hposr
  unfold condDoMass
  rw [← hmargB _ (Finset.disjoint_union_left.2 ⟨hYZ, hZW.symm⟩), ← hmargB _ hZW.symm]
  change _ = marginalMass q (Y ∪ (Z ∪ W)) b / marginalMass q (Z ∪ W) b
  rw [← hmargA _ (fun v hv ↦ by simp [hv]), ← hmargA _ Finset.subset_union_left]
  exact key.symm

end CKSD
