module

public import CKSD.LinearModels.DirectedGraphical.Markov

/-!
# Augmentation and rule 3 of the do-calculus

Augmenting `G_{\bar X}` by an intervention indicator with an arrow into each vertex of `Z`
turns the deletion of the action `do(Z = z)` into the deletion of an observation, and yields
rule 3 of the do-calculus from the global directed Markov property.

## Main definitions

* `CKSD.CausalGraph.nonAncestorPart`: the set `Z(W)` of vertices of `Z` that are not ancestors
  of `W` in `G_{\bar X}`.
* `CKSD.CausalGraph.augment`: the graph augmented by an intervention indicator.

## Main results

* `CKSD.CausalGraph.dSeparated_augment_of_rule_three`: the graph-theoretic step of rule 3.
* `CKSD.condDoMass_rule_three`: rule 3 (insertion and deletion of actions),
  `P(y | do(x), do(z), w) = P(y | do(x), w)` when `Y` and `Z` are d-separated by `X ∪ W` in
  `G_{\bar X, \overline{Z(W)}}`.

## References

* J. Pearl, *Causality*, 2nd ed., Cambridge University Press, 2009, §3.4.

Source: GAPS 105.64.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

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
def augmentedLocalMass (localMass : V → (V → S) → S → ℝ) (X Z : Finset V)
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
theorem respectsParents_augmentedLocalMass (G : CausalGraph V)
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
theorem directedFactorizationMass_augmentedLocalMass [Fintype V]
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
private theorem sum_option_pi [Fintype V] [Fintype S]
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
theorem CausalGraph.dSeparated_augment_of_rule_three (G : CausalGraph V)
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
  exact hsep.symm.false_of_isTrailWith hrtr hr0 hrn

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
    ((Finset.disjoint_map e).2 (Finset.disjoint_union_right.2 ⟨hXY.symm, hYW⟩))
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

end CKSD
