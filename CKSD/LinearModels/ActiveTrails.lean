module

public import CKSD.LinearModels.Causal

/-!
# Trails in finite causal graphs

A trail of length `n` in a causal graph is a sequence `q 0, …, q n` of vertices, consecutive
ones adjacent, in which repetitions are allowed. A trail is read off a function `ℕ → V`; only
the values at `0, …, n` matter. Its interior vertices are classified as colliders
(`q (k - 1) → q k ← q (k + 1)`) or noncolliders, and a trail *with* predicates `P` and `N`
requires every interior collider to satisfy `P` and every interior noncollider to satisfy `N`.

With `P` the ancestral closure of `C` and `N` the complement of `C`, this is the active-trail
condition of d-separation. The main results are:

* an active trail between `A` and `B` can be shortened to an active path, that is, to an
  injective active trail (`CausalGraph.exists_injective_activeTrail`);
* a trail between `A` and `B` whose noncolliders avoid `C` and whose colliders lie in the
  ancestral closure of `A ∪ B ∪ C` can be turned into an active trail
  (`CausalGraph.exists_activeTrail_of_semiActive`);
* consequently such a trail cannot exist when `A` and `B` are d-separated by `C`
  (`CausalGraph.false_of_dSeparated_of_semiActiveTrail`).

These are the graph-theoretic steps in the proof that a recursively factorizing mass function
satisfies the global directed Markov property (Lauritzen, *Graphical Models*, 1996, §3.2).
-/

@[expose] public section

noncomputable section

open Set

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V : Type*}

namespace CausalGraph

/-- Status of the middle vertex `b` of consecutive trail vertices `a, b, c`: if `b` is a
collider (`a → b ← c`) it must satisfy `P`, otherwise it must satisfy `N`. -/
def TripleStatus (G : CausalGraph V) (P N : V → Prop) (a b c : V) : Prop :=
  if G.edge a b ∧ G.edge c b then P b else N b

/-- A trail `q 0, …, q n` whose interior colliders satisfy `P` and whose interior noncolliders
satisfy `N`. Repeated vertices are allowed. -/
def IsTrailWith (G : CausalGraph V) (P N : V → Prop) (n : ℕ) (q : ℕ → V) : Prop :=
  (∀ k < n, G.Adjacent (q k) (q (k + 1))) ∧
    ∀ k, k + 2 ≤ n → G.TripleStatus P N (q k) (q (k + 1)) (q (k + 2))

/-- A vertex lies in `C` or is an ancestor of a vertex of `C`. -/
def MemAncestorClosure (G : CausalGraph V) (C : Set V) (v : V) : Prop :=
  ∃ z ∈ C, z = v ∨ G.IsDescendant v z

/-- A directed path from `v` to a vertex of `T` whose vertices after `v` avoid `C`. -/
def ForwardReach (G : CausalGraph V) (C T : Set V) (v : V) : Prop :=
  ∃ (m : ℕ) (r : ℕ → V), r 0 = v ∧ r m ∈ T ∧ (∀ i < m, G.edge (r i) (r (i + 1))) ∧
    ∀ i, 0 < i → i ≤ m → r i ∉ C

/-- Concatenation of a trail `q₁` of length `n₁` with a trail `q₂`. -/
def trailAppend (n₁ : ℕ) (q₁ q₂ : ℕ → V) : ℕ → V :=
  fun k ↦ if k ≤ n₁ then q₁ k else q₂ (k - n₁)

/-- A directed acyclic graph has no loops. -/
theorem not_edge_self (G : CausalGraph V) (v : V) : ¬ G.edge v v :=
  fun h ↦ G.acyclic v (Relation.TransGen.single h)

/-- A directed acyclic graph has no two-cycles. -/
theorem not_edge_of_edge (G : CausalGraph V) {a b : V} (h : G.edge a b) : ¬ G.edge b a :=
  fun h' ↦ G.acyclic a (Relation.TransGen.tail (Relation.TransGen.single h) h')

/-- The middle vertex of a triple is a noncollider when it has an arrow towards its right
neighbour. -/
theorem tripleStatus_of_edge_right (G : CausalGraph V) {P N : V → Prop} {a b c : V}
    (h : G.edge b c) (hN : N b) : G.TripleStatus P N a b c := by
  unfold TripleStatus
  rw [ite_eq_right fun hc ↦ G.not_edge_of_edge h hc.2]
  exact hN

/-- The middle vertex of a triple is a noncollider when it has an arrow towards its left
neighbour. -/
theorem tripleStatus_of_edge_left (G : CausalGraph V) {P N : V → Prop} {a b c : V}
    (h : G.edge b a) (hN : N b) : G.TripleStatus P N a b c := by
  unfold TripleStatus
  rw [ite_eq_right fun hc ↦ G.not_edge_of_edge h hc.1]
  exact hN

/-- The status of a triple does not depend on its orientation. -/
theorem tripleStatus_comm (G : CausalGraph V) {P N : V → Prop} {a b c : V} :
    G.TripleStatus P N a b c ↔ G.TripleStatus P N c b a := by
  unfold TripleStatus
  by_cases h1 : G.edge a b <;> by_cases h2 : G.edge c b <;> simp [h1, h2]

/-- `trailAppend` agrees with the first trail up to its length. -/
theorem trailAppend_of_le {n₁ k : ℕ} (q₁ q₂ : ℕ → V) (hk : k ≤ n₁) :
    trailAppend n₁ q₁ q₂ k = q₁ k := ite_eq_left hk

/-- `trailAppend` agrees with the shifted second trail from the junction on. -/
theorem trailAppend_of_ge {n₁ k : ℕ} {q₁ q₂ : ℕ → V} (hj : q₁ n₁ = q₂ 0) (hk : n₁ ≤ k) :
    trailAppend n₁ q₁ q₂ k = q₂ (k - n₁) := by
  unfold trailAppend
  split_ifs with h
  · have : k = n₁ := le_antisymm h hk
    subst this
    simpa using hj
  · rfl

namespace IsTrailWith

variable {G : CausalGraph V} {P N : V → Prop}

/-- The reverse of a trail is a trail. -/
theorem rev {n : ℕ} {q : ℕ → V} (h : G.IsTrailWith P N n q) :
    G.IsTrailWith P N n (fun k ↦ q (n - k)) := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · have := h.1 (n - k - 1) (by omega)
    have e1 : n - k - 1 + 1 = n - k := by omega
    have e2 : n - (k + 1) = n - k - 1 := by omega
    rw [e1] at this
    simp only [e2]
    exact Or.symm this
  · have := h.2 (n - k - 2) (by omega)
    have e1 : n - k - 2 + 1 = n - (k + 1) := by omega
    have e2 : n - k - 2 + 2 = n - k := by omega
    have e3 : n - (k + 2) = n - k - 2 := by omega
    rw [e1, e2] at this
    simp only [e3]
    exact G.tripleStatus_comm.1 this

/-- A suffix of a trail, shifted to start at `0`, is a trail. -/
theorem shift {n m : ℕ} {q : ℕ → V} (h : G.IsTrailWith P N n q) (hm : m ≤ n) :
    G.IsTrailWith P N (n - m) (fun k ↦ q (k + m)) := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · have := h.1 (k + m) (by omega)
    simp only [Nat.add_right_comm k 1 m]
    exact this
  · have := h.2 (k + m) (by omega)
    simp only [Nat.add_right_comm k 1 m, Nat.add_right_comm k 2 m]
    exact this

/-- A prefix of a trail is a trail. -/
theorem trunc {n m : ℕ} {q : ℕ → V} (h : G.IsTrailWith P N n q) (hm : m ≤ n) :
    G.IsTrailWith P N m q :=
  ⟨fun k hk ↦ h.1 k (by omega), fun k hk ↦ h.2 k (by omega)⟩

/-- Concatenation of two trails meeting at a vertex with admissible status is a trail. -/
theorem append {n₁ n₂ : ℕ} {q₁ q₂ : ℕ → V} (h₁ : G.IsTrailWith P N n₁ q₁)
    (h₂ : G.IsTrailWith P N n₂ q₂) (hj : q₁ n₁ = q₂ 0)
    (hst : 0 < n₁ → 0 < n₂ → G.TripleStatus P N (q₁ (n₁ - 1)) (q₁ n₁) (q₂ 1)) :
    G.IsTrailWith P N (n₁ + n₂) (trailAppend n₁ q₁ q₂) := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · by_cases hk' : k + 1 ≤ n₁
    · rw [trailAppend_of_le _ _ hk', trailAppend_of_le _ _ (by omega)]
      exact h₁.1 k (by omega)
    · rw [trailAppend_of_ge hj (by omega), trailAppend_of_ge hj (by omega)]
      have e : k + 1 - n₁ = k - n₁ + 1 := by omega
      rw [e]
      exact h₂.1 _ (by omega)
  · by_cases hk' : k + 2 ≤ n₁
    · rw [trailAppend_of_le _ _ hk', trailAppend_of_le _ _ (by omega),
        trailAppend_of_le _ _ (by omega)]
      exact h₁.2 k hk'
    by_cases hk'' : n₁ ≤ k
    · rw [trailAppend_of_ge hj hk'', trailAppend_of_ge hj (by omega),
        trailAppend_of_ge hj (by omega)]
      have e1 : k + 1 - n₁ = k - n₁ + 1 := by omega
      have e2 : k + 2 - n₁ = k - n₁ + 2 := by omega
      rw [e1, e2]
      exact h₂.2 _ (by omega)
    · have e0 : k = n₁ - 1 := by omega
      rw [trailAppend_of_le _ _ (by omega), trailAppend_of_le _ _ (by omega),
        trailAppend_of_ge hj (by omega)]
      have e1 : k + 2 - n₁ = 1 := by omega
      have e2 : k + 1 = n₁ := by omega
      rw [e1, e2, e0]
      exact hst (by omega) (by omega)

/-- Extending a trail by one adjacent vertex, with an admissible status at the old endpoint,
gives a trail. -/
theorem snoc {n : ℕ} {q : ℕ → V} {w : V} (h : G.IsTrailWith P N n q)
    (hadj : G.Adjacent (q n) w) (hst : 0 < n → G.TripleStatus P N (q (n - 1)) (q n) w) :
    ∃ q' : ℕ → V, G.IsTrailWith P N (n + 1) q' ∧ (∀ k ≤ n, q' k = q k) ∧ q' (n + 1) = w := by
  have h₂ : G.IsTrailWith P N 1 (fun k ↦ if k = 0 then q n else w) :=
    ⟨fun k hk ↦ by
      obtain rfl : k = 0 := by omega
      simpa using hadj, fun k hk ↦ by omega⟩
  refine ⟨_, h.append h₂ (by simp) fun h1 _ ↦ by simpa using hst h1, ?_, ?_⟩
  · exact fun k hk ↦ trailAppend_of_le _ _ hk
  · rw [trailAppend_of_ge (by simp) (by omega)]
    simp

end IsTrailWith

/-- A forward directed chain is a trail whose interior vertices are all noncolliders. -/
theorem isTrailWith_of_forward (G : CausalGraph V) {P N : V → Prop} {m : ℕ} {r : ℕ → V}
    (hf : ∀ i < m, G.edge (r i) (r (i + 1))) (hN : ∀ i, 0 < i → i < m → N (r i)) :
    G.IsTrailWith P N m r :=
  ⟨fun k hk ↦ Or.inl (hf k hk), fun k hk ↦
    G.tripleStatus_of_edge_right (hf (k + 1) (by omega)) (hN (k + 1) (by omega) (by omega))⟩

/-- Along a forward directed chain every later vertex is a descendant of the first. -/
theorem isDescendant_of_forward (G : CausalGraph V) {m : ℕ} {r : ℕ → V}
    (hf : ∀ i < m, G.edge (r i) (r (i + 1))) :
    ∀ i, 0 < i → i ≤ m → G.IsDescendant (r 0) (r i) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Relation.TransGen.single (hf 0 (by omega))
    · exact Relation.TransGen.tail (ih hpos (by omega)) (hf i (by omega))

/-- A nonempty directed path is a forward chain. -/
theorem exists_forward_of_isDescendant (G : CausalGraph V) {u t : V}
    (h : G.IsDescendant u t) :
    ∃ (m : ℕ) (r : ℕ → V), 0 < m ∧ r 0 = u ∧ r m = t ∧ ∀ i < m, G.edge (r i) (r (i + 1)) := by
  induction h with
  | @single b h =>
    exact ⟨1, fun k ↦ if k = 0 then u else b, one_pos, rfl, by simp, fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa using h⟩
  | @tail b c _ hbc ih =>
    obtain ⟨m, r, hm, h0, hmb, hf⟩ := ih
    refine ⟨m + 1, fun k ↦ if k ≤ m then r k else c, by omega, by simpa using h0,
      by simp, fun i hi ↦ ?_⟩
    by_cases hi' : i + 1 ≤ m
    · simp only [ite_eq_left hi', ite_eq_left (show i ≤ m by omega)]
      exact hf i (by omega)
    · obtain rfl : i = m := by omega
      simp only [le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false, hmb]
      exact hbc

/-- If `v` lies outside the ancestral closure of `C` and is `t ∈ T` or an ancestor of some
`t ∈ T`, then a directed path from `v` reaches `T` avoiding `C`. -/
theorem forwardReach_of_not_memAncestorClosure (G : CausalGraph V) {C T : Set V} {v : V}
    (hv : ¬ G.MemAncestorClosure C v) (ht : ∃ t ∈ T, t = v ∨ G.IsDescendant v t) :
    G.ForwardReach C T v := by
  obtain ⟨t, htT, rfl | hvt⟩ := ht
  · exact ⟨0, fun _ ↦ t, rfl, htT, fun i hi ↦ absurd hi (Nat.not_lt_zero _),
      fun i hi hi' ↦ by omega⟩
  · obtain ⟨m, r, _, h0, hm, hf⟩ := G.exists_forward_of_isDescendant hvt
    refine ⟨m, r, h0, hm ▸ htT, hf, fun i hi hi' hC ↦ hv ⟨r i, hC, Or.inr ?_⟩⟩
    rw [← h0]
    exact G.isDescendant_of_forward hf i hi hi'

/-- Junction step of the shortening argument: cutting a loop `q i = q j` out of an active trail
leaves an admissible status at the junction. -/
theorem tripleStatus_of_loop (G : CausalGraph V) {C : Set V} {n : ℕ} {q : ℕ → V}
    (h : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) n q) {i j : ℕ} (hi : 0 < i)
    (hij : i < j) (hj : j < n) (hq : q i = q j) :
    G.TripleStatus (G.MemAncestorClosure C) (· ∉ C) (q (i - 1)) (q i) (q (j + 1)) := by
  have hsi := h.2 (i - 1) (by omega)
  have hsj := h.2 (j - 1) (by omega)
  have e1 : i - 1 + 1 = i := by omega
  have e2 : i - 1 + 2 = i + 1 := by omega
  have e3 : j - 1 + 1 = j := by omega
  have e4 : j - 1 + 2 = j + 1 := by omega
  rw [e1, e2] at hsi
  rw [e3, e4, ← hq] at hsj
  unfold TripleStatus at hsi hsj ⊢
  by_cases hw : q i ∈ C
  · have hc1 : G.edge (q (i - 1)) (q i) := by
      by_contra hc
      rw [ite_eq_right fun hh ↦ hc hh.1] at hsi
      exact hsi hw
    have hc2 : G.edge (q (j + 1)) (q i) := by
      by_contra hc
      rw [ite_eq_right fun hh ↦ hc hh.2] at hsj
      exact hsj hw
    rw [ite_eq_left ⟨hc1, hc2⟩]
    exact ⟨q i, hw, Or.inl rfl⟩
  split_ifs with hcol
  swap
  · exact hw
  by_contra hP
  -- the loop leaves `q i` forwards and returns to it backwards
  have hfwd : G.edge (q i) (q (i + 1)) := by
    rcases h.1 i (by omega) with he | he
    · exact he
    · exact absurd (by rw [ite_eq_left ⟨hcol.1, he⟩] at hsi; exact hsi) hP
  have hbwd : G.edge (q (j - 1 + 1)) (q (j - 1)) := by
    rw [e3, ← hq]
    rcases h.1 (j - 1) (by omega) with he | he
    · rw [e3, ← hq] at he
      exact absurd (by rw [ite_eq_left ⟨he, hcol.2⟩] at hsj; exact hsj) hP
    · rwa [e3, ← hq] at he
  -- first backward step after `i`
  have hex : ∃ m, i ≤ m ∧ m < j ∧ G.edge (q (m + 1)) (q m) := ⟨j - 1, by omega, by omega, hbwd⟩
  let m := Nat.find hex
  have hm : i ≤ m ∧ m < j ∧ G.edge (q (m + 1)) (q m) := Nat.find_spec hex
  have hmin : ∀ k, i ≤ k → k < m → G.edge (q k) (q (k + 1)) := by
    intro k hk hkm
    have hnot := Nat.find_min hex hkm
    rcases h.1 k (by omega) with he | he
    · exact he
    · exact absurd ⟨hk, by omega, he⟩ hnot
  have hmi : i < m := by
    rcases Nat.eq_or_lt_of_le hm.1 with he | he
    · exact absurd (he ▸ hm.2.2) (G.not_edge_of_edge hfwd)
    · exact he
  -- descendants along the forward run
  have hdesc : ∀ k, i < k → k ≤ m → G.IsDescendant (q i) (q k) := by
    have := G.isDescendant_of_forward (r := fun k ↦ q (k + i)) (m := m - i)
      (fun k hk ↦ by simpa [Nat.add_right_comm k 1 i] using hmin (k + i) (by omega) (by omega))
    intro k hk hkm
    have h' := this (k - i) (by omega) (by omega)
    simpa [Nat.sub_add_cancel hk.le] using h'
  -- `q m` is an active collider, hence in the ancestral closure of `C`
  have hsm := h.2 (m - 1) (by omega)
  have f1 : m - 1 + 1 = m := by omega
  have f2 : m - 1 + 2 = m + 1 := by omega
  rw [f1, f2] at hsm
  unfold TripleStatus at hsm
  have hprev : G.edge (q (m - 1)) (q m) := by
    have := hmin (m - 1) (by omega) (by omega)
    rwa [f1] at this
  rw [ite_eq_left ⟨hprev, hm.2.2⟩] at hsm
  obtain ⟨z, hz, hz'⟩ := hsm
  refine hP ⟨z, hz, Or.inr ?_⟩
  rcases hz' with rfl | hz'
  · exact hdesc m hmi le_rfl
  · exact (hdesc m hmi le_rfl).trans hz'

/-- An active trail can be shortened to an injective active trail with the same endpoints. -/
theorem exists_injective_activeTrail (G : CausalGraph V) (C : Set V) :
    ∀ (n : ℕ) (q : ℕ → V), G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) n q →
      ∃ (m : ℕ) (r : ℕ → V), G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) m r ∧
        r 0 = q 0 ∧ r m = q n ∧ ∀ i ≤ m, ∀ j ≤ m, r i = r j → i = j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q h
  by_cases hinj : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j
  · exact ⟨n, q, h, rfl, rfl, hinj⟩
  push Not at hinj
  obtain ⟨i, j, hij, hq⟩ : ∃ i j, i < j ∧ j ≤ n ∧ q i = q j := by
    obtain ⟨i, hi, j, hj, hq, hne⟩ := hinj
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact ⟨i, j, h', hj, hq⟩
    · exact ⟨j, i, h', hi, hq.symm⟩
  obtain ⟨hjn, hq⟩ := hq
  set d := j - i with hd
  let q' : ℕ → V := fun k ↦ if k ≤ i then q k else q (k + d)
  have hq'le : ∀ k ≤ i, q' k = q k := fun k hk ↦ ite_eq_left hk
  have hq'ge : ∀ k, i ≤ k → q' k = q (k + d) := by
    intro k hk
    by_cases hk' : k ≤ i
    · have : k = i := le_antisymm hk' hk
      subst this
      rw [hq'le k le_rfl, hq]
      congr 1
      omega
    · exact ite_eq_right hk'
  have htr : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) (n - d) q' := by
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · by_cases hk' : k + 1 ≤ i
      · rw [hq'le k (by omega), hq'le (k + 1) hk']
        exact h.1 k (by omega)
      · rw [hq'ge k (by omega), hq'ge (k + 1) (by omega), Nat.add_right_comm]
        exact h.1 (k + d) (by omega)
    · by_cases hk' : k + 2 ≤ i
      · rw [hq'le k (by omega), hq'le (k + 1) (by omega), hq'le (k + 2) hk']
        exact h.2 k (by omega)
      by_cases hk'' : i ≤ k
      · rw [hq'ge k hk'', hq'ge (k + 1) (by omega), hq'ge (k + 2) (by omega),
          Nat.add_right_comm k 1 d, Nat.add_right_comm k 2 d]
        exact h.2 (k + d) (by omega)
      · have e0 : k = i - 1 := by omega
        rw [hq'le k (by omega), hq'le (k + 1) (by omega), hq'ge (k + 2) (by omega)]
        have e1 : k + 2 + d = j + 1 := by omega
        have e2 : k + 1 = i := by omega
        rw [e1, e2, e0]
        exact G.tripleStatus_of_loop h (by omega) hij (by omega) hq
  obtain ⟨m, r, hr, hr0, hrm, hrinj⟩ := ih (n - d) (by omega) q' htr
  refine ⟨m, r, hr, ?_, ?_, hrinj⟩
  · rw [hr0, hq'le 0 (Nat.zero_le _)]
  · rw [hrm, hq'ge (n - d) (by omega)]
    congr 1
    omega

/-- An injective active trail is an active path. -/
theorem isActivePath_of_isTrailWith (G : CausalGraph V) {C : Set V} {n : ℕ} {q : ℕ → V}
    (h : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) n q)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j) :
    G.IsActivePath C (fun i : Fin (n + 1) ↦ q i) := by
  refine ⟨fun i j hij ↦ Fin.ext (hinj i (by omega) j (by omega) hij), fun i ↦ ?_, fun i ↦ ?_⟩
  · simpa [Adjacent] using h.1 i i.isLt
  · have := h.2 i (by omega)
    simpa [TripleStatus, MemAncestorClosure] using this

/-- On a trail that leaves `q i` along an outgoing arrow and arrives at `q j` against an arrow
out of `q j`, some interior vertex `q m` with `i < m < j` is a collider descending from `q i`. -/
theorem exists_collider_of_forward_backward (G : CausalGraph V) {P N : V → Prop} {n : ℕ}
    {q : ℕ → V} (h : G.IsTrailWith P N n q) {i j : ℕ} (hij : i < j) (hjn : j ≤ n)
    (hfwd : G.edge (q i) (q (i + 1))) (hbwd : G.edge (q j) (q (j - 1))) :
    ∃ m, i < m ∧ m < j ∧ P (q m) ∧ G.IsDescendant (q i) (q m) := by
  have hex : ∃ m, i ≤ m ∧ m < j ∧ G.edge (q (m + 1)) (q m) :=
    ⟨j - 1, by omega, by omega, by rw [show j - 1 + 1 = j by omega]; exact hbwd⟩
  have hm : i ≤ Nat.find hex ∧ Nat.find hex < j ∧
      G.edge (q (Nat.find hex + 1)) (q (Nat.find hex)) := Nat.find_spec hex
  have hmin : ∀ k, i ≤ k → k < Nat.find hex → G.edge (q k) (q (k + 1)) := by
    intro k hk hkm
    have hnot := Nat.find_min hex hkm
    rcases h.1 k (by omega) with he | he
    · exact he
    · exact absurd ⟨hk, by omega, he⟩ hnot
  have hmi : i < Nat.find hex := by
    rcases Nat.eq_or_lt_of_le hm.1 with he | he
    · rw [← he] at hm
      exact absurd hm.2.2 (G.not_edge_of_edge hfwd)
    · exact he
  have hdesc : G.IsDescendant (q i) (q (Nat.find hex)) := by
    have := G.isDescendant_of_forward (r := fun k ↦ q (k + i)) (m := Nat.find hex - i)
      (fun k hk ↦ by simpa [Nat.add_right_comm k 1 i] using hmin (k + i) (by omega) (by omega))
      (Nat.find hex - i) (by omega) le_rfl
    simpa [Nat.sub_add_cancel hm.1] using this
  refine ⟨Nat.find hex, hmi, hm.2.1, ?_, hdesc⟩
  have hs := h.2 (Nat.find hex - 1) (by omega)
  have f1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  have f2 : Nat.find hex - 1 + 2 = Nat.find hex + 1 := by omega
  rw [f1, f2] at hs
  have hprev : G.edge (q (Nat.find hex - 1)) (q (Nat.find hex)) := by
    have := hmin (Nat.find hex - 1) (by omega) (by omega)
    rwa [f1] at this
  unfold TripleStatus at hs
  rwa [ite_eq_left ⟨hprev, hm.2.2⟩] at hs

/-- An active path, read as a function on `ℕ`, is an injective active trail. -/
theorem isTrailWith_of_isActivePath (G : CausalGraph V) {C : Set V} {n : ℕ}
    {p : Fin (n + 1) → V} (h : G.IsActivePath C p) :
    G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) n (fun k ↦ p ⟨min k n, by omega⟩) ∧
      ∀ i ≤ n, ∀ j ≤ n, p ⟨min i n, by omega⟩ = p ⟨min j n, by omega⟩ → i = j := by
  refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, fun i hi j hj hij ↦ ?_⟩
  · have := h.2.1 ⟨k, hk⟩
    have e1 : (⟨min k n, by omega⟩ : Fin (n + 1)) = (⟨k, hk⟩ : Fin n).castSucc :=
      Fin.ext (by simp; omega)
    have e2 : (⟨min (k + 1) n, by omega⟩ : Fin (n + 1)) = (⟨k, hk⟩ : Fin n).succ :=
      Fin.ext (by simp; omega)
    show G.Adjacent (p ⟨min k n, _⟩) (p ⟨min (k + 1) n, _⟩)
    rw [e1, e2]
    exact this
  · have := h.2.2 ⟨k, by omega⟩
    have e1 : (⟨min k n, by omega⟩ : Fin (n + 1)) = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
    have e2 : (⟨min (k + 1) n, by omega⟩ : Fin (n + 1)) = ⟨k + 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    have e3 : (⟨min (k + 2) n, by omega⟩ : Fin (n + 1)) = ⟨k + 2, by omega⟩ :=
      Fin.ext (by simp; omega)
    show G.TripleStatus _ _ (p ⟨min k n, _⟩) (p ⟨min (k + 1) n, _⟩) (p ⟨min (k + 2) n, _⟩)
    rw [e1, e2, e3]
    exact this
  · have := Fin.ext_iff.1 (h.1 hij)
    simp only at this
    omega

/-- A trail between `A` and `B` whose noncolliders avoid `C` and whose colliders lie in a set
`D` all of whose vertices outside the ancestral closure of `C` are ancestors of `A ∪ B` (or lie
in it) can be modified into an active trail between `A` and `B`. -/
theorem exists_activeTrail_of_semiActive (G : CausalGraph V) {A B C D : Set V}
    (hAC : ∀ a ∈ A, a ∉ C) (hBC : ∀ b ∈ B, b ∉ C)
    (hD : ∀ v ∈ D, ¬ G.MemAncestorClosure C v → ∃ t ∈ A ∪ B, t = v ∨ G.IsDescendant v t)
    {n : ℕ} {q : ℕ → V} (h : G.IsTrailWith (· ∈ D) (· ∉ C) n q) (h0 : q 0 ∈ A)
    (hn : q n ∈ B) :
    ∃ (m : ℕ) (r : ℕ → V), G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) m r ∧ r 0 ∈ A ∧
      r m ∈ B := by
  -- bad colliders: interior colliders outside the ancestral closure of `C`
  let bad : ℕ → Prop := fun k ↦ 0 < k ∧ k < n ∧ G.edge (q (k - 1)) (q k) ∧
    G.edge (q (k + 1)) (q k) ∧ ¬ G.MemAncestorClosure C (q k)
  have hbad : ∀ k, bad k → G.ForwardReach C A (q k) ∨ G.ForwardReach C B (q k) := by
    rintro k ⟨hk0, hkn, he1, he2, hk⟩
    have hs := h.2 (k - 1) (by omega)
    have f1 : k - 1 + 1 = k := by omega
    have f2 : k - 1 + 2 = k + 1 := by omega
    rw [f1, f2] at hs
    unfold TripleStatus at hs
    rw [ite_eq_left ⟨he1, he2⟩] at hs
    obtain ⟨t, ht, ht'⟩ := hD _ hs hk
    rcases ht with ht | ht
    · exact Or.inl (G.forwardReach_of_not_memAncestorClosure hk ⟨t, ht, ht'⟩)
    · exact Or.inr (G.forwardReach_of_not_memAncestorClosure hk ⟨t, ht, ht'⟩)
  have hrefl : ∀ {T : Set V} {v : V}, v ∈ T → G.ForwardReach C T v := fun hv ↦
    ⟨0, fun _ ↦ _, rfl, hv, fun i hi ↦ absurd hi (Nat.not_lt_zero _), fun i hi hi' ↦ by omega⟩
  have hexB : ∃ k, (k = n ∨ bad k) ∧ G.ForwardReach C B (q k) := ⟨n, Or.inl rfl, hrefl hn⟩
  let kB := Nat.find hexB
  have hkB : (kB = n ∨ bad kB) ∧ G.ForwardReach C B (q kB) := Nat.find_spec hexB
  have hkBn : kB ≤ n := Nat.find_min' hexB ⟨Or.inl rfl, hrefl hn⟩
  let PA : ℕ → Prop := fun k ↦ (k = 0 ∨ bad k) ∧ G.ForwardReach C A (q k)
  let kA := Nat.findGreatest PA kB
  have hkA : PA kA := Nat.findGreatest_spec (P := PA) (Nat.zero_le _) ⟨Or.inl rfl, hrefl h0⟩
  have hkAB : kA ≤ kB := Nat.findGreatest_le kB
  have hnotbad : ∀ k, kA < k → k < kB → ¬ bad k := by
    intro k hk1 hk2 hk
    rcases hbad k hk with hr | hr
    · exact absurd (Nat.le_findGreatest (P := PA) hk2.le ⟨Or.inr hk, hr⟩) (by omega)
    · exact Nat.find_min hexB hk2 ⟨Or.inr hk, hr⟩
  have hnC : ∀ k, (k = 0 ∨ k = n ∨ bad k) → q k ∉ C := by
    rintro k (rfl | rfl | ⟨-, -, -, -, hk⟩)
    · exact hAC _ h0
    · exact hBC _ hn
    · exact fun hC ↦ hk ⟨q k, hC, Or.inl rfl⟩
  have hkAC : q kA ∉ C := hnC kA (hkA.1.elim Or.inl fun hb ↦ Or.inr (Or.inr hb))
  have hkBC : q kB ∉ C := hnC kB (hkB.1.elim (fun h ↦ Or.inr (Or.inl h)) fun hb ↦ Or.inr (Or.inr hb))
  obtain ⟨mA, rA, hrA0, hrAm, hrAf, hrAC⟩ := hkA.2
  obtain ⟨mB, rB, hrB0, hrBm, hrBf, hrBC⟩ := hkB.2
  -- the three pieces
  have hT1 : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) mA (fun k ↦ rA (mA - k)) :=
    (G.isTrailWith_of_forward hrAf fun i hi hi' ↦ hrAC i hi hi'.le).rev
  have hT3 : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) mB rB :=
    G.isTrailWith_of_forward hrBf fun i hi hi' ↦ hrBC i hi hi'.le
  have hT2 : G.IsTrailWith (G.MemAncestorClosure C) (· ∉ C) (kB - kA) (fun k ↦ q (k + kA)) := by
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · have := h.1 (k + kA) (by omega)
      simpa [Nat.add_right_comm k 1 kA] using this
    · have hs := h.2 (k + kA) (by omega)
      simp only [Nat.add_right_comm k 1 kA, Nat.add_right_comm k 2 kA]
      have hnb := hnotbad (k + kA + 1) (by omega) (by omega)
      unfold TripleStatus at hs ⊢
      split_ifs at hs ⊢ with hc
      · by_contra hP
        refine hnb ⟨by omega, by omega, ?_, ?_, hP⟩
        · have e : k + kA + 1 - 1 = k + kA := by omega
          rw [e]
          exact hc.1
        · exact hc.2
      · exact hs
  have hT12 := hT1.append hT2 (by simp [hrA0]) fun h1 _ ↦ by
    simp only [Nat.sub_self]
    have e : mA - (mA - 1) = 1 := by omega
    rw [e]
    exact G.tripleStatus_of_edge_left (hrAf 0 h1) (by rw [hrA0]; exact hkAC)
  have hjunc : trailAppend mA (fun k ↦ rA (mA - k)) (fun k ↦ q (k + kA)) (mA + (kB - kA)) =
      rB 0 := by
    rw [trailAppend_of_ge (by simp [hrA0]) (by omega), hrB0]
    congr 1
    omega
  have hT := hT12.append hT3 hjunc fun _ h2 ↦ by
    rw [hjunc]
    exact G.tripleStatus_of_edge_right (hrBf 0 h2) (hrB0 ▸ hkBC)
  refine ⟨_, _, hT, ?_, ?_⟩
  · rw [trailAppend_of_le _ _ (Nat.zero_le _), trailAppend_of_le _ _ (Nat.zero_le _)]
    simpa using hrAm
  · rw [trailAppend_of_ge hjunc (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hrBm

/-- If `A` and `B` are d-separated by `C`, there is no trail between `A` and `B` whose
noncolliders avoid `C` and whose colliders lie in a set `D` all of whose vertices outside the
ancestral closure of `C` are ancestors of `A ∪ B` or lie in it. -/
theorem false_of_dSeparated_of_semiActiveTrail (G : CausalGraph V) {A B C D : Set V}
    (hsep : G.DSeparated A B C) (hAC : ∀ a ∈ A, a ∉ C) (hBC : ∀ b ∈ B, b ∉ C)
    (hD : ∀ v ∈ D, ¬ G.MemAncestorClosure C v → ∃ t ∈ A ∪ B, t = v ∨ G.IsDescendant v t)
    {n : ℕ} {q : ℕ → V} (h : G.IsTrailWith (· ∈ D) (· ∉ C) n q) (h0 : q 0 ∈ A)
    (hn : q n ∈ B) : False := by
  obtain ⟨m, r, hr, hr0, hrm⟩ := G.exists_activeTrail_of_semiActive hAC hBC hD h h0 hn
  obtain ⟨m', r', hr', hr'0, hr'm, hinj⟩ := G.exists_injective_activeTrail C m r hr
  refine hsep m' (fun i ↦ r' i) ?_ ?_ (G.isActivePath_of_isTrailWith hr' hinj)
  · simpa [hr'0] using hr0
  · simpa [hr'm] using hrm

end CausalGraph

end CKSD
