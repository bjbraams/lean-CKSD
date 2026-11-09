module

public import CKSD.Learning.RandomGraphs.Connectivity

/-!
# Small components of the subcritical binomial random graph

For `p = c/n` with `0 ≤ c < 1`, every component of `G(n, p)` has `O(log n)` vertices with
probability tending to one.

The proof explores the component of a vertex `v`: a state `(D, P)` consists of discovered and
processed vertices, and each step processes the least discovered unprocessed vertex `u`,
revealing which undiscovered vertices are adjacent to `u`. A history of `m` steps is a sequence
of newly discovered sets; it is realized by the event that the revealed pairs are edges and the
remaining pairs from `u` to undiscovered vertices are not, which has probability
`p^{#found} (1-p)^{#missed}` (`binomialRandom_real_exploreEvent`). If the component has more
than `m` vertices, the first `m` steps discover at least `m` new vertices. Weighting each
history by `λ^{#found}` and summing step by step (binomial theorem) gives
`P(|C(v)| > m) ≤ λ^{-m} (1 - p + pλ)^{nm}`, which for `λ = 1/c'` with `c' = max(c, 1/2)` is at
most `(c' e^{1-c'})^m`, a geometric rate below one.

## Main results

* `CKSD.binomialRandom_real_reachableSet_card_le`: the exponential tail bound for the size of the
  component of a vertex.
* `CKSD.exists_tendsto_binomialRandom_components_le_log'`: the subcritical phase of GAPS 107.47.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set unitInterval
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {V : Type*} [Fintype V] [LinearOrder V]

/-! ### The exploration process -/

/-- One step of the exploration process. A state is a pair `(D, P)` of discovered and processed
vertices; the least discovered unprocessed vertex is processed and the set `a` is added to the
discovered vertices. If every discovered vertex is processed, the state does not change. -/
def exploreStep (a : Finset V) (s : Finset V × Finset V) : Finset V × Finset V :=
  if h : (s.1 \ s.2).Nonempty then (s.1 ∪ a, insert ((s.1 \ s.2).min' h) s.2) else s

/-- Admissible histories of `m` exploration steps from the state `s`: at every step some
discovered vertex is unprocessed and the newly discovered set is undiscovered so far. -/
def ExploreValid : (m : ℕ) → (Fin m → Finset V) → Finset V × Finset V → Prop
  | 0, _, _ => True
  | m + 1, N, s => (s.1 \ s.2).Nonempty ∧ N 0 ⊆ s.1ᶜ ∧
      ExploreValid m (Fin.tail N) (exploreStep (N 0) s)

/-- The pairs revealed as edges along a history: the processed vertex joined to the newly
discovered vertices. -/
def exploreFound : (m : ℕ) → (Fin m → Finset V) → Finset V × Finset V → Finset (Sym2 V)
  | 0, _, _ => ∅
  | m + 1, N, s => if h : (s.1 \ s.2).Nonempty then
      (N 0).image (fun w ↦ s((s.1 \ s.2).min' h, w)) ∪
        exploreFound m (Fin.tail N) (exploreStep (N 0) s) else ∅

/-- The pairs revealed as non-edges along a history: the processed vertex joined to the
undiscovered vertices that are not discovered at this step. -/
def exploreMissed : (m : ℕ) → (Fin m → Finset V) → Finset V × Finset V → Finset (Sym2 V)
  | 0, _, _ => ∅
  | m + 1, N, s => if h : (s.1 \ s.2).Nonempty then
      (s.1ᶜ \ N 0).image (fun w ↦ s((s.1 \ s.2).min' h, w)) ∪
        exploreMissed m (Fin.tail N) (exploreStep (N 0) s) else ∅

omit [Fintype V] in
/-- The exploration step is monotone in both coordinates. -/
theorem subset_exploreStep (a : Finset V) (s : Finset V × Finset V) :
    s.1 ⊆ (exploreStep a s).1 ∧ s.2 ⊆ (exploreStep a s).2 := by
  unfold exploreStep
  split_ifs
  · exact ⟨Finset.subset_union_left, Finset.subset_insert _ _⟩
  · exact ⟨le_rfl, le_rfl⟩

/-- Every revealed pair of a valid history from `s` joins an unprocessed vertex `x` to a
different, undiscovered vertex `y`. -/
theorem exploreFound_union_exploreMissed_spec (m : ℕ) :
    ∀ (N : Fin m → Finset V) (s : Finset V × Finset V), ExploreValid m N s →
      ∀ e ∈ exploreFound m N s ∪ exploreMissed m N s,
        ∃ x y, e = s(x, y) ∧ x ≠ y ∧ x ∉ s.2 ∧ y ∉ s.1 := by
  induction m with
  | zero => intro N s _ e he; simp [exploreFound, exploreMissed] at he
  | succ m ih =>
    rintro N s ⟨hne, hsub, hval⟩ e he
    have hmono := subset_exploreStep (N 0) s
    set u := (s.1 \ s.2).min' hne
    have hu : u ∈ s.1 \ s.2 := Finset.min'_mem _ hne
    simp only [exploreFound, exploreMissed, dite_eq_left hne, Finset.mem_union, Finset.mem_image]
      at he
    rcases he with (⟨w, hw, rfl⟩ | he) | (⟨w, hw, rfl⟩ | he)
    · have hw' : w ∉ s.1 := Finset.mem_compl.mp (hsub hw)
      exact ⟨u, w, rfl, fun h ↦ hw' (h ▸ (Finset.mem_sdiff.mp hu).1),
        (Finset.mem_sdiff.mp hu).2, hw'⟩
    · obtain ⟨x, y, rfl, hxy, hx, hy⟩ := ih _ _ hval e (Finset.mem_union_left _ he)
      exact ⟨x, y, rfl, hxy, fun h ↦ hx (hmono.2 h), fun h ↦ hy (hmono.1 h)⟩
    · have hw' : w ∉ s.1 := Finset.mem_compl.mp (Finset.mem_sdiff.mp hw).1
      exact ⟨u, w, rfl, fun h ↦ hw' (h ▸ (Finset.mem_sdiff.mp hu).1),
        (Finset.mem_sdiff.mp hu).2, hw'⟩
    · obtain ⟨x, y, rfl, hxy, hx, hy⟩ := ih _ _ hval e (Finset.mem_union_right _ he)
      exact ⟨x, y, rfl, hxy, fun h ↦ hx (hmono.2 h), fun h ↦ hy (hmono.1 h)⟩

/-- In a valid step from `s`, the processed vertex `u` is processed in the next state and
discovered in it, so it is an endpoint of no later revealed pair. -/
private theorem not_mem_later_of_valid {m : ℕ} {N : Fin (m + 1) → Finset V}
    {s : Finset V × Finset V} (hne : (s.1 \ s.2).Nonempty)
    (hval : ExploreValid m (Fin.tail N) (exploreStep (N 0) s)) (w : V) :
    s((s.1 \ s.2).min' hne, w) ∉ exploreFound m (Fin.tail N) (exploreStep (N 0) s) ∪
      exploreMissed m (Fin.tail N) (exploreStep (N 0) s) := by
  intro h
  obtain ⟨x, y, hxy, -, hx, hy⟩ := exploreFound_union_exploreMissed_spec m _ _ hval _ h
  have hu : (s.1 \ s.2).min' hne ∈ s.1 \ s.2 := Finset.min'_mem _ hne
  have hstep : exploreStep (N 0) s = (s.1 ∪ N 0, insert ((s.1 \ s.2).min' hne) s.2) := by
    simp [exploreStep, dite_eq_left hne]
  rw [hstep] at hx hy
  rcases Sym2.eq_iff.mp hxy with ⟨h1, -⟩ | ⟨h2, -⟩
  · rw [← h1] at hx
    exact hx (Finset.mem_insert_self _ _)
  · rw [← h2] at hy
    exact hy (Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1)

/-- Found and missed pairs of a valid history are disjoint. -/
theorem exploreFound_exploreMissed_props (m : ℕ) :
    ∀ (N : Fin m → Finset V) (s : Finset V × Finset V), ExploreValid m N s →
      Disjoint (exploreFound m N s) (exploreMissed m N s) := by
  induction m with
  | zero => intro N s _; simp [exploreFound]
  | succ m ih =>
    rintro N s ⟨hne, hsub, hval⟩
    simp only [exploreFound, exploreMissed, dite_eq_left hne]
    have hlater := not_mem_later_of_valid (N := N) hne hval
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    refine ⟨⟨?_, ?_⟩, ?_, ih _ _ hval⟩
    · rw [Finset.disjoint_left]
      simp only [Finset.mem_image, Finset.mem_sdiff]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', ⟨-, hw'⟩, h⟩
      have := Sym2.congr_right.mp h
      exact hw' (this ▸ hw)
    · rw [Finset.disjoint_left]
      simp only [Finset.mem_image]
      rintro _ ⟨w, -, rfl⟩ h
      exact hlater w (Finset.mem_union_right _ h)
    · rw [Finset.disjoint_left]
      rintro e he he'
      simp only [Finset.mem_image] at he'
      obtain ⟨w, -, rfl⟩ := he'
      exact hlater w (Finset.mem_union_left _ he)

/-- Cardinality recursion for found pairs. -/
theorem card_exploreFound_succ {m : ℕ} {N : Fin (m + 1) → Finset V} {s : Finset V × Finset V}
    (hval : ExploreValid (m + 1) N s) :
    (exploreFound (m + 1) N s).card =
      (N 0).card + (exploreFound m (Fin.tail N) (exploreStep (N 0) s)).card := by
  obtain ⟨hne, hsub, hval'⟩ := hval
  simp only [exploreFound, dite_eq_left hne]
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _
    (fun w w' h ↦ Sym2.congr_right.mp h)]
  rw [Finset.disjoint_left]
  rintro _ he h
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp he
  exact not_mem_later_of_valid (N := N) hne hval' w (Finset.mem_union_left _ h)

/-- Cardinality recursion for missed pairs. -/
theorem card_exploreMissed_succ {m : ℕ} {N : Fin (m + 1) → Finset V} {s : Finset V × Finset V}
    (hval : ExploreValid (m + 1) N s) :
    (exploreMissed (m + 1) N s).card = (s.1ᶜ.card - (N 0).card) +
      (exploreMissed m (Fin.tail N) (exploreStep (N 0) s)).card := by
  obtain ⟨hne, hsub, hval'⟩ := hval
  simp only [exploreMissed, dite_eq_left hne]
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _
    (fun w w' h ↦ Sym2.congr_right.mp h), Finset.card_sdiff_of_subset hsub]
  rw [Finset.disjoint_left]
  rintro _ he h
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp he
  exact not_mem_later_of_valid (N := N) hne hval' w (Finset.mem_union_right _ h)

/-- The weight of a history, `x^{#found} y^{#missed}`, restricted to admissible histories. -/
def exploreWeight (x y : ℝ) (m : ℕ) (N : Fin m → Finset V) (s : Finset V × Finset V) : ℝ :=
  open scoped Classical in
  if ExploreValid m N s then x ^ (exploreFound m N s).card * y ^ (exploreMissed m N s).card
  else 0

/-- One-step decomposition of the weight of a history. -/
private theorem exploreWeight_cons (x y : ℝ) (m : ℕ) (a : Finset V) (N : Fin m → Finset V)
    (s : Finset V × Finset V) (hne : (s.1 \ s.2).Nonempty) :
    exploreWeight x y (m + 1) (Fin.cons a N) s =
      if a ⊆ s.1ᶜ then x ^ a.card * y ^ (s.1ᶜ.card - a.card) *
        exploreWeight x y m N (exploreStep a s) else 0 := by
  classical
  have hval : ExploreValid (m + 1) (Fin.cons a N) s ↔
      a ⊆ s.1ᶜ ∧ ExploreValid m N (exploreStep a s) := by
    simp only [ExploreValid, Fin.cons_zero, Fin.tail_cons]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hne, h⟩⟩
  unfold exploreWeight
  by_cases h : a ⊆ s.1ᶜ ∧ ExploreValid m N (exploreStep a s)
  · have hv := hval.mpr h
    rw [ite_eq_left hv, ite_eq_left h.1, ite_eq_left h.2, card_exploreFound_succ hv, card_exploreMissed_succ hv]
    simp only [Fin.cons_zero, Fin.tail_cons]
    ring
  · rw [ite_eq_right (fun hv ↦ h (hval.mp hv))]
    by_cases ha : a ⊆ s.1ᶜ
    · rw [ite_eq_left ha, ite_eq_right (fun hv ↦ h ⟨ha, hv⟩), mul_zero]
    · rw [ite_eq_right ha]

/-- The total weight of admissible histories of length `m` is at most `((x + y)^{|V|})^m` when
`x, y ≥ 0` and `x + y ≥ 1`. -/
theorem sum_exploreWeight_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 1 ≤ x + y) (m : ℕ) :
    ∀ s : Finset V × Finset V,
      ∑ N : Fin m → Finset V, exploreWeight x y m N s ≤ ((x + y) ^ Fintype.card V) ^ m := by
  classical
  have hw0 : ∀ m N s, 0 ≤ exploreWeight (V := V) x y m N s := by
    intro m N s
    unfold exploreWeight
    split_ifs <;> positivity
  have hR : 1 ≤ (x + y) ^ Fintype.card V := one_le_pow₀ hxy
  induction m with
  | zero =>
    intro s
    simp [exploreWeight, ExploreValid, exploreFound, exploreMissed]
  | succ m ih =>
    intro s
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) ↦ Finset V).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply]
    by_cases hne : (s.1 \ s.2).Nonempty
    · simp_rw [exploreWeight_cons x y m _ _ s hne]
      calc ∑ a : Finset V, ∑ N : Fin m → Finset V, (if a ⊆ s.1ᶜ then
            x ^ a.card * y ^ (s.1ᶜ.card - a.card) * exploreWeight x y m N (exploreStep a s)
            else 0)
          = ∑ a : Finset V, if a ⊆ s.1ᶜ then x ^ a.card * y ^ (s.1ᶜ.card - a.card) *
              ∑ N : Fin m → Finset V, exploreWeight x y m N (exploreStep a s) else 0 := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            split_ifs
            · rw [Finset.mul_sum]
            · simp
        _ ≤ ∑ a : Finset V, if a ⊆ s.1ᶜ then x ^ a.card * y ^ (s.1ᶜ.card - a.card) *
              ((x + y) ^ Fintype.card V) ^ m else 0 := by
            refine Finset.sum_le_sum fun a _ ↦ ?_
            split_ifs
            · exact mul_le_mul_of_nonneg_left (ih _) (by positivity)
            · exact le_rfl
        _ = ∑ a ∈ s.1ᶜ.powerset, x ^ a.card * y ^ (s.1ᶜ.card - a.card) *
              ((x + y) ^ Fintype.card V) ^ m := by
            rw [← Finset.sum_filter]
            congr 1
            ext a
            simp
        _ = (x + y) ^ s.1ᶜ.card * ((x + y) ^ Fintype.card V) ^ m := by
            rw [← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow]
        _ ≤ (x + y) ^ Fintype.card V * ((x + y) ^ Fintype.card V) ^ m := by
            gcongr
            exact Finset.card_le_univ _
        _ = ((x + y) ^ Fintype.card V) ^ (m + 1) := by ring
    · have hz : ∀ a (N : Fin m → Finset V), exploreWeight x y (m + 1) (Fin.cons a N) s = 0 := by
        intro a N
        unfold exploreWeight
        rw [ite_eq_right]
        exact fun h ↦ hne h.1
      simp_rw [hz]
      simp only [Finset.sum_const_zero]
      positivity

/-! ### Exploring the component of a vertex -/

/-- The event that a history is realized: its found pairs are edges and its missed pairs are
not. -/
def exploreEvent (m : ℕ) (N : Fin m → Finset V) (s : Finset V × Finset V) :
    Set (SimpleGraph V) :=
  {G | (∀ e ∈ exploreFound m N s, e ∈ G.edgeSet) ∧ ∀ e ∈ exploreMissed m N s, e ∉ G.edgeSet}

/-- An admissible history is realized with probability `p^{#found} (1-p)^{#missed}`. -/
theorem binomialRandom_real_exploreEvent (p : I) {m : ℕ} {N : Fin m → Finset V}
    {s : Finset V × Finset V} (hval : ExploreValid m N s) :
    (SimpleGraph.binomialRandom V p).real (exploreEvent m N s) =
      (p : ℝ) ^ (exploreFound m N s).card * (1 - p) ^ (exploreMissed m N s).card := by
  have hspec := exploreFound_union_exploreMissed_spec m N s hval
  refine binomialRandom_real_edges p _ _ (fun e he ↦ ?_) (fun e he ↦ ?_)
    (exploreFound_exploreMissed_props m N s hval)
  · obtain ⟨x, y, rfl, hxy, -⟩ := hspec e (Finset.mem_union_left _ he)
    exact Sym2.mk_isDiag_iff.not.mpr hxy
  · obtain ⟨x, y, rfl, hxy, -⟩ := hspec e (Finset.mem_union_right _ he)
    exact Sym2.mk_isDiag_iff.not.mpr hxy

open scoped Classical in
/-- The set discovered from the state `s` in a graph `G`: the undiscovered neighbours of the next
processed vertex. -/
def exploreNew (G : SimpleGraph V) (s : Finset V × Finset V) : Finset V :=
  if h : (s.1 \ s.2).Nonempty then
    Finset.univ.filter fun w ↦ w ∉ s.1 ∧ G.Adj ((s.1 \ s.2).min' h) w
  else ∅

/-- The history of the exploration of `G` from the state `s`. -/
def exploreHistory (G : SimpleGraph V) : (m : ℕ) → Finset V × Finset V → Fin m → Finset V
  | 0, _ => Fin.elim0
  | m + 1, s => Fin.cons (exploreNew G s) (exploreHistory G m (exploreStep (exploreNew G s) s))

open scoped Classical in
/-- The vertices reachable from `v`. -/
def reachableSet (G : SimpleGraph V) (v : V) : Finset V :=
  Finset.univ.filter (G.Reachable v)

omit [Fintype V] [LinearOrder V] in
/-- A vertex set closed under adjacency contains everything reachable from its elements. -/
private theorem mem_of_reachable_of_closed {G : SimpleGraph V} {S : Finset V}
    (hS : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) {a b : V} (ha : a ∈ S) (h : G.Reachable a b) :
    b ∈ S := by
  obtain ⟨q⟩ := h
  induction q with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hS _ ha _ hadj)

/-- The invariant of the exploration of the component of `v`. -/
def ExploreInv (G : SimpleGraph V) (v : V) (s : Finset V × Finset V) : Prop :=
  s.2 ⊆ s.1 ∧ v ∈ s.1 ∧ (∀ w ∈ s.1, G.Reachable v w) ∧ ∀ u ∈ s.2, ∀ w, G.Adj u w → w ∈ s.1

/-- While fewer vertices are processed than the component has, some discovered vertex is
unprocessed. -/
private theorem exploreInv_nonempty {G : SimpleGraph V} {v : V} {s : Finset V × Finset V}
    (hI : ExploreInv G v s) (hcard : s.2.card + 1 ≤ (reachableSet G v).card) :
    (s.1 \ s.2).Nonempty := by
  classical
  obtain ⟨h21, hv, -, hcl⟩ := hI
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
  have heq : s.1 = s.2 := Finset.Subset.antisymm hne h21
  have hsub : reachableSet G v ⊆ s.1 := by
    intro w hw
    simp only [reachableSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine mem_of_reachable_of_closed (fun a ha b hab ↦ hcl a (heq ▸ ha) b hab) hv hw
  have := Finset.card_le_card hsub
  rw [heq] at this
  omega

/-- The exploration of `G` from a state satisfying the invariant is an admissible realized
history, and it discovers enough vertices as long as the component is large. -/
theorem exploreHistory_spec (G : SimpleGraph V) (v : V) (m : ℕ) :
    ∀ s : Finset V × Finset V, ExploreInv G v s →
      s.2.card + m + 1 ≤ (reachableSet G v).card →
      ExploreValid m (exploreHistory G m s) s ∧ G ∈ exploreEvent m (exploreHistory G m s) s ∧
        s.2.card + m + 1 ≤ (exploreFound m (exploreHistory G m s) s).card + s.1.card := by
  classical
  induction m with
  | zero =>
    intro s hI hcard
    refine ⟨trivial, ⟨by simp [exploreFound], by simp [exploreMissed]⟩, ?_⟩
    have hne := exploreInv_nonempty hI (by omega)
    have hlt : s.2 ⊂ s.1 := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hI.1, fun h ↦ ?_⟩
      obtain ⟨w, hw⟩ := hne
      rw [Finset.mem_sdiff, h] at hw
      exact hw.2 hw.1
    have := Finset.card_lt_card hlt
    simp only [exploreFound, Finset.card_empty]
    omega
  | succ m ih =>
    intro s hI hcard
    have hne := exploreInv_nonempty hI (by omega)
    set u := (s.1 \ s.2).min' hne with hu_def
    have hu : u ∈ s.1 \ s.2 := Finset.min'_mem _ hne
    set a := exploreNew G s with ha_def
    have ha : a = Finset.univ.filter fun w ↦ w ∉ s.1 ∧ G.Adj u w := by
      rw [ha_def, exploreNew, dite_eq_left hne]
    have hstep : exploreStep a s = (s.1 ∪ a, insert u s.2) := by
      rw [exploreStep, dite_eq_left hne]
    have haC : a ⊆ s.1ᶜ := by
      intro w hw
      rw [ha] at hw
      exact Finset.mem_compl.mpr (Finset.mem_filter.mp hw).2.1
    obtain ⟨h21, hv, hreach, hcl⟩ := hI
    have hI' : ExploreInv G v (exploreStep a s) := by
      rw [hstep]
      refine ⟨Finset.insert_subset (Finset.mem_union_left _ (Finset.mem_sdiff.mp hu).1)
        (h21.trans Finset.subset_union_left), Finset.mem_union_left _ hv, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hreach w hw
        · rw [ha] at hw
          exact (hreach u (Finset.mem_sdiff.mp hu).1).trans
            (Finset.mem_filter.mp hw).2.2.reachable
      · intro x hx w hxw
        rcases Finset.mem_insert.mp hx with rfl | hx
        · by_cases hw : w ∈ s.1
          · exact Finset.mem_union_left _ hw
          · refine Finset.mem_union_right _ ?_
            rw [ha]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hxw⟩
        · exact Finset.mem_union_left _ (hcl x hx w hxw)
    have hcard2 : (exploreStep a s).2.card = s.2.card + 1 := by
      rw [hstep]
      exact Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hu).2
    have hcard1 : (exploreStep a s).1.card = s.1.card + a.card := by
      rw [hstep]
      exact Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun w hw hwa ↦
        Finset.mem_compl.mp (haC hwa) hw)
    obtain ⟨hval, hev, hc⟩ := ih (exploreStep a s) hI' (by omega)
    have hhist : exploreHistory G (m + 1) s = Fin.cons a (exploreHistory G m (exploreStep a s)) :=
      rfl
    have hval' : ExploreValid (m + 1) (exploreHistory G (m + 1) s) s := by
      rw [hhist]
      simp only [ExploreValid, Fin.cons_zero, Fin.tail_cons]
      exact ⟨hne, haC, hval⟩
    refine ⟨hval', ⟨?_, ?_⟩, ?_⟩
    · rw [hhist]
      simp only [exploreFound, dite_eq_left hne, Fin.cons_zero, Fin.tail_cons]
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
        rw [ha] at hw
        exact (Finset.mem_filter.mp hw).2.2
      · exact hev.1 e he
    · rw [hhist]
      simp only [exploreMissed, dite_eq_left hne, Fin.cons_zero, Fin.tail_cons]
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
        rw [Finset.mem_sdiff, Finset.mem_compl] at hw
        intro hadj
        refine hw.2 ?_
        rw [ha]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1, hadj⟩
      · exact hev.2 e he
    · rw [card_exploreFound_succ hval', hhist]
      simp only [Fin.cons_zero, Fin.tail_cons]
      omega

/-- The component of `v` has more than `m` vertices with probability at most
`λ^{-m} (1 - p + pλ)^{m|V|}` for every `λ ≥ 1` (exploration and the exponential moment bound). -/
theorem binomialRandom_real_reachableSet_card_le (p : I) (v : V) (m : ℕ) {lam : ℝ}
    (hlam : 1 ≤ lam) :
    (SimpleGraph.binomialRandom V p).real {G | m + 1 ≤ (reachableSet G v).card} ≤
      (lam ^ m)⁻¹ * ((1 - p + p * lam) ^ Fintype.card V) ^ m := by
  classical
  set s₀ : Finset V × Finset V := ({v}, ∅)
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith [p.2.2]
  have hlam0 : 0 < lam := by linarith
  set H := Finset.univ.filter fun N : Fin m → Finset V ↦
    ExploreValid m N s₀ ∧ m ≤ (exploreFound m N s₀).card
  have hsub : {G : SimpleGraph V | m + 1 ≤ (reachableSet G v).card} ⊆
      ⋃ N ∈ H, exploreEvent m N s₀ := by
    intro G hG
    have hI : ExploreInv G v s₀ := ⟨by simp [s₀], by simp [s₀], by simp [s₀], by simp [s₀]⟩
    obtain ⟨hval, hev, hc⟩ := exploreHistory_spec G v m s₀ hI (by simpa [s₀] using hG)
    simp only [Set.mem_iUnion]
    refine ⟨exploreHistory G m s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval, ?_⟩, hev⟩
    have h1 : s₀.1.card = 1 := Finset.card_singleton v
    have h2 : s₀.2.card = 0 := Finset.card_empty
    omega
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ N ∈ H, (SimpleGraph.binomialRandom V p).real (exploreEvent m N s₀) ≤
      (lam ^ m)⁻¹ * exploreWeight ((p : ℝ) * lam) (1 - p) m N s₀ := by
    intro N hN
    obtain ⟨hval, hcard⟩ := (Finset.mem_filter.mp hN).2
    rw [binomialRandom_real_exploreEvent p hval, exploreWeight, ite_eq_left hval, mul_pow]
    have hl : lam ^ m ≤ lam ^ (exploreFound m N s₀).card := pow_le_pow_right₀ hlam hcard
    rw [← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq0 _)
    rw [mul_comm ((lam ^ m)⁻¹), mul_assoc]
    refine le_mul_of_one_le_right (pow_nonneg hp0 _) ?_
    rw [inv_mul_eq_div, one_le_div (pow_pos hlam0 m)]
    exact hl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hw0 : ∀ N, 0 ≤ exploreWeight ((p : ℝ) * lam) (1 - p) m N s₀ := by
    intro N
    unfold exploreWeight
    split_ifs <;> positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
    fun N _ _ ↦ hw0 N).trans ?_
  have := sum_exploreWeight_le (V := V) (mul_nonneg hp0 hlam0.le) hq0
    (by nlinarith) m s₀
  convert this using 3
  ring

omit [LinearOrder V] in
/-- The connected component of `v` has as many vertices as are reachable from `v`. -/
theorem ncard_supp_connectedComponentMk (G : SimpleGraph V) (v : V) :
    (G.connectedComponentMk v).supp.ncard = (reachableSet G v).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    reachableSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact SimpleGraph.reachable_comm

/-- Union bound over the vertices: some component has more than `m` vertices with probability
at most `|V| λ^{-m} (1 - p + pλ)^{m|V|}`. -/
theorem binomialRandom_real_exists_large_component_le (p : I) (m : ℕ) {lam : ℝ}
    (hlam : 1 ≤ lam) :
    (SimpleGraph.binomialRandom V p).real {G | ∃ v, m + 1 ≤ (reachableSet G v).card} ≤
      Fintype.card V * ((lam ^ m)⁻¹ * ((1 - p + p * lam) ^ Fintype.card V) ^ m) := by
  have hsub : {G : SimpleGraph V | ∃ v, m + 1 ≤ (reachableSet G v).card} =
      ⋃ v ∈ (Finset.univ : Finset V), {G | m + 1 ≤ (reachableSet G v).card} := by
    ext G
    simp
  rw [hsub]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun v _ ↦
    binomialRandom_real_reachableSet_card_le p v m hlam).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- GAPS 107.47, subcritical phase: for `p = c/n` with `0 ≤ c < 1`, all components of
`G(n, p)` have at most `C log n` vertices with probability tending to one. -/
theorem exists_tendsto_binomialRandom_components_le_log' (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) :
    ∃ C > (0 : ℝ), Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
      (Set.projIcc (0 : ℝ) 1 zero_le_one (c / n))).real
        {G | ∀ v, ((G.connectedComponentMk v).supp.ncard : ℝ) ≤ C * Real.log n})
      atTop (𝓝 1) := by
  set c' := max c (1 / 2) with hc'
  have hc'0 : 0 < c' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc'1 : c' < 1 := max_lt hc (by norm_num)
  set lam := c'⁻¹ with hlam_def
  have hlam : 1 ≤ lam := by rw [hlam_def, le_inv_comm₀ one_pos hc'0, inv_one]; exact hc'1.le
  set ρ := c' * Real.exp (1 - c') with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by
    have h := Real.log_lt_sub_one_of_pos hc'0 hc'1.ne
    have : Real.log ρ < 0 := by
      rw [hρ, Real.log_mul hc'0.ne' (Real.exp_pos _).ne', Real.log_exp]
      linarith
    exact (Real.log_neg_iff hρ0).mp this
  set L := -Real.log ρ with hL
  have hL0 : 0 < L := by rw [hL]; linarith [Real.log_neg hρ0 hρ1]
  refine ⟨2 / L, by positivity, ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ 1 - Real.exp L * (1 / n)) atTop (𝓝 1) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat.const_mul (Real.exp L)).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
    (Eventually.of_forall fun n ↦ measureReal_le_one)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set pn : I := Set.projIcc (0 : ℝ) 1 zero_le_one (c / n) with hpn
  have hpn_eq : (pn : ℝ) = c / n := by
    rw [hpn, Set.coe_projIcc, min_eq_right, max_eq_right (div_nonneg hc0 hn0.le)]
    rw [div_le_one hn0]
    linarith [(show (1 : ℝ) ≤ n by exact_mod_cast hn)]
  set m := ⌊2 / L * Real.log n⌋₊ with hm
  -- the bad event has small probability
  have hbad := binomialRandom_real_exists_large_component_le (V := Fin n) pn m hlam
  rw [Fintype.card_fin] at hbad
  have hR : (lam ^ m)⁻¹ * ((1 - pn + pn * lam) ^ n) ^ m ≤ ρ ^ m := by
    have h2' : 0 ≤ 1 - (pn : ℝ) + pn * lam := by
      have := pn.2.1
      nlinarith
    have hbase : (1 - (pn : ℝ) + pn * lam) ^ n ≤ Real.exp (1 - c') := by
      have h1 : 1 - (pn : ℝ) + pn * lam ≤ Real.exp (pn * (lam - 1)) := by
        have := Real.add_one_le_exp (pn * (lam - 1))
        linarith
      have h2 : 0 ≤ 1 - (pn : ℝ) + pn * lam := by
        have := pn.2.1
        nlinarith
      calc (1 - (pn : ℝ) + pn * lam) ^ n ≤ Real.exp (pn * (lam - 1)) ^ n :=
            pow_le_pow_left₀ h2 h1 n
        _ = Real.exp (c * (lam - 1)) := by
            rw [← Real.exp_nat_mul, hpn_eq]; congr 1; field_simp
        _ ≤ Real.exp (c' * (lam - 1)) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ = Real.exp (1 - c') := by
            congr 1; rw [hlam_def, mul_sub, mul_inv_cancel₀ hc'0.ne', mul_one]
    rw [← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (by linarith)) (pow_nonneg h2' n)) ?_ m
    calc lam⁻¹ * (1 - (pn : ℝ) + pn * lam) ^ n ≤ lam⁻¹ * Real.exp (1 - c') :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = ρ := by rw [hlam_def, inv_inv]
  have hρm : (n : ℝ) * ρ ^ m ≤ Real.exp L * (1 / n) := by
    have hfl : 2 / L * Real.log n - 1 < m := by
      have := Nat.lt_floor_add_one (2 / L * Real.log n)
      rw [← hm] at this
      linarith
    have hρexp : ρ ^ m = Real.exp (-(L * m)) := by
      rw [hL, ← Real.exp_log hρ0, ← Real.exp_nat_mul, Real.exp_log hρ0]
      congr 1; ring
    rw [hρexp]
    have : Real.exp (-(L * m)) ≤ Real.exp (L - 2 * Real.log n) := by
      apply Real.exp_le_exp.mpr
      have : L * (2 / L * Real.log n - 1) = 2 * Real.log n - L := by field_simp
      nlinarith
    calc (n : ℝ) * Real.exp (-(L * m)) ≤ n * Real.exp (L - 2 * Real.log n) :=
          mul_le_mul_of_nonneg_left this hn0.le
      _ = Real.exp L * (1 / n) := by
          rw [Real.exp_sub, show 2 * Real.log n = Real.log n + Real.log n by ring,
            Real.exp_add, Real.exp_log hn0]
          field_simp
  -- the good event contains the complement of the bad event
  have hgood : {G : SimpleGraph (Fin n) | ∃ v, m + 1 ≤ (reachableSet G v).card}ᶜ ⊆
      {G | ∀ v, ((G.connectedComponentMk v).supp.ncard : ℝ) ≤ 2 / L * Real.log n} := by
    intro G hG v
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le] at hG
    rw [ncard_supp_connectedComponentMk]
    have h1 : (reachableSet G v).card ≤ m := Nat.lt_succ_iff.mp (hG v)
    calc ((reachableSet G v).card : ℝ) ≤ m := by exact_mod_cast h1
      _ ≤ 2 / L * Real.log n := Nat.floor_le (by positivity)
  have hmono := measureReal_mono (μ := SimpleGraph.binomialRandom (Fin n) pn) hgood
    (measure_ne_top _ _)
  rw [probReal_compl_eq_one_sub (DiscreteMeasurableSpace.forall_measurableSet _)] at hmono
  have := hbad.trans (mul_le_mul_of_nonneg_left hR hn0.le)
  linarith

end CKSD
