module

public import CKSD.Geometry.Persistence
public import CKSD.Geometry.FiniteCombinatorics

/-!
# Distances between full persistence diagrams

Finite bars are partially matched, with unmatched bars sent to the diagonal. Essential bars
are matched bijectively. Bottleneck and real-power Wasserstein distances satisfy triangle
inequalities; Wasserstein composition uses Mathlib `ENNReal.Lp_add_le`.

## Main definitions

* `CKSD.essentialBottleneckEDist`, `CKSD.fullBottleneckEDist`: bottleneck distances.
* `CKSD.diagramWassersteinCost`, `CKSD.diagramWassersteinEDist`: Wasserstein distances.
* `CKSD.DiagramMatching.trans`: composition of partial matchings.

## Main results

* `CKSD.fullBottleneckEDist_triangle`, `CKSD.diagramWassersteinEDist_triangle`: triangle
  inequalities.
* `CKSD.exists_equiv_of_card_eq`: rank counts determine a full diagram up to reindexing.
-/

@[expose] public section

noncomputable section

open Module Set
open scoped ENNReal NNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

section Distances

/-- Bottleneck distance between essential parts: the best bijection of essential births, and
`∞` when the numbers of essential bars differ. -/
def essentialBottleneckEDist {κ κ' : Type*} (e : κ → ℝ) (e' : κ' → ℝ) : ℝ≥0∞ :=
  ⨅ σ : κ ≃ κ', ⨆ k, ENNReal.ofReal |e k - e' (σ k)|

/-- Bottleneck distance between full diagrams with finite parts `D, E` and essential parts
`e, e'`. Finite and essential points are at infinite distance, so the two parts are matched
separately. -/
def fullBottleneckEDist {α β κ κ' : Type*} (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  max (bottleneckEDist D E) (essentialBottleneckEDist e e')

/-- `q`-th power cost of a partial matching of finite parts together with a bijection of essential
parts, with `ℓ^∞` distances between matched points and distance `(d - b)/2` of an unmatched point
to the diagonal. The intended range is `1 ≤ q`, where the induced distance is a metric. -/
def diagramWassersteinCost {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (M : DiagramMatching α β) (σ : κ ≃ κ') (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  (∑ i, (if h : ∃ j, M.relates i j then
      ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
    else ENNReal.ofReal ((D.death i - D.birth i) / 2)) ^ q) +
  (∑ j, (if ∃ i, M.relates i j then 0 else ENNReal.ofReal ((E.death j - E.birth j) / 2)) ^ q) +
  ∑ k, ENNReal.ofReal |e k - e' (σ k)| ^ q

/-- The `q`-Wasserstein distance between full persistence diagrams, `∞` when the numbers of
essential bars differ. The definition is made for every real `q`; it satisfies the triangle
inequality, and so is an extended pseudometric on diagrams, for `1 ≤ q`
(`CKSD.diagramWassersteinEDist_triangle`). -/
def diagramWassersteinEDist {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  ⨅ M : DiagramMatching α β, ⨅ σ : κ ≃ κ', diagramWassersteinCost q M σ D e E e' ^ (1 / q)

namespace DiagramMatching

variable {α β γ : Type*} (M : DiagramMatching α β) (D : FiniteDeathDiagram α)
  (E : FiniteDeathDiagram β)

/-- The cost of a matching bounds the distance of each matched pair. -/
theorem ofReal_le_cost_of_relates {i : α} {j : β} (h : M.relates i j) :
    ENNReal.ofReal (max |D.birth i - E.birth j| |D.death i - E.death j|) ≤ M.cost D E := by
  have hex : ∃ j, M.relates i j := ⟨j, h⟩
  have hc : hex.choose = j := M.left_unique _ _ _ hex.choose_spec h
  refine le_trans ?_ (le_max_left _ _)
  refine le_iSup_of_le i ?_
  rw [dite_eq_left hex, hc]

/-- The cost of a matching bounds the diagonal distance of each unmatched left point. -/
theorem ofReal_le_cost_of_not_left {i : α} (h : ¬ ∃ j, M.relates i j) :
    ENNReal.ofReal ((D.death i - D.birth i) / 2) ≤ M.cost D E := by
  refine le_trans ?_ (le_max_left _ _)
  refine le_iSup_of_le i ?_
  rw [dite_eq_right h]

/-- The cost of a matching bounds the diagonal distance of each unmatched right point. -/
theorem ofReal_le_cost_of_not_right {j : β} (h : ¬ ∃ i, M.relates i j) :
    ENNReal.ofReal ((E.death j - E.birth j) / 2) ≤ M.cost D E := by
  refine le_trans ?_ (le_max_right _ _)
  refine le_iSup_of_le j ?_
  rw [dite_eq_right h]

/-- A bound on all matched pairs and on all unmatched points bounds the cost. -/
theorem cost_le {c : ℝ≥0∞}
    (h1 : ∀ i j, M.relates i j →
      ENNReal.ofReal (max |D.birth i - E.birth j| |D.death i - E.death j|) ≤ c)
    (h2 : ∀ i, (¬ ∃ j, M.relates i j) → ENNReal.ofReal ((D.death i - D.birth i) / 2) ≤ c)
    (h3 : ∀ j, (¬ ∃ i, M.relates i j) → ENNReal.ofReal ((E.death j - E.birth j) / 2) ≤ c) :
    M.cost D E ≤ c := by
  unfold cost
  refine max_le (iSup_le fun i ↦ ?_) (iSup_le fun j ↦ ?_)
  · split_ifs with h
    · exact h1 i _ h.choose_spec
    · exact h2 i h
  · split_ifs with h
    · exact h1 _ j h.choose_spec
    · exact h3 j h

/-- A partial matching is a bi-unique relation in the sense of Mathlib's `Relator`. -/
theorem biUnique : Relator.BiUnique M.relates :=
  ⟨fun _ _ _ h h' ↦ M.right_unique _ _ _ h h', fun _ _ _ h h' ↦ M.left_unique _ _ _ h h'⟩

/-- The composite of two partial matchings. -/
def trans (M : DiagramMatching α β) (N : DiagramMatching β γ) : DiagramMatching α γ where
  relates i k := ∃ j, M.relates i j ∧ N.relates j k
  left_unique := by
    rintro i k k' ⟨j, h1, h2⟩ ⟨j', h1', h2'⟩
    obtain rfl := M.left_unique _ _ _ h1 h1'
    exact N.left_unique _ _ _ h2 h2'
  right_unique := by
    rintro i i' k ⟨j, h1, h2⟩ ⟨j', h1', h2'⟩
    obtain rfl := N.right_unique _ _ _ h2 h2'
    exact M.right_unique _ _ _ h1 h1'

/-- The cost of a composite matching is at most the sum of the costs. -/
theorem cost_trans_le (N : DiagramMatching β γ) (F : FiniteDeathDiagram γ) :
    (M.trans N).cost D F ≤ M.cost D E + N.cost E F := by
  refine cost_le _ _ _ ?_ ?_ ?_
  · rintro i k ⟨j, h1, h2⟩
    have hM := M.ofReal_le_cost_of_relates D E h1
    have hN := N.ofReal_le_cost_of_relates E F h2
    refine le_trans ?_ (add_le_add hM hN)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_)
    · exact (abs_sub_le _ (E.birth j) _).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact (abs_sub_le _ (E.death j) _).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _))
  · intro i hi
    by_cases hj : ∃ j, M.relates i j
    · obtain ⟨j, hij⟩ := hj
      have hjN : ¬ ∃ k, N.relates j k := fun ⟨k, hk⟩ ↦ hi ⟨k, j, hij, hk⟩
      have hM := M.ofReal_le_cost_of_relates D E hij
      have hN := N.ofReal_le_cost_of_not_left E F hjN
      refine le_trans ?_ (add_le_add hM hN)
      rw [← ENNReal.ofReal_add (by positivity) (le_of_lt (by linarith [E.birth_lt_death j]))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := le_abs_self (D.death i - E.death j)
      have h2 := neg_abs_le (D.birth i - E.birth j)
      have h3 := le_max_left |D.birth i - E.birth j| |D.death i - E.death j|
      have h4 := le_max_right |D.birth i - E.birth j| |D.death i - E.death j|
      linarith
    · exact (M.ofReal_le_cost_of_not_left D E hj).trans le_self_add
  · intro k hk
    by_cases hj : ∃ j, N.relates j k
    · obtain ⟨j, hjk⟩ := hj
      have hjM : ¬ ∃ i, M.relates i j := fun ⟨i, hi⟩ ↦ hk ⟨i, j, hi, hjk⟩
      have hM := M.ofReal_le_cost_of_not_right D E hjM
      have hN := N.ofReal_le_cost_of_relates E F hjk
      refine le_trans ?_ (add_le_add hM hN)
      rw [← ENNReal.ofReal_add (le_of_lt (by linarith [E.birth_lt_death j])) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := neg_abs_le (E.death j - F.death k)
      have h2 := le_abs_self (E.birth j - F.birth k)
      have h3 := le_max_left |E.birth j - F.birth k| |E.death j - F.death k|
      have h4 := le_max_right |E.birth j - F.birth k| |E.death j - F.death k|
      linarith
    · exact (N.ofReal_le_cost_of_not_right E F hj).trans le_add_self

end DiagramMatching

/-- The triangle inequality for the bottleneck distance of finite-death diagrams. -/
theorem bottleneckEDist_triangle {α β γ : Type*} (D : FiniteDeathDiagram α)
    (E : FiniteDeathDiagram β) (F : FiniteDeathDiagram γ) :
    bottleneckEDist D F ≤ bottleneckEDist D E + bottleneckEDist E F := by
  unfold bottleneckEDist
  exact ENNReal.le_iInf_add_iInf fun M N ↦ (iInf_le _ (M.trans N)).trans (M.cost_trans_le D E N F)

/-- The triangle inequality for the bottleneck distance of essential parts. -/
theorem essentialBottleneckEDist_triangle {κ κ' κ'' : Type*} (e : κ → ℝ) (e' : κ' → ℝ)
    (e'' : κ'' → ℝ) :
    essentialBottleneckEDist e e'' ≤ essentialBottleneckEDist e e' +
      essentialBottleneckEDist e' e'' := by
  unfold essentialBottleneckEDist
  refine ENNReal.le_iInf_add_iInf fun σ τ ↦ (iInf_le _ (σ.trans τ)).trans (iSup_le fun k ↦ ?_)
  refine le_trans ?_ (add_le_add (le_iSup _ k) (le_iSup _ (σ k)))
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

/-- The triangle inequality for the bottleneck distance of full diagrams. -/
theorem fullBottleneckEDist_triangle {α β γ κ κ' κ'' : Type*} (D : FiniteDeathDiagram α)
    (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) (F : FiniteDeathDiagram γ)
    (e'' : κ'' → ℝ) :
    fullBottleneckEDist D e F e'' ≤ fullBottleneckEDist D e E e' + fullBottleneckEDist E e' F e'' := by
  unfold fullBottleneckEDist
  refine max_le ((bottleneckEDist_triangle D E F).trans
    (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
  exact (essentialBottleneckEDist_triangle e e' e'').trans
    (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- Below a level `x` and above `z < x`, there is a level `y` such that the values of a finite
family below `x` are exactly those at most `y`. -/
theorem exists_le_lt_forall_lt_iff_le {γ L : Type*} [Fintype γ] [LinearOrder L] (w : γ → L)
    {x z : L} (hzx : z < x) : ∃ y, z ≤ y ∧ y < x ∧ ∀ c, w c < x ↔ w c ≤ y := by
  set S := Finset.univ.filter fun c ↦ w c < x
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨z, le_rfl, hzx, fun c ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩⟩
    · have : c ∈ S := by simp [S, hc]
      simp [hS] at this
    · have : c ∈ S := by simp [S, lt_of_le_of_lt hc hzx]
      simp [hS] at this
  · obtain ⟨c0, hc0, hmax⟩ := S.exists_max_image w hS
    have hc0' : w c0 < x := by simpa [S] using hc0
    refine ⟨max z (w c0), le_max_left _ _, max_lt hzx hc0', fun c ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩⟩
    · exact (hmax c (by simp [S, hc])).trans (le_max_right _ _)
    · rcases le_max_iff.mp hc with h | h
      · exact lt_of_le_of_lt h hzx
      · exact lt_of_le_of_lt h hc0'

/-- Two finite families with equal fibre cardinalities are related by a bijection. -/
theorem exists_equiv_comp_eq_of_card_filter_eq {α β γ : Type*} [Fintype α] [Fintype β]
    (u : α → γ) (v : β → γ)
    (h : ∀ c, (Finset.univ.filter fun a ↦ u a = c).card =
      (Finset.univ.filter fun b ↦ v b = c).card) :
    ∃ σ : α ≃ β, ∀ a, v (σ a) = u a := by
  refine ⟨Equiv.ofFiberEquiv fun c ↦ Fintype.equivOfCardEq ?_, Equiv.ofFiberEquiv_map _⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact h c

/-- Real families with the same distribution function have the same fibre cardinalities. -/
theorem card_filter_eq_of_card_filter_le_eq {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (u : κ → ℝ) (v : κ' → ℝ)
    (h : ∀ a, (Finset.univ.filter fun k ↦ u k ≤ a).card =
      (Finset.univ.filter fun k ↦ v k ≤ a).card) (x : ℝ) :
    (Finset.univ.filter fun k ↦ u k = x).card = (Finset.univ.filter fun k ↦ v k = x).card := by
  obtain ⟨y, -, -, hy⟩ := exists_le_lt_forall_lt_iff_le (Sum.elim u v) (sub_one_lt x)
  have hu := card_filter_eq_add_of_iff (P := fun k ↦ u k ≤ x) (Q := fun k ↦ u k = x)
    (S := fun k ↦ u k ≤ y) (fun k ↦ by
      have := hy (.inl k); simp only [Sum.elim_inl] at this; rw [← this, le_iff_eq_or_lt])
    (fun k hk h' ↦ by have := (hy (.inl k)).mpr (by simpa using h'); simp at this; linarith)
  have hv := card_filter_eq_add_of_iff (P := fun k ↦ v k ≤ x) (Q := fun k ↦ v k = x)
    (S := fun k ↦ v k ≤ y) (fun k ↦ by
      have := hy (.inr k); simp only [Sum.elim_inr] at this; rw [← this, le_iff_eq_or_lt])
    (fun k hk h' ↦ by have := (hy (.inr k)).mpr (by simpa using h'); simp at this; linarith)
  have h1 := h x
  have h2 := h y
  omega

/-- Inclusion–exclusion for the multiplicity of a point `(x, y)` of a finite-death diagram, in
terms of the counts of bars containing `[a, b]`. -/
theorem card_filter_birth_death_eq_add {α : Type*} [Fintype α] (D : FiniteDeathDiagram α)
    {x x' y y'' : ℝ} (hx : ∀ i, D.birth i < x ↔ D.birth i ≤ x')
    (hy : ∀ i, D.death i < y ↔ D.death i ≤ y'') :
    (Finset.univ.filter fun i ↦ D.birth i = x ∧ D.death i = y).card +
        (Finset.univ.filter fun i ↦ D.birth i ≤ x ∧ y < D.death i).card +
        (Finset.univ.filter fun i ↦ D.birth i ≤ x' ∧ y'' < D.death i).card =
      (Finset.univ.filter fun i ↦ D.birth i ≤ x ∧ y'' < D.death i).card +
        (Finset.univ.filter fun i ↦ D.birth i ≤ x' ∧ y < D.death i).card := by
  have hA := card_filter_eq_add_of_iff (P := fun i ↦ D.birth i ≤ x ∧ y'' < D.death i)
    (Q := fun i ↦ D.birth i ≤ x' ∧ y'' < D.death i) (S := fun i ↦ D.birth i = x ∧ y ≤ D.death i)
    (fun i ↦ by
      have h1 := hx i
      have h2 := hy i
      constructor
      · rintro ⟨hb, hd⟩
        rcases hb.lt_or_eq with hb | hb
        · exact Or.inl ⟨h1.mp hb, hd⟩
        · refine Or.inr ⟨hb, ?_⟩
          by_contra hc
          exact absurd (h2.mp (not_le.mp hc)) (not_le.mpr hd)
      · rintro (⟨hb, hd⟩ | ⟨hb, hd⟩)
        · exact ⟨(h1.mpr hb).le, hd⟩
        · refine ⟨hb.le, ?_⟩
          by_contra hc
          exact absurd (h2.mpr (not_lt.mp hc)) (not_lt.mpr hd))
    (fun i hQ hS ↦ by
      have := (hx i).mpr hQ.1
      rw [hS.1] at this
      exact lt_irrefl _ this)
  have hB := card_filter_eq_add_of_iff (P := fun i ↦ D.birth i = x ∧ y ≤ D.death i)
    (Q := fun i ↦ D.birth i = x ∧ D.death i = y) (S := fun i ↦ D.birth i = x ∧ y < D.death i)
    (fun i ↦ by
      constructor
      · rintro ⟨hb, hd⟩
        rcases hd.lt_or_eq with hd | hd
        · exact Or.inr ⟨hb, hd⟩
        · exact Or.inl ⟨hb, hd.symm⟩
      · rintro (⟨hb, hd⟩ | ⟨hb, hd⟩)
        · exact ⟨hb, hd.ge⟩
        · exact ⟨hb, hd.le⟩)
    (fun i hQ hS ↦ by rw [hQ.2] at hS; exact lt_irrefl _ hS.2)
  have hC := card_filter_eq_add_of_iff (P := fun i ↦ D.birth i ≤ x ∧ y < D.death i)
    (Q := fun i ↦ D.birth i ≤ x' ∧ y < D.death i) (S := fun i ↦ D.birth i = x ∧ y < D.death i)
    (fun i ↦ by
      have h1 := hx i
      constructor
      · rintro ⟨hb, hd⟩
        rcases hb.lt_or_eq with hb | hb
        · exact Or.inl ⟨h1.mp hb, hd⟩
        · exact Or.inr ⟨hb, hd⟩
      · rintro (⟨hb, hd⟩ | ⟨hb, hd⟩)
        · exact ⟨(h1.mpr hb).le, hd⟩
        · exact ⟨hb.le, hd⟩)
    (fun i hQ hS ↦ by
      have := (hx i).mpr hQ.1
      rw [hS.1] at this
      exact lt_irrefl _ this)
  omega

/-- Full diagrams with the same counts of bars containing each interval `[a, b]` agree up to
reindexing: the counts determine the finite and the essential parts. -/
theorem exists_equiv_of_card_eq {α β κ κ' : Type*} [Fintype α] [Fintype β]
    [Fintype κ] [Fintype κ'] (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β)
    (e' : κ' → ℝ)
    (h : ∀ a b, a ≤ b →
      (Finset.univ.filter fun i ↦ D.birth i ≤ a ∧ b < D.death i).card +
          (Finset.univ.filter fun k ↦ e k ≤ a).card =
        (Finset.univ.filter fun i ↦ E.birth i ≤ a ∧ b < E.death i).card +
          (Finset.univ.filter fun k ↦ e' k ≤ a).card) :
    ∃ σ : α ≃ β, (∀ i, E.birth (σ i) = D.birth i ∧ E.death (σ i) = D.death i) ∧
      ∃ τ : κ ≃ κ', ∀ k, e' (τ k) = e k := by
  -- essential parts
  have hM : ∀ a, (Finset.univ.filter fun k ↦ e k ≤ a).card =
      (Finset.univ.filter fun k ↦ e' k ≤ a).card := by
    intro a
    obtain ⟨MD, hMD⟩ := Finite.exists_le D.death
    obtain ⟨ME, hME⟩ := Finite.exists_le E.death
    set b := max a (max MD ME)
    have hDb : ∀ i, D.death i ≤ b := fun i ↦ (hMD i).trans (le_max_left _ _ |>.trans
      (le_max_right _ _))
    have hEb : ∀ i, E.death i ≤ b := fun i ↦ (hME i).trans (le_max_right _ _ |>.trans
      (le_max_right _ _))
    have hab : a ≤ b := le_max_left _ _
    have := h a b hab
    rw [Finset.filter_false_of_mem (fun i _ ↦ fun hi ↦ absurd hi.2 (not_lt.mpr (hDb i))),
      Finset.filter_false_of_mem (fun i _ ↦ fun hi ↦ absurd hi.2 (not_lt.mpr (hEb i)))] at this
    simpa using this
  have hN : ∀ a b, a ≤ b → (Finset.univ.filter fun i ↦ D.birth i ≤ a ∧ b < D.death i).card =
      (Finset.univ.filter fun i ↦ E.birth i ≤ a ∧ b < E.death i).card := by
    intro a b hab
    have := h a b hab
    have := hM a
    omega
  -- finite parts
  have hfib : ∀ c : ℝ × ℝ,
      (Finset.univ.filter fun i ↦ (D.birth i, D.death i) = c).card =
        (Finset.univ.filter fun i ↦ (E.birth i, E.death i) = c).card := by
    rintro ⟨x, y⟩
    simp only [Prod.mk.injEq]
    by_cases hxy : x < y
    · obtain ⟨x', -, hx'x, hx'⟩ := exists_le_lt_forall_lt_iff_le (Sum.elim D.birth E.birth)
        (sub_one_lt x)
      obtain ⟨y'', hxy'', -, hy''⟩ := exists_le_lt_forall_lt_iff_le
        (Sum.elim D.death E.death) hxy
      have hD := card_filter_birth_death_eq_add D (x' := x') (y'' := y'')
        (fun i ↦ by simpa using hx' (.inl i)) (fun i ↦ by simpa using hy'' (.inl i))
      have hE := card_filter_birth_death_eq_add E (x' := x') (y'' := y'')
        (fun i ↦ by simpa using hx' (.inr i)) (fun i ↦ by simpa using hy'' (.inr i))
      have h1 := hN x y hxy.le
      have h2 := hN x' y'' (by linarith)
      have h3 := hN x y'' hxy''
      have h4 := hN x' y (by linarith)
      omega
    · have hD : ∀ i, ¬ (D.birth i = x ∧ D.death i = y) := fun i hi ↦ by
        have := D.birth_lt_death i
        rw [hi.1, hi.2] at this
        exact hxy this
      have hE : ∀ i, ¬ (E.birth i = x ∧ E.death i = y) := fun i hi ↦ by
        have := E.birth_lt_death i
        rw [hi.1, hi.2] at this
        exact hxy this
      rw [Finset.filter_false_of_mem (fun i _ ↦ hD i), Finset.filter_false_of_mem (fun i _ ↦ hE i),
        Finset.card_empty, Finset.card_empty]
  obtain ⟨σ, hσ⟩ := exists_equiv_comp_eq_of_card_filter_eq
    (fun i ↦ (D.birth i, D.death i)) (fun i ↦ (E.birth i, E.death i)) (fun c ↦ by convert hfib c)
  obtain ⟨τ, hτ⟩ := exists_equiv_comp_eq_of_card_filter_eq e e'
    (card_filter_eq_of_card_filter_le_eq e e' hM)
  exact ⟨σ, fun i ↦ ⟨congrArg Prod.fst (hσ i), congrArg Prod.snd (hσ i)⟩, τ, hτ⟩

/-- Full diagrams with the same counts of bars containing each interval `[a, b]` are at
bottleneck distance zero. -/
theorem fullBottleneckEDist_eq_zero_of_card_eq {α β κ κ' : Type*} [Fintype α] [Fintype β]
    [Fintype κ] [Fintype κ'] (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β)
    (e' : κ' → ℝ)
    (h : ∀ a b, a ≤ b →
      (Finset.univ.filter fun i ↦ D.birth i ≤ a ∧ b < D.death i).card +
          (Finset.univ.filter fun k ↦ e k ≤ a).card =
        (Finset.univ.filter fun i ↦ E.birth i ≤ a ∧ b < E.death i).card +
          (Finset.univ.filter fun k ↦ e' k ≤ a).card) :
    fullBottleneckEDist D e E e' = 0 := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_equiv_of_card_eq D e E e' h
  have hb : ∀ i, E.birth (σ i) = D.birth i := fun i ↦ (hσ i).1
  have hd : ∀ i, E.death (σ i) = D.death i := fun i ↦ (hσ i).2
  let M : DiagramMatching α β :=
    { relates := fun i j ↦ j = σ i
      left_unique := fun i j k hj hk ↦ hj.trans hk.symm
      right_unique := fun i j k hi hj ↦ σ.injective (hi.symm.trans hj) }
  refine le_antisymm (max_le ?_ ?_) bot_le
  · refine (iInf_le _ M).trans (M.cost_le D E (fun i j hij ↦ ?_) (fun i hi ↦ ?_) (fun j hj ↦ ?_))
    · change j = σ i at hij
      subst hij
      simp [hb, hd]
    · exact absurd ⟨σ i, rfl⟩ hi
    · exact absurd ⟨σ.symm j, by simp [M]⟩ hj
  · refine (iInf_le _ τ).trans (iSup_le fun k ↦ ?_)
    simp [hτ]

namespace DiagramMatching

variable {α β γ : Type*} (M : DiagramMatching α β) (D : FiniteDeathDiagram α)
  (E : FiniteDeathDiagram β)

/-- The distance of a left point to its partner, or to the diagonal when it is unmatched. -/
def leftCost (i : α) : ℝ≥0∞ :=
  if h : ∃ j, M.relates i j then
    ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
  else ENNReal.ofReal ((D.death i - D.birth i) / 2)

/-- The distance of an unmatched right point to the diagonal, and zero for a matched one. -/
def rightCost (j : β) : ℝ≥0∞ :=
  if ∃ i, M.relates i j then 0 else ENNReal.ofReal ((E.death j - E.birth j) / 2)

/-- The left term of a matched point is its distance to the partner. -/
theorem leftCost_of_relates {i : α} {j : β} (h : M.relates i j) :
    M.leftCost D E i = ENNReal.ofReal (max |D.birth i - E.birth j| |D.death i - E.death j|) := by
  have hex : ∃ j, M.relates i j := ⟨j, h⟩
  have hc : hex.choose = j := M.left_unique _ _ _ hex.choose_spec h
  rw [leftCost, dite_eq_left hex, hc]

/-- The left term of an unmatched point is its distance to the diagonal. -/
theorem leftCost_of_not {i : α} (h : ¬ ∃ j, M.relates i j) :
    M.leftCost D E i = ENNReal.ofReal ((D.death i - D.birth i) / 2) := by
  rw [leftCost, dite_eq_right h]

/-- The right term of a matched point is zero. -/
theorem rightCost_of_relates {i : α} {j : β} (h : M.relates i j) : M.rightCost E j = 0 := by
  rw [rightCost, ite_eq_left ⟨i, h⟩]

/-- The right term of an unmatched point is its distance to the diagonal. -/
theorem rightCost_of_not {j : β} (h : ¬ ∃ i, M.relates i j) :
    M.rightCost E j = ENNReal.ofReal ((E.death j - E.birth j) / 2) := by
  rw [rightCost, ite_eq_right h]

end DiagramMatching

/-- The `q`-Wasserstein cost as a sum of left terms, right terms, and essential terms. -/
theorem diagramWassersteinCost_eq {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (M : DiagramMatching α β) (σ : κ ≃ κ') (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) :
    diagramWassersteinCost q M σ D e E e' = ∑ i, M.leftCost D E i ^ q +
      ∑ j, M.rightCost E j ^ q + ∑ k, ENNReal.ofReal |e k - e' (σ k)| ^ q := by
  unfold diagramWassersteinCost DiagramMatching.leftCost DiagramMatching.rightCost
  congr 2 <;> exact Finset.sum_congr rfl fun j _ ↦ by congr 1; split_ifs <;> rfl

/-- Summing a function of the partner along a partial bijection. -/
private theorem sum_dite_exists_eq {γ β : Type*} [Fintype γ] [Fintype β] (R : γ → β → Prop)
    (hR1 : ∀ k j j', R k j → R k j' → j = j') (hR2 : ∀ k k' j, R k j → R k' j → k = k')
    (F : β → ℝ≥0∞) :
    ∑ k, (if h : ∃ j, R k j then F h.choose else 0) = ∑ j, (if ∃ k, R k j then F j else 0) := by
  have h1 : ∀ k, (if h : ∃ j, R k j then F h.choose else 0) =
      ∑ j, (if R k j then F j else 0) := by
    intro k
    by_cases h : ∃ j, R k j
    · rw [dite_eq_left h, Finset.sum_eq_single h.choose]
      · rw [ite_eq_left h.choose_spec]
      · intro j _ hj
        rw [ite_eq_right]
        exact fun hkj ↦ hj (hR1 _ _ _ hkj h.choose_spec)
      · simp
    · rw [dite_eq_right h]
      push Not at h
      simp [h]
  have h2 : ∀ j, ∑ k, (if R k j then F j else 0) = if ∃ k, R k j then F j else 0 := by
    intro j
    by_cases h : ∃ k, R k j
    · obtain ⟨k0, hk0⟩ := h
      rw [ite_eq_left ⟨k0, hk0⟩, Finset.sum_eq_single k0]
      · rw [ite_eq_left hk0]
      · intro k _ hk
        rw [ite_eq_right]
        exact fun hkj ↦ hk (hR2 _ _ _ hkj hk0)
      · simp
    · push Not at h
      simp [h]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [h2]

/-- A power of a conditional with zero default, for a positive exponent. -/
private theorem dite_rpow_eq {p : Prop} [Decidable p] {q : ℝ} (hq : 0 < q) (x : p → ℝ≥0∞) :
    (if h : p then x h else 0) ^ q = if h : p then x h ^ q else 0 := by
  split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq]

/-- The cost of a composite matching, to the power `1/q`, is at most the sum of the costs of the
two matchings, to the power `1/q` (Minkowski's inequality). -/
theorem diagramWassersteinCost_trans_rpow_le {α β γ κ κ' κ'' : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype κ] [Fintype κ'] {q : ℝ} (hq : 1 ≤ q) (M : DiagramMatching α β)
    (N : DiagramMatching β γ) (σ : κ ≃ κ') (τ : κ' ≃ κ'') (D : FiniteDeathDiagram α)
    (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) (F : FiniteDeathDiagram γ)
    (e'' : κ'' → ℝ) :
    diagramWassersteinCost q (M.trans N) (σ.trans τ) D e F e'' ^ (1 / q) ≤
      diagramWassersteinCost q M σ D e E e' ^ (1 / q) +
        diagramWassersteinCost q N τ E e' F e'' ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  let T : α ⊕ γ ⊕ κ → ℝ≥0∞ := Sum.elim (fun i ↦ (M.trans N).leftCost D F i)
    (Sum.elim (fun k ↦ (M.trans N).rightCost F k) (fun k ↦ ENNReal.ofReal |e k - e'' (τ (σ k))|))
  let A : α ⊕ γ ⊕ κ → ℝ≥0∞ := Sum.elim (fun i ↦ M.leftCost D E i)
    (Sum.elim (fun k ↦ if h : ∃ j, N.relates j k then M.rightCost E h.choose else 0)
      (fun k ↦ ENNReal.ofReal |e k - e' (σ k)|))
  let B : α ⊕ γ ⊕ κ → ℝ≥0∞ :=
    Sum.elim (fun i ↦ if h : ∃ j, M.relates i j then N.leftCost E F h.choose else 0)
      (Sum.elim (fun k ↦ if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftCost E F h.choose)
        else N.rightCost F k) (fun k ↦ ENNReal.ofReal |e' (σ k) - e'' (τ (σ k))|))
  have hcost : diagramWassersteinCost q (M.trans N) (σ.trans τ) D e F e'' = ∑ x, T x ^ q := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
    rfl
  have hTAB : ∀ x, T x ≤ A x + B x := by
    rintro (i | k | k)
    · change (M.trans N).leftCost D F i ≤ M.leftCost D E i +
        (if h : ∃ j, M.relates i j then N.leftCost E F h.choose else 0)
      by_cases hi : ∃ j, M.relates i j
      · have hij : M.relates i hi.choose := hi.choose_spec
        rw [dite_eq_left hi, M.leftCost_of_relates D E hij]
        by_cases hj : ∃ k, N.relates hi.choose k
        · obtain ⟨k, hjk⟩ := hj
          rw [(M.trans N).leftCost_of_relates D F ⟨_, hij, hjk⟩, N.leftCost_of_relates E F hjk,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_)
          · exact (abs_sub_le _ (E.birth hi.choose) _).trans
              (add_le_add (le_max_left _ _) (le_max_left _ _))
          · exact (abs_sub_le _ (E.death hi.choose) _).trans
              (add_le_add (le_max_right _ _) (le_max_right _ _))
        · have hnot : ¬ ∃ k, (M.trans N).relates i k := by
            rintro ⟨k, j', h1, h2⟩
            obtain rfl := M.left_unique _ _ _ hij h1
            exact hj ⟨k, h2⟩
          have hlt := E.birth_lt_death hi.choose
          rw [(M.trans N).leftCost_of_not D F hnot, N.leftCost_of_not E F hj,
            ← ENNReal.ofReal_add (by positivity) (by linarith)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := le_abs_self (D.death i - E.death hi.choose)
          have h2 := neg_abs_le (D.birth i - E.birth hi.choose)
          have h3 := le_max_left |D.birth i - E.birth hi.choose| |D.death i - E.death hi.choose|
          have h4 := le_max_right |D.birth i - E.birth hi.choose| |D.death i - E.death hi.choose|
          linarith
      · have hnot : ¬ ∃ k, (M.trans N).relates i k := by
          rintro ⟨k, j', h1, -⟩
          exact hi ⟨j', h1⟩
        rw [dite_eq_right hi, add_zero, (M.trans N).leftCost_of_not D F hnot,
          M.leftCost_of_not D E hi]
    · change (M.trans N).rightCost F k ≤
        (if h : ∃ j, N.relates j k then M.rightCost E h.choose else 0) +
        (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftCost E F h.choose)
        else N.rightCost F k)
      by_cases hk : ∃ j, N.relates j k
      · have hjk : N.relates hk.choose k := hk.choose_spec
        rw [dite_eq_left hk, dite_eq_left hk]
        by_cases hj : ∃ i, M.relates i hk.choose
        · obtain ⟨i, hij⟩ := hj
          rw [(M.trans N).rightCost_of_relates F (i := i) ⟨_, hij, hjk⟩]
          exact bot_le
        · have hnot : ¬ ∃ i, (M.trans N).relates i k := by
            rintro ⟨i, j', h1, h2⟩
            obtain rfl := N.right_unique _ _ _ h2 hjk
            exact hj ⟨i, h1⟩
          have hlt := E.birth_lt_death hk.choose
          rw [ite_eq_right hj, M.rightCost_of_not E hj, N.leftCost_of_relates E F hjk,
            (M.trans N).rightCost_of_not F hnot, ← ENNReal.ofReal_add (by linarith) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := neg_abs_le (E.death hk.choose - F.death k)
          have h2 := le_abs_self (E.birth hk.choose - F.birth k)
          have h3 := le_max_left |E.birth hk.choose - F.birth k| |E.death hk.choose - F.death k|
          have h4 := le_max_right |E.birth hk.choose - F.birth k| |E.death hk.choose - F.death k|
          linarith
      · have hnot : ¬ ∃ i, (M.trans N).relates i k := by
          rintro ⟨i, j', -, h2⟩
          exact hk ⟨j', h2⟩
        rw [dite_eq_right hk, dite_eq_right hk, zero_add, (M.trans N).rightCost_of_not F hnot,
          N.rightCost_of_not F hk]
    · change ENNReal.ofReal |e k - e'' (τ (σ k))| ≤ ENNReal.ofReal |e k - e' (σ k)| +
        ENNReal.ofReal |e' (σ k) - e'' (τ (σ k))|
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
  have hA : ∑ x, A x ^ q ≤ diagramWassersteinCost q M σ D e E e' := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc]
    refine add_le_add (add_le_add le_rfl ?_) le_rfl
    change ∑ k, (if h : ∃ j, N.relates j k then M.rightCost E h.choose else 0) ^ q ≤ _
    simp_rw [dite_rpow_eq hq0]
    rw [sum_dite_exists_eq (fun k j ↦ N.relates j k) (fun k j j' h h' ↦ N.right_unique _ _ _ h h')
      (fun k k' j h h' ↦ N.left_unique _ _ _ h h') (fun j ↦ M.rightCost E j ^ q)]
    exact Finset.sum_le_sum fun j _ ↦ by split_ifs <;> simp
  have hB : ∑ x, B x ^ q ≤ diagramWassersteinCost q N τ E e' F e'' := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h1 : ∑ i, B (.inl i) ^ q =
        ∑ j, (if ∃ i, M.relates i j then N.leftCost E F j ^ q else 0) := by
      change ∑ i, (if h : ∃ j, M.relates i j then N.leftCost E F h.choose else 0) ^ q = _
      simp_rw [dite_rpow_eq hq0]
      exact sum_dite_exists_eq M.relates (fun i j j' h h' ↦ M.left_unique _ _ _ h h')
        (fun i i' j h h' ↦ M.right_unique _ _ _ h h') (fun j ↦ N.leftCost E F j ^ q)
    have h2 : ∑ k, B (.inr (.inl k)) ^ q ≤
        ∑ j, (if ∃ i, M.relates i j then 0 else N.leftCost E F j ^ q) +
          ∑ k, N.rightCost F k ^ q := by
      have hpt : ∀ k, B (.inr (.inl k)) ^ q ≤ (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftCost E F h.choose ^ q) else 0) +
          N.rightCost F k ^ q := by
        intro k
        change (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftCost E F h.choose)
          else N.rightCost F k) ^ q ≤ _
        split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq0]
      refine (Finset.sum_le_sum fun k _ ↦ hpt k).trans ?_
      rw [Finset.sum_add_distrib]
      refine add_le_add ?_ le_rfl
      rw [sum_dite_exists_eq (fun k j ↦ N.relates j k) (fun k j j' h h' ↦ N.right_unique _ _ _ h h')
        (fun k k' j h h' ↦ N.left_unique _ _ _ h h')
        (fun j ↦ if ∃ i, M.relates i j then 0 else N.leftCost E F j ^ q)]
      exact Finset.sum_le_sum fun j _ ↦ by split_ifs <;> simp
    have h3 : ∑ k, B (.inr (.inr k)) ^ q = ∑ j, ENNReal.ofReal |e' j - e'' (τ j)| ^ q :=
      Equiv.sum_comp σ (fun j ↦ ENNReal.ofReal |e' j - e'' (τ j)| ^ q)
    have h4 : ∑ j, (if ∃ i, M.relates i j then N.leftCost E F j ^ q else 0) +
        ∑ j, (if ∃ i, M.relates i j then 0 else N.leftCost E F j ^ q) =
        ∑ j, N.leftCost E F j ^ q := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
    rw [h1, h3, ← h4]
    calc _ ≤ ∑ j, (if ∃ i, M.relates i j then N.leftCost E F j ^ q else 0) +
          ((∑ j, (if ∃ i, M.relates i j then 0 else N.leftCost E F j ^ q) +
            ∑ k, N.rightCost F k ^ q) + ∑ j, ENNReal.ofReal |e' j - e'' (τ j)| ^ q) :=
          add_le_add le_rfl (add_le_add h2 le_rfl)
      _ = _ := by ring
  calc diagramWassersteinCost q (M.trans N) (σ.trans τ) D e F e'' ^ (1 / q)
      = (∑ x, T x ^ q) ^ (1 / q) := by rw [hcost]
    _ ≤ (∑ x, (A x + B x) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ ↦ ENNReal.rpow_le_rpow (hTAB x) hq0.le)
          (by positivity)
    _ ≤ (∑ x, A x ^ q) ^ (1 / q) + (∑ x, B x ^ q) ^ (1 / q) := ENNReal.Lp_add_le _ _ _ hq
    _ ≤ _ := add_le_add (ENNReal.rpow_le_rpow hA (by positivity))
        (ENNReal.rpow_le_rpow hB (by positivity))

/-- The triangle inequality for the `q`-Wasserstein distance of full diagrams, `1 ≤ q`. -/
theorem diagramWassersteinEDist_triangle {α β γ κ κ' κ'' : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype κ] [Fintype κ'] {q : ℝ} (hq : 1 ≤ q) (D : FiniteDeathDiagram α)
    (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) (F : FiniteDeathDiagram γ)
    (e'' : κ'' → ℝ) :
    diagramWassersteinEDist q D e F e'' ≤
      diagramWassersteinEDist q D e E e' + diagramWassersteinEDist q E e' F e'' := by
  unfold diagramWassersteinEDist
  refine ENNReal.le_iInf_add_iInf fun M N ↦ ENNReal.le_iInf_add_iInf fun σ τ ↦ ?_
  exact (iInf_le_of_le (M.trans N) (iInf_le _ (σ.trans τ))).trans
    (diagramWassersteinCost_trans_rpow_le hq M N σ τ D e E e' F e'')

end Distances

end CKSD
