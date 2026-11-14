module

public import CKSD.Geometry.Persistence
public import CKSD.Geometry.MatrixReduction
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Topology.MetricSpace.GromovHausdorff
public import Mathlib.LinearAlgebra.Matrix.ToLin


/-!
# Finite simplicial persistence rank invariants

Finite oriented simplicial chains, sublevel cycles and boundaries, and the rank invariant of
persistent homology. Finite barcodes are reconstructed from rank multiplicities at filtration
values. The filtration function `f` on simplices is arbitrary unless stated otherwise; the
homological reading of the rank invariant needs `f` monotone on faces (`IsMonotoneOnFaces`).

## Main definitions

* `CKSD.simplexIncidence`, `CKSD.simplicialBoundary`: signed incidences and the boundary map.
* `CKSD.sublevelChains`, `CKSD.sublevelCycles`, `CKSD.sublevelBoundaries`.
* `CKSD.sublevelPersistentBetti`, `CKSD.sublevelPersistentHomology`.
* `CKSD.IsSublevelDiagram`: a full persistence diagram of a sublevel filtration.

## Main results

* `CKSD.exists_is_sublevel_diagram`: existence of sublevel diagrams (GAPS 108.18).
* `CKSD.simplicial_boundary_apply_simplicial_boundary`: the boundary squares to zero.
-/

@[expose] public section

noncomputable section

open Module Set
open scoped ENNReal NNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The rank inequality behind the nonnegativity of persistence multiplicities: for `Y ≤ X` and
`U ≤ V`, `dim (Y ⊓ V) + dim (X ⊓ U) ≤ dim (X ⊓ V) + dim (Y ⊓ U)`. -/
theorem finrank_inf_add_finrank_inf_le {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {X Y U V : Submodule 𝕜 W} (hYX : Y ≤ X) (hUV : U ≤ V) :
    finrank 𝕜 ↥(Y ⊓ V) + finrank 𝕜 ↥(X ⊓ U) ≤ finrank 𝕜 ↥(X ⊓ V) + finrank 𝕜 ↥(Y ⊓ U) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ V) (X ⊓ U)
  have hinf : Y ⊓ V ⊓ (X ⊓ U) = Y ⊓ U := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans hUV))
        (le_inf (inf_le_left.trans hYX) inf_le_right)
  have hsup : Y ⊓ V ⊔ X ⊓ U ≤ X ⊓ V :=
    sup_le (inf_le_inf_right _ hYX) (inf_le_inf_left _ hUV)
  rw [hinf] at h
  have := Submodule.finrank_mono hsup
  omega

/-- For `Y ≤ X`: `dim Y + dim (X ⊓ U) ≤ dim X + dim (Y ⊓ U)`. -/
theorem finrank_add_finrank_inf_le {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] {X Y U : Submodule 𝕜 W} (hYX : Y ≤ X) :
    finrank 𝕜 Y + finrank 𝕜 ↥(X ⊓ U) ≤ finrank 𝕜 X + finrank 𝕜 ↥(Y ⊓ U) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq Y (X ⊓ U)
  have hinf : Y ⊓ (X ⊓ U) = Y ⊓ U := by
    rw [← inf_assoc, inf_eq_left.mpr hYX]
  rw [hinf] at h
  have := Submodule.finrank_mono (sup_le hYX inf_le_left : Y ⊔ X ⊓ U ≤ X)
  omega

/-- Two-variable telescoping of a function vanishing at the first index `0`. -/
theorem eq_sum_sum_add_sum_of_eq_zero (r : ℕ → ℕ → ℤ) (h0 : ∀ j, r 0 j = 0) (i j n : ℕ)
    (hjn : j ≤ n) :
    r i j = (∑ s ∈ Finset.range i, ∑ t ∈ Finset.range (n - j),
        (r (s + 1) (j + t) - r s (j + t) - r (s + 1) (j + t + 1) + r s (j + t + 1))) +
      ∑ s ∈ Finset.range i, (r (s + 1) n - r s n) := by
  have hinner : ∀ s, ∑ t ∈ Finset.range (n - j),
      (r (s + 1) (j + t) - r s (j + t) - r (s + 1) (j + t + 1) + r s (j + t + 1)) =
      (r (s + 1) j - r s j) - (r (s + 1) n - r s n) := by
    intro s
    have := Finset.sum_range_sub' (fun t ↦ r (s + 1) (j + t) - r s (j + t)) (n - j)
    simp only [add_zero, Nat.add_sub_cancel' hjn] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [show j + (t + 1) = j + t + 1 by ring]
    ring
  simp_rw [hinner]
  rw [← Finset.sum_add_distrib]
  simp only [sub_add_cancel]
  rw [Finset.sum_range_sub (fun s ↦ r s j), h0, sub_zero]

/-- Counting the elements of a sigma type over the fibres where a predicate holds. -/
theorem card_filter_sigma_fin {β : Type*} [Fintype β] (M : β → ℕ) (P : β → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x : (Σ q, Fin (M q)) ↦ P x.1).card =
      ∑ q, if P q then M q else 0 := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  split_ifs <;> simp

/-- A sum over `Fin n` of the indices below `k ≤ n` is a sum over `range k`. -/
theorem sum_fin_ite_lt_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) {n k : ℕ}
    (hk : k ≤ n) : (∑ s : Fin n, if s.val < k then F s.val else 0) = ∑ s ∈ Finset.range k, F s := by
  rw [Fin.sum_univ_eq_sum_range (fun s ↦ if s < k then F s else 0) n, ← Finset.sum_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A sum over `Fin n` of the indices at least `k ≤ n` is a sum over `range (n - k)`. -/
theorem sum_fin_ite_le_eq_sum_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) {n k : ℕ} :
    (∑ u : Fin n, if k ≤ u.val then F u.val else 0) =
      ∑ t ∈ Finset.range (n - k), F (k + t) := by
  rw [Fin.sum_univ_eq_sum_range (fun u ↦ if k ≤ u then F u else 0) n, ← Finset.sum_filter,
    ← Finset.sum_Ico_eq_sum_range]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

section Chains

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

/-- Signed incidence number of the face `τ` in the simplex `σ`: nonzero exactly when `τ` is a
nonempty codimension-one face, with sign `(-1)^k` where the deleted vertex is the `k`th vertex of
`σ` in increasing order (counting from `0`). -/
def simplexIncidence (τ σ : Finset ι) : 𝕜 :=
  if τ.Nonempty ∧ τ ⊆ σ ∧ τ.card + 1 = σ.card then
    (-1) ^ (σ.filter fun w ↦ ∃ v ∈ σ \ τ, w < v).card
  else 0

/-- The simplicial boundary on chains, which are functions on finite vertex sets. Vertices have
zero boundary (no augmentation). -/
def simplicialBoundary : (Finset ι → 𝕜) →ₗ[𝕜] (Finset ι → 𝕜) :=
  (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ).mulVecLin

/-- A function on simplices is monotone along faces of `K`. -/
def IsMonotoneOnFaces (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) : Prop :=
  ∀ τ σ, σ ∈ K → τ.Nonempty → τ ⊆ σ → f τ ≤ f σ

/-- Chains of dimension `p` of the sublevel subcomplex `K_a = {σ ∈ K : f σ ≤ a}`. -/
def sublevelChains (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ) (a : ℝ) :
    Submodule 𝕜 (Finset ι → 𝕜) where
  carrier := {c | ∀ σ, c σ ≠ 0 → σ ∈ K ∧ σ.card = p + 1 ∧ f σ ≤ a}
  zero_mem' := by simp
  add_mem' := by
    intro c c' hc hc' σ hσ
    by_cases h : c σ = 0
    · exact hc' σ (by simpa [h] using hσ)
    · exact hc σ h
  smul_mem' := by
    intro r c hc σ hσ
    exact hc σ (right_ne_zero_of_mul (by simpa using hσ))

/-- Cycles of dimension `p` of `K_a`. -/
def sublevelCycles (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ) (a : ℝ) :
    Submodule 𝕜 (Finset ι → 𝕜) :=
  sublevelChains 𝕜 K f p a ⊓ LinearMap.ker (simplicialBoundary 𝕜)

/-- Boundaries of dimension `p` of `K_b`. -/
def sublevelBoundaries (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (b : ℝ) : Submodule 𝕜 (Finset ι → 𝕜) :=
  (sublevelChains 𝕜 K f (p + 1) b).map (simplicialBoundary 𝕜)

/-- Persistent Betti number `dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))`, where `Z_p(K_a)` and
`B_p(K_b)` are the cycles and boundaries of the chains spanned by simplices of value at most `a`,
respectively `b`. Monotonicity of `f` is not assumed; when `f` is `IsMonotoneOnFaces`, the sets
`K_a` are subcomplexes and this is the rank of `H_p(K_a) → H_p(K_b)` for `a ≤ b`. -/
def sublevelPersistentBetti (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (a b : ℝ) : ℕ :=
  finrank 𝕜 (sublevelCycles 𝕜 K f p a) -
    finrank 𝕜 ↥(sublevelCycles 𝕜 K f p a ⊓ sublevelBoundaries 𝕜 K f p b)

/-- The persistent homology group `Z_p(K_a) / (Z_p(K_a) ∩ B_p(K_b))` in degree `p`. When `f` is
`IsMonotoneOnFaces` and `a ≤ b`, it is the image of `H_p(K_a) → H_p(K_b)`. -/
abbrev sublevelPersistentHomology (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (a b : ℝ) : Type _ :=
  ↥(sublevelCycles 𝕜 K f p a) ⧸
    (sublevelBoundaries 𝕜 K f p b).comap (sublevelCycles 𝕜 K f p a).subtype

/-- `(D, e)` is the degree-`p` persistence diagram of the sublevel filtration of `f`: finite bars
`[D.birth i, D.death i)` and essential bars `[e k, ∞)`, such that for `a ≤ b` the persistent
Betti number counts the bars containing `[a, b]`. -/
def IsSublevelDiagram (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {α κ : Type*} [Fintype α] [Fintype κ] (D : FiniteDeathDiagram α) (e : κ → ℝ) : Prop :=
  ∀ a b, a ≤ b → sublevelPersistentBetti 𝕜 K f p a b =
    (Finset.univ.filter fun i ↦ D.birth i ≤ a ∧ b < D.death i).card +
      (Finset.univ.filter fun k ↦ e k ≤ a).card

omit [Fintype ι] [LinearOrder ι] in
/-- Sublevel chains grow with the level. -/
theorem sublevel_chains_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (q : ℕ)
    {a a' : ℝ} (h : a ≤ a') : sublevelChains 𝕜 K f q a ≤ sublevelChains 𝕜 K f q a' := by
  intro c hc σ hσ
  obtain ⟨h1, h2, h3⟩ := hc σ hσ
  exact ⟨h1, h2, h3.trans h⟩

omit [Fintype ι] [LinearOrder ι] in
/-- Sublevel chains of two functions agree when the sublevel sets agree on `K`. -/
theorem sublevel_chains_congr_fun (K : PreAbstractSimplicialComplex ι) {f h : Finset ι → ℝ}
    (q : ℕ) {a a' : ℝ} (hiff : ∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a') :
    sublevelChains 𝕜 K f q a = sublevelChains 𝕜 K h q a' := by
  ext c
  constructor
  · intro hc σ hσ
    obtain ⟨h1, h2, h3⟩ := hc σ hσ
    exact ⟨h1, h2, (hiff σ h1).mp h3⟩
  · intro hc σ hσ
    obtain ⟨h1, h2, h3⟩ := hc σ hσ
    exact ⟨h1, h2, (hiff σ h1).mpr h3⟩

/-- Persistent Betti numbers of two functions agree when the two pairs of sublevel sets agree. -/
theorem sublevel_persistent_betti_congr_fun (K : PreAbstractSimplicialComplex ι)
    {f h : Finset ι → ℝ} (p : ℕ) {a a' b b' : ℝ} (ha : ∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a')
    (hb : ∀ σ ∈ K, f σ ≤ b ↔ h σ ≤ b') :
    sublevelPersistentBetti 𝕜 K f p a b = sublevelPersistentBetti 𝕜 K h p a' b' := by
  unfold sublevelPersistentBetti sublevelCycles sublevelBoundaries
  rw [sublevel_chains_congr_fun 𝕜 K p ha, sublevel_chains_congr_fun 𝕜 K (p + 1) hb]

/-- The persistent Betti number as an integer difference of dimensions. -/
theorem sublevel_persistent_betti_cast (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
    (p : ℕ) (a b : ℝ) :
    (sublevelPersistentBetti 𝕜 K f p a b : ℤ) =
      (finrank 𝕜 (sublevelCycles 𝕜 K f p a) : ℤ) -
        finrank 𝕜 ↥(sublevelCycles 𝕜 K f p a ⊓ sublevelBoundaries 𝕜 K f p b) := by
  unfold sublevelPersistentBetti
  have := Submodule.finrank_mono (inf_le_left (a := sublevelCycles 𝕜 K f p a)
    (b := sublevelBoundaries 𝕜 K f p b))
  omega

/-- A sublevel diagram indexed by arbitrary finite types can be reindexed by `Fin`. -/
theorem IsSublevelDiagram.exists_fin {K : PreAbstractSimplicialComplex ι} {f : Finset ι → ℝ}
    {p : ℕ} {α κ : Type*} [Fintype α] [Fintype κ] {D : FiniteDeathDiagram α} {e : κ → ℝ}
    (h : IsSublevelDiagram 𝕜 K f p D e) :
    ∃ (n r : ℕ) (D' : FiniteDeathDiagram (Fin n)) (e' : Fin r → ℝ),
      IsSublevelDiagram 𝕜 K f p D' e' := by
  set σ := Fintype.equivFin α
  set τ := Fintype.equivFin κ
  refine ⟨Fintype.card α, Fintype.card κ,
    ⟨D.birth ∘ σ.symm, D.death ∘ σ.symm, fun i ↦ D.birth_lt_death _⟩, e ∘ τ.symm,
    fun a b hab ↦ ?_⟩
  rw [h a b hab]
  congr 1
  · exact Finset.card_equiv σ (fun i ↦ by simp)
  · exact Finset.card_equiv τ (fun i ↦ by simp)

/-- Strengthened existence of sublevel diagrams: the bars can be chosen with endpoints that are
values of `f` at simplices of `K`. -/
theorem exists_is_sublevel_diagram_and_values (K : PreAbstractSimplicialComplex ι)
    (f : Finset ι → ℝ) (p : ℕ) :
    ∃ (n r : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ),
      IsSublevelDiagram 𝕜 K f p D e ∧ (∀ i, ∃ σ ∈ K, f σ = D.birth i) ∧
        (∀ i, ∃ σ ∈ K, f σ = D.death i) ∧ ∀ k, ∃ σ ∈ K, f σ = e k := by
  -- the critical values `c 0 < ⋯ < c (n - 1)`
  set T := (Finset.univ.filter (· ∈ K)).image f
  set n := T.card
  set c := T.orderEmbOfFin rfl
  have hc_mem : ∀ s, c s ∈ T := fun s ↦ T.orderEmbOfFin_mem rfl s
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, ∀ s, t0 < c s := by
    obtain ⟨M, hM⟩ := Finite.exists_ge c
    exact ⟨M - 1, fun s ↦ by linarith [hM s]⟩
  have hval : ∀ σ ∈ K, ∃ s, c s = f σ := by
    intro σ hσ
    have hT : f σ ∈ T := Finset.mem_image_of_mem f (by simpa using hσ)
    have hT' : f σ ∈ Set.range c := by
      rw [T.range_orderEmbOfFin rfl]
      exact hT
    exact hT'
  -- levels: `tl 0` lies below all values, `tl (s + 1) = c s`
  set tl : ℕ → ℝ := fun i ↦ if h : i ≠ 0 ∧ i ≤ n then c ⟨i - 1, by omega⟩ else t0
  have htl0 : tl 0 = t0 := by simp [tl]
  have htls : ∀ s : Fin n, tl (s.val + 1) = c s := by
    intro s
    simp only [tl]
    rw [dite_eq_left ⟨by omega, s.2⟩]
    rfl
  have htl_mono : ∀ i i', i ≤ i' → i' ≤ n → tl i ≤ tl i' := by
    intro i i' hii' hi'
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [htl0]
      rcases Nat.eq_zero_or_pos i' with rfl | hi''
      · rw [htl0]
      · have := htls ⟨i' - 1, by omega⟩
        simp only [show i' - 1 + 1 = i' by omega] at this
        rw [this]
        exact (ht0 _).le
    · have e1 := htls ⟨i - 1, by omega⟩
      have e2 := htls ⟨i' - 1, by omega⟩
      simp only [show i - 1 + 1 = i by omega, show i' - 1 + 1 = i' by omega] at e1 e2
      rw [e1, e2]
      exact c.monotone (Fin.mk_le_mk.mpr (by omega))
  -- the level index of a real number
  set k : ℝ → ℕ := fun a ↦ (Finset.univ.filter fun s : Fin n ↦ c s ≤ a).card
  have hk_le : ∀ a, k a ≤ n := fun a ↦ (Finset.card_filter_le _ _).trans (by simp)
  have hk_iff : ∀ a (s : Fin n), c s ≤ a ↔ s.val < k a := by
    intro a s
    constructor
    · intro hs
      have hsub : Finset.Iic s ⊆ Finset.univ.filter fun s : Fin n ↦ c s ≤ a := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (c.monotone (Finset.mem_Iic.mp hi)).trans hs
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this
      simp only [k]
      omega
    · intro hs
      by_contra hcon
      have hsub : (Finset.univ.filter fun s : Fin n ↦ c s ≤ a) ⊆ Finset.Iio s := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_Iio]
        by_contra hle
        exact hcon ((c.monotone (not_lt.mp hle)).trans hi)
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      simp only [k] at hs
      omega
  have hk_mono : ∀ a b, a ≤ b → k a ≤ k b := fun a b hab ↦
    Finset.card_le_card fun s hs ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact hs.trans hab
  have hlevel : ∀ a, ∀ σ ∈ K, f σ ≤ a ↔ f σ ≤ tl (k a) := by
    intro a σ hσ
    obtain ⟨s, hs⟩ := hval σ hσ
    rw [← hs, hk_iff a s]
    rcases Nat.eq_zero_or_pos (k a) with h0 | hpos
    · rw [h0, htl0]
      simp only [not_lt_zero, false_iff, not_le]
      exact ht0 s
    · have e1 := htls ⟨k a - 1, by have := hk_le a; omega⟩
      simp only [show k a - 1 + 1 = k a by omega] at e1
      rw [e1, c.le_iff_le, Fin.le_def]
      simp only
      omega
  -- the rank function on level indices
  set r : ℕ → ℕ → ℤ := fun i j ↦ sublevelPersistentBetti 𝕜 K f p (tl i) (tl j)
  have hr : ∀ i j, r i j = (finrank 𝕜 (sublevelCycles 𝕜 K f p (tl i)) : ℤ) -
      finrank 𝕜 ↥(sublevelCycles 𝕜 K f p (tl i) ⊓ sublevelBoundaries 𝕜 K f p (tl j)) :=
    fun i j ↦ sublevel_persistent_betti_cast 𝕜 K f p _ _
  have hr0 : ∀ j, r 0 j = 0 := by
    intro j
    have hbot : sublevelChains 𝕜 K f p (tl 0) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      ext σ
      by_contra hσ
      obtain ⟨h1, -, h3⟩ := hx σ hσ
      obtain ⟨s, hs⟩ := hval σ h1
      rw [htl0, ← hs] at h3
      exact absurd h3 (not_le.mpr (ht0 s))
    have hZ0 : sublevelCycles 𝕜 K f p (tl 0) = ⊥ := by
      unfold sublevelCycles
      rw [hbot, bot_inf_eq]
    rw [hr, hZ0, bot_inf_eq]
    simp
  have hZ : ∀ i i', i ≤ i' → i' ≤ n →
      sublevelCycles 𝕜 K f p (tl i) ≤ sublevelCycles 𝕜 K f p (tl i') := fun i i' h h' ↦
    inf_le_inf_right _ (sublevel_chains_mono 𝕜 K f p (htl_mono i i' h h'))
  have hB : ∀ j j', j ≤ j' → j' ≤ n →
      sublevelBoundaries 𝕜 K f p (tl j) ≤ sublevelBoundaries 𝕜 K f p (tl j') := fun j j' h h' ↦
    Submodule.map_mono (sublevel_chains_mono 𝕜 K f (p + 1) (htl_mono j j' h h'))
  -- multiplicities
  set m' : ℕ → ℕ → ℤ := fun s u ↦ r (s + 1) u - r s u - r (s + 1) (u + 1) + r s (u + 1)
  have hm' : ∀ s u, s < n → u < n → 0 ≤ m' s u := by
    intro s u hs hu
    have := finrank_inf_add_finrank_inf_le (hZ s (s + 1) (by omega) (by omega))
      (hB u (u + 1) (by omega) (by omega))
    simp only [m', hr]
    omega
  set e' : ℕ → ℤ := fun s ↦ r (s + 1) n - r s n
  have he' : ∀ s, s < n → 0 ≤ e' s := by
    intro s hs
    have := finrank_add_finrank_inf_le (U := sublevelBoundaries 𝕜 K f p (tl n))
      (hZ s (s + 1) (by omega) (by omega))
    simp only [e', hr]
    omega
  -- the diagram
  set M : Fin n × Fin n → ℕ := fun q ↦ if q.1 < q.2 then (m' q.1 q.2).toNat else 0
  set E : Fin n → ℕ := fun s ↦ (e' s).toNat
  let D0 : FiniteDeathDiagram (Σ q : Fin n × Fin n, Fin (M q)) :=
    { birth := fun x ↦ c x.1.1
      death := fun x ↦ c x.1.2
      birth_lt_death := by
        rintro ⟨q, x⟩
        by_cases hq : q.1 < q.2
        · exact c.strictMono hq
        · simp only [M, hq, ite_false] at x
          exact x.elim0 }
  let e0 : (Σ s : Fin n, Fin (E s)) → ℝ := fun y ↦ c y.1
  have hdiag : IsSublevelDiagram 𝕜 K f p D0 e0 := by
    intro a b hab
    have hka := hk_le a
    have hkb := hk_le b
    have hkab := hk_mono a b hab
    rw [sublevel_persistent_betti_congr_fun 𝕜 K p (hlevel a) (hlevel b)]
    have h1 : ((Finset.univ.filter fun x : (Σ q : Fin n × Fin n, Fin (M q)) ↦
        D0.birth x ≤ a ∧ b < D0.death x).card : ℤ) =
        ∑ s ∈ Finset.range (k a), ∑ t ∈ Finset.range (n - k b), m' s (k b + t) := by
      change ((Finset.univ.filter fun x : (Σ q : Fin n × Fin n, Fin (M q)) ↦
        c x.1.1 ≤ a ∧ b < c x.1.2).card : ℤ) = _
      rw [card_filter_sigma_fin M (fun q ↦ c q.1 ≤ a ∧ b < c q.2)]
      push_cast
      rw [Fintype.sum_prod_type]
      have hterm : ∀ s u : Fin n, (if c s ≤ a ∧ b < c u then ((M (s, u) : ℕ) : ℤ) else 0) =
          if s.val < k a then (if k b ≤ u.val then m' s u else 0) else 0 := by
        intro s u
        have hbu : b < c u ↔ k b ≤ u.val := by
          rw [← not_le, hk_iff b u, not_lt]
        by_cases hs : s.val < k a
        · have h1 : c s ≤ a := (hk_iff a s).mpr hs
          by_cases hu : k b ≤ u.val
          · have h2 : b < c u := hbu.mpr hu
            have hsu : s < u := Fin.lt_def.mpr (by omega)
            simp only [h1, h2, hs, hu, and_self, ite_true, M, hsu]
            exact Int.toNat_of_nonneg (hm' _ _ s.2 u.2)
          · have h2 : ¬ b < c u := fun h ↦ hu (hbu.mp h)
            simp [h2, hu]
        · have h1 : ¬ c s ≤ a := fun h ↦ hs ((hk_iff a s).mp h)
          simp [h1, hs]
      simp_rw [hterm]
      have hout : ∀ s : Fin n, (∑ u : Fin n,
          (if s.val < k a then (if k b ≤ u.val then m' s u else 0) else 0)) =
          if s.val < k a then ∑ u : Fin n, (if k b ≤ u.val then m' s u else 0) else 0 := by
        intro s
        split_ifs <;> simp
      simp_rw [hout]
      rw [sum_fin_ite_lt_eq_sum_range (fun s ↦ ∑ u : Fin n,
        (if k b ≤ u.val then m' s u else 0)) hka]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      exact sum_fin_ite_le_eq_sum_range (fun u ↦ m' s u)
    have h2 : ((Finset.univ.filter fun y : (Σ s : Fin n, Fin (E s)) ↦ e0 y ≤ a).card : ℤ) =
        ∑ s ∈ Finset.range (k a), e' s := by
      change ((Finset.univ.filter fun y : (Σ s : Fin n, Fin (E s)) ↦ c y.1 ≤ a).card : ℤ) = _
      rw [card_filter_sigma_fin E (fun s ↦ c s ≤ a)]
      push_cast
      have hterm : ∀ s : Fin n, (if c s ≤ a then ((E s : ℕ) : ℤ) else 0) =
          if s.val < k a then e' s else 0 := by
        intro s
        by_cases hs : s.val < k a
        · have h1 : c s ≤ a := (hk_iff a s).mpr hs
          simp only [h1, hs, ite_true, E]
          exact Int.toNat_of_nonneg (he' _ s.2)
        · have h1 : ¬ c s ≤ a := fun h ↦ hs ((hk_iff a s).mp h)
          simp [h1, hs]
      simp_rw [hterm]
      exact sum_fin_ite_lt_eq_sum_range e' hka
    have htel := eq_sum_sum_add_sum_of_eq_zero r hr0 (k a) (k b) n hkb
    zify
    rw [h1, h2]
    exact htel
  have hcK : ∀ s, ∃ σ ∈ K, f σ = c s := fun s ↦ by
    obtain ⟨σ, hσ, h⟩ := Finset.mem_image.mp (hc_mem s)
    exact ⟨σ, by simpa using hσ, h⟩
  set σe := Fintype.equivFin (Σ q : Fin n × Fin n, Fin (M q))
  set τe := Fintype.equivFin (Σ s : Fin n, Fin (E s))
  refine ⟨_, _, ⟨D0.birth ∘ σe.symm, D0.death ∘ σe.symm, fun i ↦ D0.birth_lt_death _⟩,
    e0 ∘ τe.symm, fun a b hab ↦ ?_, fun i ↦ hcK _, fun i ↦ hcK _, fun k ↦ hcK _⟩
  rw [hdiag a b hab]
  congr 1
  · exact Finset.card_equiv σe (fun i ↦ by simp)
  · exact Finset.card_equiv τe (fun i ↦ by simp)

/-- GAPS 108.18, finite sublevel form: persistence diagrams of sublevel filtrations of finite
simplicial complexes exist. Monotonicity of `f` is not assumed: the proof uses only that the
chain spaces of `K_a` grow with `a`, and the bars are read off from the rank function at the
critical values by inclusion–exclusion. For `f` monotone on faces this is the interval
decomposition of the finite-type persistence module `a ↦ H_p(K_a)`, read through its rank
invariant. -/
theorem exists_is_sublevel_diagram (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
    (p : ℕ) :
    ∃ (n r : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ),
      IsSublevelDiagram 𝕜 K f p D e := by
  obtain ⟨n, r, D, e, h, -⟩ := exists_is_sublevel_diagram_and_values 𝕜 K f p
  exact ⟨n, r, D, e, h⟩

end Chains

section BoundarySquare

attribute [-instance] Classical.propDecidable

variable {ι : Type*} [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

/-- The incidence number of the face obtained by deleting the vertex `x`: the sign
`(-1)^k` where `x` is the `k`th vertex of `σ`. -/
theorem simplex_incidence_erase {σ : Finset ι} {x : ι} (hx : x ∈ σ) (hne : (σ.erase x).Nonempty) :
    simplexIncidence 𝕜 (σ.erase x) σ = (-1) ^ (σ.filter (· < x)).card := by
  unfold simplexIncidence
  rw [ite_eq_left ⟨hne, Finset.erase_subset _ _, Finset.card_erase_add_one hx⟩]
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨hw, v, ⟨hv, hv'⟩, hwv⟩
    have : v = x := by by_contra h; exact hv' ⟨h, hv⟩
    exact ⟨hw, this ▸ hwv⟩
  · rintro ⟨hw, hwx⟩
    exact ⟨hw, x, ⟨hx, fun h ↦ h.1 rfl⟩, hwx⟩

/-- Incidence numbers vanish unless the first set is obtained by deleting one vertex. -/
theorem simplex_incidence_eq_zero {τ σ : Finset ι} (h : ∀ x ∈ σ, τ ≠ σ.erase x) :
    simplexIncidence 𝕜 τ σ = 0 := by
  unfold simplexIncidence
  rw [ite_eq_right]
  rintro ⟨-, hsub, hcard⟩
  have hc : (σ \ τ).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  have hxσ : x ∈ σ := (Finset.mem_sdiff.mp (hx ▸ Finset.mem_singleton_self x)).1
  refine h x hxσ (Finset.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
  · refine Finset.mem_erase.mpr ⟨?_, hsub hy⟩
    rintro rfl
    exact (Finset.mem_sdiff.mp (hx ▸ Finset.mem_singleton_self y)).2 hy
  · obtain ⟨hyx, hyσ⟩ := Finset.mem_erase.mp hy
    by_contra hyτ
    have : y ∈ σ \ τ := Finset.mem_sdiff.mpr ⟨hyσ, hyτ⟩
    rw [hx] at this
    exact hyx (Finset.mem_singleton.mp this)

/-- Incidence numbers vanish when the face is empty. -/
theorem simplex_incidence_empty_left (σ : Finset ι) : simplexIncidence 𝕜 ∅ σ = 0 := by
  unfold simplexIncidence
  simp

/-- The boundary of a boundary vanishes: `∑_τ [ρ : τ] [τ : σ] = 0`. -/
theorem sum_simplex_incidence_mul_simplex_incidence [Fintype ι] (ρ σ : Finset ι) :
    ∑ τ, simplexIncidence 𝕜 ρ τ * simplexIncidence 𝕜 τ σ = 0 := by
  have hinj : ∀ x ∈ σ, ∀ y ∈ σ, σ.erase x = σ.erase y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have : y ∈ σ.erase x := Finset.mem_erase.mpr ⟨Ne.symm hne, hy⟩
    rw [hxy] at this
    exact (Finset.notMem_erase y σ) this
  rw [← Finset.sum_subset (Finset.subset_univ (σ.image fun x ↦ σ.erase x))]
  swap
  · intro τ _ hτ
    rw [simplex_incidence_eq_zero 𝕜 (σ := σ) (fun x hx h ↦ hτ (Finset.mem_image.mpr ⟨x, hx, h.symm⟩)),
      mul_zero]
  rw [Finset.sum_image hinj]
  by_cases hA : ∃ u ∈ σ, ∃ v ∈ σ, u < v ∧ ρ = (σ.erase u).erase v
  · obtain ⟨u, hu, v, hv, huv, rfl⟩ := hA
    have hvu : v ∈ σ.erase u := Finset.mem_erase.mpr ⟨huv.ne', hv⟩
    have huv' : u ∈ σ.erase v := Finset.mem_erase.mpr ⟨huv.ne, hu⟩
    rw [← Finset.sum_subset (show ({u, v} : Finset ι) ⊆ σ from Finset.insert_subset hu
      (Finset.singleton_subset_iff.mpr hv))]
    swap
    · intro x hx hxuv
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxuv
      rw [simplex_incidence_eq_zero 𝕜, zero_mul]
      intro y _ h
      have : x ∈ (σ.erase u).erase v := by simp [hxuv.1, hxuv.2, hx]
      rw [h] at this
      simp at this
    rw [Finset.sum_pair huv.ne]
    by_cases hne : ((σ.erase u).erase v).Nonempty
    · have hcomm : (σ.erase u).erase v = (σ.erase v).erase u := Finset.erase_right_comm
      have hne1 : (σ.erase u).Nonempty := hne.mono (Finset.erase_subset _ _)
      have hne2 : (σ.erase v).Nonempty := (hcomm ▸ hne).mono (Finset.erase_subset _ _)
      rw [simplex_incidence_erase 𝕜 hvu hne, simplex_incidence_erase 𝕜 hu hne1, hcomm,
        simplex_incidence_erase 𝕜 huv' (hcomm ▸ hne), simplex_incidence_erase 𝕜 hv hne2]
      have h1 : ((σ.erase u).filter (· < v)).card + 1 = (σ.filter (· < v)).card := by
        rw [Finset.filter_erase, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hu, huv⟩)]
      have h2 : ((σ.erase v).filter (· < u)).card = (σ.filter (· < u)).card := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [huv.le])]
      rw [h2, ← h1, pow_succ]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne, simplex_incidence_empty_left]
  · refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [simplex_incidence_eq_zero 𝕜, zero_mul]
    intro y hy h
    obtain ⟨hyx, hyσ⟩ := Finset.mem_erase.mp hy
    rcases lt_or_gt_of_ne hyx with hlt | hlt
    · exact hA ⟨y, hyσ, x, hx, hlt, h.trans Finset.erase_right_comm⟩
    · exact hA ⟨x, hx, y, hyσ, hlt, h⟩

/-- The boundary of a boundary vanishes. -/
theorem simplicial_boundary_apply_simplicial_boundary [Fintype ι] (c : Finset ι → 𝕜) :
    simplicialBoundary 𝕜 (simplicialBoundary 𝕜 c) = 0 := by
  unfold simplicialBoundary
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have : (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ) *
      (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ) = 0 := by
    ext ρ σ
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact sum_simplex_incidence_mul_simplex_incidence 𝕜 ρ σ
  rw [this, Matrix.zero_mulVec]

end BoundarySquare

end CKSD
