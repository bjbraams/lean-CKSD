module

public import CKSD.Geometry.Persistence
public import CKSD.Geometry.MatrixReduction
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Topology.MetricSpace.GromovHausdorff
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Sublevel persistence of monotone functions on finite simplicial complexes

A finite simplicial complex is a Mathlib `PreAbstractSimplicialComplex` on a finite, linearly
ordered vertex type; the order orients simplices. Chains with coefficients in a field `𝕜` are
functions on finite vertex sets, and the boundary is the alternating deleted-vertex sum. For a
function `f` on simplices that is monotone along faces, the sublevel subcomplexes `K_a` form a
filtration, and the persistent Betti number in degree `p` is the rank
`dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))` of the map `H_p(K_a) → H_p(K_b)`.

A persistence diagram of the filtration in degree `p` is described by its finite bars `[b, d)`
(a `FiniteDeathDiagram`, zero-length bars discarded) and the births of its essential bars
`[b, ∞)`, subject to the requirement that for `a ≤ b` the persistent Betti number counts the bars
containing `[a, b]`. The rank invariant determines the diagram, so this pins down the diagram up
to reindexing.

Full diagrams are compared by matching finite bars partially (unmatched points go to the
diagonal) and essential bars bijectively, in the bottleneck and in the `q`-Wasserstein sense.
Both distances satisfy the triangle inequality (for the `q`-Wasserstein distance by Minkowski's
inequality, Mathlib's `ENNReal.Lp_add_le`).

Stability is proved combinatorially. If `f` and `g` are both ordered by a common function `h`
(`h σ ≤ h τ → f σ ≤ f τ`), every diagram of `h` relabels to diagrams of `f` and of `g`, and
matching bars with the same label costs at most `max_σ |f σ - g σ|`; when `h` is injective on `K`,
the endpoint simplices of distinct bars are distinct, which bounds the `q`-Wasserstein cost by
`∑_σ |f σ - g σ|^q`. In general, a convex combination of `f` and `g` that resolves one pair of
simplices ordered oppositely by `f` and `g` splits the comparison into two with fewer such pairs.

The Rips filtration of a finite metric space is the monotone function `σ ↦ diam σ / 2` on the full
simplex, in the diameter-`2r` convention of GAPS 108.21; its Gromov–Hausdorff stability
(GAPS 108.36) is proved in `CKSD.Geometry.RipsStability`.

Sources: GAPS 108.19, 108.35, 108.36.
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

/-- Persistent Betti number: the rank of `H_p(K_a) → H_p(K_b)`, computed as
`dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))`. -/
def sublevelPersistentBetti (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (a b : ℝ) : ℕ :=
  finrank 𝕜 (sublevelCycles 𝕜 K f p a) -
    finrank 𝕜 ↥(sublevelCycles 𝕜 K f p a ⊓ sublevelBoundaries 𝕜 K f p b)

/-- The persistent homology group in degree `p`, the image of `H_p(K_a) → H_p(K_b)`, realized
as `Z_p(K_a) / (Z_p(K_a) ∩ B_p(K_b))`. -/
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
theorem sublevelChains_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (q : ℕ)
    {a a' : ℝ} (h : a ≤ a') : sublevelChains 𝕜 K f q a ≤ sublevelChains 𝕜 K f q a' := by
  intro c hc σ hσ
  obtain ⟨h1, h2, h3⟩ := hc σ hσ
  exact ⟨h1, h2, h3.trans h⟩

omit [Fintype ι] [LinearOrder ι] in
/-- Sublevel chains depend only on the sublevel set. -/
theorem sublevelChains_congr (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (q : ℕ)
    {a a' : ℝ} (h : ∀ σ ∈ K, f σ ≤ a ↔ f σ ≤ a') :
    sublevelChains 𝕜 K f q a = sublevelChains 𝕜 K f q a' := by
  ext c
  constructor
  · intro hc σ hσ
    obtain ⟨h1, h2, h3⟩ := hc σ hσ
    exact ⟨h1, h2, (h σ h1).mp h3⟩
  · intro hc σ hσ
    obtain ⟨h1, h2, h3⟩ := hc σ hσ
    exact ⟨h1, h2, (h σ h1).mpr h3⟩

/-- Persistent Betti numbers depend only on the two sublevel sets. -/
theorem sublevelPersistentBetti_congr (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
    (p : ℕ) {a a' b b' : ℝ} (ha : ∀ σ ∈ K, f σ ≤ a ↔ f σ ≤ a')
    (hb : ∀ σ ∈ K, f σ ≤ b ↔ f σ ≤ b') :
    sublevelPersistentBetti 𝕜 K f p a b = sublevelPersistentBetti 𝕜 K f p a' b' := by
  unfold sublevelPersistentBetti sublevelCycles sublevelBoundaries
  rw [sublevelChains_congr 𝕜 K f p ha, sublevelChains_congr 𝕜 K f (p + 1) hb]

/-- The persistent Betti number as an integer difference of dimensions. -/
theorem sublevelPersistentBetti_cast (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
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
theorem exists_isSublevelDiagram_and_values (K : PreAbstractSimplicialComplex ι)
    (f : Finset ι → ℝ) (p : ℕ) :
    ∃ (n r : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ),
      IsSublevelDiagram 𝕜 K f p D e ∧ (∀ i, ∃ σ ∈ K, f σ = D.birth i) ∧
        (∀ i, ∃ σ ∈ K, f σ = D.death i) ∧ ∀ k, ∃ σ ∈ K, f σ = e k := by
  -- the critical values `c 0 < ⋯ < c (n - 1)`
  set T := (Finset.univ.filter (· ∈ K)).image f
  set n := T.card
  set c := T.orderEmbOfFin rfl
  set t0 : ℝ := -(1 + ∑ v ∈ T, |v|)
  have hc_mem : ∀ s, c s ∈ T := fun s ↦ T.orderEmbOfFin_mem rfl s
  have ht0 : ∀ s, t0 < c s := by
    intro s
    have h1 := Finset.single_le_sum (fun v _ ↦ abs_nonneg v) (hc_mem s)
    have h2 := neg_abs_le (c s)
    simp only [t0]
    linarith
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
    fun i j ↦ sublevelPersistentBetti_cast 𝕜 K f p _ _
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
    inf_le_inf_right _ (sublevelChains_mono 𝕜 K f p (htl_mono i i' h h'))
  have hB : ∀ j j', j ≤ j' → j' ≤ n →
      sublevelBoundaries 𝕜 K f p (tl j) ≤ sublevelBoundaries 𝕜 K f p (tl j') := fun j j' h h' ↦
    Submodule.map_mono (sublevelChains_mono 𝕜 K f (p + 1) (htl_mono j j' h h'))
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
    rw [sublevelPersistentBetti_congr 𝕜 K f p (hlevel a) (hlevel b)]
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

/-- GAPS 108.18, finite sublevel form: persistence diagrams of monotone sublevel filtrations of
finite simplicial complexes exist. This is the interval decomposition of the finite-type
persistence module `a ↦ H_p(K_a)`, read through its rank invariant. The proof uses only that the
chain spaces of `K_a` grow with `a`; the bars are read off from the rank function at the critical
values by inclusion–exclusion. -/
theorem exists_isSublevelDiagram (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
    (hf : IsMonotoneOnFaces K f) (p : ℕ) :
    ∃ (n r : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ), IsSublevelDiagram 𝕜 K f p D e := by
  obtain ⟨n, r, D, e, h, -⟩ := exists_isSublevelDiagram_and_values 𝕜 K f p
  exact ⟨n, r, D, e, h⟩

end Chains

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
to the diagonal. -/
def diagramWassersteinCost {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (M : DiagramMatching α β) (σ : κ ≃ κ') (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  (∑ i, (if h : ∃ j, M.relates i j then
      ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
    else ENNReal.ofReal ((D.death i - D.birth i) / 2)) ^ q) +
  (∑ j, (if ∃ i, M.relates i j then 0 else ENNReal.ofReal ((E.death j - E.birth j) / 2)) ^ q) +
  ∑ k, ENNReal.ofReal |e k - e' (σ k)| ^ q

/-- The `q`-Wasserstein distance between full persistence diagrams, `∞` when the numbers of
essential bars differ. -/
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

/-- The composite of two partial matchings. -/
def comp (M : DiagramMatching α β) (N : DiagramMatching β γ) : DiagramMatching α γ where
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
theorem cost_comp_le (N : DiagramMatching β γ) (F : FiniteDeathDiagram γ) :
    (M.comp N).cost D F ≤ M.cost D E + N.cost E F := by
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
  exact ENNReal.le_iInf_add_iInf fun M N ↦ (iInf_le _ (M.comp N)).trans (M.cost_comp_le D E N F)

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
theorem exists_le_lt_forall_lt_iff_le {γ : Type*} [Fintype γ] (w : γ → ℝ) {x z : ℝ}
    (hzx : z < x) : ∃ y, z ≤ y ∧ y < x ∧ ∀ c, w c < x ↔ w c ≤ y := by
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
    (h : ∀ c, (Finset.univ.filter fun a ↦ u a = c).card = (Finset.univ.filter fun b ↦ v b = c).card) :
    ∃ σ : α ≃ β, ∀ a, v (σ a) = u a := by
  refine ⟨Equiv.ofFiberEquiv fun c ↦ Fintype.equivOfCardEq ?_, Equiv.ofFiberEquiv_map _⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  exact h c

/-- Real families with the same distribution function have the same fibre cardinalities. -/
theorem card_filter_eq_of_card_filter_le_eq {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (u : κ → ℝ) (v : κ' → ℝ)
    (h : ∀ a, (Finset.univ.filter fun k ↦ u k ≤ a).card = (Finset.univ.filter fun k ↦ v k ≤ a).card)
    (x : ℝ) :
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
    set b := |a| + ∑ i, |D.death i| + ∑ i, |E.death i|
    have hDb : ∀ i, D.death i ≤ b := fun i ↦ by
      have h1 := Finset.single_le_sum (f := fun i ↦ |D.death i|) (fun i _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ i, |E.death i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      have := le_abs_self (D.death i)
      have := abs_nonneg a
      simp only [b]
      linarith
    have hEb : ∀ i, E.death i ≤ b := fun i ↦ by
      have h1 := Finset.single_le_sum (f := fun i ↦ |E.death i|) (fun i _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ i, |D.death i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      have := le_abs_self (E.death i)
      have := abs_nonneg a
      simp only [b]
      linarith
    have hab : a ≤ b := by
      have h2 : 0 ≤ ∑ i, |D.death i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      have h3 : 0 ≤ ∑ i, |E.death i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      have := le_abs_self a
      simp only [b]
      linarith
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
def leftTerm (i : α) : ℝ≥0∞ :=
  if h : ∃ j, M.relates i j then
    ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
  else ENNReal.ofReal ((D.death i - D.birth i) / 2)

/-- The distance of an unmatched right point to the diagonal, and zero for a matched one. -/
def rightTerm (j : β) : ℝ≥0∞ :=
  if ∃ i, M.relates i j then 0 else ENNReal.ofReal ((E.death j - E.birth j) / 2)

/-- The left term of a matched point is its distance to the partner. -/
theorem leftTerm_of_relates {i : α} {j : β} (h : M.relates i j) :
    M.leftTerm D E i = ENNReal.ofReal (max |D.birth i - E.birth j| |D.death i - E.death j|) := by
  have hex : ∃ j, M.relates i j := ⟨j, h⟩
  have hc : hex.choose = j := M.left_unique _ _ _ hex.choose_spec h
  rw [leftTerm, dite_eq_left hex, hc]

/-- The left term of an unmatched point is its distance to the diagonal. -/
theorem leftTerm_of_not {i : α} (h : ¬ ∃ j, M.relates i j) :
    M.leftTerm D E i = ENNReal.ofReal ((D.death i - D.birth i) / 2) := by
  rw [leftTerm, dite_eq_right h]

/-- The right term of a matched point is zero. -/
theorem rightTerm_of_relates {i : α} {j : β} (h : M.relates i j) : M.rightTerm E j = 0 := by
  rw [rightTerm, ite_eq_left ⟨i, h⟩]

/-- The right term of an unmatched point is its distance to the diagonal. -/
theorem rightTerm_of_not {j : β} (h : ¬ ∃ i, M.relates i j) :
    M.rightTerm E j = ENNReal.ofReal ((E.death j - E.birth j) / 2) := by
  rw [rightTerm, ite_eq_right h]

end DiagramMatching

/-- The `q`-Wasserstein cost as a sum of left terms, right terms, and essential terms. -/
theorem diagramWassersteinCost_eq {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (M : DiagramMatching α β) (σ : κ ≃ κ') (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) :
    diagramWassersteinCost q M σ D e E e' = ∑ i, M.leftTerm D E i ^ q +
      ∑ j, M.rightTerm E j ^ q + ∑ k, ENNReal.ofReal |e k - e' (σ k)| ^ q := by
  unfold diagramWassersteinCost DiagramMatching.leftTerm DiagramMatching.rightTerm
  congr 2 <;> exact Finset.sum_congr rfl fun j _ ↦ by congr 1; split_ifs <;> rfl

/-- Summing a function of the partner along a partial bijection. -/
theorem sum_dite_exists_eq {γ β : Type*} [Fintype γ] [Fintype β] (R : γ → β → Prop)
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
theorem dite_rpow_eq {p : Prop} [Decidable p] {q : ℝ} (hq : 0 < q) (x : p → ℝ≥0∞) :
    (if h : p then x h else 0) ^ q = if h : p then x h ^ q else 0 := by
  split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq]

/-- The cost of a composite matching, to the power `1/q`, is at most the sum of the costs of the
two matchings, to the power `1/q` (Minkowski's inequality). -/
theorem diagramWassersteinCost_comp_rpow_le {α β γ κ κ' κ'' : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype κ] [Fintype κ'] {q : ℝ} (hq : 1 ≤ q) (M : DiagramMatching α β)
    (N : DiagramMatching β γ) (σ : κ ≃ κ') (τ : κ' ≃ κ'') (D : FiniteDeathDiagram α)
    (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) (F : FiniteDeathDiagram γ)
    (e'' : κ'' → ℝ) :
    diagramWassersteinCost q (M.comp N) (σ.trans τ) D e F e'' ^ (1 / q) ≤
      diagramWassersteinCost q M σ D e E e' ^ (1 / q) +
        diagramWassersteinCost q N τ E e' F e'' ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  let T : α ⊕ γ ⊕ κ → ℝ≥0∞ := Sum.elim (fun i ↦ (M.comp N).leftTerm D F i)
    (Sum.elim (fun k ↦ (M.comp N).rightTerm F k) (fun k ↦ ENNReal.ofReal |e k - e'' (τ (σ k))|))
  let A : α ⊕ γ ⊕ κ → ℝ≥0∞ := Sum.elim (fun i ↦ M.leftTerm D E i)
    (Sum.elim (fun k ↦ if h : ∃ j, N.relates j k then M.rightTerm E h.choose else 0)
      (fun k ↦ ENNReal.ofReal |e k - e' (σ k)|))
  let B : α ⊕ γ ⊕ κ → ℝ≥0∞ :=
    Sum.elim (fun i ↦ if h : ∃ j, M.relates i j then N.leftTerm E F h.choose else 0)
      (Sum.elim (fun k ↦ if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftTerm E F h.choose)
        else N.rightTerm F k) (fun k ↦ ENNReal.ofReal |e' (σ k) - e'' (τ (σ k))|))
  have hcost : diagramWassersteinCost q (M.comp N) (σ.trans τ) D e F e'' = ∑ x, T x ^ q := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
    rfl
  have hTAB : ∀ x, T x ≤ A x + B x := by
    rintro (i | k | k)
    · change (M.comp N).leftTerm D F i ≤ M.leftTerm D E i +
        (if h : ∃ j, M.relates i j then N.leftTerm E F h.choose else 0)
      by_cases hi : ∃ j, M.relates i j
      · have hij : M.relates i hi.choose := hi.choose_spec
        rw [dite_eq_left hi, M.leftTerm_of_relates D E hij]
        by_cases hj : ∃ k, N.relates hi.choose k
        · obtain ⟨k, hjk⟩ := hj
          rw [(M.comp N).leftTerm_of_relates D F ⟨_, hij, hjk⟩, N.leftTerm_of_relates E F hjk,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_)
          · exact (abs_sub_le _ (E.birth hi.choose) _).trans
              (add_le_add (le_max_left _ _) (le_max_left _ _))
          · exact (abs_sub_le _ (E.death hi.choose) _).trans
              (add_le_add (le_max_right _ _) (le_max_right _ _))
        · have hnot : ¬ ∃ k, (M.comp N).relates i k := by
            rintro ⟨k, j', h1, h2⟩
            obtain rfl := M.left_unique _ _ _ hij h1
            exact hj ⟨k, h2⟩
          have hlt := E.birth_lt_death hi.choose
          rw [(M.comp N).leftTerm_of_not D F hnot, N.leftTerm_of_not E F hj,
            ← ENNReal.ofReal_add (by positivity) (by linarith)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := le_abs_self (D.death i - E.death hi.choose)
          have h2 := neg_abs_le (D.birth i - E.birth hi.choose)
          have h3 := le_max_left |D.birth i - E.birth hi.choose| |D.death i - E.death hi.choose|
          have h4 := le_max_right |D.birth i - E.birth hi.choose| |D.death i - E.death hi.choose|
          linarith
      · have hnot : ¬ ∃ k, (M.comp N).relates i k := by
          rintro ⟨k, j', h1, -⟩
          exact hi ⟨j', h1⟩
        rw [dite_eq_right hi, add_zero, (M.comp N).leftTerm_of_not D F hnot,
          M.leftTerm_of_not D E hi]
    · change (M.comp N).rightTerm F k ≤
        (if h : ∃ j, N.relates j k then M.rightTerm E h.choose else 0) +
        (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftTerm E F h.choose) else N.rightTerm F k)
      by_cases hk : ∃ j, N.relates j k
      · have hjk : N.relates hk.choose k := hk.choose_spec
        rw [dite_eq_left hk, dite_eq_left hk]
        by_cases hj : ∃ i, M.relates i hk.choose
        · obtain ⟨i, hij⟩ := hj
          rw [(M.comp N).rightTerm_of_relates F (i := i) ⟨_, hij, hjk⟩]
          exact bot_le
        · have hnot : ¬ ∃ i, (M.comp N).relates i k := by
            rintro ⟨i, j', h1, h2⟩
            obtain rfl := N.right_unique _ _ _ h2 hjk
            exact hj ⟨i, h1⟩
          have hlt := E.birth_lt_death hk.choose
          rw [ite_eq_right hj, M.rightTerm_of_not E hj, N.leftTerm_of_relates E F hjk,
            (M.comp N).rightTerm_of_not F hnot, ← ENNReal.ofReal_add (by linarith) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := neg_abs_le (E.death hk.choose - F.death k)
          have h2 := le_abs_self (E.birth hk.choose - F.birth k)
          have h3 := le_max_left |E.birth hk.choose - F.birth k| |E.death hk.choose - F.death k|
          have h4 := le_max_right |E.birth hk.choose - F.birth k| |E.death hk.choose - F.death k|
          linarith
      · have hnot : ¬ ∃ i, (M.comp N).relates i k := by
          rintro ⟨i, j', -, h2⟩
          exact hk ⟨j', h2⟩
        rw [dite_eq_right hk, dite_eq_right hk, zero_add, (M.comp N).rightTerm_of_not F hnot,
          N.rightTerm_of_not F hk]
    · change ENNReal.ofReal |e k - e'' (τ (σ k))| ≤ ENNReal.ofReal |e k - e' (σ k)| +
        ENNReal.ofReal |e' (σ k) - e'' (τ (σ k))|
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
  have hA : ∑ x, A x ^ q ≤ diagramWassersteinCost q M σ D e E e' := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc]
    refine add_le_add (add_le_add le_rfl ?_) le_rfl
    change ∑ k, (if h : ∃ j, N.relates j k then M.rightTerm E h.choose else 0) ^ q ≤ _
    simp_rw [dite_rpow_eq hq0]
    rw [sum_dite_exists_eq (fun k j ↦ N.relates j k) (fun k j j' h h' ↦ N.right_unique _ _ _ h h')
      (fun k k' j h h' ↦ N.left_unique _ _ _ h h') (fun j ↦ M.rightTerm E j ^ q)]
    exact Finset.sum_le_sum fun j _ ↦ by split_ifs <;> simp
  have hB : ∑ x, B x ^ q ≤ diagramWassersteinCost q N τ E e' F e'' := by
    rw [diagramWassersteinCost_eq, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h1 : ∑ i, B (.inl i) ^ q = ∑ j, (if ∃ i, M.relates i j then N.leftTerm E F j ^ q else 0) := by
      change ∑ i, (if h : ∃ j, M.relates i j then N.leftTerm E F h.choose else 0) ^ q = _
      simp_rw [dite_rpow_eq hq0]
      exact sum_dite_exists_eq M.relates (fun i j j' h h' ↦ M.left_unique _ _ _ h h')
        (fun i i' j h h' ↦ M.right_unique _ _ _ h h') (fun j ↦ N.leftTerm E F j ^ q)
    have h2 : ∑ k, B (.inr (.inl k)) ^ q ≤
        ∑ j, (if ∃ i, M.relates i j then 0 else N.leftTerm E F j ^ q) + ∑ k, N.rightTerm F k ^ q := by
      have hpt : ∀ k, B (.inr (.inl k)) ^ q ≤ (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftTerm E F h.choose ^ q) else 0) +
          N.rightTerm F k ^ q := by
        intro k
        change (if h : ∃ j, N.relates j k then
          (if ∃ i, M.relates i h.choose then 0 else N.leftTerm E F h.choose) else N.rightTerm F k) ^ q ≤ _
        split_ifs <;> simp [ENNReal.zero_rpow_of_pos hq0]
      refine (Finset.sum_le_sum fun k _ ↦ hpt k).trans ?_
      rw [Finset.sum_add_distrib]
      refine add_le_add ?_ le_rfl
      rw [sum_dite_exists_eq (fun k j ↦ N.relates j k) (fun k j j' h h' ↦ N.right_unique _ _ _ h h')
        (fun k k' j h h' ↦ N.left_unique _ _ _ h h')
        (fun j ↦ if ∃ i, M.relates i j then 0 else N.leftTerm E F j ^ q)]
      exact Finset.sum_le_sum fun j _ ↦ by split_ifs <;> simp
    have h3 : ∑ k, B (.inr (.inr k)) ^ q = ∑ j, ENNReal.ofReal |e' j - e'' (τ j)| ^ q :=
      Equiv.sum_comp σ (fun j ↦ ENNReal.ofReal |e' j - e'' (τ j)| ^ q)
    have h4 : ∑ j, (if ∃ i, M.relates i j then N.leftTerm E F j ^ q else 0) +
        ∑ j, (if ∃ i, M.relates i j then 0 else N.leftTerm E F j ^ q) =
        ∑ j, N.leftTerm E F j ^ q := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
    rw [h1, h3, ← h4]
    calc _ ≤ ∑ j, (if ∃ i, M.relates i j then N.leftTerm E F j ^ q else 0) +
          ((∑ j, (if ∃ i, M.relates i j then 0 else N.leftTerm E F j ^ q) +
            ∑ k, N.rightTerm F k ^ q) + ∑ j, ENNReal.ofReal |e' j - e'' (τ j)| ^ q) :=
          add_le_add le_rfl (add_le_add h2 le_rfl)
      _ = _ := by ring
  calc diagramWassersteinCost q (M.comp N) (σ.trans τ) D e F e'' ^ (1 / q)
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
  exact (iInf_le_of_le (M.comp N) (iInf_le _ (σ.trans τ))).trans
    (diagramWassersteinCost_comp_rpow_le hq M N σ τ D e E e' F e'')

end Distances

section Stability

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

omit [Fintype ι] [LinearOrder ι] in
/-- Sublevel chains of two functions agree when the sublevel sets agree on `K`. -/
theorem sublevelChains_congr_fun (K : PreAbstractSimplicialComplex ι) {f h : Finset ι → ℝ}
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
theorem sublevelPersistentBetti_congr_fun (K : PreAbstractSimplicialComplex ι)
    {f h : Finset ι → ℝ} (p : ℕ) {a a' b b' : ℝ} (ha : ∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a')
    (hb : ∀ σ ∈ K, f σ ≤ b ↔ h σ ≤ b') :
    sublevelPersistentBetti 𝕜 K f p a b = sublevelPersistentBetti 𝕜 K h p a' b' := by
  unfold sublevelPersistentBetti sublevelCycles sublevelBoundaries
  rw [sublevelChains_congr_fun 𝕜 K p ha, sublevelChains_congr_fun 𝕜 K (p + 1) hb]

omit [LinearOrder ι] in
/-- If `f` is ordered by `h` on `K` (`h σ ≤ h τ → f σ ≤ f τ`), every sublevel set of `f` on `K`
is a sublevel set of `h`. -/
theorem exists_forall_le_iff_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f h : Finset ι → ℝ} (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ) (a : ℝ) :
    ∃ a', ∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a' := by
  set S := Finset.univ.filter fun σ ↦ σ ∈ K ∧ f σ ≤ a
  rcases S.eq_empty_or_nonempty with hS | hS
  · set t0 : ℝ := -(1 + ∑ σ ∈ Finset.univ.filter (· ∈ K), |h σ|)
    refine ⟨t0, fun σ hσ ↦ ⟨fun hσa ↦ ?_, fun hσt ↦ ?_⟩⟩
    · have : σ ∈ S := by simp [S, hσ, hσa]
      simp [hS] at this
    · have h1 := Finset.single_le_sum (f := fun σ ↦ |h σ|) (fun σ _ ↦ abs_nonneg _)
        (show σ ∈ Finset.univ.filter (· ∈ K) by simpa using hσ)
      have h2 := neg_abs_le (h σ)
      simp only [t0] at hσt
      linarith
  · obtain ⟨σ0, hσ0, hmax⟩ := S.exists_max_image h hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hσ0
    refine ⟨h σ0, fun σ hσ ↦ ⟨fun hσa ↦ hmax σ (by simp [S, hσ, hσa]), fun hσt ↦ ?_⟩⟩
    exact (hfh σ hσ σ0 hσ0.1 hσt).trans hσ0.2

omit [LinearOrder ι] in
/-- Two-level version of `exists_forall_le_iff_le_of_ordered`, with ordered levels. -/
theorem exists_le_forall_le_iff_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f h : Finset ι → ℝ} (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ a' b', a' ≤ b' ∧ (∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a') ∧ ∀ σ ∈ K, f σ ≤ b ↔ h σ ≤ b' := by
  obtain ⟨a', ha'⟩ := exists_forall_le_iff_le_of_ordered K hfh a
  obtain ⟨b', hb'⟩ := exists_forall_le_iff_le_of_ordered K hfh b
  refine ⟨a', max a' b', le_max_left _ _, ha', fun σ hσ ↦ ?_⟩
  rw [le_max_iff, ← ha' σ hσ, ← hb' σ hσ]
  exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun h ↦ h.trans hab) id⟩

/-- The finite part of the relabelling of a diagram along simplices `sb`, `sd`: the bar `i`
becomes `[f (sb i), f (sd i))`, and bars of length zero are discarded. -/
def relabelDiagram {α : Type*} (f : Finset ι → ℝ) (sb sd : α → Finset ι) :
    FiniteDeathDiagram {i : α // f (sb i) < f (sd i)} where
  birth i := f (sb i.1)
  death i := f (sd i.1)
  birth_lt_death i := i.2

/-- Relabelling: let `f` be ordered by `h` on `K`. If the bars of a diagram of `h` have endpoints
`h (sb i)`, `h (sd i)` and `h (se k)` at simplices of `K`, then the relabelled bars
`[f (sb i), f (sd i))` (without those of length zero) and `[f (se k), ∞)` form a diagram of `f`. -/
theorem IsSublevelDiagram.relabel {K : PreAbstractSimplicialComplex ι} {f h : Finset ι → ℝ}
    {p : ℕ} {α κ : Type*} [Fintype α] [Fintype κ] {D : FiniteDeathDiagram α} {e : κ → ℝ}
    (hD : IsSublevelDiagram 𝕜 K h p D e) (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ)
    (sb sd : α → Finset ι) (se : κ → Finset ι) (hsbK : ∀ i, sb i ∈ K)
    (hsb : ∀ i, h (sb i) = D.birth i) (hsdK : ∀ i, sd i ∈ K) (hsd : ∀ i, h (sd i) = D.death i)
    (hseK : ∀ k, se k ∈ K) (hse : ∀ k, h (se k) = e k) :
    IsSublevelDiagram 𝕜 K f p (relabelDiagram f sb sd) (fun k ↦ f (se k)) := by
  intro a b hab
  obtain ⟨a', b', hab', ha', hb'⟩ := exists_le_forall_le_iff_le_of_ordered K hfh hab
  rw [sublevelPersistentBetti_congr_fun 𝕜 K p ha' hb', hD a' b' hab']
  congr 1
  · symm
    refine Finset.card_bij (fun i _ ↦ i.1) (fun i hi ↦ ?_) (fun i _ j _ hij ↦ Subtype.ext hij)
      (fun i hi ↦ ?_)
    · have hi' := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change f (sb i.1) ≤ a ∧ b < f (sd i.1) at hi'
      rw [← hsb, ← hsd, ← ha' _ (hsbK _), ← not_le, ← hb' _ (hsdK _), not_le]
      exact hi'
    · have hi' := (Finset.mem_filter.mp hi).2
      rw [← hsb, ← hsd, ← ha' _ (hsbK _), ← not_le, ← hb' _ (hsdK _), not_le] at hi'
      exact ⟨⟨i, lt_of_le_of_lt hi'.1 (lt_of_le_of_lt hab hi'.2)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩, rfl⟩
  · refine Finset.card_bij (fun k _ ↦ k) (fun k hk ↦ ?_) (fun _ _ _ _ h ↦ h) (fun k hk ↦ ⟨k, ?_, rfl⟩)
    · have hk' := (Finset.mem_filter.mp hk).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hse, ← ha' _ (hseK _)] at hk'
      exact hk'
    · have hk' := (Finset.mem_filter.mp hk).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hse, ← ha' _ (hseK _)]
      exact hk'

/-- Bottleneck stability when the two functions are ordered by a common monotone function `h`.
The diagrams of `f` and `g` are both relabellings of one diagram of `h`, and matching the bars
with the same label costs at most `δ`. -/
theorem fullBottleneckEDist_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f g h : Finset ι → ℝ} (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ)
    (hgh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → g σ ≤ g τ) (p : ℕ) {δ : ℝ}
    (hδ : ∀ σ ∈ K, |f σ - g σ| ≤ δ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    {D : FiniteDeathDiagram α} {e : κ → ℝ} {E : FiniteDeathDiagram β} {e' : κ' → ℝ}
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  obtain ⟨n, r, Dh, eh, hDh, hb, hd, he⟩ := exists_isSublevelDiagram_and_values 𝕜 K h p
  choose sb hsbK hsb using hb
  choose sd hsdK hsd using hd
  choose se hseK hse using he
  have hDf := hDh.relabel 𝕜 hfh sb sd se hsbK hsb hsdK hsd hseK hse
  have hDg := hDh.relabel 𝕜 hgh sb sd se hsbK hsb hsdK hsd hseK hse
  have h1 : fullBottleneckEDist D e (relabelDiagram f sb sd) (fun k ↦ f (se k)) = 0 :=
    fullBottleneckEDist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hD a b hab, ← hDf a b hab]
  have h3 : fullBottleneckEDist (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e' = 0 :=
    fullBottleneckEDist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hDg a b hab, ← hE a b hab]
  have hle : ∀ i, g (sb i) ≤ g (sd i) := fun i ↦
    hgh _ (hsbK i) _ (hsdK i) (by rw [hsb, hsd]; exact (Dh.birth_lt_death i).le)
  have hle' : ∀ i, f (sb i) ≤ f (sd i) := fun i ↦
    hfh _ (hsbK i) _ (hsdK i) (by rw [hsb, hsd]; exact (Dh.birth_lt_death i).le)
  have h2 : fullBottleneckEDist (relabelDiagram f sb sd) (fun k ↦ f (se k))
      (relabelDiagram g sb sd) (fun k ↦ g (se k)) ≤ ENNReal.ofReal δ := by
    let M : DiagramMatching {i // f (sb i) < f (sd i)} {i // g (sb i) < g (sd i)} :=
      { relates := fun x y ↦ x.1 = y.1
        left_unique := fun x y z hy hz ↦ Subtype.ext (hy.symm.trans hz)
        right_unique := fun x y z hx hy ↦ Subtype.ext (hx.trans hy.symm) }
    refine max_le ((iInf_le _ M).trans (M.cost_le _ _ ?_ ?_ ?_)) ?_
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      change i = j at hij
      subst hij
      exact ENNReal.ofReal_le_ofReal (max_le (hδ _ (hsbK i)) (hδ _ (hsdK i)))
    · rintro ⟨i, hi⟩ hx
      have hgi : ¬ g (sb i) < g (sd i) := fun hlt ↦ hx ⟨⟨i, hlt⟩, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := abs_le.mp (hδ _ (hsbK i))
      have h2 := abs_le.mp (hδ _ (hsdK i))
      simp only [relabelDiagram]
      linarith [not_lt.mp hgi]
    · rintro ⟨i, hi⟩ hx
      have hfi : ¬ f (sb i) < f (sd i) := fun hlt ↦ hx ⟨⟨i, hlt⟩, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := abs_le.mp (hδ _ (hsbK i))
      have h2 := abs_le.mp (hδ _ (hsdK i))
      simp only [relabelDiagram]
      linarith [not_lt.mp hfi]
    · refine (iInf_le _ (Equiv.refl _)).trans (iSup_le fun k ↦ ?_)
      exact ENNReal.ofReal_le_ofReal (hδ _ (hseK k))
  calc fullBottleneckEDist D e E e'
      ≤ fullBottleneckEDist D e (relabelDiagram f sb sd) (fun k ↦ f (se k)) +
          fullBottleneckEDist (relabelDiagram f sb sd) (fun k ↦ f (se k)) E e' :=
        fullBottleneckEDist_triangle _ _ _ _ _ _
    _ ≤ 0 + (fullBottleneckEDist (relabelDiagram f sb sd) (fun k ↦ f (se k))
          (relabelDiagram g sb sd) (fun k ↦ g (se k)) +
        fullBottleneckEDist (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e') := by
        rw [h1]
        exact add_le_add le_rfl (fullBottleneckEDist_triangle _ _ _ _ _ _)
    _ ≤ ENNReal.ofReal δ := by rw [h3, zero_add, add_zero]; exact h2


omit [LinearOrder ι] in
/-- Pairs of simplices of `K` ordered oppositely by `f` and `g`. -/
def discordantPairs (K : PreAbstractSimplicialComplex ι) (f g : Finset ι → ℝ) :
    Finset (Finset ι × Finset ι) :=
  Finset.univ.filter fun q ↦ q.1 ∈ K ∧ q.2 ∈ K ∧ f q.1 < f q.2 ∧ g q.2 < g q.1

omit [Fintype ι] [LinearOrder ι] in
/-- A convex combination of functions monotone along faces is monotone along faces. -/
theorem IsMonotoneOnFaces.convexComb {K : PreAbstractSimplicialComplex ι} {f g : Finset ι → ℝ}
    (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : IsMonotoneOnFaces K fun ρ ↦ (1 - t) * f ρ + t * g ρ := by
  intro τ σ hσ hτ hτσ
  have h1 := hf τ σ hσ hτ hτσ
  have h2 := hg τ σ hσ hτ hτσ
  have := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht1)
  have := mul_le_mul_of_nonneg_left h2 ht0
  linarith

/-- Bottleneck stability for `Fin`-indexed diagrams, by strong induction on the number of
discordant pairs: without discordant pairs, `f` and `g` are both ordered by `f + g`; otherwise an
intermediate convex combination `m` resolves one discordant pair and has fewer discordant pairs with
both `f` and `g`. -/
theorem fullBottleneckEDist_le_of_card_discordantPairs_le (K : PreAbstractSimplicialComplex ι)
    (p N : ℕ) : ∀ f g : Finset ι → ℝ, IsMonotoneOnFaces K f → IsMonotoneOnFaces K g →
      (discordantPairs K f g).card ≤ N → ∀ δ : ℝ, (∀ σ ∈ K, |f σ - g σ| ≤ δ) →
      ∀ (n r n' r' : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ)
        (E : FiniteDeathDiagram (Fin n')) (e' : Fin r' → ℝ),
        IsSublevelDiagram 𝕜 K f p D e → IsSublevelDiagram 𝕜 K g p E e' →
        fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f g hf hg hN δ hδ n r n' r' D e E e' hD hE
  rcases (discordantPairs K f g).eq_empty_or_nonempty with h0 | ⟨⟨σ, τ⟩, hq⟩
  · have hnot : ∀ σ ∈ K, ∀ τ ∈ K, ¬ (f σ < f τ ∧ g τ < g σ) := by
      intro σ hσ τ hτ hc
      have : (σ, τ) ∈ discordantPairs K f g := by
        simp [discordantPairs, hσ, hτ, hc.1, hc.2]
      simp [h0] at this
    refine fullBottleneckEDist_le_of_ordered 𝕜 K (h := fun ρ ↦ f ρ + g ρ) ?_ ?_ p hδ hD hE
    · intro σ hσ τ hτ hle
      by_contra hc
      have := hnot τ hτ σ hσ
      push Not at hc this
      linarith [this hc]
    · intro σ hσ τ hτ hle
      by_contra hc
      have := hnot σ hσ τ hτ
      push Not at hc this
      have h' : f τ ≤ f σ := by
        by_contra h''
        exact absurd (this (not_le.mp h'')) (not_le.mpr hc)
      linarith
  · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hσ, hτ, hf0, hg0⟩ := hq
    set d0 := f σ - f τ
    set d1 := g σ - g τ
    have hd0 : d0 < 0 := by simp only [d0]; linarith
    have hd1 : 0 < d1 := by simp only [d1]; linarith
    set t := d0 / (d0 - d1)
    have ht0 : 0 < t := div_pos_of_neg_of_neg hd0 (by linarith)
    have ht1 : t < 1 := by
      rw [div_lt_one_of_neg (by linarith)]
      linarith
    have hzero : (1 - t) * d0 + t * d1 = 0 := by
      have hne : d0 - d1 ≠ 0 := (show d0 - d1 < 0 by linarith).ne
      simp only [t]
      field_simp
      ring
    set m : Finset ι → ℝ := fun ρ ↦ (1 - t) * f ρ + t * g ρ
    have hm : IsMonotoneOnFaces K m := hf.convexComb hg ht0.le ht1.le
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ σ hσ)
    have hst : (σ, τ) ∈ discordantPairs K f g := by
      simp [discordantPairs, hσ, hτ, hf0, hg0]
    have hmστ : m σ = m τ := by
      simp only [m]
      simp only [d0, d1] at hzero
      linarith
    -- the discordant pairs of `f, m` and of `m, g` are discordant pairs of `f, g`
    have hfm : discordantPairs K f m ⊂ discordantPairs K f g := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq ↦ ?_, fun heq ↦ ?_⟩
      · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hq
        refine ⟨h1, h2, h3, ?_⟩
        by_contra hc
        push Not at hc
        simp only [m] at h4
        have := mul_le_mul_of_nonneg_left hc ht0.le
        have := mul_lt_mul_of_pos_left h3 (sub_pos.mpr ht1)
        linarith
      · rw [← heq] at hst
        simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hst
        exact absurd hst.2.2.2 (by rw [hmστ]; exact lt_irrefl _)
    have hmg : discordantPairs K m g ⊂ discordantPairs K f g := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq ↦ ?_, fun heq ↦ ?_⟩
      · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hq
        refine ⟨h1, h2, ?_, h4⟩
        by_contra hc
        push Not at hc
        simp only [m] at h3
        have := mul_le_mul_of_nonneg_left hc (sub_pos.mpr ht1).le
        have := mul_lt_mul_of_pos_left h4 ht0
        linarith
      · rw [← heq] at hst
        simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hst
        exact absurd hst.2.2.1 (by rw [hmστ]; exact lt_irrefl _)
    have hδfm : ∀ ρ ∈ K, |f ρ - m ρ| ≤ t * δ := by
      intro ρ hρ
      have : f ρ - m ρ = t * (f ρ - g ρ) := by simp only [m]; ring
      rw [this, abs_mul, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left (hδ ρ hρ) ht0.le
    have hδmg : ∀ ρ ∈ K, |m ρ - g ρ| ≤ (1 - t) * δ := by
      intro ρ hρ
      have : m ρ - g ρ = (1 - t) * (f ρ - g ρ) := by simp only [m]; ring
      rw [this, abs_mul, abs_of_pos (sub_pos.mpr ht1)]
      exact mul_le_mul_of_nonneg_left (hδ ρ hρ) (sub_pos.mpr ht1).le
    obtain ⟨n0, r0, Dm, em, hDm⟩ := exists_isSublevelDiagram_and_values 𝕜 K m p
    have hlt1 := (Finset.card_lt_card hfm).trans_le hN
    have hlt2 := (Finset.card_lt_card hmg).trans_le hN
    calc fullBottleneckEDist D e E e'
        ≤ fullBottleneckEDist D e Dm em + fullBottleneckEDist Dm em E e' :=
          fullBottleneckEDist_triangle _ _ _ _ _ _
      _ ≤ ENNReal.ofReal (t * δ) + ENNReal.ofReal ((1 - t) * δ) :=
          add_le_add (ih _ hlt1 f m hf hm le_rfl _ hδfm _ _ _ _ D e Dm em hD hDm.1)
            (ih _ hlt2 m g hm hg le_rfl _ hδmg _ _ _ _ Dm em E e' hDm.1 hE)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (mul_nonneg ht0.le hδ0)
            (mul_nonneg (sub_pos.mpr ht1).le hδ0)]
          ring_nf

/-- GAPS 108.19, simplicial form: for monotone functions `f, g` on the simplices of a finite
simplicial complex, the degree-`p` persistence diagrams of the sublevel filtrations (finite and
essential parts) are within bottleneck distance `‖f - g‖_∞ = max_{σ ∈ K} |f σ - g σ|`. The
statement for tame functions on triangulable spaces, with singular homology of sublevel sets,
is not formalized; for piecewise-linear functions it reduces to this case. -/
theorem fullBottleneckEDist_le_of_isSublevelDiagram (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (δ : ℝ) (hδ : ∀ σ ∈ K, |f σ - g σ| ≤ δ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  obtain ⟨n, r, D0, e0, hD0, -⟩ := exists_isSublevelDiagram_and_values 𝕜 K f p
  obtain ⟨n', r', E0, e0', hE0, -⟩ := exists_isSublevelDiagram_and_values 𝕜 K g p
  have h1 : fullBottleneckEDist D e D0 e0 = 0 :=
    fullBottleneckEDist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hD a b hab, ← hD0 a b hab]
  have h3 : fullBottleneckEDist E0 e0' E e' = 0 :=
    fullBottleneckEDist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hE0 a b hab, ← hE a b hab]
  have h2 := fullBottleneckEDist_le_of_card_discordantPairs_le 𝕜 K p _ f g hf hg le_rfl δ hδ
    n r n' r' D0 e0 E0 e0' hD0 hE0
  calc fullBottleneckEDist D e E e'
      ≤ fullBottleneckEDist D e D0 e0 + fullBottleneckEDist D0 e0 E e' :=
        fullBottleneckEDist_triangle _ _ _ _ _ _
    _ ≤ 0 + (fullBottleneckEDist D0 e0 E0 e0' + fullBottleneckEDist E0 e0' E e') := by
        rw [h1]
        exact add_le_add le_rfl (fullBottleneckEDist_triangle _ _ _ _ _ _)
    _ ≤ ENNReal.ofReal δ := by rw [h3, zero_add, add_zero]; exact h2

omit [LinearOrder ι] in
/-- For `h` injective on `K`, passing from the level just below `h σ` to `h σ` adds at most the
simplex `σ`, and only in dimension `σ.card - 1`; so the image of the chains under any linear map
grows in dimension by at most one, and not at all in other dimensions. -/
theorem finrank_map_sublevelChains_le (K : PreAbstractSimplicialComplex ι) {h : Finset ι → ℝ}
    (hinj : ∀ σ ∈ K, ∀ τ ∈ K, h σ = h τ → σ = τ) (φ : (Finset ι → 𝕜) →ₗ[𝕜] (Finset ι → 𝕜))
    (q : ℕ) {σ : Finset ι} (hσ : σ ∈ K) {x : ℝ} (hx : ∀ τ ∈ K, h τ < h σ ↔ h τ ≤ x) :
    finrank 𝕜 ((sublevelChains 𝕜 K h q (h σ)).map φ) ≤
      finrank 𝕜 ((sublevelChains 𝕜 K h q x).map φ) + if σ.card = q + 1 then 1 else 0 := by
  have hlt : ∀ c ∈ sublevelChains 𝕜 K h q (h σ), ∀ τ, τ ≠ σ → c τ ≠ 0 →
      τ ∈ K ∧ τ.card = q + 1 ∧ h τ ≤ x := by
    intro c hc τ hτσ hτ
    obtain ⟨h1, h2, h3⟩ := hc τ hτ
    refine ⟨h1, h2, (hx τ h1).mp (lt_of_le_of_ne h3 fun heq ↦ hτσ (hinj _ h1 _ hσ heq))⟩
  split_ifs with hcard
  · have hle : sublevelChains 𝕜 K h q (h σ) ≤
        sublevelChains 𝕜 K h q x ⊔ Submodule.span 𝕜 {Pi.single σ 1} := by
      intro c hc
      refine Submodule.mem_sup.mpr ⟨c - c σ • Pi.single σ 1, ?_, c σ • Pi.single σ 1,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), by simp⟩
      intro τ hτ
      by_cases hτσ : τ = σ
      · subst hτσ
        simp at hτ
      · refine hlt c hc τ hτσ ?_
        simpa [Pi.single_apply, hτσ] using hτ
    have := Submodule.finrank_mono (Submodule.map_mono (f := φ) hle)
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton] at this
    refine this.trans ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_)
    refine add_le_add le_rfl ((finrank_span_le_card ({φ (Pi.single σ 1)} : Set _)).trans ?_)
    simp
  · have hle : sublevelChains 𝕜 K h q (h σ) ≤ sublevelChains 𝕜 K h q x := by
      intro c hc τ hτ
      by_cases hτσ : τ = σ
      · subst hτσ
        exact absurd (hc τ hτ).2.1 hcard
      · exact hlt c hc τ hτσ hτ
    simpa using Submodule.finrank_mono (Submodule.map_mono (f := φ) hle)

/-- Sublevel cycles grow with the level. -/
theorem sublevelCycles_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {a a' : ℝ} (h : a ≤ a') : sublevelCycles 𝕜 K f p a ≤ sublevelCycles 𝕜 K f p a' :=
  inf_le_inf_right _ (sublevelChains_mono 𝕜 K f p h)

/-- Boundaries grow with the level. -/
theorem sublevelBoundaries_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {b b' : ℝ} (h : b ≤ b') : sublevelBoundaries 𝕜 K f p b ≤ sublevelBoundaries 𝕜 K f p b' :=
  Submodule.map_mono (sublevelChains_mono 𝕜 K f (p + 1) h)

/-- For `h` injective on `K`, a diagram of `h` in degree `p` has at most one bar (finite or
essential) born at `h σ`, and none unless `σ` is a `p`-simplex. -/
theorem card_birth_add_card_essential_le (K : PreAbstractSimplicialComplex ι)
    {h : Finset ι → ℝ} (hinj : ∀ σ ∈ K, ∀ τ ∈ K, h σ = h τ → σ = τ) {p : ℕ} {α κ : Type*}
    [Fintype α] [Fintype κ] {D : FiniteDeathDiagram α} {e : κ → ℝ}
    (hD : IsSublevelDiagram 𝕜 K h p D e) {σ : Finset ι} (hσ : σ ∈ K) :
    (Finset.univ.filter fun i ↦ D.birth i = h σ).card +
        (Finset.univ.filter fun k ↦ e k = h σ).card ≤ if σ.card = p + 1 then 1 else 0 := by
  set x := h σ with hxdef
  obtain ⟨x', -, hx'x, hx'⟩ := exists_le_lt_forall_lt_iff_le
    (Sum.elim (Sum.elim D.birth e) (fun τ : {τ // τ ∈ K} ↦ h τ.1)) (sub_one_lt x)
  have hK : ∀ τ ∈ K, h τ < x ↔ h τ ≤ x' := fun τ hτ ↦ by simpa using hx' (.inr ⟨τ, hτ⟩)
  have hb : ∀ i, D.birth i < x ↔ D.birth i ≤ x' := fun i ↦ by simpa using hx' (.inl (.inl i))
  have he : ∀ k, e k < x ↔ e k ≤ x' := fun k ↦ by simpa using hx' (.inl (.inr k))
  have h1 := card_filter_eq_add_of_iff (P := fun i ↦ D.birth i ≤ x ∧ x < D.death i)
    (Q := fun i ↦ D.birth i ≤ x' ∧ x < D.death i) (S := fun i ↦ D.birth i = x)
    (fun i ↦ ⟨fun ⟨h1, h2⟩ ↦ h1.lt_or_eq.elim (fun h ↦ Or.inl ⟨(hb i).mp h, h2⟩) Or.inr,
      fun h ↦ h.elim (fun ⟨h1, h2⟩ ↦ ⟨((hb i).mpr h1).le, h2⟩)
        (fun h ↦ ⟨h.le, h ▸ D.birth_lt_death i⟩)⟩)
    (fun i hQ hS ↦ by have := (hb i).mpr hQ.1; rw [hS] at this; exact lt_irrefl _ this)
  have h2 := card_filter_eq_add_of_iff (P := fun k ↦ e k ≤ x) (Q := fun k ↦ e k ≤ x')
    (S := fun k ↦ e k = x)
    (fun k ↦ ⟨fun h ↦ h.lt_or_eq.elim (fun h ↦ Or.inl ((he k).mp h)) Or.inr,
      fun h ↦ h.elim (fun h ↦ ((he k).mpr h).le) (fun h ↦ h.le)⟩)
    (fun k hQ hS ↦ by have := (he k).mpr hQ; rw [hS] at this; exact lt_irrefl _ this)
  have hPB1 := hD x x le_rfl
  have hPB2 := hD x' x hx'x.le
  have hc1 := sublevelPersistentBetti_cast 𝕜 K h p x x
  have hc2 := sublevelPersistentBetti_cast 𝕜 K h p x' x
  have hZ := sublevelCycles_mono 𝕜 K h p hx'x.le
  have I1 := finrank_add_finrank_inf_le (U := sublevelBoundaries 𝕜 K h p x) hZ
  have I1' := Submodule.finrank_mono (inf_le_inf_right (sublevelBoundaries 𝕜 K h p x) hZ)
  have I2 := finrank_add_finrank_inf_le (U := LinearMap.ker (simplicialBoundary 𝕜))
    (sublevelChains_mono 𝕜 K h p hx'x.le)
  have I3 := finrank_map_sublevelChains_le 𝕜 K hinj LinearMap.id p hσ hK
  rw [← hxdef] at I3
  have e1 : (sublevelChains 𝕜 K h p x).map LinearMap.id = sublevelChains 𝕜 K h p x :=
    Submodule.map_id _
  have e2 : (sublevelChains 𝕜 K h p x').map LinearMap.id = sublevelChains 𝕜 K h p x' :=
    Submodule.map_id _
  rw [e1, e2] at I3
  unfold sublevelCycles at hc1 hc2 hZ I1 I1'
  split_ifs at I3 ⊢ <;> omega

/-- For `h` injective on `K`, a diagram of `h` in degree `p` has at most one finite bar dying at
`h σ`, and none unless `σ` is a `(p + 1)`-simplex. -/
theorem card_death_le (K : PreAbstractSimplicialComplex ι)
    {h : Finset ι → ℝ} (hinj : ∀ σ ∈ K, ∀ τ ∈ K, h σ = h τ → σ = τ) {p : ℕ} {α κ : Type*}
    [Fintype α] [Fintype κ] {D : FiniteDeathDiagram α} {e : κ → ℝ}
    (hD : IsSublevelDiagram 𝕜 K h p D e) {σ : Finset ι} (hσ : σ ∈ K) :
    (Finset.univ.filter fun i ↦ D.death i = h σ).card ≤ if σ.card = p + 2 then 1 else 0 := by
  set y := h σ with hydef
  obtain ⟨y', -, hy'y, hy'⟩ := exists_le_lt_forall_lt_iff_le
    (Sum.elim (Sum.elim D.birth D.death) (fun τ : {τ // τ ∈ K} ↦ h τ.1)) (sub_one_lt y)
  have hK : ∀ τ ∈ K, h τ < y ↔ h τ ≤ y' := fun τ hτ ↦ by simpa using hy' (.inr ⟨τ, hτ⟩)
  have hb : ∀ i, D.birth i < y ↔ D.birth i ≤ y' := fun i ↦ by simpa using hy' (.inl (.inl i))
  have hd : ∀ i, D.death i < y ↔ D.death i ≤ y' := fun i ↦ by simpa using hy' (.inl (.inr i))
  have h1 := card_filter_eq_add_of_iff (P := fun i ↦ D.birth i ≤ y' ∧ y' < D.death i)
    (Q := fun i ↦ D.birth i ≤ y' ∧ y < D.death i) (S := fun i ↦ D.death i = y)
    (fun i ↦ by
      constructor
      · rintro ⟨h1, h2⟩
        have : y ≤ D.death i := by
          by_contra hc
          exact absurd ((hd i).mp (not_le.mp hc)) (not_le.mpr h2)
        rcases this.lt_or_eq with h3 | h3
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr h3.symm
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨h1, lt_trans hy'y h2⟩
        · refine ⟨(hb i).mp (h ▸ D.birth_lt_death i), h ▸ hy'y⟩)
    (fun i hQ hS ↦ by rw [hS] at hQ; exact lt_irrefl _ hQ.2)
  have hPB1 := hD y' y' le_rfl
  have hPB2 := hD y' y hy'y.le
  have hc1 := sublevelPersistentBetti_cast 𝕜 K h p y' y'
  have hc2 := sublevelPersistentBetti_cast 𝕜 K h p y' y
  have hB := sublevelBoundaries_mono 𝕜 K h p hy'y.le
  have I1 := finrank_add_finrank_inf_le (U := sublevelCycles 𝕜 K h p y') hB
  rw [inf_comm (sublevelBoundaries 𝕜 K h p y), inf_comm (sublevelBoundaries 𝕜 K h p y')] at I1
  have I3 := finrank_map_sublevelChains_le 𝕜 K hinj (simplicialBoundary 𝕜) (p + 1) hσ hK
  rw [← hydef] at I3
  unfold sublevelBoundaries at hc1 hc2 hB I1
  split_ifs at I3 ⊢ <;> omega

/-- Diagrams related by bijections preserving all points are at `q`-Wasserstein distance zero. -/
theorem diagramWassersteinEDist_eq_zero_of_equiv {α β κ κ' : Type*} [Fintype α] [Fintype β]
    [Fintype κ] {q : ℝ} (hq : 0 < q) {D : FiniteDeathDiagram α} {e : κ → ℝ}
    {E : FiniteDeathDiagram β} {e' : κ' → ℝ} (σ : α ≃ β)
    (hσ : ∀ i, E.birth (σ i) = D.birth i ∧ E.death (σ i) = D.death i) (τ : κ ≃ κ')
    (hτ : ∀ k, e' (τ k) = e k) : diagramWassersteinEDist q D e E e' = 0 := by
  let M : DiagramMatching α β :=
    { relates := fun i j ↦ j = σ i
      left_unique := fun i j k hj hk ↦ hj.trans hk.symm
      right_unique := fun i j k hi hj ↦ σ.injective (hi.symm.trans hj) }
  refine le_antisymm ((iInf_le_of_le M (iInf_le _ τ)).trans (le_of_eq ?_)) bot_le
  rw [diagramWassersteinCost_eq]
  have h1 : ∀ i, M.leftTerm D E i = 0 := fun i ↦ by
    rw [M.leftTerm_of_relates D E (j := σ i) rfl, (hσ i).1, (hσ i).2]
    simp
  have h2 : ∀ j, M.rightTerm E j = 0 := fun j ↦
    M.rightTerm_of_relates E (i := σ.symm j) (by simp [M])
  simp [h1, h2, hτ, ENNReal.zero_rpow_of_pos hq, hq]

/-- Diagrams of the same function are at `q`-Wasserstein distance zero. -/
theorem diagramWassersteinEDist_eq_zero_of_isSublevelDiagram {K : PreAbstractSimplicialComplex ι}
    {f : Finset ι → ℝ} {p : ℕ} {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [Fintype κ'] {q : ℝ} (hq : 0 < q) {D : FiniteDeathDiagram α} {e : κ → ℝ}
    {E : FiniteDeathDiagram β} {e' : κ' → ℝ} (hD : IsSublevelDiagram 𝕜 K f p D e)
    (hE : IsSublevelDiagram 𝕜 K f p E e') : diagramWassersteinEDist q D e E e' = 0 := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_equiv_of_card_eq D e E e' fun a b hab ↦ by
    rw [← hD a b hab, ← hE a b hab]
  exact diagramWassersteinEDist_eq_zero_of_equiv hq σ hσ τ hτ

/-- `q`-Wasserstein stability when the two functions are ordered by a common function `h` that is
injective on `K`. The bars of the diagram of `h` have distinct endpoint simplices, and matching
the relabelled bars with the same label costs at most `∑_{σ ∈ K} |f σ - g σ|^q`. -/
theorem diagramWassersteinEDist_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f g h : Finset ι → ℝ} (hinj : ∀ σ ∈ K, ∀ τ ∈ K, h σ = h τ → σ = τ)
    (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ)
    (hgh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → g σ ≤ g τ) (p : ℕ) {q : ℝ} (hq : 1 ≤ q)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    {D : FiniteDeathDiagram α} {e : κ → ℝ} {E : FiniteDeathDiagram β} {e' : κ' → ℝ}
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    diagramWassersteinEDist q D e E e' ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, r, Dh, eh, hDh, hb, hd, he⟩ := exists_isSublevelDiagram_and_values 𝕜 K h p
  choose sb hsbK hsb using hb
  choose sd hsdK hsd using hd
  choose se hseK hse using he
  -- the endpoint simplices are distinct
  have hB := fun i ↦ card_birth_add_card_essential_le 𝕜 K hinj hDh (hsbK i)
  have hE' := fun k ↦ card_birth_add_card_essential_le 𝕜 K hinj hDh (hseK k)
  have hDd := fun i ↦ card_death_le 𝕜 K hinj hDh (hsdK i)
  have hmemb : ∀ i, i ∈ Finset.univ.filter fun j ↦ Dh.birth j = h (sb i) := fun i ↦ by
    simp [hsb]
  have hmeme : ∀ k, k ∈ Finset.univ.filter fun l ↦ eh l = h (se k) := fun k ↦ by simp [hse]
  have hmemd : ∀ i, i ∈ Finset.univ.filter fun j ↦ Dh.death j = h (sd i) := fun i ↦ by
    simp [hsd]
  have hcb : ∀ i, (sb i).card = p + 1 := fun i ↦ by
    have := hB i
    have := Finset.card_pos.mpr ⟨i, hmemb i⟩
    split_ifs at * <;> omega
  have hce : ∀ k, (se k).card = p + 1 := fun k ↦ by
    have := hE' k
    have := Finset.card_pos.mpr ⟨k, hmeme k⟩
    split_ifs at * <;> omega
  have hcd : ∀ i, (sd i).card = p + 2 := fun i ↦ by
    have := hDd i
    have := Finset.card_pos.mpr ⟨i, hmemd i⟩
    split_ifs at * <;> omega
  have hsb_inj : ∀ i j, sb i = sb j → i = j := fun i j hij ↦ by
    have h1 : (Finset.univ.filter fun l ↦ Dh.birth l = h (sb i)).card ≤ 1 := by
      have := hB i; split_ifs at this <;> omega
    refine Finset.card_le_one.mp h1 i (hmemb i) j ?_
    rw [hij]
    exact hmemb j
  have hsd_inj : ∀ i j, sd i = sd j → i = j := fun i j hij ↦ by
    have h1 : (Finset.univ.filter fun l ↦ Dh.death l = h (sd i)).card ≤ 1 := by
      have := hDd i; split_ifs at this <;> omega
    refine Finset.card_le_one.mp h1 i (hmemd i) j ?_
    rw [hij]
    exact hmemd j
  have hse_inj : ∀ k l, se k = se l → k = l := fun k l hkl ↦ by
    have h1 : (Finset.univ.filter fun m ↦ eh m = h (se k)).card ≤ 1 := by
      have := hE' k; split_ifs at this <;> omega
    refine Finset.card_le_one.mp h1 k (hmeme k) l ?_
    rw [hkl]
    exact hmeme l
  have hsb_se : ∀ i k, sb i ≠ se k := fun i k hik ↦ by
    have := hB i
    have h1 := Finset.card_pos.mpr ⟨i, hmemb i⟩
    have h2 := Finset.card_pos.mpr ⟨k, show k ∈ Finset.univ.filter fun l ↦ eh l = h (sb i) by
      rw [hik]; exact hmeme k⟩
    split_ifs at this <;> omega
  -- the relabelled diagrams
  have hDf := hDh.relabel 𝕜 hfh sb sd se hsbK hsb hsdK hsd hseK hse
  have hDg := hDh.relabel 𝕜 hgh sb sd se hsbK hsb hsdK hsd hseK hse
  have h1 := diagramWassersteinEDist_eq_zero_of_isSublevelDiagram 𝕜 hq0 hD hDf
  have h3 := diagramWassersteinEDist_eq_zero_of_isSublevelDiagram 𝕜 hq0 hDg hE
  set G : Finset ι → ℝ≥0∞ := fun σ ↦ ENNReal.ofReal |f σ - g σ| ^ q
  set U : Fin n → ℝ≥0∞ := fun i ↦ G (sb i) + G (sd i)
  have hle : ∀ i, g (sb i) ≤ g (sd i) := fun i ↦
    hgh _ (hsbK i) _ (hsdK i) (by rw [hsb, hsd]; exact (Dh.birth_lt_death i).le)
  have hle' : ∀ i, f (sb i) ≤ f (sd i) := fun i ↦
    hfh _ (hsbK i) _ (hsdK i) (by rw [hsb, hsd]; exact (Dh.birth_lt_death i).le)
  have hW : ∀ i, ENNReal.ofReal (max |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|) ^ q ≤ U i := by
    intro i
    rcases le_total |f (sb i) - g (sb i)| |f (sd i) - g (sd i)| with hab | hab
    · rw [max_eq_right hab]; exact le_add_self
    · rw [max_eq_left hab]; exact le_self_add
  let M : DiagramMatching {i // f (sb i) < f (sd i)} {i // g (sb i) < g (sd i)} :=
    { relates := fun x y ↦ x.1 = y.1
      left_unique := fun x y z hy hz ↦ Subtype.ext (hy.symm.trans hz)
      right_unique := fun x y z hx hy ↦ Subtype.ext (hx.trans hy.symm) }
  have hL : ∀ x, M.leftTerm (relabelDiagram f sb sd) (relabelDiagram g sb sd) x ^ q ≤ U x.1 := by
    rintro ⟨i, hi⟩
    refine le_trans (ENNReal.rpow_le_rpow ?_ hq0.le) (hW i)
    by_cases hgi : g (sb i) < g (sd i)
    · rw [M.leftTerm_of_relates _ _ (j := ⟨i, hgi⟩) rfl]
      rfl
    · have hnot : ¬ ∃ y, M.relates ⟨i, hi⟩ y := fun ⟨y, hy⟩ ↦ hgi (by
        have := y.2; rw [← show i = y.1 from hy] at this; exact this)
      rw [M.leftTerm_of_not _ _ hnot]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := le_max_left |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h3 := le_max_right |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h4 := neg_abs_le (f (sb i) - g (sb i))
      have h5 := le_abs_self (f (sd i) - g (sd i))
      simp only [relabelDiagram]
      linarith [not_lt.mp hgi]
  have hR : ∀ y, M.rightTerm (relabelDiagram g sb sd) y ^ q ≤
      if f (sb y.1) < f (sd y.1) then 0 else U y.1 := by
    rintro ⟨i, hi⟩
    by_cases hfi : f (sb i) < f (sd i)
    · rw [M.rightTerm_of_relates _ (i := ⟨i, hfi⟩) rfl, ite_eq_left hfi,
        ENNReal.zero_rpow_of_pos hq0]
    · have hnot : ¬ ∃ x, M.relates x ⟨i, hi⟩ := fun ⟨x, hx⟩ ↦ hfi (by
        have := x.2; rw [show x.1 = i from hx] at this; exact this)
      rw [M.rightTerm_of_not _ hnot, ite_eq_right hfi]
      refine le_trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le) (hW i)
      have h2 := le_max_left |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h3 := le_max_right |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h4 := le_abs_self (f (sb i) - g (sb i))
      have h5 := neg_abs_le (f (sd i) - g (sd i))
      simp only [relabelDiagram]
      linarith [not_lt.mp hfi]
  have hsub : ∀ (P : Fin n → Prop) (F : Fin n → ℝ≥0∞),
      ∑ x : {i // P i}, F x.1 = ∑ i, if P i then F i else 0 := fun P F ↦ by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) F).symm
  have hcost : diagramWassersteinCost q M (Equiv.refl _) (relabelDiagram f sb sd)
      (fun k ↦ f (se k)) (relabelDiagram g sb sd) (fun k ↦ g (se k)) ≤
      ∑ σ ∈ Finset.univ.filter (· ∈ K), G σ := by
    rw [diagramWassersteinCost_eq]
    have hA : ∑ x, M.leftTerm (relabelDiagram f sb sd) (relabelDiagram g sb sd) x ^ q +
        ∑ y, M.rightTerm (relabelDiagram g sb sd) y ^ q ≤ ∑ i, U i := by
      refine (add_le_add (Finset.sum_le_sum fun x _ ↦ hL x)
        (Finset.sum_le_sum fun y _ ↦ hR y)).trans ?_
      rw [hsub (fun i ↦ f (sb i) < f (sd i)) U,
        hsub (fun i ↦ g (sb i) < g (sd i)) (fun i ↦ if f (sb i) < f (sd i) then 0 else U i),
        ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ ↦ by split_ifs <;> simp
    set φ : Fin n ⊕ Fin n ⊕ Fin r → Finset ι := Sum.elim sb (Sum.elim sd se)
    have hφ : ∀ x ∈ (Finset.univ : Finset (Fin n ⊕ Fin n ⊕ Fin r)),
        ∀ y ∈ (Finset.univ : Finset (Fin n ⊕ Fin n ⊕ Fin r)), φ x = φ y → x = y := by
      rintro (i | i | k) - (j | j | l) - hxy <;> simp only [φ, Sum.elim_inl, Sum.elim_inr] at hxy
      · rw [hsb_inj i j hxy]
      · have := hcb i; rw [hxy, hcd j] at this; omega
      · exact absurd hxy (hsb_se i l)
      · have := hcb j; rw [← hxy, hcd i] at this; omega
      · rw [hsd_inj i j hxy]
      · have := hce l; rw [← hxy, hcd i] at this; omega
      · exact absurd hxy.symm (hsb_se j k)
      · have := hce k; rw [hxy, hcd j] at this; omega
      · rw [hse_inj k l hxy]
    have himg : (Finset.univ : Finset (Fin n ⊕ Fin n ⊕ Fin r)).image φ ⊆
        Finset.univ.filter (· ∈ K) := by
      intro σ hσ
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hσ
      rcases x with i | i | k <;> simp [φ, hsbK, hsdK, hseK]
    calc _ ≤ ∑ i, U i + ∑ k, G (se k) := add_le_add hA le_rfl
      _ = ∑ x, G (φ x) := by
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc, ← Finset.sum_add_distrib]
          rfl
      _ = ∑ σ ∈ Finset.univ.image φ, G σ := (Finset.sum_image hφ).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset himg
  have h2 : diagramWassersteinEDist q (relabelDiagram f sb sd) (fun k ↦ f (se k))
      (relabelDiagram g sb sd) (fun k ↦ g (se k)) ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), G σ) ^ (1 / q) :=
    (iInf_le_of_le M (iInf_le _ (Equiv.refl _))).trans
      (ENNReal.rpow_le_rpow hcost (by positivity))
  calc diagramWassersteinEDist q D e E e'
      ≤ diagramWassersteinEDist q D e (relabelDiagram f sb sd) (fun k ↦ f (se k)) +
          diagramWassersteinEDist q (relabelDiagram f sb sd) (fun k ↦ f (se k)) E e' :=
        diagramWassersteinEDist_triangle hq _ _ _ _ _ _
    _ ≤ 0 + (diagramWassersteinEDist q (relabelDiagram f sb sd) (fun k ↦ f (se k))
          (relabelDiagram g sb sd) (fun k ↦ g (se k)) +
        diagramWassersteinEDist q (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e') := by
        rw [h1]
        exact add_le_add le_rfl (diagramWassersteinEDist_triangle hq _ _ _ _ _ _)
    _ ≤ _ := by rw [h3, zero_add, add_zero]; exact h2

omit [LinearOrder ι] in
/-- Every function on simplices is ordered by a function injective on `K`: break ties by an
enumeration of the simplices and take ranks. -/
theorem exists_injective_ordered (K : PreAbstractSimplicialComplex ι) (h : Finset ι → ℝ) :
    ∃ h' : Finset ι → ℝ, (∀ σ ∈ K, ∀ τ ∈ K, h' σ = h' τ → σ = τ) ∧
      ∀ σ ∈ K, ∀ τ ∈ K, h' σ ≤ h' τ → h σ ≤ h τ := by
  set en := Fintype.equivFin (Finset ι)
  set key : Finset ι → ℝ ×ₗ ℕ := fun σ ↦ toLex (h σ, (en σ : ℕ))
  have hkey : ∀ σ τ, key σ = key τ → σ = τ := fun σ τ hστ ↦ by
    have := congrArg (fun x ↦ (ofLex x).2) hστ
    simp only [key, ofLex_toLex] at this
    exact en.injective (Fin.ext this)
  set rank : Finset ι → ℝ := fun σ ↦
    ((Finset.univ.filter fun τ ↦ τ ∈ K ∧ key τ < key σ).card : ℝ)
  have hrank : ∀ σ ∈ K, ∀ τ, key σ < key τ → rank σ < rank τ := by
    intro σ hσ τ hστ
    simp only [rank, Nat.cast_lt]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun ρ hρ ↦ ?_, fun heq ↦ ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      exact ⟨hρ.1, hρ.2.trans hστ⟩
    · have : σ ∈ Finset.univ.filter fun ρ ↦ ρ ∈ K ∧ key ρ < key τ := by simp [hσ, hστ]
      rw [← heq] at this
      simp at this
  refine ⟨rank, fun σ hσ τ hτ heq ↦ ?_, fun σ hσ τ hτ hle ↦ ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne (fun hk ↦ hne (hkey σ τ hk)) with hlt | hlt
    · exact absurd heq (hrank σ hσ τ hlt).ne
    · exact absurd heq (hrank τ hτ σ hlt).ne'
  · have hk : key σ ≤ key τ := by
      by_contra hc
      exact absurd hle (not_le.mpr (hrank τ hτ σ (not_le.mp hc)))
    rcases (Prod.Lex.le_iff).mp hk with h1 | h1
    · exact h1.le
    · exact h1.1.le

/-- `q`-Wasserstein stability for `Fin`-indexed diagrams, by strong induction on the number of
discordant pairs, as for the bottleneck distance. -/
theorem diagramWassersteinEDist_le_of_card_discordantPairs_le (K : PreAbstractSimplicialComplex ι)
    (p : ℕ) {q : ℝ} (hq : 1 ≤ q) (N : ℕ) : ∀ f g : Finset ι → ℝ, IsMonotoneOnFaces K f →
      IsMonotoneOnFaces K g → (discordantPairs K f g).card ≤ N →
      ∀ (n r n' r' : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ)
        (E : FiniteDeathDiagram (Fin n')) (e' : Fin r' → ℝ),
        IsSublevelDiagram 𝕜 K f p D e → IsSublevelDiagram 𝕜 K g p E e' →
        diagramWassersteinEDist q D e E e' ≤
          (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f g hf hg hN n r n' r' D e E e' hD hE
  rcases (discordantPairs K f g).eq_empty_or_nonempty with h0 | ⟨⟨σ, τ⟩, hq'⟩
  · have hnot : ∀ σ ∈ K, ∀ τ ∈ K, ¬ (f σ < f τ ∧ g τ < g σ) := by
      intro σ hσ τ hτ hc
      have : (σ, τ) ∈ discordantPairs K f g := by
        simp [discordantPairs, hσ, hτ, hc.1, hc.2]
      simp [h0] at this
    obtain ⟨h', hinj, hord⟩ := exists_injective_ordered K (fun ρ ↦ f ρ + g ρ)
    refine diagramWassersteinEDist_le_of_ordered 𝕜 K hinj ?_ ?_ p hq hD hE
    · intro σ hσ τ hτ hle
      have hle' := hord σ hσ τ hτ hle
      by_contra hc
      have := hnot τ hτ σ hσ
      push Not at hc this
      linarith [this hc]
    · intro σ hσ τ hτ hle
      have hle' := hord σ hσ τ hτ hle
      by_contra hc
      have := hnot σ hσ τ hτ
      push Not at hc this
      have h' : f τ ≤ f σ := by
        by_contra h''
        exact absurd (this (not_le.mp h'')) (not_le.mpr hc)
      linarith
  · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    obtain ⟨hσ, hτ, hf0, hg0⟩ := hq'
    set d0 := f σ - f τ
    set d1 := g σ - g τ
    have hd0 : d0 < 0 := by simp only [d0]; linarith
    have hd1 : 0 < d1 := by simp only [d1]; linarith
    set t := d0 / (d0 - d1)
    have ht0 : 0 < t := div_pos_of_neg_of_neg hd0 (by linarith)
    have ht1 : t < 1 := by
      rw [div_lt_one_of_neg (by linarith)]
      linarith
    have hzero : (1 - t) * d0 + t * d1 = 0 := by
      have hne : d0 - d1 ≠ 0 := (show d0 - d1 < 0 by linarith).ne
      simp only [t]
      field_simp
      ring
    set m : Finset ι → ℝ := fun ρ ↦ (1 - t) * f ρ + t * g ρ
    have hm : IsMonotoneOnFaces K m := hf.convexComb hg ht0.le ht1.le
    have hst : (σ, τ) ∈ discordantPairs K f g := by
      simp [discordantPairs, hσ, hτ, hf0, hg0]
    have hmστ : m σ = m τ := by
      simp only [m]
      simp only [d0, d1] at hzero
      linarith
    have hfm : discordantPairs K f m ⊂ discordantPairs K f g := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq ↦ ?_, fun heq ↦ ?_⟩
      · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hq
        refine ⟨h1, h2, h3, ?_⟩
        by_contra hc
        push Not at hc
        simp only [m] at h4
        have := mul_le_mul_of_nonneg_left hc ht0.le
        have := mul_lt_mul_of_pos_left h3 (sub_pos.mpr ht1)
        linarith
      · rw [← heq] at hst
        simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hst
        exact absurd hst.2.2.2 (by rw [hmστ]; exact lt_irrefl _)
    have hmg : discordantPairs K m g ⊂ discordantPairs K f g := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun q hq ↦ ?_, fun heq ↦ ?_⟩
      · simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hq
        refine ⟨h1, h2, ?_, h4⟩
        by_contra hc
        push Not at hc
        simp only [m] at h3
        have := mul_le_mul_of_nonneg_left hc (sub_pos.mpr ht1).le
        have := mul_lt_mul_of_pos_left h4 ht0
        linarith
      · rw [← heq] at hst
        simp only [discordantPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hst
        exact absurd hst.2.2.1 (by rw [hmστ]; exact lt_irrefl _)
    set S := ∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q
    have hscale : ∀ c : ℝ, 0 ≤ c → ∀ u : Finset ι → ℝ, (∀ ρ, u ρ = c * (f ρ - g ρ)) →
        (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |u σ| ^ q) ^ (1 / q) =
          ENNReal.ofReal c * S ^ (1 / q) := by
      intro c hc u hu
      have : ∀ σ, ENNReal.ofReal |u σ| ^ q = ENNReal.ofReal c ^ q * ENNReal.ofReal |f σ - g σ| ^ q :=
        fun σ ↦ by
          rw [hu, abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc,
            ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      simp_rw [this]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    have hSfm := hscale t ht0.le (fun ρ ↦ f ρ - m ρ) (fun ρ ↦ by simp only [m]; ring)
    have hSmg := hscale (1 - t) (sub_pos.mpr ht1).le (fun ρ ↦ m ρ - g ρ)
      (fun ρ ↦ by simp only [m]; ring)
    obtain ⟨n0, r0, Dm, em, hDm⟩ := exists_isSublevelDiagram_and_values 𝕜 K m p
    have hlt1 := (Finset.card_lt_card hfm).trans_le hN
    have hlt2 := (Finset.card_lt_card hmg).trans_le hN
    calc diagramWassersteinEDist q D e E e'
        ≤ diagramWassersteinEDist q D e Dm em + diagramWassersteinEDist q Dm em E e' :=
          diagramWassersteinEDist_triangle hq _ _ _ _ _ _
      _ ≤ ENNReal.ofReal t * S ^ (1 / q) + ENNReal.ofReal (1 - t) * S ^ (1 / q) := by
          rw [← hSfm, ← hSmg]
          exact add_le_add (ih _ hlt1 f m hf hm le_rfl _ _ _ _ D e Dm em hD hDm.1)
            (ih _ hlt2 m g hm hg le_rfl _ _ _ _ Dm em E e' hDm.1 hE)
      _ = S ^ (1 / q) := by
          rw [← add_mul, ← ENNReal.ofReal_add ht0.le (sub_pos.mpr ht1).le]
          simp

/-- GAPS 108.35, the finite-complex clause: for monotone functions `f, g` on the simplices of a
finite simplicial complex `K` and `1 ≤ q < ∞`, the `q`-Wasserstein distance between the full
degree-`p` diagrams is at most `(∑_{σ ∈ K} |f σ - g σ|^q)^{1/q}`. The clauses for tame Lipschitz
functions on triangulable spaces with polynomially growing triangulations are not formalized. -/
theorem diagramWassersteinEDist_le_of_isSublevelDiagram
    (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (q : ℝ) (hq : 1 ≤ q)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    diagramWassersteinEDist q D e E e' ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, r, D0, e0, hD0, -⟩ := exists_isSublevelDiagram_and_values 𝕜 K f p
  obtain ⟨n', r', E0, e0', hE0, -⟩ := exists_isSublevelDiagram_and_values 𝕜 K g p
  have h1 := diagramWassersteinEDist_eq_zero_of_isSublevelDiagram 𝕜 hq0 hD hD0
  have h3 := diagramWassersteinEDist_eq_zero_of_isSublevelDiagram 𝕜 hq0 hE0 hE
  have h2 := diagramWassersteinEDist_le_of_card_discordantPairs_le 𝕜 K p hq _ f g hf hg le_rfl
    n r n' r' D0 e0 E0 e0' hD0 hE0
  calc diagramWassersteinEDist q D e E e'
      ≤ diagramWassersteinEDist q D e D0 e0 + diagramWassersteinEDist q D0 e0 E e' :=
        diagramWassersteinEDist_triangle hq _ _ _ _ _ _
    _ ≤ 0 + (diagramWassersteinEDist q D0 e0 E0 e0' + diagramWassersteinEDist q E0 e0' E e') := by
        rw [h1]
        exact add_le_add le_rfl (diagramWassersteinEDist_triangle hq _ _ _ _ _ _)
    _ ≤ _ := by rw [h3, zero_add, add_zero]; exact h2

/-- The full simplex on a finite vertex type: all nonempty vertex sets. -/
def fullSimplexComplex (X : Type*) : PreAbstractSimplicialComplex X := ⊤

/-- The Rips filtration value of a simplex in the diameter-`2r` convention: `σ ∈ Rips(r)` exactly
when `diam σ ≤ 2r`. -/
def ripsFiltrationValue {X : Type*} [PseudoMetricSpace X] (σ : Finset X) : ℝ :=
  Metric.diam (σ : Set X) / 2

/-- Diameters are monotone, so the Rips filtration is a monotone filtration of the full simplex. -/
theorem isMonotoneOnFaces_ripsFiltrationValue {X : Type*} [PseudoMetricSpace X] [Fintype X]
    [LinearOrder X] : IsMonotoneOnFaces (fullSimplexComplex X) (ripsFiltrationValue (X := X)) := by
  intro τ σ _ _ hτσ
  unfold ripsFiltrationValue
  gcongr
  exact Metric.diam_mono (by exact_mod_cast hτσ) σ.finite_toSet.isBounded

end Stability

end CKSD
