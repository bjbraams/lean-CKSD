module

public import CKSD.Geometry.SimplicialPersistence

/-!
# Gromov–Hausdorff stability of Rips persistence

The simplicial boundary squares to zero. Two homological invariances of sublevel persistence of
monotone functions on finite simplicial complexes follow:

* removing a vertex `w` with a twin `v` (adding `v` to a simplex containing `w` gives a simplex of
  the same filtration value) leaves the persistent Betti numbers unchanged: the chain homotopy
  `σ ↦ ±(σ ∪ {v})` retracts the cycles onto those avoiding `w`;
* persistent Betti numbers are invariant under an order embedding of the vertices.

Together they give pullback invariance: along a map of vertices with an order-embedded section,
the filtration `σ ↦ Φ (π σ)` of the full simplex has the persistent Betti numbers of `Φ`.

For finite metric spaces `X` and `Y`, an optimal coupling realizing `d_GH(X, Y)` gives a
correspondence of distortion at most `2 d_GH(X, Y)`. On two ordered copies of the correspondence,
the Rips filtrations of `X` and `Y` pull back to monotone functions within `d_GH(X, Y)` of each
other, and bottleneck stability (GAPS 108.19) gives GAPS 108.36. The optimal coupling is
Mathlib's `GromovHausdorff.ghDist_eq_hausdorffDist`.

Sources: GAPS 108.19 and 108.36.
-/

@[expose] public section

noncomputable section

open Module Set
open scoped ENNReal NNReal

namespace CKSD

section BoundarySquare

variable {ι : Type*} [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

/-- The incidence number of the face obtained by deleting the vertex `x`: the sign
`(-1)^k` where `x` is the `k`th vertex of `σ`. -/
theorem simplexIncidence_erase {σ : Finset ι} {x : ι} (hx : x ∈ σ) (hne : (σ.erase x).Nonempty) :
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
theorem simplexIncidence_eq_zero {τ σ : Finset ι} (h : ∀ x ∈ σ, τ ≠ σ.erase x) :
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
theorem simplexIncidence_empty_left (σ : Finset ι) : simplexIncidence 𝕜 ∅ σ = 0 := by
  unfold simplexIncidence
  simp

/-- The boundary of a boundary vanishes: `∑_τ [ρ : τ] [τ : σ] = 0`. -/
theorem sum_simplexIncidence_mul_simplexIncidence [Fintype ι] (ρ σ : Finset ι) :
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
    rw [simplexIncidence_eq_zero 𝕜 (σ := σ) (fun x hx h ↦ hτ (Finset.mem_image.mpr ⟨x, hx, h.symm⟩)),
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
      rw [simplexIncidence_eq_zero 𝕜, zero_mul]
      intro y _ h
      have : x ∈ (σ.erase u).erase v := by simp [hxuv.1, hxuv.2, hx]
      rw [h] at this
      simp at this
    rw [Finset.sum_pair huv.ne]
    by_cases hne : ((σ.erase u).erase v).Nonempty
    · have hcomm : (σ.erase u).erase v = (σ.erase v).erase u := Finset.erase_right_comm
      have hne1 : (σ.erase u).Nonempty := hne.mono (Finset.erase_subset _ _)
      have hne2 : (σ.erase v).Nonempty := (hcomm ▸ hne).mono (Finset.erase_subset _ _)
      rw [simplexIncidence_erase 𝕜 hvu hne, simplexIncidence_erase 𝕜 hu hne1, hcomm,
        simplexIncidence_erase 𝕜 huv' (hcomm ▸ hne), simplexIncidence_erase 𝕜 hv hne2]
      have h1 : ((σ.erase u).filter (· < v)).card + 1 = (σ.filter (· < v)).card := by
        rw [Finset.filter_erase, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hu, huv⟩)]
      have h2 : ((σ.erase v).filter (· < u)).card = (σ.filter (· < u)).card := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [huv.le])]
      rw [h2, ← h1, pow_succ]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne, simplexIncidence_empty_left]
  · refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [simplexIncidence_eq_zero 𝕜, zero_mul]
    intro y hy h
    obtain ⟨hyx, hyσ⟩ := Finset.mem_erase.mp hy
    rcases lt_or_gt_of_ne hyx with hlt | hlt
    · exact hA ⟨y, hyσ, x, hx, hlt, h.trans Finset.erase_right_comm⟩
    · exact hA ⟨x, hx, y, hyσ, hlt, h⟩

/-- The boundary of a boundary vanishes. -/
theorem simplicialBoundary_apply_simplicialBoundary [Fintype ι] (c : Finset ι → 𝕜) :
    simplicialBoundary 𝕜 (simplicialBoundary 𝕜 c) = 0 := by
  unfold simplicialBoundary
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have : (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ) *
      (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ) = 0 := by
    ext ρ σ
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact sum_simplexIncidence_mul_simplexIncidence 𝕜 ρ σ
  rw [this, Matrix.zero_mulVec]

end BoundarySquare

section Twin

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

omit [Fintype ι] [LinearOrder ι] in
/-- Faces of simplices of a simplicial complex are simplices. -/
theorem mem_of_subset_of_mem {K : PreAbstractSimplicialComplex ι}
    {σ τ : Finset ι} (hσ : σ ∈ K) (hτσ : τ ⊆ σ) (hτ : τ.Nonempty) : τ ∈ K :=
  K.isRelLowerSet_faces.mem_of_le hσ hτσ hτ

/-- The simplicial boundary, evaluated at a simplex. -/
theorem simplicialBoundary_apply (c : Finset ι → 𝕜) (τ : Finset ι) :
    simplicialBoundary 𝕜 c τ = ∑ σ, simplexIncidence 𝕜 τ σ * c σ := rfl

/-- The boundary maps chains of the sublevel complex to chains of the sublevel complex. -/
theorem simplicialBoundary_mem_sublevelChains {K : PreAbstractSimplicialComplex ι}
    {F : Finset ι → ℝ} (hF : IsMonotoneOnFaces K F) {q : ℕ} {a : ℝ} {c : Finset ι → 𝕜}
    (hc : c ∈ sublevelChains 𝕜 K F (q + 1) a) :
    simplicialBoundary 𝕜 c ∈ sublevelChains 𝕜 K F q a := by
  intro τ hτ
  rw [simplicialBoundary_apply] at hτ
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
  have hinc := left_ne_zero_of_mul hσ
  obtain ⟨h1, h2, h3⟩ := hc σ (right_ne_zero_of_mul hσ)
  unfold simplexIncidence at hinc
  split_ifs at hinc with hcond
  · obtain ⟨hne, hsub, hcard⟩ := hcond
    exact ⟨mem_of_subset_of_mem h1 hsub hne, by omega, (hF τ σ h1 hne hsub).trans h3⟩
  · exact absurd rfl hinc

omit [Fintype ι] in
/-- The incidence number of a codimension-one face is a sign. -/
theorem simplexIncidence_insert_mul_self {σ : Finset ι} {v : ι} (hv : v ∉ σ) (hσ : σ.Nonempty) :
    simplexIncidence 𝕜 σ (insert v σ) * simplexIncidence 𝕜 σ (insert v σ) = 1 := by
  have h := simplexIncidence_erase 𝕜 (Finset.mem_insert_self v σ)
    (by rw [Finset.erase_insert hv]; exact hσ)
  rw [Finset.erase_insert hv] at h
  rw [h, ← pow_add, ← two_mul, pow_mul]
  simp

omit [Fintype ι] in
/-- The incidence number of a codimension-one face is nonzero. -/
theorem simplexIncidence_insert_ne_zero {σ : Finset ι} {v : ι} (hv : v ∉ σ) (hσ : σ.Nonempty) :
    simplexIncidence 𝕜 σ (insert v σ) ≠ 0 := fun h ↦ by
  have := simplexIncidence_insert_mul_self 𝕜 hv hσ
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- The chain homotopy of a twin pair `(v, w)`: it sends a simplex `σ` containing `w` but not `v`
to `± (σ ∪ {v})`, with the sign of `σ` in the boundary of `σ ∪ {v}`, and the other simplices to
zero. -/
def twinHomotopy (v w : ι) : (Finset ι → 𝕜) →ₗ[𝕜] (Finset ι → 𝕜) where
  toFun c ρ := if w ∈ ρ ∧ v ∈ ρ then simplexIncidence 𝕜 (ρ.erase v) ρ * c (ρ.erase v) else 0
  map_add' c d := by
    ext ρ
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' r c := by
    ext ρ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

omit [Fintype ι] in
/-- The twin homotopy raises the dimension by one and preserves sublevel complexes. -/
theorem twinHomotopy_mem_sublevelChains {K : PreAbstractSimplicialComplex ι}
    {F : Finset ι → ℝ} {v w : ι} (hvw : v ≠ w)
    (htwin : ∀ σ ∈ K, w ∈ σ → insert v σ ∈ K ∧ F (insert v σ) = F σ) {q : ℕ} {a : ℝ}
    {c : Finset ι → 𝕜} (hc : c ∈ sublevelChains 𝕜 K F q a) :
    twinHomotopy 𝕜 v w c ∈ sublevelChains 𝕜 K F (q + 1) a := by
  intro ρ hρ
  change (if w ∈ ρ ∧ v ∈ ρ then simplexIncidence 𝕜 (ρ.erase v) ρ * c (ρ.erase v) else 0) ≠ 0
    at hρ
  split_ifs at hρ with hwv
  · obtain ⟨h1, h2, h3⟩ := hc _ (right_ne_zero_of_mul hρ)
    have hw : w ∈ ρ.erase v := Finset.mem_erase.mpr ⟨hvw.symm, hwv.1⟩
    obtain ⟨h4, h5⟩ := htwin _ h1 hw
    rw [Finset.insert_erase hwv.2] at h4 h5
    refine ⟨h4, ?_, h5 ▸ h3⟩
    have := Finset.card_erase_add_one hwv.2
    omega
  · exact absurd rfl hρ

/-- The boundary of a chain vanishing on the simplices that contain `w` but not `v`, evaluated at
such a simplex `σ`, only sees the simplex `σ ∪ {v}`. -/
theorem simplicialBoundary_apply_of_twin {v w : ι} {c : Finset ι → 𝕜}
    (hc : ∀ τ, w ∈ τ → v ∉ τ → c τ = 0) {σ : Finset ι} (hwσ : w ∈ σ) (hvσ : v ∉ σ) :
    simplicialBoundary 𝕜 c σ = simplexIncidence 𝕜 σ (insert v σ) * c (insert v σ) := by
  rw [simplicialBoundary_apply, Finset.sum_eq_single (insert v σ)]
  · intro τ _ hτ
    by_cases hinc : simplexIncidence 𝕜 σ τ = 0
    · rw [hinc, zero_mul]
    · have : ∃ x ∈ τ, σ = τ.erase x := by
        by_contra hcon
        push Not at hcon
        exact hinc (simplexIncidence_eq_zero 𝕜 hcon)
      obtain ⟨x, hx, rfl⟩ := this
      have hxv : x ≠ v := by
        rintro rfl
        exact hτ (Finset.insert_erase hx).symm
      rw [hc τ (Finset.mem_of_mem_erase hwσ) (fun hv ↦ hvσ (Finset.mem_erase.mpr ⟨hxv.symm, hv⟩)),
        mul_zero]
  · simp

/-- The boundary of the twin homotopy restores the coefficients on simplices containing `w` but
not `v`. -/
theorem simplicialBoundary_twinHomotopy_apply {v w : ι} (c : Finset ι → 𝕜)
    {σ : Finset ι} (hwσ : w ∈ σ) (hvσ : v ∉ σ) :
    simplicialBoundary 𝕜 (twinHomotopy 𝕜 v w c) σ = c σ := by
  rw [simplicialBoundary_apply_of_twin 𝕜 (fun τ _ hvτ ↦ ?_) hwσ hvσ]
  · change simplexIncidence 𝕜 σ (insert v σ) * (if w ∈ insert v σ ∧ v ∈ insert v σ then
      simplexIncidence 𝕜 ((insert v σ).erase v) (insert v σ) * c ((insert v σ).erase v) else 0) = _
    rw [ite_eq_left ⟨Finset.mem_insert_of_mem hwσ, Finset.mem_insert_self v σ⟩,
      Finset.erase_insert hvσ, ← mul_assoc, simplexIncidence_insert_mul_self 𝕜 hvσ ⟨w, hwσ⟩,
      one_mul]
  · change (if w ∈ τ ∧ v ∈ τ then _ else 0) = 0
    rw [ite_eq_right (fun h ↦ absurd h.2 hvτ)]

/-- A chain vanishing on the simplices containing `w` but not `v`, whose boundary vanishes on
those simplices as well, vanishes on all simplices containing `w`. -/
theorem eq_zero_of_twin {v w : ι} (hvw : v ≠ w) {c : Finset ι → 𝕜}
    (hc : ∀ τ, w ∈ τ → v ∉ τ → c τ = 0)
    (hdc : ∀ τ, w ∈ τ → v ∉ τ → simplicialBoundary 𝕜 c τ = 0) {ρ : Finset ι} (hwρ : w ∈ ρ) :
    c ρ = 0 := by
  by_cases hvρ : v ∈ ρ
  · have hw : w ∈ ρ.erase v := Finset.mem_erase.mpr ⟨hvw.symm, hwρ⟩
    have hv : v ∉ ρ.erase v := Finset.notMem_erase v ρ
    have := hdc _ hw hv
    rw [simplicialBoundary_apply_of_twin 𝕜 hc hw hv, Finset.insert_erase hvρ] at this
    have hne := simplexIncidence_insert_ne_zero 𝕜 hv ⟨w, hw⟩
    rw [Finset.insert_erase hvρ] at hne
    exact (mul_eq_zero.mp this).resolve_left hne
  · exact hc ρ hwρ hvρ

/-- Removing a twin: let `v ≠ w` be vertices such that adding `v` to a simplex containing `w`
gives a simplex with the same filtration value. Then deleting all simplices containing `w` does
not change the persistent Betti numbers of the sublevel filtration. -/
theorem sublevelPersistentBetti_eq_of_twin {K K' : PreAbstractSimplicialComplex ι}
    {F : Finset ι → ℝ} (hF : IsMonotoneOnFaces K F) {v w : ι} (hvw : v ≠ w)
    (hK' : ∀ σ, σ ∈ K' ↔ σ ∈ K ∧ w ∉ σ)
    (htwin : ∀ σ ∈ K, w ∈ σ → insert v σ ∈ K ∧ F (insert v σ) = F σ) (p : ℕ) {a b : ℝ}
    (hab : a ≤ b) : sublevelPersistentBetti 𝕜 K F p a b = sublevelPersistentBetti 𝕜 K' F p a b := by
  unfold sublevelPersistentBetti
  have hC' : ∀ q c, c ∈ sublevelChains 𝕜 K' F q a ↔
      c ∈ sublevelChains 𝕜 K F q a ∧ ∀ ρ, w ∈ ρ → c ρ = 0 := fun q c ↦ by
    constructor
    · intro hc
      refine ⟨fun σ hσ ↦ ?_, fun ρ hρ ↦ ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hc σ hσ
        exact ⟨((hK' σ).mp h1).1, h2, h3⟩
      · by_contra h
        exact ((hK' ρ).mp (hc ρ h).1).2 hρ
    · rintro ⟨hc, hw⟩ σ hσ
      obtain ⟨h1, h2, h3⟩ := hc σ hσ
      exact ⟨(hK' σ).mpr ⟨h1, fun h ↦ hσ (hw σ h)⟩, h2, h3⟩
  have hC'b : ∀ q c, c ∈ sublevelChains 𝕜 K' F q b ↔
      c ∈ sublevelChains 𝕜 K F q b ∧ ∀ ρ, w ∈ ρ → c ρ = 0 := fun q c ↦ by
    constructor
    · intro hc
      refine ⟨fun σ hσ ↦ ?_, fun ρ hρ ↦ ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hc σ hσ
        exact ⟨((hK' σ).mp h1).1, h2, h3⟩
      · by_contra h
        exact ((hK' ρ).mp (hc ρ h).1).2 hρ
    · rintro ⟨hc, hw⟩ σ hσ
      obtain ⟨h1, h2, h3⟩ := hc σ hσ
      exact ⟨(hK' σ).mpr ⟨h1, fun h ↦ hσ (hw σ h)⟩, h2, h3⟩
  set Z := sublevelCycles 𝕜 K F p a
  set B := sublevelBoundaries 𝕜 K F p b
  set Z' := sublevelCycles 𝕜 K' F p a
  set B' := sublevelBoundaries 𝕜 K' F p b
  have hZ'Z : Z' ≤ Z := fun z hz ↦ ⟨((hC' p z).mp hz.1).1, hz.2⟩
  have hB'B : B' ≤ B := Submodule.map_mono fun c hc ↦ ((hC'b (p + 1) c).mp hc).1
  -- a boundary that is a cycle of `K'` is a boundary of `K'`
  have hinf : Z' ⊓ B = Z' ⊓ B' := by
    refine le_antisymm (fun z hz ↦ ⟨hz.1, ?_⟩) (inf_le_inf_left _ hB'B)
    obtain ⟨hz', c, hc, rfl⟩ := hz
    set c'' := c - simplicialBoundary 𝕜 (twinHomotopy 𝕜 v w c)
    have hc''mem : c'' ∈ sublevelChains 𝕜 K F (p + 1) b :=
      sub_mem hc (simplicialBoundary_mem_sublevelChains 𝕜 hF
        (twinHomotopy_mem_sublevelChains 𝕜 hvw htwin hc))
    have hdc'' : simplicialBoundary 𝕜 c'' = simplicialBoundary 𝕜 c := by
      simp [c'', simplicialBoundary_apply_simplicialBoundary]
    have hW : ∀ τ, w ∈ τ → v ∉ τ → c'' τ = 0 := fun τ hw hv ↦ by
      simp only [c'', Pi.sub_apply, simplicialBoundary_twinHomotopy_apply 𝕜 c hw hv, sub_self]
    have hzero : ∀ ρ, w ∈ ρ → c'' ρ = 0 := fun ρ hρ ↦
      eq_zero_of_twin 𝕜 hvw hW (fun τ hw _ ↦ by
        rw [hdc'']; exact ((hC' p _).mp hz'.1).2 τ hw) hρ
    exact ⟨c'', (hC'b (p + 1) c'').mpr ⟨hc''mem, hzero⟩, hdc''⟩
  -- every cycle of `K` is a cycle of `K'` up to a boundary
  have hsup : Z ≤ Z' ⊔ (Z ⊓ B) := by
    intro z hz
    set d := simplicialBoundary 𝕜 (twinHomotopy 𝕜 v w z)
    have hHz := twinHomotopy_mem_sublevelChains 𝕜 hvw htwin hz.1
    have hdmem : d ∈ sublevelChains 𝕜 K F p a := simplicialBoundary_mem_sublevelChains 𝕜 hF hHz
    have hdcyc : d ∈ LinearMap.ker (simplicialBoundary 𝕜) :=
      LinearMap.mem_ker.mpr (simplicialBoundary_apply_simplicialBoundary 𝕜 _)
    have hdB : d ∈ B := ⟨_, sublevelChains_mono 𝕜 K F (p + 1) hab hHz, rfl⟩
    have hz1 : z - d ∈ Z' := by
      have hcyc : z - d ∈ LinearMap.ker (simplicialBoundary 𝕜) := sub_mem hz.2 hdcyc
      have hW : ∀ τ, w ∈ τ → v ∉ τ → (z - d) τ = 0 := fun τ hw hv ↦ by
        simp only [d, Pi.sub_apply, simplicialBoundary_twinHomotopy_apply 𝕜 z hw hv, sub_self]
      have hzero : ∀ ρ, w ∈ ρ → (z - d) ρ = 0 := fun ρ hρ ↦
        eq_zero_of_twin 𝕜 hvw hW (fun τ _ _ ↦ by
          rw [LinearMap.mem_ker.mp hcyc]; rfl) hρ
      exact ⟨(hC' p _).mpr ⟨sub_mem hz.1 hdmem, hzero⟩, hcyc⟩
    exact Submodule.mem_sup.mpr ⟨z - d, hz1, d, ⟨⟨hdmem, hdcyc⟩, hdB⟩, sub_add_cancel z d⟩
  have hsup' : Z' ⊔ (Z ⊓ B) = Z := le_antisymm (sup_le hZ'Z inf_le_left) hsup
  have hinf' : Z' ⊓ (Z ⊓ B) = Z' ⊓ B' := by
    rw [← inf_assoc, inf_eq_left.mpr hZ'Z, hinf]
  have key := Submodule.finrank_sup_add_finrank_inf_eq Z' (Z ⊓ B)
  rw [hsup', hinf'] at key
  have h1 := Submodule.finrank_mono (inf_le_left : Z ⊓ B ≤ Z)
  have h2 := Submodule.finrank_mono (inf_le_left : Z' ⊓ B' ≤ Z')
  omega

end Twin

section Relabel

variable {X V : Type*} [Fintype X] [LinearOrder X] [Fintype V] [LinearOrder V] (𝕜 : Type*)
  [Field 𝕜]

/-- Incidence numbers are invariant under an order embedding of the vertices. -/
theorem simplexIncidence_map (s : X ↪o V) (μ σ : Finset X) :
    simplexIncidence 𝕜 (μ.map s.toEmbedding) (σ.map s.toEmbedding) = simplexIncidence 𝕜 μ σ := by
  unfold simplexIncidence
  simp only [Finset.map_nonempty, Finset.map_subset_map, Finset.card_map]
  congr 2
  symm
  refine Finset.card_bij (fun x _ ↦ s x) (fun x hx ↦ ?_) (fun x _ y _ h ↦ s.injective h)
    (fun w hw ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_map] at hx ⊢
    obtain ⟨hx, y, ⟨hy, hyμ⟩, hlt⟩ := hx
    refine ⟨⟨x, hx, rfl⟩, s y, ⟨⟨y, hy, rfl⟩, ?_⟩, s.lt_iff_lt.mpr hlt⟩
    rintro ⟨z, hz, hzy⟩
    exact hyμ (s.injective hzy ▸ hz)
  · simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_map] at hw
    obtain ⟨⟨x, hx, rfl⟩, _, ⟨⟨y, hy, rfl⟩, hyμ⟩, hlt⟩ := hw
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨hx, y, ⟨hy, fun h ↦ hyμ ⟨y, h, rfl⟩⟩, s.lt_iff_lt.mp hlt⟩

/-- Transport of chains along an order embedding of the vertices. -/
def chainMap (s : X ↪o V) : (Finset X → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) :=
  (Matrix.of fun (ρ : Finset V) (σ : Finset X) ↦
    if σ.map s.toEmbedding = ρ then (1 : 𝕜) else 0).mulVecLin

omit [Fintype V] in
/-- Transported chains take the original coefficient on the image of a simplex. -/
theorem chainMap_apply_map (s : X ↪o V) (c : Finset X → 𝕜) (μ : Finset X) :
    chainMap 𝕜 s c (μ.map s.toEmbedding) = c μ := by
  change ∑ σ, (if σ.map s.toEmbedding = μ.map s.toEmbedding then (1 : 𝕜) else 0) * c σ = c μ
  rw [Finset.sum_eq_single μ]
  · simp
  · intro σ _ hσ
    rw [ite_eq_right (fun h ↦ hσ (Finset.map_injective _ h)), zero_mul]
  · simp

omit [Fintype V] in
/-- Transported chains vanish off the image of the vertex embedding. -/
theorem chainMap_apply_of_notMem (s : X ↪o V) (c : Finset X → 𝕜) {ρ : Finset V}
    (hρ : ∀ μ : Finset X, μ.map s.toEmbedding ≠ ρ) : chainMap 𝕜 s c ρ = 0 := by
  change ∑ σ, (if σ.map s.toEmbedding = ρ then (1 : 𝕜) else 0) * c σ = 0
  exact Finset.sum_eq_zero fun σ _ ↦ by rw [ite_eq_right (hρ σ), zero_mul]

omit [Fintype V] in
/-- Transport of chains is injective. -/
theorem chainMap_injective (s : X ↪o V) : Function.Injective (chainMap 𝕜 s) := by
  intro c d h
  ext μ
  rw [← chainMap_apply_map 𝕜 s c μ, ← chainMap_apply_map 𝕜 s d μ, h]

omit [Fintype X] [Fintype V] in
/-- A subset of the image of an order embedding is the image of a subset. -/
theorem exists_map_eq_of_subset_map (s : X ↪o V) {ρ : Finset V} {σ : Finset X}
    (h : ρ ⊆ σ.map s.toEmbedding) : ∃ μ : Finset X, μ.map s.toEmbedding = ρ := by
  classical
  refine ⟨σ.filter fun x ↦ s x ∈ ρ, ?_⟩
  ext y
  simp only [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (h hy)
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- Transport of chains commutes with the boundary. -/
theorem simplicialBoundary_chainMap (s : X ↪o V) (c : Finset X → 𝕜) :
    simplicialBoundary 𝕜 (chainMap 𝕜 s c) = chainMap 𝕜 s (simplicialBoundary 𝕜 c) := by
  ext ρ
  rw [simplicialBoundary_apply]
  have hsum : ∑ τ, simplexIncidence 𝕜 ρ τ * chainMap 𝕜 s c τ =
      ∑ σ, simplexIncidence 𝕜 ρ (σ.map s.toEmbedding) * c σ := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun σ : Finset X ↦
      σ.map s.toEmbedding))]
    · rw [Finset.sum_image (fun σ _ τ _ h ↦ Finset.map_injective _ h)]
      exact Finset.sum_congr rfl fun σ _ ↦ by rw [chainMap_apply_map]
    · intro τ _ hτ
      rw [chainMap_apply_of_notMem 𝕜 s c (fun μ h ↦ hτ (Finset.mem_image.mpr ⟨μ, by simp, h⟩)),
        mul_zero]
  rw [hsum]
  by_cases hρ : ∃ μ : Finset X, μ.map s.toEmbedding = ρ
  · obtain ⟨μ, rfl⟩ := hρ
    rw [chainMap_apply_map, simplicialBoundary_apply]
    exact Finset.sum_congr rfl fun σ _ ↦ by rw [simplexIncidence_map]
  · push Not at hρ
    rw [chainMap_apply_of_notMem 𝕜 s _ hρ]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [simplexIncidence_eq_zero 𝕜, zero_mul]
    intro x _ h
    exact (exists_map_eq_of_subset_map s (h ▸ Finset.erase_subset x _)).elim fun μ hμ ↦
      hρ μ hμ

omit [Fintype V] in
/-- Sublevel chains of the transported complex are the transported sublevel chains. -/
theorem sublevelChains_map (s : X ↪o V) {K : PreAbstractSimplicialComplex X}
    {KV : PreAbstractSimplicialComplex V}
    (hKV : ∀ ρ, ρ ∈ KV ↔ ∃ σ ∈ K, σ.map s.toEmbedding = ρ) {F : Finset X → ℝ}
    {FV : Finset V → ℝ} (hF : ∀ σ, FV (σ.map s.toEmbedding) = F σ) (q : ℕ) (a : ℝ) :
    sublevelChains 𝕜 KV FV q a = (sublevelChains 𝕜 K F q a).map (chainMap 𝕜 s) := by
  ext d
  constructor
  · intro hd
    refine ⟨fun μ ↦ d (μ.map s.toEmbedding), fun μ hμ ↦ ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hd _ hμ
      obtain ⟨σ, hσ, hσμ⟩ := (hKV _).mp h1
      obtain rfl := Finset.map_injective _ hσμ
      exact ⟨hσ, by simpa using h2, by rwa [hF] at h3⟩
    · ext ρ
      by_cases hρ : ∃ μ : Finset X, μ.map s.toEmbedding = ρ
      · obtain ⟨μ, rfl⟩ := hρ
        rw [chainMap_apply_map]
      · push Not at hρ
        rw [chainMap_apply_of_notMem 𝕜 s _ hρ]
        by_contra h
        obtain ⟨σ, -, hσ⟩ := (hKV ρ).mp (hd ρ (Ne.symm h)).1
        exact hρ σ hσ
  · rintro ⟨c, hc, rfl⟩ ρ hρ
    by_cases hρ' : ∃ μ : Finset X, μ.map s.toEmbedding = ρ
    · obtain ⟨μ, rfl⟩ := hρ'
      rw [chainMap_apply_map] at hρ
      obtain ⟨h1, h2, h3⟩ := hc μ hρ
      exact ⟨(hKV _).mpr ⟨μ, h1, rfl⟩, by simpa using h2, by rwa [hF]⟩
    · push Not at hρ'
      exact absurd (chainMap_apply_of_notMem 𝕜 s c hρ') hρ

/-- Persistent Betti numbers are invariant under an order embedding of the vertices. -/
theorem sublevelPersistentBetti_map (s : X ↪o V) {K : PreAbstractSimplicialComplex X}
    {KV : PreAbstractSimplicialComplex V}
    (hKV : ∀ ρ, ρ ∈ KV ↔ ∃ σ ∈ K, σ.map s.toEmbedding = ρ) {F : Finset X → ℝ}
    {FV : Finset V → ℝ} (hF : ∀ σ, FV (σ.map s.toEmbedding) = F σ) (p : ℕ) (a b : ℝ) :
    sublevelPersistentBetti 𝕜 KV FV p a b = sublevelPersistentBetti 𝕜 K F p a b := by
  have hT := chainMap_injective 𝕜 s
  have hZ : sublevelCycles 𝕜 KV FV p a = (sublevelCycles 𝕜 K F p a).map (chainMap 𝕜 s) := by
    unfold sublevelCycles
    rw [sublevelChains_map 𝕜 s hKV hF]
    ext d
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hd⟩
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      have hd' : simplicialBoundary 𝕜 (chainMap 𝕜 s c) = 0 := hd
      rw [simplicialBoundary_chainMap] at hd'
      exact LinearMap.mem_ker.mpr (hT (hd'.trans (map_zero _).symm))
    · rintro ⟨c, ⟨hc, hc'⟩, rfl⟩
      refine ⟨⟨c, hc, rfl⟩, ?_⟩
      have hc'' : simplicialBoundary 𝕜 c = 0 := hc'
      exact LinearMap.mem_ker.mpr (by rw [simplicialBoundary_chainMap, hc'', map_zero])
  have hB : sublevelBoundaries 𝕜 KV FV p b =
      (sublevelBoundaries 𝕜 K F p b).map (chainMap 𝕜 s) := by
    unfold sublevelBoundaries
    rw [sublevelChains_map 𝕜 s hKV hF, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun c ↦ simplicialBoundary_chainMap 𝕜 s c
  unfold sublevelPersistentBetti
  rw [hZ, hB, ← Submodule.map_inf _ hT,
    ← (Submodule.equivMapOfInjective _ hT (sublevelCycles 𝕜 K F p a)).finrank_eq,
    ← (Submodule.equivMapOfInjective _ hT _).finrank_eq]

end Relabel

section Pullback

variable {X V : Type*} [Fintype X] [LinearOrder X] [Fintype V] [LinearOrder V] (𝕜 : Type*)
  [Field 𝕜]

/-- The full simplex on a finite set `T` of vertices: all nonempty subsets of `T`. -/
def subsetComplex (T : Finset V) : PreAbstractSimplicialComplex V where
  faces := {σ | σ.Nonempty ∧ σ ⊆ T}
  isRelLowerSet_faces := fun _ hσ ↦ ⟨hσ.1, fun _ hτσ hτ ↦ ⟨hτ, hτσ.trans hσ.2⟩⟩

omit [Fintype V] [LinearOrder V] in
/-- Membership in the full simplex on a finite set of vertices. -/
theorem mem_subsetComplex {T σ : Finset V} : σ ∈ subsetComplex T ↔ σ.Nonempty ∧ σ ⊆ T := Iff.rfl

omit [Fintype V] [LinearOrder V] in
/-- Membership in the full simplex: all nonempty vertex sets. -/
theorem mem_top_complex {σ : Finset V} : σ ∈ (⊤ : PreAbstractSimplicialComplex V) ↔ σ.Nonempty :=
  Iff.rfl

/-- Pullback invariance: for a map `π` of vertices with an order-embedded section `s`, the
sublevel filtration `σ ↦ Φ (π σ)` of the full simplex on `V` has the same persistent Betti numbers
as the sublevel filtration of `Φ` on the full simplex on `X`. The vertices outside the image of `s`
are twins of vertices in the image and are removed one at a time. -/
theorem sublevelPersistentBetti_pullback (π : V → X) (s : X ↪o V) (hs : ∀ x, π (s x) = x)
    (Φ : Finset X → ℝ) (hΦ : IsMonotoneOnFaces ⊤ Φ) (p : ℕ) {a b : ℝ} (hab : a ≤ b) :
    sublevelPersistentBetti 𝕜 ⊤ (fun σ ↦ Φ (σ.image π)) p a b =
      sublevelPersistentBetti 𝕜 ⊤ Φ p a b := by
  set F : Finset V → ℝ := fun σ ↦ Φ (σ.image π)
  set S : Finset V := Finset.univ.map s.toEmbedding
  have hF : ∀ T : Finset V, IsMonotoneOnFaces (subsetComplex T) F := by
    intro T τ σ _ hτ hτσ
    exact hΦ _ _ (hτ.image π |>.mono (Finset.image_subset_image hτσ)) (hτ.image π)
      (Finset.image_subset_image hτσ)
  have hind : ∀ n : ℕ, ∀ T : Finset V, S ⊆ T → (T \ S).card = n →
      sublevelPersistentBetti 𝕜 (subsetComplex T) F p a b =
        sublevelPersistentBetti 𝕜 (subsetComplex S) F p a b := by
    intro n
    induction n with
    | zero =>
      intro T hST hn
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hn
      rw [le_antisymm hn hST]
    | succ n ih =>
      intro T hST hn
      obtain ⟨w, hw⟩ : (T \ S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨hwT, hwS⟩ := Finset.mem_sdiff.mp hw
      set v := s (π w)
      have hvS : v ∈ S := Finset.mem_map_of_mem _ (Finset.mem_univ _)
      have hvw : v ≠ w := fun h ↦ hwS (h ▸ hvS)
      rw [sublevelPersistentBetti_eq_of_twin 𝕜 (K' := subsetComplex (T.erase w)) (hF T) hvw
        (fun σ ↦ by
          simp only [mem_subsetComplex, Finset.subset_erase]
          tauto)
        (fun σ hσ hwσ ↦ by
          refine ⟨⟨Finset.insert_nonempty _ _, Finset.insert_subset (hST hvS) hσ.2⟩, ?_⟩
          simp only [F, Finset.image_insert, v, hs]
          rw [Finset.insert_eq_of_mem (Finset.mem_image_of_mem π hwσ)]) p hab]
      refine ih _ (fun x hx ↦ Finset.mem_erase.mpr ⟨fun h ↦ hwS (h ▸ hx), hST hx⟩) ?_
      rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hw]
      omega
  have htop : (⊤ : PreAbstractSimplicialComplex V) = subsetComplex Finset.univ := by
    ext σ
    exact ⟨fun h ↦ ⟨h, Finset.subset_univ _⟩, fun h ↦ h.1⟩
  rw [htop, hind _ Finset.univ (Finset.subset_univ _) rfl]
  refine sublevelPersistentBetti_map 𝕜 s (fun ρ ↦ ?_) (fun σ ↦ ?_) p a b
  · rw [mem_subsetComplex]
    constructor
    · rintro ⟨hne, hsub⟩
      obtain ⟨μ, hμ⟩ := exists_map_eq_of_subset_map s hsub
      exact ⟨μ, by rw [mem_top_complex, ← Finset.map_nonempty (f := s.toEmbedding), hμ]; exact hne,
        hμ⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨Finset.map_nonempty.mpr hμ, Finset.map_subset_map.mpr (Finset.subset_univ _)⟩
  · simp only [F]
    congr 1
    ext x
    simp [hs]

end Pullback

section Rips

/-- Diameters of the two projections of a set of pairs in a correspondence of distortion at most
`2 d` differ by at most `2 d`. -/
theorem diam_image_le_diam_image_add {X Y V Z : Type*} [MetricSpace X] [MetricSpace Y]
    [PseudoMetricSpace Z] [DecidableEq X] [DecidableEq Y] {Φ : X → Z} {Ψ : Y → Z}
    (hΦ : Isometry Φ) (hΨ : Isometry Ψ) {d : ℝ} (hd : 0 ≤ d) (πX : V → X) (πY : V → Y)
    (hR : ∀ u, dist (Φ (πX u)) (Ψ (πY u)) ≤ d) (σ : Finset V) :
    Metric.diam ((σ.image πX : Finset X) : Set X) ≤
      Metric.diam ((σ.image πY : Finset Y) : Set Y) + 2 * d := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx x' hx' ↦ ?_
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx')
  have h1 : dist (πY u) (πY u') ≤ Metric.diam ((σ.image πY : Finset Y) : Set Y) :=
    Metric.dist_le_diam_of_mem (Finset.finite_toSet _).isBounded
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu'))
  rw [← hΦ.dist_eq, ← hΨ.dist_eq] at *
  have h2 := dist_triangle4 (Φ (πX u)) (Ψ (πY u)) (Ψ (πY u')) (Φ (πX u'))
  have h3 := hR u
  have h4 := hR u'
  rw [dist_comm] at h4
  linarith

/-- The Rips filtration value of the image of a simplex under a vertex map is monotone along
faces. -/
theorem isMonotoneOnFaces_ripsFiltrationValue_image {V W : Type*} [PseudoMetricSpace W]
    [Fintype W] [LinearOrder W] [DecidableEq W] (π : V → W) :
    IsMonotoneOnFaces ⊤ fun σ : Finset V ↦ ripsFiltrationValue (σ.image π) := by
  intro τ σ _ hτ hτσ
  exact isMonotoneOnFaces_ripsFiltrationValue _ _
    (hτ.image π |>.mono (Finset.image_subset_image hτσ)) (hτ.image π)
    (Finset.image_subset_image hτσ)

/-- GAPS 108.36, for finite metric spaces: the degree-`p` persistence diagrams of the Rips
filtrations of two nonempty finite metric spaces, in the diameter-`2r` parameter, are within
bottleneck distance `d_GH(X, Y)`. In the maximum-edge parameter the filtration values double, and
the bound becomes `2 d_GH(X, Y)`. The linear orders on the points only orient simplices. Totally
bounded spaces (where `q`-tameness is needed) and the Čech variants are not formalized. -/
theorem fullBottleneckEDist_rips_le_ghDist (𝕜 : Type*) [Field 𝕜] {X Y : Type*} [MetricSpace X]
    [Fintype X] [Nonempty X] [LinearOrder X] [MetricSpace Y] [Fintype Y] [Nonempty Y]
    [LinearOrder Y] (p : ℕ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 (fullSimplexComplex X) ripsFiltrationValue p D e)
    (hE : IsSublevelDiagram 𝕜 (fullSimplexComplex Y) ripsFiltrationValue p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal (GromovHausdorff.ghDist X Y) := by
  classical
  obtain ⟨Φ, Ψ, hΦ, hΨ, hd⟩ := GromovHausdorff.ghDist_eq_hausdorffDist X Y
  set d := GromovHausdorff.ghDist X Y
  have hd0 : 0 ≤ d := hd ▸ Metric.hausdorffDist_nonneg
  have hfin : Metric.hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (finite_range _).isBounded (finite_range _).isBounded
  have hX : ∀ x, ∃ y, dist (Φ x) (Ψ y) ≤ d := by
    intro x
    obtain ⟨z, ⟨y, rfl⟩, hz⟩ :=
      (finite_range Ψ).isCompact.exists_infDist_eq_dist (range_nonempty Ψ) (Φ x)
    exact ⟨y, hz ▸ hd ▸ Metric.infDist_le_hausdorffDist_of_mem (mem_range_self x) hfin⟩
  have hY : ∀ y, ∃ x, dist (Φ x) (Ψ y) ≤ d := by
    intro y
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ :=
      (finite_range Φ).isCompact.exists_infDist_eq_dist (range_nonempty Φ) (Ψ y)
    refine ⟨x, ?_⟩
    rw [dist_comm, ← hz, hd, Metric.hausdorffDist_comm]
    exact Metric.infDist_le_hausdorffDist_of_mem (mem_range_self y)
      (by rwa [Metric.hausdorffEDist_comm])
  choose yX hyX using hX
  choose xY hxY using hY
  -- the vertices: two copies of the correspondence, ordered so that both sections are monotone
  let pr : Lex ((X ×ₗ Y) ⊕ (Y ×ₗ X)) → X × Y := fun w ↦
    match ofLex w with
    | .inl q => ofLex q
    | .inr q => ((ofLex q).2, (ofLex q).1)
  let V := {w : Lex ((X ×ₗ Y) ⊕ (Y ×ₗ X)) // dist (Φ (pr w).1) (Ψ (pr w).2) ≤ d}
  let πX : V → X := fun v ↦ (pr v.1).1
  let πY : V → Y := fun v ↦ (pr v.1).2
  let sX : X ↪o V := OrderEmbedding.ofStrictMono
    (fun x ↦ ⟨toLex (.inl (toLex (x, yX x))), hyX x⟩) fun x x' h ↦ by
      change toLex (Sum.inl (toLex (x, yX x)) : (X ×ₗ Y) ⊕ (Y ×ₗ X)) <
        toLex (Sum.inl (toLex (x', yX x')))
      rw [Sum.Lex.inl_lt_inl_iff, Prod.Lex.toLex_lt_toLex]
      exact Or.inl h
  let sY : Y ↪o V := OrderEmbedding.ofStrictMono
    (fun y ↦ ⟨toLex (.inr (toLex (y, xY y))), hxY y⟩) fun y y' h ↦ by
      change toLex (Sum.inr (toLex (y, xY y)) : (X ×ₗ Y) ⊕ (Y ×ₗ X)) <
        toLex (Sum.inr (toLex (y', xY y')))
      rw [Sum.Lex.inr_lt_inr_iff, Prod.Lex.toLex_lt_toLex]
      exact Or.inl h
  have hsX : ∀ x, πX (sX x) = x := fun x ↦ rfl
  have hsY : ∀ y, πY (sY y) = y := fun y ↦ rfl
  set f : Finset V → ℝ := fun σ ↦ ripsFiltrationValue (σ.image πX)
  set g : Finset V → ℝ := fun σ ↦ ripsFiltrationValue (σ.image πY)
  have hD' : IsSublevelDiagram 𝕜 ⊤ f p D e := fun a b hab ↦
    (sublevelPersistentBetti_pullback 𝕜 πX sX hsX ripsFiltrationValue
      isMonotoneOnFaces_ripsFiltrationValue p hab).trans (hD a b hab)
  have hE' : IsSublevelDiagram 𝕜 ⊤ g p E e' := fun a b hab ↦
    (sublevelPersistentBetti_pullback 𝕜 πY sY hsY ripsFiltrationValue
      isMonotoneOnFaces_ripsFiltrationValue p hab).trans (hE a b hab)
  have hR : ∀ u : V, dist (Φ (πX u)) (Ψ (πY u)) ≤ d := fun u ↦ u.2
  refine fullBottleneckEDist_le_of_isSublevelDiagram 𝕜 ⊤ f g (isMonotoneOnFaces_ripsFiltrationValue_image πX)
    (isMonotoneOnFaces_ripsFiltrationValue_image πY) p d
    (fun σ _ ↦ ?_) D e E e' hD' hE'
  have h1 := diam_image_le_diam_image_add hΦ hΨ hd0 πX πY hR σ
  have h2 := diam_image_le_diam_image_add hΨ hΦ hd0 πY πX
    (fun u ↦ by rw [dist_comm]; exact hR u) σ
  simp only [f, g, ripsFiltrationValue]
  rw [abs_le]
  constructor <;> linarith

end Rips

end CKSD
