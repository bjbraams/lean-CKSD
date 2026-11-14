module

public import CKSD.Geometry.SimplicialPersistence.Chains
public import CKSD.Geometry.DiagramDistances


/-!
# Stability of finite simplicial persistence diagrams

Relabeling along a common simplex order and resolving discordant pairs prove bottleneck and
Wasserstein stability. Distinct endpoint simplices control the Wasserstein cost. The Rips
filtration uses the diameter divided by two.

## Main definitions

* `CKSD.relabelDiagram`, `CKSD.discordantPairs`.
* `CKSD.ripsFiltrationValue`: the Rips filtration value `diam σ / 2`.

## Main results

* `CKSD.full_bottleneck_e_dist_le_of_is_sublevel_diagram`: bottleneck stability (GAPS 108.19).
* `CKSD.diagram_wasserstein_e_dist_le_of_is_sublevel_diagram`: Wasserstein stability (GAPS 108.35).
* `CKSD.rips_filtration_value_le_iff`: Rips filtration values and `CKSD.IsRipsSimplex`.
-/

@[expose] public section

noncomputable section

open Module Set
open scoped ENNReal NNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

section Stability

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

omit [LinearOrder ι] in
/-- If `f` is ordered by `h` on `K` (`h σ ≤ h τ → f σ ≤ f τ`), every sublevel set of `f` on `K`
is a sublevel set of `h`. -/
theorem exists_forall_le_iff_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f h : Finset ι → ℝ} (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ) (a : ℝ) :
    ∃ a', ∀ σ ∈ K, f σ ≤ a ↔ h σ ≤ a' := by
  set S := Finset.univ.filter fun σ ↦ σ ∈ K ∧ f σ ≤ a
  rcases S.eq_empty_or_nonempty with hS | hS
  · obtain ⟨M, hM⟩ := Finite.exists_ge h
    refine ⟨M - 1, fun σ hσ ↦ ⟨fun hσa ↦ ?_, fun hσt ↦ ?_⟩⟩
    · have : σ ∈ S := by simp [S, hσ, hσa]
      simp [hS] at this
    · linarith [hM σ]
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
  rw [sublevel_persistent_betti_congr_fun 𝕜 K p ha' hb', hD a' b' hab']
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
theorem full_bottleneck_e_dist_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f g h : Finset ι → ℝ} (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ)
    (hgh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → g σ ≤ g τ) (p : ℕ) {δ : ℝ}
    (hδ : ∀ σ ∈ K, |f σ - g σ| ≤ δ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    {D : FiniteDeathDiagram α} {e : κ → ℝ} {E : FiniteDeathDiagram β} {e' : κ' → ℝ}
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  obtain ⟨n, r, Dh, eh, hDh, hb, hd, he⟩ := exists_is_sublevel_diagram_and_values 𝕜 K h p
  choose sb hsbK hsb using hb
  choose sd hsdK hsd using hd
  choose se hseK hse using he
  have hDf := hDh.relabel 𝕜 hfh sb sd se hsbK hsb hsdK hsd hseK hse
  have hDg := hDh.relabel 𝕜 hgh sb sd se hsbK hsb hsdK hsd hseK hse
  have h1 : fullBottleneckEDist D e (relabelDiagram f sb sd) (fun k ↦ f (se k)) = 0 :=
    full_bottleneck_e_dist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hD a b hab, ← hDf a b hab]
  have h3 : fullBottleneckEDist (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e' = 0 :=
    full_bottleneck_e_dist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
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
        full_bottleneck_e_dist_triangle _ _ _ _ _ _
    _ ≤ 0 + (fullBottleneckEDist (relabelDiagram f sb sd) (fun k ↦ f (se k))
          (relabelDiagram g sb sd) (fun k ↦ g (se k)) +
        fullBottleneckEDist (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e') := by
        rw [h1]
        exact add_le_add le_rfl (full_bottleneck_e_dist_triangle _ _ _ _ _ _)
    _ ≤ ENNReal.ofReal δ := by rw [h3, zero_add, add_zero]; exact h2


omit [LinearOrder ι] in
/-- Pairs of simplices of `K` ordered oppositely by `f` and `g`. -/
def discordantPairs (K : PreAbstractSimplicialComplex ι) (f g : Finset ι → ℝ) :
    Finset (Finset ι × Finset ι) :=
  Finset.univ.filter fun q ↦ q.1 ∈ K ∧ q.2 ∈ K ∧ f q.1 < f q.2 ∧ g q.2 < g q.1

omit [Fintype ι] [LinearOrder ι] in
/-- A convex combination of functions monotone along faces is monotone along faces. -/
theorem IsMonotoneOnFaces.convex_comb {K : PreAbstractSimplicialComplex ι} {f g : Finset ι → ℝ}
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
theorem full_bottleneck_e_dist_le_of_card_discordant_pairs_le (K : PreAbstractSimplicialComplex ι)
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
    refine full_bottleneck_e_dist_le_of_ordered 𝕜 K (h := fun ρ ↦ f ρ + g ρ) ?_ ?_ p hδ hD hE
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
    have hm : IsMonotoneOnFaces K m := hf.convex_comb hg ht0.le ht1.le
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
    obtain ⟨n0, r0, Dm, em, hDm⟩ := exists_is_sublevel_diagram_and_values 𝕜 K m p
    have hlt1 := (Finset.card_lt_card hfm).trans_le hN
    have hlt2 := (Finset.card_lt_card hmg).trans_le hN
    calc fullBottleneckEDist D e E e'
        ≤ fullBottleneckEDist D e Dm em + fullBottleneckEDist Dm em E e' :=
          full_bottleneck_e_dist_triangle _ _ _ _ _ _
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
theorem full_bottleneck_e_dist_le_of_is_sublevel_diagram (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (δ : ℝ) (hδ : ∀ σ ∈ K, |f σ - g σ| ≤ δ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  obtain ⟨n, r, D0, e0, hD0, -⟩ := exists_is_sublevel_diagram_and_values 𝕜 K f p
  obtain ⟨n', r', E0, e0', hE0, -⟩ := exists_is_sublevel_diagram_and_values 𝕜 K g p
  have h1 : fullBottleneckEDist D e D0 e0 = 0 :=
    full_bottleneck_e_dist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hD a b hab, ← hD0 a b hab]
  have h3 : fullBottleneckEDist E0 e0' E e' = 0 :=
    full_bottleneck_e_dist_eq_zero_of_card_eq _ _ _ _ fun a b hab ↦ by
      rw [← hE0 a b hab, ← hE a b hab]
  have h2 := full_bottleneck_e_dist_le_of_card_discordant_pairs_le 𝕜 K p _ f g hf hg le_rfl δ hδ
    n r n' r' D0 e0 E0 e0' hD0 hE0
  calc fullBottleneckEDist D e E e'
      ≤ fullBottleneckEDist D e D0 e0 + fullBottleneckEDist D0 e0 E e' :=
        full_bottleneck_e_dist_triangle _ _ _ _ _ _
    _ ≤ 0 + (fullBottleneckEDist D0 e0 E0 e0' + fullBottleneckEDist E0 e0' E e') := by
        rw [h1]
        exact add_le_add le_rfl (full_bottleneck_e_dist_triangle _ _ _ _ _ _)
    _ ≤ ENNReal.ofReal δ := by rw [h3, zero_add, add_zero]; exact h2

omit [LinearOrder ι] in
/-- For `h` injective on `K`, passing from the level just below `h σ` to `h σ` adds at most the
simplex `σ`, and only in dimension `σ.card - 1`; so the image of the chains under any linear map
grows in dimension by at most one, and not at all in other dimensions. -/
theorem finrank_map_sublevel_chains_le (K : PreAbstractSimplicialComplex ι) {h : Finset ι → ℝ}
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
theorem sublevel_cycles_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {a a' : ℝ} (h : a ≤ a') : sublevelCycles 𝕜 K f p a ≤ sublevelCycles 𝕜 K f p a' :=
  inf_le_inf_right _ (sublevel_chains_mono 𝕜 K f p h)

/-- Boundaries grow with the level. -/
theorem sublevel_boundaries_mono (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {b b' : ℝ} (h : b ≤ b') : sublevelBoundaries 𝕜 K f p b ≤ sublevelBoundaries 𝕜 K f p b' :=
  Submodule.map_mono (sublevel_chains_mono 𝕜 K f (p + 1) h)

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
  have hc1 := sublevel_persistent_betti_cast 𝕜 K h p x x
  have hc2 := sublevel_persistent_betti_cast 𝕜 K h p x' x
  have hZ := sublevel_cycles_mono 𝕜 K h p hx'x.le
  have I1 := finrank_add_finrank_inf_le (U := sublevelBoundaries 𝕜 K h p x) hZ
  have I1' := Submodule.finrank_mono (inf_le_inf_right (sublevelBoundaries 𝕜 K h p x) hZ)
  have I2 := finrank_add_finrank_inf_le (U := LinearMap.ker (simplicialBoundary 𝕜))
    (sublevel_chains_mono 𝕜 K h p hx'x.le)
  have I3 := finrank_map_sublevel_chains_le 𝕜 K hinj LinearMap.id p hσ hK
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
  have hc1 := sublevel_persistent_betti_cast 𝕜 K h p y' y'
  have hc2 := sublevel_persistent_betti_cast 𝕜 K h p y' y
  have hB := sublevel_boundaries_mono 𝕜 K h p hy'y.le
  have I1 := finrank_add_finrank_inf_le (U := sublevelCycles 𝕜 K h p y') hB
  rw [inf_comm (sublevelBoundaries 𝕜 K h p y), inf_comm (sublevelBoundaries 𝕜 K h p y')] at I1
  have I3 := finrank_map_sublevel_chains_le 𝕜 K hinj (simplicialBoundary 𝕜) (p + 1) hσ hK
  rw [← hydef] at I3
  unfold sublevelBoundaries at hc1 hc2 hB I1
  split_ifs at I3 ⊢ <;> omega

/-- Diagrams related by bijections preserving all points are at `q`-Wasserstein distance zero. -/
theorem diagram_wasserstein_e_dist_eq_zero_of_equiv {α β κ κ' : Type*} [Fintype α] [Fintype β]
    [Fintype κ] {q : ℝ} (hq : 0 < q) {D : FiniteDeathDiagram α} {e : κ → ℝ}
    {E : FiniteDeathDiagram β} {e' : κ' → ℝ} (σ : α ≃ β)
    (hσ : ∀ i, E.birth (σ i) = D.birth i ∧ E.death (σ i) = D.death i) (τ : κ ≃ κ')
    (hτ : ∀ k, e' (τ k) = e k) : diagramWassersteinEDist q D e E e' = 0 := by
  let M : DiagramMatching α β :=
    { relates := fun i j ↦ j = σ i
      left_unique := fun i j k hj hk ↦ hj.trans hk.symm
      right_unique := fun i j k hi hj ↦ σ.injective (hi.symm.trans hj) }
  refine le_antisymm ((iInf_le_of_le M (iInf_le _ τ)).trans (le_of_eq ?_)) bot_le
  rw [diagram_wasserstein_cost_eq]
  have h1 : ∀ i, M.leftCost D E i = 0 := fun i ↦ by
    rw [M.left_cost_of_relates D E (j := σ i) rfl, (hσ i).1, (hσ i).2]
    simp
  have h2 : ∀ j, M.rightCost E j = 0 := fun j ↦
    M.right_cost_of_relates E (i := σ.symm j) (by simp [M])
  simp [h1, h2, hτ, ENNReal.zero_rpow_of_pos hq, hq]

/-- Diagrams of the same function are at `q`-Wasserstein distance zero. -/
theorem diagram_wasserstein_e_dist_eq_zero_of_is_sublevel_diagram {K : PreAbstractSimplicialComplex ι}
    {f : Finset ι → ℝ} {p : ℕ} {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [Fintype κ'] {q : ℝ} (hq : 0 < q) {D : FiniteDeathDiagram α} {e : κ → ℝ}
    {E : FiniteDeathDiagram β} {e' : κ' → ℝ} (hD : IsSublevelDiagram 𝕜 K f p D e)
    (hE : IsSublevelDiagram 𝕜 K f p E e') : diagramWassersteinEDist q D e E e' = 0 := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_equiv_of_card_eq D e E e' fun a b hab ↦ by
    rw [← hD a b hab, ← hE a b hab]
  exact diagram_wasserstein_e_dist_eq_zero_of_equiv hq σ hσ τ hτ

/-- `q`-Wasserstein stability when the two functions are ordered by a common function `h` that is
injective on `K`. The bars of the diagram of `h` have distinct endpoint simplices, and matching
the relabelled bars with the same label costs at most `∑_{σ ∈ K} |f σ - g σ|^q`. -/
theorem diagram_wasserstein_e_dist_le_of_ordered (K : PreAbstractSimplicialComplex ι)
    {f g h : Finset ι → ℝ} (hinj : ∀ σ ∈ K, ∀ τ ∈ K, h σ = h τ → σ = τ)
    (hfh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → f σ ≤ f τ)
    (hgh : ∀ σ ∈ K, ∀ τ ∈ K, h σ ≤ h τ → g σ ≤ g τ) (p : ℕ) {q : ℝ} (hq : 1 ≤ q)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    {D : FiniteDeathDiagram α} {e : κ → ℝ} {E : FiniteDeathDiagram β} {e' : κ' → ℝ}
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    diagramWassersteinEDist q D e E e' ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, r, Dh, eh, hDh, hb, hd, he⟩ := exists_is_sublevel_diagram_and_values 𝕜 K h p
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
  have h1 := diagram_wasserstein_e_dist_eq_zero_of_is_sublevel_diagram 𝕜 hq0 hD hDf
  have h3 := diagram_wasserstein_e_dist_eq_zero_of_is_sublevel_diagram 𝕜 hq0 hDg hE
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
  have hL : ∀ x, M.leftCost (relabelDiagram f sb sd) (relabelDiagram g sb sd) x ^ q ≤ U x.1 := by
    rintro ⟨i, hi⟩
    refine le_trans (ENNReal.rpow_le_rpow ?_ hq0.le) (hW i)
    by_cases hgi : g (sb i) < g (sd i)
    · rw [M.left_cost_of_relates _ _ (j := ⟨i, hgi⟩) rfl]
      rfl
    · have hnot : ¬ ∃ y, M.relates ⟨i, hi⟩ y := fun ⟨y, hy⟩ ↦ hgi (by
        have := y.2; rw [← show i = y.1 from hy] at this; exact this)
      rw [M.left_cost_of_not _ _ hnot]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := le_max_left |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h3 := le_max_right |f (sb i) - g (sb i)| |f (sd i) - g (sd i)|
      have h4 := neg_abs_le (f (sb i) - g (sb i))
      have h5 := le_abs_self (f (sd i) - g (sd i))
      simp only [relabelDiagram]
      linarith [not_lt.mp hgi]
  have hR : ∀ y, M.rightCost (relabelDiagram g sb sd) y ^ q ≤
      if f (sb y.1) < f (sd y.1) then 0 else U y.1 := by
    rintro ⟨i, hi⟩
    by_cases hfi : f (sb i) < f (sd i)
    · rw [M.right_cost_of_relates _ (i := ⟨i, hfi⟩) rfl, ite_eq_left hfi,
        ENNReal.zero_rpow_of_pos hq0]
    · have hnot : ¬ ∃ x, M.relates x ⟨i, hi⟩ := fun ⟨x, hx⟩ ↦ hfi (by
        have := x.2; rw [show x.1 = i from hx] at this; exact this)
      rw [M.right_cost_of_not _ hnot, ite_eq_right hfi]
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
    rw [diagram_wasserstein_cost_eq]
    have hA : ∑ x, M.leftCost (relabelDiagram f sb sd) (relabelDiagram g sb sd) x ^ q +
        ∑ y, M.rightCost (relabelDiagram g sb sd) y ^ q ≤ ∑ i, U i := by
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
        diagram_wasserstein_e_dist_triangle hq _ _ _ _ _ _
    _ ≤ 0 + (diagramWassersteinEDist q (relabelDiagram f sb sd) (fun k ↦ f (se k))
          (relabelDiagram g sb sd) (fun k ↦ g (se k)) +
        diagramWassersteinEDist q (relabelDiagram g sb sd) (fun k ↦ g (se k)) E e') := by
        rw [h1]
        exact add_le_add le_rfl (diagram_wasserstein_e_dist_triangle hq _ _ _ _ _ _)
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
theorem diagram_wasserstein_e_dist_le_of_card_discordant_pairs_le (K : PreAbstractSimplicialComplex ι)
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
    refine diagram_wasserstein_e_dist_le_of_ordered 𝕜 K hinj ?_ ?_ p hq hD hE
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
    have hm : IsMonotoneOnFaces K m := hf.convex_comb hg ht0.le ht1.le
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
    obtain ⟨n0, r0, Dm, em, hDm⟩ := exists_is_sublevel_diagram_and_values 𝕜 K m p
    have hlt1 := (Finset.card_lt_card hfm).trans_le hN
    have hlt2 := (Finset.card_lt_card hmg).trans_le hN
    calc diagramWassersteinEDist q D e E e'
        ≤ diagramWassersteinEDist q D e Dm em + diagramWassersteinEDist q Dm em E e' :=
          diagram_wasserstein_e_dist_triangle hq _ _ _ _ _ _
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
theorem diagram_wasserstein_e_dist_le_of_is_sublevel_diagram
    (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (q : ℝ) (hq : 1 ≤ q)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    diagramWassersteinEDist q D e E e' ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, r, D0, e0, hD0, -⟩ := exists_is_sublevel_diagram_and_values 𝕜 K f p
  obtain ⟨n', r', E0, e0', hE0, -⟩ := exists_is_sublevel_diagram_and_values 𝕜 K g p
  have h1 := diagram_wasserstein_e_dist_eq_zero_of_is_sublevel_diagram 𝕜 hq0 hD hD0
  have h3 := diagram_wasserstein_e_dist_eq_zero_of_is_sublevel_diagram 𝕜 hq0 hE0 hE
  have h2 := diagram_wasserstein_e_dist_le_of_card_discordant_pairs_le 𝕜 K p hq _ f g hf hg le_rfl
    n r n' r' D0 e0 E0 e0' hD0 hE0
  calc diagramWassersteinEDist q D e E e'
      ≤ diagramWassersteinEDist q D e D0 e0 + diagramWassersteinEDist q D0 e0 E e' :=
        diagram_wasserstein_e_dist_triangle hq _ _ _ _ _ _
    _ ≤ 0 + (diagramWassersteinEDist q D0 e0 E0 e0' + diagramWassersteinEDist q E0 e0' E e') := by
        rw [h1]
        exact add_le_add le_rfl (diagram_wasserstein_e_dist_triangle hq _ _ _ _ _ _)
    _ ≤ _ := by rw [h3, zero_add, add_zero]; exact h2

/-- The Rips filtration value of a simplex in the diameter-`2r` convention: `σ ∈ Rips(r)` exactly
when `diam σ ≤ 2r`. -/
def ripsFiltrationValue {X : Type*} [PseudoMetricSpace X] (σ : Finset X) : ℝ :=
  Metric.diam (σ : Set X) / 2

/-- Diameters are monotone, so the Rips filtration is a monotone filtration of the full simplex. -/
theorem is_monotone_on_faces_rips_filtration_value {X : Type*} [PseudoMetricSpace X] :
    IsMonotoneOnFaces (⊤ : PreAbstractSimplicialComplex X) (ripsFiltrationValue (X := X)) := by
  intro τ σ _ _ hτσ
  unfold ripsFiltrationValue
  gcongr
  exact Metric.diam_mono (by exact_mod_cast hτσ) σ.finite_toSet.isBounded

/-- A nonempty simplex has Rips filtration value at most `r` exactly when it is a Rips simplex of
parameter `r`, that is, when all its pairwise distances are at most `2r`. -/
theorem rips_filtration_value_le_iff {X : Type*} [PseudoMetricSpace X] {σ : Finset X}
    (hσ : σ.Nonempty) {r : ℝ} : ripsFiltrationValue σ ≤ r ↔ IsRipsSimplex r σ := by
  unfold ripsFiltrationValue IsRipsSimplex
  rw [div_le_iff₀ two_pos, mul_comm]
  refine ⟨fun h x hx y hy ↦ (Metric.dist_le_diam_of_mem σ.finite_toSet.isBounded
    (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy)).trans h, fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := hσ
  exact Metric.diam_le_of_forall_dist_le (by linarith [h x hx x hx, dist_self x])
    fun x hx y hy ↦ h x hx y hy

end Stability

end CKSD
