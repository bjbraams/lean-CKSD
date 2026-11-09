module

public import CKSD.Asymptotics.Basic

/-!
# The Hájek projection of a U-statistic

For an iid sample from `P` and a symmetric square-integrable kernel `h` of order `m + 1` with mean
`θ` and first projection `g(x) = E h(x, X₂, …, X_{m+1}) - θ`, the remainder
`Uₙ - θ - ((m + 1)/n) ∑ᵢ g(Xᵢ)` of the Hájek projection has second moment `O(n⁻²)`. This is
the analytic core of the central limit theorem for U-statistics (GAPS 102.8).

The remainder is the U-statistic of the kernel `r(z) = h(z) - θ - ∑ⱼ g(zⱼ)`, all of whose
one-coordinate conditional means vanish. Two terms `r(x ∘ f)` and `r(x ∘ f')` whose index sets
share at most one index are orthogonal: integrate out the coordinates of `f` other than the shared
one (Mathlib's `measurePreserving_piEquivPiSubtypeProd` and `measurePreserving_piCongrLeft`).
At most `(n)ₖ k³ (k - 1) n^(k-2)` ordered pairs of injections share two indices, which gives the
bound.

## Main results

* `CKSD.uStatistic_projection_spec`: measurability, square integrability and centring of `g`.
* `CKSD.memLp_uStatistic_sub_projection` and
  `CKSD.exists_integral_sq_uStatistic_sub_projection_le`: the remainder is square integrable with
  second moment at most `C / n²` for `n ≥ 2 (m + 1)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-! ### Counting injections -/

/-- The number of injections `Fin k → Fin n` is the descending factorial. -/
private theorem card_filter_injective_fin (k n : ℕ) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective).card =
      n.descFactorial k := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- Each index `i` is the `j`-th value of the same number of injections. -/
private theorem card_injective_apply_eq (k n : ℕ) (j : Fin k) (i i' : Fin n) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter
        (fun f ↦ Function.Injective f ∧ f j = i)).card =
      ((Finset.univ : Finset (Fin k → Fin n)).filter
        (fun f ↦ Function.Injective f ∧ f j = i')).card := by
  refine Finset.card_bij (fun f _ ↦ Equiv.swap i i' ∘ f) (fun f hf ↦ ?_)
    (fun f _ f' _ hff' ↦ ?_) (fun f hf ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨(Equiv.injective _).comp hf.1, by simp [hf.2]⟩
  · funext x; exact (Equiv.injective _) (congrFun hff' x)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    refine ⟨Equiv.swap i i' ∘ f, ⟨(Equiv.injective _).comp hf.1, by simp [hf.2]⟩, ?_⟩
    funext x; simp

/-- Summing a one-coordinate function over all coordinates of all injections:
`n ∑_f ∑_j φ (f j) = k (n)_k ∑_i φ i`. -/
private theorem natCast_mul_sum_injective_sum_apply (k n : ℕ) (φ : Fin n → ℝ) :
    (n : ℝ) * ∑ f ∈ (Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective,
        ∑ j, φ (f j) = k * n.descFactorial k * ∑ i, φ i := by
  set I := (Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective
  set c : Fin k → Fin n → ℕ := fun j i ↦
    ((Finset.univ : Finset (Fin k → Fin n)).filter (fun f ↦ Function.Injective f ∧ f j = i)).card
  have hsum : ∀ j, ∑ f ∈ I, φ (f j) = ∑ i, (c j i : ℝ) * φ i := by
    intro j
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun f ↦ f j) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_congr rfl (fun f hf ↦ by rw [(Finset.mem_filter.1 hf).2]), Finset.sum_const,
      nsmul_eq_mul, Finset.filter_filter]
  have hc : ∀ j i, (n : ℝ) * c j i = n.descFactorial k := by
    intro j i
    have htot : ∑ i', c j i' = n.descFactorial k := by
      rw [← card_filter_injective_fin k n]
      simp only [c, ← Finset.filter_filter]
      exact (Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)).symm
    have : ∑ i', c j i' = n * c j i := by
      rw [Finset.sum_congr rfl fun i' _ ↦ card_injective_apply_eq k n j i' i, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact_mod_cast this.symm.trans htot
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [hsum, Finset.mul_sum, ← mul_assoc, hc]
  simp [Finset.sum_const, Finset.mul_sum, mul_assoc]

/-- At most `k² n^(k-2)` maps `Fin k → Fin n` send two given distinct coordinates into a set of
at most `k` elements. -/
private theorem card_filter_apply_mem_apply_mem_le {k n : ℕ} (R : Finset (Fin n))
    (hR : R.card ≤ k)
    {a b : Fin k} (hab : a ≠ b) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter (fun f' ↦ f' a ∈ R ∧ f' b ∈ R)).card ≤
      k ^ 2 * n ^ (k - 2) := by
  set t : Fin k → Finset (Fin n) := fun j ↦ if j = a ∨ j = b then R else Finset.univ
  have heq : (Finset.univ : Finset (Fin k → Fin n)).filter (fun f' ↦ f' a ∈ R ∧ f' b ∈ R) =
      Fintype.piFinset t := by
    ext f'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, t]
    constructor
    · rintro ⟨ha, hb⟩ j
      split_ifs with h
      · rcases h with rfl | rfl <;> assumption
      · exact Finset.mem_univ _
    · intro h
      exact ⟨by simpa using h a, by simpa using h b⟩
  rw [heq, Fintype.card_piFinset]
  simp only [t, apply_ite Finset.card, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h2 : ((Finset.univ : Finset (Fin k)).filter (fun j ↦ j = a ∨ j = b)).card = 2 := by
    rw [show (Finset.univ : Finset (Fin k)).filter (fun j ↦ j = a ∨ j = b) = {a, b} by
      ext; simp]
    exact Finset.card_pair hab
  have h3 : ((Finset.univ : Finset (Fin k)).filter (fun j ↦ ¬(j = a ∨ j = b))).card = k - 2 := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), h2,
      Finset.card_univ, Fintype.card_fin]
  rw [h2, h3]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hR 2)

/-- For a fixed `f : Fin k → Fin n`, at most `k³ (k - 1) n^(k-2)` maps `f'` have two distinct
coordinates with values in the range of `f`. -/
private theorem card_filter_two_apply_mem_range_le {k n : ℕ} (f : Fin k → Fin n) :
    ((Finset.univ : Finset (Fin k → Fin n)).filter
        (fun f' ↦ ∃ a b, a ≠ b ∧ f' a ∈ range f ∧ f' b ∈ range f)).card ≤
      k ^ 3 * (k - 1) * n ^ (k - 2) := by
  set R := Finset.univ.image f
  have hR : R.card ≤ k := Finset.card_image_le.trans (by simp)
  have hsub : (Finset.univ : Finset (Fin k → Fin n)).filter
      (fun f' ↦ ∃ a b, a ≠ b ∧ f' a ∈ range f ∧ f' b ∈ range f) ⊆
      ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p ↦ p.1 ≠ p.2)).biUnion
        (fun p ↦ (Finset.univ : Finset (Fin k → Fin n)).filter
          (fun f' ↦ f' p.1 ∈ R ∧ f' p.2 ∈ R)) := by
    intro f' hf'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf'
    obtain ⟨a, b, hab, ha, hb⟩ := hf'
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
    refine ⟨a, b, hab, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := ha; exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    · obtain ⟨j, hj⟩ := hb; exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum fun p hp ↦ card_filter_apply_mem_apply_mem_le R hR
    (Finset.mem_filter.1 hp).2).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have : ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p ↦ p.1 ≠ p.2)).card =
      k * (k - 1) := by
    rw [show (Finset.univ : Finset (Fin k × Fin k)).filter (fun p ↦ p.1 ≠ p.2) =
      (Finset.univ : Finset (Fin k)).offDiag by ext; simp, Finset.offDiag_card,
      Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  rw [this]
  calc k * (k - 1) * (k ^ 2 * n ^ (k - 2)) = k ^ 3 * (k - 1) * n ^ (k - 2) := by ring
    _ ≤ _ := le_rfl

/-! ### Orthogonality of degenerate kernel terms -/

section Measure

variable {E : Type*} [MeasurableSpace E]


/-- Reindexing an iid product measure along an injection `f : Fin k → Fin n` gives the iid
product measure: `x ↦ x ∘ f` maps `Pⁿ` to `Pᵏ`. -/
private theorem measurePreserving_pi_comp_injective (P : Measure E) [IsProbabilityMeasure P] {k n : ℕ}
    {f : Fin k → Fin n} (hf : Function.Injective f) :
    MeasurePreserving (fun x : Fin n → E ↦ x ∘ f) (Measure.pi fun _ ↦ P)
      (Measure.pi fun _ ↦ P) := by
  have hind : iIndepFun (fun (j : Fin k) (x : Fin n → E) ↦ x (f j)) (Measure.pi fun _ ↦ P) :=
    (iIndepFun_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ id)
      (fun _ ↦ aemeasurable_id)).precomp hf
  refine ⟨by fun_prop, ?_⟩
  have := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j ↦ (measurable_pi_apply (f j)).aemeasurable)).1 hind
  change Measure.map (fun (ω : Fin n → E) (i : Fin k) ↦ ω (f i)) _ = _
  rw [this]
  congr 1
  funext j
  exact (measurePreserving_eval _ (f j)).map_eq

/-- If `G` does not depend on the coordinates in `p` and the integral of `F` over these
coordinates vanishes for almost every value of the others, then `∫ F G dPⁿ = 0`. -/
private theorem integral_mul_eq_zero_of_slice (P : Measure E) [IsProbabilityMeasure P] {n : ℕ}
    (p : Fin n → Prop) [DecidablePred p] (F G : (Fin n → E) → ℝ)
    (hF : MemLp F 2 (Measure.pi fun _ ↦ P)) (hG : MemLp G 2 (Measure.pi fun _ ↦ P))
    (hGp : ∀ x y : Fin n → E, (∀ l, ¬ p l → x l = y l) → G x = G y)
    (hFp : ∀ᵐ w ∂(Measure.pi fun _ : {l // ¬ p l} ↦ P),
      ∫ u, F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ E) p).symm (u, w))
        ∂(Measure.pi fun _ : {l // p l} ↦ P) = 0) :
    ∫ x, F x * G x ∂(Measure.pi fun _ ↦ P) = 0 := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ E) p
  have hes := (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n ↦ P) p).symm e
  have hint : Integrable (fun x ↦ F x * G x) (Measure.pi fun _ ↦ P) := hF.integrable_mul hG
  rw [← hes.integral_comp' (fun x ↦ F x * G x)]
  rw [integral_prod_symm (fun z ↦ F (e.symm z) * G (e.symm z))
    (hes.integrable_comp_of_integrable hint)]
  refine integral_eq_zero_of_ae ?_
  obtain ⟨a⟩ := nonempty_of_isProbabilityMeasure P
  filter_upwards [hFp] with w hw
  have hGc : ∀ u, G (e.symm (u, w)) = G (e.symm (fun _ ↦ a, w)) := fun u ↦
    hGp _ _ fun l hl ↦ by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hl]
  simp_rw [hGc]
  rw [integral_mul_const, hw, zero_mul]
  rfl

/-- Terms `r(x ∘ f)` and `r(x ∘ f')` of a degenerate kernel are orthogonal when the injections
`f` and `f'` share at most one index: integrate out the other coordinates of `f`. -/
private theorem integral_kernel_mul_kernel_eq_zero (P : Measure E) [IsProbabilityMeasure P]
    {m n : ℕ} (r : (Fin (m + 1) → E) → ℝ) (hr : MemLp r 2 (Measure.pi fun _ ↦ P))
    (hdeg : ∀ j₀ : Fin (m + 1), ∀ᵐ a ∂P,
      ∫ z, r (j₀.insertNth a z) ∂(Measure.pi fun _ : Fin m ↦ P) = 0)
    {f f' : Fin (m + 1) → Fin n} (hf : Function.Injective f) (hf' : Function.Injective f')
    (hov : ∀ a b, f' a ∈ range f → f' b ∈ range f → a = b) :
    ∫ x, r (x ∘ f) * r (x ∘ f') ∂(Measure.pi fun _ ↦ P) = 0 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ j, f' j ∈ range f → f' j = f j₀ := by
    by_cases hex : ∃ a, f' a ∈ range f
    · obtain ⟨a, j₀, hj₀⟩ := hex
      exact ⟨j₀, fun j hj ↦ by rw [hov j a hj ⟨j₀, hj₀⟩, hj₀]⟩
    · push Not at hex
      exact ⟨0, fun j hj ↦ (hex j hj).elim⟩
  set p : Fin n → Prop := fun l ↦ ∃ j', f (j₀.succAbove j') = l with hp
  have hnp : ¬ p (f j₀) := fun ⟨j', hj'⟩ ↦ Fin.succAbove_ne j₀ j' (hf hj')
  have hlaw := measurePreserving_pi_comp_injective P hf
  have hlaw' := measurePreserving_pi_comp_injective P hf'
  refine integral_mul_eq_zero_of_slice P p _ _ (hr.comp_measurePreserving hlaw)
    (hr.comp_measurePreserving hlaw') (fun x y hxy ↦ ?_) ?_
  · congr 1
    funext j
    refine hxy _ fun ⟨j', hj'⟩ ↦ Fin.succAbove_ne j₀ j' (hf ?_)
    rw [hj', hj₀ j ⟨_, hj'⟩]
  -- the slice integral
  set τ : Fin m ≃ {l // p l} := Equiv.ofBijective (fun j' ↦ ⟨f (j₀.succAbove j'), j', rfl⟩)
    ⟨fun a b hab ↦ Fin.succAbove_right_injective (hf (congrArg Subtype.val hab)),
      fun ⟨l, j', hj'⟩ ↦ ⟨j', Subtype.ext hj'⟩⟩ with hτ
  have hτp := measurePreserving_piCongrLeft (fun _ : {l // p l} ↦ P) τ
  have hev := (measurePreserving_eval (fun _ : {l // ¬ p l} ↦ P)
    ⟨f j₀, hnp⟩).quasiMeasurePreserving.ae (hdeg j₀)
  filter_upwards [hev] with w hw
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ E) p
  have hcomp : ∀ u, (e.symm (u, w)) ∘ f = j₀.insertNth (w ⟨f j₀, hnp⟩) (fun j' ↦ u (τ j')) := by
    intro u
    funext j
    refine Fin.succAboveCases j₀ ?_ (fun j' ↦ ?_) j
    · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hnp]
    · have hpj : p (f (j₀.succAbove j')) := ⟨j', rfl⟩
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hpj]
      rfl
  simp_rw [hcomp]
  rw [← hτp.integral_comp' (fun u ↦ r (j₀.insertNth (w ⟨f j₀, hnp⟩) (fun j' ↦ u (τ j'))))]
  convert hw using 3 with z
  congr 1
  funext j'
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]

/-- Integrating out the second variable of a square-integrable function on a product of
probability spaces gives a square-integrable function of the first variable (Jensen). -/
private theorem memLp_integral_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : α × β → ℝ) (hm : Measurable H) (h2 : MemLp H 2 (μ.prod ν)) :
    MemLp (fun a ↦ ∫ y, H (a, y) ∂ν) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable).2
  have hb := h2.integrable_sq.integral_prod_left
  apply hb.mono' (hm.stronglyMeasurable.integral_prod_right'.pow 2).aestronglyMeasurable
  filter_upwards [h2.integrable_sq.prod_right_ae] with x hx
  have hx2 : MemLp (fun y ↦ H (x, y)) 2 ν :=
    (memLp_two_iff_integrable_sq (hm.comp measurable_prodMk_left).aestronglyMeasurable).2 hx
  have hv := ProbabilityTheory.variance_nonneg (fun y ↦ H (x, y)) ν
  rw [ProbabilityTheory.variance_eq_sub hx2] at hv
  simp only [Pi.pow_apply] at hv ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith


/-- The first projection `g(a) = ∫ h(a, y) dPᵐ(y) - θ` of a square-integrable kernel is
measurable, square integrable and centred, and `y ↦ h(a, y)` is integrable for almost every `a`. -/
theorem uStatistic_projection_spec (P : Measure E) [IsProbabilityMeasure P] {m : ℕ}
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) (θ : ℝ)
    (hθ : θ = ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P)) (g : E → ℝ)
    (hg : ∀ a, g a = (∫ y, h (Fin.cases a y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ) :
    Measurable g ∧ MemLp g 2 P ∧ ∫ a, g a ∂P = 0 ∧
      ∀ᵐ a ∂P, Integrable (fun y ↦ h (Fin.cons a y)) (Measure.pi fun _ : Fin m ↦ P) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ E) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ P) 0
  have hes := he.symm e
  set H : E × (Fin m → E) → ℝ := fun p ↦ h (Fin.cons p.1 p.2) with hH
  have hHe : H = h ∘ e.symm := by
    funext p
    simp [H, e, MeasurableEquiv.piFinSuccAbove]
  have hHm : Measurable H := by rw [hHe]; exact hmeas.comp e.symm.measurable
  have hH2 : MemLp H 2 (P.prod (Measure.pi fun _ : Fin m ↦ P)) := by
    rw [hHe]; exact h2.comp_measurePreserving hes
  have hgeq : g = fun a ↦ (∫ y, H (a, y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ := funext hg
  have hHi := hH2.integrable one_le_two
  refine ⟨?_, ?_, ?_, hHi.prod_right_ae⟩
  · rw [hgeq]
    exact (hHm.stronglyMeasurable.integral_prod_right'.measurable).sub_const _
  · rw [hgeq]
    exact (memLp_integral_prod_right _ _ H hHm hH2).sub (memLp_const θ)
  · rw [hgeq, integral_sub hHi.integral_prod_left (integrable_const θ), ← integral_prod _ hHi,
      hHe]
    change (∫ z, h (e.symm z) ∂_) - _ = 0
    rw [hes.integral_comp' (g := h), ← hθ]
    simp

/-- The kernel `r(z) = h(z) - θ - ∑ⱼ g(zⱼ)` of a symmetric kernel `h` is square integrable and
degenerate: integrating out all coordinates but any one gives `0` almost everywhere. -/
private theorem uStatistic_degenerateKernel_spec (P : Measure E) [IsProbabilityMeasure P] {m : ℕ}
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) (θ : ℝ)
    (hθ : θ = ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P)) (g : E → ℝ)
    (hg : ∀ a, g a = (∫ y, h (Fin.cases a y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ) :
    MemLp (fun z ↦ h z - θ - ∑ j, g (z j)) 2 (Measure.pi fun _ : Fin (m + 1) ↦ P) ∧
      ∀ j₀ : Fin (m + 1), ∀ᵐ a ∂P,
        ∫ z, (fun z ↦ h z - θ - ∑ j, g (z j)) (j₀.insertNth a z)
          ∂(Measure.pi fun _ : Fin m ↦ P) = 0 := by
  obtain ⟨hgm, hg2, hg0, hint⟩ := uStatistic_projection_spec P h hmeas h2 θ hθ g hg
  refine ⟨(h2.sub (memLp_const θ)).sub (memLp_finsetSum _ fun j _ ↦
    hg2.comp_measurePreserving (measurePreserving_eval _ j)), fun j₀ ↦ ?_⟩
  filter_upwards [hint] with a ha
  have hgi : ∀ j' : Fin m, Integrable (fun z : Fin m → E ↦ g (z j'))
      (Measure.pi fun _ : Fin m ↦ P) := fun j' ↦
    (hg2.comp_measurePreserving (measurePreserving_eval _ j')).integrable one_le_two
  have hgz : ∀ j' : Fin m, ∫ z, g (z j') ∂(Measure.pi fun _ : Fin m ↦ P) = 0 := fun j' ↦ by
    have hmap := integral_map (μ := Measure.pi fun _ : Fin m ↦ P)
      (measurable_pi_apply j').aemeasurable (f := g)
      (by rw [(measurePreserving_eval (fun _ : Fin m ↦ P) j').map_eq]
          exact hgm.aestronglyMeasurable)
    rw [(measurePreserving_eval (fun _ : Fin m ↦ P) j').map_eq, hg0] at hmap
    exact hmap.symm
  have hpt : ∀ z : Fin m → E, h (j₀.insertNth a z) - θ -
      ∑ j, g ((j₀.insertNth a z : Fin (m + 1) → E) j) =
      (h (Fin.cons a z) - θ - g a) - ∑ j', g (z j') := by
    intro z
    rw [← Fin.insertNth_comp_cycleRange_symm j₀ a z, hsym, Fin.sum_univ_succAbove _ j₀]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring
  simp_rw [hpt]
  have hA : Integrable (fun z : Fin m → E ↦ h (Fin.cons a z) - θ - g a)
      (Measure.pi fun _ : Fin m ↦ P) := (ha.sub (integrable_const θ)).sub (integrable_const _)
  have hB : Integrable (fun z : Fin m → E ↦ ∑ j', g (z j')) (Measure.pi fun _ : Fin m ↦ P) :=
    integrable_finsetSum _ fun j' _ ↦ hgi j'
  have hA' : Integrable (fun z : Fin m → E ↦ h (Fin.cons a z) - θ)
      (Measure.pi fun _ : Fin m ↦ P) := ha.sub (integrable_const θ)
  rw [integral_sub hA hB, integral_finsetSum _ fun j' _ ↦ hgi j',
    Finset.sum_eq_zero fun j' _ ↦ hgz j', integral_sub hA' (integrable_const _),
    integral_sub ha (integrable_const θ), hg a]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ y, h (Fin.cons a y) ∂_) - θ - ((∫ y, h (Fin.cons a y) ∂_) - θ) - 0 = 0
  ring

end Measure

/-! ### The second moment of the remainder -/

/-- The remainder of the Hájek projection is the U-statistic of the kernel
`h(z) - θ - ∑ⱼ g(zⱼ)`. -/
theorem uStatistic_sub_projection_eq {E : Type*} {k n : ℕ} (hkn : k ≤ n) (hk : 0 < k)
    (h : (Fin k → E) → ℝ) (θ : ℝ) (g : E → ℝ) (x : Fin n → E) :
    uStatistic k n h x - θ - ((k : ℝ) / n) * ∑ i, g (x i) =
      ((n.descFactorial k : ℕ) : ℝ)⁻¹ *
        ∑ f ∈ (Finset.univ : Finset (Fin k → Fin n)).filter Function.Injective,
          (h (x ∘ f) - θ - ∑ j, g (x (f j))) := by
  have hD : ((n.descFactorial k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hkn))
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hS := natCast_mul_sum_injective_sum_apply k n (fun i ↦ g (x i))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    card_filter_injective_fin, nsmul_eq_mul, uStatistic]
  field_simp
  linear_combination hS

section Measure

variable {E : Type*} [MeasurableSpace E]

/-- The second moment of a sum of degenerate kernel terms over the injections: only the pairs of
injections sharing at least two indices contribute, each at most `∫ r²`. -/
private theorem integral_sq_sum_kernel_le (P : Measure E) [IsProbabilityMeasure P] {m n : ℕ}
    (r : (Fin (m + 1) → E) → ℝ) (hr : MemLp r 2 (Measure.pi fun _ ↦ P))
    (hdeg : ∀ j₀ : Fin (m + 1), ∀ᵐ a ∂P,
      ∫ z, r (j₀.insertNth a z) ∂(Measure.pi fun _ : Fin m ↦ P) = 0) :
    ∫ x, (∑ f ∈ (Finset.univ : Finset (Fin (m + 1) → Fin n)).filter Function.Injective,
        r (x ∘ f)) ^ 2 ∂(Measure.pi fun _ ↦ P) ≤
      n.descFactorial (m + 1) * ((m + 1) ^ 3 * m * n ^ (m + 1 - 2)) *
        ∫ z, r z ^ 2 ∂(Measure.pi fun _ ↦ P) := by
  set I := (Finset.univ : Finset (Fin (m + 1) → Fin n)).filter Function.Injective
  set V := ∫ z, r z ^ 2 ∂(Measure.pi fun _ : Fin (m + 1) ↦ P)
  have hV : 0 ≤ V := integral_nonneg fun _ ↦ sq_nonneg _
  have hinj : ∀ f ∈ I, Function.Injective f := fun f hf ↦ (Finset.mem_filter.1 hf).2
  have hL2 : ∀ f ∈ I, MemLp (fun x : Fin n → E ↦ r (x ∘ f)) 2 (Measure.pi fun _ ↦ P) :=
    fun f hf ↦ hr.comp_measurePreserving (measurePreserving_pi_comp_injective P (hinj f hf))
  have hsq : ∀ f ∈ I, ∫ x, r (x ∘ f) ^ 2 ∂(Measure.pi fun _ ↦ P) = V := fun f hf ↦ by
    have hmp := measurePreserving_pi_comp_injective P (hinj f hf)
    have := integral_map (μ := Measure.pi fun _ : Fin n ↦ P) hmp.measurable.aemeasurable
      (f := fun z ↦ r z ^ 2) (by rw [hmp.map_eq]; exact hr.aestronglyMeasurable.pow 2)
    rw [hmp.map_eq] at this
    exact this.symm
  have hprod : ∀ f ∈ I, ∀ f' ∈ I, Integrable (fun x : Fin n → E ↦ r (x ∘ f) * r (x ∘ f'))
      (Measure.pi fun _ ↦ P) := fun f hf f' hf' ↦ (hL2 f hf).integrable_mul (hL2 f' hf')
  set bad : (Fin (m + 1) → Fin n) → (Fin (m + 1) → Fin n) → Prop :=
    fun f f' ↦ ∃ a b, a ≠ b ∧ f' a ∈ range f ∧ f' b ∈ range f
  have hterm : ∀ f ∈ I, ∀ f' ∈ I, ∫ x, r (x ∘ f) * r (x ∘ f') ∂(Measure.pi fun _ ↦ P) ≤
      if bad f f' then V else 0 := by
    intro f hf f' hf'
    split_ifs with hb
    · calc ∫ x, r (x ∘ f) * r (x ∘ f') ∂(Measure.pi fun _ ↦ P)
          ≤ ∫ x, (r (x ∘ f) ^ 2 + r (x ∘ f') ^ 2) / 2 ∂(Measure.pi fun _ ↦ P) :=
            integral_mono (hprod f hf f' hf')
              (((hL2 f hf).integrable_sq.add (hL2 f' hf').integrable_sq).div_const 2)
              fun x ↦ by nlinarith [sq_nonneg (r (x ∘ f) - r (x ∘ f'))]
        _ = V := by
            rw [integral_div, integral_add (hL2 f hf).integrable_sq (hL2 f' hf').integrable_sq,
              hsq f hf, hsq f' hf']
            ring
    · refine le_of_eq (integral_kernel_mul_kernel_eq_zero P r hr hdeg (hinj f hf) (hinj f' hf')
        fun a b ha hb' ↦ ?_)
      by_contra hab
      exact hb ⟨a, b, hab, ha, hb'⟩
  have hexp : ∀ x : Fin n → E, (∑ f ∈ I, r (x ∘ f)) ^ 2 =
      ∑ f ∈ I, ∑ f' ∈ I, r (x ∘ f) * r (x ∘ f') := fun x ↦ by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun f hf ↦ integrable_finsetSum _ fun f' hf' ↦ hprod f hf f' hf']
  have hcount : ∀ f ∈ I, ∑ f' ∈ I, (if bad f f' then V else 0) ≤
      ((m + 1) ^ 3 * m * n ^ (m + 1 - 2) : ℕ) * V := by
    intro f _
    calc ∑ f' ∈ I, (if bad f f' then V else 0)
        ≤ ∑ f' : Fin (m + 1) → Fin n, (if bad f f' then V else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ ↦ by split_ifs <;> simp [hV]
      _ = ((Finset.univ : Finset (Fin (m + 1) → Fin n)).filter (bad f)).card * V := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hV
          have := card_filter_two_apply_mem_range_le (k := m + 1) (n := n) f
          simp only [add_tsub_cancel_right] at this
          exact_mod_cast this
  calc ∑ f ∈ I, ∫ x, ∑ f' ∈ I, r (x ∘ f) * r (x ∘ f') ∂(Measure.pi fun _ ↦ P)
      = ∑ f ∈ I, ∑ f' ∈ I, ∫ x, r (x ∘ f) * r (x ∘ f') ∂(Measure.pi fun _ ↦ P) :=
        Finset.sum_congr rfl fun f hf ↦ integral_finsetSum _ fun f' hf' ↦ hprod f hf f' hf'
    _ ≤ ∑ f ∈ I, ∑ f' ∈ I, (if bad f f' then V else 0) :=
        Finset.sum_le_sum fun f hf ↦ Finset.sum_le_sum fun f' hf' ↦ hterm f hf f' hf'
    _ ≤ ∑ f ∈ I, ((m + 1) ^ 3 * m * n ^ (m + 1 - 2) : ℕ) * V := Finset.sum_le_sum hcount
    _ = _ := by
        rw [Finset.sum_const, card_filter_injective_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The remainder `Uₙ - θ - ((m + 1)/n) ∑ᵢ g(xᵢ)` of the Hájek projection is square integrable
for every sample size. -/
theorem memLp_uStatistic_sub_projection (P : Measure E) [IsProbabilityMeasure P] {m : ℕ}
    (h : (Fin (m + 1) → E) → ℝ) (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) (θ : ℝ)
    {g : E → ℝ} (hg2 : MemLp g 2 P) (n : ℕ) :
    MemLp (fun x : Fin n → E ↦ uStatistic (m + 1) n h x - θ -
      ((m + 1 : ℕ) : ℝ) / n * ∑ i, g (x i)) 2 (Measure.pi fun _ ↦ P) := by
  refine ((?_ : MemLp (fun x ↦ uStatistic (m + 1) n h x) 2 _).sub (memLp_const θ)).sub
    ((memLp_finsetSum _ fun i _ ↦
      hg2.comp_measurePreserving (measurePreserving_eval _ i)).const_mul _)
  simp only [uStatistic]
  exact (memLp_finsetSum _ fun f hf ↦ h2.comp_measurePreserving
    (measurePreserving_pi_comp_injective P (Finset.mem_filter.1 hf).2)).const_mul _

/-- The arithmetic behind the `O(n⁻²)` rate: `m n^(m-1) n² ≤ m 2^(m+1) (n)_{m+1}` for
`n ≥ 2 (m + 1)`. -/
private theorem mul_pow_mul_sq_le_descFactorial {m n : ℕ} (hn : 2 * (m + 1) ≤ n) :
    m * n ^ (m + 1 - 2) * n ^ 2 ≤ m * 2 ^ (m + 1) * n.descFactorial (m + 1) := by
  cases m with
  | zero => simp
  | succ m =>
    have h1 : n ≤ 2 * (n + 1 - (m + 1 + 1)) := by omega
    have h2 := Nat.pow_le_pow_left h1 (m + 1 + 1)
    have h3 := Nat.pow_sub_le_descFactorial n (m + 1 + 1)
    rw [mul_pow] at h2
    calc (m + 1) * n ^ (m + 1 + 1 - 2) * n ^ 2 = (m + 1) * n ^ (m + 1 + 1) := by
          rw [show m + 1 + 1 - 2 = m by omega]; ring
      _ ≤ (m + 1) * (2 ^ (m + 1 + 1) * (n + 1 - (m + 1 + 1)) ^ (m + 1 + 1)) := by gcongr
      _ ≤ (m + 1) * (2 ^ (m + 1 + 1) * n.descFactorial (m + 1 + 1)) := by gcongr
      _ = _ := by ring

/-- **The Hájek projection of a U-statistic.** For a symmetric square-integrable kernel `h` of
order `m + 1` under `P`, with mean `θ` and first projection `g`, the remainder
`Uₙ - θ - ((m + 1)/n) ∑ᵢ g(xᵢ)` has second moment at most `C / n²` under `Pⁿ` for
`n ≥ 2 (m + 1)`. -/
theorem exists_integral_sq_uStatistic_sub_projection_le (P : Measure E) [IsProbabilityMeasure P]
    {m : ℕ} (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) (θ : ℝ)
    (hθ : θ = ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P)) (g : E → ℝ)
    (hg : ∀ a, g a = (∫ y, h (Fin.cases a y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ) :
    ∃ C, ∀ n, 2 * (m + 1) ≤ n →
      ∫ x, (uStatistic (m + 1) n h x - θ - ((m + 1 : ℕ) : ℝ) / n * ∑ i, g (x i)) ^ 2
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨hr, hdeg⟩ := uStatistic_degenerateKernel_spec P h hmeas hsym h2 θ hθ g hg
  set r := fun z : Fin (m + 1) → E ↦ h z - θ - ∑ j, g (z j) with hrdef
  set V := ∫ z, r z ^ 2 ∂(Measure.pi fun _ : Fin (m + 1) ↦ P)
  have hV : 0 ≤ V := integral_nonneg fun _ ↦ sq_nonneg _
  refine ⟨((m + 1 : ℕ) : ℝ) ^ 3 * V * (m * 2 ^ (m + 1)), fun n hn ↦ ?_⟩
  have hkn : m + 1 ≤ n := by omega
  set D : ℝ := ((n.descFactorial (m + 1) : ℕ) : ℝ)
  have hD : 0 < D := by
    have := Nat.descFactorial_eq_zero_iff_lt.not.2 (not_lt.2 hkn)
    positivity
  have heq : ∀ x : Fin n → E, uStatistic (m + 1) n h x - θ - ((m + 1 : ℕ) : ℝ) / n *
      ∑ i, g (x i) = D⁻¹ * ∑ f ∈ (Finset.univ : Finset (Fin (m + 1) → Fin n)).filter
        Function.Injective, r (x ∘ f) := fun x ↦
    uStatistic_sub_projection_eq hkn (Nat.succ_pos m) h θ g x
  simp_rw [heq, mul_pow]
  rw [integral_const_mul]
  have hb := integral_sq_sum_kernel_le P r hr hdeg (n := n)
  have hnat : ((m * n ^ (m + 1 - 2) * n ^ 2 : ℕ) : ℝ) ≤ ((m * 2 ^ (m + 1) *
      n.descFactorial (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast mul_pow_mul_sq_le_descFactorial hn
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc D⁻¹ ^ 2 * ∫ x, (∑ f ∈ (Finset.univ : Finset (Fin (m + 1) → Fin n)).filter
          Function.Injective, r (x ∘ f)) ^ 2 ∂(Measure.pi fun _ ↦ P)
      ≤ D⁻¹ ^ 2 * (D * ((m + 1) ^ 3 * m * n ^ (m + 1 - 2)) * V) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((m + 1 : ℕ) : ℝ) ^ 3 * V * (m * n ^ (m + 1 - 2) * n ^ 2) / (D * n ^ 2) := by
        push_cast
        field_simp
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * V * (m * 2 ^ (m + 1) * D) / (D * n ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnat (by positivity))
          (by positivity)
    _ = _ := by
        field_simp

end Measure

end CKSD
