module

public import CKSD.Inference.Basic


/-!
# Completeness of symmetric statistics in convex complete families

Let `C` be a convex set of probability laws on `X` that is complete: a measurable function with
mean zero under every law of `C` vanishes almost everywhere under every law of `C`. Then a
measurable symmetric function `g` of a sample of size `n` with mean zero under every product law
`Pⁿ`, `P ∈ C`, vanishes `Pⁿ`-almost everywhere (GAPS 101.13).

The proof first shows `∫ g d(Q₁ ⊗ ⋯ ⊗ Qₙ) = 0` for all `Qᵢ ∈ C`: the product of the uniform
mixture of `(Qᵢ)_{i ∈ S}` expands multilinearly into products `Q_{τ 1} ⊗ ⋯ ⊗ Q_{τ n}`, and a
Möbius inversion over the ranges of `τ` isolates the permutations, whose integrals agree by
symmetry. Completeness, applied one coordinate at a time, then gives `∫_B g dPⁿ = 0` for every
measurable box `B`, and a π-λ argument gives `g = 0` almost everywhere.

## Main results

* `CKSD.ae_eq_zero_of_set_integral_pi_eq_zero`: an integrable function on a finite product with
  vanishing integrals over all measurable boxes vanishes almost everywhere.
* `CKSD.ae_eq_zero_pi_of_is_complete_statistic_of_convex`: the completeness of symmetric statistics.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- An integrable function on a finite product of measurable spaces whose integrals over all
measurable boxes `∏ᵢ Aᵢ` vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_set_integral_pi_eq_zero {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : Measure (∀ i, α i)) {g : (∀ i, α i) → ℝ}
    (hg : Integrable g μ)
    (hbox : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) →
      ∫ x in univ.pi s, g x ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  have huniv : ∫ x, g x ∂μ = 0 := by
    simpa using hbox (fun _ ↦ univ) fun _ ↦ MeasurableSet.univ
  suffices key : ∀ A, MeasurableSet A → ∫ x in A, g x ∂μ = 0 from
    hg.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ ↦ key A hA
  refine MeasurableSpace.induction_on_inter (C := fun A _ ↦ ∫ x in A, g x ∂μ = 0)
    generateFrom_pi.symm isPiSystem_pi (by simp) ?_ ?_ ?_
  · rintro t ⟨s, hs, rfl⟩
    exact hbox s fun i ↦ hs i (mem_univ i)
  · intro t htm ht
    rw [setIntegral_compl htm hg, ht, huniv, sub_zero]
  · intro f hd hfm hf
    rw [integral_iUnion hfm hd hg.integrableOn, tsum_congr hf, tsum_zero]

section Mixtures

variable {X : Type*} [MeasurableSpace X]

/-- A set of probability laws that is closed under binary mixtures contains the uniform mixture
`(card S)⁻¹ • ∑ i ∈ S, Q i` of any nonempty finite family of its members. -/
private theorem exists_mem_eq_inv_card_smul_sum {C : Set (ProbabilityMeasure X)}
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {ι : Type*} (Q : ι → C) (S : Finset ι) (hS : S.Nonempty) :
    ∃ R ∈ C, (R : Measure X) = ((S.card : ℝ≥0∞))⁻¹ • ∑ i ∈ S, ((Q i).val : Measure X) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨(Q a).val, (Q a).2, by simp⟩
  | cons a S ha hS ih =>
    obtain ⟨R, hRC, hR⟩ := ih
    set s := S.card with hs
    have hs0 : s ≠ 0 := Finset.card_ne_zero.2 hS
    set α : ℝ≥0 := ((s : ℝ≥0) + 1)⁻¹ with hα
    have hα1 : α ≤ 1 := inv_le_one_of_one_le₀ (by simp)
    obtain ⟨R', hR'C, hR'⟩ := hconv (Q a).val (Q a).2 R hRC α hα1
    refine ⟨R', hR'C, ?_⟩
    have h1α : (1 - α : ℝ≥0) = s * α := by
      rw [hα, eq_comm, ← div_eq_mul_inv, tsub_eq_of_eq_add]
      field_simp
    have hαE : (α : ℝ≥0∞) = ((s : ℝ≥0∞) + 1)⁻¹ := by
      rw [hα, ENNReal.coe_inv (by positivity)]
      simp
    rw [hR', hR, h1α, ENNReal.coe_mul, smul_smul, ENNReal.coe_natCast,
      mul_comm (s : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast hs0) (ENNReal.natCast_ne_top s), mul_one,
      ← smul_add, Finset.sum_cons, Finset.card_cons, hαE]
    push_cast
    rfl

/-- The `n`-fold product of a mixture `ν = ∑ i, w i • μ i` expands multilinearly as the sum, over
all assignments `τ : Fin n → ι` of components to coordinates, of `∏ j, w (τ j)` times the
product measure `Measure.pi (fun j ↦ μ (τ j))`. -/
private theorem pi_eq_sum_prod_smul_pi {ι : Type*} [Fintype ι] {n : ℕ} (ν : Measure X)
    [SigmaFinite ν] (w : ι → ℝ≥0∞) (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]
    (hν : ν = ∑ i, w i • μ i) :
    Measure.pi (fun _ : Fin n ↦ ν) =
      ∑ τ : Fin n → ι, (∏ j, w (τ j)) • Measure.pi (fun j ↦ μ (τ j)) := by
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, Measure.pi_pi, hν]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Finset.prod_mul_distrib]

/-- A permutation-invariant function has the same integral under the product measure
`Measure.pi μ` and under its permuted version `Measure.pi (fun j ↦ μ (σ j))`. -/
theorem integral_pi_comp_equiv_of_symmetric {n : ℕ} (μ : Fin n → Measure X)
    [∀ i, SigmaFinite (μ i)] (g : (Fin n → X) → ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, g (x ∘ σ) = g x) (σ : Equiv.Perm (Fin n)) :
    ∫ x, g x ∂(Measure.pi fun j ↦ μ (σ j)) = ∫ x, g x ∂(Measure.pi μ) := by
  have hmp := measurePreserving_piCongrLeft μ σ
  rw [← hmp.integral_comp' g]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  have : (MeasurableEquiv.piCongrLeft (fun _ ↦ X) σ) z = z ∘ σ.symm := by
    funext i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  beta_reduce
  rw [this, hsym]

/-- Let `C` be closed under binary mixtures and let `g` be a symmetric function of `n ≥ 1`
coordinates that is integrable with mean zero under `Pⁿ` for every `P ∈ C`. Then `g` is
integrable with mean zero under every product `Q₁ ⊗ ⋯ ⊗ Qₙ` with all `Qᵢ ∈ C`. The proof
expands the `n`-th power of uniform mixtures of the `Qᵢ` and applies Möbius inversion over
subsets of the index set. -/
private theorem integrable_and_integral_pi_eq_zero {C : Set (ProbabilityMeasure X)}
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {n : ℕ} (hn : 0 < n) (g : (Fin n → X) → ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin n ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ (P : Measure X)) = 0)
    (Q : Fin n → C) :
    Integrable g (Measure.pi fun i ↦ ((Q i).val : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun i ↦ ((Q i).val : Measure X)) = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set ν : (Fin n → Fin n) → Measure (Fin n → X) :=
    fun τ ↦ Measure.pi fun j ↦ ((Q (τ j)).val : Measure X) with hνdef
  set a : (Fin n → Fin n) → ℝ := fun τ ↦ ∫ x, g x ∂(ν τ) with hadef
  -- the uniform mixture over `S` and its product expansion
  have hmix : ∀ S : Finset (Fin n), S.Nonempty → ∃ R ∈ C,
      Measure.pi (fun _ : Fin n ↦ (R : Measure X)) = ∑ τ : Fin n → Fin n,
        (if ∀ j, τ j ∈ S then ((S.card : ℝ≥0∞)⁻¹) ^ n else 0) • ν τ := by
    intro S hS
    obtain ⟨R, hRC, hR⟩ := exists_mem_eq_inv_card_smul_sum hconv Q S hS
    refine ⟨R, hRC, ?_⟩
    have hR' : (R : Measure X) = ∑ i, (if i ∈ S then ((S.card : ℝ≥0∞))⁻¹ else 0) •
        ((Q i).val : Measure X) := by
      rw [hR, Finset.smul_sum]
      simp_rw [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [pi_eq_sum_prod_smul_pi _ _ _ hR']
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    congr 1
    split_ifs with hτ
    · simp only [hτ, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · push Not at hτ
      obtain ⟨j, hj⟩ := hτ
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  -- integrability under all mixed products
  have hcard0 : ((Finset.univ : Finset (Fin n)).card : ℝ≥0∞)⁻¹ ^ n ≠ 0 := by
    simp
  have hcardtop : ((Finset.univ : Finset (Fin n)).card : ℝ≥0∞)⁻¹ ^ n ≠ ⊤ := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne'))
  have hνint : ∀ τ, Integrable g (ν τ) := by
    obtain ⟨R, hRC, hR⟩ := hmix Finset.univ Finset.univ_nonempty
    have h := (hint R hRC).1
    rw [hR, integrable_finsetSum_measure] at h
    intro τ
    have h' := h τ (Finset.mem_univ τ)
    simp only [Finset.mem_univ, implies_true, ite_true] at h'
    exact (integrable_smul_measure hcard0 hcardtop).1 h'
  -- the sums over maps with values in `S` vanish
  have hB : ∀ S : Finset (Fin n),
      ∑ τ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter (fun τ ↦ ∀ j, τ j ∈ S), a τ = 0 := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | hS
    · refine Finset.sum_eq_zero fun τ hτ ↦ ?_
      exact absurd ((Finset.mem_filter.1 hτ).2 ⟨0, hn⟩) (Finset.notMem_empty _)
    obtain ⟨R, hRC, hR⟩ := hmix S hS
    have h := (hint R hRC).2
    rw [hR, integral_finsetSum_measure fun τ _ ↦ (hνint τ).smul_measure (by
      split_ifs
      · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hS.card_pos.ne'))
      · exact ENNReal.zero_ne_top)] at h
    simp_rw [integral_smul_measure, apply_ite ENNReal.toReal, ENNReal.toReal_zero, ite_smul,
      zero_smul] at h
    rw [← Finset.sum_filter] at h
    simp_rw [smul_eq_mul] at h
    rw [← Finset.mul_sum] at h
    have hpos : (((S.card : ℝ≥0∞))⁻¹ ^ n).toReal ≠ 0 := by
      rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
      positivity
    exact (mul_eq_zero.1 h).resolve_left hpos
  -- Möbius inversion: the sums over maps with range exactly `S` vanish
  have hfib : ∀ S T : Finset (Fin n), T ⊆ S →
      ((Finset.univ : Finset (Fin n → Fin n)).filter (fun τ ↦ ∀ j, τ j ∈ S)).filter
        (fun τ ↦ Finset.univ.image τ = T) =
      (Finset.univ : Finset (Fin n → Fin n)).filter (fun τ ↦ Finset.univ.image τ = T) := by
    intro S T hTS
    ext τ
    simp only [Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h ↦ h.2
    · rintro rfl
      exact ⟨fun j ↦ hTS (Finset.mem_image_of_mem _ (Finset.mem_univ j)), rfl⟩
  have hA : ∀ S : Finset (Fin n), ∑ τ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
      (fun τ ↦ Finset.univ.image τ = S), a τ = 0 := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      have hsplit := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin n → Fin n)).filter (fun τ ↦ ∀ j, τ j ∈ S))
        (t := S.powerset) (g := fun τ ↦ Finset.univ.image τ)
        (fun τ hτ ↦ Finset.mem_powerset.2 fun i hi ↦ by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
          exact (Finset.mem_filter.1 hτ).2 j) a
      rw [hB S, Finset.sum_eq_single_of_mem S (Finset.mem_powerset_self S) fun T hT hTS ↦ by
        rw [hfib S T (Finset.mem_powerset.1 hT)]
        exact ih T (Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hT, hTS⟩),
        hfib S S subset_rfl] at hsplit
      exact hsplit
  have hU := hA Finset.univ
  have heq : ∀ τ ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
      (fun τ ↦ Finset.univ.image τ = Finset.univ), a τ = a id := by
    intro τ hτ
    have hsurj : Function.Surjective τ := fun i ↦ by
      have hi : i ∈ Finset.univ.image τ := by
        rw [(Finset.mem_filter.1 hτ).2]; exact Finset.mem_univ i
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hi
      exact ⟨j, hj⟩
    have hbij : Function.Bijective τ := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
    have := integral_pi_comp_equiv_of_symmetric (fun i ↦ ((Q i).val : Measure X)) g hsym
      (Equiv.ofBijective τ hbij)
    exact this
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul] at hU
  have hid : id ∈ (Finset.univ : Finset (Fin n → Fin n)).filter
      (fun τ ↦ Finset.univ.image τ = Finset.univ) := by simp
  have hcard : ((((Finset.univ : Finset (Fin n → Fin n)).filter
      (fun τ ↦ Finset.univ.image τ = Finset.univ)).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨id, hid⟩).ne'
  exact ⟨hνint id, (mul_eq_zero.1 hU).resolve_left hcard⟩

/-- Fubini at the coordinate `j`: integrate the `j`-th coordinate last. -/
theorem integral_pi_eq_integral_integral_insert_nth {n : ℕ} (μ : Fin (n + 1) → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] (j : Fin (n + 1)) {F : (Fin (n + 1) → X) → ℝ}
    (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun t ↦ ∫ y, F (j.insertNth t y) ∂(Measure.pi fun i ↦ μ (j.succAbove i)))
        (μ j) ∧
      ∫ x, F x ∂(Measure.pi μ) =
        ∫ t, ∫ y, F (j.insertNth t y) ∂(Measure.pi fun i ↦ μ (j.succAbove i)) ∂(μ j) := by
  have hes := (measurePreserving_piFinSuccAbove μ j).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ X) j)
  have hFi := hes.integrable_comp_of_integrable hF
  refine ⟨hFi.integral_prod_left, ?_⟩
  rw [← hes.integral_comp' F]
  exact integral_prod (fun p ↦ F ((MeasurableEquiv.piFinSuccAbove (fun _ ↦ X) j).symm p)) hFi

/-- **Completeness of symmetric statistics.** In a convex complete set `C` of probability laws, a
measurable symmetric function of a sample of size `n` that has mean zero under every `Pⁿ`,
`P ∈ C`, vanishes `Pⁿ`-almost everywhere for every `P ∈ C`. -/
theorem ae_eq_zero_pi_of_is_complete_statistic_of_convex {C : Set (ProbabilityMeasure X)}
    (hc : ∀ f : X → ℝ, Measurable f →
      (∀ P ∈ C, Integrable f (P : Measure X) ∧ ∫ x, f x ∂(P : Measure X) = 0) →
      ∀ P ∈ C, ∀ᵐ x ∂(P : Measure X), f x = 0)
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X))
    {n : ℕ} (g : (Fin n → X) → ℝ) (hgm : Measurable g)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, g (x ∘ σ) = g x)
    (hint : ∀ P ∈ C, Integrable g (Measure.pi fun _ : Fin n ↦ (P : Measure X)) ∧
      ∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ (P : Measure X)) = 0)
    (P : ProbabilityMeasure X) (hP : P ∈ C) :
    g =ᵐ[Measure.pi fun _ : Fin n ↦ (P : Measure X)] 0 := by
  cases n with
  | zero =>
    obtain ⟨-, h0⟩ := hint P hP
    have x₀ : Fin 0 → X := Fin.elim0
    have hconst : ∀ x : Fin 0 → X, g x = g x₀ := fun x ↦ congrArg g (Subsingleton.elim _ _)
    rw [integral_congr_ae (ae_of_all _ hconst), integral_const, probReal_univ, one_smul] at h0
    exact ae_of_all _ fun x ↦ (hconst x).trans h0
  | succ n =>
  have step₁ := integrable_and_integral_pi_eq_zero hconv (Nat.succ_pos n) g hsym hint
  set fam : ℕ → (Fin (n + 1) → C) → Fin (n + 1) → C :=
    fun j Q i ↦ if (i : ℕ) < j then ⟨P, hP⟩ else Q i with hfam
  set G : ℕ → (Fin (n + 1) → Set X) → (Fin (n + 1) → X) → ℝ :=
    fun j s ↦ {x | ∀ i : Fin (n + 1), (i : ℕ) < j → x i ∈ s i}.indicator g with hG
  have hBm : ∀ (j : ℕ) (s : Fin (n + 1) → Set X), (∀ i, MeasurableSet (s i)) →
      MeasurableSet {x : Fin (n + 1) → X | ∀ i : Fin (n + 1), (i : ℕ) < j → x i ∈ s i} := by
    intro j s hs
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
      measurable_pi_apply i (hs i)
  have hGint : ∀ j s, (∀ i, MeasurableSet (s i)) → ∀ Q : Fin (n + 1) → C,
      Integrable (G j s) (Measure.pi fun i ↦ ((Q i).val : Measure X)) :=
    fun j s hs Q ↦ (step₁ Q).1.indicator (hBm j s hs)
  have hGm : ∀ j s, (∀ i, MeasurableSet (s i)) → Measurable (G j s) :=
    fun j s hs ↦ hgm.indicator (hBm j s hs)
  have claim : ∀ j ≤ n + 1, ∀ (Q : Fin (n + 1) → C) (s : Fin (n + 1) → Set X),
      (∀ i, MeasurableSet (s i)) →
        ∫ x, G j s x ∂(Measure.pi fun i ↦ ((fam j Q i).val : Measure X)) = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ Q s _
      simpa [G, fam] using (step₁ Q).2
    | succ j ih =>
      intro hj Q s hs
      set jj : Fin (n + 1) := ⟨j, by omega⟩
      set ν : Fin n → Measure X := fun i ↦ ((fam j Q (jj.succAbove i)).val : Measure X)
      set ψ : X → ℝ := fun t ↦ ∫ y, G j s (jj.insertNth t y) ∂(Measure.pi ν)
      -- the slice integral `ψ` has mean zero under every law of `C`
      have hslice : ∀ R ∈ C, Integrable ψ (R : Measure X) ∧ ∫ t, ψ t ∂(R : Measure X) = 0 := by
        intro R hR
        set Q' := Function.update Q jj ⟨R, hR⟩
        have hjj : fam j Q' jj = ⟨R, hR⟩ := by simp [fam, Q', jj]
        have hoff : ∀ i, fam j Q' (jj.succAbove i) = fam j Q (jj.succAbove i) := fun i ↦ by
          simp [fam, Q']
        have hF := integral_pi_eq_integral_integral_insert_nth
          (fun i ↦ ((fam j Q' i).val : Measure X)) jj (hGint j s hs (fam j Q'))
        simp only [hjj, hoff] at hF
        exact ⟨hF.1, hF.2 ▸ ih (by omega) Q' s hs⟩
      have hψm : Measurable ψ := by
        have : Measurable (fun p : X × (Fin n → X) ↦ G j s (jj.insertNth p.1 p.2)) :=
          (hGm j s hs).comp (MeasurableEquiv.piFinSuccAbove (fun _ ↦ X) jj).symm.measurable
        exact this.stronglyMeasurable.integral_prod_right'.measurable
      have hψ0 := hc ψ hψm hslice P hP
      -- integrate the `j`-th coordinate last
      have hjjP : fam (j + 1) Q jj = ⟨P, hP⟩ := by simp [fam, jj]
      have hoff : ∀ i, fam (j + 1) Q (jj.succAbove i) = fam j Q (jj.succAbove i) := fun i ↦ by
        have hne : ((jj.succAbove i : Fin (n + 1)) : ℕ) ≠ j := fun h ↦
          Fin.succAbove_ne jj i (Fin.ext h)
        simp only [fam]
        congr 1
        exact propext ⟨fun h ↦ by omega, fun h ↦ by omega⟩
      have hF := integral_pi_eq_integral_integral_insert_nth
        (fun i ↦ ((fam (j + 1) Q i).val : Measure X)) jj (hGint (j + 1) s hs (fam (j + 1) Q))
      simp only [hjjP, hoff] at hF
      rw [hF.2]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hψ0] with t ht
      have hpt : ∀ y : Fin n → X, G (j + 1) s (jj.insertNth t y) =
          (s jj).indicator (fun _ ↦ G j s (jj.insertNth t y)) t := by
        intro y
        simp only [G, Set.indicator, mem_ofPred_eq]
        by_cases hts : t ∈ s jj
        · simp only [hts, ite_true]
          congr 1
          refine propext ⟨fun h i hi ↦ h i (by omega), fun h i hi ↦ ?_⟩
          by_cases hij : (i : ℕ) = j
          · have : i = jj := Fin.ext hij
            subst this
            simpa using hts
          · exact h i (by omega)
        · simp only [hts, ite_false, ite_eq_right_iff]
          intro h
          exact absurd (by simpa using h jj (by simp [jj])) hts
      simp_rw [hpt]
      by_cases hts : t ∈ s jj
      · simp only [Set.indicator_of_mem hts]
        exact ht
      · simp [Set.indicator_of_notMem hts]
  -- all boxes
  have hfamP : ∀ Q i, fam (n + 1) Q i = ⟨P, hP⟩ := fun Q i ↦ by simp [fam, i.isLt]
  obtain ⟨Q₀⟩ : Nonempty (Fin (n + 1) → C) := ⟨fun _ ↦ ⟨P, hP⟩⟩
  refine ae_eq_zero_of_set_integral_pi_eq_zero _ (hint P hP).1 fun s hs ↦ ?_
  have h := claim (n + 1) le_rfl Q₀ s hs
  simp only [hfamP] at h
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  convert h using 3 with x
  simp only [G, Set.indicator, mem_univ_pi, mem_ofPred_eq]
  congr 1
  exact propext ⟨fun h i _ ↦ h i, fun h i ↦ h i i.isLt⟩

end Mixtures

end CKSD
