module

public import CKSD.Nonparametric.Basic

/-!
# False discovery rate control by the Benjamini–Hochberg procedure

## Main definitions

* `CKSD.benjaminiHochbergFalseDiscoveryProportion`: the proportion of true null hypotheses among
  the rejections of the Benjamini–Hochberg procedure.

## Main results

* `CKSD.benjaminiHochbergCount_le`, `CKSD.benjaminiHochbergCount_le_card`,
  `CKSD.le_benjaminiHochbergCount`: the Benjamini–Hochberg count is the largest attained level.
* `CKSD.benjaminiHochberg_rejection_div_eq_sum`: the leave-one-out decomposition of the
  rejection proportion.
* `CKSD.integral_benjaminiHochbergFalseDiscoveryProportion_le`: the Benjamini–Hochberg
  procedure at level `α` controls the false discovery rate at `α m₀ / m` for independent
  p-values whose null p-values are superuniform.

Source: GAPS 103.37.

## References

* S. Dudoit and M. J. van der Laan, *Multiple Testing Procedures with Applications to Genomics*,
  Springer, 2008.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The Benjamini–Hochberg count `R` is attained: `R ≤ m` and `R ≤ #{j : x j ≤ R α / m}`. -/
private theorem benjaminiHochbergCount_le_and_le_card {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤ m ∧ benjaminiHochbergCount x α ≤
      (Finset.univ.filter fun j ↦ x j ≤ (benjaminiHochbergCount x α : ℝ) * α / m).card := by
  classical
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup
    ((Finset.range (m + 1)).filter fun k : ℕ ↦
      k ≤ (Finset.univ.filter fun i ↦ x i ≤ (k : ℝ) * α / m).card)
    ⟨0, by simp⟩ id
  have hR : benjaminiHochbergCount x α = k := by
    rw [benjaminiHochbergCount_def]; convert heq; rfl
  rw [Finset.mem_filter, Finset.mem_range] at hk
  rw [hR]
  exact ⟨by omega, by convert hk.2⟩

/-- The Benjamini–Hochberg count is at most the number of hypotheses. -/
theorem benjaminiHochbergCount_le {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤ m :=
  (benjaminiHochbergCount_le_and_le_card x α).1

/-- The Benjamini–Hochberg count `R` satisfies its defining inequality
`R ≤ #{j : x j ≤ R α / m}`. -/
theorem benjaminiHochbergCount_le_card {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤
      (Finset.univ.filter fun j ↦ x j ≤ (benjaminiHochbergCount x α : ℝ) * α / m).card :=
  (benjaminiHochbergCount_le_and_le_card x α).2

/-- Every `k ≤ m` satisfying the Benjamini–Hochberg inequality is at most the count. -/
theorem le_benjaminiHochbergCount {m : ℕ} (x : Fin m → ℝ) (α : ℝ) (k : ℕ) (hk : k ≤ m)
    (hkN : k ≤ (Finset.univ.filter fun j ↦ x j ≤ (k : ℝ) * α / m).card) :
    k ≤ benjaminiHochbergCount x α := by
  classical
  simp only [benjaminiHochbergCount_def]
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
    convert hkN⟩)

/-- Setting a p-value to zero can only enlarge the sets of p-values below each threshold. -/
private theorem filter_le_subset_filter_update_zero {m : ℕ} (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m) (k : ℕ) :
    (Finset.univ.filter fun j ↦ x j ≤ (k : ℝ) * α / m) ⊆
      (Finset.univ.filter fun j ↦ Function.update x i 0 j ≤ (k : ℝ) * α / m) := by
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  by_cases hji : j = i
  · subst hji; simp only [Function.update_self]; positivity
  · simp [Function.update_of_ne hji, hj]

/-- Setting one p-value to zero does not decrease the Benjamini–Hochberg count. -/
theorem benjaminiHochbergCount_le_update_zero {m : ℕ} (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m) :
    benjaminiHochbergCount x α ≤ benjaminiHochbergCount (Function.update x i 0) α :=
  le_benjaminiHochbergCount _ α _ (benjaminiHochbergCount_le x α)
    ((benjaminiHochbergCount_le_card x α).trans
      (Finset.card_le_card (filter_le_subset_filter_update_zero x α hα i _)))

/-- After setting one p-value to zero, the Benjamini–Hochberg procedure rejects at least once. -/
theorem one_le_benjaminiHochbergCount_update_zero {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (i : Fin m) :
    1 ≤ benjaminiHochbergCount (Function.update x i 0) α := by
  refine le_benjaminiHochbergCount _ α 1 hm ?_
  rw [Finset.one_le_card]
  exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.update_self]; positivity⟩

/-- The Benjamini–Hochberg count is unchanged by setting the `i`-th p-value to zero whenever
that p-value is rejected by the modified count. -/
theorem benjaminiHochbergCount_eq_update_zero_of_le {m : ℕ} (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m)
    (hi : x i ≤ (benjaminiHochbergCount (Function.update x i 0) α : ℝ) * α / m) :
    benjaminiHochbergCount x α = benjaminiHochbergCount (Function.update x i 0) α := by
  classical
  set q := Function.update x i 0
  have heq : (Finset.univ.filter fun j ↦ q j ≤ (benjaminiHochbergCount q α : ℝ) * α / m) =
      (Finset.univ.filter fun j ↦ x j ≤ (benjaminiHochbergCount q α : ℝ) * α / m) := by
    refine Finset.Subset.antisymm (fun j hj ↦ ?_) (filter_le_subset_filter_update_zero x α hα i _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hji : j = i
    · subst hji; exact hi
    · simpa [q, Function.update_of_ne hji] using hj
  refine le_antisymm (benjaminiHochbergCount_le_update_zero x α hα i) ?_
  refine le_benjaminiHochbergCount x α _ (benjaminiHochbergCount_le q α) ?_
  rw [← heq]; exact benjaminiHochbergCount_le_card q α

/-- Leave-one-out decomposition of a Benjamini–Hochberg rejection: the contribution of
hypothesis `i` to the false discovery proportion splits over the value `k` of the count
computed with `x i` replaced by zero. -/
theorem benjaminiHochberg_rejection_div_eq_sum {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m) :
    (if x i ≤ (benjaminiHochbergCount x α : ℝ) * α / m then (1 : ℝ) else 0) /
        max (benjaminiHochbergCount x α : ℝ) 1 =
      ∑ k ∈ Finset.Icc 1 m, (if x i ≤ (k : ℝ) * α / m ∧
        benjaminiHochbergCount (Function.update x i 0) α = k then (1 : ℝ) / k else 0) := by
  classical
  have hmono := benjaminiHochbergCount_le_update_zero x α hα i
  have hone := one_le_benjaminiHochbergCount_update_zero hm x α hα i
  have hsame := benjaminiHochbergCount_eq_update_zero_of_le x α hα i
  set R := benjaminiHochbergCount x α
  set Rq := benjaminiHochbergCount (Function.update x i 0) α
  have hRqm : Rq ≤ m := benjaminiHochbergCount_le _ α
  by_cases hrej : x i ≤ (R : ℝ) * α / m
  · have hle : x i ≤ (Rq : ℝ) * α / m := hrej.trans (by
      gcongr)
    have hR : R = Rq := hsame hle
    rw [ite_eq_left hrej, Finset.sum_eq_single Rq]
    · rw [ite_eq_left ⟨hle, rfl⟩, hR, max_eq_left (by exact_mod_cast hone)]
    · intro k _ hk
      rw [ite_eq_right]; rintro ⟨_, h⟩; exact hk h.symm
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨hone, hRqm⟩) h
  · rw [ite_eq_right hrej, zero_div]
    symm
    refine Finset.sum_eq_zero fun k _ ↦ ite_eq_right ?_
    rintro ⟨hk, hRk⟩
    rw [← hRk] at hk
    exact hrej (by rw [hsame hk]; exact hk)

/-- The Benjamini–Hochberg count is a measurable function of the p-values. -/
theorem measurable_benjaminiHochbergCount (m : ℕ) (α : ℝ) :
    Measurable fun x : Fin m → ℝ ↦ benjaminiHochbergCount x α := by
  classical
  -- the count factors through the finitely many rejection counts
  set N : (Fin m → ℝ) → (Fin (m + 1) → ℕ) := fun x k ↦
    (Finset.univ.filter fun j ↦ x j ≤ ((k : ℕ) : ℝ) * α / m).card with hN
  set G : (Fin (m + 1) → ℕ) → ℕ := fun v ↦
    ((Finset.range (m + 1)).filter fun k : ℕ ↦
      k ≤ (if h : k < m + 1 then v ⟨k, h⟩ else 0)).sup id with hG
  have hfac : (fun x : Fin m → ℝ ↦ benjaminiHochbergCount x α) = G ∘ N := by
    funext x
    simp only [Function.comp, hG, hN, benjaminiHochbergCount_def]
    congr 1
    refine Finset.filter_congr fun k hk ↦ ?_
    rw [dite_eq_left (Finset.mem_range.mp hk)]
  rw [hfac]
  refine (measurable_of_countable G).comp ?_
  refine measurable_pi_iff.mpr fun k ↦ ?_
  simp only [hN, Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
    measurable_const measurable_const

/-- The false discovery proportion of the Benjamini–Hochberg procedure at level `α` with
p-values `x` and set of true null hypotheses `H₀`: the number of rejected true nulls divided by
the number of rejections, with `0 / 0 = 0`. -/
def benjaminiHochbergFalseDiscoveryProportion {m : ℕ} (H₀ : Finset (Fin m)) (x : Fin m → ℝ)
    (α : ℝ) : ℝ :=
  ((H₀.filter fun i ↦ x i ≤ (benjaminiHochbergCount x α : ℝ) * α / m).card : ℝ) /
    max (benjaminiHochbergCount x α : ℝ) 1

/-- GAPS 103.37: false discovery rate control by the Benjamini–Hochberg procedure. For
mutually independent p-values whose true-null p-values are superuniform,
`P(p_i ≤ t) ≤ t` for `t ∈ [0, 1]`, the expected false discovery proportion at level
`α ∈ (0, 1)` is at most `α |H₀| / m`. -/
theorem integral_benjaminiHochbergFalseDiscoveryProportion_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (hind : iIndepFun p μ)
    (H₀ : Finset (Fin m)) (hvalid : ∀ i ∈ H₀, ∀ t ∈ Icc (0 : ℝ) 1,
      μ.real {ω | p i ω ≤ t} ≤ t) (α : ℝ) (hα : α ∈ Ioo 0 1) :
    ∫ ω, benjaminiHochbergFalseDiscoveryProportion H₀ (fun j ↦ p j ω) α ∂μ ≤
      α * H₀.card / m := by
  unfold benjaminiHochbergFalseDiscoveryProportion
  classical
  obtain ⟨hα0, hα1⟩ := hα
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the leave-one-out counts
  set Ri : Fin m → Ω → ℕ := fun i ω ↦
    benjaminiHochbergCount (Function.update (fun j ↦ p j ω) i 0) α with hRi
  have hupd_meas : ∀ i, Measurable fun ω ↦ Function.update (fun j ↦ p j ω) i 0 := by
    intro i
    refine measurable_pi_iff.mpr fun j ↦ ?_
    by_cases hji : j = i
    · subst hji; simp only [Function.update_self]; exact measurable_const
    · simp only [Function.update_of_ne hji]; exact hp j
  have hRi_meas : ∀ i, Measurable (Ri i) := fun i ↦
    (measurable_benjaminiHochbergCount m α).comp (hupd_meas i)
  -- independence of `p i` and the leave-one-out count
  have hindep : ∀ i, IndepFun (p i) (Ri i) μ := by
    intro i
    have h := hind.indepFun_finset {i} (Finset.univ \ {i}) Finset.disjoint_sdiff hp
    have hφ : Measurable fun z : ({i} : Finset (Fin m)) → ℝ ↦ z ⟨i, Finset.mem_singleton_self i⟩ :=
      measurable_pi_apply _
    let ext : ((Finset.univ \ {i} : Finset (Fin m)) → ℝ) → (Fin m → ℝ) := fun z j ↦
      if hj : j ∈ Finset.univ \ {i} then z ⟨j, hj⟩ else 0
    have hext_meas : Measurable ext := by
      refine measurable_pi_iff.mpr fun j ↦ ?_
      by_cases hj : j ∈ Finset.univ \ {i}
      · simp only [ext, dite_eq_left hj]; exact measurable_pi_apply _
      · simp only [ext, dite_eq_right hj]; exact measurable_const
    have h2 := h.comp hφ ((measurable_benjaminiHochbergCount m α).comp hext_meas)
    have e1 : p i = (fun z : ({i} : Finset (Fin m)) → ℝ ↦ z ⟨i, Finset.mem_singleton_self i⟩) ∘
        (fun ω (j : ({i} : Finset (Fin m))) ↦ p j ω) := rfl
    have e2 : Ri i = ((fun x : Fin m → ℝ ↦ benjaminiHochbergCount x α) ∘ ext) ∘
        (fun ω (j : (Finset.univ \ {i} : Finset (Fin m))) ↦ p j ω) := by
      funext ω
      refine congrArg (fun x ↦ benjaminiHochbergCount x α) (funext fun j ↦ ?_)
      by_cases hji : j = i
      · subst hji; simp [ext]
      · simp only [Function.update_of_ne hji, ext,
          dite_eq_left (show j ∈ Finset.univ \ {i} by simp [hji])]
    rw [e1, e2]
    exact h2
  -- the events
  set E : Fin m → ℕ → Set Ω := fun i k ↦ {ω | p i ω ≤ (k : ℝ) * α / m} ∩ Ri i ⁻¹' {k} with hE
  have hE_meas : ∀ i k, MeasurableSet (E i k) := fun i k ↦
    (measurableSet_le (hp i) measurable_const).inter (hRi_meas i (measurableSet_singleton k))
  -- pointwise decomposition of the false discovery proportion
  have hpt : ∀ ω, ((H₀.filter fun i ↦ p i ω ≤
      (benjaminiHochbergCount (fun j ↦ p j ω) α : ℝ) * α / m).card : ℝ) /
        max (benjaminiHochbergCount (fun j ↦ p j ω) α : ℝ) 1 =
      ∑ i ∈ H₀, ∑ k ∈ Finset.Icc 1 m, (E i k).indicator (fun _ ↦ (1 : ℝ) / k) ω := by
    intro ω
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      benjaminiHochberg_rejection_div_eq_sum hm (fun j ↦ p j ω) α hα0.le i]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Set.indicator, hE, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      mem_ofPred_eq, hRi]
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun k _ ↦
    (integrable_const _).indicator (hE_meas i k)]
  have hterm : ∀ i ∈ H₀, ∫ ω, ∑ k ∈ Finset.Icc 1 m, (E i k).indicator (fun _ ↦ (1 : ℝ) / k) ω ∂μ
      ≤ α / m := by
    intro i hi
    rw [integral_finsetSum _ fun k _ ↦ (integrable_const _).indicator (hE_meas i k)]
    have hk : ∀ k ∈ Finset.Icc 1 m, ∫ ω, (E i k).indicator (fun _ ↦ (1 : ℝ) / k) ω ∂μ ≤
        α / m * μ.real (Ri i ⁻¹' {k}) := by
      intro k hk
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [integral_indicator_const _ (hE_meas i k), smul_eq_mul]
      have hmul : μ.real (E i k) = μ.real {ω | p i ω ≤ (k : ℝ) * α / m} *
          μ.real (Ri i ⁻¹' {k}) := by
        simp only [hE, Measure.real]
        rw [← ENNReal.toReal_mul]
        congr 1
        exact (hindep i).measure_inter_preimage_eq_mul (Iic ((k : ℝ) * α / m)) {k}
          measurableSet_Iic (measurableSet_singleton k)
      have ht : (k : ℝ) * α / m ∈ Icc (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hmR]
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm
        nlinarith
      have hv := hvalid i hi _ ht
      rw [hmul]
      have hB := measureReal_nonneg (μ := μ) (s := Ri i ⁻¹' {k})
      calc μ.real {ω | p i ω ≤ (k : ℝ) * α / m} * μ.real (Ri i ⁻¹' {k}) * (1 / k)
          ≤ (k : ℝ) * α / m * μ.real (Ri i ⁻¹' {k}) * (1 / k) := by gcongr
        _ = α / m * μ.real (Ri i ⁻¹' {k}) := by field_simp
    refine (Finset.sum_le_sum hk).trans ?_
    rw [← Finset.mul_sum, sum_measureReal_preimage_singleton _ fun k _ ↦
      hRi_meas i (measurableSet_singleton k)]
    have : μ.real (Ri i ⁻¹' ↑(Finset.Icc 1 m)) ≤ 1 := measureReal_le_one
    have hαm : 0 ≤ α / m := by positivity
    nlinarith
  calc ∑ i ∈ H₀, ∫ ω, ∑ k ∈ Finset.Icc 1 m, (E i k).indicator (fun _ ↦ (1 : ℝ) / k) ω ∂μ
      ≤ ∑ _i ∈ H₀, α / m := Finset.sum_le_sum hterm
    _ = α * H₀.card / m := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CKSD
