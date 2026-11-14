module

public import CKSD.Learning.Generalization.Concentration

/-!
# Stability bounds for learning algorithms

Generalization bounds from uniform (replace-one) algorithmic stability for bounded measurable
losses, following Bousquet and Elisseeff. A learning algorithm is represented by its loss
`loss x z` at the test point `z` after training on the sample `x`.

## Main results

* `CKSD.integral_integral_loss_le`: the exchange step, the expected risk is at most the expected
  loss on one training point plus the stability constant.
* `CKSD.abs_integral_sub_sum_div_sub_le_of_stable`: bounded differences of the generalization
  defect.
* `CKSD.measureReal_sum_div_add_lt_integral_le_of_stable`: the high-probability generalization
  bound (GAPS 107.12).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The integral of a measurable function with values in `[0, M]` against a probability
measure lies in `[0, M]`. -/
private theorem integral_mem_Icc_of_mem_Icc {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ x, g x ∈ Icc 0 M) : ∫ x, g x ∂μ ∈ Icc 0 M :=
  ⟨integral_nonneg fun x ↦ (hb x).1, (integral_mono (Integrable.of_mem_Icc 0 M hg.aemeasurable
    (ae_of_all _ hb)) (integrable_const M) fun x ↦ (hb x).2).trans (by simp)⟩

/-- Exchange step for replace-one stable algorithms: the expected risk of the output is at most
the expected loss on the `i`-th training point plus the stability constant. -/
theorem integral_integral_loss_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ)
    (loss : (Fin n → X) → X → ℝ) (hm : Measurable (Function.uncurry loss))
    (beta M : ℝ) (hl : ∀ x z, loss x z ∈ Icc 0 M)
    (hstable : ∀ x y, (∃ i : Fin n, ∀ j, j ≠ i → x j = y j) →
      ∀ z, |loss x z - loss y z| ≤ beta) (i : Fin n) :
    ∫ x, ∫ z, loss x z ∂P ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ∫ x, loss x (x i) ∂(Measure.pi fun _ : Fin n ↦ P) + beta := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set Pm := Measure.pi fun _ : Fin m ↦ P
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ X) i
  have hmp : MeasurePreserving e.symm (P.prod Pm) (Measure.pi fun _ : Fin (m + 1) ↦ P) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ P) i).symm
  have hes : Measurable e.symm := e.symm.measurable
  have hei : ∀ y, e.symm y i = y.1 := fun y ↦ by simp [e]
  have hediff : ∀ a b w, ∀ j, j ≠ i → e.symm (a, w) j = e.symm (b, w) j := by
    intro a b w j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [e]
  have hl1 : ∀ p : (Fin (m + 1) → X) × X, Function.uncurry loss p ∈ Icc 0 M := fun p ↦ hl _ _
  -- measurability of the iterated integrands
  have hR : Measurable fun x : Fin (m + 1) → X ↦ ∫ z, loss x z ∂P :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have hS : Measurable fun x : Fin (m + 1) → X ↦ loss x (x i) :=
    hm.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hRb : ∀ x, ∫ z, loss x z ∂P ∈ Icc 0 M := fun x ↦
    integral_mem_Icc_of_mem_Icc (hm.comp measurable_prodMk_left) (hl x)
  -- rewrite both sides on the product `P ⊗ Pm`
  have hlhs : ∫ x, ∫ z, loss x z ∂P ∂(Measure.pi fun _ : Fin (m + 1) ↦ P) =
      ∫ a, ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm ∂P := by
    rw [← hmp.integral_comp' (fun x ↦ ∫ z, loss x z ∂P)]
    exact integral_prod _ (Integrable.of_mem_Icc 0 M (hR.comp hes).aemeasurable
      (ae_of_all _ fun y ↦ hRb _))
  have hrhs : ∫ x, loss x (x i) ∂(Measure.pi fun _ : Fin (m + 1) ↦ P) =
      ∫ z, ∫ w, loss (e.symm (z, w)) z ∂Pm ∂P := by
    rw [← hmp.integral_comp' (fun x ↦ loss x (x i))]
    simp only [hei]
    exact integral_prod (fun y ↦ loss (e.symm y) y.1)
      (Integrable.of_mem_Icc 0 M (hm.comp (hes.prodMk measurable_fst)).aemeasurable
        (ae_of_all _ fun y ↦ hl _ _))
  -- the swapped integrand
  have hF : Measurable fun p : X × (Fin m → X) ↦ loss (e.symm (p.1, p.2)) p.1 :=
    hm.comp ((hes.comp (measurable_fst.prodMk measurable_snd)).prodMk measurable_fst)
  have hswap : ∫ w, ∫ z, loss (e.symm (z, w)) z ∂P ∂Pm =
      ∫ z, ∫ w, loss (e.symm (z, w)) z ∂Pm ∂P := by
    refine (integral_integral_swap ?_).symm
    exact Integrable.of_mem_Icc 0 M hF.aemeasurable (ae_of_all _ fun _ ↦ hl _ _)
  have hinner : ∀ a, ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm ≤
      ∫ w, ∫ z, loss (e.symm (z, w)) z ∂P ∂Pm + beta := by
    intro a
    have hmeas1 : Measurable fun w : Fin m → X ↦ ∫ z, loss (e.symm (a, w)) z ∂P :=
      hR.comp (hes.comp measurable_prodMk_left)
    have hmeas2 : Measurable fun w : Fin m → X ↦ ∫ z, loss (e.symm (z, w)) z ∂P := by
      have : Measurable fun q : (Fin m → X) × X ↦ loss (e.symm (q.2, q.1)) q.2 :=
        hm.comp ((hes.comp (measurable_snd.prodMk measurable_fst)).prodMk measurable_snd)
      exact this.stronglyMeasurable.integral_prod_right'.measurable
    have hb2 : ∀ w, ∫ z, loss (e.symm (z, w)) z ∂P ∈ Icc 0 M := fun w ↦
      integral_mem_Icc_of_mem_Icc (hF.comp (measurable_id.prodMk measurable_const))
        fun z ↦ hl _ _
    have hpt : ∀ w, ∫ z, loss (e.symm (a, w)) z ∂P ≤
        ∫ z, loss (e.symm (z, w)) z ∂P + beta := by
      intro w
      have hi1 : Integrable (fun z ↦ loss (e.symm (z, w)) z) P :=
        Integrable.of_mem_Icc 0 M (hF.comp (measurable_id.prodMk measurable_const)).aemeasurable
          (ae_of_all _ fun z ↦ hl _ _)
      calc ∫ z, loss (e.symm (a, w)) z ∂P ≤ ∫ z, (loss (e.symm (z, w)) z + beta) ∂P := by
            refine integral_mono (Integrable.of_mem_Icc 0 M
              (hm.comp measurable_prodMk_left).aemeasurable (ae_of_all _ (hl _)))
              (hi1.add (integrable_const _)) fun z ↦ ?_
            have := hstable _ _ ⟨i, hediff a z w⟩ z
            linarith [(abs_le.mp this).2]
        _ = ∫ z, loss (e.symm (z, w)) z ∂P + beta := by
            rw [integral_add hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    have hi2 : Integrable (fun w ↦ ∫ z, loss (e.symm (z, w)) z ∂P) Pm :=
      Integrable.of_mem_Icc 0 M hmeas2.aemeasurable (ae_of_all _ hb2)
    calc ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm
        ≤ ∫ w, (∫ z, loss (e.symm (z, w)) z ∂P + beta) ∂Pm :=
          integral_mono (Integrable.of_mem_Icc 0 M hmeas1.aemeasurable
            (ae_of_all _ fun w ↦ hRb _))
            (hi2.add (integrable_const _)) hpt
      _ = _ := by rw [integral_add hi2 (integrable_const _), integral_const, probReal_univ,
          one_smul]
  have hmeasA : Measurable fun a : X ↦ ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm := by
    have : Measurable fun p : X × (Fin m → X) ↦ ∫ z, loss (e.symm p) z ∂P := hR.comp hes
    exact this.stronglyMeasurable.integral_prod_right'.measurable
  have hbA : ∀ a, ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm ∈ Icc 0 M := fun a ↦
    integral_mem_Icc_of_mem_Icc (hR.comp (hes.comp measurable_prodMk_left)) fun w ↦ hRb _
  rw [hlhs, hrhs, ← hswap]
  calc ∫ a, ∫ w, ∫ z, loss (e.symm (a, w)) z ∂P ∂Pm ∂P
      ≤ ∫ _a, (∫ w, ∫ z, loss (e.symm (z, w)) z ∂P ∂Pm + beta) ∂P :=
        integral_mono (Integrable.of_mem_Icc 0 M hmeasA.aemeasurable (ae_of_all _ hbA))
          (integrable_const _) hinner
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

/-- Bounded differences of the generalization defect `∫ ℓ(x, ·) dP - n⁻¹ ∑ⱼ ℓ(x, xⱼ)` of a
`β`-uniformly stable algorithm with losses in `[0, M]`: changing one training point changes it
by at most `2β + M / n`. -/
theorem abs_integral_sub_sum_div_sub_le_of_stable {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (loss : (Fin n → X) → X → ℝ) (hm : Measurable (Function.uncurry loss))
    {beta M : ℝ} (hl : ∀ x z, loss x z ∈ Icc 0 M)
    (hstable : ∀ x y, (∃ i : Fin n, ∀ j, j ≠ i → x j = y j) →
      ∀ z, |loss x z - loss y z| ≤ beta) (i : Fin n) {x x' : Fin n → X}
    (hxx' : ∀ l, l ≠ i → x l = x' l) :
    |(∫ z, loss x z ∂P - (∑ j, loss x (x j)) / n) -
        (∫ z, loss x' z ∂P - (∑ j, loss x' (x' j)) / n)| ≤ 2 * beta + M / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hb : 0 ≤ beta := by simpa using hstable x x ⟨i, fun _ _ ↦ rfl⟩ (x i)
  have h1 : |∫ z, loss x z ∂P - ∫ z, loss x' z ∂P| ≤ beta := by
    rw [← integral_sub
      (Integrable.of_mem_Icc 0 M (X := fun z ↦ loss x z)
        (hm.comp measurable_prodMk_left).aemeasurable (ae_of_all _ (hl x)))
      (Integrable.of_mem_Icc 0 M (X := fun z ↦ loss x' z)
        (hm.comp measurable_prodMk_left).aemeasurable (ae_of_all _ (hl x')))]
    have := norm_integral_le_of_norm_le_const (μ := P) (C := beta)
      (f := fun z ↦ loss x z - loss x' z)
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hstable x x' ⟨i, hxx'⟩ z)
    simpa [Real.norm_eq_abs] using this
  have h2 : |∑ j, loss x (x j) - ∑ j, loss x' (x' j)| ≤ n * beta + M := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j, (loss x (x j) - loss x' (x' j))| ≤ ∑ j, |loss x (x j) - loss x' (x' j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (beta + if j = i then M else 0) := Finset.sum_le_sum fun j _ ↦ by
          by_cases hj : j = i
          · subst hj
            simp only [ite_true]
            obtain ⟨a1, a2⟩ := hl x (x j); obtain ⟨b1, b2⟩ := hl x' (x' j)
            rw [abs_le]; constructor <;> linarith
          · simp only [hj, ite_false, add_zero]
            rw [← hxx' j hj]
            exact hstable x x' ⟨i, hxx'⟩ _
      _ = n * beta + M := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
          simp
  have h3 : |(∑ j, loss x (x j)) / n - (∑ j, loss x' (x' j)) / n| ≤ beta + M / n := by
    rw [← sub_div, abs_div, abs_of_pos hnr, div_le_iff₀ hnr, add_mul,
      div_mul_cancel₀ _ hnr.ne']
    linarith
  rw [show (∫ z, loss x z ∂P - (∑ j, loss x (x j)) / n) -
      (∫ z, loss x' z ∂P - (∑ j, loss x' (x' j)) / n) =
        (∫ z, loss x z ∂P - ∫ z, loss x' z ∂P) -
          ((∑ j, loss x (x j)) / n - (∑ j, loss x' (x' j)) / n) by ring]
  calc _ ≤ |∫ z, loss x z ∂P - ∫ z, loss x' z ∂P| +
        |(∑ j, loss x (x j)) / n - (∑ j, loss x' (x' j)) / n| := abs_sub _ _
    _ ≤ _ := by linarith

/-- GAPS 107.12: generalization of a measurable uniformly stable algorithm. If replacing one
training point changes every loss by at most `β` and losses lie in `[0, M]`, then with
probability at least `1 - δ` the risk is at most the empirical risk plus
`β + (2 n β + M) √(log(1/δ) / (2n))` (Bousquet–Elisseeff). -/
theorem measureReal_sum_div_add_lt_integral_le_of_stable {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (loss : (Fin n → X) → X → ℝ) (hm : Measurable (Function.uncurry loss))
    (beta M : ℝ) (hl : ∀ x z, loss x z ∈ Icc 0 M)
    (hstable : ∀ x y, (∃ i : Fin n, ∀ j, j ≠ i → x j = y j) →
      ∀ z, |loss x z - loss y z| ≤ beta)
    (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    (Measure.pi fun _ : Fin n ↦ P).real {x |
      (∑ i, loss x (x i)) / n + beta + (2 * n * beta + M) *
        Real.sqrt (Real.log (1 / delta) / (2 * n)) < ∫ z, loss x z ∂P} ≤ delta := by
  set Pn := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hb : 0 ≤ beta := by
    simpa using hstable (fun _ ↦ x0) (fun _ ↦ x0) ⟨⟨0, hn⟩, fun _ _ ↦ rfl⟩ x0
  have hM : 0 ≤ M := (hl (fun _ ↦ x0) x0).1.trans (hl _ _).2
  -- the defect `Φ = risk - empirical risk`
  set Φ : (Fin n → X) → ℝ := fun x ↦ ∫ z, loss x z ∂P - (∑ i, loss x (x i)) / n with hΦ_def
  have hR : Measurable fun x : Fin n → X ↦ ∫ z, loss x z ∂P :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have hS : ∀ i, Measurable fun x : Fin n → X ↦ loss x (x i) := fun i ↦
    hm.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hRb : ∀ x, ∫ z, loss x z ∂P ∈ Icc 0 M := fun x ↦
    integral_mem_Icc_of_mem_Icc (hm.comp measurable_prodMk_left) (hl x)
  have hΦm : Measurable Φ := hR.sub ((Finset.measurable_sum _ fun i _ ↦ hS i).div_const _)
  have hRi : Integrable (fun x : Fin n → X ↦ ∫ z, loss x z ∂P) Pn :=
    Integrable.of_mem_Icc 0 M hR.aemeasurable (ae_of_all _ hRb)
  have hSi : ∀ i, Integrable (fun x : Fin n → X ↦ loss x (x i)) Pn := fun i ↦
    Integrable.of_mem_Icc 0 M (hS i).aemeasurable (ae_of_all _ fun x ↦ hl _ _)
  -- expected defect
  have hEΦ : ∫ x, Φ x ∂Pn ≤ beta := by
    have hsumi : Integrable (fun x : Fin n → X ↦ ∑ i, loss x (x i)) Pn :=
      integrable_finsetSum _ fun i _ ↦ hSi i
    rw [integral_sub hRi (hsumi.div_const _), integral_div, integral_finsetSum _ fun i _ ↦ hSi i]
    have hex := fun i ↦ integral_integral_loss_le P n loss hm beta M hl hstable i
    have hsum : (n : ℝ) * ∫ x, ∫ z, loss x z ∂P ∂Pn ≤
        ∑ i, ∫ x, loss x (x i) ∂Pn + n * beta := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hex i
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      linarith
    have : ∫ x, ∫ z, loss x z ∂P ∂Pn - beta ≤ (∑ i, ∫ x, loss x (x i) ∂Pn) / n := by
      rw [le_div_iff₀ hnr]; linarith
    linarith
  -- bounded differences
  set c : ℝ := 2 * beta + M / n with hc_def
  have hbd : ∀ (i : Fin n) (x x' : Fin n → X), (∀ l, l ≠ i → x l = x' l) →
      |Φ x - Φ x'| ≤ c := fun i x x' hxx' ↦
    abs_integral_sub_sum_div_sub_le_of_stable P loss hm hl hstable i hxx'
  have hsub := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences P Φ hΦm
    (fun _ ↦ c) hbd
  -- the tail bound
  set L := Real.log (1 / delta) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr hd)
  by_cases hzero : 2 * n * beta + M = 0
  · have hb0 : beta = 0 := by nlinarith
    have hM0 : M = 0 := by nlinarith
    have hempty : {x : Fin n → X | (∑ i, loss x (x i)) / n + beta + (2 * n * beta + M) *
        Real.sqrt (Real.log (1 / delta) / (2 * n)) < ∫ z, loss x z ∂P} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [hzero, zero_mul, add_zero, hb0, add_zero]
      have h1 := (hRb x).2
      have h2 : 0 ≤ (∑ i, loss x (x i)) / n :=
        div_nonneg (Finset.sum_nonneg fun i _ ↦ (hl _ _).1) hnr.le
      rw [hM0] at h1
      linarith
    rw [hempty, measureReal_empty]
    exact hd.1.le
  have hpos : 0 < 2 * n * beta + M := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
  set tt := (2 * n * beta + M) * Real.sqrt (L / (2 * n)) with htt
  have htt0 : 0 ≤ tt := mul_nonneg hpos.le (Real.sqrt_nonneg _)
  have hsubset : {x : Fin n → X | (∑ i, loss x (x i)) / n + beta + tt < ∫ z, loss x z ∂P} ⊆
      {x | tt ≤ Φ x - ∫ y, Φ y ∂Pn} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    simp only [Φ] at hEΦ ⊢
    linarith
  have hc0 : 0 ≤ c := by positivity
  calc Pn.real {x | (∑ i, loss x (x i)) / n + beta + tt < ∫ z, loss x z ∂P}
      ≤ Pn.real {x | tt ≤ Φ x - ∫ y, Φ y ∂Pn} := measureReal_mono hsubset
    _ ≤ Real.exp (-tt ^ 2 / (2 * ((∑ _i : Fin n, c.toNNReal ^ 2 / 4 : ℝ≥0) : ℝ))) :=
        hsub.measure_ge_le htt0
    _ = delta := by
        have hcoe : ((∑ _i : Fin n, c.toNNReal ^ 2 / 4 : ℝ≥0) : ℝ) = n * c ^ 2 / 4 := by
          push_cast
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.coe_toNNReal _ hc0]
          ring
        have hsq : tt ^ 2 = (2 * n * beta + M) ^ 2 * (L / (2 * n)) := by
          rw [htt, mul_pow, Real.sq_sqrt (by positivity)]
        have hcn : c = (2 * n * beta + M) / n := by
          rw [hc_def]; field_simp
        rw [hcoe, hsq, hcn]
        have : -((2 * n * beta + M) ^ 2 * (L / (2 * n))) /
            (2 * (n * ((2 * n * beta + M) / n) ^ 2 / 4)) = -L := by
          field_simp
          ring
        rw [this, hL, Real.exp_neg, Real.exp_log (one_div_pos.mpr hd.1), one_div, inv_inv]

end CKSD
