module

public import CKSD.Asymptotics.LikelihoodSupport

/-!
# Scalar likelihood-root asymptotic normality

A consistent measurable root of the score equation has an asymptotically linear expansion and
a normal limit under local third-derivative domination and the information identities.
Sources: GAPS 102.3 and `SYNOPSIS102.md`. The proof uses the integral and Taylor estimates in
`CKSD.Asymptotics.LikelihoodSupport` and Mathlib's strong law and central limit theorem through
the adapters in `CKSD.Asymptotics.Convergence`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 102.3, scalar smooth likelihood-score roots and their efficient expansion.
`ell` is the per-observation log likelihood; the score/information moment
identities and the local third-derivative envelope are explicit hypotheses. -/
theorem mle_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (ell : ℝ → E → ℝ)
    (hm : ∀ theta, Measurable (ell theta)) (hsmooth : ∀ x, ContDiff ℝ 3 (fun theta ↦ ell theta x))
    (theta₀ I : ℝ) (hI : 0 < I) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M P)
    (henv : ∀ x theta, |theta - theta₀| < r →
      |deriv (deriv (deriv (fun t ↦ ell t x))) theta| ≤ M x)
    (hscore : MemLp (fun x ↦ deriv (fun t ↦ ell t x) theta₀) 2 P)
    (hmean : (∫ x, deriv (fun t ↦ ell t x) theta₀ ∂P) = 0)
    (hvar : (∫ x, deriv (fun t ↦ ell t x) theta₀ ^ 2 ∂P) = I)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀) P)
    (hinfo : (∫ x, deriv (deriv (fun t ↦ ell t x)) theta₀ ∂P) = -I)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : ∀ n : ℕ, 1 ≤ n → ∀ᵐ w ∂mu,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0) :
    TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        deriv (fun t ↦ ell t (X i w)) theta₀) 0 ∧
      TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hc3 : ∀ x, ContDiff ℝ (2 + 1) (fun t ↦ ell t x) := hsmooth
  have hdiff : ∀ x, Differentiable ℝ (fun t ↦ ell t x) := fun x ↦
    (contDiff_succ_iff_deriv.1 (hc3 x)).1
  have hdiff1 : ∀ x, Differentiable ℝ (fun t ↦ deriv (fun s ↦ ell s x) t) := fun x ↦
    ((contDiff_succ_iff_deriv.1 (hc3 x)).2.2).differentiable (by norm_num)
  set S : E → ℝ := fun x ↦ deriv (fun t ↦ ell t x) theta₀ with hSdef
  set H : E → ℝ := fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀ with hHdef
  have hSm : Measurable S := measurable_deriv_param ell hm hdiff theta₀
  have hℓ1m : ∀ t, Measurable (fun x ↦ deriv (fun s ↦ ell s x) t) :=
    measurable_deriv_param ell hm hdiff
  have hHm : Measurable H :=
    measurable_deriv_param (fun t x ↦ deriv (fun s ↦ ell s x) t) hℓ1m hdiff1 theta₀
  set M' : E → ℝ := hM.aestronglyMeasurable.mk M with hM'def
  have hM'm : Measurable M' := hM.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMM' : M =ᵐ[P] M' := hM.aestronglyMeasurable.ae_eq_mk
  have hM'i : Integrable M' P := hM.congr hMM'
  have hMae : ∀ᵐ w ∂mu, ∀ i, M (X i w) = M' (X i w) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ x ∂(mu.map (X i)), M x = M' x := by rw [hlaw i]; exact hMM'
    exact ae_of_ae_map (hXm i).aemeasurable this
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w) with hZ
  set B : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H (X i w) with hB
  set A : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M' (X i w) with hA
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ hSm.comp (hXm i)).const_mul _
  have hZlim : TendstoInDistribution mu Z (gaussianReal 0 (Real.toNNReal I)) := by
    have := tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu P X ⟨hXm, hind, hlaw⟩ S hSm
      hscore hmean
    rwa [hvar] at this
  have hBlim : TendstoInProbabilityConst mu B (-I) := by
    have := tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ H hHm hhess
    rwa [hinfo] at this
  have hAlim : TendstoInProbabilityConst mu A (∫ x, M' x ∂P) :=
    tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ M' hM'm hM'i
  set m : ℝ := ∫ x, M' x ∂P with hmdef
  have hrem : TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0 := by
    intro ε hε
    refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
    have hη5 : 0 < η / 5 := by positivity
    obtain ⟨K, hK, hZev⟩ :=
      exists_measureReal_lt_norm_le_of_tendstoInDistribution mu Z hZm _ hZlim hη5
    set κ : ℝ := min (I / 4) (ε * I ^ 2 / (8 * K)) with hκ
    have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
    have hκI : κ ≤ I / 4 := min_le_left _ _
    have hκK : 4 * κ * K / I ^ 2 ≤ ε / 2 := by
      have : κ ≤ ε * I ^ 2 / (8 * K) := min_le_right _ _
      rw [div_le_iff₀ (by positivity)]
      calc 4 * κ * K ≤ 4 * (ε * I ^ 2 / (8 * K)) * K := by gcongr
        _ = ε / 2 * I ^ 2 := by field_simp; ring
    have ev : ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) → ∀ᶠ n in atTop, u n ≤ η / 5 :=
      fun hu ↦ hu.eventually (eventually_le_nhds hη5)
    have hm1 : 0 < κ / (|m| + 1) := by positivity
    filter_upwards [hZev, ev (hcons (r / 2) (by positivity)), ev (hBlim κ hκpos),
      ev (hAlim 1 one_pos), ev (hcons _ hm1), eventually_ge_atTop 1]
      with n hZn h1 h2 h3 h4 hn1
    set N : Set Ω := {w | ¬ ((∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0 ∧
      ∀ i, M (X i w) = M' (X i w))} with hN
    have hnull : mu N = 0 := by
      have := (hroot n hn1).and hMae
      rwa [ae_iff] at this
    have hsub : {w | ε < dist (Real.sqrt n * (T n w - theta₀) -
        (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0} ⊆
        N ∪ {w | r / 2 < dist (T n w) theta₀} ∪ {w | κ < dist (B n w) (-I)} ∪
          {w | 1 < dist (A n w) m} ∪ {w | κ / (|m| + 1) < dist (T n w) theta₀} ∪
            {w | K < ‖Z n w‖} := by
      intro w hw
      by_contra hcon
      simp only [mem_union, not_or, mem_ofPred_eq, not_lt, hN, not_not] at hcon
      obtain ⟨⟨⟨⟨⟨⟨hroot', hM'w⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩ := hcon
      simp only [mem_ofPred_eq] at hw
      refine (not_lt.2 ?_) hw
      rw [Real.dist_eq] at g1 g2 g3 g4
      rw [Real.norm_eq_abs] at g5
      set d : ℝ := |T n w - theta₀| with hd
      have hdr : d < r := by linarith
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
      have hnsq : ((n : ℝ))⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      set R : ℕ → ℝ := fun i ↦ deriv (fun t ↦ ell t (X i w)) (T n w) - S (X i w) -
        (T n w - theta₀) * H (X i w) with hR
      have hRb : ∀ i, |R i| ≤ M' (X i w) * (T n w - theta₀) ^ 2 := fun i ↦ by
        rw [← hM'w i]
        exact abs_deriv_sub_taylor_le (fun t ↦ ell t (X i w)) (hsmooth _) theta₀ r (M (X i w))
          (fun t ht ↦ henv _ t ht) (T n w) hdr
      set q : ℝ := (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, R i with hq
      have hsumR : ∑ i ∈ Finset.range n, R i = -(∑ i ∈ Finset.range n, S (X i w)) -
          (T n w - theta₀) * ∑ i ∈ Finset.range n, H (X i w) := by
        simp only [hR, Finset.sum_sub_distrib, ← Finset.mul_sum, hroot']
        ring
      have heq : Z n w + Real.sqrt n * (T n w - theta₀) * B n w + q = 0 := by
        simp only [hZ, hB, hq, hsumR]
        rw [hnsq]
        field_simp
        ring
      have hqb : |q| ≤ |Real.sqrt n * (T n w - theta₀)| * (d * A n w) := by
        have h1 : |∑ i ∈ Finset.range n, R i| ≤
            (T n w - theta₀) ^ 2 * ∑ i ∈ Finset.range n, M' (X i w) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ ↦ (hRb i).trans_eq (mul_comm _ _)
        rw [hq, abs_mul, abs_inv, abs_of_pos hsn, abs_mul, abs_of_pos hsn, hd]
        calc (Real.sqrt n)⁻¹ * |∑ i ∈ Finset.range n, R i|
            ≤ (Real.sqrt n)⁻¹ * ((T n w - theta₀) ^ 2 * ∑ i ∈ Finset.range n, M' (X i w)) :=
              mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hsn.le)
          _ = Real.sqrt n * |T n w - theta₀| * (|T n w - theta₀| * A n w) := by
              simp only [hA]
              rw [← sq_abs (T n w - theta₀), hnsq]
              field_simp
      have hBI : |B n w + I| ≤ κ := by simpa [sub_neg_eq_add] using g2
      have hdA : d * A n w ≤ κ := by
        have hAabs : |A n w| ≤ |m| + 1 := by
          have := abs_sub_abs_le_abs_sub (A n w) m
          linarith
        have hd0 : 0 ≤ d := abs_nonneg _
        have hdk : d ≤ κ / (|m| + 1) := g4
        calc d * A n w ≤ d * |A n w| := mul_le_mul_of_nonneg_left (le_abs_self _) hd0
          _ ≤ d * (|m| + 1) := mul_le_mul_of_nonneg_left hAabs hd0
          _ ≤ κ / (|m| + 1) * (|m| + 1) := mul_le_mul_of_nonneg_right hdk (by positivity)
          _ = κ := div_mul_cancel₀ κ (by positivity)
      have hmain := abs_sub_div_le_of_score_equation hI hκI heq hqb hBI hdA
      have hform : Real.sqrt n * (T n w - theta₀) -
          (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w) =
          Real.sqrt n * (T n w - theta₀) - Z n w / I := by
        simp only [hZ]; rw [mul_inv]; ring
      rw [Real.dist_eq, sub_zero, hform]
      calc |Real.sqrt n * (T n w - theta₀) - Z n w / I| ≤ 4 * κ * |Z n w| / I ^ 2 := hmain
        _ ≤ 4 * κ * K / I ^ 2 := by gcongr
        _ ≤ ε / 2 := hκK
        _ ≤ ε := by linarith
    calc mu.real {w | ε < dist (Real.sqrt n * (T n w - theta₀) -
          (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0}
        ≤ mu.real (N ∪ {w | r / 2 < dist (T n w) theta₀} ∪ {w | κ < dist (B n w) (-I)} ∪
          {w | 1 < dist (A n w) m} ∪ {w | κ / (|m| + 1) < dist (T n w) theta₀} ∪
            {w | K < ‖Z n w‖}) := measureReal_mono hsub
      _ ≤ mu.real N + mu.real {w | r / 2 < dist (T n w) theta₀} +
          mu.real {w | κ < dist (B n w) (-I)} + mu.real {w | 1 < dist (A n w) m} +
          mu.real {w | κ / (|m| + 1) < dist (T n w) theta₀} + mu.real {w | K < ‖Z n w‖} := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measureReal_union_le _ _
      _ ≤ 0 + η / 5 + η / 5 + η / 5 + η / 5 + η / 5 := by
        rw [measureReal_def, hnull, ENNReal.toReal_zero]
        gcongr
      _ = η := by ring
  refine ⟨hrem, ?_⟩
  have hX' : TendstoInDistribution mu (fun n w ↦ I⁻¹ * Z n w)
      (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
    have := tendstoInDistribution_comp_of_continuous mu Z hZm _ (fun x ↦ I⁻¹ * x)
      (continuous_const.mul continuous_id) hZlim
    convert this using 1
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hI.le,
      Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]
    field_simp
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub mu _ _
    (fun n ↦ (hZm n).const_mul _) (fun n ↦ ((hT n).sub_const _).const_mul _) _ hX' ?_
  convert hrem using 3 with n w
  simp only [hZ]
  rw [mul_inv]
  ring

end CKSD
