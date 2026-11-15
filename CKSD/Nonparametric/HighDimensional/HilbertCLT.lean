module

import CKSD.Asymptotics.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.Probability.Moments.SampleMean
public import CKSD.Inference.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The central limit theorem in a separable Hilbert space

## Main results

* `CKSD.tendstoInDistribution_hilbert_sampleAverage`: the central limit theorem for i.i.d.
  square-integrable random elements of a separable Hilbert space.

The proof follows the classical route: the one-dimensional marginals obey the real central limit
theorem (`CKSD.tendstoInDistribution_inv_sqrt_mul_sum_of_iid`); the laws are tight, since their
second moments and the second moments of their distances to the finite-dimensional spans of a
dense sequence are controlled by TauCeti's Bienaymé identity
`TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`; Mathlib's Prokhorov theorem
`isCompact_closure_of_isTightMeasureSet` supplies a limit point, identified through its
marginals; and Mathlib's `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` with the
trigonometric polynomials `BoundedContinuousFunction.charPoly` gives convergence.

Source: GAPS 103.29.

## References

* T. Hsing and R. Eubank, *Theoretical Foundations of Functional Data Analysis, with an Introduction
  to Linear Operators*, Wiley, 2015.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- For i.i.d. square-integrable `X i` with law `P` and mean `m`, and a continuous linear map
`T`, the normalized centred sum `n^{-1/2} ∑_{i<n} (X i - m)` satisfies
`E ‖T(·)‖² ≤ ∫ ‖T (x - m)‖² dP` (with equality for `n ≥ 1`). -/
private lemma integral_norm_clm_normalizedSum_sq_le {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Measure H} [IsProbabilityMeasure P] {X : ℕ → Ω → H}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P) (T : H →L[ℝ] H)
    (n : ℕ) :
    ∫ ω, ‖T ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ z, z ∂P))‖ ^ 2 ∂μ ≤
      ∫ x, ‖T (x - ∫ z, z ∂P)‖ ^ 2 ∂P := by
  set m := ∫ z, z ∂P
  obtain ⟨hmeas, hind, hlaw⟩ := hiid
  have hf : Measurable fun x : H ↦ T (x - m) :=
    T.continuous.measurable.comp (measurable_id.sub_const m)
  have hLpP : MemLp (fun x : H ↦ T (x - m)) 2 P :=
    (h2.sub (memLp_const m)).continuousLinearMap_comp T
  have hLp : ∀ i, MemLp (fun ω ↦ T (X i ω - m)) 2 μ := fun i ↦ by
    rw [← hlaw i] at hLpP
    exact hLpP.comp_of_map (hmeas i).aemeasurable
  have hsq : ∀ i, ∫ ω, ‖T (X i ω - m)‖ ^ 2 ∂μ = ∫ x, ‖T (x - m)‖ ^ 2 ∂P := fun i ↦ by
    rw [← hlaw i, integral_map (hmeas i).aemeasurable
      (hf.norm.pow_const 2).aestronglyMeasurable]
  have hint : Integrable (fun x : H ↦ x) P := h2.integrable one_le_two
  have hmean : ∀ i, μ[fun ω ↦ T (X i ω - m)] = 0 := fun i ↦ by
    have : μ[fun ω ↦ T (X i ω - m)] = ∫ x, T (x - m) ∂P := by
      rw [← hlaw i, integral_map (hmeas i).aemeasurable hf.aestronglyMeasurable]
    have h3 : ∫ x, T (x - m) ∂P = T (∫ x, (x - m) ∂P) :=
      T.integral_comp_comm (hint.sub (integrable_const m))
    rw [this, h3, integral_sub hint (integrable_const m)]
    simp [m]
  have hindep : Set.Pairwise (↑(Finset.range n)) fun i j ↦
      IndepFun (fun ω ↦ T (X i ω - m)) (fun ω ↦ T (X j ω - m)) μ :=
    fun i _ j _ hij ↦ (hind.comp (fun _ ↦ fun x ↦ T (x - m)) (fun _ ↦ hf)).indepFun hij
  have key := TauCeti.integral_norm_sum_sq_of_pairwise_indepFun (fun i _ ↦ hLp i)
    (fun i _ ↦ hmean i) hindep
  have hc : 0 ≤ ∫ x, ‖T (x - m)‖ ^ 2 ∂P := integral_nonneg fun _ ↦ by positivity
  simp_rw [map_smul, map_sum, norm_smul, mul_pow]
  rw [integral_const_mul, key, Finset.sum_congr rfl (fun i _ ↦ hsq i), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hc
  · rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Chebyshev's inequality for a square-integrable random vector: `μ {r ≤ ‖f‖} ≤ c / r²`
whenever `E ‖f‖² ≤ c`. -/
private lemma measure_le_norm_le_ofReal_div_sq {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → H} (hf : MemLp f 2 μ) {r : ℝ} (hr : 0 < r) {c : ℝ}
    (hc : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ c) :
    μ {ω | r ≤ ‖f ω‖} ≤ ENNReal.ofReal (c / r ^ 2) := by
  have hint : Integrable (fun ω ↦ ‖f ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ by positivity) hint (r ^ 2)
  have hset : {ω | r ≤ ‖f ω‖} = {ω | r ^ 2 ≤ ‖f ω‖ ^ 2} := by
    ext ω
    simp only [mem_ofPred_eq]
    exact (pow_le_pow_iff_left₀ hr.le (norm_nonneg _) two_ne_zero).symm
  rw [hset, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- In a Hilbert space, the set of points of norm at most `R` that lie within `1 / (j + 1)` of
the finite-dimensional subspace `V (k j)` for every `j` is compact. -/
private lemma isCompact_closedBall_inter_iInter_norm_sub_starProjection_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (V : ℕ → Submodule ℝ H)
    [∀ k, FiniteDimensional ℝ (V k)] (k : ℕ → ℕ) (R : ℝ) :
    IsCompact (Metric.closedBall (0 : H) R ∩
      ⋂ j : ℕ, {x | ‖x - (V (k j)).starProjection x‖ ≤ 1 / ((j : ℝ) + 1)}) := by
  refine TotallyBounded.isCompact_of_isClosed ?_ ?_
  · rw [Metric.totallyBounded_iff]
    intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hδ)
    set W := V (k j)
    have hC : IsCompact ((↑) '' Metric.closedBall (0 : W) R : Set H) :=
      (isCompact_closedBall 0 R).image continuous_subtype_val
    obtain ⟨t, ht, hcover⟩ :=
      Metric.totallyBounded_iff.1 hC.totallyBounded (δ / 2) (half_pos hδ)
    refine ⟨t, ht, fun x hx ↦ ?_⟩
    have hxR : ‖x‖ ≤ R := by simpa using hx.1
    have hxj : ‖x - W.starProjection x‖ ≤ 1 / ((j : ℝ) + 1) := (mem_iInter.1 hx.2) j
    have hy : W.starProjection x ∈ ((↑) '' Metric.closedBall (0 : W) R : Set H) :=
      ⟨W.orthogonalProjectionOnto x, by
        simpa using (W.norm_orthogonalProjectionOnto_apply_le x).trans hxR, rfl⟩
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hcover hy)
    refine mem_iUnion₂.2 ⟨z, hz, ?_⟩
    rw [Metric.mem_ball] at hyz ⊢
    calc dist x z ≤ dist x (W.starProjection x) + dist (W.starProjection x) z :=
          dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by
          rw [dist_eq_norm]
          exact add_lt_add_of_le_of_lt (hxj.trans hj.le) hyz
      _ = δ := add_halves δ
  · refine Metric.isClosed_closedBall.inter (isClosed_iInter fun j ↦ ?_)
    exact isClosed_le (by fun_prop) continuous_const

/-- Tightness criterion in a Hilbert space: if `V k` are finite-dimensional subspaces, the second
moments `E ‖Z n‖²` are bounded uniformly in `n`, and the second moments of the distances
`‖Z n - P_{V k} Z n‖` are bounded by `c k → 0` uniformly in `n`, then the laws of the `Z n` form
a tight family. -/
private lemma isTightMeasureSet_range_map_of_integral_norm_sub_starProjection_le
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : ℕ → Submodule ℝ H) [∀ k, FiniteDimensional ℝ (V k)]
    {Z : ℕ → Ω → H} (hZ : ∀ n, Measurable (Z n)) (hZ2 : ∀ n, MemLp (Z n) 2 μ)
    {s : ℝ} (hs : ∀ n, ∫ ω, ‖Z n ω‖ ^ 2 ∂μ ≤ s)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hcZ : ∀ n k, ∫ ω, ‖Z n ω - (V k).starProjection (Z n ω)‖ ^ 2 ∂μ ≤ c k) :
    IsTightMeasureSet (Set.range fun n ↦ μ.map (Z n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ le_top⟩
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε2 ℕ
  have hk : ∀ j : ℕ, ∃ k, c k * ((j : ℝ) + 1) ^ 2 ≤ ε' j := by
    intro j
    have : Tendsto (fun k ↦ c k * ((j : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
      simpa using hc.mul_const (((j : ℝ) + 1) ^ 2)
    exact (this.eventually (ge_mem_nhds (NNReal.coe_pos.mpr (hε'pos j)))).exists
  choose k hk using hk
  have hη : 0 < (ε / 2).toReal :=
    ENNReal.toReal_pos hε2 (ENNReal.div_ne_top hεtop two_ne_zero)
  have hRlim : Tendsto (fun R : ℝ ↦ s / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  obtain ⟨R, hR, hR0⟩ :=
    ((hRlim.eventually (ge_mem_nhds hη)).and (eventually_gt_atTop 0)).exists
  set K := Metric.closedBall (0 : H) R ∩
    ⋂ j : ℕ, {x | ‖x - (V (k j)).starProjection x‖ ≤ 1 / ((j : ℝ) + 1)} with hKdef
  have hK := isCompact_closedBall_inter_iInter_norm_sub_starProjection_le V k R
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [Measure.map_apply (hZ n) hK.isClosed.measurableSet.compl]
  have hsub : Z n ⁻¹' Kᶜ ⊆ {ω | R ≤ ‖Z n ω‖} ∪
      ⋃ j : ℕ, {ω | 1 / ((j : ℝ) + 1) ≤ ‖Z n ω - (V (k j)).starProjection (Z n ω)‖} := by
    intro ω hω
    simp only [K, mem_preimage, mem_compl_iff, mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, mem_iInter, mem_ofPred_eq, not_and_or, not_forall, not_le] at hω
    rcases hω with h | ⟨j, hj⟩
    · exact Or.inl h.le
    · exact Or.inr (mem_iUnion.2 ⟨j, hj.le⟩)
  calc μ (Z n ⁻¹' Kᶜ)
      ≤ μ {ω | R ≤ ‖Z n ω‖} + μ (⋃ j : ℕ,
          {ω | 1 / ((j : ℝ) + 1) ≤ ‖Z n ω - (V (k j)).starProjection (Z n ω)‖}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ε / 2 + ∑' j, (ε' j : ℝ≥0∞) := by
        refine add_le_add ?_ ((measure_iUnion_le _).trans (tsum_le_tsum fun j ↦ ?_))
        · refine (measure_le_norm_le_ofReal_div_sq (hZ2 n) hR0 (hs n)).trans ?_
          rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top hεtop two_ne_zero)]
          exact ENNReal.ofReal_le_ofReal hR
        · have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
          refine (measure_le_norm_le_ofReal_div_sq
            ((hZ2 n).sub ((hZ2 n).continuousLinearMap_comp _)) hj (hcZ n (k j))).trans ?_
          rw [← ENNReal.ofReal_coe_nnreal]
          refine ENNReal.ofReal_le_ofReal ?_
          calc c (k j) / (1 / ((j : ℝ) + 1)) ^ 2 = c (k j) * ((j : ℝ) + 1) ^ 2 := by
                field_simp
            _ ≤ (ε' j : ℝ) := hk j
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hε'sum.le
    _ = ε := ENNReal.add_halves ε

/-- The laws of `√n (X̄_n - m)` for i.i.d. square-integrable `X i` in a separable Hilbert
space form a tight family: their distances to the spans of the first `k` terms of a dense
sequence have second moments bounded, uniformly in `n`, by `E ‖(I - P_k)(X - m)‖² → 0`. -/
private lemma isTightMeasureSet_range_map_of_eq_normalizedSum {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure H} [IsProbabilityMeasure P]
    {X : ℕ → Ω → H} (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    {Z : ℕ → Ω → H}
    (hZeq : ∀ n ω, Z n ω = (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ z, z ∂P))
    (hZm : ∀ n, Measurable (Z n)) (hZ2 : ∀ n, MemLp (Z n) 2 μ) :
    IsTightMeasureSet (Set.range fun n ↦ μ.map (Z n)) := by
  set m := ∫ z, z ∂P with hm
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  set V : ℕ → Submodule ℝ H := fun k ↦ Submodule.span ℝ (d '' {i | i < k}) with hV
  have : ∀ k, FiniteDimensional ℝ (V k) := fun k ↦
    FiniteDimensional.span_of_finite ℝ ((Set.finite_lt_nat k).image d)
  have hVmono : Monotone V := fun k l hkl ↦
    Submodule.span_mono (Set.image_mono fun i (hi : i < k) ↦ lt_of_lt_of_le hi hkl)
  have hVdense : ⊤ ≤ (⨆ k, V k).topologicalClosure := by
    intro x _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine closure_mono (fun y hy ↦ ?_) (hd x)
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.mem_iSup_of_mem (i + 1)
      (Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩)
  have hnorm_sub : ∀ k (y : H), ‖y - (V k).starProjection y‖ ≤ ‖y‖ := fun k y ↦ by
    have := (V k).starProjection_add_starProjection_orthogonal y
    rw [← eq_sub_iff_add_eq'] at this
    rw [← this]
    exact (V k)ᗮ.norm_starProjection_apply_le y
  set c : ℕ → ℝ := fun k ↦ ∫ x, ‖(x - m) - (V k).starProjection (x - m)‖ ^ 2 ∂P with hc
  have hint2 : Integrable (fun x : H ↦ ‖x - m‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm (h2.sub (memLp_const m)).aestronglyMeasurable).1
      (h2.sub (memLp_const m))
  have hclim : Tendsto c atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun k x ↦ ‖(x - m) - (V k).starProjection (x - m)‖ ^ 2) (f := fun _ ↦ 0)
      (fun x ↦ ‖x - m‖ ^ 2) (fun k ↦ by fun_prop) hint2
      (fun k ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hnorm_sub k _) 2)
      (ae_of_all _ fun x ↦ by
        have h := Submodule.starProjection_tendsto_self V hVmono (x - m) hVdense
        have h' := ((tendsto_const_nhds (x := x - m)).sub h).norm.pow 2
        simpa using h')
    simpa only [integral_zero] using this
  have hs : ∀ n, ∫ ω, ‖Z n ω‖ ^ 2 ∂μ ≤ ∫ x, ‖x - m‖ ^ 2 ∂P := fun n ↦ by
    simp only [hZeq]
    exact integral_norm_clm_normalizedSum_sq_le hiid h2 (ContinuousLinearMap.id ℝ H) n
  have hcZ : ∀ n k, ∫ ω, ‖Z n ω - (V k).starProjection (Z n ω)‖ ^ 2 ∂μ ≤ c k := fun n k ↦ by
    simp only [hZeq]
    exact integral_norm_clm_normalizedSum_sq_le hiid h2
      (ContinuousLinearMap.id ℝ H - (V k).starProjection) n
  exact isTightMeasureSet_range_map_of_integral_norm_sub_starProjection_le V hZm hZ2
    hs hclim hcZ

/-- GAPS 103.29: the central limit theorem in a separable Hilbert space. For i.i.d.
square-integrable `X_i` with mean `m`, `√n (X̄_n - m)` converges in law to a centred Gaussian
measure `G`, characterized by its one-dimensional marginals
`⟪u, ·⟫_* G = N(0, E ⟪u, X - m⟫²)`. -/
theorem tendstoInDistribution_hilbert_sampleAverage {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure H) [IsProbabilityMeasure P]
    (X : ℕ → Ω → H) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P) :
    ∃ (G : Measure H) (_ : IsProbabilityMeasure G),
      (∀ u : H, G.map (fun x ↦ inner ℝ u x) =
        gaussianReal 0 (Real.toNNReal (∫ x, (inner ℝ u (x - ∫ z, z ∂P)) ^ 2 ∂P))) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (sampleAverage X n ω - ∫ z, z ∂P))
        atTop id (fun _ ↦ μ) G := by
  set m := ∫ z, z ∂P with hm
  have hmeas := hiid.1
  have hlaw := hiid.2.2
  set Z : ℕ → Ω → H := fun n ω ↦ Real.sqrt n • (sampleAverage X n ω - m) with hZdef
  have hZeq : ∀ n ω, Z n ω = (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - m) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Z, sampleAverage]
    have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have h1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      field_simp; linarith
    have h3 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      field_simp; linarith
    simp only [Z, sampleAverage, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      smul_sub, smul_smul, h1, ← Nat.cast_smul_eq_nsmul ℝ, h3]
  have hXLp : ∀ i, MemLp (fun ω ↦ X i ω - m) 2 μ := fun i ↦ by
    have h2' := h2
    rw [← hlaw i] at h2'
    exact (h2'.comp_of_map (hmeas i).aemeasurable).sub (memLp_const m)
  have hZm : ∀ n, Measurable (Z n) := fun n ↦ by
    simp only [Z, sampleAverage]
    fun_prop
  have hZ2 : ∀ n, MemLp (Z n) 2 μ := fun n ↦ by
    have : Z n = fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (X i ω - m) :=
      funext (hZeq n)
    rw [this]
    exact (memLp_finsetSum (Finset.range n) fun i _ ↦ hXLp i).const_smul ((Real.sqrt n)⁻¹ : ℝ)
  -- one-dimensional marginals: the classical central limit theorem
  set σ : H → ℝ≥0 := fun t ↦ Real.toNNReal (∫ x, (inner ℝ t (x - m)) ^ 2 ∂P) with hσ
  have hclt : ∀ t : H, TendstoInDistribution (fun n ω ↦ inner ℝ t (Z n ω)) atTop id
      (fun _ ↦ μ) (gaussianReal 0 (σ t)) := by
    intro t
    have hs : Measurable fun x : H ↦ inner ℝ t (x - m) := by fun_prop
    have hint : Integrable (fun x : H ↦ x) P := h2.integrable one_le_two
    have hs2 : MemLp (fun x : H ↦ inner ℝ t (x - m)) 2 P :=
      (h2.sub (memLp_const m)).continuousLinearMap_comp (innerSL ℝ t)
    have hs0 : ∫ x, inner ℝ t (x - m) ∂P = 0 := by
      have h3 : ∫ x, inner ℝ t (x - m) ∂P = inner ℝ t (∫ x, (x - m) ∂P) :=
        integral_inner (hint.sub (integrable_const m)) t
      rw [h3, integral_sub hint (integrable_const m)]
      simp [m]
    refine (tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid _ hs hs2 hs0).congr
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
    dsimp only
    rw [hZeq n ω, inner_smul_right, inner_sum]
  have htight := isTightMeasureSet_range_map_of_eq_normalizedSum hiid h2 hZeq hZm hZ2
  -- a limit point `G` of the laws, by Prokhorov's theorem
  let ν : ℕ → ProbabilityMeasure H := fun n ↦
    ⟨μ.map (Z n), inferInstance⟩
  have htight' : IsTightMeasureSet {(ν n : Measure H) | n} := htight
  have hcomp : IsCompact (closure (Set.range ν)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight')
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨G, -, hG⟩ := hcomp.ultrafilter_le_nhds (U.map ν)
    (.trans (by simp) (monotone_principal subset_closure))
  have hGU : Tendsto ν U (𝓝 G) := hG
  -- identification of the one-dimensional marginals of `G`
  have hmarg : ∀ u : H, (G : Measure H).map (fun x ↦ inner ℝ u x) = gaussianReal 0 (σ u) := by
    intro u
    have hcont : Continuous fun x : H ↦ inner ℝ u x := continuous_const.inner continuous_id
    have hA : Tendsto (fun n ↦ (ν n).map (fun x ↦ inner ℝ u x)) U
        (𝓝 (G.map (fun x ↦ inner ℝ u x))) :=
      ((ProbabilityMeasure.continuous_map hcont).tendsto G).comp hGU
    have hB := (hclt u).tendsto.mono_left (Ultrafilter.of_le atTop)
    have hAB : (fun n ↦ (ν n).map (fun x ↦ inner ℝ u x)) = fun n ↦
        (⟨μ.map (fun ω ↦ inner ℝ u (Z n ω)), inferInstance⟩ : ProbabilityMeasure ℝ) := by
      funext n
      apply Subtype.ext
      simp only [ν]
      exact Measure.map_map hcont.measurable (hZm n)
    rw [hAB] at hA
    have := congrArg (fun ρ : ProbabilityMeasure ℝ ↦ (ρ : Measure ℝ)) (tendsto_nhds_unique hA hB)
    simpa using this
  -- convergence of the characteristic functions to that of `G`
  have hchar : ∀ t : H, Tendsto (fun n ↦ charFun (ν n : Measure H) t) atTop
      (𝓝 (charFun (G : Measure H) t)) := by
    intro t
    have h1 : ∀ n, charFun (ν n : Measure H) t =
        charFun (μ.map (fun ω ↦ inner ℝ t (Z n ω))) (1 : ℝ) := fun n ↦ by
      -- unfold the coercion of the probability measure `ν n` for the `rw` below
      change charFun (μ.map (Z n)) t = _
      rw [charFun_map_eq_charFun_map_inner_one (hZm n).aemeasurable]
      simp_rw [real_inner_comm t]
    have h2' : charFun (G : Measure H) t = charFun (gaussianReal 0 (σ t)) (1 : ℝ) := by
      have := charFun_map_eq_charFun_map_inner_one (μ := (G : Measure H)) aemeasurable_id t
      rw [Measure.map_id] at this
      rw [this, ← hmarg t]
      simp_rw [id, real_inner_comm t]
    simp_rw [h1, h2']
    simpa using (hclt t).tendsto_charFun 1
  refine ⟨G, inferInstance, hmarg, ⟨fun n ↦ (hZm n).aemeasurable, aemeasurable_id, ?_⟩⟩
  have hsep := BoundedContinuousFunction.separatesPoints_charPoly Real.continuous_probChar
    Real.probChar_ne_one
    (L := innerₗ H) continuous_inner
    (fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩)
  have := ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ htight' hsep
    (fun g hg ↦ ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun hchar hg)
  convert this using 2
  exact congrArg 𝓝 (Subtype.ext (Measure.map_id (μ := (G : Measure H))))

end CKSD
