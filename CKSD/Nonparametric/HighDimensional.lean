module

public import CKSD.Nonparametric.LowerBounds
public import CKSD.Nonparametric.Models
public import CKSD.Asymptotics.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import TauCeti.Probability.Moments.SampleMean


/-!
# Principal components, the lasso, and false discovery rate control

Results on high-dimensional estimation and multiple testing: the central limit theorem in a
separable Hilbert space, the optimality of principal components for reconstruction, the
deterministic analysis of the lasso, and the Benjamini–Hochberg procedure.

## Main definitions

* `CKSD.benjaminiHochbergFalseDiscoveryProportion`: the proportion of true null hypotheses among
  the rejections of the Benjamini–Hochberg procedure.

## Main results

* `CKSD.tendsto_in_distribution_hilbert_sample_average`: the central limit theorem for i.i.d.
  square-integrable random elements of a separable Hilbert space.
* `CKSD.sum_ite_le_integral_norm_sub_sum_inner_smul_sq`: no projection onto `k` orthonormal
  directions has expected reconstruction error below the sum of the trailing eigenvalues of the
  covariance.
* `CKSD.IsLassoEstimator.norm_apply_sub_sq_div_le`: the basic inequality of the lasso, with the
  cone condition `CKSD.IsLassoEstimator.restricted_l1_norm_compl_sub_le` and the prediction and
  `ℓ¹` error bounds under compatibility.
* `CKSD.integral_benjamini_hochberg_false_discovery_proportion_le`: the Benjamini–Hochberg
  procedure at level `α` controls the false discovery rate at `α m₀ / m` for independent
  p-values whose null p-values are superuniform.

The Hilbert-space central limit theorem is proved by the classical route: the one-dimensional
marginals obey the real central limit theorem
(`CKSD.tendsto_in_distribution_inv_sqrt_mul_sum_of_iid`);
the laws are tight, since their second moments and the second moments of their distances to the
finite-dimensional spans of a dense sequence are controlled by TauCeti's Bienaymé identity
`TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`; Mathlib's Prokhorov theorem
`isCompact_closure_of_isTightMeasureSet` supplies a limit point, identified through its
marginals; and Mathlib's `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` with the
trigonometric polynomials `BoundedContinuousFunction.charPoly` gives convergence.

Sources: GAPS 103.29, 103.31, 103.34, and 103.37.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- For i.i.d. square-integrable `X i` with law `P` and mean `m`, and a continuous linear map
`T`, the normalized centred sum `n^{-1/2} ∑_{i<n} (X i - m)` satisfies
`E ‖T(·)‖² ≤ ∫ ‖T (x - m)‖² dP` (with equality for `n ≥ 1`). -/
private lemma integral_norm_clm_normalized_sum_sq_le {Ω H : Type*} [MeasurableSpace Ω]
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
private lemma measure_le_norm_le_of_real_div_sq {Ω H : Type*} [MeasurableSpace Ω]
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
private lemma is_compact_closed_ball_inter_i_inter_norm_sub_star_projection_le {H : Type*}
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
private lemma is_tight_measure_set_range_map_of_integral_norm_sub_star_projection_le
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
  have hK := is_compact_closed_ball_inter_i_inter_norm_sub_star_projection_le V k R
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
        · refine (measure_le_norm_le_of_real_div_sq (hZ2 n) hR0 (hs n)).trans ?_
          rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top hεtop two_ne_zero)]
          exact ENNReal.ofReal_le_ofReal hR
        · have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
          refine (measure_le_norm_le_of_real_div_sq
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
private lemma is_tight_measure_set_range_map_of_eq_normalized_sum {Ω H : Type*} [MeasurableSpace Ω]
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
    exact integral_norm_clm_normalized_sum_sq_le hiid h2 (ContinuousLinearMap.id ℝ H) n
  have hcZ : ∀ n k, ∫ ω, ‖Z n ω - (V k).starProjection (Z n ω)‖ ^ 2 ∂μ ≤ c k := fun n k ↦ by
    simp only [hZeq]
    exact integral_norm_clm_normalized_sum_sq_le hiid h2
      (ContinuousLinearMap.id ℝ H - (V k).starProjection) n
  exact is_tight_measure_set_range_map_of_integral_norm_sub_star_projection_le V hZm hZ2
    hs hclim hcZ

/-- GAPS 103.29: the central limit theorem in a separable Hilbert space. For i.i.d.
square-integrable `X_i` with mean `m`, `√n (X̄_n - m)` converges in law to a centred Gaussian
measure `G`, characterized by its one-dimensional marginals
`⟪u, ·⟫_* G = N(0, E ⟪u, X - m⟫²)`. -/
theorem tendsto_in_distribution_hilbert_sample_average {Ω H : Type*} [MeasurableSpace Ω]
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
    refine (tendsto_in_distribution_inv_sqrt_mul_sum_of_iid μ P X hiid _ hs hs2 hs0).congr
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
    show _ = inner ℝ t (Z n ω)
    rw [hZeq n ω, inner_smul_right, inner_sum]
  have htight := is_tight_measure_set_range_map_of_eq_normalized_sum hiid h2 hZeq hZm hZ2
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

/-- Pythagoras for the projection onto the span of an orthonormal family. -/
theorem norm_sub_sum_inner_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (q : Fin k → E) (hq : Orthonormal ℝ q) (y : E) :
    ‖y - ∑ j, inner ℝ y (q j) • q j‖ ^ 2 = ‖y‖ ^ 2 - ∑ j, inner ℝ y (q j) ^ 2 := by
  have h1 : inner ℝ y (∑ j, inner ℝ y (q j) • q j) = ∑ j, inner ℝ y (q j) ^ 2 := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [real_inner_smul_right, sq]
  have h2 : ‖∑ j, inner ℝ y (q j) • q j‖ ^ 2 = ∑ j, inner ℝ y (q j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_left, hq.inner_right_fintype, sq]
  rw [norm_sub_sq_real, h1, h2]
  ring

/-- GAPS 103.31: principal components minimize the expected reconstruction error, in finite
dimension and about any specified center `m`. If the second-moment operator of `X - m` is
diagonal in the orthonormal basis `e` with nonincreasing eigenvalues `λ_j`, then no projection
onto the span of `k` orthonormal vectors `q_i` has expected squared reconstruction error below
the trailing eigenvalue sum `∑_{j ≥ k} λ_j`. Attainment by the leading eigenvectors,
uniqueness, and the Hilbert-space case are not asserted. -/
theorem sum_ite_le_integral_norm_sub_sum_inner_smul_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : MemLp X 2 μ) (m : E) (e : OrthonormalBasis (Fin d) ℝ E)
    (lambda : Fin d → ℝ) (hlambda : Antitone lambda)
    (hcov : ∀ i j, (∫ ω, inner ℝ (X ω - m) (e i) * inner ℝ (X ω - m) (e j) ∂μ) =
      if i = j then lambda i else 0)
    (q : Fin k → E) (hq : Orthonormal ℝ q) :
    (∑ j : Fin d, if k ≤ j.val then lambda j else 0) ≤
      ∫ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 ∂μ := by
  have : FiniteDimensional ℝ E := e.toBasis.finiteDimensional_of_finite
  have hk : k ≤ d := by
    simpa [Module.finrank_eq_card_basis e.toBasis] using
      hq.linearIndependent.fintype_card_le_finrank
  set y := fun (j : Fin d) (ω : Ω) ↦ inner ℝ (X ω - m) (e j) with hy
  set w := fun (i : Fin k) (j : Fin d) ↦ inner ℝ (e j) (q i) with hw
  have hY : MemLp (fun ω ↦ X ω - m) 2 μ := hX.sub (memLp_const m)
  have hyL2 : ∀ j, MemLp (y j) 2 μ := fun j ↦ MemLp.inner_const (𝕜 := ℝ) hY (e j)
  have hint : ∀ j l, Integrable (fun ω ↦ y j ω * y l ω) μ := fun j l ↦
    (hyL2 j).integrable_mul (hyL2 l)
  -- pointwise expansion in the eigenbasis
  have hpt : ∀ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 =
      ∑ j, y j ω * y j ω - ∑ i, ∑ j, ∑ l, w i j * w i l * (y j ω * y l ω) := by
    intro ω
    rw [norm_sub_sum_inner_smul_sq q hq, ← e.sum_sq_inner_left]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [sq]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← e.sum_inner_mul_inner, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [hy, hw]; ring
  have hInt : ∫ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 ∂μ =
      ∑ j, lambda j - ∑ j, lambda j * ∑ i, w i j ^ 2 := by
    simp_rw [hpt]
    rw [integral_sub (integrable_finsetSum _ fun j _ ↦ hint j j)
      (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        integrable_finsetSum _ fun l _ ↦ (hint j l).const_mul _),
      integral_finsetSum _ fun j _ ↦ hint j j,
      integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        integrable_finsetSum _ fun l _ ↦ (hint j l).const_mul _]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [hcov j j]; simp
    · have hi : ∀ i, ∫ a, ∑ j, ∑ l, w i j * w i l * (y j a * y l a) ∂μ =
          ∑ j, lambda j * w i j ^ 2 := by
        intro i
        rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun l _ ↦
          (hint j l).const_mul _]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [integral_finsetSum _ fun l _ ↦ (hint j l).const_mul _]
        simp_rw [integral_const_mul]
        simp only [hy, hcov, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
      simp_rw [hi]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
  rcases hk.lt_or_eq with hlt | heq
  swap
  · have hzero : (∑ j : Fin d, if k ≤ j.val then lambda j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by simp only [show ¬ k ≤ j.val by omega, ↓reduceIte]
    rw [hzero]
    exact integral_nonneg fun ω ↦ by positivity
  rw [hInt]
  have hc1 : ∀ j, ∑ i, w i j ^ 2 ≤ 1 := by
    intro j
    have := hq.sum_inner_products_le (x := e j) (s := Finset.univ)
    simpa [hw, real_inner_comm, e.orthonormal.1 j] using this
  have hc0 : ∀ j, 0 ≤ ∑ i, w i j ^ 2 := fun j ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hcsum : ∑ j, ∑ i, w i j ^ 2 = k := by
    rw [Finset.sum_comm]
    have : ∀ i, ∑ j, w i j ^ 2 = 1 := by
      intro i
      simp only [hw]
      rw [e.sum_sq_inner_right (q i), hq.1 i]
      norm_num
    simp [this]
  set t := lambda ⟨k, hlt⟩ with ht
  have hterm : ∀ j : Fin d,
      0 ≤ (lambda j - t) * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) := by
    intro j
    by_cases hj : j.val < k
    · simp only [hj, ↓reduceIte]
      apply mul_nonneg
      · exact sub_nonneg.mpr (hlambda (Fin.le_def.mpr (by simpa using hj.le)))
      · linarith [hc1 j]
    · simp only [hj, ↓reduceIte]
      apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (hlambda (by simp [Fin.le_def]; omega))
      · linarith [hc0 j]
  have hsumind : ∑ j : Fin d, (if j.val < k then (1 : ℝ) else 0) = k := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_filter_val_lt,
      min_eq_right hk]
  have hexp : ∀ j : Fin d, (lambda j - t) * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) =
      ((if j.val < k then lambda j else 0) - lambda j * ∑ i, w i j ^ 2) -
        t * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) := by
    intro j; split_ifs <;> ring
  have htot := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hterm j
  rw [Finset.sum_congr rfl fun j _ ↦ hexp j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hsumind, hcsum, sub_self, mul_zero,
    sub_zero] at htot
  have hsplit : ∑ j, lambda j = ∑ j : Fin d, (if j.val < k then lambda j else 0) +
      ∑ j : Fin d, (if k ≤ j.val then lambda j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j.val < k
    · simp only [hj, show ¬ k ≤ j.val by omega, ↓reduceIte, add_zero]
    · simp only [hj, show k ≤ j.val by omega, ↓reduceIte, zero_add]
  linarith

/-- The coordinate `ℓ¹` norm is convex along segments:
`‖x - h (x - y)‖₁ ≤ (1 - h) ‖x‖₁ + h ‖y‖₁` for `0 ≤ h ≤ 1`. -/
theorem restricted_l1_norm_sub_smul_sub_le {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    restrictedL1Norm S (x - h • (x - y)) ≤
      (1 - h) * restrictedL1Norm S x + h * restrictedL1Norm S y := by
  unfold restrictedL1Norm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have : (x - h • (x - y)) j = (1 - h) * x j + h * y j := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this]
  calc |(1 - h) * x j + h * y j| ≤ |(1 - h) * x j| + |h * y j| := abs_add_le _ _
    _ = (1 - h) * |x j| + h * |y j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]

/-- The basic inequality of the lasso. Let `y = A β + ε` with `β` supported in `S`, and let `b`
be a lasso estimate with penalty `λ > 0` on the noise event `|⟪ε, A δ⟫| / n ≤ λ ‖δ‖₁ / 2`.
Then `‖A (b - β)‖² / n ≤ (3λ/2) ‖(b - β)_S‖₁ - (λ/2) ‖(b - β)_{Sᶜ}‖₁`. -/
theorem IsLassoEstimator.norm_apply_sub_sq_div_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda)
    (S : Finset (Fin p)) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ) :
    ‖A (b - β)‖ ^ 2 / n ≤
      3 * lambda / 2 * restrictedL1Norm S (b - β) - lambda / 2 * restrictedL1Norm Sᶜ (b - β) := by
  have hmin : ∀ t, ‖A β + ε - A b‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b ≤
      ‖A β + ε - A t‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ t := hb
  set δ := b - β with hδ
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set u' := ‖A δ‖ ^ 2 with hu'
  set e := inner ℝ ε (A δ) with he
  -- first-order condition of the lasso along the segment towards `β`
  have hvar : ∀ h : ℝ, 0 < h → h ≤ 1 →
      u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
        restrictedL1Norm Finset.univ b) + h * u' / (2 * n) := by
    intro h h0 h1
    have hm := hmin (b - h • δ)
    have hr : A β + ε - A b = ε - A δ := by rw [hδ, map_sub]; abel
    have hr' : A β + ε - A (b - h • δ) = (ε - A δ) + h • A δ := by
      rw [map_sub, map_smul, hδ, map_sub]; abel
    rw [hr, hr', norm_add_sq_real, norm_smul, inner_smul_right, inner_sub_left,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos h0] at hm
    have hl1 := restricted_l1_norm_sub_smul_sub_le Finset.univ b β h h0.le h1
    rw [← hδ] at hl1
    have key : 0 ≤ h * ((e - u') / n + h * u' / (2 * n) +
        lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) := by
      have : h * ((e - u') / n + h * u' / (2 * n) +
          lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) =
          ((‖ε - A δ‖ ^ 2 + 2 * (h * (e - u')) + (h * ‖A δ‖) ^ 2) / (2 * n) +
            lambda * ((1 - h) * restrictedL1Norm Finset.univ b +
              h * restrictedL1Norm Finset.univ β)) -
          (‖ε - A δ‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b) := by
        rw [hu']; field_simp; ring
      rw [this, sub_nonneg]
      refine hm.trans ?_
      gcongr
    have := (mul_nonneg_iff_of_pos_left h0).mp key
    have h2 : (e - u') / n = e / n - u' / n := by ring
    linarith
  have hvar' : u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b) := by
    by_contra hcon
    rw [not_le] at hcon
    set gapv := u' / n - (e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b)) with hgap
    have hgpos : 0 < gapv := by linarith
    have hc : 0 ≤ u' / (2 * n) := by positivity
    set h := min 1 (gapv / (2 * (u' / (2 * n) + 1))) with hh
    have hpos : 0 < h := lt_min one_pos (by positivity)
    have hle : h ≤ 1 := min_le_left _ _
    have hle2 : h ≤ gapv / (2 * (u' / (2 * n) + 1)) := min_le_right _ _
    have := hvar h hpos hle
    have hmul : h * (u' / (2 * n)) ≤ gapv / 2 := by
      calc h * (u' / (2 * n)) ≤ gapv / (2 * (u' / (2 * n) + 1)) * (u' / (2 * n) + 1) := by
            apply mul_le_mul hle2 (by linarith) hc (by positivity)
        _ = gapv / 2 := by
            have hgen : ∀ g q : ℝ, q ≠ 0 → g / (2 * q) * q = g / 2 := by
              intro g q hq; field_simp
            exact hgen _ _ (by positivity)
    have : h * u' / (2 * n) = h * (u' / (2 * n)) := by ring
    linarith
  -- split the `L1` norms over `S` and its complement
  have hβc : restrictedL1Norm Sᶜ β = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsupp j (Finset.mem_compl.mp hj), abs_zero]
  have hcomp : restrictedL1Norm Sᶜ δ = restrictedL1Norm Sᶜ b := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hδ, PiLp.sub_apply, hsupp j (Finset.mem_compl.mp hj), sub_zero]
  have htri := restricted_l1_norm_le_add_sub S β b
  have hsβ := restricted_l1_norm_add_compl S β
  have hsb := restricted_l1_norm_add_compl S b
  have hsδ := restricted_l1_norm_add_compl S δ
  have hnz := hnoise δ
  have habs := neg_abs_le e
  have habs' := le_abs_self e
  set a := restrictedL1Norm S δ
  set c := restrictedL1Norm Sᶜ δ
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have he' : e / n ≤ |e| / n := div_le_div_of_nonneg_right habs' hN.le
  have hu0 : 0 ≤ u' / n := by positivity
  -- the main inequality `u ≤ (3λ/2) a - (λ/2) c`
  have hmain : u' / n ≤ 3 * lambda / 2 * a - lambda / 2 * c := by
    rw [← hsδ] at hnz
    nlinarith
  exact hmain

/-- GAPS 103.34: the cone condition for the lasso. Under the noise event
`|⟪ε, A δ⟫| / n ≤ λ ‖δ‖₁ / 2`, the error `δ = b - β` of a lasso estimate satisfies
`‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, where `S` contains the support of `β`. -/
theorem IsLassoEstimator.restricted_l1_norm_compl_sub_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda)
    (S : Finset (Fin p)) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ) :
    restrictedL1Norm Sᶜ (b - β) ≤ 3 * restrictedL1Norm S (b - β) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have hu0 : 0 ≤ ‖A (b - β)‖ ^ 2 / n := by positivity
  nlinarith

/-- Under the compatibility condition, the lasso error has `‖δ_S‖₁ ≤ 3 λ |S| / (2 κ²)`. -/
private theorem IsLassoEstimator.restricted_l1_norm_sub_le_aux {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    restrictedL1Norm S (b - β) ≤ 3 * lambda * S.card / (2 * κ ^ 2) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have hcone := hb.restricted_l1_norm_compl_sub_le hn hlambda S hsupp hnoise
  set a := restrictedL1Norm S (b - β)
  set c := restrictedL1Norm Sᶜ (b - β)
  set u := ‖A (b - β)‖ ^ 2 / n with hu
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hcomp : κ ^ 2 * a ^ 2 ≤ S.card * u := by
    calc κ ^ 2 * a ^ 2 ≤ (S.card : ℝ) * ‖A (b - β)‖ ^ 2 / n := hcompat (b - β) hcone
      _ = _ := by rw [hu]; ring
  have hka : κ ^ 2 * a ≤ 3 * lambda * S.card / 2 := by
    rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · have : κ ^ 2 * a ^ 2 ≤ S.card * (3 * lambda / 2 * a) := by
        calc κ ^ 2 * a ^ 2 ≤ S.card * u := hcomp
          _ ≤ S.card * (3 * lambda / 2 * a) := by
            apply mul_le_mul_of_nonneg_left _ hs.le; nlinarith
      nlinarith
  rw [le_div_iff₀ (by positivity)]; nlinarith

/-- GAPS 103.34: the lasso prediction bound under compatibility. Under the noise event and the
compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, a lasso estimate
satisfies `‖A (b - β)‖² / n ≤ 9 λ² |S| / (4 κ²)`. -/
theorem IsLassoEstimator.norm_apply_sub_sq_div_le_of_has_compatibility {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    ‖A (b - β)‖ ^ 2 / n ≤ 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) := by
  have hmain := hb.norm_apply_sub_sq_div_le hn hlambda S hsupp hnoise
  have ha := hb.restricted_l1_norm_sub_le_aux hn hlambda hκ S hne hsupp hnoise hcompat
  have hc0 : 0 ≤ restrictedL1Norm Sᶜ (b - β) := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  calc ‖A (b - β)‖ ^ 2 / n ≤ 3 * lambda / 2 * restrictedL1Norm S (b - β) := by nlinarith
    _ ≤ 3 * lambda / 2 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
    _ = 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) := by field_simp; ring

/-- GAPS 103.34: the lasso `ℓ¹` error bound under compatibility. Under the noise event and the
compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ 3 ‖δ_S‖₁`, a lasso estimate
satisfies `‖b - β‖₁ ≤ 6 λ |S| / κ²`. -/
theorem IsLassoEstimator.restricted_l1_norm_sub_le {n p : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {β b : EuclideanSpace ℝ (Fin p)} {ε : EuclideanSpace ℝ (Fin n)} {lambda κ : ℝ}
    (hb : IsLassoEstimator A (A β + ε) lambda b) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (S : Finset (Fin p)) (hne : S.Nonempty) (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : HasCompatibility A S 3 κ) :
    restrictedL1Norm Finset.univ (b - β) ≤ 6 * lambda * S.card / κ ^ 2 := by
  have hcone := hb.restricted_l1_norm_compl_sub_le hn hlambda S hsupp hnoise
  have ha := hb.restricted_l1_norm_sub_le_aux hn hlambda hκ S hne hsupp hnoise hcompat
  rw [← restricted_l1_norm_add_compl S (b - β)]
  calc restrictedL1Norm S (b - β) + restrictedL1Norm Sᶜ (b - β)
      ≤ 4 * restrictedL1Norm S (b - β) := by linarith
    _ ≤ 4 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
    _ = 6 * lambda * S.card / κ ^ 2 := by field_simp; ring

/-- The Benjamini–Hochberg count `R` is attained: `R ≤ m` and `R ≤ #{j : x j ≤ R α / m}`. -/
private theorem benjamini_hochberg_count_le_and_le_card {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤ m ∧ benjaminiHochbergCount x α ≤
      (Finset.univ.filter fun j ↦ x j ≤ (benjaminiHochbergCount x α : ℝ) * α / m).card := by
  classical
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup
    ((Finset.range (m + 1)).filter fun k : ℕ ↦
      k ≤ (Finset.univ.filter fun i ↦ x i ≤ (k : ℝ) * α / m).card)
    ⟨0, by simp⟩ id
  have hR : benjaminiHochbergCount x α = k := by
    rw [benjaminiHochbergCount]; convert heq; rfl
  rw [Finset.mem_filter, Finset.mem_range] at hk
  rw [hR]
  exact ⟨by omega, by convert hk.2⟩

/-- The Benjamini–Hochberg count is at most the number of hypotheses. -/
theorem benjamini_hochberg_count_le {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤ m :=
  (benjamini_hochberg_count_le_and_le_card x α).1

/-- The Benjamini–Hochberg count `R` satisfies its defining inequality
`R ≤ #{j : x j ≤ R α / m}`. -/
theorem benjamini_hochberg_count_le_card {m : ℕ} (x : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount x α ≤
      (Finset.univ.filter fun j ↦ x j ≤ (benjaminiHochbergCount x α : ℝ) * α / m).card :=
  (benjamini_hochberg_count_le_and_le_card x α).2

/-- Every `k ≤ m` satisfying the Benjamini–Hochberg inequality is at most the count. -/
theorem le_benjamini_hochberg_count {m : ℕ} (x : Fin m → ℝ) (α : ℝ) (k : ℕ) (hk : k ≤ m)
    (hkN : k ≤ (Finset.univ.filter fun j ↦ x j ≤ (k : ℝ) * α / m).card) :
    k ≤ benjaminiHochbergCount x α := by
  classical
  unfold benjaminiHochbergCount
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
theorem benjamini_hochberg_count_le_update_zero {m : ℕ} (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m) :
    benjaminiHochbergCount x α ≤ benjaminiHochbergCount (Function.update x i 0) α :=
  le_benjamini_hochberg_count _ α _ (benjamini_hochberg_count_le x α)
    ((benjamini_hochberg_count_le_card x α).trans
      (Finset.card_le_card (filter_le_subset_filter_update_zero x α hα i _)))

/-- After setting one p-value to zero, the Benjamini–Hochberg procedure rejects at least once. -/
theorem one_le_benjamini_hochberg_count_update_zero {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (i : Fin m) :
    1 ≤ benjaminiHochbergCount (Function.update x i 0) α := by
  refine le_benjamini_hochberg_count _ α 1 hm ?_
  rw [Finset.one_le_card]
  exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.update_self]; positivity⟩

/-- The Benjamini–Hochberg count is unchanged by setting the `i`-th p-value to zero whenever
that p-value is rejected by the modified count. -/
theorem benjamini_hochberg_count_eq_update_zero_of_le {m : ℕ} (x : Fin m → ℝ) (α : ℝ)
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
  refine le_antisymm (benjamini_hochberg_count_le_update_zero x α hα i) ?_
  refine le_benjamini_hochberg_count x α _ (benjamini_hochberg_count_le q α) ?_
  rw [← heq]; exact benjamini_hochberg_count_le_card q α

/-- Leave-one-out decomposition of a Benjamini–Hochberg rejection: the contribution of
hypothesis `i` to the false discovery proportion splits over the value `k` of the count
computed with `x i` replaced by zero. -/
theorem benjamini_hochberg_rejection_div_eq_sum {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (i : Fin m) :
    (if x i ≤ (benjaminiHochbergCount x α : ℝ) * α / m then (1 : ℝ) else 0) /
        max (benjaminiHochbergCount x α : ℝ) 1 =
      ∑ k ∈ Finset.Icc 1 m, (if x i ≤ (k : ℝ) * α / m ∧
        benjaminiHochbergCount (Function.update x i 0) α = k then (1 : ℝ) / k else 0) := by
  classical
  have hmono := benjamini_hochberg_count_le_update_zero x α hα i
  have hone := one_le_benjamini_hochberg_count_update_zero hm x α hα i
  have hsame := benjamini_hochberg_count_eq_update_zero_of_le x α hα i
  set R := benjaminiHochbergCount x α
  set Rq := benjaminiHochbergCount (Function.update x i 0) α
  have hRqm : Rq ≤ m := benjamini_hochberg_count_le _ α
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
theorem measurable_benjamini_hochberg_count (m : ℕ) (α : ℝ) :
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
    simp only [Function.comp, hG, hN, benjaminiHochbergCount]
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
theorem integral_benjamini_hochberg_false_discovery_proportion_le {Ω : Type*} [MeasurableSpace Ω]
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
    (measurable_benjamini_hochberg_count m α).comp (hupd_meas i)
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
    have h2 := h.comp hφ ((measurable_benjamini_hochberg_count m α).comp hext_meas)
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
      benjamini_hochberg_rejection_div_eq_sum hm (fun j ↦ p j ω) α hα0.le i]
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
