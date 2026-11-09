module

public import CKSD.Geometry.Basic
public import CKSD.Asymptotics.MultivariateCLT
public import CKSD.Bayes.Basic
public import TauCeti.Probability.Moments.Covariance

/-!
# Geometric statistics: Fréchet means, sampling, and multidimensional scaling

Cheeger's inequalities for weighted graphs (GAPS 108.1) are in `CKSD.Geometry.Cheeger`.

## Main results

* `CKSD.existsUnique_frechet_mean_of_midpoint_inequality`: existence and uniqueness of the
  Fréchet mean in a complete space satisfying the CAT(0) midpoint inequality (GAPS 108.5).
* `CKSD.isBoundedInProbability_hausdorff_sampling_error`: the Hausdorff sampling rate of a support
  under a uniform small-ball lower bound (GAPS 108.7).
* `CKSD.posSemidef_double_centering_iff_sq_euclidean_distances`: Schoenberg's criterion for
  Euclidean distance matrices, the basis of classical multidimensional scaling (GAPS 108.8).
* `CKSD.extrinsic_mean_iff_nearest_expectation`,
  `CKSD.tendstoInDistribution_projected_sampleAverage`: the extrinsic mean as the projection of the
  Euclidean mean and its delta-method central limit theorem (GAPS 108.10).

## Main definitions

* `CKSD.centeringMatrix`: the centering matrix `J = I - n⁻¹ 1 1ᵀ`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory Filter Set

/-- Squared distances to any point are integrable once they are integrable for one point. -/
theorem integrable_dist_sq_of_integrable_dist_sq
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (P : Measure X)
    [IsFiniteMeasure P] (o : X) (h2 : Integrable (fun x ↦ dist o x ^ 2) P) (p : X) :
    Integrable (fun x ↦ dist p x ^ 2) P := by
  refine ((h2.const_mul 2).add (integrable_const (2 * dist p o ^ 2))).mono'
    ((continuous_const.dist continuous_id).pow 2).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  have h := pow_le_pow_left₀ dist_nonneg (dist_triangle p o x) 2
  nlinarith [sq_nonneg (dist p o - dist o x)]

/-- GAPS 108.5, existence and uniqueness in a complete space satisfying the CAT(0) midpoint
inequality: if a complete metric space has midpoints `mid x y` with
`d(z, mid x y)² ≤ (d(z, x)² + d(z, y)²) / 2 - d(x, y)² / 4`, then every probability law with finite
second moment has a unique Fréchet mean, a unique minimizer of `p ↦ ∫ d(p, x)² dP(x)`. -/
theorem existsUnique_frechet_mean_of_midpoint_inequality
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (mid : X → X → X)
    (hmid : ∀ x y z, dist z (mid x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4)
    (o : X) (h2 : Integrable (fun x ↦ dist o x ^ 2) P) :
    ∃! m : X, ∀ p : X, (∫ x, dist m x ^ 2 ∂P) ≤ ∫ x, dist p x ^ 2 ∂P := by
  set F : X → ℝ := fun p ↦ ∫ x, dist p x ^ 2 ∂P with hF
  have hint := integrable_dist_sq_of_integrable_dist_sq P o h2
  have hF0 : ∀ p, 0 ≤ F p := fun p ↦ integral_nonneg fun x ↦ sq_nonneg _
  -- the integrated midpoint inequality
  have hFmid : ∀ x y, dist x y ^ 2 ≤ 2 * F x + 2 * F y - 4 * F (mid x y) := by
    intro x y
    have hle : F (mid x y) ≤ ∫ z, ((dist x z ^ 2 + dist y z ^ 2) / 2 - dist x y ^ 2 / 4) ∂P := by
      refine integral_mono (hint _) ?_ fun z ↦ ?_
      · exact (((hint x).add (hint y)).div_const 2).sub (integrable_const _)
      · simpa only [dist_comm] using hmid x y z
    rw [integral_sub (f := fun z ↦ (dist x z ^ 2 + dist y z ^ 2) / 2)
      (((hint x).add (hint y)).div_const 2) (integrable_const _),
      integral_div, integral_add (hint x) (hint y), integral_const, probReal_univ,
      one_smul] at hle
    simp only [F] at hle ⊢
    linarith
  have : Nonempty X := ⟨o⟩
  set I := sInf (range F) with hI
  have hbdd : BddBelow (range F) := ⟨0, by rintro _ ⟨p, rfl⟩; exact hF0 p⟩
  have hIle : ∀ p, I ≤ F p := fun p ↦ csInf_le hbdd ⟨p, rfl⟩
  have hex : ∀ n : ℕ, ∃ u, F u < I + 1 / (n + 1) := by
    intro n
    have : I < I + 1 / (n + 1) := by
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := exists_lt_of_csInf_lt (range_nonempty F) this
    exact ⟨u, hu⟩
  choose u hu using hex
  -- the minimizing sequence is Cauchy
  have hdist : ∀ n k, dist (u n) (u k) ^ 2 ≤ 2 / (n + 1) + 2 / (k + 1) := by
    intro n k
    have h := hFmid (u n) (u k)
    have := hIle (mid (u n) (u k))
    have hn := hu n
    have hk := hu k
    have e1 : 2 / ((n : ℝ) + 1) = 2 * (1 / (n + 1)) := by ring
    have e2 : 2 / ((k : ℝ) + 1) = 2 * (1 / (k + 1)) := by ring
    rw [e1, e2]
    linarith
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ ↦ Real.sqrt (4 / (N + 1))) ?_ ?_
    · intro n k N hn hk
      apply Real.le_sqrt_of_sq_le
      refine (hdist n k).trans ?_
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : 2 / ((n : ℝ) + 1) ≤ 2 / (N + 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have h2' : 2 / ((k : ℝ) + 1) ≤ 2 / (N + 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have : 4 / ((N : ℝ) + 1) = 2 / (N + 1) + 2 / (N + 1) := by ring
      linarith
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
      have h' : Tendsto (fun N : ℕ ↦ √(4 * (1 / ((N : ℝ) + 1)))) atTop (𝓝 (√(4 * 0))) :=
        (Real.continuous_sqrt.tendsto _).comp h
      rw [mul_zero, Real.sqrt_zero] at h'
      refine h'.congr fun N ↦ ?_
      congr 1
      ring
  obtain ⟨m, hm⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hFu : Tendsto (fun n ↦ F (u n)) atTop (𝓝 I) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n ↦ hIle _)
      (fun n ↦ (hu n).le)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add I
    simpa using this
  have hδ : Tendsto (fun n ↦ dist m (u n)) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.mp hm)
    simpa only [dist_comm] using this
  -- comparison of `F m` with `F (u n)`
  have hcomp : ∀ n, F m ≤ (1 + dist m (u n)) * F (u n) + dist m (u n) + dist m (u n) ^ 2 := by
    intro n
    set δ := dist m (u n)
    have hδ0 : 0 ≤ δ := dist_nonneg
    have hle : F m ≤ ∫ x, ((1 + δ) * dist (u n) x ^ 2 + (δ + δ ^ 2)) ∂P := by
      refine integral_mono (hint m) (((hint _).const_mul _).add (integrable_const _)) fun x ↦ ?_
      have htri : dist m x ≤ δ + dist (u n) x := dist_triangle _ _ _
      have ha : 0 ≤ dist (u n) x := dist_nonneg
      have h2a : 2 * dist (u n) x ≤ dist (u n) x ^ 2 + 1 := by
        nlinarith [sq_nonneg (dist (u n) x - 1)]
      have : dist m x ^ 2 ≤ (δ + dist (u n) x) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg htri 2
      nlinarith
    rw [integral_add ((hint _).const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul] at hle
    simp only [F] at hle ⊢
    linarith
  have hlim : Tendsto (fun n ↦ (1 + dist m (u n)) * F (u n) + dist m (u n) + dist m (u n) ^ 2)
      atTop (𝓝 ((1 + 0) * I + 0 + 0 ^ 2)) :=
    ((tendsto_const_nhds.add hδ).mul hFu).add hδ |>.add (hδ.pow 2)
  simp only [add_zero, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hlim
  have hFm : F m ≤ I := ge_of_tendsto' hlim hcomp
  refine ⟨m, fun p ↦ hFm.trans (hIle p), fun m' hm' ↦ ?_⟩
  have h1 := hm' m
  have h3 := hFmid m' m
  have h4 : F m ≤ F (mid m' m) := hFm.trans (hIle _)
  have h5 : F m' ≤ F m := h1
  have : dist m' m ^ 2 ≤ 0 := by simp only [F] at *; linarith
  have : dist m' m = 0 := by nlinarith [dist_nonneg (x := m') (y := m)]
  exact dist_eq_zero.mp this

/-- A packing bound for nets: if every open ball of radius `s > 0` centered in `K` has
`P`-mass at least `a > 0` under a probability measure `P`, then a finite subset `F ⊆ K` with
`|F| a ≤ 1` is a `2s`-net of `K`. -/
private theorem exists_finset_net_of_le_measure_ball {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (K : Set X) {s a : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hball : ∀ x ∈ K, ENNReal.ofReal a ≤ P (Metric.ball x s)) :
    ∃ F : Finset X, (F : Set X) ⊆ K ∧ (F.card : ℝ) * a ≤ 1 ∧
      ∀ y ∈ K, ∃ z ∈ F, dist y z < 2 * s := by
  classical
  have hsmall : ∀ F : Finset X, (F : Set X) ⊆ K →
      (F : Set X).Pairwise (fun x y ↦ 2 * s ≤ dist x y) → (F.card : ℝ) * a ≤ 1 := by
    intro F hFK hsep
    have hdisj : (F : Set X).PairwiseDisjoint (fun x ↦ Metric.ball x s) := by
      intro x hx y hy hxy
      rw [Function.onFun, Set.disjoint_left]
      intro z hzx hzy
      have h1 := hsep hx hy hxy
      rw [Metric.mem_ball] at hzx hzy
      have h2 := dist_triangle_left x y z
      linarith
    have hU := measure_biUnion_finset (μ := P) hdisj (fun x _ ↦ measurableSet_ball)
    have hle : ∑ x ∈ F, P (Metric.ball x s) ≤ 1 := hU ▸ prob_le_one
    have h : ∑ _x ∈ F, ENNReal.ofReal a ≤ 1 :=
      (Finset.sum_le_sum fun x hx ↦ hball x (hFK hx)).trans hle
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)] at h
    exact ENNReal.ofReal_le_one.mp h
  by_contra hno
  push Not at hno
  have hbuild : ∀ k : ℕ, ∃ F : Finset X, (F : Set X) ⊆ K ∧
      (F : Set X).Pairwise (fun x y ↦ 2 * s ≤ dist x y) ∧ F.card = k := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp, rfl⟩
    | succ k ih =>
      obtain ⟨F, hFK, hsep, hcard⟩ := ih
      obtain ⟨y, hyK, hy⟩ := hno F hFK (hsmall F hFK hsep)
      have hyF : y ∉ F := fun h ↦ by
        have := hy y h
        rw [dist_self] at this
        linarith
      refine ⟨insert y F, ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]; exact insert_subset hyK hFK
      · rw [Finset.coe_insert]
        refine Set.pairwise_insert.2 ⟨hsep, fun b hb _ ↦ ⟨hy b hb, ?_⟩⟩
        rw [dist_comm]; exact hy b hb
      · rw [Finset.card_insert_of_notMem hyF, hcard]
  obtain ⟨F, hFK, hsep, hcard⟩ := hbuild (⌈1 / a⌉₊ + 1)
  have h := hsmall F hFK hsep
  rw [hcard] at h
  have h1 : 1 / a < ((⌈1 / a⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  rw [div_lt_iff₀ ha] at h1
  linarith

/-- For an i.i.d. sequence with law `P` and a measurable set `B`, the probability that none of
the first `n` observations falls in `B` is `(1 - P(B))^n`. -/
private theorem measureReal_forall_lt_notMem_eq_pow {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    {B : Set X} (hB : MeasurableSet B) (n : ℕ) :
    μ.real {ω | ∀ i < n, Xn i ω ∉ B} = (1 - P.real B) ^ n := by
  have hset : {ω | ∀ i < n, Xn i ω ∉ B} = ⋂ i ∈ Finset.range n, Xn i ⁻¹' (fun _ ↦ Bᶜ) i := by
    ext ω; simp
  rw [hset, measureReal_def, hiid.2.1.measure_inter_preimage_eq_mul (Finset.range n)
    (fun i _ ↦ hB.compl), ENNReal.toReal_prod]
  have h : ∀ i, (μ (Xn i ⁻¹' Bᶜ)).toReal = 1 - P.real B := by
    intro i
    rw [← Measure.map_apply (hiid.1 i) hB.compl, hiid.2.2 i, ← measureReal_def,
      probReal_compl_eq_one_sub hB]
  exact (Finset.prod_congr rfl fun i _ ↦ h i).trans (by simp)

/-- GAPS 108.7, noiseless Hausdorff sampling rate from a uniform small-ball lower bound: if a
law `P` is carried by a compact set `K` and gives every ball of radius `r < r₀` centered in `K`
mass at least `c r^d`, then the Hausdorff distance between `K` and an i.i.d. sample of size `n` is
`O_P((log n / n)^{1/d})`. -/
theorem isBoundedInProbability_hausdorff_sampling_error
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P) (K : Set X)
      (hK : IsCompact K)
    (hsupp : P K = 1) (d c r₀ : ℝ) (hd : 0 < d) (hc : 0 < c) (hr₀ : 0 < r₀)
    (hlower : ∀ x ∈ K, ∀ r ∈ Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (c * Real.rpow r d) ≤ P (Metric.ball x r)) :
    IsBoundedInProbability μ (fun n ω ↦
      Metric.hausdorffDist (range fun i : Fin n ↦ Xn i.val ω) K /
        Real.rpow (Real.log (n + 1) / n) (1 / d)) := by
  -- a packing net of `K` at scale `t = C r_n` and a union bound over its balls
  intro ε hε
  set r : ℕ → ℝ := fun n ↦ Real.rpow (Real.log (n + 1) / n) (1 / d) with hr_def
  -- the constant
  set C := 2 * (2 / c) ^ (1 / d) with hC_def
  have hCpos : 0 < C := by positivity
  have hC2 : c * (C / 2) ^ d = 2 := by
    rw [hC_def, mul_div_cancel_left₀ _ (two_ne_zero), one_div,
      Real.rpow_inv_rpow (by positivity) hd.ne']
    field_simp
  refine ⟨C, hCpos, ?_⟩
  -- `r n → 0`
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n + 1) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    exact h.congr fun n ↦ by simp
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h := hlog.rpow_const (p := 1 / d) (Or.inr (by positivity))
    rwa [Real.zero_rpow (by positivity)] at h
  have hsmallr : ∀ᶠ n in atTop, C * r n < r₀ :=
    (hr0.const_mul C).eventually (gt_mem_nhds (show C * 0 < r₀ by rw [mul_zero]; exact hr₀))
  -- the final numerical bound
  set K₀ := 1 / (c * (C / 4) ^ d) with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (K₀ / (ε * Real.log 2))
  filter_upwards [hsmallr, eventually_ge_atTop (max N 1)] with n hn hnN
  have hn1 : 1 ≤ n := le_of_max_le_right hnN
  have hnN' : N ≤ n := le_of_max_le_left hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log (n + 1) := Real.log_pos (by linarith)
  have hrn : 0 < r n := Real.rpow_pos_of_pos (div_pos hL hnR) _
  have hrd : r n ^ d = Real.log (n + 1) / n := by
    change ((Real.log (n + 1) / n) ^ (1 / d)) ^ d = _
    rw [one_div, Real.rpow_inv_rpow (div_pos hL hnR).le hd.ne']
  set t := C * r n with ht_def
  have ht : 0 < t := mul_pos hCpos hrn
  -- a net of `K` from the packing bound
  have hball4 : ∀ x ∈ K, ENNReal.ofReal (c * (t / 4) ^ d) ≤ P (Metric.ball x (t / 4)) :=
    fun x hx ↦ hlower x hx _ ⟨by positivity, by linarith⟩
  obtain ⟨F, hFK, hFcard, hFnet⟩ := exists_finset_net_of_le_measure_ball P K (s := t / 4)
    (by positivity) (by positivity) hball4
  set p := c * (t / 2) ^ d with hp_def
  have hball2 : ∀ z ∈ F, p ≤ P.real (Metric.ball z (t / 2)) := fun z hz ↦
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
      (hlower z (hFK hz) (t / 2) ⟨by positivity, by linarith⟩)
  -- inclusion of events
  set A := ⋃ i ∈ Finset.range n, Xn i ⁻¹' Kᶜ
  set B := ⋃ z ∈ F, {ω | ∀ i < n, Xn i ω ∉ Metric.ball z (t / 2)}
  have hsub : {ω | C < |Metric.hausdorffDist (range fun i : Fin n ↦ Xn i.val ω) K / r n|} ⊆
      A ∪ B := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rw [abs_of_nonneg (div_nonneg Metric.hausdorffDist_nonneg hrn.le), lt_div_iff₀ hrn] at hω
    by_contra hnot
    simp only [A, B, mem_union, mem_iUnion, mem_preimage, mem_compl_iff, Finset.mem_range,
      mem_ofPred_eq, not_or, not_exists, not_forall, not_not] at hnot
    obtain ⟨hK', hB'⟩ := hnot
    refine absurd (Metric.hausdorffDist_le_of_mem_dist ht.le ?_ ?_) (not_le.mpr hω)
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, hK' i i.2, by rw [dist_self]; exact ht.le⟩
    · intro y hy
      obtain ⟨z, hzF, hyz⟩ := hFnet y hy
      obtain ⟨i, hi, hiz⟩ := hB' z hzF
      refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
      rw [Metric.mem_ball] at hiz
      linarith [dist_triangle y z (Xn i ω), dist_comm z (Xn i ω)]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hA : μ.real A = 0 := by
    refine le_antisymm ((measureReal_biUnion_finset_le _ _).trans ?_) measureReal_nonneg
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).le
    rw [measureReal_def, ← Measure.map_apply (hiid.1 i) hKm.compl, hiid.2.2 i,
      (prob_compl_eq_zero_iff hKm).mpr hsupp, ENNReal.toReal_zero]
  have hB : μ.real B ≤ F.card * Real.exp (-(p * n)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun z hz ↦ ?_
    rw [measureReal_forall_lt_notMem_eq_pow μ P Xn hiid measurableSet_ball]
    set q := P.real (Metric.ball z (t / 2))
    have hq1 : q ≤ 1 := measureReal_le_one
    calc (1 - q) ^ n ≤ Real.exp (-q) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) n
      _ = Real.exp (-(q * n)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(p * n)) := Real.exp_le_exp.mpr (by nlinarith [hball2 z hz])
  -- the numerical estimate
  have hpn : p * n = 2 * Real.log (n + 1) := by
    rw [hp_def, ht_def, mul_div_right_comm, Real.mul_rpow (by positivity) hrn.le, hrd,
      ← mul_assoc, hC2]
    field_simp
  have hFb : (F.card : ℝ) ≤ K₀ * (n / Real.log (n + 1)) := by
    have h2 : c * (t / 4) ^ d = c * (C / 4) ^ d * (Real.log (n + 1) / n) := by
      rw [ht_def, mul_div_right_comm, Real.mul_rpow (by positivity) hrn.le, hrd, mul_assoc]
    refine ((le_div_iff₀ (by positivity)).2 hFcard).trans_eq ?_
    rw [h2, hK₀]
    field_simp
  calc μ.real {ω | C < |Metric.hausdorffDist (range fun i : Fin n ↦ Xn i.val ω) K / r n|}
      ≤ μ.real (A ∪ B) := measureReal_mono hsub
    _ ≤ μ.real A + μ.real B := measureReal_union_le _ _
    _ ≤ 0 + F.card * Real.exp (-(p * n)) := by rw [hA, zero_add, zero_add]; exact hB
    _ ≤ K₀ * (n / Real.log (n + 1)) * Real.exp (-(2 * Real.log (n + 1))) := by
        rw [zero_add, hpn]
        exact mul_le_mul_of_nonneg_right hFb (Real.exp_pos _).le
    _ ≤ ε := by
        have he : Real.exp (-(2 * Real.log (n + 1))) = ((n : ℝ) + 1)⁻¹ ^ 2 := by
          rw [← Real.log_rpow (by positivity) 2, ← Real.log_inv, Real.exp_log (by positivity)]
          norm_num
        rw [he]
        have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hNn : K₀ / (ε * Real.log 2) < n + 1 := by
          linarith [show (N : ℝ) ≤ n by exact_mod_cast hnN']
        rw [div_lt_iff₀ (by positivity)] at hNn
        have key : K₀ * (n / Real.log (n + 1)) * ((n : ℝ) + 1)⁻¹ ^ 2 ≤
            K₀ / (Real.log 2 * (n + 1)) := by
          have h1 : (n : ℝ) / Real.log (n + 1) ≤ (n + 1) / Real.log 2 :=
            div_le_div₀ (by positivity) (by linarith) hl2
              (Real.log_le_log (by norm_num) (by linarith))
          calc K₀ * (n / Real.log (n + 1)) * ((n : ℝ) + 1)⁻¹ ^ 2
              ≤ K₀ * ((n + 1) / Real.log 2) * ((n : ℝ) + 1)⁻¹ ^ 2 := by gcongr
            _ = K₀ / (Real.log 2 * (n + 1)) := by field_simp
        refine key.trans ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith

/-- The centering matrix `J = I - 11ᵀ/n`. -/
noncomputable def centeringMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (n : ℝ)⁻¹ • Matrix.of (fun _ _ ↦ (1 : ℝ))

/-- Entries of a doubly centered matrix. -/
theorem centeringMatrix_mul_mul_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (centeringMatrix n * D * centeringMatrix n) i j =
      D i j - (n : ℝ)⁻¹ * ∑ k, D k j - (n : ℝ)⁻¹ * ∑ k, D i k +
        (n : ℝ)⁻¹ ^ 2 * ∑ k, ∑ l, D k l := by
  have h : centeringMatrix n * D * centeringMatrix n =
      D - (n : ℝ)⁻¹ • (Matrix.of (fun _ _ ↦ (1 : ℝ)) * D) -
        (n : ℝ)⁻¹ • (D * Matrix.of (fun _ _ ↦ (1 : ℝ))) +
        ((n : ℝ)⁻¹ ^ 2) • (Matrix.of (fun _ _ ↦ (1 : ℝ)) * D * Matrix.of (fun _ _ ↦ (1 : ℝ))) := by
    simp only [centeringMatrix, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [sq]; abel
  rw [h, Finset.sum_comm (f := fun k l ↦ D k l)]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.of_apply, smul_eq_mul, one_mul, mul_one]

/-- Expansion of a sum of squared deviations from a fixed value. -/
theorem sum_sub_sq_eq {n : ℕ} (a : Fin n → ℝ) (j : ℝ) :
    ∑ l, (a l - j) ^ 2 = ∑ l, a l ^ 2 - 2 * j * ∑ l, a l + n * j ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- One-coordinate form of the double-centering identity: for `c n = 1`, minus one half of the
doubly centered squared differences `(a_i - a_j)²` is the product of the centered values
`(a_i - ā)(a_j - ā)`. -/
theorem neg_half_mul_doubleCentered_sq_sub_eq {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (hc : c * n = 1)
    (i j : Fin n) :
    -(1 / 2 : ℝ) * ((a i - a j) ^ 2 - c * ∑ l, (a l - a j) ^ 2 - c * ∑ l, (a i - a l) ^ 2 +
      c ^ 2 * ∑ l, ∑ l', (a l - a l') ^ 2) =
      (a i - c * ∑ l, a l) * (a j - c * ∑ l, a l) := by
  have e2 : ∑ l, (a i - a l) ^ 2 = ∑ l, (a l - a i) ^ 2 :=
    Finset.sum_congr rfl fun l _ ↦ by ring
  have e3 : ∑ l, ∑ l', (a l - a l') ^ 2 =
      ∑ l, (∑ l', a l' ^ 2 - 2 * a l * ∑ l', a l' + n * a l ^ 2) :=
    Finset.sum_congr rfl fun l _ ↦ by
      rw [← sum_sub_sq_eq]; exact Finset.sum_congr rfl fun l' _ ↦ by ring
  rw [e2, e3, sum_sub_sq_eq, sum_sub_sq_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination ((a i ^ 2 + a j ^ 2) / 2 - c * ∑ l, a l ^ 2) * hc

/-- GAPS 108.8, Schoenberg's Euclidean-distance criterion by double centering: a symmetric matrix
`D` with zero diagonal is a matrix of squared Euclidean distances `‖x_i - x_j‖²` exactly when
`-½ J D J` is positive semidefinite, where `J` is the centering matrix. The points can be taken in
`ℝ^n`; classical multidimensional scaling recovers them from a square root of `-½ J D J`. -/
theorem posSemidef_double_centering_iff_sq_euclidean_distances
    {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hsym : D.IsSymm) (hdiag : ∀ i, D i i = 0) :
    let J := (1 : Matrix (Fin n) (Fin n) ℝ) - (n : ℝ)⁻¹ • Matrix.of (fun _ _ ↦ (1 : ℝ));
    ((-(1 / 2 : ℝ)) • (J * D * J)).PosSemidef ↔
      ∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, D i j = ‖x i - x j‖ ^ 2 := by
  intro J
  change ((-(1 / 2 : ℝ)) • (centeringMatrix n * D * centeringMatrix n)).PosSemidef ↔ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ ↦ ⟨Fin.elim0, fun i ↦ i.elim0⟩,
      fun _ ↦ by convert Matrix.PosSemidef.zero; exact Subsingleton.elim _ _⟩
  set c : ℝ := (n : ℝ)⁻¹ with hcdef
  have hc : c * n = 1 := inv_mul_cancel₀ (by exact_mod_cast hn.ne')
  set B := (-(1 / 2 : ℝ)) • (centeringMatrix n * D * centeringMatrix n) with hBdef
  have hB : ∀ i j, B i j = -(1 / 2 : ℝ) * (D i j - c * ∑ k, D k j - c * ∑ k, D i k +
      c ^ 2 * ∑ k, ∑ l, D k l) := fun i j ↦ by
    rw [hBdef, Matrix.smul_apply, centeringMatrix_mul_mul_apply, smul_eq_mul]
  have hcol : ∀ j, ∑ k, D k j = ∑ k, D j k := fun j ↦
    Finset.sum_congr rfl fun k _ ↦ hsym.apply j k
  constructor
  · intro hBpsd
    have hB0 : 0 ≤ B := Matrix.nonneg_iff_posSemidef.mpr hBpsd
    set C := CFC.sqrt B
    have hCC : Cᴴ * C = B := by
      have h1 : Cᴴ = C := (CFC.sqrt_nonneg B).isSelfAdjoint.star_eq
      rw [h1, CFC.sqrt_mul_sqrt_self B hB0]
    refine ⟨fun i ↦ WithLp.toLp 2 fun k ↦ C k i, fun i j ↦ ?_⟩
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply]
    have hentry : ∀ i j, B i j = ∑ k, C k i * C k j := fun i j ↦ by
      rw [← hCC, Matrix.mul_apply]
      simp [Matrix.conjTranspose_apply]
    have : ∑ k, (C k i - C k j) ^ 2 = B i i + B j j - 2 * B i j := by
      rw [hentry, hentry, hentry, ← Finset.sum_add_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [this, hB, hB, hB, hdiag, hdiag, hcol i, hcol j]
    ring
  · rintro ⟨x, hx⟩
    set m : Fin n → ℝ := fun k ↦ c * ∑ l, x l k
    let C : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k i ↦ x i k - m k
    have hBC : B = Cᴴ * C := by
      ext i j
      rw [Matrix.mul_apply, hB]
      simp only [Matrix.conjTranspose_apply, star_trivial, C, Matrix.of_apply, m]
      simp only [hx, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
      rw [Finset.sum_comm (f := fun k l ↦ (x k l - x j l) ^ 2),
        Finset.sum_comm (f := fun k l ↦ (x i l - x k l) ^ 2)]
      have hdouble : ∑ k, ∑ l, ∑ q, (x k q - x l q) ^ 2 =
          ∑ q, ∑ k, ∑ l, (x k q - x l q) ^ 2 := by
        calc ∑ k, ∑ l, ∑ q, (x k q - x l q) ^ 2 = ∑ k, ∑ q, ∑ l, (x k q - x l q) ^ 2 :=
              Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
          _ = ∑ q, ∑ k, ∑ l, (x k q - x l q) ^ 2 := Finset.sum_comm
      rw [hdouble, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ ↦ by
        have := neg_half_mul_doubleCentered_sq_sub_eq (fun l ↦ x l q) c hc i j
        simp only at this
        linarith
    rw [hBC]
    exact Matrix.posSemidef_conjTranspose_mul_self C

/-- GAPS 108.10: squared-distance comparisons over a set are equivalent to distance comparisons
with the Euclidean expectation. For a law `P` on `ℝ^d` with finite second moment, a candidate point
`m` minimizes `p ↦ E ‖X - p‖²` over `S` exactly when it is a point of `S` nearest to `E X`; in
particular the extrinsic mean on `S` is the nearest-point projection of the Euclidean mean. The
proof uses TauCeti's covariance-trace decomposition of the second moment about a point. -/
theorem extrinsic_mean_iff_nearest_expectation {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (h2 : MemLp id 2 P) (S : Set (EuclideanSpace ℝ (Fin d)))
    (m : EuclideanSpace ℝ (Fin d)) :
    (∀ p ∈ S, (∫ x, ‖x - m‖ ^ 2 ∂P) ≤ ∫ x, ‖x - p‖ ^ 2 ∂P) ↔
      ∀ p ∈ S, ‖(∫ x, x ∂P) - m‖ ≤ ‖(∫ x, x ∂P) - p‖ := by
  simp only [TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix P h2,
    add_le_add_iff_right]
  exact forall₂_congr fun p _ ↦ pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero

/-- GAPS 108.10, projected empirical-mean central limit theorem (delta method): for an i.i.d.
sample with finite second moments, mean `m` and covariance matrix `C`, and a measurable map `proj`
differentiable at `m` with derivative `D`, `√n (proj(X̄_n) - proj m)` converges in distribution to
the image of `N(0, C)` under `D`. -/
theorem tendstoInDistribution_projected_sampleAverage {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (h2 : MemLp id 2 P) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hm : Measurable proj) (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hd : HasFDerivAt proj D (∫ x, x ∂P)) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt n • (proj (sampleAverage X n ω) - proj (∫ x, x ∂P))) atTop id
      (fun _ ↦ μ) ((multivariateGaussian 0 (TauCeti.covMatrix P)).map D) :=
  tendstoInDistribution_of_map_eq
    (tendstoInDistribution_delta_method μ (fun n ω ↦ sampleAverage X n ω)
      (fun n ↦ (Finset.measurable_fun_sum _ fun i _ ↦ hiid.1 i).const_smul ((n : ℝ)⁻¹))
      _ proj hm D hd (tendstoInDistribution_sqrt_smul_sampleAverage μ P X hiid h2)).1
    aemeasurable_id (by rw [Measure.map_id]; rfl)

end CKSD
