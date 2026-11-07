module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import TauCeti.Probability.Moments.Covariance

/-!
# Geometry: GeometricStatistics

Sources: `GAPS.md`, `SYNOPSIS108.md`, and `STRUCTURE108.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 108.1: Cheeger's inequalities for a finite weighted connected graph. -/
theorem cheeger_inequalities {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin n) (Fin n) ℝ)
    (hsym : W.IsSymm) (hpos : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 0)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 0 < cutWeight W S) :
    spectralGap W / 2 ≤ cheegerConstant W ∧ cheegerConstant W ≤ Real.sqrt (2 * spectralGap W) ∧
      1 - Real.sqrt (1 - cheegerConstant W ^ 2) ≤ spectralGap W := by
  sorry

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
inequality. -/
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
      have h2a : 2 * dist (u n) x ≤ dist (u n) x ^ 2 + 1 := by nlinarith [sq_nonneg (dist (u n) x - 1)]
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

/-- GAPS 108.7, noiseless Hausdorff sampling rate from a uniform small-ball lower bound. -/
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
  sorry

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

/-- One-coordinate form of the double-centering identity. -/
theorem centered_identity {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (hc : c * n = 1) (i j : Fin n) :
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

/-- Squared Euclidean distance in coordinates. -/
theorem euclideanSpace_norm_sub_sq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ‖u - v‖ ^ 2 = ∑ k, (u k - v k) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- GAPS 108.8, Schoenberg's Euclidean-distance criterion by double centering. -/
theorem posSemidef_double_centering_iff_sq_euclidean_distances
    {n : ℕ} (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ)
    (hsym : D.IsSymm) (hdiag : ∀ i, D i i = 0) :
    let J := (1 : Matrix (Fin n) (Fin n) ℝ) - (n : ℝ)⁻¹ • Matrix.of (fun _ _ ↦ (1 : ℝ));
    ((-(1 / 2 : ℝ)) • (J * D * J)).PosSemidef ↔
      ∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, D i j = ‖x i - x j‖ ^ 2 := by
  intro J
  change ((-(1 / 2 : ℝ)) • (centeringMatrix n * D * centeringMatrix n)).PosSemidef ↔ _
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
    rw [euclideanSpace_norm_sub_sq]
    have hentry : ∀ i j, B i j = ∑ k, C k i * C k j := fun i j ↦ by
      rw [← hCC, Matrix.mul_apply]
      simp [Matrix.conjTranspose_apply]
    have : ∑ k, (C k i - C k j) ^ 2 = B i i + B j j - 2 * B i j := by
      rw [hentry, hentry, hentry, ← Finset.sum_add_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    dsimp only
    rw [this, hB, hB, hB, hdiag, hdiag, hcol i, hcol j]
    ring
  · rintro ⟨x, hx⟩
    set m : Fin n → ℝ := fun k ↦ c * ∑ l, x l k
    let C : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k i ↦ x i k - m k
    have hBC : B = Cᴴ * C := by
      ext i j
      rw [Matrix.mul_apply, hB]
      simp only [Matrix.conjTranspose_apply, star_trivial, C, Matrix.of_apply, m]
      simp only [hx, euclideanSpace_norm_sub_sq]
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
        have := centered_identity (fun l ↦ x l q) c hc i j
        simp only at this
        linarith
    rw [hBC]
    exact Matrix.posSemidef_conjTranspose_mul_self C

/-- GAPS 108.10, extrinsic means are nearest points to the Euclidean expectation.
Uses TauCeti's covariance-trace decomposition of the second moment about a point. -/
theorem extrinsic_mean_iff_nearest_expectation {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (h2 : MemLp id 2 P) (S : Set (EuclideanSpace ℝ (Fin d)))
    (m : EuclideanSpace ℝ (Fin d)) (hm : m ∈ S) :
    (∀ p ∈ S, (∫ x, ‖x - m‖ ^ 2 ∂P) ≤ ∫ x, ‖x - p‖ ^ 2 ∂P) ↔
      ∀ p ∈ S, ‖(∫ x, x ∂P) - m‖ ≤ ‖(∫ x, x ∂P) - p‖ := by
  constructor
  · intro h p hp
    have hcomp := h p hp
    rw [TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix P h2 m,
      TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix P h2 p] at hcomp
    nlinarith [norm_nonneg ((∫ x, x ∂P) - m), norm_nonneg ((∫ x, x ∂P) - p)]
  · intro h p hp
    have hcomp := h p hp
    rw [TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix P h2 m,
      TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix P h2 p]
    nlinarith [norm_nonneg ((∫ x, x ∂P) - m), norm_nonneg ((∫ x, x ∂P) - p)]

/-- GAPS 108.10, projected empirical-mean central limit theorem. -/
theorem tendstoInDistribution_projected_sampleAverage {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IsIndependentIdenticallyDistributed μ X P)
      (h2 : MemLp id 2 P) :
    let m := ∫ x, x ∂P;
    let C := Matrix.of (fun i j ↦ ∫ x, (x i - m i) * (x j - m j) ∂P);
    ∀ (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    ∀ (hm : Measurable proj),
    ∀ (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    ∀ (hd : HasFDerivAt proj D m),
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (proj (sampleAverage X n ω) - proj m))
      ((multivariateGaussian 0 C).map D) := by
  sorry


end CKSD
