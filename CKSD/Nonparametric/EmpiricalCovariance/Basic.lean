module

public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Moments.Covariance
public import CKSD.Asymptotics.Basic


/-!
# Empirical covariance: moment and fluctuation estimates

Population and sample-centred covariance matrices in finite-dimensional Euclidean space,
with a finite fourth moment. Their entries are root-`n` consistent, and the squared entrywise
error is negligible at the central-limit scale. The centred quadratic statistic supplies
the scalar central limit theorem for covariance Rayleigh values.

Mathlib supplies moment inequalities, the law of large numbers and the central limit theorem;
TauCeti supplies the population covariance matrix. These estimates are shared by the
nonparametric leading-component results and multivariate Gaussian eigenvalue limits.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator
namespace CKSD

/-- Population covariance in Euclidean coordinates, using Mathlib's covariance adapter. -/
abbrev euclideanCovarianceMatrix {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin d) ℝ :=
  TauCeti.covMatrix P

/-- The sample-centred empirical covariance matrix, with divisor `n`. -/
def empiricalCovarianceMatrix {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (∑ k ∈ Finset.range n,
    (X k ω i - sampleAverage X n ω i) * (X k ω j - sampleAverage X n ω j)) / n

/-- The entrywise `ℓ¹` norm `∑ᵢ ∑ⱼ |Aᵢⱼ|` of a square matrix. -/
def entrySum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, |A i j|

/-- The bilinear form of a matrix in coordinates: `⟪x, A y⟫ = ∑ᵢ ∑ⱼ xᵢ Aᵢⱼ yⱼ`. -/
theorem inner_to_euclidean_clm_eq_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) = ∑ i, ∑ j, x i * A i j * y j := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The Hölder triple `1/4 + 1/4 = 1/2`. -/
private theorem holder_triple_four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

section Population

variable {d : ℕ} {P : Measure (EuclideanSpace ℝ (Fin d))}

/-- Coordinates of a vector with finite fourth moment have finite fourth moments. -/
private theorem mem_lp_coord (h4 : MemLp id 4 P) (i : Fin d) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) 4 P :=
  (memLp_piLp_iff.mp h4) i

/-- The coordinates of the mean vector are the means of the coordinates. -/
private theorem integral_apply_eq [IsProbabilityMeasure P] (h4 : MemLp id 4 P) (i : Fin d) :
    (∫ z, z ∂P) i = ∫ x, x i ∂P :=
  eval_integral_piLp (fun i ↦ (mem_lp_coord h4 i).integrable (by norm_num)) i

/-- The covariance matrix entries as integrals of centered products. -/
private theorem euclidean_covariance_matrix_eq [IsProbabilityMeasure P] (h4 : MemLp id 4 P)
    (i j : Fin d) :
    euclideanCovarianceMatrix P i j =
      ∫ x, (x i - (∫ z, z ∂P) i) * (x j - (∫ z, z ∂P) j) ∂P := by
  rw [integral_apply_eq h4, integral_apply_eq h4, euclideanCovarianceMatrix,
    TauCeti.covMatrix_apply, covariance]

/-- The covariance matrix is symmetric. -/
theorem euclidean_covariance_matrix_symm (i j : Fin d) :
    euclideanCovarianceMatrix P i j = euclideanCovarianceMatrix P j i :=
  TauCeti.covMatrix_apply_comm P i j

/-- The centered product statistic `(xᵢ - mᵢ)(xⱼ - mⱼ) - Σᵢⱼ`, with `m` the mean of `P`. -/
def centeredProduct (P : Measure (EuclideanSpace ℝ (Fin d))) (i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (x i - (∫ z, z ∂P) i) * (x j - (∫ z, z ∂P) j) - euclideanCovarianceMatrix P i j

/-- Products of centered coordinates are square integrable under a fourth moment. -/
private theorem mem_lp_centered_product_aux [IsProbabilityMeasure P] (h4 : MemLp id 4 P)
    (i j : Fin d) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ (x i - (∫ z, z ∂P) i) * (x j - (∫ z, z ∂P) j))
      2 P := by
  have := holder_triple_four_four_two
  have hi : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x i - (∫ z, z ∂P) i) 4 P :=
    (mem_lp_coord h4 i).sub (memLp_const _)
  have hj : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x j - (∫ z, z ∂P) j) 4 P :=
    (mem_lp_coord h4 j).sub (memLp_const _)
  exact hi.mul (r := 2) hj

/-- The centered product statistic is square integrable under a fourth moment. -/
private theorem mem_lp_centered_product [IsProbabilityMeasure P] (h4 : MemLp id 4 P) (i j : Fin d) :
    MemLp (centeredProduct P i j) 2 P :=
  (mem_lp_centered_product_aux h4 i j).sub (memLp_const _)

/-- The centered product statistic has mean zero. -/
private theorem integral_centered_product [IsProbabilityMeasure P] (h4 : MemLp id 4 P)
    (i j : Fin d) :
    ∫ x, centeredProduct P i j x ∂P = 0 := by
  unfold centeredProduct
  rw [integral_sub ((mem_lp_centered_product_aux h4 i j).integrable (by norm_num))
    (integrable_const _), integral_const, euclidean_covariance_matrix_eq h4]
  simp

/-- The centered product statistic is measurable. -/
private theorem measurable_centered_product (i j : Fin d) : Measurable (centeredProduct P i j) := by
  unfold centeredProduct; fun_prop

/-- The centered coordinate statistic `xᵢ - mᵢ`. -/
def centeredCoord (P : Measure (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := x i - (∫ z, z ∂P) i

/-- The centered coordinate is square integrable under a fourth moment. -/
private theorem mem_lp_centered_coord [IsProbabilityMeasure P] (h4 : MemLp id 4 P) (i : Fin d) :
    MemLp (centeredCoord P i) 2 P :=
  ((mem_lp_coord h4 i).sub (memLp_const _)).mono_exponent (by norm_num)

/-- The centered coordinate has mean zero. -/
private theorem integral_centered_coord [IsProbabilityMeasure P] (h4 : MemLp id 4 P) (i : Fin d) :
    ∫ x, centeredCoord P i x ∂P = 0 := by
  unfold centeredCoord
  rw [integral_sub ((mem_lp_coord h4 i).integrable (by norm_num)) (integrable_const _),
    integral_const, integral_apply_eq h4]
  simp

/-- The centered coordinate is measurable. -/
private theorem measurable_centered_coord (i : Fin d) : Measurable (centeredCoord P i) := by
  unfold centeredCoord; fun_prop

end Population

section Sample

variable {Ω : Type*} {d : ℕ}

/-- The sample mean of the centered product statistic. -/
def sampleProdMean (P : Measure (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (i j : Fin d) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, centeredProduct P i j (X k ω)

/-- The sample mean of the centered coordinate statistic, `X̄ᵢ - mᵢ` for `n ≥ 1`. -/
def sampleCoordMean (P : Measure (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (i : Fin d) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, centeredCoord P i (X k ω)

/-- Coordinates of the sample average. -/
theorem sample_average_apply (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω)
    (i : Fin d) :
    sampleAverage X n ω i = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω i := by
  simp [sampleAverage]

/-- For `n ≥ 1`, `Σ̂ᵢⱼ - Σᵢⱼ` is the sample mean of the centered product minus the product of
the centered coordinate means. -/
theorem empirical_covariance_matrix_sub_eq (P : Measure (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) {n : ℕ} (hn : 0 < n) (ω : Ω) (i j : Fin d) :
    empiricalCovarianceMatrix X n ω i j - euclideanCovarianceMatrix P i j =
      sampleProdMean P X i j n ω - sampleCoordMean P X i n ω * sampleCoordMean P X j n ω := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set m := ∫ z, z ∂P
  set ci := sampleCoordMean P X i n ω
  set cj := sampleCoordMean P X j n ω
  have hci : sampleAverage X n ω i = m i + ci := by
    simp only [ci, sampleCoordMean, centeredCoord, sample_average_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp; ring
  have hcj : sampleAverage X n ω j = m j + cj := by
    simp only [cj, sampleCoordMean, centeredCoord, sample_average_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp; ring
  have hsi : ∑ k ∈ Finset.range n, (X k ω i - m i) = n * ci := by
    simp only [ci, sampleCoordMean, centeredCoord]; field_simp; rfl
  have hsj : ∑ k ∈ Finset.range n, (X k ω j - m j) = n * cj := by
    simp only [cj, sampleCoordMean, centeredCoord]; field_simp; rfl
  unfold empiricalCovarianceMatrix sampleProdMean centeredProduct
  rw [hci, hcj]
  have e : ∀ k, (X k ω i - (m i + ci)) * (X k ω j - (m j + cj)) =
      (X k ω i - m i) * (X k ω j - m j) - ci * (X k ω j - m j) - cj * (X k ω i - m i) +
        ci * cj := fun k ↦ by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsi, hsj,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

end Sample

section Limits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Sums of sequences bounded in probability are bounded in probability. -/
private theorem IsBoundedInProbability.add' [IsFiniteMeasure μ] {X Y : ℕ → Ω → ℝ}
    (hX : IsBoundedInProbability μ X) (hY : IsBoundedInProbability μ Y) :
    IsBoundedInProbability μ (fun n ω ↦ X n ω + Y n ω) := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hX (ε / 2) (half_pos hε)
  obtain ⟨C₂, hC₂, h₂⟩ := hY (ε / 2) (half_pos hε)
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  calc μ.real {ω | C₁ + C₂ < |X n ω + Y n ω|}
      ≤ μ.real ({ω | C₁ < |X n ω|} ∪ {ω | C₂ < |Y n ω|}) := by
        refine measureReal_mono (fun ω (hω : C₁ + C₂ < |X n ω + Y n ω|) ↦ ?_)
        by_contra h
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at h
        have := abs_add_le (X n ω) (Y n ω)
        linarith [h.1, h.2]
    _ ≤ μ.real {ω | C₁ < |X n ω|} + μ.real {ω | C₂ < |Y n ω|} := measureReal_union_le _ _
    _ ≤ ε := by linarith

/-- Eventual pointwise domination preserves boundedness in probability. -/
private theorem IsBoundedInProbability.of_abs_le {X Y : ℕ → Ω → ℝ} (hX : IsBoundedInProbability μ X)
    (h : ∀ᶠ n in atTop, ∀ ω, |Y n ω| ≤ |X n ω|) [IsFiniteMeasure μ] :
    IsBoundedInProbability μ Y := by
  intro ε hε
  obtain ⟨C, hC, hev⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, h] with n hn hn'
  refine le_trans (measureReal_mono fun ω (hω : C < |Y n ω|) ↦ ?_) hn
  exact (show C < |X n ω| from hω.trans_le (hn' ω))

/-- Eventual pointwise domination by a sequence tending to zero in probability. -/
theorem tendstoInMeasure_zero_of_abs_le' [IsFiniteMeasure μ] {X Y : ℕ → Ω → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ ↦ 0))
    (h : ∀ᶠ n in atTop, ∀ ω, |Y n ω| ≤ |X n ω|) :
    TendstoInMeasure μ Y atTop (fun _ ↦ 0) :=
  tendsto_in_measure_zero_of_abs_le μ X Y (fun _ _ ↦ 0) one_pos
    (h.mono fun _ hn ↦ Filter.Eventually.of_forall fun ω _ ↦ hn ω) hX
    (tendsto_in_measure_const_of_tendsto μ (fun _ ↦ 0) tendsto_const_nhds)

/-- Finite sums of sequences tending to zero in probability tend to zero in probability. -/
theorem tendsto_in_measure_finset_sum_zero [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    {X : ι → ℕ → Ω → ℝ} (hX : ∀ i ∈ s, TendstoInMeasure μ (X i) atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ s, X i n ω) atTop (fun _ ↦ 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using tendsto_in_measure_const_of_tendsto μ (fun _ ↦ (0 : ℝ)) tendsto_const_nhds
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tendsto_in_measure_add_zero μ _ _ (hX a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

/-- Finite sums of sequences bounded in probability are bounded in probability. -/
private theorem is_bounded_in_probability_finset_sum [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    {X : ι → ℕ → Ω → ℝ} (hX : ∀ i ∈ s, IsBoundedInProbability μ (X i)) :
    IsBoundedInProbability μ (fun n ω ↦ ∑ i ∈ s, X i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact is_bounded_in_probability_of_tendsto_in_measure μ _ 0
      (tendsto_in_measure_const_of_tendsto μ (fun _ ↦ (0 : ℝ)) tendsto_const_nhds)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hX a (Finset.mem_insert_self a s)).add'
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

/-- If `|Yₙ| ≤ K |Vₙ|` whenever `|Uₙ| < δ`, with `Vₙ` bounded and `Uₙ → 0` in probability, then
`Yₙ` is bounded in probability. -/
theorem IsBoundedInProbability.of_abs_le_of_tendsto_in_measure [IsFiniteMeasure μ]
    {V U Y : ℕ → Ω → ℝ} (hV : IsBoundedInProbability μ V)
    (hU : TendstoInMeasure μ U atTop (fun _ ↦ 0)) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ n ω, |U n ω| < δ → |Y n ω| ≤ K * |V n ω|) :
    IsBoundedInProbability μ Y := by
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at hU
  intro ε hε
  obtain ⟨C, hC, hev⟩ := hV (ε / 2) (half_pos hε)
  refine ⟨(K + 1) * C, by positivity, ?_⟩
  have hU' := (hU (δ / 2) (half_pos hδ)).eventually (eventually_le_nhds (half_pos hε))
  filter_upwards [hev, hU'] with n hn hn'
  calc μ.real {ω | (K + 1) * C < |Y n ω|}
      ≤ μ.real ({ω | C < |V n ω|} ∪ {ω | δ / 2 < dist (U n ω) 0}) := by
        refine measureReal_mono (fun ω (hω : (K + 1) * C < |Y n ω|) ↦ ?_)
        by_contra hc
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt, Real.dist_eq, sub_zero] at hc
        have := h n ω (by linarith [hc.2])
        nlinarith [hc.1, abs_nonneg (V n ω)]
    _ ≤ μ.real {ω | C < |V n ω|} + μ.real {ω | δ / 2 < dist (U n ω) 0} :=
        measureReal_union_le _ _
    _ ≤ ε := by linarith

end Limits

section IID

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Type*}
  [MeasurableSpace E] {P : Measure E} {X : ℕ → Ω → E}

/-- Weak law of large numbers for a centered square-integrable statistic of an i.i.d. sequence. -/
private theorem tendsto_in_measure_sample_mean_zero (hiid : IsIndependentIdenticallyDistributed μ X P)
    {s : E → ℝ} (hs : Measurable s) (h2 : MemLp s 2 P) (h0 : ∫ x, s x ∂P = 0) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, s (X k ω))
      atTop (fun _ ↦ 0) := by
  have hP : IsProbabilityMeasure P := by
    rw [← hiid.2.2 0]; infer_instance
  have := tendsto_in_measure_sample_mean_of_iid μ P X hiid s hs (h2.integrable (by norm_num))
  rwa [h0] at this

/-- Root-`n` boundedness of the sample mean of a centered square-integrable statistic, from the
central limit theorem. -/
private theorem is_bounded_in_probability_sqrt_mul_sample_mean
    (hiid : IsIndependentIdenticallyDistributed μ X P)
    {s : E → ℝ} (hs : Measurable s) (h2 : MemLp s 2 P) (h0 : ∫ x, s x ∂P = 0) :
    IsBoundedInProbability μ
      (fun (n : ℕ) ω ↦ Real.sqrt n * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, s (X k ω))) := by
  have hP : IsProbabilityMeasure P := by
    rw [← hiid.2.2 0]; infer_instance
  have hclt := tendsto_in_distribution_inv_sqrt_mul_sum_of_iid μ P X hiid s hs h2 h0
  have e : (fun (n : ℕ) ω ↦ Real.sqrt n * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, s (X k ω))) =
      fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, s (X k ω) := by
    funext n ω
    rw [← mul_assoc]
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h : (0 : ℝ) < n := by exact_mod_cast hn
      have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr h).ne'
      rw [show (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ by
        rw [← mul_inv, Real.mul_self_sqrt h.le]]
      field_simp
  rw [e]
  exact is_bounded_in_probability_of_tendsto_in_distribution μ _ hclt

end IID

section Entries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
  {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

/-- The centered coordinate means tend to zero in probability. -/
private theorem tendsto_in_measure_sample_coord_mean (hiid : IsIndependentIdenticallyDistributed μ X P)
    (h4 : MemLp id 4 P) (i : Fin d) :
    TendstoInMeasure μ (sampleCoordMean P X i) atTop (fun _ ↦ 0) :=
  tendsto_in_measure_sample_mean_zero hiid (measurable_centered_coord i) (mem_lp_centered_coord h4 i)
    (integral_centered_coord h4 i)

/-- The centered coordinate means are of order `n^{-1/2}` in probability. -/
private theorem is_bounded_in_probability_sqrt_mul_sample_coord_mean
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) (i : Fin d) :
    IsBoundedInProbability μ (fun (n : ℕ) ω ↦ Real.sqrt n * sampleCoordMean P X i n ω) :=
  is_bounded_in_probability_sqrt_mul_sample_mean hiid (measurable_centered_coord i)
    (mem_lp_centered_coord h4 i) (integral_centered_coord h4 i)

/-- Products of centered coordinate means tend to zero in probability. -/
private theorem tendsto_in_measure_sample_coord_mean_mul
    (hiid : IsIndependentIdenticallyDistributed μ X P)
    (h4 : MemLp id 4 P) (i j : Fin d) :
    TendstoInMeasure μ (fun n ω ↦ sampleCoordMean P X i n ω * sampleCoordMean P X j n ω)
      atTop (fun _ ↦ 0) :=
  tendsto_in_measure_mul_zero_of_is_bounded_in_probability μ _ _
    (is_bounded_in_probability_of_tendsto_in_measure μ _ 0 (tendsto_in_measure_sample_coord_mean hiid h4 i))
    (tendsto_in_measure_sample_coord_mean hiid h4 j)

/-- Products of centered coordinate means are `o_P(n^{-1/2})`. -/
theorem tendsto_in_measure_sqrt_mul_sample_coord_mean_mul
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) (i j : Fin d) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n * sampleCoordMean P X i n ω *
      sampleCoordMean P X j n ω) atTop (fun _ ↦ 0) :=
  tendsto_in_measure_mul_zero_of_is_bounded_in_probability μ _ _
    (is_bounded_in_probability_sqrt_mul_sample_coord_mean hiid h4 i)
    (tendsto_in_measure_sample_coord_mean hiid h4 j)

/-- Consistency of each empirical covariance entry. -/
private theorem tendsto_in_measure_empirical_covariance_sub
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) (i j : Fin d) :
    TendstoInMeasure μ (fun n ω ↦ empiricalCovarianceMatrix X n ω i j -
      euclideanCovarianceMatrix P i j) atTop (fun _ ↦ 0) := by
  have ha : TendstoInMeasure μ (sampleProdMean P X i j) atTop (fun _ ↦ 0) :=
    tendsto_in_measure_sample_mean_zero hiid (measurable_centered_product i j)
      (mem_lp_centered_product h4 i j) (integral_centered_product h4 i j)
  have hc := tendsto_in_measure_const_mul_zero μ _ (-1)
    (tendsto_in_measure_sample_coord_mean_mul hiid h4 i j)
  refine tendstoInMeasure_zero_of_abs_le' (tendsto_in_measure_add_zero μ _ _ ha hc) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  rw [empirical_covariance_matrix_sub_eq P X hn ω i j]
  apply le_of_eq; congr 1; ring

/-- Each empirical covariance entry is root-`n` consistent. -/
private theorem is_bounded_in_probability_sqrt_mul_empirical_covariance_sub
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) (i j : Fin d) :
    IsBoundedInProbability μ (fun (n : ℕ) ω ↦ Real.sqrt n * (empiricalCovarianceMatrix X n ω i j -
      euclideanCovarianceMatrix P i j)) := by
  have ha : IsBoundedInProbability μ (fun (n : ℕ) ω ↦ Real.sqrt n * sampleProdMean P X i j n ω) :=
    is_bounded_in_probability_sqrt_mul_sample_mean hiid (measurable_centered_product i j)
      (mem_lp_centered_product h4 i j) (integral_centered_product h4 i j)
  have hc := is_bounded_in_probability_of_tendsto_in_measure μ _ 0
    (tendsto_in_measure_const_mul_zero μ _ (-1)
      (tendsto_in_measure_sqrt_mul_sample_coord_mean_mul hiid h4 i j))
  refine (ha.add' hc).of_abs_le ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  rw [empirical_covariance_matrix_sub_eq P X hn ω i j]
  apply le_of_eq; congr 1; ring

/-- The entrywise `ℓ¹` error of the empirical covariance tends to zero in probability. -/
theorem tendsto_in_measure_entry_sum (hiid : IsIndependentIdenticallyDistributed μ X P)
    (h4 : MemLp id 4 P) :
    TendstoInMeasure μ (fun n ω ↦ entrySum (empiricalCovarianceMatrix X n ω -
      euclideanCovarianceMatrix P)) atTop (fun _ ↦ 0) := by
  simp only [entrySum, Matrix.sub_apply]
  refine tendsto_in_measure_finset_sum_zero _ fun i _ ↦ tendsto_in_measure_finset_sum_zero _ fun j _ ↦ ?_
  exact tendstoInMeasure_zero_of_abs_le' (tendsto_in_measure_empirical_covariance_sub hiid h4 i j)
    (Filter.Eventually.of_forall fun n ω ↦ by rw [abs_abs])

/-- The entrywise `ℓ¹` error of the empirical covariance is `O_P(n^{-1/2})`. -/
theorem is_bounded_in_probability_sqrt_mul_entry_sum
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) :
    IsBoundedInProbability μ (fun (n : ℕ) ω ↦ Real.sqrt n * entrySum
      (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P)) := by
  simp only [entrySum, Matrix.sub_apply, Finset.mul_sum]
  refine is_bounded_in_probability_finset_sum _ fun i _ ↦ is_bounded_in_probability_finset_sum _
    fun j _ ↦ ?_
  refine (is_bounded_in_probability_sqrt_mul_empirical_covariance_sub hiid h4 i j).of_abs_le
    (Filter.Eventually.of_forall fun n ω ↦ ?_)
  rw [abs_mul, abs_mul, abs_abs]

/-- The squared entrywise `ℓ¹` error of the empirical covariance is `o_P(n^{-1/2})`. -/
theorem tendsto_in_measure_sqrt_mul_entry_sum_sq
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n * entrySum
      (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) ^ 2) atTop
      (fun _ ↦ 0) := by
  have := tendsto_in_measure_mul_zero_of_is_bounded_in_probability μ _ _
    (is_bounded_in_probability_sqrt_mul_entry_sum hiid h4) (tendsto_in_measure_entry_sum hiid h4)
  refine this.congr_left fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_
  simp only; ring

/-- The empirical covariance matrix is a measurable function of the sample. -/
theorem measurable_empirical_covariance_matrix (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable fun ω ↦ empiricalCovarianceMatrix X n ω := by
  have hc : ∀ k (i : Fin d), Measurable fun ω ↦ X k ω i := fun k i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp (hX k)
  have ha : ∀ i : Fin d, Measurable fun ω ↦ sampleAverage X n ω i := fun i ↦ by
    rw [show (fun ω ↦ sampleAverage X n ω i) = fun ω ↦
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω i from funext fun ω ↦ sample_average_apply X n ω i]
    have : Measurable fun ω ↦ ∑ k ∈ Finset.range n, X k ω i :=
      Finset.measurable_fun_sum (Finset.range n) fun k _ ↦ hc k i
    exact this.const_mul _
  refine Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ ?_
  unfold empiricalCovarianceMatrix
  exact (Finset.measurable_fun_sum _ fun k _ ↦
    ((hc k i).sub (ha i)).mul ((hc k j).sub (ha j))).div_const _

omit [IsProbabilityMeasure P] in
/-- The Rayleigh value of the covariance at its unit eigenvector `v` is the eigenvalue. -/
theorem inner_euclidean_covariance_matrix_self {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {lam : ℝ}
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lam • v) :
    inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v) = lam := by
  rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]; ring

/-- The centered quadratic statistic `∑ᵢ ∑ⱼ vᵢ vⱼ ((xᵢ - mᵢ)(xⱼ - mⱼ) - Σᵢⱼ)`. -/
def quadStat (P : Measure (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, v i * centeredProduct P i j x * v j

omit [IsProbabilityMeasure P] in
/-- The centered quadratic statistic equals `⟪x - m, v⟫² - λ`. -/
theorem quad_stat_eq {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {lam : ℝ}
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lam • v)
    (x : EuclideanSpace ℝ (Fin d)) :
    quadStat P v x = inner ℝ (x - ∫ z, z ∂P) v ^ 2 - lam := by
  have h := inner_euclidean_covariance_matrix_self hv heig
  rw [inner_to_euclidean_clm_eq_sum] at h
  rw [← h, PiLp.inner_apply, sq, Finset.sum_mul_sum]
  unfold quadStat centeredProduct
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
  ring

/-- The centered quadratic statistic is square integrable under a fourth moment. -/
theorem mem_lp_quad_stat (h4 : MemLp id 4 P) (v : EuclideanSpace ℝ (Fin d)) :
    MemLp (quadStat P v) 2 P := by
  unfold quadStat
  exact memLp_finsetSum _ fun i _ ↦ memLp_finsetSum _ fun j _ ↦
    ((mem_lp_centered_product h4 i j).const_mul (v i)).mul_const (v j)

/-- The centered quadratic statistic has mean zero. -/
theorem integral_quad_stat (h4 : MemLp id 4 P) (v : EuclideanSpace ℝ (Fin d)) :
    ∫ x, quadStat P v x ∂P = 0 := by
  have hint : ∀ i j, Integrable (fun x ↦ v i * centeredProduct P i j x * v j) P := fun i j ↦
    ((((mem_lp_centered_product h4 i j).integrable (by norm_num)).const_mul (v i)).mul_const (v j))
  unfold quadStat
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [integral_mul_const, integral_const_mul, integral_centered_product h4]; ring

omit [IsProbabilityMeasure P] in
/-- The centered quadratic statistic is measurable. -/
theorem measurable_quad_stat (v : EuclideanSpace ℝ (Fin d)) : Measurable (quadStat P v) := by
  unfold quadStat
  exact Finset.measurable_fun_sum _ fun i _ ↦ Finset.measurable_fun_sum _ fun j _ ↦
    ((measurable_centered_product i j).const_mul _).mul_const _

/-- The second moment of the centered quadratic statistic is `Var ⟪X - m, v⟫²`. -/
theorem integral_quad_stat_sq_eq_variance (h4 : MemLp id 4 P) {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) {lam : ℝ}
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lam • v) :
    ∫ x, quadStat P v x ^ 2 ∂P = Var[fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2; P] := by
  have hY : (fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2) = fun x ↦ quadStat P v x + lam := by
    funext x; rw [quad_stat_eq hv heig]; ring
  have hint : Integrable (quadStat P v) P := (mem_lp_quad_stat h4 v).integrable (by norm_num)
  have hmean : ∫ x, inner ℝ (x - ∫ z, z ∂P) v ^ 2 ∂P = lam := by
    rw [hY, integral_add hint (integrable_const _), integral_quad_stat h4, integral_const]; simp
  rw [variance_eq_integral (by rw [hY]; exact ((measurable_quad_stat v).add_const _).aemeasurable),
    hmean]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [quad_stat_eq hv heig]

end Entries

end CKSD
