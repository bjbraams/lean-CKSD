module

public import CKSD.LinearModels.BlockWishart
public import CKSD.LinearModels.SphericityBasic
public import TauCeti.Analysis.Matrix.PosSemidef.Determinant
/-!
# Block-independence ratios and Gaussian sample covariance

The determinant ratio of a positive-definite matrix and its two principal blocks lies in
`(0,1]` by Hadamard–Fischer. It is measurable and invariant under nonzero rescaling, so its
Gaussian sample-covariance law agrees with the corresponding centered-scatter Wishart law.

The statistic is Muirhead, *Aspects of Multivariate Statistical Theory*, equation (8), printed
page 532 (PDF page 558 of the local 2005 copy); see also Anderson, *An Introduction to
Multivariate Statistical Analysis*, 3rd ed., Section 9.2. Pinned TauCeti supplies the matrix
Hadamard–Fischer inequality, and local sample theory supplies the Gaussian scatter law.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology MatrixOrder BigOperators
namespace CKSD
/-- The determinant ratio for independence of two consecutive coordinate blocks. -/
def blockIndependenceRatio {p q : ℕ} (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) : ℝ :=
  A.det / ((A.submatrix (Fin.castAdd q) (Fin.castAdd q)).det *
    (A.submatrix (Fin.natAdd p) (Fin.natAdd p)).det)
/-- A Hermitian matrix reindexed as a sum is the matrix of its two principal blocks. -/
theorem submatrix_fin_sum_fin_equiv_eq_from_blocks {p q : ℕ}
    {A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ} (hA : A.IsHermitian) :
    A.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (A.submatrix (Fin.castAdd q) (Fin.castAdd q))
      (A.submatrix (Fin.castAdd q) (Fin.natAdd p))
      (A.submatrix (Fin.castAdd q) (Fin.natAdd p)).conjTranspose
      (A.submatrix (Fin.natAdd p) (Fin.natAdd p)) := by
  ext (i|i) (j|j) <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply]
  simpa only [star_trivial] using (hA.apply (Fin.castAdd q j) (Fin.natAdd p i))
/-- The determinant of a Hermitian block-diagonal matrix factors into its block determinants. -/
theorem det_eq_mul_det_principal_blocks_of_zero {p q : ℕ}
    {A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ} (hA : A.IsHermitian)
    (hblock : A.submatrix (Fin.castAdd q) (Fin.natAdd p) = 0) :
    A.det = (A.submatrix (Fin.castAdd q) (Fin.castAdd q)).det *
      (A.submatrix (Fin.natAdd p) (Fin.natAdd p)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv A,
    submatrix_fin_sum_fin_equiv_eq_from_blocks hA, hblock, Matrix.conjTranspose_zero,
    Matrix.det_fromBlocks_zero₂₁]
/-- The positive-definite block determinant ratio lies in the unit interval. -/
theorem block_independence_ratio_mem_ioc {p q : ℕ}
    {A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ} (hA : A.PosDef) :
    blockIndependenceRatio A ∈ Ioc (0 : ℝ) 1 := by
  have hf : Function.Injective (Fin.castAdd q : Fin p → Fin (p+q)) := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin (p+q) ↦ k.val) h
  have hg : Function.Injective (Fin.natAdd p : Fin q → Fin (p+q)) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun k : Fin (p+q) ↦ k.val) h
    simpa using hv
  have h₁ := hA.submatrix hf
  have h₂ := hA.submatrix hg
  have hden := mul_pos h₁.det_pos h₂.det_pos
  refine ⟨div_pos hA.det_pos hden, (div_le_one hden).2 ?_⟩
  have hpos := hA.posSemidef.submatrix finSumFinEquiv
  rw [submatrix_fin_sum_fin_equiv_eq_from_blocks hA.isHermitian] at hpos
  have h := hpos.det_fromBlocks_le
  rw [← submatrix_fin_sum_fin_equiv_eq_from_blocks hA.isHermitian] at h
  simpa only [Matrix.det_submatrix_equiv_self] using h
/-- Nonzero rescaling leaves the block determinant ratio invariant. -/
theorem block_independence_ratio_smul {p q : ℕ}
    (A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ) {r : ℝ} (hr : r ≠ 0) :
    blockIndependenceRatio (r • A) = blockIndependenceRatio A := by
  simp only [blockIndependenceRatio, Matrix.submatrix_smul, Pi.smul_apply, Matrix.det_smul, Fintype.card_fin]
  rw [pow_add]
  convert mul_div_mul_left A.det
    ((A.submatrix (Fin.castAdd q) (Fin.castAdd q)).det *
      (A.submatrix (Fin.natAdd p) (Fin.natAdd p)).det) (mul_ne_zero (pow_ne_zero p hr) (pow_ne_zero q hr)) using 1; ring
/-- The block determinant ratio is a Borel measurable matrix statistic. -/
theorem measurable_block_independence_ratio (p q : ℕ) :
    Measurable (blockIndependenceRatio : Matrix (Fin (p+q)) (Fin (p+q)) ℝ → ℝ) := by
  unfold blockIndependenceRatio
  fun_prop
/-- The block determinant ratio of Gaussian sample covariance has its scatter Wishart law. -/
theorem map_block_independence_ratio_sample_covariance_matrix_eq_wishart
    {n p q : ℕ} (hpq : 0 < p+q) (hn : p+q+1 ≤ n)
    (m : EuclideanSpace ℝ (Fin (p+q))) (Sigma : Matrix (Fin (p+q)) (Fin (p+q)) ℝ)
    (hS : Sigma.PosDef) :
    (Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma)).map
      (fun x ↦ blockIndependenceRatio (sampleCovarianceMatrix x)) =
      (TauCeti.Probability.wishartGramMeasure (n-1) Sigma).map
        (fun A ↦ blockIndependenceRatio (A.val : Matrix (Fin (p+q)) (Fin (p+q)) ℝ)) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have heq : (fun x : Fin n → EuclideanSpace ℝ (Fin (p+q)) ↦
      blockIndependenceRatio (sampleCovarianceMatrix x)) =
      fun x ↦ blockIndependenceRatio (scatterMatrix x) := by
    funext x
    exact block_independence_ratio_smul _ (inv_ne_zero hn0)
  rw [heq]
  change (Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma)).map
    (blockIndependenceRatio ∘ scatterMatrix) = _
  rw [← Measure.map_map (measurable_block_independence_ratio p q) measurable_scatter_matrix,
    (gaussian_sample_mean_scatter_matrix_wishart_and_hotelling hpq hn m Sigma hS).2.1,
    Measure.map_map (measurable_block_independence_ratio p q) measurable_subtype_coe]
  rfl
end CKSD
