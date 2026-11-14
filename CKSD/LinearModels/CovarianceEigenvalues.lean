module
public import CKSD.LinearModels.EigenvaluePerturbation
public import CKSD.Nonparametric.EmpiricalCovariance.Basic
public import TauCeti.Probability.Distributions.Gaussian.MixedMoments
public import Mathlib.Probability.Distributions.Gaussian.Fernique
/-!
# Central limit law for simple covariance eigenvalues

A first-order eigenvalue perturbation bound and entrywise covariance fluctuation estimates
give asymptotic normality at any simple population eigenvalue under a fourth moment.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Module InnerProductSpace
open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
namespace CKSD

/-- Matrix form of the simple-eigenvalue quadratic remainder. -/
theorem abs_simple_matrix_eigenvalue_sub_rayleigh_le {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (j : Fin p) (u : EuclideanSpace ℝ (Fin p)) (hu : ‖u‖ = 1)
    (hAu : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = symmetricMatrixEigenvalues A j • u)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ k : Fin p, k ≠ j → δ ≤
      |symmetricMatrixEigenvalues A j - symmetricMatrixEigenvalues A k|) :
    |symmetricMatrixEigenvalues B j - symmetricMatrixEigenvalues A j -
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (B - A) u)| ≤
      (4 * Real.sqrt 2 / δ) * ‖B - A‖ ^ 2 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S := Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hT : LinearMap.IsSymmetric (T : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have hS : LinearMap.IsSymmetric (S : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.2 hB
  let e : Fin p ≃ Fin (Fintype.card (Fin p)) := finCongr (Fintype.card_fin p).symm
  have hla (i : Fin p) : hT.eigenvalues finrank_euclideanSpace (e i) = symmetricMatrixEigenvalues A i := by
    simp only [symmetricMatrixEigenvalues, dite_eq_left hA, Matrix.IsHermitian.eigenvalues₀]
    rfl
  have hlb (i : Fin p) : hS.eigenvalues finrank_euclideanSpace (e i) = symmetricMatrixEigenvalues B i := by
    simp only [symmetricMatrixEigenvalues, dite_eq_left hB, Matrix.IsHermitian.eigenvalues₀]
    rfl
  have hh := abs_simple_eigenvalue_sub_rayleigh_le T S hT hS finrank_euclideanSpace
    (e j) u hu (by simpa only [hla] using hAu) δ hδ (fun k hk ↦ by
      have hne : e.symm k ≠ j := fun h ↦ hk (by rw [← h, e.apply_symm_apply])
      have h := hgap (e.symm k) hne
      rw [← hla, ← hla, e.apply_symm_apply] at h
      exact h)
  rw [hla, hlb] at hh
  have hmap : S - T = Matrix.toEuclideanCLM (𝕜 := ℝ) (B - A) := by
    exact (map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ)) B A).symm
  rw [hmap, Matrix.l2_opNorm_toEuclideanCLM] at hh
  exact hh

/-- The Euclidean operator norm is bounded by the dimension times the entrywise sum. -/
theorem norm_matrix_le_card_mul_entrySum {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    ‖A‖ ≤ p * entrySum A := by
  have he (i j : Fin p) : ‖A i j‖ ≤ entrySum A := by
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (fun k _ ↦ abs_nonneg (A i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg fun l _ ↦ abs_nonneg (A k l))
        (Finset.mem_univ i))
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold entrySum; positivity)
  intro x
  change ‖Matrix.toEuclideanLin A x‖ ≤ _
  simpa only [Fintype.card_fin] using
    Matrix.norm_toEuclideanLin_le_of_entry_le_square he x

end CKSD

namespace CKSD
/-- A simple ordered empirical covariance eigenvalue has the scalar Rayleigh central limit law. -/
theorem simple_empirical_covariance_eigenvalue_asymptotics
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (j : Fin d) (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ)
    (hgap : 0 < gap)
    (hlambda : lambda = symmetricMatrixEigenvalues (euclideanCovarianceMatrix P) j)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hsep : ∀ k : Fin d, k ≠ j → gap ≤
      |lambda - symmetricMatrixEigenvalues (euclideanCovarianceMatrix P) k|) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
      (symmetricMatrixEigenvalues (empiricalCovarianceMatrix X n ω) j - lambda))
      atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal
        (Var[fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2; P]))) := by
  have hS : (euclideanCovarianceMatrix P).IsHermitian := TauCeti.isHermitian_covMatrix P
  have hA (n : ℕ) (ω : Ω) : (empiricalCovarianceMatrix X n ω).IsHermitian := by
    rw [Matrix.IsHermitian.ext_iff]
    intro i k
    simp [empiricalCovarianceMatrix, mul_comm]
  have hrem : TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n *
      (symmetricMatrixEigenvalues (empiricalCovarianceMatrix X n ω) j - lambda -
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) v)))
      atTop (fun _ ↦ 0) := by
    let C := (4 * Real.sqrt 2 / gap) * (d : ℝ) ^ 2
    have hlim := tendstoInMeasure_const_mul_zero μ _ C
      (tendstoInMeasure_sqrt_mul_entrySum_sq hiid h4)
    refine tendstoInMeasure_zero_of_abs_le' hlim (Filter.Eventually.of_forall fun n ω ↦ ?_)
    have hbd := abs_simple_matrix_eigenvalue_sub_rayleigh_le
      (euclideanCovarianceMatrix P) (empiricalCovarianceMatrix X n ω) hS (hA n ω)
      j v hv (by rw [← hlambda]; exact heig) gap hgap (by simpa only [← hlambda] using hsep)
    rw [← hlambda] at hbd
    let E := empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P
    have hnorm := norm_matrix_le_card_mul_entrySum E
    calc |Real.sqrt n * (symmetricMatrixEigenvalues (empiricalCovarianceMatrix X n ω) j -
          lambda - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) E v))| =
          Real.sqrt n * |symmetricMatrixEigenvalues (empiricalCovarianceMatrix X n ω) j -
            lambda - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) E v)| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt n * ((4 * Real.sqrt 2 / gap) * ‖E‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt n * ((4 * Real.sqrt 2 / gap) * ((d : ℝ) * entrySum E) ^ 2) := by
            gcongr
      _ = |C * (Real.sqrt n * entrySum E ^ 2)| := by
            rw [abs_of_nonneg (by dsimp [C]; positivity)]
            dsimp [C]
            ring
  have hmeasA := measurable_empiricalCovarianceMatrix hiid.1
  have hmeasEigen (n : ℕ) : Measurable (fun ω ↦ symmetricMatrixEigenvalues
      (empiricalCovarianceMatrix X n ω) j) := by
    have h := (Matrix.measurable_eigenvalues₀ (n := Fin d) (𝕜 := ℝ)).comp
      ((hmeasA n).subtype_mk (h := hA n))
    have hc := (measurable_pi_apply ⟨j.val, by simpa only [Fintype.card_fin] using j.isLt⟩).comp h
    convert hc using 1
    funext ω
    simp only [symmetricMatrixEigenvalues, dite_eq_left (hA n ω), Function.comp_apply]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid (quadStat P v)
    (measurable_quadStat v) (memLp_quadStat h4 v) (integral_quadStat h4 v)
  rw [integral_quadStat_sq_eq_variance h4 hv heig] at hclt
  have hmeasA := measurable_empiricalCovarianceMatrix hiid.1
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ _ _
    (fun n ↦ measurable_const.mul (Finset.measurable_fun_sum _ fun k _ ↦
      (measurable_quadStat v).comp (hiid.1 k)))
    (fun n ↦ measurable_const.mul
      ((hmeasEigen n).sub_const _)) hclt ?_
  -- the difference is the remainder plus a negligible quadratic term
  have hR : TendstoInMeasure μ (fun (n : ℕ) ω ↦ ∑ i, ∑ j, (-(v i * v j)) *
      (Real.sqrt n * sampleCoordMean P X i n ω * sampleCoordMean P X j n ω)) atTop
      (fun _ ↦ 0) :=
    tendstoInMeasure_finsetSum_zero _ fun i _ ↦ tendstoInMeasure_finsetSum_zero _ fun j _ ↦
      tendstoInMeasure_const_mul_zero μ _ _
        (tendstoInMeasure_sqrt_mul_sampleCoordMean_mul hiid h4 i j)
  refine tendstoInMeasure_zero_of_abs_le' (tendstoInMeasure_add_zero μ _ _ hrem hR) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  apply le_of_eq
  congr 1
  set A := empiricalCovarianceMatrix X n ω
  have hQ : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (A - euclideanCovarianceMatrix P) v) =
      ∑ i, ∑ j, v i * (sampleProdMean P X i j n ω -
        sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) * v j := by
    rw [inner_toEuclideanCLM_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.sub_apply, empiricalCovarianceMatrix_sub_eq P X hn ω i j]
  have hW : (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, quadStat P v (X k ω) =
      ∑ i, ∑ j, v i * (Real.sqrt n * sampleProdMean P X i j n ω) * v j := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
      rw [show (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ by
        rw [← mul_inv, Real.mul_self_sqrt hnR.le]]
      field_simp
    simp only [quadStat, sampleProdMean, ← mul_assoc, hs]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hsum : Real.sqrt n * (∑ i, ∑ j, v i * (sampleProdMean P X i j n ω -
        sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) * v j) =
      ∑ i, ∑ j, v i * (Real.sqrt n * sampleProdMean P X i j n ω) * v j +
        ∑ i, ∑ j, (-(v i * v j)) *
          (Real.sqrt n * sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hQ, hW]
  linear_combination hsum

/-- Variance of the squared centered Gaussian eigenvector coordinate. -/
theorem variance_sq_inner_gaussian_eigenvector {d : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian P]
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda : ℝ)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v) :
    Var[fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2; P] = 2 * lambda ^ 2 := by
  have h4 := IsGaussian.memLp_id P 4 (by simp)
  have hY : (fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2) = fun x ↦ quadStat P v x + lambda := by
    funext x
    rw [quadStat_eq hv heig]
    ring
  have hmean : ∫ x, inner ℝ (x - ∫ z, z ∂P) v ^ 2 ∂P = lambda := by
    rw [hY, integral_add ((memLp_quadStat h4 v).integrable (by norm_num))
      (integrable_const _), integral_quadStat h4, integral_const]
    simp
  have hc : covarianceBilinDual P (toDualMap ℝ _ v) (toDualMap ℝ _ v) = lambda := by
    rw [← covarianceBilin_eq_covarianceBilinDual, covarianceBilin_apply IsGaussian.memLp_two_id]
    convert hmean using 1
    congr 1
    funext x
    simp only [id_eq, real_inner_comm v, sq]
  have hm4 : ∫ x, (inner ℝ (x - ∫ z, z ∂P) v ^ 2) ^ 2 ∂P = 3 * lambda ^ 2 := by
    have h := ProbabilityTheory.IsGaussian.integral_pow_two_mul_sub_dual P (toDualMap ℝ _ v) 2
    rw [hc] at h
    norm_num at h
    calc
      _ = ∫ x, (toDualMap ℝ _ v) (x - P[id]) ^ 4 ∂P := by
        congr 1
        funext x
        change (inner ℝ (x - ∫ z, z ∂P) v ^ 2) ^ 2 =
          inner ℝ v (x - ∫ z, z ∂P) ^ 4
        rw [real_inner_comm v]
        ring
      _ = lambda ^ 2 * 3 := h
      _ = _ := by ring
  rw [variance_eq_sub (by rw [hY]; exact (memLp_quadStat h4 v).add (memLp_const _)), hmean]
  change (∫ x, (inner ℝ (x - ∫ z, z ∂P) v ^ 2) ^ 2 ∂P) - lambda ^ 2 = _
  rw [hm4]
  ring

end CKSD
