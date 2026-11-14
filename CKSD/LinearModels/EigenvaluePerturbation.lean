module

public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.Eigenvector
public import TauCeti.Analysis.Matrix.Eigenvalues.Continuous


/-!
# First-order perturbation of a simple ordered eigenvalue

A population spectral gap gives a quadratic remainder after subtracting the Rayleigh linear
term. The bound is valid for every ordered index and does not require sample simplicity.
It combines the operator Weyl inequality with the population-gap eigenvector alignment theorem
in TauCeti, following Yu, Wang and Samworth, Biometrika 102 (2015), Corollary 1.
The imported alignment theorem credits its Kitware implementation in its module header.
-/

@[expose] public section
noncomputable section
open Module
open scoped RealInnerProductSpace
namespace CKSD

/-- Ordered Hermitian eigenvalues, with an explicit zero convention outside the Hermitian locus. -/
def symmetricMatrixEigenvalues {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues₀ ⟨j.val, by simp⟩ else 0


/-- A population spectral gap gives a quadratic remainder for a simple ordered eigenvalue. -/
theorem abs_simple_eigenvalue_sub_rayleigh_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (A B : E →L[ℝ] E) (hA : LinearMap.IsSymmetric (A : E →ₗ[ℝ] E))
    (hB : LinearMap.IsSymmetric (B : E →ₗ[ℝ] E)) (hn : finrank ℝ E = n)
    (j : Fin n) (u : E) (hu : ‖u‖ = 1)
    (hAu : A u = hA.eigenvalues hn j • u) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ k : Fin n, k ≠ j → δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    |hB.eigenvalues hn j - hA.eigenvalues hn j - inner ℝ u ((B - A) u)| ≤
      (4 * Real.sqrt 2 / δ) * ‖B - A‖ ^ 2 := by
  let v := hB.eigenvectorBasis hn j
  have hv : ‖v‖ = 1 := (hB.eigenvectorBasis hn).orthonormal.norm_eq_one j
  have hBv : B v = hB.eigenvalues hn j • v := hB.apply_eigenvectorBasis hn j
  obtain ⟨c, hc, hclose⟩ :=
    LinearMap.IsSymmetric.exists_norm_eq_one_and_norm_smul_sub_eigenvector_le
      hu hv hAu hBv hδ hgap
  have hnorm : ((B : E →ₗ[ℝ] E) - (A : E →ₗ[ℝ] E)).toContinuousLinearMap = B - A := by
    ext x
    rfl
  rw [hnorm] at hclose
  let z := c • v
  have hBz : B z = hB.eigenvalues hn j • z := by
    simp only [z, map_smul, hBv, smul_smul]
    rw [mul_comm]
  have hweyl : |hB.eigenvalues hn j - hA.eigenvalues hn j| ≤ ‖B - A‖ :=
    hB.abs_eigenvalue_sub_eigenvalue_le_norm hA hn j
  have hs : inner ℝ u (A z) = inner ℝ (A u) z := (hA u z).symm
  have hEq : inner ℝ u ((B - A) z) =
      (hB.eigenvalues hn j - hA.eigenvalues hn j) * inner ℝ u z := by
    rw [sub_apply, inner_sub_right, hBz, real_inner_smul_right,
      hs, hAu, real_inner_smul_left]
    ring
  have hid : hB.eigenvalues hn j - hA.eigenvalues hn j - inner ℝ u ((B - A) u) =
      inner ℝ u ((B - A) (z - u)) +
        (hB.eigenvalues hn j - hA.eigenvalues hn j) * (1 - inner ℝ u z) := by
    rw [map_sub, inner_sub_right, hEq]
    ring
  have hi : |inner ℝ u ((B - A) (z - u))| ≤ ‖B - A‖ * ‖z - u‖ := by
    calc _ ≤ ‖u‖ * ‖(B - A) (z - u)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B - A‖ * ‖z - u‖ := by rw [hu, one_mul]; exact (B - A).le_opNorm _
  have ho : |1 - inner ℝ u z| ≤ ‖z - u‖ := by
    have he : 1 - inner ℝ u z = inner ℝ u (u - z) := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, hu]
      norm_num
    rw [he]
    simpa only [hu, one_mul, norm_sub_rev] using abs_real_inner_le_norm u (u - z)
  rw [hid]
  calc _ ≤ |inner ℝ u ((B - A) (z - u))| +
        |(hB.eigenvalues hn j - hA.eigenvalues hn j) * (1 - inner ℝ u z)| := abs_add_le _ _
    _ ≤ ‖B - A‖ * ‖z - u‖ + ‖B - A‖ * ‖z - u‖ := by
        apply add_le_add hi
        rw [abs_mul]
        exact mul_le_mul hweyl ho (abs_nonneg _) (norm_nonneg _)
    _ = 2 * ‖B - A‖ * ‖z - u‖ := by ring
    _ ≤ 2 * ‖B - A‖ * (2 * Real.sqrt 2 * ‖B - A‖ / δ) :=
        mul_le_mul_of_nonneg_left hclose (by positivity)
    _ = (4 * Real.sqrt 2 / δ) * ‖B - A‖ ^ 2 := by ring

end CKSD
