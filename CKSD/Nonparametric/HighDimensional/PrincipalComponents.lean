module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
public import CKSD.Nonparametric.Basic

/-!
# Optimality of principal components for reconstruction

## Main results

* `CKSD.norm_sub_sum_inner_smul_sq`: Pythagoras for the projection onto the span of an
  orthonormal family.
* `CKSD.sum_ite_le_integral_norm_sub_sum_inner_smul_sq`: no projection onto `k` orthonormal
  directions has expected reconstruction error below the sum of the trailing eigenvalues of the
  covariance.

Source: GAPS 103.31.

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

end CKSD
