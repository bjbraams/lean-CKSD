module

import CKSD.Bayes.MonteCarlo.FiniteChain
public import CKSD.Bayes.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Metropolis–Hastings chains on finite state spaces

The Metropolis–Hastings transition matrix `CKSD.metropolisTransition π q` of a target `π` and a
proposal matrix `q` on a finite state space, its reversibility, and its convergence. Markov
chains are specified by their finite-dimensional path probabilities as in
`CKSD.Bayes.MonteCarlo.FiniteChain`; total-variation convergence on a finite space is stated as
convergence uniform over events `A`.

## Main results

* `CKSD.metropolisTransition_mem_rowStochastic`, `CKSD.metropolisTransition_detailedBalance`,
  `CKSD.sum_mul_metropolisTransition`: the Metropolis–Hastings matrix is row stochastic and
  reversible with respect to its target, which is therefore invariant (GAPS 104.22).
* `CKSD.abs_sum_independenceSampler_pow_sub_le`: the independence sampler converges at rate
  `(1 - 1 / M)ⁿ` when `π ≤ M g` (GAPS 104.32).
* `CKSD.eventually_abs_metropolisTransition_pow_sub_le`: total-variation convergence of an
  irreducible aperiodic Metropolis–Hastings chain (GAPS 104.31).
* `CKSD.ae_tendsto_sampleAverage_metropolis`: the ergodic theorem for such a chain, via the
  Poisson equation `CKSD.exists_sub_mulVec_eq_of_offDiag_pos` and the general
  `CKSD.ae_tendsto_sampleAverage_of_sub_mulVec_eq` (GAPS 104.31).

The central limit theorem for finite-state chains is in `CKSD.Bayes.MonteCarlo.MarkovChainCLT`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

section Metropolis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The Metropolis–Hastings acceptance probability is at most one. -/
theorem metropolisAcceptance_le_one (π : ι → ℝ) (q : Matrix ι ι ℝ) (x y : ι) :
    metropolisAcceptance π q x y ≤ 1 := by
  rw [metropolisAcceptance_def]
  split_ifs
  exacts [le_rfl, min_le_left _ _]

omit [Fintype ι] [DecidableEq ι] in
/-- The Metropolis–Hastings acceptance probability is nonnegative for nonnegative weights and
proposals. -/
theorem metropolisAcceptance_nonneg {π : ι → ℝ} {q : Matrix ι ι ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hq : ∀ x y, 0 ≤ q x y) (x y : ι) : 0 ≤ metropolisAcceptance π q x y := by
  rw [metropolisAcceptance_def]
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one
      (div_nonneg (mul_nonneg (hπ y) (hq y x)) (mul_nonneg (hπ x) (hq x y)))

/-- Each row of the Metropolis–Hastings matrix sums to one, for arbitrary `π` and `q`, because
the diagonal carries the rejected mass. -/
theorem sum_metropolisTransition (π : ι → ℝ) (q : Matrix ι ι ℝ) (x : ι) :
    ∑ y, metropolisTransition π q x y = 1 := by
  simp [metropolisTransition_apply, Finset.sum_add_distrib]

/-- GAPS 104.22: for nonnegative target weights and a row-stochastic proposal, the
Metropolis–Hastings matrix is row stochastic. -/
theorem metropolisTransition_mem_rowStochastic {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hπ : ∀ x, 0 ≤ π x) (hq : q ∈ Matrix.rowStochastic ℝ ι) :
    metropolisTransition π q ∈ Matrix.rowStochastic ℝ ι := by
  have hq0 (x y : ι) : 0 ≤ q x y := Matrix.nonneg_of_mem_rowStochastic hq
  refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun x y ↦ ?_, sum_metropolisTransition π q⟩
  have hrow : ∑ z, q x z * metropolisAcceptance π q x z ≤ 1 :=
    calc _ ≤ ∑ z, q x z := Finset.sum_le_sum fun z _ ↦
          mul_le_of_le_one_right (hq0 x z) (metropolisAcceptance_le_one π q x z)
      _ = 1 := Matrix.sum_row_of_mem_rowStochastic hq x
  rw [metropolisTransition_apply]
  refine add_nonneg (mul_nonneg (hq0 x y) (metropolisAcceptance_nonneg hπ hq0 x y)) ?_
  split_ifs
  · exact sub_nonneg.mpr hrow
  · exact le_rfl

/-- GAPS 104.22: detailed balance `π(x) P(x, y) = π(y) P(y, x)` of the Metropolis–Hastings matrix
`P`, for nonnegative target weights (not necessarily normalized) and nonnegative proposals. -/
theorem metropolisTransition_detailedBalance {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hπ : ∀ x, 0 ≤ π x) (hq : ∀ x y, 0 ≤ q x y) (x y : ι) :
    π x * metropolisTransition π q x y = π y * metropolisTransition π q y x := by
  have hflux (x y : ι) :
      π x * q x y * metropolisAcceptance π q x y = min (π x * q x y) (π y * q y x) := by
    rw [metropolisAcceptance_def]
    split_ifs with hzero
    · simp [hzero, min_eq_left (mul_nonneg (hπ y) (hq y x))]
    · rw [mul_min_of_nonneg _ _ (mul_nonneg (hπ x) (hq x y)), mul_one]
      congr 1
      field_simp [(mul_ne_zero_iff.mp hzero).1, (mul_ne_zero_iff.mp hzero).2]
  by_cases hxy : x = y
  · subst y; rfl
  · simp only [metropolisTransition_apply, hxy, Ne.symm hxy, ↓reduceIte, add_zero]
    simp only [← mul_assoc, hflux, min_comm]

/-- GAPS 104.22: the target weights are invariant for the Metropolis–Hastings matrix,
`∑ₓ π(x) P(x, y) = π(y)`. -/
theorem sum_mul_metropolisTransition {π : ι → ℝ} {q : Matrix ι ι ℝ}
    (hπ : ∀ x, 0 ≤ π x) (hq : ∀ x y, 0 ≤ q x y) (y : ι) :
    ∑ x, π x * metropolisTransition π q x y = π y := by
  simp_rw [metropolisTransition_detailedBalance hπ hq _ y]
  rw [← Finset.mul_sum, sum_metropolisTransition, mul_one]

/-- GAPS 104.32: uniform convergence rate of the independence sampler. For a positive target
`π` and a positive proposal density `g` with `π ≤ M g`, every row of the `n`-step
Metropolis–Hastings matrix with proposal `q(x, y) = g(y)` is within `(1 - 1 / M)ⁿ` of `π`,
uniformly over events. The condition `π ≤ M g` forces `M ≥ 1`. -/
theorem abs_sum_independenceSampler_pow_sub_le (π g : ι → ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hg : ∀ x, 0 < g x) (hg1 : ∑ x, g x = 1)
    (M : ℝ) (hdom : ∀ x, π x ≤ M * g x)
    (n : ℕ) (x : ι) (A : Finset ι) :
    |(∑ y ∈ A, (metropolisTransition π (fun _ y ↦ g y) ^ n) x y) - ∑ y ∈ A, π y| ≤
      (1 - 1 / M) ^ n := by
  set q : Matrix ι ι ℝ := fun _ y ↦ g y with hq
  have hM : 1 ≤ M := by
    calc (1 : ℝ) = ∑ x, π x := hπ1.symm
      _ ≤ ∑ x, M * g x := Finset.sum_le_sum fun x _ ↦ hdom x
      _ = M := by rw [← Finset.mul_sum, hg1, mul_one]
  have hMpos : 0 < M := by linarith
  have hgy (y : ι) : 1 / M * π y ≤ g y := by
    rw [one_div_mul_eq_div, div_le_iff₀ hMpos]
    linarith [hdom y]
  -- The independence sampler is minorized by `π / M` in every row.
  have hmin (x y : ι) : 1 / M * π y ≤ metropolisTransition π q x y := by
    have hrej : 0 ≤ 1 - ∑ z, q x z * metropolisAcceptance π q x z := by
      have : ∑ z, q x z * metropolisAcceptance π q x z ≤ ∑ z, q x z :=
        Finset.sum_le_sum fun z _ ↦
          mul_le_of_le_one_right (hg z).le (metropolisAcceptance_le_one π q x z)
      simp only [hq, hg1] at this ⊢
      linarith
    by_cases hxy : x = y
    · subst hxy
      have h1 : metropolisAcceptance π q x x = 1 := by
        have hne : π x * q x x ≠ 0 := (mul_pos (hπ x) (hg x)).ne'
        simp [metropolisAcceptance_def, hne]
      simp only [metropolisTransition_apply, ↓reduceIte, h1, mul_one]
      have : q x x = g x := rfl
      linarith [hgy x]
    · simp only [metropolisTransition_apply, hxy, ↓reduceIte, add_zero]
      rw [metropolisAcceptance_def]
      have hne : π x * q x y ≠ 0 := (mul_pos (hπ x) (hg y)).ne'
      simp only [hne, ↓reduceIte]
      rw [mul_min_of_nonneg _ _ (hg y).le, mul_one]
      refine le_min (hgy y) ?_
      have hrw : q x y * (π y * q y x / (π x * q x y)) = π y * (g x / π x) := by
        simp only [hq]
        field_simp [(hπ x).ne', (hg y).ne']
      rw [hrw, mul_comm (1 / M)]
      refine mul_le_mul_of_nonneg_left ?_ (hπ y).le
      rw [div_le_div_iff₀ hMpos (hπ x)]
      linarith [hdom x]
  exact abs_sum_pow_sub_le_of_minorization π _ (fun x ↦ (hπ x).le) hπ1
    (sum_metropolisTransition π q)
    (sum_mul_metropolisTransition (fun x ↦ (hπ x).le) fun _ y ↦ (hg y).le) _ hmin A n x

/-- GAPS 104.31, finite-state form of total-variation convergence of Metropolis–Hastings.
The target is positive; irreducibility is taken in the sufficient form `q x y > 0` for `x ≠ y`,
and aperiodicity in the sufficient form that some proposed move has acceptance below one.
The convergence is uniform over events, which is total-variation convergence. -/
theorem eventually_abs_metropolisTransition_pow_sub_le (π : ι → ℝ)
    (q : Matrix (ι) (ι) ℝ) (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : q ∈ Matrix.rowStochastic ℝ ι)
    (hirr : ∀ x y, x ≠ y → 0 < q x y)
    (hap : ∃ x y, 0 < q x y ∧ metropolisAcceptance π q x y < 1) (x : ι) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ A : Finset (ι),
      |∑ y ∈ A, (metropolisTransition π q ^ n) x y - ∑ y ∈ A, π y| ≤ ε := by
  set P := metropolisTransition π q with hPdef
  have hq1 : ∀ x, ∑ y, q x y = 1 := Matrix.sum_row_of_mem_rowStochastic hq
  have hPmem : P ∈ Matrix.rowStochastic ℝ ι :=
    metropolisTransition_mem_rowStochastic (fun x ↦ (hπ x).le) hq
  have hP0 (u z : ι) : 0 ≤ P u z := Matrix.nonneg_of_mem_rowStochastic hPmem
  have hPst := sum_mul_metropolisTransition (fun x ↦ (hπ x).le)
    (fun x y ↦ Matrix.nonneg_of_mem_rowStochastic hq (i := x) (j := y))
  replace hq (u z : ι) : 0 ≤ q u z := Matrix.nonneg_of_mem_rowStochastic hq
  obtain ⟨x₀, y₀, hqy₀, hacc₀⟩ := hap
  have hacc_le := metropolisAcceptance_le_one π q
  have hacc_pos (u z : ι) : 0 < metropolisAcceptance π q u z := by
    rw [metropolisAcceptance_def]
    split_ifs with h0
    · exact one_pos
    · have hqz : 0 < q u z := lt_of_le_of_ne (hq u z) fun h ↦ h0 (by rw [← h, mul_zero])
      have hzu : 0 < q z u := by
        by_cases hzu : z = u
        · subst hzu; exact hqz
        · exact hirr z u hzu
      exact lt_min one_pos (div_pos (mul_pos (hπ z) hzu) (mul_pos (hπ u) hqz))
  -- Off-diagonal moves are possible, and the state `x₀` rejects with positive probability.
  have hoff (u z : ι) (h : u ≠ z) : 0 < P u z := by
    simp only [hPdef, metropolisTransition_apply, h, ↓reduceIte, add_zero]
    exact mul_pos (hirr u z h) (hacc_pos u z)
  have hdiag : 0 < P x₀ x₀ := by
    have hlt : ∑ z, q x₀ z * metropolisAcceptance π q x₀ z < ∑ z, q x₀ z := by
      apply Finset.sum_lt_sum
      · intro z _
        simpa using mul_le_mul_of_nonneg_left (hacc_le x₀ z) (hq x₀ z)
      · exact ⟨y₀, Finset.mem_univ _, by
          simpa using mul_lt_mul_of_pos_left hacc₀ hqy₀⟩
    simp only [hPdef, metropolisTransition_apply, ↓reduceIte]
    rw [hq1] at hlt
    have := mul_nonneg (hq x₀ x₀) (hacc_pos x₀ x₀).le
    linarith
  have hto (u : ι) : 0 < P u x₀ := by
    by_cases h : u = x₀
    · subst h; exact hdiag
    · exact hoff u x₀ h
  have hfrom (z : ι) : 0 < P x₀ z := by
    by_cases h : x₀ = z
    · subst h; exact hdiag
    · exact hoff x₀ z h
  -- Three steps through `x₀` give a strictly positive matrix.
  set K := P ^ 3 with hKdef
  have hKpos (u z : ι) : 0 < K u z := pow_three_apply_pos_of_pos_through hP0 hto hfrom u z
  have hK0 (u z : ι) : 0 ≤ K u z := Matrix.nonneg_of_mem_rowStochastic (pow_mem hPmem 3)
  have hK1 : ∀ u, ∑ z, K u z = 1 := Matrix.sum_row_of_mem_rowStochastic (pow_mem hPmem 3)
  have hKst := sum_mul_pow_eq_of_stationary hPst 3
  set m := (Finset.univ : Finset (ι × ι)).inf' ⟨(x, x), Finset.mem_univ _⟩
    (fun z ↦ K z.1 z.2) with hm
  have hm_pos : 0 < m := (Finset.lt_inf'_iff _).2 fun z _ ↦ hKpos z.1 z.2
  have hm_le (u z : ι) : m ≤ K u z :=
    Finset.inf'_le (fun z : ι × ι ↦ K z.1 z.2) (Finset.mem_univ (u, z))
  have hm_one : m ≤ 1 := by
    have := Finset.single_le_sum (f := fun z ↦ K x z) (fun z _ ↦ hK0 x z)
      (Finset.mem_univ x)
    have h1 : ∑ z, K x z = 1 := hK1 x
    linarith [hm_le x x]
  have hπle (y : ι) : π y ≤ 1 := hπ1 ▸ Finset.single_le_sum (f := π)
    (fun z _ ↦ (hπ z).le) (Finset.mem_univ y)
  have hmin (u z : ι) : m * π z ≤ K u z :=
    (mul_le_of_le_one_right hm_pos.le (hπle z)).trans (hm_le u z)
  have hK3 (k : ℕ) (u : ι) (A : Finset (ι)) :
      |∑ y ∈ A, (K ^ k) u y - ∑ y ∈ A, π y| ≤ (1 - m) ^ k :=
    abs_sum_pow_sub_le_of_minorization π K (fun z ↦ (hπ z).le) hπ1 hK1 hKst m hmin A k u
  -- Remaining steps average the errors of `K ^ k` with stochastic weights.
  have hbound (n : ℕ) (A : Finset (ι)) :
      |∑ y ∈ A, (P ^ n) x y - ∑ y ∈ A, π y| ≤ (1 - m) ^ (n / 3) := by
    have hR0 (u z : ι) : 0 ≤ (P ^ (n % 3)) u z :=
      Matrix.nonneg_of_mem_rowStochastic (pow_mem hPmem (n % 3))
    have hR1 : ∀ u, ∑ z, (P ^ (n % 3)) u z = 1 :=
      Matrix.sum_row_of_mem_rowStochastic (pow_mem hPmem (n % 3))
    have hsplit : P ^ n = P ^ (n % 3) * K ^ (n / 3) := by
      rw [hKdef, ← pow_mul, ← pow_add, Nat.mod_add_div]
    have hrw : ∑ y ∈ A, (P ^ n) x y - ∑ y ∈ A, π y =
        ∑ z, (P ^ (n % 3)) x z * (∑ y ∈ A, (K ^ (n / 3)) z y - ∑ y ∈ A, π y) := by
      simp_rw [hsplit, Matrix.mul_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hR1, one_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hrw]
    calc
      _ ≤ ∑ z, (P ^ (n % 3)) x z * |∑ y ∈ A, (K ^ (n / 3)) z y - ∑ y ∈ A, π y| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun z _ ↦ by rw [abs_mul, abs_of_nonneg (hR0 x z)]
      _ ≤ ∑ z, (P ^ (n % 3)) x z * (1 - m) ^ (n / 3) :=
        Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (hK3 _ z A) (hR0 x z)
      _ = (1 - m) ^ (n / 3) := by rw [← Finset.sum_mul, hR1, one_mul]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - m < 1)
  filter_upwards [eventually_ge_atTop (3 * k₀)] with n hn A
  have hk : k₀ ≤ n / 3 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  calc
    _ ≤ (1 - m) ^ (n / 3) := hbound n A
    _ ≤ (1 - m) ^ k₀ := pow_le_pow_of_le_one (by linarith) (by linarith) hk
    _ ≤ ε := hk₀.le

/-- Off-diagonal entries of the Metropolis transition are positive when the target is positive
and the proposal is positive off the diagonal. -/
theorem metropolisTransition_pos_of_ne (π : ι → ℝ)
    (q : Matrix (ι) (ι) ℝ) (hπ : ∀ x, 0 < π x)
    (hirr : ∀ x y, x ≠ y → 0 < q x y) (x y : ι) (hxy : x ≠ y) :
    0 < metropolisTransition π q x y := by
  have hacc : 0 < metropolisAcceptance π q x y := by
    rw [metropolisAcceptance_def]
    split_ifs with h0
    · exact one_pos
    · exact lt_min one_pos (div_pos (mul_pos (hπ y) (hirr y x (Ne.symm hxy)))
        (mul_pos (hπ x) (hirr x y hxy)))
  simp only [metropolisTransition_apply, hxy, ↓reduceIte, add_zero]
  exact mul_pos (hirr x y hxy) hacc

/-- GAPS 104.31, finite-state ergodic theorem for Metropolis–Hastings from an arbitrary initial
law `ν` (a point mass `ν = 1_{x₀}` gives a fixed initial state). The chain is specified by its
finite-dimensional path probabilities; irreducibility is taken in the sufficient form `q x y > 0`
for `x ≠ y`. On a finite space every function is `π`-integrable. -/
theorem ae_tendsto_sampleAverage_metropolis {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (π : ι → ℝ)
    (q : Matrix (ι) (ι) ℝ) (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : q ∈ Matrix.rowStochastic ℝ ι)
    (hirr : ∀ x y, x ≠ y → 0 < q x y)
    (X : ℕ → Ω → ι) (hX : ∀ n, Measurable (X n)) (ν : ι → ℝ)
    (hlaw : ∀ n : ℕ, ∀ path : ℕ → ι,
      μ.real {ω | ∀ i ≤ n, X i ω = path i} = ν (path 0) *
        ∏ i ∈ Finset.range n, metropolisTransition π q (path i) (path (i + 1)))
    (h : ι → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ sampleAverage (fun i ω ↦ h (X i ω)) n ω) atTop
      (𝓝 (∑ x, π x * h x)) := by
  set P := metropolisTransition π q with hPdef
  have hPmem : P ∈ Matrix.rowStochastic ℝ ι :=
    metropolisTransition_mem_rowStochastic (fun x ↦ (hπ x).le) hq
  have hP0 (x y : ι) : 0 ≤ P x y := Matrix.nonneg_of_mem_rowStochastic hPmem
  have hP1 : ∀ x, ∑ y, P x y = 1 := sum_metropolisTransition π q
  have hPst := sum_mul_metropolisTransition (fun x ↦ (hπ x).le)
    (fun x y ↦ Matrix.nonneg_of_mem_rowStochastic hq (i := x) (j := y))
  have hoff : ∀ x y, x ≠ y → 0 < P x y := metropolisTransition_pos_of_ne π q hπ hirr
  have hstep : HasTransitionMatrix μ P X := .of_measureReal_eq_prod ν hlaw
  set m := ∑ x, π x * h x with hm
  set g : ι → ℝ := fun x ↦ h x - m with hg
  have hgc : ∑ x, π x * g x = 0 := by
    simp only [hg, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul, hm,
      sub_self]
  obtain ⟨u, hu⟩ := exists_sub_mulVec_eq_of_offDiag_pos π P hπ hπ1 hPmem hPst hoff g hgc
  exact ae_tendsto_sampleAverage_of_sub_mulVec_eq μ P hP0 hP1 X hX hstep h m u hu

end Metropolis

end CKSD
