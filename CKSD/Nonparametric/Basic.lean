module

public import CKSD.Asymptotics.Basic
public import Statlib.Divergence.TotalVariation.Event
public import Statlib.Divergence.TotalVariation.Integral
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Basic notions of nonparametric and high-dimensional statistics

This file collects the definitions shared by the files on Section 103 (nonparametric
statistics, shape constraints, high-dimensional and sparse estimation).

## Main definitions

* `CKSD.totalVariationDistance`: the total variation distance `sup_A |P(A) - Q(A)|` in the
  statistical normalization, which is half of Mathlib's `MeasureTheory.tvDist`.
* `CKSD.kolmogorovSmirnovStatistic`: `sup_t |F_n(t) - F(t)|`, the supremum taken over rational
  points.
* `CKSD.finiteKernelDensityEstimator`, `CKSD.kernelDensityEstimator`: the one-dimensional kernel
  density estimator `(n h)⁻¹ ∑ᵢ K((t - Xᵢ) / h)` of a finite sample and of the first `n`
  observations of a sequence.
* `CKSD.restrictedL1Norm`, `CKSD.sparsity`, `CKSD.bestSparseL1Error`: coordinate `ℓ¹` norms
  on a set of coordinates, the number of nonzero coordinates, and the `ℓ¹` error of the best
  `s`-sparse approximation.
* `CKSD.HasRestrictedIsometry`: the restricted isometry property of order `s` with constant `δ`.
* `CKSD.benjaminiHochbergCount`: the number of rejections of the Benjamini–Hochberg procedure.

## Main results

* `CKSD.abs_measureReal_sub_le_totalVariationDistance`: every event discrepancy is bounded by
  the total variation distance.
* `CKSD.tvDist_eq_two_mul_totalVariationDistance`: for probability measures, Mathlib's
  `tvDist` is twice `totalVariationDistance` (via Statlib's `etvDist_eq_two_mul_iSup_sub`).
* `CKSD.abs_integral_sub_integral_le_mul_totalVariationDistance`: expectations of a function
  with values in `[0, c]` under two probability measures differ by at most `c` times their
  total variation distance (via Statlib's `integral_sub_integral_le_tvDist`).
* `CKSD.klFun_le_sq_sub_one`: the Kullback–Leibler function is dominated by the `χ²`
  integrand on `[0, ∞)`, the pointwise step of the bound `KL ≤ χ²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- Discrete measurable structure for finite permutations. -/
scoped instance rankMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Total variation distance in the statistical convention, `sup_A |P(A) - Q(A)|` over
measurable events `A`. For probability measures it is `tvDist P Q / 2`
(`CKSD.tvDist_eq_two_mul_totalVariationDistance`). -/
def totalVariationDistance {X : Type*} [MeasurableSpace X] (P Q : Measure X) : ℝ :=
  sSup {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |P.real A - Q.real A|}

/-- For finite measures, every measurable event difference is bounded by statistical total
variation. -/
theorem abs_measureReal_sub_le_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (A : Set X) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ totalVariationDistance P Q := by
  apply le_csSup (show BddAbove {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ?_)
    (show |P.real A - Q.real A| ∈ {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ⟨A, hA, rfl⟩)
  refine ⟨P.real univ + Q.real univ, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  apply abs_le.mpr
  constructor <;> linarith [measureReal_nonneg (μ := P) (s := B),
    measureReal_nonneg (μ := Q) (s := B),
    measureReal_mono (μ := P) (subset_univ B), measureReal_mono (μ := Q) (subset_univ B)]

/-- The statistical total variation distance of finite measures is nonnegative. -/
theorem totalVariationDistance_nonneg {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    0 ≤ totalVariationDistance P Q :=
  (abs_nonneg _).trans (abs_measureReal_sub_le_totalVariationDistance P Q ∅ .empty)

/-- For probability measures, Mathlib's total variation distance `tvDist` (the total variation
norm of `P - Q`) is twice the statistical total variation distance `sup_A |P(A) - Q(A)|`. -/
theorem tvDist_eq_two_mul_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    tvDist P Q = 2 * totalVariationDistance P Q := by
  set S := ⨆ E, ⨆ (_ : MeasurableSet E), P E - Q E with hSdef
  have hSle : S ≤ 1 := iSup₂_le fun E _ ↦ tsub_le_self.trans prob_le_one
  have hStop : S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hSle
  have hT0 := totalVariationDistance_nonneg P Q
  have hS : S = ENNReal.ofReal (totalVariationDistance P Q) := by
    refine le_antisymm (iSup₂_le fun E hE ↦ ?_) ?_
    · rw [← ofReal_measureReal (μ := P) (s := E), ← ofReal_measureReal (μ := Q) (s := E),
        ← ENNReal.ofReal_sub _ measureReal_nonneg]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (abs_measureReal_sub_le_totalVariationDistance P Q E hE))
    · rw [ENNReal.ofReal_le_iff_le_toReal hStop]
      have key : ∀ E, MeasurableSet E → P.real E - Q.real E ≤ S.toReal := fun E hE ↦
        (ENNReal.le_toReal_sub (measure_ne_top Q E)).trans
          (ENNReal.toReal_mono hStop (le_iSup₂ (f := fun E (_ : MeasurableSet E) ↦ P E - Q E)
            E hE))
      refine csSup_le ⟨_, ∅, .empty, rfl⟩ ?_
      rintro r ⟨A, hA, rfl⟩
      refine abs_le.mpr ⟨?_, key A hA⟩
      have := key Aᶜ hA.compl
      rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at this
      linarith
  rw [tvDist, etvDist_eq_two_mul_iSup_sub P Q (by simp), ← hSdef, hS, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hT0]
  simp

/-- A measurable function with values in `[0, c]` has expectations under two probability
measures differing by at most `c` times their total variation distance. The proof applies
Statlib's variational bound `ProbabilityTheory.integral_sub_integral_le_tvDist` to
`± (2 / c • ψ - 1)`. -/
theorem abs_integral_sub_integral_le_mul_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {ψ : X → ℝ}
    {c : ℝ} (hψ : Measurable ψ) (h0 : ∀ x, 0 ≤ ψ x) (hc : ∀ x, ψ x ≤ c) :
    |∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂| ≤ c * totalVariationDistance P₁ P₂ := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure P₁
  have hc0 : 0 ≤ c := (h0 x₀).trans (hc x₀)
  have htv := (tvDist_eq_two_mul_totalVariationDistance P₁ P₂).le
  rcases hc0.eq_or_lt with rfl | hcpos
  · have : ψ = fun _ ↦ 0 := funext fun x ↦ le_antisymm (hc x) (h0 x)
    simp [this]
  have hint : ∀ P : Measure X, [IsProbabilityMeasure P] → Integrable ψ P := fun P _ ↦
    Integrable.of_bound hψ.aestronglyMeasurable c (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hc x)
  set f : X → ℝ := fun x ↦ 2 / c * ψ x - 1
  have hf : ∀ x, |f x| ≤ 1 := fun x ↦ by
    have h1 := h0 x; have h2 := hc x
    rw [abs_le]; constructor
    · simp only [f]; have : 0 ≤ 2 / c * ψ x := by positivity
      linarith
    · simp only [f]; have : 2 / c * ψ x ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]; linarith
      linarith
  have hfi : ∀ P : Measure X, [IsProbabilityMeasure P] →
      ∫ x, f x ∂P = 2 / c * ∫ x, ψ x ∂P - 1 := fun P _ ↦ by
    simp only [f]
    rw [integral_sub ((hint P).const_mul _) (integrable_const _), integral_const_mul]
    simp
  have h1 := integral_sub_integral_le_tvDist (μ := P₁) (ν := P₂) (f := f)
    (by fun_prop) (ae_of_all _ hf)
  have h2 := integral_sub_integral_le_tvDist (μ := P₁) (ν := P₂) (f := fun x ↦ - f x)
    (by fun_prop) (ae_of_all _ fun x ↦ by rw [abs_neg]; exact hf x)
  rw [integral_neg, integral_neg, hfi, hfi] at h2
  rw [hfi, hfi] at h1
  have key : |2 / c * (∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂)| ≤ 2 * totalVariationDistance P₁ P₂ := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by positivity)] at key
  have : 2 / c * |∫ x, ψ x ∂P₁ - ∫ x, ψ x ∂P₂| * (c / 2) ≤
      2 * totalVariationDistance P₁ P₂ * (c / 2) := by gcongr
  field_simp at this
  linarith

/-- Kolmogorov–Smirnov discrepancy `sup_t |F_n(t) - F(t)|` between the empirical distribution
function of the first `n` observations and the distribution function of `P`; the supremum over
the rationals equals the supremum over the reals by right continuity. -/
def kolmogorovSmirnovStatistic {Ω : Type*} (X : ℕ → Ω → ℝ) (P : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sSup (range fun t : ℚ ↦ |empiricalCDF X n ω t - cdf P t|)

/-- The kernel density estimator `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)` of a finite sample `x` with
kernel `K` and bandwidth `h`. -/
def finiteKernelDensityEstimator {n : ℕ} (K : ℝ → ℝ) (h : ℝ)
    (sample : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, K ((t - sample i) / h)) / ((n : ℝ) * h)

/-- The kernel density estimator at `t` built from the first `n` observations of the sequence
`X` with bandwidth `h n`. -/
def kernelDensityEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  finiteKernelDensityEstimator K (h n) (fun i : Fin n ↦ X i ω) t

/-- The kernel density estimator of a sequence is a sum over the first `n` indices. -/
theorem kernelDensityEstimator_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) :
    kernelDensityEstimator X K h n ω t =
      (∑ i ∈ Finset.range n, K ((t - X i ω) / h n)) / ((n : ℝ) * h n) := by
  rw [kernelDensityEstimator, finiteKernelDensityEstimator,
    Finset.sum_range (fun i ↦ K ((t - X i ω) / h n))]

/-- The coordinate `ℓ¹` norm `∑_{j ∈ S} |x j|` restricted to a set `S` of coordinates. -/
def restrictedL1Norm {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j ∈ S, |x j|

/-- The number of nonzero coordinates of a finite-dimensional vector. -/
def sparsity {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) : ℕ :=
  (Finset.univ.filter fun j ↦ x j ≠ 0).card

/-- The best `s`-term approximation error `σ_s(x)₁ = inf {‖x - y‖₁ : y is s-sparse}`. -/
def bestSparseL1Error {p : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⨅ y : {y : EuclideanSpace ℝ (Fin p) // sparsity y ≤ s}, restrictedL1Norm Finset.univ (x - y.val)

/-- `A` has the restricted isometry property of order `s` with constant `δ`:
`(1 - δ) ‖x‖² ≤ ‖A x‖² ≤ (1 + δ) ‖x‖²` for every `s`-sparse `x`. The constant is a parameter,
not the infimum of admissible constants. -/
def HasRestrictedIsometry {p n : ℕ} (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, sparsity x ≤ s →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- The Benjamini–Hochberg rejection count at level `α`: the largest `k ≤ m` such that at
least `k` of the p-values are at most `k α / m`, with value `0` when no `k ≥ 1` qualifies. -/
def benjaminiHochbergCount {m : ℕ} (p : Fin m → ℝ) (α : ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ ↦
    k ≤ (Finset.univ.filter fun i ↦ p i ≤ (k : ℝ) * α / m).card).sup id

/-- The Kullback–Leibler function is dominated by the `χ²` integrand on `[0, ∞)`:
`klFun x ≤ (x - 1)²` for `x ≥ 0`, from `log x ≤ x - 1`. -/
theorem klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) : InformationTheory.klFun x ≤ (x - 1) ^ 2 := by
  rw [InformationTheory.klFun_apply]
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

end CKSD
