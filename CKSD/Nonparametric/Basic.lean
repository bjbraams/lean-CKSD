module

import CKSD.Asymptotics.Basic
import Statlib.Divergence.TotalVariation.Event
import Statlib.Divergence.TotalVariation.Integral
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import CKSD.Inference.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

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
* `CKSD.IsBoundedInProbability.add`, `CKSD.isBoundedInProbability_finsetSum`,
  `CKSD.IsBoundedInProbability.of_abs_le`,
  `CKSD.IsBoundedInProbability.of_abs_le_of_tendstoInMeasure`,
  `CKSD.tendstoInMeasure_finsetSum_zero`: closure properties of boundedness in probability and of
  convergence in probability to zero, for real-valued sequences on a finite measure space.
-/

public section

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

/-- The total variation distance is the supremum of the event differences. -/
theorem totalVariationDistance_def {X : Type*} [MeasurableSpace X] (P Q : Measure X) :
    totalVariationDistance P Q =
      sSup {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |P.real A - Q.real A|} := by
  rw [totalVariationDistance]

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

/-- The finite-sample kernel density estimator is `(n h)⁻¹ ∑ᵢ K((t - xᵢ) / h)`. -/
theorem finiteKernelDensityEstimator_def {n : ℕ} (K : ℝ → ℝ) (h : ℝ) (sample : Fin n → ℝ)
    (t : ℝ) : finiteKernelDensityEstimator K h sample t =
      (∑ i, K ((t - sample i) / h)) / ((n : ℝ) * h) := by
  rw [finiteKernelDensityEstimator]

/-- The kernel density estimator at `t` built from the first `n` observations of the sequence
`X` with bandwidth `h n`. -/
def kernelDensityEstimator {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  finiteKernelDensityEstimator K (h n) (fun i : Fin n ↦ X i ω) t

/-- The kernel density estimator of a sequence is the finite-sample estimator of its first `n`
observations. -/
theorem kernelDensityEstimator_def {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : kernelDensityEstimator X K h n ω t =
      finiteKernelDensityEstimator K (h n) (fun i : Fin n ↦ X i ω) t := by
  rw [kernelDensityEstimator]

/-- The kernel density estimator of a sequence is a sum over the first `n` indices. -/
theorem kernelDensityEstimator_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) :
    kernelDensityEstimator X K h n ω t =
      (∑ i ∈ Finset.range n, K ((t - X i ω) / h n)) / ((n : ℝ) * h n) := by
  rw [kernelDensityEstimator, finiteKernelDensityEstimator_def,
    Finset.sum_range (fun i ↦ K ((t - X i ω) / h n))]

/-- The coordinate `ℓ¹` norm `∑_{j ∈ S} |x j|` restricted to a set `S` of coordinates. -/
def restrictedL1Norm {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j ∈ S, |x j|

/-- The restricted `ℓ¹` norm is the sum of the absolute coordinates in `S`. -/
theorem restrictedL1Norm_def {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x = ∑ j ∈ S, |x j| := by
  rw [restrictedL1Norm]

/-- The restricted `ℓ¹` norm is nonnegative. -/
theorem restrictedL1Norm_nonneg {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) :
    0 ≤ restrictedL1Norm S x := by
  rw [restrictedL1Norm_def]
  exact Finset.sum_nonneg fun j _ ↦ abs_nonneg _

/-- The restricted `ℓ¹` norm is at most the full `ℓ¹` norm. -/
theorem restrictedL1Norm_le_univ {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x ≤ restrictedL1Norm Finset.univ x := by
  rw [restrictedL1Norm_def, restrictedL1Norm_def]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ abs_nonneg _

/-- The number of nonzero coordinates of a finite-dimensional vector. -/
def sparsity {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) : ℕ :=
  (Finset.univ.filter fun j ↦ x j ≠ 0).card

/-- The sparsity is the number of nonzero coordinates. -/
theorem sparsity_def {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) :
    sparsity x = (Finset.univ.filter fun j ↦ x j ≠ 0).card := by
  rw [sparsity]

/-- The best `s`-term approximation error `σ_s(x)₁ = inf {‖x - y‖₁ : y is s-sparse}`. -/
def bestSparseL1Error {p : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⨅ y : {y : EuclideanSpace ℝ (Fin p) // sparsity y ≤ s}, restrictedL1Norm Finset.univ (x - y.val)

/-- The best `s`-term error is the infimum of the `ℓ¹` distances to `s`-sparse vectors. -/
theorem bestSparseL1Error_def {p : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin p)) :
    bestSparseL1Error s x = ⨅ y : {y : EuclideanSpace ℝ (Fin p) // sparsity y ≤ s},
      restrictedL1Norm Finset.univ (x - y.val) := by
  rw [bestSparseL1Error]

/-- `A` has the restricted isometry property of order `s` with constant `δ`:
`(1 - δ) ‖x‖² ≤ ‖A x‖² ≤ (1 + δ) ‖x‖²` for every `s`-sparse `x`. The constant is a parameter,
not the infimum of admissible constants. -/
@[expose] def HasRestrictedIsometry {p n : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, sparsity x ≤ s →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- The Benjamini–Hochberg rejection count at level `α`: the largest `k ≤ m` such that at
least `k` of the p-values are at most `k α / m`, with value `0` when no `k ≥ 1` qualifies. -/
def benjaminiHochbergCount {m : ℕ} (p : Fin m → ℝ) (α : ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ ↦
    k ≤ (Finset.univ.filter fun i ↦ p i ≤ (k : ℝ) * α / m).card).sup id

/-- The Benjamini–Hochberg count is the largest qualifying `k ≤ m`. -/
theorem benjaminiHochbergCount_def {m : ℕ} (p : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount p α = ((Finset.range (m + 1)).filter fun k : ℕ ↦
      k ≤ (Finset.univ.filter fun i ↦ p i ≤ (k : ℝ) * α / m).card).sup id := by
  rw [benjaminiHochbergCount]

/-- The Kullback–Leibler function is dominated by the `χ²` integrand on `[0, ∞)`:
`klFun x ≤ (x - 1)²` for `x ≥ 0`, from `log x ≤ x - 1`. -/
theorem klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) : InformationTheory.klFun x ≤ (x - 1) ^ 2 := by
  rw [InformationTheory.klFun_apply]
  rcases hx.eq_or_lt with rfl | hpos
  · simp
  have := Real.log_le_sub_one_of_pos hpos
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

/-- A weighted average with nonnegative weights summing to one stays within `B` of `y` when
every point carrying positive weight does. -/
theorem abs_sum_mul_sub_le_of_sum_eq_one {ι : Type*} (s : Finset ι) (a g : ι → ℝ) (y B : ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (hsum : ∑ i ∈ s, a i = 1)
    (hg : ∀ i ∈ s, a i ≠ 0 → |g i - y| ≤ B) :
    |∑ i ∈ s, a i * g i - y| ≤ B := by
  have e1 : ∑ i ∈ s, a i * g i - y = ∑ i ∈ s, a i * (g i - y) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [e1]
  calc |∑ i ∈ s, a i * (g i - y)| ≤ ∑ i ∈ s, |a i * (g i - y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, a i * B := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [abs_mul, abs_of_nonneg (ha0 i hi)]
        by_cases hai : a i = 0
        · simp [hai]
        · exact mul_le_mul_of_nonneg_left (hg i hi hai) (ha0 i hi)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A countable sum of nonnegative functions has integral at most `a` when the `i`-th summand
has integral at most `a w i` for weights with `∑ w i ≤ 1`. -/
theorem lintegral_tsum_le_of_le_mul {α ι : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} {F : ι → α → ℝ≥0∞} (hF : ∀ i, AEMeasurable (F i) μ) {a : ℝ≥0∞}
    {w : ι → ℝ≥0∞} (hw : ∑' i, w i ≤ 1) (h : ∀ i, ∫⁻ x, F i x ∂μ ≤ a * w i) :
    ∫⁻ x, ∑' i, F i x ∂μ ≤ a := by
  rw [lintegral_tsum hF]
  calc ∑' i, ∫⁻ x, F i x ∂μ ≤ ∑' i, a * w i := tsum_le_tsum h
    _ = a * ∑' i, w i := ENNReal.tsum_mul_left
    _ ≤ a * 1 := by gcongr
    _ = a := mul_one _

/-- An oracle bound valid for every comparison index passes to the infimum: if
`X ≤ C (B i + c)` for all `i`, with `B i ≥ 0`, `c ≥ 0` and `C > 0`, then
`X ≤ C (inf_i B i + c)`. -/
theorem le_ofReal_mul_iInf_add {ι : Type*} [Nonempty ι] {X : ℝ≥0∞} {C c : ℝ} (hC : 0 < C)
    (hc : 0 ≤ c) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (h : ∀ i, X ≤ ENNReal.ofReal (C * (B i + c))) :
    X ≤ ENNReal.ofReal (C * ((⨅ i, B i) + c)) := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hfin : X ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h i₀)
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  have hr : ∀ i, X.toReal / C - c ≤ B i := by
    intro i
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h i)
    rw [ENNReal.toReal_ofReal (by have := hB i; positivity), ← div_le_iff₀' hC] at this
    linarith
  have := le_ciInf hr
  rw [div_sub' hC.ne', div_le_iff₀ hC] at this
  linarith

/-- A function that agrees on `[a, t]`, for some `a < t`, with an affine function of slope `σ`
has left derivative `σ` at `t`. -/
theorem derivWithin_Iio_eq_of_eq_affine {G : ℝ → ℝ} {a t c σ : ℝ} (hat : a < t)
    (h : ∀ u, a ≤ u → u ≤ t → G u = c + σ * (u - a)) : derivWithin G (Iio t) t = σ := by
  have hL : HasDerivWithinAt (fun u ↦ c + σ * (u - a)) σ (Iio t) t := by
    simpa using ((((hasDerivAt_id t).sub_const a).const_mul σ).const_add c).hasDerivWithinAt
  have hEq : G =ᶠ[𝓝[<] t] (fun u ↦ c + σ * (u - a)) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hat) fun u hu ↦ h u hu.1.le hu.2.le
  exact (hL.congr_of_eventuallyEq hEq (h t hat.le le_rfl)).derivWithin
    (uniqueDiffWithinAt_Iio t)

/-- A point of `(y 0, y k]` lies in one of the cells `(y j, y (j + 1)]`, `j < k`. -/
theorem exists_mem_Ioc_of_grid {k : ℕ} {y : ℕ → ℝ} {t : ℝ} (ht : y 0 < t) (htk : t ≤ y k) :
    ∃ j < k, t ∈ Ioc (y j) (y (j + 1)) := by
  classical
  have hex : ∃ l, t ≤ y l ∧ l ≤ k := ⟨k, htk, le_rfl⟩
  obtain ⟨hl1, hl2⟩ := Nat.find_spec hex
  have hl0 : Nat.find hex ≠ 0 := fun h ↦ by rw [h] at hl1; linarith
  refine ⟨Nat.find hex - 1, by omega, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hl1⟩
  by_contra hc
  push Not at hc
  exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨hc, by omega⟩

/-- The step function with value `s m` on the cell `(y m, y (m + 1)]` of a strictly increasing
grid `y 0 < ⋯ < y k` takes the value `s j` on the cell `(y j, y (j + 1)]`. -/
theorem sum_indicator_Ioc_eq_of_mem {k : ℕ} {y : ℕ → ℝ} (s : ℕ → ℝ)
    (hymono : StrictMonoOn y (Iic k)) {j : ℕ} (hj : j < k) {t : ℝ}
    (ht : t ∈ Ioc (y j) (y (j + 1))) :
    ∑ m ∈ Finset.range k, (Ioc (y m) (y (m + 1))).indicator (fun _ ↦ s m) t = s j := by
  rw [Finset.sum_eq_single j, indicator_of_mem ht]
  · intro m hm hmj
    have hm' := Finset.mem_range.mp hm
    refine indicator_of_notMem (fun hmem ↦ ?_) _
    rcases lt_or_gt_of_ne hmj with h | h
    · linarith [hmem.2, ht.1, hymono.monotoneOn (mem_Iic.mpr (by omega : m + 1 ≤ k))
        (mem_Iic.mpr hj.le) (by omega : m + 1 ≤ j)]
    · linarith [hmem.1, ht.2, hymono.monotoneOn (mem_Iic.mpr (by omega : j + 1 ≤ k))
        (mem_Iic.mpr hm'.le) (by omega : j + 1 ≤ m)]
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

/-- The step function on the cells `(y j, y (j + 1)]` of a monotone grid `y 0 ≤ ⋯ ≤ y k`
vanishes outside `(y 0, y k]`. -/
theorem sum_indicator_Ioc_eq_zero_of_notMem {k : ℕ} {y : ℕ → ℝ} (s : ℕ → ℝ)
    (hymono : MonotoneOn y (Iic k)) {t : ℝ} (ht : t ∉ Ioc (y 0) (y k)) :
    ∑ m ∈ Finset.range k, (Ioc (y m) (y (m + 1))).indicator (fun _ ↦ s m) t = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ indicator_of_notMem (fun hmem ↦ ht ⟨?_, ?_⟩) _
  all_goals have hj' := Finset.mem_range.mp hj
  · exact (hymono (mem_Iic.mpr (Nat.zero_le k)) (mem_Iic.mpr hj'.le) (Nat.zero_le j)).trans_lt
      hmem.1
  · exact hmem.2.trans (hymono (mem_Iic.mpr (by omega)) (mem_Iic.mpr le_rfl) (by omega))

/-- If the ratios `b i / a i` of nonnegative numbers `b i` to positive numbers `a i`, `i < n`,
have sum at most `n`, then `∏ b i ≤ ∏ a i`: this is the arithmetic-geometric mean inequality
for the ratios. -/
theorem prod_le_prod_of_sum_div_le {n : ℕ} {a b : ℕ → ℝ} (ha : ∀ i < n, 0 < a i)
    (hb : ∀ i < n, 0 ≤ b i) (h : ∑ i ∈ Finset.range n, b i / a i ≤ n) :
    ∏ i ∈ Finset.range n, b i ≤ ∏ i ∈ Finset.range n, a i := by
  have hprod0 : 0 ≤ ∏ i ∈ Finset.range n, a i :=
    Finset.prod_nonneg fun i hi ↦ (ha i (Finset.mem_range.mp hi)).le
  by_cases hz : ∃ i < n, b i = 0
  · obtain ⟨i, hi, hbi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hi) hbi]
    exact hprod0
  push Not at hz
  have hpos : ∀ i ∈ Finset.range n, 0 < b i / a i := fun i hi ↦
    div_pos ((hb i (Finset.mem_range.mp hi)).lt_of_ne (hz i (Finset.mem_range.mp hi)).symm)
      (ha i (Finset.mem_range.mp hi))
  have hu : ∏ i ∈ Finset.range n, (b i / a i) ≤ 1 := by
    have hlog : Real.log (∏ i ∈ Finset.range n, (b i / a i)) ≤ 0 := by
      rw [Real.log_prod fun i hi ↦ (hpos i hi).ne']
      calc ∑ i ∈ Finset.range n, Real.log (b i / a i)
          ≤ ∑ i ∈ Finset.range n, (b i / a i - 1) :=
            Finset.sum_le_sum fun i hi ↦ Real.log_le_sub_one_of_pos (hpos i hi)
        _ = ∑ i ∈ Finset.range n, b i / a i - n := by
            rw [Finset.sum_sub_distrib]; simp
        _ ≤ 0 := by linarith
    by_contra hc
    push Not at hc
    exact absurd hlog (not_le.mpr (Real.log_pos hc))
  have hsplit : ∏ i ∈ Finset.range n, b i =
      (∏ i ∈ Finset.range n, a i) * ∏ i ∈ Finset.range n, (b i / a i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    field_simp [(ha i (Finset.mem_range.mp hi)).ne']
  rw [hsplit]
  calc _ ≤ (∏ i ∈ Finset.range n, a i) * 1 := mul_le_mul_of_nonneg_left hu hprod0
    _ = _ := mul_one _

/-- A bias of order `h ^ 2` is negligible at the scale `√(n h)` when `n h ^ 5` stays bounded:
if `b n / h n ^ 2 → 0` and eventually `n * h n ^ 5 ≤ C`, then `√(n * h n) * b n → 0`. -/
theorem tendsto_sqrt_mul_mul_of_tendsto_div_sq {h b : ℕ → ℝ} (hh : ∀ n, 0 < h n) {C : ℝ}
    (hC : ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ^ 5 ≤ C)
    (hb : Tendsto (fun n ↦ b n / h n ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ Real.sqrt ((n : ℝ) * h n) * b n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using (hb.abs.const_mul (Real.sqrt (max C 0))))
  filter_upwards [hC] with n hn
  have hh0' := (hh n).ne'
  have hrh : |Real.sqrt ((n : ℝ) * h n) * h n ^ 2| ≤ Real.sqrt (max C 0) := by
    refine Real.abs_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (by have := hh n; positivity)]
    calc (n : ℝ) * h n * (h n ^ 2) ^ 2 = n * h n ^ 5 := by ring
      _ ≤ max C 0 := hn.trans (le_max_left _ _)
  have : Real.sqrt ((n : ℝ) * h n) * b n =
      Real.sqrt ((n : ℝ) * h n) * h n ^ 2 * (b n / h n ^ 2) := by
    field_simp
  rw [this, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hrh (abs_nonneg _)

section BoundedInProbability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Sums of sequences bounded in probability are bounded in probability. -/
theorem IsBoundedInProbability.add [IsFiniteMeasure μ] {X Y : ℕ → Ω → ℝ}
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
theorem IsBoundedInProbability.of_abs_le {X Y : ℕ → Ω → ℝ} (hX : IsBoundedInProbability μ X)
    (h : ∀ᶠ n in atTop, ∀ ω, |Y n ω| ≤ |X n ω|) [IsFiniteMeasure μ] :
    IsBoundedInProbability μ Y := by
  intro ε hε
  obtain ⟨C, hC, hev⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, h] with n hn hn'
  refine le_trans (measureReal_mono fun ω (hω : C < |Y n ω|) ↦ ?_) hn
  exact (show C < |X n ω| from hω.trans_le (hn' ω))

/-- Finite sums of sequences tending to zero in probability tend to zero in probability. -/
theorem tendstoInMeasure_finsetSum_zero [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    {X : ι → ℕ → Ω → ℝ} (hX : ∀ i ∈ s, TendstoInMeasure μ (X i) atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ s, X i n ω) atTop (fun _ ↦ 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using tendstoInMeasure_const_of_tendsto μ (fun _ ↦ (0 : ℝ)) tendsto_const_nhds
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tendstoInMeasure_add_zero μ _ _ (hX a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

/-- Finite sums of sequences bounded in probability are bounded in probability. -/
theorem isBoundedInProbability_finsetSum [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    {X : ι → ℕ → Ω → ℝ} (hX : ∀ i ∈ s, IsBoundedInProbability μ (X i)) :
    IsBoundedInProbability μ (fun n ω ↦ ∑ i ∈ s, X i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isBoundedInProbability_of_tendstoInMeasure μ _ 0
      (tendstoInMeasure_const_of_tendsto μ (fun _ ↦ (0 : ℝ)) tendsto_const_nhds)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hX a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

/-- If `|Yₙ| ≤ K |Vₙ|` whenever `|Uₙ| < δ`, with `Vₙ` bounded and `Uₙ → 0` in probability, then
`Yₙ` is bounded in probability. -/
theorem IsBoundedInProbability.of_abs_le_of_tendstoInMeasure [IsFiniteMeasure μ]
    {V U Y : ℕ → Ω → ℝ} (hV : IsBoundedInProbability μ V)
    (hU : TendstoInMeasure μ U atTop (fun _ ↦ 0)) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h : ∀ n ω, |U n ω| < δ → |Y n ω| ≤ K * |V n ω|) :
    IsBoundedInProbability μ Y := by
  rw [tendstoInMeasure_iff_measureReal_lt_dist] at hU
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

end BoundedInProbability

end CKSD
