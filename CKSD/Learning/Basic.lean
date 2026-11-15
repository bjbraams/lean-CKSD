module

public import CKSD.Nonparametric.Basic
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Basic objects of statistical learning

This file collects the definitions shared by several files of the Learning section (Section 107
of the catalogue).

## Main definitions

* `CKSD.empiricalRademacherComplexityOfSet`: the empirical Rademacher complexity
  `𝔼_σ sup_{f ∈ F} n⁻¹ ∑ᵢ σᵢ f(xᵢ)` of a class `F` of real functions at a sample `x`, the
  expectation being over a uniform sign vector `σ ∈ {±1}ⁿ`.
* `CKSD.empiricalRademacherComplexity`: the same quantity for an indexed class `h ↦ f h`.
* `CKSD.classificationRisk`: the binary classification risk of a classifier `g` for a feature
  law `P` and regression function `η(x) = P(Y = 1 | X = x)`.
* `CKSD.hedgeWeight`: the exponential-weights (Hedge) probabilities.
* `CKSD.IsDifferentiallyPrivate`: `(ε, δ)`-differential privacy of a Markov kernel for a given
  neighbouring relation.
* `CKSD.armPlayCount`, `CKSD.armSampleAverage`: play counts and prefix reward averages of a
  multi-armed bandit.

## Main results

* `CKSD.sum_mul_log_sub_log_nonneg`: Gibbs' inequality for finite sums, from Mathlib's
  `InformationTheory.klFun_nonneg`.

## Conventions

The supremum in the Rademacher complexity is the real `sSup`, which is `0` for a set that is
empty or not bounded above. All theorems about it concern classes for which the suprema are
finite and attained or bounded (finite classes, or classes with bounded values), so the
convention never decides a statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical Rademacher complexity of a class `F` of real functions at the sample `x`:
the average over the `2ⁿ` sign vectors `σ` of `sup_{f ∈ F} n⁻¹ ∑ᵢ σᵢ f(xᵢ)`, with `true`
coding `+1`. The supremum is the real `sSup` (so it is `0` for an empty class or a class whose
signed averages are unbounded above). -/
def empiricalRademacherComplexityOfSet {X : Type*} (n : ℕ) (F : Set (X → ℝ))
    (x : Fin n → X) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ∑ s : Fin n → Bool,
    sSup ((fun f ↦ (∑ i, (if s i then (1 : ℝ) else -1) * f (x i)) / n) '' F)

/-- Empirical Rademacher complexity of the indexed class `{f h | h ∈ H}` at the sample `x`; it is
`empiricalRademacherComplexityOfSet` of the range of `f`. -/
def empiricalRademacherComplexity
    {H X : Type*} (n : ℕ) (f : H → X → ℝ) (x : Fin n → X) : ℝ :=
  empiricalRademacherComplexityOfSet n (range f) x

/-- The empirical Rademacher complexity of an indexed class as an average of suprema over the
index set. -/
theorem empiricalRademacherComplexity_eq {H X : Type*} (n : ℕ) (f : H → X → ℝ)
    (x : Fin n → X) :
    empiricalRademacherComplexity n f x = (2 : ℝ)⁻¹ ^ n * ∑ σ : Fin n → Bool,
      sSup (range fun h ↦ (∑ i, (if σ i then (1 : ℝ) else -1) * f h (x i)) / n) := by
  simp only [empiricalRademacherComplexity, empiricalRademacherComplexityOfSet, ← range_comp]
  rfl

/-- Binary classification risk `𝔼[g(X) ≠ Y]` of the classifier `g` (with `true` coding the
label `1`), for the feature law `P` and the regression function `η(x) = P(Y = 1 | X = x)`:
`∫ (1 - η) 1{g = 1} + η 1{g = 0} dP`. -/
def classificationRisk {X : Type*} [MeasurableSpace X] (P : Measure X)
    (η : X → ℝ) (g : X → Bool) : ℝ :=
  ∫ x, if g x then 1 - η x else η x ∂P

/-- Exponential-weights (Hedge) probabilities after `t` rounds with learning rate `η`:
`pₜ(i) ∝ exp(-η ∑_{s<t} ℓₛ(i))`. -/
def hedgeWeight {K : ℕ} (loss : ℕ → Fin K → ℝ) (eta : ℝ) (t : ℕ) (i : Fin K) : ℝ :=
  Real.exp (-eta * ∑ s ∈ Finset.range t, loss s i) /
    (∑ j, Real.exp (-eta * ∑ s ∈ Finset.range t, loss s j))

/-- `(ε, δ)`-differential privacy of a kernel `M` for the neighbouring relation `R`:
`M d A ≤ e^ε M d' A + δ` for all neighbouring `d, d'` and measurable events `A`. Local
privacy is the case of the total relation. -/
def IsDifferentiallyPrivate {D Y : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    (R : D → D → Prop) (epsilon delta : ℝ) (M : Kernel D Y) : Prop :=
  ∀ d d', R d d' → ∀ A : Set Y, MeasurableSet A →
    M d A ≤ ENNReal.ofReal (Real.exp epsilon) * M d' A + ENNReal.ofReal delta

/-- Number of plays of arm `i` before time `t` by the arm process `A`. -/
def armPlayCount {Ω : Type*} {K : ℕ} (A : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter fun j ↦ A j ω = i).card

/-- Average `n⁻¹ ∑_{j<n} R i j` of the first `n` rewards of arm `i` in the reward table `R`
(equal to `0` for `n = 0`). -/
def armSampleAverage {Ω : Type*} {K : ℕ} (R : Fin K → ℕ → Ω → ℝ)
    (i : Fin K) (n : ℕ) (ω : Ω) : ℝ := (∑ j ∈ Finset.range n, R i j ω) / n

/-- Gibbs' inequality for finite sums: if `p ≥ 0` and `q > 0` on `S` have equal totals, then
`∑ p (log p - log q) ≥ 0`. Each term is at least `p - q`, since `q · klFun (p / q) ≥ 0`
(Mathlib's `InformationTheory.klFun_nonneg`). -/
theorem sum_mul_log_sub_log_nonneg {ι : Type*} (S : Finset ι) {p q : ι → ℝ}
    (hp : ∀ i ∈ S, 0 ≤ p i) (hq : ∀ i ∈ S, 0 < q i) (hpq : ∑ i ∈ S, p i = ∑ i ∈ S, q i) :
    0 ≤ ∑ i ∈ S, p i * (Real.log (p i) - Real.log (q i)) := by
  have h : ∀ i ∈ S, p i - q i ≤ p i * (Real.log (p i) - Real.log (q i)) := by
    intro i hi
    have hq0 := hq i hi
    rcases (hp i hi).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]; linarith
    have hk := mul_nonneg hq0.le
      (InformationTheory.klFun_nonneg (div_nonneg (hp i hi) hq0.le))
    rw [InformationTheory.klFun_apply, Real.log_div hpos.ne' hq0.ne'] at hk
    have e : q i * (p i / q i * (Real.log (p i) - Real.log (q i)) + 1 - p i / q i) =
        p i * (Real.log (p i) - Real.log (q i)) + q i - p i := by
      field_simp
    linarith
  have := Finset.sum_le_sum h
  rwa [Finset.sum_sub_distrib, hpq, sub_self] at this

end CKSD
