module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.MartingaleCLT.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Independence.Integration


/-!
# The martingale central limit theorem for triangular arrays

## Main results

* `CKSD.tendsto_in_distribution_martingale_array_sum` (GAPS 106.1): the martingale central limit
  theorem for triangular arrays of square-integrable martingale differences under convergence
  of the conditional variances and the conditional Lindeberg condition.

The proof is the characteristic-function argument of B. M. Brown (1971): each row is truncated
at the first index where the summed conditional variances exceed `v + 1`, the bounded case
`CKSD.tendsto_in_distribution_sum_of_sum_cond_var_le` of `CKSD.Asymptotics.MartingaleCLT.Basic`
applies to the truncated rows, and Slutsky's lemma removes the truncation, which only acts on
events of vanishing probability. The application to sample autocorrelations is in
`CKSD.Processes.TimeSeries.SampleAutocorrelation`.

## References

* B. M. Brown, “Martingale central limit theorems,” *Annals of Mathematical Statistics* 42
  (1971), 59–66.
* P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press,
  1980, Section 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Truncating at the first time the partial sums of a nonnegative sequence exceed `B ≥ 0`
keeps the truncated sum at most `B`. -/
private theorem sum_ite_sum_le_mul_le {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) {B : ℝ} (hB : 0 ≤ B)
    (k : ℕ) :
    ∑ j ∈ Finset.range k,
      (if ∑ i ∈ Finset.range (j + 1), σ i ≤ B then (1 : ℝ) else 0) * σ j ≤ B := by
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    by_cases hk : ∑ i ∈ Finset.range (k + 1), σ i ≤ B
    · have h1 : ∀ j ∈ Finset.range (k + 1),
          (if ∑ i ∈ Finset.range (j + 1), σ i ≤ B then (1 : ℝ) else 0) * σ j = σ j := by
        intro j hj
        have hc : ∑ i ∈ Finset.range (j + 1), σ i ≤ B :=
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
            (Finset.mem_range.mp hj)) fun i _ _ ↦ hσ i).trans hk
        simp only [hc, ↓reduceIte, one_mul]
      rw [Finset.sum_congr rfl h1]; exact hk
    · rw [Finset.sum_range_succ]
      simp only [hk, ↓reduceIte, zero_mul, add_zero]
      exact ih

/-- If the partial sums of a nonnegative sequence stay at most `B` up to `k`, the truncation
indicators up to `k` are all equal to one. -/
private theorem sum_range_succ_le_of_sum_le {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) {B : ℝ} {k : ℕ}
    (h : ∑ i ∈ Finset.range k, σ i ≤ B) {j : ℕ} (hj : j < k) :
    ∑ i ∈ Finset.range (j + 1), σ i ≤ B :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj)
    fun i _ _ ↦ hσ i).trans h

/-- GAPS 106.1: triangular-array martingale central limit theorem. For each `n`, let
`X n 0, …, X n (k n - 1)` be square-integrable martingale differences for the filtration `F n`
(`X n j` is `F n (j + 1)`-measurable with `𝔼[X n j | F n j] = 0`). If
`∑_j 𝔼[X_{n,j}² | F n j] → v` and `∑_j 𝔼[X_{n,j}² 1{|X_{n,j}| > ε} | F n j] → 0` in probability
for every `ε > 0`, then `∑_j X_{n,j} ⇒ N(0, v)`. The limit `v` is automatically nonnegative. -/
theorem tendsto_in_distribution_martingale_array_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ha : ∀ n j, Measurable[F n (j + 1)] (X n j))
    (h2 : ∀ n j, MemLp (X n j) 2 μ)
    (h0 : ∀ n j, μ[X n j | F n j] =ᵐ[μ] fun _ ↦ 0) (v : ℝ)
    (hvar : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (k n), μ[(fun ω ↦ X n j ω ^ 2) | F n j] ω) atTop (fun _ ↦ v))
    (hlin : ∀ ε > 0, TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (k n),
        μ[(fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0) | F n j] ω) atTop (fun _ ↦ 0)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ ∑ j ∈ Finset.range (k n), X n j ω) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal v)) := by
  set σ2 : ℕ → ℕ → Ω → ℝ := fun n j ↦ μ[fun ω ↦ X n j ω ^ 2 | F n j] with hσ2
  set ℓ : ℝ → ℕ → ℕ → Ω → ℝ := fun ε n j ↦
    μ[fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0 | F n j] with hℓ
  have hσ0 : ∀ n j, 0 ≤ᵐ[μ] σ2 n j := fun n j ↦
    condExp_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _)
  have hσ0' : ∀ n, ∀ᵐ ω ∂μ, ∀ j, 0 ≤ σ2 n j ω := fun n ↦ ae_all_iff.2 (hσ0 n)
  have hσm : ∀ n j, StronglyMeasurable[F n j] (σ2 n j) := fun n j ↦ stronglyMeasurable_condExp
  have hv0 : 0 ≤ v := nonneg_of_tendsto_in_measure_of_nonneg (fun n ↦ by
    filter_upwards [hσ0' n] with ω hω
    exact Finset.sum_nonneg fun j _ ↦ hω j) hvar
  set B : ℝ := v + 1 with hB
  have hB0 : 0 ≤ B := by linarith
  -- the truncation
  set ind : ℕ → ℕ → Ω → ℝ := fun n j ω ↦
    if ∑ i ∈ Finset.range (j + 1), σ2 n i ω ≤ B then 1 else 0 with hind
  have hindm : ∀ n j, StronglyMeasurable[F n j] (ind n j) := fun n j ↦ by
    have hs : StronglyMeasurable[F n j] fun ω ↦ ∑ i ∈ Finset.range (j + 1), σ2 n i ω :=
      Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
        (hσm n i).mono ((F n).mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    exact (Measurable.ite (measurableSet_le hs.measurable measurable_const) measurable_const
      measurable_const).stronglyMeasurable
  have hind01 : ∀ n j ω, ind n j ω = 0 ∨ ind n j ω = 1 := fun n j ω ↦ by
    simp only [hind]; split_ifs <;> simp
  set X' : ℕ → ℕ → Ω → ℝ := fun n j ω ↦ ind n j ω * X n j ω with hX'
  set σ2' : ℕ → ℕ → Ω → ℝ := fun n j ω ↦ ind n j ω * σ2 n j ω with hσ2'
  set ℓ' : ℝ → ℕ → ℕ → Ω → ℝ := fun ε n j ω ↦ ind n j ω * ℓ ε n j ω with hℓ'
  have htr := fun n j ↦ mul_zero_or_one_martingale_difference ((F n).mono (Nat.le_succ j))
    ((F n).le (j + 1)) (hindm n j) (hind01 n j) (ha n j).stronglyMeasurable (h2 n j) (h0 n j)
  have hX'm : ∀ n j, StronglyMeasurable[F n (j + 1)] (X' n j) := fun n j ↦ (htr n j).1
  have h2' : ∀ n j, MemLp (X' n j) 2 μ := fun n j ↦ (htr n j).2.1
  have h0' : ∀ n j, μ[X' n j | F n j] =ᵐ[μ] 0 := fun n j ↦ (htr n j).2.2.1
  have hσ'm : ∀ n j, StronglyMeasurable[F n j] (σ2' n j) := fun n j ↦
    (hindm n j).mul (hσm n j)
  have hσ' : ∀ n j, σ2' n j =ᵐ[μ] μ[fun ω ↦ X' n j ω ^ 2 | F n j] := fun n j ↦
    (htr n j).2.2.2.1
  have hℓ'eq : ∀ ε > 0, ∀ n j, ℓ' ε n j =ᵐ[μ]
      μ[fun ω ↦ if ε < |X' n j ω| then X' n j ω ^ 2 else 0 | F n j] := fun ε hε n j ↦
    (htr n j).2.2.2.2 ε hε
  have hσ0'' : ∀ n j, 0 ≤ᵐ[μ] σ2' n j := fun n j ↦ (hσ0 n j).mono fun ω hω ↦ by
    rcases hind01 n j ω with h | h <;>
      simp only [hσ2', h, zero_mul, one_mul, Pi.zero_apply, le_refl]
    exact hω
  have hB' : ∀ n, ∀ᵐ ω ∂μ, ∑ j ∈ Finset.range (k n), σ2' n j ω ≤ B := fun n ↦ by
    filter_upwards [hσ0' n] with ω hω
    exact sum_ite_sum_le_mul_le hω hB0 (k n)
  -- the truncated and original row sums agree outside small events
  set V : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), σ2 n j ω with hV
  set V' : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), σ2' n j ω with hV'
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω with hS
  set S' : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), X' n j ω with hS'
  set E : ℕ → Set Ω := fun n ↦ {ω | 1 ≤ dist (V n ω) v} with hE
  have hEt : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.1 hvar) 1 one_pos
  have hoff : ∀ n, ∀ᵐ ω ∂μ, ω ∉ E n → ∀ j < k n, ind n j ω = 1 := fun n ↦ by
    filter_upwards [hσ0' n] with ω hω hωE j hj
    simp only [hE, Set.mem_ofPred_eq, not_le, Real.dist_eq] at hωE
    have hVB : V n ω ≤ B := by linarith [le_abs_self (V n ω - v)]
    have hc := sum_range_succ_le_of_sum_le hω hVB hj
    simp only [hind, hc, ↓reduceIte]
  have hSS' : TendstoInMeasure μ (fun n ω ↦ S n ω - S' n ω) atTop (fun _ ↦ 0) := by
    refine tendsto_in_measure_of_ae_eq_of_measure_tendsto_zero (Z := fun _ _ ↦ 0) E hEt
      (fun n ↦ ?_) (tendsto_in_measure_const_of_tendsto μ (fun _ ↦ 0) tendsto_const_nhds)
    filter_upwards [hoff n] with ω hω hωE
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun j hj ↦ by
      simp only [hX', hω hωE j (Finset.mem_range.mp hj), one_mul]
  have hV'v : TendstoInMeasure μ V' atTop (fun _ ↦ v) := by
    refine tendsto_in_measure_of_ae_eq_of_measure_tendsto_zero E hEt (fun n ↦ ?_) hvar
    filter_upwards [hoff n] with ω hω hωE
    exact Finset.sum_congr rfl fun j hj ↦ by
      simp only [hσ2', hω hωE j (Finset.mem_range.mp hj), one_mul]
  -- the truncated conditional Lindeberg sums tend to zero in mean
  have hindae : ∀ n j, AEStronglyMeasurable (ind n j) μ := fun n j ↦
    ((hindm n j).mono ((F n).le j)).aestronglyMeasurable
  have hind_b : ∀ n j, ∀ᵐ ω ∂μ, ‖ind n j ω‖ ≤ 1 := fun n j ↦ ae_of_all _ fun ω ↦ by
    rcases hind01 n j ω with h | h <;> simp [h]
  have hℓ0 : ∀ ε n j, 0 ≤ᵐ[μ] ℓ ε n j := fun ε n j ↦ condExp_nonneg (ae_of_all _ fun ω ↦ by
    simp only [Pi.zero_apply]; split_ifs <;> positivity)
  have hℓσ : ∀ ε n j, ℓ ε n j ≤ᵐ[μ] σ2 n j := fun ε n j ↦
    condExp_mono (integrable_ite_lt_abs_sq (h2 n j) ε) (h2 n j).integrable_sq
      (ae_of_all _ fun ω ↦ by
        simp only
        split_ifs
        · exact le_rfl
        · positivity)
  have hEL : ∀ ε > 0, Tendsto (fun n ↦ ∫ ω, ∑ j ∈ Finset.range (k n), ℓ' ε n j ω ∂μ) atTop
      (𝓝 0) := by
    intro ε hε
    have hYi : ∀ n, Integrable (fun ω ↦ ∑ j ∈ Finset.range (k n), ℓ' ε n j ω) μ := fun n ↦
      integrable_finsetSum _ fun j _ ↦
        (integrable_condExp (μ := μ) (m := F n j)
          (f := fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0)).bdd_mul (hindae n j)
          (hind_b n j)
    have hLm : ∀ n, Measurable (fun ω ↦ ∑ j ∈ Finset.range (k n), ℓ ε n j ω) := fun n ↦
      Finset.measurable_fun_sum _ fun j _ ↦
        ((stronglyMeasurable_condExp (μ := μ) (m := F n j)
          (f := fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0)).mono ((F n).le j)).measurable
    refine tendsto_integral_of_le_of_tendsto_in_measure (B := B) hYi hLm (fun n ↦ ?_)
      (fun n ↦ ?_) (fun n ↦ ?_) (hlin ε hε)
    · filter_upwards [ae_all_iff.2 (hℓ0 ε n)] with ω hω
      exact Finset.sum_nonneg fun j _ ↦ by
        rcases hind01 n j ω with h | h
        · simp [hℓ', h]
        · simp only [hℓ', h, one_mul]; exact hω j
    · filter_upwards [hB' n, ae_all_iff.2 (hℓσ ε n), ae_all_iff.2 (hℓ0 ε n)] with ω hω h1 h0
      refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) hω
      rcases hind01 n j ω with h | h
      · simp [hℓ', hσ2', h]
      · simp only [hℓ', hσ2', h, one_mul]; exact h1 j
    · filter_upwards [ae_all_iff.2 (hℓ0 ε n)] with ω hω
      refine Finset.sum_le_sum fun j _ ↦ ?_
      rcases hind01 n j ω with h | h
      · simp only [hℓ', h, zero_mul]; exact hω j
      · simp [hℓ', h]
  have hS' := tendsto_in_distribution_sum_of_sum_cond_var_le μ F X' σ2' ℓ' k hX'm h2' h0' hσ'm hσ'
    hℓ'eq hσ0'' hv0 hB' hV'v hEL
  exact tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable μ S' S
    (fun n ↦ Finset.measurable_fun_sum _ fun j _ ↦ ((hX'm n j).mono ((F n).le _)).measurable)
    (fun n ↦ Finset.measurable_fun_sum _ fun j _ ↦ (ha n j).mono ((F n).le _) le_rfl) hS' hSS'

end CKSD
