module

public import CKSD.LinearModels.Basic
public import CKSD.Inference.Basic


/-!
# Design-based inference in survey sampling and randomized experiments

A sampling design on a finite population `{0, …, N-1}` is a probability measure on its subsets
(samples), with the discrete measurable structure. Population values are fixed; all randomness
comes from the design. This file proves the classical design-based moment identities.

## Main definitions

* `CKSD.inclusionProb`, `CKSD.jointInclusionProb`: first- and second-order inclusion
  probabilities `πᵢ = P(i ∈ s)` and `πᵢⱼ = P(i, j ∈ s)`.
* `CKSD.horvitzThompson`: the Horvitz–Thompson estimator `∑_{i ∈ s} yᵢ / πᵢ` of the population
  total, and `CKSD.horvitzThompsonVarianceEstimator` its unbiased variance estimator.
* `CKSD.differenceInMeans`: the difference of treated and control means in a completely
  randomized experiment.

## Main results

* `CKSD.integral_horvitz_thompson`, `CKSD.variance_horvitz_thompson`,
  `CKSD.integral_horvitz_thompson_variance_estimator`,
  `CKSD.variance_horvitz_thompson_eq_sen_yates_grundy`: unbiasedness and design variance of the
  Horvitz–Thompson estimator, unbiased variance estimation, and the Sen–Yates–Grundy form for
  fixed-size designs (GAPS 105.72).
* `CKSD.integral_sum_div_simple_random_sample_design`,
  `CKSD.variance_sum_div_simple_random_sample_design`: the sample mean under simple random sampling
  is unbiased with variance `(1 - n/N) S² / n` (finite-population correction, GAPS 105.73).
* `CKSD.sq_sum_div_le_sum_sq_div_of_sum_eq`, `CKSD.sq_sum_div_eq_sum_sq_div_iff`: Neyman
  allocation minimizes `∑ₕ aₕ² / nₕ` subject to `∑ₕ nₕ = n` (GAPS 105.73).
* `CKSD.integral_difference_in_means`, `CKSD.variance_difference_in_means`: Neyman's unbiasedness
  and exact variance `S₁²/n₁ + S₀²/n₀ - S²_{τ}/N` for the difference in means (GAPS 105.46).

The moment identities use Mathlib's indicator and finite-sum integrals and its second-moment
formula for the variance; the Neyman lower bound is Mathlib's `Finset.sq_sum_div_le_sum_sq_div`.

## References

* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, J. Amer. Statist. Assoc. 47 (1952).
* W. G. Cochran, *Sampling Techniques*, 3rd ed., Wiley, 1977.
* J. Neyman, *On the application of probability theory to agricultural experiments* (1923),
  translated in Statist. Sci. 5 (1990).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common finite-sample measurable structure.
attribute [local instance] finiteSampleMeasurableSpace

/-- Every real statistic on the finite sample space has finite moments under a finite design. -/
private theorem mem_lp_sample {N : ℕ} (P : Measure (Finset (Fin N))) [IsFiniteMeasure P]
    (f : Finset (Fin N) → ℝ) (p : ℝ≥0∞) : MemLp f p P := by
  exact eLpNorm_lt_top_of_finite (measurable_of_countable f).aestronglyMeasurable

/-- The mean of a sum over a random sample is the sum of the summands weighted by their
first-order inclusion probabilities. -/
theorem integral_sum_mem_eq_sum_measure_real {N : ℕ} (P : Measure (Finset (Fin N)))
    [IsFiniteMeasure P]
    (b : Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, b i ∂P) = ∑ i, P.real {s | i ∈ s} * b i := by
  classical
  have hfun : (fun s : Finset (Fin N) ↦ ∑ i ∈ s, b i) =
      (fun s ↦ ∑ i, if i ∈ s then b i else 0) := by
    funext s
    simp
  rw [hfun, integral_finsetSum _ (fun i _ ↦ (mem_lp_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul] using
    (integral_indicator_const (μ := P) (b i)
      (Set.to_countable {s : Finset (Fin N) | i ∈ s}).measurableSet)

/-- The mean of a double sum over a random sample is the double sum of the summands weighted
by their joint inclusion probabilities. -/
theorem integral_sum_sum_mem_eq_sum_sum_measure_real {N : ℕ} (P : Measure (Finset (Fin N)))
    [IsFiniteMeasure P]
    (b : Fin N → Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, ∑ j ∈ s, b i j ∂P) =
      ∑ i, ∑ j, P.real {s | i ∈ s ∧ j ∈ s} * b i j := by
  classical
  have hfun : (fun s : Finset (Fin N) ↦ ∑ i ∈ s, ∑ j ∈ s, b i j) =
      (fun s ↦ ∑ i, ∑ j, if i ∈ s ∧ j ∈ s then b i j else 0) := by
    funext s
    simp only [ite_and]
    simp
  rw [hfun, integral_finsetSum _ (fun i _ ↦ (mem_lp_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ (mem_lp_sample P _ 1).integrable le_rfl)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul] using
    (integral_indicator_const (μ := P) (b i j)
      (Set.to_countable {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}).measurableSet)

/-- Mean and design variance of the Horvitz–Thompson estimator, with the inclusion
probabilities as local definitions. -/
private theorem horvitz_thompson_aux
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    (∀ i, 0 < pi i) →
    let T := fun s : Finset (Fin N) ↦ ∑ i ∈ s, y i / pi i;
    (∫ s, T s ∂P) = ∑ i, y i ∧
      Var[T; P] = ∑ i, ∑ j, (pij i j - pi i * pi j) * y i * y j / (pi i * pi j) := by
  classical
  dsimp only
  intro hp
  let pi := fun i ↦ P.real {s : Finset (Fin N) | i ∈ s}
  let pij := fun i j ↦ P.real {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}
  have hpi0 : ∀ i, pi i ≠ 0 := fun i ↦ (hp i).ne'
  let T := fun s : Finset (Fin N) ↦ ∑ i ∈ s, y i / pi i
  have hmean : (∫ s, T s ∂P) = ∑ i, y i := by
    rw [integral_sum_mem_eq_sum_measure_real]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_cancel₀ (y i) (hp i).ne'
  refine ⟨hmean, ?_⟩
  rw [ProbabilityTheory.variance_eq_sub (mem_lp_sample P T 2), hmean]
  have hsquare : T ^ 2 =
      (fun s ↦ ∑ i ∈ s, ∑ j ∈ s, y i / pi i * (y j / pi j)) := by
    funext s
    simp only [T, pow_two, Pi.mul_apply, Finset.sum_mul_sum]
  rw [hsquare, integral_sum_sum_mem_eq_sum_sum_measure_real]
  have hpop : (∑ i, y i) ^ 2 = ∑ i, ∑ j, y i * y j := by
    simp only [pow_two, Finset.sum_mul_sum]
  rw [hpop, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change pij i j * (y i / pi i * (y j / pi j)) - y i * y j = _
  change _ = (pij i j - pi i * pi j) * y i * y j / (pi i * pi j)
  field_simp [hpi0 i, hpi0 j]

/-- Unbiasedness of the Horvitz–Thompson variance estimator, with the inclusion probabilities
as local definitions. -/
private theorem horvitz_thompson_variance_estimator_aux
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    (∀ i j, 0 < pij i j) →
    (∫ s, ∑ i ∈ s, ∑ j ∈ s,
      (pij i j - pi i * pi j) / pij i j * y i * y j / (pi i * pi j) ∂P) =
      Var[fun s ↦ ∑ i ∈ s, y i / pi i; P] := by
  classical
  dsimp only
  intro hp
  have hpi : ∀ i, 0 < P.real {s : Finset (Fin N) | i ∈ s} := by
    intro i
    simpa only [and_self] using hp i i
  rw [integral_sum_sum_mem_eq_sum_sum_measure_real, (horvitz_thompson_aux P y hpi).2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  field_simp [(hp i j).ne']

/-- The Sen–Yates–Grundy form of the Horvitz–Thompson variance, with the inclusion
probabilities as local definitions. -/
private theorem sen_yates_grundy_aux
    {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (n : ℕ) (hn : ∀ᵐ s ∂P, s.card = n) (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    (∀ i, 0 < pi i) →
    Var[fun s ↦ ∑ i ∈ s, y i / pi i; P] =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, (pij i j - pi i * pi j) * (y i / pi i - y j / pi j) ^ 2 := by
  classical
  dsimp only
  intro hp
  let pi := fun i ↦ P.real {s : Finset (Fin N) | i ∈ s}
  let pij := fun i j ↦ P.real {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}
  let c := fun i j ↦ pij i j - pi i * pi j
  let w := fun i ↦ y i / pi i
  have htotal : ∑ i, pi i = (n : ℝ) := by
    calc
      _ = ∫ s, ∑ i ∈ s, (1 : ℝ) ∂P := by
        simpa only [mul_one] using (integral_sum_mem_eq_sum_measure_real P (fun _ ↦ (1 : ℝ))).symm
      _ = ∫ _, (n : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hn] with s hs
        simp [hs]
      _ = _ := by simp
  have hrow : ∀ i, ∑ j, pij i j = (n : ℝ) * pi i := by
    intro i
    calc
      _ = ∫ s, ∑ j : Fin N, if i ∈ s ∧ j ∈ s then (1 : ℝ) else 0 ∂P := by
        rw [integral_finsetSum _
          (fun j _ ↦ (mem_lp_sample P _ 1).integrable le_rfl)]
        apply Finset.sum_congr rfl
        intro j _
        simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul, mul_one] using
          (integral_indicator_const (μ := P) (1 : ℝ)
            (Set.to_countable {s : Finset (Fin N) | i ∈ s ∧ j ∈ s}).measurableSet).symm
      _ = ∫ s, if i ∈ s then (n : ℝ) else 0 ∂P := by
        apply integral_congr_ae
        filter_upwards [hn] with s hs
        by_cases hi : i ∈ s <;> simp [hi, hs]
      _ = _ := by
        simpa only [Set.indicator, mem_ofPred_eq, smul_eq_mul, mul_comm] using
          (integral_indicator_const (μ := P) (n : ℝ)
            (Set.to_countable {s : Finset (Fin N) | i ∈ s}).measurableSet)
  have hrow0 : ∀ i, ∑ j, c i j = 0 := by
    intro i
    simp only [c, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, htotal]
    ring
  have hsym : ∀ i j, c i j = c j i := by
    intro i j
    simp only [c, pij, and_comm, mul_comm]
  have hcol0 : ∀ j, ∑ i, c i j = 0 := by
    intro j
    simp_rw [hsym _ j]
    exact hrow0 j
  have hfirst : (∑ i, ∑ j, w i ^ 2 * c i j) = 0 := by
    simp_rw [← Finset.mul_sum, hrow0, mul_zero]
    simp
  have hsecond : (∑ i, ∑ j, w j ^ 2 * c i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol0, mul_zero]
    simp
  have hdiff : (∑ i, ∑ j, c i j * (w i - w j) ^ 2) =
      -2 * ∑ i, ∑ j, c i j * w i * w j := by
    have hexpand : ∀ i j, c i j * (w i - w j) ^ 2 =
        w i ^ 2 * c i j + w j ^ 2 * c i j - 2 * (c i j * w i * w j) := by
      intro i j
      ring
    simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    simp_rw [← Finset.mul_sum]
    ring
  have hvar : Var[fun s ↦ ∑ i ∈ s, y i / pi i; P] =
      ∑ i, ∑ j, c i j * w i * w j := by
    rw [(horvitz_thompson_aux P y hp).2]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [c, w, pi, pij, div_eq_mul_inv, mul_inv_rev]
    ring
  change Var[fun s ↦ ∑ i ∈ s, y i / pi i; P] =
    -(1 / 2 : ℝ) * ∑ i, ∑ j, c i j * (w i - w j) ^ 2
  rw [hvar, hdiff]
  ring

/-- Under simple random sampling of `n` units, the probability that the sample contains a given
set `B` of at most `n` units is `C(N - |B|, n - |B|) / C(N, n)`. -/
theorem simple_random_sample_design_real_superset {N n : ℕ} (B : Finset (Fin N))
    (hB : B.card ≤ n) :
    (simpleRandomSampleDesign N n).real {s | B ⊆ s} =
      (Nat.choose (N - B.card) (n - B.card) : ℝ) / Nat.choose N n := by
  have hset : ({s : Finset (Fin N) | B ⊆ s} ∩ {s | s.card = n}) =
      ↑((Finset.univ.powersetCard n).filter (B ⊆ ·)) := by
    ext s; simp [and_comm]
  have hmeas : MeasurableSet {s : Finset (Fin N) | s.card = n} :=
    (Set.to_countable _).measurableSet
  simp only [simpleRandomSampleDesign, measureReal_def, smul_apply,
    Measure.restrict_apply' hmeas, hset, Measure.count_apply_finset, smul_eq_mul]
  rw [Finset.card_filter_powersetCard_subset B Finset.univ n (Finset.subset_univ B) hB,
    Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv, mul_comm]

/-- Simple random sampling of `n ≤ N` units is a probability measure. -/
theorem is_probability_measure_simple_random_sample_design {N n : ℕ} (h : n ≤ N) :
    IsProbabilityMeasure (simpleRandomSampleDesign N n) := by
  constructor
  have hset : {s : Finset (Fin N) | s.card = n} =
      ((Finset.univ : Finset (Fin N)).powersetCard n : Set (Finset (Fin N))) := by
    ext s; simp
  have hC : (Nat.choose N n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  simp only [simpleRandomSampleDesign, smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, hset, Measure.count_apply_finset, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hC (ENNReal.natCast_ne_top _)

/-- Under simple random sampling, the probability that the sample contains `B` is the
proportion of `n`-subsets containing `B`. -/
theorem simple_random_sample_design_real_superset_eq_card {N n : ℕ} (B : Finset (Fin N)) :
    (simpleRandomSampleDesign N n).real {s | B ⊆ s} =
      (((Finset.univ.powersetCard n).filter (B ⊆ ·)).card : ℝ) / Nat.choose N n := by
  have hset : ({s : Finset (Fin N) | B ⊆ s} ∩ {s | s.card = n}) =
      ↑((Finset.univ.powersetCard n).filter (B ⊆ ·)) := by
    ext s; simp [and_comm]
  have hmeas : MeasurableSet {s : Finset (Fin N) | s.card = n} :=
    (Set.to_countable _).measurableSet
  simp only [simpleRandomSampleDesign, measureReal_def, smul_apply,
    Measure.restrict_apply' hmeas, hset, Measure.count_apply_finset, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv, mul_comm]

/-- First-order inclusion probabilities of simple random sampling. -/
theorem simple_random_sample_design_real_mem {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (i : Fin N) :
    (simpleRandomSampleDesign N n).real {s | i ∈ s} = n / N := by
  have := simple_random_sample_design_real_superset (N := N) (n := n) {i} (by simpa using hn)
  simp only [Finset.singleton_subset_iff, Finset.card_singleton] at this
  rw [this]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq M k
  have hC : (Nat.choose (M + 1) (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hnN).ne'
  simp only [Nat.add_sub_cancel]
  rw [div_eq_div_iff hC (by positivity)]
  have h' : ((M + 1 : ℕ) : ℝ) * (Nat.choose M k) = (Nat.choose (M + 1) (k + 1)) * (k + 1 : ℕ) := by
    exact_mod_cast h
  push_cast at h' ⊢
  linarith

/-- Second-order inclusion probabilities of simple random sampling for distinct units. -/
theorem simple_random_sample_design_real_mem_mem {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : n ≤ N) {i j : Fin N} (hij : i ≠ j) :
    (simpleRandomSampleDesign N n).real {s | i ∈ s ∧ j ∈ s} =
      n * (n - 1) / (N * (N - 1)) := by
  have hset : {s : Finset (Fin N) | i ∈ s ∧ j ∈ s} = {s | {i, j} ⊆ s} := by
    ext s; simp [Finset.insert_subset_iff]
  have hcard : ({i, j} : Finset (Fin N)).card = 2 := Finset.card_pair hij
  rw [hset]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [simple_random_sample_design_real_superset_eq_card]
    have : (Finset.univ.powersetCard 1).filter (({i, j} : Finset (Fin N)) ⊆ ·) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_powersetCard_univ, Finset.notMem_empty,
        iff_false, not_and]
      intro hs hsub
      have := Finset.card_le_card hsub
      omega
    simp [this]
  · rw [simple_random_sample_design_real_superset {i, j} (by omega), hcard]
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h₁ := Nat.add_one_mul_choose_eq (M + 1) (k + 1)
    have h₂ := Nat.add_one_mul_choose_eq M k
    have hC : (Nat.choose (M + 2) (k + 2) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hnN).ne'
    simp only [Nat.add_sub_cancel]
    rw [div_eq_div_iff hC (by push_cast; nlinarith)]
    have h₁' : ((M + 2 : ℕ) : ℝ) * (Nat.choose (M + 1) (k + 1)) =
        (Nat.choose (M + 2) (k + 2)) * (k + 2 : ℕ) := by exact_mod_cast h₁
    have h₂' : ((M + 1 : ℕ) : ℝ) * (Nat.choose M k) =
        (Nat.choose (M + 1) (k + 1)) * (k + 1 : ℕ) := by exact_mod_cast h₂
    push_cast at h₁' h₂' ⊢
    linear_combination (↑k + 1 : ℝ) * h₁' + ((M : ℝ) + 2) * h₂'

/-- The finite-population variance as a difference of sums. -/
theorem population_variance_eq_sum_sq {N : ℕ} (hN : 1 ≤ N) (y : Fin N → ℝ) :
    populationVariance y = ((∑ i, y i ^ 2) - (∑ i, y i) ^ 2 / N) / (N - 1) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold populationVariance populationMean
  rw [Nat.cast_sub hN, Nat.cast_one]
  congr 1
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- A double sum with one coefficient on the diagonal and another off it. -/
private theorem sum_sum_ite_mul_mul {N : ℕ} (d e : ℝ) (w : Fin N → ℝ) :
    (∑ i, ∑ j, (if i = j then d else e) * w i * w j) =
      (d - e) * ∑ i, w i ^ 2 + e * (∑ i, w i) ^ 2 := by
  have h : ∀ i j, (if i = j then d else e) * w i * w j =
      e * (w i * w j) + if i = j then (d - e) * w i ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij; ring
    · ring
  have hsq : (∑ i, ∑ j, e * (w i * w j)) = e * (∑ i, w i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hsq, ← Finset.mul_sum]
  ring

/-- Mean and design variance of a sample total under simple random sampling. -/
private theorem simple_random_sample_design_sum_aux {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : n ≤ N) (w : Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, w i ∂simpleRandomSampleDesign N n) = n / N * ∑ i, w i ∧
      Var[fun s ↦ ∑ i ∈ s, w i; simpleRandomSampleDesign N n] =
        n * (N - n) / N * populationVariance w := by
  have := is_probability_measure_simple_random_sample_design hnN
  set P := simpleRandomSampleDesign N n
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpi : ∀ i, P.real {s | i ∈ s} = n / N := simple_random_sample_design_real_mem hn hnN
  have hpos : ∀ i, 0 < P.real {s | i ∈ s} := fun i ↦ by
    rw [hpi]; exact div_pos (by positivity) (by positivity)
  have hHT := horvitz_thompson_aux P (fun i ↦ n / N * w i) hpos
  have hT : (fun s : Finset (Fin N) ↦ ∑ i ∈ s, (n / N * w i) / P.real {s | i ∈ s}) =
      fun s ↦ ∑ i ∈ s, w i := by
    funext s
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hpi]
    field_simp
  simp only [hT] at hHT
  refine ⟨by rw [hHT.1, Finset.mul_sum], ?_⟩
  rw [hHT.2]
  have hpij : ∀ i j, P.real {s | i ∈ s ∧ j ∈ s} =
      if i = j then (n / N : ℝ) else n * (n - 1) / (N * (N - 1)) := by
    intro i j
    split_ifs with hij
    · subst hij; simpa using hpi i
    · exact simple_random_sample_design_real_mem_mem hN hn hnN hij
  have hterm : ∀ i j, (P.real {s | i ∈ s ∧ j ∈ s} - P.real {s | i ∈ s} * P.real {s | j ∈ s}) *
      (n / N * w i) * (n / N * w j) / (P.real {s | i ∈ s} * P.real {s | j ∈ s}) =
      (if i = j then (n / N - (n / N) ^ 2 : ℝ) else n * (n - 1) / (N * (N - 1)) - (n / N) ^ 2) *
        w i * w j := by
    intro i j
    rw [hpij, hpi, hpi]
    split_ifs <;> field_simp
  simp_rw [hterm]
  rw [sum_sum_ite_mul_mul, population_variance_eq_sum_sq (by omega)]
  field_simp
  ring

/-- Mean and design variance of the sample mean under simple random sampling. -/
private theorem simple_random_sample_mean_aux
    {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (y : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y i) / n;
    (∫ s, T s ∂simpleRandomSampleDesign N n) = populationMean y ∧
      Var[T; simpleRandomSampleDesign N n] = (1 - (n : ℝ) / N) * populationVariance y / n := by
  intro T
  have hT : T = fun s ↦ ∑ i ∈ s, y i / n := funext fun s ↦ Finset.sum_div _ _ _
  obtain ⟨h1, h2⟩ := simple_random_sample_design_sum_aux hN hn hnN (fun i ↦ y i / n)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [hT, h1, h2, population_variance_eq_sum_sq (by omega), population_variance_eq_sum_sq (by omega)]
  simp only [div_pow, ← Finset.sum_div, populationMean]
  refine ⟨by field_simp, ?_⟩
  field_simp

/-- Mean and design variance of the difference in means of a completely randomized
experiment. -/
private theorem difference_in_means_aux {N : ℕ} (n₁ n₀ : ℕ) (hn : n₁ + n₀ = N)
    (h₁ : 0 < n₁) (h₀ : 0 < n₀) (y₁ y₀ : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y₁ i) / n₁ - (∑ i ∈ sᶜ, y₀ i) / n₀;
    (∫ s, T s ∂simpleRandomSampleDesign N n₁) = populationMean (y₁ - y₀) ∧
      Var[T; simpleRandomSampleDesign N n₁] =
        populationVariance y₁ / n₁ + populationVariance y₀ / n₀ -
          populationVariance (y₁ - y₀) / N := by
  intro T
  have hnN : n₁ ≤ N := by omega
  have := is_probability_measure_simple_random_sample_design hnN
  let w := fun i ↦ y₁ i / n₁ + y₀ i / n₀
  let c := (∑ i, y₀ i) / n₀
  have hT : T = fun s ↦ (∑ i ∈ s, w i) - c := by
    funext s
    simp only [T, w, c, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [← Finset.sum_compl_add_sum s y₀]
    ring
  obtain ⟨hm, hv⟩ := simple_random_sample_design_sum_aux (by omega) h₁ hnN w
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn₁ : (n₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hn₀ : (n₀ : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
  have hNr : (N : ℝ) = n₁ + n₀ := by exact_mod_cast hn.symm
  have hint : Integrable (fun s : Finset (Fin N) ↦ ∑ i ∈ s, w i)
      (simpleRandomSampleDesign N n₁) :=
    (mem_lp_sample _ _ 1).integrable le_rfl
  constructor
  · rw [hT, integral_sub hint (integrable_const c), hm, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
    simp only [w, c, populationMean, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div]
    rw [hNr]
    field_simp
    ring
  · rw [hT, ProbabilityTheory.variance_sub_const (measurable_of_countable _).aestronglyMeasurable,
      hv]
    rw [population_variance_eq_sum_sq (by omega), population_variance_eq_sum_sq (by omega),
      population_variance_eq_sum_sq (by omega), population_variance_eq_sum_sq (by omega)]
    have e1 : (∑ i, w i ^ 2) = (∑ i, y₁ i ^ 2) / n₁ ^ 2 + (∑ i, y₀ i ^ 2) / n₀ ^ 2 +
        2 * (∑ i, y₁ i * y₀ i) / (n₁ * n₀) := by
      have h : ∀ i, w i ^ 2 = y₁ i ^ 2 / n₁ ^ 2 + y₀ i ^ 2 / n₀ ^ 2 +
          2 * (y₁ i * y₀ i) / (n₁ * n₀) := by
        intro i
        simp only [w]
        field_simp
        ring
      simp_rw [h, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    have e2 : (∑ i, (y₁ - y₀) i ^ 2) = (∑ i, y₁ i ^ 2) + (∑ i, y₀ i ^ 2) -
        2 * (∑ i, y₁ i * y₀ i) := by
      have h : ∀ i, (y₁ - y₀) i ^ 2 = y₁ i ^ 2 + y₀ i ^ 2 - 2 * (y₁ i * y₀ i) := by
        intro i
        simp only [Pi.sub_apply]
        ring
      simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e3 : (∑ i, w i) = (∑ i, y₁ i) / n₁ + (∑ i, y₀ i) / n₀ := by
      simp only [w, Finset.sum_add_distrib, ← Finset.sum_div]
    have e4 : (∑ i, (y₁ - y₀) i) = (∑ i, y₁ i) - (∑ i, y₀ i) := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [e1, e2, e3, e4, hNr]
    have hN1 : (n₁ : ℝ) + n₀ - 1 ≠ 0 := by
      have : (1 : ℝ) ≤ n₁ := by exact_mod_cast h₁
      have : (1 : ℝ) ≤ n₀ := by exact_mod_cast h₀
      linarith
    have hN0' : (n₁ : ℝ) + n₀ ≠ 0 := by rw [← hNr]; exact hN0
    field_simp
    ring

/-- The Neyman allocation bound and its equality case, with a positive sample size. -/
private theorem neyman_allocation_aux {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (n : ℝ) (hn : 0 < n) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hxsum : ∑ i, x i = n) :
    (∑ i, a i) ^ 2 / n ≤ ∑ i, a i ^ 2 / x i ∧
      ((∑ i, a i) ^ 2 / n = ∑ i, a i ^ 2 / x i ↔
        ∀ i, x i = n * a i / ∑ j, a j) := by
  classical
  let S := ∑ i, a i
  have hn0 : n ≠ 0 := hn.ne'
  have hx0 : ∀ i, x i ≠ 0 := fun i ↦ (hx i).ne'
  have hS : 0 < S := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hxsum
      linarith
    · exact Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have hS0 : S ≠ 0 := hS.ne'
  let q := fun i ↦ (a i - (S / n) * x i) ^ 2 / x i
  have hq : ∀ i, 0 ≤ q i := fun i ↦ div_nonneg (sq_nonneg _) (hx i).le
  have hid : (∑ i, q i) = (∑ i, a i ^ 2 / x i) - S ^ 2 / n := by
    have hterm : ∀ i, q i = a i ^ 2 / x i - (2 * S / n) * a i +
        (S / n) ^ 2 * x i := by
      intro i
      dsimp [q]
      field_simp [hn0, hx0 i]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    change (∑ i, a i ^ 2 / x i) - (2 * S / n) * S + (S / n) ^ 2 *
      (∑ i, x i) = _
    rw [hxsum]
    field_simp
    ring
  have hbound : S ^ 2 / n ≤ ∑ i, a i ^ 2 / x i := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hq i)
    rw [hid] at this
    linarith
  refine ⟨hbound, ?_⟩
  constructor
  · intro heq i
    have hz : ∑ j, q j = 0 := by rw [hid, ← heq]; ring
    have hqi : q i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hq j)).mp hz i (Finset.mem_univ i)
    have hi : a i - (S / n) * x i = 0 := by
      have : (a i - (S / n) * x i) ^ 2 = 0 :=
        (div_eq_zero_iff.mp hqi).resolve_right (hx0 i)
      exact sq_eq_zero_iff.mp this
    dsimp [S] at hS0 ⊢
    apply (eq_div_iff hS0).mpr
    have hi' : a i * n - S * x i = 0 := by
      have := (div_eq_zero_iff.mp (show (a i * n - S * x i) / n = 0 by
        convert hi using 1; field_simp)).resolve_right hn0
      exact this
    dsimp [S] at hi'
    nlinarith
  · intro heq
    have hz : ∑ i, q i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      dsimp [q]
      rw [heq i]
      change (a i - (S / n) * (n * a i / S)) ^ 2 / _ = 0
      have : a i - (S / n) * (n * a i / S) = 0 := by
        field_simp
        ring
      rw [this]
      simp
    rw [hid] at hz
    linarith


/-! ### The Horvitz–Thompson estimator -/

/-- The first-order inclusion probability `πᵢ = P(i ∈ s)` of unit `i` under the design `P`. -/
def inclusionProb {N : ℕ} (P : Measure (Finset (Fin N))) (i : Fin N) : ℝ :=
  P.real {s | i ∈ s}

/-- The second-order inclusion probability `πᵢⱼ = P(i ∈ s, j ∈ s)` under the design `P`. -/
def jointInclusionProb {N : ℕ} (P : Measure (Finset (Fin N))) (i j : Fin N) : ℝ :=
  P.real {s | i ∈ s ∧ j ∈ s}

/-- The Horvitz–Thompson estimator `∑_{i ∈ s} yᵢ / πᵢ` of the population total. -/
def horvitzThompson {N : ℕ} (P : Measure (Finset (Fin N))) (y : Fin N → ℝ)
    (s : Finset (Fin N)) : ℝ :=
  ∑ i ∈ s, y i / inclusionProb P i

/-- The Horvitz–Thompson estimator of the design variance of `horvitzThompson P y`:
`∑_{i, j ∈ s} (πᵢⱼ - πᵢ πⱼ) / πᵢⱼ · yᵢ yⱼ / (πᵢ πⱼ)`. -/
def horvitzThompsonVarianceEstimator {N : ℕ} (P : Measure (Finset (Fin N))) (y : Fin N → ℝ)
    (s : Finset (Fin N)) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, (jointInclusionProb P i j - inclusionProb P i * inclusionProb P j) /
    jointInclusionProb P i j * y i * y j / (inclusionProb P i * inclusionProb P j)

/-- GAPS 105.72, Horvitz–Thompson unbiasedness: when every unit has positive inclusion
probability, the Horvitz–Thompson estimator is design-unbiased for the population total. -/
theorem integral_horvitz_thompson {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) (hp : ∀ i, 0 < inclusionProb P i) :
    (∫ s, horvitzThompson P y s ∂P) = ∑ i, y i :=
  (horvitz_thompson_aux P y hp).1

/-- GAPS 105.72, exact design variance of the Horvitz–Thompson estimator:
`Var(T) = ∑ᵢ ∑ⱼ (πᵢⱼ - πᵢ πⱼ) yᵢ yⱼ / (πᵢ πⱼ)`. -/
theorem variance_horvitz_thompson {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) (hp : ∀ i, 0 < inclusionProb P i) :
    Var[horvitzThompson P y; P] = ∑ i, ∑ j,
      (jointInclusionProb P i j - inclusionProb P i * inclusionProb P j) * y i * y j /
        (inclusionProb P i * inclusionProb P j) :=
  (horvitz_thompson_aux P y hp).2

/-- GAPS 105.72, unbiased estimation of the Horvitz–Thompson design variance: when all joint
inclusion probabilities are positive, `horvitzThompsonVarianceEstimator` is design-unbiased
for the variance of the Horvitz–Thompson estimator. -/
theorem integral_horvitz_thompson_variance_estimator {N : ℕ} (P : Measure (Finset (Fin N)))
    [IsProbabilityMeasure P] (y : Fin N → ℝ) (hp : ∀ i j, 0 < jointInclusionProb P i j) :
    (∫ s, horvitzThompsonVarianceEstimator P y s ∂P) = Var[horvitzThompson P y; P] :=
  horvitz_thompson_variance_estimator_aux P y hp

/-- GAPS 105.72, Sen–Yates–Grundy identity for a fixed-size sampling design: if almost every
sample has `n` units, then
`Var(T) = -(1/2) ∑ᵢ ∑ⱼ (πᵢⱼ - πᵢ πⱼ) (yᵢ / πᵢ - yⱼ / πⱼ)²`. -/
theorem variance_horvitz_thompson_eq_sen_yates_grundy {N : ℕ} (P : Measure (Finset (Fin N)))
    [IsProbabilityMeasure P] (n : ℕ) (hn : ∀ᵐ s ∂P, s.card = n) (y : Fin N → ℝ)
    (hp : ∀ i, 0 < inclusionProb P i) :
    Var[horvitzThompson P y; P] = -(1 / 2 : ℝ) * ∑ i, ∑ j,
      (jointInclusionProb P i j - inclusionProb P i * inclusionProb P j) *
        (y i / inclusionProb P i - y j / inclusionProb P j) ^ 2 :=
  sen_yates_grundy_aux P n hn y hp

/-! ### Simple random sampling -/

/-- The mean of a sample total under simple random sampling of `1 ≤ n ≤ N` units is
`(n / N) ∑ᵢ wᵢ`. -/
theorem integral_sum_simple_random_sample_design {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : n ≤ N) (w : Fin N → ℝ) :
    (∫ s, ∑ i ∈ s, w i ∂simpleRandomSampleDesign N n) = n / N * ∑ i, w i :=
  (simple_random_sample_design_sum_aux hN hn hnN w).1

/-- The design variance of a sample total under simple random sampling of `1 ≤ n ≤ N` units is
`n (N - n) / N · S²`, with `S²` the population variance. -/
theorem variance_sum_simple_random_sample_design {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : n ≤ N) (w : Fin N → ℝ) :
    Var[fun s ↦ ∑ i ∈ s, w i; simpleRandomSampleDesign N n] =
      n * (N - n) / N * populationVariance w :=
  (simple_random_sample_design_sum_aux hN hn hnN w).2

/-- GAPS 105.73, finite-population correction for a simple random sample mean: the sample mean
is design-unbiased for the population mean. -/
theorem integral_sum_div_simple_random_sample_design {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n)
    (hnN : n ≤ N) (y : Fin N → ℝ) :
    (∫ s, (∑ i ∈ s, y i) / n ∂simpleRandomSampleDesign N n) = populationMean y :=
  (simple_random_sample_mean_aux hN n hn hnN y).1

/-- GAPS 105.73, finite-population correction for a simple random sample mean: the design
variance of the sample mean is `(1 - n / N) S² / n`. -/
theorem variance_sum_div_simple_random_sample_design {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n)
    (hnN : n ≤ N) (y : Fin N → ℝ) :
    Var[fun s ↦ (∑ i ∈ s, y i) / n; simpleRandomSampleDesign N n] =
      (1 - (n : ℝ) / N) * populationVariance y / n :=
  (simple_random_sample_mean_aux hN n hn hnN y).2

/-! ### Neyman allocation -/

/-- GAPS 105.73, the continuous Neyman allocation optimization, lower bound: for positive
allocations `xₕ` with `∑ₕ xₕ = n`, `(∑ₕ aₕ)² / n ≤ ∑ₕ aₕ² / xₕ`. This is Mathlib's
`Finset.sq_sum_div_le_sum_sq_div`. -/
theorem sq_sum_div_le_sum_sq_div_of_sum_eq {ι : Type*} [Fintype ι] (a : ι → ℝ) {n : ℝ}
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) (hxsum : ∑ i, x i = n) :
    (∑ i, a i) ^ 2 / n ≤ ∑ i, a i ^ 2 / x i :=
  hxsum ▸ Finset.sq_sum_div_le_sum_sq_div _ a fun i _ ↦ hx i

/-- GAPS 105.73, the continuous Neyman allocation optimization, equality case: for positive
`aₕ` and positive allocations `xₕ` with `∑ₕ xₕ = n`, the bound
`(∑ₕ aₕ)² / n ≤ ∑ₕ aₕ² / xₕ` is attained exactly at the Neyman allocation
`xₕ = n aₕ / ∑ₖ aₖ`. -/
theorem sq_sum_div_eq_sum_sq_div_iff {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {n : ℝ} (x : ι → ℝ) (hx : ∀ i, 0 < x i) (hxsum : ∑ i, x i = n) :
    (∑ i, a i) ^ 2 / n = ∑ i, a i ^ 2 / x i ↔ ∀ i, x i = n * a i / ∑ j, a j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have hn : 0 < n := hxsum ▸ Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty
    exact (neyman_allocation_aux a ha n hn x hx hxsum).2

/-! ### Completely randomized experiments -/

/-- The difference in means `(∑_{i ∈ s} y₁ᵢ) / n₁ - (∑_{i ∉ s} y₀ᵢ) / n₀` of a completely
randomized experiment in which the units of `s` are treated. -/
def differenceInMeans {N : ℕ} (n₁ n₀ : ℕ) (y₁ y₀ : Fin N → ℝ) (s : Finset (Fin N)) : ℝ :=
  (∑ i ∈ s, y₁ i) / n₁ - (∑ i ∈ sᶜ, y₀ i) / n₀

/-- GAPS 105.46, Neyman's unbiasedness in a completely randomized experiment: when `n₁ > 0`
units drawn by simple random sampling are treated and the `n₀ > 0` others are controls, the
difference in means is unbiased for the average treatment effect. -/
theorem integral_difference_in_means {N : ℕ} (n₁ n₀ : ℕ) (hn : n₁ + n₀ = N) (h₁ : 0 < n₁)
    (h₀ : 0 < n₀) (y₁ y₀ : Fin N → ℝ) :
    (∫ s, differenceInMeans n₁ n₀ y₁ y₀ s ∂simpleRandomSampleDesign N n₁) =
      populationMean (y₁ - y₀) :=
  (difference_in_means_aux n₁ n₀ hn h₁ h₀ y₁ y₀).1

/-- GAPS 105.46, Neyman's exact design variance in a completely randomized experiment:
`Var = S₁² / n₁ + S₀² / n₀ - S²_{y₁ - y₀} / N`, with the population variances of the potential
outcomes and of the unit-level effects. -/
theorem variance_difference_in_means {N : ℕ} (n₁ n₀ : ℕ) (hn : n₁ + n₀ = N) (h₁ : 0 < n₁)
    (h₀ : 0 < n₀) (y₁ y₀ : Fin N → ℝ) :
    Var[differenceInMeans n₁ n₀ y₁ y₀; simpleRandomSampleDesign N n₁] =
      populationVariance y₁ / n₁ + populationVariance y₀ / n₀ -
        populationVariance (y₁ - y₀) / N :=
  (difference_in_means_aux n₁ n₀ hn h₁ h₀ y₁ y₀).2

end CKSD
