module

public import CKSD.Inference.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Independence.InfinitePi


/-!
# Exponentially consistent tests

Uniformly consistent tests of a simple null against a set of alternatives can be upgraded to
tests whose errors of both kinds decay exponentially in the sample size. The construction splits
the sample into consecutive blocks of a fixed length `k` on which a fixed test has errors at most
`1/4`, and rejects when at least half of the block tests reject. The block tests are independent
under every product law, so Hoeffding's inequality (Mathlib's
`ProbabilityTheory.measure_sum_range_ge_le_of_iIndepFun`) bounds both errors by `exp (-⌊n/k⌋/8)`.

## Main results

* `CKSD.infinite_pi_map_fin_val`: the first `n` coordinates of an i.i.d. sequence have the
  `n`-fold product law.
* `CKSD.i_indep_fun_block_sample`, `CKSD.infinite_pi_map_block_sample`: consecutive blocks of an
  i.i.d. sequence are i.i.d. with the product law on the block.
* `CKSD.exists_exponentially_consistent_tests`: exponentially consistent tests from uniformly
  consistent ones.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

variable {X : Type*} [MeasurableSpace X]

/-- The first `n` coordinates of an i.i.d. sequence with law `P` have the `n`-fold product law. -/
theorem infinite_pi_map_fin_val (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ P).map (fun ω (i : Fin n) ↦ ω i) =
      Measure.pi fun _ : Fin n ↦ P := by
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- The `j`-th block of length `k` of a sequence: the coordinates `j k, …, j k + k - 1`. -/
def blockSample (k j : ℕ) (ω : ℕ → X) : Fin k → X := fun i ↦ ω (j * k + i)

/-- The block map is measurable. -/
@[fun_prop] theorem measurable_block_sample (k j : ℕ) :
    Measurable (blockSample (X := X) k j) :=
  measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _

/-- Each block of length `k` of an i.i.d. sequence has the `k`-fold product law. -/
theorem infinite_pi_map_block_sample (P : Measure X) [IsProbabilityMeasure P] (k j : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ P).map (blockSample k j) = Measure.pi fun _ : Fin k ↦ P := by
  have hinj : Function.Injective fun i : Fin k ↦ j * k + (i : ℕ) :=
    fun a b h ↦ Fin.ext (by simpa using h)
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ P) hinj

/-- The consecutive blocks of length `k` of an i.i.d. sequence are independent. -/
theorem i_indep_fun_block_sample (P : Measure X) [IsProbabilityMeasure P] (k : ℕ) :
    iIndepFun (fun j ↦ blockSample (X := X) k j) (Measure.infinitePi fun _ : ℕ ↦ P) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun j ↦ measurable_block_sample k j)]
  simp_rw [infinite_pi_map_block_sample, ← Measure.infinitePi_eq_pi]
  have hinj : Function.Injective fun p : ℕ × Fin k ↦ p.1 * k + (p.2 : ℕ) := by
    rintro ⟨a, i⟩ ⟨b, l⟩ h
    have hk : 0 < k := Fin.pos i
    simp only at h
    have hdiv : ∀ (c : ℕ) (r : Fin k), (c * k + r) / k = c := fun c r ↦ by
      rw [mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt r.2, add_zero]
    have h1 : a = b := by rw [← hdiv a i, h, hdiv b l]
    subst h1
    simp only [Prod.mk.injEq, true_and]
    exact Fin.ext (by omega)
  have hcomp : (fun ω (j : ℕ) ↦ blockSample (X := X) k j ω) =
      (MeasurableEquiv.curry ℕ (Fin k) X) ∘ (fun ω (p : ℕ × Fin k) ↦ ω (p.1 * k + p.2)) := by
    ext ω j i; rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj hinj]
  exact Measure.infinitePi_map_curry (fun _ _ ↦ P)

/-- Hoeffding's inequality for block statistics: if `g` takes values in an interval of length
one, the centred sum of `g` over the first `m` blocks of length `k` of an i.i.d. sequence exceeds
`m/4` with probability at most `exp (-m/8)`. -/
theorem measure_real_sum_block_sample_ge_le (Q : Measure X) [IsProbabilityMeasure Q] (k m : ℕ)
    {g : (Fin k → X) → ℝ} (hg : Measurable g) {a : ℝ} (hga : ∀ z, g z ∈ Icc a (a + 1)) :
    (Measure.infinitePi fun _ : ℕ ↦ Q).real
      {ω | (m : ℝ) / 4 ≤ ∑ j ∈ Finset.range m,
        (g (blockSample k j ω) - ∫ z, g z ∂(Measure.pi fun _ : Fin k ↦ Q))} ≤
      Real.exp (-(m : ℝ) / 8) := by
  set μ := Measure.infinitePi fun _ : ℕ ↦ Q
  set c := ∫ z, g z ∂(Measure.pi fun _ : Fin k ↦ Q)
  have hmean : ∀ j, μ[fun ω ↦ g (blockSample k j ω)] = c := by
    intro j
    change ∫ ω, g (blockSample k j ω) ∂μ = ∫ z, g z ∂(Measure.pi fun _ : Fin k ↦ Q)
    rw [← infinite_pi_map_block_sample Q k j, integral_map (by fun_prop) hg.aestronglyMeasurable]
  have hind : iIndepFun (fun j ω ↦ g (blockSample k j ω) - c) μ :=
    (i_indep_fun_block_sample Q k).comp (fun _ z ↦ g z - c) (fun _ ↦ hg.sub_const _)
  have hsub : ∀ j < m, HasSubgaussianMGF (fun ω ↦ g (blockSample k j ω) - c)
      ((‖(a + 1) - a‖₊ / 2) ^ 2) μ := by
    intro j _
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω ↦ g (blockSample k j ω))
      (a := a) (b := a + 1) (hg.comp (measurable_block_sample k j)).aemeasurable
      (ae_of_all _ fun ω ↦ hga _)
    rwa [hmean j] at this
  refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind hsub (ε := (m : ℝ) / 4)
    (by positivity)).trans (le_of_eq ?_)
  congr 1
  have h1 : ‖(a + 1) - a‖₊ = 1 := by simp
  rw [h1]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    push_cast
    field_simp
    ring

/-- **Exponentially consistent tests.** If tests `φ n` of `P θ₀` against the alternatives `A`
have type I error tending to zero and type II error tending to zero uniformly on `A`, then there
are tests `ψ n` and `β > 0` whose type I error and uniform type II error are both at most
`exp (1/8) exp (-β n)`. The tests `ψ n` reject when at least half of the block tests reject. -/
theorem exists_exponentially_consistent_tests {Θ : Type*} (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (θ₀ : Θ) (A : Set Θ)
    (φ : ∀ n : ℕ, (Fin n → X) → ℝ) (hφ : ∀ n, IsStatisticalTest (φ n))
    (h0 : Tendsto (fun n : ℕ ↦ ∫ x, φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0))
    (h1 : ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ ∈ A,
      (∫ x, 1 - φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ ε) :
    ∃ β > 0, ∃ ψ : ∀ n : ℕ, (Fin n → X) → ℝ, (∀ n, IsStatisticalTest (ψ n)) ∧ ∀ n : ℕ,
      (∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤
        Real.exp (1 / 8) * Real.exp (-β * n) ∧
      ∀ θ ∈ A, (∫ x, 1 - ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤
        Real.exp (1 / 8) * Real.exp (-β * n) := by
  obtain ⟨k, hk1, hk0, hkA⟩ := ((eventually_ge_atTop 1).and
    ((h0.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (h1 (1 / 4) (by norm_num)))).exists
  have hne : Nonempty X := by
    rcases isEmpty_or_nonempty X with h | h
    · exact absurd (Measure.eq_zero_of_isEmpty (P θ₀)) (IsProbabilityMeasure.ne_zero _)
    · exact h
  let x₀ : X := Classical.arbitrary X
  -- extension of a finite sample to a sequence, and the block statistic
  let ext : ∀ n : ℕ, (Fin n → X) → ℕ → X := fun n x i ↦ if h : i < n then x ⟨i, h⟩ else x₀
  have hext : ∀ n, Measurable (ext n) := fun n ↦ measurable_pi_iff.2 fun i ↦ by
    by_cases h : i < n
    · simp only [ext, h, ↓reduceDIte]; exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]; exact measurable_const
  let S : ℕ → (ℕ → X) → ℝ := fun n ω ↦
    ∑ j ∈ Finset.range (n / k), φ k (blockSample k j ω)
  have hS : ∀ n, Measurable (S n) := fun n ↦
    Finset.measurable_sum _ fun j _ ↦ (hφ k).1.comp (measurable_block_sample k j)
  let E : ℕ → Set (ℕ → X) := fun n ↦ {ω | ((n / k : ℕ) : ℝ) / 2 ≤ S n ω}
  have hE : ∀ n, MeasurableSet (E n) := fun n ↦ measurableSet_le measurable_const (hS n)
  refine ⟨1 / (8 * k), by positivity, fun n x ↦ (E n).indicator 1 (ext n x), fun n ↦ ?_, ?_⟩
  · refine ⟨(measurable_one.indicator (hE n)).comp (hext n), fun x ↦ ?_⟩
    by_cases h : ext n x ∈ E n <;> simp [h]
  intro n
  -- the test depends only on the first `n` coordinates
  have hSext : ∀ ω : ℕ → X, S n (ext n fun i : Fin n ↦ ω i) = S n ω := by
    intro ω
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    congr 1
    funext i
    have hj' : j + 1 ≤ n / k := Finset.mem_range.1 hj
    have hlt : j * k + i < n := by
      have h2 : (j + 1) * k ≤ n / k * k := Nat.mul_le_mul_right k hj'
      have h3 := Nat.div_mul_le_self n k
      have h4 := i.2
      nlinarith
    simp [blockSample, ext, hlt]
  have hlaw : ∀ θ (h : ℝ → ℝ), Measurable h → (∫ x, h ((E n).indicator 1 (ext n x))
      ∂(Measure.pi fun _ : Fin n ↦ P θ)) =
      ∫ ω, h ((E n).indicator 1 ω) ∂(Measure.infinitePi fun _ : ℕ ↦ P θ) := by
    intro θ h hh
    rw [← infinite_pi_map_fin_val (P θ) n,
      integral_map (measurable_pi_iff.2 fun i ↦ measurable_pi_apply _).aemeasurable
        (hh.comp ((measurable_one.indicator (hE n)).comp (hext n))).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [Set.indicator, E, Set.mem_ofPred_eq, hSext, Pi.one_apply]
  set m := n / k with hm
  have hk : 0 < k := hk1
  have hexp : Real.exp (-(m : ℝ) / 8) ≤ Real.exp (1 / 8) * Real.exp (-(1 / (8 * k)) * n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hnat : n ≤ k * (m + 1) := by
      have h1 : k * m + n % k = n := Nat.div_add_mod n k
      have h2 := Nat.mod_lt n hk
      rw [mul_add, mul_one]
      linarith
    have hreal : (n : ℝ) ≤ k * (m + 1) := by exact_mod_cast hnat
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show -(1 / (8 * (k : ℝ))) * n = -(n / k) / 8 by field_simp]
    have : (n : ℝ) / k ≤ m + 1 := by rw [div_le_iff₀ hk']; linarith
    linarith
  have hsum : ∀ (ω : ℕ → X) (a : ℝ),
      ∑ j ∈ Finset.range m, (φ k (blockSample k j ω) - a) = S n ω - m * a := by
    intro ω a
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hint : ∀ θ, Integrable (φ k) (Measure.pi fun _ : Fin k ↦ P θ) := fun θ ↦
    Integrable.of_mem_Icc 0 1 (hφ k).1.aemeasurable (ae_of_all _ (hφ k).2)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  constructor
  · have hl := hlaw θ₀ id measurable_id
    simp only [id] at hl
    show (∫ x, (E n).indicator 1 (ext n x) ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤ _
    rw [hl, integral_indicator_one (hE n)]
    refine le_trans ?_ (le_trans (measure_real_sum_block_sample_ge_le (P θ₀) k m (hφ k).1
      (a := 0) (fun z ↦ by simpa using (hφ k).2 z)) hexp)
    refine measureReal_mono (fun ω hω ↦ ?_)
    simp only [E, Set.mem_ofPred_eq] at hω ⊢
    rw [hsum]
    nlinarith
  · intro θ hθ
    have hl := hlaw θ (fun t ↦ 1 - t) (measurable_const.sub measurable_id)
    show (∫ x, 1 - (E n).indicator 1 (ext n x) ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ _
    rw [hl]
    have hb : 3 / 4 ≤ ∫ z, φ k z ∂(Measure.pi fun _ : Fin k ↦ P θ) := by
      have := hkA θ hθ
      rw [integral_sub (integrable_const _) (hint θ)] at this
      simp at this
      linarith
    rw [integral_sub (integrable_const (1 : ℝ))
      (Integrable.indicator (f := (1 : (ℕ → X) → ℝ)) (integrable_const _) (hE n)),
      integral_indicator_one (hE n)]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [← probReal_compl_eq_one_sub (hE n)]
    refine le_trans ?_ (le_trans (measure_real_sum_block_sample_ge_le (P θ) k m
      (g := fun z ↦ -φ k z) (hφ k).1.neg (a := -1)
      (fun z ↦ by have := (hφ k).2 z; constructor <;> simp <;> linarith [this.1, this.2]))
      hexp)
    refine measureReal_mono (fun ω hω ↦ ?_)
    simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    rw [integral_neg]
    have : ∑ j ∈ Finset.range m, (-φ k (blockSample k j ω) -
        -∫ z, φ k z ∂(Measure.pi fun _ : Fin k ↦ P θ)) =
        -∑ j ∈ Finset.range m, (φ k (blockSample k j ω) -
          ∫ z, φ k z ∂(Measure.pi fun _ : Fin k ↦ P θ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [this, hsum]
    nlinarith

end CKSD
