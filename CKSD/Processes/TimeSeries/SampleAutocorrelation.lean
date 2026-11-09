module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.MartingaleCLT.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Independence.Integration
public import CKSD.Processes.TimeSeries.CentralLimit

/-!
# Central limit theorem for sample autocorrelations

## Main results

* `CKSD.tendstoInDistribution_sample_autocorrelations` (GAPS 106.4, independent case of
  Bartlett's theorem): for iid observations with finite positive variance,
  `√n (ρ̂(1), …, ρ̂(m)) ⇒ N(0, I_m)`.

Cramér–Wold (Mathlib's `TendstoInDistribution.of_inner`) reduces the claim to a scalar
combination `∑ₕ tₕ √n ρ̂(h)`. After centering at the mean `c`, the main term
`n^{-1/2} ∑_{i < n - m} (X (i + m) - c) ∑ₕ tₕ (X (i + m - h) - c)` is a sum of martingale
differences for the past σ-algebras `σ(X k : k < i + m)`. Its conditional variances obey a law of
large numbers: the diagonal products by the strong law, the off-diagonal products by Chebyshev's
inequality, since they are uncorrelated. Its conditional Lindeberg sums tend to zero because
every summand is a fixed function of a window of `m + 1` observations with law `P^{m+1}`. The
martingale central limit theorem `CKSD.tendstoInDistribution_martingale_array_sum` therefore
applies. The centering and boundary remainders tend to zero in probability, `γ̂(0) → σ²`, and
Slutsky's theorem (Mathlib's
`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`) completes the proof.

The general linear-process form of Bartlett's theorem is not covered.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Convergence in probability to a constant `a` is convergence of `Zₙ - a` to `0`. -/
private theorem tendstoInMeasure_const_iff_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : ℕ → Ω → ℝ} {a : ℝ} :
    TendstoInMeasure μ Z atTop (fun _ ↦ a) ↔
      TendstoInMeasure μ (fun n ω ↦ Z n ω - a) atTop (fun _ ↦ 0) := by
  simp only [tendstoInMeasure_iff_dist, Real.dist_eq, sub_zero]

/-- Sums of sequences converging in probability to constants converge to the sum. -/
private theorem tendstoInMeasure_const_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Z W : ℕ → Ω → ℝ} {a b : ℝ}
    (hZ : TendstoInMeasure μ Z atTop (fun _ ↦ a)) (hW : TendstoInMeasure μ W atTop (fun _ ↦ b)) :
    TendstoInMeasure μ (fun n ω ↦ Z n ω + W n ω) atTop (fun _ ↦ a + b) := by
  rw [tendstoInMeasure_const_iff_sub] at hZ hW ⊢
  refine (tendstoInMeasure_add_zero μ _ _ hZ hW).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  ring

/-- Products of sequences converging in probability to constants converge to the product. -/
private theorem tendstoInMeasure_const_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Z W : ℕ → Ω → ℝ} {a b : ℝ}
    (hZ : TendstoInMeasure μ Z atTop (fun _ ↦ a)) (hW : TendstoInMeasure μ W atTop (fun _ ↦ b)) :
    TendstoInMeasure μ (fun n ω ↦ Z n ω * W n ω) atTop (fun _ ↦ a * b) := by
  have hZb := isBoundedInProbability_of_tendstoInMeasure μ Z a hZ
  rw [tendstoInMeasure_const_iff_sub] at hZ hW ⊢
  refine (tendstoInMeasure_add_zero μ _ _
    (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ Z _ hZb hW)
    (tendstoInMeasure_const_mul_zero μ _ b hZ)).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  ring

/-- A deterministic convergent sequence converges in probability to its limit. -/
private theorem tendstoInMeasure_of_tendsto_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a)) :
    TendstoInMeasure μ (fun n (_ : Ω) ↦ u n) atTop (fun _ ↦ a) := by
  rw [tendstoInMeasure_const_iff_sub]
  exact tendstoInMeasure_const_of_tendsto μ (fun n ↦ u n - a) (by
    simpa using hu.sub_const a)

/-- Finite sums of sequences converging in probability to constants converge to the sum. -/
private theorem tendstoInMeasure_finsetSum_const {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (s : Finset ι) {Z : ι → ℕ → Ω → ℝ} {a : ι → ℝ}
    (hZ : ∀ i ∈ s, TendstoInMeasure μ (Z i) atTop (fun _ ↦ a i)) :
    TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ s, Z i n ω) atTop (fun _ ↦ ∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendstoInMeasure_of_tendsto_const (μ := μ) (tendsto_const_nhds (x := 0))
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact tendstoInMeasure_const_add (hZ j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hZ i (Finset.mem_insert_of_mem hi))

/-- `(n - b) / n → 1`. -/
private theorem tendsto_natCast_sub_div_self (b : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n - b : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 - (b : ℝ) / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ)).const_sub 1
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (b + 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  rw [Nat.cast_sub (by omega)]
  field_simp

/-- A shifted iid sequence is iid with the same law. -/
private theorem IsIndependentIdenticallyDistributed.shift {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {μ : Measure Ω} {X : ℕ → Ω → E} {P : Measure E}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (a : ℕ) :
    IsIndependentIdenticallyDistributed μ (fun k ↦ X (k + a)) P :=
  ⟨fun _ ↦ hiid.1 _, hiid.2.1.precomp (add_left_injective a), fun _ ↦ hiid.2.2 _⟩

/-- Weak law of large numbers for shifted and truncated sums: for an iid sequence with law `P`
and integrable `s`, `n⁻¹ ∑_{k < n - b} s (X (k + a)) → ∫ s dP` in probability. -/
private theorem tendstoInMeasure_inv_mul_sum_range_sub_of_iid {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) {s : ℝ → ℝ} (hs : Measurable s)
    (hint : Integrable s P) (a b : ℕ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - b), s (X (k + a) ω))
      atTop (fun _ ↦ ∫ x, s x ∂P) := by
  have h := (tendstoInMeasure_sampleMean_of_iid μ P _ (hiid.shift a) s hs hint).comp
    (tendsto_sub_atTop_nat b)
  have h2 := tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const (μ := μ)
    (tendsto_natCast_sub_div_self b)) h
  rw [one_mul] at h2
  refine h2.congr' (eventually_ge_atTop (b + 1) |>.mono fun n hn ↦ ae_of_all _ fun ω ↦ ?_)
    EventuallyEq.rfl
  have hnb : ((n - b : ℕ) : ℝ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  simp only [Function.comp_apply]
  field_simp

/-- The σ-algebra `σ(X i : i < j)` generated by the observations before time `j`. -/
@[instance_reducible] private def pastSigma {Ω : Type*} (X : ℕ → Ω → ℝ) (j : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i < j, MeasurableSpace.comap (X i) inferInstance

/-- Observations before time `j` are measurable for `σ(X i : i < j)`. -/
private theorem measurable_pastSigma {Ω : Type*} {X : ℕ → Ω → ℝ} {i j : ℕ} (hij : i < j) :
    Measurable[pastSigma X j] (X i) :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun i (_ : i < j) ↦
    MeasurableSpace.comap (X i) inferInstance) i hij)

/-- `σ(X i : i < j)` is a sub-σ-algebra for measurable observations. -/
private theorem pastSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hm : ∀ i, Measurable (X i)) (j : ℕ) : pastSigma X j ≤ mΩ :=
  iSup₂_le fun i _ ↦ (hm i).comap_le

/-- The past σ-algebras increase. -/
private theorem pastSigma_mono {Ω : Type*} {X : ℕ → Ω → ℝ} : Monotone (pastSigma X) :=
  fun _ _ hjk ↦ iSup₂_le fun i hi ↦ le_iSup₂ (f := fun i (_ : i < _) ↦
    MeasurableSpace.comap (X i) inferInstance) i (lt_of_lt_of_le hi hjk)

/-- For independent observations, `X j` is independent of the past `σ(X i : i < j)`. -/
private theorem indep_comap_pastSigma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (j : ℕ) :
    Indep (MeasurableSpace.comap (X j) inferInstance) (pastSigma X j) μ := by
  have h := indep_iSup_of_disjoint (fun i ↦ (hm i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 hind) (S := {j}) (T := {i | i < j})
    (Set.disjoint_singleton_left.2 (lt_irrefl j))
  rwa [iSup_singleton] at h

/-- A function of `X j` is independent of every past-measurable random variable. -/
private theorem indepFun_comp_of_measurable_pastSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    {j : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ) {g : Ω → ℝ} (hg : Measurable[pastSigma X j] g) :
    IndepFun (fun ω ↦ φ (X j ω)) g μ := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
    (indep_comap_pastSigma hm hind j) ?_) (measurable_iff_comap_le.1 hg)
  exact measurable_iff_comap_le.1 (hφ.comp (comap_measurable (X j)))

/-- Integrals of functions of an observation are integrals against the common law. -/
private theorem integral_comp_of_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {P : Measure ℝ} {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (k : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) : ∫ ω, φ (X k ω) ∂μ = ∫ x, φ x ∂P := by
  rw [← hiid.2.2 k, integral_map (hiid.1 k).aemeasurable hφ.aestronglyMeasurable]

/-- Functions of an observation integrable for the common law are integrable. -/
private theorem integrable_comp_of_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {P : Measure ℝ} {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (k : ℕ)
    {φ : ℝ → ℝ} (hφ : Integrable φ P) : Integrable (fun ω ↦ φ (X k ω)) μ := by
  rw [← hiid.2.2 k] at hφ
  exact hφ.comp_measurable (hiid.1 k)

/-- For iid square-integrable observations with mean `c` and `i < j`, the product
`(X i - c) (X j - c)` is square integrable with `𝔼[((X i - c) (X j - c))²] = σ⁴`. -/
private theorem memLp_mul_and_integral_sq_of_iid {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P) (c : ℝ) {i j : ℕ}
    (hij : i < j) :
    MemLp (fun ω ↦ (X i ω - c) * (X j ω - c)) 2 μ ∧
      ∫ ω, ((X i ω - c) * (X j ω - c)) ^ 2 ∂μ = (∫ x, (x - c) ^ 2 ∂P) ^ 2 := by
  have hsq : Integrable (fun x : ℝ ↦ (x - c) ^ 2) P :=
    (hP2.sub (memLp_const c)).integrable_sq
  have hind : IndepFun (fun ω ↦ (X j ω - c) ^ 2) (fun ω ↦ (X i ω - c) ^ 2) μ :=
    indepFun_comp_of_measurable_pastSigma (φ := fun x ↦ (x - c) ^ 2) hiid.1 hiid.2.1
      (by fun_prop) (((measurable_pastSigma hij).sub_const c).pow_const 2)
  have hint : Integrable (fun ω ↦ ((X i ω - c) * (X j ω - c)) ^ 2) μ := by
    have := IndepFun.integrable_mul hind (integrable_comp_of_iid hiid j hsq)
      (integrable_comp_of_iid hiid i hsq)
    refine this.congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.mul_apply]; ring
  refine ⟨(memLp_two_iff_integrable_sq (by
    exact (((hiid.1 i).sub_const c).mul ((hiid.1 j).sub_const c)).aestronglyMeasurable)).2 hint,
    ?_⟩
  have h := IndepFun.integral_fun_mul_eq_mul_integral hind
    (((hiid.1 j).sub_const c).pow_const 2).aestronglyMeasurable
    (((hiid.1 i).sub_const c).pow_const 2).aestronglyMeasurable
  rw [integral_comp_of_iid hiid j (φ := fun x ↦ (x - c) ^ 2) (by fun_prop),
    integral_comp_of_iid hiid i (φ := fun x ↦ (x - c) ^ 2) (by fun_prop)] at h
  rw [← sq] at h
  rw [← h]
  congr 1; ext ω; ring

/-- Centered iid observations have mean zero. -/
private theorem integral_sub_mean_of_iid {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (k : ℕ) : ∫ ω, (X k ω - ∫ x, x ∂P) ∂μ = 0 := by
  have hi : Integrable (fun x : ℝ ↦ x) P := hP2.integrable one_le_two
  rw [integral_comp_of_iid hiid k (φ := fun x ↦ x - ∫ x, x ∂P) (by fun_prop),
    integral_sub hi (integrable_const _)]
  simp

/-- For iid observations with mean `c` and lags `a < a'`, the products
`Zⱼ = (X (j + a) - c) (X (j + a') - c)` are uncorrelated: `𝔼[Zⱼ Zₖ] = 0` for `j < k`. -/
private theorem integral_mul_lag_products_of_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    {a a' : ℕ} (haa : a < a') {j k : ℕ} (hjk : j < k) :
    ∫ ω, ((X (j + a) ω - ∫ x, x ∂P) * (X (j + a') ω - ∫ x, x ∂P)) *
      ((X (k + a) ω - ∫ x, x ∂P) * (X (k + a') ω - ∫ x, x ∂P)) ∂μ = 0 := by
  set c := ∫ x, x ∂P
  have hg : Measurable[pastSigma X (k + a')] fun ω ↦
      (X (j + a) ω - c) * (X (j + a') ω - c) * (X (k + a) ω - c) :=
    (((measurable_pastSigma (by omega)).sub_const c).mul
      ((measurable_pastSigma (by omega)).sub_const c)).mul
      ((measurable_pastSigma (by omega)).sub_const c)
  have hind := indepFun_comp_of_measurable_pastSigma (φ := fun x ↦ x - c) hiid.1 hiid.2.1
    (by fun_prop) hg
  have h := IndepFun.integral_fun_mul_eq_mul_integral hind
    ((hiid.1 _).sub_const c).aestronglyMeasurable
    (hg.mono (pastSigma_le hiid.1 _) le_rfl).aestronglyMeasurable
  rw [integral_sub_mean_of_iid hiid hP2, zero_mul] at h
  rw [← h]
  congr 1; ext ω; ring

/-- Off-diagonal law of large numbers: for iid square-integrable observations with mean `c` and
lags `a < a'`, `n⁻¹ ∑_{k < n - b} (X (k + a) - c) (X (k + a') - c) → 0` in probability. The
summands are uncorrelated with second moment `σ⁴`, so Chebyshev's inequality applies. -/
private theorem tendstoInMeasure_inv_mul_sum_lag_products {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    {a a' : ℕ} (haa : a < a') (b : ℕ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - b),
      (X (k + a) ω - ∫ x, x ∂P) * (X (k + a') ω - ∫ x, x ∂P)) atTop (fun _ ↦ 0) := by
  set c := ∫ x, x ∂P
  set s4 := (∫ x, (x - c) ^ 2 ∂P) ^ 2
  set Z : ℕ → Ω → ℝ := fun k ω ↦ (X (k + a) ω - c) * (X (k + a') ω - c)
  have hZ := fun k ↦ memLp_mul_and_integral_sq_of_iid hiid hP2 c (i := k + a) (j := k + a')
    (by omega)
  have hZZ : ∀ j k, ∫ ω, Z j ω * Z k ω ∂μ = if j = k then s4 else 0 := by
    intro j k
    rcases lt_trichotomy j k with h | rfl | h
    · simp only [h.ne, ↓reduceIte]; exact integral_mul_lag_products_of_lt hiid hP2 haa h
    · simp only [↓reduceIte]
      show _ = (∫ x, (x - c) ^ 2 ∂P) ^ 2
      rw [← (hZ j).2]; congr 1; ext ω; ring
    · simp only [h.ne', ↓reduceIte]
      rw [← integral_mul_lag_products_of_lt hiid hP2 haa h]
      congr 1; ext ω; simp only [Z]; ring
  have hS2 : ∀ N, ∫ ω, (∑ k ∈ Finset.range N, Z k ω) ^ 2 ∂μ = N * s4 := by
    intro N
    have hexp : ∀ ω, (∑ k ∈ Finset.range N, Z k ω) ^ 2 =
        ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, Z j ω * Z k ω := fun ω ↦ by
      rw [sq, Finset.sum_mul_sum]
    have hint : ∀ j k, Integrable (fun ω ↦ Z j ω * Z k ω) μ := fun j k ↦
      (hZ j).1.integrable_mul (hZ k).1
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hint j k]
    simp_rw [integral_finsetSum _ fun k _ ↦ hint _ k, hZZ]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_congr rfl fun x hx ↦ (ite_eq_left (Finset.mem_range.1 hx) : _ = s4)]
    simp
  have hS2i : ∀ N, Integrable (fun ω ↦ (∑ k ∈ Finset.range N, Z k ω) ^ 2) μ := fun N ↦
    (memLp_finsetSum (Finset.range N) fun k _ ↦ (hZ k).1).integrable_sq
  rw [tendstoInMeasure_iff_measureReal_lt_dist]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ s4 / ε ^ 2 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.const_mul (s4 / ε ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set N := n - b
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n b
  have hδ : 0 < ((n : ℝ) * ε) ^ 2 := by positivity
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) (hS2i N)
    (((n : ℝ) * ε) ^ 2)
  rw [hS2] at hM
  have hsub : {ω | ε < dist ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range N, Z k ω) 0} ⊆
      {ω | ((n : ℝ) * ε) ^ 2 ≤ (∑ k ∈ Finset.range N, Z k ω) ^ 2} := by
    intro ω hω
    simp only [Real.dist_eq, sub_zero, mem_ofPred_eq, abs_mul, abs_inv, Nat.abs_cast] at hω ⊢
    rw [← sq_abs (∑ k ∈ Finset.range N, Z k ω)]
    have : (n : ℝ) * ε < |∑ k ∈ Finset.range N, Z k ω| := by
      rw [inv_mul_eq_div, lt_div_iff₀ hn'] at hω; linarith
    exact pow_le_pow_left₀ (by positivity) this.le 2
  have hs4 : 0 ≤ s4 := sq_nonneg _
  calc μ.real {ω | ε < dist ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range N, Z k ω) 0}
      ≤ μ.real {ω | ((n : ℝ) * ε) ^ 2 ≤ (∑ k ∈ Finset.range N, Z k ω) ^ 2} :=
        measureReal_mono hsub
    _ ≤ N * s4 / ((n : ℝ) * ε) ^ 2 := by rw [le_div_iff₀ hδ, mul_comm]; exact hM
    _ ≤ n * s4 / ((n : ℝ) * ε) ^ 2 := by gcongr
    _ = s4 / ε ^ 2 * (n : ℝ)⁻¹ := by field_simp

/-- For iid observations with law `P`, every window `(X i, …, X (i + m))` has law `P^{m+1}`. -/
private theorem map_window_eq_pi_of_iid {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (m i : ℕ) :
    μ.map (fun ω (k : Fin (m + 1)) ↦ X (i + k) ω) = Measure.pi fun _ ↦ P := by
  have hind : iIndepFun (fun k : Fin (m + 1) ↦ X (i + k)) μ :=
    hiid.2.1.precomp (g := fun k : Fin (m + 1) ↦ i + (k : ℕ))
      fun k l hkl ↦ Fin.ext (by simpa using hkl)
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun k ↦ (hiid.1 _).aemeasurable).1 hind]
  simp_rw [hiid.2.2]

/-- Nonnegative integrable random variables with means tending to zero tend to zero in
probability (Markov's inequality). -/
private theorem tendstoInMeasure_zero_of_integral_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ} (hZ0 : ∀ n, 0 ≤ᵐ[μ] Z n)
    (hZi : ∀ n, Integrable (Z n) μ) (hZ : Tendsto (fun n ↦ ∫ ω, Z n ω ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ Z atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_measureReal_lt_dist]
  intro ε hε
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) (by
    simpa using hZ.div_const ε)
  have hM := mul_meas_ge_le_integral_of_nonneg (hZ0 n) (hZi n) ε
  rw [le_div_iff₀ hε, mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hε.le) hM
  have hsub : {ω | ε < dist (Z n ω) 0} ≤ᵐ[μ] {ω | ε ≤ Z n ω} := by
    filter_upwards [hZ0 n] with ω hω h
    simp only [Real.dist_eq, sub_zero, Pi.zero_apply] at h hω ⊢
    rw [abs_of_nonneg hω] at h
    exact h.le
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

/-- Centered observations of an iid sequence with square-integrable law are square integrable. -/
private theorem memLp_sub_of_iid {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {P : Measure ℝ} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P) (c : ℝ) (k : ℕ) :
    MemLp (fun ω ↦ X k ω - c) 2 μ := by
  have h : MemLp (fun x : ℝ ↦ x - c) 2 (μ.map (X k)) := by
    rw [hiid.2.2 k]; exact hP2.sub (memLp_const c)
  exact h.comp_of_map (hiid.1 k).aemeasurable

/-- Pull-out and independence: for a past-measurable integrable `f` and an integrable function
`φ` of the current observation, `𝔼[f φ(X j) | σ(X i : i < j)] = f 𝔼 φ(X j)`. -/
private theorem condExp_mul_comp_pastSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} {X : ℕ → Ω → ℝ}
    (hiid : IsIndependentIdenticallyDistributed μ X P) {j : ℕ} {f : Ω → ℝ}
    (hf : Measurable[pastSigma X j] f) (hfi : Integrable f μ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hφi : Integrable φ P) :
    μ[fun ω ↦ f ω * φ (X j ω) | pastSigma X j] =ᵐ[μ] fun ω ↦ f ω * ∫ x, φ x ∂P := by
  have hind := indepFun_comp_of_measurable_pastSigma hiid.1 hiid.2.1 hφ hf
  have hgi : Integrable (fun ω ↦ φ (X j ω)) μ := integrable_comp_of_iid hiid j hφi
  have hprod : Integrable (f * fun ω ↦ φ (X j ω)) μ := IndepFun.integrable_mul hind.symm hfi hgi
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := pastSigma X j)
    hf.stronglyMeasurable hprod hgi
  have h2 := condExp_indep_eq (μ := μ) (f := fun ω ↦ φ (X j ω)) (hiid.1 j).comap_le
    (pastSigma_le hiid.1 j) (hφ.comp (comap_measurable (X j))).stronglyMeasurable
    (indep_comap_pastSigma hiid.1 hiid.2.1 j)
  filter_upwards [h1, h2] with ω h1 h2
  change μ[f * fun ω ↦ φ (X j ω) | pastSigma X j] ω = _
  rw [h1, Pi.mul_apply, h2, integral_comp_of_iid hiid j hφ]

/-- Law of large numbers for the products at two lags `a, a' ≥ 0`:
`n⁻¹ ∑_{k < n - b} (X (k + a) - c) (X (k + a') - c) → σ² 1{a = a'}` in probability. -/
private theorem tendstoInMeasure_inv_mul_sum_lag_products' {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (a a' b : ℕ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - b),
      (X (k + a) ω - ∫ x, x ∂P) * (X (k + a') ω - ∫ x, x ∂P)) atTop
      (fun _ ↦ if a = a' then ∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P else 0) := by
  rcases lt_trichotomy a a' with h | rfl | h
  · simp only [h.ne, ↓reduceIte]
    exact tendstoInMeasure_inv_mul_sum_lag_products hiid hP2 h b
  · simp only [↓reduceIte]
    refine (tendstoInMeasure_inv_mul_sum_range_sub_of_iid hiid
      (s := fun x ↦ (x - ∫ x, x ∂P) ^ 2) (by fun_prop)
      (hP2.sub (memLp_const _)).integrable_sq a b).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
    simp only [sq]
  · simp only [h.ne', ↓reduceIte]
    refine (tendstoInMeasure_inv_mul_sum_lag_products hiid hP2 h b).congr_left
      fun n ↦ ae_of_all _ fun ω ↦ ?_
    simp only [mul_comm (X (_ + a') ω - _)]

/-- Law of large numbers for the conditional variances of the lag martingale differences: with
`Wᵢ = ∑_{h < m} t_h (X (i + m - (h + 1)) - c)`, `n⁻¹ ∑_{i < n - m} Wᵢ² σ² → σ⁴ ∑_h t_h²` in
probability. -/
private theorem tendstoInMeasure_sum_inv_mul_sq_lagSum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (m : ℕ) (t : Fin m → ℝ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ ∑ i ∈ Finset.range (n - m),
      (n : ℝ)⁻¹ * (∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - ∫ x, x ∂P)) ^ 2 *
        ∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) atTop
      (fun _ ↦ (∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) * (∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) *
        ∑ h : Fin m, t h ^ 2) := by
  set c := ∫ x, x ∂P
  set σ2 := ∫ x, (x - c) ^ 2 ∂P
  have hpair : ∀ h h' : Fin m, TendstoInMeasure μ (fun (n : ℕ) ω ↦ σ2 * (t h * t h' *
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range (n - m),
        (X (i + (m - (h + 1))) ω - c) * (X (i + (m - (h' + 1))) ω - c)))) atTop
      (fun _ ↦ σ2 * (t h * t h' * if h = h' then σ2 else 0)) := by
    intro h h'
    have hiff : (m - (h + 1 : ℕ) = m - (h' + 1 : ℕ)) ↔ h = h' := by
      have := h.isLt; have := h'.isLt
      constructor
      · intro e; exact Fin.ext (by omega)
      · rintro rfl; rfl
    have hl := tendstoInMeasure_inv_mul_sum_lag_products' hiid hP2 (m - (h + 1 : ℕ))
      (m - (h' + 1 : ℕ)) m
    simp only [hiff] at hl
    exact tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const tendsto_const_nhds)
      (tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const tendsto_const_nhds) hl)
  have hsum := tendstoInMeasure_finsetSum_const Finset.univ fun h _ ↦
    tendstoInMeasure_finsetSum_const Finset.univ fun h' _ ↦ hpair h h'
  have hlim : ∑ h : Fin m, ∑ h' : Fin m, σ2 * (t h * t h' * if h = h' then σ2 else 0) =
      σ2 * σ2 * ∑ h : Fin m, t h ^ 2 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ ↦ by ring
  rw [hlim] at hsum
  refine hsum.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  simp only [sq, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun h' _ ↦ Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun h' _ ↦
    Finset.sum_congr rfl fun i _ ↦ by ring

/-- Lindeberg condition for the lag martingale differences
`Dₙᵢ = n^{-1/2} (X (i + m) - c) ∑_{h < m} t_h (X (i + m - (h + 1)) - c)`: the summed truncated
second moments tend to zero. Each `Dₙᵢ` is a fixed function of the window
`(X i, …, X (i + m))`, whose law is `P^{m+1}`, so dominated convergence applies. -/
private theorem tendsto_sum_integral_lag_lindeberg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P)
    (m : ℕ) (t : Fin m → ℝ) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hV2 : Integrable (fun ω ↦ ((X (0 + m) ω - c) *
      ∑ h : Fin m, t h * (X (0 + (m - (h + 1))) ω - c)) ^ 2) μ) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range (n - m), ∫ ω,
      (if ε < |(Real.sqrt n)⁻¹ * ((X (i + m) ω - c) *
        ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c))| then
        ((Real.sqrt n)⁻¹ * ((X (i + m) ω - c) *
          ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c))) ^ 2 else 0) ∂μ) atTop (𝓝 0) := by
  set g : (Fin (m + 1) → ℝ) → ℝ := fun x ↦ (x (Fin.last m) - c) *
    ∑ h : Fin m, t h * (x ⟨m - (h + 1), by omega⟩ - c) with hgdef
  have hg : Measurable g := by fun_prop
  have hVg : ∀ i ω, (X (i + m) ω - c) * ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c) =
      g (fun k ↦ X (i + k) ω) := fun i ω ↦ by simp [hgdef]
  have hΦ : ∀ i, Measurable (fun ω (k : Fin (m + 1)) ↦ X (i + k) ω) := fun i ↦
    measurable_pi_iff.2 fun k ↦ hiid.1 _
  set G : ℕ → (Fin (m + 1) → ℝ) → ℝ := fun n x ↦
    if ε < |(Real.sqrt n)⁻¹ * g x| then ((Real.sqrt n)⁻¹ * g x) ^ 2 else 0 with hGdef
  have hGm : ∀ n, Measurable (G n) := fun n ↦
    Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
      measurable_const
  have hterm : ∀ (n : ℕ) (i : ℕ), ∫ ω, (if ε < |(Real.sqrt n)⁻¹ * ((X (i + m) ω - c) *
        ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c))| then
        ((Real.sqrt n)⁻¹ * ((X (i + m) ω - c) *
          ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c))) ^ 2 else 0) ∂μ =
      ∫ x, G n x ∂(Measure.pi fun _ ↦ P) := fun n i ↦ by
    rw [← map_window_eq_pi_of_iid hiid m i,
      integral_map (hΦ i).aemeasurable (hGm n).aestronglyMeasurable]
    simp only [hVg, hGdef]
  simp_rw [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg2 : Integrable (fun x ↦ g x ^ 2) (Measure.pi fun _ ↦ P) := by
    rw [← map_window_eq_pi_of_iid hiid m 0,
      integrable_map_measure (hg.pow_const 2).aestronglyMeasurable (hΦ 0).aemeasurable]
    refine hV2.congr (ae_of_all _ fun ω ↦ ?_)
    simp only [Function.comp_apply, hVg]
  set H : ℕ → (Fin (m + 1) → ℝ) → ℝ := fun n x ↦
    if ε < |(Real.sqrt n)⁻¹ * g x| then g x ^ 2 else 0 with hHdef
  have hinvsqrt : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hH : Tendsto (fun n ↦ ∫ x, H n x ∂(Measure.pi fun _ ↦ P)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x ↦ g x ^ 2)
      (F := H) (f := fun _ ↦ 0)
      (fun n ↦ (Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
        (by fun_prop) measurable_const).aestronglyMeasurable) hg2
      (fun n ↦ ae_of_all _ fun x ↦ by
        simp only [hHdef]
        split_ifs <;> simp [sq_nonneg])
      (ae_of_all _ fun x ↦ by
        have hx : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹ * g x) atTop (𝓝 0) := by
          simpa using hinvsqrt.mul_const (g x)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(hx.abs.eventually (gt_mem_nhds (by simpa using hε)))] with n hn
        simp only [hHdef, ite_eq_right (not_lt.2 hn.le)])
    simpa using h
  refine squeeze_zero' (Eventually.of_forall fun n ↦ mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg fun x ↦ by simp only [hGdef]; split_ifs <;> positivity)) ?_ hH
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hG0 : 0 ≤ ∫ x, G n x ∂(Measure.pi fun _ ↦ P) :=
    integral_nonneg fun x ↦ by simp only [hGdef]; split_ifs <;> positivity
  calc ((n - m : ℕ) : ℝ) * ∫ x, G n x ∂(Measure.pi fun _ ↦ P)
      ≤ n * ∫ x, G n x ∂(Measure.pi fun _ ↦ P) := by
        gcongr; exact_mod_cast Nat.sub_le n m
    _ = ∫ x, H n x ∂(Measure.pi fun _ ↦ P) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [hGdef, hHdef]
        split_ifs
        · rw [mul_pow, inv_pow, Real.sq_sqrt hn'.le]; field_simp
        · simp

/-- Martingale central limit theorem for the lag sums of an iid sequence with mean `c` and
variance `σ²`: with `Wᵢ = ∑_{h < m} t_h (X (i + m - (h + 1)) - c)`, the sums
`n^{-1/2} ∑_{i < n - m} (X (i + m) - c) Wᵢ` converge in law to `N(0, σ⁴ ∑_h t_h²)`. The summands
are martingale differences for `σ(X k : k < i + m)`, with conditional variances `n⁻¹ Wᵢ² σ²`;
GAPS 106.1 (`tendstoInDistribution_martingale_array_sum`) applies. -/
private theorem tendstoInDistribution_sum_lag_martingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (m : ℕ) (t : Fin m → ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ ∑ i ∈ Finset.range (n - m),
      (Real.sqrt n)⁻¹ * ((X (i + m) ω - ∫ x, x ∂P) *
        ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - ∫ x, x ∂P))) atTop id (fun _ ↦ μ)
      (gaussianReal 0 ((∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) * (∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) *
        ∑ h : Fin m, t h ^ 2).toNNReal) := by
  set c := ∫ x, x ∂P
  set σ2 := ∫ x, (x - c) ^ 2 ∂P
  set W : ℕ → Ω → ℝ := fun i ω ↦ ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c) with hW
  set D : ℕ → ℕ → Ω → ℝ := fun n i ω ↦ (Real.sqrt n)⁻¹ * ((X (i + m) ω - c) * W i ω) with hD
  let F : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq := fun i ↦ pastSigma X (i + m)
      mono' := fun i j hij ↦ pastSigma_mono (by omega)
      le' := fun i ↦ pastSigma_le hiid.1 _ }
  have hWm : ∀ i, Measurable[pastSigma X (i + m)] (W i) := fun i ↦
    Finset.measurable_fun_sum _ fun h _ ↦ measurable_const.mul
      ((measurable_pastSigma (by have := h.isLt; omega)).sub_const c)
  have hW2 : ∀ i, MemLp (W i) 2 μ := fun i ↦
    memLp_finsetSum _ fun h _ ↦ (memLp_sub_of_iid hiid hP2 c _).const_mul (t h)
  have hsq : Integrable (fun x : ℝ ↦ (x - c) ^ 2) P := (hP2.sub (memLp_const c)).integrable_sq
  have hlin1 : Integrable (fun x : ℝ ↦ x - c) P :=
    (hP2.sub (memLp_const c)).integrable one_le_two
  have hc0 : ∫ x, (x - c) ∂P = 0 := by
    have hi : Integrable (fun x : ℝ ↦ x) P := hP2.integrable one_le_two
    rw [integral_sub hi (integrable_const c)]; simp [c]
  have hV2 : ∀ i, Integrable (fun ω ↦ W i ω ^ 2 * (X (i + m) ω - c) ^ 2) μ := fun i ↦ by
    have hind := indepFun_comp_of_measurable_pastSigma (φ := fun x ↦ (x - c) ^ 2) hiid.1
      hiid.2.1 (by fun_prop) ((hWm i).pow_const 2)
    exact IndepFun.integrable_mul hind.symm (hW2 i).integrable_sq
      (integrable_comp_of_iid hiid _ hsq)
  have hXm : ∀ i, Measurable (fun ω ↦ X (i + m) ω - c) := fun i ↦ (hiid.1 _).sub_const c
  have hWm' : ∀ i, Measurable (W i) := fun i ↦ (hWm i).mono (pastSigma_le hiid.1 _) le_rfl
  have ha : ∀ n i, Measurable[F (i + 1)] (D n i) := fun n i ↦
    measurable_const.mul (((measurable_pastSigma (by omega)).sub_const c).mul
      ((hWm i).mono (pastSigma_mono (by omega)) le_rfl))
  have hDsq : ∀ (n : ℕ) i, (fun ω ↦ D n i ω ^ 2) =
      fun ω ↦ ((n : ℝ)⁻¹ * W i ω ^ 2) * (X (i + m) ω - c) ^ 2 := fun n i ↦ by
    funext ω
    simp only [hD, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have h2 : ∀ n i, MemLp (D n i) 2 μ := fun n i ↦ by
    have hm : AEStronglyMeasurable (D n i) μ :=
      (measurable_const.mul ((hXm i).mul (hWm' i))).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    rw [hDsq]
    exact ((hV2 i).const_mul ((n : ℝ)⁻¹)).congr (ae_of_all _ fun ω ↦ by simp only; ring)
  have h0 : ∀ n i, μ[D n i | F i] =ᵐ[μ] fun _ ↦ 0 := fun n i ↦ by
    have h := condExp_mul_comp_pastSigma hiid (j := i + m)
      (f := fun ω ↦ (Real.sqrt n)⁻¹ * W i ω) (measurable_const.mul (hWm i))
      (((hW2 i).integrable one_le_two).const_mul _) (φ := fun x ↦ x - c) (by fun_prop) hlin1
    have heq : D n i = fun ω ↦ ((Real.sqrt n)⁻¹ * W i ω) * (X (i + m) ω - c) := by
      funext ω; simp only [hD]; ring
    rw [heq]
    filter_upwards [h] with ω hω
    rw [hω, hc0, mul_zero]
  have hce : ∀ (n : ℕ) i, μ[fun ω ↦ D n i ω ^ 2 | F i] =ᵐ[μ]
      fun ω ↦ ((n : ℝ)⁻¹ * W i ω ^ 2) * σ2 := fun n i ↦ by
    rw [hDsq]
    exact condExp_mul_comp_pastSigma hiid (j := i + m) (f := fun ω ↦ (n : ℝ)⁻¹ * W i ω ^ 2)
      (measurable_const.mul ((hWm i).pow_const 2)) ((hW2 i).integrable_sq.const_mul _)
      (φ := fun x ↦ (x - c) ^ 2) (by fun_prop) hsq
  have hvar : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (n - m), μ[(fun ω ↦ D n j ω ^ 2) | F j] ω) atTop
      (fun _ ↦ σ2 * σ2 * ∑ h : Fin m, t h ^ 2) := by
    refine (tendstoInMeasure_sum_inv_mul_sq_lagSum hiid hP2 m t).congr_left fun n ↦ ?_
    filter_upwards [ae_all_iff.2 fun i ↦ hce n i] with ω hω
    exact Finset.sum_congr rfl fun i _ ↦ (hω i).symm
  have hlin : ∀ ε > 0, TendstoInMeasure μ (fun (n : ℕ) ω ↦
      ∑ j ∈ Finset.range (n - m),
        μ[(fun ω ↦ if ε < |D n j ω| then D n j ω ^ 2 else 0) | F j] ω) atTop
      (fun _ ↦ 0) := by
    intro ε hε
    refine tendstoInMeasure_zero_of_integral_tendsto_zero (fun n ↦ ?_)
      (fun n ↦ integrable_finsetSum _ fun j _ ↦ integrable_condExp) ?_
    · filter_upwards [ae_all_iff.2 fun j ↦ condExp_nonneg (μ := μ) (m := F j)
        (f := fun ω ↦ if ε < |D n j ω| then D n j ω ^ 2 else 0)
        (ae_of_all _ fun ω ↦ by simp only [Pi.zero_apply]; split_ifs <;> positivity)]
        with ω hω
      exact Finset.sum_nonneg fun j _ ↦ hω j
    · have hL := tendsto_sum_integral_lag_lindeberg hiid m t c hε (by
        refine (hV2 0).congr (ae_of_all _ fun ω ↦ ?_); simp only [hW]; ring)
      refine hL.congr fun n ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ integrable_condExp]
      exact Finset.sum_congr rfl fun j _ ↦ (integral_condExp (F.le j)).symm
  have hclt := tendstoInDistribution_martingale_array_sum μ (fun _ ↦ F) D (fun n ↦ n - m) ha h2
    h0 _ hvar hlin
  exact hclt

/-- Sample autocovariances of measurable observations are measurable. -/
private theorem measurable_sampleAutocovariance {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (ℓ n : ℕ) :
    Measurable (sampleAutocovariance X ℓ n) := by
  have hA : Measurable (sampleAverage X n) := by
    have h : sampleAverage X n = fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [sampleAverage]
    rw [h]; exact measurable_const.mul (Finset.measurable_fun_sum _ fun i _ ↦ hm i)
  exact (Finset.measurable_fun_sum _ fun k _ ↦ ((hm _).sub hA).mul ((hm _).sub hA)).div_const _

/-- The remainder in the centered decomposition of the sample autocovariance at lag `ℓ`:
`Q = -n⁻¹ ∑_{k < n - ℓ} (X (k + ℓ) - c) - n⁻¹ ∑_{k < n - ℓ} (X k - c) + (n - ℓ) n⁻¹ (X̄ - c)`. -/
private def acovRemainder {Ω : Type*} (X : ℕ → Ω → ℝ) (c : ℝ) (ℓ n : ℕ) (ω : Ω) : ℝ :=
  -((n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - ℓ), (X (k + ℓ) ω - c)) -
    (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - ℓ), (X (k + 0) ω - c) +
    ((n - ℓ : ℕ) : ℝ) / n * (sampleAverage X n ω - c)

/-- Centered decomposition of the sample autocovariance: for every centering constant `c`,
`γ̂(ℓ) = n⁻¹ ∑_{k < n - ℓ} (X (k + ℓ) - c) (X k - c) + (X̄ - c) Q`. -/
private theorem sampleAutocovariance_eq_add {Ω : Type*} (X : ℕ → Ω → ℝ) (c : ℝ) (ℓ n : ℕ)
    (ω : Ω) :
    sampleAutocovariance X ℓ n ω = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n - ℓ),
      (X (k + ℓ) ω - c) * (X k ω - c) +
      (sampleAverage X n ω - c) * acovRemainder X c ℓ n ω := by
  set B := sampleAverage X n ω - c
  have h : ∀ k, (X (k + ℓ) ω - sampleAverage X n ω) * (X k ω - sampleAverage X n ω) =
      (X (k + ℓ) ω - c) * (X k ω - c) - B * (X (k + ℓ) ω - c) - B * (X k ω - c) + B * B :=
    fun k ↦ by simp only [B]; ring
  simp only [sampleAutocovariance, acovRemainder, h, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, add_zero]
  ring

/-- `√n (X̄ₙ - c) = n^{-1/2} ∑_{k < n} (X k - c)` for every `n`. -/
private theorem sqrt_mul_sampleAverage_sub {Ω : Type*} (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ)
    (ω : Ω) :
    Real.sqrt n * (sampleAverage X n ω - c) =
      (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  simp only [sampleAverage, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsq := Real.mul_self_sqrt hn'.le
  set r := Real.sqrt n
  rw [← hsq]
  field_simp

/-- Differences of sequences converging in probability to constants converge to the
difference. -/
private theorem tendstoInMeasure_const_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Z W : ℕ → Ω → ℝ} {a b : ℝ}
    (hZ : TendstoInMeasure μ Z atTop (fun _ ↦ a)) (hW : TendstoInMeasure μ W atTop (fun _ ↦ b)) :
    TendstoInMeasure μ (fun n ω ↦ Z n ω - W n ω) atTop (fun _ ↦ a - b) := by
  have h := tendstoInMeasure_const_add hZ (tendstoInMeasure_const_mul
    (tendstoInMeasure_of_tendsto_const (μ := μ) (tendsto_const_nhds (x := (-1 : ℝ)))) hW)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- For iid observations with mean `c`, the sample mean converges: `X̄ₙ - c → 0`. -/
private theorem tendstoInMeasure_sampleAverage_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P) :
    TendstoInMeasure μ (fun n ω ↦ sampleAverage X n ω - ∫ x, x ∂P) atTop (fun _ ↦ 0) := by
  rw [← tendstoInMeasure_const_iff_sub]
  refine (tendstoInMeasure_sampleMean_of_iid μ P X hiid id measurable_id
    (hP2.integrable one_le_two)).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  simp [sampleAverage, smul_eq_mul]

/-- The remainder in the centered decomposition of the sample autocovariance tends to zero in
probability. -/
private theorem tendstoInMeasure_acovRemainder {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (ℓ : ℕ) :
    TendstoInMeasure μ (fun n ω ↦ acovRemainder X (∫ x, x ∂P) ℓ n ω) atTop (fun _ ↦ 0) := by
  set c := ∫ x, x ∂P with hc
  have hi : Integrable (fun x : ℝ ↦ x - c) P := (hP2.sub (memLp_const c)).integrable one_le_two
  have hc0 : ∫ x, (x - c) ∂P = 0 := by
    have hi' : Integrable (fun x : ℝ ↦ x) P := hP2.integrable one_le_two
    rw [integral_sub hi' (integrable_const c)]; simp [c]
  have h1 := tendstoInMeasure_inv_mul_sum_range_sub_of_iid hiid (s := fun x ↦ x - c)
    (by fun_prop) hi ℓ ℓ
  have h2 := tendstoInMeasure_inv_mul_sum_range_sub_of_iid hiid (s := fun x ↦ x - c)
    (by fun_prop) hi 0 ℓ
  have h3 := tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const (μ := μ)
    (tendsto_natCast_sub_div_self ℓ)) (tendstoInMeasure_sampleAverage_sub hiid hP2)
  rw [hc0] at h1 h2
  have h := tendstoInMeasure_const_add (tendstoInMeasure_const_sub
    (tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const (μ := μ)
      (tendsto_const_nhds (x := (-1 : ℝ)))) h1) h2) h3
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  simp only [acovRemainder, ← hc, add_zero]; ring

/-- For iid observations with positive variance `σ²`, the sample variance `γ̂(0) → σ²` in
probability. -/
private theorem tendstoInMeasure_sampleAutocovariance_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P) :
    TendstoInMeasure μ (fun n ω ↦ sampleAutocovariance X 0 n ω) atTop
      (fun _ ↦ ∫ x, (x - ∫ x, x ∂P) ^ 2 ∂P) := by
  set c := ∫ x, x ∂P
  have h1 := tendstoInMeasure_inv_mul_sum_range_sub_of_iid hiid (s := fun x ↦ (x - c) ^ 2)
    (by fun_prop) (hP2.sub (memLp_const c)).integrable_sq 0 0
  have h := tendstoInMeasure_const_add h1 (tendstoInMeasure_const_mul
    (tendstoInMeasure_sampleAverage_sub hiid hP2) (tendstoInMeasure_acovRemainder hiid hP2 0))
  simp only [mul_zero, add_zero] at h
  refine h.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  simp only [sampleAutocovariance_eq_add X c 0 n ω, sq, add_zero]
  rfl

/-- Lag decomposition of the normalized sample autocovariance: for `ℓ ≤ m ≤ n`,
`√n γ̂(ℓ) = n^{-1/2} ∑_{i < n - m} (X (i + m) - c) (X (i + m - ℓ) - c) + Rₙ`, where `Rₙ` collects
the first `m - ℓ` products and the centering remainder. -/
private theorem sqrt_mul_sampleAutocovariance_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (c : ℝ)
    {ℓ m n : ℕ} (hℓ : ℓ ≤ m) (hm : m ≤ n) (ω : Ω) :
    Real.sqrt n * sampleAutocovariance X ℓ n ω =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (n - m), (X (i + m) ω - c) * (X (i + (m - ℓ)) ω - c) +
      ((Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range (m - ℓ), (X (k + ℓ) ω - c) * (X k ω - c) +
        Real.sqrt n * (sampleAverage X n ω - c) * acovRemainder X c ℓ n ω) := by
  have hs : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
  have hsplit : n - ℓ = (m - ℓ) + (n - m) := by omega
  rw [sampleAutocovariance_eq_add X c ℓ n ω, mul_add, ← mul_assoc, hs, hsplit,
    Finset.sum_range_add]
  have hterm : ∀ i ∈ Finset.range (n - m),
      (X (m - ℓ + i + ℓ) ω - c) * (X (m - ℓ + i) ω - c) =
        (X (i + m) ω - c) * (X (i + (m - ℓ)) ω - c) := fun i _ ↦ by
    rw [show m - ℓ + i + ℓ = i + m by omega, show m - ℓ + i = i + (m - ℓ) by omega]
  rw [Finset.sum_congr rfl hterm]
  ring

/-- A fixed measurable random variable divided by `√n` tends to zero in probability. -/
private theorem tendstoInMeasure_inv_sqrt_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C : Ω → ℝ} (hC : Measurable C) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ * C ω) atTop (fun _ ↦ 0) := by
  have hb : IsBoundedInProbability μ (fun (_ : ℕ) ↦ C) :=
    isBoundedInProbability_of_tendstoInDistribution μ _ (Z := C) (μ' := μ)
      ⟨fun _ ↦ hC.aemeasurable, hC.aemeasurable, tendsto_const_nhds⟩
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine (tendstoInMeasure_mul_zero_of_isBoundedInProbability μ _ _ hb
    (tendstoInMeasure_const_of_tendsto μ _ hinv)).congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
  simp only [mul_comm]

/-- The remainder in the lag decomposition tends to zero in probability: the first `m - ℓ`
products are a fixed random variable divided by `√n`, and `√n (X̄ₙ - c)` is bounded in
probability by the central limit theorem while the centering remainder tends to zero. -/
private theorem tendstoInMeasure_lag_remainder {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure ℝ} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hiid : IsIndependentIdenticallyDistributed μ X P) (hP2 : MemLp id 2 P)
    (ℓ m : ℕ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦
      (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range (m - ℓ),
        (X (k + ℓ) ω - ∫ x, x ∂P) * (X k ω - ∫ x, x ∂P) +
        Real.sqrt n * (sampleAverage X n ω - ∫ x, x ∂P) *
          acovRemainder X (∫ x, x ∂P) ℓ n ω) atTop (fun _ ↦ 0) := by
  set c := ∫ x, x ∂P with hc
  have h1 := tendstoInMeasure_inv_sqrt_mul (μ := μ)
    (C := fun ω ↦ ∑ k ∈ Finset.range (m - ℓ), (X (k + ℓ) ω - c) * (X k ω - c))
    (Finset.measurable_fun_sum _ fun k _ ↦ ((hiid.1 _).sub_const c).mul
      ((hiid.1 _).sub_const c))
  have hc0 : ∫ x, (x - c) ∂P = 0 := by
    have hi' : Integrable (fun x : ℝ ↦ x) P := hP2.integrable one_le_two
    rw [integral_sub hi' (integrable_const c)]; simp [c]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid (fun x ↦ x - c)
    (by fun_prop) (hP2.sub (memLp_const c)) hc0
  have hb := isBoundedInProbability_of_tendstoInDistribution μ _ hclt
  have hb' : IsBoundedInProbability μ
      (fun (n : ℕ) ω ↦ Real.sqrt n * (sampleAverage X n ω - c)) := by
    have he : (fun (n : ℕ) ω ↦ Real.sqrt n * (sampleAverage X n ω - c)) =
        fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (X i ω - c) := by
      funext n ω; exact sqrt_mul_sampleAverage_sub X c n ω
    rw [he]; exact hb
  have h2 := tendstoInMeasure_mul_zero_of_isBoundedInProbability μ _ _ hb'
    (tendstoInMeasure_acovRemainder hiid hP2 ℓ)
  exact tendstoInMeasure_add_zero μ _ _ h1 h2
/-- GAPS 106.4, independent-observation case of Bartlett's theorem: for iid observations with
finite positive variance, the normalized sample autocorrelations
`√n ρ̂(h) = √n γ̂(h) / γ̂(0)` at lags `h = 1, …, m` converge jointly in law to independent
standard normal variables. Finite variance follows from `0 < Var`
(`memLp_id_two_of_variance_pos`). -/
theorem tendstoInDistribution_sample_autocorrelations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (hv : 0 < Var[id; P]) (m : ℕ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω / sampleAutocovariance X 0 n ω))
      atTop id (fun _ ↦ μ)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have hP2 : MemLp id 2 P := memLp_id_two_of_variance_pos hv
  set c := ∫ x, x ∂P with hc
  set σ2 := ∫ x, (x - c) ^ 2 ∂P with hσ2
  have hσ0 : 0 < σ2 := by
    have h := hv; rw [variance_eq_integral aemeasurable_id] at h; simpa [hσ2, hc] using h
  have hγm := measurable_sampleAutocovariance hiid.1
  have hVm : ∀ n : ℕ, Measurable fun ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω / sampleAutocovariance X 0 n ω :
      EuclideanSpace ℝ (Fin m)) := fun n ↦
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i ↦
      (measurable_const.mul (hγm _ n)).div (hγm 0 n))
  refine TendstoInDistribution.of_inner aemeasurable_id (fun n ↦ (hVm n).aemeasurable)
    fun t ↦ ?_
  set A : ℕ → Ω → ℝ := fun n ω ↦
    ∑ i : Fin m, t i * (Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω) with hA
  set M : ℕ → Ω → ℝ := fun n ω ↦ ∑ i ∈ Finset.range (n - m), (Real.sqrt n)⁻¹ *
    ((X (i + m) ω - c) * ∑ h : Fin m, t h * (X (i + (m - (h + 1))) ω - c)) with hM
  have hMd := tendstoInDistribution_sum_lag_martingale hiid hP2 m (fun i ↦ t i)
  have hR : TendstoInMeasure μ (fun n ω ↦ A n ω - M n ω) atTop (fun _ ↦ 0) := by
    have h := tendstoInMeasure_finsetSum_const Finset.univ fun (h : Fin m) _ ↦
      tendstoInMeasure_const_mul (tendstoInMeasure_of_tendsto_const (μ := μ)
        (tendsto_const_nhds (x := t h))) (tendstoInMeasure_lag_remainder hiid hP2 (h + 1) m)
    simp only [mul_zero, Finset.sum_const_zero, ← hc] at h
    refine h.congr' (eventually_ge_atTop m |>.mono fun n hn ↦ ae_of_all _ fun ω ↦ ?_)
      EventuallyEq.rfl
    simp only [hA, hM]
    rw [eq_sub_iff_add_eq]
    conv_rhs => rw [Finset.sum_congr rfl fun (h : Fin m) _ ↦ by
      rw [sqrt_mul_sampleAutocovariance_eq X c (by have := h.isLt; omega) hn ω]]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  have hRm : ∀ n, AEMeasurable (fun ω ↦ A n ω - M n ω) μ := fun n ↦ by
    refine (Measurable.sub ?_ ?_).aemeasurable
    · exact Finset.measurable_fun_sum _ fun i _ ↦ measurable_const.mul
        (measurable_const.mul (hγm _ n))
    · exact Finset.measurable_fun_sum _ fun i _ ↦ measurable_const.mul
        (((hiid.1 _).sub_const c).mul (Finset.measurable_fun_sum _ fun h _ ↦
          measurable_const.mul ((hiid.1 _).sub_const c)))
  have hAd := hMd.add_of_tendstoInMeasure_const hR hRm
  have hinv : TendstoInMeasure μ (fun n ω ↦ (sampleAutocovariance X 0 n ω)⁻¹) atTop
      (fun _ ↦ σ2⁻¹) :=
    tendstoInMeasure_comp_of_continuousAt μ _ σ2 Inv.inv (continuousAt_inv₀ hσ0.ne')
      (tendstoInMeasure_sampleAutocovariance_zero hiid hP2)
  have hT := hAd.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 * p.2) (by fun_prop) hinv
    (fun n ↦ (hγm 0 n).inv.aemeasurable)
  have hlaw : (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun z ↦ inner ℝ (id z) t) =
      (gaussianReal 0 (σ2 * σ2 * ∑ h : Fin m, t h ^ 2).toNNReal).map
        (fun ω ↦ (id ω + 0) * σ2⁻¹) := by
    have h1 : (fun z : EuclideanSpace ℝ (Fin m) ↦ inner ℝ (id z) t) = ⇑(innerSL ℝ t) := by
      funext z; simp [innerSL_apply_apply, real_inner_comm]
    have h2 : (fun ω : ℝ ↦ (id ω + 0) * σ2⁻¹) = (σ2⁻¹ * ·) := by
      funext ω; simp [mul_comm]
    rw [h1, h2, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm, gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    have hs : 0 ≤ σ2 * σ2 * ∑ h : Fin m, t h ^ 2 :=
      mul_nonneg (mul_self_nonneg σ2) (Finset.sum_nonneg fun h _ ↦ sq_nonneg _)
    have ht : 0 ≤ ∑ h : Fin m, t h ^ 2 := Finset.sum_nonneg fun h _ ↦ sq_nonneg _
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hs,
      EuclideanSpace.real_norm_sq_eq, Real.coe_toNNReal _ ht]
    field_simp
  refine (tendstoInDistribution_of_map_eq hT (by fun_prop) hlaw).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  simp only [PiLp.inner_apply, Pi.add_apply]
  change (M n ω + (A n ω - M n ω)) * _ = _
  rw [add_sub_cancel, hA, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.inner_apply, conj_trivial]
  ring

end CKSD
