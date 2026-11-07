module

public import CKSD.Nonparametric.Basic

/-!
# Nonparametric: Estimation

Sources: `GAPS.md`, `SYNOPSIS103.md`, and `STRUCTURE103.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common rank measurable structure.
attribute [local instance] rankMeasurableSpace

/-- GAPS 103.1, finite-sample Dvoretzky–Kiefer–Wolfowitz–Massart bound. -/
theorem measure_kolmogorovSmirnovStatistic_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < Real.sqrt n * kolmogorovSmirnovStatistic X P n ω} ≤ 2 * Real.exp
      (-2 * t ^ 2) := by
  sorry

/-- GAPS 103.4, pointwise bias-corrected kernel-density central limit theorem. -/
theorem tendstoInDistribution_kernelDensityEstimator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hf2 : ContDiff ℝ 2 f)
    (hL2 : MemLp f 2 volume) (hD2 : MemLp (deriv (deriv f)) 2 volume)
    (hDb : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C)
    (hKm : Measurable K) (hKpos : ∀ x, 0 ≤ K x) (hKsym : ∀ x, K (-x) = K x)
    (hKb : ∃ C, ∀ x, K x ≤ C) (hKi : Integrable K volume)
    (hK1 : (∫ x, K x) = 1) (hK2 : Integrable (fun x ↦ x ^ 2 * K x) volume)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop)
    (hnh5 : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ^ 5 ≤ C)
    (t : ℝ) (ht : 0 < f t) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt ((n : ℝ) * h n) *
      (kernelDensityEstimator X K h n ω t - f t - h n ^ 2 / 2 *
        (∫ u, u ^ 2 * K u) * deriv (deriv f) t))
      (gaussianReal 0 (Real.toNNReal ((∫ u, K u ^ 2) * f t))) := by
  sorry

/-- GAPS 103.5, one-dimensional universal almost-sure L1 consistency. -/
theorem ae_tendsto_integral_abs_kernelDensityEstimator_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hKm : Measurable K) (hKi : Integrable K volume)
    (hK1 : (∫ x, K x) = 1) (hKb : ∃ C, ∀ x, |K x| ≤ C)
    (hKc : ∃ R > 0, ∀ x, R < |x| → K x = 0)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ t, |kernelDensityEstimator X K h n ω t - f t|) atTop (𝓝 0) := by
  sorry

/-- GAPS 103.8, representer theorem in its Hilbert feature-vector formulation. -/
theorem minimizer_mem_span_of_feature_vectors
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {n : ℕ} (v : Fin n → H) (y : Fin n → ℝ)
    (L : ℝ → ℝ → ℝ) (lambda : ℝ) (hlambda : 0 < lambda) (f : H)
    (hmin : ∀ g : H, (∑ i, L (y i) (inner ℝ f (v i))) + lambda * ‖f‖ ^ 2 ≤
      (∑ i, L (y i) (inner ℝ g (v i))) + lambda * ‖g‖ ^ 2) :
    f ∈ Submodule.span ℝ (range v) := by
  let S := Submodule.span ℝ (range v)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (finite_range v)
  have hinner (i : Fin n) : inner ℝ (S.starProjection f) (v i) = inner ℝ f (v i) := by
    have h := S.starProjection_inner_eq_zero f (v i) (Submodule.subset_span (mem_range_self i))
    rw [inner_sub_left] at h
    exact (sub_eq_zero.mp h).symm
  have h := hmin (S.starProjection f)
  simp_rw [hinner] at h
  have hnorm := S.norm_starProjection_apply_le f
  apply (S.mem_iff_norm_starProjection f).mpr
  have hs : ‖f‖ ^ 2 ≤ ‖S.starProjection f‖ ^ 2 :=
    (mul_le_mul_iff_right₀ hlambda).mp (by linarith only [h])
  nlinarith [norm_nonneg f, norm_nonneg (S.starProjection f)]

/-- Summing `f (σ i)` over all permutations: `n * ∑_σ f (σ i) = n! * ∑_k f k`. -/
theorem natCast_mul_sum_perm_apply {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (n : ℝ) * ∑ σ : Equiv.Perm (Fin n), f (σ i) = n.factorial * ∑ k, f k := by
  have hind : ∀ i' : Fin n, ∑ σ : Equiv.Perm (Fin n), f (σ i') =
      ∑ σ : Equiv.Perm (Fin n), f (σ i) := by
    intro i'
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i i')) _ _ fun σ ↦ ?_
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  calc (n : ℝ) * ∑ σ : Equiv.Perm (Fin n), f (σ i)
      = ∑ i' : Fin n, ∑ σ : Equiv.Perm (Fin n), f (σ i') := by
        rw [Finset.sum_congr rfl fun i' _ ↦ hind i', Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ k, f k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ ↦ Equiv.sum_comp σ f
    _ = n.factorial * ∑ k, f k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]

/-- Summing `a (σ i) a (σ j)` over permutations for `i ≠ j`. -/
theorem natCast_mul_sum_perm_apply_mul_apply {n : ℕ} (a : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) :
    (n : ℝ) * (n - 1) * ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) =
      n.factorial * ((∑ k, a k) ^ 2 - ∑ k, a k ^ 2) := by
  set F := fun j' : Fin n ↦ ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j') with hF
  have hind : ∀ j', j' ≠ i → F j' = F j := by
    intro j' hj'
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j j')) _ _ fun σ ↦ ?_
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne hij hj'.symm]
  have hdiag : (n : ℝ) * F i = n.factorial * ∑ k, a k ^ 2 := by
    have := natCast_mul_sum_perm_apply (fun k ↦ a k ^ 2) i
    simpa [hF, sq] using this
  have htot : (n : ℝ) * ∑ j', F j' = n.factorial * (∑ k, a k) ^ 2 := by
    have hsum : ∑ j', F j' = ∑ σ : Equiv.Perm (Fin n), a (σ i) * ∑ k, a k := by
      simp only [hF]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      rw [← Finset.mul_sum, Equiv.sum_comp σ a]
    rw [hsum, ← Finset.sum_mul, ← mul_assoc, natCast_mul_sum_perm_apply a i]
    ring
  have hsplit : ∑ j', F j' = F i + ((n : ℝ) - 1) * F j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    rw [Finset.sum_congr rfl fun j' hj' ↦ hind j' (Finset.ne_of_mem_erase hj'),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact i.elim0)
    push_cast [this]
    ring
  rw [hsplit] at htot
  change (n : ℝ) * (n - 1) * F j = _
  linear_combination htot - hdiag

/-- GAPS 103.14, the exact mean and variance under uniform ranks. -/
theorem linear_rank_statistic_mean_and_variance (n : ℕ) (hn : 2 ≤ n) (a c : Fin n → ℝ) :
    let P := ((Nat.factorial n : ℝ≥0∞)⁻¹) •
      (Measure.count : Measure (Equiv.Perm (Fin n)));
    let abar := (∑ i, a i) / n;
    let cbar := (∑ i, c i) / n;
    let T := fun σ : Equiv.Perm (Fin n) ↦ ∑ i, c i * a (σ i);
    (∫ σ, T σ ∂P) = (n : ℝ) * abar * cbar ∧
      variance P T = (∑ i, (c i - cbar) ^ 2) *
        (∑ i, (a i - abar) ^ 2) / (n - 1 : ℕ) := by
  intro P abar cbar T
  have : MeasurableSingletonClass (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hint : ∀ g : Equiv.Perm (Fin n) → ℝ,
      ∫ σ, g σ ∂P = (n.factorial : ℝ)⁻¹ * ∑ σ, g σ := by
    intro g
    simp only [P]
    rw [integral_smul_measure, integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  set A := ∑ k, a k
  set C := ∑ k, c k
  set Sa := ∑ k, a k ^ 2
  set Sc := ∑ k, c k ^ 2
  -- first moments
  have hsum1 : ∀ i, ∑ σ : Equiv.Perm (Fin n), a (σ i) = n.factorial * A / n := by
    intro i
    rw [eq_div_iff hn0, mul_comm, natCast_mul_sum_perm_apply]
  have hmean : ∫ σ, T σ ∂P = A * C / n := by
    rw [hint]
    simp only [T]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsum1, ← Finset.sum_mul]
    field_simp
    simp only [C]
    ring
  -- second moments
  have hsum2 : ∀ i j, ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) =
      if i = j then n.factorial * Sa / n
      else n.factorial * (A ^ 2 - Sa) / (n * (n - 1)) := by
    intro i j
    split_ifs with h
    · subst h
      rw [eq_div_iff hn0, mul_comm]
      simp only [← sq]
      exact natCast_mul_sum_perm_apply (fun k ↦ a k ^ 2) i
    · rw [eq_div_iff (mul_ne_zero hn0 hn1), mul_comm]
      exact natCast_mul_sum_perm_apply_mul_apply a i j h
  have hsq : ∑ σ, T σ ^ 2 = Sc * (n.factorial * Sa / n) +
      (C ^ 2 - Sc) * (n.factorial * (A ^ 2 - Sa) / (n * (n - 1))) := by
    set K : ℝ := n.factorial * (A ^ 2 - Sa) / (n * (n - 1)) with hK
    set D : ℝ := n.factorial * Sa / n with hD
    have hexpand : ∑ σ, T σ ^ 2 =
        ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j)) := by
      simp only [T, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_comm]
    have hterm : ∀ i j, ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j)) =
        c i * c j * K + if i = j then c i * c j * (D - K) else 0 := by
      intro i j
      have h2 := hsum2 i j
      calc ∑ σ : Equiv.Perm (Fin n), c i * a (σ i) * (c j * a (σ j))
          = c i * c j * ∑ σ : Equiv.Perm (Fin n), a (σ i) * a (σ j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun σ _ ↦ by ring
        _ = _ := by rw [h2]; split_ifs <;> ring
    rw [hexpand]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h1 : ∑ i, ∑ j, c i * c j * K = C ^ 2 * K := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_mul]
    have h2 : ∑ i, c i * c i * (D - K) = Sc * (D - K) := by
      rw [Finset.sum_mul]; simp only [sq]
    rw [h1, h2]
    ring
  have hvar : variance P T = (n.factorial : ℝ)⁻¹ * ∑ σ, T σ ^ 2 - (A * C / n) ^ 2 := by
    unfold variance
    rw [hmean, hint]
    have hexp : ∀ σ, (T σ - A * C / n) ^ 2 =
        T σ ^ 2 - 2 * (A * C / n) * T σ + (A * C / n) ^ 2 := fun σ ↦ by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have hm := hmean
    rw [hint] at hm
    rw [mul_add, mul_sub, ← mul_assoc _ (2 * (A * C / n)), mul_comm _ (2 * (A * C / n)),
      mul_assoc, hm]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hmean]; simp only [abar, cbar, A, C]; field_simp
  · rw [hvar, hsq]
    have hc : ∑ i, (c i - cbar) ^ 2 = Sc - C ^ 2 / n := by
      simp only [cbar, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    have ha : ∑ i, (a i - abar) ^ 2 = Sa - A ^ 2 / n := by
      simp only [abar, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    rw [hc, ha]
    have : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    field_simp
    ring


end CKSD
