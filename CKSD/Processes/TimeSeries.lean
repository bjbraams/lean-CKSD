module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Processes: TimeSeries

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
The long-run variance limit regroups the double covariance sum by lag and applies Mathlib's
dominated convergence theorem for series (Tannery's theorem).
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 106.1: triangular-array martingale central limit theorem. -/
theorem tendstoInDistribution_martingale_array_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ha : ∀ n j, Measurable[F n (j + 1)] (X n j))
    (h2 : ∀ n j, MemLp (X n j) 2 μ)
    (h0 : ∀ n j, μ[X n j | F n j] =ᵐ[μ] fun _ ↦ 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hvar : TendstoInProbabilityConst μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n), μ[(fun ω ↦ X n j ω ^ 2) | F n j] ω) v)
    (hlin : ∀ ε > 0, TendstoInProbabilityConst μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n),
        μ[(fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0) | F n j] ω) 0) :
    TendstoInDistribution μ (fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω)
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

/-- GAPS 106.2, Wold decomposition of a stationary sequence in a real Hilbert space. -/
theorem exists_wold_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (X : ℤ → H)
    (hstat : ∀ s t, inner ℝ (X s) (X t) = inner ℝ (X (s - t)) (X 0)) :
    let past := fun t ↦ (Submodule.span ℝ {x | ∃ s : ℤ, s ≤ t ∧ x = X s}).topologicalClosure;
    ∀ (P : ℤ → H →L[ℝ] H),
    ∀ (hproj : ∀ t x, P t x ∈ past t ∧ ∀ y ∈ past t, inner ℝ (x - P t x) y = 0),
    let e := fun t ↦ X t - P (t - 1) (X t);
    ∀ (he : 0 < ‖e 0‖),
    ∃ (a : ℕ → ℝ) (V : ℤ → H), a 0 = 1 ∧ Summable (fun j ↦ a j ^ 2) ∧
      (∀ t s, V t ∈ past s) ∧ (∀ t s, inner ℝ (V t) (e s) = 0) ∧
      ∀ t, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j • e (t - j)) + V t) atTop (𝓝 (X t)) := by
  sorry

/-- GAPS 106.4, independent-observation special case of Bartlett's theorem. -/
theorem tendstoInDistribution_sample_autocorrelations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (m : ℕ) :
    TendstoInDistribution μ (fun n ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω / sampleAutocovariance X 0 n ω))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry

/-- The lag-counting weight `#{(i, j) : i, j < n, i - j = h} / n`. -/
def lagCountWeight (n : ℕ) (h : ℤ) : ℝ :=
  (((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card : ℝ) / n

/-- A normalized double sum over `i, j < n` of a function of `i - j`, regrouped by lag. -/
theorem sum_sum_eq_tsum_lagCountWeight (γ : ℤ → ℝ) (n : ℕ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ ((i : ℤ) - j) =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
  classical
  let s := Finset.range n ×ˢ Finset.range n
  let g : ℕ × ℕ → ℤ := fun p ↦ (p.1 : ℤ) - p.2
  have hsupp : ∀ h ∉ s.image g, lagCountWeight n h * γ h = 0 := by
    intro h hh
    have : (s.filter fun p ↦ g p = h) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hp hgp
      exact hh (Finset.mem_image.2 ⟨p, hp, hgp⟩)
    simp [lagCountWeight, s, g, this]
  have hfib : ∑ p ∈ s, γ (g p) =
      ∑ h ∈ s.image g, ((s.filter fun p ↦ g p = h).card : ℝ) * γ h := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun p hp ↦ Finset.mem_image_of_mem g hp)]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [Finset.sum_congr rfl (g := fun _ ↦ γ h) (fun p hp ↦ by
      show γ (g p) = γ h
      rw [(Finset.mem_filter.1 hp).2])]
    simp
  rw [tsum_eq_sum hsupp, ← Finset.sum_product']
  change (n : ℝ)⁻¹ * ∑ p ∈ s, γ (g p) = _
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [lagCountWeight, s, g]
  ring

/-- Lag-counting weights are nonnegative. -/
theorem lagCountWeight_nonneg (n : ℕ) (h : ℤ) : 0 ≤ lagCountWeight n h := by
  unfold lagCountWeight; positivity

/-- Lag-counting weights are at most one. -/
theorem lagCountWeight_le_one (n : ℕ) (h : ℤ) : lagCountWeight n h ≤ 1 := by
  unfold lagCountWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [div_le_one (by exact_mod_cast hn)]
  have : ((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card
      ≤ (Finset.range n).card := by
    refine Finset.card_le_card_of_injOn Prod.snd (fun p hp ↦ ?_) ?_
    · simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range] at hp
      simpa using hp.1.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      have : (p.1 : ℤ) = q.1 := by rw [← hpq] at hq; linarith [hp.2, hq.2]
      exact Prod.ext (by exact_mod_cast this) hpq
  simpa using (Nat.cast_le (α := ℝ)).2 this

/-- The lower bound `(n - |h|)/n` for the lag-counting weight. -/
theorem le_lagCountWeight (n : ℕ) (h : ℤ) :
    ((n - (h.toNat + (-h).toNat) : ℕ) : ℝ) / n ≤ lagCountWeight n h := by
  unfold lagCountWeight
  gcongr
  refine (Finset.card_range _).symm.le.trans ?_
  refine Finset.card_le_card_of_injOn (fun j ↦ (j + h.toNat, j + (-h).toNat)) (fun j hj ↦ ?_) ?_
  · simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, by push_cast; omega⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    omega

/-- Lag-counting weights tend to one at each fixed lag. -/
theorem tendsto_lagCountWeight (h : ℤ) : Tendsto (fun n ↦ lagCountWeight n h) atTop (𝓝 1) := by
  set a := h.toNat + (-h).toNat
  have hlow : Tendsto (fun n : ℕ ↦ ((n - a : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 - (a : ℝ) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)).const_sub 1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (a + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Nat.cast_sub (by omega)]
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n ↦ le_lagCountWeight n h) (fun n ↦ lagCountWeight_le_one n h)


/-- GAPS 106.12, long-run variance from summable autocovariances. -/
theorem tendsto_normalized_variance_eq_tsum_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ)
    (h2 : ∀ t, MemLp (X t) 2 μ) (γ : ℤ → ℝ) (hγ : Summable (fun t ↦ |γ t|))
    (hcov : ∀ s t, covariance μ (X s) (X t) = γ (s - t)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * variance μ (sampleAverage (fun j ↦ X j) n))
      atTop (𝓝 (∑' h : ℤ, γ h)) := by
  have hrepr : ∀ n : ℕ, 0 < n → (n : ℝ) * variance μ (sampleAverage (fun j ↦ X j) n) =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
    intro n hn
    rw [← sum_sum_eq_tsum_lagCountWeight]
    have havg : sampleAverage (fun j : ℕ ↦ X j) n =
        fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [sampleAverage, smul_eq_mul]
    have hvar : variance μ (sampleAverage (fun j : ℕ ↦ X j) n) =
        ProbabilityTheory.covariance (sampleAverage (fun j : ℕ ↦ X j) n)
          (sampleAverage (fun j : ℕ ↦ X j) n) μ := by
      simp only [variance, ProbabilityTheory.covariance, sq]
    rw [hvar, havg, covariance_const_mul_left, covariance_const_mul_right,
      covariance_fun_sum_fun_sum' (X := fun i : ℕ ↦ X i) (Y := fun i : ℕ ↦ X i)
      (fun i _ ↦ h2 i) (fun i _ ↦ h2 i)]
    simp only [show ∀ s t, ProbabilityTheory.covariance (X s) (X t) μ = γ (s - t) from hcov]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun n h ↦ lagCountWeight n h * γ h)
    (g := γ) (bound := fun h ↦ |γ h|) hγ
    (fun h ↦ by simpa using (tendsto_lagCountWeight h).mul_const (γ h))
    (Eventually.of_forall fun n h ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lagCountWeight_nonneg n h)]
      exact mul_le_of_le_one_left (abs_nonneg _) (lagCountWeight_le_one n h))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn using (hrepr n hn).symm

/-- GAPS 106.14, real Gaussian realization of a positive-definite stationary covariance. -/
theorem exists_stationary_gaussian_process_of_posSemidef (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    ∃ P : Measure (ℤ → ℝ), IsProbabilityMeasure P ∧
      (∀ h : ℤ, P.map (fun x t ↦ x (t + h)) = P) ∧
      ∀ n : ℕ, ∀ t : Fin n → ℤ,
        P.map (fun x ↦ WithLp.toLp 2 (fun i : Fin n ↦ x (t i))) =
          multivariateGaussian 0 (fun i j ↦ γ (t i - t j)) := by
  sorry

/-- GAPS 106.18, finite-variance GARCH series when `alpha + beta < 1`. -/
theorem garch_series_summable_and_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1)
    (a₀ a b : ℝ) (ha₀ : 0 < a₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) :
    let V := fun t ω ↦ a₀ * ∑' n : ℕ,
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2);
    let X := fun t ω ↦ Real.sqrt (V t ω) * ε t ω;
    (∀ t, ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2))) ∧
      (∀ t, (∫ ω, V t ω ∂μ) = a₀ / (1 - a - b)) ∧
      (∀ t, ∀ᵐ ω ∂μ, V t ω = a₀ + a * X (t - 1) ω ^ 2 + b * V (t - 1) ω) ∧
      ∀ s t, covariance μ (X s) (X t) = if s = t then a₀ / (1 - a - b) else 0 := by
  sorry


end CKSD
