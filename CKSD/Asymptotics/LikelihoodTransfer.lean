module
public import CKSD.Asymptotics.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
/-!
# Weighted weak convergence

Truncation gives convergence of weighted bounded continuous integrals when the
nonnegative continuous weights have mass at most one and limiting mass one.
This is the change-of-law argument in van der Vaart, *Asymptotic Statistics*,
Lemma 6.4 and the proof of Theorem 7.10. The integral-one interface is retained
as a specialization.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
attribute [local instance] Classical.propDecidable
/-- Truncation `x ↦ max 0 (min x k)` as a bounded continuous function. -/
def clipBCF (k : ℝ) (hk : 0 ≤ k) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x ↦ max 0 (min x k), by fun_prop⟩ (2 * k) (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 : 0 ≤ max 0 (min x k) ∧ max 0 (min x k) ≤ k := ⟨le_max_left _ _, max_le hk (min_le_right _ _)⟩
    have h2 : 0 ≤ max 0 (min y k) ∧ max 0 (min y k) ≤ k := ⟨le_max_left _ _, max_le hk (min_le_right _ _)⟩
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

/-- Weighted weak convergence: if probability measures `μₙ` converge weakly to `ν` and a
continuous nonnegative weight `w` is integrable with integral at most one under every `μₙ`
and integral one under `ν`, then
`∫ w f dμₙ → ∫ w f dν` for bounded continuous `f`. -/
theorem tendsto_integral_mul_of_tendsto_of_integral_le_one {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)] (ν : Measure X)
    [IsProbabilityMeasure ν]
    (h : Tendsto (β := ProbabilityMeasure X) (fun n ↦ ⟨μs n, inferInstance⟩) atTop
      (𝓝 ⟨ν, inferInstance⟩))
    (w : X → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hμint : ∀ n, Integrable w (μs n))
    (hμw : ∀ n, ∫ x, w x ∂μs n ≤ 1) (hνw : ∫ x, w x ∂ν = 1)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n ↦ ∫ x, w x * f x ∂μs n) atTop (𝓝 (∫ x, w x * f x ∂ν)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h
  simp only [ProbabilityMeasure.coe_mk] at h
  have hwint := hμint
  have hνint : Integrable w ν := by
    by_contra hni; rw [integral_undef hni] at hνw; exact zero_ne_one hνw
  -- truncations
  let t : ℕ → BoundedContinuousFunction X ℝ := fun k ↦
    (clipBCF k (Nat.cast_nonneg k)).compContinuous ⟨w, hw⟩
  have ht : ∀ k x, t k x = min (w x) k := fun k x ↦ by
    simp [t, clipBCF, hw0 x]
  have htint : ∀ (m : Measure X) [IsProbabilityMeasure m] k, Integrable (t k) m :=
    fun m _ k ↦ (t k).integrable m
  -- Tail control by the missing mass of a bounded truncation.
  have herr : ∀ (m : Measure X) [IsProbabilityMeasure m], Integrable w m → ∫ x, w x ∂m ≤ 1 →
      ∀ k : ℕ, |∫ x, w x * f x ∂m - ∫ x, t k x * f x ∂m| ≤ ‖f‖ * (1 - ∫ x, t k x ∂m) := by
    intro m _ hwm h1 k
    have hi1 : Integrable (fun x ↦ w x * f x) m := hwm.mul_bdd f.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
    have hi2 : Integrable (fun x ↦ t k x * f x) m := (htint m k).mul_bdd
      f.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ f.norm_coe_le_norm x)
    have hi3 : Integrable (fun x ↦ ‖f‖ * (w x - t k x)) m := (hwm.sub (htint m k)).const_mul _
    rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hi3 (ae_of_all _ fun x ↦ ?_)).trans ?_
    · have hle : t k x ≤ w x := by rw [ht]; exact min_le_left _ _
      rw [← sub_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle), mul_comm]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (sub_nonneg.2 hle)
    · rw [integral_const_mul, integral_sub hwm (htint m k)]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right h1 _) (norm_nonneg f)
  have hD : Tendsto (fun k : ℕ ↦ ∫ x, t k x ∂ν) atTop (𝓝 (∫ x, w x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence w (fun k ↦ (t k).continuous.aestronglyMeasurable)
      hνint (fun k ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · rw [ht, Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 x) (Nat.cast_nonneg k))]
      exact min_le_left _ _
    · have : ∀ᶠ k : ℕ in atTop, t k x = w x := by
        filter_upwards [eventually_ge_atTop ⌈w x⌉₊] with k hk
        rw [ht]; exact min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hk))
      exact tendsto_const_nhds.congr' (this.mono fun k hk ↦ hk.symm)
  rw [hνw] at hD
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfn : 0 ≤ ‖f‖ := norm_nonneg f
  have hD' : Tendsto (fun k : ℕ ↦ ‖f‖ * (1 - ∫ x, t k x ∂ν)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hD).const_mul ‖f‖
  obtain ⟨k, hk⟩ := (hD'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have h1 : Tendsto (fun n ↦ ‖f‖ * (1 - ∫ x, t k x ∂μs n)) atTop
      (𝓝 (‖f‖ * (1 - ∫ x, t k x ∂ν))) := ((tendsto_const_nhds.sub (h (t k))).const_mul ‖f‖)
  have h2 := h (t k * f)
  simp only [FunLike.coe_mul, Pi.mul_apply] at h2
  filter_upwards [h1.eventually (gt_mem_nhds hk), Metric.tendsto_nhds.1 h2 (ε / 4) (by positivity)]
    with n hn1 hn2
  have e1 := herr (μs n) (hwint n) (hμw n) k
  have e2 := herr ν hνint hνw.le k
  rw [Real.dist_eq] at hn2 ⊢
  calc |∫ x, w x * f x ∂μs n - ∫ x, w x * f x ∂ν|
      ≤ |∫ x, w x * f x ∂μs n - ∫ x, t k x * f x ∂μs n| +
        |∫ x, t k x * f x ∂μs n - ∫ x, t k x * f x ∂ν| +
        |∫ x, w x * f x ∂ν - ∫ x, t k x * f x ∂ν| := by
          have := abs_sub_le (∫ x, w x * f x ∂μs n) (∫ x, t k x * f x ∂μs n) (∫ x, w x * f x ∂ν)
          have := abs_sub_le (∫ x, t k x * f x ∂μs n) (∫ x, t k x * f x ∂ν) (∫ x, w x * f x ∂ν)
          rw [abs_sub_comm (∫ x, t k x * f x ∂ν)] at this
          linarith
    _ < ε := by linarith

/-- Weighted weak convergence: if probability measures `μₙ` converge weakly to `ν` and a
continuous nonnegative weight `w` has integral one under every `μₙ` and under `ν`, then
`∫ w f dμₙ → ∫ w f dν` for bounded continuous `f`. -/
theorem tendsto_integral_mul_of_tendsto {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μs : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μs n)] (ν : Measure X)
    [IsProbabilityMeasure ν]
    (h : Tendsto (β := ProbabilityMeasure X) (fun n ↦ ⟨μs n, inferInstance⟩) atTop
      (𝓝 ⟨ν, inferInstance⟩))
    (w : X → ℝ) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hμw : ∀ n, ∫ x, w x ∂μs n = 1) (hνw : ∫ x, w x ∂ν = 1)
    (f : BoundedContinuousFunction X ℝ) :
    Tendsto (fun n ↦ ∫ x, w x * f x ∂μs n) atTop (𝓝 (∫ x, w x * f x ∂ν)) := by
  apply tendsto_integral_mul_of_tendsto_of_integral_le_one μs ν h w hw hw0 ?_
    (fun n ↦ (hμw n).le) hνw f
  intro n
  by_contra hni
  have ht := hμw n
  rw [integral_undef hni] at ht
  exact zero_ne_one ht


end CKSD
