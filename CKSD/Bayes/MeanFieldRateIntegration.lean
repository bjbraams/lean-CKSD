module
public import CKSD.Bayes.Basic
/-!
# Integrating individual and averaged error bounds

A uniform bound on each residual's expectation controls the expectation of an individual
residual plus the empirical average. Extended nonnegative integrals then give the same bound
for squared errors uniformly over any time set. The supremum need not be measurable.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- An individual plus an averaged residual bound integrates to twice the common mean bound. -/
theorem lintegral_le_of_individual_add_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (i : Fin N) (f : Fin N → Ω → ℝ)
    (hf : ∀ j, Integrable (f j) P) (hnn : ∀ j, ∀ᵐ ω ∂P, 0 ≤ f j ω)
    (A B : ℝ) (hA : 0 ≤ A) (hmean : ∀ j, ∫ ω, f j ω ∂P ≤ B)
    (g : Ω → ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂P, g ω ≤ ENNReal.ofReal (A *
      (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω))) :
    ∫⁻ ω, g ω ∂P ≤ ENNReal.ofReal (2 * A * B) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : Integrable (fun ω ↦ ∑ j, f j ω) P := integrable_finsetSum _ fun j _ ↦ hf j
  have hu : Integrable (fun ω ↦ A * (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω)) P :=
    ((hf i).add (hs.const_mul _)).const_mul A
  have hunn : ∀ᵐ ω ∂P, 0 ≤ A * (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω) := by
    filter_upwards [ae_all_iff.2 hnn] with ω hω
    exact mul_nonneg hA (add_nonneg (hω i)
      (mul_nonneg (inv_nonneg.mpr hNR.le) (Finset.sum_nonneg fun j _ ↦ hω j)))
  have hsum : (∫ ω, ∑ j, f j ω ∂P) ≤ (N : ℝ) * B := by
    rw [integral_finsetSum _ fun j _ ↦ hf j]
    calc (∑ j : Fin N, ∫ ω, f j ω ∂P) ≤ ∑ _j : Fin N, B :=
          Finset.sum_le_sum fun j _ ↦ hmean j
      _ = _ := by simp
  have havg : (N : ℝ)⁻¹ * (∫ ω, ∑ j, f j ω ∂P) ≤ B := by
    calc _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNR.le)
      _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul]
  calc (∫⁻ ω, g ω ∂P) ≤ ∫⁻ ω, ENNReal.ofReal (A *
        (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω)) ∂P := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (∫ ω, A * (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hu hunn).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul, integral_add (hf i) (hs.const_mul _), integral_const_mul]
      calc _ ≤ A * (B + B) := mul_le_mul_of_nonneg_left (add_le_add (hmean i) havg) hA
        _ = _ := by ring

/-- An almost-sure squared-error bound integrates uniformly over an arbitrary time set. -/
theorem lintegral_iSup_enorm_sq_le_of_individual_add_average_bound
    {Ω ι E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) {N : ℕ} (i : Fin N) (f : Fin N → Ω → ℝ)
    (hf : ∀ j, Integrable (f j) P) (hnn : ∀ j, ∀ᵐ ω ∂P, 0 ≤ f j ω)
    (A B : ℝ) (hA : 0 ≤ A) (hmean : ∀ j, ∫ ω, f j ω ∂P ≤ B)
    (g : Ω → ι → E) (S : Set ι)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ S, ‖g ω t‖ ^ 2 ≤ A *
      (f i ω + (N : ℝ)⁻¹ * ∑ j, f j ω)) :
    ∫⁻ ω, ⨆ t ∈ S, ‖g ω t‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (2 * A * B) := by
  apply lintegral_le_of_individual_add_average_bound P i f hf hnn A B hA hmean
  filter_upwards [hbound] with ω hω
  refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hω t ht)
end CKSD
