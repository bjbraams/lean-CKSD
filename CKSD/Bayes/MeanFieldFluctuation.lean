module

public import CKSD.Bayes.MeanFieldCoupling

/-!
# Empirical interaction fluctuations

Bounded continuous interactions have measurable empirical fluctuations with almost surely
continuous paths. Their boundedness justifies Fubini when time-integrating mean-square bounds.
This module uses Mathlib product integration and the local jointly measurable process adapter.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD

/-- Fubini converts a uniform bound on expected continuous fluctuations into a bound on the
expected time-integrated fluctuation, retaining integrability of that time integral. -/
theorem integrable_integral_and_integral_le_mul_of_bounded_process
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℝ → Ω → ℝ) (hf : ∀ t, Measurable (f t)) (hf0 : ∀ t ω, 0 ≤ f t ω)
    (hfc : ∀ᵐ ω ∂P, Continuous (fun t ↦ f t ω))
    {T D B : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, f t ω ≤ D)
    (hmean : ∀ t ∈ Icc (0 : ℝ) T, (∫ ω, f t ω ∂P) ≤ B) :
    Integrable (fun ω ↦ ∫ t in (0 : ℝ)..T, f t ω) P ∧
      (∫ ω, (∫ t in (0 : ℝ)..T, f t ω) ∂P) ≤ T * B := by
  let ν := volume.restrict (Ioc (0 : ℝ) T)
  have hprod : Integrable (Function.uncurry f) (ν.prod P) := by
    apply Integrable.of_bound (aestronglyMeasurable_uncurry_of_ae_continuous P ν f hf hfc) D
    have htime : ∀ᵐ t ∂ν, t ∈ Ioc (0 : ℝ) T := ae_restrict_mem measurableSet_Ioc
    filter_upwards [(Measure.quasiMeasurePreserving_fst (ν := P)).ae htime,
      (Measure.quasiMeasurePreserving_snd (μ := ν)).ae hbound] with z hz hω
    change |f z.1 z.2| ≤ D
    rw [abs_of_nonneg (hf0 z.1 z.2)]
    exact hω z.1 ⟨hz.1.le, hz.2⟩
  have hint : Integrable (fun ω ↦ ∫ t in (0 : ℝ)..T, f t ω) P := by
    simpa only [intervalIntegral.integral_of_le hT, ν, Function.uncurry] using hprod.integral_prod_right
  have hswap : (∫ ω, (∫ t in (0 : ℝ)..T, f t ω) ∂P) =
      ∫ t in (0 : ℝ)..T, ∫ ω, f t ω ∂P := by
    simpa only [intervalIntegral.integral_of_le hT, ν, Function.uncurry] using (integral_integral_swap hprod).symm
  have htimeInt : IntervalIntegrable (fun t ↦ ∫ ω, f t ω ∂P) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hprod.integral_prod_left
  refine ⟨hint, ?_⟩
  rw [hswap]
  calc (∫ t in (0 : ℝ)..T, ∫ ω, f t ω ∂P) ≤ ∫ t in (0 : ℝ)..T, B :=
      intervalIntegral.integral_mono_on hT htimeInt (intervalIntegrable_const) hmean
    _ = T * B := by simp

/-- Empirical interaction fluctuation around the marginal law of the zeroth nonlinear copy. -/
def interactionFluctuation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (K : E → E → E) (Y : ℕ → ℝ → Ω → E)
    (N : ℕ) (i : Fin N) (t : ℝ) (ω : Ω) : E :=
  (N : ℝ)⁻¹ • ∑ j : Fin N, K (Y i t ω) (Y j t ω) - ∫ z, K (Y i t ω) (Y 0 t z) ∂P

/-- Empirical interaction fluctuations have measurable sections and almost surely continuous
paths whenever the nonlinear copies do and the interaction is bounded and continuous. -/
theorem interactionFluctuation_measurable_ae_continuous {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    (hK : Continuous (Function.uncurry K)) {κ : ℝ} (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (Y : ℕ → ℝ → Ω → E) (hYm : ∀ i t, Measurable (Y i t))
    (hYc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t ↦ Y i t ω)) (N : ℕ) :
    (∀ i t, Measurable (interactionFluctuation P K Y N i t)) ∧
      ∀ i, ∀ᵐ ω ∂P, Continuous (fun t ↦ interactionFluctuation P K Y N i t ω) := by
  have hv := continuous_integral_interaction P K hK hKb (Y 0) (hYm 0) (hYc 0)
  constructor
  · intro i t
    have hmean' : StronglyMeasurable (Function.uncurry (fun x z ↦ K x (Y 0 t z))) :=
      (hK.measurable.comp (measurable_fst.prodMk ((hYm 0 t).comp measurable_snd))).stronglyMeasurable
    have hmean : Measurable (fun x ↦ ∫ z, K x (Y 0 t z) ∂P) := hmean'.integral_prod_right.measurable
    change Measurable (fun ω ↦ (N : ℝ)⁻¹ • ∑ j : Fin N, K (Y i t ω) (Y j t ω) - ∫ z, K (Y i t ω) (Y 0 t z) ∂P)
    exact ((Finset.measurable_sum (Finset.univ : Finset (Fin N)) fun j _ ↦
      hK.measurable.comp ((hYm i t).prodMk (hYm j t))).const_smul _).sub (hmean.comp (hYm i t))
  · intro i
    filter_upwards [ae_all_iff.2 hYc] with ω hω
    change Continuous (fun t ↦ (N : ℝ)⁻¹ • ∑ j : Fin N, K (Y i t ω) (Y j t ω) - ∫ z, K (Y i t ω) (Y 0 t z) ∂P)
    exact ((continuous_finsetSum (Finset.univ : Finset (Fin N)) fun j _ ↦ hK.comp ((hω i).prodMk (hω j))).const_smul _).sub
      (hv.comp (continuous_id.prodMk (hω i)))

/-- A bounded interaction gives an absolute bound on the empirical fluctuation, independent
of the sample size and configuration. -/
theorem norm_interactionFluctuation_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    {κ : ℝ} (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (Y : ℕ → ℝ → Ω → E) {N : ℕ} (hN : 0 < N) (i : Fin N) (t : ℝ) (ω : Ω) :
    ‖interactionFluctuation P K Y N i t ω‖ ≤ 2 * κ := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have havg : ‖(N : ℝ)⁻¹ • ∑ j : Fin N, K (Y i t ω) (Y j t ω)‖ ≤ κ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    calc (N : ℝ)⁻¹ * ‖∑ j : Fin N, K (Y i t ω) (Y j t ω)‖ ≤
          (N : ℝ)⁻¹ * ∑ j : Fin N, ‖K (Y i t ω) (Y j t ω)‖ := by
            gcongr
            exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ j : Fin N, κ := by gcongr with j; exact hKb _ _
      _ = κ := by simp [hN0]
  exact (norm_sub_le _ _).trans (by
    have hm := norm_integral_interaction_le P K hKb (Y 0 t) (Y i t ω)
    linarith)

/-- Pointwise mean-square fluctuation bounds integrate over bounded time intervals, with
integrability justified by bounded interactions and continuous nonlinear paths. -/
theorem integrable_integral_sq_interactionFluctuation_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    (hK : Continuous (Function.uncurry K)) {κ : ℝ} (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (Y : ℕ → ℝ → Ω → E) (hYm : ∀ i t, Measurable (Y i t))
    (hYc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t ↦ Y i t ω))
    {N : ℕ} (hN : 0 < N) (i : Fin N) {T B : ℝ} (hT : 0 ≤ T)
    (hmean : ∀ t ∈ Icc (0 : ℝ) T, (∫ ω, ‖interactionFluctuation P K Y N i t ω‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ω ↦ ∫ t in (0 : ℝ)..T, ‖interactionFluctuation P K Y N i t ω‖ ^ 2) P ∧
      (∫ ω, (∫ t in (0 : ℝ)..T, ‖interactionFluctuation P K Y N i t ω‖ ^ 2) ∂P) ≤ T * B := by
  have hm := interactionFluctuation_measurable_ae_continuous P K hK hKb Y hYm hYc N
  apply integrable_integral_and_integral_le_mul_of_bounded_process P
    (fun t ω ↦ ‖interactionFluctuation P K Y N i t ω‖ ^ 2)
    (fun t ↦ (hm.1 i t).norm.pow_const 2) (fun _ _ ↦ sq_nonneg _)
    ((hm.2 i).mono fun ω hω ↦ hω.norm.pow 2) hT (D := (2 * κ) ^ 2) _ hmean
  exact ae_of_all _ fun ω t _ ↦ by
    have hb := norm_interactionFluctuation_le P K hKb Y hN i t ω
    have hb0 : 0 ≤ 2 * κ := (norm_nonneg _).trans hb
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end CKSD
