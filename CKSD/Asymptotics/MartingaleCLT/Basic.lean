module

public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.Lindeberg.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# Martingale central limit theorem: bounded conditional variances

Infrastructure for the martingale central limit theorem for triangular arrays of
martingale differences (GAPS 106.1, `CKSD.tendstoInDistribution_martingale_array_sum`).

The proof follows B. M. Brown (1971). For a row of martingale differences `Xⱼ` with conditional
variances `σⱼ²` and partial sums `Sₖ`, `Vₖ = ∑_{j<k} σⱼ²`, the products
`Zₖ = exp (i t Sₖ + t² Vₖ / 2)` satisfy `‖𝔼 Zₖ₊₁ - 𝔼 Zₖ‖ ≤ exp (t² B / 2) (𝔼 (t² σₖ² / 2)² +
|t|³ ε 𝔼 σₖ² / 3 + 2 t² 𝔼 ℓₖ)` when `V ≤ B`, by the pull-out property of conditional
expectations (Mathlib's `condExp_stronglyMeasurable_bilin_of_bound`) and the Taylor bounds of
`CKSD.Asymptotics.Lindeberg.Basic`. Summing gives `𝔼 Z_k → 1` under the conditional Lindeberg
condition, and then `𝔼 exp (i t S_k) → exp (-t² v / 2)`.

## Main results

* `CKSD.integral_mul_ofReal_condExp`: `∫ W g = ∫ W 𝔼[g | m]` for bounded `m`-measurable `W`.
* `CKSD.condExp_sq_le_sq_add_condExp_ite`: `𝔼[Y² | m] ≤ ε² + 𝔼[Y² 1{|Y| > ε} | m]`.
* `CKSD.tendsto_integral_of_le_of_tendstoInMeasure`: bounded convergence in probability.
* `CKSD.tendstoInMeasure_of_ae_eq_of_measure_tendsto_zero`: convergence in probability is
  unaffected by changes on events of vanishing probability.
* `CKSD.tendstoInDistribution_sum_of_sum_condVar_le`: the martingale central limit theorem for
  rows whose summed conditional variances are bounded.
* `CKSD.mul_zero_or_one_martingaleDifference`: truncation by predictable `{0, 1}` factors.

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

/-- Pulling a bounded `m`-measurable complex factor through a real conditional expectation:
`∫ W g = ∫ W 𝔼[g | m]`. -/
theorem integral_mul_ofReal_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {W : Ω → ℂ} (hW : StronglyMeasurable[m] W) {c : ℝ}
    (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ c) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫ ω, W ω * (g ω : ℂ) ∂μ = ∫ ω, W ω * ((μ[g | m]) ω : ℂ) ∂μ := by
  let B : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  have hB : ∀ w x, B w x = w * (x : ℂ) := fun w x ↦ by
    simp [B, real_smul, mul_comm]
  have h := condExp_stronglyMeasurable_bilin_of_bound B hm hW hg c hWb
  calc ∫ ω, W ω * (g ω : ℂ) ∂μ = ∫ ω, B (W ω) (g ω) ∂μ := by simp_rw [hB]
    _ = ∫ ω, (μ[fun ω ↦ B (W ω) (g ω) | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, B (W ω) ((μ[g | m]) ω) ∂μ := integral_congr_ae h
    _ = _ := by simp_rw [hB]

/-- Complex coercion preserves integrability. -/
private theorem integrable_ofReal_complex {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {g : Ω → ℝ} (hg : Integrable g μ) : Integrable (fun ω ↦ (g ω : ℂ)) μ := hg.ofReal

/-- The conditional Taylor estimate behind one step of the martingale telescoping argument.
Let `W` be a bounded `𝓕`-measurable complex factor, `Y` a square-integrable variable with
`𝔼[Y | 𝓕] = 0`, conditional variance `σ ∈ [0, B]` and conditional truncated second moment `ℓ`.
Then `‖𝔼[W exp (i t Y)] - 𝔼[W exp (-t² σ / 2)]‖ ≤ c (𝔼 (t² σ / 2)² + |t|³ ε 𝔼 σ / 3 + 2 t² 𝔼 ℓ)`
when `‖W‖ ≤ c`. -/
private theorem norm_integral_mul_cexp_sub_le {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hFm : 𝓕 ≤ mΩ) {W : Ω → ℂ}
    (hWm : StronglyMeasurable[𝓕] W) {c : ℝ} (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ c) {Y σ ℓ : Ω → ℝ}
    (h2 : MemLp Y 2 μ) (h0 : μ[Y | 𝓕] =ᵐ[μ] 0) (hσm : StronglyMeasurable[𝓕] σ)
    (hσ : σ =ᵐ[μ] μ[fun ω ↦ Y ω ^ 2 | 𝓕]) {ε : ℝ} (hε : 0 ≤ ε)
    (hℓ : ℓ =ᵐ[μ] μ[fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0 | 𝓕]) {B : ℝ}
    (hσB : ∀ᵐ ω ∂μ, 0 ≤ σ ω ∧ σ ω ≤ B) (t : ℝ) :
    ‖∫ ω, W ω * cexp (((t * Y ω : ℝ) : ℂ) * I) ∂μ -
      ∫ ω, W ω * ((Real.exp (-(t ^ 2 / 2 * σ ω)) : ℝ) : ℂ) ∂μ‖ ≤
      c * (∫ ω, (t ^ 2 / 2 * σ ω) ^ 2 ∂μ + |t| ^ 3 * ε / 3 * ∫ ω, σ ω ∂μ +
        2 * t ^ 2 * ∫ ω, ℓ ω ∂μ) := by
  have hWae : AEStronglyMeasurable W μ := (hWm.mono hFm).aestronglyMeasurable
  -- integrability
  have hX1 : Integrable Y μ := h2.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ Y ω ^ 2) μ := h2.integrable_sq
  have hσi : Integrable σ μ := integrable_condExp.congr hσ.symm
  have hℓi : Integrable ℓ μ := integrable_condExp.congr hℓ.symm
  set a : Ω → ℝ := fun ω ↦ t ^ 2 / 2 * σ ω with ha
  have hσae : AEStronglyMeasurable σ μ := (hσm.mono hFm).aestronglyMeasurable
  have ha2 : Integrable (fun ω ↦ a ω ^ 2) μ := by
    refine Integrable.of_bound (C := (t ^ 2 / 2 * B) ^ 2)
      ((hσae.const_mul _).pow 2) ?_
    filter_upwards [hσB] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (by have := hω.1; positivity)
      (mul_le_mul_of_nonneg_left hω.2 (by positivity)) 2
  have hWint : ∀ {g : Ω → ℝ}, Integrable g μ → Integrable (fun ω ↦ W ω * (g ω : ℂ)) μ :=
    fun hg ↦ (integrable_ofReal_complex hg).bdd_mul hWae hWb
  have hWi : Integrable W μ := Integrable.of_bound hWae c hWb
  -- the martingale-difference and conditional-variance identities
  have hEX : ∫ ω, W ω * (Y ω : ℂ) ∂μ = 0 := by
    rw [integral_mul_ofReal_condExp hFm hWm hWb hX1]
    have h0' : (fun ω ↦ W ω * ((μ[Y | 𝓕]) ω : ℂ)) =ᵐ[μ] fun _ ↦ 0 :=
      h0.mono fun ω hω ↦ by simp only [hω, Pi.zero_apply, ofReal_zero, mul_zero]
    rw [integral_congr_ae h0', integral_zero]
  have hEX2 : ∫ ω, W ω * ((Y ω ^ 2 : ℝ) : ℂ) ∂μ = ∫ ω, W ω * (σ ω : ℂ) ∂μ := by
    rw [integral_mul_ofReal_condExp hFm hWm hWb hX2]
    have hσ' : (fun ω ↦ W ω * ((μ[fun ω ↦ Y ω ^ 2 | 𝓕]) ω : ℂ)) =ᵐ[μ]
        fun ω ↦ W ω * (σ ω : ℂ) := hσ.mono fun ω hω ↦ by simp only [hω]
    exact integral_congr_ae hσ'
  -- the Taylor remainder
  set ρ : Ω → ℂ := fun ω ↦ cexp (((t * Y ω : ℝ) : ℂ) * I) -
    (1 + ((t * Y ω : ℝ) : ℂ) * I - ((t * Y ω : ℝ) : ℂ) ^ 2 / 2) with hρ
  have hXae : AEStronglyMeasurable Y μ := h2.aestronglyMeasurable
  have hρae : AEStronglyMeasurable ρ μ := by
    have hcont : Continuous fun x : ℝ ↦ cexp (((t * x : ℝ) : ℂ) * I) -
        (1 + ((t * x : ℝ) : ℂ) * I - ((t * x : ℝ) : ℂ) ^ 2 / 2) := by fun_prop
    exact hcont.comp_aestronglyMeasurable hXae
  have hρi : Integrable ρ μ := by
    refine (hX2.const_mul (2 * t ^ 2)).mono' hρae (ae_of_all _ fun ω ↦ ?_)
    have := (norm_cexp_ofReal_mul_I_sub_le (t * Y ω)).2
    rw [mul_pow] at this
    simp only [hρ]
    linarith
  have hT := integrable_ite_lt_abs_sq h2 ε
  have ha0 : ∀ᵐ ω ∂μ, 0 ≤ a ω := hσB.mono fun ω hω ↦ by
    simp only [ha]; have := hω.1; positivity
  have hEi : Integrable (fun ω ↦ Real.exp (-a ω)) μ := by
    refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (hσae.const_mul (t ^ 2 / 2)).neg) 1 ?_
    filter_upwards [ha0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hbi : Integrable (fun ω ↦ 1 - a ω - Real.exp (-a ω)) μ :=
    ((integrable_const 1).sub (hσi.const_mul _)).sub hEi
  have hpt : ∀ ω, W ω * cexp (((t * Y ω : ℝ) : ℂ) * I) - W ω * ((Real.exp (-a ω) : ℝ) : ℂ) =
      W ω * ((1 - a ω - Real.exp (-a ω) : ℝ) : ℂ) + ((t : ℂ) * I) * (W ω * (Y ω : ℂ)) -
      ((t ^ 2 / 2 : ℝ) : ℂ) * (W ω * ((Y ω ^ 2 : ℝ) : ℂ)) +
      ((t ^ 2 / 2 : ℝ) : ℂ) * (W ω * (σ ω : ℂ)) + W ω * ρ ω := fun ω ↦ by
    simp only [hρ, ha]; push_cast; ring
  have hI1 : Integrable (fun ω ↦ W ω * cexp (((t * Y ω : ℝ) : ℂ) * I)) μ := by
    refine Integrable.of_bound ?_ c ?_
    · exact hWae.mul ((by fun_prop : Continuous fun x : ℝ ↦ cexp (((t * x : ℝ) : ℂ) * I)
        ).comp_aestronglyMeasurable hXae)
    · filter_upwards [hWb] with ω hω
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hω
  have hsplit : ∫ ω, W ω * cexp (((t * Y ω : ℝ) : ℂ) * I) ∂μ -
      ∫ ω, W ω * ((Real.exp (-a ω) : ℝ) : ℂ) ∂μ =
      ∫ ω, W ω * ((1 - a ω - Real.exp (-a ω) : ℝ) : ℂ) ∂μ + ∫ ω, W ω * ρ ω ∂μ := by
    rw [← integral_sub hI1 (hWint hEi), integral_congr_ae (Eventually.of_forall hpt),
      integral_add _ (hρi.bdd_mul hWae hWb), integral_add _ ((hWint hσi).const_mul _),
      integral_sub _ ((hWint hX2).const_mul _), integral_add (hWint hbi)
        ((hWint hX1).const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
      hEX, hEX2]
    · ring
    · exact (hWint hbi).add ((hWint hX1).const_mul _)
    · exact ((hWint hbi).add ((hWint hX1).const_mul _)).sub ((hWint hX2).const_mul _)
    · exact (((hWint hbi).add ((hWint hX1).const_mul _)).sub ((hWint hX2).const_mul _)).add
        ((hWint hσi).const_mul _)
  rw [hsplit]
  have hb1 : ‖∫ ω, W ω * ((1 - a ω - Real.exp (-a ω) : ℝ) : ℂ) ∂μ‖ ≤
      c * ∫ ω, a ω ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (ha2.const_mul c) ?_
    filter_upwards [hWb, ha0] with ω hω h0ω
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    have := Real.abs_exp_neg_sub_one_sub_le_sq h0ω
    rw [abs_sub_comm, show 1 - a ω - Real.exp (-a ω) = -(Real.exp (-a ω) - (1 - a ω)) by ring,
      abs_neg] at *
    exact mul_le_mul hω this (abs_nonneg _) ((norm_nonneg _).trans hω)
  have hb2 : ‖∫ ω, W ω * ρ ω ∂μ‖ ≤ c * (|t| ^ 3 * ε / 3 * ∫ ω, Y ω ^ 2 ∂μ +
      2 * t ^ 2 * ∫ ω, (if ε < |Y ω| then Y ω ^ 2 else 0) ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hX2.const_mul _)
      (hT.const_mul _), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (((hX2.const_mul _).add (hT.const_mul _)).const_mul c) ?_
    filter_upwards [hWb] with ω hω
    rw [norm_mul]
    exact mul_le_mul hω (norm_cexp_ofReal_mul_I_sub_le_lindeberg hε t (Y ω)) (norm_nonneg _)
      ((norm_nonneg _).trans hω)
  have hσint : ∫ ω, Y ω ^ 2 ∂μ = ∫ ω, σ ω ∂μ := by
    rw [integral_congr_ae hσ, integral_condExp hFm]
  have hℓint : ∫ ω, (if ε < |Y ω| then Y ω ^ 2 else 0) ∂μ = ∫ ω, ℓ ω ∂μ := by
    rw [integral_congr_ae hℓ, integral_condExp hFm]
  rw [hσint, hℓint] at hb2
  refine (norm_add_le _ _).trans ?_
  linarith


/-- One step of the martingale telescoping argument. With `S m = ∑_{i<m} X i`,
`V m = ∑_{i<m} σ²ᵢ` and `Z m = exp (i t S m + t² V m / 2)`, if `X m` is a square-integrable
martingale difference with conditional variance `σ²ₘ` and conditional truncated second moment
`ℓₘ`, and `V (m + 1) ≤ B`, then
`‖𝔼 Z (m + 1) - 𝔼 Z m‖ ≤ exp (t² B / 2) (𝔼 (t² σ²ₘ / 2)² + |t|³ ε 𝔼 σ²ₘ / 3 + 2 t² 𝔼 ℓₘ)`. -/
private theorem norm_integral_mdsZ_succ_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X σ2 ℓ : ℕ → Ω → ℝ) (m : ℕ)
    (hX : ∀ i, StronglyMeasurable[F (i + 1)] (X i)) (h2 : MemLp (X m) 2 μ)
    (h0 : μ[X m | F m] =ᵐ[μ] 0) (hσm : ∀ i, StronglyMeasurable[F i] (σ2 i))
    (hσ : σ2 m =ᵐ[μ] μ[fun ω ↦ X m ω ^ 2 | F m]) {ε : ℝ} (hε : 0 ≤ ε)
    (hℓ : ℓ m =ᵐ[μ] μ[fun ω ↦ if ε < |X m ω| then X m ω ^ 2 else 0 | F m])
    (hσ0 : ∀ i, 0 ≤ᵐ[μ] σ2 i) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range (m + 1), σ2 i ω ≤ B) (t : ℝ) :
    ‖∫ ω, cexp (((t * ∑ i ∈ Finset.range (m + 1), X i ω : ℝ) : ℂ) * I +
        ((t ^ 2 / 2 * ∑ i ∈ Finset.range (m + 1), σ2 i ω : ℝ) : ℂ)) ∂μ -
      ∫ ω, cexp (((t * ∑ i ∈ Finset.range m, X i ω : ℝ) : ℂ) * I +
        ((t ^ 2 / 2 * ∑ i ∈ Finset.range m, σ2 i ω : ℝ) : ℂ)) ∂μ‖ ≤
      Real.exp (t ^ 2 / 2 * B) * (∫ ω, (t ^ 2 / 2 * σ2 m ω) ^ 2 ∂μ +
        |t| ^ 3 * ε / 3 * ∫ ω, σ2 m ω ∂μ + 2 * t ^ 2 * ∫ ω, ℓ m ω ∂μ) := by
  have hFm : F m ≤ mΩ := F.le m
  set S : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range m, X i ω with hS
  set V : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range (m + 1), σ2 i ω with hV
  have hSm : StronglyMeasurable[F m] S :=
    Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      (hX i).mono (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  have hVm : StronglyMeasurable[F m] V :=
    Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
      (hσm i).mono (F.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  set W : Ω → ℂ := fun ω ↦ cexp (((t * S ω : ℝ) : ℂ) * I + ((t ^ 2 / 2 * V ω : ℝ) : ℂ)) with hW
  have hWm : StronglyMeasurable[F m] W := by
    have hc : Continuous fun p : ℝ × ℝ ↦ cexp (((t * p.1 : ℝ) : ℂ) * I +
        ((t ^ 2 / 2 * p.2 : ℝ) : ℂ)) := by fun_prop
    have hp : StronglyMeasurable[F m] (fun ω ↦ (S ω, V ω)) := hSm.prodMk hVm
    have := hc.comp_stronglyMeasurable hp
    exact this
  set c := Real.exp (t ^ 2 / 2 * B) with hc
  have hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ c := by
    filter_upwards [hB] with ω hω
    rw [hW, norm_exp]
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      zero_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω (by positivity))
  have hσ0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ σ2 i ω := ae_all_iff.2 hσ0
  have hσB : ∀ᵐ ω ∂μ, 0 ≤ σ2 m ω ∧ σ2 m ω ≤ B := by
    filter_upwards [hB, hσ0'] with ω hω h0ω
    exact ⟨h0ω m, (Finset.single_le_sum (fun i _ ↦ h0ω i)
      (Finset.self_mem_range_succ m)).trans hω⟩
  set a : Ω → ℝ := fun ω ↦ t ^ 2 / 2 * σ2 m ω with ha
  -- the two exponentials
  have hZ1 : ∀ ω, cexp (((t * ∑ i ∈ Finset.range (m + 1), X i ω : ℝ) : ℂ) * I +
      ((t ^ 2 / 2 * ∑ i ∈ Finset.range (m + 1), σ2 i ω : ℝ) : ℂ)) =
      W ω * cexp (((t * X m ω : ℝ) : ℂ) * I) := fun ω ↦ by
    simp only [hW, hS, hV, Finset.sum_range_succ (fun i ↦ X i ω)]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hZ0 : ∀ ω, cexp (((t * ∑ i ∈ Finset.range m, X i ω : ℝ) : ℂ) * I +
      ((t ^ 2 / 2 * ∑ i ∈ Finset.range m, σ2 i ω : ℝ) : ℂ)) =
      W ω * ((Real.exp (-a ω) : ℝ) : ℂ) := fun ω ↦ by
    simp only [hW, hS, hV, ha, Finset.sum_range_succ (fun i ↦ σ2 i ω), ofReal_exp]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [integral_congr_ae (Eventually.of_forall hZ1), integral_congr_ae (Eventually.of_forall hZ0)]
  exact norm_integral_mul_cexp_sub_le hFm hWm hWb h2 h0 (hσm m) hσ hε hℓ hσB t

/-- A conditional variance is at most `ε²` plus the conditional truncated second moment. -/
theorem condExp_sq_le_sq_add_condExp_ite {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (ε : ℝ) :
    μ[fun ω ↦ Y ω ^ 2 | m] ≤ᵐ[μ]
      fun ω ↦ ε ^ 2 + (μ[fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0 | m]) ω := by
  have hT := integrable_ite_lt_abs_sq hY ε
  have hle : (fun ω ↦ Y ω ^ 2) ≤ᵐ[μ]
      (fun _ ↦ ε ^ 2) + fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0 := ae_of_all _ fun ω ↦ by
    simp only [Pi.add_apply]
    split_ifs with h
    · nlinarith [sq_nonneg ε]
    · rw [add_zero, ← sq_abs (Y ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.mp h) 2
  have h1 := condExp_mono (m := m) hY.integrable_sq ((integrable_const _).add hT) hle
  have h2 := condExp_add (integrable_const (ε ^ 2)) hT m
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [h2ω, Pi.add_apply, condExp_const hm] at h1ω
  exact h1ω

/-- The row estimate of the martingale telescoping argument: for martingale differences
`X 0, …, X (k - 1)` with conditional variances `σ²ⱼ` whose sum `V` is at most `B`, and
conditional truncated second moments `ℓⱼ` with sum `L`,
`‖𝔼 exp (i t ∑ⱼ Xⱼ + t² V / 2) - 1‖ ≤ exp (t² B / 2) (t⁴ B (ε² + 𝔼 L) / 4 + |t|³ ε B / 3 +
2 t² 𝔼 L)`. -/
private theorem norm_integral_mdsZ_sub_one_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X σ2 ℓ : ℕ → Ω → ℝ) (k : ℕ)
    (hX : ∀ i, StronglyMeasurable[F (i + 1)] (X i)) (h2 : ∀ i, MemLp (X i) 2 μ)
    (h0 : ∀ i, μ[X i | F i] =ᵐ[μ] 0) (hσm : ∀ i, StronglyMeasurable[F i] (σ2 i))
    (hσ : ∀ i, σ2 i =ᵐ[μ] μ[fun ω ↦ X i ω ^ 2 | F i]) {ε : ℝ} (hε : 0 ≤ ε)
    (hℓ : ∀ i, ℓ i =ᵐ[μ] μ[fun ω ↦ if ε < |X i ω| then X i ω ^ 2 else 0 | F i])
    (hσ0 : ∀ i, 0 ≤ᵐ[μ] σ2 i) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range k, σ2 i ω ≤ B) (t : ℝ) :
    ‖∫ ω, cexp (((t * ∑ i ∈ Finset.range k, X i ω : ℝ) : ℂ) * I +
        ((t ^ 2 / 2 * ∑ i ∈ Finset.range k, σ2 i ω : ℝ) : ℂ)) ∂μ - 1‖ ≤
      Real.exp (t ^ 2 / 2 * B) * (t ^ 4 / 4 * B * (ε ^ 2 + ∫ ω, ∑ i ∈ Finset.range k, ℓ i ω ∂μ) +
        |t| ^ 3 * ε / 3 * B + 2 * t ^ 2 * ∫ ω, ∑ i ∈ Finset.range k, ℓ i ω ∂μ) := by
  set Z : ℕ → ℂ := fun m ↦ ∫ ω, cexp (((t * ∑ i ∈ Finset.range m, X i ω : ℝ) : ℂ) * I +
    ((t ^ 2 / 2 * ∑ i ∈ Finset.range m, σ2 i ω : ℝ) : ℂ)) ∂μ with hZ
  have hσ0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ σ2 i ω := ae_all_iff.2 hσ0
  have hσi : ∀ i, Integrable (σ2 i) μ := fun i ↦ integrable_condExp.congr (hσ i).symm
  have hℓi : ∀ i, Integrable (ℓ i) μ := fun i ↦ integrable_condExp.congr (hℓ i).symm
  have hℓ0 : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ ℓ i ω := ae_all_iff.2 fun i ↦ by
    filter_upwards [hℓ i, condExp_nonneg (m := F i) (f := fun ω ↦
      if ε < |X i ω| then X i ω ^ 2 else 0) (ae_of_all _ fun ω ↦ by
        simp only [Pi.zero_apply]; split_ifs <;> positivity)] with ω h1 h2
    rw [h1]; exact h2
  have hσℓ : ∀ᵐ ω ∂μ, ∀ i, σ2 i ω ≤ ε ^ 2 + ℓ i ω := ae_all_iff.2 fun i ↦ by
    filter_upwards [hσ i, hℓ i, condExp_sq_le_sq_add_condExp_ite (F.le i) (h2 i) ε]
      with ω h1 h2 h3
    rw [h1, h2]; exact h3
  have hBm : ∀ m < k, ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range (m + 1), σ2 i ω ≤ B := fun m hm ↦ by
    filter_upwards [hB, hσ0'] with ω hω h0ω
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hm)
      fun i _ _ ↦ h0ω i).trans hω
  have hstep := fun m (hm : m ∈ Finset.range k) ↦ norm_integral_mdsZ_succ_sub_le F X σ2 ℓ m hX
    (h2 m) (h0 m) hσm (hσ m) hε (hℓ m) hσ0 (hBm m (Finset.mem_range.mp hm)) t
  have hZ0 : Z 0 = 1 := by simp [hZ]
  have htel : Z k - 1 = ∑ m ∈ Finset.range k, (Z (m + 1) - Z m) := by
    rw [Finset.sum_range_sub, hZ0]
  rw [show (∫ ω, cexp (((t * ∑ i ∈ Finset.range k, X i ω : ℝ) : ℂ) * I +
      ((t ^ 2 / 2 * ∑ i ∈ Finset.range k, σ2 i ω : ℝ) : ℂ)) ∂μ) = Z k from rfl, htel]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← integral_finsetSum _ fun i _ ↦ hσi i, ← integral_finsetSum _ fun i _ ↦ hℓi i]
  have hσB : ∀ m ∈ Finset.range k, ∀ᵐ ω ∂μ, 0 ≤ σ2 m ω ∧ σ2 m ω ≤ B := fun m hm ↦ by
    filter_upwards [hBm m (Finset.mem_range.mp hm), hσ0'] with ω hω h0ω
    exact ⟨h0ω m, (Finset.single_le_sum (fun i _ ↦ h0ω i)
      (Finset.self_mem_range_succ m)).trans hω⟩
  have ha2 : ∀ m ∈ Finset.range k, Integrable (fun ω ↦ (t ^ 2 / 2 * σ2 m ω) ^ 2) μ :=
    fun m hm ↦ by
      refine Integrable.of_bound (C := (t ^ 2 / 2 * B) ^ 2)
        ((((hσm m).mono (F.le m)).aestronglyMeasurable.const_mul _).pow 2) ?_
      filter_upwards [hσB m hm] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (by have := hω.1; positivity)
        (mul_le_mul_of_nonneg_left hω.2 (by positivity)) 2
  have hLi : Integrable (fun ω ↦ ∑ i ∈ Finset.range k, ℓ i ω) μ :=
    integrable_finsetSum _ fun i _ ↦ hℓi i
  have h1 : ∑ m ∈ Finset.range k, ∫ ω, (t ^ 2 / 2 * σ2 m ω) ^ 2 ∂μ ≤
      t ^ 4 / 4 * B * (ε ^ 2 + ∫ ω, ∑ i ∈ Finset.range k, ℓ i ω ∂μ) := by
    rw [← integral_finsetSum _ ha2]
    have hrhs : t ^ 4 / 4 * B * (ε ^ 2 + ∫ ω, ∑ i ∈ Finset.range k, ℓ i ω ∂μ) =
        ∫ ω, t ^ 4 / 4 * B * (ε ^ 2 + ∑ i ∈ Finset.range k, ℓ i ω) ∂μ := by
      rw [integral_const_mul, integral_add (integrable_const _) hLi, integral_const]; simp
    rw [hrhs]
    refine integral_mono_ae (integrable_finsetSum _ ha2)
      (((integrable_const _).add hLi).const_mul _) ?_
    filter_upwards [hB, hσ0', hσℓ, hℓ0] with ω hω h0ω hσℓω hℓ0ω
    have hL : ∀ m ∈ Finset.range k, ℓ m ω ≤ ∑ i ∈ Finset.range k, ℓ i ω := fun m hm ↦
      Finset.single_le_sum (fun i _ ↦ hℓ0ω i) hm
    calc ∑ m ∈ Finset.range k, (t ^ 2 / 2 * σ2 m ω) ^ 2
        = t ^ 4 / 4 * ∑ m ∈ Finset.range k, σ2 m ω * σ2 m ω := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ ↦ by ring
      _ ≤ t ^ 4 / 4 * ∑ m ∈ Finset.range k, σ2 m ω * (ε ^ 2 + ∑ i ∈ Finset.range k, ℓ i ω) := by
          gcongr with m hm
          · exact h0ω m
          · exact (hσℓω m).trans (by linarith [hL m hm])
      _ = t ^ 4 / 4 * (∑ m ∈ Finset.range k, σ2 m ω) * (ε ^ 2 + ∑ i ∈ Finset.range k, ℓ i ω) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ _ := by
          have : 0 ≤ ε ^ 2 + ∑ i ∈ Finset.range k, ℓ i ω :=
            add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hℓ0ω i)
          gcongr
  have h2' : ∫ ω, ∑ i ∈ Finset.range k, σ2 i ω ∂μ ≤ B := by
    have := integral_mono_ae (integrable_finsetSum _ fun i _ ↦ hσi i) (integrable_const B) hB
    simpa using this
  have h3 : 0 ≤ |t| ^ 3 * ε / 3 := by positivity
  nlinarith

/-- Bounded convergence in probability: if `0 ≤ Yₙ ≤ B` and `Yₙ ≤ Lₙ` almost surely with
`Lₙ → 0` in probability, then `𝔼 Yₙ → 0`. -/
theorem tendsto_integral_of_le_of_tendstoInMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y L : ℕ → Ω → ℝ} {B : ℝ}
    (hY : ∀ n, Integrable (Y n) μ) (hLm : ∀ n, Measurable (L n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ] Y n) (hYB : ∀ n, ∀ᵐ ω ∂μ, Y n ω ≤ B) (hYL : ∀ n, Y n ≤ᵐ[μ] L n)
    (hL : TendstoInMeasure μ L atTop fun _ ↦ 0) :
    Tendsto (fun n ↦ ∫ ω, Y n ω ∂μ) atTop (𝓝 0) := by
  have hB : 0 ≤ B := by
    obtain ⟨ω, h0, h1⟩ := ((hY0 0).and (hYB 0)).exists
    exact (h0 : (0 : ℝ) ≤ Y 0 ω).trans h1
  refine Metric.tendsto_atTop.2 fun δ hδ ↦ ?_
  have hδ2 : 0 < δ / 2 := by positivity
  rw [tendstoInMeasure_iff_dist] at hL
  have hL' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hL (δ / 2) hδ2)
  rw [ENNReal.toReal_zero] at hL'
  have hev := (hL'.const_mul B).eventually (gt_mem_nhds (by rw [mul_zero]; exact hδ2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  set s := {ω | δ / 2 ≤ dist (L n ω) 0} with hs
  have hsm : MeasurableSet s := measurableSet_le measurable_const ((hLm n).dist measurable_const)
  have hbound : ∫ ω, Y n ω ∂μ ≤ δ / 2 + B * μ.real s := by
    have hrhs : δ / 2 + B * μ.real s = ∫ ω, (δ / 2 + s.indicator (fun _ ↦ B) ω) ∂μ := by
      rw [integral_add (integrable_const _) ((integrable_const B).indicator hsm),
        integral_const, integral_indicator_const _ hsm]
      simp [mul_comm]
    rw [hrhs]
    refine integral_mono_ae (hY n) ((integrable_const _).add
      ((integrable_const B).indicator hsm)) ?_
    filter_upwards [hYB n, hYL n] with ω hB' hL'
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω]; linarith
    · rw [Set.indicator_of_notMem hω]
      simp only [hs, Set.mem_ofPred_eq, not_le, Real.dist_eq, sub_zero] at hω
      linarith [le_abs_self (L n ω)]
  have h0 : 0 ≤ ∫ ω, Y n ω ∂μ := integral_nonneg_of_ae (hY0 n)
  have hNn := hN n hn
  simp only [Function.comp_apply] at hNn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  change B * μ.real s < δ / 2 at hNn
  linarith

/-- Convergence in probability transfers to sequences that agree with the original one outside
events whose probabilities tend to zero. -/
theorem tendstoInMeasure_of_ae_eq_of_measure_tendsto_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {Y Z : ℕ → Ω → ℝ} {g : Ω → ℝ} (E : ℕ → Set Ω)
    (hE : Tendsto (fun n ↦ μ (E n)) atTop (𝓝 0))
    (hYZ : ∀ n, ∀ᵐ ω ∂μ, ω ∉ E n → Y n ω = Z n ω) (hZ : TendstoInMeasure μ Z atTop g) :
    TendstoInMeasure μ Y atTop g := by
  rw [tendstoInMeasure_iff_dist] at hZ ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (hZ ε hε).add hE) (fun _ ↦ bot_le) (fun n ↦ ?_)
  refine (measure_mono_ae ?_).trans (measure_union_le _ (E n))
  filter_upwards [hYZ n] with ω hω hmem
  by_cases h : ω ∈ E n
  · exact Or.inr h
  · left
    change ε ≤ dist (Z n ω) (g ω)
    rw [← hω h]; exact hmem

/-- If `Vₙ ≥ 0` almost surely and `Vₙ → v` in probability, then `v ≥ 0`. -/
theorem nonneg_of_tendstoInMeasure_of_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {V : ℕ → Ω → ℝ} {v : ℝ}
    (hV0 : ∀ n, 0 ≤ᵐ[μ] V n) (hV : TendstoInMeasure μ V atTop fun _ ↦ v) : 0 ≤ v := by
  by_contra hv
  push Not at hv
  rw [tendstoInMeasure_iff_dist] at hV
  have h := hV (-v) (by linarith)
  have h1 : ∀ n, μ {ω | -v ≤ dist (V n ω) v} = 1 := fun n ↦ by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := μ)]
    refine measure_mono_ae ?_
    filter_upwards [hV0 n] with ω hω _
    have h0 : (0 : ℝ) ≤ V n ω := hω
    change -v ≤ dist (V n ω) v
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  simp only [h1] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- The martingale central limit theorem when the conditional variances of each row sum to at
most a constant `B`: square-integrable martingale-difference rows whose summed conditional
variances `V n ≤ B` converge in probability to `v ≥ 0`, and whose summed conditional truncated
second moments tend to zero in mean, have row sums converging in distribution to `N(0, v)`.
The proof compares `𝔼 exp (i t Sₙ)` with `exp (-t² v / 2)` through the telescoping estimate
`norm_integral_mdsZ_sub_one_le`. -/
theorem tendstoInDistribution_sum_of_sum_condVar_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X σ2 : ℕ → ℕ → Ω → ℝ) (ℓ : ℝ → ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hX : ∀ n i, StronglyMeasurable[F n (i + 1)] (X n i)) (h2 : ∀ n i, MemLp (X n i) 2 μ)
    (h0 : ∀ n i, μ[X n i | F n i] =ᵐ[μ] 0) (hσm : ∀ n i, StronglyMeasurable[F n i] (σ2 n i))
    (hσ : ∀ n i, σ2 n i =ᵐ[μ] μ[fun ω ↦ X n i ω ^ 2 | F n i])
    (hℓ : ∀ ε > 0, ∀ n i, ℓ ε n i =ᵐ[μ]
      μ[fun ω ↦ if ε < |X n i ω| then X n i ω ^ 2 else 0 | F n i])
    (hσ0 : ∀ n i, 0 ≤ᵐ[μ] σ2 n i) {B v : ℝ} (hv0 : 0 ≤ v)
    (hB : ∀ n, ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range (k n), σ2 n i ω ≤ B)
    (hV : TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ Finset.range (k n), σ2 n i ω) atTop
      fun _ ↦ v)
    (hL : ∀ ε > 0, Tendsto (fun n ↦ ∫ ω, ∑ i ∈ Finset.range (k n), ℓ ε n i ω ∂μ) atTop
      (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i ∈ Finset.range (k n), X n i ω) atTop id
      (fun _ ↦ μ) (gaussianReal 0 v.toNNReal) := by
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω with hSdef
  set V : ℕ → Ω → ℝ := fun n ω ↦ ∑ j ∈ Finset.range (k n), σ2 n j ω with hVdef
  have hrow := fun n ε (hε : 0 < ε) t ↦ norm_integral_mdsZ_sub_one_le (F n) (X n) (σ2 n)
    (ℓ ε n) (k n) (hX n) (h2 n) (h0 n) (hσm n) (hσ n) hε.le (hℓ ε hε n) (hσ0 n)
    (hB n) t
  -- measurability
  have hXmeas : ∀ n j, Measurable (X n j) := fun n j ↦
    ((hX n j).mono ((F n).le _)).measurable
  have hSm : ∀ n, Measurable (S n) := fun n ↦
    Finset.measurable_fun_sum _ fun j _ ↦ hXmeas n j
  have hVm : ∀ n, Measurable (V n) := fun n ↦
    Finset.measurable_fun_sum _ fun j _ ↦ ((hσm n j).mono ((F n).le j)).measurable
  have hV0B : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ V n ω ∧ V n ω ≤ B := fun n ↦ by
    filter_upwards [hB n, ae_all_iff.2 (hσ0 n)] with ω hω h0
    exact ⟨Finset.sum_nonneg fun j _ ↦ h0 j, hω⟩
  -- characteristic functions of the truncated row sums
  have hchar : ∀ t, Tendsto (fun n ↦ charFun (μ.map (S n)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 v.toNNReal).map id) t)) := by
    intro t
    set e := Real.exp (t ^ 2 / 2 * v) with he
    have hlim : charFun ((gaussianReal 0 v.toNNReal).map id) t = ((e⁻¹ : ℝ) : ℂ) := by
      rw [Measure.map_id, charFun_gaussianReal, Real.coe_toNNReal _ hv0, he, ← Real.exp_neg,
        ofReal_exp]
      push_cast; ring_nf
    have hφ : ∀ n, charFun (μ.map (S n)) t = ∫ ω, cexp (((t * S n ω : ℝ) : ℂ) * I) ∂μ :=
      fun n ↦ by
        rw [charFun_apply_real, integral_map (hSm n).aemeasurable (by fun_prop)]
        simp only [ofReal_mul]
    set c := Real.exp (t ^ 2 / 2 * B) with hc
    have hZ : Tendsto (fun n ↦ ∫ ω, cexp (((t * S n ω : ℝ) : ℂ) * I +
        ((t ^ 2 / 2 * V n ω : ℝ) : ℂ)) ∂μ) atTop (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
      let G : ℝ → ℝ := fun ε ↦ c * (t ^ 4 / 4 * B * ε ^ 2 + |t| ^ 3 * ε / 3 * B)
      have hG : Tendsto G (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto G (𝓝 0) (𝓝 (G 0)) := (by fun_prop : Continuous G).continuousAt.tendsto
        simpa [G] using this.mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hεδ, hε0⟩ := ((hG.eventually (gt_mem_nhds hδ)).and self_mem_nhdsWithin).exists
      have hε0' : (0 : ℝ) < ε := hε0
      have hRn : Tendsto (fun n ↦ c * (t ^ 4 / 4 * B *
          (ε ^ 2 + ∫ ω, ∑ j ∈ Finset.range (k n), ℓ ε n j ω ∂μ) + |t| ^ 3 * ε / 3 * B +
          2 * t ^ 2 * ∫ ω, ∑ j ∈ Finset.range (k n), ℓ ε n j ω ∂μ)) atTop (𝓝 (G ε)) := by
        have h := hL ε hε0'
        have := ((((h.const_add (ε ^ 2)).const_mul (t ^ 4 / 4 * B)).add_const
          (|t| ^ 3 * ε / 3 * B)).add (h.const_mul (2 * t ^ 2))).const_mul c
        convert this using 2
        simp only [G]; ring
      filter_upwards [hRn.eventually (gt_mem_nhds hεδ)] with n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact (hrow n ε hε0' t).trans_lt hn
    have hW : Tendsto (fun n ↦ ∫ ω, |Real.exp (t ^ 2 / 2 * V n ω) - e| ∂μ) atTop (𝓝 0) := by
      have hJ := tendstoInMeasure_comp_of_continuousAt μ V v
        (fun x ↦ |Real.exp (t ^ 2 / 2 * x) - e|) (by fun_prop) hV
      simp only [he, sub_self, abs_zero] at hJ
      refine tendsto_integral_of_le_of_tendstoInMeasure (B := c + e) (fun n ↦ ?_)
        (fun n ↦ by fun_prop) (fun n ↦ ae_of_all _ fun ω ↦ abs_nonneg _) (fun n ↦ ?_)
        (fun n ↦ ae_of_all _ fun ω ↦ le_rfl) hJ
      · refine Integrable.of_bound (by fun_prop) (c + e) ?_
        filter_upwards [hV0B n] with ω hω
        rw [Real.norm_eq_abs, abs_abs]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        have : Real.exp (t ^ 2 / 2 * V n ω) ≤ c :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 (by positivity))
        linarith
      · filter_upwards [hV0B n] with ω hω
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        have : Real.exp (t ^ 2 / 2 * V n ω) ≤ c :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 (by positivity))
        linarith
    have hD : Tendsto (fun n ↦ (∫ ω, cexp (((t * S n ω : ℝ) : ℂ) * I) ∂μ) * ((e : ℝ) : ℂ) -
        ∫ ω, cexp (((t * S n ω : ℝ) : ℂ) * I + ((t ^ 2 / 2 * V n ω : ℝ) : ℂ)) ∂μ) atTop
        (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hW
      have hi1 : Integrable (fun ω ↦ cexp (((t * S n ω : ℝ) : ℂ) * I) * ((e : ℝ) : ℂ)) μ := by
        refine Integrable.of_bound (by fun_prop) e (ae_of_all _ fun ω ↦ ?_)
        rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      have hi2 : Integrable (fun ω ↦ cexp (((t * S n ω : ℝ) : ℂ) * I +
          ((t ^ 2 / 2 * V n ω : ℝ) : ℂ))) μ := by
        refine Integrable.of_bound (by fun_prop) c ?_
        filter_upwards [hV0B n] with ω hω
        rw [norm_exp]
        simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, zero_add]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.2 (by positivity))
      rw [← integral_mul_const, ← integral_sub hi1 hi2]
      refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
        (ae_of_all _ fun ω ↦ ?_))
      have hsplit : cexp (((t * S n ω : ℝ) : ℂ) * I + ((t ^ 2 / 2 * V n ω : ℝ) : ℂ)) =
          cexp (((t * S n ω : ℝ) : ℂ) * I) * ((Real.exp (t ^ 2 / 2 * V n ω) : ℝ) : ℂ) := by
        rw [ofReal_exp, ← Complex.exp_add]
      simp only
      rw [hsplit, ← mul_sub, norm_mul, norm_exp_ofReal_mul_I, one_mul, ← ofReal_sub, norm_real,
        Real.norm_eq_abs, abs_sub_comm]
    have h1 := (hD.add hZ).mul_const (((e⁻¹ : ℝ) : ℂ))
    rw [zero_add, one_mul] at h1
    rw [hlim]
    refine h1.congr fun n ↦ ?_
    rw [hφ, sub_add_cancel, mul_assoc, ← ofReal_mul, mul_inv_cancel₀ (Real.exp_pos _).ne',
      ofReal_one, mul_one]
  exact TendstoInDistribution.of_tendsto_charFun (fun n ↦ (hSm n).aemeasurable)
    aemeasurable_id hchar

/-- Multiplying a square-integrable martingale difference `Y` (for `𝓕 ≤ 𝓖`, `Y` being
`𝓖`-measurable with `𝔼[Y | 𝓕] = 0`) by an `𝓕`-measurable `{0, 1}`-valued factor `ι` gives a
square-integrable martingale difference whose conditional variance and conditional truncated
second moments are those of `Y` multiplied by `ι`. -/
theorem mul_zero_or_one_martingaleDifference {Ω : Type*} {𝓕 𝓖 mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h𝓕𝓖 : 𝓕 ≤ 𝓖) (h𝓖 : 𝓖 ≤ mΩ) {ι Y : Ω → ℝ}
    (hι : StronglyMeasurable[𝓕] ι) (hι01 : ∀ ω, ι ω = 0 ∨ ι ω = 1)
    (hY : StronglyMeasurable[𝓖] Y) (h2 : MemLp Y 2 μ) (h0 : μ[Y | 𝓕] =ᵐ[μ] 0) :
    StronglyMeasurable[𝓖] (fun ω ↦ ι ω * Y ω) ∧ MemLp (fun ω ↦ ι ω * Y ω) 2 μ ∧
      μ[fun ω ↦ ι ω * Y ω | 𝓕] =ᵐ[μ] 0 ∧
      (fun ω ↦ ι ω * (μ[fun ω ↦ Y ω ^ 2 | 𝓕]) ω) =ᵐ[μ]
        μ[fun ω ↦ (ι ω * Y ω) ^ 2 | 𝓕] ∧
      ∀ ε > 0, (fun ω ↦ ι ω * (μ[fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0 | 𝓕]) ω) =ᵐ[μ]
        μ[fun ω ↦ if ε < |ι ω * Y ω| then (ι ω * Y ω) ^ 2 else 0 | 𝓕] := by
  have hm : StronglyMeasurable[𝓖] (fun ω ↦ ι ω * Y ω) := (hι.mono h𝓕𝓖).mul hY
  have h2' : MemLp (fun ω ↦ ι ω * Y ω) 2 μ :=
    h2.of_le (hm.mono h𝓖).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rcases hι01 ω with h | h <;> simp [h])
  refine ⟨hm, h2', ?_, ?_, fun ε hε ↦ ?_⟩
  · have := condExp_mul_of_stronglyMeasurable_left hι (h2'.integrable one_le_two)
      (h2.integrable one_le_two)
    filter_upwards [this, h0] with ω h1 h2
    change μ[ι * Y | 𝓕] ω = 0
    rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]
  · have heq : (fun ω ↦ (ι ω * Y ω) ^ 2) = ι * fun ω ↦ Y ω ^ 2 := by
      ext ω; rcases hι01 ω with h | h <;> simp [h]
    have hint : Integrable (ι * fun ω ↦ Y ω ^ 2) μ := heq ▸ h2'.integrable_sq
    rw [heq]
    exact (condExp_mul_of_stronglyMeasurable_left hι hint h2.integrable_sq).symm
  · have heq : (fun ω ↦ if ε < |ι ω * Y ω| then (ι ω * Y ω) ^ 2 else 0) =
        ι * fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0 := by
      ext ω
      rcases hι01 ω with h | h
      · simp [h, not_lt.mpr hε.le]
      · simp [h]
    have hint : Integrable (ι * fun ω ↦ if ε < |Y ω| then Y ω ^ 2 else 0) μ :=
      heq ▸ integrable_ite_lt_abs_sq h2' ε
    rw [heq]
    exact (condExp_mul_of_stronglyMeasurable_left hι hint
      (integrable_ite_lt_abs_sq h2 ε)).symm

end CKSD
