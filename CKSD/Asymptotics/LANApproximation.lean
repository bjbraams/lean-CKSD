module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under the Apache 2.0 license, as in Mathlib's LICENSE.
The proof is adapted from Mathlib.MeasureTheory.Function.ConvergenceInDistribution.
-/
/-!
# Metric Slutsky perturbations for varying observation spaces

Weak convergence is preserved by perturbations small in probability, allowing
both the observation spaces and probability laws to depend on the index. The
target is a second-countable pseudometric space and need not be a vector space.

This adapts Mathlib's bounded-Lipschitz proof of
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`: probability
measures and domains vary with the index, and metric distances replace vector
norm differences. The application is van der Vaart, *Asymptotic Statistics*
(1998), Theorem 7.10, printed pp. 98–99, PDF pp. 114–115.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace CKSD
variable {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [MeasurableSpace Ω'] [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
set_option backward.isDefEq.respectTransparency.types false in
/-- Metric Slutsky perturbations allow both observation spaces and probability measures to vary. -/
theorem tendsto_in_distribution_of_dist_small_in_probability
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {l : Filter ι} [l.IsCountablyGenerated]
    {X : (i : ι) → Ω i → E} (Y : (i : ι) → Ω i → E) (Z : Ω' → E)
    (hXZ : TendstoInDistribution X l Z μ ν)
    (hXY : ∀ ε > 0, Tendsto (fun n ↦ (μ n).real {ω | ε ≤ dist (Y n ω) (X n ω)}) l (𝓝 0))
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution Y l Z μ ν := by
  have hZ : AEMeasurable Z ν := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) (μ i) := hXZ.forall_aemeasurable
  let x₀ : E := Classical.choice ((nonempty_of_isProbabilityMeasure ν).map Z)
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂((μ n).map (Y n))) l (𝓝 (∫ ω, F ω ∂(ν.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(ν.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂((μ n).map (Y n)) - ∫ ω, F ω ∂(ν.map Z)|
      ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(ν.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂((μ n).map (Y n))) (∫ ω, F ω ∂((μ n).map (X n)))
      (∫ ω, F ω ∂(ν.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) (μ n) := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) (μ n) := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂(μ n)‖
    _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := norm_integral_le_integral_norm _
    -- Either `dist (Y n x) (X n x)` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂(μ n)
        + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, ‖F (Y n a) - F (X n a)‖ ∂(μ n) := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, L * (ε / 2) ∂(μ n)
        + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, M ∂(μ n) := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ by simpa only [dist_eq_norm] using! hF_lip.dist_le_mul_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    -- The goal is now a simple computation
    _ = L * (ε / 2) * (μ n).real {x | dist (Y n x) (X n x) < ε / 2}
        + M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(ν.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂((μ n).map (X n)) - ∫ ω, F ω ∂(ν.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn
end CKSD
