module

public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.UStatistics
public import Mathlib.Topology.Order.Compact
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# Consistency, argmax and multinomial asymptotics

Consistency from outer uniform convergence and a separated maximum, the compact deterministic
argmax theorem, and Pearson's multinomial limit. U-statistic projection and variance interfaces
are re-exported from `CKSD.Asymptotics.UStatistics`.
Sources: GAPS 102.23, 102.31 and 102.33, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Constant random variables converge in probability to their constant value. -/
theorem tendstoInProbabilityConst_const {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) (x : E) :
    TendstoInProbabilityConst μ (fun _ _ ↦ x) x := by
  intro ε hε
  have hn : ¬ ε < 0 := not_lt_of_ge hε.le
  simp [dist_self, hn]

/-- GAPS 102.23: consistency from uniform convergence and a separated maximum.
Pointwise bounds avoid any unmentioned measurability of a supremum. -/
theorem tendstoInProbabilityConst_m_estimator {Ω Θ : Type*} [MeasurableSpace Ω]
    [MetricSpace Θ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Θ → ℝ) (Mn : ℕ → Ω → Θ → ℝ) (θ₀ : Θ) (T : ℕ → Ω → Θ)
    (e r : ℕ → Ω → ℝ)
    (he : TendstoInProbabilityConst μ e 0) (hr : TendstoInProbabilityConst μ r 0)
    (hsep : ∀ ε > 0, ∃ δ > 0, ∀ θ, ε ≤ dist θ θ₀ → M θ ≤ M θ₀ - δ)
    (hunif : ∀ n, ∀ᵐ ω ∂μ, ∀ θ, |Mn n ω θ - M θ| ≤ e n ω)
    (hopt : ∀ n, ∀ᵐ ω ∂μ, Mn n ω θ₀ - r n ω ≤ Mn n ω (T n ω)) :
    TendstoInProbabilityConst μ T θ₀ := by
  intro ε hε
  obtain ⟨δ, hδ, hsepδ⟩ := hsep ε hε
  have he' := he (δ / 8) (by positivity)
  have hr' := hr (δ / 4) (by positivity)
  simp only [Real.dist_eq, sub_zero] at he' hr'
  have hbound (n : ℕ) : μ.real {ω | ε < dist (T n ω) θ₀} ≤
      μ.real {ω | δ / 8 < |e n ω|} + μ.real {ω | δ / 4 < |r n ω|} := by
    have hsub : {ω | ε < dist (T n ω) θ₀} ≤ᵐ[μ]
        {ω | δ / 8 < |e n ω|} ∪ {ω | δ / 4 < |r n ω|} := by
      filter_upwards [hunif n, hopt n] with ω hu ho
      intro hdist
      change δ / 8 < |e n ω| ∨ δ / 4 < |r n ω|
      by_contra hfalse
      have heabs : |e n ω| ≤ δ / 8 := le_of_not_gt fun h ↦ hfalse (Or.inl h)
      have hrabs : |r n ω| ≤ δ / 4 := le_of_not_gt fun h ↦ hfalse (Or.inr h)
      have heup : e n ω ≤ δ / 8 := (le_abs_self _).trans heabs
      have hrup : r n ω ≤ δ / 4 := (le_abs_self _).trans hrabs
      have hu₀ := (abs_le.mp (hu θ₀)).1
      have huT := (abs_le.mp (hu (T n ω))).2
      have hgap := hsepδ (T n ω) hdist.le
      linarith
    exact (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)).trans
      (measureReal_union_le _ _)
  exact squeeze_zero (fun _ ↦ measureReal_nonneg) hbound
    (by simpa using he'.add hr')

/-- GAPS 102.31: Pearson's test for a simple multinomial null. -/
theorem tendstoInDistribution_pearson_statistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (X : ℕ → Ω → Fin k)
    (hiid : IsIndependentIdenticallyDistributed μ X (∑ i, ENNReal.ofReal (p i) • Measure.dirac i)) :
    TendstoInDistribution μ (fun n ω ↦ ∑ i : Fin k,
      (((Finset.range n).filter (fun j ↦ X j ω = i)).card - (n : ℝ) * p i) ^ 2 /
        ((n : ℝ) * p i)) (TauCeti.Probability.chiSquaredMeasure (k - 1 : ℕ)) := by
  sorry

/-- GAPS 102.33, compact deterministic-limit scope of the argmax theorem. -/
theorem tendstoInProbabilityConst_argmax_of_compact
    {Ω H : Type*} [MeasurableSpace Ω]
    [MetricSpace H] [CompactSpace H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : H → ℝ) (hc : Continuous M) (θ : H) (huniq : ∀ h, h ≠ θ → M h < M θ)
    (Mn : ℕ → Ω → H → ℝ) (T : ℕ → Ω → H)
    (e : ℕ → Ω → ℝ) (he : TendstoInProbabilityConst μ e 0)
    (hu : ∀ n, ∀ᵐ ω ∂μ, ∀ h, |Mn n ω h - M h| ≤ e n ω)
    (ho : ∀ n, ∀ᵐ ω ∂μ, ∀ h, Mn n ω h ≤ Mn n ω (T n ω)) :
    TendstoInProbabilityConst μ T θ := by
  have hsep : ∀ ε > 0, ∃ δ > 0, ∀ h, ε ≤ dist h θ → M h ≤ M θ - δ := by
    intro ε hε
    let K := {h : H | ε ≤ dist h θ}
    have hclosed : IsClosed K := isClosed_le continuous_const
      (continuous_id.dist continuous_const)
    by_cases hne : K.Nonempty
    · obtain ⟨m, hm, hmax⟩ := hclosed.isCompact.exists_isMaxOn hne hc.continuousOn
      have hmne : m ≠ θ := by
        intro heq
        change ε ≤ dist m θ at hm
        rw [heq, dist_self] at hm
        exact (not_le_of_gt hε) hm
      refine ⟨M θ - M m, sub_pos.mpr (huniq m hmne), ?_⟩
      intro h hh
      have hMh : M h ≤ M m := hmax hh
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro h hh
      exact (hne ⟨h, hh⟩).elim
  apply tendstoInProbabilityConst_m_estimator μ M Mn θ T e (fun _ _ ↦ 0)
    he (tendstoInProbabilityConst_const μ 0) hsep hu
  intro n
  filter_upwards [ho n] with ω hω
  simpa only [sub_zero] using hω θ


end CKSD
