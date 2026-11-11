module
public import CKSD.Bayes.Basic
public import TauCeti.Probability.BrownianMotion.RunningMaximum
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Topology.Sequences

/-!
# Integrable bounds for Brownian forcing

A coordinatewise Brownian path plus an integrable initial vector has an integrable random bound
uniform on compact time intervals. A countable dense set of time sections gives a strongly
measurable indistinguishable version. Pinned TauCeti geometric Brownian running-maximum bounds
then control `exp(W)` and `exp(-W)`, whose sum dominates `|W|`. Independence is unnecessary.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- An a.s. continuous process with a.e. strongly measurable sections on a separable
first-countable time space has a sectionwise strongly measurable indistinguishable version. -/
theorem exists_stronglyMeasurable_version_of_ae_continuous
    {Ω ι E : Type*} [MeasurableSpace Ω] [TopologicalSpace ι] [FirstCountableTopology ι]
    [TopologicalSpace.SeparableSpace ι] [MetricSpace E] [CompleteSpace E] [Nonempty E]
    (P : Measure Ω) (X : ι → Ω → E) (hXm : ∀ t, AEStronglyMeasurable (X t) P)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) :
    ∃ X' : ι → Ω → E, (∀ t, StronglyMeasurable (X' t)) ∧ ∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ι
  let _ : Countable S := hSc.to_subtype
  have hseq (t : ι) : ∃ ψ : ℕ → S, Tendsto (fun n ↦ (ψ n : ι)) atTop (𝓝 t) := by
    obtain ⟨ψ, hψmem, hψ⟩ := mem_closure_iff_seq_limit.1 (hSd t)
    exact ⟨fun n ↦ ⟨ψ n, hψmem n⟩, hψ⟩
  choose ψ hψ using hseq
  let V : S → Ω → E := fun q ↦ (hXm q).mk (X q)
  let X' : ι → Ω → E := fun t ω ↦ limUnder atTop (fun n ↦ V (ψ t n) ω)
  have hVm (q : S) : StronglyMeasurable (V q) := (hXm q).stronglyMeasurable_mk
  refine ⟨X', fun t ↦ StronglyMeasurable.limUnder (fun n ↦ hVm (ψ t n)), ?_⟩
  have hVeq (q : S) : X q =ᵐ[P] V q := (hXm q).ae_eq_mk
  filter_upwards [hXc, ae_all_iff.2 hVeq] with ω hc heq
  intro t
  have hh : Tendsto (fun n ↦ V (ψ t n) ω) atTop (𝓝 (X t ω)) := by
    convert hc.continuousAt.tendsto.comp (hψ t) using 1
    funext n
    exact (heq (ψ t n)).symm
  exact hh.limUnder_eq


/-- A real Brownian motion has an integrable random bound uniform on a compact time interval. -/
theorem IsBrownianReal.exists_integrable_uniform_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (T : ℝ≥0) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, ‖W t ω‖ ≤ D ω := by
  obtain ⟨V, hVm, hVW⟩ := exists_stronglyMeasurable_version_of_ae_continuous P W
    (fun t ↦ (hW.aemeasurable t).aestronglyMeasurable) hW.cont
  have hVc : ∀ᵐ ω ∂P, Continuous (fun t ↦ V t ω) := by
    filter_upwards [hW.cont, hVW] with ω hc heq
    exact hc.congr fun t ↦ (heq t).symm
  have hVB : IsPreBrownianReal V P := hW.toIsPreBrownianReal.congr
    (fun t ↦ hVW.mono fun ω heq ↦ (heq t).symm)
  have hVF := hVB.isFilteredPreBrownianReal_natural hVm
  have hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun r ↦ V r ω) (Ioi t) t :=
    hVc.mono fun ω hc t _ ↦ hc.continuousWithinAt
  let S : ℝ → Ω → ℝ≥0∞ := fun σ ω ↦ ⨆ t ≤ T, ENNReal.ofReal (Real.exp (σ * V t ω))
  have hSm (σ : ℝ) : AEMeasurable (S σ) P := by
    apply aemeasurable_iSup_le_ofReal
      (fun t ↦ ((hVm t).measurable.const_mul σ).exp.aemeasurable)
    exact hVc.mono fun ω hc t _ ↦ ((hc.const_mul σ).rexp).continuousWithinAt
  have hSi (σ : ℝ) : (∫⁻ ω, S σ ω ∂P) < ∞ := by
    have hh := hVF.lintegral_iSup_geometricBrownianMotion_lt_top hcont 1 (σ ^ 2 / 2) σ
    simpa only [S, TauCeti.Probability.geometricBrownianMotion_def, sub_self, zero_mul,
      zero_add, one_mul] using hh
  let R : Ω → ℝ≥0∞ := fun ω ↦ S 1 ω + S (-1) ω
  have hRm : AEMeasurable R P := (hSm 1).add (hSm (-1))
  have hRi : (∫⁻ ω, R ω ∂P) < ∞ := by
    rw [show R = fun ω ↦ S 1 ω + S (-1) ω from rfl, lintegral_add_left' (hSm 1)]
    exact ENNReal.add_lt_top.2 ⟨hSi 1, hSi (-1)⟩
  refine ⟨fun ω ↦ (R ω).toReal, integrable_toReal_of_lintegral_ne_top hRm hRi.ne, ?_⟩
  filter_upwards [hVW, ae_lt_top' hRm hRi.ne] with ω heq hRfin
  intro t ht
  have habs : |V t ω| ≤ Real.exp (V t ω) + Real.exp (-V t ω) := by
    rcases le_total 0 (V t ω) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      linarith [Real.add_one_le_exp (V t ω), Real.exp_pos (-V t ω)]
    · rw [abs_of_nonpos hneg]
      linarith [Real.add_one_le_exp (-V t ω), Real.exp_pos (V t ω)]
  have hEN : ENNReal.ofReal |V t ω| ≤ R ω := by
    calc _ ≤ ENNReal.ofReal (Real.exp (V t ω) + Real.exp (-V t ω)) := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal (Real.exp (V t ω)) + ENNReal.ofReal (Real.exp (-V t ω)) :=
        ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ R ω := by
        apply add_le_add
        · exact le_iSup₂_of_le t ht (by simp)
        · exact le_iSup₂_of_le t ht (by simp)
  have hh := ENNReal.toReal_mono hRfin.ne hEN
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hh
  simpa only [Real.norm_eq_abs, heq t] using hh


/-- Coordinatewise Brownian motion has an integrable random bound uniform on compact intervals. -/
theorem exists_integrable_uniform_bound_brownianEuclidean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hW : ∀ j, IsBrownianReal (fun t ω ↦ W t ω j) P) (T : ℝ≥0) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, ‖W t ω‖ ≤ D ω := by
  choose D hDi hDb using fun j ↦ IsBrownianReal.exists_integrable_uniform_bound P
    (fun t ω ↦ W t ω j) (hW j) T
  refine ⟨fun ω ↦ ∑ j, D j ω, integrable_finsetSum _ fun j _ ↦ hDi j, ?_⟩
  filter_upwards [ae_all_iff.2 hDb] with ω hω
  intro t ht
  have hnorm (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ≤ ∑ j, ‖v j‖ := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun j _ ↦ norm_nonneg _,
      Finset.sum_sq_le_sq_sum_of_nonneg fun j _ ↦ norm_nonneg _⟩
  exact (hnorm _).trans (Finset.sum_le_sum fun j _ ↦ hω j t ht)

/-- An integrable initial vector plus Brownian motion admits a uniform integrable random bound. -/
theorem exists_integrable_uniform_bound_add_brownianEuclidean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (hξ : Integrable ξ P)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hW : ∀ j, IsBrownianReal (fun t ω ↦ W t ω j) P) (T : ℝ) :
    ∃ B : Ω → ℝ, Integrable B P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖ξ ω + W t.toNNReal ω‖ ≤ B ω := by
  obtain ⟨D, hDi, hDb⟩ := exists_integrable_uniform_bound_brownianEuclidean P W hW T.toNNReal
  refine ⟨fun ω ↦ ‖ξ ω‖ + D ω, hξ.norm.add hDi, ?_⟩
  filter_upwards [hDb] with ω hω
  intro t ht
  exact (norm_add_le _ _).trans (add_le_add le_rfl (hω t.toNNReal (Real.toNNReal_mono ht.2)))
end CKSD
