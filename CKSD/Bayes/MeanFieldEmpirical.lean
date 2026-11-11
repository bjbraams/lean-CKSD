module
public import CKSD.Bayes.MeanFieldChaosStability
public import CKSD.Bayes.MeanFieldGlobal
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Empirical
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
/-!
# Empirical Wasserstein convergence and image-law convergence

Almost surely, the empirical first-Wasserstein laws of iid integrable random variables converge
to their common law. The finite-sample convention used by CKSD is compared explicitly with
TauCeti's convention, which indexes a sample of size `n + 1` by `n`.

Mathlib supplies almost-sure convergence in distribution. Eventual measurability suffices for
weak convergence of image laws, so finitely many unconstrained particle paths do not affect the
limit. Pinned TauCeti supplies empirical Wasserstein consistency on separable metric spaces.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
/-- The finite-index empirical law agrees with TauCeti's offset sequence convention. -/
theorem empiricalMeasure_succ_eq_tauCeti {E : Type*} [MeasurableSpace E]
    (x : ℕ → E) (n : ℕ) :
    empiricalMeasure (n + 1) (fun j ↦ x j) =
      (TauCeti.Probability.empiricalMeasure x n : Measure E) := by
  rw [empiricalMeasure, TauCeti.Probability.empiricalMeasure_toMeasure, Finset.smul_sum]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)) (n + 1)

/-- Eventual measurability suffices for weak convergence of image laws under almost sure
pointwise convergence. -/
theorem tendsto_probabilityMeasure_map_of_eventually_aemeasurable_of_ae_tendsto
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → E) (Z : Ω → E) (hFm : ∀ᶠ n in atTop, AEMeasurable (F n) P)
    (hZm : AEMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ F n ω) atTop (𝓝 (Z ω))) :
    Tendsto (β := ProbabilityMeasure E) (fun n ↦ ⟨P.map (F n), inferInstance⟩) atTop
      (𝓝 ⟨P.map Z, inferInstance⟩) := by
  classical
  let F' : ℕ → Ω → E := fun n ↦ if AEMeasurable (F n) P then F n else Z
  have hF'm (n : ℕ) : AEMeasurable (F' n) P := by
    dsimp [F']
    split_ifs with hm
    · exact hm
    · exact hZm
  have hF'eq : ∀ᶠ n in atTop, F' n = F n := hFm.mono fun n hn ↦ by simp only [F', ite_eq_left hn]
  have hconv' : ∀ᵐ ω ∂P, Tendsto (fun n ↦ F' n ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hconv] with ω hω
    exact hω.congr' (hF'eq.mono fun n hn ↦ (congrFun hn ω).symm)
  have ht := tendstoInDistribution_of_ae_tendsto hF'm hZm hconv'
  exact ht.tendsto.congr' (hF'eq.mono fun n hn ↦ by rw [hn])

/-- Iid integrable random paths have almost surely consistent empirical first-Wasserstein laws. -/
theorem ae_tendsto_empirical_wasserstein_one
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → E)
    (hZm : ∀ i, Measurable (Z i)) (hZi : Integrable (Z 0) P)
    (hind : iIndepFun Z P) (hid : ∀ i, IdentDistrib (Z i) (Z 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦
      (TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j ↦ Z j ω)) (P.map (Z 0))).toReal)
        atTop (𝓝 0) := by
  let μ : ProbabilityMeasure E := ⟨P.map (Z 0), inferInstance⟩
  have hμ : TauCeti.HasFiniteMoment 1 (μ : Measure E) :=
    hasFiniteMoment_one_map_of_integrable P (Z 0) (hZm 0) hZi
  have hHasLaw (i : ℕ) : HasLaw (Z i) (μ : Measure E) P := ⟨(hZm i).aemeasurable, (hid i).map_eq⟩
  have hstrong := TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae
    (p := 1) (by norm_num) (by norm_num) hμ hind hHasLaw
  filter_upwards [hstrong] with ω hω
  have hr : Tendsto (fun n ↦ (TauCeti.wassersteinEDist 1
      (empiricalMeasure (n + 1) (fun j ↦ Z j ω)) (P.map (Z 0))).toReal) atTop (𝓝 0) := by
    have hr0 := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hω
    change Tendsto (fun n ↦ (TauCeti.wassersteinEDist 1
      (TauCeti.Probability.empiricalMeasure (fun i ↦ Z i ω) n : Measure E)
      (P.map (Z 0))).toReal) atTop (𝓝 (0 : ℝ≥0∞).toReal) at hr0
    simpa only [← empiricalMeasure_succ_eq_tauCeti, ENNReal.toReal_zero] using hr0
  apply (hr.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact congrArg (fun M : ℕ ↦
    (TauCeti.wassersteinEDist 1 (empiricalMeasure M (fun j ↦ Z j ω)) (P.map (Z 0))).toReal)
      (Nat.sub_add_cancel hN)
/-- Finite empirical laws have finite first moment. -/
theorem hasFiniteMoment_one_empiricalMeasure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (x : Fin N → E) :
    TauCeti.HasFiniteMoment 1 (empiricalMeasure N x) := by
  let P : Measure (Fin N) := empiricalMeasure N id
  let := isProbabilityMeasure_empiricalMeasure hN (id : Fin N → Fin N)
  have hi : Integrable x P := Integrable.of_bound (measurable_of_finite x).aestronglyMeasurable
    ‖x‖ (ae_of_all _ fun j ↦ norm_le_pi_norm x j)
  have hh := hasFiniteMoment_one_map_of_integrable P x (measurable_of_finite x) hi
  simpa only [P, map_empiricalMeasure N id x (measurable_of_finite x), id_eq] using hh

/-- A finite empirical law and an integrable image law are at finite first-Wasserstein distance. -/
theorem wassersteinEDist_one_empirical_map_ne_top
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) (x : Fin N → E)
    (Z : Ω → E) (hZm : Measurable Z) (hZi : Integrable Z P) :
    TauCeti.wassersteinEDist 1 (empiricalMeasure N x) (P.map Z) ≠ ∞ := by
  let := isProbabilityMeasure_empiricalMeasure hN x
  exact (TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment
    measurable_edist (hasFiniteMoment_one_empiricalMeasure hN x)).mp
    (hasFiniteMoment_one_map_of_integrable P Z hZm hZi)
/-- Continuous process paths give an almost-everywhere measurable compact-path constructor. -/
theorem aemeasurable_pathOn_of_ae_continuous
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (F : ℝ → Ω → E) (hFm : ∀ t, AEMeasurable (F t) P)
    (hFc : ∀ᵐ ω ∂P, Continuous (fun t ↦ F t ω)) {T : ℝ} (hT : 0 ≤ T) :
    AEMeasurable (fun ω ↦ pathOn T (fun t ↦ F t ω)) P := by
  obtain ⟨G, hGm, hG⟩ := exists_measurable_continuousPath_version P F hFm hFc hT
  apply hGm.aemeasurable.congr
  filter_upwards [hG, hFc] with ω hω hc
  apply ContinuousMap.ext
  intro t
  rw [pathOn_apply_of_continuousOn T (fun s ↦ F s ω) hc.continuousOn t]
  exact hω t

/-- Vanishing uniform coupling errors imply weak convergence of every fixed finite set of
particle laws. Only eventual measurability is required for the particle vectors. -/
theorem tendsto_joint_image_laws_of_ae_uniform_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → ℕ → Ω → E) (Z : ℕ → Ω → E) (k : ℕ)
    (hXm : ∀ᶠ N in atTop, AEMeasurable (fun ω (i : Fin k) ↦ X N i ω) P)
    (hZm : ∀ i, AEMeasurable (Z i) P) (r : ℕ → Ω → ℝ) (C : ℝ)
    (hr : ∀ᵐ ω ∂P, Tendsto (fun N ↦ r N ω) atTop (𝓝 0))
    (hbound : ∀ N, 0 < N → ∀ᵐ ω ∂P, ∀ i : Fin N, ‖X N i ω - Z i ω‖ ≤ C * r N ω) :
    Tendsto (β := ProbabilityMeasure (Fin k → E))
      (fun N ↦ ⟨P.map (fun ω (i : Fin k) ↦ X N i ω), inferInstance⟩) atTop
      (𝓝 ⟨P.map (fun ω (i : Fin k) ↦ Z i ω), inferInstance⟩) := by
  have hall : ∀ᵐ ω ∂P, ∀ N, ∀ i : Fin N, ‖X N i ω - Z i ω‖ ≤ C * r N ω := by
    apply ae_all_iff.2
    intro N
    by_cases hN : 0 < N
    · exact hbound N hN
    · exact ae_of_all _ fun _ i ↦ False.elim (hN (lt_of_le_of_lt (Nat.zero_le i) i.isLt))
  apply tendsto_probabilityMeasure_map_of_eventually_aemeasurable_of_ae_tendsto P _ _ hXm
    (AEMeasurable.of_eval fun i ↦ hZm i)
  filter_upwards [hr, hall] with ω hrω hω
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlimit : Tendsto (fun N ↦ C * r N ω) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrω
  apply squeeze_zero' (Eventually.of_forall fun N ↦ norm_nonneg _) _ hlimit
  filter_upwards [eventually_ge_atTop k] with N hN
  exact hω N ⟨i, lt_of_lt_of_le i.isLt hN⟩
end CKSD
