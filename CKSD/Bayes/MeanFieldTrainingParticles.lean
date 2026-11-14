module

public import CKSD.Bayes.MeanFieldChaosCoupling
public import CKSD.Bayes.MeanFieldChaosEquations
public import CKSD.Bayes.MeanFieldTrainingPaths
public import Mathlib.Analysis.Calculus.Deriv.Prod
/-!
# Uniform empirical marginal convergence for mean-field training

Deterministic finite-vector integral equations and synchronous coupling bound
all empirical marginal discrepancies by a single empirical path-law discrepancy.
Iid integrable reference paths therefore give almost-sure uniform first-Wasserstein
convergence on compact time intervals. No measurability of the supplied particle
paths is assumed; only the reference iid paths enter the probabilistic argument.

The proof reuses the local whole-path coupling estimate and pinned TauCeti's
empirical Wasserstein consistency theorem. Mathlib supplies finite-coordinate
integration, compact path norms and convergence bounds. This is the empirical
training limit in GAPS 104.53.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- A differentiable finite particle configuration satisfies its vector integral equation. -/
theorem particle_vector_integral_eq_of_has_deriv_at
    {N : ℕ} (hN : 0<N) (b : E → Measure E → E) {L : ℝ}
    (hb : IsWassersteinLipschitzDrift b L) (ξ : Fin N → E) (x : ℝ → Fin N → E)
    (hx0 : x 0 = ξ) (hx : ∀ i t, HasDerivAt (fun s ↦ x s i)
      (b (x t i) (empiricalMeasure N (x t))) t) :
    Continuous x ∧ ∀ t, x t = ξ + ∫ s in (0:ℝ)..t,
      fun j ↦ b (x s j) (empiricalMeasure N (x s)) := by
  let F : (Fin N → E) → Fin N → E := fun z j ↦ b (z j) (empiricalMeasure N z)
  have hd (t : ℝ) : HasDerivAt x (F (x t)) t := hasDerivAt_pi.mpr fun i ↦ hx i t
  have hc : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hd t).continuousAt
  refine ⟨hc, fun t ↦ ?_⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := t)
    (fun s _ ↦ hd s) (((hb.lipschitz_with_particle_drift b hN).continuous.comp hc).intervalIntegrable 0 t)
  rw [hx0] at hi
  dsimp only [F] at hi
  rw [hi]
  abel
/-- Coordinate reference integral equations combine into a finite-vector equation. -/
theorem reference_vector_integral_eq_on_icc
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0≤T)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Z : ℕ → Ω → C(Icc (0:ℝ) T,E)) (hZm : Measurable (Z 0)) (hZi : Integrable (Z 0) P)
    (ξ : ℕ → Ω → E)
    (hZe : ∀ i ω (t : Icc (0:ℝ) T), Z i ω t = ξ i ω + ∫ s in (0:ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)))
    (N : ℕ) (ω : Ω) (t : ℝ) (ht : t∈Icc (0:ℝ) T) :
    (fun j : Fin N ↦ (Z j ω).IccExtend hT t) =
      (fun j : Fin N ↦ ξ j ω) + ∫ s in (0:ℝ)..t,
        fun j : Fin N ↦ b ((Z j ω).IccExtend hT s)
          (P.map (fun z ↦ (Z 0 z).IccExtend hT s)) := by
  have hc : Continuous (fun q : ℝ × E ↦ b q.2
      (P.map (fun z ↦ (Z 0 z).IccExtend hT q.1))) := by
    have heq : (fun t x ↦ b x (P.map (fun z ↦ (Z 0 z).IccExtend hT t))) =
        nonlinearFrozenDrift P hT b (Z 0) hZm hZi := by
      funext t x
      rw [nonlinearFrozenDrift, path_marginal_law_to_measure]
    change Continuous (uncurry (fun t x ↦ b x (P.map (fun z ↦ (Z 0 z).IccExtend hT t))))
    rw [heq]
    exact continuous_nonlinear_frozen_drift P hT b hb (Z 0) hZm hZi
  have hv : Continuous (fun s ↦ fun j : Fin N ↦ b ((Z j ω).IccExtend hT s)
      (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) := by
    apply continuous_pi
    intro j
    exact hc.comp (continuous_id.prodMk ((Z j ω).IccExtend hT).continuous)
  funext j
  have hp := (ContinuousLinearMap.proj j : (Fin N → E) →L[ℝ] E).intervalIntegral_comp_comm
    (hv.intervalIntegrable (μ := volume) 0 t)
  change (∫ s in (0:ℝ)..t, b ((Z j ω).IccExtend hT s)
      (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) =
      (∫ s in (0:ℝ)..t, fun j : Fin N ↦ b ((Z j ω).IccExtend hT s)
        (P.map (fun z ↦ (Z 0 z).IccExtend hT s))) j at hp
  simp only [Pi.add_apply]
  change (Z j ω).IccExtend hT t = ξ j ω + _
  have hzt : (Z j ω).IccExtend hT t = Z j ω ⟨t,ht⟩ :=
    Set.IccExtend_of_mem (h := hT) (fun u ↦ Z j ω u) ht
  rw [← hp, hzt]
  exact hZe j ω ⟨t,ht⟩
/-- A deterministic particle/reference coupling controls all empirical marginal discrepancies
by one empirical path-law discrepancy. Particle maps need not be measurable. -/
theorem i_sup_wasserstein_e_dist_particle_marginals_le
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0≤T)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Z : ℕ → Ω → C(Icc (0:ℝ) T,E)) (hZm : Measurable (Z 0)) (hZi : Integrable (Z 0) P)
    (ξ : ℕ → Ω → E)
    (hZe : ∀ i ω (t : Icc (0:ℝ) T), Z i ω t = ξ i ω + ∫ s in (0:ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)))
    (θ : ℕ → ℕ → ℝ → Ω → E)
    (hθ : ∀ N, ∀ i<N, ∀ ω, θ N i 0 ω=ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
      (b (θ N i t ω) (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))) t)
    {N : ℕ} (hN : 0<N) (ω : Ω) :
    (⨆ t∈Icc (0:ℝ) T, TauCeti.wassersteinEDist 1
      (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))
      (P.map (fun z ↦ (Z 0 z).IccExtend hT t))) ≤
    ENNReal.ofReal ((((Real.toNNReal L : ℝ)*T*Real.exp (2*(Real.toNNReal L : ℝ)*T))+1) *
      (TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j ↦ Z j ω)) (P.map (Z 0))).toReal) := by
  let μ : ℝ → Measure E := fun t ↦ P.map (fun z ↦ (Z 0 z).IccExtend hT t)
  let x : ℝ → Fin N → E := fun t j ↦ θ N j t ω
  let y : ℝ → Fin N → E := fun t j ↦ (Z j ω).IccExtend hT t
  let C := (Real.toNNReal L : ℝ)*T*Real.exp (2*(Real.toNNReal L : ℝ)*T)
  let r := (TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j ↦ Z j ω)) (P.map (Z 0))).toReal
  have hxc := particle_vector_integral_eq_of_has_deriv_at hN b hb (fun j ↦ ξ j ω) x
    (funext fun j ↦ (hθ N j j.isLt ω).1) (fun j t ↦ (hθ N j j.isLt ω).2 t)
  have hyc : Continuous y := continuous_pi fun j ↦ ((Z j ω).IccExtend hT).continuous
  have hμp (t : ℝ) : IsProbabilityMeasure (μ t) := inferInstance
  have hμi (t : ℝ) : Integrable (fun v ↦ ‖v‖) (μ t) := by
    exact (integrable_map_measure continuous_norm.aestronglyMeasurable
      (((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hZm).aemeasurable)).2
      (integrable_icc_extend_eval P hT (Z 0) hZm hZi t).norm
  have hμb : Continuous (uncurry (fun t v ↦ b v (μ t))) := by
    have heq : (fun t x ↦ b x (μ t)) = nonlinearFrozenDrift P hT b (Z 0) hZm hZi := by
      funext t x
      rw [nonlinearFrozenDrift, path_marginal_law_to_measure]
    rw [heq]
    exact continuous_nonlinear_frozen_drift P hT b hb (Z 0) hZm hZi
  have hW (t : ℝ) : (TauCeti.wassersteinEDist 1 (empiricalMeasure N (y t)) (μ t)).toReal ≤ r := by
    have h := wasserstein_e_dist_one_empirical_icc_extend_to_real_le hN hT
      (fun j ↦ Z j ω) (P.map (Z 0))
      (wasserstein_e_dist_one_empirical_map_ne_top P hN (fun j ↦ Z j ω) (Z 0) hZm hZi) t
    have hE : Measurable (fun f : C(Icc (0:ℝ) T,E) ↦ f.IccExtend hT t) :=
      ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
    rw [hE.aemeasurable.map_map_of_aemeasurable hZm.aemeasurable] at h
    exact h
  have hxy := norm_sub_le_of_particle_integral_eq hT hN b hb μ hμp hμi hμb x y
    (fun _ j ↦ ξ j ω) hxc.1 hyc (fun t _ ↦ hxc.2 t)
    (fun t ht ↦ reference_vector_integral_eq_on_icc P hT b hb Z hZm hZi ξ hZe N ω t ht)
    r ENNReal.toReal_nonneg (fun t _ ↦ hW t)
  apply iSup₂_le
  intro t ht
  let η := empiricalMeasure N (x t)
  let ζ := empiricalMeasure N (y t)
  have hηp : IsProbabilityMeasure η := is_probability_measure_empirical_measure hN _
  have hζp : IsProbabilityMeasure ζ := is_probability_measure_empirical_measure hN _
  have hηζ : TauCeti.wassersteinEDist 1 η ζ ≠ ∞ :=
    (TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment measurable_edist
      (has_finite_moment_one_empirical_measure hN (x t))).mp (has_finite_moment_one_empirical_measure hN (y t))
  have hζμ : TauCeti.wassersteinEDist 1 ζ (μ t) ≠ ∞ :=
    wasserstein_e_dist_one_empirical_map_ne_top P hN (y t) _
      ((ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)).comp hZm)
      (integrable_icc_extend_eval P hT (Z 0) hZm hZi t)
  have htri := TauCeti.wassersteinEDist_triangle (p:=1) measurable_edist le_rfl η ζ (μ t)
  have hfin : TauCeti.wassersteinEDist 1 η (μ t) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hηζ,hζμ⟩) htri
  apply (ENNReal.le_ofReal_iff_toReal_le hfin (by positivity : 0≤(C+1)*r)).mpr
  have hrtri := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hηζ,hζμ⟩) htri
  rw [ENNReal.toReal_add hηζ hζμ] at hrtri
  have hηζb := wasserstein_e_dist_one_empirical_to_real_le_norm_sub hN (x t) (y t)
  have hh := hxy t ht
  have hhW := hW t
  change (TauCeti.wassersteinEDist 1 η (μ t)).toReal ≤ (C+1)*r
  dsimp only [η,ζ] at hrtri
  nlinarith
/-- Iid reference paths and differentiable interacting particles give almost-sure uniform
first-Wasserstein convergence of the empirical marginals on a fixed compact time interval. -/
theorem ae_tendsto_i_sup_empirical_particle_marginals
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0≤T)
    (b : E → Measure E → E) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (Z : ℕ → Ω → C(Icc (0:ℝ) T,E)) (hZm : ∀ i, Measurable (Z i)) (hZi : Integrable (Z 0) P)
    (hind : iIndepFun Z P) (hid : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (ξ : ℕ → Ω → E)
    (hZe : ∀ i ω (t : Icc (0:ℝ) T), Z i ω t = ξ i ω + ∫ s in (0:ℝ)..t,
      b ((Z i ω).IccExtend hT s) (P.map (fun z ↦ (Z 0 z).IccExtend hT s)))
    (θ : ℕ → ℕ → ℝ → Ω → E)
    (hθ : ∀ N, ∀ i<N, ∀ ω, θ N i 0 ω=ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
      (b (θ N i t ω) (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))) t) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦ ⨆ t∈Icc (0:ℝ) T, TauCeti.wassersteinEDist 1
      (empiricalMeasure N (fun j : Fin N ↦ θ N j t ω))
      (P.map (fun z ↦ (Z 0 z).IccExtend hT t))) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_empirical_wasserstein_one P Z hZm hZi hind hid] with ω hω
  let C := ((Real.toNNReal L : ℝ)*T*Real.exp (2*(Real.toNNReal L : ℝ)*T))+1
  have hc : Tendsto (fun N ↦ ENNReal.ofReal (C *
      (TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j ↦ Z j ω)) (P.map (Z 0))).toReal))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun N ↦ C * (TauCeti.wassersteinEDist 1
        (empiricalMeasure N (fun j ↦ Z j ω)) (P.map (Z 0))).toReal) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hω
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  exact i_sup_wasserstein_e_dist_particle_marginals_le P hT b hb Z (hZm 0) hZi ξ hZe θ hθ hN ω
end CKSD
