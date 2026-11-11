module
public import CKSD.Bayes.MeanFieldParticles
public import CKSD.Bayes.MeanFieldStability
public import CKSD.Bayes.MeanFieldPathLaws
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
/-!
# Pathwise stability for propagation of chaos

A synchronous finite-particle coupling is controlled by the first-Wasserstein discrepancy of
its reference empirical marginals. The configuration norm is the maximum of its particle norms,
so the stability constant is independent of the number of particles. Nonexpansive path
evaluation transfers a discrepancy of entire path laws uniformly to all their time marginals.

Mathlib supplies continuous path norms and finite-dimensional integration. Pinned TauCeti
supplies pushforward contraction for Wasserstein distance, and the local forced-equation
stability theorem supplies Grönwall's estimate.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Common forcing stability needs the drift perturbation only along the reference solution. -/
theorem norm_sub_le_exp_mul_integral_of_forced_eq_on_path
    {T : ℝ} (v w : ℝ → E → E)
    (hv : Continuous (Function.uncurry v)) (hw : Continuous (Function.uncurry w))
    {K : ℝ≥0} (hvK : ∀ s, LipschitzWith K (v s))
    (a : ℝ → ℝ) (ha : Continuous a) (ha0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s)
    (x y F : ℝ → E) (hx : Continuous x) (hy : Continuous y)
    (hvw : ∀ s ∈ Icc (0 : ℝ) T, ‖v s (y s) - w s (y s)‖ ≤ a s)
    (hxe : ∀ t ∈ Icc (0 : ℝ) T, x t = F t + ∫ s in (0 : ℝ)..t, v s (x s))
    (hye : ∀ t ∈ Icc (0 : ℝ) T, y t = F t + ∫ s in (0 : ℝ)..t, w s (y s)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤
      Real.exp ((K : ℝ) * T) * ∫ s in (0 : ℝ)..t, a s := by
  let w' : ℝ → E → E := fun t z ↦ v t z + (w t (y t) - v t (y t))
  have hw' : Continuous (Function.uncurry w') := hv.add
    (((hw.comp (continuous_id.prodMk hy)).sub (hv.comp (continuous_id.prodMk hy))).comp continuous_fst)
  have heq (s : ℝ) : w' s (y s) = w s (y s) := by dsimp [w']; abel
  apply norm_sub_le_exp_mul_integral_of_forced_eq v w' hv hw' hvK a ha ha0
    (fun s hs z ↦ ?_) x y F hx hy hxe
    (fun t ht ↦ by simpa only [heq] using hye t ht)
  have h : v s z - w' s z = v s (y s) - w s (y s) := by dsimp [w']; abel
  simpa only [h] using hvw s hs

section ParticleComparison
variable {d N : ℕ}
local notation "F" => EuclideanSpace ℝ (Fin d)
/-- Empirical laws have integrable norm. -/
theorem integrable_norm_empiricalMeasure (hN : 0 < N) (x : Fin N → F) :
    Integrable (fun z ↦ ‖z‖) (empiricalMeasure N x) := by
  dsimp only [empiricalMeasure]
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne'))
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact integrable_dirac (by finiteness)

/-- Common-forcing particle paths are controlled by the discrepancy of the reference empirical
marginals from their prescribed law. The norm of a configuration is its maximum particle norm. -/
theorem norm_sub_le_of_particle_integral_eq
    {T : ℝ} (_hT : 0 ≤ T) (hN : 0 < N)
    (b : F → Measure F → F) {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (μ : ℝ → Measure F) (hμp : ∀ t, IsProbabilityMeasure (μ t))
    (hμi : ∀ t, Integrable (fun z ↦ ‖z‖) (μ t))
    (hμb : Continuous (Function.uncurry (fun t x ↦ b x (μ t))))
    (x y f : ℝ → Fin N → F) (hx : Continuous x) (hy : Continuous y)
    (hxe : ∀ t ∈ Icc (0 : ℝ) T, x t = f t + ∫ s in (0 : ℝ)..t,
      fun j ↦ b (x s j) (empiricalMeasure N (x s)))
    (hye : ∀ t ∈ Icc (0 : ℝ) T, y t = f t + ∫ s in (0 : ℝ)..t,
      fun j ↦ b (y s j) (μ s))
    (r : ℝ) (hr : 0 ≤ r)
    (hW : ∀ t ∈ Icc (0 : ℝ) T,
      (TauCeti.wassersteinEDist 1 (empiricalMeasure N (y t)) (μ t)).toReal ≤ r) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤
      ((Real.toNNReal L : ℝ) * T * Real.exp (2 * (Real.toNNReal L : ℝ) * T)) * r := by
  let K := Real.toNNReal L
  let v : ℝ → (Fin N → F) → Fin N → F := fun _ z j ↦ b (z j) (empiricalMeasure N z)
  let w : ℝ → (Fin N → F) → Fin N → F := fun t z j ↦ b (z j) (μ t)
  have hvK : ∀ t, LipschitzWith (2 * K) (v t) := fun _ ↦ hb.lipschitzWith_particleDrift b hN
  have hv : Continuous (Function.uncurry v) := (hvK 0).continuous.comp continuous_snd
  have hw : Continuous (Function.uncurry w) := by
    apply continuous_pi
    intro j
    exact hμb.comp (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖v t (y t) - w t (y t)‖ ≤ (K : ℝ) * r := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg hr)).2
    intro j
    have hh := hb (y t j) (y t j) (empiricalMeasure N (y t)) (μ t)
      (isProbabilityMeasure_empiricalMeasure hN _) (hμp t)
      (integrable_norm_empiricalMeasure hN _) (hμi t)
    simp only [sub_self, norm_zero, zero_add] at hh
    have hnn : 0 ≤ (TauCeti.wassersteinEDist 1 (empiricalMeasure N (y t)) (μ t)).toReal := ENNReal.toReal_nonneg
    exact hh.trans ((mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) hnn).trans
      (mul_le_mul_of_nonneg_left (hW t ht) K.coe_nonneg))
  have hg := norm_sub_le_exp_mul_integral_of_forced_eq_on_path v w hv hw hvK
    (fun _ ↦ (K : ℝ) * r) continuous_const (fun _ _ ↦ mul_nonneg K.coe_nonneg hr)
    x y f hx hy hp hxe hye
  intro t ht
  have h := hg t ht
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, NNReal.coe_mul,
    NNReal.coe_ofNat] at h
  calc ‖x t - y t‖ ≤ Real.exp (2 * (K : ℝ) * T) * (t * ((K : ℝ) * r)) := h
    _ ≤ Real.exp (2 * (K : ℝ) * T) * (T * ((K : ℝ) * r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2 (mul_nonneg K.coe_nonneg hr)) (Real.exp_pos _).le
    _ = _ := by dsimp [K]; ring
end ParticleComparison

section Evaluation
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Pushforward of an empirical law is the empirical law of the mapped atoms. -/
theorem map_empiricalMeasure {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (N : ℕ) (x : Fin N → A) (f : A → B) (hf : Measurable f) :
    (empiricalMeasure N x).map f = empiricalMeasure N (fun j ↦ f (x j)) := by
  rw [empiricalMeasure, Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  · simp only [Measure.map_dirac' hf]
    rfl
  · exact hf.aemeasurable

omit [NormedSpace ℝ E] in
/-- Evaluation at any projected time cannot increase first-Wasserstein distance of path laws. -/
theorem wassersteinEDist_one_IccExtend_map_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ)
    (μ ν : Measure C(Icc (0 : ℝ) T, E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TauCeti.wassersteinEDist 1 (μ.map fun f ↦ f.IccExtend hT t)
      (ν.map fun f ↦ f.IccExtend hT t) ≤ TauCeti.wassersteinEDist 1 μ ν := by
  have hf : Measurable (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
  have hLip : LipschitzWith 1 (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ContinuousMap.sub_apply,
      ContinuousMap.coe_IccExtend, Set.IccExtend, Function.comp_apply] using
      (f - g).norm_coe_le_norm (Set.projIcc 0 T hT t)
  simpa only [ENNReal.coe_one, one_mul] using
    TauCeti.wassersteinEDist_map_le_mul (p := 1) measurable_edist hf hLip μ ν

omit [NormedSpace ℝ E] in
/-- Empirical marginal Wasserstein discrepancy is uniformly bounded by the discrepancy of path
laws, whenever the latter is finite. -/
theorem wassersteinEDist_one_empirical_IccExtend_toReal_le {N : ℕ} (hN : 0 < N)
    {T : ℝ} (hT : 0 ≤ T) (z : Fin N → C(Icc (0 : ℝ) T, E))
    (μ : Measure C(Icc (0 : ℝ) T, E)) [IsProbabilityMeasure μ]
    (hfin : TauCeti.wassersteinEDist 1 (empiricalMeasure N z) μ ≠ ∞) (t : ℝ) :
    (TauCeti.wassersteinEDist 1 (empiricalMeasure N (fun j ↦ (z j).IccExtend hT t))
      (μ.map fun f ↦ f.IccExtend hT t)).toReal ≤
        (TauCeti.wassersteinEDist 1 (empiricalMeasure N z) μ).toReal := by
  let := isProbabilityMeasure_empiricalMeasure hN z
  apply ENNReal.toReal_mono hfin
  have hm : Measurable (fun f : C(Icc (0 : ℝ) T, E) ↦ f.IccExtend hT t) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
  rw [← map_empiricalMeasure N z _ hm]
  exact wassersteinEDist_one_IccExtend_map_le hT t _ _
end Evaluation
end CKSD
