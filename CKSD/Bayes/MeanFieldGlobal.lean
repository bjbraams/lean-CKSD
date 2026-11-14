module
public import CKSD.Bayes.MeanFieldPicard
public import CKSD.Bayes.MeanFieldCore
public import CKSD.Bayes.MeanFieldParticles
/-!
# Global pathwise solutions with continuous additive forcing

An almost-surely continuous process with a.e. measurable sections has a measurable continuous-path
version on each bounded interval. Rational coordinates and the Borel reconstruction map supply
these versions. Lipschitz drift solutions are consistent on overlapping intervals, so they glue
to a process with measurable sections and almost-surely continuous global paths.

The finite-configuration drift therefore gives existence of the general particle system, without
moment assumptions on the initial states. Mathlib supplies measurability, integration and continuous
path APIs; the finite-interval solver and TauCeti integral Grönwall estimates are imported locally.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [NormedSpace ℝ E] in
/-- An almost-surely continuous process with almost-everywhere measurable sections has a measurable continuous-path version on every compact interval. -/
theorem exists_measurable_continuousPath_version (P : Measure Ω) (F : ℝ → Ω → E)
    (hFm : ∀ t, AEMeasurable (F t) P) (hFc : ∀ᵐ ω ∂P, Continuous (fun t ↦ F t ω))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ G : Ω → C(Icc (0 : ℝ) T, E), Measurable G ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, G ω t = F t ω := by
  let τ (q : ℚ) : ℝ := projIcc 0 T hT q
  let f (q : ℚ) : Ω → E := (hFm (τ q)).mk (F (τ q))
  have hfm (q : ℚ) : Measurable (f q) := (hFm (τ q)).measurable_mk
  let G : Ω → C(Icc (0 : ℝ) T, E) := fun ω ↦ pathOfRationalCoordinates hT (fun q ↦ f q ω)
  refine ⟨G, (measurable_pathOfRationalCoordinates hT).comp
    (measurable_pi_iff.2 hfm), ?_⟩
  have heq : ∀ᵐ ω ∂P, ∀ q : ℚ, F (τ q) ω = f q ω :=
    ae_all_iff.2 fun q ↦ (hFm (τ q)).ae_eq_mk
  filter_upwards [hFc, heq] with ω hc hω
  let p : C(Icc (0 : ℝ) T, E) := ⟨fun t ↦ F t ω, hc.comp continuous_subtype_val⟩
  have hcoord : (fun q ↦ f q ω) = pathRationalCoordinates hT p := by
    funext q
    exact (hω q).symm
  intro t
  dsimp only [G]
  rw [hcoord, pathOfRationalCoordinates_apply]
  rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Two continuous paths with a common additive forcing and Lipschitz drift coincide. -/
theorem eqOn_of_forced_integral_eq (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (F x y : ℝ → E) (hx : Continuous x) (hy : Continuous y) {T : ℝ}
    (hxe : ∀ t ∈ Icc (0 : ℝ) T, x t = F t + ∫ s in (0 : ℝ)..t, b (x s))
    (hye : ∀ t ∈ Icc (0 : ℝ) T, y t = F t + ∫ s in (0 : ℝ)..t, b (y s)) :
    EqOn x y (Icc (0 : ℝ) T) := by
  have hφ : Continuous (fun t ↦ ‖x t-y t‖) := (hx.sub hy).norm
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : x t-y t = ∫ s in (0 : ℝ)..t, b (x s)-b (y s) := by
    have hint := intervalIntegral.integral_sub (μ := volume) ((hb.continuous.comp hx).intervalIntegrable (0:ℝ) t)
      ((hb.continuous.comp hy).intervalIntegrable (0:ℝ) t)
    simp only [Function.comp_def] at hint
    rw [hint, hxe t ht, hye t ht]
    abel
  have hineq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖x t-y t‖ ≤ 0+(L:ℝ)*∫ s in (0:ℝ)..t, ‖x s-y s‖ := by
    rw [heq t ht, zero_add]
    calc _ ≤ ∫ s in (0:ℝ)..t, ‖b (x s)-b (y s)‖ := intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in (0:ℝ)..t, (L:ℝ)*‖x s-y s‖ :=
        intervalIntegral.integral_mono ht.1
          (((hb.continuous.comp hx).sub (hb.continuous.comp hy)).norm.intervalIntegrable _ _)
          ((hφ.const_mul _).intervalIntegrable _ _) (fun s ↦ hb.norm_sub_le _ _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  intro t ht
  have hgr := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn L.coe_nonneg hineq t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hgr) (norm_nonneg _)))

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- Consistent measurable compact paths glue to an almost-surely continuous process with measurable sections. -/
theorem exists_measurable_process_of_consistent_paths (P : Measure Ω)
    (S : (n : ℕ) → Ω → C(Icc (0:ℝ) ((n:ℝ)+1), E)) (hSm : ∀ n, Measurable (S n))
    (hcons : ∀ᵐ ω ∂P, ∀ (n m : ℕ) (t : ℝ), 0 ≤ t → t ≤ (n:ℝ)+1 → t ≤ (m:ℝ)+1 →
      (S n ω).IccExtend (by positivity) t = (S m ω).IccExtend (by positivity) t) :
    ∃ X : ℝ → Ω → E, (∀ t, Measurable (X t)) ∧
      ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧
        ∀ (n : ℕ) (t : Icc (0:ℝ) ((n:ℝ)+1)), X t ω = S n ω t := by
  classical
  let T : ℕ → ℝ := fun n ↦ (n:ℝ)+1
  have hT (n : ℕ) : 0 ≤ T n := by dsimp [T]; positivity
  let y (n : ℕ) (ω : Ω) : C(ℝ,E) := (S n ω).IccExtend (hT n)
  have hym (n : ℕ) (t : ℝ) : Measurable (fun ω ↦ y n ω t) :=
    (continuous_eval_const (projIcc 0 (T n) (hT n) t)).measurable.comp (hSm n)
  let N : ℝ → ℕ := fun t ↦ (exists_nat_gt (max 0 t)).choose
  have hNt (t : ℝ) : max 0 t < T (N t) := by
    have h := (exists_nat_gt (max 0 t)).choose_spec
    change max 0 t < (N t:ℝ) at h
    dsimp only [T]
    linarith
  let X : ℝ → Ω → E := fun t ω ↦ y (N t) ω (max 0 t)
  refine ⟨X, fun t ↦ hym (N t) (max 0 t), ?_⟩
  filter_upwards [hcons] with ω hω
  have hXeq (n : ℕ) (s : ℝ) (hs : max 0 s ≤ T n) : X s ω = y n ω (max 0 s) :=
    hω (N s) n (max 0 s) (le_max_left _ _) (hNt s).le hs
  have hXc : Continuous (fun t ↦ X t ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hloc : (fun s ↦ X s ω) =ᶠ[𝓝 t] fun s ↦ y (N t) ω (max 0 s) := by
      have hnear : ∀ᶠ s in 𝓝 t, max 0 s < T (N t) :=
        (continuous_const.max continuous_id).continuousAt.eventually (gt_mem_nhds (hNt t))
      filter_upwards [hnear] with s hs
      exact hXeq (N t) s hs.le
    have hc : Continuous (fun s : ℝ ↦ y (N t) ω (max 0 s)) :=
      (y (N t) ω).continuous.comp (continuous_const.max continuous_id)
    exact hc.continuousAt.congr_of_eventuallyEq hloc
  refine ⟨hXc, ?_⟩
  intro n t
  have he := hXeq n t (by rw [max_eq_right t.2.1]; exact t.2.2)
  simpa only [max_eq_right t.2.1, y, ContinuousMap.coe_IccExtend,
    Set.IccExtend_of_mem (h := hT n) (fun z ↦ S n ω z) t.2] using he

/-- Globally Lipschitz drifts admit measurable solutions for almost-surely continuous additive forcings. -/
theorem exists_global_solution_of_continuous_forcing (P : Measure Ω) (b : E → E)
    {L : ℝ≥0} (hb : LipschitzWith L b) (F : ℝ → Ω → E)
    (hFm : ∀ t, AEMeasurable (F t) P) (hFc : ∀ᵐ ω ∂P, Continuous (fun t ↦ F t ω)) :
    ∃ X : ℝ → Ω → E, (∀ t, Measurable (X t)) ∧
      ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω) ∧
        ∀ t ≥ 0, X t ω = F t ω + ∫ s in (0:ℝ)..t, b (X s ω) := by
  classical
  let T : ℕ → ℝ := fun n ↦ (n:ℝ)+1
  have hT (n : ℕ) : 0 ≤ T n := by dsimp [T]; positivity
  choose H hHm hH using fun n ↦ exists_measurable_continuousPath_version P F hFm hFc (hT n)
  let v : ℝ → E → E := fun _ x ↦ b x
  have hv : Continuous (Function.uncurry v) := hb.continuous.comp continuous_snd
  let S (n : ℕ) (ω : Ω) : C(Icc (0:ℝ) (T n), E) :=
    (pathForcingEquiv (hT n) v hv (fun _ ↦ hb)).symm (H n ω)
  have hSm (n : ℕ) : Measurable (S n) :=
    (lipschitzWith_pathForcingEquiv_symm (hT n) v hv (fun _ ↦ hb)).continuous.measurable.comp (hHm n)
  let y (n : ℕ) (ω : Ω) : C(ℝ,E) := (S n ω).IccExtend (hT n)
  have hye (n : ℕ) (ω : Ω) (hω : ∀ t : Icc (0:ℝ) (T n), H n ω t = F t ω)
      (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T n)) :
      y n ω t = F t ω + ∫ s in (0:ℝ)..t, b (y n ω s) := by
    have he := pathForcingEquiv_symm_apply_eq (hT n) v hv (fun _ ↦ hb) (H n ω) ⟨t,ht⟩
    change S n ω ⟨t,ht⟩ = H n ω ⟨t,ht⟩ + ∫ s in (0:ℝ)..t, b (y n ω s) at he
    rw [hω ⟨t,ht⟩] at he
    have hyv : y n ω t = S n ω ⟨t,ht⟩ := Set.IccExtend_of_mem (h := hT n) (fun z ↦ S n ω z) ht
    exact hyv.trans he
  have hcons : ∀ᵐ ω ∂P, ∀ (n m : ℕ) (t : ℝ), 0 ≤ t → t ≤ (n:ℝ)+1 → t ≤ (m:ℝ)+1 →
      (S n ω).IccExtend (by positivity) t = (S m ω).IccExtend (by positivity) t := by
    filter_upwards [ae_all_iff.2 hH] with ω hω
    intro n m t ht htn htm
    have he := eqOn_of_forced_integral_eq b hb (fun t ↦ F t ω) (y n ω) (y m ω)
      (y n ω).continuous (y m ω).continuous
      (fun s hs ↦ hye n ω (hω n) s ⟨hs.1,hs.2.trans htn⟩)
      (fun s hs ↦ hye m ω (hω m) s ⟨hs.1,hs.2.trans htm⟩)
    exact he ⟨ht,le_rfl⟩
  obtain ⟨X,hXm,hX⟩ := exists_measurable_process_of_consistent_paths P S hSm hcons
  refine ⟨X,hXm,?_⟩
  filter_upwards [hX,ae_all_iff.2 hH] with ω hω hFω
  refine ⟨hω.1,?_⟩
  intro t ht
  obtain ⟨n,hnt⟩ := exists_nat_gt t
  have htn : t ≤ T n := by dsimp [T]; linarith
  have hsame (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) : X s ω = y n ω s := by
    have hp := hω.2 n (⟨s,⟨hs.1,hs.2.trans htn⟩⟩ : Icc (0:ℝ) (T n))
    change X s ω = S n ω ⟨s,⟨hs.1,hs.2.trans htn⟩⟩ at hp
    rw [show y n ω s = S n ω ⟨s,⟨hs.1,hs.2.trans htn⟩⟩ from
      Set.IccExtend_of_mem (h := hT n) (fun z ↦ S n ω z) ⟨hs.1,hs.2.trans htn⟩]
    exact hp
  rw [hsame t ⟨ht,le_rfl⟩,hye n ω (hFω n) t ⟨ht,htn⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s ∈ Icc (0:ℝ) t := by simpa only [uIcc_of_le ht] using hs
  exact congrArg b (hsame s hst).symm

/-- General finite particle systems exist for iid initial states and Brownian forcings. -/
theorem exists_particleSystem_of_wassersteinLipschitz
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀) (N : ℕ) :
    ∃ X, IsParticleSystem b X₀ W N X P := by
  classical
  by_cases hN : 0 < N
  · let A := Fin N → EuclideanSpace ℝ (Fin d)
    let B : A → A := fun x i ↦ b (x i) (empiricalMeasure N x)
    have hB : LipschitzWith (2 * Real.toNNReal L) B := hb.lipschitzWith_particleDrift b hN
    let F : ℝ → Ω → A := fun t ω i ↦ X₀ i ω + W i t.toNNReal ω
    have hWm (i : ℕ) (t : ℝ≥0) : AEMeasurable (W i t) P := by
      have hc : AEMeasurable (fun ω (j : Fin d) ↦ W i t ω j) P :=
        AEMeasurable.of_eval fun j ↦ ((hiid.2.2.1 i).1 j).toIsPreBrownianReal.aemeasurable t
      convert (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hc using 1
      funext ω
      ext j
      rfl
    have hFm (t : ℝ) : AEMeasurable (F t) P :=
      AEMeasurable.of_eval fun i : Fin N ↦ (hiid.1 i).aemeasurable.add (hWm i t.toNNReal)
    have hFc : ∀ᵐ ω ∂P, Continuous (fun t ↦ F t ω) := by
      filter_upwards [ae_all_iff.2 (fun i : Fin N ↦ (hiid.2.2.1 i).ae_continuous_toNNReal)] with ω hω
      exact continuous_pi fun i ↦ continuous_const.add (hω i)
    obtain ⟨Z,hZm,hZ⟩ := exists_global_solution_of_continuous_forcing P B hB F hFm hFc
    let X : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d) :=
      fun i t ω ↦ if hi : i < N then Z t ω ⟨i,hi⟩ else 0
    refine ⟨X, ?_, ?_⟩
    · intro i t
      by_cases hi : i < N
      · simpa only [X, dite_eq_left hi, Function.comp_def] using (measurable_pi_apply (⟨i,hi⟩ : Fin N)).comp (hZm t)
      · simpa only [X, dite_eq_right hi] using (measurable_const : Measurable (fun _ : Ω ↦ (0 : EuclideanSpace ℝ (Fin d))))
    · intro i hi
      filter_upwards [hZ] with ω hω
      refine ⟨?_, ?_⟩
      · simpa only [X, dite_eq_left hi, Function.comp_def] using (continuous_apply (⟨i,hi⟩ : Fin N)).comp hω.1
      · intro t ht
        have hXeq (s : ℝ) : (fun j : Fin N ↦ X j s ω) = Z s ω := by
          funext j
          simp only [X, dite_eq_left j.isLt]
        have he := congrFun (hω.2 t ht) (⟨i,hi⟩ : Fin N)
        have hp := (ContinuousLinearMap.proj (⟨i,hi⟩ : Fin N) : A →L[ℝ] EuclideanSpace ℝ (Fin d)).intervalIntegral_comp_comm (μ := volume)
          ((hB.continuous.comp hω.1).intervalIntegrable (0:ℝ) t)
        change (∫ s in (0:ℝ)..t, B (Z s ω) ⟨i,hi⟩) =
          (∫ s in (0:ℝ)..t, B (Z s ω)) ⟨i,hi⟩ at hp
        change Z t ω ⟨i,hi⟩ = X₀ i ω + W i t.toNNReal ω +
          (∫ s in (0:ℝ)..t, B (Z s ω)) ⟨i,hi⟩ at he
        rw [← hp] at he
        change X i t ω = X₀ i ω + (∫ s in (0:ℝ)..t,
          b (X i s ω) (empiricalMeasure N fun j : Fin N ↦ X j s ω)) + W i t.toNNReal ω
        have hint : (fun s ↦ b (X i s ω) (empiricalMeasure N fun j : Fin N ↦ X j s ω)) =
            fun s ↦ B (Z s ω) ⟨i,hi⟩ := by
          funext s
          rw [hXeq]
          simp only [X, dite_eq_left hi, B]
        rw [hint]
        have he' : Z t ω ⟨i,hi⟩ = X₀ i ω + (∫ s in (0:ℝ)..t, B (Z s ω) ⟨i,hi⟩) + W i t.toNNReal ω := by
          rw [he]
          abel
        simpa only [X, dite_eq_left hi] using he' 
  · have hNz : N = 0 := by omega
    refine ⟨fun _ _ _ ↦ 0, fun _ _ ↦ measurable_const, ?_⟩
    intro i hi
    omega
end CKSD
