module

public import CKSD.Processes.Kalman.Recursion

/-!
# Gaussian laws and innovations of the Kalman filter

Under `KalmanModel.GaussianInputs`, prediction and filtering errors are centred Gaussian
and independent of the preceding observation record. The update lemmas yield conditional
state laws, independent innovations and the product predictive density in
`KalmanModel.kalman_filter`.
Gaussian shift and conditioning tools are provided by `CKSD.Processes.GaussianConditioning`.
Source: GAPS 106.7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

namespace KalmanModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (M : KalmanModel ι κ)

section Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of the Kalman filter theorem: positive-semidefinite noise and initial
covariances, a Gaussian initial state, independent Gaussian white noises independent of the
initial state, and nonsingular innovation covariances. -/
structure GaussianInputs (P : Measure Ω) (x₀ : Ω → EuclideanSpace ℝ ι)
    (w : ℕ → Ω → EuclideanSpace ℝ ι) (v : ℕ → Ω → EuclideanSpace ℝ κ) : Prop where
  /-- The state-noise covariance `Q_t` is positive semidefinite at every time. -/
  stateCov_posSemidef : ∀ t, (M.stateCov t).PosSemidef
  /-- The observation-noise covariance `R_t` is positive semidefinite at every time. -/
  obsCov_posSemidef : ∀ t, (M.obsCov t).PosSemidef
  /-- The initial state covariance is positive semidefinite. -/
  initCov_posSemidef : M.initCov.PosSemidef
  /-- The initial state has the Gaussian law with the prescribed initial mean and covariance. -/
  hasLaw_init : HasLaw x₀ (multivariateGaussian M.initMean M.initCov) P
  /-- Each state noise is centred Gaussian with covariance `Q_t`. -/
  hasLaw_stateNoise : ∀ t, HasLaw (w t) (multivariateGaussian 0 (M.stateCov t)) P
  /-- Each observation noise is centred Gaussian with covariance `R_t`. -/
  hasLaw_obsNoise : ∀ t, HasLaw (v t) (multivariateGaussian 0 (M.obsCov t)) P
  /-- State noises at distinct times are jointly independent. -/
  iIndepFun_stateNoise : iIndepFun w P
  /-- Observation noises at distinct times are jointly independent. -/
  iIndepFun_obsNoise : iIndepFun v P
  /-- The entire state-noise sequence is independent of the entire observation-noise sequence. -/
  indepFun_noise : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P
  /-- The initial state is independent of the paired sequences of both noise types. -/
  indepFun_init_noise : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P
  /-- Each innovation covariance is nonsingular, so its Gaussian law has a density. -/
  innovCov_det_ne_zero : ∀ t, (M.innovCov t).det ≠ 0

variable {M} {P : Measure Ω} [IsProbabilityMeasure P] {x₀ : Ω → EuclideanSpace ℝ ι}
  {w : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℕ → Ω → EuclideanSpace ℝ κ}

namespace GaussianInputs

variable (h : M.GaussianInputs P x₀ w v)
include h

omit [IsProbabilityMeasure P] in
/-- Every predicted covariance is positive semidefinite. -/
theorem predCov_posSemidef' (t : ℕ) : (M.predCov t).PosSemidef :=
  M.predCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef h.initCov_posSemidef
    h.innovCov_det_ne_zero t

/-- The prediction error and the observation record at time `t` are jointly almost everywhere
measurable, and the observation noise at time `t` is independent of them. -/
theorem aemeasurable_indepFun_predErr (t : ℕ) :
    AEMeasurable (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P ∧
      IndepFun (v t) (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P := by
  obtain ⟨G, hG, hGeq⟩ := M.exists_predErr_obsPrefix_eq_comp x₀ w v t
  have hpair : (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) =
      G ∘ fun ω ↦ (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω) := funext hGeq
  have hx₀ := h.hasLaw_init.aemeasurable
  have hw := fun t ↦ (h.hasLaw_stateNoise t).aemeasurable
  have hv := fun t ↦ (h.hasLaw_obsNoise t).aemeasurable
  rw [hpair]
  refine ⟨hG.comp_aemeasurable (hx₀.prodMk ((AEMeasurable.of_eval hw).prodMk
    (AEMeasurable.of_eval fun i : Fin t ↦ hv i))), ?_⟩
  exact (indepFun_apply_prefix_of_indepFun hx₀ hw hv h.iIndepFun_obsNoise h.indepFun_noise
    h.indepFun_init_noise t).comp measurable_id hG

/-- The filtering error at time `t` and the observation record up to time `t` are jointly
almost everywhere measurable, and the state noise at time `t` is independent of them. -/
theorem aemeasurable_indepFun_filtErr (t : ℕ) :
    AEMeasurable (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) P ∧
      IndepFun (w t) (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) P := by
  obtain ⟨G, hG, hGeq⟩ := M.exists_filtErr_obsPrefix_eq_comp x₀ w v t
  have hpair : (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) =
      G ∘ fun ω ↦ (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω) := funext hGeq
  have hx₀ := h.hasLaw_init.aemeasurable
  have hw := fun t ↦ (h.hasLaw_stateNoise t).aemeasurable
  have hv := fun t ↦ (h.hasLaw_obsNoise t).aemeasurable
  rw [hpair]
  refine ⟨hG.comp_aemeasurable (hx₀.prodMk ((AEMeasurable.of_eval fun i : Fin t ↦ hw i).prodMk
    (AEMeasurable.of_eval hv))), ?_⟩
  exact (indepFun_apply_prefix_of_indepFun' hx₀ hw hv h.iIndepFun_stateNoise h.indepFun_noise
    h.indepFun_init_noise t).comp measurable_id hG

/-- Measurement update. If the prediction error at time `t` has law `N(0, P_{t|t-1})` and is
independent of `y_0, …, y_{t-1}`, then the innovation has law `N(0, Σ_t)`, the filtering error
has law `N(0, P_{t|t})` and is independent of `y_0, …, y_t`, and the innovation is independent
of `y_0, …, y_{t-1}`. -/
theorem measurement_update (t : ℕ)
    (hlaw : HasLaw (M.predErr x₀ w v t) (multivariateGaussian 0 (M.predCov t)) P)
    (hind : IndepFun (M.predErr x₀ w v t) (M.obsPrefix x₀ w v t) P) :
    HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P ∧
      HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P ∧
      IndepFun (M.filtErr x₀ w v t) (M.obsPrefix x₀ w v (t + 1)) P ∧
      IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P := by
  obtain ⟨hm, hF⟩ := h.aemeasurable_indepFun_predErr t
  have hPt := h.predCov_posSemidef' t
  have hRt := h.obsCov_posSemidef t
  have hvt := h.hasLaw_obsNoise t
  have hεv : IndepFun (M.predErr x₀ w v t) (v t) P :=
    (hF.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst).symm
  set H := M.observation t
  set K := M.gain t
  have hinnov : M.innovation x₀ w v t = fun ω ↦ Matrix.toEuclideanLin H (M.predErr x₀ w v t ω) +
      Matrix.toEuclideanLin (1 : Matrix κ κ ℝ) (v t ω) := by
    funext ω
    simp [innovation_eq, H]
  have hfilt : M.filtErr x₀ w v t = fun ω ↦
      Matrix.toEuclideanLin (1 - K * H) (M.predErr x₀ w v t ω) +
        Matrix.toEuclideanLin (-K) (v t ω) := by
    funext ω
    exact M.filtErr_eq x₀ w v t ω
  have hlawe : HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P := by
    have := hasLaw_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv H 1
    rw [hinnov]
    convert this using 2
    simp [innovCov, innovCovOf, H]
  have hlawf : HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P := by
    have := hasLaw_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv (1 - K * H) (-K)
    rw [M.filtCov_eq_joseph (h.innovCov_det_ne_zero t)] at this
    rw [hfilt]
    exact this
  have hfe : IndepFun (M.filtErr x₀ w v t) (M.innovation x₀ w v t) P := by
    rw [hfilt, hinnov]
    exact indepFun_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv (1 - K * H) (-K) H 1
      (M.filtErr_innovation_cross (h.innovCov_det_ne_zero t))
  -- The record before time `t` is independent of the pair (prediction error, noise).
  have hYεv : IndepFun (M.obsPrefix x₀ w v t) (fun ω ↦ (M.predErr x₀ w v t ω, v t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hm.snd hm.fst hvt.aemeasurable hind.symm
      (hF.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm
  have hYfe : IndepFun (M.obsPrefix x₀ w v t)
      (fun ω ↦ (M.filtErr x₀ w v t ω, M.innovation x₀ w v t ω)) P := by
    have := hYεv.comp (φ := id) (ψ := fun q ↦
      (Matrix.toEuclideanLin (1 - K * H) q.1 + Matrix.toEuclideanLin (-K) q.2,
        Matrix.toEuclideanLin H q.1 + Matrix.toEuclideanLin (1 : Matrix κ κ ℝ) q.2))
      measurable_id (by fun_prop)
    rw [hfilt, hinnov]
    simpa only [Function.comp_def, id] using this
  have hfm : AEMeasurable (M.filtErr x₀ w v t) P := hlawf.aemeasurable
  have hem : AEMeasurable (M.innovation x₀ w v t) P := hlawe.aemeasurable
  have hf_eY : IndepFun (M.filtErr x₀ w v t)
      (fun ω ↦ (M.innovation x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hfm hem hm.snd hfe hYfe.symm
  have heY : IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P := by
    have hc := hYfe.comp (φ := id) (ψ := Prod.snd) measurable_id measurable_snd
    simpa only [Function.comp_def, id] using hc.symm
  refine ⟨hlawe, hlawf, ?_, heY⟩
  have hY : M.obsPrefix x₀ w v (t + 1) = fun ω ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ) (Fin.last t)).symm
        (M.innovation x₀ w v t ω + Matrix.toEuclideanLin (M.observation t)
          (M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t),
          M.obsPrefix x₀ w v t ω) := funext (M.obsPrefix_succ_eq x₀ w v t)
  have hmeas : Measurable fun q : EuclideanSpace ℝ κ ×
      (Fin t → EuclideanSpace ℝ κ) ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ) (Fin.last t)).symm
        (q.1 + Matrix.toEuclideanLin (M.observation t) (M.predMean (extendObservations q.2) t),
          q.2) := by
    refine (MeasurableEquiv.measurable _).comp (Measurable.prodMk ?_ measurable_snd)
    refine measurable_fst.add ?_
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
      Matrix.toEuclideanLin (M.observation t) z).comp
      ((M.measurable_predMean (y := fun i (q : EuclideanSpace ℝ κ ×
        (Fin t → EuclideanSpace ℝ κ)) ↦ extendObservations q.2 i)
        (fun i ↦ (measurable_extendObservations_apply i).comp measurable_snd) t))
  have hc := hf_eY.comp (φ := id) measurable_id hmeas
  rw [hY]
  simpa only [Function.comp_def, id] using hc

/-- Time update. If the filtering error at time `t` has law `N(0, P_{t|t})` and is independent
of `y_0, …, y_t`, then the prediction error at time `t + 1` has law `N(0, P_{t+1|t})` and is
independent of `y_0, …, y_t`. -/
theorem time_update (t : ℕ)
    (hlaw : HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P)
    (hind : IndepFun (M.filtErr x₀ w v t) (M.obsPrefix x₀ w v (t + 1)) P) :
    HasLaw (M.predErr x₀ w v (t + 1)) (multivariateGaussian 0 (M.predCov (t + 1))) P ∧
      IndepFun (M.predErr x₀ w v (t + 1)) (M.obsPrefix x₀ w v (t + 1)) P := by
  obtain ⟨hm, hF⟩ := h.aemeasurable_indepFun_filtErr t
  have hPf := M.filtCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef
    h.initCov_posSemidef h.innovCov_det_ne_zero t
  have hwt := h.hasLaw_stateNoise t
  have hφw : IndepFun (M.filtErr x₀ w v t) (w t) P :=
    (hF.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst).symm
  set F := M.transition t
  have hpred : M.predErr x₀ w v (t + 1) = fun ω ↦
      Matrix.toEuclideanLin F (M.filtErr x₀ w v t ω) +
        Matrix.toEuclideanLin (1 : Matrix ι ι ℝ) (w t ω) := by
    funext ω
    simp [predErr_succ, F]
  have hYφw : IndepFun (M.obsPrefix x₀ w v (t + 1))
      (fun ω ↦ (M.filtErr x₀ w v t ω, w t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hm.snd hm.fst hwt.aemeasurable hind.symm
      (hF.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm
  have hc := hYφw.comp (φ := id) (ψ := fun q ↦ Matrix.toEuclideanLin F q.1 +
    Matrix.toEuclideanLin (1 : Matrix ι ι ℝ) q.2) measurable_id (by fun_prop)
  rw [hpred]
  refine ⟨?_, ?_⟩
  swap
  · simpa only [Function.comp_def, id] using hc.symm
  have := hasLaw_toEuclideanLin_add_of_indepFun hPf (h.stateCov_posSemidef t) hlaw hwt hφw F 1
  convert this using 2
  simp [predCov, filtCov, F]

/-- The prediction errors: at every time `t`, `x_t - x_{t|t-1}` has law `N(0, P_{t|t-1})` and
is independent of `y_0, …, y_{t-1}`. -/
theorem predErr_hasLaw_indepFun (t : ℕ) :
    HasLaw (M.predErr x₀ w v t) (multivariateGaussian 0 (M.predCov t)) P ∧
      IndepFun (M.predErr x₀ w v t) (M.obsPrefix x₀ w v t) P := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · have hmap := TauCeti.Probability.map_affine_multivariateGaussian M.initMean
        h.initCov_posSemidef (1 : Matrix ι ι ℝ) (-M.initMean)
      simp only [Matrix.toLpLin_one, LinearMap.id_apply, add_neg_cancel, Matrix.one_mul,
        Matrix.transpose_one, Matrix.mul_one] at hmap
      have hc := HasLaw.comp (Y := fun x ↦ x + -M.initMean) ⟨by fun_prop, hmap⟩ h.hasLaw_init
      rw [show M.predCov 0 = M.initCov from rfl]
      convert hc using 1
      funext ω
      simp [predErr, state, predMean, sub_eq_add_neg]
    · have hc : M.obsPrefix x₀ w v 0 = fun _ ↦ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ κ) :=
        funext fun _ ↦ Subsingleton.elim _ _
      rw [hc]
      exact indepFun_const_right _ _
  | succ t ih =>
    obtain ⟨-, hlawf, hindf, -⟩ := h.measurement_update t ih.1 ih.2
    exact h.time_update t hlawf hindf

/-- Conditionally on `y_0, …, y_t`, the state `x_t` is Gaussian with the filtered mean and
covariance. -/
theorem condDistrib_state (t : ℕ) :
    ∀ᵐ ys ∂(P.map (M.obsPrefix x₀ w v (t + 1))),
      condDistrib (M.state x₀ w t) (M.obsPrefix x₀ w v (t + 1)) P ys =
        multivariateGaussian (M.filtMean (extendObservations ys) t) (M.filtCov t) := by
  obtain ⟨hlaw, hind⟩ := h.predErr_hasLaw_indepFun t
  obtain ⟨-, hlawf, hindf, -⟩ := h.measurement_update t hlaw hind
  have hx : M.state x₀ w t = fun ω ↦
      M.filtMean (extendObservations (M.obsPrefix x₀ w v (t + 1) ω)) t +
        M.filtErr x₀ w v t ω := by
    funext ω
    rw [M.filtMean_congr (y' := fun i ↦ M.obsProc x₀ w v i ω) fun i hi ↦ by
      simp [extendObservations_of_lt _ (Nat.lt_succ_of_le hi), obsPrefix]]
    simp [filtErr]
  rw [hx]
  exact condDistrib_add_eq_multivariateGaussian
    (M.measurable_filtMean_extendObservations (t + 1) t)
    (h.aemeasurable_indepFun_filtErr t).1.snd
    (M.filtCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef h.initCov_posSemidef
      h.innovCov_det_ne_zero t) hlawf hindf.symm

/-- Conditionally on `y_0, …, y_t`, the state `x_{t+1}` is Gaussian with the predicted mean and
covariance. -/
theorem condDistrib_state_succ (t : ℕ) :
    ∀ᵐ ys ∂(P.map (M.obsPrefix x₀ w v (t + 1))),
      condDistrib (M.state x₀ w (t + 1)) (M.obsPrefix x₀ w v (t + 1)) P ys =
        multivariateGaussian (M.predMean (extendObservations ys) (t + 1))
          (M.predCov (t + 1)) := by
  obtain ⟨hlaw, hind⟩ := h.predErr_hasLaw_indepFun (t + 1)
  have hx : M.state x₀ w (t + 1) = fun ω ↦
      M.predMean (extendObservations (M.obsPrefix x₀ w v (t + 1) ω)) (t + 1) +
        M.predErr x₀ w v (t + 1) ω := by
    funext ω
    rw [M.predMean_congr (y' := fun i ↦ M.obsProc x₀ w v i ω) fun i hi ↦ by
      simp [extendObservations_of_lt _ hi, obsPrefix]]
    simp [predErr]
  rw [hx]
  exact condDistrib_add_eq_multivariateGaussian
    (M.measurable_predMean_extendObservations (t + 1) (t + 1))
    (h.aemeasurable_indepFun_predErr (t + 1)).1.snd (h.predCov_posSemidef' (t + 1)) hlaw
    hind.symm

/-- The innovation at time `t` has law `N(0, Σ_t)`. -/
theorem hasLaw_innovation (t : ℕ) :
    HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P :=
  (h.measurement_update t (h.predErr_hasLaw_indepFun t).1 (h.predErr_hasLaw_indepFun t).2).1

/-- The innovation at time `t` is independent of `y_0, …, y_{t-1}`. -/
theorem indepFun_innovation_obsPrefix (t : ℕ) :
    IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P :=
  (h.measurement_update t (h.predErr_hasLaw_indepFun t).1
    (h.predErr_hasLaw_indepFun t).2).2.2.2

/-- The innovations are mutually independent. -/
theorem iIndepFun_innovation : iIndepFun (M.innovation x₀ w v) P := by
  refine iIndepFun_of_indepFun_finPrefix fun n ↦ ?_
  let Ψ : (Fin n → EuclideanSpace ℝ κ) → Fin n → EuclideanSpace ℝ κ :=
    fun ys i ↦ ys i - Matrix.toEuclideanLin (M.observation i)
      (M.predMean (extendObservations ys) i)
  have hΨ : Measurable Ψ := by
    refine measurable_pi_iff.mpr fun i ↦ (measurable_pi_apply i).sub ?_
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
      Matrix.toEuclideanLin (M.observation i) z).comp
      (M.measurable_predMean_extendObservations n i)
  have hpre : (fun ω (i : Fin n) ↦ M.innovation x₀ w v i ω) =
      Ψ ∘ M.obsPrefix x₀ w v n := by
    funext ω i
    have hpm : M.predMean (extendObservations (M.obsPrefix x₀ w v n ω)) i =
        M.predMean (fun j ↦ M.obsProc x₀ w v j ω) i :=
      M.predMean_congr fun j hj ↦ by simp [extendObservations_of_lt _ (hj.trans i.2), obsPrefix]
    simp only [Function.comp_apply, Ψ, innovation, hpm]
    rfl
  rw [hpre]
  exact (h.indepFun_innovation_obsPrefix n).symm.comp hΨ measurable_id

/-- The law of `(y_0, …, y_{n-1})` has density the product of the one-step predictive
densities. -/
theorem map_obsPrefix_eq_withDensity (n : ℕ) :
    P.map (M.obsPrefix x₀ w v n) = volume.withDensity (M.innovDensity n) := by
  induction n with
  | zero =>
    have hc : M.obsPrefix x₀ w v 0 = fun _ ↦ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ κ) :=
      funext fun _ ↦ Subsingleton.elim _ _
    have hd : M.innovDensity 0 = 1 := by
      funext ys
      simp [innovDensity]
    rw [hc, Measure.map_const, measure_univ, one_smul, hd, withDensity_one, volume_pi,
      Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    let g : (Fin n → EuclideanSpace ℝ κ) → EuclideanSpace ℝ κ :=
      fun ys ↦ Matrix.toEuclideanLin (M.observation n) (M.predMean (extendObservations ys) n)
    have hg : Measurable g :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
        Matrix.toEuclideanLin (M.observation n) z).comp
        (M.measurable_predMean_extendObservations n n)
    have hPD := M.innovCov_posDef h.stateCov_posSemidef h.obsCov_posSemidef
      h.initCov_posSemidef h.innovCov_det_ne_zero n
    have hm : AEMeasurable (M.obsPrefix x₀ w v n) P := (h.aemeasurable_indepFun_predErr n).1.snd
    have hjoint := map_prodMk_add_eq_compProd hg hm hPD.posSemidef (h.hasLaw_innovation n)
      (h.indepFun_innovation_obsPrefix n).symm
    let f : (Fin n → EuclideanSpace ℝ κ) → EuclideanSpace ℝ κ → ℝ≥0∞ :=
      fun ys y ↦ TauCeti.Probability.multivariateGaussianPDF (g ys) (M.innovCov n) y
    have hq : Measurable fun q : (Fin n → EuclideanSpace ℝ κ) ×
        EuclideanSpace ℝ κ ↦ (g q.1, q.2) :=
      (hg.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (Function.uncurry f) := by
      have := (measurable_multivariateGaussianPDF_uncurry (M.innovCov n)).comp hq
      exact this
    have : IsSFiniteKernel ((Kernel.const (Fin n → EuclideanSpace ℝ κ)
        (volume : Measure (EuclideanSpace ℝ κ))).withDensity f) :=
      Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦
        TauCeti.Probability.multivariateGaussianPDF_ne_top _ _ _
    have hκ : (gaussianShiftKernel (M.innovCov n)).comap g hg =
        (Kernel.const (Fin n → EuclideanSpace ℝ κ)
          (volume : Measure (EuclideanSpace ℝ κ))).withDensity f := by
      ext1 ys
      rw [Kernel.comap_apply, gaussianShiftKernel_apply, Kernel.withDensity_apply _ hf,
        Kernel.const_apply, TauCeti.Probability.multivariateGaussian_eq_withDensity hPD]
    rw [hκ, ih, Measure.withDensity_compProd_withDensity (M.measurable_innovDensity n) hf,
      Measure.compProd_const] at hjoint
    let e : (Fin n → EuclideanSpace ℝ κ) × EuclideanSpace ℝ κ ≃ᵐ
        (Fin (n + 1) → EuclideanSpace ℝ κ) :=
      MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ) (Fin.last n)).symm
    have he : ∀ q, e q = Fin.snoc q.1 q.2 := by
      intro q
      change (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ)
        (Fin.last n)).symm (q.2, q.1) = _
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
        Fin.insertNth_last']
    have hY : M.obsPrefix x₀ w v (n + 1) =
        e ∘ fun ω ↦ (M.obsPrefix x₀ w v n ω, g (M.obsPrefix x₀ w v n ω) +
          M.innovation x₀ w v n ω) := by
      funext ω
      rw [M.obsPrefix_succ_eq x₀ w v n ω, Function.comp_apply]
      change _ = (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ)
        (Fin.last n)).symm (g (M.obsPrefix x₀ w v n ω) + M.innovation x₀ w v n ω,
          M.obsPrefix x₀ w v n ω)
      rw [add_comm (M.innovation x₀ w v n ω)]
    have hvol : (volume.prod volume : Measure ((Fin n → EuclideanSpace ℝ κ) ×
        EuclideanSpace ℝ κ)).map e = volume := by
      have h₁ := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ (volume : Measure (EuclideanSpace ℝ κ))) (Fin.last n)).symm
      have h₂ := Measure.measurePreserving_swap (μ := (volume : Measure
        (Fin n → EuclideanSpace ℝ κ))) (ν := (volume : Measure (EuclideanSpace ℝ κ)))
      exact (h₁.comp h₂).map_eq
    have hD : (fun q : (Fin n → EuclideanSpace ℝ κ) × EuclideanSpace ℝ κ ↦
        M.innovDensity n q.1 * f q.1 q.2) = M.innovDensity (n + 1) ∘ e := by
      funext q
      rw [Function.comp_apply, he, M.innovDensity_snoc]
    have hpm : AEMeasurable (fun ω ↦ (M.obsPrefix x₀ w v n ω, g (M.obsPrefix x₀ w v n ω) +
        M.innovation x₀ w v n ω)) P :=
      hm.prodMk ((hg.comp_aemeasurable hm).add (h.hasLaw_innovation n).aemeasurable)
    rw [hY, ← AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hpm,
      hjoint, hD, MeasurableEquiv.map_withDensity, hvol]
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]

end GaussianInputs

end Filter

end KalmanModel

/-- GAPS 106.7: the Kalman filter for a finite-dimensional time-varying linear Gaussian
state-space model with positive-semidefinite noise and initial covariances, independent
Gaussian white noises independent of the Gaussian initial state, and nonsingular innovation
covariances. Conditionally on `y_0, …, y_t`, the state `x_t` is Gaussian with the filtered
mean and covariance and `x_{t+1}` with the predicted ones; the innovations
`y_t - H_t x_{t|t-1}` are independent with laws `N(0, Σ_t)`; and the density of
`(y_0, …, y_{n-1})` is the product of the one-step predictive densities. -/
theorem KalmanModel.kalman_filter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : KalmanModel ι κ) (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (x₀ : Ω → EuclideanSpace ℝ ι) (w : ℕ → Ω → EuclideanSpace ℝ ι)
    (v : ℕ → Ω → EuclideanSpace ℝ κ)
    (hx₀ : HasLaw x₀ (multivariateGaussian M.initMean M.initCov) P)
    (hw : ∀ t, HasLaw (w t) (multivariateGaussian 0 (M.stateCov t)) P)
    (hv : ∀ t, HasLaw (v t) (multivariateGaussian 0 (M.obsCov t)) P)
    (hwind : iIndepFun w P) (hvind : iIndepFun v P)
    (hwv : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P)
    (hx₀wv : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) :
    let x := M.state x₀ w
    let y := M.observationProcess x v
    let obs : (t : ℕ) → Ω → Fin (t + 1) → EuclideanSpace ℝ κ := fun _ ω i ↦ y i ω
    let e : ℕ → Ω → EuclideanSpace ℝ κ := fun t ω ↦
      y t ω - Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ y i ω) t)
    (∀ t, ∀ᵐ ys ∂(P.map (obs t)), condDistrib (x t) (obs t) P ys =
      multivariateGaussian (M.filtMean (extendObservations ys) t) (M.filtCov t)) ∧
    (∀ t, ∀ᵐ ys ∂(P.map (obs t)), condDistrib (x (t + 1)) (obs t) P ys =
      multivariateGaussian (M.predMean (extendObservations ys) (t + 1)) (M.predCov (t + 1))) ∧
    iIndepFun e P ∧
    (∀ t, HasLaw (e t) (multivariateGaussian 0 (M.innovCov t)) P) ∧
    ∀ n : ℕ, P.map (fun ω (i : Fin n) ↦ y i ω) =
      volume.withDensity fun ys : Fin n → EuclideanSpace ℝ κ ↦
        ∏ i : Fin n, TauCeti.Probability.multivariateGaussianPDF
          (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
          (M.innovCov i) (ys i) := by
  intro x y obs e
  have hG : M.GaussianInputs P x₀ w v :=
    ⟨hQ, hR, hP₀, hx₀, hw, hv, hwind, hvind, hwv, hx₀wv, hinnov⟩
  exact ⟨hG.condDistrib_state, hG.condDistrib_state_succ, hG.iIndepFun_innovation,
    hG.hasLaw_innovation, hG.map_obsPrefix_eq_withDensity⟩

end CKSD
