module

public import CKSD.Processes.Kalman.Model
public import CKSD.Processes.GaussianConditioning

/-!
# Kalman covariance and error identities

Deterministic matrix identities, the Joseph covariance formula, positive-semidefinite
covariance propagation, and measurable dependence of prediction/filtering errors on the past.
The state is indexed from zero and observation records are extended by zero. Source: GAPS 106.7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

section Deterministic

/-- A zero-extended observation record is measurable in each coordinate. -/
theorem measurable_extendObservations_apply {E : Type*} [Zero E] [MeasurableSpace E] {n : ℕ}
    (i : ℕ) : Measurable fun ys : Fin n → E ↦ extendObservations ys i := by
  unfold extendObservations
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The zero extension of a finite record returns the recorded values. -/
@[simp]
theorem extendObservations_of_lt {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) {i : ℕ}
    (h : i < n) : extendObservations ys i = ys ⟨i, h⟩ := by
  simp [extendObservations, h]


namespace KalmanModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (M : KalmanModel ι κ)

/-- The predicted mean at time `t` depends only on the observations before time `t`. -/
theorem predMean_congr {y y' : ℕ → EuclideanSpace ℝ κ} {t : ℕ}
    (h : ∀ i < t, y i = y' i) : M.predMean y t = M.predMean y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)
    simp only [predMean, ih', h t (Nat.lt_succ_self t)]

/-- The filtered mean at time `t` depends only on the observations up to time `t`. -/
theorem filtMean_congr {y y' : ℕ → EuclideanSpace ℝ κ} {t : ℕ}
    (h : ∀ i ≤ t, y i = y' i) : M.filtMean y t = M.filtMean y' t := by
  have hp := M.predMean_congr (t := t) fun i hi ↦ h i hi.le
  simp only [filtMean, hp, h t le_rfl]

/-- The time update of the mean: `x_{t+1|t} = F_t x_{t|t}`. -/
theorem predMean_succ (y : ℕ → EuclideanSpace ℝ κ) (t : ℕ) :
    M.predMean y (t + 1) = Matrix.toEuclideanLin (M.transition t) (M.filtMean y t) := rfl

/-- The predicted mean is a measurable function of a measurably parametrized observation
sequence. -/
theorem measurable_predMean {β : Type*} [MeasurableSpace β]
    {y : ℕ → β → EuclideanSpace ℝ κ} (hy : ∀ i, Measurable (y i)) (t : ℕ) :
    Measurable fun b ↦ M.predMean (fun i ↦ y i b) t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [predMean]
    have h1 : Measurable fun b ↦ Matrix.toEuclideanLin (M.observation t)
        (M.predMean (fun i ↦ y i b) t) := by fun_prop
    have h2 : Measurable fun b ↦ Matrix.toEuclideanLin (M.gain t)
        (y t b - Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ y i b) t)) :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ κ ↦
        Matrix.toEuclideanLin (M.gain t) z).comp ((hy t).sub h1)
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
      Matrix.toEuclideanLin (M.transition t) z).comp (ih.add h2)

/-- The filtered mean is a measurable function of a measurably parametrized observation
sequence. -/
theorem measurable_filtMean {β : Type*} [MeasurableSpace β]
    {y : ℕ → β → EuclideanSpace ℝ κ} (hy : ∀ i, Measurable (y i)) (t : ℕ) :
    Measurable fun b ↦ M.filtMean (fun i ↦ y i b) t := by
  have hF : Measurable fun b ↦ M.filtMean (fun i ↦ y i b) t := by
    unfold filtMean
    have h1 := M.measurable_predMean hy t
    have h2 : Measurable fun b ↦ Matrix.toEuclideanLin (M.observation t)
        (M.predMean (fun i ↦ y i b) t) :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
        Matrix.toEuclideanLin (M.observation t) z).comp h1
    exact h1.add ((by fun_prop : Measurable fun z : EuclideanSpace ℝ κ ↦
        Matrix.toEuclideanLin (M.gain t) z).comp ((hy t).sub h2))
  exact hF

omit [Fintype κ] [DecidableEq κ] in
/-- The state at time `s` is unchanged by a change of sample space that preserves the initial
state and the state noises before time `s`. -/
theorem state_congr {Ω Ω' : Type*} (f : Ω' → Ω) {x₀ : Ω → EuclideanSpace ℝ ι}
    {w : ℕ → Ω → EuclideanSpace ℝ ι} {x₀' : Ω' → EuclideanSpace ℝ ι}
    {w' : ℕ → Ω' → EuclideanSpace ℝ ι} (h₀ : ∀ ω, x₀' ω = x₀ (f ω)) {s : ℕ}
    (hw : ∀ i < s, ∀ ω, w' i ω = w i (f ω)) (ω : Ω') :
    M.state x₀' w' s ω = M.state x₀ w s (f ω) := by
  induction s with
  | zero => exact h₀ ω
  | succ s ih =>
    simp only [state, ih fun i hi ↦ hw i (Nat.lt_succ_of_lt hi), hw s (Nat.lt_succ_self s)]

omit [Fintype κ] [DecidableEq κ] in
/-- The state process is measurable when the initial state and the noises are. -/
theorem measurable_state {Ω : Type*} [MeasurableSpace Ω] {x₀ : Ω → EuclideanSpace ℝ ι}
    {w : ℕ → Ω → EuclideanSpace ℝ ι} (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (s : ℕ) : Measurable (M.state x₀ w s) := by
  induction s with
  | zero => exact h₀
  | succ s ih =>
    exact ((by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
      Matrix.toEuclideanLin (M.transition s) z).comp ih).add (hw s)

omit [DecidableEq κ] in
/-- The observation process is measurable when the state and the observation noise are. -/
theorem measurable_observationProcess {Ω : Type*} [MeasurableSpace Ω]
    {x : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℕ → Ω → EuclideanSpace ℝ κ}
    (hx : ∀ i, Measurable (x i)) (hv : ∀ i, Measurable (v i)) (s : ℕ) :
    Measurable (M.observationProcess x v s) :=
  ((by fun_prop : Measurable fun z : EuclideanSpace ℝ ι ↦
    Matrix.toEuclideanLin (M.observation s) z).comp (hx s)).add (hv s)

end KalmanModel

/-- Appending a value to a finite record does not change its zero extension below the old
length. -/
theorem extendObservations_snoc {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) (y : E) {j : ℕ}
    (hj : j < n) :
    extendObservations (Fin.snoc ys y : Fin (n + 1) → E) j = extendObservations ys j := by
  rw [extendObservations_of_lt _ (Nat.lt_succ_of_lt hj), extendObservations_of_lt _ hj]
  exact Fin.snoc_castSucc (α := fun _ ↦ E) (p := ys) (x := y) ⟨j, hj⟩

namespace KalmanModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (M : KalmanModel ι κ)

/-- The product of the one-step predictive densities `∏_{i<n} φ(y_i; H_i x_{i|i-1}, Σ_i)` of an
observation record `(y_0, …, y_{n-1})`. -/
def innovDensity (n : ℕ) (ys : Fin n → EuclideanSpace ℝ κ) : ℝ≥0∞ :=
  ∏ i : Fin n, TauCeti.Probability.multivariateGaussianPDF
    (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
    (M.innovCov i) (ys i)

/-- The predicted mean computed from a zero-extended record is measurable in the record. -/
theorem measurable_predMean_extendObservations (n t : ℕ) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ κ ↦
      M.predMean (extendObservations ys) t :=
  M.measurable_predMean (y := fun i ys ↦ extendObservations ys i)
    (fun i ↦ measurable_extendObservations_apply i) t

/-- The filtered mean computed from a zero-extended record is measurable in the record. -/
theorem measurable_filtMean_extendObservations (n t : ℕ) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ κ ↦
      M.filtMean (extendObservations ys) t :=
  M.measurable_filtMean (y := fun i ys ↦ extendObservations ys i)
    (fun i ↦ measurable_extendObservations_apply i) t

/-- Each one-step predictive density factor is measurable in the record. -/
theorem measurable_innovDensity_factor (n : ℕ) (i : Fin n) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ κ ↦
      TauCeti.Probability.multivariateGaussianPDF
        (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
        (M.innovCov i) (ys i) := by
  have h₁ := M.measurable_predMean_extendObservations n i
  have h₂ : Measurable fun z : EuclideanSpace ℝ ι ↦
      Matrix.toEuclideanLin (M.observation i) z := by fun_prop
  have hq : Measurable fun ys : Fin n → EuclideanSpace ℝ κ ↦
      (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i), ys i) :=
    (h₂.comp h₁).prodMk (measurable_pi_apply i)
  have := (measurable_multivariateGaussianPDF_uncurry (M.innovCov i)).comp hq
  exact this

/-- The product of predictive densities is measurable. -/
theorem measurable_innovDensity (n : ℕ) : Measurable (M.innovDensity n) := by
  unfold innovDensity
  exact Finset.measurable_prod _ fun i _ ↦ M.measurable_innovDensity_factor n i

/-- The product of predictive densities factors over the last observation. -/
theorem innovDensity_snoc (n : ℕ) (ys : Fin n → EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ κ) :
    M.innovDensity (n + 1) (Fin.snoc ys y) = M.innovDensity n ys *
      TauCeti.Probability.multivariateGaussianPDF
        (Matrix.toEuclideanLin (M.observation n) (M.predMean (extendObservations ys) n))
        (M.innovCov n) y := by
  unfold innovDensity
  rw [Fin.prod_univ_castSucc]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Fin.snoc_castSucc, Fin.val_castSucc, M.predMean_congr fun j hj ↦
      extendObservations_snoc ys y (hj.trans i.2)]
  · rw [Fin.snoc_last, Fin.val_last, M.predMean_congr fun j hj ↦ extendObservations_snoc ys y hj]

end KalmanModel


end Deterministic


namespace KalmanModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (M : KalmanModel ι κ)

section Covariance

omit [DecidableEq ι] in
/-- With a nonsingular innovation covariance, `K_t Σ_t = P_{t|t-1} H_tᵀ`. -/
theorem gain_mul_innovCov {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    M.gain t * M.innovCov t = M.predCov t * (M.observation t).transpose := by
  simp only [gain, gainOf]
  rw [Matrix.mul_assoc, ← innovCov, Matrix.nonsing_inv_mul _ hdet.isUnit, Matrix.mul_one]

/-- The cross-covariance of the filtered error and the innovation vanishes:
`(I - K_t H_t) P_{t|t-1} H_tᵀ - K_t R_t = 0`. -/
theorem filtErr_innovation_cross {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    (1 - M.gain t * M.observation t) * M.predCov t * (M.observation t).transpose +
      (-M.gain t) * M.obsCov t * (1 : Matrix κ κ ℝ).transpose = 0 := by
  have h := M.gain_mul_innovCov hdet
  simp only [innovCov, innovCovOf] at h
  calc _ = M.predCov t * (M.observation t).transpose - M.gain t *
        (M.observation t * M.predCov t * (M.observation t).transpose + M.obsCov t) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.transpose_one,
          Matrix.mul_one, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = 0 := by rw [h, sub_self]

/-- Joseph form of the filtered covariance: with a nonsingular innovation covariance,
`(I - K_t H_t) P (I - K_t H_t)ᵀ + K_t R_t K_tᵀ = P - K_t H_t P`. -/
theorem filtCov_eq_joseph {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    (1 - M.gain t * M.observation t) * M.predCov t *
        (1 - M.gain t * M.observation t).transpose +
      (-M.gain t) * M.obsCov t * (-M.gain t).transpose = M.filtCov t := by
  have h := M.gain_mul_innovCov hdet
  simp only [innovCov, innovCovOf] at h
  set K := M.gain t
  set H := M.observation t
  set C := M.predCov t
  calc _ = C - K * H * C - C * H.transpose * K.transpose +
        K * (H * C * H.transpose + M.obsCov t) * K.transpose := by
        simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          Matrix.transpose_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]
        abel
    _ = C - K * H * C := by rw [h]; abel
    _ = M.filtCov t := by simp only [filtCov, filtCovOf, K, H, C, gain]

/-- Under positive-semidefinite noise and initial covariances and nonsingular innovation
covariances, every predicted covariance is positive semidefinite. -/
theorem predCov_posSemidef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.predCov t).PosSemidef := by
  induction t with
  | zero => exact hP₀
  | succ t ih =>
    have hf : (M.filtCov t).PosSemidef := by
      rw [← M.filtCov_eq_joseph (hinnov t)]
      exact (posSemidef_mul_mul_transpose ih _).add (posSemidef_mul_mul_transpose (hR t) _)
    exact (posSemidef_mul_mul_transpose hf (M.transition t)).add (hQ t)

/-- Under the hypotheses of `predCov_posSemidef`, every filtered covariance is positive
semidefinite. -/
theorem filtCov_posSemidef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.filtCov t).PosSemidef := by
  rw [← M.filtCov_eq_joseph (hinnov t)]
  exact (posSemidef_mul_mul_transpose (M.predCov_posSemidef hQ hR hP₀ hinnov t) _).add
    (posSemidef_mul_mul_transpose (hR t) _)

/-- Under the hypotheses of `predCov_posSemidef`, every innovation covariance is positive
definite. -/
theorem innovCov_posDef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.innovCov t).PosDef := by
  have h : (M.innovCov t).PosSemidef :=
    (posSemidef_mul_mul_transpose (M.predCov_posSemidef hQ hR hP₀ hinnov t) _).add (hR t)
  exact h.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (hinnov t).isUnit)

end Covariance

section Errors

variable {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ ι) (w : ℕ → Ω → EuclideanSpace ℝ ι)
  (v : ℕ → Ω → EuclideanSpace ℝ κ)

/-- The observation process `y_t = H_t x_t + v_t` driven by `x₀`, `w`, and `v`. -/
def obsProc : ℕ → Ω → EuclideanSpace ℝ κ := M.observationProcess (M.state x₀ w) v

/-- The observation record `(y_0, …, y_{n-1})`. -/
def obsPrefix (n : ℕ) (ω : Ω) : Fin n → EuclideanSpace ℝ κ :=
  fun i ↦ M.obsProc x₀ w v i ω

/-- The prediction error `x_t - x_{t|t-1}`. -/
def predErr (t : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  M.state x₀ w t ω - M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t

/-- The filtering error `x_t - x_{t|t}`. -/
def filtErr (t : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  M.state x₀ w t ω - M.filtMean (fun i ↦ M.obsProc x₀ w v i ω) t

/-- The innovation `y_t - H_t x_{t|t-1}`. -/
def innovation (t : ℕ) (ω : Ω) : EuclideanSpace ℝ κ :=
  M.obsProc x₀ w v t ω -
    Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t)

/-- The innovation is `H_t (x_t - x_{t|t-1}) + v_t`. -/
theorem innovation_eq (t : ℕ) (ω : Ω) :
    M.innovation x₀ w v t ω =
      Matrix.toEuclideanLin (M.observation t) (M.predErr x₀ w v t ω) + v t ω := by
  simp only [innovation, predErr, obsProc, observationProcess, map_sub]
  abel

/-- The filtering error is `(I - K_t H_t)(x_t - x_{t|t-1}) - K_t v_t`. -/
theorem filtErr_eq (t : ℕ) (ω : Ω) :
    M.filtErr x₀ w v t ω =
      Matrix.toEuclideanLin (1 - M.gain t * M.observation t) (M.predErr x₀ w v t ω) +
        Matrix.toEuclideanLin (-M.gain t) (v t ω) := by
  have h : M.filtErr x₀ w v t ω = M.predErr x₀ w v t ω -
      Matrix.toEuclideanLin (M.gain t) (M.innovation x₀ w v t ω) := by
    simp only [filtErr, filtMean, predErr, innovation]
    abel
  rw [h, innovation_eq]
  simp only [map_sub, map_add, map_neg, LinearMap.sub_apply, LinearMap.neg_apply,
    Matrix.toLpLin_one, Matrix.toLpLin_mul_same, LinearMap.id_apply, LinearMap.comp_apply]
  abel

/-- The prediction error at time `t + 1` is `F_t (x_t - x_{t|t}) + w_t`. -/
theorem predErr_succ (t : ℕ) (ω : Ω) :
    M.predErr x₀ w v (t + 1) ω =
      Matrix.toEuclideanLin (M.transition t) (M.filtErr x₀ w v t ω) + w t ω := by
  simp only [predErr, filtErr, state, predMean_succ, map_sub]
  abel

/-- The observation record up to time `t` is obtained from the record before time `t` and the
innovation at time `t` by appending `e_t + H_t x_{t|t-1}`. -/
theorem obsPrefix_succ_eq (t : ℕ) (ω : Ω) :
    M.obsPrefix x₀ w v (t + 1) ω =
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ κ) (Fin.last t)).symm
        (M.innovation x₀ w v t ω + Matrix.toEuclideanLin (M.observation t)
          (M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t),
          M.obsPrefix x₀ w v t ω) := by
  have hpm : M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t =
      M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t :=
    M.predMean_congr fun i hi ↦ by simp [extendObservations_of_lt _ hi, obsPrefix]
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, Fin.insertNth_last',
    hpm]
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [innovation, obsPrefix]
  · simp [obsPrefix]

end Errors


section Congr

variable {Ω Ω' : Type*} (f : Ω → Ω') {x₀ : Ω → EuclideanSpace ℝ ι}
  {w : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℕ → Ω → EuclideanSpace ℝ κ}
  {x₀' : Ω' → EuclideanSpace ℝ ι} {w' : ℕ → Ω' → EuclideanSpace ℝ ι}
  {v' : ℕ → Ω' → EuclideanSpace ℝ κ}

omit [Fintype κ] [DecidableEq κ] in
/-- Observations up to time `s` are unchanged by a change of sample space that preserves the
initial state, the state noises before time `s`, and the observation noise at time `s`. -/
theorem obsProc_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {s : ℕ}
    (hw : ∀ i < s, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ ω, v s ω = v' s (f ω)) (ω : Ω) :
    M.obsProc x₀ w v s ω = M.obsProc x₀' w' v' s (f ω) := by
  simp only [obsProc, observationProcess, M.state_congr f h₀ hw, hv]

/-- The prediction error and the observation record at time `t` are unchanged by a change of
sample space that preserves the initial state and the noises before time `t`. -/
theorem predErr_obsPrefix_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {t : ℕ}
    (hw : ∀ i < t, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ i < t, ∀ ω, v i ω = v' i (f ω)) (ω : Ω) :
    M.predErr x₀ w v t ω = M.predErr x₀' w' v' t (f ω) ∧
      M.obsPrefix x₀ w v t ω = M.obsPrefix x₀' w' v' t (f ω) := by
  have hy : ∀ i < t, M.obsProc x₀ w v i ω = M.obsProc x₀' w' v' i (f ω) := fun i hi ↦
    M.obsProc_congr f h₀ (fun j hj ↦ hw j (hj.trans hi)) (hv i hi) ω
  refine ⟨?_, funext fun i ↦ hy i i.2⟩
  simp only [predErr, M.state_congr f h₀ hw, M.predMean_congr hy]

/-- The filtering error at time `t` and the observation record up to time `t` are unchanged
by a change of sample space that preserves the initial state, the state noises before time `t`,
and the observation noises up to time `t`. -/
theorem filtErr_obsPrefix_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {t : ℕ}
    (hw : ∀ i < t, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ i ≤ t, ∀ ω, v i ω = v' i (f ω)) (ω : Ω) :
    M.filtErr x₀ w v t ω = M.filtErr x₀' w' v' t (f ω) ∧
      M.obsPrefix x₀ w v (t + 1) ω = M.obsPrefix x₀' w' v' (t + 1) (f ω) := by
  have hy : ∀ i ≤ t, M.obsProc x₀ w v i ω = M.obsProc x₀' w' v' i (f ω) := fun i hi ↦
    M.obsProc_congr f h₀ (fun j hj ↦ hw j (lt_of_lt_of_le hj hi)) (hv i hi) ω
  refine ⟨?_, funext fun i ↦ hy i (Nat.lt_succ_iff.mp i.2)⟩
  simp only [filtErr, M.state_congr f h₀ hw, M.filtMean_congr hy]

end Congr

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {x₀ : Ω → EuclideanSpace ℝ ι}
  {w : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℕ → Ω → EuclideanSpace ℝ κ}

omit [DecidableEq κ] in
/-- The observation process is measurable for measurable inputs. -/
theorem measurable_obsProc (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (s : ℕ) : Measurable (M.obsProc x₀ w v s) :=
  M.measurable_observationProcess (M.measurable_state h₀ hw) hv s

omit [DecidableEq κ] in
/-- The observation record is measurable for measurable inputs. -/
theorem measurable_obsPrefix (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (n : ℕ) : Measurable (M.obsPrefix x₀ w v n) :=
  measurable_pi_iff.mpr fun i ↦ M.measurable_obsProc h₀ hw hv i

/-- The prediction error is measurable for measurable inputs. -/
theorem measurable_predErr (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (t : ℕ) : Measurable (M.predErr x₀ w v t) :=
  (M.measurable_state h₀ hw t).sub
    (M.measurable_predMean (M.measurable_obsProc h₀ hw hv) t)

/-- The filtering error is measurable for measurable inputs. -/
theorem measurable_filtErr (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (t : ℕ) : Measurable (M.filtErr x₀ w v t) :=
  (M.measurable_state h₀ hw t).sub
    (M.measurable_filtMean (M.measurable_obsProc h₀ hw hv) t)

end Measurability

/-- The prediction error and the observation record at time `t` are a measurable function of
the initial state, the state noises, and the observation noises before time `t`. -/
theorem exists_predErr_obsPrefix_eq_comp {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ ι)
    (w : ℕ → Ω → EuclideanSpace ℝ ι) (v : ℕ → Ω → EuclideanSpace ℝ κ) (t : ℕ) :
    ∃ G : EuclideanSpace ℝ ι × (ℕ → EuclideanSpace ℝ ι) ×
        (Fin t → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι ×
          (Fin t → EuclideanSpace ℝ κ),
      Measurable G ∧ ∀ ω, (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω) =
        G (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω) := by
  let x₀' : EuclideanSpace ℝ ι × (ℕ → EuclideanSpace ℝ ι) ×
      (Fin t → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι := fun b ↦ b.1
  let w' : ℕ → EuclideanSpace ℝ ι × (ℕ → EuclideanSpace ℝ ι) ×
      (Fin t → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι := fun i b ↦ b.2.1 i
  let v' : ℕ → EuclideanSpace ℝ ι × (ℕ → EuclideanSpace ℝ ι) ×
      (Fin t → EuclideanSpace ℝ κ) → EuclideanSpace ℝ κ :=
    fun i b ↦ extendObservations b.2.2 i
  have h₀ : Measurable x₀' := measurable_fst
  have hw : ∀ i, Measurable (w' i) := fun i ↦
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hv : ∀ i, Measurable (v' i) := fun i ↦
    (measurable_extendObservations_apply i).comp (measurable_snd.comp measurable_snd)
  refine ⟨fun b ↦ (M.predErr x₀' w' v' t b, M.obsPrefix x₀' w' v' t b),
    (M.measurable_predErr h₀ hw hv t).prodMk (M.measurable_obsPrefix h₀ hw hv t),
    fun ω ↦ ?_⟩
  obtain ⟨h1, h2⟩ := M.predErr_obsPrefix_congr
    (fun ω ↦ (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω)) (x₀ := x₀) (w := w) (v := v) (t := t)
    (x₀' := x₀') (w' := w') (v' := v')
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun i hi ω ↦ by simp [v', extendObservations_of_lt _ hi]) ω
  rw [h1, h2]

/-- The filtering error at time `t` and the observation record up to time `t` are a measurable
function of the initial state, the state noises before time `t`, and the observation noises. -/
theorem exists_filtErr_obsPrefix_eq_comp {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ ι)
    (w : ℕ → Ω → EuclideanSpace ℝ ι) (v : ℕ → Ω → EuclideanSpace ℝ κ) (t : ℕ) :
    ∃ G : EuclideanSpace ℝ ι × (Fin t → EuclideanSpace ℝ ι) ×
        (ℕ → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι ×
          (Fin (t + 1) → EuclideanSpace ℝ κ),
      Measurable G ∧ ∀ ω, (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω) =
        G (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω) := by
  let x₀' : EuclideanSpace ℝ ι × (Fin t → EuclideanSpace ℝ ι) ×
      (ℕ → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι := fun b ↦ b.1
  let w' : ℕ → EuclideanSpace ℝ ι × (Fin t → EuclideanSpace ℝ ι) ×
      (ℕ → EuclideanSpace ℝ κ) → EuclideanSpace ℝ ι :=
    fun i b ↦ extendObservations b.2.1 i
  let v' : ℕ → EuclideanSpace ℝ ι × (Fin t → EuclideanSpace ℝ ι) ×
      (ℕ → EuclideanSpace ℝ κ) → EuclideanSpace ℝ κ := fun i b ↦ b.2.2 i
  have h₀ : Measurable x₀' := measurable_fst
  have hw : ∀ i, Measurable (w' i) := fun i ↦
    (measurable_extendObservations_apply i).comp (measurable_fst.comp measurable_snd)
  have hv : ∀ i, Measurable (v' i) := fun i ↦
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  refine ⟨fun b ↦ (M.filtErr x₀' w' v' t b, M.obsPrefix x₀' w' v' (t + 1) b),
    (M.measurable_filtErr h₀ hw hv t).prodMk (M.measurable_obsPrefix h₀ hw hv (t + 1)),
    fun ω ↦ ?_⟩
  obtain ⟨h1, h2⟩ := M.filtErr_obsPrefix_congr
    (fun ω ↦ (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω)) (x₀ := x₀) (w := w) (v := v) (t := t)
    (x₀' := x₀') (w' := w') (v' := v')
    (fun _ ↦ rfl) (fun i hi ω ↦ by simp [w', extendObservations_of_lt _ hi])
    (fun _ _ _ ↦ rfl) ω
  rw [h1, h2]


end KalmanModel

end CKSD
