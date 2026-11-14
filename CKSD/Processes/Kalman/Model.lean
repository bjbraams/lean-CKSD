module

public import CKSD.Processes.Basic


/-!
# Linear Gaussian state-space recursions

The model is `x_{t+1} = F_t x_t + w_t`, `y_t = H_t x_t + v_t`, with states in
`EuclideanSpace ℝ ι` and observations in `EuclideanSpace ℝ κ` for finite index types `ι`, `κ`.
Time starts at zero. `KalmanModel` records transition, observation and covariance data; its
mean and covariance recursions use `P_{0|-1}` as the initial covariance.

## Main definitions

* `CKSD.KalmanModel`: the coefficients `F_t`, `H_t`, `Q_t`, `R_t` and the initial mean and
  covariance.
* `CKSD.KalmanModel.predCov`, `CKSD.KalmanModel.filtCov`, `CKSD.KalmanModel.innovCov`,
  `CKSD.KalmanModel.gain`: the covariance recursion `P_{t|t-1}`, `P_{t|t}`, `Σ_t`, `K_t`.
* `CKSD.KalmanModel.predMean`, `CKSD.KalmanModel.filtMean`: the mean recursion as functions of
  the observation sequence.
* `CKSD.KalmanModel.state`, `CKSD.KalmanModel.observationProcess`: the state and observation
  processes driven by an initial state and noise sequences.
* `CKSD.extendObservations`: zero extension of a finite observation record.

Source: GAPS 106.7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Coefficients of a time-varying linear Gaussian state-space model whose state coordinates are
indexed by `ι` and whose observation coordinates are indexed by `κ` (finite types in all
results). -/
structure KalmanModel (ι κ : Type*) where
  /-- State transition matrices `F_t`. -/
  transition : ℕ → Matrix ι ι ℝ
  /-- Observation matrices `H_t`. -/
  observation : ℕ → Matrix κ ι ℝ
  /-- State-noise covariances `Q_t`. -/
  stateCov : ℕ → Matrix ι ι ℝ
  /-- Observation-noise covariances `R_t`. -/
  obsCov : ℕ → Matrix κ κ ℝ
  /-- Mean of the initial state. -/
  initMean : EuclideanSpace ℝ ι
  /-- Covariance of the initial state. -/
  initCov : Matrix ι ι ℝ

namespace KalmanModel

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (M : KalmanModel ι κ)

/-- Innovation covariance `H_t C H_tᵀ + R_t` for a predicted covariance `C`. -/
def innovCovOf (t : ℕ) (C : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  M.observation t * C * (M.observation t).transpose + M.obsCov t

/-- Kalman gain `C H_tᵀ (H_t C H_tᵀ + R_t)⁻¹` for a predicted covariance `C`. -/
def gainOf (t : ℕ) (C : Matrix ι ι ℝ) : Matrix ι κ ℝ :=
  C * (M.observation t).transpose * (M.innovCovOf t C)⁻¹

/-- Filtered covariance `C - K_t H_t C` for a predicted covariance `C`. -/
def filtCovOf (t : ℕ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  C - M.gainOf t C * M.observation t * C

/-- Predicted covariances `P_{t|t-1}`, with `P_{0|-1}` the initial covariance. -/
def predCov : ℕ → Matrix ι ι ℝ
  | 0 => M.initCov
  | t + 1 => M.transition t * M.filtCovOf t (predCov t) * (M.transition t).transpose +
      M.stateCov t

/-- Innovation covariances `Σ_t = H_t P_{t|t-1} H_tᵀ + R_t`. -/
def innovCov (t : ℕ) : Matrix κ κ ℝ := M.innovCovOf t (M.predCov t)

/-- Kalman gains `K_t = P_{t|t-1} H_tᵀ Σ_t⁻¹`. -/
def gain (t : ℕ) : Matrix ι κ ℝ := M.gainOf t (M.predCov t)

/-- Filtered covariances `P_{t|t} = P_{t|t-1} - K_t H_t P_{t|t-1}`. -/
def filtCov (t : ℕ) : Matrix ι ι ℝ := M.filtCovOf t (M.predCov t)

/-- Predicted means `x_{t|t-1}` as functions of the observations, with `x_{0|-1}` the initial
mean and `x_{t+1|t} = F_t x_{t|t}`. -/
def predMean (y : ℕ → EuclideanSpace ℝ κ) : ℕ → EuclideanSpace ℝ ι
  | 0 => M.initMean
  | t + 1 => Matrix.toEuclideanLin (M.transition t)
      (predMean y t + Matrix.toEuclideanLin (M.gain t)
        (y t - Matrix.toEuclideanLin (M.observation t) (predMean y t)))

/-- Filtered means `x_{t|t} = x_{t|t-1} + K_t (y_t - H_t x_{t|t-1})`. -/
def filtMean (y : ℕ → EuclideanSpace ℝ κ) (t : ℕ) : EuclideanSpace ℝ ι :=
  M.predMean y t + Matrix.toEuclideanLin (M.gain t)
    (y t - Matrix.toEuclideanLin (M.observation t) (M.predMean y t))

/-- The state process `x_0 = x₀`, `x_{t+1} = F_t x_t + w_t`. -/
def state {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ ι)
    (w : ℕ → Ω → EuclideanSpace ℝ ι) : ℕ → Ω → EuclideanSpace ℝ ι
  | 0 => x₀
  | t + 1 => fun ω ↦ Matrix.toEuclideanLin (M.transition t) (state x₀ w t ω) + w t ω

/-- The observation process `y_t = H_t x_t + v_t`. -/
def observationProcess {Ω : Type*} (x : ℕ → Ω → EuclideanSpace ℝ ι)
    (v : ℕ → Ω → EuclideanSpace ℝ κ) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ κ :=
  Matrix.toEuclideanLin (M.observation t) (x t ω) + v t ω

end KalmanModel

/-- Extension of a finite observation record `y_0, …, y_{n-1}` by zeros. -/
def extendObservations {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) (i : ℕ) : E :=
  if h : i < n then ys ⟨i, h⟩ else 0

end CKSD
