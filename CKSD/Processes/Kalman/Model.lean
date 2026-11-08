module

public import CKSD.Processes.Basic

/-!
# Linear Gaussian state-space recursions

Time starts at zero. `KalmanModel` records transition, observation and covariance data;
its mean and covariance recursions use `P_{0|-1}` as the initial covariance.
`extendObservations` embeds a finite record by zero extension. Source: GAPS 106.7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Coefficients of a time-varying linear Gaussian state-space model with state dimension `d`
and observation dimension `p`. -/
structure KalmanModel (d p : ℕ) where
  /-- State transition matrices `F_t`. -/
  transition : ℕ → Matrix (Fin d) (Fin d) ℝ
  /-- Observation matrices `H_t`. -/
  observation : ℕ → Matrix (Fin p) (Fin d) ℝ
  /-- State-noise covariances `Q_t`. -/
  stateCov : ℕ → Matrix (Fin d) (Fin d) ℝ
  /-- Observation-noise covariances `R_t`. -/
  obsCov : ℕ → Matrix (Fin p) (Fin p) ℝ
  /-- Mean of the initial state. -/
  initMean : EuclideanSpace ℝ (Fin d)
  /-- Covariance of the initial state. -/
  initCov : Matrix (Fin d) (Fin d) ℝ

namespace KalmanModel

variable {d p : ℕ} (M : KalmanModel d p)

/-- Innovation covariance `H_t C H_tᵀ + R_t` for a predicted covariance `C`. -/
def innovCovOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  M.observation t * C * (M.observation t).transpose + M.obsCov t

/-- Kalman gain `C H_tᵀ (H_t C H_tᵀ + R_t)⁻¹` for a predicted covariance `C`. -/
def gainOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin p) ℝ :=
  C * (M.observation t).transpose * (M.innovCovOf t C)⁻¹

/-- Filtered covariance `C - K_t H_t C` for a predicted covariance `C`. -/
def filtCovOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  C - M.gainOf t C * M.observation t * C

/-- Predicted covariances `P_{t|t-1}`, with `P_{0|-1}` the initial covariance. -/
def predCov : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => M.initCov
  | t + 1 => M.transition t * M.filtCovOf t (predCov t) * (M.transition t).transpose +
      M.stateCov t

/-- Innovation covariances `Σ_t = H_t P_{t|t-1} H_tᵀ + R_t`. -/
def innovCov (t : ℕ) : Matrix (Fin p) (Fin p) ℝ := M.innovCovOf t (M.predCov t)

/-- Kalman gains `K_t = P_{t|t-1} H_tᵀ Σ_t⁻¹`. -/
def gain (t : ℕ) : Matrix (Fin d) (Fin p) ℝ := M.gainOf t (M.predCov t)

/-- Filtered covariances `P_{t|t} = P_{t|t-1} - K_t H_t P_{t|t-1}`. -/
def filtCov (t : ℕ) : Matrix (Fin d) (Fin d) ℝ := M.filtCovOf t (M.predCov t)

/-- Predicted means `x_{t|t-1}` as functions of the observations, with `x_{0|-1}` the initial
mean and `x_{t+1|t} = F_t x_{t|t}`. -/
def predMean (y : ℕ → EuclideanSpace ℝ (Fin p)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => M.initMean
  | t + 1 => Matrix.toEuclideanLin (M.transition t)
      (predMean y t + Matrix.toEuclideanLin (M.gain t)
        (y t - Matrix.toEuclideanLin (M.observation t) (predMean y t)))

/-- Filtered means `x_{t|t} = x_{t|t-1} + K_t (y_t - H_t x_{t|t-1})`. -/
def filtMean (y : ℕ → EuclideanSpace ℝ (Fin p)) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  M.predMean y t + Matrix.toEuclideanLin (M.gain t)
    (y t - Matrix.toEuclideanLin (M.observation t) (M.predMean y t))

/-- The state process `x_0 = x₀`, `x_{t+1} = F_t x_t + w_t`. -/
def state {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0 => x₀
  | t + 1 => fun ω ↦ Matrix.toEuclideanLin (M.transition t) (state x₀ w t ω) + w t ω

/-- The observation process `y_t = H_t x_t + v_t`. -/
def observationProcess {Ω : Type*} (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  Matrix.toEuclideanLin (M.observation t) (x t ω) + v t ω

end KalmanModel

/-- Extension of a finite observation record `y_0, …, y_{n-1}` by zeros. -/
def extendObservations {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) (i : ℕ) : E :=
  if h : i < n then ys ⟨i, h⟩ else 0

end CKSD
