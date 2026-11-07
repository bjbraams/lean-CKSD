module

public import CKSD.Nonparametric.EmpiricalCovariance
public import Mathlib.Probability.ProductMeasure

/-!
# The Tracy–Widom law and the spiked covariance transition

The Tracy–Widom law `F₁` of the Gaussian orthogonal ensemble is given by its distribution
function
`F₁(s) = exp (-(1/2) ∫_s^∞ (q(x) + (x - s) q(x) ^ 2) dx)`,
where `q` is the Hastings–McLeod solution of the Painlevé II equation `q'' = s q + 2 q ^ 3`,
characterized by `q(s) ~ Ai(s)` as `s → ∞`; the Airy asymptotics
`Ai(s) ~ s ^ (-1/4) exp (-(2/3) s ^ (3/2)) / (2 √π)` express this condition without the Airy
function. Since `F₁` is continuous, convergence in law to `F₁` is stated as pointwise
convergence of distribution functions. The largest eigenvalue of the symmetric sample
covariance matrix is its largest Rayleigh value.

The spiked model is stated for the diagonal covariance `diag(α, 1, …, 1)`, with all sample
sizes realized on one probability space through a doubly infinite array of independent
standard normal variables, the observation matrix of size `n × p` being its upper-left block
with the first column scaled by `√α`.
Source: GAPS 103.38.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace CKSD

/-- The leading term `s ^ (-1/4) exp (-(2/3) s ^ (3/2)) / (2 √π)` of the Airy function as
`s → ∞`. -/
def airyLeadingAsymptotic (s : ℝ) : ℝ :=
  s ^ (-1 / 4 : ℝ) * Real.exp (-(2 / 3) * s ^ (3 / 2 : ℝ)) / (2 * Real.sqrt Real.pi)

/-- The Hastings–McLeod solution of Painlevé II: a twice continuously differentiable solution
of `q'' = s q + 2 q ^ 3` with `q(s) ~ Ai(s)` as `s → ∞`. -/
def IsHastingsMcLeodSolution (q : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 q ∧ (∀ s, iteratedDeriv 2 q s = s * q s + 2 * q s ^ 3) ∧
    Tendsto (fun s ↦ q s / airyLeadingAsymptotic s) atTop (𝓝 1)

/-- The Tracy–Widom distribution function `F₁` of the Gaussian orthogonal ensemble, built
from a Hastings–McLeod solution `q`. -/
def tracyWidomOneCDF (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * ∫ x in Ioi s, (q x + (x - s) * q x ^ 2))

/-- The law of an `n × p` matrix with independent standard normal entries. -/
def standardGaussianMatrixLaw (n p : ℕ) : Measure (Fin n → Fin p → ℝ) :=
  Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin p ↦ gaussianReal 0 1

/-- The largest eigenvalue of the sample covariance `n⁻¹ XᵀX` of an `n × p` data matrix. -/
def largestSampleCovarianceEigenvalue {n p : ℕ} (X : Fin n → Fin p → ℝ) : ℝ :=
  leadingRayleighValue ((n : ℝ)⁻¹ • ((Matrix.of X)ᵀ * Matrix.of X))

/-- Johnstone's centering `(√(n-1) + √p) ^ 2 / n`. -/
def johnstoneCenter (n p : ℕ) : ℝ :=
  (Real.sqrt (n - 1) + Real.sqrt p) ^ 2 / n

/-- Johnstone's scaling `(√(n-1) + √p) ((n-1) ^ (-1/2) + p ^ (-1/2)) ^ (1/3) / n`. -/
def johnstoneScale (n p : ℕ) : ℝ :=
  (Real.sqrt (n - 1) + Real.sqrt p) *
    ((n - 1 : ℝ) ^ (-1 / 2 : ℝ) + (p : ℝ) ^ (-1 / 2 : ℝ)) ^ (1 / 3 : ℝ) / n

/-- GAPS 103.38: Johnstone's Tracy–Widom limit for the largest eigenvalue of a white Wishart
matrix as `n, p → ∞` with `p / n → y ∈ (0, ∞)`, in the form of convergence of distribution
functions to the continuous limit `F₁`. -/
theorem tendsto_largestSampleCovarianceEigenvalue_tracyWidom
    (q : ℝ → ℝ) (hq : IsHastingsMcLeodSolution q)
    (n p : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hp : Tendsto p atTop atTop)
    (y : ℝ) (hy : 0 < y) (hpn : Tendsto (fun k ↦ (p k : ℝ) / n k) atTop (𝓝 y)) (s : ℝ) :
    Tendsto (fun k ↦ (standardGaussianMatrixLaw (n k) (p k)).real
      {X | (largestSampleCovarianceEigenvalue X - johnstoneCenter (n k) (p k)) /
        johnstoneScale (n k) (p k) ≤ s}) atTop (𝓝 (tracyWidomOneCDF q s)) := by
  sorry

/-- The law of a doubly infinite array of independent standard normal variables. -/
def standardGaussianArrayLaw : Measure (ℕ × ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ × ℕ ↦ gaussianReal 0 1

/-- The `n × p` spiked data matrix with covariance `diag(α, 1, …, 1)` read off a standard
normal array. -/
def spikedDataMatrix (α : ℝ) (n p : ℕ) (ω : ℕ × ℕ → ℝ) : Fin n → Fin p → ℝ :=
  fun i j ↦ (if j.val = 0 then Real.sqrt α else 1) * ω (i.val, j.val)

/-- GAPS 103.38, subcritical spike: for `1 < α ≤ 1 + √y` the largest sample covariance
eigenvalue converges almost surely to the bulk edge `(1 + √y) ^ 2`. Scope: diagonal spiked
covariance on the array coupling described in the module header. -/
theorem ae_tendsto_largestEigenvalue_spiked_subcritical
    (n p : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hp : Tendsto p atTop atTop)
    (y : ℝ) (hy : 0 < y) (hpn : Tendsto (fun k ↦ (p k : ℝ) / n k) atTop (𝓝 y))
    (α : ℝ) (hα : 1 < α) (hαy : α ≤ 1 + Real.sqrt y) :
    ∀ᵐ ω ∂standardGaussianArrayLaw, Tendsto
      (fun k ↦ largestSampleCovarianceEigenvalue (spikedDataMatrix α (n k) (p k) ω)) atTop
      (𝓝 ((1 + Real.sqrt y) ^ 2)) := by
  sorry

/-- GAPS 103.38, supercritical spike: for `α > 1 + √y` the largest sample covariance
eigenvalue converges almost surely to `α + y α / (α - 1)`. Scope: diagonal spiked covariance
on the array coupling described in the module header. -/
theorem ae_tendsto_largestEigenvalue_spiked_supercritical
    (n p : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hp : Tendsto p atTop atTop)
    (y : ℝ) (hy : 0 < y) (hpn : Tendsto (fun k ↦ (p k : ℝ) / n k) atTop (𝓝 y))
    (α : ℝ) (hαy : 1 + Real.sqrt y < α) :
    ∀ᵐ ω ∂standardGaussianArrayLaw, Tendsto
      (fun k ↦ largestSampleCovarianceEigenvalue (spikedDataMatrix α (n k) (p k) ω)) atTop
      (𝓝 (α + y * α / (α - 1))) := by
  sorry

end CKSD
