module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Convergence control by kernel Stein discrepancies

For a target law `P` on `ℝ^d` with score `b = ∇ log p` and a kernel `k`, the Langevin Stein
kernel is
`k_P(x, y) = ⟨b x, b y⟩ k(x, y) + ⟨b x, ∇_y k(x, y)⟩ + ⟨b y, ∇_x k(x, y)⟩ + ⟨∇_x, ∇_y⟩ k(x, y)`,
and the squared kernel Stein discrepancy of `μ` is `KSD(μ)² = ∫∫ k_P(x, x') dμ(x) dμ(x')`, the
closed form of GAPS 108.71 under its integrability hypotheses.

## Main definitions

* `CKSD.mixedKernelDivergence`, `CKSD.langevinSteinKernel`, `CKSD.kernelSteinDiscrepancySq`.
* `CKSD.IsDistantlyDissipative`, `CKSD.inverseMultiquadricKernel`.

## Main results

* `CKSD.tendstoWeakly_of_kernelSteinDiscrepancySq_inverseMultiquadric_tendsto_zero`: the inverse
  multiquadric KSD controls weak convergence (GAPS 108.72(b)).
* `CKSD.exists_not_tendstoWeakly_of_kernelSteinDiscrepancySq_tendsto_zero`: fast-decaying kernels
  fail to detect non-convergence for `d ≥ 3` (GAPS 108.72(d)).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

namespace CKSD

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The mixed divergence `⟨∇_x, ∇_y⟩ k(x, y) = ∑_j ∂_{x_j} ∂_{y_j} k(x, y)`. -/
def mixedKernelDivergence (k : E → E → ℝ) (x y : E) : ℝ :=
  ∑ j : Fin d, fderiv ℝ (fun x' ↦ fderiv ℝ (k x') y (EuclideanSpace.single j 1)) x
    (EuclideanSpace.single j 1)

/-- The Langevin Stein kernel of a score `b` and a kernel `k`. -/
def langevinSteinKernel (b : E → E) (k : E → E → ℝ) (x y : E) : ℝ :=
  ⟪b x, b y⟫_ℝ * k x y + ⟪b x, gradient (k x) y⟫_ℝ + ⟪b y, gradient (fun x' ↦ k x' y) x⟫_ℝ +
    mixedKernelDivergence k x y

/-- Squared kernel Stein discrepancy of `μ`, in closed form. -/
def kernelSteinDiscrepancySq (b : E → E) (k : E → E → ℝ) (μ : Measure E) : ℝ :=
  ∫ z, langevinSteinKernel b k z.1 z.2 ∂μ.prod μ

/-- Distant dissipativity of a score: `⟨b x - b y, x - y⟩ ≤ -κ ‖x - y‖²` once `‖x - y‖ ≥ R`. -/
def IsDistantlyDissipative (b : E → E) : Prop :=
  ∃ κ > 0, ∃ R : ℝ, ∀ x y : E, R ≤ ‖x - y‖ → ⟪b x - b y, x - y⟫_ℝ ≤ -κ * ‖x - y‖ ^ 2

/-- The inverse multiquadric kernel `(c² + ‖x - y‖²)^β`. -/
def inverseMultiquadricKernel (c β : ℝ) (x y : E) : ℝ := (c ^ 2 + ‖x - y‖ ^ 2) ^ β

/-- GAPS 108.72(b): let `P` have a positive continuously differentiable density `p` with score
`b = ∇ log p` that is Lipschitz and distantly dissipative. For the inverse multiquadric kernel
with `c > 0` and `β ∈ (-1, 0)`, every sequence of laws with square-integrable score whose kernel
Stein discrepancy tends to zero converges weakly to `P`. -/
theorem tendstoWeakly_of_kernelSteinDiscrepancySq_inverseMultiquadric_tendsto_zero
    (P : Measure E) [IsProbabilityMeasure P] (p : E → ℝ) (hp : HasDensity P volume p)
    (hpos : ∀ x, 0 < p x) (hp1 : ContDiff ℝ 1 p) (b : E → E)
    (hb : ∀ x, b x = gradient (fun z ↦ Real.log (p z)) x) (L : ℝ≥0) (hlip : LipschitzWith L b)
    (hdiss : IsDistantlyDissipative b) (c β : ℝ) (hc : 0 < c) (hβ : β ∈ Ioo (-1 : ℝ) 0)
    (μ : ℕ → Measure E) (hμ : ∀ m, IsProbabilityMeasure (μ m))
    (hμb : ∀ m, Integrable (fun x ↦ ‖b x‖ ^ 2) (μ m))
    (hksd : Tendsto (fun m ↦
      kernelSteinDiscrepancySq b (inverseMultiquadricKernel c β) (μ m)) atTop (𝓝 0)) :
    TendstoWeakly μ P := by
  sorry

/-- GAPS 108.72(d): for `d ≥ 3` and the standard Gaussian target (score `b x = -x`), let `k` be a
`C²` kernel which, together with `∇_x k`, `∇_y k` and `⟨∇_x, ∇_y⟩ k`, is bounded, and whose decay
function `γ(r)` (the supremum of `|k|`, `‖∇_x k‖` and `|⟨∇_x, ∇_y⟩ k|` over `‖x - y‖ ≥ r`) is
`o(r^{-α})` with `α = (1/2 - 1/d)⁻¹`. Then some sequence of laws with finite second moments has
kernel Stein discrepancy tending to zero without converging weakly to the standard Gaussian.
This covers the Gaussian, Matérn and Wendland kernels. The `C²` hypothesis strengthens the
source's continuity requirement on the listed derivatives. Clauses (a) and (c) are not
formalized. -/
theorem exists_not_tendstoWeakly_of_kernelSteinDiscrepancySq_tendsto_zero (hd : 3 ≤ d)
    (k : E → E → ℝ) (hk : ContDiff ℝ 2 (Function.uncurry k))
    (hbdd : ∃ C, ∀ x y, |k x y| ≤ C ∧ ‖gradient (fun x' ↦ k x' y) x‖ ≤ C ∧
      ‖gradient (k x) y‖ ≤ C ∧ |mixedKernelDivergence k x y| ≤ C)
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x y, R ≤ ‖x - y‖ →
      max |k x y| (max ‖gradient (fun x' ↦ k x' y) x‖ |mixedKernelDivergence k x y|) ≤
        ε * ‖x - y‖ ^ (-(1 / 2 - 1 / (d : ℝ))⁻¹)) :
    ∃ μ : ℕ → Measure E, (∀ m, IsProbabilityMeasure (μ m)) ∧
      (∀ m, Integrable (fun x ↦ ‖x‖ ^ 2) (μ m)) ∧
      Tendsto (fun m ↦ kernelSteinDiscrepancySq (fun x ↦ -x) k (μ m)) atTop (𝓝 0) ∧
      ¬ TendstoWeakly μ (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  sorry

end CKSD
