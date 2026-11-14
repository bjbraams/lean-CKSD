module

public import CKSD.Nonparametric.Basic
public import CKSD.LinearModels.Basic

/-!
# Geometry: basic definitions

Definitions shared by the geometric and kernel parts of Section 108: weighted graphs and their
Cheeger constant and spectral gap, the distance to a measure, maximum mean discrepancy and
characteristic kernels, distance kernels, Gaussian smoothing, Laguerre cells and the semidiscrete
transport dual, and random Fourier features.

## Main definitions

* `CKSD.cheegerConstant`, `CKSD.spectralGap`: conductance and normalized-Laplacian spectral gap
  of a weighted graph on `Fin n`.
* `CKSD.massRadius`, `CKSD.distanceToMeasure`: the distance to a measure at mass `m`.
* `CKSD.squaredMMD`: the kernel double-integral expression for the squared maximum mean
  discrepancy; `CKSD.IsCharacteristicKernel`: separation of probability laws by it.
* `CKSD.unbiasedSquaredMMD`: the unbiased two-sample estimator of the squared MMD.
* `CKSD.distanceKernel`, `CKSD.centeredDistance`: the kernels of energy distance and distance
  covariance.
* `CKSD.gaussianSmoothing`, `CKSD.laguerreCell`, `CKSD.semidiscreteTransportDual`.
* `CKSD.randomFourierFeatureTerm`, `CKSD.randomFourierFeatureKernel`.

## Conventions

Several definitions use real `sInf` or Bochner integrals and so carry Mathlib's junk values: the
infimum of an empty or unbounded-below set of reals is `0`, and the integral of a non-integrable
function is `0`. Each docstring records when the defining set is nonempty and bounded, or when the
integrals exist; the theorems using these definitions carry the corresponding hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The weighted degree `d_i = ∑_j W i j` of a vertex `i` of a weighted graph with weight matrix
`W`. -/
def weightedDegree {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, W i j

/-- The volume `vol S = ∑_{i ∈ S} d_i` of a set of vertices. -/
def graphVolume {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, weightedDegree W i

/-- The weight `∑_{i ∈ S, j ∉ S} W i j` of the edges crossing the cut `(S, Sᶜ)`, each counted
once. -/
def cutWeight {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, W i j

/-- The Cheeger constant (conductance) `h(G) = min_S w(S, Sᶜ) / min (vol S, vol Sᶜ)` over the
nonempty proper vertex sets `S`. The defining set is finite; it is nonempty exactly when `n ≥ 2`,
and for `n ≤ 1` the value is the junk value `0`. -/
def cheegerConstant {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    r = cutWeight W S / min (graphVolume W S) (graphVolume W Sᶜ)}

/-- The spectral gap `λ₁` of the normalized Laplacian `I - D^{-1/2} W D^{-1/2}`, by the
degree-weighted Rayleigh principle: the infimum of `½ ∑_{i,j} W i j (f i - f j)²` over the
functions `f` with `∑ d_i f i = 0` and `∑ d_i f i² = 1`.

For nonnegative weights the defining set is bounded below by `0`, and it is nonempty as soon as two
vertices have positive degree (for instance, for a connected graph with `n ≥ 2`); otherwise the
value is the junk value `0` of `sInf ∅`. -/
def spectralGap {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ f : Fin n → ℝ, (∑ i, weightedDegree W i * f i) = 0 ∧
    (∑ i, weightedDegree W i * f i ^ 2) = 1 ∧
      r = (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2}

/-- The radius `δ_{P,u}(x) = inf {r ≥ 0 : P(B̄(x, r)) ≥ u}` needed to capture mass `u` around `x`.
For a probability measure and `u ∈ (0, 1]` the defining set is nonempty. -/
def massRadius {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (P : Measure X) (u : ℝ)
    (x : X) : ℝ :=
  sInf {r | 0 ≤ r ∧ ENNReal.ofReal u ≤ P (Metric.closedBall x r)}

/-- The distance to the measure `P` at mass `m`, `d_{P,m}(x) = (m⁻¹ ∫₀^m δ_{P,u}(x)² du)^{1/2}`. -/
def distanceToMeasure {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (P : Measure X)
    (m : ℝ) (x : X) : ℝ :=
  Real.sqrt ((∫ u in (0 : ℝ)..m, massRadius P u x ^ 2) / m)

/-- The squared maximum mean discrepancy of a kernel `k`, as the kernel double-integral
expression `∫∫ k dP dP + ∫∫ k dQ dQ - 2 ∫∫ k dP dQ` over product measures. The expression is
meaningful when `k` is integrable for the three product measures, for example for a bounded
measurable kernel; for a positive semidefinite kernel it is the squared distance of the kernel mean
embeddings (`CKSD.squaredMMD_eq_norm_kernelMeanEmbedding_sub_sq`). -/
def squaredMMD {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  (∫ z, k z.1 z.2 ∂P.prod P) + (∫ z, k z.1 z.2 ∂Q.prod Q) -
    2 * ∫ z, k z.1 z.2 ∂P.prod Q

/-- A kernel is characteristic when the squared MMD separates probability laws: for probability
measures `P, Q` for which `k` is integrable against `P ⊗ P`, `Q ⊗ Q` and `P ⊗ Q`, the squared MMD
vanishes exactly when `P = Q`. For bounded measurable kernels the integrability conditions hold
for all pairs of probability measures. Symmetry and positive definiteness of the kernel are
separate properties. -/
def IsCharacteristicKernel {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) : Prop :=
  ∀ P Q : Measure X, IsProbabilityMeasure P → IsProbabilityMeasure Q →
    Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod P) →
    Integrable (fun z : X × X ↦ k z.1 z.2) (Q.prod Q) →
    Integrable (fun z : X × X ↦ k z.1 z.2) (P.prod Q) →
    (squaredMMD k P Q = 0 ↔ P = Q)

/-- The unbiased estimator of the squared MMD from two samples `x, y` of equal size `n`:
`(n (n - 1))⁻¹ ∑_{i ≠ j} (k(x_i, x_j) + k(y_i, y_j)) - 2 n⁻² ∑_{i,j} k(x_i, y_j)`. -/
def unbiasedSquaredMMD {X : Type*} (k : X → X → ℝ) (n : ℕ) (x y : Fin n → X) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j then k (x i) (x j) + k (y i) (y j) else 0) /
    ((n : ℝ) * (n - 1 : ℕ))) - 2 / (n : ℝ) ^ 2 * ∑ i, ∑ j, k (x i) (y j)

/-- The distance-induced kernel `k(x, y) = (‖x‖ + ‖y‖ - ‖x - y‖) / 2` with base point `0`, whose
squared MMD is half the energy distance. -/
def distanceKernel {E : Type*} [SeminormedAddCommGroup E] (x y : E) : ℝ :=
  (‖x‖ + ‖y‖ - ‖x - y‖) / 2

/-- The doubly centered distance
`d(x, y) - ∫ d(x, z) dP(z) - ∫ d(z, y) dP(z) + ∫∫ d(z, z') dP(z) dP(z')` of distance covariance. -/
def centeredDistance {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (P : Measure X)
    (x y : X) : ℝ :=
  dist x y - (∫ z, dist x z ∂P) - (∫ z, dist z y ∂P) + ∫ z, dist z.1 z.2 ∂P.prod P

/-- Gaussian smoothing `P * N(0, σ² I)`, the law of `X + σ Z` for independent `X ∼ P` and standard
Gaussian `Z`, as the pushforward of `P ⊗ N(0, σ² I)` under addition. -/
def gaussianSmoothing {d : ℕ} (sigma : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (multivariateGaussian 0 (sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)))).map
    (fun z ↦ z.1 + z.2)

/-- The Laguerre cell `{x : ‖x - y_j‖² - g_j ≤ ‖x - y_i‖² - g_i for all i}` of the site `y_j` with
weights `g`, for the squared Euclidean cost. -/
def laguerreCell {d k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (j : Fin k) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ‖x - y j‖ ^ 2 - g j ≤ ‖x - y i‖ ^ 2 - g i}

/-- The semidiscrete transport dual functional
`g ↦ ∫ min_j (‖x - y_j‖² - g_j) dP(x) + ∑_j b_j g_j` for the transport of `P` to the discrete law
with masses `b_j` at the sites `y_j`. -/
def semidiscreteTransportDual {d k : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (b g : Fin k → ℝ) : ℝ :=
  (∫ x, sInf (range fun j ↦ ‖x - y j‖ ^ 2 - g j) ∂P) + ∑ j, b j * g j

/-- The random-feature summand `2 cos(⟨w, x⟩ + b) cos(⟨w, y⟩ + b)` at the frequency-phase pair
`s = (w, b)`. -/
def randomFourierFeatureTerm {d : ℕ} (x y : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  2 * Real.cos (inner ℝ s.1 x + s.2) * Real.cos (inner ℝ s.1 y + s.2)

/-- The random Fourier feature kernel of a sample of `D` frequency-phase pairs: the sample mean
`D⁻¹ ∑_j 2 cos(⟨w_j, x⟩ + b_j) cos(⟨w_j, y⟩ + b_j)` of the random-feature summands. -/
def randomFourierFeatureKernel {d D : ℕ}
    (sample : Fin D → EuclideanSpace ℝ (Fin d) × ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (D : ℝ)⁻¹ * ∑ j, randomFourierFeatureTerm x y (sample j)

end CKSD
