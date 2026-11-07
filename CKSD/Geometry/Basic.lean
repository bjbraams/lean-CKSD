module

public import CKSD.Nonparametric.Basic
public import CKSD.LinearModels.Basic

/-!
# Geometry: definitions

Sources: `GAPS.md`, `SYNOPSIS108.md`, and `STRUCTURE108.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Weighted degree of a vertex. -/
def weightedDegree {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, W i j

/-- Weighted volume of a set of vertices. -/
def graphVolume {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, weightedDegree W i

/-- Weight crossing a cut, counted once. -/
def cutWeight {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, W i j

/-- Conductance, with nonempty proper cuts only. -/
def cheegerConstant {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    r = cutWeight W S / min (graphVolume W S) (graphVolume W Sᶜ)}

/-- The normalized Laplacian's spectral gap, via the degree-weighted Rayleigh principle. -/
def spectralGap {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ f : Fin n → ℝ, (∑ i, weightedDegree W i * f i) = 0 ∧
    (∑ i, weightedDegree W i * f i ^ 2) = 1 ∧
      r = (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2}

/-- Radius needed to capture mass `u` around `x`. -/
def massRadius {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (u : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r | 0 ≤ r ∧ ENNReal.ofReal u ≤ P (Metric.closedBall x r)}

/-- Distance to a measure at mass `m`. -/
def distanceToMeasure {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt ((∫ u in (0 : ℝ)..m, massRadius P u x ^ 2) / m)

/-- Squared maximum mean discrepancy as the kernel double-integral expression. -/
def squaredMMD {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  (∫ z, k z.1 z.2 ∂P.prod P) + (∫ z, k z.1 z.2 ∂Q.prod Q) -
    2 * ∫ z, k z.1 z.2 ∂P.prod Q

/-- Characteristicness expressed by vanishing squared discrepancy. -/
def IsCharacteristicKernel {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) : Prop :=
  ∀ P Q : Measure X, IsProbabilityMeasure P → IsProbabilityMeasure Q →
    (squaredMMD k P Q = 0 ↔ P = Q)

/-- Unbiased empirical MMD squared for equal sample sizes. -/
def unbiasedSquaredMMD {X : Type*} (k : X → X → ℝ) (n : ℕ) (x y : Fin n → X) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j then k (x i) (x j) + k (y i) (y j) else 0) /
    ((n : ℝ) * (n - 1 : ℕ))) - 2 / (n : ℝ) ^ 2 * ∑ i, ∑ j, k (x i) (y j)

/-- The distance-induced kernel with base point zero. -/
def distanceKernel {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (‖x‖ + ‖y‖ - ‖x - y‖) / 2

/-- Doubly centered pairwise distance. -/
def centeredDistance {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  dist x y - (∫ z, dist x z ∂P) - (∫ z, dist z y ∂P) + ∫ z, dist z.1 z.2 ∂P.prod P

/-- Gaussian convolution as a pushforward of independent addition. -/
def gaussianSmoothing {d : ℕ} (sigma : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (multivariateGaussian 0 (sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)))).map
    (fun z ↦ z.1 + z.2)

/-- Laguerre cell for the squared Euclidean cost. -/
def laguerreCell {d k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (j : Fin k) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ‖x - y j‖ ^ 2 - g j ≤ ‖x - y i‖ ^ 2 - g i}

/-- Semidiscrete transport dual functional. -/
def semidiscreteTransportDual {d k : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (b g : Fin k → ℝ) : ℝ :=
  (∫ x, sInf (range fun j ↦ ‖x - y j‖ ^ 2 - g j) ∂P) + ∑ j, b j * g j

/-- A finite random-Fourier-feature kernel. -/
def randomFourierFeatureKernel {d D : ℕ}
    (sample : Fin D → EuclideanSpace ℝ (Fin d) × ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 / D * ∑ j, Real.cos (inner ℝ (sample j).1 x + (sample j).2) *
    Real.cos (inner ℝ (sample j).1 y + (sample j).2)


end CKSD
