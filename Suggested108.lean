module

public import Suggested107

/-!
# Suggested statements for Section 108

Sources: `GAPS.md`, `SYNOPSIS108.md`, `STRUCTURE108.md`.
Every theorem proof is admitted. Wasserstein distances use TauCeti's
`wassersteinEDist`, with finite-moment hypotheses before taking `toReal`.
The Rayleigh infimum below defines the first nonzero normalized-Laplacian
spectral value, rather than choosing an ordering of eigenvectors.

Not represented: 108.4 (reach and graph-geodesic approximation), 108.5's
manifold CLT, 108.13 and 108.15 (injectivity radius/cut locus/logarithms),
108.18–20 and 108.22–23 (persistence modules, diagrams, landscapes and
homotopy inference), 108.32 (the persistence pairing interpretation),
108.34–37 (Morse and persistence-stability/inference frameworks),
108.44 (universal Gibbs kernels for entropic costs), 108.47 (a weighted
Brownian bridge law), 108.50's statistical minimax part, 108.51's torus
estimator, 108.53 and 108.55 (semidual/entropic-map statistical classes),
108.58 (Wasserstein differentiation and Karcher regularity), and 108.72
(Stein convergence-control and counterexample classes). The finite-feature
limits in 108.61 do not cover infinite-rank Gaussian-chaos series; the
independence criterion in 108.63 does not include the fourth-order statistic.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD.Section108

attribute [local instance] Classical.propDecidable

/-- Weighted degree of a vertex. -/
def degree {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := ∑ j, W i j

/-- Weighted volume of a set of vertices. -/
def graphVolume {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, degree W i

/-- Weight crossing a cut, counted once. -/
def cut {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, W i j

/-- Conductance, with nonempty proper cuts only. -/
def cheeger {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ S : Finset (Fin n), S.Nonempty ∧ S ≠ Finset.univ ∧
    r = cut W S / min (graphVolume W S) (graphVolume W Sᶜ)}

/-- The normalized Laplacian's spectral gap, via the degree-weighted Rayleigh principle. -/
def spectralGap {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r | ∃ f : Fin n → ℝ, (∑ i, degree W i * f i) = 0 ∧
    (∑ i, degree W i * f i ^ 2) = 1 ∧
      r = (∑ i, ∑ j, W i j * (f i - f j) ^ 2) / 2}

/-- Radius needed to capture mass `u` around `x`. -/
def massRadius {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (u : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r | 0 ≤ r ∧ ENNReal.ofReal u ≤ P (Metric.closedBall x r)}

/-- Distance to a measure at mass `m`. -/
def dtm {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt ((∫ u in (0 : ℝ)..m, massRadius P u x ^ 2) / m)

/-- Squared maximum mean discrepancy as the kernel double-integral expression. -/
def mmdSq {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  (∫ z, k z.1 z.2 ∂P.prod P) + (∫ z, k z.1 z.2 ∂Q.prod Q) -
    2 * ∫ z, k z.1 z.2 ∂P.prod Q

/-- Characteristicness expressed by vanishing squared discrepancy. -/
def Characteristic {X : Type*} [MeasurableSpace X] (k : X → X → ℝ) : Prop :=
  ∀ P Q : Measure X, IsProbabilityMeasure P → IsProbabilityMeasure Q →
    (mmdSq k P Q = 0 ↔ P = Q)

/-- Unbiased empirical MMD squared for equal sample sizes. -/
def mmdU {X : Type*} (k : X → X → ℝ) (n : ℕ) (x y : Fin n → X) : ℝ :=
  ((∑ i, ∑ j, if i ≠ j then k (x i) (x j) + k (y i) (y j) else 0) /
    ((n : ℝ) * (n - 1 : ℕ))) - 2 / (n : ℝ) ^ 2 * ∑ i, ∑ j, k (x i) (y j)

/-- The distance-induced kernel with base point zero. -/
def distanceKernel {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (‖x‖ + ‖y‖ - ‖x - y‖) / 2

/-- Doubly centered pairwise distance. -/
def centeredDistance {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  dist x y - (∫ z, dist x z ∂P) - (∫ z, dist z y ∂P) + ∫ z, dist z.1 z.2 ∂P.prod P

/-- GAPS 108.1: Cheeger's inequalities for a finite weighted connected graph. -/
theorem gap108_1 {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin n) (Fin n) ℝ)
    (hsym : W.IsSymm) (hpos : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 0)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 0 < cut W S) :
    spectralGap W / 2 ≤ cheeger W ∧ cheeger W ≤ Real.sqrt (2 * spectralGap W) ∧
      1 - Real.sqrt (1 - cheeger W ^ 2) ≤ spectralGap W := by
  sorry

/-- GAPS 108.5, existence and uniqueness in a complete space satisfying the CAT(0) midpoint inequality. -/
theorem gap108_5 {X : Type*} [MetricSpace X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (mid : X → X → X)
    (hmid : ∀ x y z, dist z (mid x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4)
    (o : X) (h2 : Integrable (fun x ↦ dist o x ^ 2) P) :
    ∃! m : X, ∀ p : X, (∫ x, dist m x ^ 2 ∂P) ≤ ∫ x, dist p x ^ 2 ∂P := by
  sorry

/-- GAPS 108.7, noiseless Hausdorff sampling rate from a uniform small-ball lower bound. -/
theorem gap108_7 {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → X) (hiid : IID μ Xn P) (K : Set X) (hK : IsCompact K)
    (hsupp : P K = 1) (d c r₀ : ℝ) (hd : 0 < d) (hc : 0 < c) (hr₀ : 0 < r₀)
    (hlower : ∀ x ∈ K, ∀ r ∈ Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (c * Real.rpow r d) ≤ P (Metric.ball x r)) :
    BoundedInProbability μ (fun n ω ↦
      Metric.hausdorffDist (range fun i : Fin n ↦ Xn i.val ω) K /
        Real.rpow (Real.log (n + 1) / n) (1 / d)) := by
  sorry

/-- GAPS 108.8, Schoenberg's Euclidean-distance criterion by double centering. -/
theorem gap108_8 {n : ℕ} (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ)
    (hsym : D.IsSymm) (hdiag : ∀ i, D i i = 0) :
    let J := (1 : Matrix (Fin n) (Fin n) ℝ) - (n : ℝ)⁻¹ • Matrix.of (fun _ _ ↦ (1 : ℝ));
    ((-(1 / 2 : ℝ)) • (J * D * J)).PosSemidef ↔
      ∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, D i j = ‖x i - x j‖ ^ 2 := by
  sorry

/-- GAPS 108.10, extrinsic means are nearest points to the Euclidean expectation. -/
theorem gap108_10 {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (h2 : MemLp id 2 P) (S : Set (EuclideanSpace ℝ (Fin d)))
    (m : EuclideanSpace ℝ (Fin d)) (hm : m ∈ S) :
    (∀ p ∈ S, (∫ x, ‖x - m‖ ^ 2 ∂P) ≤ ∫ x, ‖x - p‖ ^ 2 ∂P) ↔
      ∀ p ∈ S, ‖(∫ x, x ∂P) - m‖ ≤ ‖(∫ x, x ∂P) - p‖ := by
  sorry

/-- GAPS 108.10, projected empirical-mean central limit theorem. -/
theorem gap108_10_clt {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hiid : IID μ X P) (h2 : MemLp id 2 P) :
    let m := ∫ x, x ∂P;
    let C := Matrix.of (fun i j ↦ ∫ x, (x i - m i) * (x j - m j) ∂P);
    ∀ (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
    ∀ (hm : Measurable proj),
    ∀ (D : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)),
    ∀ (hd : HasFDerivAt proj D m),
    InLaw μ (fun n ω ↦ Real.sqrt n • (proj (average X n ω) - proj m))
      ((multivariateGaussian 0 C).map D) := by
  sorry

/-- GAPS 108.21, the Euclidean Čech/Rips inclusions, in the diameter-`2r` convention. -/
theorem gap108_21 {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (r : ℝ) (hr : 0 ≤ r) :
    ((∃ c, ∀ x ∈ S, dist x c ≤ r) → ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) ∧
      ((∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2 * r) →
        ∃ c, ∀ x ∈ S, dist x c ≤ Real.sqrt 2 * r) := by
  sorry

/-- GAPS 108.24: stability of distance to a measure. -/
theorem gap108_24 {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 2 P) (hQ : MemLp id 2 Q) (m : ℝ) (hm : m ∈ Ioc 0 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    |dtm P m x - dtm Q m x| ≤
      (TauCeti.wassersteinEDist 2 P Q).toReal / Real.sqrt m := by
  sorry

/-- GAPS 108.40, all three bounded-support regimes on a unit ball. -/
theorem gap108_40 (d : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ P : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P →
      P (Metric.closedBall 0 1) = 1 → ∀ n : ℕ, 1 ≤ n →
      (∫ x, Real.rpow (TauCeti.wassersteinEDist (ENNReal.ofReal p) (empirical n x) P).toReal p
        ∂(Measure.pi fun _ : Fin n ↦ P)) ≤ C *
        (if (d : ℝ) < 2 * p then (Real.sqrt n)⁻¹
          else if (d : ℝ) = 2 * p then Real.log (1 + n) / Real.sqrt n
          else Real.rpow n (-p / d)) := by
  sorry

/-- GAPS 108.42: L2 stability of optimal maps with a fixed absolutely continuous source. -/
theorem gap108_42 {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (νn : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (hνn : ∀ n, IsProbabilityMeasure (νn n)) (hac : μ ≪ volume)
    (hμ2 : MemLp id 2 μ) (hν2 : MemLp id 2 ν) (hνn2 : ∀ n, MemLp id 2 (νn n))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Tn : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : Measurable T) (hTn : ∀ n, Measurable (Tn n))
    (hpush : μ.map T = ν) (hpushn : ∀ n, μ.map (Tn n) = νn n)
    (hopt : (∫ x, ‖x - T x‖ ^ 2 ∂μ) = (TauCeti.wassersteinEDist 2 μ ν).toReal ^ 2)
    (hoptn : ∀ n, (∫ x, ‖x - Tn n x‖ ^ 2 ∂μ) = (TauCeti.wassersteinEDist 2 μ (νn n)).toReal ^ 2)
    (hconv : Tendsto (fun n ↦ (TauCeti.wassersteinEDist 2 (νn n) ν).toReal) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖Tn n x - T x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  sorry

/-- GAPS 108.43, the missing upgrade from a zero-distortion coupling to an isometry.
The full-support assumption realizes the source's restriction to the supports. -/
theorem gap108_43 {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x, ∀ r > 0, 0 < μ (Metric.ball x r))
    (hν : ∀ y, ∀ r > 0, 0 < ν (Metric.ball y r))
    (π : Measure (X × Y)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hdist : ∀ᵐ z ∂π.prod π, dist z.1.1 z.2.1 = dist z.1.2 z.2.2) :
    ∃ f : X ≃ᵢ Y, μ.map f = ν := by
  sorry

/-- GAPS 108.46: the Gaussian Bures formula, allowing both covariances to be singular. -/
theorem gap108_46 {d : ℕ} (m n : EuclideanSpace ℝ (Fin d))
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (TauCeti.wassersteinEDist 2 (multivariateGaussian m A) (multivariateGaussian n B)).toReal ^ 2 =
      ‖m - n‖ ^ 2 + Matrix.trace (A + B - 2 • CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)) := by
  sorry

/-- GAPS 108.46: the covariance equation and unique Gaussian barycenter of finitely many laws. -/
theorem gap108_46_barycenter {k d : ℕ} (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (m : Fin k → EuclideanSpace ℝ (Fin d)) (A : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i).PosDef) :
    let F := fun P : Measure (EuclideanSpace ℝ (Fin d)) ↦
      ∑ i, w i * (TauCeti.wassersteinEDist 2 P (multivariateGaussian (m i) (A i))).toReal ^ 2;
    ∃ S : Matrix (Fin d) (Fin d) ℝ, S.PosDef ∧
      S = ∑ i, w i • CFC.sqrt (CFC.sqrt S * A i * CFC.sqrt S) ∧
      ∀ P : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P → MemLp id 2 P →
        F (multivariateGaussian (∑ i, w i • m i) S) ≤ F P ∧
          (F (multivariateGaussian (∑ i, w i • m i) S) = F P ↔
            P = multivariateGaussian (∑ i, w i • m i) S) := by
  sorry

/-- GAPS 108.50, quantization lower bound for the uniform unit cube. -/
theorem gap108_50 {d : ℕ} (hd : 3 ≤ d) (n : ℕ) (hn : 1 ≤ n)
    (Q : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Q]
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hsupp : Q (range x) = 1) :
    let cube := {z : EuclideanSpace ℝ (Fin d) | ∀ i, z i ∈ Icc (0 : ℝ) 1};
    Real.rpow n (-(1 / (d : ℝ))) / (108 * d) ≤
      (TauCeti.wassersteinEDist 1 (volume.restrict cube) Q).toReal := by
  sorry

/-- Gaussian convolution as a pushforward of independent addition. -/
def smooth {d : ℕ} (sigma : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (multivariateGaussian 0 (sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)))).map
    (fun z ↦ z.1 + z.2)

/-- GAPS 108.51, the parametric rate of Gaussian-smoothed empirical W1 on a bounded cube. -/
theorem gap108_51 (d : ℕ) (sigma : ℝ) (hs : 0 < sigma) :
    ∃ C > 0, ∀ P : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P →
      P {x | ∀ i, x i ∈ Icc (-1 : ℝ) 1} = 1 → ∀ n : ℕ, 1 ≤ n →
      (∫ x, (TauCeti.wassersteinEDist 1 (smooth sigma (empirical n x)) (smooth sigma P)).toReal
        ∂(Measure.pi fun _ : Fin n ↦ P)) ≤ C / Real.sqrt n := by
  sorry

/-- Laguerre cell for the squared Euclidean cost. -/
def laguerre {d k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (j : Fin k) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ‖x - y j‖ ^ 2 - g j ≤ ‖x - y i‖ ^ 2 - g i}

/-- Semidiscrete transport dual functional. -/
def semidiscrete {d k : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (b g : Fin k → ℝ) : ℝ :=
  (∫ x, sInf (range fun j ↦ ‖x - y j‖ ^ 2 - g j) ∂P) + ∑ j, b j * g j

/-- GAPS 108.56: smooth semidiscrete dual, cell-mass equations and dual attainment. -/
theorem gap108_56 {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP : P ≪ volume) (h2 : MemLp id 2 P)
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (hy : Function.Injective y)
    (b : Fin k → ℝ) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1) :
    let E := semidiscrete P y b;
    ConcaveOn ℝ univ E ∧ ContDiff ℝ 1 E ∧
      (∀ g, HasFDerivAt E
        (∑ j, (b j - P.real (laguerre y g j)) • (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) g) ∧
      (∀ g, (∀ h, E h ≤ E g) ↔ ∀ j, P.real (laguerre y g j) = b j) ∧
      ∃ g, (∀ h, E h ≤ E g) ∧
        E g = (TauCeti.wassersteinEDist 2 P (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))).toReal ^ 2 := by
  sorry

/-- GAPS 108.57, the covariance-commutation criterion for compatibility with the standard Gaussian. -/
theorem gap108_57 {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    CFC.sqrt B * (CFC.sqrt A)⁻¹ =
      (CFC.sqrt A)⁻¹ * CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A) * (CFC.sqrt A)⁻¹ ↔
      A * B = B * A := by
  sorry

/-- GAPS 108.59, the energy-descent inequality for the averaged-transport update.
Only this finite-step inequality is asserted, not the convergence of the iteration. -/
theorem gap108_59 {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (hP2 : MemLp id 2 P)
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (P.map (T i))).toReal ^ 2) :
    let g := fun x ↦ x - (k : ℝ)⁻¹ • ∑ i, T i x;
    let F := fun Q ↦ (∑ i, (TauCeti.wassersteinEDist 2 Q (P.map (T i))).toReal ^ 2) / (2 * k);
    ∀ (tau : ℝ),
    ∀ (htau : tau ∈ Icc 0 1),
    F (P.map (fun x ↦ x - tau • g x)) - F P ≤
      -(tau - tau ^ 2 / 2) * ∫ x, ‖g x‖ ^ 2 ∂P := by
  sorry

/-- GAPS 108.61, the null limit of MMD for a bounded finite-dimensional feature map. -/
theorem gap108_61_null {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn Yn : ℕ → Ω → X) (hiid : IID μ (fun i ω ↦ (Xn i ω, Yn i ω)) (P.prod P))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (hb : ∃ C, ∀ x, ‖phi x‖ ≤ C) :
    let m := ∫ x, phi x ∂P;
    let C := Matrix.of fun i j ↦ ∫ x, (phi x i - m i) * (phi x j - m j) ∂P;
    let k := fun x y ↦ inner ℝ (phi x) (phi y);
    InLaw μ (fun n ω ↦ (n : ℝ) * mmdU k n (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω))
      ((multivariateGaussian 0 C).map (fun z ↦ 2 * (‖z‖ ^ 2 - Matrix.trace C))) ∧
      InLaw μ (fun n ω ↦ (n : ℝ) *
        ‖average (fun i ω ↦ phi (Xn i ω)) n ω - average (fun i ω ↦ phi (Yn i ω)) n ω‖ ^ 2)
        ((multivariateGaussian 0 C).map (fun z ↦ 2 * ‖z‖ ^ 2)) := by
  sorry

/-- GAPS 108.61, alternative MMD CLT for a bounded finite-dimensional feature map. -/
theorem gap108_61_alternative {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xn Yn : ℕ → Ω → X) (hiid : IID μ (fun i ω ↦ (Xn i ω, Yn i ω)) (P.prod Q))
    (phi : X → EuclideanSpace ℝ (Fin d)) (hm : Measurable phi)
    (hb : ∃ C, ∀ x, ‖phi x‖ ≤ C) :
    let delta := (∫ x, phi x ∂P) - ∫ x, phi x ∂Q;
    let k := fun x y ↦ inner ℝ (phi x) (phi y);
    InLaw μ (fun n ω ↦ Real.sqrt n *
      (mmdU k n (fun i ↦ Xn i.val ω) (fun i ↦ Yn i.val ω) - ‖delta‖ ^ 2))
      (gaussianReal 0 (Real.toNNReal
        (4 * variance P (fun x ↦ inner ℝ (phi x) delta) +
          4 * variance Q (fun x ↦ inner ℝ (phi x) delta)))) := by
  sorry

/-- GAPS 108.62: nonnegativity, separation, and the kernel form of energy distance. -/
theorem gap108_62 {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x ↦ ‖x‖) P) (hQ : Integrable (fun x ↦ ‖x‖) Q) :
    let D := 2 * (∫ z, ‖z.1 - z.2‖ ∂P.prod Q) - (∫ z, ‖z.1 - z.2‖ ∂P.prod P) -
      ∫ z, ‖z.1 - z.2‖ ∂Q.prod Q;
    0 ≤ D ∧ (D = 0 ↔ P = Q) ∧ D = 2 * mmdSq distanceKernel P Q := by
  sorry

/-- GAPS 108.62: distance covariance detects independence and equals four times HSIC. -/
theorem gap108_62_covariance {d e : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)))
    [IsProbabilityMeasure P] (h2 : MemLp id 2 P) :
    let mu := P.map Prod.fst;
    let nu := P.map Prod.snd;
    let V := ∫ z, centeredDistance mu z.1.1 z.2.1 * centeredDistance nu z.1.2 z.2.2 ∂P.prod P;
    let k := fun x y : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) ↦
      distanceKernel x.1 y.1 * distanceKernel x.2 y.2;
    0 ≤ V ∧ (V = 0 ↔ P = mu.prod nu) ∧ V = 4 * mmdSq k P (mu.prod nu) := by
  sorry

/-- GAPS 108.63, independence criterion for a characteristic product-space kernel. -/
theorem gap108_63 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (k : (X × Y) → (X × Y) → ℝ)
    (hk : Characteristic k) :
    mmdSq k P ((P.map Prod.fst).prod (P.map Prod.snd)) = 0 ↔
      IndepFun Prod.fst Prod.snd P := by
  sorry

/-- GAPS 108.68(c), characteristicness iff the symmetric spectral measure has full support. -/
theorem gap108_68_spectral {d : ℕ} (hd : 0 < d)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure L]
    (hsym : L.map (fun x ↦ -x) = L) :
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    Characteristic k ↔ ∀ x, ∀ r > 0, 0 < L (Metric.ball x r) := by
  sorry

/-- GAPS 108.68(d), quadratic-polynomial MMD depends only on the first two moments. -/
theorem gap108_68_polynomial {d : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : MemLp id 4 P) (hQ : MemLp id 4 Q) :
    let m := (∫ x, x ∂P) - ∫ x, x ∂Q;
    mmdSq (fun x y ↦ (1 + inner ℝ x y) ^ 2) P Q =
      2 * ‖m‖ ^ 2 + ∑ i, ∑ j,
        ((∫ x, x i * x j ∂P) - ∫ x, x i * x j ∂Q) ^ 2 := by
  sorry

/-- GAPS 108.70, MMD metrizes weak convergence along uniformly tight sequences. -/
theorem gap108_70 {X : Type*} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (P : ℕ → Measure X) (Q : Measure X) (hP : ∀ n, IsProbabilityMeasure (P n))
    [IsProbabilityMeasure Q] (k : X → X → ℝ)
    (hk : Continuous (Function.uncurry k)) (hb : ∃ C, ∀ x y, |k x y| ≤ C)
    (hchar : Characteristic k)
    (htight : ∀ epsilon > 0, ∃ K : Set X, IsCompact K ∧
      ∀ n, (P n) Kᶜ ≤ ENNReal.ofReal epsilon) :
    Weakly P Q ↔ Tendsto (fun n ↦ mmdSq k (P n) Q) atTop (𝓝 0) := by
  sorry

/-- GAPS 108.71, scalar Langevin Stein identity for bounded continuously differentiable tests. -/
theorem gap108_71 (P : Measure ℝ) [IsProbabilityMeasure P] (p g : ℝ → ℝ)
    (hp : HasDensity P volume p) (hpos : ∀ x, 0 < p x)
    (hp1 : ContDiff ℝ 1 p) (hg : ContDiff ℝ 1 g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) (hscore : Integrable (fun x ↦ |deriv p x / p x|) P)
    (hder : Integrable (deriv g) P) :
    (∫ x, g x * (deriv p x / p x) + deriv g x ∂P) = 0 := by
  sorry

/-- A finite random-Fourier-feature kernel. -/
def randomFeatures {d D : ℕ}
    (sample : Fin D → EuclideanSpace ℝ (Fin d) × ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 / D * ∑ j, Real.cos (inner ℝ (sample j).1 x + (sample j).2) *
    Real.cos (inner ℝ (sample j).1 y + (sample j).2)

/-- GAPS 108.74: unbiased random Fourier features and their pointwise Hoeffding bound. -/
theorem gap108_74 {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (x y : EuclideanSpace ℝ (Fin d)) (epsilon : ℝ) (he : 0 < epsilon) :
    let P := Measure.pi (fun _ : Fin D ↦ L.prod phase);
    let k := ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    (∫ sample, randomFeatures sample x y ∂P) = k ∧
      P.real {sample | epsilon ≤ |randomFeatures sample x y - k|} ≤
        2 * Real.exp (-(D : ℝ) * epsilon ^ 2 / 8) := by
  sorry

/-- GAPS 108.74: the uniform compact-set random-feature bound. -/
theorem gap108_74_uniform {d : ℕ} (D : ℕ) (hD : 1 ≤ D)
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] (hL2 : MemLp id 2 L)
    (phase : Measure ℝ) [IsProbabilityMeasure phase]
    (hphase : phase = (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Icc 0 (2 * Real.pi)))
    (M : Set (EuclideanSpace ℝ (Fin d))) (hM : IsCompact M)
    (epsilon : ℝ) (he : 0 < epsilon) :
    let sigma := Real.sqrt (∫ w, ‖w‖ ^ 2 ∂L);
    ∀ (hscale : epsilon ≤ sigma * Metric.diam M),
    let k := fun x y ↦ ∫ w, Real.cos (inner ℝ w (x - y)) ∂L;
    let P := Measure.pi (fun _ : Fin D ↦ L.prod phase);
    P.real {sample | ∃ x ∈ M, ∃ y ∈ M, epsilon ≤ |randomFeatures sample x y - k x y|} ≤
      98 * (sigma * Metric.diam M / epsilon) ^ 2 *
        Real.exp (-(D : ℝ) * epsilon ^ 2 / (32 * (d + 1))) := by
  sorry

/-- GAPS 108.74, deterministic transfer of a uniform kernel error to squared MMD. -/
theorem gap108_74_mmd {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (M : Set X) (hM : IsCompact M) (hP : P M = 1) (hQ : Q M = 1)
    (k l : X → X → ℝ) (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (epsilon : ℝ) (he : 0 ≤ epsilon) (herr : ∀ x ∈ M, ∀ y ∈ M, |k x y - l x y| ≤ epsilon) :
    |mmdSq k P Q - mmdSq l P Q| ≤ 4 * epsilon := by
  sorry

end CKSD.Section108
