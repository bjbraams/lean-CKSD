module

public import CKSD.Geometry.Basic
public import CKSD.Bayes.Basic

/-!
# Geometry: Transport

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

/-- GAPS 108.40, all three bounded-support regimes on a unit ball. -/
theorem integral_empirical_wasserstein_rpow_le (d : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ P : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P →
      P (Metric.closedBall 0 1) = 1 → ∀ n : ℕ, 1 ≤ n →
      (∫ x, Real.rpow (TauCeti.wassersteinEDist (ENNReal.ofReal p)
        (empiricalMeasure n x) P).toReal p
        ∂(Measure.pi fun _ : Fin n ↦ P)) ≤ C *
        (if (d : ℝ) < 2 * p then (Real.sqrt n)⁻¹
          else if (d : ℝ) = 2 * p then Real.log (1 + n) / Real.sqrt n
          else Real.rpow n (-p / d)) := by
  sorry

/-- GAPS 108.42: L2 stability of optimal maps with a fixed absolutely continuous source. -/
theorem tendsto_integral_sq_optimal_map_sub {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
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
theorem exists_measure_preserving_isometryEquiv_of_zero_distortion
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
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
theorem wasserstein_multivariateGaussian_sq_eq {d : ℕ} (m n : EuclideanSpace ℝ (Fin d))
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (TauCeti.wassersteinEDist 2 (multivariateGaussian m A) (multivariateGaussian n B)).toReal ^ 2 =
      ‖m - n‖ ^ 2 + Matrix.trace (A + B - 2 • CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A)) := by
  sorry

/-- GAPS 108.46: the covariance equation and unique Gaussian barycenter of finitely many laws. -/
theorem exists_unique_gaussian_wasserstein_barycenter {k d : ℕ} (w : Fin k → ℝ)
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
theorem wasserstein_uniform_cube_lower_bound {d : ℕ} (hd : 3 ≤ d) (n : ℕ) (hn : 1 ≤ n)
    (Q : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Q]
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (hsupp : Q (range x) = 1) :
    let cube := {z : EuclideanSpace ℝ (Fin d) | ∀ i, z i ∈ Icc (0 : ℝ) 1};
    Real.rpow n (-(1 / (d : ℝ))) / (108 * d) ≤
      (TauCeti.wassersteinEDist 1 (volume.restrict cube) Q).toReal := by
  sorry

/-- GAPS 108.51, the parametric rate of Gaussian-smoothed empirical W1 on a bounded cube. -/
theorem integral_wasserstein_gaussianSmoothing_empiricalMeasure_le
    (d : ℕ) (sigma : ℝ) (hs : 0 < sigma) :
    ∃ C > 0, ∀ P : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure P →
      P {x | ∀ i, x i ∈ Icc (-1 : ℝ) 1} = 1 → ∀ n : ℕ, 1 ≤ n →
      (∫ x, (TauCeti.wassersteinEDist 1 (gaussianSmoothing sigma (empiricalMeasure n x))
        (gaussianSmoothing sigma P)).toReal
        ∂(Measure.pi fun _ : Fin n ↦ P)) ≤ C / Real.sqrt n := by
  sorry

/-- GAPS 108.56: smooth semidiscrete dual, cell-mass equations and dual attainment. -/
theorem semidiscreteTransportDual_concave_differentiable_and_attains_max {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hP : P ≪ volume) (h2 : MemLp id 2 P)
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (hy : Function.Injective y)
    (b : Fin k → ℝ) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1) :
    let E := semidiscreteTransportDual P y b;
    ConcaveOn ℝ univ E ∧ ContDiff ℝ 1 E ∧
      (∀ g, HasFDerivAt E
        (∑ j, (b j - P.real (laguerreCell y g j)) • (ContinuousLinearMap.proj j : (Fin k → ℝ)
          →L[ℝ] ℝ)) g) ∧
      (∀ g, (∀ h, E h ≤ E g) ↔ ∀ j, P.real (laguerreCell y g j) = b j) ∧
      ∃ g, (∀ h, E h ≤ E g) ∧
        E g = (TauCeti.wassersteinEDist 2 P (∑ j, ENNReal.ofReal (b j) • Measure.dirac
          (y j))).toReal ^ 2 := by
  sorry

/-- GAPS 108.57, the covariance-commutation criterion for compatibility with the standard
Gaussian. -/
theorem gaussian_optimal_maps_compatible_iff_covariances_commute
    {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    CFC.sqrt B * (CFC.sqrt A)⁻¹ =
      (CFC.sqrt A)⁻¹ * CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A) * (CFC.sqrt A)⁻¹ ↔
      A * B = B * A := by
  sorry

/-- GAPS 108.59, the energy-descent inequality for the averaged-transport update.
Only this finite-step inequality is asserted, not the convergence of the iteration. -/
theorem wasserstein_energy_descent_of_averaged_transport {d k : ℕ} (hk : 0 < k)
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


end CKSD
