module

public import CKSD.Geometry.Basic
public import CKSD.Geometry.GaussianTransport
public import CKSD.Geometry.OptimalMapStability
public import CKSD.Bayes.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.MeasureTheory.Measure.Support

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

/-- A continuous map from a compact space onto a law with full support takes the support of
the source law onto the target space. -/
theorem exists_mem_support_preimage_of_support_eq_univ
    {A Z : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (π : Measure A) (f : A → Z) (hf : Continuous f) (ρ : Measure Z)
    (hmap : π.map f = ρ) (hfull : ρ.support = univ) (z : Z) :
    ∃ w ∈ π.support, f w = z := by
  have hclosed : IsClosed (f '' π.support) := π.isClosed_support.isCompact.image hf |>.isClosed
  have hsupport : ∀ᵐ w ∂π, w ∈ π.support := π.support_mem_ae
  have hae : ∀ᵐ z ∂ρ, z ∈ f '' π.support := by
    rw [← hmap]
    apply (ae_map_iff (p := fun z ↦ z ∈ f '' π.support)
      hf.measurable.aemeasurable hclosed.measurableSet).mpr
    exact hsupport.mono fun w hw ↦ mem_image_of_mem f hw
  exact ρ.support_subset_of_isClosed hclosed hae (hfull ▸ mem_univ z)

/-- GAPS 108.43, the upgrade from a zero-distortion coupling to an isometry.
The full-support assumption realizes the source's restriction to the supports. -/
theorem exists_measure_preserving_isometryEquiv_of_zero_distortion
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y)

    (hμ : ∀ x, ∀ r > 0, 0 < μ (Metric.ball x r))
    (hν : ∀ y, ∀ r > 0, 0 < ν (Metric.ball y r))
    (π : Measure (X × Y)) [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hdist : ∀ᵐ z ∂π.prod π, dist z.1.1 z.2.1 = dist z.1.2 z.2.2) :
    ∃ f : X ≃ᵢ Y, μ.map f = ν := by
  have hpair : ∀ z ∈ π.support, ∀ w ∈ π.support, dist z.1 w.1 = dist z.2 w.2 := by
    have ha : ∀ᵐ z ∂π, ∀ w ∈ π.support, dist z.1 w.1 = dist z.2 w.2 := by
      filter_upwards [Measure.ae_ae_of_ae_prod hdist] with z hz
      exact π.support_subset_of_isClosed (isClosed_eq (by fun_prop) (by fun_prop)) hz
    intro z hz w hw
    have hb : ∀ᵐ z ∂π, dist z.1 w.1 = dist z.2 w.2 := ha.mono fun z hz ↦ hz w hw
    exact π.support_subset_of_isClosed (isClosed_eq (by fun_prop) (by fun_prop)) hb hz
  have hfullμ : μ.support = univ := by
    ext x
    simp only [mem_univ, iff_true]
    rw [(Metric.nhds_basis_ball).mem_measureSupport]
    exact fun r hr ↦ hμ x r hr
  have hfullν : ν.support = univ := by
    ext y
    simp only [mem_univ, iff_true]
    rw [(Metric.nhds_basis_ball).mem_measureSupport]
    exact fun r hr ↦ hν y r hr
  have hfstsurj := exists_mem_support_preimage_of_support_eq_univ π Prod.fst continuous_fst
    μ hfst hfullμ
  have hsndsurj := exists_mem_support_preimage_of_support_eq_univ π Prod.snd continuous_snd
    ν hsnd hfullν
  choose s hs hsx using hfstsurj
  let f : X → Y := fun x ↦ (s x).2
  have hiso : Isometry f := Isometry.of_dist_eq fun x x' ↦ by
    simpa only [f, hsx] using (hpair (s x) (hs x) (s x') (hs x')).symm
  have hgraph : ∀ z ∈ π.support, f z.1 = z.2 := by
    intro z hz
    have h := hpair (s z.1) (hs z.1) z hz
    rw [hsx, dist_self] at h
    exact dist_eq_zero.mp h.symm
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hsndsurj y
    exact ⟨z.1, (hgraph z hz).trans hzy⟩
  let e : X ≃ᵢ Y :=
    { Equiv.ofBijective f ⟨hiso.injective, hfsurj⟩ with isometry_toFun := hiso }
  refine ⟨e, ?_⟩
  change μ.map f = ν
  rw [← hfst, Measure.map_map hiso.continuous.measurable measurable_fst, ← hsnd]
  have hsupport : ∀ᵐ z ∂π, z ∈ π.support := π.support_mem_ae
  exact Measure.map_congr (hsupport.mono fun z hz ↦ hgraph z hz)

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

/-- A matrix commuting with `B` commutes with its square root `CFC.sqrt B`. -/
theorem commute_cfcSqrt_right {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (h : Commute A B) :
    Commute A (CFC.sqrt B) := by
  rw [CFC.sqrt_eq_cfc]
  exact (h.symm.cfc_nnreal _).symm

/-- GAPS 108.57, the covariance-commutation criterion for compatibility with the standard
Gaussian. -/
theorem gaussian_optimal_maps_compatible_iff_covariances_commute
    {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    CFC.sqrt B * (CFC.sqrt A)⁻¹ =
      (CFC.sqrt A)⁻¹ * CFC.sqrt (CFC.sqrt A * B * CFC.sqrt A) * (CFC.sqrt A)⁻¹ ↔
      A * B = B * A := by
  set S := CFC.sqrt A with hSdef
  set R := CFC.sqrt B with hRdef
  have hA0 : 0 ≤ A := hA.posSemidef.nonneg
  have hB0 : 0 ≤ B := hB.posSemidef.nonneg
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg A
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg B
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff A).mpr hA.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hinvS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSsa : S.conjTranspose = S := hS0.isSelfAdjoint
  have hRsa : R.conjTranspose = R := hR0.isSelfAdjoint
  constructor
  · intro h
    set M := CFC.sqrt (S * B * S)
    have hMsa : M.conjTranspose = M := (CFC.sqrt_nonneg _).isSelfAdjoint
    have hstar := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv, hSsa, hRsa, hMsa, ← Matrix.mul_assoc, ← h] at hstar
    -- `hstar : S⁻¹ * R = R * S⁻¹`
    have hcomm : S * R = R * S := by
      calc S * R = S * (R * S⁻¹) * S := by
            rw [Matrix.mul_assoc S, Matrix.mul_assoc R, hinvS, Matrix.mul_one]
        _ = S * (S⁻¹ * R) * S := by rw [hstar]
        _ = R * S := by rw [← Matrix.mul_assoc S, hSinv, Matrix.one_mul]
    have hSR : Commute S R := hcomm
    have hSB : Commute S B := by
      have := hSR.mul_right hSR
      rwa [hRR] at this
    have hAB : Commute A B := by
      have := hSB.mul_left hSB
      rwa [hSS] at this
    exact hAB.eq
  · intro h
    have hSB : Commute S B := commute_cfcSqrt_right (h.symm : Commute B A) |>.symm
    have hSR : Commute S R := commute_cfcSqrt_right hSB
    have hM : CFC.sqrt (S * B * S) = S * R := by
      refine CFC.sqrt_unique ?_ (hSR.mul_nonneg hS0 hR0 |> fun h ↦ ?_)
      · calc S * R * (S * R) = S * S * (R * R) := by
              rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, ← hSR.eq, Matrix.mul_assoc,
                Matrix.mul_assoc]
          _ = S * (S * B) := by rw [hRR, Matrix.mul_assoc]
          _ = S * (B * S) := by rw [hSB.eq]
          _ = S * B * S := (Matrix.mul_assoc _ _ _).symm
      · exact h
    rw [hM, ← Matrix.mul_assoc, hinvS, Matrix.one_mul]

/-- The squared `2`-Wasserstein distance between the laws of `S` and `T` under `P` is at most
the mean squared distance `∫ ‖S x - T x‖² dP`, by the coupling `(S, T)_# P`. -/
theorem wassersteinEDist_two_map_toReal_sq_le {d : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) {S T : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d)} (hS : Measurable S) (hT : Measurable T)
    (h : MemLp (fun x ↦ S x - T x) 2 P) :
    (TauCeti.wassersteinEDist 2 (P.map S) (P.map T)).toReal ^ 2 ≤ ∫ x, ‖S x - T x‖ ^ 2 ∂P := by
  have hc := TauCeti.isCoupling_map_prodMk_of_aemeasurable (γ := P) hS.aemeasurable
    hT.aemeasurable rfl rfl
  have hW := TauCeti.wassersteinEDist_le hc 2
  rw [eLpNorm_map_measure (by fun_prop) (by fun_prop)] at hW
  have he : eLpNorm ((fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      edist z.1 z.2) ∘ fun x ↦ (S x, T x)) 2 P = eLpNorm (fun x ↦ S x - T x) 2 P := by
    refine eLpNorm_congr_enorm_ae (by fun_prop) h.aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp [edist_eq_enorm_sub]
  rw [he, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hW
  have hI : 0 ≤ ∫ x, ‖S x - T x‖ ^ (2 : ℝ≥0∞).toReal ∂P :=
    integral_nonneg fun x ↦ by positivity
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hW
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
  refine hsq.trans_eq ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hI ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- Pointwise form of the descent identity: with `g = x - k⁻¹ ∑ Tᵢ`, moving `x` by `-τ g` changes
the sum of squared distances to the `Tᵢ` by `-k (2τ - τ²) ‖g‖²`. -/
theorem sum_norm_sub_smul_sub_sq {d k : ℕ} (hk : 0 < k) (x : EuclideanSpace ℝ (Fin d))
    (t : Fin k → EuclideanSpace ℝ (Fin d)) (tau : ℝ) :
    ∑ i, ‖x - tau • (x - (k : ℝ)⁻¹ • ∑ j, t j) - t i‖ ^ 2 =
      ∑ i, ‖x - t i‖ ^ 2 - k * (2 * tau - tau ^ 2) * ‖x - (k : ℝ)⁻¹ • ∑ j, t j‖ ^ 2 := by
  set g := x - (k : ℝ)⁻¹ • ∑ j, t j
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsum : ∑ i, (x - t i) = (k : ℝ) • g := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_sub, smul_smul, mul_inv_cancel₀ hk', one_smul, Nat.cast_smul_eq_nsmul]
  have hpt : ∀ i, ‖x - tau • g - t i‖ ^ 2 =
      ‖x - t i‖ ^ 2 - 2 * tau * inner ℝ (x - t i) g + tau ^ 2 * ‖g‖ ^ 2 := by
    intro i
    rw [show x - tau • g - t i = (x - t i) - tau • g by abel, norm_sub_sq_real, inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- GAPS 108.59, the energy-descent inequality for the averaged-transport update.
The finite-step inequality holds for every real step size; the usual descent interpretation
uses step sizes in `[0, 1]`. No convergence of the iteration is asserted. -/
theorem wasserstein_energy_descent_of_averaged_transport {d k : ℕ} (hk : 0 < k)
    (P : Measure (EuclideanSpace ℝ (Fin d)))  (hP2 : MemLp id 2 P)
    (T : Fin k → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ i, Measurable (T i)) (hT2 : ∀ i, MemLp (T i) 2 P)
    (hopt : ∀ i, (∫ x, ‖x - T i x‖ ^ 2 ∂P) =
      (TauCeti.wassersteinEDist 2 P (P.map (T i))).toReal ^ 2) :
    let g := fun x ↦ x - (k : ℝ)⁻¹ • ∑ i, T i x;
    let F := fun Q ↦ (∑ i, (TauCeti.wassersteinEDist 2 Q (P.map (T i))).toReal ^ 2) / (2 * k);
    ∀ (tau : ℝ),
    F (P.map (fun x ↦ x - tau • g x)) - F P ≤
      -(tau - tau ^ 2 / 2) * ∫ x, ‖g x‖ ^ 2 ∂P := by
  intro g F tau
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsumT : MemLp (fun x ↦ ∑ i, T i x) 2 P := memLp_finsetSum Finset.univ fun i _ ↦ hT2 i
  have hg2 : MemLp g 2 P := hP2.sub (hsumT.const_smul ((k : ℝ)⁻¹))
  have hgm : Measurable g := measurable_id.sub
    ((Finset.measurable_fun_sum Finset.univ fun i _ ↦ hT i).const_smul ((k : ℝ)⁻¹))
  have hSm : Measurable fun x ↦ x - tau • g x := measurable_id.sub (hgm.const_smul tau)
  have hS2 : MemLp (fun x ↦ x - tau • g x) 2 P := hP2.sub (hg2.const_smul tau)
  have hdiff : ∀ i, MemLp (fun x ↦ x - tau • g x - T i x) 2 P := fun i ↦ hS2.sub (hT2 i)
  have hdiff0 : ∀ i, MemLp (fun x ↦ x - T i x) 2 P := fun i ↦ hP2.sub (hT2 i)
  have hint : ∀ {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}, MemLp f 2 P →
      Integrable (fun x ↦ ‖f x‖ ^ 2) P := fun hf ↦ hf.integrable_norm_pow two_ne_zero
  -- each new squared distance is bounded by the cost of the coupling through `P`
  have hbound : ∀ i, (TauCeti.wassersteinEDist 2 (P.map fun x ↦ x - tau • g x)
      (P.map (T i))).toReal ^ 2 ≤ ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P :=
    fun i ↦ wassersteinEDist_two_map_toReal_sq_le P hSm (hT i) (hdiff i)
  have hnew : F (P.map fun x ↦ x - tau • g x) ≤
      (∑ i, ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P) / (2 * k) := by
    simp only [F]
    gcongr with i
    exact hbound i
  have hold : F P = (∑ i, ∫ x, ‖x - T i x‖ ^ 2 ∂P) / (2 * k) := by
    simp only [F, hopt]
  have hid : (∑ i, ∫ x, ‖x - tau • g x - T i x‖ ^ 2 ∂P) =
      (∑ i, ∫ x, ‖x - T i x‖ ^ 2 ∂P) - k * (2 * tau - tau ^ 2) * ∫ x, ‖g x‖ ^ 2 ∂P := by
    rw [← integral_finsetSum _ fun i _ ↦ hint (hdiff i),
      ← integral_finsetSum _ fun i _ ↦ hint (hdiff0 i), ← integral_const_mul,
      ← integral_sub (integrable_finsetSum _ fun i _ ↦ hint (hdiff0 i))
        ((hint hg2).const_mul _)]
    congr 1
    ext x
    exact sum_norm_sub_smul_sub_sq hk x (fun i ↦ T i x) tau
  rw [hold]
  refine (sub_le_sub_right hnew _).trans_eq ?_
  rw [hid]
  field_simp
  ring


end CKSD
