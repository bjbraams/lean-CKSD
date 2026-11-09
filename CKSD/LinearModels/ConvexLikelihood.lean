module

public import CKSD.Asymptotics.ConvexRegression.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import TauCeti.Probability.Distributions.Gaussian.Projection

/-!
# Convex likelihood values and constrained deviance limits

Pointwise convergence of convex likelihood processes gives uniform convergence on norm balls.
At random minimizers, tightness then turns this into convergence of minimum values. After
whitening the information matrix, the difference between unrestricted and subspace-constrained
minima is asymptotically the squared norm of an orthogonal Gaussian projection.

The convexity argument uses `CKSD.Asymptotics.ConvexArgmin.Basic`. The chi-squared projection
law is TauCeti's `Submodule.map_norm_sq_starProjection_stdGaussian`; whitening uses Mathlib's
positive definite matrices and continuous functional calculus.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- Uniform convergence in probability on every norm ball may be evaluated at random points
whose norms are bounded in probability. -/
theorem tendstoInMeasure_eval_of_uniform_on_balls (P : Measure Ω) [IsFiniteMeasure P]
    (g : ℕ → Ω → E → ℝ) (q : E → ℝ)
    (hu : ∀ R ε : ℝ, 0 < ε → Tendsto
      (fun n ↦ P {w | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n w h - q h|}) atTop (𝓝 0))
    (α : ℕ → Ω → E)
    (htight : ∀ η > (0 : ℝ≥0∞), ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < ‖α n w‖} ≤ η) :
    TendstoInMeasure P (fun n w ↦ g n w (α n w) - q (α n w)) atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨R,hR⟩ := htight (η/2) (ENNReal.half_pos hη.ne')
  have hU := ENNReal.tendsto_nhds_zero.1 (hu R ε hε) (η/2) (ENNReal.half_pos hη.ne')
  filter_upwards [hR,hU] with n hn hUn
  have hsub : {w | ε ≤ ‖g n w (α n w)-q (α n w)-0‖} ⊆
      {w | R < ‖α n w‖} ∪ {w | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n w h-q h|} := by
    intro w hw
    simp only [mem_ofPred_eq,mem_union] at *
    by_cases h : R < ‖α n w‖
    · exact Or.inl h
    · exact Or.inr ⟨α n w,not_lt.1 h,by simpa [Real.norm_eq_abs] using hw⟩
  calc P {w | ε ≤ ‖g n w (α n w)-q (α n w)-0‖}
      ≤ P ({w | R < ‖α n w‖} ∪ {w | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n w h-q h|}) := measure_mono hsub
    _ ≤ P {w | R < ‖α n w‖} + P {w | ∃ h, ‖h‖ ≤ R ∧ ε ≤ |g n w h-q h|} := measure_union_le _ _
    _ ≤ η/2+η/2 := add_le_add hn hUn
    _ = η := ENNReal.add_halves η

end CKSD

namespace CKSD

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For random convex functions with identity quadratic limit and tight random linear score,
their minimum values are asymptotically minus one half of the squared score norm. -/
theorem tendstoInMeasure_convex_minValue (P : Measure Ω) [IsFiniteMeasure P]
    (Z : ℕ → Ω → E → ℝ) (hZ : ∀ n w, ConvexOn ℝ univ (Z n w)) (U : ℕ → Ω → E)
    (hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {w | ε ≤ |Z n w h + ⟪U n w,h⟫ - ‖h‖^2/2|}) atTop (𝓝 0))
    (htight : ∀ η > (0 : ℝ≥0∞), ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < ‖U n w‖} ≤ η)
    (α : ℕ → Ω → E) (hmin : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h, Z n w (α n w) ≤ Z n w h) :
    TendstoInMeasure P (fun n w ↦ Z n w (α n w) + ‖U n w‖^2/2) atTop (fun _ ↦ 0) := by
  have hδ : TendstoInMeasure P (fun n w ↦ α n w-U n w) atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_sub_of_convexOn_of_isMinOn Z hZ U
      (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) (fun _ ↦ rfl)
      (fun _ _ ↦ rfl) (c := 1) (by norm_num)
    · intro h
      simp only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,one_mul]
      exact le_rfl
    · simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using hpt
    · exact htight
    · exact hmin
  have htightα : ∀ η > (0 : ℝ≥0∞), ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < ‖α n w‖} ≤ η := by
    intro η hη
    obtain ⟨R,hR⟩ := htight (η/2) (ENNReal.half_pos hη.ne')
    have hD := (tendstoInMeasure_iff_norm.1 hδ) 1 one_pos
    have hD' := ENNReal.tendsto_nhds_zero.1 hD (η/2) (ENNReal.half_pos hη.ne')
    refine ⟨|R|+1,?_⟩
    filter_upwards [hR,hD'] with n hn hDn
    have hsub : {w | |R|+1 < ‖α n w‖} ⊆
        {w | R < ‖U n w‖} ∪ {w | 1 ≤ ‖α n w-U n w-0‖} := by
      intro w hw
      simp only [mem_union,mem_ofPred_eq,sub_zero] at *
      by_cases h : R < ‖U n w‖
      · exact Or.inl h
      · right
        have hnorm' : ‖α n w‖ ≤ ‖α n w-U n w‖ + ‖U n w‖ := by
          calc ‖α n w‖ = ‖(α n w-U n w)+U n w‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith [not_lt.1 h,le_abs_self R]
    calc P {w | |R|+1 < ‖α n w‖}
        ≤ P ({w | R < ‖U n w‖} ∪ {w | 1 ≤ ‖α n w-U n w-0‖}) := measure_mono hsub
      _ ≤ P {w | R < ‖U n w‖}+P {w | 1 ≤ ‖α n w-U n w-0‖} := measure_union_le _ _
      _ ≤ η/2+η/2 := add_le_add hn hDn
      _ = η := ENNReal.add_halves η
  have hcon (n) (w) : ConvexOn ℝ univ (fun h ↦ Z n w h+⟪U n w,h⟫) :=
    (hZ n w).add (((innerSL ℝ (U n w)) : E →ₗ[ℝ] ℝ).convexOn convex_univ)
  have hu := tendsto_measure_exists_abs_sub_of_convexOn
    (fun n w h ↦ Z n w h+⟪U n w,h⟫) hcon
    (by fun_prop : Continuous (fun h : E ↦ ‖h‖^2/2)) hpt
  have heval := tendstoInMeasure_eval_of_uniform_on_balls P
    (fun n w h ↦ Z n w h+⟪U n w,h⟫) (fun h ↦ ‖h‖^2/2)
    (fun R ε hε ↦ hu R hε) α htightα
  have hnδ : TendstoInMeasure P (fun n w ↦ ‖α n w-U n w‖) atTop (fun _ ↦ (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_norm] at hδ ⊢
    simpa only [sub_zero,norm_norm] using hδ
  have hsδ := tendstoInMeasure_comp_of_continuousAt P (fun n w ↦ ‖α n w-U n w‖) 0
    (fun r ↦ r^2/2) (by fun_prop) hnδ
  simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div] at hsδ
  have hsum := tendstoInMeasure_add_zero P _ _ heval hsδ
  refine hsum.congr (fun n ↦ ae_of_all _ fun w ↦ ?_) EventuallyEq.rfl
  have hnorm := norm_sub_sq_real (α n w) (U n w)
  rw [real_inner_comm] at hnorm
  dsimp only
  linarith

end CKSD

namespace CKSD

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A convex likelihood process with an identity quadratic approximation and asymptotically
standard Gaussian score has chi-squared deviance between its full and subspace-constrained
minima, with degrees of freedom equal to the codimension of the subspace. -/
theorem tendstoInDistribution_convex_deviance (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → E → ℝ) (hZ : ∀ n w, ConvexOn ℝ univ (Z n w))
    (U : ℕ → Ω → E) (hUm : ∀ n, Measurable (U n))
    (hclt : TendstoInDistribution U atTop id (fun _ ↦ P) (stdGaussian E))
    (hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      P {w | ε ≤ |Z n w h + ⟪U n w,h⟫ - ‖h‖^2/2|}) atTop (𝓝 0))
    (K : Submodule ℝ E) (α : ℕ → Ω → E) (β : ℕ → Ω → K)
    (hminα : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h, Z n w (α n w) ≤ Z n w h)
    (hminβ : ∀ᶠ n in atTop, ∀ᵐ w ∂P, ∀ h : K, Z n w (β n w) ≤ Z n w h)
    (D : ℕ → Ω → ℝ) (hDm : ∀ n, Measurable (D n))
    (hD : ∀ n, D n =ᵐ[P] fun w ↦ -2 * (Z n w (α n w)-Z n w (β n w))) :
    TendstoInDistribution D atTop id (fun _ ↦ P)
      (TauCeti.Probability.chiSquaredMeasure (Module.finrank ℝ Kᗮ)) := by
  have htight : ∀ η > (0 : ℝ≥0∞), ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < ‖U n w‖} ≤ η := by
    intro η hη
    rcases eq_or_ne η ⊤ with rfl | hηt
    · exact ⟨0,Eventually.of_forall fun _ ↦ le_top⟩
    obtain ⟨R,-,hR⟩ := exists_measureReal_lt_norm_le_of_tendstoInDistribution P U hclt
      (ENNReal.toReal_pos hη.ne' hηt)
    refine ⟨R,hR.mono fun n hn ↦ ?_⟩
    rw [← ofReal_measureReal]
    exact (ENNReal.ofReal_le_iff_le_toReal hηt).2 hn
  have hvalα := tendstoInMeasure_convex_minValue P Z hZ U hpt htight α hminα
  let ZK : ℕ → Ω → K → ℝ := fun n w h ↦ Z n w h
  let UK : ℕ → Ω → K := fun n w ↦ K.orthogonalProjectionOnto (U n w)
  have hZK : ∀ n w, ConvexOn ℝ univ (ZK n w) := fun n w ↦ by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    exact (hZ n w).2 (mem_univ (x : E)) (mem_univ (y : E)) ha hb hab
  have hptK : ∀ h : K, ∀ ε > 0, Tendsto (fun n ↦
      P {w | ε ≤ |ZK n w h+⟪UK n w,h⟫-‖h‖^2/2|}) atTop (𝓝 0) := by
    intro h ε hε
    simpa only [ZK,UK,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,Submodule.norm_coe]
      using hpt h ε hε
  have htightK : ∀ η > (0 : ℝ≥0∞), ∃ R : ℝ, ∀ᶠ n in atTop, P {w | R < ‖UK n w‖} ≤ η := by
    intro η hη
    obtain ⟨R,hR⟩ := htight η hη
    refine ⟨R,hR.mono fun n hn ↦ (measure_mono fun w hw ↦ ?_).trans hn⟩
    exact lt_of_lt_of_le hw (K.norm_orthogonalProjectionOnto_apply_le _)
  have hvalβ := tendstoInMeasure_convex_minValue P ZK hZK UK hptK htightK β hminβ
  have herr := tendstoInMeasure_add_zero P _ _
    (tendstoInMeasure_const_mul_zero P _ (-2) hvalα)
    (tendstoInMeasure_const_mul_zero P _ 2 hvalβ)
  let W : ℕ → Ω → ℝ := fun n w ↦ ‖Kᗮ.starProjection (U n w)‖^2
  have herr' : TendstoInMeasure P (fun n w ↦ D n w-W n w) atTop (fun _ ↦ 0) := by
    refine herr.congr (fun n ↦ (hD n).mono fun w hw ↦ ?_) EventuallyEq.rfl
    have hnorm := Submodule.norm_sq_eq_add_norm_sq_projection (U n w) K
    simp only [W,ZK,UK,Submodule.starProjection_apply,Submodule.norm_coe,hw]
    linarith
  have hW : TendstoInDistribution W atTop id (fun _ ↦ P)
      (TauCeti.Probability.chiSquaredMeasure (Module.finrank ℝ Kᗮ)) := by
    refine tendstoInDistribution_of_map_eq
      (hclt.continuous_comp (g := fun x : E ↦ ‖Kᗮ.starProjection x‖^2) (by fun_prop))
      aemeasurable_id ?_
    simpa only [Function.comp_id,Measure.map_id] using Kᗮ.map_norm_sq_starProjection_stdGaussian.symm
  exact tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable P W D
    (fun n ↦ by have := hUm n; fun_prop) hDm hW herr'

end CKSD

namespace CKSD

/-- A positive definite information matrix and positive dispersion admit an invertible
linear whitening change of coordinates, with the corresponding score and quadratic identities. -/
theorem exists_glm_whitening {p : ℕ} {J : Matrix (Fin p) (Fin p) ℝ} (hJ : J.PosDef) {φ : ℝ} (hφ : 0 < φ) :
    let S := CFC.sqrt J⁻¹
    ∃ F : EuclideanSpace ℝ (Fin p) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin p),
      (∀ z, F z = Real.sqrt φ • S.toEuclideanLin z) ∧
      (∀ u z, ⟪u,F z⟫/φ = ⟪(Real.sqrt φ)⁻¹ • S.toEuclideanLin u,z⟫) ∧
      ∀ z, ⟪F z,J.toEuclideanLin (F z)⟫/φ = ‖z‖^2 := by
  intro S
  have hJ0 : 0 ≤ J⁻¹ := Matrix.nonneg_iff_posSemidef.2 hJ.inv.posSemidef
  have hSS : S*S=J⁻¹ := CFC.sqrt_mul_sqrt_self J⁻¹ hJ0
  have hS0 : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg J⁻¹)
  have hsym : LinearMap.IsSymmetric S.toEuclideanLin :=
    Matrix.isSymmetric_toEuclideanLin_iff.2 hS0.isHermitian
  have hSdet : IsUnit S.det := by
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hJ.inv.isUnit
    rw [← hSS, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left hd
  have hSJS : S*J*S=1 := by
    have hj : J=(S*S)⁻¹ := by rw [hSS,Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJ.isUnit)]
    rw [hj,Matrix.mul_inv_rev,← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hSdet,
      Matrix.one_mul,Matrix.nonsing_inv_mul _ hSdet]
  have hsφ : Real.sqrt φ ≠ 0 := Real.sqrt_ne_zero'.2 hφ
  have hMdet : IsUnit ((Real.sqrt φ) • S).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hsφ)).mul hSdet
  let F := Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
    ((Real.sqrt φ) • S) hMdet
  have hF (z) : F z = Real.sqrt φ • S.toEuclideanLin z := by
    change (Matrix.toLin (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin p) ℝ).toBasis ((Real.sqrt φ) • S)) z = _
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
    simp only [map_smul,LinearMap.smul_apply]
  refine ⟨F,hF,?_,?_⟩
  · intro u z
    rw [hF,real_inner_smul_right,real_inner_smul_left,hsym u z]
    have hs2 : (Real.sqrt φ)^2=φ := Real.sq_sqrt hφ.le
    field_simp
    rw [hs2]
    ring
  · intro z
    rw [hF,map_smul,real_inner_smul_left,real_inner_smul_right,hsym z]
    have he : S.toEuclideanLin (J.toEuclideanLin (S.toEuclideanLin z)) = z := by
      change ((Matrix.toLpLinAlgEquiv 2 S * Matrix.toLpLinAlgEquiv 2 J *
        Matrix.toLpLinAlgEquiv 2 S) z) = z
      rw [← map_mul,← map_mul,hSJS,map_one]
      rfl
    rw [he,real_inner_self_eq_norm_sq]
    have hs2 : (Real.sqrt φ)^2=φ := Real.sq_sqrt hφ.le
    rw [← mul_assoc,← pow_two,hs2,mul_div_cancel_left₀ _ hφ.ne']

end CKSD
