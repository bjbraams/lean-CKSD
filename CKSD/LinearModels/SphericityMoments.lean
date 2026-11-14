module
public import TauCeti.Probability.Distributions.Wishart.Transforms
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Moments.Determinacy
public import CKSD.LinearModels.WishartRatioMoments
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
/-!
# Spherical Wishart determinant-to-trace moments

The trace law follows from pinned TauCeti's Wishart matrix MGF and Gamma MGF uniqueness.
Determinant tilting and Gamma inverse moments give exact natural moments of the sphericity
ratio; Mathlib's weighted AM–GM supplies its compact support bound.
-/
@[expose] public section
noncomputable section
open Filter Set Real MeasureTheory ProbabilityTheory Matrix
open scoped Topology BigOperators ENNReal NNReal MatrixOrder
namespace CKSD

/-- The trace of a spherical Gaussian-Gram Wishart matrix has the corresponding Gamma law. -/
theorem map_trace_wishartGramMeasure_smul_one {p : ℕ} (hp : 0 < p) (ν : ℕ) (hν : 0 < ν)
    (v : ℝ) (hv : 0 < v) :
    (TauCeti.Probability.wishartGramMeasure ν (v • (1 : Matrix (Fin p) (Fin p) ℝ))).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ (A : Matrix (Fin p) (Fin p) ℝ).trace) =
        gammaMeasure ((ν : ℝ) * p / 2) (1 / (2 * v)) := by
  let E := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
  let S : Matrix (Fin p) (Fin p) ℝ := v • 1
  let θ : E := ⟨1, IsSelfAdjoint.one _⟩
  let f : E → ℝ := fun A ↦ (A : Matrix (Fin p) (Fin p) ℝ).trace
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hshape : 0 < (ν : ℝ) * p / 2 := by positivity
  have hrate : 0 < 1 / (2 * v) := by positivity
  let : IsProbabilityMeasure (gammaMeasure ((ν : ℝ) * p / 2) (1 / (2 * v))) :=
    isProbabilityMeasure_gammaMeasure hshape hrate
  have hS : S.PosSemidef := (Matrix.PosSemidef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosSemidef).smul hv.le
  have hroot : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  change (TauCeti.Probability.wishartGramMeasure ν S).map f = _
  symm
  apply TauCeti.Measure.ext_of_mgf
  · rw [TauCeti.Probability.integrableExpSet_id_gammaMeasure hshape hrate, interior_Iio]
    exact hrate
  · filter_upwards [Iio_mem_nhds hrate] with t ht
    have hcoef : 0 < 1 - 2 * t * v := by
      have := (lt_div_iff₀ (by positivity : 0 < 2 * v)).1 ht
      nlinarith
    have hmat : 1 - (2 * t) • (CFC.sqrt S * (θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S) =
        (1 - 2 * t * v) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
      dsimp only [θ]
      rw [Matrix.mul_one, hroot]
      dsimp only [S]
      rw [smul_smul]
      module
    have hpencil : (1 - (2 * t) • (CFC.sqrt S * (θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef := by
      rw [hmat]
      exact (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef).smul hcoef
    have hw := TauCeti.Probability.mgf_trace_mul_wishartGramMeasure_sqrt (Θ := θ) ν S hpencil
    have htr : (fun A : E ↦ ((θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) = f := by
      funext A
      dsimp only [θ, f]
      rw [Matrix.one_mul]
    rw [htr] at hw
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hw
    rw [← Real.rpow_natCast, ← Real.rpow_mul hcoef.le] at hw
    rw [TauCeti.Probability.mgf_id_gammaMeasure hshape hrate ht,
      mgf_map hfm.aemeasurable (by fun_prop)]
    change (1 - t / (1 / (2 * v))) ^ (-((ν : ℝ) * p / 2)) = mgf f (TauCeti.Probability.wishartGramMeasure ν S) t
    rw [hw]
    have hrdiv : t / (1 / (2 * v)) = 2 * t * v := by field_simp [hv.ne']
    rw [hrdiv]
    congr 1
    ring

/-- Matrix AM-GM bounds the determinant by the dimension-th power of the mean eigenvalue. -/
theorem det_le_trace_div_pow_of_posDef {p : ℕ} (hp : 0 < p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef) :
    A.det ≤ (A.trace / p) ^ p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let eigs := hA.isHermitian.eigenvalues
  have heigs (i : Fin p) : 0 ≤ eigs i := (hA.eigenvalues_pos i).le
  have hsum : (∑ _i : Fin p, (p : ℝ)⁻¹) = 1 := by simp [hpR.ne']
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin p))
    (fun _ ↦ (p : ℝ)⁻¹) eigs (fun _ _ ↦ inv_nonneg.2 hpR.le) hsum (fun i _ ↦ heigs i)
  rw [Real.finsetProd_rpow _ _ (fun i _ ↦ heigs i), ← Finset.mul_sum] at h
  have hdet : (∏ i, eigs i) = A.det := hA.isHermitian.det_eq_prod_eigenvalues.symm
  have htrace : (∑ i, eigs i) = A.trace := hA.isHermitian.trace_eq_sum_eigenvalues.symm
  rw [hdet, htrace] at h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hA.det_pos.le _) h p
  rw [Real.rpow_inv_natCast_pow hA.det_pos.le hp.ne'] at hpow
  simpa only [div_eq_inv_mul] using hpow

/-- The sphericity determinant ratio of a positive definite matrix lies in the unit interval. -/
theorem det_trace_ratio_mem_Ioc {p : ℕ} (hp : 0 < p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef) :
    A.det / (A.trace / p) ^ p ∈ Ioc (0 : ℝ) 1 := by
  let : Nonempty (Fin p) := Fin.pos_iff_nonempty.1 hp
  have htrace : 0 < A.trace / p := div_pos hA.trace_pos (by exact_mod_cast hp)
  exact ⟨div_pos hA.det_pos (pow_pos htrace _),
    (div_le_one (pow_pos htrace _)).2 (det_le_trace_div_pow_of_posDef hp A hA)⟩

/-- Spherical Wishart normalizers combine the two scalar scales into their product. -/
theorem wishartNormalizer_smul_one {p : ℕ} (n v : ℝ) (hv : 0 < v) :
    wishartNormalizer n (v • (1 : Matrix (Fin p) (Fin p) ℝ)) =
      (2 * v) ^ (n * p / 2) * TauCeti.multivariateGamma p (n / 2) := by
  rw [wishartNormalizer, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul hv.le, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.le]
  rw [show (p : ℝ) * (n / 2) = n * p / 2 by ring]

/-- Determinant tilting reduces sphericity moments to an inverse trace moment. -/
theorem integral_det_trace_ratio_pow_wishartGramMeasure {p e : ℕ}
    (hp : 0 < p) (he : p ≤ e) (v : ℝ) (hv : 0 < v) (k : ℕ) :
    (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      ((A : Matrix (Fin p) (Fin p) ℝ).det / ((A : Matrix (Fin p) (Fin p) ℝ).trace / p) ^ p) ^ k
        ∂TauCeti.Probability.wishartGramMeasure e (v • 1)) =
      (wishartNormalizer ((e : ℝ) + 2 * k) (v • (1 : Matrix (Fin p) (Fin p) ℝ)) /
        wishartNormalizer e (v • (1 : Matrix (Fin p) (Fin p) ℝ))) *
        (p : ℝ) ^ (p * k) * (1 / (2 * v)) ^ (p * k) *
        Real.Gamma ((e : ℝ) * p / 2) / Real.Gamma (((e + 2 * k : ℕ) : ℝ) * p / 2) := by
  let E := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
  let S : Matrix (Fin p) (Fin p) ℝ := v • 1
  let μ := TauCeti.Probability.wishartGramMeasure e S
  let μ' := TauCeti.Probability.wishartGramMeasure (e + 2 * k) S
  let C := wishartNormalizer ((e : ℝ) + 2 * k) S / wishartNormalizer e S
  let g : E → ℝ := fun A ↦ ((A : Matrix (Fin p) (Fin p) ℝ).trace ^ (p * k))⁻¹
  have hS : S.PosDef := (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef).smul hv
  have hen : (p : ℝ) - 1 < e := (sub_one_lt _).trans_le (Nat.cast_le.2 he)
  have hC : 0 ≤ C := (div_pos (wishartNormalizer_pos hS (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
    (wishartNormalizer_pos hS hen)).le
  have hweighted : (∫ A, g A ∂μ.withDensity
      (fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k))) =
      ∫ A, ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k) * g A ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k)) (by fun_prop)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g]
    apply integral_congr_ae
    filter_upwards [TauCeti.Probability.ae_posDef_wishartGramMeasure hS he] with A hA
    rw [ENNReal.toReal_ofReal (pow_nonneg hA.det_pos.le k), smul_eq_mul]
  have hratio : (∫ A : E, ((A : Matrix (Fin p) (Fin p) ℝ).det /
      ((A : Matrix (Fin p) (Fin p) ℝ).trace / p) ^ p) ^ k ∂μ) =
      (p : ℝ) ^ (p * k) * ∫ A : E, ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k) * g A ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun A ↦ by
      dsimp only [g]
      rw [div_pow, ← pow_mul, div_pow, div_div_eq_mul_div, div_eq_mul_inv]
      ring
  rw [hratio, ← hweighted]
  change _ * (∫ A, g A ∂(TauCeti.Probability.wishartGramMeasure e S).withDensity
    (fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k))) = _
  rw [withDensity_det_pow_wishartGramMeasure hS he k, integral_smul_measure,
    ENNReal.toReal_ofReal hC, smul_eq_mul]
  have he' : 0 < e + 2 * k := lt_of_lt_of_le hp (by omega)
  have htrace := map_trace_wishartGramMeasure_smul_one hp (e + 2 * k) he' v hv
  have hgintegral : (∫ A : E, g A ∂μ') =
      (1 / (2 * v)) ^ (p * k) * Real.Gamma ((e : ℝ) * p / 2) /
        Real.Gamma (((e + 2 * k : ℕ) : ℝ) * p / 2) := by
    rw [← integral_map (by fun_prop : Measurable (fun A : E ↦ (A : Matrix (Fin p) (Fin p) ℝ).trace)).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ (x ^ (p * k))⁻¹)
        ((TauCeti.Probability.wishartGramMeasure (e + 2 * k) S).map
          (fun A : E ↦ (A : Matrix (Fin p) (Fin p) ℝ).trace)))]
    rw [htrace, TauCeti.Probability.integral_inv_pow_gammaMeasure (by positivity) (p * k) (by
      have heR : (0 : ℝ) < e := by exact_mod_cast (lt_of_lt_of_le hp he)
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      push_cast
      nlinarith)]
    congr 2
    push_cast
    ring
  rw [hgintegral]
  ring

/-- The scale in a spherical determinant tilt cancels against the inverse trace-moment scale. -/
theorem wishartNormalizer_spherical_shift_ratio_mul_rate_pow {p : ℕ} (n v : ℝ)
    (hv : 0 < v) (hn : (p : ℝ) - 1 < n) (k : ℕ) :
    (wishartNormalizer (n + 2 * k) (v • (1 : Matrix (Fin p) (Fin p) ℝ)) /
      wishartNormalizer n (v • (1 : Matrix (Fin p) (Fin p) ℝ))) * (1 / (2 * v)) ^ (p * k) =
      TauCeti.multivariateGamma p (n / 2 + k) / TauCeti.multivariateGamma p (n / 2) := by
  have hbase : 0 < TauCeti.multivariateGamma p (n / 2) := TauCeti.multivariateGamma_pos (by linarith)
  have h2v : 0 < 2 * v := by positivity
  rw [wishartNormalizer_smul_one _ _ hv, wishartNormalizer_smul_one _ _ hv,
    show (n + 2 * (k : ℝ)) * p / 2 = n * p / 2 + (p * k : ℕ) by push_cast; ring,
    show (n + 2 * (k : ℝ)) / 2 = n / 2 + k by ring,
    Real.rpow_add h2v, Real.rpow_natCast, _root_.one_div_pow]
  field_simp [(Real.rpow_pos_of_pos h2v (n * p / 2)).ne', pow_ne_zero (p * k) h2v.ne', hbase.ne']

/-- Exact natural moments of the spherical Wishart sphericity ratio. -/
theorem integral_det_trace_ratio_pow_wishartGram_eq_gamma {p e : ℕ}
    (hp : 0 < p) (he : p ≤ e) (v : ℝ) (hv : 0 < v) (k : ℕ) :
    (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      ((A : Matrix (Fin p) (Fin p) ℝ).det / ((A : Matrix (Fin p) (Fin p) ℝ).trace / p) ^ p) ^ k
        ∂TauCeti.Probability.wishartGramMeasure e (v • 1)) =
      (p : ℝ) ^ (p * k) * TauCeti.multivariateGamma p ((e : ℝ) / 2 + k) *
        Real.Gamma ((p : ℝ) * ((e : ℝ) / 2)) /
        (TauCeti.multivariateGamma p ((e : ℝ) / 2) * Real.Gamma ((p : ℝ) * ((e : ℝ) / 2) + p * k)) := by
  have hen : (p : ℝ) - 1 < e := (sub_one_lt _).trans_le (Nat.cast_le.2 he)
  have hcancel := wishartNormalizer_spherical_shift_ratio_mul_rate_pow (p := p) e v hv hen k
  rw [integral_det_trace_ratio_pow_wishartGramMeasure hp he v hv k]
  have hshape : (((e + 2 * k : ℕ) : ℝ) * p / 2) = (p : ℝ) * ((e : ℝ) / 2) + p * k := by push_cast; ring
  rw [hshape, show (e : ℝ) * p / 2 = (p : ℝ) * ((e : ℝ) / 2) by ring]
  calc _ = (p : ℝ) ^ (p * k) *
      ((wishartNormalizer ((e : ℝ) + 2 * k) (v • (1 : Matrix (Fin p) (Fin p) ℝ)) /
        wishartNormalizer e (v • (1 : Matrix (Fin p) (Fin p) ℝ))) * (1 / (2 * v)) ^ (p * k)) *
          Real.Gamma ((p : ℝ) * ((e : ℝ) / 2)) / Real.Gamma ((p : ℝ) * ((e : ℝ) / 2) + p * k) := by ring
    _ = _ := by rw [hcancel]; ring

end CKSD
