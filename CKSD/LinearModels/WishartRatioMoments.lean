module

public import CKSD.LinearModels.WishartTilt
public import TauCeti.Analysis.Matrix.PosSemidef.Determinant
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.Probability.Distributions.Beta.Basic
public import Mathlib.MeasureTheory.Integral.Pi
/-!
# Moments of a Wishart determinant ratio

A natural determinant tilt changes the first Wishart degree from `e` to `e+2k`.
Convolution with the second Wishart law and a negative determinant moment then give the
ratio's natural moments. These agree with the moments of the corresponding independent
Beta product, including the singular second-Wishart regime and zero-dimensional matrices.

Pinned TauCeti supplies Wishart density agreement, convolution, determinant moments, Beta
moments, and multivariate Gamma identities. The determinant-tilt calculation is local.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
namespace CKSD
/-- A natural determinant tilt of a nonsingular Gaussian-Gram Wishart law. -/
theorem with_density_det_pow_wishart_gram_measure {p e : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (he : p ≤ e) (k : ℕ) :
    (TauCeti.Probability.wishartGramMeasure e S).withDensity
      (fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k)) =
      ENNReal.ofReal (wishartNormalizer ((e:ℝ)+2*k) S / wishartNormalizer e S) •
        TauCeti.Probability.wishartGramMeasure (e+2*k) S := by
  rw [TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS he,
    with_density_det_pow_nonsingular_wishart_measure hS ((sub_one_lt _).trans_le (Nat.cast_le.2 he)),
    TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS (by omega : p ≤ e+2*k)]
  push_cast
  rfl

/-- Determinant-ratio moments reduce to one shifted Wishart determinant moment. -/
theorem integral_det_ratio_pow_wishart_gram_prod {p e : ℕ}
    (h : ℕ) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (he : p ≤ e) (k : ℕ) :
    (∫ z, ((z.1 : Matrix (Fin p) (Fin p) ℝ).det /
      ((z.1 + z.2 : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : Matrix (Fin p) (Fin p) ℝ).det) ^ k
      ∂(TauCeti.Probability.wishartGramMeasure e S).prod
        (TauCeti.Probability.wishartGramMeasure h S)) =
      (wishartNormalizer ((e:ℝ)+2*k) S / wishartNormalizer e S) *
        ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ))
          ∂TauCeti.Probability.wishartGramMeasure (e+2*k+h) S := by
  let E := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
  let μ := TauCeti.Probability.wishartGramMeasure e S
  let ν := TauCeti.Probability.wishartGramMeasure h S
  let μ' := TauCeti.Probability.wishartGramMeasure (e+2*k) S
  let C := wishartNormalizer ((e:ℝ)+2*k) S / wishartNormalizer e S
  let f : E → ℝ≥0∞ := fun A ↦ ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ k)
  let g : E × E → ℝ := fun z ↦ ((z.1+z.2 : E) : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hweight : (μ.prod ν).withDensity (fun z ↦ f z.1) = ENNReal.ofReal C • (μ'.prod ν) := by
    rw [← prod_withDensity_left hf]
    change ((TauCeti.Probability.wishartGramMeasure e S).withDensity f).prod ν = _
    rw [with_density_det_pow_wishart_gram_measure hS he k, Measure.prod_smul_left]
  have hpos : ∀ᵐ z : E × E ∂μ.prod ν, (z.1 : Matrix (Fin p) (Fin p) ℝ).PosDef := by
    apply (Measure.ae_prod_iff_ae_ae
      (TauCeti.measurableSet_setOfPred_posDef.preimage (measurable_subtype_coe.comp measurable_fst))).2
    filter_upwards [TauCeti.Probability.ae_posDef_wishartGramMeasure hS he] with A hA
    exact ae_of_all _ fun _ ↦ hA
  have hweighted : (∫ z, g z ∂(μ.prod ν).withDensity (fun z ↦ f z.1)) =
      ∫ z, ((z.1 : Matrix (Fin p) (Fin p) ℝ).det / ((z.1+z.2 : E) : Matrix (Fin p) (Fin p) ℝ).det)^k
        ∂μ.prod ν := by
    rw [integral_withDensity_eq_integral_toReal_smul (μ := μ.prod ν)
      (f := fun z : E × E ↦ f z.1) (hf.comp measurable_fst)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g]
    apply integral_congr_ae
    filter_upwards [hpos] with z hz
    dsimp [f, g]
    rw [ENNReal.toReal_ofReal (pow_nonneg hz.det_pos.le k),
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv]
  have heR : (p:ℝ) ≤ e := Nat.cast_le.2 he
  have hen : (p:ℝ)-1 < e := by linarith
  have henk : (p:ℝ)-1 < (e:ℝ)+2*k := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hC : 0 ≤ C := (div_pos (wishart_normalizer_pos hS henk) (wishart_normalizer_pos hS hen)).le
  rw [← hweighted, hweight, integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]
  congr 1
  have hsum : (μ'.prod ν).map (fun z : E × E ↦ z.1+z.2) =
      TauCeti.Probability.wishartGramMeasure (e+2*k+h) S := by
    exact TauCeti.Probability.wishartGramMeasure_conv_wishartGramMeasure (e+2*k) h S
  have hm : Measurable (fun A : E ↦ (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ))) := by
    have hd : Measurable (fun A : E ↦ (A : Matrix (Fin p) (Fin p) ℝ).det) := by fun_prop
    simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, Function.comp_def] using
      (measurable_inv.comp (hd.pow_const k))
  rw [← hsum, integral_map (by fun_prop) hm.aestronglyMeasurable]

/-- Wishart normalizers cancel against the shifted negative determinant moment. -/
theorem wishart_normalizer_ratio_mul_negative_moment {p : ℕ}
    (n m : ℝ) (k : ℕ) {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hn : (p:ℝ)-1 < n) (hm : (p:ℝ)-1 < m) :
    (wishartNormalizer (n+2*k) S / wishartNormalizer n S) *
      (2 ^ ((p:ℝ) * (-(k:ℝ))) * S.det ^ (-(k:ℝ)) *
        TauCeti.multivariateGamma p (m/2) / TauCeti.multivariateGamma p (m/2+k)) =
      TauCeti.multivariateGamma p (n/2+k) * TauCeti.multivariateGamma p (m/2) /
        (TauCeti.multivariateGamma p (n/2) * TauCeti.multivariateGamma p (m/2+k)) := by
  have hkn : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hG₀ : 0 < TauCeti.multivariateGamma p (n/2) := TauCeti.multivariateGamma_pos (by linarith)
  have hG₁ : 0 < TauCeti.multivariateGamma p (m/2+k) := TauCeti.multivariateGamma_pos (by linarith)
  unfold wishartNormalizer
  rw [show (n+2*(k:ℝ))*(p:ℝ)/2 = n*(p:ℝ)/2+(p:ℝ)*k by ring,
    show (n+2*(k:ℝ))/2 = n/2+k by ring,
    Real.rpow_add two_pos, Real.rpow_add hS.det_pos, Real.rpow_natCast,
    mul_neg, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg hS.det_pos.le, Real.rpow_natCast]
  field_simp [(Real.rpow_pos_of_pos two_pos (n*(p:ℝ)/2)).ne',
    (Real.rpow_pos_of_pos two_pos ((p:ℝ)*k)).ne',
    (Real.rpow_pos_of_pos hS.det_pos (n/2)).ne', pow_ne_zero k hS.det_pos.ne', hG₀.ne', hG₁.ne']

/-- The natural moments of a Wishart determinant ratio are a quotient of multivariate Gamma values. -/
theorem integral_det_ratio_pow_wishart_gram_prod_eq_gamma {p e h : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (he : p ≤ e) (k : ℕ) :
    (∫ z, ((z.1 : Matrix (Fin p) (Fin p) ℝ).det /
      ((z.1 + z.2 : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : Matrix (Fin p) (Fin p) ℝ).det) ^ k
      ∂(TauCeti.Probability.wishartGramMeasure e S).prod
        (TauCeti.Probability.wishartGramMeasure h S)) =
      TauCeti.multivariateGamma p ((e:ℝ)/2+k) * TauCeti.multivariateGamma p (((e:ℝ)+h)/2) /
        (TauCeti.multivariateGamma p ((e:ℝ)/2) * TauCeti.multivariateGamma p (((e:ℝ)+h)/2+k)) := by
  have hen : (p:ℝ)-1 < e := (sub_one_lt _).trans_le (Nat.cast_le.2 he)
  have hmn : (p:ℝ)-1 < (e:ℝ)+h := by linarith [(Nat.cast_nonneg h : (0:ℝ)≤h)]
  have hsum : (p:ℝ)-1 < (e+2*k+h:ℕ) := by
    push_cast
    linarith [(Nat.cast_nonneg h : (0:ℝ)≤h), (Nat.cast_nonneg k : (0:ℝ)≤k)]
  have hq : -((((e+2*k+h:ℕ):ℝ)-(p:ℝ)+1)/2) < -(k:ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg h : (0:ℝ)≤h)]
  rw [integral_det_ratio_pow_wishart_gram_prod h hS he,
    TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS (by omega : p ≤ e+2*k+h),
    TauCeti.Probability.integral_rpow_det_nonsingularWishartMeasure hS hsum hq]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [show ((e:ℝ)+2*k+h)/2+ -(k:ℝ) = ((e:ℝ)+h)/2 by ring,
    show ((e:ℝ)+2*k+h)/2 = ((e:ℝ)+h)/2+k by ring]
  exact wishart_normalizer_ratio_mul_negative_moment e ((e:ℝ)+h) k hS hen hmn

/-- The moments of the independent Beta product agree with the Wishart ratio moments. -/
theorem integral_beta_product_pow_eq_gamma {p e h : ℕ} (he : p ≤ e) (hh : 0 < h) (k : ℕ) :
    (∫ v : Fin p → ℝ, (∏ i, v i)^k ∂Measure.pi (fun i : Fin p ↦
      betaMeasure (((e:ℝ)-i.val)/2) ((h:ℝ)/2))) =
      TauCeti.multivariateGamma p ((e:ℝ)/2+k) * TauCeti.multivariateGamma p (((e:ℝ)+h)/2) /
        (TauCeti.multivariateGamma p ((e:ℝ)/2) * TauCeti.multivariateGamma p (((e:ℝ)+h)/2+k)) := by
  have ha (i : Fin p) : 0 < ((e:ℝ)-i.val)/2 := by
    have hi : (i.val:ℝ) < e := by exact_mod_cast (lt_of_lt_of_le i.isLt he)
    linarith
  have hb : 0 < (h:ℝ)/2 := by positivity
  have hfun : (fun v : Fin p → ℝ ↦ (∏ i, v i)^k) = fun v ↦ ∏ i, (v i)^k :=
    funext fun _ ↦ (Finset.prod_pow _ _ _).symm
  let _ (i : Fin p) : IsProbabilityMeasure (betaMeasure (((e:ℝ)-i.val)/2) ((h:ℝ)/2)) :=
    isProbabilityMeasureBeta (ha i) hb
  rw [hfun, integral_fintype_prod_eq_prod (fun (_ : Fin p) (x : ℝ) ↦ x ^ k)]
  simp_rw [TauCeti.Probability.integral_pow_betaMeasure (ha _) hb]
  have hquot (a b c d : ℝ) : a*b/(c*d) = (a/c)*(b/d) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hquot, TauCeti.multivariateGamma_div_multivariateGamma,
    TauCeti.multivariateGamma_div_multivariateGamma, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [show ((e:ℝ)-(i.val:ℝ))/2+(k:ℝ) = (e:ℝ)/2+k-(i.val:ℝ)/2 by ring,
    show ((e:ℝ)-(i.val:ℝ))/2+(h:ℝ)/2 = ((e:ℝ)+h)/2-(i.val:ℝ)/2 by ring,
    show ((e:ℝ)-(i.val:ℝ))/2 = (e:ℝ)/2-(i.val:ℝ)/2 by ring,
    show ((e:ℝ)+h)/2-(i.val:ℝ)/2+(k:ℝ) = ((e:ℝ)+h)/2+k-(i.val:ℝ)/2 by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
end CKSD
