module
public import CKSD.LinearModels.WishartRatioMoments
/-!
# Gamma factors for block Wishart determinant ratios

A determinant tilt shifts the full Wishart degree by twice the natural moment order. The
normalizers and the two inverse block-determinant moments then reduce to a shifted Wilks Gamma
quotient. This follows the density-tilt calculation in Muirhead, *Aspects of Multivariate
Statistical Theory*, Theorem 11.2.3, printed page 532 (PDF page 558 of the local 2005 copy).

Pinned TauCeti supplies dimension splitting of the multivariate Gamma function and positivity;
Mathlib supplies real-power identities. The Wishart normalizer is imported locally.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
namespace CKSD
/-- The Gamma quotient for a block determinant ratio reduces to a shifted Wilks quotient. -/
theorem multivariateGamma_block_ratio {p q : ℕ} {a : ℝ}
    (ha : ((p+q:ℕ):ℝ)-1 < 2*a) (k : ℕ) :
    TauCeti.multivariateGamma (p+q) (a+k) * TauCeti.multivariateGamma p a * TauCeti.multivariateGamma q a /
      (TauCeti.multivariateGamma (p+q) a * TauCeti.multivariateGamma p (a+k) * TauCeti.multivariateGamma q (a+k)) =
      TauCeti.multivariateGamma p (a-q/2+k) * TauCeti.multivariateGamma p a /
        (TauCeti.multivariateGamma p (a-q/2) * TauCeti.multivariateGamma p (a+k)) := by
  have hq : ((q:ℝ)-1)/2 < a := by
    push_cast at ha
    have := Nat.cast_nonneg (α := ℝ) p
    linarith
  have hqk : ((q:ℝ)-1)/2 < a+k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [show p+q=q+p by omega, TauCeti.multivariateGamma_add, TauCeti.multivariateGamma_add,
    show a+(k:ℝ)-(q:ℝ)/2 = a-q/2+k by ring]
  field_simp [(Real.rpow_pos_of_pos Real.pi_pos ((q:ℝ)*p/2)).ne',
    (TauCeti.multivariateGamma_pos hq).ne', (TauCeti.multivariateGamma_pos hqk).ne']
/-- The determinant tilt normalizer separates into its scalar, scale and Gamma factors. -/
theorem wishartNormalizer_shift_ratio {p : ℕ} (n : ℝ) (k : ℕ)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hn : (p:ℝ)-1 < n) :
    wishartNormalizer (n+2*k) S / wishartNormalizer n S =
      2^((p:ℝ)*k) * S.det^k *
        (TauCeti.multivariateGamma p (n/2+k) / TauCeti.multivariateGamma p (n/2)) := by
  unfold wishartNormalizer
  rw [show (n+2*(k:ℝ))*(p:ℝ)/2 = n*(p:ℝ)/2+(p:ℝ)*k by ring,
    show (n+2*(k:ℝ))/2 = n/2+k by ring, Real.rpow_add two_pos,
    Real.rpow_add hS.det_pos, Real.rpow_natCast]
  field_simp [(Real.rpow_pos_of_pos two_pos (n*p/2)).ne',
    (Real.rpow_pos_of_pos hS.det_pos (n/2)).ne',
    (TauCeti.multivariateGamma_pos (show ((p:ℝ)-1)/2<n/2 by linarith)).ne']
/-- Block-diagonal scale factors cancel against the shifted inverse determinant moments. -/
theorem wishartNormalizer_block_ratio_mul_negative_moments {p q : ℕ}
    (n : ℝ) (k : ℕ) {S : Matrix (Fin (p+q)) (Fin (p+q)) ℝ}
    {A : Matrix (Fin p) (Fin p) ℝ} {B : Matrix (Fin q) (Fin q) ℝ}
    (hS : S.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hdet : S.det = A.det*B.det) (hn : ((p+q:ℕ):ℝ)-1 < n) :
    (wishartNormalizer (n+2*k) S / wishartNormalizer n S) *
      (2^((p:ℝ)*(-(k:ℝ))) * A.det^(-(k:ℝ)) * TauCeti.multivariateGamma p (n/2) /
        TauCeti.multivariateGamma p (n/2+k)) *
      (2^((q:ℝ)*(-(k:ℝ))) * B.det^(-(k:ℝ)) * TauCeti.multivariateGamma q (n/2) /
        TauCeti.multivariateGamma q (n/2+k)) =
      TauCeti.multivariateGamma p (n/2-q/2+k) * TauCeti.multivariateGamma p (n/2) /
        (TauCeti.multivariateGamma p (n/2-q/2) * TauCeti.multivariateGamma p (n/2+k)) := by
  rw [wishartNormalizer_shift_ratio n k hS hn, hdet]
  have hp : ((p:ℝ)-1)/2 < n/2+k := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) k]
  have hq : ((q:ℝ)-1)/2 < n/2+k := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) k]
  rw [show (((p+q:ℕ):ℝ)*(k:ℝ)) = (p:ℝ)*k+(q:ℝ)*k by push_cast; ring,
    Real.rpow_add two_pos, mul_pow, mul_neg, mul_neg,
    Real.rpow_neg two_pos.le, Real.rpow_neg two_pos.le,
    Real.rpow_neg hA.det_pos.le, Real.rpow_neg hB.det_pos.le,
    Real.rpow_natCast, Real.rpow_natCast]
  have heq := multivariateGamma_block_ratio (p := p) (q := q)
    (a := n/2) (by linarith) k
  convert heq using 1
  field_simp [(Real.rpow_pos_of_pos two_pos ((p:ℝ)*k)).ne',
    (Real.rpow_pos_of_pos two_pos ((q:ℝ)*k)).ne',
    pow_ne_zero k hA.det_pos.ne', pow_ne_zero k hB.det_pos.ne',
    (TauCeti.multivariateGamma_pos hp).ne', (TauCeti.multivariateGamma_pos hq).ne',
    (TauCeti.multivariateGamma_pos (show (((p+q:ℕ):ℝ)-1)/2<n/2 by linarith)).ne']
end CKSD
