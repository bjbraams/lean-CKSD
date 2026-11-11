module
public import CKSD.LinearModels.BlockIndependenceBasic
public import CKSD.LinearModels.BlockWishartGamma
/-!
# Moments of the block-independence determinant ratio

Weighting the full Wishart density by a natural determinant power shifts its degree by twice
the moment order. The shifted diagonal blocks are independent Wishart matrices, so their
inverse determinant moments factor. Scale and Gamma cancellation gives the same moments as
the corresponding independent Beta product.

This follows Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 11.2.3, printed
page 532 (PDF page 558 of the local 2005 copy). The proof uses the local Wishart determinant
tilt and independent-block law, and pinned TauCeti's real-power determinant moments.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology MatrixOrder BigOperators
namespace CKSD
/-- A block-ratio moment is a product of inverse block moments after a determinant tilt. -/
theorem integral_blockIndependenceRatio_pow_wishartGramMeasure
    {p q ν : ℕ} {S : Matrix (Fin (p+q)) (Fin (p+q)) ℝ}
    (hS : S.PosDef) (hν : p+q ≤ ν)
    (hblock : S.submatrix (Fin.castAdd q) (Fin.natAdd p) = 0) (k : ℕ) :
    (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin (p+q)) (Fin (p+q)) ℝ),
      blockIndependenceRatio A.val ^ k ∂TauCeti.Probability.wishartGramMeasure ν S) =
      (wishartNormalizer ((ν:ℝ)+2*k) S / wishartNormalizer ν S) *
        (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ))
          ∂TauCeti.Probability.wishartGramMeasure (ν+2*k) (S.submatrix (Fin.castAdd q) (Fin.castAdd q))) *
        (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ),
          (A : Matrix (Fin q) (Fin q) ℝ).det ^ (-(k:ℝ))
          ∂TauCeti.Probability.wishartGramMeasure (ν+2*k) (S.submatrix (Fin.natAdd p) (Fin.natAdd p))) := by
  let E := selfAdjoint.submodule ℝ (Matrix (Fin (p+q)) (Fin (p+q)) ℝ)
  let μ := TauCeti.Probability.wishartGramMeasure ν S
  let μ' := TauCeti.Probability.wishartGramMeasure (ν+2*k) S
  let C := wishartNormalizer ((ν:ℝ)+2*k) S / wishartNormalizer ν S
  let f : E → ℝ≥0∞ := fun A ↦ ENNReal.ofReal ((A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ).det ^ k)
  let g : E → ℝ := fun A ↦
    ((A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ).submatrix (Fin.castAdd q) (Fin.castAdd q)).det ^ (-(k:ℝ)) *
    ((A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ).submatrix (Fin.natAdd p) (Fin.natAdd p)).det ^ (-(k:ℝ))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hweight : μ.withDensity f = ENNReal.ofReal C • μ' :=
    withDensity_det_pow_wishartGramMeasure hS hν k
  have hweighted : (∫ A, g A ∂μ.withDensity f) =
      ∫ A, blockIndependenceRatio (A : Matrix (Fin (p+q)) (Fin (p+q)) ℝ)^k ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hf
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g]
    apply integral_congr_ae
    filter_upwards [TauCeti.Probability.ae_posDef_wishartGramMeasure hS hν] with A hA
    dsimp [f, g, blockIndependenceRatio]
    rw [ENNReal.toReal_ofReal (pow_nonneg hA.det_pos.le k),
      Real.rpow_neg_natCast, Real.rpow_neg_natCast, zpow_neg, zpow_natCast,
      zpow_neg, zpow_natCast, div_pow, mul_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hνR : ((p+q:ℕ):ℝ)-1 < ν := (sub_one_lt _).trans_le (Nat.cast_le.2 hν)
  have hνk : ((p+q:ℕ):ℝ)-1 < (ν:ℝ)+2*k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hC : 0 ≤ C := (div_pos (wishartNormalizer_pos hS hνk) (wishartNormalizer_pos hS hνR)).le
  rw [← hweighted, hweight, integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul, mul_assoc]
  congr 1
  let π := fun A : E ↦
    (Matrix.symmetricCongruenceLinearMap ((1 : Matrix (Fin (p+q)) (Fin (p+q)) ℝ).submatrix (Fin.castAdd q) id) A,
      Matrix.symmetricCongruenceLinearMap ((1 : Matrix (Fin (p+q)) (Fin (p+q)) ℝ).submatrix (Fin.natAdd p) id) A)
  let gp := fun z : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) ↦
    (z.1 : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ)) *
      (z.2 : Matrix (Fin q) (Fin q) ℝ).det ^ (-(k:ℝ))
  have hg : g = gp ∘ π := by
    funext A
    dsimp [g, gp, π]
    rw [coe_symmetricCongruenceLinearMap_submatrix_one,
      coe_symmetricCongruenceLinearMap_submatrix_one]
  rw [hg]
  change (∫ A, gp (π A) ∂μ') = _
  have hgp : Measurable gp := by dsimp [gp]; fun_prop
  rw [← integral_map (by fun_prop : Measurable π).aemeasurable hgp.aestronglyMeasurable]
  have hpair := map_pair_principalBlocks_wishartGramMeasure (ν+2*k) hS.posSemidef
    (Fin.castAdd q) (Fin.natAdd p) hblock
  change μ'.map π = _ at hpair
  rw [hpair]
  change (∫ z : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ×
      selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ), (z.1 : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ)) *
    (z.2 : Matrix (Fin q) (Fin q) ℝ).det ^ (-(k:ℝ)) ∂_) = _
  exact integral_prod_mul (L := ℝ)
    (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ)))
    (fun A : selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) ↦
      (A : Matrix (Fin q) (Fin q) ℝ).det ^ (-(k:ℝ)))

/-- The shifted inverse determinant moment is valid for every natural tilt order. -/
theorem integral_negative_natCast_det_shift_wishartGramMeasure {p ν : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hν : p ≤ ν) (k : ℕ) :
    (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (-(k:ℝ))
      ∂TauCeti.Probability.wishartGramMeasure (ν+2*k) S) =
      2 ^ ((p:ℝ) * (-(k:ℝ))) * S.det ^ (-(k:ℝ)) *
        TauCeti.multivariateGamma p ((ν:ℝ)/2) / TauCeti.multivariateGamma p ((ν:ℝ)/2+k) := by
  have hn : (p:ℝ)-1 < (ν+2*k:ℕ) := by
    push_cast
    have h := Nat.cast_le (α := ℝ).2 hν
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hq : -((((ν+2*k:ℕ):ℝ)-(p:ℝ)+1)/2) < -(k:ℝ) := by
    push_cast
    have h := Nat.cast_le (α := ℝ).2 hν
    linarith
  rw [TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure hS (by omega : p ≤ ν+2*k),
    TauCeti.Probability.integral_rpow_det_nonsingularWishartMeasure hS hn hq]
  push_cast
  rw [show ((ν:ℝ)+2*k)/2+ -(k:ℝ) = (ν:ℝ)/2 by ring,
    show ((ν:ℝ)+2*k)/2 = (ν:ℝ)/2+k by ring]

/-- The natural moments of the block determinant ratio are the shifted Wilks Gamma quotient. -/
theorem integral_blockIndependenceRatio_pow_wishartGramMeasure_eq_gamma
    {p q ν : ℕ} {S : Matrix (Fin (p+q)) (Fin (p+q)) ℝ}
    (hS : S.PosDef) (hν : p+q ≤ ν)
    (hblock : S.submatrix (Fin.castAdd q) (Fin.natAdd p) = 0) (k : ℕ) :
    (∫ A : selfAdjoint.submodule ℝ (Matrix (Fin (p+q)) (Fin (p+q)) ℝ),
      blockIndependenceRatio A.val ^ k ∂TauCeti.Probability.wishartGramMeasure ν S) =
      TauCeti.multivariateGamma p ((ν:ℝ)/2-q/2+k) * TauCeti.multivariateGamma p ((ν:ℝ)/2) /
        (TauCeti.multivariateGamma p ((ν:ℝ)/2-q/2) * TauCeti.multivariateGamma p ((ν:ℝ)/2+k)) := by
  have hf : Function.Injective (Fin.castAdd q : Fin p → Fin (p+q)) := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin (p+q) ↦ k.val) h
  have hg : Function.Injective (Fin.natAdd p : Fin q → Fin (p+q)) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun k : Fin (p+q) ↦ k.val) h
    simpa using hv
  have hA := hS.submatrix hf
  have hB := hS.submatrix hg
  rw [integral_blockIndependenceRatio_pow_wishartGramMeasure hS hν hblock,
    integral_negative_natCast_det_shift_wishartGramMeasure hA (by omega : p ≤ ν),
    integral_negative_natCast_det_shift_wishartGramMeasure hB (by omega : q ≤ ν)]
  exact wishartNormalizer_block_ratio_mul_negative_moments ν k hS hA hB
    (det_eq_mul_det_principalBlocks_of_zero hS.isHermitian hblock)
    ((sub_one_lt _).trans_le (Nat.cast_le.2 hν))

/-- The Beta product with block-independence shapes has the same Gamma quotient. -/
theorem integral_blockIndependence_beta_product_pow_eq_gamma {p q ν : ℕ}
    (hν : p+q ≤ ν) (hq : 0 < q) (k : ℕ) :
    (∫ v : Fin p → ℝ, (∏ i, v i)^k ∂Measure.pi (fun i : Fin p ↦
      betaMeasure (((ν:ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2))) =
      TauCeti.multivariateGamma p ((ν:ℝ)/2-q/2+k) * TauCeti.multivariateGamma p ((ν:ℝ)/2) /
        (TauCeti.multivariateGamma p ((ν:ℝ)/2-q/2) * TauCeti.multivariateGamma p ((ν:ℝ)/2+k)) := by
  have h := integral_beta_product_pow_eq_gamma (p := p) (e := ν-q) (h := q)
    (by omega : p ≤ ν-q) hq k
  have hcast : ((ν-q:ℕ):ℝ) = (ν:ℝ)-q := Nat.cast_sub (by omega : q ≤ ν)
  simpa only [hcast, sub_add_cancel, sub_div] using h

end CKSD
