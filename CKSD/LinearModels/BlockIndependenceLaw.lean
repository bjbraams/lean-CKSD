module

public import CKSD.LinearModels.BlockIndependenceMoments
public import TauCeti.Probability.Moments.CompactDeterminacy
/-!
# Exact Beta-product law for block independence

For a block-diagonal positive-definite covariance, the Wishart determinant ratio for two
coordinate blocks has a finite independent Beta-product law. Hadamard–Fischer bounds the
ratio in the unit interval; equality of natural moments therefore determines its law.

This is Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 11.2.4 and its
specialization to two blocks, printed pages 533–534 (PDF pages 559–560 of the local 2005
copy). Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Theorems
9.3.1–9.3.3, printed pages 387–388 (PDF pages 405–406), gives a conditional-regression
reduction to the same law. Pinned TauCeti supplies compact moment determinacy; the moments
and matrix support bound are proved by local modules.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology MatrixOrder BigOperators
namespace CKSD
/-- The block-independence Wishart determinant ratio has a finite independent Beta-product law. -/
theorem map_block_independence_ratio_wishart_eq_beta_product {p q ν : ℕ}
    (hq : 0 < q) (hν : p+q ≤ ν)
    (S : Matrix (Fin (p+q)) (Fin (p+q)) ℝ) (hS : S.PosDef)
    (hblock : S.submatrix (Fin.castAdd q) (Fin.natAdd p) = 0) :
    (TauCeti.Probability.wishartGramMeasure ν S).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin (p+q)) (Fin (p+q)) ℝ) ↦ blockIndependenceRatio A.val) =
      (Measure.pi fun i : Fin p ↦ betaMeasure (((ν:ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2)).map
        (fun x : Fin p → ℝ ↦ ∏ i, x i) := by
  have ha (i : Fin p) : 0 < ((ν:ℝ)-(q:ℝ)-i.val)/2 := by
    have hi : (i.val:ℝ) < (ν-q:ℕ) := by exact_mod_cast (by omega : i.val < ν-q)
    rw [Nat.cast_sub (by omega : q ≤ ν)] at hi
    linarith
  have hb : 0 < (q:ℝ)/2 := by positivity
  let _ (i : Fin p) : IsProbabilityMeasure (betaMeasure (((ν:ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2)) :=
    isProbabilityMeasureBeta (ha i) hb
  let E := selfAdjoint.submodule ℝ (Matrix (Fin (p+q)) (Fin (p+q)) ℝ)
  let f : E → ℝ := fun A ↦ blockIndependenceRatio A.val
  let g : (Fin p → ℝ) → ℝ := fun x ↦ ∏ i, x i
  have hf : Measurable f := (measurable_block_independence_ratio p q).comp measurable_subtype_coe
  have hg : Measurable g := by dsimp [g]; fun_prop
  change (TauCeti.Probability.wishartGramMeasure ν S).map f =
    (Measure.pi fun i : Fin p ↦ betaMeasure (((ν:ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2)).map g
  apply TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (K := Icc (0:ℝ) 1) isCompact_Icc
  · change ∀ᵐ x ∂_, x ∈ Icc (0:ℝ) 1
    apply (ae_map_iff hf.aemeasurable measurableSet_Icc).2
    filter_upwards [TauCeti.Probability.ae_posDef_wishartGramMeasure hS hν] with A hA
    exact ⟨(block_independence_ratio_mem_ioc hA).1.le, (block_independence_ratio_mem_ioc hA).2⟩
  · change ∀ᵐ x ∂_, x ∈ Icc (0:ℝ) 1
    apply (ae_map_iff hg.aemeasurable measurableSet_Icc).2
    have hv : ∀ᵐ x ∂Measure.pi (fun i : Fin p ↦ betaMeasure (((ν:ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2)),
        ∀ i, x i ∈ Icc (0:ℝ) 1 :=
      ae_all_iff.2 fun i ↦ Measure.tendsto_eval_ae_ae.eventually
        (TauCeti.Probability.ae_mem_Icc_betaMeasure _ _)
    filter_upwards [hv] with x hx
    exact ⟨Finset.prod_nonneg fun i _ ↦ (hx i).1,
      Finset.prod_le_one₀ (fun i _ ↦ (hx i).1) (fun i _ ↦ (hx i).2)⟩
  · intro k
    rw [integral_map hf.aemeasurable (by fun_prop), integral_map hg.aemeasurable (by fun_prop)]
    exact (integral_block_independence_ratio_pow_wishart_gram_measure_eq_gamma hS hν hblock k).trans
      (integral_block_independence_beta_product_pow_eq_gamma hν hq k).symm

end CKSD
