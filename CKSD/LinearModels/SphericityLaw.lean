module
public import CKSD.LinearModels.SphericityBetaMoments
public import CKSD.LinearModels.SphericityBasic
public import TauCeti.Probability.Moments.CompactDeterminacy
/-!
# Exact Beta-product law of the sphericity ratio

The determinant-to-average-trace ratio of a spherical Gaussian-Gram Wishart matrix has
compact support in the unit interval. Its natural moments agree with those of a finite
independent Beta product. Pinned TauCeti's compact moment determinacy identifies the laws;
the matrix moments and Gamma-to-Beta algebra are local project theory.
-/
@[expose] public section
noncomputable section
open Filter Set Real MeasureTheory ProbabilityTheory Matrix
open scoped Topology BigOperators ENNReal NNReal MatrixOrder
namespace CKSD
/-- The exact spherical Wishart sphericity law is a product of independent Beta factors. -/
theorem map_sphericityRatio_wishart_eq_beta_product {p e : ℕ}
    (hp : 0 < p) (he : p ≤ e) (v : ℝ) (hv : 0 < v) :
    (TauCeti.Probability.wishartGramMeasure e (v • (1 : Matrix (Fin p) (Fin p) ℝ))).map
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ sphericityRatio A.val) =
      (Measure.pi fun i : Fin (p-1) ↦ betaMeasure (((e : ℝ) - (i.val + 1)) / 2)
        (((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p)).map (fun x ↦ ∏ i, x i) := by
  have hp0 : 0 < p := hp
  have hpa (i : Fin (p-1)) : 0 < ((e : ℝ) - (i.val + 1)) / 2 := by
    have hi : i.val + 1 < e := by omega
    have hiR : (i.val : ℝ) + 1 < e := by exact_mod_cast hi
    linarith
  have hpb (i : Fin (p-1)) : 0 < ((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p := by positivity
  let : ∀ i : Fin (p-1), IsProbabilityMeasure (betaMeasure (((e : ℝ) - (i.val + 1)) / 2)
    (((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p)) := fun i ↦ isProbabilityMeasureBeta (hpa i) (hpb i)
  let E := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
  let f : E → ℝ := fun A ↦ (A : Matrix (Fin p) (Fin p) ℝ).det /
    ((A : Matrix (Fin p) (Fin p) ℝ).trace / p)^p
  let g : (Fin (p-1) → ℝ) → ℝ := fun x ↦ ∏ i, x i
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hS : (v • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef := Matrix.PosDef.one.smul hv
  change (TauCeti.Probability.wishartGramMeasure e (v • 1)).map f =
    (Measure.pi fun i : Fin (p-1) ↦ betaMeasure (((e : ℝ) - (i.val + 1)) / 2)
      (((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p)).map g
  apply TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (K := Icc (0 : ℝ) 1) isCompact_Icc
  · change ∀ᵐ z ∂_, z ∈ Icc (0 : ℝ) 1
    apply (ae_map_iff hf.aemeasurable measurableSet_Icc).2
    filter_upwards [TauCeti.Probability.ae_posDef_wishartGramMeasure hS he] with A hA
    exact ⟨(det_trace_ratio_mem_Ioc hp0 A.val hA).1.le, (det_trace_ratio_mem_Ioc hp0 A.val hA).2⟩
  · change ∀ᵐ z ∂_, z ∈ Icc (0 : ℝ) 1
    apply (ae_map_iff hg.aemeasurable measurableSet_Icc).2
    have hs : ∀ᵐ x ∂Measure.pi (fun i : Fin (p-1) ↦ betaMeasure (((e : ℝ) - (i.val + 1)) / 2)
        (((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p)), ∀ i, x i ∈ Icc (0 : ℝ) 1 :=
      ae_all_iff.2 fun i ↦ Measure.tendsto_eval_ae_ae.eventually
        (TauCeti.Probability.ae_mem_Icc_betaMeasure _ _)
    filter_upwards [hs] with x hx
    exact ⟨Finset.prod_nonneg fun i _ ↦ (hx i).1,
      Finset.prod_le_one₀ (fun i _ ↦ (hx i).1) (fun i _ ↦ (hx i).2)⟩
  · intro k
    rw [integral_map hf.aemeasurable (by fun_prop), integral_map hg.aemeasurable (by fun_prop)]
    exact (integral_det_trace_ratio_pow_wishartGram_eq_gamma hp0 he v hv k).trans (integral_sphericity_beta_product_pow_eq_gamma hp0 he k).symm
end CKSD