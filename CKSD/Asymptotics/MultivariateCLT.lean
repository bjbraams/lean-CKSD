module

public import CKSD.Asymptotics.Basic
public import Mathlib.Probability.CramerWold
public import TauCeti.Probability.Distributions.Gaussian.Transforms
public import TauCeti.Probability.Moments.Covariance

/-!
# Euclidean central limit theorem

Independent identically distributed Euclidean random vectors with finite second moment
satisfy the multivariate central limit theorem, including singular covariance matrices.
The random vectors need only be almost everywhere measurable. Mathlib's Cramér–Wold
theorem reduces the result to its scalar IID central limit theorem. TauCeti identifies
covariance matrices with covariance bilinear forms and computes Gaussian scalar projections.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
noncomputable section

/-- The multivariate central limit theorem for IID Euclidean random vectors with finite
second moment, centered by their common expectation and scaled by the square root of
the sample size. The limiting covariance may be singular. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_of_iid {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (h2 : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ •
        ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • ∫ ω, X 0 ω ∂μ))
      atTop id (fun _ ↦ μ)
      (multivariateGaussian 0 (TauCeti.covMatrix (μ.map (X 0)))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let P := μ.map (X 0)
  have hXm : ∀ i, AEMeasurable (X i) μ := fun i ↦ (hident i).aemeasurable_fst
  have h2P : MemLp id 2 P :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hXm 0)).mpr h2
  let : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (μ.map (X 0)))
  have hZn : ∀ n : ℕ, AEMeasurable (fun ω ↦ (Real.sqrt n)⁻¹ •
      ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • ∫ ω, X 0 ω ∂μ)) μ := by
    intro n
    exact ((Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm i).sub aemeasurable_const).const_smul ((Real.sqrt n)⁻¹ : ℝ)
  apply _root_.TendstoInDistribution.of_inner aemeasurable_id hZn
  intro t
  let s : E → ℝ := fun x ↦ inner ℝ x t
  have hs : Measurable s := by fun_prop
  have h2s : MemLp (s ∘ X 0) 2 μ := by
    simpa only [s, Function.comp_def] using h2.inner_const (𝕜 := ℝ) t
  have hind : iIndepFun (fun i ↦ s ∘ X i) μ := hindep.comp (fun _ ↦ s) (fun _ ↦ hs)
  have hid : ∀ i, IdentDistrib (s ∘ X i) (s ∘ X 0) μ μ :=
    fun i ↦ (hident i).comp hs
  have hvar : Var[s ∘ X 0; μ] = inner ℝ t ((TauCeti.covMatrix P).toEuclideanLin t) := by
    have he := covarianceBilin_self h2P t
    rw [TauCeti.covarianceBilin_eq_covMatrix P h2P t t] at he
    have hmap : Var[fun x : E ↦ inner ℝ t x; P] = Var[s ∘ X 0; μ] := by
      change Var[fun x : E ↦ inner ℝ t x; μ.map (X 0)] = _
      rw [variance_map (by fun_prop) (hXm 0)]
      congr 1
      ext ω
      exact real_inner_comm _ _
    exact hmap.symm.trans he.symm
  have hY : HasLaw (fun z : E ↦ inner ℝ z t)
      (gaussianReal 0 (Var[s ∘ X 0; μ]).toNNReal)
      (multivariateGaussian 0 (TauCeti.covMatrix P)) := by
    refine ⟨by fun_prop, ?_⟩
    have hf : (fun z : E ↦ inner ℝ z t) = fun z ↦ inner ℝ t z := funext fun z ↦ real_inner_comm _ _
    rw [hf, TauCeti.Probability.map_inner_multivariateGaussian 0 t
      (TauCeti.posSemidef_covMatrix P h2P), inner_zero_right, hvar]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ↦ s ∘ X i) (P := μ)
    (Y := fun z : E ↦ inner ℝ z t)
    (P' := multivariateGaussian 0 (TauCeti.covMatrix P)) hY h2s hind hid
  convert hclt using 1
  · funext n ω
    simp only [real_inner_smul_left, inner_sub_left, sum_inner, s, Function.comp_apply]
    have hmean : inner ℝ (∫ ω, X 0 ω ∂μ) t = ∫ ω, s (X 0 ω) ∂μ := by
      calc inner ℝ (∫ ω, X 0 ω ∂μ) t = inner ℝ t (∫ ω, X 0 ω ∂μ) :=
            real_inner_comm _ _
        _ = ∫ ω, inner ℝ t (X 0 ω) ∂μ :=
            (innerSL ℝ t).integral_comp_comm (h2.integrable (by norm_num)) |>.symm
        _ = _ := integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_comm _ _)
    rw [hmean]
  · rfl

/-- The Euclidean sample-mean central limit theorem for an i.i.d. sequence with law `P`, with the
population covariance matrix as the limiting Gaussian covariance. -/
theorem tendstoInDistribution_sqrt_smul_sampleAverage
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n •
      (sampleAverage X n ω - ∫ x, x ∂P))
      atTop id (fun _ ↦ μ) (multivariateGaussian 0 (TauCeti.covMatrix P)) := by
  let E := EuclideanSpace ℝ (Fin d)
  have h2X : MemLp (X 0) 2 μ := by
    have h : MemLp id 2 (μ.map (X 0)) := (hiid.2.2 0).symm ▸ h2
    exact h.comp_of_map (hiid.1 0).aemeasurable
  have hid : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i ↦
    ⟨(hiid.1 i).aemeasurable, (hiid.1 0).aemeasurable,
      (hiid.2.2 i).trans (hiid.2.2 0).symm⟩
  have hc := tendstoInDistribution_inv_sqrt_smul_sum_sub_of_iid μ X h2X hiid.2.1 hid
  rw [hiid.2.2 0] at hc
  have hm : (∫ ω, X 0 ω ∂μ) = ∫ x, x ∂P := by
    rw [← hiid.2.2 0]
    exact (integral_map (hiid.1 0).aemeasurable
      (aestronglyMeasurable_id : AEStronglyMeasurable (id : E → E) (μ.map (X 0)))).symm
  rw [hm] at hc
  have heq : ∀ n : ℕ, (fun ω ↦ (Real.sqrt n)⁻¹ •
      ((∑ i ∈ Finset.range n, X i ω) - (n : ℝ) • ∫ x, x ∂P)) =
      fun ω ↦ Real.sqrt n • (sampleAverage X n ω - ∫ x, x ∂P) := by
    intro n
    funext ω
    by_cases hn : n = 0
    · simp [hn]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
    have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [smul_sub, smul_smul, sampleAverage]
    congr 1 <;> congr 1 <;> field_simp <;> nlinarith
  exact hc.congr (fun n ↦ ae_of_all _ fun ω ↦ congrFun (heq n) ω) (ae_of_all _ fun _ ↦ rfl)

end
end CKSD
