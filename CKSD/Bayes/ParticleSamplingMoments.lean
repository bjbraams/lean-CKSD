module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Real moments of bounded iid sampling errors

Hoeffding's lemma and independence make the centered iid sum sub-Gaussian after
normalization by oscillation and square-root sample size. Exponential domination
then bounds every nonnegative real absolute moment, with an explicit factorial
constant. These estimates supply the sampling step in Del Moral, *Feynman-Kac
Formulae* (2004), Lemma 7.3.3 and Theorem 7.4.4.

The sub-Gaussian and product-independence results are reused from pinned Mathlib.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators Nat
namespace CKSD
/-- A real power is dominated by an exponential with an explicit factorial coefficient. -/
theorem abs_rpow_le_one_add_factorial_mul_exp {p : ℝ} (hp : 0 ≤ p) {m : ℕ}
    (hpm : p ≤ m) (x : ℝ) :
    |x|^p ≤ 1+(m !:ℝ)*(Real.exp x+Real.exp (-x)) := by
  have hpow : |x|^p ≤ 1+|x|^m := by
    by_cases hx : |x| ≤ 1
    · exact (Real.rpow_le_one (abs_nonneg x) hx hp).trans (le_add_of_nonneg_right (pow_nonneg (abs_nonneg x) m))
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hpm
      rw [Real.rpow_natCast] at hh
      exact hh.trans (by linarith)
  have hf := (div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos m))).1
    (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) m)
  have he : Real.exp |x| ≤ Real.exp x+Real.exp (-x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have hf2 : |x|^m ≤ (m !:ℝ)*(Real.exp x+Real.exp (-x)) :=
    hf.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (m !)))
  exact hpow.trans (by linarith [hf2])
/-- A sub-Gaussian variable of parameter one has a uniform moment bound of every real order. -/
theorem integral_abs_rpow_le_of_hasSubgaussianMGF_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : HasSubgaussianMGF Y 1 P) {p : ℝ} (hp : 0 ≤ p)
    {m : ℕ} (hpm : p ≤ m) :
    (∫ ω, |Y ω|^p ∂P) ≤ 1+2*(m !:ℝ)*Real.exp (1/2) := by
  have hi : Integrable (fun ω ↦ |Y ω|^p) P := by
    have hh := (hY.memLp (p := (NNReal.mk p hp))).integrable_norm_rpow'
    rw [ENNReal.coe_toReal] at hh
    simpa only [Real.norm_eq_abs,NNReal.coe_mk] using hh
  have hpos : Integrable (fun ω ↦ Real.exp (Y ω)) P := by
    simpa only [one_mul] using hY.integrable_exp_mul 1
  have hneg : Integrable (fun ω ↦ Real.exp (-Y ω)) P := by
    simpa only [neg_one_mul] using hY.integrable_exp_mul (-1)
  calc _ ≤ ∫ ω, 1+(m !:ℝ)*(Real.exp (Y ω)+Real.exp (-Y ω)) ∂P := by
        apply integral_mono hi ((integrable_const 1).add ((hpos.add hneg).const_mul _))
        exact fun ω ↦ abs_rpow_le_one_add_factorial_mul_exp hp hpm (Y ω)
    _ = 1+(m !:ℝ)*((∫ ω,Real.exp (Y ω) ∂P)+(∫ ω,Real.exp (-Y ω) ∂P)) := by
        rw [integral_add (f := fun _ : Ω ↦ (1:ℝ))
          (g := fun ω ↦ (m !:ℝ)*(Real.exp (Y ω)+Real.exp (-Y ω)))
          (integrable_const 1) ((hpos.add hneg).const_mul _),
          integral_const_mul,integral_add hpos hneg]
        simp
    _ ≤ _ := by
        have h1 := hY.mgf_le 1
        have h2 := hY.mgf_le (-1)
        simp only [mgf,one_mul,neg_one_mul,NNReal.coe_one,one_pow,neg_one_sq] at h1 h2
        have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg (m !))
        nlinarith
/-- Centered iid sums, normalized by the square-root sample size and oscillation, are
sub-Gaussian of parameter one. -/
theorem hasSubgaussianMGF_normalized_iid_sum
    {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
    {N : ℕ} (hN : 0<N) (f : X → ℝ) (hf : Measurable f) {B : ℝ} (hB : 0<B)
    (hfo : ∀ x y, |f x-f y|≤B) :
    HasSubgaussianMGF (fun z : Fin N → X ↦ (B*Real.sqrt N)⁻¹ *
      ∑ i, (f (z i)-∫ x,f x ∂ν)) 1 (Measure.pi (fun _ : Fin N ↦ ν)) := by
  classical
  let x₀ : X := Classical.choice inferInstance
  have hr : ∀ᵐ x ∂ν, f x∈Icc (f x₀-B) (f x₀+B) := by
    refine ae_of_all _ fun x ↦ ?_
    have h:=abs_le.mp (hfo x x₀)
    constructor <;> linarith
  have hc : ((‖(f x₀+B)-(f x₀-B)‖₊/2)^2 : ℝ≥0) = (NNReal.mk (B^2) (sq_nonneg B)) := by
    apply NNReal.coe_injective
    change (‖(f x₀+B)-(f x₀-B)‖/2)^2=B^2
    rw [show (f x₀+B)-(f x₀-B)=2*B by ring,Real.norm_of_nonneg (by positivity)]
    ring
  have hbase := hasSubgaussianMGF_of_mem_Icc hf.aemeasurable hr
  rw [hc] at hbase
  let π:=Measure.pi (fun _ : Fin N ↦ ν)
  have hi (i : Fin N) : HasSubgaussianMGF
      (fun z : Fin N → X ↦ f (z i)-∫ x,f x ∂ν) (NNReal.mk (B^2) (sq_nonneg B)) π := by
    apply HasSubgaussianMGF.of_map (Y := fun z : Fin N → X ↦ z i)
      (X := fun x ↦ f x-∫ y,f y ∂ν) (measurable_pi_apply i).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin N ↦ ν) i).map_eq]
    exact hbase
  have hind : iIndepFun (fun (i : Fin N) (z : Fin N → X) ↦ f (z i)-∫ x,f x ∂ν) π :=
    iIndepFun_pi (fun _ : Fin N ↦ hf.aemeasurable.sub_const _)
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ)
    (c := fun _ ↦ ((NNReal.mk (B^2) (sq_nonneg B)) : ℝ≥0)) (fun i _ ↦ hi i)
  have hz := (HasSubgaussianMGF_iff_kernel.mp hs).const_mul ((B*Real.sqrt N)⁻¹)
  apply HasSubgaussianMGF_iff_kernel.mpr
  convert hz using 1
  apply NNReal.coe_injective
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    NNReal.coe_mul,NNReal.coe_mk,NNReal.coe_one,NNReal.coe_natCast]
  have hnR : (0:ℝ)<N := Nat.cast_pos.2 hN
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  field_simp [hB.ne',(Real.sqrt_pos.2 hnR).ne']
  nlinarith
end CKSD
