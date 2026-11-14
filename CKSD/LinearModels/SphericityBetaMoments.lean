module

public import CKSD.LinearModels.GammaIntegerMultiplication
public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import CKSD.LinearModels.SphericityMoments
public import TauCeti.Probability.Distributions.Beta.Basic
public import Mathlib.MeasureTheory.Integral.Pi
/-!
# Beta-product moments for the sphericity ratio

The integer multiplication formula for natural-shift Gamma quotients turns the spherical
Wishart determinant-to-trace moments into a product of Beta moments. The zero-index Gamma
factors cancel, leaving `p-1` Beta factors with shapes `(e-i)/2` and `i/2+i/p`.

Pinned TauCeti supplies the multivariate Gamma quotient and Beta moments; Mathlib supplies
finite-product integration. The integer multiplication adapter is local.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CKSD
/-- Spherical determinant-to-trace moments agree with a product of Beta moments. -/
theorem sphericity_gamma_moment_eq_product {p : ℕ} (hp : 0 < p) {a : ℝ}
    (ha : (p:ℝ)-1 < 2*a) (k : ℕ) :
    (p:ℝ)^(p*k) * TauCeti.multivariateGamma p (a+k) * Real.Gamma ((p:ℝ)*a) /
      (TauCeti.multivariateGamma p a * Real.Gamma ((p:ℝ)*a+(p:ℝ)*k)) =
      ∏ i : Fin (p-1), Real.Gamma (a-((i.val:ℝ)+1)/2+k) * Real.Gamma (a+((i.val:ℝ)+1)/(p:ℝ)) /
        (Real.Gamma (a-((i.val:ℝ)+1)/2) * Real.Gamma (a+((i.val:ℝ)+1)/(p:ℝ)+k)) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.2 hp
  have ha0 : 0 < a := by
    have : (1:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  let C := (p:ℝ)^(p*k)
  let R : Fin p → ℝ := fun i ↦ Real.Gamma (a+k-i.val/2) / Real.Gamma (a-i.val/2)
  let Q : Fin p → ℝ := fun i ↦ Real.Gamma (a+i.val/(p:ℝ)+k) / Real.Gamma (a+i.val/(p:ℝ))
  have hC : C ≠ 0 := pow_ne_zero _ hpR.ne'
  have hrewrite : (p:ℝ)^(p*k) * TauCeti.multivariateGamma p (a+k) * Real.Gamma ((p:ℝ)*a) /
      (TauCeti.multivariateGamma p a * Real.Gamma ((p:ℝ)*a+(p:ℝ)*k)) =
      (TauCeti.multivariateGamma p (a+k) / TauCeti.multivariateGamma p a) *
        (C / (Real.Gamma ((p:ℝ)*a+(p:ℝ)*k) / Real.Gamma ((p:ℝ)*a))) := by
    simp only [C, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hrewrite, gamma_mul_add_nat_mul_div hp ha0 k]
  have hcanc : C / (C * ∏ i, Q i) = 1 / (∏ i, Q i) := by
    simpa only [mul_one] using mul_div_mul_left (1:ℝ) (∏ i, Q i) hC
  change (TauCeti.multivariateGamma p (a+k) / TauCeti.multivariateGamma p a) *
    (C / (C * ∏ i, Q i)) = _
  rw [hcanc, TauCeti.multivariateGamma_div_multivariateGamma, mul_one_div]
  change (∏ i, R i) / (∏ i, Q i) = _
  rw [← Finset.prod_div_distrib]
  have hpair (i : Fin p) : R i / Q i =
      Real.Gamma (a-i.val/2+k)*Real.Gamma (a+i.val/(p:ℝ)) /
        (Real.Gamma (a-i.val/2)*Real.Gamma (a+i.val/(p:ℝ)+k)) := by
    rw [show a-i.val/2+k = a+k-i.val/2 by ring]
    simp only [R, Q, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simp_rw [hpair]
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero, add_zero,
    show Real.Gamma (a+k)*Real.Gamma a / (Real.Gamma a*Real.Gamma (a+k)) = 1 by
      rw [mul_comm (Real.Gamma (a+k))]; exact div_self (mul_ne_zero (Real.Gamma_pos_of_pos ha0).ne'
        (Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg ha0 (Nat.cast_nonneg k))).ne'), one_mul,
    Nat.succ_sub_one, Fin.val_succ, Nat.cast_add, Nat.cast_one]
/-- Independent Beta-product moments equal the spherical Wishart Gamma quotient. -/
theorem integral_sphericity_beta_product_pow_eq_gamma {p e : ℕ}
    (hp : 0 < p) (he : p ≤ e) (k : ℕ) :
    (∫ x : Fin (p-1) → ℝ, (∏ i, x i)^k ∂Measure.pi (fun i : Fin (p-1) ↦
      betaMeasure (((e:ℝ)-((i.val:ℝ)+1))/2) (((i.val:ℝ)+1)/2+((i.val:ℝ)+1)/(p:ℝ)))) =
      (p:ℝ)^(p*k) * TauCeti.multivariateGamma p ((e:ℝ)/2+k) * Real.Gamma ((p:ℝ)*((e:ℝ)/2)) /
        (TauCeti.multivariateGamma p ((e:ℝ)/2) * Real.Gamma ((p:ℝ)*((e:ℝ)/2)+(p:ℝ)*k)) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.2 hp
  have ha (i : Fin (p-1)) : 0 < ((e:ℝ)-((i.val:ℝ)+1))/2 := by
    have hi : (i.val:ℝ)+1 < e := by exact_mod_cast (by omega : i.val+1 < e)
    linarith
  have hb (i : Fin (p-1)) : 0 < ((i.val:ℝ)+1)/2+((i.val:ℝ)+1)/(p:ℝ) := by positivity
  let _ (i : Fin (p-1)) : IsProbabilityMeasure
      (betaMeasure (((e:ℝ)-((i.val:ℝ)+1))/2) (((i.val:ℝ)+1)/2+((i.val:ℝ)+1)/(p:ℝ))) :=
    isProbabilityMeasureBeta (ha i) (hb i)
  have hfun : (fun x : Fin (p-1) → ℝ ↦ (∏ i, x i)^k) = fun x ↦ ∏ i, (x i)^k :=
    funext fun _ ↦ (Finset.prod_pow _ _ _).symm
  rw [hfun, integral_fintype_prod_eq_prod (fun (_ : Fin (p-1)) (x : ℝ) ↦ x^k)]
  simp_rw [TauCeti.Probability.integral_pow_betaMeasure (ha _) (hb _)]
  rw [sphericity_gamma_moment_eq_product hp (show (p:ℝ)-1 < 2*((e:ℝ)/2) by
    have := Nat.cast_le (α := ℝ).2 he; linarith) k]
  apply Finset.prod_congr rfl
  intro i _
  congr 2 <;> congr 1 <;> ring
end CKSD
