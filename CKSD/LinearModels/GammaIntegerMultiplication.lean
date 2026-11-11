module
public import TauCeti.Analysis.SpecialFunctions.Gamma
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
/-!
# Integer multiplication of Gamma quotients

For a positive argument and a natural shift, Gamma quotients are finite rising products.
Reindexing a product of length `p*k` by `Fin k × Fin p` gives the integer multiplication formula
needed for determinant-to-trace moments. This uses pinned TauCeti's positive Gamma recurrence
product and Mathlib's finite-product equivalence, without a general Gauss multiplication theorem.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CKSD
/-- Positive Gamma quotients with natural shift are finite products. -/
theorem gamma_add_nat_div_eq_prod_fin {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a+k) / Real.Gamma a = ∏ j : Fin k, (a+j.val) := by
  apply (div_eq_iff (Real.Gamma_pos_of_pos ha).ne').2
  simpa only [Finset.prod_range] using (Real.prod_range_add_mul_Gamma ha k).symm
/-- The integer multiplication identity for Gamma quotients with natural shifts. -/
theorem gamma_mul_add_nat_mul_div {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma ((p:ℝ)*a+(p:ℝ)*k) / Real.Gamma ((p:ℝ)*a) =
      (p:ℝ)^(p*k) * ∏ j : Fin p,
        (Real.Gamma (a+j.val/(p:ℝ)+k) / Real.Gamma (a+j.val/(p:ℝ))) := by
  have hpR : (0:ℝ) < p := Nat.cast_pos.2 hp
  have hj (j : Fin p) : 0 < a+j.val/(p:ℝ) := add_pos_of_pos_of_nonneg ha (by positivity)
  rw [show (p:ℝ)*k = ((k*p:ℕ):ℝ) by push_cast; ring,
    gamma_add_nat_div_eq_prod_fin (mul_pos hpR ha)]
  simp_rw [gamma_add_nat_div_eq_prod_fin (hj _)]
  have hreindex : (∏ i : Fin (k*p), ((p:ℝ)*a+i.val)) =
      ∏ r : Fin k, ∏ j : Fin p, ((p:ℝ)*a+(j.val+(p:ℝ)*r.val)) := by
    rw [← Fintype.prod_prod_type (f := fun i : Fin k × Fin p ↦ ((p:ℝ)*a+(i.2.val+(p:ℝ)*i.1.val)))]
    symm
    apply Fintype.prod_equiv finProdFinEquiv
    intro i
    dsimp [finProdFinEquiv]
    push_cast
    rfl
  rw [hreindex]
  have hfactor (r : Fin k) (j : Fin p) : (p:ℝ)*a+(j.val+(p:ℝ)*r.val) =
      (p:ℝ)*(a+j.val/(p:ℝ)+r.val) := by field_simp; ring
  simp_rw [hfactor, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Finset.prod_comm]
end CKSD
