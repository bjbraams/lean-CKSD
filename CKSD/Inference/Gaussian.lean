module

public import CKSD.Inference.Basic

/-!
# Inference: Gaussian

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.57, strict James–Stein improvement in dimension at least three. -/
theorem james_stein_risk_eq_and_lt {p : ℕ} (hp : 3 ≤ p) (θ : EuclideanSpace ℝ (Fin p)) :
    let P := multivariateGaussian θ (1 : Matrix (Fin p) (Fin p) ℝ);
    let δ := fun x : EuclideanSpace ℝ (Fin p) ↦ (1 - ((p : ℝ) - 2) / ‖x‖ ^ 2) • x;
    (∫ x, ‖δ x - θ‖ ^ 2 ∂P) = (p : ℝ) - ((p : ℝ) - 2) ^ 2 *
      (∫ x, (‖x‖ ^ 2)⁻¹ ∂P) ∧ (∫ x, ‖δ x - θ‖ ^ 2 ∂P) < p := by
  sorry

/-- GAPS 101.64: Gaussian integration by parts, in the continuously differentiable scope. -/
theorem gaussian_integration_by_parts {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0)
    (hv : 0 < v) (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hg : ContDiff ℝ 1 g) :
    let P := multivariateGaussian θ ((v : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ));
    ∀ (hL2 : MemLp g 2 P),
    ∀ (hder : ∀ i, Integrable
      (fun x ↦ (fderiv ℝ g x (EuclideanSpace.single i 1)) i) P),
    ∀ (i : Fin p),
    (∫ x, (x i - θ i) * g x i ∂P) =
      (v : ℝ) * ∫ x, (fderiv ℝ g x (EuclideanSpace.single i 1)) i ∂P := by
  sorry

/-- GAPS 101.69: existence and uniqueness of a regular natural-exponential-family maximum.
The domain is the full Laplace-integrability domain, not an arbitrary open
subset of it. The criterion is the per-observation log likelihood. -/
theorem exists_exponential_family_mle_iff_mem_interior_convex_support
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    ∀ (hNne : N.Nonempty),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t : EuclideanSpace ℝ (Fin d)),
    (∃ eta ∈ N, ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta) ↔
      t ∈ interior (convexHull ℝ nu.support) := by
  sorry

/-- GAPS 101.69: a natural-family maximizer is unique and solves the mean equation. -/
theorem exponential_family_mle_unique_and_mean_eq
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    ∀ (hN : IsOpen N),
    let A := fun eta : EuclideanSpace ℝ (Fin d) ↦
      Real.log (∫ x, Real.exp (inner ℝ eta x) ∂nu);
    ∀ (t eta : EuclideanSpace ℝ (Fin d)),
    ∀ (heta : eta ∈ N),
    ∀ (hmax : ∀ zeta ∈ N, inner ℝ zeta t - A zeta ≤ inner ℝ eta t - A eta),
    HasFDerivAt A (innerSL ℝ t) eta ∧
      ∀ zeta ∈ N, inner ℝ zeta t - A zeta = inner ℝ eta t - A eta → zeta = eta := by
  sorry


/-- GAPS 101.60: the simultaneous-contrast supremum underlying Scheffé's method.
This is the geometric identity; its Gaussian pivot uses the projection sampling laws. -/
theorem scheffe_contrast_supremum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Submodule ℝ H) (v : H) (hv : v ∈ S) (s : ℝ) (hs : 0 < s) :
    sSup {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} =
      ‖v‖ ^ 2 / s ^ 2 := by
  by_cases hv0 : v = 0
  · subst v
    by_cases hS : ∃ u ∈ S, u ≠ (0 : H)
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = {0} := by
        ext r
        simp only [inner_zero_right, zero_pow two_ne_zero, zero_div, mem_ofPred_eq,
          mem_singleton_iff]
        exact ⟨fun ⟨_, _, _, hr⟩ ↦ hr, fun hr ↦ by
          obtain ⟨u, hu, hune⟩ := hS
          exact ⟨u, hu, hune, hr⟩⟩
      rw [hset]
      simp
    · have hset : {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧
          r = inner ℝ u (0 : H) ^ 2 / (s ^ 2 * ‖u‖ ^ 2)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro r ⟨u, hu, hune, _⟩
        exact hS ⟨u, hu, hune⟩
      rw [hset]
      simp
  · let R := {r : ℝ | ∃ u ∈ S, u ≠ 0 ∧ r = inner ℝ u v ^ 2 / (s ^ 2 * ‖u‖ ^ 2)}
    have hupper : ∀ r ∈ R, r ≤ ‖v‖ ^ 2 / s ^ 2 := by
      rintro r ⟨u, hu, hune, rfl⟩
      have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hune
      have hcs := real_inner_mul_inner_self_le u v
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
      apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos hu0))
        (sq_pos_of_pos hs)).mpr
      nlinarith [mul_nonneg (sq_nonneg s)
        (show 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 by nlinarith)]
    have hmem : ‖v‖ ^ 2 / s ^ 2 ∈ R := by
      refine ⟨v, hv, hv0, ?_⟩
      rw [real_inner_self_eq_norm_sq]
      field_simp [ne_of_gt hs, norm_ne_zero_iff.mpr hv0]
    exact le_antisymm (csSup_le ⟨_, hmem⟩ hupper) (le_csSup ⟨_, hupper⟩ hmem)

end CKSD
