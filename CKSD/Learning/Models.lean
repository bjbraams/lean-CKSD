module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic

/-!
# Learning: Models

Sources: `GAPS.md`, `SYNOPSIS107.md`, and `STRUCTURE107.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 107.26, finite-state entropy variational formula for the log partition function. -/
theorem log_sum_exp_entropy_variational_formula {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    let Z := ∑ i, Real.exp (a i);
    (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      (∑ i, (w i * a i - w i * Real.log (w i))) ≤ Real.log Z) ∧
      (∑ i, ((Real.exp (a i) / Z) * a i -
        (Real.exp (a i) / Z) * Real.log (Real.exp (a i) / Z))) = Real.log Z := by
  intro Z
  have hZ : 0 < Z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hq1 : ∑ i, Real.exp (a i) / Z = 1 := by rw [← Finset.sum_div, div_self hZ.ne']
  constructor
  · intro w hw hw1
    have hpt : ∀ i, w i * a i - w i * Real.log (w i) ≤
        w i * Real.log Z + (Real.exp (a i) / Z - w i) := by
      intro i
      rcases (hw i).lt_or_eq with hpos | hzero
      · have hq : 0 < Real.exp (a i) / Z := div_pos (Real.exp_pos _) hZ
        have hl := Real.log_le_sub_one_of_pos (div_pos hq hpos)
        rw [Real.log_div hq.ne' hpos.ne', Real.log_div (Real.exp_pos _).ne' hZ.ne',
          Real.log_exp] at hl
        have := mul_le_mul_of_nonneg_left hl hpos.le
        have hc : w i * (Real.exp (a i) / Z / w i - 1) = Real.exp (a i) / Z - w i := by
          field_simp
        rw [hc] at this
        nlinarith
      · rw [← hzero]; simp only [zero_mul, sub_zero, zero_add]; positivity
    calc (∑ i, (w i * a i - w i * Real.log (w i)))
        ≤ ∑ i, (w i * Real.log Z + (Real.exp (a i) / Z - w i)) := Finset.sum_le_sum fun i _ ↦ hpt i
      _ = Real.log Z := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, Finset.sum_sub_distrib, hq1, hw1]
        ring
  · have hpt : ∀ i, (Real.exp (a i) / Z) * a i -
        (Real.exp (a i) / Z) * Real.log (Real.exp (a i) / Z) = (Real.exp (a i) / Z) * Real.log Z := by
      intro i
      rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]; ring
    simp_rw [hpt]
    rw [← Finset.sum_mul, hq1, one_mul]

/-- GAPS 107.26, the zero-temperature limit of a finite log partition function. -/
theorem tendsto_log_sum_exp_div_atTop {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    Tendsto (fun beta : ℝ ↦ Real.log (∑ i, Real.exp (beta * a i)) / beta)
      atTop (𝓝 (sSup (range a))) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ a hne
  have hM : sSup (range a) = a k := by
    apply le_antisymm
    · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact csSup_le (range_nonempty a) (by rintro _ ⟨i, rfl⟩; exact hk i (Finset.mem_univ _))
    · exact le_csSup (finite_range a).bddAbove ⟨k, rfl⟩
  rw [hM]
  have hlow : ∀ β > (0 : ℝ), a k ≤ Real.log (∑ i, Real.exp (β * a i)) / β := by
    intro β hβ
    rw [le_div_iff₀ hβ, ← Real.log_exp (a k * β)]
    apply Real.log_le_log (Real.exp_pos _)
    rw [mul_comm]
    exact Finset.single_le_sum (f := fun i ↦ Real.exp (β * a i)) (fun i _ ↦ (Real.exp_pos _).le)
      (Finset.mem_univ k)
  have hup : ∀ β > (0 : ℝ), Real.log (∑ i, Real.exp (β * a i)) / β ≤ a k + Real.log n / β := by
    intro β hβ
    have hsum : ∑ i, Real.exp (β * a i) ≤ n * Real.exp (β * a k) := by
      calc ∑ i, Real.exp (β * a i) ≤ ∑ _i : Fin n, Real.exp (β * a k) :=
            Finset.sum_le_sum fun i _ ↦ Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left (hk i (Finset.mem_univ _)) hβ.le)
        _ = n * Real.exp (β * a k) := by simp
    have hpos : 0 < ∑ i, Real.exp (β * a i) := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) hne
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hl := Real.log_le_log hpos hsum
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    rw [div_le_iff₀ hβ, add_mul, div_mul_cancel₀ _ hβ.ne']
    linarith
  have hlim : Tendsto (fun β : ℝ ↦ a k + Real.log n / β) atTop (𝓝 (a k)) := by
    have := (tendsto_const_nhds (x := a k)).add
      ((tendsto_const_nhds (x := Real.log n)).div_atTop tendsto_id)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (eventually_gt_atTop 0 |>.mono hlow) (eventually_gt_atTop 0 |>.mono hup)

/-- GAPS 107.30, finite-width tangent-kernel training dynamics for a differentiable model. -/
theorem hasDerivAt_predictions_of_gradient_flow {p n : ℕ} (_hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n))
    (theta : ℝ → EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (D : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : HasFDerivAt f D (theta t))
    (hflow : HasDerivAt theta (-((n : ℝ)⁻¹) • D.adjoint (f (theta t) - y)) t) :
    HasDerivAt (f ∘ theta) (-((n : ℝ)⁻¹) • D (D.adjoint (f (theta t) - y))) t := by
  simpa only [map_smul] using hf.comp_hasDerivAt t hflow

/-- GAPS 107.31, the underparameterized ridgeless risk with Gaussian noise. -/
theorem ridgeless_gaussian_risk_eq {n p : ℕ} (hn : p + 1 < n)
    (beta : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0) :
    let P := (Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)));
    let A := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ Matrix.of (fun i j ↦ x i j);
    let fit := fun z : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin n) ↦
      Matrix.toEuclideanLin (𝕜 := ℝ) (((A z.1).transpose) * A z.1)⁻¹
        (Matrix.toEuclideanLin (𝕜 := ℝ) ((A z.1).transpose)
          (Matrix.toEuclideanLin (𝕜 := ℝ) (A z.1) beta + Real.sqrt v • z.2));
    (∫ z, ‖fit z - beta‖ ^ 2 ∂P) = (v : ℝ) * p / (n - p - 1 : ℕ) := by
  sorry

/-- GAPS 107.40, least-squares gradient descent and the preserved nullspace component. -/
theorem tendsto_least_squares_gradient_descent {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (theta₀ : EuclideanSpace ℝ (Fin p))
    (eta : ℝ) (he : 0 < eta) (hstep : eta * ‖A‖ ^ 2 < 2) :
    let update := fun x ↦ x - eta • A.adjoint (A x - y);
    ∃ thetaStar, A.adjoint (A thetaStar - y) = 0 ∧
      thetaStar - theta₀ ∈ LinearMap.range A.adjoint.toLinearMap ∧
      Tendsto (fun t : ℕ ↦ update^[t] theta₀) atTop (𝓝 thetaStar) := by
  sorry


end CKSD
