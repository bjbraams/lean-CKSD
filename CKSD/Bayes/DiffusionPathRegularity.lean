module

public import Mathlib.Analysis.Calculus.Deriv.Basic
/-!
# One-sided differential equations and path continuity

Right derivatives alone do not express the usual continuous-path ODE solution convention:
a right-continuous step has zero right derivative even at its jump. The examples here isolate
that path-regularity obstruction. They are not a formal counterexample to an entire diffusion
or Fokker–Planck theorem. They explain the continuous-trajectory hypothesis in the
probability-flow representation, GAPS 104.63.

The proofs use Mathlib's derivative locality and one-sided neighborhood filters.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace CKSD
/-- A right-continuous step has zero right derivative everywhere, including at its jump. -/
theorem has_deriv_within_at_right_step (a c t : ℝ) :
    HasDerivWithinAt (fun s : ℝ ↦ if s < a then 0 else c) 0 (Ici t) t := by
  by_cases ht : t < a
  · apply (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
      simp only [mem_Iio] at hs
      simp only [hs, ite_true]
    · simp only [ht, ite_true]
  · apply (hasDerivWithinAt_const t (Ici t) c).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_Ici] at hs
      simp only [not_lt.mpr ((not_lt.mp ht).trans hs), ite_false]
    · simp only [ht, ite_false]
/-- Zero right derivatives and an initial condition do not imply the constant ODE solution. -/
theorem exists_nonconstant_zero_right_derivative :
    ∃ z : ℝ → ℝ, z 0 = 0 ∧ (∀ t, HasDerivWithinAt z 0 (Ici t) t) ∧ z 1 ≠ 0 := by
  refine ⟨(fun t : ℝ ↦ if t < 1 then 0 else 1), by norm_num,
    (fun t ↦ has_deriv_within_at_right_step 1 1 t), by norm_num⟩
end CKSD
