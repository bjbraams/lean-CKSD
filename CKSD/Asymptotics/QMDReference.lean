module

public import CKSD.Asymptotics.Statistics

/-!
# Reference-measure degeneracy for quadratic-mean differentiability

`rn_deriv_count_eq_zero_of_no_atoms` shows that an atomless measure has chosen
Radon–Nikodym derivative zero relative to counting measure.
`has_quadratic_mean_deriv_at_of_rn_deriv_eq_zero` shows that the square-root-density
remainder then vanishes regardless of the prescribed derivative. These facts explain
why semiparametric results require a sigma-finite common dominating reference.

The proofs use Mathlib's `withDensity_rnDeriv_le` and Statlib's definition of QMD.
They do not assert a stochastic counterexample to a convolution theorem.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace CKSD

/-- Relative to counting measure, the chosen Radon–Nikodym derivative of an atomless law is
zero, even though every law is absolutely continuous with respect to counting measure. -/
theorem rn_deriv_count_eq_zero_of_no_atoms
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Measure X) [NullSingletonClass P] : P.rnDeriv Measure.count = 0 := by
  classical
  funext x
  have h := Measure.withDensity_rnDeriv_le P Measure.count {x}
  have hval : (Measure.count.withDensity (P.rnDeriv Measure.count)) {x} =
      P.rnDeriv Measure.count x := by
    rw [count_withDensity]
    rw [Measure.sum_apply _ (measurableSet_singleton x)]
    rw [tsum_eq_single x]
    · simp [Measure.dirac_apply']
    · intro b hb
      simp [Measure.dirac_apply', hb]
  rw [hval, measure_singleton] at h
  exact le_antisymm h zero_le

/-- A square-root Radon–Nikodym remainder is vacuous if all chosen reference densities vanish.
Sigma-finite domination rules out this degeneracy for probability path laws. -/
theorem has_quadratic_mean_deriv_at_of_rn_deriv_eq_zero
    {X E : Type*} [MeasurableSpace X] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (P : E → Measure X) (ν : Measure X) (θ : E)
    (A : E →ₗ[ℝ] Lp ℝ 2 (P θ)) (hzero : ∀ t, (P t).rnDeriv ν = 0) :
    HasQuadraticMeanDerivAt P ν θ A := by
  unfold HasQuadraticMeanDerivAt QMD.HasQuadraticMeanDerivWithinAt
  simp only [hzero, Pi.zero_apply, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero, sub_zero,
    lpNorm_fun_zero]
  exact Asymptotics.IsLittleOTVS.zero (𝕜 := ℝ) (E := ℝ) (fun y : E => y - θ) (𝓝[Set.univ] θ)

end CKSD
