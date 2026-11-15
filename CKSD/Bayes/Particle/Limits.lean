module

import CKSD.Bayes.Particle.UniformMoments
public import CKSD.Bayes.Particle.Filter
import CKSD.Bayes.Particle.EmpiricalMoments

/-!
# Uniform particle moment bounds

Uniform-in-time error bounds for the bootstrap particle filter under potential and transition
comparisons. Fixed-time semigroup and central limit results are reexported from
`CKSD.Bayes.Particle.LimitCore`.

Source: Del Moral, *Feynman–Kac Formulae*, Theorem 7.4.4, printed pages 244–246
(PDF pages 257–259 of the local 2004 copy); GAPS 104.60.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- GAPS 104.60: uniform-in-time `Lᵖ` particle error bound for a fixed mixing model.
The bound `C` is uniform in time, particle number, and test functions with oscillation at most
one. It is chosen after the model, so this formulation does not assert Del Moral's form
`c_p / (εM² εG)` with `c_p` depending only on `p`; the proof gives `C = 2 K_p / (εM⁴ εG²)`,
where `K_p` is the constant of the i.i.d. bound `CKSD.exists_iid_empirical_mean_lpNorm_bound`. -/
theorem exists_uniform_particle_moment_bound {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (εG εM : ℝ) (hG : εG ∈ Ioc 0 1) (hM : εM ∈ Ioc 0 1)
    (hpotential : ∀ n x y, εG * M.potential n y ≤ M.potential n x)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal εM * M.transition n y A ≤ M.transition n x A)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ N : ℕ, ∀ ξ : ℕ → Ω → Fin (N + 1) → X,
      IsBootstrapParticleSystem P M (N + 1) ξ → ∀ n : ℕ, ∀ f : X → ℝ, Measurable f →
      (∀ x y, |f x - f y| ≤ 1) →
      Real.sqrt (N + 1) * Real.rpow
        (∫ ω, |(∑ i, f (ξ n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n| ^ p ∂P) (1 / p) ≤ C := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨C, hC, hbound⟩ :=
      exists_uniform_particle_lpNorm_bound P M hG hM hpotential htransition p hp
  refine ⟨C, hC, fun N ξ hξ n f hf hosc ↦ ?_⟩
  have hFm : Measurable (fun ω ↦ (∑ i, f (ξ n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n) :=
    ((Finset.measurable_fun_sum _ fun i _ ↦
      hf.comp ((measurable_pi_apply i).comp (hξ.1 n))).div_const _).sub measurable_const
  have hLp : lpNorm (fun ω ↦ (∑ i, f (ξ n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n)
      (ENNReal.ofReal p) P ≤ C / Real.sqrt (N + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbound (N + 1) (by omega) ξ hξ n f hf hosc
  rw [lpNorm_ofReal_eq_integral_abs_rpow P hp0 hFm.aestronglyMeasurable] at hLp
  have hs : 0 < Real.sqrt (N + 1) := by positivity
  have h := mul_le_mul_of_nonneg_left hLp hs.le
  have hscale : Real.sqrt (N + 1) * (C / Real.sqrt (N + 1)) = C := by field_simp [hs.ne']
  rw [hscale] at h
  exact h

end CKSD
