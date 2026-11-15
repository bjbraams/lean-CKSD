module

public import CKSD.Bayes.Basic

/-!
# The leapfrog integrator of Hamiltonian Monte Carlo

The leapfrog step `CKSD.leapfrogStep` on phase space `ℝᵈ × ℝᵈ` is the composition of two
momentum kicks and a position drift, each a shear.

## Main results

* `CKSD.measurePreserving_leapfrogStep`, `CKSD.measurePreserving_leapfrogStep_iterate`: one and
  iterated leapfrog steps preserve Lebesgue measure (GAPS 104.35).
* `CKSD.leapfrogStep_momentumFlip_leapfrogStep`, `CKSD.leapfrogStep_iterate_reversible`: leapfrog
  steps are reversible under momentum flip (GAPS 104.35).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

section Leapfrog

variable {d : ℕ}

/-- A single leapfrog step preserves Lebesgue measure on phase space: it is the composition of
two momentum kicks and a position drift, each a shear. -/
theorem measurePreserving_leapfrogStep
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (leapfrogStep g h) volume volume := by
  let E := EuclideanSpace ℝ (Fin d)
  let K := fun z : E × E ↦ (z.1, z.2 - (h / 2) • g z.1)
  let D := fun z : E × E ↦ (z.1 + h • z.2, z.2)
  -- Each kick is a translation in momentum at a fixed position.
  have hK : MeasurePreserving K volume volume := by
    rw [Measure.volume_eq_prod E E]
    apply (MeasurePreserving.id (volume : Measure E)).skew_product
      (g := fun x p ↦ p - (h / 2) • g x)
    · exact measurable_snd.sub ((hg.comp measurable_fst).const_smul (h / 2))
    · exact ae_of_all _ fun x ↦ by
        simpa only [sub_eq_add_neg, neg_smul] using
          (measurePreserving_add_right (volume : Measure E) (-(h / 2) • g x)).map_eq
  -- Interchanging position and momentum turns the drift into another translation.
  have hDskew : MeasurePreserving (fun z : E × E ↦ (z.1, z.2 + h • z.1))
      volume volume := by
    rw [Measure.volume_eq_prod E E]
    apply (MeasurePreserving.id (volume : Measure E)).skew_product
      (g := fun x p ↦ p + h • x)
    · exact measurable_snd.add (measurable_fst.const_smul h)
    · exact ae_of_all _ fun x ↦
        (measurePreserving_add_right (volume : Measure E) (h • x)).map_eq
  have hswap : MeasurePreserving (Prod.swap : E × E → E × E) volume volume := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.measurePreserving_swap
  have hD : MeasurePreserving D volume volume := hswap.comp (hDskew.comp hswap)
  have hstep : leapfrogStep g h = K ∘ D ∘ K := funext fun z ↦ by rw [leapfrogStep_apply]; rfl
  rw [hstep]
  exact hK.comp (hD.comp hK)

/-- GAPS 104.35: repeated leapfrog steps preserve Lebesgue measure on phase space. -/
theorem measurePreserving_leapfrogStep_iterate
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g) (h : ℝ)
    (L : ℕ) : MeasurePreserving ((leapfrogStep g h)^[L]) volume volume :=
  (measurePreserving_leapfrogStep g hg h).iterate L

/-- A single leapfrog step is reversible: flipping the momentum after a step and stepping again
returns the flipped initial point. -/
theorem leapfrogStep_momentumFlip_leapfrogStep
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    leapfrogStep g h (momentumFlip (leapfrogStep g h z)) = momentumFlip z := by
  have hp : -(z.2 - (h / 2) • g z.1 -
      (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1))) -
      (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1)) =
      -(z.2 - (h / 2) • g z.1) := by abel
  have hx : z.1 + h • (z.2 - (h / 2) • g z.1) +
      h • (-(z.2 - (h / 2) • g z.1)) = z.1 := by
    simp only [smul_neg]
    abel
  simp only [leapfrogStep_apply, momentumFlip_apply]
  rw [hp, hx]
  congr 1
  abel

/-- GAPS 104.35: repeated leapfrog steps are reversible under momentum flip,
`Φᴸ ∘ R ∘ Φᴸ = R` for `R (x, p) = (x, -p)`. -/
theorem leapfrogStep_iterate_reversible
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ) (L : ℕ)
    (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    (leapfrogStep g h)^[L] (momentumFlip ((leapfrogStep g h)^[L] z)) = momentumFlip z := by
  induction L generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih,
        leapfrogStep_momentumFlip_leapfrogStep]

end Leapfrog

end CKSD
