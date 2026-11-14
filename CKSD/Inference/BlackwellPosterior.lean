module

public import CKSD.Inference.Factorization
public import CKSD.Inference.Model

/-!
# Compact likelihood-vector experiments

A finite family is dominated by its sum. Bounded versions of the corresponding
Radon–Nikodym densities define a statistic with values in a compact cube. On a
standard Borel observation space this statistic is sufficient, by the existing
Fisher–Neyman factorization theorem. These are the measurable reduction steps
for Blackwell comparison with a finite parameter set (GAPS 101.62).
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD

/-- The compact cube of bounded likelihood vectors. -/
abbrev finiteLikelihoodCube (Θ : Type*) := Icc (0 : Θ → ℝ) 1

/-- The likelihood cube is the order interval from zero to one. -/
theorem finite_likelihood_cube_def (Θ : Type*) :
    finiteLikelihoodCube Θ = Icc (0 : Θ → ℝ) 1 := rfl

/-- A likelihood vector belongs to the cube exactly when its coordinates lie in `[0, 1]`. -/
theorem mem_finite_likelihood_cube_iff {Θ : Type*} (u : Θ → ℝ) :
    u ∈ finiteLikelihoodCube Θ ↔ (∀ θ, 0 ≤ u θ) ∧ ∀ θ, u θ ≤ 1 := Iff.rfl

/-- The sum of a finite family of probability laws dominates every family member. -/
@[expose] def finiteDominatingMeasure {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) : Measure X := ∑ θ, P θ

/-- The dominating measure is the finite sum of the experiment laws. -/
theorem finite_dominating_measure_def {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) : finiteDominatingMeasure P = ∑ θ, P θ := rfl

/-- A finite dominating sum is finite whenever every component law is finite. -/
instance {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] :
    IsFiniteMeasure (finiteDominatingMeasure P) := by
  rw [finite_dominating_measure_def]
  infer_instance

/-- A finite family member is bounded above by the dominating sum. -/
theorem le_finite_dominating_measure {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) (θ : Θ) : P θ ≤ finiteDominatingMeasure P := by
  intro s
  rw [finite_dominating_measure_def]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.single_le_sum (f := fun θ' ↦ P θ' s) (fun _ _ ↦ zero_le) (Finset.mem_univ θ)

/-- Finite likelihood vectors use bounded versions of the Radon–Nikodym densities. -/
@[expose] def finiteLikelihoodMap {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) (x : X) : finiteLikelihoodCube Θ :=
  ⟨fun θ ↦ min 1 (((P θ).rnDeriv (finiteDominatingMeasure P) x).toReal),
    (fun _θ ↦ le_min zero_le_one ENNReal.toReal_nonneg), fun _θ ↦ min_le_left _ _⟩

/-- The likelihood vector consists of the Radon–Nikodym densities clamped above at one. -/
theorem finite_likelihood_map_def {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) (x : X) :
    (finiteLikelihoodMap P x).val =
      fun θ ↦ min 1 (((P θ).rnDeriv (finiteDominatingMeasure P) x).toReal) := rfl

/-- Each likelihood coordinate is the corresponding clamped density. -/
theorem finite_likelihood_map_apply {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) (x : X) (θ : Θ) :
    (finiteLikelihoodMap P x).val θ =
      min 1 (((P θ).rnDeriv (finiteDominatingMeasure P) x).toReal) := rfl

/-- The bounded likelihood vector is measurable. -/
theorem measurable_finite_likelihood_map {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) : Measurable (finiteLikelihoodMap P) := by
  apply Measurable.subtype_mk
  exact Measurable.of_eval fun θ ↦ measurable_const.min
    (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- A coordinate of the bounded likelihood vector is a density relative to the dominating sum. -/
theorem has_density_finite_likelihood_map {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (θ : Θ) :
    HasDensity (P θ) (finiteDominatingMeasure P) (fun x ↦ (finiteLikelihoodMap P x).val θ) := by
  have hm : Measurable (fun x ↦ (finiteLikelihoodMap P x).val θ) :=
    (measurable_pi_apply θ).comp (measurable_subtype_coe.comp (measurable_finite_likelihood_map P))
  refine ⟨hm, ae_of_all _ fun x ↦ (finiteLikelihoodMap P x).property.1 θ, ?_⟩
  have hd := le_finite_dominating_measure P θ
  rw [← Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hd)]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_le_one_of_le hd] with x hx
  have hreal : ((P θ).rnDeriv (finiteDominatingMeasure P) x).toReal ≤ 1 := by
    simpa only [Pi.one_apply, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hx
  -- Expand only the clamped coordinate after changing the reference density.
  rw [finite_likelihood_map_apply]
  change (P θ).rnDeriv (finiteDominatingMeasure P) x =
    ENNReal.ofReal (min 1 (((P θ).rnDeriv (finiteDominatingMeasure P) x).toReal))
  rw [min_eq_right hreal, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx)]

/-- In a standard Borel sample space, the finite likelihood vector is sufficient. -/
theorem is_sufficient_statistic_finite_likelihood_map
    {Θ X : Type*} [Fintype Θ] [Nonempty Θ] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] :
    IsSufficientStatistic P (finiteLikelihoodMap P) := by
  apply is_sufficient_statistic_of_factorization P (finiteDominatingMeasure P) (fun _ ↦ inferInstance)
    (fun θ x ↦ (finiteLikelihoodMap P x).val θ) (has_density_finite_likelihood_map P)
    (measurable_finite_likelihood_map P) (fun θ s ↦ s.val θ) (fun _ ↦ 1)
  · intro θ
    exact ⟨(measurable_pi_apply θ).comp measurable_subtype_coe, fun s ↦ s.property.1 θ⟩
  · intro θ
    exact ae_of_all _ fun x ↦ (mul_one _).symm

/-- Pushing a finite experiment to its likelihood cube expresses each law as a coordinate tilt
of the pushed-forward dominating sum. -/
theorem map_finite_likelihood_eq_with_density
    {Θ X : Type*} [Fintype Θ] [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (θ : Θ) :
    (P θ).map (finiteLikelihoodMap P) =
      ((finiteDominatingMeasure P).map (finiteLikelihoodMap P)).withDensity
        (fun z ↦ ENNReal.ofReal (z.val θ)) := by
  let g : finiteLikelihoodCube Θ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (z.val θ)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((measurable_pi_apply θ).comp measurable_subtype_coe)
  calc
    _ = ((finiteDominatingMeasure P).withDensity (g ∘ finiteLikelihoodMap P)).map
        (finiteLikelihoodMap P) :=
      congrArg (Measure.map (finiteLikelihoodMap P)) (has_density_finite_likelihood_map P θ).2.2
    _ = _ := map_with_density_comp _ (measurable_finite_likelihood_map P) hg

/-- A standard Borel finite experiment can be reconstructed by one Markov kernel from its
bounded likelihood vector. -/
theorem is_garbling_of_finite_likelihood_map
    {Θ X : Type*} [Fintype Θ] [Nonempty Θ] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] :
    IsGarbling (fun θ ↦ (P θ).map (finiteLikelihoodMap P)) P := by
  obtain ⟨_, K, hK, h⟩ := is_sufficient_statistic_finite_likelihood_map P
  have := hK
  refine ⟨K, hK, fun θ ↦ ?_⟩
  have he := congrArg (fun m : Measure (finiteLikelihoodCube Θ × X) ↦ m.map Prod.snd) (h θ)
  have hprod : Measurable (fun x ↦ (finiteLikelihoodMap P x, x)) :=
    (measurable_finite_likelihood_map P).prodMk measurable_id
  rw [Measure.map_map measurable_snd hprod] at he
  have hs : Prod.snd ∘ (fun x ↦ (finiteLikelihoodMap P x, x)) = id := rfl
  rw [hs, Measure.map_id] at he
  -- The mapped second coordinate is the composition-product marginal.
  change P θ = (((P θ).map (finiteLikelihoodMap P)) ⊗ₘ K).snd at he
  rw [Measure.snd_compProd] at he
  exact he

end CKSD
