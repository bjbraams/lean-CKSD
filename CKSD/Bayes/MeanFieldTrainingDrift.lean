module

public import CKSD.Bayes.MeanFieldCore
public import CKSD.Bayes.MeanFieldPathLaws
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein
public import Mathlib.Analysis.Normed.Module.HahnBanach
/-!
# Bounded Lipschitz mean-field training velocities

Scalar Kantorovich-Rubinstein weak duality, applied to a supporting functional,
bounds vector-valued differences of expectations in first Wasserstein distance.
A bounded Lipschitz interaction therefore gives a bounded drift Lipschitz in both
position and law. These estimates supply the training-velocity hypotheses in
GAPS 104.53 and the characteristic-flow argument for mean-field equations.

Pinned TauCeti supplies Wasserstein weak duality and finite-moment criteria;
Mathlib supplies Hahn-Banach and Bochner integration. The law-Lipschitz estimate
is the coupling estimate used in Carmona and Delarue, *Probabilistic Theory of
Mean Field Games with Applications*, Volume I, Chapter 6.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace CKSD
/-- A vector-valued Lipschitz expectation is Lipschitz in the first Wasserstein distance. -/
theorem norm_integral_sub_integral_le_mul_wasserstein_e_dist_one
    {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {K : ℝ≥0} (f : X → F) (hf : LipschitzWith K f)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (hW : TauCeti.wassersteinEDist 1 μ ν ≠ ∞) :
    ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤ (K:ℝ) * (TauCeti.wassersteinEDist 1 μ ν).toReal := by
  obtain ⟨g, hg, hgv⟩ := exists_dual_vector'' ℝ ((∫ x, f x ∂μ) - ∫ x, f x ∂ν)
  by_cases hK : K = 0
  · subst K
    have hc (x y : X) : f x = f y := dist_eq_zero.mp (by simpa using hf.dist_le_mul x y)
    let x₀ : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
    have heq : f = fun _ ↦ f x₀ := funext fun x ↦ hc x x₀
    rw [heq]
    simp
  have hKpos : 0 < (K:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
  have hgl : LipschitzWith 1 g := g.lipschitzWith.weaken (by exact_mod_cast hg)
  have hgf : LipschitzWith K (fun x ↦ g (f x)) := by simpa only [one_mul, Function.comp_def] using hgl.comp hf
  have hs : LipschitzWith 1 (fun x ↦ (K:ℝ)⁻¹ * g (f x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, one_mul, NNReal.coe_one]
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hKpos)]
    have h := hgf.dist_le_mul x y
    rw [Real.dist_eq] at h
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hKpos.le)).trans_eq
      (by field_simp)
  have h := TauCeti.ofReal_integral_sub_integral_le_wassersteinEDist_one hs
    ((g.integrable_comp hμ).const_mul _) ((g.integrable_comp hν).const_mul _)
  have hr : (K:ℝ)⁻¹ * ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ ≤
      (TauCeti.wassersteinEDist 1 μ ν).toReal := by
    have hh := ENNReal.toReal_mono hW h
    rw [integral_const_mul, integral_const_mul, g.integral_comp_comm hμ,
      g.integral_comp_comm hν, ← mul_sub, ← map_sub, hgv] at hh
    simpa only [RCLike.ofReal_real_eq_id, id_eq,
      ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hKpos.le) (norm_nonneg _))] using hh
  have hr' : ‖(∫ x, f x ∂μ) - ∫ x, f x ∂ν‖ / (K:ℝ) ≤
      (TauCeti.wassersteinEDist 1 μ ν).toReal := by
    simpa only [div_eq_mul_inv, mul_comm] using hr
  simpa only [mul_comm] using (div_le_iff₀ hKpos).mp hr' 
/-- Velocity `-∇_θΨ(θ; ρ) = ∇V(θ) - ∫ ∇_θU(θ, θ') ρ(dθ')` of the mean-field gradient flow. -/
def meanFieldVelocity {p : ℕ} (gradV : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (gradU : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (ρ : Measure (EuclideanSpace ℝ (Fin p))) (θ : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  gradV θ - ∫ θ', gradU θ θ' ∂ρ
section Training
variable {p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin p)
/-- Fixing the first interaction argument preserves its Lipschitz bound in the second. -/
theorem lipschitz_with_mean_field_interaction (gradU : E → E → E) (L : ℝ)
    (hUl : ∀ θ θ' η η', ‖gradU θ θ' - gradU η η'‖ ≤ L * (‖θ - η‖ + ‖θ' - η'‖))
    (θ : E) : LipschitzWith (Real.toNNReal L) (gradU θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have h := hUl θ x θ y
  simp only [sub_self, norm_zero, zero_add] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
/-- Bounded Lipschitz interaction fields are integrable against any finite measure. -/
theorem integrable_mean_field_interaction (gradU : E → E → E) (B L : ℝ)
    (hUb : ∀ θ θ', ‖gradU θ θ'‖ ≤ B)
    (hUl : ∀ θ θ' η η', ‖gradU θ θ' - gradU η η'‖ ≤ L * (‖θ - η‖ + ‖θ' - η'‖))
    (μ : Measure E) [IsFiniteMeasure μ] (θ : E) : Integrable (gradU θ) μ := by
  exact Integrable.of_bound
    (lipschitz_with_mean_field_interaction gradU L hUl θ).continuous.aestronglyMeasurable B
    (ae_of_all _ (hUb θ))
/-- Mean-field velocities are bounded uniformly over probability laws. -/
theorem norm_mean_field_velocity_le (gradV : E → E) (gradU : E → E → E) (B : ℝ)
    (hVb : ∀ θ, ‖gradV θ‖ ≤ B) (hUb : ∀ θ θ', ‖gradU θ θ'‖ ≤ B)
    (μ : Measure E) [IsProbabilityMeasure μ] (θ : E) :
    ‖meanFieldVelocity gradV gradU μ θ‖ ≤ 2 * B := by
  have hi : ‖∫ θ', gradU θ θ' ∂μ‖ ≤ B :=
    by simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (hUb θ))
  exact (norm_sub_le _ _).trans (by linarith [hVb θ])
/-- Mean-field training is Lipschitz in position and first-Wasserstein law. -/
theorem is_wasserstein_lipschitz_drift_mean_field_velocity
    (gradV : E → E) (gradU : E → E → E) (B L : ℝ)
    (_hVb : ∀ θ, ‖gradV θ‖ ≤ B) (hUb : ∀ θ θ', ‖gradU θ θ'‖ ≤ B)
    (hVl : ∀ θ η, ‖gradV θ - gradV η‖ ≤ L * ‖θ - η‖)
    (hUl : ∀ θ θ' η η', ‖gradU θ θ' - gradU η η'‖ ≤ L * (‖θ - η‖ + ‖θ' - η'‖)) :
    IsWassersteinLipschitzDrift (fun θ μ ↦ meanFieldVelocity gradV gradU μ θ)
      (2 * (Real.toNNReal L : ℝ)) := by
  intro x y μ ν hμp hνp hμ hν
  let := hμp
  let := hνp
  let K : ℝ≥0 := Real.toNNReal L
  have hLK : L ≤ (K:ℝ) := Real.le_coe_toNNReal L
  have hμid : Integrable (id : E → E) μ :=
    hμ.mono' aestronglyMeasurable_id (ae_of_all _ fun _ ↦ le_rfl)
  have hνid : Integrable (id : E → E) ν :=
    hν.mono' aestronglyMeasurable_id (ae_of_all _ fun _ ↦ le_rfl)
  have hμmom : TauCeti.HasFiniteMoment 1 μ := by
    simpa only [Measure.map_id] using has_finite_moment_one_map_of_integrable μ id measurable_id hμid
  have hνmom : TauCeti.HasFiniteMoment 1 ν := by
    simpa only [Measure.map_id] using has_finite_moment_one_map_of_integrable ν id measurable_id hνid
  have hW := (TauCeti.hasFiniteMoment_iff_wassersteinEDist_ne_top_of_hasFiniteMoment
    measurable_edist hμmom).mp hνmom
  have hi (z : E) (η : Measure E) [IsFiniteMeasure η] : Integrable (gradU z) η :=
    integrable_mean_field_interaction gradU B L hUb hUl η z
  have hsame : ‖(∫ z, gradU x z ∂μ) - ∫ z, gradU y z ∂μ‖ ≤ (K:ℝ)*‖x-y‖ := by
    rw [← integral_sub (hi x μ) (hi y μ)]
    have hb : ∀ᵐ z ∂μ, ‖gradU x z - gradU y z‖ ≤ (K:ℝ)*‖x-y‖ := by
      refine ae_of_all _ fun z ↦ ?_
      have h := hUl x z y z
      simp only [sub_self, norm_zero, add_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_right hLK (norm_nonneg _))
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb
  have hlaw : ‖(∫ z, gradU y z ∂μ) - ∫ z, gradU y z ∂ν‖ ≤
      (K:ℝ) * (TauCeti.wassersteinEDist 1 μ ν).toReal :=
    norm_integral_sub_integral_le_mul_wasserstein_e_dist_one μ ν (gradU y)
      (lipschitz_with_mean_field_interaction gradU L hUl y) (hi y μ) (hi y ν) hW
  have hV : ‖gradV x-gradV y‖ ≤ (K:ℝ)*‖x-y‖ :=
    (hVl x y).trans (mul_le_mul_of_nonneg_right hLK (norm_nonneg _))
  have heq : meanFieldVelocity gradV gradU μ x - meanFieldVelocity gradV gradU ν y =
      (gradV x-gradV y) - (((∫ z, gradU x z ∂μ) - ∫ z, gradU y z ∂μ) +
        ((∫ z, gradU y z ∂μ) - ∫ z, gradU y z ∂ν)) := by
    dsimp [meanFieldVelocity]
    abel
  rw [heq]
  calc _ ≤ ‖gradV x-gradV y‖ +
        (‖(∫ z, gradU x z ∂μ) - ∫ z, gradU y z ∂μ‖ +
          ‖(∫ z, gradU y z ∂μ) - ∫ z, gradU y z ∂ν‖) :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := by
      dsimp only [K] at hsame hlaw hV ⊢
      nlinarith [(Real.toNNReal L).coe_nonneg,
        ENNReal.toReal_nonneg (a := TauCeti.wassersteinEDist 1 μ ν)]
end Training
end CKSD
