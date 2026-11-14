module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.BoltzmannEntropy
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.InformationTheory.KullbackLeibler.Convex
public import Mathlib.Topology.Instances.EReal.Lemmas
/-!
# Quadratic-moment control of the JKO free energy

Gaussian change of reference expresses Boltzmann entropy as relative entropy plus a quadratic
moment correction. For a nonnegative potential this gives a finite lower bound on the free
energy at every P2 law and characterizes its finite domain. Bounded Wasserstein families have
uniformly bounded quadratic moments. An extended-real small-tilt lemma supports narrow lower
semicontinuity without incorrectly treating bounded Wasserstein sets as compact.

Pinned TauCeti supplies Gaussian entropy tilting, moment identities and Wasserstein spaces;
Mathlib supplies Gaussian integrability and extended-real order topology. These are the
Euclidean moment-compensation ingredients for the JKO direct method, GAPS 104.43; see
Santambrogio, *Optimal Transport for Applied Mathematicians*, Section 8.3, and Villani,
*Optimal Transport: Old and New*, Chapter 23 (the unbounded-domain estimates require the
quadratic compensation used here).
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The underlying measure of a law in the Wasserstein space `P₂(ℝᵈ)`. -/
def wassersteinLaw {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))

/-- Free energy `∫ ρ log ρ + ∫ V dρ` on the Wasserstein space, with the entropy relative to
Lebesgue measure; it is `⊤` for laws without a density. -/
def jkoFreeEnergy {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) : EReal :=
  TauCeti.boltzmannEntropy volume (wassersteinLaw ν) + TauCeti.potentialEnergy V (wassersteinLaw ν)

/-- Real Lebesgue density of the absolutely continuous part of a Wasserstein law.
This represents the whole law when that law is absolutely continuous with respect to volume. -/
def wassersteinDensity {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((wassersteinLaw ν).rnDeriv volume x).toReal

/-- A law in the quadratic Wasserstein space is a probability measure. -/
instance isProbabilityMeasure_wassersteinLaw (μ : TauCeti.WassersteinSpace 2 E) :
    IsProbabilityMeasure (wassersteinLaw μ) := by
  change IsProbabilityMeasure (((μ : ProbabilityMeasure E) : Measure E))
  infer_instance
/-- Every centered Gaussian envelope on Euclidean space is integrable. -/
theorem integrable_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E ↦ Real.exp (-(a*‖x‖^2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (a : ℂ)) (by simpa using ha) 0 0
  apply h.norm.congr
  exact ae_of_all _ fun x ↦ by
    dsimp only
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_pow]

/-- A quadratic change of reference identifies the free energy with Gaussian relative entropy
plus potential energy and an explicit second-moment correction. -/
theorem jko_free_energy_eq_kl_div_gaussian_add
    (V : E → ℝ) {a : ℝ} (ha : 0 < a) (μ : TauCeti.WassersteinSpace 2 E) :
    jkoFreeEnergy V μ =
      (klDiv (wassersteinLaw μ) (volume.tilted (fun x : E ↦ -(a*‖x‖^2))) : EReal) +
        TauCeti.potentialEnergy V (wassersteinLaw μ) +
          ((-a*(∫ x, ‖x‖^2 ∂wassersteinLaw μ)-
            Real.log (∫ x : E, Real.exp (-(a*‖x‖^2))) : ℝ) : EReal) := by
  have h := TauCeti.WassersteinSpace.boltzmannEntropy_eq_klDiv_tilted_add (p := 2)
    (m := (volume : Measure E)) (a := a) (x₀ := (0:E)) (by norm_num)
    (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two,dist_zero_right] using
      integrable_exp_neg_mul_norm_sq (d := d) ha) μ
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,dist_zero_right] at h
  change TauCeti.boltzmannEntropy volume (wassersteinLaw μ) = _ at h
  rw [jkoFreeEnergy, h]
  change (klDiv _ _ : EReal)+((- (a*_) - _ : ℝ) : EReal)+_ = _
  rw [neg_mul]
  ac_rfl

/-- A nonnegative potential gives the usual quadratic Gaussian lower bound on the free energy. -/
theorem jko_free_energy_gaussian_lower_bound
    (V : E → ℝ) (hV : ∀ x, 0 ≤ V x) {a : ℝ} (ha : 0 < a)
    (μ : TauCeti.WassersteinSpace 2 E) :
    (((-a*(∫ x, ‖x‖^2 ∂wassersteinLaw μ)-
      Real.log (∫ x : E, Real.exp (-(a*‖x‖^2)))) : ℝ) : EReal) ≤ jkoFreeEnergy V μ := by
  have hp : 0 ≤ TauCeti.potentialEnergy V (wassersteinLaw μ) := by
    rw [TauCeti.potentialEnergy_of_nonneg_ae (ae_of_all _ hV)]
    exact EReal.coe_ennreal_nonneg _
  rw [jko_free_energy_eq_kl_div_gaussian_add V ha μ]
  have h0 : (0 : EReal) ≤ (klDiv (wassersteinLaw μ)
    (volume.tilted (fun x : E ↦ -(a*‖x‖^2))) : EReal) := EReal.coe_ennreal_nonneg _
  simpa only [zero_add, add_zero, add_comm] using add_le_add_right (add_nonneg h0 hp)
    (((-a*(∫ x, ‖x‖^2 ∂wassersteinLaw μ)-Real.log (∫ x : E, Real.exp (-(a*‖x‖^2)))) : ℝ) : EReal)

/-- A nonnegative-potential free energy has no minus-infinite values on P2. -/
theorem jko_free_energy_ne_bot (V : E → ℝ) (hV : ∀ x, 0 ≤ V x)
    (μ : TauCeti.WassersteinSpace 2 E) : jkoFreeEnergy V μ ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (jko_free_energy_gaussian_lower_bound V hV zero_lt_one μ)
/-- Lower semicontinuity after every positive quadratic tilt implies lower semicontinuity
along a sequence with bounded quadratic moments. -/
theorem ereal_le_liminf_of_positive_tilts {F : EReal} {u : ℕ → EReal} {m M : ℝ}
    {mn : ℕ → ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M) (hmn : ∀ n, mn n ≤ M)
    (htilt : ∀ a > 0, F + ((a*m : ℝ) : EReal) ≤
      liminf (fun n ↦ u n+((a*mn n : ℝ) : EReal)) atTop) : F ≤ liminf u atTop := by
  apply le_of_forall_lt_imp_le_of_dense
  intro s hs
  obtain ⟨r, hsr, hrF⟩ := EReal.exists_between_coe_real hs
  obtain ⟨R, hrR, hRF⟩ := EReal.exists_between_coe_real hrF
  have hgap : 0 < R-r := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hrR)
  let a : ℝ := (R-r)/(M+1)
  have ha : 0 < a := div_pos hgap (by linarith)
  have hid : a*(M+1)=R-r := by dsimp [a]; exact div_mul_cancel₀ _ (by linarith)
  have har : r+a*M < R := by nlinarith
  have hcomp : ((r+a*M : ℝ) : EReal) < F + ((a*m : ℝ) : EReal) :=
    ((EReal.coe_lt_coe_iff.mpr har).trans hRF).trans_le
      (le_add_of_nonneg_right (by exact_mod_cast mul_nonneg ha.le hm))
  have hev := eventually_lt_of_lt_liminf (hcomp.trans_le (htilt a ha))
  have hev' : ∀ᶠ n in atTop, (r : EReal) ≤ u n := by
    filter_upwards [hev] with n hn
    have ht : ((r+a*M : ℝ) : EReal) < u n+((a*M : ℝ) : EReal) :=
      hn.trans_le (by
        apply add_le_add le_rfl
        exact_mod_cast mul_le_mul_of_nonneg_left (hmn n) ha.le)
    have hh : (r : EReal)+((a*M : ℝ) : EReal) ≤ u n+((a*M : ℝ) : EReal) := by
      simpa only [EReal.coe_add] using ht.le
    exact (EReal.addLECancellable_coe (a*M)).add_le_add_iff_right.mp hh
  exact hsr.le.trans (le_liminf_of_le (h := hev'))
/-- Finite free energy is equivalent to finite Gaussian relative entropy and potential energy. -/
theorem jko_free_energy_ne_top_iff_kl_div_gaussian_and_potential
    (V : E → ℝ) (hV : ∀ x, 0 ≤ V x) {a : ℝ} (ha : 0 < a)
    (μ : TauCeti.WassersteinSpace 2 E) :
    jkoFreeEnergy V μ ≠ ⊤ ↔
      klDiv (wassersteinLaw μ) (volume.tilted (fun x : E ↦ -(a*‖x‖^2))) ≠ ∞ ∧
        TauCeti.potentialEnergy V (wassersteinLaw μ) ≠ ⊤ := by
  have hp : TauCeti.potentialEnergy V (wassersteinLaw μ) ≠ ⊥ := by
    rw [TauCeti.potentialEnergy_of_nonneg_ae (ae_of_all _ hV)]
    exact EReal.coe_ennreal_ne_bot _
  rw [jko_free_energy_eq_kl_div_gaussian_add V ha μ]
  simpa only [ne_eq,EReal.add_coe_eq_top_iff,EReal.coe_ennreal_eq_top_iff] using
    EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ennreal_ne_bot
      (klDiv (wassersteinLaw μ) (volume.tilted (fun x : E ↦ -(a*‖x‖^2))))) hp

/-- Finite free energy for a nonnegative continuous potential makes the potential integrable. -/
theorem integrable_potential_of_jko_free_energy_ne_top
    (V : E → ℝ) (hVc : Continuous V) (hV : ∀ x, 0 ≤ V x)
    (μ : TauCeti.WassersteinSpace 2 E) (hF : jkoFreeEnergy V μ ≠ ⊤) :
    Integrable V (wassersteinLaw μ) := by
  have hp := ((jko_free_energy_ne_top_iff_kl_div_gaussian_and_potential V hV zero_lt_one μ).1 hF).2
  apply (TauCeti.integrable_iff_potentialEnergy_ne_top_and_ne_bot hVc.aestronglyMeasurable).2
  refine ⟨hp, ?_⟩
  rw [TauCeti.potentialEnergy_of_nonneg_ae (ae_of_all _ hV)]
  exact EReal.coe_ennreal_ne_bot _

/-- The second moment is the square of the quadratic Wasserstein distance from the origin. -/
theorem integral_norm_sq_eq_wasserstein_dirac_sq (μ : TauCeti.WassersteinSpace 2 E) :
    (∫ x, ‖x‖^2 ∂wassersteinLaw μ) =
      (TauCeti.wassersteinEDist 2 (Measure.dirac (0:E)) (wassersteinLaw μ)).toReal^2 := by
  have hi : Integrable (fun x : E ↦ ‖x‖^2) (wassersteinLaw μ) := by
    change Integrable (fun x : E ↦ ‖x‖^2) ((μ : ProbabilityMeasure E) : Measure E)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,dist_zero_right] using
      TauCeti.WassersteinSpace.integrable_dist_rpow (p := 2) (by norm_num) μ (0:E)
  have hp := TauCeti.eLpNorm_rpow_eq_lintegral (p := (2 : ℝ≥0∞))
    (f := fun x : E ↦ edist (0:E) x) (μ := wassersteinLaw μ) (by norm_num) (by norm_num)
    (by fun_prop)
  norm_num only [ENNReal.toReal_ofNat,ENNReal.rpow_two,enorm_eq_self] at hp
  have heq : (TauCeti.wassersteinEDist 2 (Measure.dirac (0:E)) (wassersteinLaw μ))^2 =
      ENNReal.ofReal (∫ x, ‖x‖^2 ∂wassersteinLaw μ) := by
    rw [TauCeti.wassersteinEDist_dirac_left measurable_edist]
    rw [hp, ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _)]
    apply lintegral_congr
    intro x
    simp only [edist_dist,dist_zero_left,ENNReal.ofReal_pow (norm_nonneg _)]
  have ht := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)] at ht
  exact ht.symm

/-- A Wasserstein-bounded sequence has uniformly bounded second moments. -/
theorem exists_integral_norm_sq_le_of_is_bounded (v : ℕ → TauCeti.WassersteinSpace 2 E)
    (hv : Bornology.IsBounded (range v)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, (∫ x, ‖x‖^2 ∂wassersteinLaw (v n)) ≤ B := by
  have hmem : TauCeti.HasFiniteMoment 2 (diracProba (0:E) : Measure E) := by
    change TauCeti.HasFiniteMoment 2 (Measure.dirac (0:E))
    exact TauCeti.hasFiniteMoment_dirac 2 (0:E)
  let δ : TauCeti.WassersteinSpace 2 E := TauCeti.WassersteinSpace.mk (diracProba (0:E)) hmem
  have hδ : wassersteinLaw δ = Measure.dirac (0:E) := by
    exact congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk (diracProba (0:E)) hmem)
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall δ).1 hv
  refine ⟨R^2,sq_nonneg _,fun n ↦ ?_⟩
  rw [integral_norm_sq_eq_wasserstein_dirac_sq, ← hδ]
  change (TauCeti.wassersteinEDist 2 ((δ : ProbabilityMeasure E) : Measure E)
    ((v n : ProbabilityMeasure E) : Measure E)).toReal^2 ≤ R^2
  rw [← TauCeti.WassersteinSpace.dist_def]
  exact pow_le_pow_left₀ (dist_nonneg (x := δ) (y := v n))
    (by simpa only [dist_comm] using Metric.mem_closedBall.1 (hR (mem_range_self n))) 2
end CKSD
