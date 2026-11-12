module
public import CKSD.Bayes.JKOEnergy
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Resolvent
/-!
# Existence of every JKO step on Euclidean space

For continuous nonnegative potentials, free energy is narrowly lower semicontinuous along
quadratically Wasserstein-bounded sequences. The proof uses small positive Gaussian tilts,
relative entropy lower semicontinuity and a uniform moment bound. Gaussian moment compensation
also bounds a Moreau envelope below at a Dirac law for every positive step. Pinned TauCeti's
proper-space direct method therefore yields a minimizer for every positive JKO step.

No convexity of the potential or global lower bound on Boltzmann entropy is required.
Mathlib supplies extended-real topology and integration. Pinned TauCeti supplies narrow entropy
and potential lower semicontinuity and the abstract resolvent theorem. This is the discrete
existence part of GAPS 104.43, using the moment-compensated direct method for the whole Euclidean
space rather than the compact-domain simplification in Santambrogio, Section 8.3.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Adding the Gaussian quadratic correction leaves a narrowly lower-semicontinuous entropy
and nonnegative potential, up to a finite normalization constant. -/
theorem jkoFreeEnergy_add_quadratic_eq (V : E → ℝ) {a : ℝ} (ha : 0<a)
    (μ : TauCeti.WassersteinSpace 2 E) :
    jkoFreeEnergy V μ+((a*(∫ x,‖x‖^2 ∂wassersteinLaw μ) : ℝ) : EReal) =
      (klDiv (wassersteinLaw μ) (volume.tilted (fun x : E ↦ -(a*‖x‖^2))) : EReal) +
        TauCeti.potentialEnergy V (wassersteinLaw μ)+
          ((-Real.log (∫ x : E,Real.exp (-(a*‖x‖^2))) : ℝ) : EReal) := by
  rw [jkoFreeEnergy_eq_klDiv_gaussian_add V ha μ,add_assoc,← EReal.coe_add]
  congr 1
  congr 1
  ring

/-- The free energy is narrowly lower semicontinuous along any Wasserstein-bounded sequence. -/
theorem jkoFreeEnergy_le_liminf_of_isBounded
    (V : E → ℝ) (hVc : Continuous V) (hV : ∀ x,0≤V x)
    {u : ℕ → TauCeti.WassersteinSpace 2 E} {ν : TauCeti.WassersteinSpace 2 E}
    (hu : Bornology.IsBounded (range u))
    (hlim : Tendsto (fun n ↦ (u n : ProbabilityMeasure E)) atTop (𝓝 (ν : ProbabilityMeasure E))) :
    jkoFreeEnergy V ν ≤ liminf (fun n ↦ jkoFreeEnergy V (u n)) atTop := by
  obtain ⟨B,hB,hbound⟩ := exists_integral_norm_sq_le_of_isBounded u hu
  apply ereal_le_liminf_of_positive_tilts
    (mn := fun n ↦ ∫ x,‖x‖^2 ∂wassersteinLaw (u n))
    (m := ∫ x,‖x‖^2 ∂wassersteinLaw ν)
    (integral_nonneg fun _ ↦ sq_nonneg _) hB hbound
  intro a ha
  let R : ProbabilityMeasure E := ⟨volume.tilted (fun x : E ↦ -(a*‖x‖^2)),
    isProbabilityMeasure_tilted (integrable_exp_neg_mul_norm_sq ha)⟩
  let G : ProbabilityMeasure E → EReal := fun μ ↦ (klDiv (μ : Measure E) (R : Measure E) : EReal)+
    TauCeti.potentialEnergy V (μ : Measure E)+
      ((-Real.log (∫ x : E,Real.exp (-(a*‖x‖^2))) : ℝ) : EReal)
  have hK : LowerSemicontinuous (fun μ : ProbabilityMeasure E ↦
      (klDiv (μ : Measure E) (R : Measure E) : EReal)) := by
    apply continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure.comp (continuous_id.prodMk continuous_const))
    exact fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  have hP : LowerSemicontinuous (fun μ : ProbabilityMeasure E ↦
      TauCeti.potentialEnergy V (μ : Measure E)) :=
    TauCeti.lowerSemicontinuous_potentialEnergy hVc.lowerSemicontinuous
      ⟨0,by rintro _ ⟨x,rfl⟩; exact hV x⟩
  have hPnb (μ : ProbabilityMeasure E) : TauCeti.potentialEnergy V (μ : Measure E) ≠ ⊥ := by
    rw [TauCeti.potentialEnergy_of_nonneg_ae (ae_of_all _ hV)]
    exact EReal.coe_ennreal_ne_bot _
  have hG : LowerSemicontinuous G := by
    apply (hK.add' hP (fun μ ↦ EReal.continuousAt_add
      (Or.inr (hPnb μ)) (Or.inl (EReal.coe_ennreal_ne_bot _)))).add' continuous_const.lowerSemicontinuous
    intro μ
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hrep (μ : TauCeti.WassersteinSpace 2 E) :
      G (μ : ProbabilityMeasure E) = jkoFreeEnergy V μ+
        ((a*(∫ x,‖x‖^2 ∂wassersteinLaw μ) : ℝ) : EReal) := by
    dsimp only [G,R]
    change (klDiv (wassersteinLaw μ) (volume.tilted (fun x : E ↦ -(a*‖x‖^2))) : EReal)+
      TauCeti.potentialEnergy V (wassersteinLaw μ)+
        ((-Real.log (∫ x : E,Real.exp (-(a*‖x‖^2))) : ℝ) : EReal) = _
    exact (jkoFreeEnergy_add_quadratic_eq V ha μ).symm
  have h := (hG.le_liminf (ν : ProbabilityMeasure E)).trans hlim.liminf_le_liminf_comp
  simpa only [Function.comp_def,hrep] using h
/-- Gaussian moment compensation bounds the JKO Moreau envelope below at a Dirac law for
every positive step size. -/
theorem exists_moreauYosida_jkoFreeEnergy_ne_bot
    (V : E → ℝ) (hV : ∀ x,0≤V x) (τ : ℝ≥0) (hτ : 0<τ) :
    ∃ δ : TauCeti.WassersteinSpace 2 E, TauCeti.moreauYosida (jkoFreeEnergy V) τ δ ≠ ⊥ := by
  have hmem : TauCeti.HasFiniteMoment 2 (diracProba (0:E) : Measure E) := by
    change TauCeti.HasFiniteMoment 2 (Measure.dirac (0:E))
    exact TauCeti.hasFiniteMoment_dirac 2 (0:E)
  let δ : TauCeti.WassersteinSpace 2 E := TauCeti.WassersteinSpace.mk (diracProba (0:E)) hmem
  have hδ : wassersteinLaw δ = Measure.dirac (0:E) :=
    congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk (diracProba (0:E)) hmem)
  let a : ℝ := 1/(2*(τ:ℝ))
  have ha : 0<a := one_div_pos.mpr (mul_pos two_pos (by exact_mod_cast hτ))
  let Z := ∫ x : E,Real.exp (-(a*‖x‖^2))
  refine ⟨δ,ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-Real.log Z)) ?_⟩
  apply TauCeti.le_moreauYosida_iff.mpr
  intro ν _
  have hpen : ((edist δ ν^2/(2*τ) : ℝ≥0∞) : EReal) =
      ((a*(∫ x,‖x‖^2 ∂wassersteinLaw ν) : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal (by finiteness : edist δ ν^2/(2*τ) ≠ ∞)]
    apply congrArg ((↑) : ℝ → EReal)
    simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_mul,
      ENNReal.toReal_ofNat,ENNReal.coe_toReal]
    have hd : (edist δ ν).toReal^2 = ∫ x,‖x‖^2 ∂wassersteinLaw ν := by
      rw [TauCeti.WassersteinSpace.edist_def]
      change (TauCeti.wassersteinEDist 2 (wassersteinLaw δ) (wassersteinLaw ν)).toReal^2 = _
      rw [hδ,integral_norm_sq_eq_wasserstein_dirac_sq]
    rw [hd]
    dsimp [a]
    ring
  rw [hpen]
  calc ((-Real.log Z : ℝ) : EReal) =
        ((-a*(∫ x,‖x‖^2 ∂wassersteinLaw ν)-Real.log Z : ℝ) : EReal)+
          ((a*(∫ x,‖x‖^2 ∂wassersteinLaw ν) : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
    _ ≤ _ := add_le_add (jkoFreeEnergy_gaussian_lower_bound V hV ha ν) le_rfl

/-- Every positive JKO step for a continuous nonnegative potential has a minimizer. -/
theorem nonempty_moreauYosidaResolvent_jkoFreeEnergy
    (V : E → ℝ) (hVc : Continuous V) (hV : ∀ x,0≤V x) (τ : ℝ≥0) (hτ : 0<τ)
    (μ : TauCeti.WassersteinSpace 2 E) :
    (TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ μ).Nonempty := by
  obtain ⟨δ,hδ⟩ := exists_moreauYosida_jkoFreeEnergy_ne_bot V hV (τ+1) (by positivity)
  exact TauCeti.WassersteinSpace.moreauYosidaResolvent_nonempty_of_properSpace
    (p := 2) (X := E) (φ := jkoFreeEnergy V) (τ₀ := τ+1) (μ₀ := δ)
    (fun {v} {ν} hv hν ↦ jkoFreeEnergy_le_liminf_of_isBounded V hVc hV (u := v) (ν := ν) hv hν) hτ (lt_add_of_pos_right τ one_pos) hδ μ
end CKSD
