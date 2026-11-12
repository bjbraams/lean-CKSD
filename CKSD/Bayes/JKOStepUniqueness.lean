module
public import CKSD.Bayes.JKOEnergy
public import TauCeti.InformationTheory.KullbackLeibler.Convex
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture.Basic
/-!
# Uniqueness of the JKO minimizing step

The Boltzmann free energy is strictly convex along ordinary mixtures of distinct laws in its
finite domain, even when the nonnegative continuous potential is not convex. A Gaussian change
of reference reduces this to strict convexity of relative entropy: the potential and quadratic
moment corrections are affine along ordinary mixtures. Convexity of squared Wasserstein cost
then gives at most one minimizer of each positive-time JKO objective. A finite-energy comparison
law guarantees that every minimizer lies in the finite domain.

Pinned TauCeti supplies strict relative-entropy mixture convexity, squared-Wasserstein mixture
convexity, mixtures inside the Wasserstein space, and Moreau–Yosida minimality. Mathlib supplies
affinity of integration. These lemmas support the unique-step part of GAPS 104.43; the time-step
limit is separate. The ordinary-mixture argument is the classical JKO uniqueness argument.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set InformationTheory
open scoped NNReal ENNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P₂" => TauCeti.WassersteinSpace 2 E
/-- The square of the Wasserstein distance is convex along ordinary mixtures. -/
theorem wasserstein_dist_sq_le_half_add_half (μ ν η ζ : P₂)
    (hζ : wassersteinLaw ζ = (1 / 2 : ℝ≥0∞) • wassersteinLaw ν +
      (1 / 2 : ℝ≥0∞) • wassersteinLaw η) :
    dist μ ζ ^ 2 ≤ (dist μ ν ^ 2 + dist μ η ^ 2) / 2 := by
  have h := TauCeti.wassersteinEDist_smul_add_smul_rpow_le (p := (2 : ℝ≥0∞))
    measurable_edist (by norm_num) (by norm_num)
    (a := (1 / 2 : ℝ≥0∞)) (b := (1 / 2 : ℝ≥0∞)) (by simpa only [one_div] using ENNReal.inv_two_add_inv_two)
    (wassersteinLaw μ) (wassersteinLaw ν) (wassersteinLaw η)
  rw [← hζ] at h
  simp only [wassersteinLaw, ← TauCeti.WassersteinSpace.edist_def] at h
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, ← dist_edist] at hr
  linarith
/-- Integration is affine along an ordinary half mixture. -/
theorem integral_wasserstein_half_mixture (ν η ζ : P₂)
    (hζ : wassersteinLaw ζ = (1 / 2 : ℝ≥0∞) • wassersteinLaw ν +
      (1 / 2 : ℝ≥0∞) • wassersteinLaw η)
    (f : E → ℝ) (hν : Integrable f (wassersteinLaw ν)) (hη : Integrable f (wassersteinLaw η)) :
    ∫ x, f x ∂wassersteinLaw ζ = ((∫ x, f x ∂wassersteinLaw ν) +
      ∫ x, f x ∂wassersteinLaw η) / 2 := by
  rw [hζ,integral_add_measure (hν.smul_measure (by finiteness)) (hη.smul_measure (by finiteness))]
  simp only [integral_smul_measure,ENNReal.toReal_div,ENNReal.toReal_one,
    ENNReal.toReal_ofNat,smul_eq_mul]
  ring

/-- The free energy is strictly convex along ordinary half mixtures of distinct finite-energy laws. -/
theorem jkoFreeEnergy_toReal_half_mixture_lt
    (V : E → ℝ) (hVc : Continuous V) (hV : ∀ x, 0 ≤ V x)
    (ν η ζ : P₂) (hν : jkoFreeEnergy V ν ≠ ⊤) (hη : jkoFreeEnergy V η ≠ ⊤)
    (hne : ν ≠ η)
    (hζ : wassersteinLaw ζ = (1 / 2 : ℝ≥0∞) • wassersteinLaw ν +
      (1 / 2 : ℝ≥0∞) • wassersteinLaw η) :
    jkoFreeEnergy V ζ ≠ ⊤ ∧ (jkoFreeEnergy V ζ).toReal <
      ((jkoFreeEnergy V ν).toReal + (jkoFreeEnergy V η).toReal) / 2 := by
  let G : Measure E := volume.tilted (fun x : E ↦ -((1 : ℝ)*‖x‖^2))
  have hG := integrable_exp_neg_mul_norm_sq (d := d) zero_lt_one
  have : IsProbabilityMeasure G := isProbabilityMeasure_tilted hG
  have hνK := ((jkoFreeEnergy_ne_top_iff_klDiv_gaussian_and_potential V hV zero_lt_one ν).1 hν).1
  have hηK := ((jkoFreeEnergy_ne_top_iff_klDiv_gaussian_and_potential V hV zero_lt_one η).1 hη).1
  change klDiv (wassersteinLaw ν) G ≠ ∞ at hνK
  change klDiv (wassersteinLaw η) G ≠ ∞ at hηK
  have hnm : wassersteinLaw ν ≠ wassersteinLaw η := fun he ↦ hne
    (TauCeti.WassersteinSpace.ext (ProbabilityMeasure.toMeasure_injective he))
  have hh := TauCeti.klDiv_smul_add_smul_lt (ρ := G) (μ := wassersteinLaw ν)
    (ν := wassersteinLaw η) (a := (1/2 : ℝ≥0)) (b := (1/2 : ℝ≥0))
    (by norm_num) (by norm_num) (by norm_num) hνK hηK hnm
  have hζNN : (1 / 2 : ℝ≥0) • wassersteinLaw ν + (1 / 2 : ℝ≥0) • wassersteinLaw η =
      wassersteinLaw ζ := by
    rw [hζ]
    ext s hs
    simp only [add_apply,smul_apply,Measure.nnreal_smul_coe_apply,smul_eq_mul]
    congr 2 <;> norm_num
  rw [hζNN] at hh
  have hζK : klDiv (wassersteinLaw ζ) G ≠ ∞ := ne_top_of_lt hh
  have hKreal := ENNReal.toReal_strict_mono (by finiteness) hh
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hKreal
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hKreal
  have hνV := integrable_potential_of_jkoFreeEnergy_ne_top V hVc hV ν hν
  have hηV := integrable_potential_of_jkoFreeEnergy_ne_top V hVc hV η hη
  have hζV : Integrable V (wassersteinLaw ζ) := by
    rw [hζ]
    exact (hνV.smul_measure (by finiteness)).add_measure (hηV.smul_measure (by finiteness))
  have hζF : jkoFreeEnergy V ζ ≠ ⊤ :=
    (jkoFreeEnergy_ne_top_iff_klDiv_gaussian_and_potential V hV zero_lt_one ζ).2
      ⟨hζK, by rw [TauCeti.potentialEnergy_of_integrable hζV]; exact EReal.coe_ne_top _⟩
  refine ⟨hζF, ?_⟩
  have hmi (μ : P₂) : Integrable (fun x : E ↦ ‖x‖^2) (wassersteinLaw μ) := by
    change Integrable (fun x : E ↦ ‖x‖^2) ((μ : ProbabilityMeasure E) : Measure E)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,dist_zero_right] using
      TauCeti.WassersteinSpace.integrable_dist_rpow (p := 2) (by norm_num) μ (0:E)
  have hmV := integral_wasserstein_half_mixture ν η ζ hζ V hνV hηV
  have hmM := integral_wasserstein_half_mixture ν η ζ hζ (fun x : E ↦ ‖x‖^2) (hmi ν) (hmi η)
  have hreal (μ : P₂) (hμK : klDiv (wassersteinLaw μ) G ≠ ∞) (hμV : Integrable V (wassersteinLaw μ)) :
      (jkoFreeEnergy V μ).toReal = (klDiv (wassersteinLaw μ) G).toReal +
        (∫ x, V x ∂wassersteinLaw μ) - (∫ x, ‖x‖^2 ∂wassersteinLaw μ) -
        Real.log (∫ x : E, Real.exp (-((1:ℝ)*‖x‖^2))) := by
    rw [jkoFreeEnergy_eq_klDiv_gaussian_add V zero_lt_one μ,
      TauCeti.potentialEnergy_of_integrable hμV,← EReal.coe_ennreal_toReal hμK]
    simp only [← EReal.coe_add,EReal.toReal_coe,one_mul]
    ring
  rw [hreal ζ hζK hζV,hreal ν hνK hνV,hreal η hηK hηV]
  rw [hmV,hmM]
  norm_num at hKreal
  linarith
/-- A nonnegative continuous-potential JKO step has at most one minimizer, by ordinary-mixture
strict entropy convexity. No convexity assumption on the potential is needed. -/
theorem subsingleton_moreauYosidaResolvent_jkoFreeEnergy
    (V : E → ℝ) (hVc : Continuous V) (hV : ∀ x, 0 ≤ V x)
    (ρ₀ : P₂) (hF : jkoFreeEnergy V ρ₀ ≠ ⊤)
    (τ : ℝ≥0) (hτ : 0 < τ) (μ : P₂) :
    Set.Subsingleton (TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ μ) := by
  have hmy : TauCeti.moreauYosida (jkoFreeEnergy V) τ μ ≠ ⊤ := by
    have hh := TauCeti.moreauYosida_le (jkoFreeEnergy V) τ (x := μ) (y := ρ₀) (edist_ne_top _ _)
    apply ne_top_of_le_ne_top ?_ hh
    rw [TauCeti.coe_edist_sq_div_eq_coe_dist_sq_div hτ]
    simpa only [ne_eq,EReal.add_coe_eq_top_iff] using hF
  intro ν hν η hη
  by_contra hne
  have hνF := TauCeti.apply_ne_top_of_mem_moreauYosidaResolvent hν hmy
  have hηF := TauCeti.apply_ne_top_of_mem_moreauYosidaResolvent hη hmy
  obtain ⟨ζ,hζ⟩ := TauCeti.WassersteinSpace.exists_coe_eq_smul_add_smul (p := (2 : ℝ≥0∞))
    (a := (1/2 : ℝ≥0∞)) (b := (1/2 : ℝ≥0∞))
    (by simpa only [one_div] using ENNReal.inv_two_add_inv_two) ν η
  change wassersteinLaw ζ = (1/2 : ℝ≥0∞) • wassersteinLaw ν + (1/2 : ℝ≥0∞) • wassersteinLaw η at hζ
  obtain ⟨hζF,hstrict⟩ := jkoFreeEnergy_toReal_half_mixture_lt V hVc hV ν η ζ hνF hηF hne hζ
  have hcost := wasserstein_dist_sq_le_half_add_half μ ν η ζ hζ
  have hreal (ξ : P₂) (hξ : jkoFreeEnergy V ξ ≠ ⊤) :
      jkoFreeEnergy V ξ = ((jkoFreeEnergy V ξ).toReal : EReal) :=
    (EReal.coe_toReal hξ (jkoFreeEnergy_ne_bot V hV ξ)).symm
  have hn := TauCeti.add_toReal_sq_div_le_of_mem_moreauYosidaResolvent hτ hν (z := ζ)
    (edist_ne_top _ _) (hreal ν hνF) (hreal ζ hζF)
  have he := TauCeti.add_toReal_sq_div_le_of_mem_moreauYosidaResolvent hτ hη (z := ζ)
    (edist_ne_top _ _) (hreal η hηF) (hreal ζ hζF)
  simp only [← dist_edist] at hn he
  have hc : dist μ ζ ^ 2 / (2 * (τ : ℝ)) ≤
      (dist μ ν ^ 2 / (2 * (τ : ℝ)) + dist μ η ^ 2 / (2 * (τ : ℝ))) / 2 := by
    calc
      _ ≤ ((dist μ ν ^ 2 + dist μ η ^ 2) / 2) / (2 * (τ : ℝ)) :=
        div_le_div_of_nonneg_right hcost (by positivity)
      _ = _ := by ring
  linarith
end CKSD
