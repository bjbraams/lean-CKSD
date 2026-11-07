module

public import CKSD.LinearModels.Causal

/-!
# Treatment-effect influence functions in finite strata

Conditional means, variances, and propensities are defined by integrals on observed strata.
The results cover the variance identity and bounded-score path derivatives of the observed-data
functional. They do not assert the full convolution bound or cross-fitting central limit theorem.
Source: GAPS 105.56.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace CKSD

/-- Joint covariate-stratum and treatment event. -/
def treatmentStratum {Ω : Type*} {k : ℕ} (X : Ω → Fin k) (A : Ω → Bool)
    (x : Fin k) (a : Bool) : Set Ω := {ω | X ω = x ∧ A ω = a}

/-- Observed conditional outcome mean in a treatment stratum. -/
def stratumOutcomeMean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ)
    (x : Fin k) (a : Bool) : ℝ :=
  (∫ ω in treatmentStratum X A x a, Y ω ∂P) / P.real (treatmentStratum X A x a)

/-- Observed conditional outcome variance in a treatment stratum. -/
def stratumOutcomeVariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ)
    (x : Fin k) (a : Bool) : ℝ :=
  (∫ ω in treatmentStratum X A x a, (Y ω - stratumOutcomeMean P X A Y x a) ^ 2 ∂P) /
    P.real (treatmentStratum X A x a)

/-- Propensity in a finite observed covariate stratum. -/
def stratumPropensity {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (x : Fin k) : ℝ :=
  P.real (treatmentStratum X A x true) / P.real {ω | X ω = x}

/-- Identified treatment-effect functional of an observed law with finite covariate strata. -/
def finiteStrataTreatmentEffect {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, stratumOutcomeMean P X A Y (X ω) true - stratumOutcomeMean P X A Y (X ω) false ∂P

/-- Treatment-effect influence function at the true finite-stratum nuisances. -/
def finiteStrataTreatmentInfluence {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (X : Ω → Fin k) (A : Ω → Bool) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  treatmentEffectInfluence (fun x ↦ stratumOutcomeMean P X A Y x false)
    (fun x ↦ stratumOutcomeMean P X A Y x true) (stratumPropensity P X A)
    (finiteStrataTreatmentEffect P X A Y) (X ω) (A ω) (Y ω)

section StrataIntegrals

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- Treatment strata are measurable. -/
theorem measurableSet_treatmentStratum {X : Ω → Fin k} {A : Ω → Bool} (hX : Measurable X)
    (hA : Measurable A) (x : Fin k) (a : Bool) : MeasurableSet (treatmentStratum X A x a) :=
  (hX (measurableSet_singleton x)).inter (hA (measurableSet_singleton a))

/-- An integral splits over the finite partition into treatment strata. -/
theorem integral_eq_sum_treatmentStratum (P : Measure Ω) {X : Ω → Fin k} {A : Ω → Bool}
    (hX : Measurable X) (hA : Measurable A) (h : Ω → ℝ)
    (hh : ∀ x a, IntegrableOn h (treatmentStratum X A x a) P) :
    (∫ ω, h ω ∂P) = ∑ x, ∑ a, ∫ ω in treatmentStratum X A x a, h ω ∂P := by
  classical
  have hpt : (fun ω ↦ h ω) =
      fun ω ↦ ∑ x, ∑ a, (treatmentStratum X A x a).indicator h ω := by
    funext ω
    rw [Finset.sum_eq_single (X ω), Finset.sum_eq_single (A ω)]
    · rw [indicator_of_mem]; exact ⟨rfl, rfl⟩
    · intro a _ ha; rw [indicator_of_notMem]; exact fun h ↦ ha h.2.symm
    · simp
    · intro x _ hx
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      rw [indicator_of_notMem]; exact fun h ↦ hx h.1.symm
    · simp
  have hmeas := measurableSet_treatmentStratum hX hA
  rw [show (∫ ω, h ω ∂P) = ∫ ω, ∑ x, ∑ a, (treatmentStratum X A x a).indicator h ω ∂P from
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ congrFun hpt ω)]
  rw [integral_finsetSum _ fun x _ ↦ integrable_finsetSum _ fun a _ ↦
    (hh x a).integrable_indicator (hmeas x a)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [integral_finsetSum _ fun a _ ↦ (hh x a).integrable_indicator (hmeas x a)]
  exact Finset.sum_congr rfl fun a _ ↦ integral_indicator (hmeas x a)

/-- Within one stratum, an affine function of the centred outcome integrates to its constant
part, and its square to the constant part plus the scaled within-stratum variance. -/
theorem setIntegral_affine_centred (P : Measure Ω) [IsFiniteMeasure P] {S : Set Ω}
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) (hpos : 0 < P.real S)
    (c d : ℝ) :
    let m := (∫ ω in S, Y ω ∂P) / P.real S;
    (∫ ω in S, c + d * (Y ω - m) ∂P) = c * P.real S ∧
      (∫ ω in S, (c + d * (Y ω - m)) ^ 2 ∂P) =
        c ^ 2 * P.real S + d ^ 2 * ∫ ω in S, (Y ω - m) ^ 2 ∂P := by
  intro m
  have hYi : IntegrableOn Y S P := (hY.integrable one_le_two).integrableOn
  have hc : IntegrableOn (fun _ ↦ c) S P := integrableOn_const (measure_ne_top _ _)
  have hm : IntegrableOn (fun _ ↦ m) S P := integrableOn_const (measure_ne_top _ _)
  have hYm : IntegrableOn (fun ω ↦ Y ω - m) S P := hYi.sub hm
  have hsq : IntegrableOn (fun ω ↦ (Y ω - m) ^ 2) S P :=
    ((hY.sub (memLp_const m)).integrable_sq).integrableOn
  have hzero : (∫ ω in S, (Y ω - m) ∂P) = 0 := by
    rw [integral_sub hYi hm, setIntegral_const, smul_eq_mul]
    simp only [m]
    field_simp
    ring
  constructor
  · rw [integral_add hc (hYm.const_mul d), integral_const_mul, hzero, setIntegral_const,
      smul_eq_mul]
    ring
  · have hexp : (fun ω ↦ (c + d * (Y ω - m)) ^ 2) =
        fun ω ↦ c ^ 2 + (2 * c * d) * (Y ω - m) + d ^ 2 * (Y ω - m) ^ 2 := by
      funext ω; ring
    have i₀ : IntegrableOn (fun _ ↦ c ^ 2) S P := integrableOn_const (measure_ne_top _ _)
    have i₁ : IntegrableOn (fun ω ↦ 2 * c * d * (Y ω - m)) S P := hYm.const_mul _
    have i₂ : IntegrableOn (fun ω ↦ c ^ 2 + 2 * c * d * (Y ω - m)) S P := i₀.add i₁
    have i₃ : IntegrableOn (fun ω ↦ d ^ 2 * (Y ω - m) ^ 2) S P := hsq.const_mul _
    rw [hexp, integral_add i₂ i₃, integral_add i₀ i₁, integral_const_mul, integral_const_mul,
      hzero, setIntegral_const, smul_eq_mul]
    ring

/-- Integral of a function of the stratum labels. -/
theorem integral_comp_treatmentStratum (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → Fin k}
    {A : Ω → Bool} (hX : Measurable X) (hA : Measurable A) (F : Fin k → Bool → ℝ) :
    (∫ ω, F (X ω) (A ω) ∂P) = ∑ x, ∑ a, F x a * P.real (treatmentStratum X A x a) := by
  have hmeas := measurableSet_treatmentStratum hX hA
  have hEq : ∀ x a, EqOn (fun ω ↦ F (X ω) (A ω)) (fun _ ↦ F x a) (treatmentStratum X A x a) :=
    fun x a ω hω ↦ by
      obtain ⟨h₁, h₂⟩ := hω
      simp only [h₁, h₂]
  rw [integral_eq_sum_treatmentStratum P hX hA _ fun x a ↦
    (integrableOn_const (measure_ne_top _ _)).congr_fun (hEq x a).symm (hmeas x a)]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  rw [setIntegral_congr_fun (hmeas x a) (hEq x a), setIntegral_const, smul_eq_mul, mul_comm]

end StrataIntegrals

/-- GAPS 105.56: mean zero and the variance formula for the treatment-effect influence function
in finite strata. Positive joint stratum masses express overlap explicitly. -/
theorem finiteStrataTreatmentInfluence_mean_and_variance
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : MemLp Y 2 P)
    (hpos : ∀ x a, 0 < P.real (treatmentStratum X A x a)) :
    (∫ ω, finiteStrataTreatmentInfluence P X A Y ω ∂P) = 0 ∧
      variance P (finiteStrataTreatmentInfluence P X A Y) =
        variance P (fun ω ↦ stratumOutcomeMean P X A Y (X ω) true -
          stratumOutcomeMean P X A Y (X ω) false) +
          ∫ ω, stratumOutcomeVariance P X A Y (X ω) true / stratumPropensity P X A (X ω) +
            stratumOutcomeVariance P X A Y (X ω) false /
              (1 - stratumPropensity P X A (X ω)) ∂P := by
  set S := treatmentStratum X A with hSdef
  set p := fun x a ↦ P.real (S x a) with hpdef
  set m := stratumOutcomeMean P X A Y with hmdef
  set v := stratumOutcomeVariance P X A Y with hvdef
  set e := stratumPropensity P X A with hedef
  set ate := finiteStrataTreatmentEffect P X A Y with hatedef
  set φ := finiteStrataTreatmentInfluence P X A Y with hφdef
  have hmeas := measurableSet_treatmentStratum hX hA
  have hmem : ∀ x a ω, ω ∈ S x a → X ω = x ∧ A ω = a := fun x a ω h ↦ h
  -- stratum sizes
  have hq : ∀ x, P.real {ω | X ω = x} = p x true + p x false := by
    intro x
    have hU : {ω | X ω = x} = S x true ∪ S x false := by
      ext ω
      simp only [hSdef, treatmentStratum, mem_union, mem_ofPred_eq]
      cases A ω <;> simp
    rw [hU, measureReal_union _ (hmeas x false)]
    rw [Set.disjoint_left]
    rintro ω ⟨-, h₁⟩ ⟨-, h₂⟩
    rw [h₁] at h₂
    exact Bool.noConfusion h₂
  have he : ∀ x, e x = p x true / (p x true + p x false) := fun x ↦ by
    rw [← hq]; rfl
  have he' : ∀ x, 1 - e x = p x false / (p x true + p x false) := fun x ↦ by
    rw [he]
    have h₁ : 0 < p x true := hpos x true
    have h₂ : 0 < p x false := hpos x false
    field_simp
    ring
  have hlabel : ∀ F : Fin k → Bool → ℝ,
      (∫ ω, F (X ω) (A ω) ∂P) = ∑ x, ∑ a, F x a * p x a :=
    integral_comp_treatmentStratum P hX hA
  have hsum : ∑ x, ∑ a, p x a = 1 := by
    have := hlabel (fun _ _ ↦ 1)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    rw [this]
  have hate : ate = ∑ x, ∑ a, (m x true - m x false) * p x a :=
    hlabel (fun x _ ↦ m x true - m x false)
  -- the influence function is affine in the outcome on every stratum
  let c : Fin k → ℝ := fun x ↦ m x true - m x false - ate
  let d : Fin k → Bool → ℝ := fun x a ↦ if a then 1 / e x else -1 / (1 - e x)
  have heq : ∀ x a, EqOn φ (fun ω ↦ c x + d x a * (Y ω - m x a)) (S x a) := by
    intro x a ω hω
    obtain ⟨h₁, h₂⟩ := hmem x a ω hω
    simp only [φ, finiteStrataTreatmentInfluence, treatmentEffectInfluence, h₁, h₂, c, d]
    cases a <;> simp <;> ring
  have hYS : ∀ x a, IntegrableOn (fun ω ↦ c x + d x a * (Y ω - m x a)) (S x a) P := by
    intro x a
    exact (integrableOn_const (measure_ne_top _ _)).add
      ((((hY.integrable one_le_two).integrableOn).sub
        (integrableOn_const (measure_ne_top _ _))).const_mul _)
  have hYS2 : ∀ x a, IntegrableOn (fun ω ↦ (c x + d x a * (Y ω - m x a)) ^ 2) (S x a) P := by
    intro x a
    exact (((memLp_const (c x)).add ((hY.sub (memLp_const (m x a))).const_mul (d x a))
      ).integrable_sq).integrableOn
  have hφint : ∀ x a, (∫ ω in S x a, φ ω ∂P) = (m x true - m x false - ate) * p x a := by
    intro x a
    rw [setIntegral_congr_fun (hmeas x a) (heq x a)]
    exact (setIntegral_affine_centred P hY (hpos x a) (c x) (d x a)).1
  have hφint2 : ∀ x a, (∫ ω in S x a, φ ω ^ 2 ∂P) =
      c x ^ 2 * p x a + d x a ^ 2 * (v x a * p x a) := by
    intro x a
    rw [setIntegral_congr_fun (hmeas x a)
      (g := fun ω ↦ (c x + d x a * (Y ω - m x a)) ^ 2) (fun ω hω ↦ by rw [heq x a hω])]
    refine Eq.trans (setIntegral_affine_centred P hY (hpos x a) (c x) (d x a)).2 ?_
    congr 2
    show _ = (∫ ω in S x a, (Y ω - m x a) ^ 2 ∂P) / P.real (S x a) * P.real (S x a)
    rw [div_mul_cancel₀ _ (hpos x a).ne']
    rfl
  have hmean : (∫ ω, φ ω ∂P) = 0 := by
    rw [integral_eq_sum_treatmentStratum P hX hA _ fun x a ↦
      (hYS x a).congr_fun (heq x a).symm (hmeas x a)]
    rw [Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ hφint x a]
    have : (∑ x, ∑ a, (m x true - m x false - ate) * p x a) =
        (∑ x, ∑ a, (m x true - m x false) * p x a) - ate * ∑ x, ∑ a, p x a := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [this, ← hate, hsum]
    ring
  refine ⟨hmean, ?_⟩
  have hvarφ : variance P φ = ∑ x, ∑ a, (c x ^ 2 * p x a + d x a ^ 2 * (v x a * p x a)) := by
    unfold variance
    rw [hmean]
    simp only [sub_zero]
    rw [integral_eq_sum_treatmentStratum P hX hA _ fun x a ↦
      (hYS2 x a).congr_fun (fun ω hω ↦ by simp only [heq x a hω]) (hmeas x a)]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ hφint2 x a
  have hvarg : variance P (fun ω ↦ m (X ω) true - m (X ω) false) =
      ∑ x, ∑ a, c x ^ 2 * p x a := by
    unfold variance
    have : (∫ ω, m (X ω) true - m (X ω) false ∂P) = ate := rfl
    rw [this]
    exact hlabel (fun x _ ↦ (m x true - m x false - ate) ^ 2)
  have hrest : (∫ ω, v (X ω) true / e (X ω) + v (X ω) false / (1 - e (X ω)) ∂P) =
      ∑ x, ∑ a, (v x true / e x + v x false / (1 - e x)) * p x a :=
    hlabel (fun x _ ↦ v x true / e x + v x false / (1 - e x))
  rw [hvarφ, hvarg, hrest, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Fintype.sum_bool, d, c, ite_true, Bool.false_eq_true, ite_false]
  rw [he' x, he x]
  have h₁ : 0 < p x true := hpos x true
  have h₂ : 0 < p x false := hpos x false
  field_simp
  ring

section ScoreTilt

open Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Set integrals against a nonnegative linear score tilt of a measure. -/
theorem setIntegral_withDensity_score_tilt (P : Measure Ω) {s : Ω → ℝ} (hs : Measurable s)
    {t : ℝ} (ht : ∀ ω, 0 ≤ 1 + t * s ω) {B : Set Ω} (hB : MeasurableSet B) (g : Ω → ℝ) :
    (∫ ω in B, g ω ∂P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t * s ω))) =
      ∫ ω in B, (1 + t * s ω) * g ω ∂P := by
  rw [restrict_withDensity hB, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (ht ω)]

/-- The covariate stratum splits into its two treatment strata. -/
theorem measureReal_covariateStratum_eq_add {k : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → Fin k} {A : Ω → Bool} (hX : Measurable X) (hA : Measurable A) (x : Fin k) :
    P.real {ω | X ω = x} =
      P.real (treatmentStratum X A x true) + P.real (treatmentStratum X A x false) := by
  have hU : {ω | X ω = x} = treatmentStratum X A x true ∪ treatmentStratum X A x false := by
    ext ω
    simp only [treatmentStratum, mem_union, mem_ofPred_eq]
    cases A ω <;> simp
  rw [hU, measureReal_union _ (measurableSet_treatmentStratum hX hA x false)]
  rw [Set.disjoint_left]
  rintro ω ⟨-, h₁⟩ ⟨-, h₂⟩
  rw [h₁] at h₂
  exact Bool.noConfusion h₂

/-- On each treatment stratum the influence function is affine in the outcome. -/
theorem finiteStrataTreatmentInfluence_eqOn {k : ℕ} (P : Measure Ω) (X : Ω → Fin k)
    (A : Ω → Bool) (Y : Ω → ℝ) (x : Fin k) (a : Bool) :
    EqOn (finiteStrataTreatmentInfluence P X A Y)
      (fun ω ↦ (stratumOutcomeMean P X A Y x true - stratumOutcomeMean P X A Y x false -
          finiteStrataTreatmentEffect P X A Y) +
        (if a then 1 / stratumPropensity P X A x else -1 / (1 - stratumPropensity P X A x)) *
          (Y ω - stratumOutcomeMean P X A Y x a))
      (treatmentStratum X A x a) := by
  intro ω hω
  obtain ⟨h₁, h₂⟩ := hω
  simp only [finiteStrataTreatmentInfluence, treatmentEffectInfluence, h₁, h₂]
  cases a <;> simp <;> ring

end ScoreTilt

section

open Filter
open scoped Topology

/-- GAPS 105.56: the treatment-effect influence function represents derivatives along bounded
mean-zero score tilts of the observed law. The semiparametric convolution bound is not included. -/
theorem hasDerivAt_finiteStrataTreatmentEffect_score_tilt
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : MemLp Y 2 P)
    (hpos : ∀ x a, 0 < P.real (treatmentStratum X A x a))
    (s : Ω → ℝ) (hs : Measurable s) (hbound : ∃ C, ∀ ω, |s ω| ≤ C)
    (hmean : (∫ ω, s ω ∂P) = 0) :
    HasDerivAt (fun t : ℝ ↦ finiteStrataTreatmentEffect
      (P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t * s ω))) X A Y)
      (∫ ω, finiteStrataTreatmentInfluence P X A Y ω * s ω ∂P) 0 := by
  obtain ⟨C, hC⟩ := hbound
  have hmeas := measurableSet_treatmentStratum hX hA
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hsb : ∀ᵐ ω ∂P, ‖s ω‖ ≤ C := Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact hC ω
  have hsi : Integrable s P := Integrable.of_bound hs.aestronglyMeasurable C hsb
  have hYs : Integrable (fun ω ↦ Y ω * s ω) P := hYi.mul_bdd hs.aestronglyMeasurable hsb
  -- first-order data of the strata
  set S := treatmentStratum X A with hSdef
  set p := fun x a ↦ P.real (S x a) with hpdef
  set p' := fun x a ↦ ∫ ω in S x a, s ω ∂P with hp'def
  set n := fun x a ↦ ∫ ω in S x a, Y ω ∂P with hndef
  set n' := fun x a ↦ ∫ ω in S x a, Y ω * s ω ∂P with hn'def
  let D := fun x a (t : ℝ) ↦ p x a + t * p' x a
  let N := fun x a (t : ℝ) ↦ n x a + t * n' x a
  let Ψ := fun t : ℝ ↦
    ∑ x, ∑ a, (N x true t / D x true t - N x false t / D x false t) * D x a t
  -- near zero the tilted functional is the rational function `Ψ`
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), finiteStrataTreatmentEffect
      (P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t * s ω))) X A Y = Ψ t := by
    have hC' : 0 < |C| + 1 := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (one_div_pos.2 hC')] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have htpos : ∀ ω, 0 ≤ 1 + t * s ω := by
      intro ω
      have h1 : |t * s ω| ≤ |t| * (|C| + 1) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hC ω).trans ((le_abs_self C).trans (by linarith)))
          (abs_nonneg t)
      have h2 : |t| * (|C| + 1) < 1 := by
        rwa [lt_div_iff₀ hC'] at ht
      linarith [neg_abs_le (t * s ω)]
    set Pt := P.withDensity (fun ω ↦ ENNReal.ofReal (1 + t * s ω))
    have hdens : Integrable (fun ω ↦ 1 + t * s ω) P := (integrable_const 1).add (hsi.const_mul t)
    have : IsFiniteMeasure Pt := isFiniteMeasure_withDensity_ofReal hdens.hasFiniteIntegral
    have hD : ∀ x a, Pt.real (S x a) = D x a t := by
      intro x a
      have h := setIntegral_withDensity_score_tilt P hs htpos (hmeas x a) (fun _ ↦ (1 : ℝ))
      rw [setIntegral_const, smul_eq_mul, mul_one] at h
      rw [h]
      simp only [mul_one]
      rw [integral_add (integrableOn_const (measure_ne_top _ _)) (hsi.integrableOn.const_mul t),
        setIntegral_const, integral_const_mul, smul_eq_mul, mul_one]
    have hN : ∀ x a, (∫ ω in S x a, Y ω ∂Pt) = N x a t := by
      intro x a
      rw [setIntegral_withDensity_score_tilt P hs htpos (hmeas x a)]
      have : (fun ω ↦ (1 + t * s ω) * Y ω) = fun ω ↦ Y ω + t * (Y ω * s ω) := by
        funext ω; ring
      rw [this, integral_add hYi.integrableOn (hYs.integrableOn.const_mul t), integral_const_mul]
    unfold finiteStrataTreatmentEffect
    rw [integral_comp_treatmentStratum Pt hX hA
      (fun x _ ↦ stratumOutcomeMean Pt X A Y x true - stratumOutcomeMean Pt X A Y x false)]
    simp only [stratumOutcomeMean, ← hSdef, hN, hD]
    rfl
  -- derivative of the rational function
  have hDd : ∀ x a, HasDerivAt (D x a) (p' x a) 0 := fun x a ↦ by
    simpa [D] using ((hasDerivAt_id (0 : ℝ)).mul_const (p' x a)).const_add (p x a)
  have hNd : ∀ x a, HasDerivAt (N x a) (n' x a) 0 := fun x a ↦ by
    simpa [N] using ((hasDerivAt_id (0 : ℝ)).mul_const (n' x a)).const_add (n x a)
  have hD0 : ∀ x a, D x a 0 = p x a := fun x a ↦ by simp [D]
  have hN0 : ∀ x a, N x a 0 = n x a := fun x a ↦ by simp [N]
  have hp0 : ∀ x a, p x a ≠ 0 := fun x a ↦ (hpos x a).ne'
  have hΨ : HasDerivAt Ψ (∑ x, ∑ a,
      (((n' x true * p x true - n x true * p' x true) / p x true ^ 2 -
        (n' x false * p x false - n x false * p' x false) / p x false ^ 2) * p x a +
        (n x true / p x true - n x false / p x false) * p' x a)) 0 := by
    refine HasDerivAt.fun_sum fun x _ ↦ HasDerivAt.fun_sum fun a _ ↦ ?_
    have h := (((hNd x true).div (hDd x true) (by rw [hD0]; exact hp0 x true)).sub
      ((hNd x false).div (hDd x false) (by rw [hD0]; exact hp0 x false))).mul (hDd x a)
    simp only [hD0, hN0, Pi.sub_apply, Pi.div_apply] at h
    exact h
  refine (hΨ.congr_of_eventuallyEq hnear).congr_deriv ?_
  -- the pairing of the influence function with the score, stratum by stratum
  set m := stratumOutcomeMean P X A Y with hmdef
  set e := stratumPropensity P X A with hedef
  set ate := finiteStrataTreatmentEffect P X A Y with hatedef
  let d : Fin k → Bool → ℝ := fun x a ↦ if a then 1 / e x else -1 / (1 - e x)
  have hm : ∀ x a, m x a = n x a / p x a := fun x a ↦ rfl
  have he : ∀ x, e x = p x true / (p x true + p x false) := fun x ↦ by
    rw [hedef, stratumPropensity, measureReal_covariateStratum_eq_add P hX hA]
  have hpiece : ∀ x a, EqOn (fun ω ↦ finiteStrataTreatmentInfluence P X A Y ω * s ω)
      (fun ω ↦ (m x true - m x false - ate - d x a * m x a) * s ω + d x a * (Y ω * s ω))
      (S x a) := by
    intro x a ω hω
    simp only [finiteStrataTreatmentInfluence_eqOn P X A Y x a hω, d]
    ring
  have hpieceI : ∀ x a, IntegrableOn
      (fun ω ↦ (m x true - m x false - ate - d x a * m x a) * s ω + d x a * (Y ω * s ω))
      (S x a) P := fun x a ↦
    ((hsi.const_mul _).add (hYs.const_mul _)).integrableOn
  have hφs : (∫ ω, finiteStrataTreatmentInfluence P X A Y ω * s ω ∂P) =
      ∑ x, ∑ a, ((m x true - m x false - ate - d x a * m x a) * p' x a +
        d x a * n' x a) := by
    rw [integral_eq_sum_treatmentStratum P hX hA _ fun x a ↦
      (hpieceI x a).congr_fun (hpiece x a).symm (hmeas x a)]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    rw [setIntegral_congr_fun (hmeas x a) (hpiece x a),
      integral_add (hsi.integrableOn.const_mul _) (hYs.integrableOn.const_mul _),
      integral_const_mul, integral_const_mul]
  have hsum' : ∑ x, ∑ a, p' x a = 0 := by
    rw [← hmean, integral_eq_sum_treatmentStratum P hX hA _ fun x a ↦ hsi.integrableOn]
  have hsplit : (∑ x, ∑ a, ((m x true - m x false - ate - d x a * m x a) * p' x a +
        d x a * n' x a)) =
      (∑ x, ∑ a, ((m x true - m x false - d x a * m x a) * p' x a + d x a * n' x a)) -
        ate * ∑ x, ∑ a, p' x a := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [hφs, hsplit, hsum', mul_zero, sub_zero]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h₁ : 0 < p x true := hpos x true
  have h₂ : 0 < p x false := hpos x false
  have he' : 1 - e x = p x false / (p x true + p x false) := by
    rw [he]; field_simp; ring
  simp only [Fintype.sum_bool, d, ite_true, Bool.false_eq_true, ite_false, hm]
  rw [he', he]
  have h₁' : p x true ≠ 0 := h₁.ne'
  have h₂' : p x false ≠ 0 := h₂.ne'
  have h₃ : p x true + p x false ≠ 0 := by linarith
  field_simp
  ring

end

end CKSD
