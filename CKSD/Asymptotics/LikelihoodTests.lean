module

public import CKSD.Asymptotics.Statistics
public import CKSD.Asymptotics.Estimators
public import CKSD.Asymptotics.Experiments
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Likelihood-ratio, Wald, and score tests

The three classical test statistics of a simple null hypothesis in a scalar smooth model,
with their common chi-squared limit under the null and their common noncentral chi-squared
limit under local alternatives. The limit laws are TauCeti's chi-squared and noncentral
chi-squared measures. The estimators are functions of the sample of size `n`, so that the
laws under the null and under local alternatives are product measures on `Fin n → E`.
Sources: GAPS 102.11, with the hypotheses of GAPS 102.3 and the DQM condition of GAPS 102.13.

The proofs realize the sample as the first `n` coordinates of Mathlib's infinite product measure
`Measure.infinitePi` and use the asymptotic linearization of the likelihood root
`mle_asymptotic_linearization_and_normality` (GAPS 102.3), Mathlib's strong law and central
limit theorem through the adapters of `CKSD.Asymptotics.Estimators`, and a second-order Taylor expansion
of the sample log likelihood. All three statistics reduce to `Zₙ² / I(θ₀)` for the normalized
score `Zₙ`. Under local alternatives, the joint law of a statistic and the log likelihood ratio is
transported by Le Cam's third lemma `tendstoWeakly_of_log_likelihood_ratio_dependent`
(GAPS 102.14); the product densities use TauCeti's `TauCeti.pi_withDensity`, and the limit is
identified by TauCeti's `TauCeti.Probability.gaussianReal_map_sq_noncentral`. The DQM hypothesis of
the local-alternative theorem is implied by the smoothness and envelope hypotheses and is not used.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Wald statistic of a scalar simple null `θ = θ₀`, with information evaluated at the estimate:
`n (T - θ₀)² I(T)`. -/
def scalarWaldStatistic (I : ℝ → ℝ) (n : ℕ) (estimate θ₀ : ℝ) : ℝ :=
  n * (estimate - θ₀) ^ 2 * I estimate

/-- Rao score statistic of a scalar simple null: `ℓₙ'(θ₀)² / (n I(θ₀))`, written with the
derivative of the sample log likelihood. -/
def scalarScoreStatistic {E : Type*} (f : ℝ → E → ℝ) (I : ℝ → ℝ) {n : ℕ} (x : Fin n → E)
    (θ₀ : ℝ) : ℝ :=
  deriv (sampleLogLikelihood f x) θ₀ ^ 2 / (n * I θ₀)

/-- The coordinate process of the infinite product of a probability law is iid with that law. -/
theorem iid_infinitePi_eval {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] :
    IsIndependentIdenticallyDistributed (Measure.infinitePi fun _ : ℕ ↦ P) (fun i ω ↦ ω i) P :=
  ⟨fun i ↦ measurable_pi_apply i,
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ ↦ id) (fun _ ↦ measurable_id),
    fun i ↦ Measure.infinitePi_map_eval _ i⟩

/-- The first `n` observations of an iid sequence have the `n`-fold product law. -/
theorem map_fin_eq_pi_of_iid {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) (X : ℕ → Ω → E)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (n : ℕ) :
    μ.map (fun ω (i : Fin n) ↦ X i ω) = Measure.pi (fun _ : Fin n ↦ P) := by
  have hind : iIndepFun (fun i : Fin n ↦ X i) μ := hiid.2.1.precomp Fin.val_injective
  have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := μ) (f := fun i : Fin n ↦ X i)
    (fun i ↦ (hiid.1 i).aemeasurable)).1 hind
  rw [h]
  simp [hiid.2.2]

/-- Convergence in law of statistics of the first `n` observations of an iid sequence gives weak
convergence of their laws under the `n`-fold product measures. -/
theorem tendstoWeakly_pi_of_tendstoInDistribution {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [TopologicalSpace F] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) (X : ℕ → Ω → E)
    (hiid : IsIndependentIdenticallyDistributed μ X P) (V : ∀ n, (Fin n → E) → F)
    (hV : ∀ n, Measurable (V n)) (ν : Measure F)
    (h : TendstoInDistribution μ (fun n ω ↦ V n (fun i : Fin n ↦ X i ω)) ν) :
    TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P).map (V n)) ν := by
  have heq : ∀ n, (Measure.pi fun _ : Fin n ↦ P).map (V n) =
      μ.map (fun ω ↦ V n (fun i : Fin n ↦ X i ω)) := fun n ↦ by
    rw [← map_fin_eq_pi_of_iid μ P X hiid n,
      Measure.map_map (hV n) (measurable_pi_iff.2 fun i : Fin n ↦ hiid.1 i)]
    rfl
  simp_rw [heq]
  exact h

/-- Convergence to zero in probability under the `n`-fold product measures is convergence to
zero in probability of the same statistics of the first `n` observations of an iid sequence. -/
theorem tendstoInProbabilityZero_pi_iff_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (V : ∀ n, (Fin n → E) → ℝ) (hV : ∀ n, Measurable (V n)) :
    TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P) V ↔
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ X i ω)) 0 := by
  have heq : ∀ (n : ℕ) (ε : ℝ), (Measure.pi fun _ : Fin n ↦ P).real {x | ε < |V n x|} =
      μ.real {ω | ε < dist (V n (fun i : Fin n ↦ X i ω)) 0} := fun n ε ↦ by
    have hs : MeasurableSet {x : Fin n → E | ε < |V n x|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hV n))
    rw [← map_fin_eq_pi_of_iid μ P X hiid n,
      map_measureReal_apply (measurable_pi_iff.2 fun i : Fin n ↦ hiid.1 i) hs]
    simp only [Real.dist_eq, sub_zero]
    rfl
  simp only [TendstoInProbabilityZero, TendstoInProbabilityConst, heq]

/-- The Fisher information of a family with strictly positive densities, `C³` log likelihood,
is a measurable function of the parameter. -/
theorem measurable_fisherInformation {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E)
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x))) :
    Measurable (fisherInformation P f) := by
  have hlogm : ∀ θ, Measurable (fun x ↦ Real.log (f θ x)) := fun θ ↦ (hf θ).1.log
  have hdiff : ∀ x, Differentiable ℝ (fun t ↦ Real.log (f t x)) := fun x ↦
    (hsmooth x).differentiable (by norm_num)
  have hscm : ∀ θ, Measurable (likelihoodScore f θ) :=
    measurable_deriv_param (fun t x ↦ Real.log (f t x)) hlogm hdiff
  have hscc : ∀ x, Continuous (fun θ ↦ likelihoodScore f θ x) := fun x ↦
    (hsmooth x).continuous_deriv (by norm_num)
  have hfc : ∀ x, Continuous (fun θ ↦ f θ x) := fun x ↦ by
    have : (fun θ ↦ f θ x) = fun θ ↦ Real.exp (Real.log (f θ x)) := by
      funext θ; rw [Real.exp_log (hpos θ x)]
    rw [this]
    exact Real.continuous_exp.comp (hsmooth x).continuous
  let G : ℝ → E → ℝ := fun θ x ↦ f θ x * likelihoodScore f θ x ^ 2
  have hG : Measurable (Function.uncurry G) :=
    measurable_uncurry_of_continuous_of_measurable (fun x ↦ (hfc x).mul ((hscc x).pow 2))
      (fun θ ↦ (hf θ).1.mul ((hscm θ).pow_const 2))
  have heq : fisherInformation P f = fun θ ↦ ∫ x, G θ x ∂ν := by
    funext θ
    rw [fisherInformation, (hf θ).2.2, integral_withDensity_eq_integral_toReal_smul
      (hf θ).1.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (hpos θ x).le, smul_eq_mul]
  rw [heq]
  exact (hG.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

/-- The derivative of the sample log likelihood is the sum of the likelihood scores. -/
theorem deriv_sampleLogLikelihood {E : Type*} (f : ℝ → E → ℝ)
    (hdiff : ∀ x, Differentiable ℝ (fun t ↦ Real.log (f t x))) {n : ℕ} (x : Fin n → E)
    (θ : ℝ) : deriv (sampleLogLikelihood f x) θ = ∑ i, likelihoodScore f θ (x i) := by
  unfold sampleLogLikelihood
  rw [deriv_fun_sum fun i _ ↦ (hdiff (x i)) θ]
  rfl

/-- At a global maximizer of a sample log likelihood that is differentiable in the parameter,
the sum of the likelihood scores vanishes. -/
theorem sum_likelihoodScore_eq_zero_of_isMax {E : Type*} (f : ℝ → E → ℝ)
    (hdiff : ∀ x, Differentiable ℝ (fun t ↦ Real.log (f t x))) {n : ℕ} (x : Fin n → E)
    (t : ℝ) (hmax : ∀ θ, sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x t) :
    ∑ i, likelihoodScore f t (x i) = 0 := by
  rw [← deriv_sampleLogLikelihood f hdiff x t]
  have hloc : IsLocalMax (sampleLogLikelihood f x) t :=
    IsMaxOn.isLocalMax (s := univ) (fun θ _ ↦ hmax θ) Filter.univ_mem
  exact hloc.deriv_eq_zero

/-- For a family with strictly positive densities, the `n`-fold product law at `θ` has density
`exp (∑ᵢ (log f θ xᵢ - log f θ₀ xᵢ))` with respect to the product law at `θ₀`. -/
theorem pi_eq_withDensity_exp_sum_log_sub {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (ν : Measure E) (f : ℝ → E → ℝ)
    (hf : ∀ θ, HasDensity (P θ) ν (f θ)) (hpos : ∀ θ x, 0 < f θ x) (θ θ₀ : ℝ) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ P θ) = (Measure.pi fun _ : Fin n ↦ P θ₀).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, (Real.log (f θ (x i)) - Real.log (f θ₀ (x i)))))) := by
  have hrm : Measurable (fun y ↦ ENNReal.ofReal (f θ y / f θ₀ y)) :=
    ((hf θ).1.div (hf θ₀).1).ennreal_ofReal
  have h1 : P θ = (P θ₀).withDensity (fun y ↦ ENNReal.ofReal (f θ y / f θ₀ y)) := by
    rw [(hf θ₀).2.2, ← withDensity_mul _ (hf θ₀).1.ennreal_ofReal hrm]
    conv_lhs => rw [(hf θ).2.2]
    congr 1
    funext y
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hpos θ₀ y).le, mul_div_cancel₀ _ (hpos θ₀ y).ne']
  have hσ : ∀ _ : Fin n,
      SigmaFinite ((P θ₀).withDensity (fun y ↦ ENNReal.ofReal (f θ y / f θ₀ y))) := fun _ ↦ by
    rw [← h1]; have := hP θ; infer_instance
  have hP0 := hP θ₀
  rw [show (fun _ : Fin n ↦ P θ) = fun _ ↦ (P θ₀).withDensity
      (fun y ↦ ENNReal.ofReal (f θ y / f θ₀ y)) from funext fun _ ↦ h1,
    TauCeti.pi_withDensity (fun _ : Fin n ↦ P θ₀) (fun _ ↦ hrm)]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (div_pos (hpos θ _) (hpos θ₀ _)).le),
    Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Real.exp_sub, Real.exp_log (hpos θ _), Real.exp_log (hpos θ₀ _)]

/-- If `X ~ N(m, I)` with `I > 0`, then `X² / I` has the noncentral chi-squared law with one
degree of freedom and noncentrality `m² / I`. -/
theorem gaussianReal_map_sq_div_eq_noncentralChiSquared {I : ℝ} (hI : 0 < I) (m : ℝ) :
    (gaussianReal m (Real.toNNReal I)).map (fun z ↦ z ^ 2 / I) =
      TauCeti.Probability.noncentralChiSquaredMeasure 1 (Real.toNNReal (m ^ 2 / I)) := by
  have hs : 0 < Real.sqrt I := Real.sqrt_pos.2 hI
  have hcomp : (fun z : ℝ ↦ z ^ 2 / I) = (fun y : ℝ ↦ y ^ 2) ∘ (fun z ↦ (Real.sqrt I)⁻¹ * z) := by
    funext z
    simp only [Function.comp_apply, mul_pow, inv_pow, Real.sq_sqrt hI.le]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul]
  convert TauCeti.Probability.gaussianReal_map_sq_noncentral ((Real.sqrt I)⁻¹ * m) using 2
  · congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hI.le, inv_pow,
      Real.sq_sqrt hI.le, NNReal.coe_one]
    field_simp
  · ext
    simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, Real.coe_toNNReal _
      (div_nonneg (sq_nonneg m) hI.le), mul_pow, inv_pow, Real.sq_sqrt hI.le]
    ring

/-- Exponential tilting of a centred Gaussian law: the density `exp (h z - h² I / 2)` turns
`N(0, I)` into `N(h I, I)`. -/
theorem gaussianReal_withDensity_exp_eq {I : ℝ} (hI : 0 < I) (h : ℝ) :
    (gaussianReal 0 (Real.toNNReal I)).withDensity
        (fun z ↦ ENNReal.ofReal (Real.exp (h * z - h ^ 2 * I / 2))) =
      gaussianReal (h * I) (Real.toNNReal I) := by
  have hv : Real.toNNReal I ≠ 0 := by simpa using hI
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext z
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hI.le]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- A density on an image measure is the image of the composed density. -/
theorem map_withDensity_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {ψ : α → β} (hψ : Measurable ψ) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (μ.map ψ).withDensity g = (μ.withDensity (g ∘ ψ)).map ψ := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hψ hs, withDensity_apply _ (hψ hs),
    setLIntegral_map hs hg hψ]
  rfl

/-- The joint limit law of the test statistic and the log likelihood ratio under the null,
`(Z² / I, h Z - h² I / 2)` with `Z ~ N(0, I)`, tilted by the likelihood ratio, has the
noncentral chi-squared first marginal of the local alternative, and the likelihood ratio has
mean one. -/
theorem noncentral_limit_of_tilt {I : ℝ} (hI : 0 < I) (h : ℝ) :
    let ν := (gaussianReal 0 (Real.toNNReal I)).map
      (fun z ↦ (z ^ 2 / I, h * z - h ^ 2 * I / 2));
    (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp z.2)).map Prod.fst =
        TauCeti.Probability.noncentralChiSquaredMeasure 1 (Real.toNNReal (h ^ 2 * I)) ∧
      (∫ z, Real.exp z.2 ∂ν) = 1 := by
  intro ν
  have hψ : Measurable (fun z : ℝ ↦ (z ^ 2 / I, h * z - h ^ 2 * I / 2)) := by fun_prop
  have hg : Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp z.2)) := by fun_prop
  have htilt := gaussianReal_withDensity_exp_eq hI h
  constructor
  · rw [map_withDensity_eq _ hψ hg, Measure.map_map measurable_fst hψ]
    have : ((fun z : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp z.2)) ∘
        fun z : ℝ ↦ (z ^ 2 / I, h * z - h ^ 2 * I / 2)) =
        fun z ↦ ENNReal.ofReal (Real.exp (h * z - h ^ 2 * I / 2)) := rfl
    rw [this, htilt]
    have h2 : (Prod.fst ∘ fun z : ℝ ↦ (z ^ 2 / I, h * z - h ^ 2 * I / 2)) =
        fun z ↦ z ^ 2 / I := rfl
    rw [h2, gaussianReal_map_sq_div_eq_noncentralChiSquared hI]
    congr 2
    field_simp
  · rw [integral_map hψ.aemeasurable (by fun_prop)]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)
      (by fun_prop)]
    have := congrArg (fun m : Measure ℝ ↦ (m univ).toReal) htilt
    simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      measure_univ, ENNReal.toReal_one] at this
    exact this

/-- Componentwise convergence to zero in probability gives convergence to zero of the pair. -/
theorem tendstoInProbabilityConst_prodMk_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U V : ℕ → Ω → ℝ)
    (hU : TendstoInProbabilityConst μ U 0) (hV : TendstoInProbabilityConst μ V 0) :
    TendstoInProbabilityConst μ (fun n ω ↦ (U n ω, V n ω)) 0 := by
  intro ε hε
  have h := (hU ε hε).add (hV ε hε)
  rw [add_zero] at h
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) h
  refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
  intro ω hω
  simp only [mem_ofPred_eq, mem_union, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
    lt_max_iff] at hω ⊢
  exact hω
/-- Second-order expansions behind the likelihood-ratio, Wald, and score tests of a scalar
simple null, on one probability space carrying an iid sample. Under the hypotheses of
`mle_asymptotic_linearization_and_normality`, with `aₙ = √n (Tₙ - θ₀)` and the normalized
score `Zₙ`, the likelihood-ratio statistic, the score statistic `Zₙ² / I`, and every
plug-in Wald statistic `aₙ² J(Tₙ)` with `J` continuous at `θ₀` and `J θ₀ = I` differ from
`I aₙ²` by `o_P(1)`, and the log likelihood ratio at `θ₀ + h / √n` equals
`h Zₙ - h² I / 2 + o_P(1)`. -/
theorem likelihood_test_expansions_of_iid
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (ell : ℝ → E → ℝ)
    (hm : ∀ theta, Measurable (ell theta)) (hsmooth : ∀ x, ContDiff ℝ 3 (fun theta ↦ ell theta x))
    (theta₀ I : ℝ) (hI : 0 < I) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M P)
    (henv : ∀ x theta, |theta - theta₀| < r →
      |deriv (deriv (deriv (fun t ↦ ell t x))) theta| ≤ M x)
    (hscore : MemLp (fun x ↦ deriv (fun t ↦ ell t x) theta₀) 2 P)
    (hmean : (∫ x, deriv (fun t ↦ ell t x) theta₀ ∂P) = 0)
    (hvar : (∫ x, deriv (fun t ↦ ell t x) theta₀ ^ 2 ∂P) = I)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀) P)
    (hinfo : (∫ x, deriv (deriv (fun t ↦ ell t x)) theta₀ ∂P) = -I)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : ∀ n : ℕ, 1 ≤ n → ∀ᵐ w ∂mu,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0) :
    TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal I⁻¹)) ∧
      TendstoInDistribution mu (fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        deriv (fun t ↦ ell t (X i w)) theta₀) (gaussianReal 0 (Real.toNNReal I)) ∧
      TendstoInProbabilityConst mu (fun n w ↦
        2 * ∑ i ∈ Finset.range n, (ell (T n w) (X i w) - ell theta₀ (X i w)) -
          I * (Real.sqrt n * (T n w - theta₀)) ^ 2) 0 ∧
      TendstoInProbabilityConst mu (fun n w ↦
        ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) theta₀) ^ 2 / I -
          I * (Real.sqrt n * (T n w - theta₀)) ^ 2) 0 ∧
      (∀ J : ℝ → ℝ, ContinuousAt J theta₀ → J theta₀ = I →
        TendstoInProbabilityConst mu (fun n w ↦
          (Real.sqrt n * (T n w - theta₀)) ^ 2 * J (T n w) -
            I * (Real.sqrt n * (T n w - theta₀)) ^ 2) 0) ∧
      ∀ h : ℝ, TendstoInProbabilityConst mu (fun n w ↦
        ∑ i ∈ Finset.range n, (ell (theta₀ + h / Real.sqrt n) (X i w) - ell theta₀ (X i w)) -
          (h * ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
            deriv (fun t ↦ ell t (X i w)) theta₀) - h ^ 2 * I / 2)) 0 := by
  obtain ⟨hrem, ha⟩ := mle_asymptotic_linearization_and_normality mu P X hiid ell hm hsmooth
    theta₀ I hI r hr M hM henv hscore hmean hvar hhess hinfo T hT hcons hroot
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hc3 : ∀ x, ContDiff ℝ (2 + 1) (fun t ↦ ell t x) := hsmooth
  have hdiff : ∀ x, Differentiable ℝ (fun t ↦ ell t x) := fun x ↦
    (contDiff_succ_iff_deriv.1 (hc3 x)).1
  have hdiff1 : ∀ x, Differentiable ℝ (fun t ↦ deriv (fun s ↦ ell s x) t) := fun x ↦
    ((contDiff_succ_iff_deriv.1 (hc3 x)).2.2).differentiable (by norm_num)
  set S : E → ℝ := fun x ↦ deriv (fun t ↦ ell t x) theta₀ with hSdef
  set H : E → ℝ := fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀ with hHdef
  have hSm : Measurable S := measurable_deriv_param ell hm hdiff theta₀
  have hℓ1m : ∀ t, Measurable (fun x ↦ deriv (fun s ↦ ell s x) t) :=
    measurable_deriv_param ell hm hdiff
  have hHm : Measurable H :=
    measurable_deriv_param (fun t x ↦ deriv (fun s ↦ ell s x) t) hℓ1m hdiff1 theta₀
  set M' : E → ℝ := hM.aestronglyMeasurable.mk M with hM'def
  have hM'm : Measurable M' := hM.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMM' : M =ᵐ[P] M' := hM.aestronglyMeasurable.ae_eq_mk
  have hM'i : Integrable M' P := hM.congr hMM'
  have hMae : ∀ᵐ w ∂mu, ∀ i, M (X i w) = M' (X i w) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ x ∂(mu.map (X i)), M x = M' x := by rw [hlaw i]; exact hMM'
    exact ae_of_ae_map (hXm i).aemeasurable this
  have hM0 : ∀ x, 0 ≤ M x := fun x ↦ (abs_nonneg _).trans (henv x theta₀ (by simpa using hr))
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w) with hZ
  set B : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H (X i w) with hB
  set A : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M' (X i w) with hA
  set a : ℕ → Ω → ℝ := fun n w ↦ Real.sqrt n * (T n w - theta₀) with ha_def
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ hSm.comp (hXm i)).const_mul _
  have ham : ∀ n, Measurable (a n) := fun n ↦ ((hT n).sub_const _).const_mul _
  have hZlim : TendstoInDistribution mu Z (gaussianReal 0 (Real.toNNReal I)) := by
    have := tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu P X ⟨hXm, hind, hlaw⟩ S hSm
      hscore hmean
    rwa [hvar] at this
  have hBlim : TendstoInProbabilityConst mu B (-I) := by
    have := tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ H hHm hhess
    rwa [hinfo] at this
  have hAlim : TendstoInProbabilityConst mu A (∫ x, M' x ∂P) :=
    tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ M' hM'm hM'i
  have haB : IsBoundedInProbability mu a :=
    isBoundedInProbability_of_tendstoInDistribution mu a ham _ ha
  have hZB : IsBoundedInProbability mu Z :=
    isBoundedInProbability_of_tendstoInDistribution mu Z hZm _ hZlim
  have hAB : IsBoundedInProbability mu A :=
    isBoundedInProbability_of_tendstoInProbabilityConst mu A _ hAlim
  have hd : TendstoInProbabilityConst mu (fun n w ↦ T n w - theta₀) 0 := by
    intro ε hε; simpa [Real.dist_eq] using hcons ε hε
  have hBI : TendstoInProbabilityConst mu (fun n w ↦ B n w + I) 0 := by
    intro ε hε; simpa [Real.dist_eq, sub_neg_eq_add] using hBlim ε hε
  have he : TendstoInProbabilityConst mu (fun n w ↦ a n w - Z n w / I) 0 := by
    convert hrem using 3 with n w
    simp only [ha_def, hZ, mul_inv]
    ring
  have hsn : ∀ n : ℕ, 1 ≤ n → 0 < Real.sqrt n := fun n hn ↦
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnsq : ∀ n : ℕ, ((n : ℝ)) = Real.sqrt n ^ 2 := fun n ↦
    (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have hM'0 : ∀ᵐ w ∂mu, ∀ i, 0 ≤ M' (X i w) := by
    filter_upwards [hMae] with w hw i
    rw [← hw i]; exact hM0 _
  -- Taylor remainder bound for the sample log likelihood at a point `t` near `theta₀`
  have hTay : ∀ (n : ℕ) (w : Ω), (∀ i, M (X i w) = M' (X i w)) → ∀ t : ℝ, |t - theta₀| < r →
      |∑ i ∈ Finset.range n, (ell t (X i w) - ell theta₀ (X i w)) -
        ((t - theta₀) * ∑ i ∈ Finset.range n, S (X i w) +
          (t - theta₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, H (X i w))| ≤
        |t - theta₀| ^ 3 * ∑ i ∈ Finset.range n, M' (X i w) := by
    intro n w hw t ht
    have hsplit : ∑ i ∈ Finset.range n, (ell t (X i w) - ell theta₀ (X i w)) -
        ((t - theta₀) * ∑ i ∈ Finset.range n, S (X i w) +
          (t - theta₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, H (X i w)) =
        ∑ i ∈ Finset.range n, (ell t (X i w) - ell theta₀ (X i w) - (t - theta₀) * S (X i w) -
          (t - theta₀) ^ 2 / 2 * H (X i w)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hsplit, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    have h := abs_sub_taylor_two_le (fun t ↦ ell t (X i w)) (hsmooth _) theta₀ r (M (X i w))
      (fun t ht ↦ henv _ t ht) t ht
    rw [← hw i, mul_comm (|t - theta₀| ^ 3)]
    exact h
  have hLR : TendstoInProbabilityConst mu (fun n w ↦
      2 * ∑ i ∈ Finset.range n, (ell (T n w) (X i w) - ell theta₀ (X i w)) -
        I * a n w ^ 2) 0 := by
    have h1 : TendstoInProbabilityConst mu
        (fun n w ↦ (-2 * I) * (a n w * (a n w - Z n w / I))) 0 :=
      tendstoInProbabilityConst_const_mul_zero mu _ _
        (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB he)
    have h2 : TendstoInProbabilityConst mu (fun n w ↦ a n w * (a n w * (B n w + I))) 0 :=
      tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB
        (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB hBI)
    have hX3 : TendstoInProbabilityConst mu
        (fun n w ↦ 2 * (a n w * (a n w * (A n w * (T n w - theta₀))))) 0 :=
      tendstoInProbabilityConst_const_mul_zero mu _ _
        (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB
          (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB
            (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ hAB hd)))
    have h3 : TendstoInProbabilityConst mu (fun n w ↦
        (2 * ∑ i ∈ Finset.range n, (ell (T n w) (X i w) - ell theta₀ (X i w)) -
          I * a n w ^ 2) - (-2 * I) * (a n w * (a n w - Z n w / I)) -
          a n w * (a n w * (B n w + I))) 0 := by
      refine tendstoInProbabilityConst_zero_of_abs_le mu _ _ (fun n w ↦ T n w - theta₀) hr ?_
        hX3 hd
      filter_upwards [eventually_ge_atTop 1] with n hn
      filter_upwards [hMae, hM'0] with w hw hw0 hdr
      have hb := hTay n w hw (T n w) hdr
      have hs := hsn n hn
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, M' (X i w) := Finset.sum_nonneg fun i _ ↦ hw0 i
      have key : ∀ s d sS sH L : ℝ, s ≠ 0 →
          (2 * L - I * (s * d) ^ 2) - (-2 * I) * (s * d * (s * d - (s⁻¹ * sS) / I)) -
            s * d * (s * d * ((s ^ 2)⁻¹ * sH + I)) = 2 * (L - (d * sS + d ^ 2 / 2 * sH)) := by
        intro s d sS sH L hs0
        field_simp
        ring
      have key2 : ∀ s d sM : ℝ, s ≠ 0 →
          2 * (s * d * (s * d * ((s ^ 2)⁻¹ * sM * d))) = 2 * (d ^ 3 * sM) := by
        intro s d sM hs0
        field_simp
      have hinv : ((n : ℝ))⁻¹ = (Real.sqrt n ^ 2)⁻¹ := by rw [← hnsq n]
      have heq := key (Real.sqrt n) (T n w - theta₀) (∑ i ∈ Finset.range n, S (X i w))
        (∑ i ∈ Finset.range n, H (X i w))
        (∑ i ∈ Finset.range n, (ell (T n w) (X i w) - ell theta₀ (X i w))) hs.ne'
      have heq2 := key2 (Real.sqrt n) (T n w - theta₀) (∑ i ∈ Finset.range n, M' (X i w)) hs.ne'
      simp only [ha_def, hZ, hB, hA, hinv]
      rw [heq, heq2, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hsum0]
      gcongr
    have := tendstoInProbabilityConst_add_zero mu _ _
      (tendstoInProbabilityConst_add_zero mu _ _ h1 h2) h3
    convert this using 3 with n w
    ring
  have hinv : ∀ n : ℕ, ((n : ℝ))⁻¹ = (Real.sqrt n ^ 2)⁻¹ := fun n ↦ by rw [← hnsq n]
  have hSc : TendstoInProbabilityConst mu (fun n w ↦ Z n w ^ 2 / I - I * a n w ^ 2) 0 := by
    have h1 := tendstoInProbabilityConst_const_mul_zero mu _ (-1)
      (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ hZB he)
    have h2 := tendstoInProbabilityConst_const_mul_zero mu _ (-I)
      (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB he)
    have := tendstoInProbabilityConst_add_zero mu _ _ h1 h2
    convert this using 3 with n w
    field_simp
    ring
  have hJ : ∀ J : ℝ → ℝ, ContinuousAt J theta₀ → J theta₀ = I →
      TendstoInProbabilityConst mu (fun n w ↦ a n w ^ 2 * J (T n w) - I * a n w ^ 2) 0 := by
    intro J hJc hJI
    have hJT : TendstoInProbabilityConst mu (fun n w ↦ J (T n w) - I) 0 := by
      have := tendstoInProbabilityConst_comp_of_continuousAt mu T theta₀ J hJc hcons
      intro ε hε
      simpa [Real.dist_eq, hJI] using this ε hε
    have := tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB
      (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ haB hJT)
    convert this using 3 with n w
    ring
  have hLam : ∀ h : ℝ, TendstoInProbabilityConst mu (fun n w ↦
      ∑ i ∈ Finset.range n, (ell (theta₀ + h / Real.sqrt n) (X i w) - ell theta₀ (X i w)) -
        (h * Z n w - h ^ 2 * I / 2)) 0 := by
    intro h
    have hs0 : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hU : TendstoInProbabilityConst mu (fun n _ ↦ h / Real.sqrt n) 0 :=
      tendstoInProbabilityConst_const_of_tendsto mu _ (by
        simpa [div_eq_mul_inv] using hs0.const_mul h)
    have h1 := tendstoInProbabilityConst_const_mul_zero mu _ (h ^ 2 / 2) hBI
    have hX : TendstoInProbabilityConst mu
        (fun n w ↦ |h| ^ 3 * (A n w * (Real.sqrt n)⁻¹)) 0 :=
      tendstoInProbabilityConst_const_mul_zero mu _ _
        (tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu _ _ hAB
          (tendstoInProbabilityConst_const_of_tendsto mu _ hs0))
    have h2 : TendstoInProbabilityConst mu (fun n w ↦
        (∑ i ∈ Finset.range n, (ell (theta₀ + h / Real.sqrt n) (X i w) - ell theta₀ (X i w)) -
          (h * Z n w - h ^ 2 * I / 2)) - h ^ 2 / 2 * (B n w + I)) 0 := by
      refine tendstoInProbabilityConst_zero_of_abs_le mu _ _ (fun n _ ↦ h / Real.sqrt n) hr ?_
        hX hU
      filter_upwards [eventually_ge_atTop 1] with n hn
      filter_upwards [hMae, hM'0] with w hw hw0 hdr
      have hs := hsn n hn
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range n, M' (X i w) := Finset.sum_nonneg fun i _ ↦ hw0 i
      have hb := hTay n w hw (theta₀ + h / Real.sqrt n) (by simpa using hdr)
      rw [add_sub_cancel_left] at hb
      have key3 : ∀ s sS sH L : ℝ, s ≠ 0 →
          (L - (h * (s⁻¹ * sS) - h ^ 2 * I / 2)) - h ^ 2 / 2 * ((s ^ 2)⁻¹ * sH + I) =
            L - (h / s * sS + (h / s) ^ 2 / 2 * sH) := by
        intro s sS sH L hs0
        field_simp
        ring
      have key4 : |h| ^ 3 * ((Real.sqrt n ^ 2)⁻¹ * (∑ i ∈ Finset.range n, M' (X i w)) *
          (Real.sqrt n)⁻¹) = |h / Real.sqrt n| ^ 3 * ∑ i ∈ Finset.range n, M' (X i w) := by
        rw [abs_div, abs_of_pos hs]
        field_simp
      simp only [hZ, hB, hA, hinv]
      rw [key3 _ _ _ _ hs.ne', key4, abs_of_nonneg (mul_nonneg (by positivity) hsum0)]
      exact hb
    have := tendstoInProbabilityConst_add_zero mu _ _ h1 h2
    convert this using 3 with n w
    ring
  exact ⟨ha, hZlim, hLR, hSc, hJ, hLam⟩

/-- Reduction of the scalar likelihood tests to the squared normalized score, on the coordinate
process of the infinite product `P θ₀ ^ ℕ`. Under the hypotheses of
`tendstoWeakly_likelihoodRatio_wald_score_chiSquared`, the three statistics are measurable, the
normalized score `Zₙ` of the first `n` coordinates converges in law to `N(0, I(θ₀))`, each of the
three statistics of the first `n` coordinates differs from `Zₙ² / I(θ₀)` by `o_P(1)`, and the log
likelihood ratio of `θ₀ + h / √n` against `θ₀` equals `h Zₙ - h² I(θ₀) / 2 + o_P(1)`. -/
theorem likelihood_tests_sub_score_sq_infinitePi
    {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x)))
    (θ₀ : ℝ) (hIc : ContinuousAt (fisherInformation P f) θ₀)
    (hI : 0 < fisherInformation P f θ₀) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M (P θ₀))
    (henv : ∀ x θ, |θ - θ₀| < r →
      |deriv (deriv (deriv (fun t ↦ Real.log (f t x)))) θ| ≤ M x)
    (hscore : MemLp (likelihoodScore f θ₀) 2 (P θ₀))
    (hmean : (∫ x, likelihoodScore f θ₀ x ∂P θ₀) = 0)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ Real.log (f t x))) θ₀) (P θ₀))
    (hinfo : (∫ x, deriv (deriv (fun t ↦ Real.log (f t x))) θ₀ ∂P θ₀) =
      -fisherInformation P f θ₀)
    (T : ∀ n, (Fin n → E) → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
      (fun n x ↦ T n x - θ₀))
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀), ∀ θ,
      sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x (T n x)) :
    let I := fisherInformation P f;
    let μ := Measure.infinitePi fun _ : ℕ ↦ P θ₀;
    let Z := fun (n : ℕ) (ω : ℕ → E) ↦
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, likelihoodScore f θ₀ (ω i);
    let LR := fun n (x : Fin n → E) ↦
      likelihoodRatioStatistic (sampleLogLikelihood f x (T n x)) (sampleLogLikelihood f x θ₀);
    let W := fun n (x : Fin n → E) ↦ scalarWaldStatistic I n (T n x) θ₀;
    let S := fun n (x : Fin n → E) ↦ scalarScoreStatistic f I x θ₀;
    (∀ n, Measurable (LR n)) ∧ (∀ n, Measurable (W n)) ∧ (∀ n, Measurable (S n)) ∧
      (∀ n, Measurable (Z n)) ∧
      TendstoInDistribution μ Z (gaussianReal 0 (Real.toNNReal (I θ₀))) ∧
      TendstoInProbabilityConst μ (fun n ω ↦ LR n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 ∧
      TendstoInProbabilityConst μ (fun n ω ↦ W n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 ∧
      TendstoInProbabilityConst μ (fun n ω ↦ S n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 ∧
      ∀ h : ℝ, TendstoInProbabilityConst μ (fun n ω ↦
        (∑ i : Fin n, (Real.log (f (θ₀ + h / Real.sqrt n) (ω i)) - Real.log (f θ₀ (ω i)))) -
          (h * Z n ω - h ^ 2 * I θ₀ / 2)) 0 := by
  intro I μ Z LR W S
  have hP0 := hP θ₀
  set X : ℕ → (ℕ → E) → E := fun i ω ↦ ω i with hX
  have hiid : IsIndependentIdenticallyDistributed μ X (P θ₀) := iid_infinitePi_eval (P θ₀)
  have hρm : ∀ n, Measurable (fun ω : ℕ → E ↦ fun i : Fin n ↦ X i ω) := fun n ↦
    measurable_pi_iff.2 fun i : Fin n ↦ hiid.1 i
  set ell : ℝ → E → ℝ := fun θ x ↦ Real.log (f θ x) with hell
  have hm : ∀ θ, Measurable (ell θ) := fun θ ↦ (hf θ).1.log
  have hdiff : ∀ x, Differentiable ℝ (fun t ↦ ell t x) := fun x ↦
    (hsmooth x).differentiable (by norm_num)
  have hellm : Measurable (Function.uncurry ell) :=
    measurable_uncurry_of_continuous_of_measurable (fun x ↦ (hsmooth x).continuous) hm
  set T' : ℕ → (ℕ → E) → ℝ := fun n ω ↦ T n (fun i : Fin n ↦ X i ω) with hT'def
  have hT' : ∀ n, Measurable (T' n) := fun n ↦ (hT n).comp (hρm n)
  have hcons' : TendstoInProbabilityConst μ T' θ₀ := by
    have := (tendstoInProbabilityZero_pi_iff_of_iid μ (P θ₀) X hiid (fun n x ↦ T n x - θ₀)
      (fun n ↦ (hT n).sub_const _)).1 hcons
    intro ε hε
    simpa [Real.dist_eq] using this ε hε
  have hroot' : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i ω)) (T' n ω)) = 0 := by
    intro n hn
    have h1 := hmax n hn
    rw [← map_fin_eq_pi_of_iid μ (P θ₀) X hiid n] at h1
    filter_upwards [ae_of_ae_map (hρm n).aemeasurable h1] with ω hω
    have := sum_likelihoodScore_eq_zero_of_isMax f hdiff _ _ hω
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ deriv (fun t ↦ ell t (X i ω)) (T' n ω)) n]
    exact this
  obtain ⟨-, hZlim, hLR, hSc, hJ, hLam⟩ := likelihood_test_expansions_of_iid μ (P θ₀) X hiid ell
    hm hsmooth θ₀ (I θ₀) hI r hr M hM henv hscore hmean rfl hhess hinfo T' hT' hcons' hroot'
  have hsLLm : ∀ n (t : (Fin n → E) → ℝ), Measurable t →
      Measurable (fun x : Fin n → E ↦ sampleLogLikelihood f x (t x)) := fun n t ht ↦
    Finset.measurable_sum _ fun i _ ↦ hellm.comp (ht.prodMk (measurable_pi_apply i))
  have hLRm : ∀ n, Measurable (LR n) := fun n ↦
    ((hsLLm n _ (hT n)).sub (hsLLm n _ measurable_const)).const_mul 2
  have hIm : Measurable I := measurable_fisherInformation P ν f hf hpos hsmooth
  have hWm : ∀ n, Measurable (W n) := fun n ↦
    (((hT n).sub_const θ₀).pow_const 2).const_mul _ |>.mul (hIm.comp (hT n))
  have hscm : Measurable (likelihoodScore f θ₀) :=
    measurable_deriv_param (fun t x ↦ Real.log (f t x)) hm hdiff θ₀
  have hSeq0 : ∀ n (x : Fin n → E), S n x = (∑ i, likelihoodScore f θ₀ (x i)) ^ 2 / (n * I θ₀) :=
    fun n x ↦ by simp only [S, scalarScoreStatistic, deriv_sampleLogLikelihood f hdiff]
  have hSm : ∀ n, Measurable (S n) := fun n ↦ by
    have : S n = fun x ↦ (∑ i, likelihoodScore f θ₀ (x i)) ^ 2 / (n * I θ₀) :=
      funext (hSeq0 n)
    rw [this]
    exact ((Finset.measurable_sum _ fun i _ ↦ hscm.comp (measurable_pi_apply i)).pow_const
      2).div_const _
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_sum _ fun i _ ↦ hscm.comp (measurable_pi_apply i)).const_mul _
  -- each statistic minus `I aₙ²` is negligible; so is `Zₙ² / I - I aₙ²`
  set Xq : ℕ → (ℕ → E) → ℝ := fun n ω ↦ I θ₀ * (Real.sqrt n * (T' n ω - θ₀)) ^ 2 with hXq
  have hLRd : TendstoInProbabilityConst μ
      (fun n ω ↦ LR n (fun i : Fin n ↦ X i ω) - Xq n ω) 0 := by
    convert hLR using 3 with n ω
    simp only [LR, likelihoodRatioStatistic, sampleLogLikelihood, ← Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (f (T' n ω) (X i ω)) -
      Real.log (f θ₀ (X i ω))) n]
  have hWd : TendstoInProbabilityConst μ
      (fun n ω ↦ W n (fun i : Fin n ↦ X i ω) - Xq n ω) 0 := by
    convert hJ I hIc rfl using 3 with n ω
    simp only [W, Xq, T', scalarWaldStatistic, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hSq : ∀ n ω, S n (fun i : Fin n ↦ X i ω) = Z n ω ^ 2 / I θ₀ := by
    intro n ω
    rw [hSeq0, Fin.sum_univ_eq_sum_range (fun i ↦ likelihoodScore f θ₀ (X i ω)) n]
    simp only [Z, X, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hZd : TendstoInProbabilityConst μ (fun n ω ↦ Z n ω ^ 2 / I θ₀ - Xq n ω) 0 := hSc
  have hfix : ∀ V : ∀ n, (Fin n → E) → ℝ,
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ X i ω) - Xq n ω) 0 →
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 := by
    intro V hV
    have := tendstoInProbabilityConst_add_zero μ _ _ hV
      (tendstoInProbabilityConst_const_mul_zero μ _ (-1) hZd)
    convert this using 3 with n ω
    ring
  refine ⟨hLRm, hWm, hSm, hZm, hZlim, hfix LR hLRd, hfix W hWd, ?_, fun h ↦ ?_⟩
  · have : (fun n ω ↦ S n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) = fun _ _ ↦ (0 : ℝ) := by
      funext n ω
      rw [hSq n ω, sub_self]
    rw [this]
    exact tendstoInProbabilityConst_const_of_tendsto μ _ tendsto_const_nhds
  · convert hLam h using 3 with n ω
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (f (θ₀ + h / Real.sqrt n) (ω i)) -
      Real.log (f θ₀ (ω i))) n]
    rfl

/-- GAPS 102.11, null part, for a scalar parameter and the simple null `Θ₀ = {θ₀}`
(so `q = k = 1`, `c(θ) = θ - θ₀`, and the restricted maximizer is `θ₀`). Under the
hypotheses of 102.3 at `θ₀` with Fisher information continuous at `θ₀`, and for consistent
global maximizers `T n` of the sample log likelihood, the likelihood-ratio, Wald, and score
statistics each converge in law to `χ²₁` under `P θ₀`, and the Wald and score statistics differ
from the likelihood-ratio statistic by `o_P(1)`. Composite nulls with `q < k` are outside
this scope. -/
theorem tendstoWeakly_likelihoodRatio_wald_score_chiSquared
    {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x)))
    (θ₀ : ℝ) (hIc : ContinuousAt (fisherInformation P f) θ₀)
    (hI : 0 < fisherInformation P f θ₀) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M (P θ₀))
    (henv : ∀ x θ, |θ - θ₀| < r →
      |deriv (deriv (deriv (fun t ↦ Real.log (f t x)))) θ| ≤ M x)
    (hscore : MemLp (likelihoodScore f θ₀) 2 (P θ₀))
    (hmean : (∫ x, likelihoodScore f θ₀ x ∂P θ₀) = 0)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ Real.log (f t x))) θ₀) (P θ₀))
    (hinfo : (∫ x, deriv (deriv (fun t ↦ Real.log (f t x))) θ₀ ∂P θ₀) =
      -fisherInformation P f θ₀)
    (T : ∀ n, (Fin n → E) → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
      (fun n x ↦ T n x - θ₀))
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀), ∀ θ,
      sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x (T n x)) :
    let I := fisherInformation P f;
    let LR := fun n (x : Fin n → E) ↦
      likelihoodRatioStatistic (sampleLogLikelihood f x (T n x)) (sampleLogLikelihood f x θ₀);
    let W := fun n (x : Fin n → E) ↦ scalarWaldStatistic I n (T n x) θ₀;
    let S := fun n (x : Fin n → E) ↦ scalarScoreStatistic f I x θ₀;
    TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (LR n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (W n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (S n))
        (TauCeti.Probability.chiSquaredMeasure 1) ∧
      TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
        (fun n x ↦ LR n x - W n x) ∧
      TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
        (fun n x ↦ LR n x - S n x) := by
  intro I LR W S
  have hP0 := hP θ₀
  obtain ⟨hLRm, hWm, hSm, hZm, hZlim, hLRd, hWd, hSd, -⟩ :=
    likelihood_tests_sub_score_sq_infinitePi P hP ν f hf hpos hsmooth θ₀ hIc hI r hr M hM henv
      hscore hmean hhess hinfo T hT hcons hmax
  set μ : Measure (ℕ → E) := Measure.infinitePi fun _ : ℕ ↦ P θ₀ with hμ
  have hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ ω i) (P θ₀) :=
    iid_infinitePi_eval (P θ₀)
  have hρm : ∀ n, Measurable (fun ω : ℕ → E ↦ fun i : Fin n ↦ ω i) := fun n ↦
    measurable_pi_iff.2 fun i : Fin n ↦ hiid.1 i
  set Z := fun (n : ℕ) (ω : ℕ → E) ↦
    (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, likelihoodScore f θ₀ (ω i) with hZ
  have hchi := TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure (k := 1) zero_le_one
  have hXqlim : TendstoInDistribution μ (fun n ω ↦ Z n ω ^ 2 / I θ₀)
      (TauCeti.Probability.chiSquaredMeasure 1) := by
    have := tendstoInDistribution_comp_of_continuous μ Z hZm _ (fun z ↦ z ^ 2 / I θ₀)
      (by fun_prop) hZlim
    rwa [gaussianReal_map_sq_div_eq_noncentralChiSquared hI, zero_pow two_ne_zero, zero_div,
      Real.toNNReal_zero, TauCeti.Probability.noncentralChiSquaredMeasure_zero_noncentrality]
      at this
  have conv : ∀ V : ∀ n, (Fin n → E) → ℝ, (∀ n, Measurable (V n)) →
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 →
      TendstoWeakly (fun n ↦ (Measure.pi fun _ : Fin n ↦ P θ₀).map (V n))
        (TauCeti.Probability.chiSquaredMeasure 1) := by
    intro V hV hVd
    refine tendstoWeakly_pi_of_tendstoInDistribution μ (P θ₀) _ hiid V hV _ ?_
    exact tendstoInDistribution_of_tendstoInProbabilityConst_sub μ _ _
      (fun n ↦ (hZm n).pow_const 2 |>.div_const _) (fun n ↦ (hV n).comp (hρm n)) _ hXqlim hVd
  have hdiffs : ∀ V V' : ∀ n, (Fin n → E) → ℝ, (∀ n, Measurable (V n)) →
      (∀ n, Measurable (V' n)) →
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 →
      TendstoInProbabilityConst μ (fun n ω ↦ V' n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 →
      TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
        (fun n x ↦ V n x - V' n x) := by
    intro V V' hV hV' h1 h2
    refine (tendstoInProbabilityZero_pi_iff_of_iid μ (P θ₀) _ hiid _
      (fun n ↦ (hV n).sub (hV' n))).2 ?_
    have := tendstoInProbabilityConst_add_zero μ _ _ h1
      (tendstoInProbabilityConst_const_mul_zero μ _ (-1) h2)
    convert this using 3 with n ω
    simp only [Pi.sub_apply]
    ring
  exact ⟨conv LR hLRm hLRd, conv W hWm hWd, conv S hSm hSd,
    hdiffs LR W hLRm hWm hLRd hWd, hdiffs LR S hLRm hSm hLRd hSd⟩

/-- GAPS 102.11, local-alternative part, in the scalar simple-null scope of
`tendstoWeakly_likelihoodRatio_wald_score_chiSquared`. If in addition the model is DQM at `θ₀`
with the likelihood score, then under `P (θ₀ + h / √n)` each of the three statistics converges
in law to the noncentral `χ²₁` with noncentrality `h² I(θ₀)`. -/
theorem tendstoWeakly_likelihoodRatio_wald_score_noncentralChiSquared
    {E : Type*} [MeasurableSpace E] (P : ℝ → Measure E) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (ν : Measure E) [SigmaFinite ν] (f : ℝ → E → ℝ) (hf : ∀ θ, HasDensity (P θ) ν (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (hsmooth : ∀ x, ContDiff ℝ 3 (fun θ ↦ Real.log (f θ x)))
    (θ₀ : ℝ) (hIc : ContinuousAt (fisherInformation P f) θ₀)
    (hI : 0 < fisherInformation P f θ₀) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M (P θ₀))
    (henv : ∀ x θ, |θ - θ₀| < r →
      |deriv (deriv (deriv (fun t ↦ Real.log (f t x)))) θ| ≤ M x)
    (hscore : MemLp (likelihoodScore f θ₀) 2 (P θ₀))
    (hmean : (∫ x, likelihoodScore f θ₀ x ∂P θ₀) = 0)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ Real.log (f t x))) θ₀) (P θ₀))
    (hinfo : (∫ x, deriv (deriv (fun t ↦ Real.log (f t x))) θ₀ ∂P θ₀) =
      -fisherInformation P f θ₀)
    (_hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (θ₀ + h) x) - Real.sqrt (f θ₀ x) -
        h / 2 * likelihoodScore f θ₀ x * Real.sqrt (f θ₀ x)) ^ 2 ∂ν) (fun h : ℝ ↦ h ^ 2))
    (T : ∀ n, (Fin n → E) → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInProbabilityZero (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀)
      (fun n x ↦ T n x - θ₀))
    (hmax : ∀ n : ℕ, 1 ≤ n → ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀), ∀ θ,
      sampleLogLikelihood f x θ ≤ sampleLogLikelihood f x (T n x)) (h : ℝ) :
    let I := fisherInformation P f;
    let LR := fun n (x : Fin n → E) ↦
      likelihoodRatioStatistic (sampleLogLikelihood f x (T n x)) (sampleLogLikelihood f x θ₀);
    let W := fun n (x : Fin n → E) ↦ scalarWaldStatistic I n (T n x) θ₀;
    let S := fun n (x : Fin n → E) ↦ scalarScoreStatistic f I x θ₀;
    let Q := fun n : ℕ ↦ Measure.pi fun _ : Fin n ↦ P (θ₀ + h / Real.sqrt n);
    let L := TauCeti.Probability.noncentralChiSquaredMeasure 1 (Real.toNNReal (h ^ 2 * I θ₀));
    TendstoWeakly (fun n ↦ (Q n).map (LR n)) L ∧
      TendstoWeakly (fun n ↦ (Q n).map (W n)) L ∧
      TendstoWeakly (fun n ↦ (Q n).map (S n)) L := by
  intro I LR W S Q L
  have hP0 := hP θ₀
  obtain ⟨hLRm, hWm, hSm, hZm, hZlim, hLRd, hWd, hSd, hΛ⟩ :=
    likelihood_tests_sub_score_sq_infinitePi P hP ν f hf hpos hsmooth θ₀ hIc hI r hr M hM henv
      hscore hmean hhess hinfo T hT hcons hmax
  set μ : Measure (ℕ → E) := Measure.infinitePi fun _ : ℕ ↦ P θ₀ with hμ
  have hiid : IsIndependentIdenticallyDistributed μ (fun i ω ↦ ω i) (P θ₀) :=
    iid_infinitePi_eval (P θ₀)
  have hρm : ∀ n, Measurable (fun ω : ℕ → E ↦ fun i : Fin n ↦ ω i) := fun n ↦
    measurable_pi_iff.2 fun i : Fin n ↦ hiid.1 i
  set Z := fun (n : ℕ) (ω : ℕ → E) ↦
    (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, likelihoodScore f θ₀ (ω i) with hZ
  set ψ : ℝ → ℝ × ℝ := fun z ↦ (z ^ 2 / I θ₀, h * z - h ^ 2 * I θ₀ / 2) with hψ
  have hψc : Continuous ψ := by fun_prop
  set ν₂ : Measure (ℝ × ℝ) := (gaussianReal 0 (Real.toNNReal (I θ₀))).map ψ with hν₂
  have hν₂p : IsProbabilityMeasure ν₂ := by rw [hν₂]; exact (Measure.isProbabilityMeasure_map_iff hψc.measurable.aemeasurable).2 inferInstance
  obtain ⟨hlaw, hmean1⟩ := noncentral_limit_of_tilt hI h
  have hint : Integrable (fun z : ℝ × ℝ ↦ Real.exp z.2) ν₂ := by
    by_contra hni
    rw [integral_undef hni] at hmean1
    exact zero_ne_one hmean1
  set Λ : ∀ n, (Fin n → E) → ℝ := fun n x ↦
    ∑ i, (Real.log (f (θ₀ + h / Real.sqrt n) (x i)) - Real.log (f θ₀ (x i))) with hΛdef
  have hΛm : ∀ n, Measurable (Λ n) := fun n ↦ Finset.measurable_sum _ fun i _ ↦
    ((hf _).1.log.comp (measurable_pi_apply i)).sub ((hf _).1.log.comp (measurable_pi_apply i))
  have hQ : ∀ n, IsProbabilityMeasure (Q n) := fun n ↦ by
    have := hP (θ₀ + h / Real.sqrt n); infer_instance
  have hrn : ∀ n, Q n = (Measure.pi fun _ : Fin n ↦ P θ₀).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (Λ n x))) := fun n ↦
    pi_eq_withDensity_exp_sum_log_sub P hP ν f hf hpos _ θ₀ n
  have alt : ∀ V : ∀ n, (Fin n → E) → ℝ, (∀ n, Measurable (V n)) →
      TendstoInProbabilityConst μ (fun n ω ↦ V n (fun i : Fin n ↦ ω i) - Z n ω ^ 2 / I θ₀) 0 →
      TendstoWeakly (fun n ↦ (Q n).map (V n)) L := by
    intro V hV hVd
    have hjoint : TendstoInDistribution μ
        (fun n ω ↦ (V n (fun i : Fin n ↦ ω i), Λ n (fun i : Fin n ↦ ω i))) ν₂ := by
      refine tendstoInDistribution_of_tendstoInProbabilityConst_sub μ (fun n ω ↦ ψ (Z n ω)) _
        (fun n ↦ hψc.measurable.comp (hZm n))
        (fun n ↦ ((hV n).comp (hρm n)).prodMk ((hΛm n).comp (hρm n))) ν₂
        (tendstoInDistribution_comp_of_continuous μ Z hZm _ ψ hψc hZlim) ?_
      have := tendstoInProbabilityConst_prodMk_zero μ _ _ hVd (hΛ h)
      convert this using 3 with n ω
      simp only [ψ, Λ, Prod.mk_sub_mk, Function.comp_apply, I]
    have hpi := tendstoWeakly_pi_of_tendstoInDistribution μ (P θ₀) _ hiid
      (fun n x ↦ (V n x, Λ n x)) (fun n ↦ (hV n).prodMk (hΛm n)) ν₂ hjoint
    have := tendstoWeakly_of_log_likelihood_ratio_dependent
      (fun n ↦ Measure.pi fun _ : Fin n ↦ P θ₀) Q (fun n ↦ inferInstance) hQ V Λ hV hΛm hrn ν₂
      hpi hint hmean1
    rwa [hlaw] at this
  exact ⟨alt LR hLRm hLRd, alt W hWm hWd, alt S hSm hSd⟩

/-- The Wald statistic vanishes at the null value. -/
@[simp] theorem scalarWaldStatistic_self (I : ℝ → ℝ) (n : ℕ) (θ₀ : ℝ) :
    scalarWaldStatistic I n θ₀ θ₀ = 0 := by
  simp [scalarWaldStatistic]

end CKSD
