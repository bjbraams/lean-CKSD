module

public import CKSD.Bayes.Basic
public import CKSD.Asymptotics.Basic

/-!
# Particle filters and weak diffusion equations

A Feynman–Kac specification consists of Markov transitions and positive bounded potentials.
Its unnormalized laws and bootstrap proposal laws are explicit measure constructions. Weak
Fokker–Planck solutions are specified by their integral identity on smooth compactly supported tests;
this definition does not assert existence of an SDE solution or supply a stochastic integral.
Sources: GAPS 104.37–104.60, 104.63, and 104.75–104.76.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Feynman–Kac model with fixed observations encoded in its potentials. -/
structure FeynmanKacModel (X : Type*) [MeasurableSpace X] where
  /-- Initial probability law. -/
  initial : ProbabilityMeasure X
  /-- Transition kernel from generation `n` to generation `n+1`. -/
  transition : ℕ → Kernel X X
  /-- Each transition is Markov. -/
  isMarkov_transition : ∀ n, IsMarkovKernel (transition n)
  /-- Observation potential of each generation. -/
  potential : ℕ → X → ℝ
  /-- Measurability of each potential. -/
  measurable_potential : ∀ n, Measurable (potential n)
  /-- Upper and positive lower bounds, allowed to depend on the time. -/
  potential_bounds : ∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ x, potential n x ∈ Icc a b

/-- The positive lower potential bound implies pointwise strict positivity. -/
theorem FeynmanKacModel.potential_pos {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) (x : X) : 0 < M.potential n x := by
  obtain ⟨a, b, ha, hbounds⟩ := M.potential_bounds n
  exact ha.trans_le (hbounds x).1

/-- Unnormalized Feynman–Kac measure at generation `n`. -/
def FeynmanKacModel.unnormalizedLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) : ℕ → Measure X
  | 0 => M.initial
  | n + 1 => M.transition n ∘ₘ (M.unnormalizedLaw n).withDensity
      (fun x ↦ ENNReal.ofReal (M.potential n x))

/-- Normalized filtering law. -/
def FeynmanKacModel.filterLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : Measure X :=
  (M.unnormalizedLaw n univ)⁻¹ • M.unnormalizedLaw n

/-- Bootstrap prediction law from the weighted particles at the current generation. -/
def FeynmanKacModel.particlePredictionLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (n : ℕ) (x : Fin N → X) : Measure X :=
  (∑ i, ENNReal.ofReal (M.potential n (x i)))⁻¹ •
    ∑ i, ENNReal.ofReal (M.potential n (x i)) • M.transition n (x i)

/-- Bootstrap-particle likelihood estimate as a product of mean potentials. -/
def FeynmanKacModel.particleLikelihood {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (particles : ℕ → Fin N → X) (n : ℕ) : ℝ :=
  ∏ p ∈ Finset.range n, (∑ i, M.potential p (particles p i)) / N

/-- Bootstrap sampling: conditional on the entire past, next particles are independent draws
from the weighted prediction law. This specifies a simulation protocol rather than its limits. -/
def IsBootstrapParticleSystem {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : FeynmanKacModel X) (N : ℕ) (ξ : ℕ → Ω → Fin N → X) : Prop :=
  (∀ n, Measurable (ξ n)) ∧
    P.map (ξ 0) = Measure.pi (fun _ : Fin N ↦ (M.initial : Measure X)) ∧
    ∀ n, ∀ᵐ ω ∂P,
      condDistrib (ξ (n + 1)) (fun (ω : Ω) (i : Fin (n + 1)) ↦ ξ i.val ω) P
        (fun i : Fin (n + 1) ↦ ξ i.val ω) =
          Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω))

/-- Integral against the bootstrap prediction law: the potential-weighted average of the
transition integrals from the current particles. -/
theorem FeynmanKacModel.lintegral_particlePredictionLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (n : ℕ) (x : Fin N → X) (φ : X → ℝ≥0∞) :
    ∫⁻ y, φ y ∂M.particlePredictionLaw n x =
      (∑ i, ENNReal.ofReal (M.potential n (x i)))⁻¹ *
        ∑ i, ENNReal.ofReal (M.potential n (x i)) * ∫⁻ y, φ y ∂M.transition n (x i) := by
  simp only [FeynmanKacModel.particlePredictionLaw, lintegral_smul_measure,
    lintegral_finsetSum_measure, smul_eq_mul]

/-- With at least one particle, the bootstrap prediction law is a probability measure. -/
theorem FeynmanKacModel.isProbabilityMeasure_particlePredictionLaw {X : Type*}
    [MeasurableSpace X] (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N) (n : ℕ) (x : Fin N → X) :
    IsProbabilityMeasure (M.particlePredictionLaw n x) := by
  constructor
  have hS0 : (∑ i, ENNReal.ofReal (M.potential n (x i))) ≠ 0 := by
    rw [Ne, Finset.sum_eq_zero_iff]
    push Not
    exact ⟨⟨0, hN⟩, Finset.mem_univ _, by simpa using M.potential_pos n _⟩
  have hSt : (∑ i, ENNReal.ofReal (M.potential n (x i))) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top
  have hpl := M.lintegral_particlePredictionLaw n x (fun _ ↦ 1)
  have := M.isMarkov_transition n
  simp only [lintegral_one, measure_univ, mul_one] at hpl
  rwa [ENNReal.inv_mul_cancel hS0 hSt] at hpl

/-- For `N` independent draws from a probability law `ν`, `𝔼[∑ᵢ φ(Zᵢ)] = N ∫ φ dν`. -/
theorem lintegral_sum_comp_eval_pi {X : Type*} [MeasurableSpace X] {N : ℕ} (ν : Measure X)
    [IsProbabilityMeasure ν] {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, ∑ i, φ (z i) ∂Measure.pi (fun _ : Fin N ↦ ν) = N * ∫⁻ y, φ y ∂ν := by
  rw [lintegral_finsetSum (f := fun i (z : Fin N → X) ↦ φ (z i)) _
    fun i _ ↦ hφ.comp (measurable_pi_apply i)]
  simp_rw [(measurePreserving_eval (fun _ : Fin N ↦ ν) _).lintegral_comp hφ]
  simp

/-- One step of the unnormalized Feynman–Kac recursion `γₙ₊₁(φ) = γₙ(Gₙ Qₙ φ)`. -/
theorem FeynmanKacModel.lintegral_unnormalizedLaw_succ {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂M.unnormalizedLaw (n + 1) =
      ∫⁻ x, ENNReal.ofReal (M.potential n x) * ∫⁻ y, φ y ∂M.transition n x
        ∂M.unnormalizedLaw n := by
  rw [FeynmanKacModel.unnormalizedLaw, Measure.lintegral_bind
    (M.transition n).measurable.aemeasurable hφ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (M.measurable_potential n).ennreal_ofReal
      hφ.lintegral_kernel]
  rfl

/-- One resampling step of the bootstrap filter: conditionally on the first `n + 1` generations,
the sum of `φ` over the next generation has mean `N` times the prediction integral of `φ`. -/
theorem lintegral_mul_sum_bootstrap_succ {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X)
    (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ)
    (F : (Fin (n + 1) → Fin N → X) → ℝ≥0∞) (hF : Measurable F)
    {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, F (fun i : Fin (n + 1) ↦ ξ i ω) * ∑ i, φ (ξ (n + 1) ω i) ∂P =
      ∫⁻ ω, F (fun i : Fin (n + 1) ↦ ξ i ω) *
        (N * ∫⁻ y, φ y ∂M.particlePredictionLaw n (ξ n ω)) ∂P := by
  obtain ⟨hmeas, -, hcond⟩ := hξ
  set Y : Ω → Fin (n + 1) → Fin N → X := fun ω i ↦ ξ i ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  set H : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℝ≥0∞ :=
    fun p ↦ F p.1 * ∑ i, φ (p.2 i) with hH
  have hHm : Measurable H :=
    (hF.comp measurable_fst).mul (Finset.measurable_sum _ fun i _ ↦
      hφ.comp ((measurable_pi_apply i).comp measurable_snd))
  have hlhs : ∫⁻ ω, F (Y ω) * ∑ i, φ (ξ (n + 1) ω i) ∂P =
      ∫⁻ p, H p ∂(P.map fun ω ↦ (Y ω, ξ (n + 1) ω)) := by
    rw [lintegral_map hHm (hY.prodMk (hmeas (n + 1)))]
  change ∫⁻ ω, F (Y ω) * ∑ i, φ (ξ (n + 1) ω i) ∂P = _
  rw [hlhs, ← compProd_map_condDistrib hY.aemeasurable (hmeas (n + 1)).aemeasurable,
    Measure.lintegral_compProd hHm, lintegral_map _ hY]
  · refine lintegral_congr_ae ?_
    filter_upwards [hcond n] with ω hω
    simp only [hYdef] at hω ⊢
    rw [hω]
    simp only [hH]
    have := M.isProbabilityMeasure_particlePredictionLaw hN n (ξ n ω)
    have hsm : Measurable fun z : Fin N → X ↦ ∑ i, φ (z i) :=
      Finset.measurable_sum _ fun i _ ↦ hφ.comp (measurable_pi_apply i)
    rw [lintegral_const_mul _ hsm, lintegral_sum_comp_eval_pi _ hφ]
  · exact Measurable.lintegral_kernel_prod_right (f := fun y z ↦ H (y, z)) hHm

/-- Unbiasedness of the bootstrap particle approximation of the unnormalized Feynman–Kac
measures: `𝔼[∏_{p<n} ηᵖ(Gₚ) · ηⁿ(φ)] = γₙ(φ)` for every measurable `φ ≥ 0`, where `ηᵖ` is the
empirical measure of generation `p`. -/
theorem lintegral_bootstrapWeight_mul_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X)
    (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, (∏ p ∈ Finset.range n, (∑ i, ENNReal.ofReal (M.potential p (ξ p ω i))) / N) *
      ((∑ i, φ (ξ n ω i)) / N) ∂P = ∫⁻ y, φ y ∂M.unnormalizedLaw n := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  induction n generalizing φ with
  | zero =>
    obtain ⟨hmeas, h0, -⟩ := id hξ
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    rw [← lintegral_map (f := fun z : Fin N → X ↦ (∑ i, φ (z i)) / N)
      ((Finset.measurable_sum _ fun i _ ↦ hφ.comp (measurable_pi_apply i)).div_const _)
      (hmeas 0), h0]
    simp_rw [ENNReal.div_eq_inv_mul]
    have hsm : Measurable fun z : Fin N → X ↦ ∑ i, φ (z i) :=
      Finset.measurable_sum _ fun i _ ↦ hφ.comp (measurable_pi_apply i)
    rw [lintegral_const_mul _ hsm, lintegral_sum_comp_eval_pi _ hφ, ← mul_assoc,
      ENNReal.inv_mul_cancel hN0 hNt, one_mul]
    rfl
  | succ n ih =>
    set w : ℕ → X → ℝ≥0∞ := fun p x ↦ ENNReal.ofReal (M.potential p x) with hw
    have hwm (p : ℕ) : Measurable (w p) := (M.measurable_potential p).ennreal_ofReal
    set F : (Fin (n + 1) → Fin N → X) → ℝ≥0∞ := fun y ↦
      (∏ p : Fin (n + 1), (∑ i, w p (y p i)) / N) / N with hF
    have hFm : Measurable F := by
      refine Measurable.div_const (Finset.measurable_prod _ fun p _ ↦ ?_) _
      exact (Finset.measurable_sum _ fun i _ ↦
        (hwm p).comp ((measurable_pi_apply i).comp (measurable_pi_apply p))).div_const _
    have hFeq (ω : Ω) : F (fun i : Fin (n + 1) ↦ ξ i ω) =
        (∏ p ∈ Finset.range (n + 1), (∑ i, w p (ξ p ω i)) / N) / N := by
      simp only [hF]
      rw [Fin.prod_univ_eq_prod_range (fun p ↦ (∑ i, w p (ξ p ω i)) / N)]
    have hstep := lintegral_mul_sum_bootstrap_succ P M N hN ξ hξ n F hFm hφ
    simp_rw [hFeq] at hstep
    set ψ : X → ℝ≥0∞ := fun x ↦ w n x * ∫⁻ y, φ y ∂M.transition n x with hψ
    have hψm : Measurable ψ := (hwm n).mul hφ.lintegral_kernel
    rw [M.lintegral_unnormalizedLaw_succ n hφ, ← ih hψm]
    have hlhs (ω : Ω) : (∏ p ∈ Finset.range (n + 1), (∑ i, w p (ξ p ω i)) / N) *
        ((∑ i, φ (ξ (n + 1) ω i)) / N) =
        (∏ p ∈ Finset.range (n + 1), (∑ i, w p (ξ p ω i)) / N) / N *
          ∑ i, φ (ξ (n + 1) ω i) := by
      simp only [ENNReal.div_eq_inv_mul]; ring
    simp only [hw] at hlhs hstep ⊢
    simp_rw [hlhs, hstep]
    refine lintegral_congr fun ω ↦ ?_
    set S := ∑ i, ENNReal.ofReal (M.potential n (ξ n ω i)) with hS
    have hS0 : S ≠ 0 := by
      rw [hS, Ne, Finset.sum_eq_zero_iff]
      push Not
      exact ⟨⟨0, hN⟩, Finset.mem_univ _, by simpa using M.potential_pos n _⟩
    have hSt : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.ofReal_ne_top
    rw [M.lintegral_particlePredictionLaw, Finset.prod_range_succ, ← hS]
    simp only [hψ, hw]
    simp only [ENNReal.div_eq_inv_mul]
    calc _ = ((∏ x ∈ Finset.range n,
              (N : ℝ≥0∞)⁻¹ * ∑ i, ENNReal.ofReal (M.potential x (ξ x ω i))) *
            ((N : ℝ≥0∞)⁻¹ * ∑ i, ENNReal.ofReal (M.potential n (ξ n ω i)) *
              ∫⁻ y, φ y ∂M.transition n (ξ n ω i))) * ((N : ℝ≥0∞)⁻¹ * N) * (S * S⁻¹) := by
          ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hN0 hNt, ENNReal.mul_inv_cancel hS0 hSt]; ring

/-- GAPS 104.58: unbiased likelihood estimate for multinomial resampling. -/
theorem integral_particleLikelihood_eq {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X)
    (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ) :
    (∫ ω, M.particleLikelihood (fun p ↦ ξ p ω) n ∂P) = (M.unnormalizedLaw n).real univ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnn (ω : Ω) : 0 ≤ M.particleLikelihood (fun p ↦ ξ p ω) n :=
    Finset.prod_nonneg fun p _ ↦ div_nonneg
      (Finset.sum_nonneg fun i _ ↦ (M.potential_pos p _).le) hNr.le
  have hmeas : Measurable fun ω ↦ M.particleLikelihood (fun p ↦ ξ p ω) n :=
    Finset.measurable_prod _ fun p _ ↦ (Finset.measurable_sum _ fun i _ ↦
      (M.measurable_potential p).comp ((measurable_pi_apply i).comp (hξ.1 p))).div_const _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable,
    measureReal_def]
  congr 1
  have h1 := lintegral_bootstrapWeight_mul_average P M N hN ξ hξ n
    (φ := fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ENNReal.div_self hN0 (ENNReal.natCast_ne_top N), lintegral_const, one_mul] at h1
  rw [← h1]
  refine lintegral_congr fun ω ↦ ?_
  simp only [FeynmanKacModel.particleLikelihood]
  rw [ENNReal.ofReal_prod_of_nonneg fun p _ ↦ div_nonneg
    (Finset.sum_nonneg fun i _ ↦ (M.potential_pos p _).le) hNr.le]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [ENNReal.ofReal_div_of_pos hNr, ENNReal.ofReal_sum_of_nonneg fun i _ ↦
    (M.potential_pos p _).le, ENNReal.ofReal_natCast]

/-- Gibbs law normalized by its partition integral. Use under finite positive normalizer
hypotheses. -/
def gibbsMeasure {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  let Z := ∫ x, Real.exp (-V x)
  volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x) / Z))

/-- Diffusion generator in Euclidean coordinates for drift `b` and infinitesimal covariance `A`. -/
def diffusionGenerator {d : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ f x (b t x) + (1 / 2 : ℝ) *
    ∑ i, ∑ j, A t x i j *
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Weak integral formulation of the Fokker–Planck equation on `[0,T]`. -/
def IsFokkerPlanckSolution {d : ℕ}
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)))
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, IsProbabilityMeasure (μ t)) ∧
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ⊤ f → HasCompactSupport f →
      ∀ t ∈ Icc 0 T,
        Integrable (diffusionGenerator b A f t) (μ t) ∧
        IntervalIntegrable (fun s ↦ ∫ x, diffusionGenerator b A f s x ∂μ s) volume 0 t ∧
        (∫ x, f x ∂μ t) = (∫ x, f x ∂μ 0) +
          ∫ s in (0 : ℝ)..t, ∫ x, diffusionGenerator b A f s x ∂μ s

/-- Euler–Maruyama step with an already sampled standard Gaussian increment. -/
def eulerMaruyamaStep {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • b x + Real.sqrt h • σ z

/-- Unadjusted Langevin one-step law, with noise variance `2h`. -/
def langevinStepLaw {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (P : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (P.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
    (fun z ↦ z.1 - h • gradV z.1 + Real.sqrt (2 * h) • z.2)

/-- Acceptance probability of Metropolis-adjusted Langevin with proposal variance `2h`. -/
def malaAcceptance {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  min 1 (Real.exp (V x - V y +
    (‖y - x + h • gradV x‖ ^ 2 - ‖x - y + h • gradV y‖ ^ 2) / (4 * h)))

/-- DDPM update for variance-exploding Brownian noising, using the remaining time `t`. -/
def ddpmStep {d : ℕ} (score : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t h : ℝ) (x z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x + h • score x + Real.sqrt ((t - h) * h / t) • z

/-- Feynman–Kac normalization starts from the specified prior law. -/
@[simp] theorem FeynmanKacModel.unnormalizedLaw_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) : M.unnormalizedLaw 0 = (M.initial : Measure X) := rfl

/-- The particle likelihood of an empty observation sequence is one. -/
@[simp] theorem FeynmanKacModel.particleLikelihood_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (particles : ℕ → Fin N → X) :
    M.particleLikelihood particles 0 = 1 := by simp [particleLikelihood]

/-- For `N` independent draws from a probability law `ν` and a bounded measurable `f` with
`|f| ≤ C`, the centred sum satisfies `𝔼[(∑ᵢ f(Zᵢ) - N ∫ f dν)²] ≤ N C²`. -/
theorem integral_sq_sum_comp_eval_sub_le {X : Type*} [MeasurableSpace X] {N : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∫ z, (∑ i, f (z i) - N * ∫ x, f x ∂ν) ^ 2 ∂Measure.pi (fun _ : Fin N ↦ ν) ≤ N * C ^ 2 := by
  have hmem : MemLp f 2 ν := MemLp.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
  have hvar := variance_sum_pi (μ := fun _ : Fin N ↦ ν) (X := fun _ ↦ f) (fun _ ↦ hmem)
  have hS : (∑ i : Fin N, fun z : Fin N → X ↦ f (z i)) = fun z ↦ ∑ i, f (z i) := by
    ext z; simp [Finset.sum_apply]
  rw [hS] at hvar
  have hSm : Measurable fun z : Fin N → X ↦ ∑ i, f (z i) :=
    Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)
  have hcoord (i : Fin N) : ∫ z, f (z i) ∂Measure.pi (fun _ : Fin N ↦ ν) = ∫ x, f x ∂ν := by
    rw [← integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable,
      (measurePreserving_eval (fun _ : Fin N ↦ ν) i).map_eq]
  have hint (i : Fin N) : Integrable (fun z : Fin N → X ↦ f (z i))
      (Measure.pi (fun _ : Fin N ↦ ν)) :=
    Integrable.of_bound (hf.comp (measurable_pi_apply i)).aestronglyMeasurable C
      (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hC (z i))
  have hmean : ∫ z, ∑ i, f (z i) ∂Measure.pi (fun _ : Fin N ↦ ν) = N * ∫ x, f x ∂ν := by
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    simp [hcoord]
  rw [variance_eq_integral hSm.aemeasurable, hmean] at hvar
  rw [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr
  refine (variance_le_expectation_sq hf.aestronglyMeasurable).trans ?_
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := f ^ 2) (C := C ^ 2)
    (ae_of_all _ fun x ↦ by
      simpa [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
  simpa [Real.norm_eq_abs] using (le_abs_self _).trans this


/-- Integral of a bounded measurable function against the bootstrap prediction law: the
potential-weighted average of the transition integrals from the current particles. -/
theorem FeynmanKacModel.integral_particlePredictionLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (n : ℕ) (x : Fin N → X) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂M.particlePredictionLaw n x =
      (∑ i, M.potential n (x i) * ∫ y, f y ∂M.transition n (x i)) /
        ∑ i, M.potential n (x i) := by
  have := M.isMarkov_transition n
  have hint (i : Fin N) : Integrable f (M.transition n (x i)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hC y)
  have hint' (i : Fin N) : Integrable f
      (ENNReal.ofReal (M.potential n (x i)) • M.transition n (x i)) :=
    (hint i).smul_measure ENNReal.ofReal_ne_top
  rw [FeynmanKacModel.particlePredictionLaw, integral_smul_measure,
    integral_finsetSum_measure fun i _ ↦ hint' i]
  simp_rw [integral_smul_measure]
  rw [ENNReal.toReal_inv, ENNReal.toReal_sum fun _ _ ↦ ENNReal.ofReal_ne_top]
  simp_rw [ENNReal.toReal_ofReal (M.potential_pos n _).le, smul_eq_mul]
  rw [div_eq_inv_mul]


/-- Total mass recursion `γₙ₊₁(1) = γₙ(Gₙ)` of the unnormalized Feynman–Kac measures. -/
theorem FeynmanKacModel.unnormalizedLaw_succ_univ {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) :
    M.unnormalizedLaw (n + 1) univ =
      ∫⁻ x, ENNReal.ofReal (M.potential n x) ∂M.unnormalizedLaw n := by
  have := M.isMarkov_transition n
  have h := M.lintegral_unnormalizedLaw_succ n (φ := fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  simpa only [lintegral_one, measure_univ, mul_one] using h

/-- The unnormalized Feynman–Kac measures are finite. -/
instance FeynmanKacModel.isFiniteMeasure_unnormalizedLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : IsFiniteMeasure (M.unnormalizedLaw n) := by
  induction n with
  | zero => rw [FeynmanKacModel.unnormalizedLaw_zero]; infer_instance
  | succ n ih =>
    constructor
    obtain ⟨a, b, -, hab⟩ := M.potential_bounds n
    rw [M.unnormalizedLaw_succ_univ]
    calc ∫⁻ x, ENNReal.ofReal (M.potential n x) ∂M.unnormalizedLaw n
        ≤ ∫⁻ _, ENNReal.ofReal b ∂M.unnormalizedLaw n :=
          lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hab x).2
      _ < ⊤ := by
          rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The unnormalized Feynman–Kac measures have positive total mass. -/
theorem FeynmanKacModel.unnormalizedLaw_univ_ne_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : M.unnormalizedLaw n univ ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨a, b, ha, hab⟩ := M.potential_bounds n
    rw [M.unnormalizedLaw_succ_univ]
    refine ne_of_gt (lt_of_lt_of_le ?_ (lintegral_mono fun x ↦
      ENNReal.ofReal_le_ofReal (hab x).1))
    rw [lintegral_const]
    exact ENNReal.mul_pos (by simpa using ha) ih

/-- The normalized filtering law is a probability measure. -/
instance FeynmanKacModel.isProbabilityMeasure_filterLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : IsProbabilityMeasure (M.filterLaw n) := by
  constructor
  simp only [FeynmanKacModel.filterLaw, smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (M.unnormalizedLaw_univ_ne_zero n) (measure_ne_top _ _)

/-- Real-valued recursion `γₙ₊₁(f) = γₙ(Gₙ Qₙ f)` for bounded measurable `f`. -/
theorem FeynmanKacModel.integral_unnormalizedLaw_succ {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂M.unnormalizedLaw (n + 1) =
      ∫ x, M.potential n x * ∫ y, f y ∂M.transition n x ∂M.unnormalizedLaw n := by
  have := M.isMarkov_transition n
  have hint : Integrable f (M.unnormalizedLaw (n + 1)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hC y)
  rw [FeynmanKacModel.unnormalizedLaw, Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint, Kernel.const_apply,
    integral_withDensity_eq_integral_toReal_smul (M.measurable_potential n).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (M.potential_pos n _).le, smul_eq_mul]

/-- Integrals against the filtering law are normalized integrals against `γₙ`. -/
theorem FeynmanKacModel.integral_filterLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) :
    ∫ y, f y ∂M.filterLaw n = ((M.unnormalizedLaw n).real univ)⁻¹ * ∫ y, f y ∂M.unnormalizedLaw n := by
  rw [FeynmanKacModel.filterLaw, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    measureReal_def]

/-- Filtering recursion `ηₙ₊₁(f) = ηₙ(Gₙ Qₙ f) / ηₙ(Gₙ)` for bounded measurable `f`. -/
theorem FeynmanKacModel.integral_filterLaw_succ {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂M.filterLaw (n + 1) =
      (∫ x, M.potential n x * ∫ y, f y ∂M.transition n x ∂M.filterLaw n) /
        ∫ x, M.potential n x ∂M.filterLaw n := by
  have := M.isMarkov_transition n
  have h1 : (M.unnormalizedLaw (n + 1)).real univ =
      ∫ x, M.potential n x ∂M.unnormalizedLaw n := by
    have := M.integral_unnormalizedLaw_succ n (f := fun _ ↦ (1 : ℝ)) measurable_const
      (C := 1) (fun _ ↦ by simp)
    simpa using this
  have hc : ((M.unnormalizedLaw n).real univ)⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨M.unnormalizedLaw_univ_ne_zero n, measure_ne_top _ _⟩
  rw [M.integral_filterLaw, M.integral_filterLaw, M.integral_filterLaw,
    M.integral_unnormalizedLaw_succ n hf hC, h1, mul_div_mul_left _ _ hc, div_eq_inv_mul]


/-- Conditional sampling step of the bootstrap filter: integrating a function of the past and
the next generation equals integrating it against the product prediction law. -/
theorem lintegral_bootstrap_succ {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ)
    (H : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H ((fun i : Fin (n + 1) ↦ ξ i ω), ξ (n + 1) ω) ∂P =
      ∫⁻ ω, ∫⁻ z, H ((fun i : Fin (n + 1) ↦ ξ i ω), z)
        ∂Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω)) ∂P := by
  obtain ⟨hmeas, -, hcond⟩ := hξ
  set Y : Ω → Fin (n + 1) → Fin N → X := fun ω i ↦ ξ i ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  change ∫⁻ ω, H (Y ω, ξ (n + 1) ω) ∂P = ∫⁻ ω, ∫⁻ z, H (Y ω, z) ∂_ ∂P
  rw [← lintegral_map hH (hY.prodMk (hmeas (n + 1))),
    ← compProd_map_condDistrib hY.aemeasurable (hmeas (n + 1)).aemeasurable,
    Measure.lintegral_compProd hH, lintegral_map _ hY]
  · refine lintegral_congr_ae ?_
    filter_upwards [hcond n] with ω hω
    simp only [hYdef] at hω ⊢
    rw [hω]
  · exact Measurable.lintegral_kernel_prod_right (f := fun y z ↦ H (y, z)) hH

/-- Conditional variance bound for one resampling step: with `|f| ≤ C`,
`𝔼[(∑ᵢ f(ξₙ₊₁ⁱ) - N Φₙ(ηᴺₙ)(f))²] ≤ N C²`, where `Φₙ(ηᴺₙ)` is the prediction law. -/
theorem integral_sq_sum_bootstrap_succ_sub_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ)
    (n : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ ω, (∑ i, f (ξ (n + 1) ω i) - N * ∫ y, f y ∂M.particlePredictionLaw n (ξ n ω)) ^ 2 ∂P ≤
      N * C ^ 2 := by
  have := M.isMarkov_transition n
  set m : (Fin N → X) → ℝ := fun x ↦
    (∑ i, M.potential n (x i) * ∫ y, f y ∂M.transition n (x i)) / ∑ i, M.potential n (x i)
    with hm
  have hQ : Measurable fun x ↦ ∫ y, f y ∂M.transition n x :=
    (hf.stronglyMeasurable.integral_kernel (κ := M.transition n)).measurable
  have hmm : Measurable m :=
    (Finset.measurable_sum _ fun i _ ↦
      ((M.measurable_potential n).comp (measurable_pi_apply i)).mul
        (hQ.comp (measurable_pi_apply i))).div
      (Finset.measurable_sum _ fun i _ ↦ (M.measurable_potential n).comp (measurable_pi_apply i))
  have hpred (x : Fin N → X) : ∫ y, f y ∂M.particlePredictionLaw n x = m x :=
    M.integral_particlePredictionLaw n x hf hC
  simp_rw [hpred]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary X))
  set H : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal ((∑ i, f (p.2 i) - N * m (p.1 (Fin.last n))) ^ 2) with hH
  have hs : Measurable fun p : (Fin (n + 1) → Fin N → X) × (Fin N → X) ↦ ∑ i, f (p.2 i) :=
    Finset.measurable_sum _ fun i _ ↦ hf.comp ((measurable_pi_apply i).comp measurable_snd)
  have hHm : Measurable H :=
    ENNReal.measurable_ofReal.comp ((hs.sub (measurable_const.mul
      (hmm.comp ((measurable_pi_apply _).comp measurable_fst)))).pow_const 2)
  have hmeas : Measurable fun ω ↦ (∑ i, f (ξ (n + 1) ω i) - N * m (ξ n ω)) ^ 2 :=
    ((Finset.measurable_sum _ fun i _ ↦ hf.comp ((measurable_pi_apply i).comp (hξ.1 _))).sub
      (measurable_const.mul (hmm.comp (hξ.1 n)))).pow_const 2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _)
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have hL := lintegral_bootstrap_succ P M N ξ hξ n H hHm
  simp only [hH, Fin.val_last] at hL
  rw [hL]
  refine (lintegral_mono fun ω ↦ ?_).trans (by rw [lintegral_const, measure_univ, mul_one])
  have := M.isProbabilityMeasure_particlePredictionLaw hN n (ξ n ω)
  have hint : Integrable (fun z : Fin N → X ↦ (∑ i, f (z i) - N * m (ξ n ω)) ^ 2)
      (Measure.pi fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω)) := by
    refine Integrable.of_bound (((Finset.measurable_sum _ fun i _ ↦
      hf.comp (measurable_pi_apply i)).sub measurable_const).pow_const 2).aestronglyMeasurable
      ((N * C + N * C) ^ 2) (ae_of_all _ fun z ↦ ?_)
    have h1 : |∑ i, f (z i)| ≤ N * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hC (z i)
    have h2 : |m (ξ n ω)| ≤ C := by
      rw [← hpred]
      have := norm_integral_le_of_norm_le_const (μ := M.particlePredictionLaw n (ξ n ω))
        (f := f) (C := C) (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hC y)
      simpa [Real.norm_eq_abs] using this
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    refine (abs_sub _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hpred]
  exact integral_sq_sum_comp_eval_sub_le _ hf hC


/-- Elementary ratio estimate used for the Feynman–Kac selection step: if `v, v' ≥ a > 0` and
`|u'| ≤ C v'`, then `(u/v - u'/v')² ≤ 2((u-u')² + C²(v-v')²)/a²`. -/
theorem sq_div_sub_div_le {a u v u' v' C : ℝ} (ha : 0 < a) (hv : a ≤ v) (hv' : a ≤ v')
    (hu' : |u'| ≤ C * v') :
    (u / v - u' / v') ^ 2 ≤ 2 * ((u - u') ^ 2 + C ^ 2 * (v - v') ^ 2) / a ^ 2 := by
  have hv0 : 0 < v := ha.trans_le hv
  have hv'0 : 0 < v' := ha.trans_le hv'
  set r := u' / v' with hr
  have hrC : |r| ≤ C := by rw [hr, abs_div, abs_of_pos hv'0, div_le_iff₀ hv'0]; exact hu'
  have key : u / v - r = ((u - u') - r * (v - v')) / v := by
    rw [hr]; field_simp; ring
  rw [key, div_pow]
  have hr2 : r ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs r]; exact pow_le_pow_left₀ (abs_nonneg _) hrC 2
  have h1 : ((u - u') - r * (v - v')) ^ 2 ≤ 2 * ((u - u') ^ 2 + C ^ 2 * (v - v') ^ 2) := by
    nlinarith [sq_nonneg ((u - u') + r * (v - v')), sq_nonneg (v - v'),
      mul_le_mul_of_nonneg_right hr2 (sq_nonneg (v - v'))]
  exact div_le_div₀ (by positivity) h1 (by positivity)
    (pow_le_pow_left₀ ha.le hv 2)

/-- Mean-square error bound for the bootstrap particle filter: at each fixed time `n` there is
a constant `K` such that `𝔼[(ηᴺₙ(f) - ηₙ(f))²] ≤ K C² / (N + 1)` for all `N` and all measurable
`f` with `|f| ≤ C`, where `N + 1` is the number of particles. -/
theorem exists_integral_sq_particle_average_sub_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : X → ℝ, Measurable f → ∀ C : ℝ, (∀ x, |f x| ≤ C) → ∀ N : ℕ,
      ∫ ω, ((∑ i, f (ξ N n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n) ^ 2 ∂P ≤
        K * C ^ 2 / (N + 1) := by
  have hsum (N : ℕ) (h : X → ℝ) (D : ℝ) (hD : ∀ x, |h x| ≤ D) (z : Fin (N + 1) → X) :
      |∑ i, h (z i)| ≤ (N + 1) * D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hD (z i)
  have hsq (p : Ω → ℝ) (hp : Measurable p) (D : ℝ) (hD : ∀ ω, |p ω| ≤ D) :
      Integrable (fun ω ↦ p ω ^ 2) P :=
    (MemLp.of_bound hp.aestronglyMeasurable D
      (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hD ω)).integrable_sq
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun f hf C hC N ↦ ?_⟩
    have hN' : (0 : ℝ) < N + 1 := by positivity
    have h0 : ∫ x, f x ∂M.filterLaw 0 = ∫ x, f x ∂(M.initial : Measure X) := by
      rw [M.integral_filterLaw, FeynmanKacModel.unnormalizedLaw_zero]; simp
    rw [h0]
    have hsm : Measurable fun z : Fin (N + 1) → X ↦
        ((∑ i, f (z i)) / (N + 1) - ∫ x, f x ∂(M.initial : Measure X)) ^ 2 :=
      (((Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)).div_const _).sub
        measurable_const).pow_const 2
    rw [← integral_map ((hξ N).1 0).aemeasurable hsm.aestronglyMeasurable, (hξ N).2.1]
    have hrw (z : Fin (N + 1) → X) :
        ((∑ i, f (z i)) / (N + 1) - ∫ x, f x ∂(M.initial : Measure X)) ^ 2 =
          (∑ i, f (z i) - ((N : ℝ) + 1) * ∫ x, f x ∂(M.initial : Measure X)) ^ 2 /
            (N + 1) ^ 2 := by
      field_simp
    simp_rw [hrw]
    rw [integral_div]
    have h1 := integral_sq_sum_comp_eval_sub_le (N := N + 1) (M.initial : Measure X) hf hC
    push_cast at h1
    calc _ ≤ (N + 1) * C ^ 2 / (N + 1) ^ 2 := by gcongr
      _ = 1 * C ^ 2 / (N + 1) := by field_simp
  | succ n ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    obtain ⟨a, b, ha, hab⟩ := M.potential_bounds n
    have hb : 0 < b := ha.trans_le ((hab (Classical.arbitrary X)).1.trans (hab _).2)
    refine ⟨2 + 8 * K * b ^ 2 / a ^ 2, by positivity, fun f hf C hC N ↦ ?_⟩
    have := M.isMarkov_transition n
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary X))
    have hN' : (0 : ℝ) < N + 1 := by positivity
    set G := M.potential n with hGdef
    have hGm : Measurable G := M.measurable_potential n
    have hGb (x : X) : |G x| ≤ b := by
      rw [abs_of_pos (M.potential_pos n x)]; exact (hab x).2
    set Q : X → ℝ := fun x ↦ ∫ y, f y ∂M.transition n x with hQdef
    have hQm : Measurable Q :=
      (hf.stronglyMeasurable.integral_kernel (κ := M.transition n)).measurable
    have hQb (x : X) : |Q x| ≤ C := by
      have := norm_integral_le_of_norm_le_const (μ := M.transition n x) (f := f) (C := C)
        (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hC y)
      simpa [Real.norm_eq_abs] using this
    set g : X → ℝ := fun x ↦ G x * Q x with hgdef
    have hgm : Measurable g := hGm.mul hQm
    have hgb (x : X) : |g x| ≤ b * C := by
      rw [abs_mul]; exact mul_le_mul (hGb x) (hQb x) (abs_nonneg _) hb.le
    have hmeas := (hξ N).1
    set A : Ω → ℝ := fun ω ↦ (∑ i, f (ξ N (n + 1) ω i)) / (N + 1) with hA
    set B : Ω → ℝ := fun ω ↦ ∫ y, f y ∂M.particlePredictionLaw n (ξ N n ω) with hBdef
    set u : Ω → ℝ := fun ω ↦ (∑ i, g (ξ N n ω i)) / (N + 1) with hu
    set v : Ω → ℝ := fun ω ↦ (∑ i, G (ξ N n ω i)) / (N + 1) with hv
    set u' := ∫ x, g x ∂M.filterLaw n with hu'
    set v' := ∫ x, G x ∂M.filterLaw n with hv'
    have hT : ∫ x, f x ∂M.filterLaw (n + 1) = u' / v' := M.integral_filterLaw_succ n hf hC
    have hB (ω : Ω) : B ω = u ω / v ω := by
      simp only [hBdef, hu, hv]
      rw [M.integral_particlePredictionLaw n _ hf hC, div_div_div_cancel_right₀ hN'.ne']
    have hum : Measurable u :=
      (Finset.measurable_sum _ fun i _ ↦ hgm.comp ((measurable_pi_apply i).comp (hmeas n))).div_const _
    have hvm : Measurable v :=
      (Finset.measurable_sum _ fun i _ ↦ hGm.comp ((measurable_pi_apply i).comp (hmeas n))).div_const _
    have hBm : Measurable B := by
      have : B = fun ω ↦ u ω / v ω := funext hB
      rw [this]; exact hum.div hvm
    have hSm : Measurable fun ω ↦ ∑ i, f (ξ N (n + 1) ω i) :=
      Finset.measurable_sum _ fun i _ ↦ hf.comp ((measurable_pi_apply i).comp (hmeas (n + 1)))
    have hBb (ω : Ω) : |B ω| ≤ C := by
      have := M.isProbabilityMeasure_particlePredictionLaw (N.succ_pos) n (ξ N n ω)
      have := norm_integral_le_of_norm_le_const (μ := M.particlePredictionLaw n (ξ N n ω))
        (f := f) (C := C) (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hC y)
      simpa [Real.norm_eq_abs] using this
    have hvlow (ω : Ω) : a ≤ v ω := by
      simp only [hv]
      rw [le_div_iff₀ hN']
      calc a * (N + 1) = ∑ _i : Fin (N + 1), a := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ (hab _).1
    have hGi : Integrable G (M.filterLaw n) := Integrable.of_bound hGm.aestronglyMeasurable b
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hGb x)
    have hgi : Integrable g (M.filterLaw n) := Integrable.of_bound hgm.aestronglyMeasurable (b * C)
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hgb x)
    have hvlow' : a ≤ v' := by
      calc a = ∫ _, a ∂M.filterLaw n := by simp
        _ ≤ v' := integral_mono (integrable_const _) hGi fun x ↦ (hab x).1
    have hu'b : |u'| ≤ C * v' := by
      calc |u'| ≤ ∫ x, |g x| ∂M.filterLaw n := abs_integral_le_integral_abs
        _ ≤ ∫ x, C * G x ∂M.filterLaw n :=
            integral_mono hgi.abs (hGi.const_mul C) fun x ↦ by
              simp only [hgdef]
              rw [abs_mul, abs_of_pos (M.potential_pos n x), mul_comm]
              exact mul_le_mul_of_nonneg_right (hQb x) (M.potential_pos n x).le
        _ = C * v' := integral_const_mul _ _
    -- pointwise bound
    have hpt (ω : Ω) : (A ω - u' / v') ^ 2 ≤
        2 / (N + 1) ^ 2 * (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2 +
          (4 / a ^ 2 * (u ω - u') ^ 2 + 4 * C ^ 2 / a ^ 2 * (v ω - v') ^ 2) := by
      have h1 : A ω - B ω = (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) / (N + 1) := by
        simp only [hA]; field_simp
      have h2 := sq_div_sub_div_le ha (hvlow ω) hvlow' hu'b (u := u ω)
      rw [← hB] at h2
      have h3 : (A ω - u' / v') ^ 2 ≤ 2 * (A ω - B ω) ^ 2 + 2 * (B ω - u' / v') ^ 2 := by
        nlinarith [sq_nonneg (A ω - B ω - (B ω - u' / v'))]
      rw [h1, div_pow] at h3
      calc _ ≤ _ := h3
        _ = 2 / (N + 1) ^ 2 * (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2 +
            2 * (B ω - u' / v') ^ 2 := by ring
        _ ≤ _ := by
          gcongr
          calc 2 * (B ω - u' / v') ^ 2 ≤ 2 * (2 * ((u ω - u') ^ 2 + C ^ 2 * (v ω - v') ^ 2) / a ^ 2) := by
                gcongr
            _ = _ := by ring
    -- integrability
    have hI1 : Integrable (fun ω ↦ (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2) P :=
      hsq _ (hSm.sub (measurable_const.mul hBm)) ((N + 1) * C + (N + 1) * C) fun ω ↦ by
        refine (abs_sub _ _).trans (add_le_add (hsum N f C hC _) ?_)
        rw [abs_mul, abs_of_pos hN']; exact mul_le_mul_of_nonneg_left (hBb ω) hN'.le
    have hI2 : Integrable (fun ω ↦ (u ω - u') ^ 2) P :=
      hsq _ (hum.sub measurable_const) (b * C + |u'|) fun ω ↦ by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        simp only [hu]; rw [abs_div, abs_of_pos hN', div_le_iff₀ hN', mul_comm]
        exact hsum N g _ hgb _
    have hI3 : Integrable (fun ω ↦ (v ω - v') ^ 2) P :=
      hsq _ (hvm.sub measurable_const) (b + |v'|) fun ω ↦ by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        simp only [hv]; rw [abs_div, abs_of_pos hN', div_le_iff₀ hN', mul_comm]
        exact hsum N G _ hGb _
    have hL1 := integral_sq_sum_bootstrap_succ_sub_le P M (N + 1) N.succ_pos (ξ N) (hξ N) n hf hC
    push_cast at hL1
    have hL2 := hK g hgm (b * C) hgb N
    have hL3 := hK G hGm b hGb N
    rw [hT]
    calc ∫ ω, (A ω - u' / v') ^ 2 ∂P
        ≤ ∫ ω, (2 / (N + 1) ^ 2 * (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2 +
          (4 / a ^ 2 * (u ω - u') ^ 2 + 4 * C ^ 2 / a ^ 2 * (v ω - v') ^ 2)) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
            ((hI1.const_mul _).add ((hI2.const_mul _).add (hI3.const_mul _))) (ae_of_all _ hpt)
      _ = 2 / (N + 1) ^ 2 * ∫ ω, (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2 ∂P +
          (4 / a ^ 2 * ∫ ω, (u ω - u') ^ 2 ∂P + 4 * C ^ 2 / a ^ 2 * ∫ ω, (v ω - v') ^ 2 ∂P) := by
          have j1 : Integrable (fun ω ↦ 2 / ((N : ℝ) + 1) ^ 2 *
              (∑ i, f (ξ N (n + 1) ω i) - (N + 1) * B ω) ^ 2) P := hI1.const_mul _
          have j2 : Integrable (fun ω ↦ 4 / a ^ 2 * (u ω - u') ^ 2) P := hI2.const_mul _
          have j3 : Integrable (fun ω ↦ 4 * C ^ 2 / a ^ 2 * (v ω - v') ^ 2) P := hI3.const_mul _
          have j23 : Integrable (fun ω ↦ 4 / a ^ 2 * (u ω - u') ^ 2 +
              4 * C ^ 2 / a ^ 2 * (v ω - v') ^ 2) P := j2.add j3
          rw [integral_add j1 j23, integral_add j2 j3, integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ 2 / (N + 1) ^ 2 * ((N + 1) * C ^ 2) +
          (4 / a ^ 2 * (K * (b * C) ^ 2 / (N + 1)) + 4 * C ^ 2 / a ^ 2 * (K * b ^ 2 / (N + 1))) := by
          gcongr
      _ = (2 + 8 * K * b ^ 2 / a ^ 2) * C ^ 2 / (N + 1) := by
          field_simp; ring


/-- GAPS 104.55: fixed-time consistency of the multinomial bootstrap particle filter. The proof
combines the mean-square bound `exists_integral_sq_particle_average_sub_le` with Markov's
inequality. -/
theorem tendstoInProbabilityConst_particle_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (n : ℕ) :
    TendstoInProbabilityConst P
      (fun N ω ↦ (∑ i, f (ξ N n ω i)) / (N + 1)) (∫ x, f x ∂M.filterLaw n) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨K, hK0, hK⟩ := exists_integral_sq_particle_average_sub_le P M ξ hξ n
  intro ε hε
  set c := ∫ x, f x ∂M.filterLaw n
  have hbound (N : ℕ) : P.real {ω | ε < dist ((∑ i, f (ξ N n ω i)) / (N + 1)) c} ≤
      K * C ^ 2 / ε ^ 2 * (1 / ((N : ℝ) + 1)) := by
    have hN' : (0 : ℝ) < N + 1 := by positivity
    set Y : Ω → ℝ := fun ω ↦ ((∑ i, f (ξ N n ω i)) / (N + 1) - c) ^ 2 with hY
    have hYm : Measurable Y := (((Finset.measurable_sum _ fun i _ ↦
      hf.comp ((measurable_pi_apply i).comp ((hξ N).1 n))).div_const _).sub
        measurable_const).pow_const 2
    have hYi : Integrable Y P := by
      refine Integrable.of_bound hYm.aestronglyMeasurable ((C + |c|) ^ 2)
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, hY, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add ?_ le_rfl)) 2
      rw [abs_div, abs_of_pos hN', div_le_iff₀ hN', mul_comm]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hC (ξ N n ω i)
    have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) hYi (ε ^ 2)
    have hsub : {ω | ε < dist ((∑ i, f (ξ N n ω i)) / (N + 1)) c} ⊆ {ω | ε ^ 2 ≤ Y ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
      have := pow_le_pow_left₀ hε.le hω.le 2
      rwa [sq_abs] at this
    have hmono := measureReal_mono (μ := P) hsub
    have hε2 : 0 < ε ^ 2 := by positivity
    calc P.real _ ≤ P.real {ω | ε ^ 2 ≤ Y ω} := hmono
      _ ≤ (∫ ω, Y ω ∂P) / ε ^ 2 := by rw [le_div_iff₀ hε2, mul_comm]; exact hM
      _ ≤ K * C ^ 2 / (N + 1) / ε ^ 2 := by gcongr; exact hK f hf C hC N
      _ = _ := by field_simp
  have hlim : Tendsto (fun N : ℕ ↦ K * C ^ 2 / ε ^ 2 * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K * C ^ 2 / ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ measureReal_nonneg) hbound


end CKSD
