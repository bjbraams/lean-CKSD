module

public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.RepresentationKernel
public import CKSD.Asymptotics.ConvolutionKernel
public import CKSD.Asymptotics.GaussianAnderson
public import CKSD.Asymptotics.LANLikelihood
public import CKSD.Asymptotics.LANJointLimit
public import CKSD.Asymptotics.GaussianShiftTilt
public import CKSD.Asymptotics.GaussianShiftComplete
public import CKSD.Asymptotics.KernelTranslation
public import CKSD.Inference.Model
public import Mathlib.MeasureTheory.Group.Convolution
public import Statlib.Contiguity.Def
import Mathlib.MeasureTheory.Measure.Portmanteau


/-!
# Asymptotic statistical interfaces: local experiments, efficiency, and the delta method

## Main definitions

* `CKSD.outerExpectation`, `CKSD.TendstoInOuterDistribution`: outer expectation and weak
  convergence of possibly nonmeasurable random elements.
* `CKSD.TendstoInProbabilityZero`, `CKSD.IsLittleOInProbability`, `CKSD.IsBigOInProbability`:
  stochastic orders.
* `CKSD.HasHadamardFDerivAt`: sequential Hadamard differentiability tangentially to a subspace.
* `CKSD.LocalExperiment`, `CKSD.IsLocallyAsymptoticallyNormal`, `CKSD.IsRegularEstimator`.
* `CKSD.fisherRaoMetric`, `CKSD.amariChentsovTensor`, `CKSD.openProbabilitySimplex`,
  `CKSD.simplexTangentSpace`, `CKSD.CongruentSimplexEmbedding`.

## Main results

* `CKSD.exists_gaussian_shift_kernel_of_local_limits`: limits of statistics in a LAN experiment
  are randomizations of the Gaussian shift experiment (GAPS 102.15).
* `CKSD.exists_convolution_of_is_regular_estimator`: Hájek's convolution theorem (GAPS 102.16).
* `CKSD.gaussian_risk_le_local_asymptotic_minimax`: the local asymptotic minimax theorem
  (GAPS 102.17).
* `CKSD.tendsto_in_distribution_of_has_hadamard_f_deriv_at`: the functional delta method
  (GAPS 102.28).
* `CKSD.fisher_rao_metric_congruent_embedding`: invariance of the Fisher–Rao metric under
  congruent embeddings (GAPS 102.58).
* `CKSD.is_contiguous_iff_contiguous5`: `CKSD.IsContiguous` is Statlib's `Contiguous5`.

## Conventions

The local parameter `h` of an experiment denotes the displacement `h / √n` from its centre; an
estimator is already scaled by `√n`. Observation spaces may depend on `n`. Convolutions of laws
are Mathlib's `MeasureTheory.Measure.conv`.

## References

The functional delta method uses Mathlib's closed-set portmanteau theorem
(`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`, `tendsto_of_forall_isClosed_limsup_le'`).
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Outer expectation of a nonnegative function, as the infimum over measurable majorants. -/
def outerExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : ∀ ω, f ω ≤ g ω), ∫⁻ ω, g ω ∂μ

/-- Weak convergence in the outer-expectation sense, allowing nonmeasurable random elements.
Shifting a bounded continuous test by its norm makes the integrand nonnegative. -/
def TendstoInOuterDistribution {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    Tendsto (fun n ↦ (outerExpectation μ (fun ω ↦ ENNReal.ofReal (f (X n ω) + ‖f‖))).toReal)
      atTop (𝓝 (∫ x, f x + ‖f‖ ∂ν))

/-- Convergence to zero in probability, `P n {ε < |X n|} → 0` for every `ε > 0`, for observation
spaces and laws varying with `n`. On a fixed probability space it is
`TendstoInMeasure μ X atTop (fun _ ↦ 0)`. -/
def TendstoInProbabilityZero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ (P n).real {ω | ε < |X n ω|}) atTop (𝓝 0)

/-- Stochastic little-o with an eventually positive deterministic scale. -/
def IsLittleOInProbability {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (r : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < r n) ∧
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ ‖X n ω‖ / r n) atTop (fun _ ↦ 0)

/-- Stochastic big-O with an eventually positive deterministic scale. -/
def IsBigOInProbability {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (r : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < r n) ∧
    IsBoundedInProbability μ (fun n ω ↦ ‖X n ω‖ / r n)

/-- Sequential tangential Hadamard differentiability, with a continuous linear extension. -/
def HasHadamardFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (domain : Set E)
    (D₀ : Submodule ℝ E) (D : E →L[ℝ] F) (θ : E) : Prop :=
  θ ∈ domain ∧ ∀ (t : ℕ → ℝ) (h : ℕ → E) (v : E),
    (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) → Tendsto h atTop (𝓝 v) → v ∈ D₀ →
    (∀ n, θ + t n • h n ∈ domain) →
    Tendsto (fun n ↦ (t n)⁻¹ • (g (θ + t n • h n) - g θ)) atTop (𝓝 (D v))

/-- A local experiment with observation space depending on sample size. -/
abbrev LocalExperiment (d : ℕ) (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] :=
  ∀ n, EuclideanSpace ℝ (Fin d) → ProbabilityMeasure (Ω n)

/-- Local asymptotic normality: Gaussian central sequence and log-likelihood expansion. -/
def IsLocallyAsymptoticallyNormal {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) : Prop :=
  I.PosDef ∧ (∀ n, Measurable (Δ n)) ∧
    TendstoInDistribution Δ atTop id (fun n ↦ (P n 0 : Measure (Ω n)))
      (multivariateGaussian 0 I) ∧
    ∀ h, TendstoInProbabilityZero (fun n ↦ (P n 0 : Measure (Ω n)))
      (fun n ω ↦ Real.log (((P n h : Measure (Ω n)).rnDeriv (P n 0) ω).toReal) -
        inner ℝ h (Δ n ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2)

/-- Regularity of a locally scaled estimator: its centred limit law `L` is independent of the
local parameter. -/
def IsRegularEstimator {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L] : Prop :=
  (∀ n, Measurable (T n)) ∧ ∀ h,
    TendstoInDistribution (fun n ω ↦ T n ω - h) atTop id (fun n ↦ (P n h : Measure (Ω n))) L

/-- GAPS 102.15: the asymptotic representation theorem. In a LAN experiment with information `I`,
if statistics `T n` with values in a Polish space have limit laws `L h` under every local
parameter `h`, there is a Markov kernel `K` with `L h = K ∘ₘ N(h, I⁻¹)` for all `h`, i.e. the
limit is a randomized statistic in the Gaussian shift experiment. -/
theorem exists_gaussian_shift_kernel_of_local_limits
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S : Type*} [MeasurableSpace S] [Nonempty S] [TopologicalSpace S] [PolishSpace S]
    [BorelSpace S]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → S) (hT : ∀ n, Measurable (T n))
    (L : EuclideanSpace ℝ (Fin d) → Measure S) [∀ h, IsProbabilityMeasure (L h)]
    (hlim : ∀ h, TendstoInDistribution T atTop id (fun n ↦ (P n h : Measure (Ω n))) (L h)) :
    ∃ K : Kernel (EuclideanSpace ℝ (Fin d)) S, IsMarkovKernel K ∧
      ∀ h, L h = K ∘ₘ multivariateGaussian h I⁻¹ := by
  let : MetricSpace S := TopologicalSpace.completelyMetrizableMetric S
  rcases hLAN with ⟨hI,hΔ,hΔlim,hrem⟩
  obtain ⟨φ,hφ,ρ,hjoint,hfst,hsnd⟩ :=
    exists_joint_subsequence_limit_of_marginal_limits
      (fun n ↦ (P n 0 : Measure (Ω n))) Δ T hΔ hT
      (multivariateGaussian 0 I) (L 0) hΔlim (hlim 0)
  apply exists_markov_kernel_of_map_eq_tilted_joint_laws (ρ : Measure (_ × S))
    (fun h x ↦ ENNReal.ofReal (Real.exp
      (inner ℝ h x-inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2)))
    (fun h ↦ by fun_prop) (Matrix.toEuclideanCLM (𝕜 := ℝ) I) (by fun_prop)
    (fun h ↦ multivariateGaussian h I⁻¹) L
  · intro h
    rw [hfst]
    exact map_gaussian_shift_eq_with_density hI h
  · intro h
    by_cases hh : h = 0
    · subst h
      simpa using hsnd.symm
    let a : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
      inner ℝ h x-inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2
    let w : EuclideanSpace ℝ (Fin d) × S → ℝ := fun p ↦ Real.exp (a p.1)
    have ha : Continuous a := by dsimp [a]; fun_prop
    have hw : Continuous w := by dsimp [w]; fun_prop
    have hw0 : ∀ p, 0 ≤ w p := fun p ↦ (Real.exp_pos _).le
    have hm : ∫ p, w p ∂(ρ : Measure (_ × S)) = 1 := by
      calc
        _ = ∫ x, Real.exp (a x) ∂(ρ : Measure (_ × S)).fst := by
          rw [Measure.fst,integral_map measurable_fst.aemeasurable (by fun_prop)]
        _ = 1 := by
          rw [hfst]
          exact integral_exp_inner_sub_half_covariance hI.posSemidef h
    have hi : Integrable w (ρ : Measure (_ × S)) := by
      by_contra hni
      rw [integral_undef hni] at hm
      exact zero_ne_one hm
    have := is_probability_measure_with_density_of_real_integral_one
      (ρ : Measure (_ × S)) w hw0 hi hm
    let P0 : ∀ n, Measure (Ω (φ n)) := fun n ↦ (P (φ n) 0 : Measure _)
    let Q : ∀ n, Measure (Ω (φ n)) := fun n ↦ (P (φ n) h : Measure _)
    let U : ∀ n, Ω (φ n) → EuclideanSpace ℝ (Fin d) × S :=
      fun n ω ↦ (Δ (φ n) ω,T (φ n) ω)
    let Λ : ∀ n, Ω (φ n) → ℝ :=
      fun n ω ↦ Real.log (((Q n).rnDeriv (P0 n) ω).toReal)
    have hU (n : ℕ) : Measurable (U n) := (hΔ _).prodMk (hT _)
    have hΛ (n : ℕ) : Measurable (Λ n) :=
      Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal
    let f : EuclideanSpace ℝ (Fin d) × S → (EuclideanSpace ℝ (Fin d) × S) × ℝ :=
      fun p ↦ (p,a p.1)
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hbase := hjoint.continuous_comp hf
    have hlograw := tendsto_in_distribution_of_dist_small_in_probability
      (fun n ω ↦ (U n ω,Λ n ω)) f hbase ?_
      (fun n ↦ ((hU n).prodMk (hΛ n)).aemeasurable)
    · have hlog : TendstoInDistribution (fun n ω ↦ (U n ω,Λ n ω)) atTop id P0
          ((ρ : Measure (_ × S)).map f) := by
        refine ⟨fun n ↦ ((hU n).prodMk (hΛ n)).aemeasurable,
          measurable_id.aemeasurable,?_⟩
        simpa only [Measure.map_id] using hlograw.tendsto
      have hzero : ((ρ : Measure (_ × S)).map f).snd {0} = 0 := by
        rw [Measure.snd,Measure.map_map measurable_snd hf.measurable,
          Measure.map_apply (measurable_snd.comp hf.measurable) (measurableSet_singleton 0)]
        change (ρ : Measure (_ × S)) (Prod.fst ⁻¹' {x | a x = 0}) = 0
        change (ρ : Measure (_ × S)) (Prod.fst ⁻¹' (a ⁻¹' ({0} : Set ℝ))) = 0
        rw [← Measure.map_apply measurable_fst (ha.measurable (measurableSet_singleton 0))]
        change (ρ : Measure (_ × S)).fst {x | a x = 0} = 0
        rw [hfst]
        exact multivariate_gaussian_affine_score_zero hI h hh
      have hRN := tendsto_in_distribution_joint_rn_deriv_of_log P0 Q U hU _ hlog hzero
      have hgraph : (((ρ : Measure (_ × S)).map f).map
          (fun z ↦ (z.1,Real.exp z.2))) =
          (ρ : Measure (_ × S)).map (fun p ↦ (p,w p)) := by
        rw [Measure.map_map (by fun_prop) hf.measurable]
        rfl
      have hRN' : TendstoInDistribution
          (fun n ω ↦ (U n ω,((Q n).rnDeriv (P0 n) ω).toReal)) atTop id P0
          ((ρ : Measure (_ × S)).map (fun p ↦ (p,w p))) := by
        simpa only [hgraph] using hRN
      have hchange := tendsto_in_distribution_of_joint_rn_deriv_graph
        P0 Q U hU (ρ : Measure (_ × S)) w hw hw0 hm hRN'
      have hsub : TendstoInDistribution (fun n ↦ T (φ n)) atTop id Q (L h) :=
        ⟨fun n ↦ (hT _).aemeasurable,measurable_id.aemeasurable,
          (hlim h).tendsto.comp hφ.tendsto_atTop⟩
      have heq := tendstoInDistribution_unique (fun n ↦ T (φ n)) hsub
        (hchange.continuous_comp continuous_snd)
      simpa only [Function.comp_def,Measure.map_id,Measure.snd,id_eq,w,a] using heq
    · intro ε hε
      have htail := (hrem h (ε/2) (by positivity)).comp hφ.tendsto_atTop
      apply squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) htail
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have hω' : ε ≤ |Λ n ω-a (Δ (φ n) ω)| := by
        simpa only [f,U,Function.comp_apply,dist_prod_same_left,Real.dist_eq,
          Set.mem_ofPred_eq] using hω
      have heq : Λ n ω-a (Δ (φ n) ω) =
          Real.log (((P (φ n) h : Measure _).rnDeriv (P (φ n) 0) ω).toReal) -
          inner ℝ h (Δ (φ n) ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2 := by
        dsimp [Λ,Q,P0,a]
        ring
      change ε/2 < |Real.log (((P (φ n) h : Measure _).rnDeriv (P (φ n) 0) ω).toReal) -
        inner ℝ h (Δ (φ n) ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h)/2|
      rw [← heq]
      exact (half_lt_self hε).trans_le hω'

/-- GAPS 102.16: Hájek's convolution theorem. In a LAN experiment with information `I`, the limit
law `L` of a regular estimator sequence is the convolution of `N(0, I⁻¹)` with a probability
measure `M`. -/
theorem exists_convolution_of_is_regular_estimator
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (hreg : IsRegularEstimator P T L) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure M ∧
      L = (multivariateGaussian 0 I⁻¹).conv M := by
  let Lh : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) :=
    fun h ↦ L.map (fun y ↦ h+y)
  have : ∀ h, IsProbabilityMeasure (Lh h) := fun h ↦ by dsimp [Lh]; infer_instance
  have hlim (h : EuclideanSpace ℝ (Fin d)) : TendstoInDistribution T atTop id
      (fun n ↦ (P n h : Measure (Ω n))) (Lh h) := by
    have hc := (hreg.2 h).continuous_comp (g := fun y ↦ h+y) (by fun_prop)
    have hl := tendsto_in_distribution_of_map_eq hc
      (μ'' := L.map (fun y ↦ h+y)) (W := id) aemeasurable_id (by rw [Measure.map_id]; rfl)
    have heq : (fun n ↦ (fun y ↦ h+y) ∘ (fun ω ↦ T n ω-h)) = T := by
      funext n ω
      dsimp only [Function.comp_def]
      abel
    rwa [heq] at hl
  obtain ⟨K,hK,hLaw⟩ := exists_gaussian_shift_kernel_of_local_limits P I Δ hLAN T hreg.1 Lh hlim
  have := hK
  exact exists_convolution_of_gaussian_shift_kernel hLAN.1.inv K L (fun h ↦ (hLaw h).symm)


/-- GAPS 102.17: the local asymptotic minimax theorem. In a LAN experiment with information `I`,
for a lower semicontinuous, symmetric, quasiconvex (bowl-shaped) loss `ℓ ≥ 0`, every estimator
sequence satisfies `E ℓ(N(0, I⁻¹)) ≤ sup_c liminf_n sup_{‖h‖ ≤ c} E_h ℓ(T n - h)`. -/
theorem gaussian_risk_le_local_asymptotic_minimax
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hT : ∀ n, Measurable (T n))
    (loss : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hl : LowerSemicontinuous loss)
    (hsym : ∀ x, loss (-x) = loss x) (hconv : ∀ c, Convex ℝ {x | loss x ≤ c}) :
    (∫⁻ x, loss x ∂multivariateGaussian 0 I⁻¹) ≤
      ⨆ c : ℝ≥0, Filter.liminf (fun n ↦ ⨆ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ c},
        ∫⁻ ω, loss (T n ω - h.val) ∂(P n h.val : Measure (Ω n))) atTop := by
  sorry

/-- GAPS 102.28: functional delta method for measurable maps and a closed tangent space.
The outer version for nonmeasurable empirical processes uses `TendstoInOuterDistribution`. -/
theorem tendsto_in_distribution_of_has_hadamard_f_deriv_at
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E) (hT : ∀ n, Measurable (T n))
    (θ : E) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop atTop)
    (G : Measure E) [IsProbabilityMeasure G] (D₀ : Submodule ℝ E) (hclosed : IsClosed (D₀ : Set E))
    (hsupp : G D₀ = 1) (g : E → F) (hg : Measurable g) (domain : Set E)
    (hdomain : ∀ n ω, T n ω ∈ domain) (D : E →L[ℝ] F)
    (hd : HasHadamardFDerivAt g domain D₀ D θ)
    (hlim : TendstoInDistribution (fun (n : ℕ) ω ↦ r n • (T n ω - θ)) atTop id (fun _ ↦ μ) G) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ r n • (g (T n ω) - g θ)) atTop id (fun _ ↦ μ)
      (G.map D) := by
  set Z : ℕ → Ω → E := fun n ω ↦ r n • (T n ω - θ) with hZ
  set Y : ℕ → Ω → F := fun n ω ↦ r n • (g (T n ω) - g θ) with hY
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hT n)
  have hYm : ∀ n, Measurable (Y n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hg.comp (hT n))
  -- Probability-measure versions of the laws.
  let PZ : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μ.map (Z n), inferInstance⟩
  let PY : ℕ → ProbabilityMeasure F := fun n ↦ ⟨μ.map (Y n), inferInstance⟩
  let PG : ProbabilityMeasure E := ⟨G, inferInstance⟩
  let PGD : ProbabilityMeasure F := ⟨G.map D, inferInstance⟩
  have hZlim : Tendsto PZ atTop (𝓝 PG) := (tendsto_in_distribution_id_iff.1 hlim).2
  suffices hYlim : Tendsto PY atTop (𝓝 PGD) from
    tendsto_in_distribution_id_iff.2 ⟨fun n ↦ (hYm n).aemeasurable, hYlim⟩
  refine tendsto_of_forall_isClosed_limsup_le' fun Fc hFc ↦ ?_
  -- The sets of local increments mapped into `Fc` at stage `m`.
  let A : ℕ → Set E := fun m ↦
    {h | θ + (r m)⁻¹ • h ∈ domain ∧ r m • (g (θ + (r m)⁻¹ • h) - g θ) ∈ Fc}
  let C : ℕ → Set E := fun k ↦ closure (⋃ m ≥ k, A m)
  have hCc : ∀ k, IsClosed (C k) := fun k ↦ isClosed_closure
  have hCanti : Antitone C := fun k l hkl ↦
    closure_mono (iUnion₂_subset fun m hm ↦ subset_iUnion₂_of_subset m (hkl.trans hm) le_rfl)
  have hTZ : ∀ n ω, θ + (r n)⁻¹ • Z n ω = T n ω := fun n ω ↦ by
    simp only [hZ, smul_smul, inv_mul_cancel₀ (hr n).ne', one_smul, add_sub_cancel]
  -- Step 1: bound the laws of `Yₙ` on `Fc` by those of `Zₙ` on `C k`.
  have hstep : ∀ k, limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (C k) := by
    intro k
    have hle : ∀ n ≥ k, (PY n : Measure F) Fc ≤ (PZ n : Measure E) (C k) := by
      intro n hn
      change μ.map (Y n) Fc ≤ μ.map (Z n) (C k)
      rw [Measure.map_apply (hYm n) hFc.measurableSet,
        Measure.map_apply (hZm n) (hCc k).measurableSet]
      refine measure_mono fun ω hω ↦ subset_closure ?_
      refine mem_iUnion₂.2 ⟨n, hn, ?_⟩
      simp only [A, mem_ofPred_eq, hTZ]
      exact ⟨hdomain n ω, hω⟩
    calc limsup (fun n ↦ (PY n : Measure F) Fc) atTop
        ≤ limsup (fun n ↦ (PZ n : Measure E) (C k)) atTop :=
          limsup_le_limsup (eventually_atTop.2 ⟨k, hle⟩)
      _ ≤ G (C k) := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hZlim (hCc k)
  -- Step 2: pass to the intersection.
  have hInter : Tendsto (fun k ↦ G (C k)) atTop (𝓝 (G (⋂ k, C k))) :=
    tendsto_measure_iInter_atTop (fun k ↦ (hCc k).measurableSet.nullMeasurableSet) hCanti
      ⟨0, measure_ne_top _ _⟩
  have hlimsup : limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (⋂ k, C k) :=
    ge_of_tendsto hInter (Eventually.of_forall hstep)
  -- Step 3: on `D₀`, the intersection maps into `Fc`.
  have hsub : (⋂ k, C k) ∩ D₀ ⊆ D ⁻¹' Fc := by
    rintro v ⟨hv, hvD⟩
    have hvk : ∀ k : ℕ, ∃ m, k ≤ m ∧ ∃ h ∈ A m, dist h v < 1 / ((k : ℝ) + 1) := by
      intro k
      have hk := mem_iInter.1 hv k
      obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.1 hk _ Nat.one_div_pos_of_nat
      obtain ⟨m, hm, hhm⟩ := mem_iUnion₂.1 hh
      exact ⟨m, hm, h, hhm, by rwa [dist_comm]⟩
    choose m hm h hhA hhd using hvk
    have hmlim : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
    have ht : Tendsto (fun k ↦ (r (m k))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hrlim.comp hmlim)
    have hh : Tendsto h atTop (𝓝 v) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hhd k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := hd.2 (fun k ↦ (r (m k))⁻¹) h v (fun k ↦ inv_pos.2 (hr _)) ht hh hvD
      (fun k ↦ (hhA k).1)
    simp only [inv_inv] at hconv
    exact hFc.mem_of_tendsto hconv (Eventually.of_forall fun k ↦ (hhA k).2)
  -- Step 4: conclude.
  have hD0c : G (D₀ : Set E)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hclosed.measurableSet, hsupp, tsub_self]
  refine hlimsup.trans ?_
  change G (⋂ k, C k) ≤ G.map D Fc
  rw [Measure.map_apply D.continuous.measurable hFc.measurableSet]
  calc G (⋂ k, C k) ≤ G (((⋂ k, C k) ∩ D₀) ∪ (D₀ : Set E)ᶜ) := by
        refine measure_mono fun v hv ↦ ?_
        by_cases hvD : v ∈ (D₀ : Set E)
        · exact Or.inl ⟨hv, hvD⟩
        · exact Or.inr hvD
    _ ≤ G ((⋂ k, C k) ∩ D₀) + G (D₀ : Set E)ᶜ := measure_union_le _ _
    _ ≤ G (D ⁻¹' Fc) := by rw [hD0c, add_zero]; exact measure_mono hsub


/-- Fisher–Rao bilinear form on the open finite probability simplex. -/
def fisherRaoMetric {m : ℕ} (p u v : Fin m → ℝ) : ℝ := ∑ i, u i * v i / p i

/-- Amari–Chentsov symmetric cubic tensor on the open probability simplex. -/
def amariChentsovTensor {m : ℕ} (p u v w : Fin m → ℝ) : ℝ :=
  ∑ i, u i * v i * w i / p i ^ 2

/-- The open probability simplex. -/
def openProbabilitySimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- Tangent space of the probability simplex, represented by zero-sum vectors. -/
def simplexTangentSpace (m : ℕ) : Submodule ℝ (Fin m → ℝ) where
  carrier := {u | ∑ i, u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    change (∑ i, u i) = 0 at hu
    change (∑ i, v i) = 0 at hv
    change (∑ i, (u i + v i)) = 0
    rw [Finset.sum_add_distrib, hu, hv, add_zero]
  smul_mem' := by
    intro a u hu
    change (∑ i, u i) = 0 at hu
    change (∑ i, a * u i) = 0
    rw [← Finset.mul_sum, hu, mul_zero]

/-- A congruent embedding splits each input category into a nonempty block of output categories. -/
structure CongruentSimplexEmbedding (m n : ℕ) where
  /-- Block label of an output category. -/
  block : Fin n → Fin m
  /-- Every input category has a block. -/
  surjective_block : Function.Surjective block
  /-- Conditional probability of each output category within its block. -/
  weight : Fin n → ℝ
  /-- Strictly positive weights. -/
  weight_pos : ∀ j, 0 < weight j
  /-- Weights in a block sum to one. -/
  sum_weight : ∀ i, ∑ j, (if block j = i then weight j else 0) = 1

/-- The map `p ↦ (p (block j) · weight j)ⱼ` of a congruent simplex embedding; it is the
restriction of a linear map, and so is its own derivative. -/
def CongruentSimplexEmbedding.map {m n : ℕ} (f : CongruentSimplexEmbedding m n)
    (p : Fin m → ℝ) : Fin n → ℝ := fun j ↦ p (f.block j) * f.weight j

/-- GAPS 102.58: the Fisher–Rao metric `∑ uᵢ vᵢ / pᵢ` on the open simplex is invariant under
congruent embeddings (Chentsov's defining invariance). -/
theorem fisher_rao_metric_congruent_embedding {m n : ℕ} (f : CongruentSimplexEmbedding m n)
    (p : Fin m → ℝ) (hp : p ∈ openProbabilitySimplex m) (u v : Fin m → ℝ) :
    fisherRaoMetric (f.map p) (f.map u) (f.map v) = fisherRaoMetric p u v := by
  let a := fun i ↦ u i * v i / p i
  have hterm (j : Fin n) : f.map u j * f.map v j / f.map p j = a (f.block j) * f.weight j := by
    dsimp [CongruentSimplexEmbedding.map, a]
    field_simp [ne_of_gt (hp.1 (f.block j)), ne_of_gt (f.weight_pos j)]

  unfold fisherRaoMetric
  simp_rw [hterm]
  calc
    (∑ j, a (f.block j) * f.weight j) =
        ∑ j, ∑ i, if f.block j = i then a i * f.weight j else 0 := by simp
    _ = ∑ i, ∑ j, if f.block j = i then a i * f.weight j else 0 := Finset.sum_comm
    _ = ∑ i, a i * (∑ j, if f.block j = i then f.weight j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ i, u i * v i / p i := by simp_rw [f.sum_weight, mul_one]; rfl

/-- For probability measures, `CKSD.IsContiguous` is Statlib's direct set formulation
`Contiguous5` of contiguity. -/
theorem is_contiguous_iff_contiguous5 {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → ProbabilityMeasure Ω) :
    IsContiguous (fun n ↦ (P n : Measure Ω)) (fun n ↦ (Q n : Measure Ω)) ↔
      _root_.Contiguous5 atTop P Q := by
  constructor
  · intro h A hA hP
    apply NNReal.tendsto_coe.mp
    have hp := NNReal.tendsto_coe.mpr hP
    have hq := h A hA (by simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hp)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hq
  · intro h A hA hP
    have hp : Tendsto (fun n ↦ P n (A n)) atTop (𝓝 0) := by
      apply NNReal.tendsto_coe.mp
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hP
    have hq := NNReal.tendsto_coe.mpr (h hA hp)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hq

end CKSD
