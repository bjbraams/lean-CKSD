module

public import CKSD.Asymptotics.LAN.Basic
import CKSD.Asymptotics.LAN.ConvolutionKernel
import CKSD.Asymptotics.LAN.LikelihoodLimit
import CKSD.Asymptotics.LAN.JointLimit
import CKSD.Asymptotics.LAN.GaussianShiftTilt
import CKSD.Inference.KernelDisintegration
public import Mathlib.Order.CompletePartialOrder
import CKSD.Asymptotics.LAN.Approximation
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Asymptotic representation, convolution and local asymptotic minimax theorems

The limit theorems for locally asymptotically normal experiments: limits of statistics are
randomizations of the Gaussian shift experiment, limit laws of regular estimators are Gaussian
convolutions, and the Gaussian risk bounds the local asymptotic minimax risk.

## Main results

* `CKSD.exists_gaussian_shift_kernel_of_local_limits`: limits of statistics in a LAN experiment
  are randomizations of the Gaussian shift experiment (GAPS 102.15).
* `CKSD.exists_convolution_of_isRegularEstimator`: Hájek's convolution theorem (GAPS 102.16).
* `CKSD.gaussian_risk_le_local_asymptotic_minimax`: the local asymptotic minimax theorem
  (GAPS 102.17).

## Conventions

The definitions of `CKSD.LocalExperiment`, `CKSD.IsLocallyAsymptoticallyNormal` and
`CKSD.IsRegularEstimator` are in `CKSD.Asymptotics.LAN.Basic`. Convolutions of laws are
Mathlib's `MeasureTheory.Measure.conv`. The common randomization kernel is constructed in
`CKSD.Inference.KernelDisintegration`.

## References

van der Vaart, *Asymptotic Statistics*, Chapters 7 and 8 (asymptotic representation,
convolution and local asymptotic minimax theorems).
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

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
  rcases hLAN with ⟨hI, hΔ, hΔlim, hrem⟩
  obtain ⟨φ, hφ, ρ, hjoint, hfst, hsnd⟩ :=
    exists_joint_subsequence_limit_of_marginal_limits
      (fun n ↦ (P n 0 : Measure (Ω n))) Δ T hΔ hT
      (multivariateGaussian 0 I) (L 0) hΔlim (hlim 0)
  apply exists_markovKernel_of_map_eq_tilted_joint_laws (ρ : Measure (_ × S))
    (fun h x ↦ ENNReal.ofReal (Real.exp
      (inner ℝ h x - inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2)))
    (fun h ↦ by fun_prop) (Matrix.toEuclideanCLM (𝕜 := ℝ) I) (by fun_prop)
    (fun h ↦ multivariateGaussian h I⁻¹) L
  · intro h
    rw [hfst]
    exact map_gaussianShift_eq_withDensity hI h
  · intro h
    by_cases hh : h = 0
    · subst h
      simpa using hsnd.symm
    let a : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
      inner ℝ h x - inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2
    let w : EuclideanSpace ℝ (Fin d) × S → ℝ := fun p ↦ Real.exp (a p.1)
    have ha : Continuous a := by dsimp [a]; fun_prop
    have hw : Continuous w := by dsimp [w]; fun_prop
    have hw0 : ∀ p, 0 ≤ w p := fun p ↦ (Real.exp_pos _).le
    have hm : ∫ p, w p ∂(ρ : Measure (_ × S)) = 1 := by
      calc
        _ = ∫ x, Real.exp (a x) ∂(ρ : Measure (_ × S)).fst := by
          rw [Measure.fst, integral_map measurable_fst.aemeasurable (by fun_prop)]
        _ = 1 := by
          rw [hfst]
          exact integral_exp_inner_sub_half_covariance hI.posSemidef h
    have hi : Integrable w (ρ : Measure (_ × S)) := by
      by_contra hni
      rw [integral_undef hni] at hm
      exact zero_ne_one hm
    have := isProbabilityMeasure_withDensity_of_real_integral_one
      (ρ : Measure (_ × S)) w hw0 hi hm
    let P0 : ∀ n, Measure (Ω (φ n)) := fun n ↦ (P (φ n) 0 : Measure _)
    let Q : ∀ n, Measure (Ω (φ n)) := fun n ↦ (P (φ n) h : Measure _)
    let U : ∀ n, Ω (φ n) → EuclideanSpace ℝ (Fin d) × S :=
      fun n ω ↦ (Δ (φ n) ω, T (φ n) ω)
    let Λ : ∀ n, Ω (φ n) → ℝ :=
      fun n ω ↦ Real.log (((Q n).rnDeriv (P0 n) ω).toReal)
    have hU (n : ℕ) : Measurable (U n) := (hΔ _).prodMk (hT _)
    have hΛ (n : ℕ) : Measurable (Λ n) :=
      Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal
    let f : EuclideanSpace ℝ (Fin d) × S → (EuclideanSpace ℝ (Fin d) × S) × ℝ :=
      fun p ↦ (p, a p.1)
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hbase := hjoint.continuous_comp hf
    have hlograw := tendstoInDistribution_of_dist_small_in_probability
      (fun n ω ↦ (U n ω, Λ n ω)) f hbase ?_
      (fun n ↦ ((hU n).prodMk (hΛ n)).aemeasurable)
    · have hlog : TendstoInDistribution (fun n ω ↦ (U n ω, Λ n ω)) atTop id P0
          ((ρ : Measure (_ × S)).map f) := by
        refine ⟨fun n ↦ ((hU n).prodMk (hΛ n)).aemeasurable,
          measurable_id.aemeasurable, ?_⟩
        simpa only [Measure.map_id] using hlograw.tendsto
      have hzero : ((ρ : Measure (_ × S)).map f).snd {0} = 0 := by
        rw [Measure.snd, Measure.map_map measurable_snd hf.measurable,
          Measure.map_apply (measurable_snd.comp hf.measurable) (measurableSet_singleton 0)]
        have h0 := multivariateGaussian_affine_score_eq_zero hI h hh
        rw [← hfst, Measure.fst_apply (s := {x | a x = 0})
          (ha.measurable (measurableSet_singleton 0))] at h0
        exact h0
      have hRN := tendstoInDistribution_joint_rnDeriv_of_log P0 Q U hU _ hlog hzero
      have hgraph : (((ρ : Measure (_ × S)).map f).map
          (fun z ↦ (z.1, Real.exp z.2))) =
          (ρ : Measure (_ × S)).map (fun p ↦ (p, w p)) := by
        rw [Measure.map_map (by fun_prop) hf.measurable]
        rfl
      have hRN' : TendstoInDistribution
          (fun n ω ↦ (U n ω, ((Q n).rnDeriv (P0 n) ω).toReal)) atTop id P0
          ((ρ : Measure (_ × S)).map (fun p ↦ (p, w p))) := by
        simpa only [hgraph] using hRN
      have hchange := tendstoInDistribution_of_joint_rnDeriv_graph
        P0 Q U hU (ρ : Measure (_ × S)) w hw hw0 hm hRN'
      have hsub : TendstoInDistribution (fun n ↦ T (φ n)) atTop id Q (L h) :=
        ⟨fun n ↦ (hT _).aemeasurable, measurable_id.aemeasurable,
          (hlim h).tendsto.comp hφ.tendsto_atTop⟩
      have heq := tendstoInDistribution_unique (fun n ↦ T (φ n)) hsub
        (hchange.continuous_comp continuous_snd)
      simpa only [Function.comp_def, Measure.map_id, Measure.snd, id_eq, w, a] using heq
    · intro ε hε
      have htail := (hrem h (ε / 2) (by positivity)).comp hφ.tendsto_atTop
      apply squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) htail
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have hω' : ε ≤ |Λ n ω - a (Δ (φ n) ω)| := by
        simpa only [f, U, Function.comp_apply, dist_prod_same_left, Real.dist_eq,
          Set.mem_ofPred_eq] using hω
      have heq : Λ n ω - a (Δ (φ n) ω) =
          Real.log (((P (φ n) h : Measure _).rnDeriv (P (φ n) 0) ω).toReal) -
          inner ℝ h (Δ (φ n) ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2 := by
        dsimp [Λ, Q, P0, a]
        ring
      simp only [Set.mem_ofPred_eq]
      rw [← heq]
      exact (half_lt_self hε).trans_le hω'

/-- GAPS 102.16: Hájek's convolution theorem. In a LAN experiment with information `I`, the limit
law `L` of a regular estimator sequence is the convolution of `N(0, I⁻¹)` with a probability
measure `M`. -/
theorem exists_convolution_of_isRegularEstimator
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (hreg : IsRegularEstimator P T L) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure M ∧
      L = (multivariateGaussian 0 I⁻¹).conv M := by
  let Lh : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) :=
    fun h ↦ L.map (fun y ↦ h + y)
  have : ∀ h, IsProbabilityMeasure (Lh h) := fun h ↦ by dsimp [Lh]; infer_instance
  have hlim (h : EuclideanSpace ℝ (Fin d)) : TendstoInDistribution T atTop id
      (fun n ↦ (P n h : Measure (Ω n))) (Lh h) := by
    have hc := (hreg.2 h).continuous_comp (g := fun y ↦ h + y) (by fun_prop)
    have hl := tendstoInDistribution_of_map_eq hc
      (μ'' := L.map (fun y ↦ h + y)) (W := id) aemeasurable_id (by rw [Measure.map_id]; rfl)
    have heq : (fun n ↦ (fun y ↦ h + y) ∘ (fun ω ↦ T n ω - h)) = T := by
      funext n ω
      dsimp only [Function.comp_def]
      abel
    rwa [heq] at hl
  obtain ⟨K, hK, hLaw⟩ := exists_gaussian_shift_kernel_of_local_limits P I Δ hLAN T hreg.1 Lh hlim
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

end CKSD
