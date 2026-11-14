module

public import CKSD.Bayes.ParticleFilter
public import CKSD.Asymptotics.Lindeberg.Basic
public import CKSD.Bayes.ParticleFluctuations

/-!
# Central limit theorem for the local errors of the bootstrap particle filter

Given the past, the next generation of the bootstrap particle filter consists of independent
draws from the prediction law, so the conditional characteristic function of a local error
(`CKSD.FeynmanKacModel.localError`) is the `N`-th power of a characteristic function. The
Gaussian comparison of `CKSD.Bayes.ParticleFluctuations` and the Lévy continuity theorem give the
central limit theorem for the summed local errors.

## Main results

* `CKSD.integral_cexp_sum_localError_succ`: one step of the characteristic function recursion.
* `CKSD.tendsto_integral_cexp_sum_localError`: convergence of the characteristic functions of the
  summed local errors.
* `CKSD.tendstoInDistribution_sum_localError`: the central limit theorem for the summed local
  errors.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The path obtained from the first `n + 1` generations `yz.1` followed by the generation `yz.2`
(repeated at all later times). -/
private def extendPath {N n : ℕ} (yz : (Fin (n + 1) → Fin N → X) × (Fin N → X)) (q : ℕ) :
    Fin N → X :=
  if h : q < n + 1 then yz.1 ⟨q, h⟩ else yz.2

/-- `extendPath` is measurable. -/
private theorem measurable_extendPath {N n : ℕ} :
    Measurable (extendPath : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℕ → Fin N → X) := by
  refine measurable_pi_iff.2 fun q ↦ ?_
  by_cases h : q < n + 1
  · simp only [extendPath, h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [extendPath, h, dite_false]
    exact measurable_snd

omit [MeasurableSpace X] in
/-- Extending the first `n + 1` generations of a path by a generation `z` keeps generations
`q < n + 1`. -/
private theorem extendPath_of_lt {N n : ℕ} (x : ℕ → Fin N → X) (z : Fin N → X) {q : ℕ}
    (hq : q < n + 1) : extendPath ((fun i : Fin (n + 1) ↦ x i), z) q = x q := by
  simp [extendPath, hq]

omit [MeasurableSpace X] in
/-- Extending the first `n + 1` generations of a path by a generation `z` puts `z` at time
`n + 1`. -/
private theorem extendPath_succ {N n : ℕ} (y : Fin (n + 1) → Fin N → X) (z : Fin N → X) :
    extendPath (y, z) (n + 1) = z := by
  simp [extendPath]

/-- The norm of `exp (i t s)` for real `t, s` is one. -/
private theorem norm_cexp_mul_mul_I (t s : ℝ) : ‖cexp (t * s * I)‖ = 1 := by
  rw [← ofReal_mul, norm_exp_ofReal_mul_I]

/-- One generation of the characteristic function recursion: conditionally on the first `m + 1`
generations, the characteristic function of the local error of generation `m + 1` is the
`(N + 1)`-th power of a characteristic function under the prediction law. -/
theorem integral_cexp_sum_localError_succ [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X) (N : ℕ)
    (ξ : ℕ → Ω → Fin (N + 1) → X) (hξ : IsBootstrapParticleSystem P M (N + 1) ξ)
    (φ : ℕ → X → ℝ) (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B)
    (t : ℝ) (m : ℕ) :
    Integrable (fun ω ↦ cexp (t * (∑ p ∈ Finset.range (m + 1),
        M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) *
      (∫ x, cexp (((t * M.particleLikelihood (fun q ↦ ξ q ω) (m + 1)) / Real.sqrt (N + 1) : ℝ) *
        (φ (m + 1) x - ∫ y, φ (m + 1) y ∂M.particlePredictionLaw m (ξ m ω)) * I)
          ∂M.particlePredictionLaw m (ξ m ω)) ^ (N + 1)) P ∧
    ∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1 + 1), M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) ∂P =
      ∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1),
        M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) *
      (∫ x, cexp (((t * M.particleLikelihood (fun q ↦ ξ q ω) (m + 1)) / Real.sqrt (N + 1) : ℝ) *
        (φ (m + 1) x - ∫ y, φ (m + 1) y ∂M.particlePredictionLaw m (ξ m ω)) * I)
          ∂M.particlePredictionLaw m (ξ m ω)) ^ (N + 1) ∂P := by
  have hS : Measurable fun yz : (Fin (m + 1) → Fin (N + 1) → X) × (Fin (N + 1) → X) ↦
      ∑ p ∈ Finset.range (m + 1 + 1), M.localError φ (extendPath yz) p :=
    Finset.measurable_sum _ fun p _ ↦ (M.measurable_localError hφ hB p).comp measurable_extendPath
  have hH : Measurable fun yz : (Fin (m + 1) → Fin (N + 1) → X) × (Fin (N + 1) → X) ↦
      cexp (t * (∑ p ∈ Finset.range (m + 1 + 1), M.localError φ (extendPath yz) p : ℝ) * I) := by
    fun_prop
  have key := integral_bootstrap_succ P M (N + 1) ξ hξ m _ hH (C := 1)
    fun yz ↦ (norm_cexp_mul_mul_I _ _).le
  have hinner : ∀ ω, ∫ z, cexp (t * (∑ p ∈ Finset.range (m + 1 + 1),
        M.localError φ (extendPath ((fun i : Fin (m + 1) ↦ ξ i ω), z)) p : ℝ) * I)
        ∂Measure.pi (fun _ : Fin (N + 1) ↦ M.particlePredictionLaw m (ξ m ω)) =
      cexp (t * (∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) *
      (∫ x, cexp (((t * M.particleLikelihood (fun q ↦ ξ q ω) (m + 1)) / Real.sqrt (N + 1) : ℝ) *
        (φ (m + 1) x - ∫ y, φ (m + 1) y ∂M.particlePredictionLaw m (ξ m ω)) * I)
          ∂M.particlePredictionLaw m (ξ m ω)) ^ (N + 1) := by
    intro ω
    have := M.isProbabilityMeasure_particlePredictionLaw (Nat.succ_pos N) m (ξ m ω)
    set c := ∫ y, φ (m + 1) y ∂M.particlePredictionLaw m (ξ m ω)
    set u := (t * M.particleLikelihood (fun q ↦ ξ q ω) (m + 1)) / Real.sqrt (N + 1)
    have hpt : ∀ z : Fin (N + 1) → X, cexp (t * (∑ p ∈ Finset.range (m + 1 + 1),
        M.localError φ (extendPath ((fun i : Fin (m + 1) ↦ ξ i ω), z)) p : ℝ) * I) =
        cexp (t * (∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) *
          cexp (u * (∑ j, (φ (m + 1) (z j) - c) : ℝ) * I) := by
      intro z
      have h1 : ∀ p ∈ Finset.range (m + 1),
          M.localError φ (extendPath ((fun i : Fin (m + 1) ↦ ξ i ω), z)) p =
            M.localError φ (fun q ↦ ξ q ω) p := fun p hp ↦
        M.localError_congr φ fun q hq ↦
          extendPath_of_lt (fun q ↦ ξ q ω) z (hq.trans_lt (Finset.mem_range.1 hp))
      have h2 : M.localError φ (extendPath ((fun i : Fin (m + 1) ↦ ξ i ω), z)) (m + 1) =
          M.particleLikelihood (fun q ↦ ξ q ω) (m + 1) * (∑ j, (φ (m + 1) (z j) - c)) /
            Real.sqrt (N + 1) := by
        simp only [FeynmanKacModel.localError, extendPath_succ]
        rw [M.particleLikelihood_congr (fun q hq ↦ extendPath_of_lt (fun q ↦ ξ q ω) z hq),
          M.pathPredMean_congr (fun q hq ↦ extendPath_of_lt (fun q ↦ ξ q ω) z hq)]
        push_cast
        rfl
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, h2, ← Complex.exp_add]
      congr 1
      simp only [u]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_cexp_sum_pi _ (N + 1) (fun x ↦ φ (m + 1) x - c) u]
    push_cast
    rfl
  have hlhs : ∀ ω, cexp (t * (∑ p ∈ Finset.range (m + 1 + 1),
      M.localError φ (extendPath ((fun i : Fin (m + 1) ↦ ξ i ω), ξ (m + 1) ω)) p : ℝ) * I) =
      cexp (t * (∑ p ∈ Finset.range (m + 1 + 1), M.localError φ (fun q ↦ ξ q ω) p : ℝ) * I) := by
    intro ω
    congr 4
    refine Finset.sum_congr rfl fun p hp ↦ M.localError_congr φ fun q hq ↦ ?_
    rcases Nat.lt_or_ge q (m + 1) with h | h
    · exact extendPath_of_lt (fun q ↦ ξ q ω) _ h
    · obtain rfl : q = m + 1 := le_antisymm (hq.trans (Nat.lt_succ_iff.1
        (Finset.mem_range.1 hp))) h
      exact extendPath_succ _ _
  have hA := aestronglyMeasurable_integral_bootstrap_succ P M (N + 1) ξ hξ m _ hH
  beta_reduce at key hA
  refine ⟨Integrable.of_bound (hA.congr (ae_of_all _ hinner)) 1 (ae_of_all _ fun ω ↦ ?_), ?_⟩
  · have := M.isProbabilityMeasure_particlePredictionLaw (Nat.succ_pos N) m (ξ m ω)
    rw [← hinner ω]
    refine (norm_integral_le_of_norm_le_const
      (ae_of_all _ fun z ↦ (norm_cexp_mul_mul_I _ _).le)).trans ?_
    simp
  · rw [← integral_congr_ae (ae_of_all _ hlhs), key]
    exact integral_congr_ae (ae_of_all _ hinner)

/-- `a / √(N + 1) + b / (N + 1) → 0`. -/
private theorem tendsto_div_sqrt_add_div (a b : ℝ) :
    Tendsto (fun N : ℕ ↦ a / Real.sqrt (N + 1) + b / (N + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ ↦ (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 := Real.tendsto_sqrt_atTop.comp h1
  simpa using (tendsto_const_nhds (x := a)).div_atTop h2 |>.add
    ((tendsto_const_nhds (x := b)).div_atTop h1)

/-- Central limit theorem for the local error of the initial generation, at the level of
characteristic functions. -/
theorem tendsto_integral_cexp_localError_zero [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (φ : ℕ → X → ℝ) (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B) (t : ℝ) :
    Tendsto (fun N ↦ ∫ ω, cexp (t * (M.localError φ (fun q ↦ ξ N q ω) 0 : ℝ) * I) ∂P) atTop
      (𝓝 (Real.exp (-(M.localVariance φ 0 * t ^ 2 / 2)) : ℂ)) := by
  set c := ∫ y, φ 0 y ∂(M.initial : Measure X)
  have hint : ∀ N : ℕ, ∫ ω, cexp (t * (M.localError φ (fun q ↦ ξ N q ω) 0 : ℝ) * I) ∂P =
      (∫ x, cexp ((t / Real.sqrt (N + 1) : ℝ) * (φ 0 x - c) * I) ∂(M.initial : Measure X)) ^
        (N + 1) := by
    intro N
    have hsum : Measurable fun z : Fin (N + 1) → X ↦ ∑ j, (φ 0 (z j) - c) :=
      Finset.measurable_sum _ fun j _ ↦ ((hφ 0).comp (measurable_pi_apply j)).sub_const _
    have hF : Measurable fun z : Fin (N + 1) → X ↦
        cexp ((t / Real.sqrt (N + 1) : ℝ) * (∑ j, (φ 0 (z j) - c) : ℝ) * I) := by fun_prop
    calc ∫ ω, cexp (t * (M.localError φ (fun q ↦ ξ N q ω) 0 : ℝ) * I) ∂P
        = ∫ ω, cexp ((t / Real.sqrt (N + 1) : ℝ) * (∑ j, (φ 0 (ξ N 0 ω j) - c) : ℝ) * I) ∂P := by
          refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
          simp only [FeynmanKacModel.localError, FeynmanKacModel.particleLikelihood_zero,
            FeynmanKacModel.pathPredMean, c]
          push_cast
          congr 1
          ring
      _ = ∫ z, cexp ((t / Real.sqrt (N + 1) : ℝ) * (∑ j, (φ 0 (z j) - c) : ℝ) * I)
            ∂(P.map (ξ N 0)) :=
          (integral_map ((hξ N).1 0).aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by
          rw [(hξ N).2.1, integral_cexp_sum_pi _ (N + 1) (fun x ↦ φ 0 x - c)]
          push_cast
          rfl
  have hvar : M.localVariance φ 0 * t ^ 2 / 2 =
      t ^ 2 * (∫ x, (φ 0 x - c) ^ 2 ∂(M.initial : Measure X)) / 2 := by
    simp only [FeynmanKacModel.localVariance, M.integral_filterLaw,
      FeynmanKacModel.unnormalizedLaw_zero, probReal_univ, inv_one, one_pow, one_mul, c]
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero, hvar]
  simp_rw [hint]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦
    norm_integral_cexp_pow_sub_gaussian_le (M.initial : Measure X) (hφ 0) (hB 0) N
      (le_refl |t|)) ?_
  exact tendsto_div_sqrt_add_div _ _

/-- The random Gaussian factors of the conditional characteristic functions are integrable. -/
private theorem integrable_norm_gaussianFactor_sub [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X) (N : ℕ)
    (ξ : ℕ → Ω → Fin (N + 1) → X) (hξ : IsBootstrapParticleSystem P M (N + 1) ξ)
    {g : X → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (t a : ℝ) (ha : 0 ≤ a)
    (p : ℕ) :
    Integrable (fun ω ↦ ‖(Real.exp (-((t * M.particleLikelihood (fun q ↦ ξ q ω) (p + 1)) ^ 2 *
        (∫ x, (g x - ∫ y, g y ∂M.particlePredictionLaw p (ξ p ω)) ^ 2
          ∂M.particlePredictionLaw p (ξ p ω)) / 2)) : ℂ) - (Real.exp (-a) : ℂ)‖) P := by
  have hpath : Measurable fun ω (q : ℕ) ↦ ξ q ω := measurable_pi_iff.2 fun q ↦ hξ.1 q
  have hg2 : ∀ x, |g x ^ 2| ≤ B ^ 2 := fun x ↦ by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hσ : (fun ω ↦ ∫ x, (g x - ∫ y, g y ∂M.particlePredictionLaw p (ξ p ω)) ^ 2
      ∂M.particlePredictionLaw p (ξ p ω)) = fun ω ↦
        ∫ x, g x ^ 2 ∂M.particlePredictionLaw p (ξ p ω) -
          (∫ x, g x ∂M.particlePredictionLaw p (ξ p ω)) ^ 2 := funext fun ω ↦ by
    have := M.isProbabilityMeasure_particlePredictionLaw (Nat.succ_pos N) p (ξ p ω)
    exact integral_sub_integral_sq hg hB
  have hσm : Measurable fun ω ↦ ∫ x, (g x - ∫ y, g y ∂M.particlePredictionLaw p (ξ p ω)) ^ 2
      ∂M.particlePredictionLaw p (ξ p ω) := by
    rw [hσ]
    exact ((M.measurable_integral_particlePredictionLaw p (hg.pow_const 2) hg2).comp (hξ.1 p)).sub
      (((M.measurable_integral_particlePredictionLaw p hg hB).comp (hξ.1 p)).pow_const 2)
  have hLm : Measurable fun ω ↦ M.particleLikelihood (fun q ↦ ξ q ω) (p + 1) :=
    (M.measurable_particleLikelihood _).comp hpath
  refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun ω ↦ ?_)
  have h0 : 0 ≤ ∫ x, (g x - ∫ y, g y ∂M.particlePredictionLaw p (ξ p ω)) ^ 2
      ∂M.particlePredictionLaw p (ξ p ω) := integral_nonneg fun _ ↦ sq_nonneg _
  rw [norm_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-((t * M.particleLikelihood (fun q ↦ ξ q ω) (p + 1)) ^ 2 *
      (∫ x, (g x - ∫ y, g y ∂M.particlePredictionLaw p (ξ p ω)) ^ 2
        ∂M.particlePredictionLaw p (ξ p ω)) / 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 ha)]

/-- Central limit theorem for the summed local errors of the first `m + 1` generations, at the
level of characteristic functions: `E exp (i t ∑ₚ₌₀ᵐ Wᴺₚ) → exp (-(∑ₚ vₚ) t² / 2)`. -/
theorem tendsto_integral_cexp_sum_localError [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (φ : ℕ → X → ℝ) (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B) (t : ℝ)
    (m : ℕ) :
    Tendsto (fun N ↦ ∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1),
        M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I) ∂P) atTop
      (𝓝 (Real.exp (-((∑ p ∈ Finset.range (m + 1), M.localVariance φ p) * t ^ 2 / 2)) : ℂ)) := by
  induction m with
  | zero => simpa using tendsto_integral_cexp_localError_zero P M ξ hξ φ hφ hB t
  | succ m ih =>
    have hpath : ∀ N, Measurable fun ω (q : ℕ) ↦ ξ N q ω := fun N ↦
      measurable_pi_iff.2 fun q ↦ (hξ N).1 q
    obtain ⟨⟨K, hK⟩, -⟩ := tendsto_integral_abs_particleLikelihood_sub P M ξ hξ (m + 1)
    have hv0 : 0 ≤ M.localVariance φ (m + 1) * t ^ 2 / 2 := by
      have : 0 ≤ M.localVariance φ (m + 1) :=
        mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
      positivity
    set g : ℂ := (Real.exp (-(M.localVariance φ (m + 1) * t ^ 2 / 2)) : ℂ) with hg
    set E : ℂ := (Real.exp (-((∑ p ∈ Finset.range (m + 1), M.localVariance φ p) * t ^ 2 / 2)) : ℂ)
    have hT : (Real.exp (-((∑ p ∈ Finset.range (m + 1 + 1), M.localVariance φ p) * t ^ 2 / 2)) :
        ℂ) = g * E := by
      rw [hg, ← ofReal_mul, ← Real.exp_add, Finset.sum_range_succ]
      congr 2
      ring
    have hgn : ‖g‖ ≤ 1 := by
      rw [hg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 hv0)
    have hA : ∀ N, Measurable fun ω ↦ cexp (t * (∑ p ∈ Finset.range (m + 1),
        M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I) := fun N ↦ by
      have : Measurable fun ω ↦ ∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ N q ω) p :=
        Finset.measurable_sum _ fun p _ ↦ (M.measurable_localError hφ hB p).comp (hpath N)
      fun_prop
    have hbd : ∀ N, ‖∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1 + 1),
        M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I) ∂P - g * E‖ ≤
        ((|t| * K) ^ 3 * (2 * B) / 3 * (2 * B) ^ 2 / Real.sqrt (N + 1) +
          (|t| * K) ^ 4 / 4 * (2 * B) ^ 2 * (2 * B) ^ 2 / (N + 1)) +
        ∫ ω, ‖(Real.exp (-((t * M.particleLikelihood (fun q ↦ ξ N q ω) (m + 1)) ^ 2 *
          (∫ x, (φ (m + 1) x - ∫ y, φ (m + 1) y ∂M.particlePredictionLaw m (ξ N m ω)) ^ 2
            ∂M.particlePredictionLaw m (ξ N m ω)) / 2)) : ℂ) - g‖ ∂P +
        ‖∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1),
          M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I) ∂P - E‖ := by
      intro N
      obtain ⟨hint, heq⟩ :=
        integral_cexp_sum_localError_succ P M N (ξ N) (hξ N) φ hφ hB t m
      have hgA : Integrable (fun ω ↦ g * cexp (t * (∑ p ∈ Finset.range (m + 1),
          M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I)) P :=
        (Integrable.of_bound (hA N).aestronglyMeasurable 1
          (ae_of_all _ fun ω ↦ (norm_cexp_mul_mul_I _ _).le)).const_mul g
      have hGi := integrable_norm_gaussianFactor_sub P M N (ξ N) (hξ N) (hφ (m + 1)) (hB _) t _
        hv0 m
      rw [heq, show ∀ a b : ℂ, a - g * E = (a - g * b) + g * (b - E) from fun a b ↦ by ring,
        ← integral_const_mul, ← integral_sub hint hgA]
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (|t| * K) ^ 3 * (2 * B) / 3 * (2 * B) ^ 2 / Real.sqrt (N + 1) +
          (|t| * K) ^ 4 / 4 * (2 * B) ^ 2 * (2 * B) ^ 2 / (N + 1) := ⟨_, rfl⟩
      rw [← hε]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_integral_le_integral_norm _).trans ((integral_mono (hint.sub hgA).norm
          ((integrable_const ε).add hGi) fun ω ↦ ?_).trans (le_of_eq ?_))
        swap
        · simp only [Pi.add_apply]
          rw [integral_add (integrable_const ε) hGi, integral_const, probReal_univ, one_smul]
        have := M.isProbabilityMeasure_particlePredictionLaw (Nat.succ_pos N) m (ξ N m ω)
        have hs : |t * M.particleLikelihood (fun q ↦ ξ N q ω) (m + 1)| ≤ |t| * K := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK N ω) (abs_nonneg t)
        have hJ := norm_integral_cexp_pow_sub_gaussian_le (M.particlePredictionLaw m (ξ N m ω))
          (hφ (m + 1)) (hB _) N hs
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [mul_comm g, ← mul_sub, norm_mul, norm_cexp_mul_mul_I, one_mul]
        exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hε ▸ hJ) le_rfl)
      · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hgn
    rw [hT, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hbd ?_
    have h := ((tendsto_div_sqrt_add_div ((|t| * K) ^ 3 * (2 * B) / 3 * (2 * B) ^ 2)
      ((|t| * K) ^ 4 / 4 * (2 * B) ^ 2 * (2 * B) ^ 2)).add
        (tendsto_integral_norm_gaussianFactor_sub P M ξ hξ φ hφ hB t m)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 ih)
    rw [add_zero, add_zero] at h
    exact h

/-- **Central limit theorem for the summed local errors** of the bootstrap particle filter:
`∑ₚ₌₀ᵐ Wᴺₚ` converges in distribution to the centred normal law with variance `∑ₚ₌₀ᵐ vₚ`. -/
theorem tendstoInDistribution_sum_localError [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (φ : ℕ → X → ℝ) (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B) (m : ℕ) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ ∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ N q ω) p) atTop id
      (fun _ ↦ P) (gaussianReal 0 (∑ p ∈ Finset.range (m + 1), M.localVariance φ p).toNNReal) := by
  have hS : ∀ N, Measurable fun ω ↦
      ∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ N q ω) p := fun N ↦
    Finset.measurable_sum _ fun p _ ↦ (M.measurable_localError hφ hB p).comp
      (measurable_pi_iff.2 fun q ↦ (hξ N).1 q)
  refine TendstoInDistribution.of_tendsto_charFun (fun N ↦ (hS N).aemeasurable) aemeasurable_id
    fun t ↦ ?_
  have hv0 : 0 ≤ ∑ p ∈ Finset.range (m + 1), M.localVariance φ p :=
    Finset.sum_nonneg fun p _ ↦ mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  have hlim : charFun ((gaussianReal 0
      (∑ p ∈ Finset.range (m + 1), M.localVariance φ p).toNNReal).map id) t =
      (Real.exp (-((∑ p ∈ Finset.range (m + 1), M.localVariance φ p) * t ^ 2 / 2)) : ℂ) := by
    rw [Measure.map_id, charFun_gaussianReal, ofReal_exp, Real.coe_toNNReal _ hv0]
    push_cast; ring_nf
  rw [hlim]
  have hcf : ∀ N, charFun (P.map fun ω ↦
      ∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ N q ω) p) t =
      ∫ ω, cexp (t * (∑ p ∈ Finset.range (m + 1), M.localError φ (fun q ↦ ξ N q ω) p : ℝ) * I)
        ∂P := fun N ↦ by
    rw [charFun_apply_real, integral_map (hS N).aemeasurable (by fun_prop)]
  simp_rw [hcf]
  exact tendsto_integral_cexp_sum_localError P M ξ hξ φ hφ hB t m

end CKSD
