module

public import CKSD.Bayes.ParticleFilter
public import CKSD.Asymptotics.Lindeberg.Basic

/-!
# Fluctuations of the bootstrap particle filter

Tools for the fixed-time central limit theorems of the bootstrap particle filter. Along a path
`x : ℕ → Fin N → X` of particle generations, the local error of generation `p` in the direction
of a bounded function `φ p` is the centred sum `∑ᵢ (φ p (x p i) - ηᴺ̃ₚ(φ p))`, where `ηᴺ̃ₚ` is the
prediction law from the previous generation (the initial law for `p = 0`). Weighted by the
particle likelihood and scaled by `N^{-1/2}`, the sum over `p ≤ m` of the local errors converges
in law to a centred normal law.

Given the past, the next generation consists of independent draws from the prediction law, so the
conditional characteristic function of a local error is the `N`-th power of a characteristic
function. Lindeberg's estimate `CKSD.norm_prod_charFun_sub_exp_le` compares it with a Gaussian
factor, and the mean-square bounds of `CKSD.exists_integral_sq_particle_average_sub_le` control
the random variances. The characteristic-function recursion and the Lévy continuity argument are
in `CKSD.Bayes.ParticleCentralLimit`.

## Main definitions

* `CKSD.FeynmanKacModel.pathPredMean`: prediction integrals along a path of generations.
* `CKSD.FeynmanKacModel.localError`: the weighted, scaled local error of a generation.
* `CKSD.FeynmanKacModel.localVariance`: its limiting variance.

## Main results

* `CKSD.integral_bootstrap_succ`: one conditional sampling step for bounded complex functions.
* `CKSD.tendsto_integral_abs_particleLikelihood_sub`: mean-absolute consistency of the particle
  likelihood estimates.
* `CKSD.tendsto_integral_norm_gaussianFactor_sub`: the random Gaussian factors converge in mean
  to the deterministic one.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- Conditional sampling step of the bootstrap filter for bounded complex functions: integrating
a function of the past and the next generation equals integrating it against the product
prediction law. -/
theorem integral_bootstrap_succ [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ)
    (H : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℂ) (hH : Measurable H) {C : ℝ}
    (hC : ∀ z, ‖H z‖ ≤ C) :
    ∫ ω, H ((fun i : Fin (n + 1) ↦ ξ i ω), ξ (n + 1) ω) ∂P =
      ∫ ω, ∫ z, H ((fun i : Fin (n + 1) ↦ ξ i ω), z)
        ∂Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω)) ∂P := by
  obtain ⟨hmeas, -, hcond⟩ := hξ
  set Y : Ω → Fin (n + 1) → Fin N → X := fun ω i ↦ ξ i ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  change ∫ ω, H (Y ω, ξ (n + 1) ω) ∂P = ∫ ω, ∫ z, H (Y ω, z) ∂_ ∂P
  have hint : Integrable H ((P.map Y) ⊗ₘ condDistrib (ξ (n + 1)) Y P) :=
    Integrable.of_bound hH.aestronglyMeasurable C (ae_of_all _ hC)
  rw [← integral_map (hY.prodMk (hmeas (n + 1))).aemeasurable hH.aestronglyMeasurable,
    ← compProd_map_condDistrib hY.aemeasurable (hmeas (n + 1)).aemeasurable,
    Measure.integral_compProd hint,
    integral_map hY.aemeasurable]
  · refine integral_congr_ae ?_
    filter_upwards [hcond n] with ω hω
    simp only [hYdef] at hω ⊢
    rw [hω]
  · exact hH.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable

/-- For `N` independent draws from `ν`, the characteristic function of `∑ⱼ g(zⱼ)` is the `N`-th
power of that of `g`: `∫ exp (i u ∑ⱼ g(zⱼ)) = (∫ exp (i u g) dν)^N`. -/
theorem integral_cexp_sum_pi (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) (g : X → ℝ)
    (u : ℝ) :
    ∫ z, cexp (u * (∑ j, g (z j) : ℝ) * I) ∂Measure.pi (fun _ : Fin N ↦ ν) =
      (∫ x, cexp (u * g x * I) ∂ν) ^ N := by
  have h : ∀ z : Fin N → X, cexp (u * (∑ j, g (z j) : ℝ) * I) =
      ∏ j, (fun (_ : Fin N) x ↦ cexp (u * g x * I)) j (z j) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [h]
  refine (integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (_ : Fin N) (x : X) ↦ cexp (u * g x * I))).trans ?_
  simp

/-- Lindeberg's estimate for `N` independent copies of a bounded variable: if `|g| ≤ B` and
`σ² = ∫ (g - ν g)² dν`, the `N`-th power of the characteristic function of `g - ν g` at `u`
differs from `exp (-N σ² u² / 2)` by at most `|u|³ (2B) N σ² / 3 + u⁴ N σ² (2B)² / 4`. -/
theorem norm_integral_cexp_pow_sub_exp_le (ν : Measure X) [IsProbabilityMeasure ν] {g : X → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (N : ℕ) (u : ℝ) :
    ‖(∫ x, cexp (u * (g x - ∫ y, g y ∂ν) * I) ∂ν) ^ N -
        (Real.exp (-(N * (∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν) * u ^ 2 / 2)) : ℂ)‖ ≤
      |u| ^ 3 * (2 * B) / 3 * (N * ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν) +
        u ^ 4 / 4 * (N * ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν) * (2 * B) ^ 2 := by
  set c := ∫ y, g y ∂ν
  set Y : X → ℝ := fun x ↦ g x - c with hYdef
  have hYm : Measurable Y := hg.sub measurable_const
  have hint : Integrable g ν :=
    Integrable.of_bound hg.aestronglyMeasurable B (ae_of_all _ fun x ↦ hB x)
  have hY2 : ∀ x, |Y x| ≤ 2 * B := by
    intro x
    have hc : |c| ≤ B := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ y, |g y| ∂ν ≤ ∫ _, B ∂ν :=
            integral_mono hint.abs (integrable_const _) fun y ↦ hB y
        _ = B := by simp
    calc |Y x| ≤ |g x| + |c| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x]
  have hmem : MemLp Y 2 ν := MemLp.of_bound hYm.aestronglyMeasurable (2 * B)
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hY2 x)
  have h0 : ∫ x, Y x ∂ν = 0 := by
    simp only [hYdef]
    rw [integral_sub hint (integrable_const _)]
    simp [c]
  have := nonempty_of_isProbabilityMeasure ν
  have hB0 : 0 ≤ 2 * B := (abs_nonneg _).trans (hY2 (Classical.arbitrary X))
  have hmain := norm_prod_charFun_sub_exp_le (μ := ν) (Finset.univ : Finset (Fin N))
    (fun _ ↦ Y) (fun _ _ ↦ hmem) (fun _ _ ↦ h0) hB0 u
  have hind : ∫ x, (if 2 * B < |Y x| then Y x ^ 2 else 0) ∂ν = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
    simp [not_lt.2 (hY2 x)]
  have hcf : charFun (ν.map Y) u = ∫ x, cexp (u * (g x - c) * I) ∂ν := by
    rw [charFun_apply_real, integral_map hYm.aemeasurable (by fun_prop)]
    simp [hYdef]
  simp only [hind, Finset.sum_const_zero, mul_zero, add_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, hcf] at hmain
  convert hmain using 3

namespace FeynmanKacModel

/-- Prediction integral of `g` for generation `p` along a path of generations: the initial law
for `p = 0` and the bootstrap prediction law from generation `p - 1` otherwise. -/
def pathPredMean (M : FeynmanKacModel X) {N : ℕ} (x : ℕ → Fin N → X) : ℕ → (X → ℝ) → ℝ
  | 0, g => ∫ y, g y ∂(M.initial : Measure X)
  | p + 1, g => ∫ y, g y ∂M.particlePredictionLaw p (x p)

/-- Local error of generation `p` in the direction `φ p`, weighted by the particle likelihood
and scaled by `N^{-1/2}`: `Lᴺₚ ∑ᵢ (φₚ(xₚⁱ) - ηᴺ̃ₚ(φₚ)) / √N`. -/
def localError (M : FeynmanKacModel X) {N : ℕ} (φ : ℕ → X → ℝ) (x : ℕ → Fin N → X)
    (p : ℕ) : ℝ :=
  M.particleLikelihood x p * (∑ i, (φ p (x p i) - M.pathPredMean x p (φ p))) / Real.sqrt N

/-- Limiting variance of the local error of generation `p`:
`γₚ(1)² ∫ (φₚ - ηₚ φₚ)² dηₚ`. -/
def localVariance (M : FeynmanKacModel X) (φ : ℕ → X → ℝ) (p : ℕ) : ℝ :=
  (M.unnormalizedLaw p).real univ ^ 2 *
    ∫ x, (φ p x - ∫ y, φ p y ∂M.filterLaw p) ^ 2 ∂M.filterLaw p

/-- The prediction integral of generation `p + 1` is an integral against the bootstrap
prediction law from generation `p`. -/
theorem pathPredMean_succ (M : FeynmanKacModel X) {N : ℕ} (x : ℕ → Fin N → X) (p : ℕ)
    (g : X → ℝ) : M.pathPredMean x (p + 1) g = ∫ y, g y ∂M.particlePredictionLaw p (x p) := rfl

/-- The particle likelihood up to generation `p` only depends on generations before `p`. -/
theorem particleLikelihood_congr (M : FeynmanKacModel X) {N : ℕ} {x x' : ℕ → Fin N → X}
    {p : ℕ} (h : ∀ q < p, x q = x' q) : M.particleLikelihood x p = M.particleLikelihood x' p :=
  Finset.prod_congr rfl fun q hq ↦ by rw [h q (Finset.mem_range.1 hq)]

/-- The prediction integral of generation `p` only depends on generations before `p`. -/
theorem pathPredMean_congr (M : FeynmanKacModel X) {N : ℕ} {x x' : ℕ → Fin N → X}
    {p : ℕ} (h : ∀ q < p, x q = x' q) (g : X → ℝ) :
    M.pathPredMean x p g = M.pathPredMean x' p g := by
  cases p with
  | zero => rfl
  | succ p => simp only [pathPredMean, h p (Nat.lt_succ_self p)]

/-- The local error of generation `p` only depends on generations up to `p`. -/
theorem localError_congr (M : FeynmanKacModel X) {N : ℕ} (φ : ℕ → X → ℝ)
    {x x' : ℕ → Fin N → X} {p : ℕ} (h : ∀ q ≤ p, x q = x' q) :
    M.localError φ x p = M.localError φ x' p := by
  simp only [localError, M.particleLikelihood_congr (fun q hq ↦ h q hq.le),
    M.pathPredMean_congr (fun q hq ↦ h q hq.le), h p le_rfl]

/-- Measurability of a transition integral of a measurable function. -/
theorem measurable_integral_transition (M : FeynmanKacModel X) (p : ℕ) {g : X → ℝ}
    (hg : Measurable g) : Measurable fun x ↦ ∫ y, g y ∂M.transition p x :=
  (hg.stronglyMeasurable.integral_kernel (κ := M.transition p)).measurable

/-- The prediction integral of a bounded measurable function is a measurable function of the
current generation. -/
theorem measurable_integral_particlePredictionLaw (M : FeynmanKacModel X) {N : ℕ} (p : ℕ)
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    Measurable fun x : Fin N → X ↦ ∫ y, g y ∂M.particlePredictionLaw p x := by
  simp_rw [M.integral_particlePredictionLaw p _ hg hC]
  exact (Finset.measurable_sum _ fun i _ ↦
    ((M.measurable_potential p).comp (measurable_pi_apply i)).mul
      ((M.measurable_integral_transition p hg).comp (measurable_pi_apply i))).div
    (Finset.measurable_sum _ fun i _ ↦ (M.measurable_potential p).comp (measurable_pi_apply i))

/-- The particle likelihood is a measurable function of the path. -/
theorem measurable_particleLikelihood (M : FeynmanKacModel X) {N : ℕ} (p : ℕ) :
    Measurable fun x : ℕ → Fin N → X ↦ M.particleLikelihood x p :=
  Finset.measurable_prod _ fun q _ ↦ (Finset.measurable_sum _ fun i _ ↦
    (M.measurable_potential q).comp ((measurable_pi_apply i).comp
      (measurable_pi_apply q))).div_const _

/-- The prediction integral of a bounded measurable function is a measurable function of the
path. -/
theorem measurable_pathPredMean (M : FeynmanKacModel X) {N : ℕ} (p : ℕ) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    Measurable fun x : ℕ → Fin N → X ↦ M.pathPredMean x p g := by
  cases p with
  | zero => exact measurable_const
  | succ p =>
    exact (M.measurable_integral_particlePredictionLaw p hg hC).comp (measurable_pi_apply p)

/-- The local error is a measurable function of the path. -/
theorem measurable_localError (M : FeynmanKacModel X) {N : ℕ} {φ : ℕ → X → ℝ}
    (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B) (p : ℕ) :
    Measurable fun x : ℕ → Fin N → X ↦ M.localError φ x p :=
  ((M.measurable_particleLikelihood p).mul (Finset.measurable_sum _ fun i _ ↦
    ((hφ p).comp ((measurable_pi_apply i).comp (measurable_pi_apply p))).sub
      (M.measurable_pathPredMean p (hφ p) (hB p)))).div_const _

end FeynmanKacModel

/-- For a bounded measurable `Y` on a probability space, `(∫ |Y|)² ≤ ∫ Y²`. -/
private theorem sq_integral_abs_le_integral_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    (∫ ω, |Y ω| ∂μ) ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂μ := by
  have hmem : MemLp (fun ω ↦ |Y ω|) 2 μ :=
    MemLp.of_bound (continuous_abs.measurable.comp hY).aestronglyMeasurable C
    (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω)
  have h := variance_nonneg (fun ω ↦ |Y ω|) μ
  rw [variance_eq_sub hmem] at h
  simp only [Pi.pow_apply, sq_abs] at h
  linarith

/-- `L¹` convergence of products: if `A N → a` and `B N → b` in `L¹`, with `|A N| ≤ KA`,
`|B N| ≤ KB` and `|b| ≤ Kb`, then `A N B N → a b` in `L¹`. -/
private theorem tendsto_integral_abs_mul_sub_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : ℕ → Ω → ℝ} {a b KA KB Kb : ℝ} (hAm : ∀ N, Measurable (A N))
    (hBm : ∀ N, Measurable (B N)) (hA : ∀ N ω, |A N ω| ≤ KA) (hB : ∀ N ω, |B N ω| ≤ KB)
    (hb : |b| ≤ Kb)
    (hAl : Tendsto (fun N ↦ ∫ ω, |A N ω - a| ∂μ) atTop (𝓝 0))
    (hBl : Tendsto (fun N ↦ ∫ ω, |B N ω - b| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ ω, |A N ω * B N ω - a * b| ∂μ) atTop (𝓝 0) := by
  have hint : ∀ (F : Ω → ℝ) (c K : ℝ), Measurable F → (∀ ω, |F ω| ≤ K) →
      Integrable (fun ω ↦ |F ω - c|) μ := fun F c K hF hK ↦
    Integrable.of_bound
      (continuous_abs.measurable.comp (hF.sub measurable_const)).aestronglyMeasurable
      (K + |c|)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hK ω]))
  have := nonempty_of_isProbabilityMeasure μ
  have hKA : 0 ≤ KA := (abs_nonneg _).trans (hA 0 (Classical.arbitrary Ω))
  have hKb : 0 ≤ Kb := (abs_nonneg _).trans hb
  have hlim := (hBl.const_mul KA).add (hAl.const_mul Kb)
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun N ↦ ?_)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) ?_
      (ae_of_all _ fun ω ↦ ?_)
    · exact ((hint _ b KB (hBm N) (hB N)).const_mul KA).add
        ((hint _ a KA (hAm N) (hA N)).const_mul Kb)
    · show |A N ω * B N ω - a * b| ≤ KA * |B N ω - b| + Kb * |A N ω - a|
      have e : A N ω * B N ω - a * b = A N ω * (B N ω - b) + b * (A N ω - a) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      gcongr
      · exact hA N ω
  · exact (hint _ b KB (hBm N) (hB N)).const_mul KA
  · exact (hint _ a KA (hAm N) (hA N)).const_mul Kb

/-- `L¹` convergence of quotients with denominators bounded below by `c > 0`. -/
private theorem tendsto_integral_abs_div_sub_div {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : ℕ → Ω → ℝ} {a b c KA KB : ℝ} (hAm : ∀ N, Measurable (A N))
    (hBm : ∀ N, Measurable (B N)) (hA : ∀ N ω, |A N ω| ≤ KA) (hB : ∀ N ω, |B N ω| ≤ KB)
    (hc : 0 < c) (hBc : ∀ N ω, c ≤ B N ω) (hbc : c ≤ b)
    (hAl : Tendsto (fun N ↦ ∫ ω, |A N ω - a| ∂μ) atTop (𝓝 0))
    (hBl : Tendsto (fun N ↦ ∫ ω, |B N ω - b| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ ω, |A N ω / B N ω - a / b| ∂μ) atTop (𝓝 0) := by
  have hint : ∀ (F : Ω → ℝ) (d K : ℝ), Measurable F → (∀ ω, |F ω| ≤ K) →
      Integrable (fun ω ↦ |F ω - d|) μ := fun F d K hF hK ↦
    Integrable.of_bound
      (continuous_abs.measurable.comp (hF.sub measurable_const)).aestronglyMeasurable
      (K + |d|) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hK ω]))
  have hb0 : 0 < b := hc.trans_le hbc
  have hlim := (hAl.const_mul (1 / c)).add (hBl.const_mul (|a| / c ^ 2))
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun N ↦ ?_)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) ?_
      (ae_of_all _ fun ω ↦ ?_)
    · exact ((hint _ a KA (hAm N) (hA N)).const_mul _).add
        ((hint _ b KB (hBm N) (hB N)).const_mul _)
    · show |A N ω / B N ω - a / b| ≤ 1 / c * |A N ω - a| + |a| / c ^ 2 * |B N ω - b|
      have hB0 : 0 < B N ω := hc.trans_le (hBc N ω)
      have e : A N ω / B N ω - a / b =
          (A N ω - a) / B N ω + a * (b - B N ω) / (B N ω * b) := by
        field_simp; ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos hB0, div_eq_mul_inv, mul_comm, one_div]
        gcongr
        exact hBc N ω
      · rw [abs_div, abs_mul, abs_of_pos (mul_pos hB0 hb0), abs_sub_comm b, mul_div_assoc,
          div_eq_mul_inv]
        have hcc : c ^ 2 ≤ B N ω * b := by nlinarith [hBc N ω]
        have hinv : (B N ω * b)⁻¹ ≤ (c ^ 2)⁻¹ := inv_anti₀ (by positivity) hcc
        calc |a| * (|B N ω - b| * (B N ω * b)⁻¹) ≤ |a| * (|B N ω - b| * (c ^ 2)⁻¹) := by
              gcongr
          _ = |a| / c ^ 2 * |B N ω - b| := by ring
  · exact (hint _ a KA (hAm N) (hA N)).const_mul _
  · exact (hint _ b KB (hBm N) (hB N)).const_mul _

/-- An average of numbers bounded by `C` in absolute value is bounded by `C`. -/
private theorem abs_sum_div_le {N : ℕ} {f : Fin (N + 1) → ℝ} {C : ℝ} (hf : ∀ i, |f i| ≤ C) :
    |(∑ i, f i) / (N + 1)| ≤ C := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f i| ≤ ∑ _i : Fin (N + 1), C := Finset.sum_le_sum fun i _ ↦ hf i
    _ = C * (N + 1) := by simp [mul_comm]

/-- An average of numbers at least `a` is at least `a`. -/
private theorem le_sum_div {N : ℕ} {f : Fin (N + 1) → ℝ} {a : ℝ} (hf : ∀ i, a ≤ f i) :
    a ≤ (∑ i, f i) / (N + 1) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [le_div_iff₀ hN]
  calc a * (N + 1) = ∑ _i : Fin (N + 1), a := by simp [mul_comm]
    _ ≤ ∑ i, f i := Finset.sum_le_sum fun i _ ↦ hf i

/-- The integral of a function bounded by `C` against a probability measure is bounded by `C`. -/
theorem abs_integral_le_of_abs_le {ν : Measure X} [IsProbabilityMeasure ν] {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂ν| ≤ C := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |g y| ∂ν ≤ ∫ _, C ∂ν :=
        integral_mono (Integrable.of_bound hg.aestronglyMeasurable C
          (ae_of_all _ fun x ↦ hC x)).abs (integrable_const _) fun y ↦ hC y
    _ = C := by simp

/-- Mean-absolute consistency of the bootstrap particle averages at a fixed time. -/
theorem tendsto_integral_abs_particle_average_sub [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (p : ℕ) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun N : ℕ ↦ ∫ ω, |(∑ i, g (ξ N p ω i)) / (N + 1) - ∫ x, g x ∂M.filterLaw p| ∂P)
      atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_sq_particle_average_sub_le P M ξ hξ p
  have hlim : Tendsto (fun N : ℕ ↦ Real.sqrt (K * C ^ 2 * (1 / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (K * C ^ 2)).sqrt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun N ↦ ?_)
  have hYm : Measurable fun ω ↦ (∑ i, g (ξ N p ω i)) / (N + 1) - ∫ x, g x ∂M.filterLaw p :=
    ((Finset.measurable_sum _ fun i _ ↦
      hg.comp ((measurable_pi_apply i).comp ((hξ N).1 p))).div_const _).sub measurable_const
  have hYb : ∀ ω, |(∑ i, g (ξ N p ω i)) / (N + 1) - ∫ x, g x ∂M.filterLaw p| ≤ C + C :=
    fun ω ↦ (abs_sub _ _).trans (add_le_add (abs_sum_div_le fun i ↦ hC _)
      (abs_integral_le_of_abs_le hg hC))
  have h1 := sq_integral_abs_le_integral_sq (μ := P) hYm hYb
  have h2 := hK g hg C hC N
  rw [← Real.sqrt_sq (integral_nonneg fun _ ↦ abs_nonneg _)]
  refine Real.sqrt_le_sqrt (h1.trans (h2.trans_eq ?_))
  ring

/-- Total mass recursion `γₚ₊₁(1) = γₚ(1) ηₚ(Gₚ)` in real form. -/
theorem FeynmanKacModel.unnormalizedLaw_real_univ_succ (M : FeynmanKacModel X) (p : ℕ) :
    (M.unnormalizedLaw (p + 1)).real univ =
      (M.unnormalizedLaw p).real univ * ∫ x, M.potential p x ∂M.filterLaw p := by
  have := M.isMarkov_transition p
  obtain ⟨a, b, ha, hab⟩ := M.potential_bounds p
  have h1 : (M.unnormalizedLaw (p + 1)).real univ = ∫ x, M.potential p x ∂M.unnormalizedLaw p := by
    have := M.integral_unnormalizedLaw_succ p (f := fun _ ↦ (1 : ℝ)) measurable_const
      (C := 1) (fun _ ↦ by simp)
    simpa using this
  have hc : (M.unnormalizedLaw p).real univ ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨M.unnormalizedLaw_univ_ne_zero p, measure_ne_top _ _⟩
  rw [h1, M.integral_filterLaw, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Mean-absolute consistency of the particle likelihood estimates, with a uniform bound. -/
theorem tendsto_integral_abs_particleLikelihood_sub [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N)) (p : ℕ) :
    (∃ K, ∀ N ω, |M.particleLikelihood (fun q ↦ ξ N q ω) p| ≤ K) ∧
      Tendsto (fun N ↦ ∫ ω, |M.particleLikelihood (fun q ↦ ξ N q ω) p -
        (M.unnormalizedLaw p).real univ| ∂P) atTop (𝓝 0) := by
  have hpath : ∀ N, Measurable fun ω (q : ℕ) ↦ ξ N q ω := fun N ↦
    measurable_pi_iff.2 fun q ↦ (hξ N).1 q
  induction p with
  | zero =>
    refine ⟨⟨1, fun N ω ↦ by simp [FeynmanKacModel.particleLikelihood]⟩, ?_⟩
    simp [FeynmanKacModel.particleLikelihood, FeynmanKacModel.unnormalizedLaw]
  | succ p ih =>
    obtain ⟨⟨K, hK⟩, hl⟩ := ih
    obtain ⟨a, b, ha, hab⟩ := M.potential_bounds p
    have hGb : ∀ x, |M.potential p x| ≤ b := fun x ↦ by
      rw [abs_of_pos (ha.trans_le (hab x).1)]; exact (hab x).2
    have hsucc : ∀ N ω, M.particleLikelihood (fun q ↦ ξ N q ω) (p + 1) =
        M.particleLikelihood (fun q ↦ ξ N q ω) p *
          ((∑ i, M.potential p (ξ N p ω i)) / (N + 1)) := by
      intro N ω
      simp only [FeynmanKacModel.particleLikelihood, Finset.prod_range_succ]
      push_cast; rfl
    refine ⟨⟨K * b, fun N ω ↦ ?_⟩, ?_⟩
    · rw [hsucc, abs_mul]
      exact mul_le_mul (hK N ω) (abs_sum_div_le fun i ↦ hGb _) (abs_nonneg _)
        ((abs_nonneg _).trans (hK N ω))
    · simp_rw [hsucc, M.unnormalizedLaw_real_univ_succ]
      exact tendsto_integral_abs_mul_sub_mul
        (fun N ↦ (M.measurable_particleLikelihood p).comp (hpath N))
        (fun N ↦ (Finset.measurable_sum _ fun i _ ↦ (M.measurable_potential p).comp
          ((measurable_pi_apply i).comp ((hξ N).1 p))).div_const _)
        hK (fun N ω ↦ abs_sum_div_le fun i ↦ hGb _)
        (abs_integral_le_of_abs_le (M.measurable_potential p) hGb) hl
        (tendsto_integral_abs_particle_average_sub P M ξ hξ p (M.measurable_potential p) hGb)

/-- Mean-absolute consistency of the prediction integrals along the particle path. -/
theorem tendsto_integral_abs_pathPredMean_sub [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (p : ℕ) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun N ↦ ∫ ω, |M.pathPredMean (fun q ↦ ξ N q ω) p g -
      ∫ x, g x ∂M.filterLaw p| ∂P) atTop (𝓝 0) := by
  cases p with
  | zero =>
    have h0 : ∫ x, g x ∂M.filterLaw 0 = ∫ x, g x ∂(M.initial : Measure X) := by
      rw [M.integral_filterLaw, FeynmanKacModel.unnormalizedLaw_zero]; simp
    simp [FeynmanKacModel.pathPredMean, h0]
  | succ p =>
    have := M.isMarkov_transition p
    obtain ⟨a, b, ha, hab⟩ := M.potential_bounds p
    have hGb : ∀ x, |M.potential p x| ≤ b := fun x ↦ by
      rw [abs_of_pos (ha.trans_le (hab x).1)]; exact (hab x).2
    set h : X → ℝ := fun x ↦ M.potential p x * ∫ y, g y ∂M.transition p x with hh
    have hhm : Measurable h :=
      (M.measurable_potential p).mul (M.measurable_integral_transition p hg)
    have hhb : ∀ x, |h x| ≤ b * C := fun x ↦ by
      rw [hh, abs_mul]
      exact mul_le_mul (hGb x) (abs_integral_le_of_abs_le hg hC) (abs_nonneg _)
        ((abs_nonneg _).trans (hGb x))
    have hpred : ∀ N ω, M.pathPredMean (fun q ↦ ξ N q ω) (p + 1) g =
        ((∑ i, h (ξ N p ω i)) / (N + 1)) / ((∑ i, M.potential p (ξ N p ω i)) / (N + 1)) := by
      intro N ω
      simp only [FeynmanKacModel.pathPredMean]
      rw [M.integral_particlePredictionLaw p _ hg hC, div_div_div_cancel_right₀ (by positivity)]
    have hlim : ∫ x, g x ∂M.filterLaw (p + 1) =
        (∫ x, h x ∂M.filterLaw p) / ∫ x, M.potential p x ∂M.filterLaw p :=
      M.integral_filterLaw_succ p hg hC
    simp_rw [hpred, hlim]
    have hGa : a ≤ ∫ x, M.potential p x ∂M.filterLaw p := by
      calc a = ∫ _, a ∂M.filterLaw p := by simp
        _ ≤ _ := integral_mono (integrable_const _)
            (Integrable.of_bound (M.measurable_potential p).aestronglyMeasurable b
              (ae_of_all _ fun x ↦ hGb x)) fun x ↦ (hab x).1
    exact tendsto_integral_abs_div_sub_div
      (fun N ↦ (Finset.measurable_sum _ fun i _ ↦
        hhm.comp ((measurable_pi_apply i).comp ((hξ N).1 p))).div_const _)
      (fun N ↦ (Finset.measurable_sum _ fun i _ ↦ (M.measurable_potential p).comp
        ((measurable_pi_apply i).comp ((hξ N).1 p))).div_const _)
      (fun N ω ↦ abs_sum_div_le fun i ↦ hhb _) (fun N ω ↦ abs_sum_div_le fun i ↦ hGb _)
      ha (fun N ω ↦ le_sum_div fun i ↦ (hab _).1) hGa
      (tendsto_integral_abs_particle_average_sub P M ξ hξ p hhm hhb)
      (tendsto_integral_abs_particle_average_sub P M ξ hξ p (M.measurable_potential p) hGb)

/-- The conditional integral of a bounded measurable function of the past and the next generation
against the product prediction law is an almost everywhere strongly measurable function. -/
theorem aestronglyMeasurable_integral_bootstrap_succ [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ)
    (H : (Fin (n + 1) → Fin N → X) × (Fin N → X) → ℂ) (hH : Measurable H) :
    AEStronglyMeasurable (fun ω ↦ ∫ z, H ((fun i : Fin (n + 1) ↦ ξ i ω), z)
        ∂Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω))) P := by
  obtain ⟨hmeas, -, hcond⟩ := hξ
  set Y : Ω → Fin (n + 1) → Fin N → X := fun ω i ↦ ξ i ω with hYdef
  have hY : Measurable Y := measurable_pi_iff.2 fun i ↦ hmeas i
  refine ((hH.stronglyMeasurable.integral_kernel_prod_right'
    (κ := condDistrib (ξ (n + 1)) Y P)).comp_measurable hY).aestronglyMeasurable.congr ?_
  filter_upwards [hcond n] with ω hω
  simp only [Function.comp_apply, hYdef] at hω ⊢
  rw [hω]

/-- Uniform Gaussian approximation of the characteristic function of a normalized sum of `N + 1`
independent copies of a bounded variable: with `|g| ≤ B`, `σ² = ∫ (g - ν g)² dν` and
`|s| ≤ S`, the error is at most `S³ (2B)(2B)² / (3 √(N+1)) + S⁴ (2B)⁴ / (4 (N+1))`. -/
theorem norm_integral_cexp_pow_sub_gaussian_le (ν : Measure X) [IsProbabilityMeasure ν]
    {g : X → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (N : ℕ) {s S : ℝ}
    (hs : |s| ≤ S) :
    ‖(∫ x, cexp ((s / Real.sqrt (N + 1) : ℝ) * (g x - ∫ y, g y ∂ν) * I) ∂ν) ^ (N + 1) -
        (Real.exp (-(s ^ 2 * (∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν) / 2)) : ℂ)‖ ≤
      S ^ 3 * (2 * B) / 3 * (2 * B) ^ 2 / Real.sqrt (N + 1) +
        S ^ 4 / 4 * (2 * B) ^ 2 * (2 * B) ^ 2 / (N + 1) := by
  have := nonempty_of_isProbabilityMeasure ν
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  set σ2 := ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν
  have hint : Integrable g ν :=
    Integrable.of_bound hg.aestronglyMeasurable B (ae_of_all _ fun x ↦ hB x)
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hσB : σ2 ≤ (2 * B) ^ 2 := by
    have hc := abs_integral_le_of_abs_le hg hB (ν := ν)
    calc σ2 ≤ ∫ _, (2 * B) ^ 2 ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun x ↦ ?_)
          have : |g x - ∫ y, g y ∂ν| ≤ 2 * B := (abs_sub _ _).trans (by linarith [hB x])
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (2 * B) ^ 2 := by simp
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hsq : Real.sqrt (N + 1) ^ 2 = N + 1 := Real.sq_sqrt hN.le
  have hsqpos : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.2 hN
  have h := norm_integral_cexp_pow_sub_exp_le ν hg hB (N + 1) (s / Real.sqrt (N + 1))
  have hexp : ((N + 1 : ℕ) : ℝ) * σ2 * (s / Real.sqrt (N + 1)) ^ 2 = s ^ 2 * σ2 := by
    rw [div_pow, hsq]; push_cast; field_simp
  rw [hexp] at h
  have hS : 0 ≤ S := (abs_nonneg _).trans hs
  refine h.trans ?_
  push_cast
  have h3 : |s / Real.sqrt (N + 1)| ^ 3 * ((N + 1) * σ2) ≤
      S ^ 3 * (2 * B) ^ 2 / Real.sqrt (N + 1) := by
    rw [abs_div, abs_of_pos hsqpos, div_pow]
    have : Real.sqrt (N + 1) ^ 3 = (N + 1) * Real.sqrt (N + 1) := by
      rw [pow_succ, hsq]
    rw [this]
    have hs3 : |s| ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hs 3
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hsqpos]
    have : |s| ^ 3 * ((N + 1) * σ2) * Real.sqrt (N + 1) ≤
        S ^ 3 * (2 * B) ^ 2 * ((N + 1) * Real.sqrt (N + 1)) := by
      have h1 := mul_le_mul hs3 hσB hσ0 (by positivity)
      have k : 0 ≤ ((N : ℝ) + 1) * Real.sqrt (N + 1) := by positivity
      have h2 := mul_le_mul_of_nonneg_right h1 k
      calc |s| ^ 3 * ((N + 1) * σ2) * Real.sqrt (N + 1)
          = |s| ^ 3 * σ2 * ((N + 1) * Real.sqrt (N + 1)) := by ring
        _ ≤ _ := h2
    linarith
  have h4 : (s / Real.sqrt (N + 1)) ^ 4 * ((N + 1) * σ2) ≤ S ^ 4 * (2 * B) ^ 2 / (N + 1) := by
    have : (s / Real.sqrt (N + 1)) ^ 4 = s ^ 4 / (N + 1) ^ 2 := by
      rw [div_pow, show Real.sqrt (N + 1) ^ 4 = (N + 1) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]]
    rw [this, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hN]
    have hs4 : s ^ 4 ≤ S ^ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg s) hs 4
      rwa [show |s| ^ 4 = s ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs,
        ← pow_mul]] at this
    have := mul_le_mul hs4 hσB hσ0 (by positivity)
    nlinarith
  have e1 : |s / Real.sqrt (N + 1)| ^ 3 * (2 * B) / 3 * ((N + 1) * σ2) =
      (2 * B) / 3 * (|s / Real.sqrt (N + 1)| ^ 3 * ((N + 1) * σ2)) := by ring
  have e2 : (s / Real.sqrt (N + 1)) ^ 4 / 4 * ((N + 1) * σ2) * (2 * B) ^ 2 =
      (2 * B) ^ 2 / 4 * ((s / Real.sqrt (N + 1)) ^ 4 * ((N + 1) * σ2)) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * B / 3)
  have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (2 * B) ^ 2 / 4)
  have ee1 : 2 * B / 3 * (S ^ 3 * (2 * B) ^ 2 / Real.sqrt (N + 1)) =
      S ^ 3 * (2 * B) / 3 * (2 * B) ^ 2 / Real.sqrt (N + 1) := by ring
  have ee2 : (2 * B) ^ 2 / 4 * (S ^ 4 * (2 * B) ^ 2 / (N + 1)) =
      S ^ 4 / 4 * (2 * B) ^ 2 * (2 * B) ^ 2 / (N + 1) := by ring
  linarith

/-- Variance identity `∫ (g - ν g)² dν = ν(g²) - (ν g)²` for bounded measurable `g`. -/
theorem integral_sub_integral_sq {ν : Measure X} [IsProbabilityMeasure ν] {g : X → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν = ∫ x, g x ^ 2 ∂ν - (∫ y, g y ∂ν) ^ 2 := by
  have hmem : MemLp g 2 ν := MemLp.of_bound hg.aestronglyMeasurable B
    (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hB x)
  rw [← variance_eq_integral hg.aemeasurable, variance_eq_sub hmem]
  rfl

/-- `L¹` convergence of differences of bounded sequences. -/
private theorem tendsto_integral_abs_sub_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : ℕ → Ω → ℝ} {a b KA KB : ℝ} (hAm : ∀ N, Measurable (A N))
    (hBm : ∀ N, Measurable (B N)) (hA : ∀ N ω, |A N ω| ≤ KA) (hB : ∀ N ω, |B N ω| ≤ KB)
    (hAl : Tendsto (fun N ↦ ∫ ω, |A N ω - a| ∂μ) atTop (𝓝 0))
    (hBl : Tendsto (fun N ↦ ∫ ω, |B N ω - b| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ ω, |(A N ω - B N ω) - (a - b)| ∂μ) atTop (𝓝 0) := by
  have hint : ∀ (F : Ω → ℝ) (d K : ℝ), Measurable F → (∀ ω, |F ω| ≤ K) →
      Integrable (fun ω ↦ |F ω - d|) μ := fun F d K hF hK ↦
    Integrable.of_bound
      (continuous_abs.measurable.comp (hF.sub measurable_const)).aestronglyMeasurable
      (K + |d|) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hK ω]))
  have hlim := hAl.add hBl
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun N ↦ ?_)
  rw [← integral_add (hint _ a KA (hAm N) (hA N)) (hint _ b KB (hBm N) (hB N))]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
    ((hint _ a KA (hAm N) (hA N)).add (hint _ b KB (hBm N) (hB N))) (ae_of_all _ fun ω ↦ ?_)
  show |(A N ω - B N ω) - (a - b)| ≤ |A N ω - a| + |B N ω - b|
  rw [show (A N ω - B N ω) - (a - b) = (A N ω - a) - (B N ω - b) by ring]
  exact abs_sub _ _

/-- For `a, b ≥ 0`, `|exp (-a) - exp (-b)| ≤ |a - b|`. -/
private theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h4 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  rw [h2]
  nlinarith

/-- `L¹` convergence of the random Gaussian factors of the conditional characteristic functions:
`exp (-(t Lᴺₚ₊₁)² σ²ᴺ / 2) → exp (-vₚ₊₁ t² / 2)`, where `σ²ᴺ` is the variance of `φₚ₊₁` under the
prediction law and `vₚ₊₁` the limiting local variance. -/
theorem tendsto_integral_norm_gaussianFactor_sub [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (φ : ℕ → X → ℝ) (hφ : ∀ p, Measurable (φ p)) {B : ℝ} (hB : ∀ p x, |φ p x| ≤ B)
    (t : ℝ) (p : ℕ) :
    Tendsto (fun N ↦ ∫ ω, ‖(Real.exp (-((t * M.particleLikelihood (fun q ↦ ξ N q ω) (p + 1)) ^ 2 *
        (∫ x, (φ (p + 1) x - ∫ y, φ (p + 1) y ∂M.particlePredictionLaw p (ξ N p ω)) ^ 2
          ∂M.particlePredictionLaw p (ξ N p ω)) / 2)) : ℂ) -
        (Real.exp (-(M.localVariance φ (p + 1) * t ^ 2 / 2)) : ℂ)‖ ∂P) atTop (𝓝 0) := by
  have hpath : ∀ N, Measurable fun ω (q : ℕ) ↦ ξ N q ω := fun N ↦
    measurable_pi_iff.2 fun q ↦ (hξ N).1 q
  have hpred : ∀ N ω, IsProbabilityMeasure (M.particlePredictionLaw p (ξ N p ω)) := fun N ω ↦
    M.isProbabilityMeasure_particlePredictionLaw (Nat.succ_pos N) p _
  have hφ2m : Measurable fun x ↦ φ (p + 1) x ^ 2 := (hφ (p + 1)).pow_const 2
  have hφ2b : ∀ x, |φ (p + 1) x ^ 2| ≤ B ^ 2 := fun x ↦ by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _ x) 2
  obtain ⟨⟨K, hK⟩, hΓ⟩ := tendsto_integral_abs_particleLikelihood_sub P M ξ hξ (p + 1)
  obtain ⟨Γ, hΓd⟩ : ∃ Γ : ℝ, Γ = (M.unnormalizedLaw (p + 1)).real univ := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : ℕ → Ω → ℝ,
      L = fun N ω ↦ M.particleLikelihood (fun q ↦ ξ N q ω) (p + 1) := ⟨_, rfl⟩
  obtain ⟨m1, hm1d⟩ : ∃ m1 : ℕ → Ω → ℝ,
      m1 = fun N ω ↦ ∫ y, φ (p + 1) y ∂M.particlePredictionLaw p (ξ N p ω) := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m2 : ℕ → Ω → ℝ,
      m2 = fun N ω ↦ ∫ y, φ (p + 1) y ^ 2 ∂M.particlePredictionLaw p (ξ N p ω) := ⟨_, rfl⟩
  obtain ⟨e1, he1d⟩ : ∃ e1 : ℝ, e1 = ∫ x, φ (p + 1) x ∂M.filterLaw (p + 1) := ⟨_, rfl⟩
  obtain ⟨e2, he2d⟩ : ∃ e2 : ℝ, e2 = ∫ x, φ (p + 1) x ^ 2 ∂M.filterLaw (p + 1) := ⟨_, rfl⟩
  have hLm : ∀ N, Measurable (L N) := fun N ↦ by
    rw [hLd]; exact (M.measurable_particleLikelihood _).comp (hpath N)
  have hm1m : ∀ N, Measurable (m1 N) := fun N ↦ by
    rw [hm1d]; exact (M.measurable_integral_particlePredictionLaw p (hφ _) (hB _)).comp ((hξ N).1 p)
  have hm2m : ∀ N, Measurable (m2 N) := fun N ↦ by
    rw [hm2d]; exact (M.measurable_integral_particlePredictionLaw p hφ2m hφ2b).comp ((hξ N).1 p)
  have hm1b : ∀ N ω, |m1 N ω| ≤ B := fun N ω ↦ by
    have := hpred N ω
    rw [hm1d]; exact abs_integral_le_of_abs_le (hφ _) (hB _)
  have hm2b : ∀ N ω, |m2 N ω| ≤ B ^ 2 := fun N ω ↦ by
    have := hpred N ω
    rw [hm2d]; exact abs_integral_le_of_abs_le hφ2m hφ2b
  have hl1 : Tendsto (fun N ↦ ∫ ω, |m1 N ω - e1| ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_abs_pathPredMean_sub P M ξ hξ (p + 1) (hφ (p + 1)) (hB _)
    simp only [FeynmanKacModel.pathPredMean_succ] at this
    rw [hm1d, he1d]; exact this
  have hl2 : Tendsto (fun N ↦ ∫ ω, |m2 N ω - e2| ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_abs_pathPredMean_sub P M ξ hξ (p + 1) hφ2m hφ2b
    simp only [FeynmanKacModel.pathPredMean_succ] at this
    rw [hm2d, he2d]; exact this
  have hK' : ∀ N ω, |L N ω| ≤ K := fun N ω ↦ by rw [hLd]; exact hK N ω
  have hΓ' : Tendsto (fun N ↦ ∫ ω, |L N ω - Γ| ∂P) atTop (𝓝 0) := by
    rw [hLd, hΓd]; exact hΓ
  have he1b : |e1| ≤ B := by
    rw [he1d]; exact abs_integral_le_of_abs_le (hφ _) (hB _)
  -- the variance part
  have hLL := tendsto_integral_abs_mul_sub_mul (μ := P) hLm hLm hK' hK' le_rfl hΓ' hΓ'
  have h11 := tendsto_integral_abs_mul_sub_mul (μ := P) hm1m hm1m hm1b hm1b he1b hl1 hl1
  have hm11b : ∀ N ω, |m1 N ω * m1 N ω| ≤ B * B := fun N ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hm1b N ω) (hm1b N ω) (abs_nonneg _) ((abs_nonneg _).trans (hm1b N ω))
  have hLLb : ∀ N ω, |L N ω * L N ω| ≤ K * K := fun N ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hK' N ω) (hK' N ω) (abs_nonneg _) ((abs_nonneg _).trans (hK' N ω))
  have hVb : ∀ N ω, |m2 N ω - m1 N ω * m1 N ω| ≤ B ^ 2 + B * B := fun N ω ↦
    (abs_sub _ _).trans (add_le_add (hm2b N ω) (hm11b N ω))
  have hV := tendsto_integral_abs_sub_sub (μ := P) hm2m (fun N ↦ (hm1m N).mul (hm1m N)) hm2b
    hm11b hl2 h11
  have hLV := tendsto_integral_abs_mul_sub_mul (μ := P)
    (fun N ↦ (hLm N).mul (hLm N)) (fun N ↦ (hm2m N).sub ((hm1m N).mul (hm1m N)))
    (Kb := |e2 - e1 * e1|) hLLb hVb le_rfl hLL hV
  have hlim := hLV.const_mul (t ^ 2 / 2)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun N ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) ?_ (ae_of_all _ fun ω ↦ ?_)
  · refine Integrable.const_mul (Integrable.of_bound
      (C := K * K * (B ^ 2 + B * B) + |Γ * Γ * (e2 - e1 * e1)|)
      (continuous_abs.measurable.comp ((((hLm N).mul (hLm N)).mul
        ((hm2m N).sub ((hm1m N).mul (hm1m N)))).sub measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)) _
    rw [Real.norm_eq_abs]
    change |(|L N ω * L N ω * (m2 N ω - m1 N ω * m1 N ω) - Γ * Γ * (e2 - e1 * e1)|)| ≤ _
    rw [abs_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul]
    exact mul_le_mul (hLLb N ω) (hVb N ω) (abs_nonneg _)
      (mul_nonneg ((abs_nonneg _).trans (hK' N ω)) ((abs_nonneg _).trans (hK' N ω)))
  · have := hpred N ω
    subst hΓd hLd hm1d hm2d he1d he2d
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    have hv1 := integral_sub_integral_sq (ν := M.particlePredictionLaw p (ξ N p ω))
      (hφ (p + 1)) (hB _)
    have hv2 := integral_sub_integral_sq (ν := M.filterLaw (p + 1)) (hφ (p + 1)) (hB _)
    have hσ0 : 0 ≤ ∫ x, (φ (p + 1) x - ∫ y, φ (p + 1) y ∂M.particlePredictionLaw p (ξ N p ω)) ^ 2
        ∂M.particlePredictionLaw p (ξ N p ω) := integral_nonneg fun _ ↦ sq_nonneg _
    have hv0 : 0 ≤ M.localVariance φ (p + 1) :=
      mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_exp_neg_sub_exp_neg_le (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [hv1, FeynmanKacModel.localVariance, hv2]
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 / 2), ← abs_mul]
    congr 1
    ring

end CKSD
