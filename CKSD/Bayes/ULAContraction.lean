module
public import CKSD.Bayes.Diffusion
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
public import Mathlib.Analysis.SpecialFunctions.Exp
/-!
# Contractivity of ULA under synchronous Gaussian noise

Strong monotonicity and Lipschitz continuity give a deterministic Euler contraction for
`h L^2 <= alpha`. Factoring ULA as the Euler pushforward followed by common Gaussian
convolution transfers this bound to Wasserstein distance, including infinite-distance laws.

The deterministic estimate is the gradient-descent part of the coupling method of Chewi,
Log-Concave Sampling, August 20, 2026, Section 4.1. Mathlib supplies norm and exponential
calculus; pinned TauCeti supplies Lipschitz pushforwards and common-random-map transport.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CKSD

/-- One deterministic Euler step for the negative gradient drift. -/
def gradientEulerStep {E : Type*} [AddCommGroup E] [Module ℝ E] (G : E → E) (h : ℝ) (x : E) : E :=
  x - h • G x

/-- Strong monotonicity cannot exceed the Lipschitz constant on a nontrivial space. -/
theorem monotonicity_le_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] {G : E → E} {α β : ℝ}
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖)
    (hmono : ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y)) : α ≤ β := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hp := hmono x y
  have hi := real_inner_le_norm (G x - G y) (x - y)
  have hl := mul_le_mul_of_nonneg_right (hG x y) hn.le
  exact le_of_mul_le_mul_right (by nlinarith : α * ‖x-y‖^2 ≤ β * ‖x-y‖^2) (by positivity)

/-- A small Euler step is contractive with the exponential factor used by ULA. -/
theorem norm_gradientEulerStep_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : E → E} {L : ℝ≥0} (hG : LipschitzWith L G) {α h : ℝ}
    (hmono : ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (hh : 0 ≤ h) (hstep : h * (L : ℝ) ^ 2 ≤ α) (x y : E) :
    ‖gradientEulerStep G h x - gradientEulerStep G h y‖ ≤
      Real.exp (-α * h / 2) * ‖x - y‖ := by
  let u := x-y
  let g := G x-G y
  have hP : α * ‖u‖ ^ 2 ≤ ⟪g, u⟫ := hmono x y
  rw [real_inner_comm] at hP
  have hLip : ‖g‖ ≤ (L : ℝ) * ‖u‖ := hG.norm_sub_le x y
  have hLip2 : ‖g‖ ^ 2 ≤ (L : ℝ)^2 * ‖u‖^2 := by
    have := pow_le_pow_left₀ (norm_nonneg g) hLip 2
    simpa only [mul_pow] using this
  have hid : gradientEulerStep G h x - gradientEulerStep G h y = u - h • g := by
    dsimp [gradientEulerStep, u, g]
    module
  have hsquare : ‖u - h • g‖ ^ 2 ≤ (1-α*h) * ‖u‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 2*h)
    have h2 := mul_le_mul_of_nonneg_left hLip2 (sq_nonneg h)
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hh) (sq_nonneg ‖u‖)
    nlinarith
  have he : 1-α*h ≤ Real.exp (-α*h) := by simpa only [neg_mul, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-α*h)
  have hexp : (Real.exp (-α*h/2)) ^ 2 = Real.exp (-α*h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hid]
  have hm := hsquare.trans (mul_le_mul_of_nonneg_right he (sq_nonneg ‖u‖))
  have hR : 0 ≤ Real.exp (-α*h/2)*‖u‖ := by positivity
  have hsq : (Real.exp (-α*h/2)*‖u‖)^2 = Real.exp (-α*h)*‖u‖^2 := by rw [mul_pow, hexp]
  nlinarith [norm_nonneg (u-h•g)]

/-- The deterministic part of ULA has a global contraction factor. -/
theorem lipschitzWith_gradientEulerStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : E → E} {L : ℝ≥0} (hG : LipschitzWith L G) {α h : ℝ}
    (hmono : ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (hh : 0 ≤ h) (hstep : h * (L : ℝ) ^ 2 ≤ α) :
    LipschitzWith (Real.toNNReal (Real.exp (-α*h/2))) (gradientEulerStep G h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le] using
    norm_gradientEulerStep_sub_le hG hmono hh hstep x y

/-- ULA is a deterministic Euler pushforward followed by a common Gaussian convolution. -/
theorem langevinStepLaw_eq_gaussian_pushforward {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (hG : Measurable G) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    langevinStepLaw G h μ =
      ((μ.map (gradientEulerStep G h)).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun z ↦ z.1 + Real.sqrt (2*h) • z.2) := by
  have hm : Measurable (gradientEulerStep G h) := by
    change Measurable (fun x ↦ x - h • G x)
    fun_prop
  have hp := Measure.map_prod_map μ (stdGaussian (EuclideanSpace ℝ (Fin d))) hm measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (hm.prodMap measurable_id)]
  rfl

/-- Common Gaussian noise preserves the deterministic Euler contraction in Wasserstein distance. -/
theorem wassersteinEDist_langevinStepLaw_le {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {L : ℝ≥0}
    (hG : LipschitzWith L G) {α h : ℝ}
    (hmono : ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y))
    (hh : 0 ≤ h) (hstep : h * (L : ℝ)^2 ≤ α)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TauCeti.wassersteinEDist 2 (langevinStepLaw G h μ) (langevinStepLaw G h ν) ≤
      ENNReal.ofReal (Real.exp (-α*h/2)) * TauCeti.wassersteinEDist 2 μ ν := by
  let f : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun z ↦ z.1 + Real.sqrt (2*h) • z.2
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hfL (z : EuclideanSpace ℝ (Fin d)) : LipschitzWith 1 (fun x ↦ f (x,z)) := by
    dsimp [f]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_add_right, NNReal.coe_one, one_mul, le_refl]
  rw [langevinStepLaw_eq_gaussian_pushforward G h hG.continuous.measurable μ,
    langevinStepLaw_eq_gaussian_pushforward G h hG.continuous.measurable ν]
  have hc := TauCeti.wassersteinEDist_map_prod_le (p := 2) measurable_edist measurable_edist hf hfL
    (μ.map (gradientEulerStep G h)) (ν.map (gradientEulerStep G h)) (stdGaussian (EuclideanSpace ℝ (Fin d)))
  have hd := TauCeti.wassersteinEDist_map_le_mul (p := 2) measurable_edist
    (lipschitzWith_gradientEulerStep hG hmono hh hstep).continuous.measurable
    (lipschitzWith_gradientEulerStep hG hmono hh hstep) μ ν
  exact hc.trans (by simpa only [ENNReal.ofReal] using hd)
end CKSD
