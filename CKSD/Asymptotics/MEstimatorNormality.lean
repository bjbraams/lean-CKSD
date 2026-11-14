module

public import CKSD.Asymptotics.MEstimators
import CKSD.Asymptotics.ConvexRegression.Basic
import CKSD.Asymptotics.LipschitzExpansion
import CKSD.Asymptotics.MultivariateCLT
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import TauCeti.Probability.Distributions.Gaussian.Affine


/-!
# Rate and local normality of M-estimators

Asymptotic linearization and normality of M-estimators with a Lipschitz-in-parameter criterion
(GAPS 102.24). The formulation separates measurable sample criteria, deterministic local
curvature, and the quality of the empirical optimization. The fixed-design convex regression case
(GAPS 102.48) is in `CKSD.Asymptotics.RegressionMEstimators`.

## Main results

* `CKSD.m_estimator_asymptotic_linearization_and_normality`: asymptotic linearization and
  normality of M-estimators (GAPS 102.24).

## References

The proof of GAPS 102.24 follows van der Vaart, *Asymptotic Statistics*, Theorems 5.23 and 5.52:
after a modification on a null set, a peeling argument with the chaining maximal inequality of
`CKSD.Asymptotics.LipschitzChaining` gives the `√n` rate, a uniform local expansion of the
empirical process gives the linearization, and the multivariate central limit theorem with
Slutsky's lemma gives the Gaussian limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

section MEstimatorNormality

attribute [local instance] Classical.propDecidable

open scoped MatrixOrder in
/-- A negative definite matrix `V` has a uniformly negative quadratic form:
`⟪h, V h⟫ ≤ -c ‖h‖²` for some `c > 0`. The spectral bound is the argument of
`exists_pos_pos_semidef_sub_smul_one` in `CKSD.LinearModels.Decomposable`. -/
private theorem exists_pos_inner_to_euclidean_clm_le {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : (-V).PosDef) :
    ∃ c > 0, ∀ h : EuclideanSpace ℝ (Fin d),
      inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) ≤ -(c * ‖h‖ ^ 2) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · refine ⟨1, one_pos, fun h ↦ ?_⟩
    have : h = 0 := Subsingleton.elim _ _
    subst this; simp
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (-V)
    hV.isHermitian.isSelfAdjoint).2 fun x hx ↦ hV.isStrictlyPositive.spectrum_pos hx
  have hps : (-V - r • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    rw [← Matrix.le_iff]
    simpa [Algebra.algebraMap_eq_smul_one] using hle
  refine ⟨r, hr, fun h ↦ ?_⟩
  have h1 := hps.dotProduct_mulVec_nonneg (WithLp.ofLp h)
  have h2 := Matrix.inner_toEuclideanCLM V h h
  have h3 : ‖h‖ ^ 2 = WithLp.ofLp h ⬝ᵥ WithLp.ofLp h := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  simp [Matrix.sub_mulVec, Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg,
    Matrix.smul_mulVec, dotProduct_smul] at h1
  rw [h2, h3]
  linarith

/-- The empirical criterion in terms of the empirical process:
`Mₙ θ = ∫ f θ dP + n^{-1/2} Gₙ (f θ)` for `n ≥ 1`. -/
private theorem empirical_criterion_eq_integral_add {Ω X Θ : Type*} [MeasurableSpace X]
    (P : Measure X) (f : Θ → X → ℝ) (Xn : ℕ → Ω → X) {n : ℕ} (hn : 0 < n) (ω : Ω) (θ : Θ) :
    empiricalCriterion f Xn n ω θ =
      ∫ x, f θ x ∂P + (Real.sqrt n)⁻¹ * empiricalProcess P Xn n (f θ) ω := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [empiricalCriterion, empiricalProcess]
  field_simp
  rw [hsq]
  ring

/-- Tail of a geometric series: `∑_{j ∈ [a, b]} ρʲ ≤ ρᵃ / (1 - ρ)` for `0 ≤ ρ < 1`. -/
private theorem sum_icc_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (a b : ℕ) :
    ∑ j ∈ Finset.Icc a b, ρ ^ j ≤ ρ ^ a / (1 - ρ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [pow_add, ← Finset.mul_sum]
  rw [div_eq_mul_one_div]
  gcongr
  rw [geom_sum_eq h1.ne]
  have := pow_nonneg h0 (b + 1 - a)
  rw [show (ρ ^ (b + 1 - a) - 1) / (ρ - 1) = (1 - ρ ^ (b + 1 - a)) / (1 - ρ) by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring]
  gcongr
  linarith

/-- The arithmetic of a peeling shell: with `P = 2ʲ⁻¹`, a criterion gap `c x² ≤ r + g / s`,
an oscillation bound `g ≤ 4 sd (4P/s)(2 a (2P) + 1)` with `a = c / (128 sd)`, `s² r ≤ 1`,
`P < s x`, and `1 + 16 sd P ≤ c P² / 2` are incompatible. -/
private theorem shell_false {s c sd x r g P : ℝ} (hs : 0 < s) (hc : 0 < c) (hsd : 0 < sd)
    (hP : 0 ≤ P) (hcrit : c * x ^ 2 ≤ r + s⁻¹ * g)
    (hg : g ≤ 4 * sd * (4 * P / s) * (2 * (c / (128 * sd) * (2 * P)) + 1))
    (hr : s ^ 2 * r ≤ 1) (hPx : P < s * x) (hfin : 1 + 8 * sd * (2 * P) ≤ c * (4 * P ^ 2) / 8) :
    False := by
  have h1 : c * (s * x) ^ 2 ≤ s ^ 2 * r + s * g := by
    have := mul_le_mul_of_nonneg_left hcrit (sq_nonneg s)
    have e : s ^ 2 * (r + s⁻¹ * g) = s ^ 2 * r + s * g := by field_simp
    nlinarith
  have h2 : s * g ≤ c * (4 * P ^ 2) / 8 + 8 * sd * (2 * P) := by
    have := mul_le_mul_of_nonneg_left hg hs.le
    have e : s * (4 * sd * (4 * P / s) * (2 * (c / (128 * sd) * (2 * P)) + 1)) =
        c * (4 * P ^ 2) / 8 + 8 * sd * (2 * P) := by field_simp; ring
    linarith
  have h3 : P ^ 2 < (s * x) ^ 2 := by nlinarith
  nlinarith

/-- The deterministic core of the peeling argument for one sample point. Let `G` be a real
function on `ℝᵈ` (the empirical process at a fixed sample), `θ` a point with
`‖θ - θ₀‖ ≤ δ`, and `s > 0` (the root sample size). If `G` oscillates on each cube of side
`2ʲ⁺¹ / s` around `θ₀` by at most `√d · 2 · 2ʲ⁺¹ / s · (2 a 2ʲ + R)` with `a = c / (128 √d)`,
for the shells `J₀ < j ≤ M + 1`, and the criterion gap at `θ` is controlled by `G`, then
`s ‖θ - θ₀‖ ≤ 2 ^ J₀`. -/
private theorem sqrt_mul_norm_sub_le_of_shell {d : ℕ} (G : EuclideanSpace ℝ (Fin d) → ℝ)
    {θ θ₀ : EuclideanSpace ℝ (Fin d)} {s c sd δ r₀ R r : ℝ} {J₀ M : ℕ}
    (hs : 0 < s) (hc : 0 < c) (hsd : 0 < sd) (hθ : ‖θ - θ₀‖ ≤ δ) (hδr : 4 * sd * δ < r₀)
    (hM : s * δ < 2 ^ M) (hfin : ∀ j, J₀ < j → 1 + 8 * sd * 2 ^ j ≤ c * 4 ^ j / 8)
    (hR : R ≤ 1) (hr : s ^ 2 * r ≤ 1)
    (hkey : c * ‖θ - θ₀‖ ^ 2 ≤ r + s⁻¹ * |G θ - G θ₀|)
    (hshell : ∀ j, J₀ < j → j ≤ M + 1 → sd * (2 ^ (j + 1) / s) < r₀ →
      ∀ u ∈ centredCube θ₀ (2 ^ (j + 1) / s),
        |G u - G (θ₀ - WithLp.toLp 2 fun _ ↦ 2 ^ (j + 1) / s)| ≤
          sd * (2 * (2 ^ (j + 1) / s)) * (2 * (c / (128 * sd) * 2 ^ j) + R)) :
    s * ‖θ - θ₀‖ ≤ 2 ^ J₀ := by
  by_contra hω
  push Not at hω
  have hex : ∃ j : ℕ, s * ‖θ - θ₀‖ ≤ 2 ^ j :=
    pow_unbounded_of_one_lt _ (by norm_num) |>.imp fun _ h ↦ h.le
  set j := Nat.find hex with hjdef
  have hjt : s * ‖θ - θ₀‖ ≤ 2 ^ j := Nat.find_spec hex
  have hJj : J₀ < j := by
    by_contra hle
    push Not at hle
    have : (2 : ℝ) ^ j ≤ 2 ^ J₀ := pow_le_pow_right₀ (by norm_num) hle
    linarith
  have hjlow : 2 ^ (j - 1) < s * ‖θ - θ₀‖ := by
    have := Nat.find_min hex (show j - 1 < j by omega)
    push Not at this
    exact this
  have hpow : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow4 : (4 : ℝ) ^ j = 4 * (2 ^ (j - 1)) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
  have hpow1 : (2 : ℝ) ^ (j + 1) = 4 * 2 ^ (j - 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have htδ : s * ‖θ - θ₀‖ ≤ s * δ := mul_le_mul_of_nonneg_left hθ hs.le
  have hjM : j ≤ M + 1 := by
    by_contra hlt
    push Not at hlt
    have : (2 : ℝ) ^ M ≤ 2 ^ (j - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hρ0 : 0 < (2 : ℝ) ^ (j + 1) / s := by positivity
  have hρδ : (2 : ℝ) ^ (j + 1) / s < 4 * δ := by
    rw [div_lt_iff₀ hs, pow_succ, hpow]
    nlinarith
  have hjr : sd * (2 ^ (j + 1) / s) < r₀ := by nlinarith
  have hTc : θ ∈ centredCube θ₀ (2 ^ (j + 1) / s) := by
    refine mem_centred_cube_of_norm_sub_lt ?_
    rw [lt_div_iff₀ hs, pow_succ]
    nlinarith [norm_nonneg (θ - θ₀)]
  have hθc : θ₀ ∈ centredCube θ₀ (2 ^ (j + 1) / s) :=
    mem_centred_cube_of_norm_sub_lt (by rw [sub_self, norm_zero]; exact hρ0)
  have hb1 := hshell j hJj hjM hjr _ hTc
  have hb2 := hshell j hJj hjM hjr _ hθc
  set ρ : ℝ := 2 ^ (j + 1) / s with hρ
  set g : ℝ := G (θ₀ - WithLp.toLp 2 fun _ ↦ ρ) with hg
  have hGd : |G θ - G θ₀| ≤ 4 * sd * ρ * (2 * (c / (128 * sd) * 2 ^ j) + 1) := by
    have := abs_sub_le (G θ) g (G θ₀)
    rw [abs_sub_comm g] at this
    have hRnn : 2 * (c / (128 * sd) * 2 ^ j) + R ≤ 2 * (c / (128 * sd) * 2 ^ j) + 1 := by
      linarith
    have hp : 0 ≤ sd * (2 * ρ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hRnn hp]
  have hf := hfin j hJj
  rw [hpow, hpow4] at hf
  rw [hρ, hpow1, hpow] at hGd
  exact shell_false hs hc hsd (by positivity) hkey hGd hr hjlow hf

/-- **Rate of convergence of a Lipschitz M-estimator.** For a criterion family `f θ` that is
Lipschitz near `θ₀` with a square-integrable envelope, whose population criterion separates
quadratically, `∫ f θ - ∫ f θ₀ ≤ -c ‖θ - θ₀‖²` near `θ₀`, a consistent approximate maximizer
with optimization error `o_P(1/n)` satisfies `√n ‖Tₙ - θ₀‖ = O_P(1)`. The proof is the peeling
argument of van der Vaart, *Asymptotic Statistics*, Theorem 5.52, with the shell probabilities
controlled by the maximal inequality `measure_real_exists_abs_empirical_process_sub_gt_le`. -/
private theorem exists_measure_real_lt_sqrt_mul_norm_sub_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (f : EuclideanSpace ℝ (Fin d) → X → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hfm : ∀ θ ∈ Metric.ball θ₀ r₀, Measurable (f θ))
    (hfi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (f θ) P) (L : X → ℝ) (hLm : Measurable L)
    (hL0 : ∀ x, 0 ≤ L x) (hL2 : MemLp L 2 P)
    (hlip : ∀ u ∈ Metric.ball θ₀ r₀, ∀ v ∈ Metric.ball θ₀ r₀, ∀ x,
      |f u x - f v x| ≤ L x * ‖u - v‖)
    {c δ₁ : ℝ} (hc : 0 < c) (hδ₁ : 0 < δ₁)
    (hcurv : ∀ θ, ‖θ - θ₀‖ < δ₁ → ∫ x, f θ x ∂P - ∫ x, f θ₀ x ∂P ≤ -(c * ‖θ - θ₀‖ ^ 2))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hcons : TendstoInMeasure μ T atTop (fun _ ↦ θ₀))
    (r : ℕ → Ω → ℝ)
    (hr : TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ) * r n ω) atTop (fun _ ↦ 0))
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ,
      empiricalCriterion f Xn n ω θ₀ - r n ω ≤ empiricalCriterion f Xn n ω (T n ω)) :
    ∀ η > 0, ∃ K, ∀ᶠ n : ℕ in atTop, μ.real {ω | K < Real.sqrt n * ‖T n ω - θ₀‖} ≤ η := by
  intro η hη
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    refine ⟨1, Eventually.of_forall fun n ↦ ?_⟩
    have : {ω | (1 : ℝ) < Real.sqrt n * ‖T n ω - θ₀‖} = ∅ := by
      ext ω
      simp [Subsingleton.elim (T n ω - θ₀) 0]
    rw [this, measureReal_empty]; exact hη.le
  set sd : ℝ := Real.sqrt d with hsd
  have hsd0 : 0 < sd := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  set δ : ℝ := min (δ₁ / 2) (r₀ / (8 * (sd + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδδ₁ : δ < δ₁ := (min_le_left _ _).trans_lt (by linarith)
  have hδr : 4 * sd * δ < r₀ := by
    have h1 : δ ≤ r₀ / (8 * (sd + 1)) := min_le_right _ _
    have h2 : 4 * sd * (r₀ / (8 * (sd + 1))) < r₀ := by
      rw [show 4 * sd * (r₀ / (8 * (sd + 1))) = r₀ * (sd / (2 * (sd + 1))) by field_simp; ring]
      have : sd / (2 * (sd + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    nlinarith
  set β : ℝ := ∫ x, L x ^ 2 ∂P + 1 with hβ
  have hβ0 : 0 < β := by
    have : 0 ≤ ∫ x, L x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    linarith
  set φ : ℝ → ℝ := bernsteinExponent β (2 * 1 / 3) with hφ
  set a : ℝ := c / (128 * sd) with ha
  have ha0 : 0 < a := by positivity
  have hφa : 0 < φ a := by simp only [hφ, bernsteinExponent]; positivity
  set ρ : ℝ := Real.exp (-φ a) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by rw [hρ, Real.exp_lt_one_iff]; linarith
  set q : ℕ → ℝ := fun j ↦ 2 ^ d * Real.exp (-φ (a * 2 ^ j)) with hq
  have hqρ : ∀ j, q j ≤ 2 ^ d * ρ ^ (j + 1) := by
    intro j
    simp only [hq, hρ]
    gcongr
    rw [← Real.exp_nat_mul, Real.exp_le_exp, mul_neg, neg_le_neg_iff]
    have hj : ((j + 1 : ℕ) : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    have := mul_bernstein_exponent_le (β := β) (γ := 2 * 1 / 3) (t := a) (c := 2 ^ j) hβ0
      (by norm_num) ha0.le (one_le_pow₀ (by norm_num))
    calc ((j + 1 : ℕ) : ℝ) * φ a ≤ 2 ^ j * φ a := by gcongr
      _ ≤ φ (a * 2 ^ j) := by rw [mul_comm a]; exact this
  -- Conditions on the shell index.
  have hev1 : ∀ᶠ j : ℕ in atTop, 2 ^ d * ρ ^ (j + 1) ≤ 1 / 2 := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (tendsto_add_atTop_nat 1)).const_mul
      ((2 : ℝ) ^ d)
    rw [mul_zero] at this
    exact this.eventually (eventually_le_nhds (by norm_num))
  have hev2 : ∀ᶠ j : ℕ in atTop, 1 + 8 * sd * 2 ^ j ≤ c * 4 ^ j / 8 := by
    have h2 := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop
      (max 1 (8 * (8 * sd + 1) / c))
    filter_upwards [h2] with j hj
    have hx1 : 1 ≤ (2 : ℝ) ^ j := (le_max_left _ _).trans hj
    have hx2 : 8 * (8 * sd + 1) / c ≤ 2 ^ j := (le_max_right _ _).trans hj
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [div_le_iff₀ hc] at hx2
    rw [h4]
    nlinarith
  have hev3 : ∀ᶠ J : ℕ in atTop, 4 * 2 ^ d * (ρ ^ (J + 2) / (1 - ρ)) ≤ η / 4 := by
    have := (((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (tendsto_add_atTop_nat 2)).div_const (1 - ρ)).const_mul (4 * 2 ^ d)
    rw [zero_div, mul_zero] at this
    exact this.eventually (eventually_le_nhds (by positivity))
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 (hev1.and hev2)
  obtain ⟨J₀, hJ₀3, hJ₀1⟩ := (hev3.and (eventually_ge_atTop J₁)).exists
  refine ⟨2 ^ J₀, ?_⟩
  have hrem := tendsto_in_measure_lipschitz_chain_remainder μ P Xn hiid L hLm hL0 hL2 one_pos
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at hrem hcons hr
  filter_upwards [(hcons δ hδ0).eventually (eventually_le_nhds (by positivity : 0 < η / 4)),
    (hr 1 one_pos).eventually (eventually_le_nhds (by positivity : 0 < η / 4)),
    (hrem 1 one_pos).eventually (eventually_le_nhds (by positivity : 0 < η / 4)),
    eventually_ge_atTop 1] with n hnT hnr hnR hn1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (Real.sqrt n * δ) (by norm_num : (1 : ℝ) < 2)
  set G : EuclideanSpace ℝ (Fin d) → Ω → ℝ := fun θ ω ↦ empiricalProcess P Xn n (f θ) ω
    with hG
  set Rn : Ω → ℝ := lipschitzChainRemainder P Xn L 1 n with hRn
  set ρj : ℕ → ℝ := fun j ↦ 2 ^ (j + 1) / Real.sqrt n with hρj
  set anc : ℕ → EuclideanSpace ℝ (Fin d) := fun j ↦ θ₀ - WithLp.toLp 2 fun _ ↦ ρj j with hanc
  set S : Finset ℕ := (Finset.Icc (J₀ + 1) (M + 1)).filter fun j ↦ sd * ρj j < r₀ with hS
  set F : ℕ → Set Ω := fun j ↦ {ω | ∃ θ ∈ centredCube θ₀ (ρj j),
    sd * (2 * ρj j) * (2 * (a * 2 ^ j) + Rn ω) < |G θ ω - G (anc j) ω|} with hF
  have hFj : ∀ j ∈ S, μ.real (F j) ≤ 4 * q j := by
    intro j hj
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hj
    have hρ0 : 0 < ρj j := by positivity
    have hball : ∀ θ ∈ centredCube θ₀ (ρj j), θ ∈ Metric.ball θ₀ r₀ := fun θ hθ ↦ by
      rw [Metric.mem_ball, dist_eq_norm]
      exact (norm_sub_le_of_mem_centred_cube hθ).trans_lt hj.2
    have hmax := measure_real_exists_abs_empirical_process_sub_gt_le μ P Xn hiid f (anc j)
      (w := 2 * ρj j) (by positivity) (fun θ hθ ↦ hfm θ (hball θ hθ))
      (fun θ hθ ↦ hfi θ (hball θ hθ)) L hLm hL0 hL2
      (fun u hu v hv x ↦ hlip u (hball u hu) v (hball v hv) x) one_pos hn1
      (A := a * 2 ^ j) (by positivity)
    refine hmax.trans ?_
    have hq0 : 0 ≤ q j := by positivity
    exact two_mul_sum_range_pow_succ_le hq0 ((hqρ j).trans (hJ₁ j (by omega)).1) n
  set N : Set Ω := {ω | ¬ (empiricalCriterion f Xn n ω θ₀ - r n ω ≤
    empiricalCriterion f Xn n ω (T n ω))} with hN
  have hNnull : μ N = 0 := by
    have := hopt n hn1
    rwa [ae_iff] at this
  have hsub : {ω | (2 : ℝ) ^ J₀ < Real.sqrt n * ‖T n ω - θ₀‖} ⊆
      N ∪ {ω | δ < dist (T n ω) θ₀} ∪ {ω | 1 < dist ((n : ℝ) * r n ω) 0} ∪
        {ω | 1 < dist (Rn ω) 0} ∪ ⋃ j ∈ S, F j := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_ofPred_eq, not_lt,
      hN, not_not] at hcon
    obtain ⟨⟨⟨⟨hoptω, hTδ⟩, hrω⟩, hRω⟩, hFω⟩ := hcon
    simp only [mem_ofPred_eq] at hω
    rw [dist_eq_norm] at hTδ
    rw [Real.dist_eq, sub_zero] at hrω hRω
    -- The optimality inequality in terms of the empirical process.
    have hcrit := hoptω
    rw [empirical_criterion_eq_integral_add P f Xn hn1,
      empirical_criterion_eq_integral_add P f Xn hn1]
      at hcrit
    have hcurvT := hcurv (T n ω) (hTδ.trans_lt hδδ₁)
    have hkey : c * ‖T n ω - θ₀‖ ^ 2 ≤ r n ω + (Real.sqrt n)⁻¹ * |G (T n ω) ω - G θ₀ ω| := by
      have : (Real.sqrt n)⁻¹ * (G (T n ω) ω - G θ₀ ω) ≤
          (Real.sqrt n)⁻¹ * |G (T n ω) ω - G θ₀ ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 hsn.le)
      rw [mul_sub] at this
      simp only [hG] at this ⊢
      linarith
    refine hω.not_ge (sqrt_mul_norm_sub_le_of_shell (fun θ ↦ G θ ω) hsn hc hsd0 hTδ hδr hM
      (fun j hj ↦ (hJ₁ j (by omega)).2) ((le_abs_self _).trans hRω)
      (by rw [hsq]; exact (le_abs_self _).trans hrω) hkey ?_)
    intro j hJj hjM hjr u hu
    have hF1 := hFω j (by
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hjM⟩, hjr⟩)
    simp only [hF, mem_ofPred_eq, not_exists, not_and, not_lt] at hF1
    exact hF1 u hu
  calc μ.real {ω | (2 : ℝ) ^ J₀ < Real.sqrt n * ‖T n ω - θ₀‖}
      ≤ μ.real (N ∪ {ω | δ < dist (T n ω) θ₀} ∪ {ω | 1 < dist ((n : ℝ) * r n ω) 0} ∪
        {ω | 1 < dist (Rn ω) 0} ∪ ⋃ j ∈ S, F j) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real N + μ.real {ω | δ < dist (T n ω) θ₀} +
        μ.real {ω | 1 < dist ((n : ℝ) * r n ω) 0} + μ.real {ω | 1 < dist (Rn ω) 0} +
        ∑ j ∈ S, μ.real (F j) := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ (measureReal_biUnion_finset_le _ _))
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measureReal_union_le _ _
    _ ≤ 0 + η / 4 + η / 4 + η / 4 + η / 4 := by
      rw [measureReal_def, hNnull, ENNReal.toReal_zero]
      gcongr
      calc ∑ j ∈ S, μ.real (F j) ≤ ∑ j ∈ S, 4 * q j := Finset.sum_le_sum hFj
        _ ≤ ∑ j ∈ Finset.Icc (J₀ + 1) (M + 1), 4 * (2 ^ d * ρ ^ (j + 1)) :=
          (Finset.sum_le_sum fun j _ ↦ by linarith [hqρ j]).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun j _ _ ↦ by positivity)
        _ = 4 * 2 ^ d * ρ * ∑ j ∈ Finset.Icc (J₀ + 1) (M + 1), ρ ^ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
        _ ≤ 4 * 2 ^ d * ρ * (ρ ^ (J₀ + 1) / (1 - ρ)) := by
          gcongr; exact sum_icc_pow_le hρ0 hρ1 _ _
        _ = 4 * 2 ^ d * (ρ ^ (J₀ + 2) / (1 - ρ)) := by ring
        _ ≤ η / 4 := hJ₀3
    _ = η := by ring

/-- A symmetric matrix gives a symmetric bilinear form: `⟪x, V y⟫ = ⟪y, V x⟫`. -/
private theorem inner_to_euclidean_clm_comm {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.transpose = V) (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) V y) =
      inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) V x) := by
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, hV] at *
  exact dotProduct_comm _ _

/-- Completing the square: with `V ĥ = -Δ` for a symmetric `V`, the quadratic
`ψ h = ⟪h, V h⟫ / 2 + ⟪h, Δ⟫` satisfies `ψ h - ψ ĥ = ⟪h - ĥ, V (h - ĥ)⟫ / 2`. -/
private theorem quadratic_sub_eq {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.transpose = V)
    (h hh Δ : EuclideanSpace ℝ (Fin d)) (hhΔ : Matrix.toEuclideanCLM (𝕜 := ℝ) V hh = -Δ) :
    (inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2 + inner ℝ h Δ) -
      (inner ℝ hh (Matrix.toEuclideanCLM (𝕜 := ℝ) V hh) / 2 + inner ℝ hh Δ) =
      inner ℝ (h - hh) (Matrix.toEuclideanCLM (𝕜 := ℝ) V (h - hh)) / 2 := by
  have hΔ : Δ = -Matrix.toEuclideanCLM (𝕜 := ℝ) V hh := by rw [hhΔ, neg_neg]
  have hsym := inner_to_euclidean_clm_comm hV hh h
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hΔ, inner_neg_right,
    inner_neg_right, hsym]
  ring

/-- The scaled quadratic form: `⟪c h, V (c h)⟫ = c² ⟪h, V h⟫`. -/
private theorem inner_smul_to_euclidean_clm_smul {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (h : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (c • h) (Matrix.toEuclideanCLM (𝕜 := ℝ) V (c • h)) =
      c ^ 2 * inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The rescaled criterion difference in terms of the population criterion and the empirical
process: `n (Mₙ(θ₀ + h/√n) - Mₙ θ₀) = n (M(θ₀ + h/√n) - M θ₀) + √n (Gₙ(θ₀ + h/√n) - Gₙ θ₀)`. -/
private theorem nat_mul_empirical_criterion_sub {Ω X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure X) (f : EuclideanSpace ℝ (Fin d) → X → ℝ) (Xn : ℕ → Ω → X) {n : ℕ}
    (hn : 0 < n) (ω : Ω) (θ θ' : EuclideanSpace ℝ (Fin d)) :
    (n : ℝ) * (empiricalCriterion f Xn n ω θ - empiricalCriterion f Xn n ω θ') =
      n * (∫ x, f θ x ∂P - ∫ x, f θ' x ∂P) + Real.sqrt n *
        (empiricalProcess P Xn n (f θ) ω - empiricalProcess P Xn n (f θ') ω) := by
  rw [empirical_criterion_eq_integral_add P f Xn hn, empirical_criterion_eq_integral_add P f Xn hn]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have e : (n : ℝ) * (Real.sqrt n)⁻¹ = Real.sqrt n := by
    calc (n : ℝ) * (Real.sqrt n)⁻¹ = (Real.sqrt n * Real.sqrt n) * (Real.sqrt n)⁻¹ := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
      _ = Real.sqrt n := by field_simp
  linear_combination (empiricalProcess P Xn n (f θ) ω - empiricalProcess P Xn n (f θ') ω) * e

/-- The deterministic core of the M-estimator expansion: if `Φ` is within `τ` of the quadratic
`ψ h = ⟪h, V h⟫ / 2 + ⟪h, Δ⟫` at `h` and at its maximizer `ĥ` (`V ĥ = -Δ`), with `V` symmetric and
`⟪h, V h⟫ ≤ -c ‖h‖²`, and `h` maximizes `Φ` up to `ρ` relative to `ĥ`, then
`(c / 2) ‖h - ĥ‖² ≤ 2 τ + ρ`. -/
private theorem half_mul_norm_sub_sq_le {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V.transpose = V) {c : ℝ}
    (hcV : ∀ h : EuclideanSpace ℝ (Fin d),
      inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) ≤ -(c * ‖h‖ ^ 2))
    (h hh Δ : EuclideanSpace ℝ (Fin d)) (hhΔ : Matrix.toEuclideanCLM (𝕜 := ℝ) V hh = -Δ)
    (Φ : EuclideanSpace ℝ (Fin d) → ℝ) {τ ρ : ℝ}
    (h1 : |Φ h - (inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2 + inner ℝ h Δ)| ≤ τ)
    (h2 : |Φ hh - (inner ℝ hh (Matrix.toEuclideanCLM (𝕜 := ℝ) V hh) / 2 + inner ℝ hh Δ)| ≤ τ)
    (hopt : Φ hh - ρ ≤ Φ h) : c / 2 * ‖h - hh‖ ^ 2 ≤ 2 * τ + ρ := by
  have hq := quadratic_sub_eq hV h hh Δ hhΔ
  have hc := hcV (h - hh)
  rw [abs_le] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  nlinarith

/-- `V V⁻¹ = 1` on vectors, for an invertible (here negative definite) matrix. -/
private theorem to_euclidean_clm_to_euclidean_clm_inv {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : (-V).PosDef) (y : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) V (Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹ y) = y := by
  have hU : IsUnit V := by simpa using hV.isUnit.neg
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 hU
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv V hdet, Matrix.one_mulVec]

/-- Rescaling a quadratic expansion: if `|F v - ⟪v, V v⟫ / 2| ≤ κ ‖v‖²` for `‖v‖ < δq` and
`n^{-1/2} R < δq`, then `|n F(n^{-1/2} h) - ⟪h, V h⟫ / 2| ≤ κ R²` for `‖h‖ ≤ R`. -/
private theorem abs_nat_mul_sub_inner_to_euclidean_clm_le {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (F : EuclideanSpace ℝ (Fin d) → ℝ) {κ δq R : ℝ} (hκ : 0 ≤ κ) {n : ℕ} (hn : 1 ≤ n)
    (hQ : ∀ v : EuclideanSpace ℝ (Fin d), dist v 0 < δq →
      ‖F v - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) V v) / 2‖ ≤ κ * ‖‖v‖ ^ 2‖)
    (hnδ : (Real.sqrt n)⁻¹ * R < δq) (h : EuclideanSpace ℝ (Fin d)) (hh : ‖h‖ ≤ R) :
    |(n : ℝ) * F ((Real.sqrt n)⁻¹ • h) -
      inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2| ≤ κ * R ^ 2 := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hv : dist ((Real.sqrt n)⁻¹ • h) 0 < δq := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsn)]
    calc (Real.sqrt n)⁻¹ * ‖h‖ ≤ (Real.sqrt n)⁻¹ * R := by gcongr
      _ < δq := hnδ
  have hq := hQ _ hv
  rw [Real.norm_eq_abs, norm_pow, norm_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hsn), inner_smul_to_euclidean_clm_smul] at hq
  have hn' : (n : ℝ) * ((Real.sqrt n)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0)]
  have e : (n : ℝ) * F ((Real.sqrt n)⁻¹ • h) -
      inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2 =
      n * (F ((Real.sqrt n)⁻¹ • h) -
        (Real.sqrt n)⁻¹ ^ 2 * inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2) := by
    linear_combination (inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2) * hn'
  rw [e, abs_mul, Nat.abs_cast]
  calc (n : ℝ) * |F ((Real.sqrt n)⁻¹ • h) -
        (Real.sqrt n)⁻¹ ^ 2 * inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2|
      ≤ n * (κ * ((Real.sqrt n)⁻¹ * ‖h‖) ^ 2) := by gcongr
    _ = κ * ‖h‖ ^ 2 := by linear_combination (κ * ‖h‖ ^ 2) * hn'
    _ ≤ κ * R ^ 2 := by gcongr

/-- The arithmetic closing the linearization argument: `c / 2 * x ^ 2 ≤ 2 τ + ρ` with
`ρ ≤ τ = c ε² / 16` forces `x ≤ ε`. -/
private theorem le_of_half_mul_sq_le {c ε x τ ρ : ℝ} (hc : 0 < c) (hε : 0 < ε) (hx : 0 ≤ x)
    (hτ : τ = c * ε ^ 2 / 16) (hρ : ρ ≤ τ) (h : c / 2 * x ^ 2 ≤ 2 * τ + ρ) : x ≤ ε := by
  subst hτ
  by_contra hlt
  push Not at hlt
  have : ε ^ 2 < x ^ 2 := by nlinarith
  nlinarith

/-- **Asymptotic linearity of Lipschitz M-estimators** (van der Vaart, *Asymptotic Statistics*,
Theorem 5.23), given the `√n` rate. In the setting of
`tendsto_measure_real_exists_abs_sqrt_mul_empirical_process_sub_sub_inner`, with a population
criterion that has the quadratic expansion `θ₀ + h ↦ M θ₀ + ⟪h, V h⟫ / 2 + o(‖h‖²)` for a negative
definite `V`, an approximate maximizer with error `o_P(1/n)` and `√n ‖Tₙ - θ₀‖ = O_P(1)`
satisfies `√n (Tₙ - θ₀) + V⁻¹ n^{-1/2} ∑ s(Xᵢ) → 0` in probability. -/
private theorem tendsto_in_measure_sqrt_smul_sub_add_of_lipschitz {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure X) [IsProbabilityMeasure P] (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (f : EuclideanSpace ℝ (Fin d) → X → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hfm : ∀ θ ∈ Metric.ball θ₀ r₀, Measurable (f θ))
    (hfi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (f θ) P) (L : X → ℝ) (hLm : Measurable L)
    (hL0 : ∀ x, 0 ≤ L x) (hL2 : MemLp L 2 P)
    (hlip : ∀ u ∈ Metric.ball θ₀ r₀, ∀ v ∈ Metric.ball θ₀ r₀, ∀ x,
      |f u x - f v x| ≤ L x * ‖u - v‖)
    (s : X → EuclideanSpace ℝ (Fin d)) (hsm : Measurable s) (hs2 : MemLp s 2 P)
    (hs0 : ∫ x, s x ∂P = 0) (hd : ∀ x, HasFDerivAt (fun θ ↦ f θ x) (innerSL ℝ (s x)) θ₀)
    (hΔ : ∀ η > 0, ∃ K, ∀ᶠ n : ℕ in atTop,
      μ.real {ω | K < ‖(Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω)‖} ≤ η)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : (-V).PosDef)
    (hquad : Asymptotics.IsLittleO (𝓝 0)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ∫ x, f (θ₀ + h) x ∂P - ∫ x, f θ₀ x ∂P -
          inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ 2))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hrate : ∀ η > 0, ∃ K, ∀ᶠ n : ℕ in atTop,
      μ.real {ω | K < Real.sqrt n * ‖T n ω - θ₀‖} ≤ η)
    (r : ℕ → Ω → ℝ)
    (hr : TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ) * r n ω) atTop (fun _ ↦ 0))
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ θ,
      empiricalCriterion f Xn n ω θ - r n ω ≤ empiricalCriterion f Xn n ω (T n ω)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - θ₀) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
        ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))) atTop (fun _ ↦ 0) := by
  obtain ⟨c, hc, hcV⟩ := exists_pos_inner_to_euclidean_clm_le hV
  have hVt : V.transpose = V := by
    have h := hV.isHermitian.eq
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact neg_injective h
  set Δ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω) with hΔdef
  set Vi := Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹ with hVi
  set G : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ := fun n θ ω ↦ empiricalProcess P Xn n (f θ) ω
    with hG
  rw [tendsto_in_measure_iff_measure_real_lt_dist]
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨RT, hRT⟩ := hrate (η / 5) (by positivity)
  obtain ⟨K₀, hK₀⟩ := hΔ (η / 5) (by positivity)
  set R : ℝ := max RT 0 + ‖Vi‖ * max K₀ 0 + 1 with hR
  have hR0 : 0 < R := by positivity
  set τ : ℝ := c * ε ^ 2 / 16 with hτ
  have hτ0 : 0 < τ := by positivity
  set κ : ℝ := τ / (2 * R ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨δq, hδq, hQ⟩ := Metric.eventually_nhds_iff.1 (hquad.def hκ0)
  have hU := tendsto_measure_real_exists_abs_sqrt_mul_empirical_process_sub_sub_inner μ P Xn hiid
    f θ₀ hr₀ hfm hfi L hLm hL0 hL2 hlip s hsm hs2 hs0 hd hΔ hR0 (ε := τ / 2) (by positivity)
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at hr
  have hsqrt : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hRT, hK₀, hU.eventually (eventually_le_nhds (by positivity : 0 < η / 5)),
    (hr τ hτ0).eventually (eventually_le_nhds (by positivity : 0 < η / 5)),
    (hsqrt.mul_const R).eventually (gt_mem_nhds (by rw [zero_mul]; exact hδq)),
    eventually_ge_atTop 1] with n hnT hnΔ hnU hnr hnδ hn1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  set N : Set Ω := {ω | ¬ ∀ θ, empiricalCriterion f Xn n ω θ - r n ω ≤
    empiricalCriterion f Xn n ω (T n ω)} with hN
  have hNnull : μ N = 0 := by
    have := hopt n hn1
    rwa [ae_iff] at this
  -- Quadratic approximation of the population criterion on `‖h‖ ≤ R`.
  have hpop : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R →
      |(n : ℝ) * (∫ x, f (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂P - ∫ x, f θ₀ x ∂P) -
        inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2| ≤ τ / 2 := by
    intro h hh
    refine (abs_nat_mul_sub_inner_to_euclidean_clm_le V
      (fun h ↦ ∫ x, f (θ₀ + h) x ∂P - ∫ x, f θ₀ x ∂P) hκ0.le hn1 hQ hnδ h hh).trans_eq ?_
    simp only [hκ]; field_simp
  have hsub : {ω | ε < dist (Real.sqrt n • (T n ω - θ₀) + Vi (Δ n ω)) 0} ⊆
      N ∪ {ω | RT < Real.sqrt n * ‖T n ω - θ₀‖} ∪ {ω | K₀ < ‖Δ n ω‖} ∪
        {ω | ∃ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R ∧
          τ / 2 < |Real.sqrt n * (G n (θ₀ + (Real.sqrt n)⁻¹ • h) ω - G n θ₀ ω) -
            inner ℝ h (Δ n ω)|} ∪ {ω | τ < dist ((n : ℝ) * r n ω) 0} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or, mem_ofPred_eq, not_lt, not_exists, not_and, hN,
      not_not] at hcon
    obtain ⟨⟨⟨⟨hoptω, hTω⟩, hΔω⟩, hUω⟩, hrω⟩ := hcon
    simp only [mem_ofPred_eq, dist_zero_right] at hω
    rw [Real.dist_eq, sub_zero] at hrω
    set hn : EuclideanSpace ℝ (Fin d) := Real.sqrt n • (T n ω - θ₀) with hhn
    set hh : EuclideanSpace ℝ (Fin d) := -Vi (Δ n ω) with hhh
    have hhnR : ‖hn‖ ≤ R := by
      rw [hhn, norm_smul, Real.norm_eq_abs, abs_of_pos hsn]
      have := le_max_left RT 0
      have : 0 ≤ ‖Vi‖ * max K₀ 0 := by positivity
      simp only [hR]; linarith
    have hhhR : ‖hh‖ ≤ R := by
      rw [hhh, norm_neg]
      have h1 := Vi.le_opNorm (Δ n ω)
      have h2 : ‖Vi‖ * ‖Δ n ω‖ ≤ ‖Vi‖ * max K₀ 0 :=
        mul_le_mul_of_nonneg_left (hΔω.trans (le_max_left _ _)) (norm_nonneg _)
      have := le_max_right RT 0
      simp only [hR]; linarith
    have hTeq : T n ω = θ₀ + (Real.sqrt n)⁻¹ • hn := by
      rw [hhn, smul_smul, inv_mul_cancel₀ hsn.ne', one_smul, add_sub_cancel]
    set Φ : EuclideanSpace ℝ (Fin d) → ℝ := fun h ↦ (n : ℝ) *
      (empiricalCriterion f Xn n ω (θ₀ + (Real.sqrt n)⁻¹ • h) - empiricalCriterion f Xn n ω θ₀)
      with hΦ
    have happrox : ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R →
        |Φ h - (inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2 + inner ℝ h (Δ n ω))| ≤
          τ := by
      intro h hhR
      have e := nat_mul_empirical_criterion_sub P f Xn hn1 ω (θ₀ + (Real.sqrt n)⁻¹ • h) θ₀
      have h1 := hpop h hhR
      have h2 := hUω h hhR
      simp only [hΦ, e]
      simp only [hG] at h2
      have := abs_add_le ((n : ℝ) * (∫ x, f (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂P - ∫ x, f θ₀ x ∂P) -
        inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2)
        (Real.sqrt n * (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • h)) ω -
          empiricalProcess P Xn n (f θ₀) ω) - inner ℝ h (Δ n ω))
      calc _ = |((n : ℝ) * (∫ x, f (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂P - ∫ x, f θ₀ x ∂P) -
            inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2) +
            (Real.sqrt n * (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • h)) ω -
            empiricalProcess P Xn n (f θ₀) ω) - inner ℝ h (Δ n ω))| := by ring_nf
        _ ≤ τ / 2 + τ / 2 := this.trans (add_le_add h1 h2)
        _ = τ := by ring
    have hoptn : Φ hh - (n : ℝ) * r n ω ≤ Φ hn := by
      have := hoptω (θ₀ + (Real.sqrt n)⁻¹ • hh)
      rw [hTeq] at this
      simp only [hΦ]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    have hhΔ : Matrix.toEuclideanCLM (𝕜 := ℝ) V hh = -Δ n ω := by
      rw [hhh, map_neg, to_euclidean_clm_to_euclidean_clm_inv hV]
    have hfinal := half_mul_norm_sub_sq_le hVt hcV hn hh (Δ n ω) hhΔ Φ (happrox hn hhnR)
      (happrox hh hhhR) hoptn
    have hnr : (n : ℝ) * r n ω ≤ τ := (le_abs_self _).trans hrω
    have heq : hn - hh = Real.sqrt n • (T n ω - θ₀) + Vi (Δ n ω) := by
      rw [hhh, sub_neg_eq_add]
    rw [heq] at hfinal
    exact (le_of_half_mul_sq_le hc hε (norm_nonneg _) hτ hnr hfinal).not_gt hω
  calc _ ≤ μ.real (N ∪ {ω | RT < Real.sqrt n * ‖T n ω - θ₀‖} ∪ {ω | K₀ < ‖Δ n ω‖} ∪
        {ω | ∃ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R ∧
          τ / 2 < |Real.sqrt n * (G n (θ₀ + (Real.sqrt n)⁻¹ • h) ω - G n θ₀ ω) -
            inner ℝ h (Δ n ω)|} ∪ {ω | τ < dist ((n : ℝ) * r n ω) 0}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real N + μ.real {ω | RT < Real.sqrt n * ‖T n ω - θ₀‖} +
        μ.real {ω | K₀ < ‖Δ n ω‖} +
        μ.real {ω | ∃ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R ∧
          τ / 2 < |Real.sqrt n * (G n (θ₀ + (Real.sqrt n)⁻¹ • h) ω - G n θ₀ ω) -
            inner ℝ h (Δ n ω)|} + μ.real {ω | τ < dist ((n : ℝ) * r n ω) 0} := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measureReal_union_le _ _
    _ ≤ 0 + η / 5 + η / 5 + η / 5 + η / 5 := by
      rw [measureReal_def, hNnull, ENNReal.toReal_zero]
      gcongr
    _ ≤ η := by linarith


/-- The coordinates of a centred square-integrable score have mean zero. -/
private theorem integral_apply_eq_zero {X : Type*} [MeasurableSpace X] {d : ℕ} {P : Measure X}
    {s : X → EuclideanSpace ℝ (Fin d)} (hs : Integrable s P) (hs0 : ∫ x, s x ∂P = 0)
    (i : Fin d) : ∫ x, s x i ∂P = 0 := by
  have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm hs
  simp only [EuclideanSpace.proj, hs0] at this
  simpa using this

/-- The covariance matrix of the law of a centred square-integrable score is its Fisher
information matrix `(∫ sᵢ sⱼ dP)ᵢⱼ`. -/
private theorem cov_matrix_map_eq_fisher_information_matrix {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure X) [IsProbabilityMeasure P] {s : X → EuclideanSpace ℝ (Fin d)} (hsm : Measurable s)
    (hs2 : MemLp s 2 P) (hs0 : ∫ x, s x ∂P = 0) :
    TauCeti.covMatrix (P.map s) = fisherInformationMatrix P s := by
  ext i j
  rw [TauCeti.covMatrix_apply, covariance_map (by fun_prop) (by fun_prop) hsm.aemeasurable]
  simp only [covariance, Function.comp_apply,
    integral_apply_eq_zero (hs2.integrable one_le_two) hs0,
    fisherInformationMatrix]
  simp

/-- **Central limit theorem for a centred score.** For i.i.d. observations and a measurable,
square-integrable, centred score `s`, the normalized score sums `n^{-1/2} ∑ s(Xᵢ)` converge in
distribution to the centred Gaussian law with covariance the Fisher information matrix. -/
private theorem tendsto_in_distribution_inv_sqrt_smul_sum_score {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    {s : X → EuclideanSpace ℝ (Fin d)} (hsm : Measurable s)
    (hs2 : MemLp s 2 P) (hs0 : ∫ x, s x ∂P = 0) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))
      atTop id (fun _ ↦ μ) (multivariateGaussian 0 (fisherInformationMatrix P s)) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun i ↦ s ∘ Xn i with hY
  have hYlaw : ∀ i, μ.map (Y i) = P.map s := fun i ↦ by
    rw [hY, ← Measure.map_map hsm (hXm i), hlaw i]
  have h2 : MemLp (Y 0) 2 μ := by
    have : MemLp id 2 (μ.map (Y 0)) := by
      rw [hYlaw 0]
      exact (memLp_map_measure_iff aestronglyMeasurable_id hsm.aemeasurable).2 hs2
    exact this.comp_of_map (hsm.comp (hXm 0)).aemeasurable
  have hYind : iIndepFun Y μ := hind.comp (fun _ ↦ s) (fun _ ↦ hsm)
  have hYid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦
    ⟨(hsm.comp (hXm i)).aemeasurable, (hsm.comp (hXm 0)).aemeasurable,
      (hYlaw i).trans (hYlaw 0).symm⟩
  have hclt := tendsto_in_distribution_inv_sqrt_smul_sum_sub_of_iid μ Y h2 hYind hYid
  have hmean : ∫ ω, Y 0 ω ∂μ = 0 := by
    rw [hY, ← hs0, ← hlaw 0]
    exact (integral_map (hXm 0).aemeasurable (hlaw 0 ▸ hs2.aestronglyMeasurable)).symm
  rw [hmean, hYlaw 0, cov_matrix_map_eq_fisher_information_matrix P hsm hs2 hs0] at hclt
  simpa [hY] using hclt


/-- A modification of the criterion, score and Lipschitz envelope on a measurable `P`-null set
makes the almost-everywhere hypotheses of GAPS 102.24 hold everywhere. -/
private theorem exists_null_modification {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure X) (m : EuclideanSpace ℝ (Fin d) → X → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (score : X → EuclideanSpace ℝ (Fin d))
    (hs : MemLp score 2 P)
    (hd : ∀ᵐ x ∂P, HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (score x)) θ₀)
    (r₀ : ℝ) (B : X → ℝ) (hB : MemLp B 2 P)
    (hlip : ∀ᵐ x ∂P, ∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀,
      |m a x - m b x| ≤ B x * ‖a - b‖) :
    ∃ N : Set X, MeasurableSet N ∧ P N = 0 ∧ ∃ s : X → EuclideanSpace ℝ (Fin d), Measurable s ∧
      (∀ x ∉ N, s x = score x) ∧ (∀ x ∈ N, s x = 0) ∧ ∃ L : X → ℝ, Measurable L ∧
      (∀ x, 0 ≤ L x) ∧ MemLp L 2 P ∧
      (∀ x ∉ N, HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (s x)) θ₀) ∧
      (∀ x ∉ N, ∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀,
        |m a x - m b x| ≤ L x * ‖a - b‖) := by
  set s' := hs.aestronglyMeasurable.mk score
  set B' := hB.aestronglyMeasurable.mk B
  have hs'm : Measurable s' := hs.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hB'm : Measurable B' := hB.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set S : Set X := {x | ¬ (HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (score x)) θ₀ ∧
    (∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀, |m a x - m b x| ≤ B x * ‖a - b‖) ∧
    score x = s' x ∧ B x = B' x)} with hS
  have hS0 : P S = 0 := by
    rw [← ae_iff]
    filter_upwards [hd, hlip, hs.aestronglyMeasurable.ae_eq_mk, hB.aestronglyMeasurable.ae_eq_mk]
      with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set N := toMeasurable P S
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by rw [measure_toMeasurable]; exact hS0
  have hgood : ∀ x ∉ N, HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (score x)) θ₀ ∧
      (∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀, |m a x - m b x| ≤ B x * ‖a - b‖) ∧
      score x = s' x ∧ B x = B' x := fun x hx ↦ by
    by_contra h
    exact hx (subset_toMeasurable P S h)
  refine ⟨N, hN, hN0, Nᶜ.indicator s', hs'm.indicator hN.compl, fun x hx ↦ ?_,
    fun x hx ↦ by simp [hx], Nᶜ.indicator (fun x ↦ |B' x|),
    (continuous_abs.measurable.comp hB'm).indicator hN.compl,
    fun x ↦ Set.indicator_nonneg (fun _ _ ↦ abs_nonneg _) x, ?_, fun x hx ↦ ?_,
    fun x hx a ha b hb ↦ ?_⟩
  · simp [hx, (hgood x hx).2.2.1]
  · refine hB.abs.ae_eq ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hN0
    by_contra hxN
    simp [hxN, (hgood x hxN).2.2.2] at hx
  · simpa [hx, (hgood x hx).2.2.1] using (hgood x hx).1
  · simp only [Set.indicator_of_mem (show x ∈ Nᶜ from hx)]
    calc |m a x - m b x| ≤ B x * ‖a - b‖ := (hgood x hx).2.1 a ha b hb
      _ ≤ |B' x| * ‖a - b‖ := by
        rw [(hgood x hx).2.2.2]; gcongr; exact le_abs_self _

/-- GAPS 102.24: local asymptotic linearity and normality of multivariate M-estimators.
The negative-definite matrix `V` is the Hessian of the population criterion through its
quadratic little-o expansion. The empirical optimization error is `o_P(1/n)`. -/
theorem m_estimator_asymptotic_linearization_and_normality
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (m : EuclideanSpace ℝ (Fin d) → X → ℝ) (hm : ∀ θ, Measurable (m θ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (score : X → EuclideanSpace ℝ (Fin d))
    (hs : MemLp score 2 P) (hs0 : (∫ x, score x ∂P) = 0)
    (hd : ∀ᵐ x ∂P, HasFDerivAt (fun θ ↦ m θ x) (innerSL ℝ (score x)) θ₀)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (B : X → ℝ) (hB : MemLp B 2 P)
    (hlip : ∀ᵐ x ∂P, ∀ a ∈ Metric.ball θ₀ r₀, ∀ b ∈ Metric.ball θ₀ r₀,
      |m a x - m b x| ≤ B x * ‖a - b‖)
    (hmi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (m θ) P)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : (-V).PosDef)
    (hquad : Asymptotics.IsLittleO (𝓝 0)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ populationCriterion P m (θ₀ + h) -
        populationCriterion P m θ₀ -
          inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ 2))
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInMeasure μ T atTop (fun _ ↦ θ₀))
    (r : ℕ → Ω → ℝ)
    (hr : TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ) * r n ω) atTop (fun _ ↦ 0))
    (hopt : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ θ,
      empiricalCriterion m Xn n ω θ - r n ω ≤ empiricalCriterion m Xn n ω (T n ω)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - θ₀) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) V⁻¹
        ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, score (Xn i ω))) atTop (fun _ ↦ 0) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - θ₀)) atTop id (fun _ ↦ μ)
        (multivariateGaussian 0
          (V⁻¹ * fisherInformationMatrix P score * (V⁻¹).transpose)) := by
  obtain ⟨N, hN, hN0, s, hsm, hsN, hsN', L, hLm, hL0, hL2, hdN, hlipN⟩ :=
    exists_null_modification P m θ₀ score hs hd r₀ B hB hlip
  set f : EuclideanSpace ℝ (Fin d) → X → ℝ := fun θ ↦ Nᶜ.indicator (m θ) with hf
  have hNae : ∀ᵐ x ∂P, x ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hfae : ∀ θ, f θ =ᵐ[P] m θ := fun θ ↦ by
    filter_upwards [hNae] with x hx
    simp [hf, hx]
  have hsae : s =ᵐ[P] score := by
    filter_upwards [hNae] with x hx using hsN x hx
  have hfint : ∀ θ, ∫ x, f θ x ∂P = ∫ x, m θ x ∂P := fun θ ↦ integral_congr_ae (hfae θ)
  have hfm : ∀ θ ∈ Metric.ball θ₀ r₀, Measurable (f θ) := fun θ _ ↦ (hm θ).indicator hN.compl
  have hfi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (f θ) P := fun θ hθ ↦
    (hmi θ hθ).congr (hfae θ).symm
  have hlipf : ∀ u ∈ Metric.ball θ₀ r₀, ∀ v ∈ Metric.ball θ₀ r₀, ∀ x,
      |f u x - f v x| ≤ L x * ‖u - v‖ := by
    intro u hu v hv x
    by_cases hx : x ∈ N
    · simp only [hf, Set.indicator_of_notMem (show x ∉ Nᶜ from not_not.2 hx), sub_self,
        abs_zero]
      exact mul_nonneg (hL0 x) (norm_nonneg _)
    · simpa [hf, hx] using hlipN x hx u hu v hv
  have hs2 : MemLp s 2 P := hs.ae_eq hsae.symm
  have hs0' : ∫ x, s x ∂P = 0 := by rw [integral_congr_ae hsae, hs0]
  have hdf : ∀ x, HasFDerivAt (fun θ ↦ f θ x) (innerSL ℝ (s x)) θ₀ := by
    intro x
    by_cases hx : x ∈ N
    · simp only [hf, Set.indicator_of_notMem (show x ∉ Nᶜ from not_not.2 hx), hsN' x hx,
        map_zero]
      exact hasFDerivAt_const 0 θ₀
    · simpa [hf, hx] using hdN x hx
  have hgoodω : ∀ᵐ ω ∂μ, ∀ i, Xn i ω ∉ N := by
    rw [ae_all_iff]
    intro i
    refine (measure_eq_zero_iff_ae_notMem (s := Xn i ⁻¹' N)).1 ?_
    rw [← Measure.map_apply (hiid.1 i) hN, hiid.2.2 i]
    exact hN0
  have hMn : ∀ n ω, (∀ i, Xn i ω ∉ N) → ∀ θ,
      empiricalCriterion f Xn n ω θ = empiricalCriterion m Xn n ω θ := by
    intro n ω hω θ
    simp only [empiricalCriterion, hf]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hω i]
  have hsum : ∀ n ω, (∀ i, Xn i ω ∉ N) →
      ∑ i ∈ Finset.range n, s (Xn i ω) = ∑ i ∈ Finset.range n, score (Xn i ω) :=
    fun n ω hω ↦ Finset.sum_congr rfl fun i _ ↦ hsN _ (hω i)
  have hoptf : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ θ,
      empiricalCriterion f Xn n ω θ - r n ω ≤ empiricalCriterion f Xn n ω (T n ω) := by
    intro n hn
    filter_upwards [hopt n hn, hgoodω] with ω h1 h2 θ
    rw [hMn n ω h2, hMn n ω h2]
    exact h1 θ
  have hquadf : Asymptotics.IsLittleO (𝓝 0)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ∫ x, f (θ₀ + h) x ∂P - ∫ x, f θ₀ x ∂P -
          inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) V h) / 2)
      (fun h : EuclideanSpace ℝ (Fin d) ↦ ‖h‖ ^ 2) := by
    simpa only [populationCriterion, hfint] using hquad
  obtain ⟨c, hc, hcV⟩ := exists_pos_inner_to_euclidean_clm_le hV
  obtain ⟨δ₁, hδ₁, hQ⟩ := Metric.eventually_nhds_iff.1 (hquadf.def (by positivity : 0 < c / 4))
  have hcurv : ∀ θ, ‖θ - θ₀‖ < δ₁ →
      ∫ x, f θ x ∂P - ∫ x, f θ₀ x ∂P ≤ -(c / 4 * ‖θ - θ₀‖ ^ 2) := by
    intro θ hθ
    have h1 := hQ (show dist (θ - θ₀) 0 < δ₁ by rwa [dist_zero_right])
    rw [add_sub_cancel, Real.norm_eq_abs, norm_pow, norm_norm] at h1
    have h2 := hcV (θ - θ₀)
    have h3 := le_abs_self (∫ x, f θ x ∂P - ∫ x, f θ₀ x ∂P -
      inner ℝ (θ - θ₀) (Matrix.toEuclideanCLM (𝕜 := ℝ) V (θ - θ₀)) / 2)
    linarith
  have hclt := tendsto_in_distribution_inv_sqrt_smul_sum_score μ P Xn hiid hsm hs2 hs0'
  have hΔ : ∀ η > 0, ∃ K, ∀ᶠ n : ℕ in atTop,
      μ.real {ω | K < ‖(Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω)‖} ≤ η :=
    fun η hη ↦ by
      obtain ⟨M, -, hM⟩ := exists_measure_real_lt_norm_le_of_tendsto_in_distribution μ _ hclt hη
      exact ⟨M, hM⟩
  have hrate := exists_measure_real_lt_sqrt_mul_norm_sub_le μ P Xn hiid f θ₀ hr₀ hfm hfi L hLm
    hL0 hL2 hlipf (by positivity : 0 < c / 4) hδ₁ hcurv T hcons r hr
    (fun n hn ↦ (hoptf n hn).mono fun ω h ↦ h θ₀)
  have hlin := tendsto_in_measure_sqrt_smul_sub_add_of_lipschitz μ P Xn hiid f θ₀ hr₀ hfm hfi L
    hLm hL0 hL2 hlipf s hsm hs2 hs0' hdf hΔ V hV hquadf T hrate r hr hoptf
  refine ⟨hlin.congr' (Eventually.of_forall fun n ↦ ?_) EventuallyEq.rfl, ?_⟩
  · filter_upwards [hgoodω] with ω hω
    simp only [hsum n ω hω]
  have hI : fisherInformationMatrix P s = fisherInformationMatrix P score := by
    ext i j
    simp only [fisherInformationMatrix]
    refine integral_congr_ae ?_
    filter_upwards [hsae] with x hx
    rw [hx]
  have hIpsd : (fisherInformationMatrix P s).PosSemidef := by
    rw [← cov_matrix_map_eq_fisher_information_matrix P hsm hs2 hs0']
    exact TauCeti.posSemidef_covMatrix _
      ((memLp_map_measure_iff aestronglyMeasurable_id hsm.aemeasurable).2 hs2)
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun y ↦ (-V⁻¹).toEuclideanLin y + 0 with hg
  have hgc : Continuous g := (LinearMap.continuous_of_finiteDimensional _).add continuous_const
  have hcomp := hclt.continuous_comp hgc
  have hmap := TauCeti.Probability.map_affine_multivariateGaussian 0 hIpsd (-V⁻¹) 0
  have hlim : TendstoInDistribution (fun (n : ℕ) ↦ g ∘ fun ω ↦
      (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω)) atTop id (fun _ ↦ μ)
      (multivariateGaussian 0 (V⁻¹ * fisherInformationMatrix P score * (V⁻¹).transpose)) := by
    refine tendsto_in_distribution_of_map_eq hcomp aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, hmap]
    simp [hI, Matrix.transpose_neg]
  refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable μ _ _ (fun n ↦ ?_)
    (fun n ↦ ?_) hlim ?_
  · have := hiid.1
    exact hgc.measurable.comp (by fun_prop)
  · have := hT n
    fun_prop
  · refine hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
    simp only [hg, Function.comp_apply, add_zero, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      map_neg, LinearMap.neg_apply, sub_neg_eq_add]
    rfl

end MEstimatorNormality

end CKSD
