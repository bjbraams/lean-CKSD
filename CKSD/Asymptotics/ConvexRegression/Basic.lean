module

public import CKSD.Asymptotics.ConvexArgmin.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.Lindeberg.Basic
public import Mathlib.Probability.CramerWold
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.Gaussian.Transforms
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order


/-!
# Asymptotics of fixed-design convex regression M-estimators

Let `eᵢ` be independent real errors, `ρ` a convex loss with subgradient `ψ`, and `xᵢ` fixed
design vectors. A minimizer `T̂ₙ` of `b ↦ ∑_{i<n} ρ(eᵢ - ⟪xᵢ, b - β⟫)` satisfies

`√n (T̂ₙ - β) = D₁⁻¹ n^{-1/2} ∑ ψ(eᵢ) xᵢ + o_P(1)` and `√n (T̂ₙ - β) ⇒ N(0, σ² D₁⁻¹ D₀ D₁⁻¹)`,

where `σ² = E ψ(eᵢ)²`, `D₀ = lim n⁻¹ ∑ xᵢ xᵢᵀ` and `D₁ = lim n⁻¹ ∑ γᵢ xᵢ xᵢᵀ`, with `γᵢ` the
curvature of `t ↦ E ρ(eᵢ - t)` at zero. The hypotheses are uniform in `i`, so the errors need
not be identically distributed; this covers M-estimators of location-regression with iid
errors (`ρ` Huber, absolute deviation, ...) and quantile regression with heterogeneous errors.

The proof is the argument of Pollard (1991) and Hjort–Pollard: the convex process
`Zₙ(h) = ∑ [ρ(eᵢ - ⟪xᵢ, h⟫/√n) - ρ(eᵢ)]` satisfies `Zₙ(h) = -⟪Uₙ, h⟫ + ½ ⟪h, D₁ h⟫ + o_P(1)`
for each `h` (a Chebyshev bound for the nonnegative remainders, whose variances are controlled
by the `L²` continuity of `ψ`), the score `Uₙ = n^{-1/2} ∑ ψ(eᵢ) xᵢ` is asymptotically normal by
the Lindeberg–Feller theorem and the Cramér–Wold device, and the convexity lemma
`CKSD.tendsto_in_measure_sub_of_convex_on_of_is_min_on` locates the minimizer.

## Main results

* `CKSD.tendsto_in_distribution_inv_sqrt_smul_sum_smul`: the Lindeberg central limit theorem for
  the weighted score `n^{-1/2} ∑ ψ(eᵢ) xᵢ`.
* `CKSD.tendsto_in_measure_and_tendsto_in_distribution_convex_regression`: linearization and
  asymptotic normality of fixed-design convex M-estimators.

## References

* D. Pollard, *Asymptotics for least absolute deviation regression estimators*, Econometric
  Theory 7 (1991), 186–199.
* N. L. Hjort and D. Pollard, *Asymptotics for minimisers of convex processes* (1993),
  arXiv:1107.3806.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal NNReal Topology InnerProductSpace

namespace CKSD

section Design

variable {p : ℕ}

/-- A design row of index `i < n` is bounded by the maximal row norm among the first `n`. -/
private lemma norm_le_s_sup_range (x : ℕ → EuclideanSpace ℝ (Fin p)) {n i : ℕ} (hi : i < n) :
    ‖x i‖ ≤ sSup (range fun j : Fin n ↦ ‖x j.val‖) :=
  le_csSup (finite_range _).bddAbove ⟨⟨i, hi⟩, rfl⟩

/-- Under the negligible-leverage condition `maxᵢ ‖xᵢ‖ / √n → 0`, the scaled linear predictors
`n^{-1/2} ⟪xᵢ, h⟫`, `i < n`, are eventually uniformly small. -/
private lemma eventually_forall_abs_inv_sqrt_mul_inner_lt (x : ℕ → EuclideanSpace ℝ (Fin p))
    (hlev : Tendsto (fun n : ℕ ↦ sSup (range fun i : Fin n ↦ ‖x i.val‖) / Real.sqrt n) atTop
      (𝓝 0))
    (h : EuclideanSpace ℝ (Fin p)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ i < n, |(Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ| < δ := by
  have hpos : 0 < δ / (‖h‖ + 1) := by positivity
  filter_upwards [hlev.eventually (gt_mem_nhds hpos)] with n hn i hi
  have hS := norm_le_s_sup_range x hi
  set S := sSup (range fun j : Fin n ↦ ‖x j.val‖)
  have hsq : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hcs := abs_real_inner_le_norm (x i) h
  have h1 : |(Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ| ≤ S / Real.sqrt n * ‖h‖ := by
    rw [abs_mul, abs_of_nonneg hsq, div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _)))
      hsq
  have h2 : S / Real.sqrt n * ‖h‖ ≤ δ / (‖h‖ + 1) * ‖h‖ :=
    mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
  have h3 : δ / (‖h‖ + 1) * ‖h‖ < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  linarith

/-- The weighted sum of squared scaled predictors is the quadratic form of the weighted design
moment matrix: `∑ᵢ wᵢ (n^{-1/2} ⟪xᵢ, h⟫)² = hᵀ (n⁻¹ ∑ᵢ wᵢ xᵢ xᵢᵀ) h`. -/
theorem sum_mul_sq_inv_sqrt_mul_inner (x : ℕ → EuclideanSpace ℝ (Fin p)) (w : ℕ → ℝ)
    (n : ℕ) (h : EuclideanSpace ℝ (Fin p)) :
    ∑ i ∈ Finset.range n, w i * ((Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ) ^ 2 =
      WithLp.ofLp h ⬝ᵥ (Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, w i * x i j * x i k) *ᵥ WithLp.ofLp h := by
  have hin : ∀ i, ⟪x i, h⟫_ℝ = ∑ j, x i j * h j := fun i ↦ by
    simp [PiLp.inner_apply, mul_comm]
  have hsq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  simp only [hin, dotProduct, mulVec, of_apply, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hsq]; ring

/-- Convergence of the weighted design moment matrices gives convergence of the weighted sums
of squared scaled predictors to the limiting quadratic form. -/
theorem tendsto_sum_mul_sq_inv_sqrt_mul_inner (x : ℕ → EuclideanSpace ℝ (Fin p))
    (w : ℕ → ℝ) {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, w i * x i j * x i k) atTop (𝓝 M))
    (h : EuclideanSpace ℝ (Fin p)) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, w i * ((Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ) ^ 2)
      atTop (𝓝 (WithLp.ofLp h ⬝ᵥ M *ᵥ WithLp.ofLp h)) := by
  simp_rw [sum_mul_sq_inv_sqrt_mul_inner]
  have hc : Continuous fun A : Matrix (Fin p) (Fin p) ℝ ↦
      WithLp.ofLp h ⬝ᵥ A *ᵥ WithLp.ofLp h := by fun_prop
  exact (hc.tendsto M).comp hM

end Design

section Remainder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a loss `ρ` with subgradient `ψ`, the remainder
`ρ(u - t) - ρ(u) + t ψ(u)` lies between `0` and `t (ψ(u) - ψ(u - t))`. -/
private lemma remainder_nonneg_and_le {ρ ψ : ℝ → ℝ} (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v)
    (u t : ℝ) :
    0 ≤ ρ (u - t) - ρ u + t * ψ u ∧ ρ (u - t) - ρ u + t * ψ u ≤ t * (ψ u - ψ (u - t)) := by
  have h1 := hsub u (u - t)
  have h2 := hsub (u - t) u
  constructor
  · nlinarith
  · nlinarith

/-- If `ψ(u - t) - ψ(u)` has second moment at most `W`, the convex remainder
`ρ(u - t) - ρ(u) + t ψ(u)` is square integrable with second moment at most `t² W`. -/
private lemma mem_lp_remainder_and_integral_sq_le {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ)
    (hψ : Measurable ψ) (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v) {u : Ω → ℝ}
    (hu : Measurable u) (t : ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ ω, ENNReal.ofReal ((ψ (u ω - t) - ψ (u ω)) ^ 2) ∂μ ≤ ENNReal.ofReal W) :
    MemLp (fun ω ↦ ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)) 2 μ ∧
      ∫ ω, (ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)) ^ 2 ∂μ ≤ t ^ 2 * W := by
  have hρc : Continuous ρ := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  set g : Ω → ℝ := fun ω ↦ ψ (u ω - t) - ψ (u ω) with hg
  have hgm : Measurable g := (hψ.comp (hu.sub_const t)).sub (hψ.comp hu)
  have hg2 : Integrable (fun ω ↦ g ω ^ 2) μ :=
    ⟨(hgm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ sq_nonneg _)).2
        (hW.trans_lt ENNReal.ofReal_lt_top)⟩
  have hgL : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hg2
  have hDm : Measurable fun ω ↦ ρ (u ω - t) - ρ (u ω) + t * ψ (u ω) :=
    ((hρc.measurable.comp (hu.sub_const t)).sub (hρc.measurable.comp hu)).add
      ((hψ.comp hu).const_mul t)
  have hbd : ∀ ω, |ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)| ≤ |t * g ω| := by
    intro ω
    obtain ⟨h0, h1⟩ := remainder_nonneg_and_le hsub (u ω) t
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    rw [hg]
    calc t * (ψ (u ω) - ψ (u ω - t)) = -(t * (ψ (u ω - t) - ψ (u ω))) := by ring
      _ ≤ _ := neg_le_abs _
  have hDL : MemLp (fun ω ↦ ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)) 2 μ :=
    (hgL.const_mul t).mono hDm.aestronglyMeasurable (ae_of_all _ fun ω ↦ by
      simpa only [Real.norm_eq_abs] using hbd ω)
  refine ⟨hDL, ?_⟩
  have hint : ∫ ω, g ω ^ 2 ∂μ ≤ W := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _)
      (hgm.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hW0 hW
  calc ∫ ω, (ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)) ^ 2 ∂μ ≤ ∫ ω, t ^ 2 * g ω ^ 2 ∂μ := by
        refine integral_mono hDL.integrable_sq (hg2.const_mul _) fun ω ↦ ?_
        have := hbd ω
        rw [abs_mul] at this
        calc (ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)) ^ 2
            = |ρ (u ω - t) - ρ (u ω) + t * ψ (u ω)| ^ 2 := (sq_abs _).symm
          _ ≤ (|t| * |g ω|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = t ^ 2 * g ω ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
    _ = t ^ 2 * ∫ ω, g ω ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ t ^ 2 * W := mul_le_mul_of_nonneg_left hint (sq_nonneg _)

variable [IsProbabilityMeasure μ]

/-- The variance of the sum of the convex remainders of independent errors tends to zero when
the shifts `tₙᵢ` are uniformly small and their squares have bounded sums. -/
private lemma tendsto_variance_sum_remainder (e : ℕ → Ω → ℝ) (he : ∀ i, Measurable (e i))
    (hind : iIndepFun e μ) {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v)
    (hw : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      ∫⁻ ω, ENNReal.ofReal ((ψ (e i ω - t) - ψ (e i ω)) ^ 2) ∂μ ≤ ENNReal.ofReal η)
    (t : ℕ → ℕ → ℝ) (ht : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i < n, |t n i| < δ) {a : ℝ}
    (ha : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, t n i ^ 2) atTop (𝓝 a)) :
    Tendsto (fun n ↦ variance (fun ω ↦ ∑ i ∈ Finset.range n,
      (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω))) μ) atTop (𝓝 0) := by
  have ha0 : 0 ≤ a := ge_of_tendsto' ha fun n ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hρc : Continuous ρ := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  refine tendsto_order.2 ⟨fun κ hκ ↦ Eventually.of_forall fun n ↦
    hκ.trans_le (variance_nonneg _ _), fun κ hκ ↦ ?_⟩
  set η : ℝ := κ / 2 / (a + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ, hwδ⟩ := hw η hη0
  filter_upwards [ht δ hδ, ha.eventually (gt_mem_nhds (lt_add_one a))] with n hn hsum
  have hD := fun i (hi : i ∈ Finset.range n) ↦ mem_lp_remainder_and_integral_sq_le hconv hψ hsub
    (μ := μ) (he i) (t n i) hη0.le (hwδ i (t n i) (hn i (Finset.mem_range.1 hi)))
  have hfun : (fun ω ↦ ∑ i ∈ Finset.range n,
      (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω))) =
      ∑ i ∈ Finset.range n, fun ω ↦ ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω) := by
    ext ω; simp
  rw [hfun, IndepFun.variance_sum (fun i hi ↦ (hD i hi).1)]
  · calc ∑ i ∈ Finset.range n, variance (fun ω ↦ ρ (e i ω - t n i) - ρ (e i ω) +
          t n i * ψ (e i ω)) μ
        ≤ ∑ i ∈ Finset.range n, t n i ^ 2 * η := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          refine (variance_le_expectation_sq (hD i hi).1.aestronglyMeasurable).trans ?_
          simpa only [Pi.pow_apply] using (hD i hi).2
      _ = (∑ i ∈ Finset.range n, t n i ^ 2) * η := by rw [Finset.sum_mul]
      _ ≤ (a + 1) * η := mul_le_mul_of_nonneg_right hsum.le hη0.le
      _ = κ / 2 := by rw [hη]; field_simp
      _ < κ := half_lt_self hκ
  · intro i _ j _ hij
    have hm : ∀ s : ℝ, Measurable fun u : ℝ ↦ ρ (u - s) - ρ u + s * ψ u := fun s ↦
      ((hρc.measurable.comp (measurable_id.sub_const s)).sub hρc.measurable).add
        (hψ.const_mul s)
    exact (hind.indepFun hij).comp (hm (t n i)) (hm (t n j))

/-- The expectation of the sum of the convex remainders tends to `b / 2` when the
remainder means are uniformly `γᵢ t² / 2 + o(t²)` and `∑ γᵢ tₙᵢ² → b`. -/
private lemma tendsto_integral_sum_remainder (e : ℕ → Ω → ℝ) (he : ∀ i, Measurable (e i))
    {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v)
    (hw : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      ∫⁻ ω, ENNReal.ofReal ((ψ (e i ω - t) - ψ (e i ω)) ^ 2) ∂μ ≤ ENNReal.ofReal η)
    (γ : ℕ → ℝ)
    (hm : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      |∫ ω, (ρ (e i ω - t) - ρ (e i ω) + t * ψ (e i ω)) ∂μ - γ i * t ^ 2 / 2| ≤ η * t ^ 2)
    (t : ℕ → ℕ → ℝ) (ht : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i < n, |t n i| < δ) {a b : ℝ}
    (ha : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, t n i ^ 2) atTop (𝓝 a))
    (hb : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, γ i * t n i ^ 2) atTop (𝓝 b)) :
    Tendsto (fun n ↦ ∫ ω, ∑ i ∈ Finset.range n,
      (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) ∂μ) atTop (𝓝 (b / 2)) := by
  have ha0 : 0 ≤ a := ge_of_tendsto' ha fun n ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  obtain ⟨δ₁, hδ₁, hw₁⟩ := hw 1 one_pos
  have hdiff : Tendsto (fun n ↦ ∫ ω, ∑ i ∈ Finset.range n,
      (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) ∂μ -
        (∑ i ∈ Finset.range n, γ i * t n i ^ 2) / 2) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro κ hκ
    set η : ℝ := κ / 2 / (a + 1) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨δ, hδ, hmδ⟩ := hm η hη0
    filter_upwards [ht (min δ₁ δ) (lt_min hδ₁ hδ),
      ha.eventually (gt_mem_nhds (lt_add_one a))] with n hn hsum
    have hint : ∀ i ∈ Finset.range n, Integrable
        (fun ω ↦ ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) μ := fun i hi ↦
      ((mem_lp_remainder_and_integral_sq_le hconv hψ hsub (he i) (t n i) zero_le_one
        (hw₁ i (t n i) ((hn i (Finset.mem_range.1 hi)).trans_le (min_le_left _ _))))).1.integrable
        one_le_two
    rw [integral_finsetSum _ hint, Real.dist_eq, sub_zero, Finset.sum_div, ← Finset.sum_sub_distrib]
    calc |∑ i ∈ Finset.range n, (∫ ω, (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) ∂μ -
          γ i * t n i ^ 2 / 2)|
        ≤ ∑ i ∈ Finset.range n, |∫ ω, (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) ∂μ -
          γ i * t n i ^ 2 / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, η * t n i ^ 2 := Finset.sum_le_sum fun i hi ↦
          hmδ i (t n i) ((hn i (Finset.mem_range.1 hi)).trans_le (min_le_right _ _))
      _ = η * ∑ i ∈ Finset.range n, t n i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ η * (a + 1) := mul_le_mul_of_nonneg_left hsum.le hη0.le
      _ = κ / 2 := by rw [hη]; field_simp
      _ < κ := half_lt_self hκ
  simpa using hdiff.add (hb.div_const 2)

/-- **Pointwise law of large numbers for the convex remainder.** For independent errors and
uniformly small shifts `tₙᵢ` with `∑ tₙᵢ² → a` and `∑ γᵢ tₙᵢ² → b`, the sum of the remainders
`ρ(eᵢ - tₙᵢ) - ρ(eᵢ) + tₙᵢ ψ(eᵢ)` converges in probability to `b / 2`. -/
private lemma tendsto_measure_abs_sum_remainder_sub (e : ℕ → Ω → ℝ)
    (he : ∀ i, Measurable (e i)) (hind : iIndepFun e μ) {ρ ψ : ℝ → ℝ}
    (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ) (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v)
    (hw : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      ∫⁻ ω, ENNReal.ofReal ((ψ (e i ω - t) - ψ (e i ω)) ^ 2) ∂μ ≤ ENNReal.ofReal η)
    (γ : ℕ → ℝ)
    (hm : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      |∫ ω, (ρ (e i ω - t) - ρ (e i ω) + t * ψ (e i ω)) ∂μ - γ i * t ^ 2 / 2| ≤ η * t ^ 2)
    (t : ℕ → ℕ → ℝ) (ht : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i < n, |t n i| < δ) {a b : ℝ}
    (ha : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, t n i ^ 2) atTop (𝓝 a))
    (hb : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, γ i * t n i ^ 2) atTop (𝓝 b))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ μ {ω | ε ≤ |∑ i ∈ Finset.range n,
      (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) - b / 2|}) atTop (𝓝 0) := by
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ i ∈ Finset.range n,
    (ρ (e i ω - t n i) - ρ (e i ω) + t n i * ψ (e i ω)) with hS
  obtain ⟨δ₁, hδ₁, hw₁⟩ := hw 1 one_pos
  have hvar := tendsto_variance_sum_remainder e he hind hconv hψ hsub hw t ht ha
  have hmean := tendsto_integral_sum_remainder e he hconv hψ hsub hw γ hm t ht ha hb
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (variance (S n) μ / (ε / 2) ^ 2)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using hvar.div_const ((ε / 2) ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [ht δ₁ hδ₁, (Metric.tendsto_nhds.1 hmean) (ε / 2) (by positivity)] with n hn hmn
  have hL2 : MemLp (S n) 2 μ := memLp_finsetSum _ fun i hi ↦
    (mem_lp_remainder_and_integral_sq_le hconv hψ hsub (he i) (t n i) zero_le_one
      (hw₁ i (t n i) (hn i (Finset.mem_range.1 hi)))).1
  refine (measure_mono fun ω hω ↦ ?_).trans (meas_ge_le_variance_div_sq hL2 (by positivity))
  simp only [mem_ofPred_eq] at hω ⊢
  rw [Real.dist_eq] at hmn
  have := abs_sub_le (S n ω) (∫ ω, S n ω ∂μ) (b / 2)
  linarith

end Remainder

section Score

variable {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Central limit theorem for the weighted score.** Let `eᵢ` be independent, with `ψ(eᵢ)`
centred, of common variance `σ²`, and with uniformly integrable squares. If
`n⁻¹ ∑_{i<n} xᵢ xᵢᵀ → D₀` and `maxᵢ ‖xᵢ‖ / √n → 0`, then
`n^{-1/2} ∑_{i<n} ψ(eᵢ) xᵢ ⇒ N(0, σ² D₀)`. The proof applies the Lindeberg–Feller theorem to
every scalar projection and concludes by the Cramér–Wold device. -/
theorem tendsto_in_distribution_inv_sqrt_smul_sum_smul (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ℕ → Ω → ℝ) (he : ∀ i, Measurable (e i)) (hind : iIndepFun e μ) {ψ : ℝ → ℝ}
    (hψ : Measurable ψ) (hψ2 : ∀ i, MemLp (fun ω ↦ ψ (e i ω)) 2 μ)
    (hψ0 : ∀ i, ∫ ω, ψ (e i ω) ∂μ = 0) {σ2 : ℝ} (hψvar : ∀ i, ∫ ω, ψ (e i ω) ^ 2 ∂μ = σ2)
    (hUI : ∀ η > 0, ∃ K : ℝ, ∀ i,
      ∫ ω, (if K < |ψ (e i ω)| then ψ (e i ω) ^ 2 else 0) ∂μ ≤ η)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) {D₀ : Matrix (Fin p) (Fin p) ℝ} (hD₀ : D₀.PosSemidef)
    (hdesign : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, x i j * x i k) atTop (𝓝 D₀))
    (hlev : Tendsto (fun n : ℕ ↦ sSup (range fun i : Fin n ↦ ‖x i.val‖) / Real.sqrt n) atTop
      (𝓝 0)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
      ψ (e i ω) • x i) atTop id (fun _ ↦ μ) (multivariateGaussian 0 (σ2 • D₀)) := by
  have hσ : 0 ≤ σ2 := hψvar 0 ▸ integral_nonneg fun _ ↦ sq_nonneg _
  have hS : (σ2 • D₀).PosSemidef := hD₀.smul hσ
  have hUm : ∀ n : ℕ, AEMeasurable (fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
      ψ (e i ω) • x i) μ := fun n ↦ by
    have := fun i ↦ hψ.comp (he i)
    fun_prop
  refine TendstoInDistribution.of_inner aemeasurable_id hUm fun v ↦ ?_
  set c : ℕ → ℕ → ℝ := fun n j ↦ (Real.sqrt n)⁻¹ * ⟪x j, v⟫_ℝ with hc
  set X : ℕ → ℕ → Ω → ℝ := fun n j ω ↦ c n j * ψ (e j ω) with hX
  set q : ℝ := WithLp.ofLp v ⬝ᵥ D₀ *ᵥ WithLp.ofLp v with hq_def
  have hdesign' : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, (fun _ ↦ (1 : ℝ)) i * x i j * x i k) atTop (𝓝 D₀) := by
    simpa only [one_mul] using hdesign
  have hq : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, c n j ^ 2) atTop (𝓝 q) := by
    simpa only [one_mul] using tendsto_sum_mul_sq_inv_sqrt_mul_inner x (fun _ ↦ 1) hdesign' v
  have hq0 : 0 ≤ q := ge_of_tendsto' hq fun n ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have h2 : ∀ n j, MemLp (X n j) 2 μ := fun n j ↦ (hψ2 j).const_mul (c n j)
  have h0 : ∀ n j, ∫ ω, X n j ω ∂μ = 0 := fun n j ↦ by
    simp only [hX, integral_const_mul, hψ0, mul_zero]
  have hindX : ∀ n, iIndepFun (X n) μ := fun n ↦
    hind.comp (fun j u ↦ c n j * ψ u) fun j ↦ hψ.const_mul _
  have hvar : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, ∫ ω, X n j ω ^ 2 ∂μ) atTop
      (𝓝 (σ2 * q)) := by
    have : ∀ n, ∑ j ∈ Finset.range n, ∫ ω, X n j ω ^ 2 ∂μ =
        σ2 * ∑ j ∈ Finset.range n, c n j ^ 2 := fun n ↦ by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [hX, mul_pow, integral_const_mul, hψvar]
      ring
    simpa only [this] using hq.const_mul σ2
  have hlin : ∀ ε > 0, Tendsto (fun n ↦ ∑ j ∈ Finset.range n,
      ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ) atTop (𝓝 0) := by
    intro ε hε
    rw [Metric.tendsto_nhds]
    intro κ hκ
    set η : ℝ := κ / 2 / (q + 1) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨K, hK⟩ := hUI η hη0
    filter_upwards [eventually_forall_abs_inv_sqrt_mul_inner_lt x hlev v
      (by positivity : 0 < ε / (|K| + 1)), hq.eventually (gt_mem_nhds (lt_add_one q))]
      with n hn hsum
    have hterm : ∀ j < n, ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ ≤
        c n j ^ 2 * η := by
      intro j hj
      have hcj : |c n j| * |K| < ε := by
        have := hn j hj
        rw [lt_div_iff₀ (by positivity)] at this
        nlinarith [abs_nonneg (c n j)]
      calc ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ
          ≤ ∫ ω, c n j ^ 2 * (if K < |ψ (e j ω)| then ψ (e j ω) ^ 2 else 0) ∂μ := by
            refine integral_mono (integrable_ite_lt_abs_sq (h2 n j) ε)
              ((integrable_ite_lt_abs_sq (hψ2 j) K).const_mul _) fun ω ↦ ?_
            simp only [hX]
            by_cases h1 : ε < |c n j * ψ (e j ω)|
            · have hKψ : K < |ψ (e j ω)| := by
                by_contra hle
                push Not at hle
                rw [abs_mul] at h1
                have : |c n j| * |ψ (e j ω)| ≤ |c n j| * |K| :=
                  mul_le_mul_of_nonneg_left (hle.trans (le_abs_self K)) (abs_nonneg _)
                linarith
              simp only [h1, hKψ, ↓reduceIte, mul_pow, le_refl]
            · simp only [h1, ↓reduceIte]
              exact mul_nonneg (sq_nonneg _) (by split_ifs <;> positivity)
        _ = c n j ^ 2 * ∫ ω, (if K < |ψ (e j ω)| then ψ (e j ω) ^ 2 else 0) ∂μ :=
            integral_const_mul _ _
        _ ≤ c n j ^ 2 * η := mul_le_mul_of_nonneg_left (hK j) (sq_nonneg _)
    have hnonneg : 0 ≤ ∑ j ∈ Finset.range n,
        ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ :=
      Finset.sum_nonneg fun j _ ↦ integral_nonneg fun ω ↦ by split_ifs <;> positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    calc ∑ j ∈ Finset.range n, ∫ ω, (if ε < |X n j ω| then X n j ω ^ 2 else 0) ∂μ
        ≤ ∑ j ∈ Finset.range n, c n j ^ 2 * η :=
          Finset.sum_le_sum fun j hj ↦ hterm j (Finset.mem_range.1 hj)
      _ = (∑ j ∈ Finset.range n, c n j ^ 2) * η := by rw [Finset.sum_mul]
      _ ≤ (q + 1) * η := mul_le_mul_of_nonneg_right hsum.le hη0.le
      _ = κ / 2 := by rw [hη]; field_simp
      _ < κ := half_lt_self hκ
  have hlind := tendsto_in_distribution_sum_of_lindeberg_of_i_indep_fun μ X (fun n ↦ n) h2 h0
    hindX (σ2 * q) hvar hlin
  have hfun : (fun (n : ℕ) ω ↦ ⟪(Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ψ (e i ω) • x i, v⟫_ℝ) =
      fun n ω ↦ ∑ j ∈ Finset.range n, X n j ω := by
    funext n ω
    simp only [hX, hc, real_inner_smul_left, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hfun]
  refine tendsto_in_distribution_of_map_eq hlind (by fun_prop) ?_
  have hW : (fun z : EuclideanSpace ℝ (Fin p) ↦ ⟪id z, v⟫_ℝ) = fun z ↦ ⟪v, z⟫_ℝ :=
    funext fun z ↦ real_inner_comm _ _
  rw [hW, TauCeti.Probability.map_inner_multivariateGaussian 0 v hS, Measure.map_id,
    inner_zero_right, ← coe_toEuclideanCLM_eq_toEuclideanLin]
  congr 2
  change ⟪v, toEuclideanCLM (𝕜 := ℝ) (σ2 • D₀) v⟫_ℝ = σ2 * q
  rw [inner_toEuclideanCLM, smul_mulVec, dotProduct_smul, smul_eq_mul]

end Score

section Curvature

/-- A convex function on `ℝ` lies above its right-derivative tangent lines: if `ψ u` is the
right derivative of the convex function `ρ` at `u`, then `ρ u + ψ u (v - u) ≤ ρ v` for all `v`. -/
theorem add_mul_sub_le_of_convex_on_of_has_deriv_within_at {ρ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ)
    {u ψu : ℝ} (hder : HasDerivWithinAt ρ ψu (Ioi u) u) (v : ℝ) :
    ρ u + ψu * (v - u) ≤ ρ v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · have h := hconv.le_slope_of_hasDerivWithinAt_Ioi (mem_univ u) (mem_univ v) huv hder
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 huv)] at h
    linarith
  · simp
  · have hlim := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hder
    have h : (ρ u - ρ v) / (u - v) ≤ ψu := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with w (hw : u < w)
      rw [slope_def_field]
      exact hconv.slope_mono_adjacent (mem_univ v) (mem_univ w) hvu hw
    rw [div_le_iff₀ (sub_pos.2 hvu)] at h
    linarith

/-- The right derivative of a convex function on `ℝ` is monotone. -/
theorem monotone_of_convex_on_of_has_deriv_within_at {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ)
    (hder : ∀ u, HasDerivWithinAt ρ (ψ u) (Ioi u) u) : Monotone ψ := by
  intro u v huv
  rcases eq_or_lt_of_le huv with rfl | huv
  · rfl
  have h1 := add_mul_sub_le_of_convex_on_of_has_deriv_within_at hconv (hder u) v
  have h2 := add_mul_sub_le_of_convex_on_of_has_deriv_within_at hconv (hder v) u
  nlinarith

/-- **Curvature of the expected convex loss.** Let `ρ` be convex on `ℝ` with right derivative
`ψ`, `Z ∼ P` with `E ψ(Z) = 0`, and suppose that `G(s) = E ψ(Z - s)` satisfies
`|G(s) + γ s| ≤ η |s|` for `|s| ≤ |t|`. Then the expected remainder satisfies
`|E [ρ(Z - t) - ρ(Z) + t ψ(Z)] - γ t² / 2| ≤ η t²`. The proof writes the remainder as
`∫₀ᵗ (ψ(Z) - ψ(Z - s)) ds` and exchanges the integrals. -/
theorem abs_integral_remainder_sub_le (P : Measure ℝ) [IsProbabilityMeasure P] {ρ ψ : ℝ → ℝ}
    (hconv : ConvexOn ℝ univ ρ) (hder : ∀ u, HasDerivWithinAt ρ (ψ u) (Ioi u) u)
    (hψ : Measurable ψ) (hψ1 : Integrable ψ P) (hψ0 : ∫ z, ψ z ∂P = 0) {t γ η : ℝ}
    (hη : 0 ≤ η) (hint : ∀ s, |s| ≤ |t| → Integrable (fun z ↦ ψ (z - s)) P)
    (hG : ∀ s, |s| ≤ |t| → |∫ z, ψ (z - s) ∂P + γ * s| ≤ η * |s|) :
    |∫ z, (ρ (z - t) - ρ z + t * ψ z) ∂P - γ * t ^ 2 / 2| ≤ η * t ^ 2 := by
  have hmono := monotone_of_convex_on_of_has_deriv_within_at hconv hder
  have hρc : Continuous ρ := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  have hsmall : ∀ s ∈ uIcc 0 t, |s| ≤ |t| := by
    intro s hs
    rcases le_total 0 t with ht | ht
    · rw [uIcc_of_le ht] at hs
      rw [abs_of_nonneg hs.1, abs_of_nonneg ht]; exact hs.2
    · rw [uIcc_of_ge ht] at hs
      rw [abs_of_nonpos hs.2, abs_of_nonpos ht]; linarith [hs.1]
  -- the remainder as an integral of the increments of `ψ`
  have hpt : ∀ z, ρ (z - t) - ρ z + t * ψ z = ∫ s in (0 : ℝ)..t, (ψ z - ψ (z - s)) := by
    intro z
    have hanti : Antitone fun s ↦ ψ (z - s) := fun a b hab ↦ hmono (by linarith)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hanti.intervalIntegrable,
      intervalIntegral.integral_const, intervalIntegral.integral_comp_sub_left (fun u ↦ ψ u) z,
      intervalIntegral.integral_eq_sub_of_hasDeriv_right hρc.continuousOn
        (fun x _ ↦ hder x) hmono.intervalIntegrable]
    simp only [sub_zero, smul_eq_mul]
    ring
  -- integrability on the product
  have hfin : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hH : Integrable (fun z ↦ 2 * |ψ z| + |ψ (z - t)|) P :=
    (hψ1.abs.const_mul 2).add (hint t le_rfl).abs
  have hprod : Integrable (Function.uncurry fun (s z : ℝ) ↦ ψ z - ψ (z - s))
      ((volume.restrict (uIoc (0 : ℝ) t)).prod P) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hH) ?_ ?_
    · exact ((hψ.comp measurable_snd).sub
        (hψ.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable
    · have hS : ∀ᵐ s ∂(volume.restrict (uIoc (0 : ℝ) t)), s ∈ uIoc (0 : ℝ) t :=
        ae_restrict_mem measurableSet_uIoc
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hS] with q hq
      obtain ⟨s, z⟩ := q
      simp only [Function.uncurry_apply_pair, one_mul, Real.norm_eq_abs]
      have hb : ψ (z - s) ∈ uIcc (ψ (z - t)) (ψ z) := by
        rcases le_total 0 t with ht | ht
        · rw [uIoc_of_le ht] at hq
          rw [uIcc_of_le (hmono (by linarith))]
          exact ⟨hmono (by linarith [hq.2]), hmono (by linarith [hq.1])⟩
        · rw [uIoc_of_ge ht] at hq
          rw [uIcc_of_ge (hmono (by linarith))]
          exact ⟨hmono (by linarith [hq.2]), hmono (by linarith [hq.1])⟩
      rw [uIcc_comm (ψ (z - t))] at hb
      rcases le_total (ψ z) (ψ (z - t)) with h | h
      · rw [uIcc_of_le h] at hb
        rw [abs_le]; constructor <;>
          nlinarith [hb.1, hb.2, abs_nonneg (ψ z), le_abs_self (ψ z), neg_abs_le (ψ z),
            le_abs_self (ψ (z - t)), neg_abs_le (ψ (z - t))]
      · rw [uIcc_of_ge h] at hb
        rw [abs_le]; constructor <;>
          nlinarith [hb.1, hb.2, abs_nonneg (ψ z), le_abs_self (ψ z), neg_abs_le (ψ z),
            le_abs_self (ψ (z - t)), neg_abs_le (ψ (z - t))]
  -- exchange the integrals
  have hswap : ∫ z, (ρ (z - t) - ρ z + t * ψ z) ∂P =
      ∫ s in (0 : ℝ)..t, -∫ z, ψ (z - s) ∂P := by
    simp_rw [hpt]
    rw [← intervalIntegral_integral_swap hprod]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [integral_sub hψ1 (hint s (hsmall s hs)), hψ0, zero_sub]
  have hanti : AntitoneOn (fun s ↦ ∫ z, ψ (z - s) ∂P) (uIcc 0 t) := by
    intro a ha b hb hab
    exact integral_mono (hint b (hsmall b hb)) (hint a (hsmall a ha))
      fun z ↦ hmono (by linarith)
  have hγ : γ * t ^ 2 / 2 = ∫ s in (0 : ℝ)..t, γ * s := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  have hii : IntervalIntegrable (fun s ↦ -∫ z, ψ (z - s) ∂P) volume 0 t :=
    hanti.intervalIntegrable.neg
  rw [hswap, hγ, ← intervalIntegral.integral_sub hii
    ((by fun_prop : Continuous fun s : ℝ ↦ γ * s).intervalIntegrable 0 t)]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := η * |t|) (f := fun s ↦ -∫ z, ψ (z - s) ∂P - γ * s) fun s hs ↦ by
      have hs' := hsmall s (uIoc_subset_uIcc hs)
      rw [Real.norm_eq_abs, show -∫ z, ψ (z - s) ∂P - γ * s = -(∫ z, ψ (z - s) ∂P + γ * s) by
        ring, abs_neg]
      exact (hG s hs').trans (mul_le_mul_of_nonneg_left hs' hη)
  rw [Real.norm_eq_abs, sub_zero] at hbound
  calc _ ≤ η * |t| * |t| := hbound
    _ = η * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end Curvature

section Main

variable {p : ℕ}

open scoped MatrixOrder in
/-- A positive definite matrix `D` has a uniformly positive quadratic form:
`⟪h, D h⟫ ≥ c ‖h‖²` for some `c > 0` (the least eigenvalue). -/
theorem exists_pos_mul_sq_le_inner_to_euclidean_clm {D : Matrix (Fin p) (Fin p) ℝ}
    (hD : D.PosDef) :
    ∃ c > 0, ∀ h : EuclideanSpace ℝ (Fin p),
      c * ‖h‖ ^ 2 ≤ ⟪h, Matrix.toEuclideanCLM (𝕜 := ℝ) D h⟫_ℝ := by
  rcases isEmpty_or_nonempty (Fin p) with hp | hp
  · refine ⟨1, one_pos, fun h ↦ ?_⟩
    have : h = 0 := Subsingleton.elim _ _
    subst this; simp
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff D
    hD.isHermitian.isSelfAdjoint).2 fun x hx ↦ hD.isStrictlyPositive.spectrum_pos hx
  have hps : (D - r • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef := by
    rw [← Matrix.le_iff]
    simpa [Algebra.algebraMap_eq_smul_one] using hle
  refine ⟨r, hr, fun h ↦ ?_⟩
  have h1 := hps.dotProduct_mulVec_nonneg (WithLp.ofLp h)
  have h2 := Matrix.inner_toEuclideanCLM D h h
  have h3 : ‖h‖ ^ 2 = WithLp.ofLp h ⬝ᵥ WithLp.ofLp h := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  simp [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul] at h1
  rw [h2, h3]
  linarith

/-- **Asymptotics of fixed-design convex regression M-estimators.** Let `eᵢ` be independent
errors and `ρ` a convex loss with subgradient `ψ` (`ρ v ≥ ρ u + ψ u (v - u)`), with

* `ψ(eᵢ)` centred, square integrable with variance `σ²`, with uniformly integrable squares;
* `L²` continuity uniform in `i`: `E (ψ(eᵢ - t) - ψ(eᵢ))² → 0` as `t → 0`;
* uniform curvature: `E [ρ(eᵢ - t) - ρ(eᵢ) + t ψ(eᵢ)] = γᵢ t² / 2 + o(t²)` uniformly in `i`;
* design: `n⁻¹ ∑ xᵢ xᵢᵀ → D₀`, `n⁻¹ ∑ γᵢ xᵢ xᵢᵀ → D₁ ≻ 0`, `maxᵢ ‖xᵢ‖ / √n → 0`.

Then every measurable minimizer `T̂ₙ` of `b ↦ ∑_{i<n} ρ(eᵢ - ⟪xᵢ, b - β⟫)` satisfies
`√n (T̂ₙ - β) - D₁⁻¹ n^{-1/2} ∑ ψ(eᵢ) xᵢ → 0` in probability,
`n^{-1/2} ∑ ψ(eᵢ) xᵢ ⇒ N(0, σ² D₀)` and `√n (T̂ₙ - β) ⇒ N(0, σ² D₁⁻¹ D₀ D₁⁻¹)`. -/
theorem tendsto_in_measure_and_tendsto_in_distribution_convex_regression
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ℕ → Ω → ℝ) (he : ∀ i, Measurable (e i)) (hind : iIndepFun e μ)
    {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hsub : ∀ u v, ρ u + ψ u * (v - u) ≤ ρ v)
    (hψ2 : ∀ i, MemLp (fun ω ↦ ψ (e i ω)) 2 μ) (hψ0 : ∀ i, ∫ ω, ψ (e i ω) ∂μ = 0)
    {σ2 : ℝ} (hψvar : ∀ i, ∫ ω, ψ (e i ω) ^ 2 ∂μ = σ2)
    (hUI : ∀ η > 0, ∃ K : ℝ, ∀ i,
      ∫ ω, (if K < |ψ (e i ω)| then ψ (e i ω) ^ 2 else 0) ∂μ ≤ η)
    (hw : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      ∫⁻ ω, ENNReal.ofReal ((ψ (e i ω - t) - ψ (e i ω)) ^ 2) ∂μ ≤ ENNReal.ofReal η)
    (γ : ℕ → ℝ)
    (hm : ∀ η > 0, ∃ δ > 0, ∀ i t, |t| < δ →
      |∫ ω, (ρ (e i ω - t) - ρ (e i ω) + t * ψ (e i ω)) ∂μ - γ i * t ^ 2 / 2| ≤ η * t ^ 2)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) {D₀ D₁ : Matrix (Fin p) (Fin p) ℝ}
    (hD₀ : D₀.PosSemidef) (hD₁ : D₁.PosDef)
    (hdesign : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, x i j * x i k) atTop (𝓝 D₀))
    (hweighted : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, γ i * x i j * x i k) atTop (𝓝 D₁))
    (hlev : Tendsto (fun n : ℕ ↦ sSup (range fun i : Fin n ↦ ‖x i.val‖) / Real.sqrt n) atTop
      (𝓝 0))
    (β : EuclideanSpace ℝ (Fin p)) (T : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hT : ∀ n, Measurable (T n))
    (hmin : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ b, ∑ i ∈ Finset.range n, ρ (e i ω - ⟪x i, T n ω - β⟫_ℝ) ≤
      ∑ i ∈ Finset.range n, ρ (e i ω - ⟪x i, b - β⟫_ℝ)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - β) -
        (Real.sqrt n)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) D₁⁻¹
          (∑ i ∈ Finset.range n, ψ (e i ω) • x i)) atTop (fun _ ↦ 0) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
        ψ (e i ω) • x i) atTop id (fun _ ↦ μ) (multivariateGaussian 0 (σ2 • D₀)) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - β)) atTop id (fun _ ↦ μ)
        (multivariateGaussian 0 (σ2 • (D₁⁻¹ * D₀ * D₁⁻¹))) := by
  set A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) D₁ with hA_def
  set B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) D₁⁻¹ with hB_def
  have hdet : IsUnit D₁.det := (Matrix.isUnit_iff_isUnit_det _).1 hD₁.isUnit
  have hAB : ∀ u, A (B u) = u := fun u ↦ by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) D₁ * Matrix.toEuclideanCLM (𝕜 := ℝ) D₁⁻¹) u = u
    rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
    rfl
  have hAsymm : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    fun u v ↦ (Matrix.isSymmetric_toEuclideanLin_iff.2 hD₁.isHermitian) u v
  obtain ⟨c, hc, hA⟩ := exists_pos_mul_sq_le_inner_to_euclidean_clm hD₁
  set U : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, ψ (e i ω) • x i with hU
  have hclt := tendsto_in_distribution_inv_sqrt_smul_sum_smul μ e he hind hψ hψ2 hψ0 hψvar hUI x
    hD₀ hdesign hlev
  set Z : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ := fun n ω h ↦ ∑ i ∈ Finset.range n,
    (ρ (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ) - ρ (e i ω)) with hZ
  have hZc : ∀ n ω, ConvexOn ℝ univ (Z n ω) := by
    intro n ω
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
    simp only [hZ, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have key : e i ω - (Real.sqrt n)⁻¹ * ⟪x i, a • u + b • v⟫_ℝ =
        a • (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, u⟫_ℝ) +
          b • (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, v⟫_ℝ) := by
      simp only [inner_add_right, inner_smul_right, smul_eq_mul]
      linear_combination (-(e i ω)) * hab
    have hρ := hconv.2 (mem_univ (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, u⟫_ℝ))
      (mem_univ (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, v⟫_ℝ)) ha hb hab
    rw [key]
    simp only [smul_eq_mul] at hρ ⊢
    have : (a + b) * ρ (e i ω) = ρ (e i ω) := by rw [hab, one_mul]
    nlinarith
  set α : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ Real.sqrt n • (T n ω - β) with hα
  have hmin' : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, ∀ h, Z n ω (α n ω) ≤ Z n ω h := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    filter_upwards [hmin n hn] with ω hω h
    have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 hn)
    have h1 : Z n ω (α n ω) = ∑ i ∈ Finset.range n, ρ (e i ω - ⟪x i, T n ω - β⟫_ℝ) -
        ∑ i ∈ Finset.range n, ρ (e i ω) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hα, inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    have h2 : Z n ω h = ∑ i ∈ Finset.range n,
        ρ (e i ω - ⟪x i, (β + (Real.sqrt n)⁻¹ • h) - β⟫_ℝ) -
        ∑ i ∈ Finset.range n, ρ (e i ω) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [add_sub_cancel_left, inner_smul_right]
    rw [h1, h2]
    linarith [hω (β + (Real.sqrt n)⁻¹ • h)]
  have hpt : ∀ h, ∀ ε > 0, Tendsto (fun n ↦
      μ {ω | ε ≤ |Z n ω h + ⟪U n ω, h⟫_ℝ - ⟪h, A h⟫_ℝ / 2|}) atTop (𝓝 0) := by
    intro h ε hε
    have hfun : ∀ n ω, Z n ω h + ⟪U n ω, h⟫_ℝ = ∑ i ∈ Finset.range n,
        (ρ (e i ω - (Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ) - ρ (e i ω) +
          (Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ * ψ (e i ω)) := by
      intro n ω
      simp only [hZ, hU, real_inner_smul_left, sum_inner, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hq : ⟪h, A h⟫_ℝ = WithLp.ofLp h ⬝ᵥ D₁ *ᵥ WithLp.ofLp h := Matrix.inner_toEuclideanCLM _ _ _
    simp only [hfun, hq]
    have hdesign' : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, (fun _ ↦ (1 : ℝ)) i * x i j * x i k) atTop (𝓝 D₀) := by
      simpa only [one_mul] using hdesign
    have ha : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, ((Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ) ^ 2)
        atTop (𝓝 (WithLp.ofLp h ⬝ᵥ D₀ *ᵥ WithLp.ofLp h)) := by
      simpa only [one_mul] using tendsto_sum_mul_sq_inv_sqrt_mul_inner x (fun _ ↦ 1) hdesign' h
    exact tendsto_measure_abs_sum_remainder_sub e he hind hconv hψ hsub hw γ hm
      (fun n i ↦ (Real.sqrt n)⁻¹ * ⟪x i, h⟫_ℝ)
      (fun δ hδ ↦ eventually_forall_abs_inv_sqrt_mul_inner_lt x hlev h hδ) ha
      (tendsto_sum_mul_sq_inv_sqrt_mul_inner x γ hweighted h) hε
  have htight : ∀ η > (0 : ℝ≥0∞), ∃ M : ℝ, ∀ᶠ n in atTop, μ {ω | M < ‖U n ω‖} ≤ η := by
    intro η hη
    rcases eq_or_ne η ⊤ with rfl | hηt
    · exact ⟨0, Eventually.of_forall fun _ ↦ le_top⟩
    obtain ⟨M, -, hM⟩ := exists_measure_real_lt_norm_le_of_tendsto_in_distribution μ U hclt
      (ENNReal.toReal_pos hη.ne' hηt)
    refine ⟨M, hM.mono fun n hn ↦ ?_⟩
    rw [← ofReal_measureReal]
    exact (ENNReal.ofReal_le_iff_le_toReal hηt).2 hn
  have hlin := tendsto_in_measure_sub_of_convex_on_of_is_min_on Z hZc U A B hAB hAsymm hc hA hpt
    htight α hmin'
  have hlin' : TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - β) -
      (Real.sqrt n)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) D₁⁻¹
        (∑ i ∈ Finset.range n, ψ (e i ω) • x i)) atTop (fun _ ↦ 0) :=
    hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ by simp only [hα, hU, hB_def, map_smul])
      EventuallyEq.rfl
  refine ⟨hlin', hclt, ?_⟩
  -- the limit law of `√n (T̂ₙ - β)`
  have hσ : 0 ≤ σ2 := hψvar 0 ▸ integral_nonneg fun _ ↦ sq_nonneg _
  have hS : (σ2 • D₀).PosSemidef := hD₀.smul hσ
  set g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
    fun y ↦ (D₁⁻¹).toEuclideanLin y + 0 with hg
  have hgc : Continuous g := (LinearMap.continuous_of_finiteDimensional _).add continuous_const
  have hmap := TauCeti.Probability.map_affine_multivariateGaussian 0 hS D₁⁻¹ 0
  have hsymm : D₁⁻¹.transpose = D₁⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, (Matrix.isHermitian_iff_isSymm.1 hD₁.isHermitian).eq]
  have hlim : TendstoInDistribution (fun (n : ℕ) ↦ g ∘ U n) atTop id (fun _ ↦ μ)
      (multivariateGaussian 0 (σ2 • (D₁⁻¹ * D₀ * D₁⁻¹))) := by
    refine tendsto_in_distribution_of_map_eq (hclt.continuous_comp hgc) aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, hmap, hsymm, Matrix.mul_smul, Matrix.smul_mul]
    simp
  have hUm : ∀ n, Measurable (U n) := fun n ↦ by
    have := fun i ↦ hψ.comp (he i)
    fun_prop
  refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable μ _ _
    (fun n ↦ hgc.measurable.comp (hUm n)) (fun n ↦ by have := hT n; fun_prop)
    hlim ?_
  refine hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
  simp only [hα, hg, Function.comp_apply, add_zero, hB_def,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rfl

end Main

end CKSD
