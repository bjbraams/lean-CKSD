module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Linear inverse problems in sequence space

The white-noise model `Y = Af + εW` for a compact injective operator with singular system
`A eⱼ = κⱼ gⱼ` is written in its equivalent sequence form `Yⱼ = κⱼ fⱼ + ε Zⱼ`. Coordinates are
indexed from `0`, the coordinate `j` standing for the index `j + 1` of the singular system.
Squared `ℓ²` distances are taken in `ℝ≥0∞`, so that the risks and the Sobolev ellipsoid are
meaningful for arbitrary sequences. The Gaussian-prior posterior is written in its conjugate
closed form, coordinatewise independent normal.

## Main definitions

* `CKSD.inverseProblemLaw κ ε f`: the law of the sequence observation `Yⱼ = κⱼ fⱼ + ε Zⱼ`.
* `CKSD.inverseProblemRisk`, `CKSD.inverseProblemSobolevBall`: the squared `ℓ²` risk of an
  estimator and the Sobolev ellipsoid `∑ⱼ (j + 1)^{2β} fⱼ² ≤ R²`.
* `CKSD.gaussianSeqPosterior κ β ε y`: the posterior under the Gaussian prior
  `fⱼ ∼ N(0, (j + 1)^{-1-2β})`.

## Main results

* `CKSD.exists_minimax_rate_inverseProblem`: the minimax rate `ε^{2β/(2β+2a+1)}`.
* `CKSD.tendsto_gaussianSeqPosterior_contraction`: posterior contraction of the Gaussian-prior
  posterior.

Sources: GAPS 104.20.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Squared `ℓ²` distance between real sequences, possibly infinite. -/
def seqDistSq (f g : ℕ → ℝ) : ℝ≥0∞ := ∑' j, ENNReal.ofReal ((f j - g j) ^ 2)

/-- The Sobolev ellipsoid `S^β(R) = {f : ∑ⱼ j^{2β} fⱼ² ≤ R²}`, with `j` running from `1`. -/
def inverseProblemSobolevBall (β R : ℝ) : Set (ℕ → ℝ) :=
  {f | ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) ^ (2 * β) * f j ^ 2) ≤ ENNReal.ofReal (R ^ 2)}

/-- Law of the observations `Yⱼ = κⱼ fⱼ + ε Zⱼ` with independent standard normal `Zⱼ`. -/
def inverseProblemLaw (κ : ℕ → ℝ) (ε : ℝ) (f : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j ↦ gaussianReal (κ j * f j) (ε ^ 2).toNNReal

/-- Mean squared `ℓ²` risk of an estimator at the truth `f`. -/
def inverseProblemRisk (κ : ℕ → ℝ) (ε : ℝ) (fhat : (ℕ → ℝ) → ℕ → ℝ) (f : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, seqDistSq (fhat y) f ∂inverseProblemLaw κ ε f

/-- Posterior under the prior with independent `fⱼ ∼ N(0, j^{-1-2β})`, in conjugate form:
coordinate `j` is normal with mean `λⱼκⱼYⱼ / (κⱼ²λⱼ + ε²)` and variance `λⱼε² / (κⱼ²λⱼ + ε²)`. -/
def gaussianSeqPosterior (κ : ℕ → ℝ) (β ε : ℝ) (y : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j ↦
    gaussianReal ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * κ j * y j /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2))
      ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * ε ^ 2 /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)).toNNReal

/-- Polynomially decaying singular values: `c₀⁻¹ j^{-a} ≤ κⱼ ≤ c₀ j^{-a}`, `j ≥ 1`. -/
def HasPolynomialSingularValues (κ : ℕ → ℝ) (a c₀ : ℝ) : Prop :=
  ∀ j : ℕ, c₀⁻¹ * ((j : ℝ) + 1) ^ (-a) ≤ κ j ∧ κ j ≤ c₀ * ((j : ℝ) + 1) ^ (-a)

/-- GAPS 104.20: the minimax `ℓ²` rate over a Sobolev ellipsoid in a mildly ill-posed linear
inverse problem is `ε^r` with `r = 2β/(2β+2a+1)`. There are constants `0 < c ≤ C`, depending only
on `a`, `β`, `R`, and `c₀`, such that for every operator with polynomially decaying singular values
and every noise level `ε ∈ (0, 1]` some measurable estimator has worst-case squared risk at most
`(C ε^r)²` and every measurable estimator has worst-case squared risk at least `(c ε^r)²`. -/
theorem exists_minimax_rate_inverseProblem (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (hR : 0 < R) (hc₀ : 1 ≤ c₀) :
    let r := 2 * β / (2 * β + 2 * a + 1)
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ κ : ℕ → ℝ, HasPolynomialSingularValues κ a c₀ →
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        (∃ fhat : (ℕ → ℝ) → ℕ → ℝ, Measurable fhat ∧
          ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f ≤
            ENNReal.ofReal ((C * ε ^ r) ^ 2)) ∧
        ∀ fhat : (ℕ → ℝ) → ℕ → ℝ, Measurable fhat →
          ENNReal.ofReal ((c * ε ^ r) ^ 2) ≤
            ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f := by
  sorry

/-- Second moment of an affine function under a normal law, in `ℝ≥0∞`:
`∫⁻ ((c X - d)² + s) = (cμ - d)² + c² v + s` for `X ∼ N(μ, v)` and `s ≥ 0`. -/
theorem lintegral_ofReal_sq_add_gaussianReal (c d μ : ℝ) (v : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x, ENNReal.ofReal ((c * x - d) ^ 2 + s) ∂gaussianReal μ v =
      ENNReal.ofReal ((c * μ - d) ^ 2 + c ^ 2 * v + s) := by
  have hY : MemLp (fun x : ℝ ↦ c * x - d) 2 (gaussianReal μ v) :=
    ((memLp_id_gaussianReal 2).const_mul c).sub (memLp_const d)
  have hint : Integrable (fun x : ℝ ↦ (c * x - d) ^ 2 + s) (gaussianReal μ v) :=
    hY.integrable_sq.add (integrable_const s)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x ↦ by positivity)]
  congr 1
  rw [integral_add hY.integrable_sq (integrable_const s), integral_const, probReal_univ,
    one_smul]
  have hvar := variance_eq_sub hY
  have hmean : ∫ x, (c * x - d) ∂gaussianReal μ v = c * μ - d := by
    have h1 : Integrable (fun x : ℝ ↦ c * x) (gaussianReal μ v) :=
      ((memLp_id_gaussianReal 1).integrable le_rfl).const_mul c
    rw [integral_sub h1 (integrable_const d), integral_const_mul, integral_id_gaussianReal, integral_const,
      probReal_univ, one_smul]
  have hv2 : Var[fun x : ℝ ↦ c * x - d; gaussianReal μ v] = c ^ 2 * v := by
    rw [variance_sub_const (by fun_prop), variance_const_mul, variance_fun_id_gaussianReal]
  rw [hv2, hmean] at hvar
  simp only [Pi.pow_apply] at hvar
  linarith

/-- Tangent-line estimate for `t ↦ t^{-m}`: `x^{-m} + m x^{-m-1} ≤ (x - 1)^{-m}` for `m > 0`,
`x > 1`. -/
theorem rpow_neg_add_mul_rpow_neg_sub_one_le {m x : ℝ} (hm : 0 < m) (hx : 1 < x) :
    x ^ (-m) + m * x ^ (-m - 1) ≤ (x - 1) ^ (-m) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hlog : 1 / x ≤ Real.log x - Real.log (x - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by positivity)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    have : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
    linarith
  have hsplit : (x - 1) ^ (-m) = x ^ (-m) * Real.exp (m * (Real.log x - Real.log (x - 1))) := by
    rw [Real.rpow_def_of_pos hx1, Real.rpow_def_of_pos hx0, ← Real.exp_add]
    congr 1; ring
  have hexp : 1 + m * (1 / x) ≤ Real.exp (m * (Real.log x - Real.log (x - 1))) := by
    have := Real.add_one_le_exp (m * (Real.log x - Real.log (x - 1)))
    nlinarith
  have hxm : x ^ (-m - 1) = x ^ (-m) * (1 / x) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_one_div]
  rw [hsplit, hxm]
  have hpos : 0 < x ^ (-m) := Real.rpow_pos_of_pos hx0 _
  nlinarith

/-- Shifted `p`-series tail bound by telescoping: `∑_{n ≥ 1} (T + n)^{-q} ≤ T^{1-q}/(q-1)` for
`T > 0`, `q > 1`. -/
theorem tsum_ofReal_rpow_add_le {T q : ℝ} (hT : 0 < T) (hq : 1 < q) :
    ∑' n : ℕ, ENNReal.ofReal ((T + (n + 1)) ^ (-q)) ≤ ENNReal.ofReal (T ^ (1 - q) / (q - 1)) := by
  set m := q - 1 with hm
  have hm0 : 0 < m := by linarith
  have hstep (n : ℕ) : (T + (n + 1)) ^ (-q) ≤
      ((T + n) ^ (-m) - (T + (n + 1)) ^ (-m)) / m := by
    have h := rpow_neg_add_mul_rpow_neg_sub_one_le hm0 (x := T + (n + 1))
      (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
    have e1 : T + (n + 1) - 1 = T + n := by ring
    have e2 : -m - 1 = -q := by rw [hm]; ring
    rw [e1, e2] at h
    rw [le_div_iff₀ hm0]; linarith
  refine ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_
  calc ∑ n ∈ Finset.range N, ENNReal.ofReal ((T + (n + 1)) ^ (-q))
      ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (((T + n) ^ (-m) - (T + (n + 1)) ^ (-m)) / m) :=
        Finset.sum_le_sum fun n _ ↦ ENNReal.ofReal_le_ofReal (hstep n)
    _ = ENNReal.ofReal (∑ n ∈ Finset.range N, ((T + n) ^ (-m) - (T + (n + 1)) ^ (-m)) / m) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ ↦ ((Real.rpow_nonneg (by positivity) _).trans
          (hstep n))]
    _ ≤ ENNReal.ofReal (T ^ (1 - q) / (q - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have htel := Finset.sum_range_sub' (fun n : ℕ ↦ (T + n) ^ (-m)) N
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at htel
        rw [← Finset.sum_div, htel]
        have e : 1 - q = -m := by rw [hm]; ring
        rw [e, ← hm]
        gcongr
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ T + N by positivity) (-m)
        linarith


/-- Expected posterior squared `ℓ²` distance from the truth in the Gaussian sequence model: the sum
over coordinates of squared bias, variance of the posterior mean, and posterior variance. -/
theorem lintegral_lintegral_seqDistSq_gaussianSeqPosterior (κ : ℕ → ℝ) (β : ℝ) {ε : ℝ}
    (hε : 0 < ε) (f₀ : ℕ → ℝ) :
    ∫⁻ y, ∫⁻ f, seqDistSq f f₀ ∂gaussianSeqPosterior κ β ε y ∂inverseProblemLaw κ ε f₀ =
      ∑' j : ℕ, ENNReal.ofReal
        ((((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j / (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) *
            (κ j * f₀ j) - f₀ j) ^ 2 +
          (((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) ^ 2 * ε ^ 2 +
          ((j : ℝ) + 1) ^ (-1 - 2 * β) * ε ^ 2 /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) := by
  set lam : ℕ → ℝ := fun j ↦ ((j : ℝ) + 1) ^ (-1 - 2 * β) with hlam
  set D : ℕ → ℝ := fun j ↦ κ j ^ 2 * lam j + ε ^ 2 with hD
  have hlam0 (j : ℕ) : 0 ≤ lam j := Real.rpow_nonneg (by positivity) _
  have hD0 (j : ℕ) : 0 < D j := by simp only [hD]; positivity
  have hs0 (j : ℕ) : 0 ≤ lam j * ε ^ 2 / D j := by have := hlam0 j; have := hD0 j; positivity
  have hinner (y : ℕ → ℝ) : ∫⁻ f, seqDistSq f f₀ ∂gaussianSeqPosterior κ β ε y =
      ∑' j, ENNReal.ofReal ((lam j * κ j / D j * y j - f₀ j) ^ 2 + lam j * ε ^ 2 / D j) := by
    simp only [seqDistSq]
    rw [lintegral_tsum (f := fun j (f : ℕ → ℝ) ↦ ENNReal.ofReal ((f j - f₀ j) ^ 2))
      fun j ↦ Measurable.aemeasurable (by fun_prop)]
    refine tsum_congr fun j ↦ ?_
    have hg : Measurable fun x : ℝ ↦ ENNReal.ofReal ((1 * x - f₀ j) ^ 2 + 0) := by fun_prop
    have := (measurePreserving_eval_infinitePi (fun i : ℕ ↦
      gaussianReal ((((i : ℝ) + 1) ^ (-1 - 2 * β)) * κ i * y i /
        (κ i ^ 2 * ((i : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2))
      ((((i : ℝ) + 1) ^ (-1 - 2 * β)) * ε ^ 2 /
        (κ i ^ 2 * ((i : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)).toNNReal) j).lintegral_comp hg
    simp only [one_mul, add_zero, Function.eval] at this
    rw [gaussianSeqPosterior, this]
    have h2 := lintegral_ofReal_sq_add_gaussianReal 1 (f₀ j)
      ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * κ j * y j /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2))
      ((((j : ℝ) + 1) ^ (-1 - 2 * β)) * ε ^ 2 /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)).toNNReal le_rfl
    simp only [one_mul, add_zero, one_pow] at h2
    rw [h2, Real.coe_toNNReal _ (hs0 j)]
    congr 2
    simp only [hlam, hD]; ring
  simp_rw [hinner]
  rw [lintegral_tsum (f := fun j (y : ℕ → ℝ) ↦
      ENNReal.ofReal ((lam j * κ j / D j * y j - f₀ j) ^ 2 + lam j * ε ^ 2 / D j))
    fun j ↦ Measurable.aemeasurable (by fun_prop)]
  refine tsum_congr fun j ↦ ?_
  have hg : Measurable fun x : ℝ ↦
      ENNReal.ofReal ((lam j * κ j / D j * x - f₀ j) ^ 2 + lam j * ε ^ 2 / D j) := by fun_prop
  have := (measurePreserving_eval_infinitePi (fun i : ℕ ↦
    gaussianReal (κ i * f₀ i) (ε ^ 2).toNNReal) j).lintegral_comp hg
  simp only [Function.eval] at this
  rw [inverseProblemLaw, this, lintegral_ofReal_sq_add_gaussianReal _ _ _ _ (hs0 j),
    Real.coe_toNNReal _ (by positivity)]


/-- Coordinatewise bounds for the Gaussian sequence posterior with `x = ε²` and `n = j + 1`:
the squared relative bias is at most `c₀² x^r n^{2β}`, the variance of the posterior mean is at
most the posterior variance, and the posterior variance is at most `c₀² 2^{1+2β} (T + n)^{-(1+2β)}`
with `T = x^{-1/(2β+2a+1)}`. -/
theorem gaussianSeqPosterior_term_le {a β c₀ κj x n : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
    (hc₀ : 1 ≤ c₀) (hx : 0 < x) (hn : 1 ≤ n)
    (hκ : c₀⁻¹ * n ^ (-a) ≤ κj ∧ κj ≤ c₀ * n ^ (-a)) :
    let lam := n ^ (-1 - 2 * β)
    let D := κj ^ 2 * lam + x
    let r := 2 * β / (2 * β + 2 * a + 1)
    (lam * κj / D * κj - 1) ^ 2 ≤ c₀ ^ 2 * x ^ r * n ^ (2 * β) ∧
      (lam * κj / D) ^ 2 * x ≤ lam * x / D ∧
      lam * x / D ≤ c₀ ^ 2 * 2 ^ (1 + 2 * β) * (x ^ (-1 / (2 * β + 2 * a + 1)) + n) ^ (-(1 + 2 * β)) := by
  intro lam D r
  set p := 2 * β + 2 * a + 1 with hp
  set q := 1 + 2 * β with hq
  have hp0 : 0 < p := by positivity
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c₀ := by linarith
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hn0 _
  have hκ0 : 0 < κj := lt_of_lt_of_le (by positivity) hκ.1
  have hD0 : 0 < D := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by rw [div_le_one hp0]; linarith
  -- lower bound for `κj²`
  have hκsq : c₀⁻¹ ^ 2 * n ^ (-2 * a) ≤ κj ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hκ.1 2
    have e : (n ^ (-a)) ^ 2 = n ^ (-2 * a) := by
      rw [← Real.rpow_natCast (n ^ (-a)), ← Real.rpow_mul hn0.le]; norm_num [mul_comm]
    rwa [mul_pow, e] at h
  -- lower bound for `κj² λ`
  have ht : c₀⁻¹ ^ 2 * n ^ (-p) ≤ κj ^ 2 * lam := by
    have e : n ^ (-p) = n ^ (-2 * a) * lam := by
      simp only [lam]; rw [← Real.rpow_add hn0]; congr 1; linarith
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hκsq hlam0.le
  have ht0 : 0 < κj ^ 2 * lam := by positivity
  have hpr : p * r = 2 * β := by simp only [r]; field_simp; linarith
  refine ⟨?_, ?_, ?_⟩
  · -- bias
    have e1 : lam * κj / D * κj - 1 = -(x / D) := by
      simp only [D]; field_simp; ring
    rw [e1, neg_sq]
    have hxD0' : 0 < x / D := by positivity
    have hxD0 : 0 ≤ x / D := hxD0'.le
    have hxD1 : x / D ≤ 1 := by rw [div_le_one hD0]; simp only [D]; linarith
    have s1 : (x / D) ^ 2 ≤ (x / D) ^ r := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hxD0' hxD1 (by push_cast; linarith)
    have s2 : (x / D) ^ r ≤ (x * (c₀ ^ 2 * n ^ p)) ^ r := by
      refine Real.rpow_le_rpow hxD0 ?_ hr0
      rw [div_le_iff₀ hD0]
      have : 1 ≤ (c₀ ^ 2 * n ^ p) * (κj ^ 2 * lam) := by
        calc (1 : ℝ) = (c₀ ^ 2 * n ^ p) * (c₀⁻¹ ^ 2 * n ^ (-p)) := by
              rw [Real.rpow_neg hn0.le]
              have : 0 < n ^ p := Real.rpow_pos_of_pos hn0 _
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
      have hD' : κj ^ 2 * lam ≤ D := by simp only [D]; linarith
      have h1 : 1 ≤ (c₀ ^ 2 * n ^ p) * D :=
        this.trans (mul_le_mul_of_nonneg_left hD' (by positivity))
      calc x = x * 1 := (mul_one x).symm
        _ ≤ x * ((c₀ ^ 2 * n ^ p) * D) := mul_le_mul_of_nonneg_left h1 hx.le
        _ = _ := by ring
    have s3 : (x * (c₀ ^ 2 * n ^ p)) ^ r = (c₀ ^ 2) ^ r * x ^ r * n ^ (2 * β) := by
      rw [Real.mul_rpow hx.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hn0.le, hpr]; ring
    have s4 : (c₀ ^ 2) ^ r ≤ c₀ ^ 2 := by
      calc (c₀ ^ 2) ^ r ≤ (c₀ ^ 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by nlinarith) hr1
        _ = c₀ ^ 2 := Real.rpow_one _
    calc (x / D) ^ 2 ≤ (c₀ ^ 2) ^ r * x ^ r * n ^ (2 * β) := s3 ▸ s1.trans s2
      _ ≤ c₀ ^ 2 * x ^ r * n ^ (2 * β) := by gcongr
  · -- variance of the posterior mean
    have hk : lam * κj ^ 2 / D ≤ 1 := by rw [div_le_one hD0]; simp only [D]; nlinarith
    calc (lam * κj / D) ^ 2 * x = (lam * x / D) * (lam * κj ^ 2 / D) := by ring
      _ ≤ (lam * x / D) * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = lam * x / D := mul_one _
  · -- posterior variance
    set T := x ^ (-1 / p) with hT
    have hT0 : 0 < T := Real.rpow_pos_of_pos hx _
    have hxT : x = T ^ (-p) := by
      rw [hT, ← Real.rpow_mul hx.le]; field_simp; simp
    have h2q : (0 : ℝ) < 2 ^ q := by positivity
    have hq0 : 0 < q := by positivity
    have key (z : ℝ) (hz : 0 < z) (hzT : T + n ≤ 2 * z) : z ^ (-q) ≤ 2 ^ q * (T + n) ^ (-q) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity) hzT (by linarith : -q ≤ 0)
      rw [Real.mul_rpow (by norm_num) hz.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h
      calc z ^ (-q) = 2 ^ q * ((2 ^ q)⁻¹ * z ^ (-q)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h h2q.le
    have hs1 : lam * x / D ≤ lam := by
      rw [div_le_iff₀ hD0]; simp only [D]; nlinarith
    have hs2 : lam * x / D ≤ c₀ ^ 2 * x * n ^ (2 * a) := by
      rw [div_le_iff₀ hD0]
      have hD' : κj ^ 2 * lam ≤ D := by simp only [D]; linarith
      have : 1 ≤ c₀ ^ 2 * n ^ (2 * a) * κj ^ 2 := by
        calc (1 : ℝ) = c₀ ^ 2 * n ^ (2 * a) * (c₀⁻¹ ^ 2 * n ^ (-2 * a)) := by
              rw [show -2 * a = -(2 * a) by ring, Real.rpow_neg hn0.le]
              have : 0 < n ^ (2 * a) := Real.rpow_pos_of_pos hn0 _
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hκsq (by positivity)
      calc lam * x = (lam * x) * 1 := (mul_one _).symm
        _ ≤ (lam * x) * (c₀ ^ 2 * n ^ (2 * a) * κj ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (c₀ ^ 2 * x * n ^ (2 * a)) * (κj ^ 2 * lam) := by ring
        _ ≤ (c₀ ^ 2 * x * n ^ (2 * a)) * D := mul_le_mul_of_nonneg_left hD' (by positivity)
    have hc2 : 1 ≤ c₀ ^ 2 := by nlinarith
    rcases le_total T n with hTn | hnT
    · calc lam * x / D ≤ lam := hs1
        _ = n ^ (-q) := by simp only [lam, hq]; congr 1; ring
        _ ≤ 2 ^ q * (T + n) ^ (-q) := key n hn0 (by linarith)
        _ ≤ c₀ ^ 2 * 2 ^ q * (T + n) ^ (-q) := by
            rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) hc2
    · calc lam * x / D ≤ c₀ ^ 2 * x * n ^ (2 * a) := hs2
        _ ≤ c₀ ^ 2 * x * T ^ (2 * a) := by
            gcongr
        _ = c₀ ^ 2 * T ^ (-q) := by
            rw [hxT, mul_assoc, ← Real.rpow_add hT0]; congr 2; rw [hp, hq]; ring
        _ ≤ c₀ ^ 2 * (2 ^ q * (T + n) ^ (-q)) := by
            gcongr; exact key T hT0 (by linarith)
        _ = _ := by ring


/-- Uniform bound on the expected posterior squared distance over the Sobolev ellipsoid:
at most `(c₀² R² + c₀² 2^{1+2β}/β) (ε²)^r` with `r = 2β/(2β+2a+1)`. -/
theorem tsum_gaussianSeqPosterior_risk_le {a β R c₀ : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
    (hc₀ : 1 ≤ c₀) {κ : ℕ → ℝ} (hκ : HasPolynomialSingularValues κ a c₀) {ε : ℝ} (hε : 0 < ε)
    {f₀ : ℕ → ℝ} (hf₀ : f₀ ∈ inverseProblemSobolevBall β R) :
    ∑' j : ℕ, ENNReal.ofReal
        ((((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j / (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) *
            (κ j * f₀ j) - f₀ j) ^ 2 +
          (((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) ^ 2 * ε ^ 2 +
          ((j : ℝ) + 1) ^ (-1 - 2 * β) * ε ^ 2 /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) ≤
      ENNReal.ofReal ((c₀ ^ 2 * R ^ 2 + c₀ ^ 2 * 2 ^ (1 + 2 * β) / β) *
        (ε ^ 2) ^ (2 * β / (2 * β + 2 * a + 1))) := by
  set x := ε ^ 2 with hxdef
  have hx : 0 < x := by positivity
  set p := 2 * β + 2 * a + 1 with hp
  set r := 2 * β / p with hr
  set q := 1 + 2 * β with hq
  set T := x ^ (-1 / p) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hx _
  have hp0 : 0 < p := by positivity
  have hxr : 0 ≤ x ^ r := Real.rpow_nonneg hx.le _
  have hpt (j : ℕ) : ENNReal.ofReal
        ((((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j / (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + x) *
            (κ j * f₀ j) - f₀ j) ^ 2 +
          (((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + x)) ^ 2 * x +
          ((j : ℝ) + 1) ^ (-1 - 2 * β) * x /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + x)) ≤
      ENNReal.ofReal (c₀ ^ 2 * x ^ r) * ENNReal.ofReal (((j : ℝ) + 1) ^ (2 * β) * f₀ j ^ 2) +
        ENNReal.ofReal (2 * (c₀ ^ 2 * 2 ^ q)) * ENNReal.ofReal ((T + (j + 1)) ^ (-q)) := by
    have h := gaussianSeqPosterior_term_le ha hβ hc₀ hx
      (by have := Nat.cast_nonneg (α := ℝ) j; linarith : (1 : ℝ) ≤ (j : ℝ) + 1) (hκ j)
    dsimp only at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + x) * (κ j * f₀ j) - f₀ j =
        (((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
        (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + x) * κ j - 1) * f₀ j := by ring
    rw [e, mul_pow]
    have h1' := mul_le_mul_of_nonneg_right h1 (sq_nonneg (f₀ j))
    rw [← hp, ← hr] at h1'
    rw [← hp, ← hq] at h3
    have e2 : -(1 + 2 * β) = -q := by rw [hq]
    rw [e2] at h3
    nlinarith
  calc _ ≤ ∑' j : ℕ, (ENNReal.ofReal (c₀ ^ 2 * x ^ r) *
          ENNReal.ofReal (((j : ℝ) + 1) ^ (2 * β) * f₀ j ^ 2) +
        ENNReal.ofReal (2 * (c₀ ^ 2 * 2 ^ q)) * ENNReal.ofReal ((T + (j + 1)) ^ (-q))) :=
        tsum_le_tsum hpt
    _ = ENNReal.ofReal (c₀ ^ 2 * x ^ r) *
          ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) ^ (2 * β) * f₀ j ^ 2) +
        ENNReal.ofReal (2 * (c₀ ^ 2 * 2 ^ q)) * ∑' j : ℕ, ENNReal.ofReal ((T + (j + 1)) ^ (-q)) := by
        rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (c₀ ^ 2 * x ^ r) * ENNReal.ofReal (R ^ 2) +
        ENNReal.ofReal (2 * (c₀ ^ 2 * 2 ^ q)) * ENNReal.ofReal (T ^ (1 - q) / (q - 1)) := by
        gcongr
        · exact hf₀
        · exact tsum_ofReal_rpow_add_le hT0 (by rw [hq]; linarith)
    _ = _ := by
        have hTq : T ^ (1 - q) = x ^ r := by
          rw [hT, ← Real.rpow_mul hx.le, hr, hq]; congr 1; field_simp; ring
        have hq1 : q - 1 = 2 * β := by rw [hq]; ring
        rw [hTq, hq1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hq]; field_simp


/-- GAPS 104.20: uniform posterior contraction at the minimax rate for the Gaussian prior
`fⱼ ∼ N(0, j^{-1-2β})` matched to the Sobolev smoothness, for every `M_ε → ∞`. -/
theorem tendsto_gaussianSeqPosterior_contraction (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (hR : 0 < R) (hc₀ : 1 ≤ c₀) (κ : ℕ → ℝ) (hκ : HasPolynomialSingularValues κ a c₀)
    (M : ℝ → ℝ) (hM : Tendsto M (𝓝[>] 0) atTop) :
    let r := 2 * β / (2 * β + 2 * a + 1)
    Tendsto (fun ε ↦ ⨆ f₀ ∈ inverseProblemSobolevBall β R,
        ∫⁻ y, gaussianSeqPosterior κ β ε y
          {f | ENNReal.ofReal ((M ε * ε ^ r) ^ 2) ≤ seqDistSq f f₀} ∂inverseProblemLaw κ ε f₀)
      (𝓝[>] 0) (𝓝 0) := by
  intro r
  set C₁ := c₀ ^ 2 * R ^ 2 + c₀ ^ 2 * 2 ^ (1 + 2 * β) / β with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ f₀ ∈ inverseProblemSobolevBall β R,
        ∫⁻ y, gaussianSeqPosterior κ β ε y
          {f | ENNReal.ofReal ((M ε * ε ^ r) ^ 2) ≤ seqDistSq f f₀} ∂inverseProblemLaw κ ε f₀) ≤
      ENNReal.ofReal (C₁ / M ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hM.eventually_gt_atTop 0] with ε hε hMε
    have hε : 0 < ε := hε
    refine iSup₂_le fun f₀ hf₀ ↦ ?_
    have hεr : 0 < ε ^ r := Real.rpow_pos_of_pos hε _
    set c := ENNReal.ofReal ((M ε * ε ^ r) ^ 2) with hc
    have hc0 : c ≠ 0 := by
      rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hmeas : Measurable fun f : ℕ → ℝ ↦ seqDistSq f f₀ :=
      Measurable.tsum fun j ↦ by fun_prop
    have hsq : (ε ^ r) ^ 2 = (ε ^ 2) ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hε.le,
        ← Real.rpow_mul hε.le, mul_comm]
    calc ∫⁻ y, gaussianSeqPosterior κ β ε y {f | c ≤ seqDistSq f f₀} ∂inverseProblemLaw κ ε f₀
        ≤ ∫⁻ y, (∫⁻ f, seqDistSq f f₀ ∂gaussianSeqPosterior κ β ε y) * c⁻¹
            ∂inverseProblemLaw κ ε f₀ :=
          lintegral_mono fun y ↦ (meas_ge_le_lintegral_div hmeas.aemeasurable hc0
            ENNReal.ofReal_ne_top).trans_eq (div_eq_mul_inv _ _)
      _ = (∫⁻ y, ∫⁻ f, seqDistSq f f₀ ∂gaussianSeqPosterior κ β ε y
            ∂inverseProblemLaw κ ε f₀) * c⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)
      _ ≤ ENNReal.ofReal (C₁ * (ε ^ 2) ^ r) * c⁻¹ := by
          rw [lintegral_lintegral_seqDistSq_gaussianSeqPosterior κ β hε f₀]
          gcongr
          exact tsum_gaussianSeqPosterior_risk_le ha hβ hc₀ hκ hε hf₀
      _ = ENNReal.ofReal (C₁ / M ε ^ 2) := by
          rw [← div_eq_mul_inv, hc, ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          rw [mul_pow, hsq]
          have : 0 < (ε ^ 2) ^ r := Real.rpow_pos_of_pos (by positivity) _
          field_simp
  have hlim : Tendsto (fun ε ↦ ENNReal.ofReal (C₁ / M ε ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε ↦ C₁ / M ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hM)
    simpa using ENNReal.tendsto_ofReal h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) hbound

end CKSD
