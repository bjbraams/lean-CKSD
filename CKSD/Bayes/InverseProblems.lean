module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.Probability.Independence.DisjointBlocks


/-!
# Linear inverse problems in sequence space

The white-noise model `Y = Af + εW` for a compact injective operator with singular system
`A eⱼ = κⱼ gⱼ` is written in its equivalent sequence form `Yⱼ = κⱼ fⱼ + ε Zⱼ`. Coordinates are
indexed from `0`, the coordinate `j` standing for the index `j + 1` of the singular system.
Squared `ℓ²` distances are taken in `ℝ≥0∞`, so that the risks and the Sobolev ellipsoid are
meaningful for arbitrary sequences. The Gaussian-prior posterior is written in its conjugate
closed form, coordinatewise independent normal.

The minimax upper bound uses the posterior mean. The lower bound is Assouad's argument over a
hypercube on the coordinates `J, …, 2J - 1`, `J ≍ ε^{-2/(2β+2a+1)}`: coordinate `j` of the
infinite product is split off with the block independence of TauCeti's
`indepFun_of_measurable_blockSigma`, and two normal laws whose means differ by at most `ε` have
overlap at least `2e^{-2}/√(2π)`.

## Main definitions

* `CKSD.inverseProblemLaw κ ε f`: the law of the sequence observation `Yⱼ = κⱼ fⱼ + ε Zⱼ`.
* `CKSD.inverseProblemRisk`, `CKSD.inverseProblemSobolevBall`: the squared `ℓ²` risk of an
  estimator and the Sobolev ellipsoid `∑ⱼ (j + 1)^{2β} fⱼ² ≤ R²`.
* `CKSD.gaussianSeqPosterior κ β ε y`: the posterior under the Gaussian prior
  `fⱼ ∼ N(0, (j + 1)^{-1-2β})`.

## Main results

* `CKSD.exists_minimax_rate_inverse_problem`: the minimax rate `ε^{2β/(2β+2a+1)}`.
* `CKSD.tendsto_gaussian_seq_posterior_contraction`: posterior contraction of the Gaussian-prior
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

/-- Second moment of an affine function under a normal law, in `ℝ≥0∞`:
`∫⁻ ((c X - d)² + s) = (cμ - d)² + c² v + s` for `X ∼ N(μ, v)` and `s ≥ 0`. -/
theorem lintegral_of_real_sq_add_gaussian_real (c d μ : ℝ) (v : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
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
theorem tsum_of_real_rpow_add_le {T q : ℝ} (hT : 0 < T) (hq : 1 < q) :
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
theorem lintegral_lintegral_seq_dist_sq_gaussian_seq_posterior (κ : ℕ → ℝ) (β : ℝ) {ε : ℝ}
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
    have h2 := lintegral_of_real_sq_add_gaussian_real 1 (f₀ j)
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
  rw [inverseProblemLaw, this, lintegral_of_real_sq_add_gaussian_real _ _ _ _ (hs0 j),
    Real.coe_toNNReal _ (by positivity)]


/-- Coordinatewise bounds for the Gaussian sequence posterior with `x = ε²` and `n = j + 1`:
the squared relative bias is at most `c₀² x^r n^{2β}`, the variance of the posterior mean is at
most the posterior variance, and the posterior variance is at most `c₀² 2^{1+2β} (T + n)^{-(1+2β)}`
with `T = x^{-1/(2β+2a+1)}`. -/
theorem gaussian_seq_posterior_term_le {a β c₀ κj x n : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
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
theorem tsum_gaussian_seq_posterior_risk_le {a β R c₀ : ℝ} (ha : 0 ≤ a) (hβ : 0 < β)
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
    have h := gaussian_seq_posterior_term_le ha hβ hc₀ hx
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
        · exact tsum_of_real_rpow_add_le hT0 (by rw [hq]; linarith)
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
theorem tendsto_gaussian_seq_posterior_contraction (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
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
          rw [lintegral_lintegral_seq_dist_sq_gaussian_seq_posterior κ β hε f₀]
          gcongr
          exact tsum_gaussian_seq_posterior_risk_le ha hβ hc₀ hκ hε hf₀
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

/-- Under an infinite product of probability measures on `ℝ`, coordinate `j` and the remaining
coordinates are independent: their joint law is `μ j ⊗ ∏_{i ≠ j} μ i`. The argument follows
TauCeti's `infinitePi_map_none_some`. -/
private theorem map_infinite_pi_eval_restrict_ne (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (j : ℕ) :
    (Measure.infinitePi μ).map (fun x ↦ (x j, fun i : {i // i ≠ j} ↦ x i)) =
      (μ j).prod (Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i) := by
  have hind : IndepFun (fun x : ℕ → ℝ ↦ x j) (fun x (i : {i // i ≠ j}) ↦ x i)
      (Measure.infinitePi μ) :=
    TauCeti.Probability.indepFun_of_measurable_blockSigma (S := {j}) (T := {i | i ≠ j})
      (Z := fun i (x : ℕ → ℝ) ↦ x i)
      ((iIndepFun_infinitePi (X := fun _ y ↦ y) fun _ ↦ measurable_id).precomp
        Subtype.val_injective)
      (fun i _ ↦ measurable_pi_apply i)
      (Set.disjoint_singleton_left.mpr fun h ↦ h rfl)
      (TauCeti.Probability.measurable_blockSigma_of_mem (Z := fun i (x : ℕ → ℝ) ↦ x i)
        (S := {j}) (i := j) rfl)
      (@Measurable.of_eval _ _ _ (TauCeti.Probability.blockSigma _ _) _ _ fun i ↦
        TauCeti.Probability.measurable_blockSigma_of_mem (Z := fun i (x : ℕ → ℝ) ↦ x i)
          (i := i.1) i.2)
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
      (Measurable.of_eval fun i ↦ measurable_pi_apply _).aemeasurable,
    Measure.infinitePi_map_eval, Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

/-- Reassemble a sequence from its coordinate `j` and the remaining coordinates. -/
private def joinAt (j : ℕ) (y : ℝ) (r : {i // i ≠ j} → ℝ) : ℕ → ℝ :=
  fun i ↦ if h : i = j then y else r ⟨i, h⟩

/-- Reassembling a sequence from coordinate `j` and the remaining coordinates is measurable. -/
private theorem measurable_join_at (j : ℕ) :
    Measurable fun z : ℝ × ({i // i ≠ j} → ℝ) ↦ joinAt j z.1 z.2 := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  by_cases h : i = j
  · simp only [joinAt, h, ↓reduceDIte]; exact measurable_fst
  · simp only [joinAt, h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_snd

/-- Tonelli over an infinite product, integrating coordinate `j` innermost. -/
private theorem lintegral_infinite_pi_eq_lintegral_join_at (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (j : ℕ) {F : (ℕ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂Measure.infinitePi μ =
      ∫⁻ r, ∫⁻ y, F (joinAt j y r) ∂μ j ∂Measure.infinitePi fun i : {i // i ≠ j} ↦ μ i := by
  have hsplit : Measurable fun x : ℕ → ℝ ↦ (x j, fun i : {i // i ≠ j} ↦ x i) :=
    (measurable_pi_apply j).prodMk (Measurable.of_eval fun i ↦ measurable_pi_apply _)
  have hj : ∀ x : ℕ → ℝ, joinAt j (x j) (fun i : {i // i ≠ j} ↦ x i) = x := by
    intro x; funext i; by_cases h : i = j
    · subst h; simp [joinAt]
    · simp [joinAt, h]
  calc ∫⁻ x, F x ∂Measure.infinitePi μ
      = ∫⁻ x, F (joinAt j (x j) (fun i : {i // i ≠ j} ↦ x i)) ∂Measure.infinitePi μ := by
        simp_rw [hj]
    _ = ∫⁻ z, F (joinAt j z.1 z.2) ∂(Measure.infinitePi μ).map
          (fun x ↦ (x j, fun i : {i // i ≠ j} ↦ x i)) :=
        (lintegral_map (hF.comp (measurable_join_at j)) hsplit).symm
    _ = _ := by
        rw [map_infinite_pi_eval_restrict_ne]
        exact lintegral_prod_symm (fun z ↦ F (joinAt j z.1 z.2))
          (hF.comp (measurable_join_at j)).aemeasurable


/-- Lower bound for the normal density on `[m - ε, m + ε]` when `|m - m'| ≤ ε`. -/
private theorem le_gaussian_pdf_real_of_mem_icc {m m' ε y : ℝ} (hε : 0 < ε) (hm : |m - m'| ≤ ε)
    (hy : y ∈ Icc (m - ε) (m + ε)) :
    (√(2 * Real.pi * (ε ^ 2).toNNReal))⁻¹ * Real.exp (-2) ≤
      gaussianPDFReal m' (ε ^ 2).toNNReal y := by
  rw [gaussianPDFReal]
  gcongr
  rw [Real.coe_toNNReal _ (sq_nonneg ε), le_div_iff₀ (by positivity)]
  have h1 : |y - m'| ≤ 2 * ε := by
    have : |y - m| ≤ ε := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc |y - m'| = |(y - m) + (m - m')| := by ring_nf
      _ ≤ |y - m| + |m - m'| := abs_add_le _ _
      _ ≤ 2 * ε := by linarith
  have h2 : (y - m') ^ 2 ≤ (2 * ε) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

/-- Two-point lower bound in the one-dimensional normal location model with variance `ε²`:
for means at distance at most `ε`, the sum of the squared risks of `u` for the targets `c` and
`c'` under the two laws is at least `(c - c')²/2 · 2e^{-2}/√(2π)`. -/
private theorem le_lintegral_add_lintegral_gaussian_real {m m' ε : ℝ} (hε : 0 < ε)
    (hm : |m - m'| ≤ ε) {u : ℝ → ℝ} (hu : Measurable u) (c c' : ℝ) :
    ENNReal.ofReal ((c - c') ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi))) ≤
      ∫⁻ y, ENNReal.ofReal ((u y - c) ^ 2) ∂gaussianReal m (ε ^ 2).toNNReal +
        ∫⁻ y, ENNReal.ofReal ((u y - c') ^ 2) ∂gaussianReal m' (ε ^ 2).toNNReal := by
  have hv : (ε ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  set K : ℝ := (√(2 * Real.pi * (ε ^ 2).toNNReal))⁻¹ * Real.exp (-2) with hK
  have hK0 : 0 ≤ K := by positivity
  set I := Icc (m - ε) (m + ε) with hI
  have hmm : |m - m| ≤ ε := by simpa using hε.le
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop),
    ← lintegral_add_left ((measurable_gaussianPDF _ _).mul (by fun_prop))]
  calc ENNReal.ofReal ((c - c') ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi)))
      = ∫⁻ _ in I, ENNReal.ofReal (K * ((c - c') ^ 2 / 2)) := by
        rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hK, Real.coe_toNNReal _ (sq_nonneg ε), Real.sqrt_mul' _ (sq_nonneg ε),
          Real.sqrt_sq hε.le]
        field_simp
        ring
    _ ≤ ∫⁻ y in I, ((gaussianPDF m (ε ^ 2).toNNReal * fun y ↦ ENNReal.ofReal ((u y - c) ^ 2)) +
          (gaussianPDF m' (ε ^ 2).toNNReal * fun y ↦ ENNReal.ofReal ((u y - c') ^ 2))) y := by
        refine setLIntegral_mono' measurableSet_Icc fun y hy ↦ ?_
        simp only [Pi.add_apply, Pi.mul_apply, gaussianPDF]
        rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
          ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
          ← ENNReal.ofReal_add (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _))
            (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _))]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := le_gaussian_pdf_real_of_mem_icc hε hmm hy
        have h2 := le_gaussian_pdf_real_of_mem_icc hε hm hy
        have h3 : (c - c') ^ 2 / 2 ≤ (u y - c) ^ 2 + (u y - c') ^ 2 := by
          nlinarith [sq_nonneg (2 * u y - c - c')]
        nlinarith [sq_nonneg (u y - c), sq_nonneg (u y - c'), mul_le_mul_of_nonneg_left h3 hK0]
    _ ≤ _ := setLIntegral_le_lintegral _ _


/-- Two-point lower bound in the Gaussian sequence model: if the truths `f` and `f'` differ only
in coordinate `j` and the means of that coordinate are at distance at most `ε`, every estimator
`h` of coordinate `j` has summed squared risks at least `(f_j - f'_j)²/2 · 2e^{-2}/√(2π)`. -/
private theorem le_lintegral_add_lintegral_inverse_problem_law (κ : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (j : ℕ) {f f' : ℕ → ℝ} (hoff : ∀ i ≠ j, f i = f' i)
    (hshift : |κ j * f j - κ j * f' j| ≤ ε) {h : (ℕ → ℝ) → ℝ} (hh : Measurable h) :
    ENNReal.ofReal ((f j - f' j) ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi))) ≤
      ∫⁻ y, ENNReal.ofReal ((h y - f j) ^ 2) ∂inverseProblemLaw κ ε f +
        ∫⁻ y, ENNReal.ofReal ((h y - f' j) ^ 2) ∂inverseProblemLaw κ ε f' := by
  have hrest : (fun i : {i // i ≠ j} ↦ gaussianReal (κ i * f' i) (ε ^ 2).toNNReal) =
      fun i : {i // i ≠ j} ↦ gaussianReal (κ i * f i) (ε ^ 2).toNNReal := by
    funext i; rw [hoff i i.2]
  have hF (c : ℝ) : Measurable fun y : ℕ → ℝ ↦ ENNReal.ofReal ((h y - c) ^ 2) := by fun_prop
  have hG (c : ℝ) : Measurable fun z : ℝ × ({i // i ≠ j} → ℝ) ↦
      ENNReal.ofReal ((h (joinAt j z.1 z.2) - c) ^ 2) := (hF c).comp (measurable_join_at j)
  rw [inverseProblemLaw, inverseProblemLaw,
    lintegral_infinite_pi_eq_lintegral_join_at _ j (hF _),
    lintegral_infinite_pi_eq_lintegral_join_at _ j (hF _), hrest,
    ← lintegral_add_left ((hG _).lintegral_prod_left')]
  calc ENNReal.ofReal ((f j - f' j) ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi)))
      = ∫⁻ _, ENNReal.ofReal ((f j - f' j) ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi)))
          ∂Measure.infinitePi fun i : {i // i ≠ j} ↦ gaussianReal (κ i * f i) (ε ^ 2).toNNReal := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono fun r ↦
        le_lintegral_add_lintegral_gaussian_real hε hshift
          (hh.comp ((measurable_join_at j).comp (measurable_id.prodMk measurable_const))) _ _


/-- The hypercube of sequences supported on the coordinates `J, …, 2J - 1`, with value `δ` or `0`
at `J + k` according to `ω k`. -/
private def hypercubeSeq (J : ℕ) (δ : ℝ) (ω : Fin J → Bool) : ℕ → ℝ :=
  fun i ↦ if h : J ≤ i ∧ i < 2 * J then (if ω ⟨i - J, by omega⟩ then δ else 0) else 0

/-- The hypercube sequence at coordinate `J + k` is `δ` or `0` according to `ω k`. -/
private theorem hypercube_seq_add (J : ℕ) (δ : ℝ) (ω : Fin J → Bool) (k : Fin J) :
    hypercubeSeq J δ ω (J + k) = if ω k then δ else 0 := by
  have h : J ≤ J + k.val ∧ J + k.val < 2 * J := ⟨by omega, by omega⟩
  have hk : (⟨J + k.val - J, by omega⟩ : Fin J) = k := Fin.ext (by simp)
  simp only [hypercubeSeq, h, and_self, ↓reduceDIte, hk]

/-- Flipping the bit `k` changes the hypercube sequence only in coordinate `J + k`. -/
private theorem hypercube_seq_update_of_ne (J : ℕ) (δ : ℝ) (ω : Fin J → Bool) (k : Fin J)
    (b : Bool) {i : ℕ} (hi : i ≠ J + k) :
    hypercubeSeq J δ ω i = hypercubeSeq J δ (Function.update ω k b) i := by
  unfold hypercubeSeq
  by_cases h : J ≤ i ∧ i < 2 * J
  · have hne : (⟨i - J, by omega⟩ : Fin J) ≠ k := by
      intro e; apply hi; rw [← e]; simp only; omega
    simp only [h, and_self, ↓reduceDIte, Function.update_of_ne hne]
  · simp only [h, ↓reduceDIte]

/-- Averaging over the hypercube: if every pair `ω`, `ω` with bit `k` flipped has summed values
at least `D`, the sum over the hypercube is at least `2^J D / 2`. -/
private theorem pow_mul_le_two_mul_sum {J : ℕ} (k : Fin J) (g : (Fin J → Bool) → ℝ≥0∞)
    (D : ℝ≥0∞) (h : ∀ ω, D ≤ g ω + g (Function.update ω k (!ω k))) :
    2 ^ J * D ≤ 2 * ∑ ω, g ω := by
  let e : (Fin J → Bool) ≃ (Fin J → Bool) :=
    { toFun := fun ω ↦ Function.update ω k (!ω k)
      invFun := fun ω ↦ Function.update ω k (!ω k)
      left_inv := fun ω ↦ by simp
      right_inv := fun ω ↦ by simp }
  have hsum : ∑ ω, g (Function.update ω k (!ω k)) = ∑ ω, g ω := Fintype.sum_equiv e _ _ fun _ ↦ rfl
  calc 2 ^ J * D = ∑ _ω : Fin J → Bool, D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        norm_cast
    _ ≤ ∑ ω, (g ω + g (Function.update ω k (!ω k))) := Finset.sum_le_sum fun ω _ ↦ h ω
    _ = 2 * ∑ ω, g ω := by rw [Finset.sum_add_distrib, hsum, two_mul]


/-- Assouad's lower bound over the hypercube `hypercubeSeq J δ` in the Gaussian sequence model:
if the hypercube lies in the Sobolev ellipsoid and each flip moves a mean by at most `ε`, every
measurable estimator has worst-case squared risk at least `J δ²/4 · 2e^{-2}/√(2π)`. -/
private theorem le_i_sup_inverse_problem_risk_of_hypercube (κ : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (β R : ℝ) (J : ℕ) (δ : ℝ) (hshift : ∀ k : Fin J, |κ (J + k) * δ| ≤ ε)
    (hball : ∀ ω, hypercubeSeq J δ ω ∈ inverseProblemSobolevBall β R)
    {fhat : (ℕ → ℝ) → ℕ → ℝ} (hfhat : Measurable fhat) :
    ENNReal.ofReal (J * (δ ^ 2 / 2 * (2 * Real.exp (-2) / √(2 * Real.pi))) / 2) ≤
      ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f := by
  set S := ⨆ f ∈ inverseProblemSobolevBall β R, inverseProblemRisk κ ε fhat f with hS
  set A₀ : ℝ := 2 * Real.exp (-2) / √(2 * Real.pi) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set D := ENNReal.ofReal (δ ^ 2 / 2 * A₀) with hD
  let g : Fin J → (Fin J → Bool) → ℝ≥0∞ := fun k ω ↦
    ∫⁻ y, ENNReal.ofReal ((fhat y (J + k) - hypercubeSeq J δ ω (J + k)) ^ 2)
      ∂inverseProblemLaw κ ε (hypercubeSeq J δ ω)
  have hpair (k : Fin J) (ω : Fin J → Bool) : D ≤ g k ω + g k (Function.update ω k (!ω k)) := by
    have h := le_lintegral_add_lintegral_inverse_problem_law κ hε (J + k)
      (f := hypercubeSeq J δ ω) (f' := hypercubeSeq J δ (Function.update ω k (!ω k)))
      (fun i hi ↦ hypercube_seq_update_of_ne J δ ω k _ hi)
      (by
        rw [hypercube_seq_add, hypercube_seq_add, Function.update_self]
        cases ω k <;> simpa [abs_mul] using hshift k)
      ((measurable_pi_apply (J + k.val)).comp hfhat)
    have e : (hypercubeSeq J δ ω (J + k) -
        hypercubeSeq J δ (Function.update ω k (!ω k)) (J + k)) ^ 2 = δ ^ 2 := by
      rw [hypercube_seq_add, hypercube_seq_add, Function.update_self]
      cases ω k <;> simp
    rw [e] at h
    exact h
  have hrisk (ω : Fin J → Bool) :
      ∑ k, g k ω ≤ inverseProblemRisk κ ε fhat (hypercubeSeq J δ ω) := by
    rw [inverseProblemRisk, ← lintegral_finsetSum _ fun k _ ↦ by fun_prop]
    refine lintegral_mono fun y ↦ ?_
    rw [seqDistSq]
    calc ∑ k : Fin J, ENNReal.ofReal ((fhat y (J + k) - hypercubeSeq J δ ω (J + k)) ^ 2)
        = ∑' k : Fin J, ENNReal.ofReal ((fhat y (J + k) - hypercubeSeq J δ ω (J + k)) ^ 2) :=
          (tsum_fintype _).symm
      _ ≤ _ := tsum_comp_le_tsum_of_injective (f := fun k : Fin J ↦ J + k.val)
          (fun a b hab ↦ Fin.ext (by simpa using hab))
          (fun i ↦ ENNReal.ofReal ((fhat y i - hypercubeSeq J δ ω i) ^ 2))
  have hle (ω : Fin J → Bool) : inverseProblemRisk κ ε fhat (hypercubeSeq J δ ω) ≤ S :=
    le_iSup₂ (f := fun f _ ↦ inverseProblemRisk κ ε fhat f) (hypercubeSeq J δ ω) (hball ω)
  have hmain : 2 ^ J * (J * D) ≤ 2 ^ J * (2 * S) := by
    calc 2 ^ J * (J * D) = ∑ _k : Fin J, 2 ^ J * D := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ k : Fin J, 2 * ∑ ω, g k ω :=
          Finset.sum_le_sum fun k _ ↦ pow_mul_le_two_mul_sum k (g k) D (hpair k)
      _ = 2 * ∑ ω, ∑ k, g k ω := by rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * ∑ _ω : Fin J → Bool, S := by
          gcongr with ω; exact (hrisk ω).trans (hle ω)
      _ = 2 ^ J * (2 * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have h2 : (J : ℝ≥0∞) * D ≤ 2 * S :=
    (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).mp hmain
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, ← hD, ENNReal.ofReal_ofNat]
  exact ENNReal.div_le_of_le_mul (by rwa [mul_comm S])


/-- The posterior mean `λⱼκⱼYⱼ / (κⱼ²λⱼ + ε²)` under the prior `fⱼ ∼ N(0, j^{-1-2β})`. -/
private def gaussianSeqPosteriorMean (κ : ℕ → ℝ) (β ε : ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun j ↦ ((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
    (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) * y j

/-- The risk of the posterior mean is the sum of squared biases and variances, and so is at most
the expected posterior squared distance. -/
private theorem inverse_problem_risk_gaussian_seq_posterior_mean_le (κ : ℕ → ℝ) (β : ℝ) {ε : ℝ}
    (hε : 0 < ε) (f₀ : ℕ → ℝ) :
    inverseProblemRisk κ ε (gaussianSeqPosteriorMean κ β ε) f₀ ≤
      ∑' j : ℕ, ENNReal.ofReal
        ((((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j / (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) *
            (κ j * f₀ j) - f₀ j) ^ 2 +
          (((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) ^ 2 * ε ^ 2 +
          ((j : ℝ) + 1) ^ (-1 - 2 * β) * ε ^ 2 /
            (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2)) := by
  set m : ℕ → ℝ := fun j ↦ ((j : ℝ) + 1) ^ (-1 - 2 * β) * κ j /
    (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) with hm
  simp only [inverseProblemRisk, seqDistSq]
  rw [lintegral_tsum fun j ↦ Measurable.aemeasurable (by
    simp only [gaussianSeqPosteriorMean]; fun_prop)]
  refine tsum_le_tsum fun j ↦ ?_
  have hg : Measurable fun x : ℝ ↦ ENNReal.ofReal ((m j * x - f₀ j) ^ 2 + 0) := by fun_prop
  have := (measurePreserving_eval_infinitePi (fun i : ℕ ↦
    gaussianReal (κ i * f₀ i) (ε ^ 2).toNNReal) j).lintegral_comp hg
  simp only [add_zero, Function.eval] at this
  simp only [gaussianSeqPosteriorMean]
  rw [inverseProblemLaw, this]
  have h2 := lintegral_of_real_sq_add_gaussian_real (m j) (f₀ j) (κ j * f₀ j) (ε ^ 2).toNNReal
    le_rfl
  simp only [add_zero] at h2
  rw [h2, Real.coe_toNNReal _ (sq_nonneg ε)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 0 ≤ ((j : ℝ) + 1) ^ (-1 - 2 * β) * ε ^ 2 /
      (κ j ^ 2 * ((j : ℝ) + 1) ^ (-1 - 2 * β) + ε ^ 2) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) (-1 - 2 * β)
    positivity
  simp only [hm]
  linarith

/-- The posterior mean is a measurable estimator. -/
private theorem measurable_gaussian_seq_posterior_mean (κ : ℕ → ℝ) (β ε : ℝ) :
    Measurable (gaussianSeqPosteriorMean κ β ε) :=
  Measurable.of_eval fun j ↦ (measurable_pi_apply j).const_mul _

/-- GAPS 104.20: the minimax `ℓ²` rate over a Sobolev ellipsoid in a mildly ill-posed linear
inverse problem is `ε^r` with `r = 2β/(2β+2a+1)`. There are constants `0 < c ≤ C`, depending only
on `a`, `β`, `R`, and `c₀`, such that for every operator with polynomially decaying singular values
and every noise level `ε ∈ (0, 1]` some measurable estimator has worst-case squared risk at most
`(C ε^r)²` and every measurable estimator has worst-case squared risk at least `(c ε^r)²`. -/
theorem exists_minimax_rate_inverse_problem (a β R c₀ : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
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
  intro r
  set p := 2 * β + 2 * a + 1 with hp
  have hp0 : 0 < p := by positivity
  set C₁ := c₀ ^ 2 * R ^ 2 + c₀ ^ 2 * 2 ^ (1 + 2 * β) / β with hC₁
  set A₀ : ℝ := 2 * Real.exp (-2) / √(2 * Real.pi) with hA₀
  have hA₀0 : 0 < A₀ := by positivity
  set η : ℝ := min (R * 2 ^ (-β)) c₀⁻¹ with hη
  have hc₀0 : 0 < c₀ := one_pos.trans_le hc₀
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  set c : ℝ := √(A₀ * η ^ 2 * 2 ^ (-2 * β) / 4) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  refine ⟨c, max c √C₁, hc0, le_max_left _ _, fun κ hκ ε hε ↦ ⟨?_, ?_⟩⟩
  · refine ⟨gaussianSeqPosteriorMean κ β ε, measurable_gaussian_seq_posterior_mean κ β ε, ?_⟩
    refine iSup₂_le fun f hf ↦ ?_
    refine (inverse_problem_risk_gaussian_seq_posterior_mean_le κ β hε.1 f).trans
      ((tsum_gaussian_seq_posterior_risk_le ha hβ hc₀ hκ hε.1 hf).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hεr : (ε ^ 2) ^ r = (ε ^ r) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hε.1.le,
        ← Real.rpow_mul hε.1.le, mul_comm]
    have hC₁0 : 0 ≤ C₁ := by positivity
    rw [hεr, mul_pow]
    gcongr
    calc C₁ = √C₁ ^ 2 := (Real.sq_sqrt hC₁0).symm
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · intro fhat hfhat
    have hε0 := hε.1
    set t : ℝ := ε ^ (-2 / p) with ht
    have ht1 : 1 ≤ t := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε.2
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
    have ht0 : 0 < t := one_pos.trans_le ht1
    set J : ℕ := ⌈t⌉₊ with hJ
    have htJ : t ≤ J := Nat.le_ceil t
    have hJt : (J : ℝ) ≤ 2 * t := by
      have := Nat.ceil_lt_add_one ht0.le; linarith
    have hJ0 : (0 : ℝ) < J := ht0.trans_le htJ
    set δ : ℝ := η * (J : ℝ) ^ (-(1 + 2 * β) / 2) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδsq : δ ^ 2 = η ^ 2 * (J : ℝ) ^ (-(1 + 2 * β)) := by
      rw [hδ, mul_pow, ← Real.rpow_natCast ((J : ℝ) ^ _), ← Real.rpow_mul hJ0.le]
      norm_num
    have hJδ : (J : ℝ) * δ ^ 2 = η ^ 2 * (J : ℝ) ^ (-(2 * β)) := by
      rw [hδsq, mul_left_comm, ← Real.rpow_one_add' hJ0.le (by
        have : (1 : ℝ) + -(1 + 2 * β) = -(2 * β) := by ring
        rw [this]; exact neg_ne_zero.mpr (by positivity))]
      ring_nf
    have hshift : ∀ k : Fin J, |κ (J + k) * δ| ≤ ε := by
      intro k
      obtain ⟨hlo, hhi⟩ := hκ (J + k)
      have hκ0 : 0 < κ (J + k) := lt_of_lt_of_le (by positivity) hlo
      have hJj : (J : ℝ) ≤ ((J + k : ℕ) : ℝ) + 1 := by
        push_cast; linarith [k.val.cast_nonneg (α := ℝ)]
      rw [abs_of_pos (mul_pos hκ0 hδ0)]
      calc κ (J + k) * δ ≤ c₀ * (J : ℝ) ^ (-a) * δ := by
            have hpow : (((J + k : ℕ) : ℝ) + 1) ^ (-a) ≤ (J : ℝ) ^ (-a) :=
              Real.rpow_le_rpow_of_nonpos hJ0 hJj (by linarith)
            exact mul_le_mul_of_nonneg_right (hhi.trans (mul_le_mul_of_nonneg_left hpow hc₀0.le))
              hδ0.le
        _ = (c₀ * η) * (J : ℝ) ^ (-p / 2) := by
            rw [hδ, hp, show -(2 * β + 2 * a + 1) / 2 = -a + -(1 + 2 * β) / 2 by ring,
              Real.rpow_add hJ0]
            ring
        _ ≤ 1 * t ^ (-p / 2) := by
            have hcη : c₀ * η ≤ 1 := by
              calc c₀ * η ≤ c₀ * c₀⁻¹ := by gcongr; exact min_le_right _ _
                _ = 1 := mul_inv_cancel₀ hc₀0.ne'
            exact mul_le_mul hcη (Real.rpow_le_rpow_of_nonpos ht0 htJ
                (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0.le) zero_le_two))
              (by positivity) zero_le_one
        _ = ε := by
            rw [one_mul, ht, ← Real.rpow_mul hε0.le]
            rw [show -2 / p * (-p / 2) = 1 by field_simp, Real.rpow_one]
    have hball : ∀ ω, hypercubeSeq J δ ω ∈ inverseProblemSobolevBall β R := by
      intro ω
      have hzero : ∀ i ∉ Finset.Ico J (2 * J),
          ENNReal.ofReal (((i : ℝ) + 1) ^ (2 * β) * hypercubeSeq J δ ω i ^ 2) = 0 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        simp [hypercubeSeq, hi]
      have hterm : ∀ i ∈ Finset.Ico J (2 * J),
          ENNReal.ofReal (((i : ℝ) + 1) ^ (2 * β) * hypercubeSeq J δ ω i ^ 2) ≤
            ENNReal.ofReal ((2 * J : ℝ) ^ (2 * β) * δ ^ 2) := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : hypercubeSeq J δ ω i ^ 2 ≤ δ ^ 2 := by
          unfold hypercubeSeq; split_ifs <;> simp [sq_nonneg]
        have hi2 : (i : ℝ) + 1 ≤ 2 * J := by
          have : i + 1 ≤ 2 * J := hi.2
          exact_mod_cast this
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hi2 (by positivity)) hsq
          (sq_nonneg _) (by positivity)
      simp only [inverseProblemSobolevBall, Set.mem_ofPred_eq]
      rw [tsum_eq_sum (s := Finset.Ico J (2 * J)) hzero]
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [Nat.card_Ico, nsmul_eq_mul, show 2 * J - J = J by omega, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hJJ : (J : ℝ) * (J : ℝ) ^ (2 * β) * (J : ℝ) ^ (-(1 + 2 * β)) = 1 := by
        rw [← Real.rpow_one_add' hJ0.le (by positivity), ← Real.rpow_add hJ0]
        norm_num
      have hval : (J : ℝ) * ((2 * J : ℝ) ^ (2 * β) * δ ^ 2) = 2 ^ (2 * β) * η ^ 2 := by
        rw [Real.mul_rpow (by norm_num) hJ0.le, hδsq]
        calc _ = 2 ^ (2 * β) * η ^ 2 *
              ((J : ℝ) * (J : ℝ) ^ (2 * β) * (J : ℝ) ^ (-(1 + 2 * β))) := by ring
          _ = _ := by rw [hJJ, mul_one]
      rw [hval]
      have hηR : η ≤ R * 2 ^ (-β) := min_le_left _ _
      calc 2 ^ (2 * β) * η ^ 2 ≤ 2 ^ (2 * β) * (R * 2 ^ (-β)) ^ 2 := by gcongr
        _ = R ^ 2 := by
          rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (-β)), ← Real.rpow_mul (by norm_num),
            mul_left_comm, ← Real.rpow_add (by norm_num),
            show 2 * β + -β * ((2 : ℕ) : ℝ) = 0 by push_cast; ring, Real.rpow_zero, mul_one]
    refine le_trans ?_ (le_i_sup_inverse_problem_risk_of_hypercube κ hε0 β R J δ hshift hball hfhat)
    refine ENNReal.ofReal_le_ofReal ?_
    have hrhs : (J : ℝ) * (δ ^ 2 / 2 * A₀) / 2 = A₀ * η ^ 2 / 4 * (J : ℝ) ^ (-(2 * β)) := by
      have := hJδ
      calc (J : ℝ) * (δ ^ 2 / 2 * A₀) / 2 = A₀ / 4 * ((J : ℝ) * δ ^ 2) := by ring
        _ = _ := by rw [this]; ring
    rw [← hA₀, hrhs, mul_pow, hc, Real.sq_sqrt (by positivity)]
    have hεr : (ε ^ r) ^ 2 = t ^ (-(2 * β)) := by
      rw [ht, ← Real.rpow_mul hε0.le, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
      congr 1
      simp only [r, hp]; push_cast; field_simp
    rw [hεr]
    have h2t : (J : ℝ) ^ (-(2 * β)) ≥ (2 * t) ^ (-(2 * β)) :=
      Real.rpow_le_rpow_of_nonpos hJ0 hJt (by linarith)
    rw [Real.mul_rpow (by norm_num) ht0.le] at h2t
    have : (2 : ℝ) ^ (-2 * β) = 2 ^ (-(2 * β)) := by ring_nf
    rw [this]
    have h0 : 0 ≤ A₀ * η ^ 2 / 4 := by positivity
    calc A₀ * η ^ 2 * 2 ^ (-(2 * β)) / 4 * t ^ (-(2 * β))
        = A₀ * η ^ 2 / 4 * (2 ^ (-(2 * β)) * t ^ (-(2 * β))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2t h0

end CKSD
