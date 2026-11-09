module

public import CKSD.Asymptotics.LipschitzChaining

/-!
# Uniform local expansion of the empirical process of a Lipschitz family

For an iid sample and a parameter family `θ ↦ f θ` that is Lipschitz near `θ₀` with a
square-integrable envelope and differentiable at `θ₀` with derivative `⟪s, ·⟫`, the rescaled
increments of the empirical process satisfy
`√n (Gₙ f(θ₀ + h/√n) - Gₙ f θ₀) = ⟪h, n^{-1/2} ∑ s(Xᵢ)⟫ + o_P(1)`, pointwise in `h` and
uniformly over bounded sets of `h`. This is the expansion used for M-estimators.

## Main results

* `CKSD.tendsto_sqrt_mul_sub_sub_inner`: the deterministic expansion of a differentiable function.
* `CKSD.empiricalProcess_inner`: the empirical process of a linear functional of the score.
* `CKSD.tendstoInMeasure_sqrt_mul_empiricalProcess_sub_sub_inner`: the pointwise expansion.
* `CKSD.tendsto_measureReal_exists_abs_sqrt_mul_empiricalProcess_sub_sub_inner`: the uniform
  expansion over `‖h‖ ≤ R`.

## References

van der Vaart, *Asymptotic Statistics*, Lemma 19.31. The uniform expansion covers a cube by
dyadic cells and applies the maximal inequality of `CKSD.Asymptotics.LipschitzChaining` in each
cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- If `φ` has derivative `⟪v, ·⟫` at `θ₀`, then `√n (φ(θ₀ + u/√n) - φ θ₀) → ⟪u, v⟫`. -/
theorem tendsto_sqrt_mul_sub_sub_inner {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ₀ v : EuclideanSpace ℝ (Fin d)} (hφ : HasFDerivAt φ (innerSL ℝ v) θ₀)
    (u : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (φ (θ₀ + (Real.sqrt n)⁻¹ • u) - φ θ₀) - inner ℝ u v)
      atTop (𝓝 0) := by
  have h := (hφ.hasLineDerivAt u).tendsto_slope_zero_right
  have ht : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact inv_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have := (h.comp ht).sub_const (inner ℝ u v)
  have e : (innerSL ℝ v) u - inner ℝ u v = 0 := by
    rw [innerSL_apply_apply, real_inner_comm, sub_self]
  rw [e] at this
  refine this.congr' ?_
  filter_upwards with n
  simp [smul_eq_mul, inv_inv]

/-- Linear functionals of a square-integrable centred vector: the empirical process of `⟪u, s⟫`
is `⟪u, n^{-1/2} ∑ s(Xᵢ)⟫`. -/
theorem empiricalProcess_inner {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) {d : ℕ} (s : X → EuclideanSpace ℝ (Fin d))
    (hs : Integrable s P) (hs0 : ∫ x, s x ∂P = 0) (u : EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    empiricalProcess P Xn n (fun x ↦ inner ℝ u (s x)) ω =
      inner ℝ u ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω)) := by
  simp only [empiricalProcess, integral_inner hs, hs0, inner_zero_right, mul_zero, sub_zero,
    inner_smul_right, inner_sum]

/-- **Pointwise local expansion.** For a family `f θ` that is Lipschitz near `θ₀` with a
square-integrable envelope and differentiable at `θ₀` with derivative `⟪s x, ·⟫` for a centred
square-integrable `s`, and for a fixed local direction `u`,
`√n (Gₙ f(θ₀ + u/√n) - Gₙ f θ₀) - ⟪u, n^{-1/2} ∑ s(Xᵢ)⟫ → 0` in probability. The proof is
Chebyshev's inequality and dominated convergence for the second moment of the remainder. -/
theorem tendstoInMeasure_sqrt_mul_empiricalProcess_sub_sub_inner {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure X) [IsProbabilityMeasure P] (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn P) {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → X → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hfm : ∀ θ ∈ Metric.ball θ₀ r₀, Measurable (f θ))
    (hfi : ∀ θ ∈ Metric.ball θ₀ r₀, Integrable (f θ) P) (L : X → ℝ) (hL2 : MemLp L 2 P)
    (hlip : ∀ u ∈ Metric.ball θ₀ r₀, ∀ v ∈ Metric.ball θ₀ r₀, ∀ x,
      |f u x - f v x| ≤ L x * ‖u - v‖)
    (s : X → EuclideanSpace ℝ (Fin d)) (hsm : Measurable s) (hs2 : MemLp s 2 P)
    (hs0 : ∫ x, s x ∂P = 0) (hd : ∀ x, HasFDerivAt (fun θ ↦ f θ x) (innerSL ℝ (s x)) θ₀)
    (u : EuclideanSpace ℝ (Fin d)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n *
      (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • u)) ω -
        empiricalProcess P Xn n (f θ₀) ω) -
      inner ℝ u ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))) atTop (fun _ ↦ 0) := by
  set θn : ℕ → EuclideanSpace ℝ (Fin d) := fun n ↦ θ₀ + (Real.sqrt n)⁻¹ • u with hθn
  have hsqrt : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hball : ∀ᶠ n in atTop, θn n ∈ Metric.ball θ₀ r₀ := by
    have h := (hsqrt.mul_const ‖u‖).eventually (gt_mem_nhds (by rw [zero_mul]; exact hr₀))
    filter_upwards [h] with n hn
    rw [Metric.mem_ball, dist_eq_norm, hθn, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact hn
  have h0ball : θ₀ ∈ Metric.ball θ₀ r₀ := Metric.mem_ball_self hr₀
  set g : ℕ → X → ℝ := fun n x ↦ Real.sqrt n * (f (θn n) x - f θ₀ x) - inner ℝ u (s x)
    with hg
  have hsi : Integrable s P := hs2.integrable one_le_two
  have hinm : Measurable fun x ↦ inner ℝ u (s x) := by fun_prop
  have hgm : ∀ᶠ n in atTop, Measurable (g n) := by
    filter_upwards [hball] with n hn
    exact (measurable_const.mul ((hfm _ hn).sub (hfm _ h0ball))).sub hinm
  set F : X → ℝ := fun x ↦ ‖u‖ * L x + ‖u‖ * ‖s x‖ with hF
  have hF2 : MemLp F 2 P := (hL2.const_mul _).add (hs2.norm.const_mul _)
  have hgb : ∀ᶠ n in atTop, ∀ x, |g n x| ≤ F x := by
    filter_upwards [hball, eventually_ge_atTop 1] with n hn hn1
    intro x
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    have h1 := hlip _ hn _ h0ball x
    have hnorm : ‖θn n - θ₀‖ = (Real.sqrt n)⁻¹ * ‖u‖ := by
      rw [hθn, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.2 hsn.le)]
    rw [hnorm] at h1
    have h2 : |inner ℝ u (s x)| ≤ ‖u‖ * ‖s x‖ := abs_real_inner_le_norm _ _
    have h3 : |Real.sqrt n * (f (θn n) x - f θ₀ x)| ≤ ‖u‖ * L x := by
      rw [abs_mul, abs_of_pos hsn]
      calc Real.sqrt n * |f (θn n) x - f θ₀ x|
          ≤ Real.sqrt n * (L x * ((Real.sqrt n)⁻¹ * ‖u‖)) := by gcongr
        _ = ‖u‖ * L x := by field_simp
    simp only [hg, hF]
    exact (abs_sub _ _).trans (add_le_add h3 h2)
  -- The remainder is the empirical process of `g n`.
  have hexpr : ∀ᶠ n : ℕ in atTop, ∀ ω, Real.sqrt n *
      (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • u)) ω -
        empiricalProcess P Xn n (f θ₀) ω) -
      inner ℝ u ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω)) =
        empiricalProcess P Xn n (g n) ω := by
    filter_upwards [hball] with n hn
    intro ω
    have hinti : Integrable (fun x ↦ inner ℝ u (s x)) P := hsi.const_inner u
    have hd1 : Integrable (fun x ↦ Real.sqrt n * (f (θn n) x - f θ₀ x)) P :=
      ((hfi _ hn).sub (hfi _ h0ball)).const_mul _
    rw [← empiricalProcess_inner P Xn n s hsi hs0 u ω, hg,
      empiricalProcess_sub P Xn n hd1 hinti]
    congr 1
    have hI : ∫ x, (f (θn n) x - f θ₀ x) ∂P = ∫ x, f (θn n) x ∂P - ∫ x, f θ₀ x ∂P :=
      integral_sub (hfi _ hn) (hfi _ h0ball)
    simp only [empiricalProcess, integral_const_mul, hI, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp only [hθn]
    ring
  -- Second moments of the remainder tend to zero.
  have hmom : Tendsto (fun n ↦ ∫ x, g n x ^ 2 ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := P) (fun x ↦ F x ^ 2)
      (F := fun n x ↦ g n x ^ 2) (f := fun _ ↦ (0 : ℝ))
      (hgm.mono fun n hn ↦ (hn.pow_const 2).aestronglyMeasurable)
      (hgb.mono fun n hn ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hn x) 2)
      hF2.integrable_sq
      (ae_of_all _ fun x ↦ by
        have h := (tendsto_sqrt_mul_sub_sub_inner (hd x) u).pow 2
        simpa [hg, hθn] using h)
    simpa using this
  rw [tendstoInMeasure_iff_measureReal_lt_dist]
  intro c hc
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
    ((hmom.div_const (c ^ 2)).trans (by rw [zero_div]))
  filter_upwards [hexpr, hgm, hgb, eventually_ge_atTop 1] with n hn hgmn hgbn hn1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hg2 : MemLp (g n) 2 P := hF2.of_le hgmn.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (hgbn x).trans (le_abs_self _))
  have hcheb := measureReal_le_abs_sum_sub_le_of_iid μ P Xn hiid (g n) hgmn hg2 n
    (ε := c * Real.sqrt n) (by positivity)
  have hsub : {ω | c < dist (Real.sqrt n *
      (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • u)) ω -
        empiricalProcess P Xn n (f θ₀) ω) -
      inner ℝ u ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))) 0} ⊆
      {ω | c * Real.sqrt n ≤ |∑ i ∈ Finset.range n, g n (Xn i ω) - n * ∫ x, g n x ∂P|} := by
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
    rw [hn ω] at hω
    simp only [empiricalProcess, abs_mul, abs_of_pos (inv_pos.2 hsn)] at hω
    rw [inv_mul_eq_div, lt_div_iff₀ hsn] at hω
    exact hω.le
  refine (measureReal_mono hsub).trans (hcheb.trans (le_of_eq ?_))
  rw [mul_pow, hsq]
  field_simp

/-- The choice of the dyadic resolution: for `a > 0` there is a level `k` at which the
number of cells times the Bernstein tail `exp (-(a 2ᵏ))`, this tail itself, and the scaled
cell width `b (w / 2ᵏ)` are small. -/
private theorem exists_dyadic_level {a : ℝ} (ha : 0 < a) (d : ℕ) (b w : ℝ) {η ε₁ ε₂ : ℝ}
    (hη : 0 < η) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ k : ℕ, 4 * 2 ^ d * (((2 : ℝ) ^ k) ^ d * Real.exp (-(a * 2 ^ k))) ≤ η ∧
      2 ^ d * Real.exp (-(a * 2 ^ k)) ≤ 1 / 2 ∧ b * (w / 2 ^ k) ≤ ε₁ ∧
        b * (w / 2 ^ k) ≤ ε₂ := by
  have hlim1 : Tendsto (fun k : ℕ ↦ 4 * 2 ^ d * (((2 : ℝ) ^ k) ^ d *
      Real.exp (-(a * 2 ^ k)))) atTop (𝓝 0) := by
    simpa using (tendsto_two_pow_pow_mul_exp_neg ha d).const_mul (4 * 2 ^ d)
  have hlim2 : Tendsto (fun k : ℕ ↦ 2 ^ d * Real.exp (-(a * 2 ^ k))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ ↦ a * (2 : ℝ) ^ k) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop ha
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul (2 ^ d)
  have hlim3 : Tendsto (fun k : ℕ ↦ b * (w / 2 ^ k)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (b * w))
    rw [mul_zero] at this
    refine this.congr fun k ↦ ?_
    rw [one_div_pow]; ring
  exact ((hlim1.eventually (eventually_le_nhds hη)).and
    ((hlim2.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
    ((hlim3.eventually (eventually_le_nhds hε₁)).and
    (hlim3.eventually (eventually_le_nhds hε₂))))).exists

/-- The scaled dyadic cells of `[-2R, 2R)ᵈ` lie within `c √d 2R` of `θ₀`: if `θ` lies in the
cell `θ₀ + c • (cell z of level k)`, then `‖θ - θ₀‖ ≤ c (√d (2R))`. -/
private theorem norm_sub_le_of_mem_halfOpenCube_add_smul_cubeGridPoint {d : ℕ}
    {θ₀ θ : EuclideanSpace ℝ (Fin d)} {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {k : ℕ}
    {z : Fin d → ℤ} (hz : z ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) (2 ^ k))
    (hθ : θ ∈ halfOpenCube
      (θ₀ + c • cubeGridPoint (WithLp.toLp 2 fun _ ↦ -(2 * R)) (4 * R) k z)
      (c * (4 * R / 2 ^ k))) :
    ‖θ - θ₀‖ ≤ c * (Real.sqrt d * (2 * R)) := by
  rw [Fintype.mem_piFinset] at hz
  rw [← mul_assoc, mul_comm c, mul_assoc]
  refine norm_le_sqrt_card_mul_of_abs_le _ fun i ↦ ?_
  obtain ⟨h1, h2⟩ := hθ i
  have hzi := Finset.mem_Ico.1 (hz i)
  have hz1 : (0 : ℝ) ≤ z i := by exact_mod_cast hzi.1
  have hz2 : (z i : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Int.add_one_le_iff.2 hzi.2
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hwk0 : 0 < 4 * R / 2 ^ k := div_pos (by linarith) hp
  have e : (2 : ℝ) ^ k * (4 * R / 2 ^ k) = 4 * R := by field_simp
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cubeGridPoint_apply] at h1 h2
  rw [PiLp.sub_apply, abs_le]
  have hzw : 0 ≤ (z i : ℝ) * (4 * R / 2 ^ k) := mul_nonneg hz1 hwk0.le
  have hzw2 : ((z i : ℝ) + 1) * (4 * R / 2 ^ k) ≤ 2 ^ k * (4 * R / 2 ^ k) :=
    mul_le_mul_of_nonneg_right hz2 hwk0.le
  constructor <;> nlinarith

/-- The triangle-inequality step of the uniform local expansion: the expansion
`s (G(θ₀ + c h) - G θ₀) ≈ ⟪h, Δ⟫` at `h` follows, up to `5 ε / 8`, from the expansion at a
nearby anchor `v` and an oscillation bound for `G` on the cell of `v`. Here `s c = 1`. -/
private theorem abs_mul_sub_sub_inner_le_of_anchor {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ) (θ₀ h v Δ : EuclideanSpace ℝ (Fin d))
    {s c sd wk A Rm KΔ ε : ℝ} (hs : 0 < s) (hcs : s * c = 1) (hsd : 0 ≤ sd) (hwk : 0 ≤ wk)
    (hRm0 : 0 ≤ Rm) (hRm1 : Rm ≤ 1)
    (h1 : |G (θ₀ + c • h) - G (θ₀ + c • v)| ≤ sd * (c * wk) * (2 * A + Rm))
    (h2 : |s * (G (θ₀ + c • v) - G θ₀) - inner ℝ v Δ| ≤ ε / 4)
    (hhv : ‖h - v‖ ≤ sd * wk) (hΔ : ‖Δ‖ ≤ KΔ) (hk : sd * wk * KΔ ≤ ε / 8)
    (hk' : sd * wk ≤ ε / 8) (hA : sd * wk * (2 * A) = ε / 8) :
    |s * (G (θ₀ + c • h) - G θ₀) - inner ℝ h Δ| ≤ 5 * ε / 8 := by
  have hs0 : 0 ≤ s := hs.le
  have hsw : 0 ≤ sd * wk := mul_nonneg hsd hwk
  have hε8 : 0 ≤ ε / 8 := hsw.trans hk'
  have h3 : |inner ℝ (h - v) Δ| ≤ ε / 8 :=
    (abs_real_inner_le_norm _ _).trans ((mul_le_mul hhv hΔ (norm_nonneg _) hsw).trans hk)
  have h1' : s * |G (θ₀ + c • h) - G (θ₀ + c • v)| ≤ ε / 4 := by
    calc s * |G (θ₀ + c • h) - G (θ₀ + c • v)|
        ≤ s * (sd * (c * wk) * (2 * A + Rm)) := by gcongr
      _ = sd * wk * (2 * A) + sd * wk * Rm := by
        linear_combination (sd * wk * (2 * A + Rm)) * hcs
      _ ≤ ε / 8 + ε / 8 * 1 := by
        rw [hA]
        gcongr
      _ = ε / 4 := by ring
  have hsplit : s * (G (θ₀ + c • h) - G θ₀) - inner ℝ h Δ =
      s * (G (θ₀ + c • h) - G (θ₀ + c • v)) +
        (s * (G (θ₀ + c • v) - G θ₀) - inner ℝ v Δ) - inner ℝ (h - v) Δ := by
    rw [inner_sub_left]
    ring
  rw [hsplit]
  have t1 := abs_add_le (s * (G (θ₀ + c • h) - G (θ₀ + c • v)))
    (s * (G (θ₀ + c • v) - G θ₀) - inner ℝ v Δ)
  have t2 := abs_sub (s * (G (θ₀ + c • h) - G (θ₀ + c • v)) +
    (s * (G (θ₀ + c • v) - G θ₀) - inner ℝ v Δ)) (inner ℝ (h - v) Δ)
  rw [abs_mul, abs_of_pos hs] at t1
  linarith

/-- **Uniform local expansion of the empirical process.** In the setting of
`tendstoInMeasure_sqrt_mul_empiricalProcess_sub_sub_inner`, with `n^{-1/2} ∑ s(Xᵢ)` bounded in
probability, for every `R > 0` the remainder
`√n (Gₙ f(θ₀ + h/√n) - Gₙ f θ₀) - ⟪h, n^{-1/2} ∑ s(Xᵢ)⟫` tends to zero in outer probability
uniformly over `‖h‖ ≤ R`. The proof covers the cube `[-2R, 2R)ᵈ` by `2ᵏᵈ` dyadic cells,
applies the maximal inequality `measureReal_exists_abs_empiricalProcess_sub_gt_le` in each cell,
and the pointwise expansion at the cell anchors. -/
theorem tendsto_measureReal_exists_abs_sqrt_mul_empiricalProcess_sub_sub_inner {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure X) [IsProbabilityMeasure P] (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn P) {d : ℕ}
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
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ∃ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R ∧
      ε < |Real.sqrt n * (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • h)) ω -
        empiricalProcess P Xn n (f θ₀) ω) -
        inner ℝ h ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))|}) atTop (𝓝 0) := by
  set Δ : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n ω ↦
    (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω) with hΔdef
  set G : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ := fun n θ ω ↦ empiricalProcess P Xn n (f θ) ω
    with hG
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hempty : ∀ n : ℕ, {ω | ∃ h : EuclideanSpace ℝ (Fin 0), ‖h‖ ≤ R ∧
        ε < |Real.sqrt n * (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • h)) ω -
          empiricalProcess P Xn n (f θ₀) ω) -
          inner ℝ h ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))|} = ∅ := by
      intro n
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
      intro h _
      have h0 : h = 0 := Subsingleton.elim _ _
      subst h0
      simp only [smul_zero, add_zero, sub_self, mul_zero, inner_zero_left, abs_zero]
      exact hε.le
    simp_rw [hempty, measureReal_empty]
    exact tendsto_const_nhds
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨K₀, hK₀⟩ := hΔ (η / 4) (by positivity)
  set KΔ : ℝ := max K₀ 0 + 1 with hKΔ
  have hKΔ0 : 0 < KΔ := by positivity
  have hK₀Δ : K₀ ≤ KΔ := by simp only [hKΔ]; linarith [le_max_left K₀ 0]
  set β : ℝ := ∫ x, L x ^ 2 ∂P + 1 with hβ
  have hβ0 : 0 < β := by
    have : 0 ≤ ∫ x, L x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    linarith
  set φ : ℝ → ℝ := bernsteinExponent β (2 * 1 / 3) with hφ
  set w₀ : ℝ := 4 * R with hw₀
  have hw₀0 : 0 < w₀ := by positivity
  set a₀ : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun _ ↦ -(2 * R) with ha₀
  set cA : ℝ := ε / (16 * Real.sqrt d * w₀) with hcA
  have hcA0 : 0 < cA := by positivity
  set Ak : ℕ → ℝ := fun k ↦ cA * 2 ^ k with hAk
  set qk : ℕ → ℝ := fun k ↦ 2 ^ d * Real.exp (-φ (Ak k)) with hqk
  have hφpos : 0 < φ cA := by
    simp only [hφ, bernsteinExponent]; positivity
  have hq_le : ∀ k, qk k ≤ 2 ^ d * Real.exp (-(φ cA * 2 ^ k)) := by
    intro k
    simp only [hqk]
    gcongr
    have := mul_bernsteinExponent_le (β := β) (γ := 2 * 1 / 3) (t := cA) (c := 2 ^ k) hβ0
      (by norm_num) hcA0.le (one_le_pow₀ (by norm_num))
    simp only [hAk, hφ]
    rw [mul_comm cA, mul_comm (bernsteinExponent β (2 * 1 / 3) cA)]
    exact this
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_dyadic_level hφpos d (Real.sqrt d) w₀
    (by positivity : (0 : ℝ) < η / 4) (by positivity : (0 : ℝ) < ε / 8)
    (by positivity : (0 : ℝ) < ε / (8 * KΔ))
  set wk : ℝ := w₀ / 2 ^ k with hwk
  have hwk0 : 0 < wk := by positivity
  set Z : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) (2 ^ k)
    with hZ
  set u : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := cubeGridPoint a₀ w₀ k with hu
  have hZcard : (Z.card : ℝ) = (2 ^ k) ^ d := card_piFinset_Ico_two_pow d k
  have hZpos : 0 < (Z.card : ℝ) := by rw [hZcard]; positivity
  -- Pointwise expansions at the cell anchors.
  have hanchor : ∀ z ∈ Z, ∀ᶠ n : ℕ in atTop, μ.real {ω | ε / 4 < dist (Real.sqrt n *
      (G n (θ₀ + (Real.sqrt n)⁻¹ • u z) ω - G n θ₀ ω) - inner ℝ (u z) (Δ n ω)) 0} ≤
        η / (4 * Z.card) := fun z _ ↦ by
    have h := tendstoInMeasure_sqrt_mul_empiricalProcess_sub_sub_inner μ P Xn hiid f θ₀ hr₀ hfm
      hfi L hL2 hlip s hsm hs2 hs0 hd (u z)
    rw [tendstoInMeasure_iff_measureReal_lt_dist] at h
    exact (h (ε / 4) (by positivity)).eventually (eventually_le_nhds (by positivity))
  have hrad : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ * (Real.sqrt d * (2 * R)) < r₀ := by
    have hsqrt : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    exact (hsqrt.mul_const _).eventually (gt_mem_nhds (by rw [zero_mul]; exact hr₀))
  have hrem := tendstoInMeasure_lipschitzChainRemainder μ P Xn hiid L hLm hL0 hL2 one_pos
  rw [tendstoInMeasure_iff_measureReal_lt_dist] at hrem
  filter_upwards [hK₀, (Filter.eventually_all_finset Z).2 hanchor, hrad,
    (hrem 1 one_pos).eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η / 4)),
    eventually_ge_atTop 1] with n hnΔ hnA hnr hnR hn1
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  set c : ℝ := (Real.sqrt n)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 hsn
  have hcs : Real.sqrt n * c = 1 := mul_inv_cancel₀ hsn.ne'
  -- Cells and their containment in the ball.
  set cell : (Fin d → ℤ) → Set (EuclideanSpace ℝ (Fin d)) := fun z ↦
    halfOpenCube (θ₀ + c • u z) (c * wk) with hcell
  have hcellball : ∀ z ∈ Z, ∀ θ ∈ cell z, θ ∈ Metric.ball θ₀ r₀ := fun z hz θ hθ ↦ by
    rw [Metric.mem_ball, dist_eq_norm]
    exact (norm_sub_le_of_mem_halfOpenCube_add_smul_cubeGridPoint hR hc0 hz hθ).trans_lt hnr
  -- Probability of a large oscillation in some cell.
  set E : (Fin d → ℤ) → Set Ω := fun z ↦ {ω | ∃ θ ∈ cell z,
    Real.sqrt d * (c * wk) * (2 * Ak k + lipschitzChainRemainder P Xn L 1 n ω) <
      |G n θ ω - G n (θ₀ + c • u z) ω|} with hE
  have hEz : ∀ z ∈ Z, μ.real (E z) ≤ 4 * qk k := by
    intro z hz
    have hcellm : ∀ θ ∈ cell z, θ ∈ Metric.ball θ₀ r₀ := hcellball z hz
    have hmax := measureReal_exists_abs_empiricalProcess_sub_gt_le μ P Xn hiid f
      (θ₀ + c • u z) (w := c * wk) (by positivity) (fun θ hθ ↦ hfm θ (hcellm θ hθ))
      (fun θ hθ ↦ hfi θ (hcellm θ hθ)) L hLm hL0 hL2
      (fun a ha b hb x ↦ hlip a (hcellm a ha) b (hcellm b hb) x) one_pos hn1
      (A := Ak k) (by positivity)
    refine hmax.trans ?_
    have hq0 : 0 ≤ 2 ^ d * Real.exp (-bernsteinExponent (∫ x, L x ^ 2 ∂P + 1) (2 * 1 / 3)
      (Ak k)) := by positivity
    exact two_mul_sum_range_pow_succ_le hq0 ((hq_le k).trans hk2) n
  set D : (Fin d → ℤ) → Set Ω := fun z ↦ {ω | ε / 4 < dist (Real.sqrt n *
      (G n (θ₀ + (Real.sqrt n)⁻¹ • u z) ω - G n θ₀ ω) - inner ℝ (u z) (Δ n ω)) 0} with hD
  have hsub : {ω | ∃ h : EuclideanSpace ℝ (Fin d), ‖h‖ ≤ R ∧
      ε < |Real.sqrt n * (empiricalProcess P Xn n (f (θ₀ + (Real.sqrt n)⁻¹ • h)) ω -
        empiricalProcess P Xn n (f θ₀) ω) -
        inner ℝ h ((Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, s (Xn i ω))|} ⊆
      (⋃ z ∈ Z, E z) ∪ (⋃ z ∈ Z, D z) ∪
        {ω | 1 < dist (lipschitzChainRemainder P Xn L 1 n ω) 0} ∪
        {ω | K₀ < ‖Δ n ω‖} := by
    rintro ω ⟨h, hhR, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_ofPred_eq, not_lt] at hcon
    obtain ⟨⟨⟨hnE, hnD⟩, hnRω⟩, hnΔω⟩ := hcon
    have hhcube : h ∈ halfOpenCube a₀ w₀ := by
      intro i
      have := (PiLp.norm_apply_le h i).trans hhR
      rw [Real.norm_eq_abs, abs_le] at this
      simp only [ha₀, PiLp.toLp_apply, hw₀]
      constructor <;> linarith
    set z := cubeIndex a₀ w₀ k h with hzdef
    have hz : z ∈ Z := cubeIndex_mem hw₀0 hhcube k
    have hhu : h ∈ halfOpenCube (u z) wk := fun i ↦ by
      obtain ⟨h1, h2⟩ := sub_cubeGridPoint_cubeIndex_mem a₀ h hw₀0 k i
      constructor <;> simp only [hu, hzdef] <;> linarith
    set θ := θ₀ + c • h with hθ
    have hθcell : θ ∈ cell z := add_smul_mem_halfOpenCube hhu θ₀ hc0
    have h1 : |G n θ ω - G n (θ₀ + c • u z) ω| ≤
        Real.sqrt d * (c * wk) * (2 * Ak k + lipschitzChainRemainder P Xn L 1 n ω) := by
      have := hnE z hz
      simp only [hE, mem_ofPred_eq, not_exists, not_and, not_lt] at this
      exact this θ hθcell
    have h2 : |Real.sqrt n * (G n (θ₀ + c • u z) ω - G n θ₀ ω) - inner ℝ (u z) (Δ n ω)| ≤
        ε / 4 := by
      have := hnD z hz
      simp only [hD, mem_ofPred_eq, not_lt, Real.dist_eq, sub_zero] at this
      exact this
    have hR1 : lipschitzChainRemainder P Xn L 1 n ω ≤ 1 := by
      have := hnRω
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this
    have hhu' : ‖h - u z‖ ≤ Real.sqrt d * wk := by
      refine norm_le_sqrt_card_mul_of_abs_le _ fun i ↦ ?_
      obtain ⟨g1, g2⟩ := hhu i
      rw [PiLp.sub_apply, abs_of_nonneg (by linarith)]
      linarith
    have hkε : Real.sqrt d * wk * KΔ ≤ ε / 8 := by
      have := hk4
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hAk' : Real.sqrt d * wk * (2 * Ak k) = ε / 8 := by
      have key : ∀ a b e p : ℝ, 0 < a → 0 < b → 0 < p →
          a * (b / p) * (2 * (e / (16 * a * b) * p)) = e / 8 := by
        intro a b e p ha hb hp
        field_simp
        ring
      exact key _ _ _ _ hsd hw₀0 (by positivity)
    have hR0 : 0 ≤ lipschitzChainRemainder P Xn L 1 n ω :=
      add_nonneg (empiricalEnvelope_nonneg P Xn n
        (fun x ↦ Set.indicator_nonneg (fun x _ ↦ hL0 x) x) ω)
        (mul_nonneg (by positivity) (empiricalEnvelope_nonneg P Xn n hL0 ω))
    have hle : |Real.sqrt n * (G n θ ω - G n θ₀ ω) - inner ℝ h (Δ n ω)| ≤ 5 * ε / 8 :=
      abs_mul_sub_sub_inner_le_of_anchor (fun θ ↦ G n θ ω) θ₀ h (u z) (Δ n ω) hsn hcs hsd.le
        hwk0.le hR0 hR1 h1 h2 hhu' (hnΔω.trans hK₀Δ) hkε hk3 hAk'
    have hlt' : ε < |Real.sqrt n * (G n θ ω - G n θ₀ ω) - inner ℝ h (Δ n ω)| := hlt
    linarith
  calc _ ≤ μ.real ((⋃ z ∈ Z, E z) ∪ (⋃ z ∈ Z, D z) ∪
        {ω | 1 < dist (lipschitzChainRemainder P Xn L 1 n ω) 0} ∪
        {ω | K₀ < ‖Δ n ω‖}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z ∈ Z, μ.real (E z) + ∑ z ∈ Z, μ.real (D z) +
        μ.real {ω | 1 < dist (lipschitzChainRemainder P Xn L 1 n ω) 0} +
        μ.real {ω | K₀ < ‖Δ n ω‖} := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact (measureReal_union_le _ _).trans (add_le_add (measureReal_biUnion_finset_le _ _)
        (measureReal_biUnion_finset_le _ _))
    _ ≤ ∑ _z ∈ Z, 4 * qk k + ∑ _z ∈ Z, η / (4 * Z.card) + η / 4 + η / 4 := by
      gcongr with z hz z hz
      · exact hEz z hz
      · exact hnA z hz
    _ ≤ η / 4 + η / 4 + η / 4 + η / 4 := by
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have e2 : (Z.card : ℝ) * (η / (4 * Z.card)) = η / 4 := by field_simp
      have e1 : (Z.card : ℝ) * (4 * qk k) ≤ η / 4 := by
        rw [hZcard]
        refine le_trans ?_ hk1
        have := hq_le k
        have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ d := by positivity
        calc ((2 : ℝ) ^ k) ^ d * (4 * qk k)
            ≤ ((2 : ℝ) ^ k) ^ d * (4 * (2 ^ d * Real.exp (-(φ cA * 2 ^ k)))) := by gcongr
          _ = _ := by ring
      rw [e2]
      linarith
    _ = η := by ring

end CKSD
