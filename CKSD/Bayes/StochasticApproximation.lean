module

public import CKSD.Bayes.StochasticApproximation.Basic
public import CKSD.Bayes.StochasticApproximationPath
public import CKSD.Bayes.MartingaleSeries
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Stochastic approximation: Robbins–Monro and the ODE method

For the recursion `θₙ₊₁ = θₙ - aₙ(h(θₙ) + Mₙ₊₁)` in a finite-dimensional real inner product space
the limiting equation is `θ' = -h(θ)`. Its flow is specified by its defining differential equation
(`IsFlowOf`), which determines it uniquely for Lipschitz `h`. Invariant and internally chain
transitive sets follow Benaïm, the limit set of a sequence is the set of its cluster points, and
the interpolated process is piecewise linear between the times `tₙ = ∑_{k<n} aₖ`.

## Main definitions

* `CKSD.IsRobbinsMonroScheme`: the standing hypotheses on the recursion — adapted iterates and
  martingale-difference noise with a conditional second-moment bound, and Robbins–Monro steps
  `aₙ > 0`, `∑ aₙ = ∞`, `∑ aₙ² < ∞`.
* `CKSD.IsFlowOf`, `CKSD.IsInvariantSet`, `CKSD.IsInternallyChainTransitive`, `CKSD.limitSet`:
  flows, invariant and internally chain transitive sets, and limit sets.
* `CKSD.stochasticApproxTime`, `CKSD.stochasticApproxInterp`: interpolation times and the
  piecewise-linear interpolated process.

## Main results

* `CKSD.ae_tendsto_robbins_monro`: almost-sure convergence of Robbins–Monro under a strongly
  monotone Lipschitz field and bounded conditional noise variance (GAPS 104.40).
* `CKSD.ae_isInternallyChainTransitive_limitSet`: Benaïm's limit-set theorem (GAPS 104.49).
* `CKSD.ae_tendsto_equilibrium_of_chainTransitive`: convergence to an equilibrium when the only
  internally chain transitive sets are equilibria (GAPS 104.49).
* `CKSD.ae_asymptotic_pseudotrajectory`: the interpolated process is an asymptotic
  pseudotrajectory of the flow (GAPS 104.49).

The proof of `CKSD.ae_tendsto_robbins_monro` is the Robbins–Siegmund argument: a rescaled
squared distance to the root plus accumulated drift is a supermartingale bounded below, and
Mathlib's almost-everywhere martingale convergence theorem
(`MeasureTheory.Submartingale.ae_tendsto_limitProcess`) applies.

For the ODE method, predictable clipping and martingale convergence show convergence of the
accumulated weighted noise. Correcting the affine interpolation by that noise gives an
approximate ODE solution, controlled by the deterministic results in
`CKSD.Bayes.StochasticApproximationPath`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Deterministic core of the Robbins–Siegmund argument: if `Vₙ/Pₙ + ∑_{k<n} c aₖ Vₖ/Pₖ₊₁ - Sₙ`
converges, `Sₙ` converges, `1 ≤ Pₙ ≤ Pmax`, `aₙ > 0` and `∑ aₙ = ∞`, then `Vₙ → 0`. -/
private theorem tendsto_zero_of_tendsto_robbinsSiegmund {V a P S : ℕ → ℝ} {Pmax c s y : ℝ}
    (hV : ∀ n, 0 ≤ V n) (ha : ∀ n, 0 < a n)
    (hsum : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hP1 : ∀ n, 1 ≤ P n) (hPb : ∀ n, P n ≤ Pmax) (hc : 0 < c)
    (hS : Tendsto S atTop (𝓝 s))
    (hY : Tendsto (fun n ↦ V n / P n + ∑ k ∈ Finset.range n, c * a k * V k / P (k + 1) - S n)
      atTop (𝓝 y)) :
    Tendsto V atTop (𝓝 0) := by
  set B : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, c * a k * V k / P (k + 1) with hB
  have hP0 (n : ℕ) : 0 < P n := lt_of_lt_of_le one_pos (hP1 n)
  have hterm (k : ℕ) : 0 ≤ c * a k * V k / P (k + 1) :=
    div_nonneg (mul_nonneg (mul_nonneg hc.le (ha k).le) (hV k)) (hP0 _).le
  have hBmono : Monotone B := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    simp only [hB, Finset.sum_range_succ]
    linarith [hterm n]
  have hYS : Tendsto (fun n ↦ (V n / P n + B n - S n) + S n) atTop (𝓝 (y + s)) := hY.add hS
  obtain ⟨R, hR⟩ := hYS.bddAbove_range
  have hBle (n : ℕ) : B n ≤ R := by
    have h1 : V n / P n + B n - S n + S n ≤ R := hR (mem_range_self n)
    have h2 : 0 ≤ V n / P n := div_nonneg (hV n) (hP0 n).le
    linarith
  have hBbdd : BddAbove (range B) := ⟨R, by rintro _ ⟨n, rfl⟩; exact hBle n⟩
  have hBlim := tendsto_atTop_ciSup hBmono hBbdd
  set b := ⨆ n, B n
  have hW : Tendsto (fun n ↦ V n / P n) atTop (𝓝 (y - b + s)) := by
    have := (hY.sub hBlim).add hS
    refine this.congr fun n ↦ ?_
    simp only [hB]
    ring
  set ℓ := y - b + s
  have hℓ0 : 0 ≤ ℓ := ge_of_tendsto' hW fun n ↦ div_nonneg (hV n) (hP0 n).le
  have hℓ : ℓ = 0 := by
    by_contra hne
    have hℓpos : 0 < ℓ := lt_of_le_of_ne hℓ0 (Ne.symm hne)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hW.eventually (eventually_ge_nhds (half_lt_self hℓpos)))
    have hPm : 0 < Pmax := lt_of_lt_of_le one_pos ((hP1 0).trans (hPb 0))
    set κ := c * (ℓ / 2) / Pmax
    have hκ : 0 < κ := by positivity
    have hlow (n : ℕ) : κ * (∑ k ∈ Finset.range n, a k - ∑ k ∈ Finset.range n₀, a k) ≤ B n := by
      rcases le_or_gt n₀ n with hn | hn
      · rw [← Finset.sum_range_add_sum_Ico _ hn, add_sub_cancel_left, Finset.mul_sum]
        calc ∑ k ∈ Finset.Ico n₀ n, κ * a k ≤ ∑ k ∈ Finset.Ico n₀ n, c * a k * V k / P (k + 1) := by
              refine Finset.sum_le_sum fun k hk ↦ ?_
              have hk0 : n₀ ≤ k := (Finset.mem_Ico.1 hk).1
              have hVk : ℓ / 2 ≤ V k := by
                have := hn₀ k hk0
                rw [le_div_iff₀ (hP0 k)] at this
                nlinarith [hP1 k]
              rw [le_div_iff₀ (hP0 _)]
              have := hPb (k + 1)
              have hak := (ha k).le
              simp only [κ]
              rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hPm]
              have h1 : c * (ℓ / 2) * a k * P (k + 1) ≤ c * (ℓ / 2) * a k * Pmax :=
                mul_le_mul_of_nonneg_left this (by positivity)
              have h2 : c * (ℓ / 2) * a k ≤ c * a k * V k := by
                have := mul_le_mul_of_nonneg_left hVk (mul_nonneg hc.le hak)
                linarith
              nlinarith
          _ ≤ B n := by
              show _ ≤ ∑ k ∈ Finset.range n, c * a k * V k / P (k + 1)
              rw [← Finset.sum_range_add_sum_Ico _ hn]
              exact le_add_of_nonneg_left (Finset.sum_nonneg fun k _ ↦ hterm k)
      · have : ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n₀, a k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hn.le)
            fun k _ _ ↦ (ha k).le
        have hB0 : 0 ≤ B n := Finset.sum_nonneg fun k _ ↦ hterm k
        nlinarith
    have htop : Tendsto (fun n ↦ κ * (∑ k ∈ Finset.range n, a k - ∑ k ∈ Finset.range n₀, a k))
        atTop atTop :=
      (tendsto_atTop_add_const_right _ _ hsum).const_mul_atTop hκ
    obtain ⟨n, hn⟩ := (htop.eventually (eventually_gt_atTop R)).exists
    linarith [hlow n, hBle n]
  rw [hℓ] at hW
  have hPm : 0 ≤ Pmax := (zero_le_one.trans (hP1 0)).trans (hPb 0)
  refine squeeze_zero hV (fun n ↦ ?_) (by simpa using hW.const_mul Pmax)
  calc V n = P n * (V n / P n) := (mul_div_cancel₀ (V n) (hP0 n).ne').symm
    _ ≤ Pmax * (V n / P n) := mul_le_mul_of_nonneg_right (hPb n) (div_nonneg (hV n) (hP0 n).le)


section RobbinsMonroProof

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise inner product of two square-integrable functions is integrable. -/
private theorem integrable_inner_of_memLp_two {μ : Measure Ω} {f g : Ω → E} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : Integrable (fun ω ↦ inner ℝ (f ω) (g ω)) μ := by
  have hfg : Integrable (fun ω ↦ ‖f ω‖ * ‖g ω‖) μ := hf.norm.integrable_mul hg.norm
  refine hfg.mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable) (ae_of_all _ fun ω ↦ ?_)
  exact norm_inner_le_norm (f ω) (g ω)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A martingale difference is orthogonal to every square-integrable `Fₙ`-measurable function. -/
private theorem integral_inner_eq_zero_of_condExp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {n : ℕ} {N : Ω → E}
    (hN : MemLp N 2 μ) (hc : μ[N | F n] =ᵐ[μ] fun _ ↦ 0) {w : Ω → E}
    (hw : StronglyMeasurable[F n] w) (hw2 : MemLp w 2 μ) :
    ∫ ω, inner ℝ (w ω) (N ω) ∂μ = 0 := by
  have hint := integrable_inner_of_memLp_two hw2 hN
  rw [← integral_condExp (F.le n)]
  have h : μ[fun ω ↦ inner ℝ (w ω) (N ω) | F n] =ᵐ[μ]
      fun ω ↦ inner ℝ (w ω) ((μ[N | F n]) ω) :=
    condExp_bilin_of_aestronglyMeasurable_left (B := innerSL ℝ (E := E))
      hw.aestronglyMeasurable (by exact hint) (hN.integrable one_le_two)
  rw [integral_congr_ae h]
  refine (integral_congr_ae ?_).trans (integral_zero Ω ℝ)
  filter_upwards [hc] with ω hω
  rw [hω, inner_zero_right]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Set-integral form of `integral_inner_eq_zero_of_condExp` over `Fₙ`-events. -/
private theorem setIntegral_inner_eq_zero_of_condExp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {n : ℕ} {N : Ω → E}
    (hN : MemLp N 2 μ) (hc : μ[N | F n] =ᵐ[μ] fun _ ↦ 0) {w : Ω → E}
    (hw : StronglyMeasurable[F n] w) (hw2 : MemLp w 2 μ) {s : Set Ω}
    (hs : MeasurableSet[F n] s) :
    ∫ ω in s, inner ℝ (w ω) (N ω) ∂μ = 0 := by
  have h := integral_inner_eq_zero_of_condExp hN hc (hw.indicator hs)
    (hw2.indicator (F.le n s hs).nullMeasurableSet)
  rw [← h, ← integral_indicator (F.le n s hs)]
  congr 1
  funext ω
  by_cases hω : ω ∈ s <;> simp [hω]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conditional second-moment bound integrated over an `Fₙ`-event. -/
private theorem setIntegral_norm_sq_le_of_condExp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {n : ℕ} {N : Ω → E}
    (hN : MemLp N 2 μ) {K : ℝ} (hc : μ[(fun ω ↦ ‖N ω‖ ^ 2) | F n] ≤ᵐ[μ] fun _ ↦ K)
    {s : Set Ω} (hs : MeasurableSet[F n] s) :
    ∫ ω in s, ‖N ω‖ ^ 2 ∂μ ≤ K * μ.real s := by
  have hint : Integrable (fun ω ↦ ‖N ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hN.aestronglyMeasurable).1 hN
  rw [← setIntegral_condExp (F.le n) hint hs]
  calc _ ≤ ∫ _ in s, K ∂μ := setIntegral_mono_ae_restrict integrable_condExp.integrableOn
        (integrable_const K).integrableOn (ae_restrict_of_ae hc)
    _ = K * μ.real s := by rw [setIntegral_const, smul_eq_mul, mul_comm]


/-- The Robbins–Monro iterates are square integrable when the initial state is. -/
private theorem memLp_two_robbinsMonro_iterate {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {h : E → E} {a : ℕ → ℝ}
    {σ2 : E → ℝ} {θ M : ℕ → Ω → E} (hRM : IsRobbinsMonroScheme μ F h a σ2 θ M)
    (hθ2 : MemLp (θ 0) 2 μ) {L : ℝ≥0} (hL : LipschitzWith L h) (n : ℕ) :
    MemLp (θ n) 2 μ := by
  induction n with
  | zero => exact hθ2
  | succ n ih =>
    have hm : Measurable (θ n) := (hRM.measurable_iterate n).mono (F.le n) le_rfl
    have hg : MemLp (fun ω ↦ ‖h 0‖ + (L : ℝ) * ‖θ n ω‖) 2 μ :=
      (memLp_const _).add (ih.norm.const_mul _)
    have hh : MemLp (fun ω ↦ h (θ n ω)) 2 μ := by
      refine hg.of_le (hL.continuous.measurable.comp hm).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      have h1 := hL.norm_sub_le (θ n ω) 0
      rw [sub_zero] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [norm_le_norm_add_norm_sub' (h (θ n ω)) (h 0)]
    refine (ih.sub ((hh.add (hRM.memLp_noise (n + 1))).const_smul (a n))).ae_eq ?_
    filter_upwards [hRM.recursion n] with ω hω
    rw [hω]
    rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Expansion of the squared distance to `θ⋆` after one Robbins–Monro step. -/
private theorem norm_sub_smul_add_sq (x θ₀ H N : E) (a : ℝ) :
    ‖x - a • (H + N) - θ₀‖ ^ 2 =
      (‖x - θ₀‖ ^ 2 - 2 * a * inner ℝ (x - θ₀) H + a ^ 2 * ‖H‖ ^ 2 + a ^ 2 * ‖N‖ ^ 2) +
        inner ℝ ((-2 * a) • (x - θ₀) + (2 * a ^ 2) • H) N := by
  have : x - a • (H + N) - θ₀ = (x - θ₀) - a • (H + N) := by abel
  rw [this, norm_sub_sq_real, norm_smul, inner_smul_right, inner_add_right, mul_pow,
    Real.norm_eq_abs, sq_abs, norm_add_sq_real, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  ring

/-- One-step drift inequality for the squared distance to the root, integrated over an
`Fₙ`-event. -/
private theorem setIntegral_sq_dist_succ_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {h : E → E} {a : ℕ → ℝ} {K : ℝ}
    {θ M : ℕ → Ω → E} (hRM : IsRobbinsMonroScheme μ F h a (fun _ ↦ K) θ M)
    (hθ2 : MemLp (θ 0) 2 μ) {L : ℝ≥0} (hL : LipschitzWith L h) {θ₀ : E} (hz : h θ₀ = 0)
    {m : ℝ} (hdrift : ∀ x, m * ‖x - θ₀‖ ^ 2 ≤ inner ℝ (x - θ₀) (h x)) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[F n] s) :
    ∫ ω in s, ‖θ (n + 1) ω - θ₀‖ ^ 2 ∂μ ≤
      (1 + a n ^ 2 * L ^ 2 - 2 * a n * m) * ∫ ω in s, ‖θ n ω - θ₀‖ ^ 2 ∂μ +
        a n ^ 2 * K * μ.real s := by
  have hθn := memLp_two_robbinsMonro_iterate hRM hθ2 hL n
  have hmF : StronglyMeasurable[F n] (θ n) := (hRM.measurable_iterate n).stronglyMeasurable
  have hm : Measurable (θ n) := (hRM.measurable_iterate n).mono (F.le n) le_rfl
  have hx : MemLp (fun ω ↦ θ n ω - θ₀) 2 μ := hθn.sub (memLp_const θ₀)
  have hH : MemLp (fun ω ↦ h (θ n ω)) 2 μ := by
    refine (hx.norm.const_mul (L : ℝ)).of_le (hL.continuous.measurable.comp hm).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    have h1 := hL.norm_sub_le (θ n ω) θ₀
    rw [hz, sub_zero] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h1
  have hN := hRM.memLp_noise (n + 1)
  set w : Ω → E := fun ω ↦ (-2 * a n) • (θ n ω - θ₀) + (2 * a n ^ 2) • h (θ n ω) with hw
  have hwF : StronglyMeasurable[F n] w :=
    ((hmF.sub stronglyMeasurable_const).const_smul _).add
      ((hL.continuous.comp_stronglyMeasurable hmF).const_smul _)
  have hw2 : MemLp w 2 μ := (hx.const_smul _).add (hH.const_smul _)
  set A : Ω → ℝ := fun ω ↦ ‖θ n ω - θ₀‖ ^ 2 - 2 * a n * inner ℝ (θ n ω - θ₀) (h (θ n ω)) +
    a n ^ 2 * ‖h (θ n ω)‖ ^ 2 + a n ^ 2 * ‖M (n + 1) ω‖ ^ 2 with hA
  have hsq {f : Ω → E} (hf : MemLp f 2 μ) : Integrable (fun ω ↦ ‖f ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hAint : Integrable A μ :=
    (((hsq hx).sub ((integrable_inner_of_memLp_two hx hH).const_mul _)).add
      ((hsq hH).const_mul _)).add ((hsq hN).const_mul _)
  have hBint : Integrable (fun ω ↦ inner ℝ (w ω) (M (n + 1) ω)) μ :=
    integrable_inner_of_memLp_two hw2 hN
  have hpt : (fun ω ↦ ‖θ (n + 1) ω - θ₀‖ ^ 2) =ᵐ[μ]
      fun ω ↦ A ω + inner ℝ (w ω) (M (n + 1) ω) := by
    filter_upwards [hRM.recursion n] with ω hω
    rw [hω, norm_sub_smul_add_sq]
  have hAle (ω : Ω) : A ω ≤ (1 + a n ^ 2 * L ^ 2 - 2 * a n * m) * ‖θ n ω - θ₀‖ ^ 2 +
      a n ^ 2 * ‖M (n + 1) ω‖ ^ 2 := by
    have h1 := hdrift (θ n ω)
    have h2 : ‖h (θ n ω)‖ ≤ L * ‖θ n ω - θ₀‖ := by
      have := hL.norm_sub_le (θ n ω) θ₀
      rwa [hz, sub_zero] at this
    have h3 : ‖h (θ n ω)‖ ^ 2 ≤ L ^ 2 * ‖θ n ω - θ₀‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have ha := (hRM.step_pos n).le
    simp only [hA]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg (a n)), mul_le_mul_of_nonneg_left h1 ha]
  have hVint : Integrable (fun ω ↦ ‖θ n ω - θ₀‖ ^ 2) μ := hsq hx
  rw [setIntegral_congr_ae (F.le n s hs) (ae_imp_of_ae_restrict (ae_restrict_of_ae hpt)),
    integral_add hAint.integrableOn hBint.integrableOn,
    setIntegral_inner_eq_zero_of_condExp hN (hRM.condExp_noise n) hwF hw2 hs, add_zero]
  calc ∫ ω in s, A ω ∂μ ≤ ∫ ω in s, ((1 + a n ^ 2 * L ^ 2 - 2 * a n * m) * ‖θ n ω - θ₀‖ ^ 2 +
        a n ^ 2 * ‖M (n + 1) ω‖ ^ 2) ∂μ :=
        setIntegral_mono hAint.integrableOn
          ((hVint.const_mul _).add ((hsq hN).const_mul _)).integrableOn hAle
    _ = (1 + a n ^ 2 * L ^ 2 - 2 * a n * m) * ∫ ω in s, ‖θ n ω - θ₀‖ ^ 2 ∂μ +
        a n ^ 2 * ∫ ω in s, ‖M (n + 1) ω‖ ^ 2 ∂μ := by
        rw [integral_add (hVint.const_mul _).integrableOn ((hsq hN).const_mul _).integrableOn,
          integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have := setIntegral_norm_sq_le_of_condExp hN (hRM.condExp_sq_noise_le n) hs
        have ha2 := sq_nonneg (a n)
        nlinarith

/-- A real supermartingale bounded below by `-C` is bounded in `L¹`, with the bound expressed
for its negation, a submartingale. -/
private theorem eLpNorm_neg_le_of_supermartingale {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {Y : ℕ → Ω → ℝ}
    (hsup : Supermartingale Y F μ) {C : ℝ} (hC : 0 ≤ C) (hlow : ∀ n ω, -C ≤ Y n ω) (n : ℕ) :
    eLpNorm ((-Y) n) 1 μ ≤ ENNReal.ofReal (∫ ω, Y 0 ω ∂μ + 2 * C) := by
  have hYn : Integrable ((-Y) n) μ := (hsup.integrable n).neg
  rw [eLpNorm_one_eq_lintegral_enorm hYn.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hYn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : ∫ ω, Y n ω ∂μ ≤ ∫ ω, Y 0 ω ∂μ := by
    simpa using hsup.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  calc ∫ ω, ‖(-Y) n ω‖ ∂μ ≤ ∫ ω, (Y n ω + 2 * C) ∂μ :=
        integral_mono hYn.norm ((hsup.integrable n).add (integrable_const _)) fun ω ↦ by
          simp only [Pi.neg_apply, norm_neg, Real.norm_eq_abs]
          have := hlow n ω
          rw [abs_le]
          constructor <;> linarith
    _ = ∫ ω, Y n ω ∂μ + 2 * C := by
        rw [integral_add (hsup.integrable n) (integrable_const _), integral_const]
        simp
    _ ≤ ∫ ω, Y 0 ω ∂μ + 2 * C := by linarith

end RobbinsMonroProof

section Robbins

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Predictable clipping of bounded iterates gives almost-sure convergence of each continuous
linear projection of the accumulated Robbins–Monro noise. -/
theorem IsRobbinsMonroScheme.ae_exists_tendsto_sum_noise_proj
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) (L : E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k * L (M (k + 1) ω))
      atTop (𝓝 c) := by
  classical
  let A : ℕ → ℕ → Set Ω := fun R n ↦ {ω | ‖θ n ω‖ ≤ R}
  have hA (R n : ℕ) : MeasurableSet[F n] (A R n) := by
    have hm := hRM.measurable_iterate n
    let _ : MeasurableSpace Ω := F n
    exact measurableSet_le hm.norm measurable_const
  have hP (R n : ℕ) : MeasurableSet (A R n) := F.le n _ (hA R n)
  have hL2 (n : ℕ) : MemLp (L ∘ M (n + 1)) 2 μ := L.comp_memLp' (hRM.memLp_noise _)
  have hLc (n : ℕ) : μ[L ∘ M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0 := by
    have hh := L.comp_condExp_comm ((hRM.memLp_noise (n + 1)).integrable one_le_two)
      (m := F n)
    filter_upwards [hh, hRM.condExp_noise n] with ω hω hzero
    simpa [Function.comp_def, hzero] using hω.symm
  let D : ℕ → ℕ → Ω → ℝ := fun R n ↦ (A R n).indicator
    (fun ω ↦ a n * L (M (n + 1) ω))
  have hD2 (R n : ℕ) : MemLp (D R n) 2 μ :=
    ((hL2 n).const_mul (a n)).indicator (hP R n).nullMeasurableSet
  have hDm (R n : ℕ) : StronglyMeasurable[F (n + 1)] (D R n) := by
    apply StronglyMeasurable.indicator _ (F.mono (Nat.le_succ n) _ (hA R n))
    exact (L.continuous.stronglyMeasurable.comp_measurable
      (hRM.measurable_noise (n + 1))).const_mul (a n)
  have hDc (R n : ℕ) : μ[D R n | F n] =ᵐ[μ] fun _ ↦ 0 := by
    have hmul : μ[(fun ω ↦ a n * L (M (n + 1) ω)) | F n] =ᵐ[μ] fun _ ↦ 0 := by
      have hh := condExp_smul (μ := μ) (a n) (L ∘ M (n + 1)) (F n)
      change μ[(a n) • (L ∘ M (n + 1)) | F n] =ᵐ[μ] fun _ ↦ 0
      filter_upwards [hh, hLc n] with ω hω hzero
      simpa only [Pi.smul_apply, smul_eq_mul, hzero, mul_zero] using hω
    have hh := condExp_indicator (((hL2 n).integrable one_le_two).const_mul (a n)) (hA R n)
    filter_upwards [hh, hmul] with ω hω hzero
    change μ[(A R n).indicator (fun x ↦ a n * (L ∘ M (n + 1)) x) | F n] ω = 0
    rw [hω]
    by_cases hmem : ω ∈ A R n <;> simp [hmem, hzero]
  have hsecond (R n : ℕ) : (∫ ω, D R n ω ^ 2 ∂μ) ≤
      (a n) ^ 2 * ‖L‖ ^ 2 * (|K| * (1 + (R : ℝ) ^ 2)) := by
    have hN : Integrable (fun ω ↦ ‖M (n + 1) ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hRM.memLp_noise _).aestronglyMeasurable).1
        (hRM.memLp_noise _)
    have hNbound : (∫ ω in A R n, ‖M (n + 1) ω‖ ^ 2 ∂μ) ≤
        |K| * (1 + (R : ℝ) ^ 2) := by
      rw [← setIntegral_condExp (F.le n) hN (hA R n)]
      calc _ ≤ ∫ ω in A R n, |K| * (1 + (R : ℝ) ^ 2) ∂μ := by
              apply setIntegral_mono_ae_restrict integrable_condExp.integrableOn
                (integrable_const _).integrableOn
              filter_upwards [ae_restrict_of_ae (hRM.condExp_sq_noise_le n),
                ae_restrict_mem (hP R n)] with ω hω hmem
              have hnorm : ‖θ n ω‖ ≤ (R : ℝ) := hmem
              have hsquare : ‖θ n ω‖ ^ 2 ≤ (R : ℝ) ^ 2 :=
                sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _) |>.2 hnorm
              calc _ ≤ K * (1 + ‖θ n ω‖ ^ 2) := hω
                _ ≤ |K| * (1 + ‖θ n ω‖ ^ 2) :=
                  mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
                _ ≤ |K| * (1 + (R : ℝ) ^ 2) := by gcongr
        _ ≤ |K| * (1 + (R : ℝ) ^ 2) := by
          rw [setIntegral_const, smul_eq_mul]
          exact mul_le_of_le_one_left (by positivity) measureReal_le_one
    have hid : (fun ω ↦ D R n ω ^ 2) = (A R n).indicator
        (fun ω ↦ (a n * L (M (n + 1) ω)) ^ 2) := by
      funext ω
      by_cases hmem : ω ∈ A R n <;> simp [D, hmem]
    rw [hid, integral_indicator (hP R n)]
    calc _ ≤ ∫ ω in A R n, (a n) ^ 2 * ‖L‖ ^ 2 * ‖M (n + 1) ω‖ ^ 2 ∂μ := by
            apply integral_mono (((hL2 n).const_mul (a n)).integrable_sq.integrableOn)
              ((hN.const_mul _).integrableOn)
            intro ω
            change (a n * L (M (n + 1) ω)) ^ 2 ≤
              (a n) ^ 2 * ‖L‖ ^ 2 * ‖M (n + 1) ω‖ ^ 2
            have hh := L.le_opNorm (M (n + 1) ω)
            have hsquare : |L (M (n + 1) ω)| ^ 2 ≤ (‖L‖ * ‖M (n + 1) ω‖) ^ 2 := by
              exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (by simpa using hh)
            rw [sq_abs, mul_pow] at hsquare
            nlinarith [sq_nonneg (a n), mul_le_mul_of_nonneg_left hsquare (sq_nonneg (a n))]
      _ = (a n) ^ 2 * ‖L‖ ^ 2 * ∫ ω in A R n, ‖M (n + 1) ω‖ ^ 2 ∂μ :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hNbound (by positivity)
  have hsum (R : ℕ) : Summable fun n ↦ ∫ ω, D R n ω ^ 2 ∂μ :=
    Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
      (hsecond R) ((hRM.summable_sq_step.mul_right (‖L‖ ^ 2)).mul_right _)
  have hconv : ∀ R : ℕ, ∀ᵐ ω ∂μ, ∃ c,
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, D R k ω) atTop (𝓝 c) := fun R ↦
    ae_exists_tendsto_sum_martingaleDifference μ F (D R) (hDm R) (hD2 R) (hDc R) (hsum R)
  filter_upwards [ae_all_iff.2 hconv, hbdd] with ω hω hbω
  obtain ⟨B, hB⟩ := hbω
  obtain ⟨R, hR⟩ := exists_nat_ge B
  obtain ⟨c, hc⟩ := hω R
  refine ⟨c, hc.congr fun n ↦ Finset.sum_congr rfl fun k hk ↦ ?_⟩
  have hmem : ω ∈ A R k := (hB (mem_range_self k)).trans hR
  simp [D, hmem]


/-- For almost-surely bounded Robbins–Monro iterates in finite dimension, the accumulated
weighted martingale noise converges almost surely. -/
theorem IsRobbinsMonroScheme.ae_exists_tendsto_sum_noise
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k • M (k + 1) ω)
      atTop (𝓝 c) := by
  classical
  let e := (Module.finBasis ℝ E).equivFunL
  let L (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hproj (i : Fin (Module.finrank ℝ E)) :=
    hRM.ae_exists_tendsto_sum_noise_proj μ F h a K θ M hbdd (L i)
  filter_upwards [ae_all_iff.2 hproj] with ω hω
  choose c hc using hω
  have hconv : Tendsto (fun n i ↦ ∑ k ∈ Finset.range n, a k * L i (M (k + 1) ω))
      atTop (𝓝 c) := tendsto_pi_nhds.2 hc
  have hh := e.symm.continuous.continuousAt.tendsto.comp hconv
  refine ⟨e.symm c, hh.congr fun n ↦ ?_⟩
  apply e.injective
  simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  ext i
  simp [L, map_sum, map_smul]

/-- GAPS 104.40: almost-sure convergence of the Robbins–Monro recursion. If `h` is Lipschitz with
`h θ⋆ = 0` and `⟪θ - θ⋆, h θ⟫ ≥ m ‖θ - θ⋆‖²` for some `m > 0`, the initial state is square
integrable, and the conditional noise variance is bounded by a constant `K`, then `θₙ → θ⋆`
almost surely. -/
theorem ae_tendsto_robbins_monro (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun _ ↦ K) θ M)
    (hθ2 : MemLp (θ 0) 2 μ) (L : ℝ≥0) (hL : LipschitzWith L h) (θ₀ : E)
    (hz : h θ₀ = 0) (m : ℝ) (hm : 0 < m)
    (hdrift : ∀ x, m * ‖x - θ₀‖ ^ 2 ≤ inner ℝ (x - θ₀) (h x)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ θ n ω) atTop (𝓝 θ₀) := by
  set P : ℕ → ℝ := fun k ↦ ∏ j ∈ Finset.range k, (1 + a j ^ 2 * L ^ 2) with hP
  set V : ℕ → Ω → ℝ := fun k ω ↦ ‖θ k ω - θ₀‖ ^ 2 with hV
  set S : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, K * a k ^ 2 / P (k + 1) with hS
  set Y : ℕ → Ω → ℝ := fun n ω ↦
    V n ω / P n + ∑ k ∈ Finset.range n, 2 * m * a k * V k ω / P (k + 1) - S n with hY
  have hP1 (n : ℕ) : 1 ≤ P n :=
    Finset.one_le_prod₀ fun j _ ↦ le_add_of_nonneg_right (by positivity)
  have hP0 (n : ℕ) : 0 < P n := lt_of_lt_of_le one_pos (hP1 n)
  have hPsucc (n : ℕ) : P (n + 1) = P n * (1 + a n ^ 2 * L ^ 2) := Finset.prod_range_succ _ _
  set sa2 := ∑' k, a k ^ 2
  have hsumsq := hRM.summable_sq_step
  have hPb (n : ℕ) : P n ≤ Real.exp (L ^ 2 * sa2) := by
    calc P n ≤ ∏ j ∈ Finset.range n, Real.exp (a j ^ 2 * L ^ 2) :=
          Finset.prod_le_prod₀ (fun j _ ↦ by positivity) fun j _ ↦ by
            linarith [Real.add_one_le_exp (a j ^ 2 * L ^ 2)]
      _ = Real.exp (L ^ 2 * ∑ j ∈ Finset.range n, a j ^ 2) := by
          rw [← Real.exp_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
      _ ≤ Real.exp (L ^ 2 * sa2) := by
          gcongr
          exact hsumsq.sum_le_tsum _ fun j _ ↦ sq_nonneg _
  -- Square integrability and measurability.
  have hθ (n : ℕ) := memLp_two_robbinsMonro_iterate hRM hθ2 hL n
  have hVint (n : ℕ) : Integrable (V n) μ :=
    (memLp_two_iff_integrable_sq_norm ((hθ n).sub (memLp_const θ₀)).aestronglyMeasurable).1
      ((hθ n).sub (memLp_const θ₀))
  have hVm (k n : ℕ) (hk : k ≤ n) : Measurable[F n] (V k) := by
    have h1 : Measurable[F n] (θ k) := (hRM.measurable_iterate k).mono (F.mono hk) le_rfl
    exact (continuous_norm.measurable.comp (h1.sub_const θ₀)).pow_const 2
  have hYint (n : ℕ) : Integrable (Y n) μ := by
    refine (((hVint n).div_const _).add (integrable_finsetSum _ fun k _ ↦
      ((hVint k).const_mul _).div_const _)).sub (integrable_const _)
  have hYadapt : StronglyAdapted F Y := by
    intro n
    refine Measurable.stronglyMeasurable ?_
    refine (((hVm n n le_rfl).div_const _).add (Finset.measurable_sum _ fun k hk ↦
      ((hVm k n (Finset.mem_range.1 hk).le).const_mul _).div_const _)).sub_const _
  have hYstep (n : ℕ) (ω : Ω) : Y (n + 1) ω = Y n ω +
      (V (n + 1) ω - (1 + a n ^ 2 * L ^ 2) * V n ω + 2 * m * a n * V n ω - K * a n ^ 2) /
        P (n + 1) := by
    simp only [hY, hS, Finset.sum_range_succ]
    rw [hPsucc n]
    have := hP0 n
    have : 0 < 1 + a n ^ 2 * L ^ 2 := by positivity
    field_simp
    ring
  have hsup : Supermartingale Y F μ := by
    refine supermartingale_of_setIntegral_succ_le hYadapt hYint fun n s hs ↦ ?_
    have hstep := setIntegral_sq_dist_succ_le hRM hθ2 hL hz hdrift n hs
    set G : Ω → ℝ := fun ω ↦ V (n + 1) ω - (1 + a n ^ 2 * L ^ 2) * V n ω +
      2 * m * a n * V n ω - K * a n ^ 2 with hG
    have hGint : Integrable G μ :=
      (((hVint (n + 1)).sub ((hVint n).const_mul _)).add ((hVint n).const_mul _)).sub
        (integrable_const _)
    have hGs : ∫ ω in s, G ω ∂μ = ∫ ω in s, V (n + 1) ω ∂μ -
        (1 + a n ^ 2 * L ^ 2) * ∫ ω in s, V n ω ∂μ + 2 * m * a n * ∫ ω in s, V n ω ∂μ -
        μ.real s * (K * a n ^ 2) := by
      rw [hG, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
        setIntegral_const, smul_eq_mul]
      · exact (hVint (n + 1)).integrableOn
      · exact ((hVint n).const_mul _).integrableOn
      · exact ((hVint (n + 1)).sub ((hVint n).const_mul _)).integrableOn
      · exact ((hVint n).const_mul _).integrableOn
      · exact (((hVint (n + 1)).sub ((hVint n).const_mul _)).add
          ((hVint n).const_mul _)).integrableOn
      · exact (integrable_const _).integrableOn
    have hfun : Y (n + 1) = fun ω ↦ Y n ω + G ω / P (n + 1) := funext (hYstep n)
    rw [hfun, integral_add (hYint n).integrableOn (hGint.div_const _).integrableOn, integral_div,
      hGs]
    have hnum : ∫ ω in s, V (n + 1) ω ∂μ - (1 + a n ^ 2 * L ^ 2) * ∫ ω in s, V n ω ∂μ +
        2 * m * a n * ∫ ω in s, V n ω ∂μ - μ.real s * (K * a n ^ 2) ≤ 0 := by
      simp only [hV] at hstep ⊢
      nlinarith
    have := div_nonpos_of_nonpos_of_nonneg hnum (hP0 (n + 1)).le
    linarith
  -- A uniform `L¹` bound.
  have hsa2 : 0 ≤ sa2 := tsum_nonneg fun _ ↦ sq_nonneg _
  set C₁ := |K| * sa2 with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg (abs_nonneg _) hsa2
  have hterm (k : ℕ) : ‖K * a k ^ 2 / P (k + 1)‖ ≤ |K| * a k ^ 2 := by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (a k)), abs_of_pos (hP0 _)]
    exact div_le_self (by positivity) (hP1 _)
  have hSb (n : ℕ) : |S n| ≤ C₁ := by
    calc |S n| ≤ ∑ k ∈ Finset.range n, |K * a k ^ 2 / P (k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, |K| * a k ^ 2 := Finset.sum_le_sum fun k _ ↦ hterm k
      _ = |K| * ∑ k ∈ Finset.range n, a k ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ C₁ := mul_le_mul_of_nonneg_left (hsumsq.sum_le_tsum _ fun _ _ ↦ sq_nonneg _)
          (abs_nonneg _)
  have hVnn (k : ℕ) (ω : Ω) : 0 ≤ V k ω := by positivity
  have hYlow (n : ℕ) (ω : Ω) : -C₁ ≤ Y n ω := by
    have h1 : 0 ≤ V n ω / P n := div_nonneg (hVnn n ω) (hP0 n).le
    have h2 : 0 ≤ ∑ k ∈ Finset.range n, 2 * m * a k * V k ω / P (k + 1) :=
      Finset.sum_nonneg fun k _ ↦ div_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (hRM.step_pos k).le) (hVnn k ω)) (hP0 _).le
    have h3 := (abs_le.1 (hSb n)).2
    simp only [hY]
    linarith
  have hbdd := eLpNorm_neg_le_of_supermartingale hsup hC₁0 hYlow
  have hconv := hsup.neg.ae_tendsto_limitProcess hbdd
  have hsumm : Summable fun k ↦ K * a k ^ 2 / P (k + 1) :=
    Summable.of_norm_bounded (hsumsq.mul_left |K|) hterm
  have hSconv : Tendsto S atTop (𝓝 (∑' k, K * a k ^ 2 / P (k + 1))) :=
    hsumm.hasSum.tendsto_sum_nat
  filter_upwards [hconv] with ω hω
  have hYω : Tendsto (fun n ↦ Y n ω) atTop (𝓝 (-(F.limitProcess (-Y) μ ω))) := by
    simpa using hω.neg
  have hV0 := tendsto_zero_of_tendsto_robbinsSiegmund (V := fun n ↦ V n ω) (P := P) (c := 2 * m)
    (fun n ↦ hVnn n ω) hRM.step_pos hRM.tendsto_sum_step hP1 hPb (by positivity) hSconv hYω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := hV0.sqrt
  rw [Real.sqrt_zero] at this
  refine this.congr fun n ↦ ?_
  simp only [hV]
  exact Real.sqrt_sq (norm_nonneg _)

/-- GAPS 104.49: Benaïm's limit-set theorem. Under Robbins–Monro steps, martingale-difference noise
with conditional second moment at most `K(1 + ‖θₙ‖²)`, a Lipschitz field, and a.s. bounded iterates,
the limit set is a.s. a compact connected internally chain transitive invariant set of the flow
of `θ' = -h(θ)`. -/
theorem ae_isInternallyChainTransitive_limitSet (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) :
    ∀ᵐ ω ∂μ, IsCompact (limitSet (θ · ω)) ∧ IsConnected (limitSet (θ · ω)) ∧
      IsInternallyChainTransitive Φ (limitSet (θ · ω)) := by
  sorry

/-- GAPS 104.49: if the only compact connected internally chain transitive invariant sets are
equilibria, the iterates converge almost surely to a possibly random equilibrium. -/
theorem ae_tendsto_equilibrium_of_chainTransitive (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖))
    (hequil : ∀ A : Set E, IsCompact A → IsConnected A →
      IsInternallyChainTransitive Φ A → ∃ x, A = {x} ∧ h x = 0) :
    ∀ᵐ ω ∂μ, ∃ x, h x = 0 ∧ Tendsto (θ · ω) atTop (𝓝 x) := by
  have hlimit := ae_isInternallyChainTransitive_limitSet μ F h a K θ M hRM L hL Φ hΦ hbdd
  filter_upwards [hlimit, hbdd] with ω hω hbω
  obtain ⟨x, hx, heq⟩ := hequil _ hω.1 hω.2.1 hω.2.2
  exact ⟨x, heq, tendsto_of_limitSet_eq_singleton _ hbω x hx⟩

/-- GAPS 104.49: the interpolated process is almost surely an asymptotic pseudotrajectory of the
flow: `sup_{0 ≤ u ≤ T} ‖θ̄(s + u) - Φᵤ(θ̄(s))‖ → 0` as `s → ∞`, for every `T > 0`. -/
theorem ae_asymptotic_pseudotrajectory (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (h : E → E) (a : ℕ → ℝ) (K : ℝ)
    (θ M : ℕ → Ω → E) (hRM : IsRobbinsMonroScheme μ F h a (fun x ↦ K * (1 + ‖x‖ ^ 2)) θ M)
    (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (range fun n ↦ ‖θ n ω‖)) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ s in atTop, ∀ u ∈ Icc 0 T,
      ‖stochasticApproxInterp a (θ · ω) (s + u) -
        Φ u (stochasticApproxInterp a (θ · ω) s)‖ ≤ ε := by
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have hh := hRM.summable_sq_step.tendsto_atTop_zero.sqrt
    rw [Real.sqrt_zero] at hh
    exact hh.congr fun n ↦ Real.sqrt_sq (hRM.step_pos n).le
  filter_upwards [hRM.ae_exists_tendsto_sum_noise μ F h a K θ M hbdd,
    hbdd, ae_all_iff.2 hRM.recursion] with ω hnoise hbω hrecω
  obtain ⟨c, hc⟩ := hnoise
  let S : ℕ → E := fun n ↦ ∑ k ∈ Finset.range n, a k • M (k + 1) ω
  have hSsucc (n : ℕ) : S (n + 1) - S n = a n • M (n + 1) ω := by
    dsimp [S]
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  apply asymptotic_pseudotrajectory_stochasticApproxInterp hRM.step_pos ha0
    hRM.tendsto_sum_step h L hL Φ hΦ (θ · ω) S hc hbω _ T hT
  intro n
  rw [hrecω n, hSsucc, smul_add]
  abel

end Robbins

/-- The interpolation times start at zero. -/
@[simp] theorem stochasticApproxTime_zero (a : ℕ → ℝ) : stochasticApproxTime a 0 = 0 := by
  simp [stochasticApproxTime]

end CKSD
