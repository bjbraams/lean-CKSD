module

public import CKSD.Bayes.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import TauCeti.Analysis.ODE.Gronwall

/-!
# Synchronous coupling for bounded Lipschitz interactions

Averaging a bounded continuous interaction against a process with continuous sample paths gives
a continuous time-position drift. Same-forcing solutions with Lipschitz base drift have a
deterministically bounded difference on every bounded time interval. Coupling the arguments of
the interaction then bounds the drift difference by the pointwise distance and its expectation.

A probabilistic integral Grönwall argument gives nonlinear same-forcing uniqueness. Joint
almost-everywhere measurability and Fubini are justified from measurable time sections,
almost-sure path continuity, and the deterministic difference bound.

Mathlib supplies dominated convergence, product integration, and measurable modifications;
TauCeti supplies `TauCeti.le_mul_exp_of_le_add_mul_integral`.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- Averaging a bounded continuous interaction against a continuous process gives a continuous
time-position drift, with no moment condition on the process. -/
theorem continuous_integral_interaction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    (hK : Continuous (Function.uncurry K)) {κ : ℝ} (hκ : ∀ x y, ‖K x y‖ ≤ κ)
    (Y : ℝ → Ω → E) (hY : ∀ t, Measurable (Y t))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) :
    Continuous fun p : ℝ × E ↦ ∫ ω, K p.2 (Y p.1 ω) ∂P := by
  apply continuous_of_dominated (bound := fun _ ↦ κ)
  · intro p
    exact (hK.measurable.comp (measurable_const.prodMk (hY p.1))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ fun ω ↦ hκ _ _
  · exact integrable_const _
  · filter_upwards [hcont] with ω hω
    exact hK.comp (continuous_snd.prodMk (hω.comp continuous_fst))

/-- The norm of the mean of a bounded interaction is bounded by the same constant. -/
theorem norm_integral_interaction_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E) {κ : ℝ}
    (hκ : ∀ x y, ‖K x y‖ ≤ κ) (Y : Ω → E) (x : E) :
    ‖∫ ω, K x (Y ω) ∂P‖ ≤ κ := by
  simpa using norm_integral_le_of_norm_le_const (μ := P) (f := fun ω ↦ K x (Y ω))
    (ae_of_all _ fun ω ↦ hκ x (Y ω))

/-- Two integral equations with the same additive forcing and bounded interaction terms differ
by a deterministic bound, independent of their initial data and the forcing. -/
theorem norm_sub_le_of_bounded_interactions_on_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b₀ : E → E) {L : ℝ≥0} (hb₀ : LipschitzWith L b₀)
    (v w : ℝ → E → E) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hvb : ∀ t x, ‖v t x‖ ≤ κ) (hwb : ∀ t x, ‖w t x‖ ≤ κ)
    (x y : ℝ → E) (hx : Continuous x) (hy : Continuous y)
    {T : ℝ} (hT : 0 ≤ T)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, x t - y t = ∫ s in (0 : ℝ)..t,
      (b₀ (x s) + v s (x s)) - (b₀ (y s) + w s (y s)))
    :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤ 2 * κ * T * Real.exp (L * T) := by
  let F : ℝ → E := fun s ↦ (b₀ (x s) + v s (x s)) - (b₀ (y s) + w s (y s))
  have hF : Continuous F := (hb₀.continuous.comp hx |>.add (hv.comp (continuous_id.prodMk hx))).sub
    (hb₀.continuous.comp hy |>.add (hw.comp (continuous_id.prodMk hy)))
  have hnorm (s : ℝ) : ‖F s‖ ≤ L * ‖x s - y s‖ + 2 * κ := by
    have hb := hb₀.norm_sub_le (x s) (y s)
    calc
      ‖F s‖ ≤ ‖b₀ (x s) - b₀ (y s)‖ + (‖v s (x s)‖ + ‖w s (y s)‖) := by
        dsimp [F]
        rw [show b₀ (x s) + v s (x s) - (b₀ (y s) + w s (y s)) =
          (b₀ (x s) - b₀ (y s)) + (v s (x s) - w s (y s)) by abel]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ _ := by linarith [hvb s (x s), hwb s (y s)]
  have hφ : Continuous (fun t ↦ ‖x t - y t‖) := (hx.sub hy).norm
  have hineq (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖x t - y t‖ ≤ 2 * κ * T + L * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
    rw [heq t ht]
    calc ‖∫ s in (0 : ℝ)..t, F s‖ ≤ ∫ s in (0 : ℝ)..t, ‖F s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in (0 : ℝ)..t, (L : ℝ) * ‖x s - y s‖ + 2 * κ :=
        intervalIntegral.integral_mono ht.1 (hF.norm.intervalIntegrable _ _)
          (((hφ.const_mul _).add continuous_const).intervalIntegrable _ _) hnorm
      _ = L * (∫ s in (0 : ℝ)..t, ‖x s - y s‖) + 2 * κ * t := by
        rw [intervalIntegral.integral_add ((hφ.const_mul _).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      _ ≤ _ := by nlinarith [ht.2]
  have hgron := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn L.coe_nonneg hineq
  intro t ht
  refine (hgron t ht).trans ?_
  rw [sub_zero]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.2
  exact mul_le_mul_of_nonneg_left ht.2 L.coe_nonneg

/-- Two integral equations with the same additive forcing and bounded interaction terms differ
by a deterministic bound, independent of their initial data and the forcing. -/
theorem norm_sub_le_of_bounded_interactions {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b₀ : E → E) {L : ℝ≥0} (hb₀ : LipschitzWith L b₀)
    (v w : ℝ → E → E) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hvb : ∀ t x, ‖v t x‖ ≤ κ) (hwb : ∀ t x, ‖w t x‖ ≤ κ)
    (x y : ℝ → E) (hx : Continuous x) (hy : Continuous y)
    (heq : ∀ t ≥ 0, x t - y t = ∫ s in (0 : ℝ)..t,
      (b₀ (x s) + v s (x s)) - (b₀ (y s) + w s (y s)))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖x t - y t‖ ≤ 2 * κ * T * Real.exp (L * T) := by
  exact norm_sub_le_of_bounded_interactions_on_Icc b₀ hb₀ v w hv hw hκ hvb hwb x y hx hy hT
    (fun t ht ↦ heq t ht.1)

/-- Coupling the variables inside the interaction bounds the difference of their averaged
interactions by their mean distance. -/
theorem norm_integral_interaction_sub_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    {L : ℝ≥0} (hK : LipschitzWith L (Function.uncurry K)) {κ : ℝ}
    (hκ : ∀ x y, ‖K x y‖ ≤ κ)
    (Y Z : Ω → E) (hY : Measurable Y) (hZ : Measurable Z)
    (hYZ : Integrable (fun ω ↦ ‖Y ω - Z ω‖) P) (x y : E) :
    ‖(∫ ω, K x (Y ω) ∂P) - ∫ ω, K y (Z ω) ∂P‖ ≤
      L * (‖x - y‖ + ∫ ω, ‖Y ω - Z ω‖ ∂P) := by
  have hi (x : E) (Y : Ω → E) (hY : Measurable Y) : Integrable (fun ω ↦ K x (Y ω)) P :=
    Integrable.of_bound (hK.continuous.measurable.comp (measurable_const.prodMk hY)).aestronglyMeasurable
      κ (ae_of_all _ fun ω ↦ hκ _ _)
  rw [← integral_sub (hi x Y hY) (hi y Z hZ)]
  calc ‖∫ ω, K x (Y ω) - K y (Z ω) ∂P‖ ≤ ∫ ω, ‖K x (Y ω) - K y (Z ω)‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (L : ℝ) * (‖x - y‖ + ‖Y ω - Z ω‖) ∂P := by
      apply integral_mono (hi x Y hY |>.sub (hi y Z hZ) |>.norm)
        ((integrable_const _).add hYZ |>.const_mul (L : ℝ))
      intro ω
      refine (hK.norm_sub_le (x, Y ω) (y, Z ω)).trans ?_
      apply mul_le_mul_of_nonneg_left ?_ L.coe_nonneg
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
      change max ‖x - y‖ ‖Y ω - Z ω‖ ≤ ‖x - y‖ + ‖Y ω - Z ω‖
      apply max_le <;> nlinarith [norm_nonneg (x - y), norm_nonneg (Y ω - Z ω)]
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const _) hYZ]
      simp

/-- A process with measurable time sections and almost surely continuous paths is jointly
almost everywhere strongly measurable on every product with a time measure. -/
theorem aestronglyMeasurable_uncurry_of_ae_continuous {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (ν : Measure ℝ) (Y : ℝ → Ω → E) (hY : ∀ t, Measurable (Y t))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) :
    AEStronglyMeasurable (Function.uncurry Y) (ν.prod P) := by
  classical
  obtain ⟨N, hNsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let Z : ℝ → Ω → E := fun t ω ↦ if ω ∈ N then 0 else Y t ω
  have hZmeas : ∀ t, Measurable (Z t) := fun t ↦
    Measurable.ite hNm measurable_const (hY t)
  have hZcont : ∀ ω, Continuous (fun t ↦ Z t ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa only [Z, ite_eq_left hω] using continuous_const
    · have hgood : Continuous (fun t ↦ Y t ω) := by
        by_contra h
        exact hω (hNsub h)
      simpa only [Z, ite_eq_right hω] using hgood
  have hZj : Measurable (Function.uncurry Z) :=
    measurable_uncurry_of_continuous_of_measurable hZcont hZmeas
  refine hZj.aestronglyMeasurable.congr ?_
  have hnotN : ∀ᵐ ω ∂P, ω ∉ N := compl_mem_ae_iff.mpr hN
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν)).ae hnotN] with p hp
  simp [Function.uncurry, Z, hp]

/-- A nonnegative continuous process bounded on a time interval vanishes if its pathwise bound
is an integral of itself plus an integral of its mean, both starting from zero. -/
theorem ae_eq_zero_of_le_integral_add_integral_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hX0 : ∀ t ω, 0 ≤ X t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    {T D A B : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, X t ω ≤ D)
    (hineq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      X t ω ≤ A * (∫ s in (0 : ℝ)..t, X s ω) + B * (∫ s in (0 : ℝ)..t, ∫ z, X s z ∂P)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, X t ω = 0 := by
  let F : ℝ → ℝ := fun t ↦ ∫ ω, X t ω ∂P
  have hInt (t : ℝ) (ht : t ∈ Icc 0 T) : Integrable (X t) P :=
    Integrable.of_bound (hX t).aestronglyMeasurable D (hbound.mono fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 t ω)]
      exact hω t ht)
  have hF : ContinuousOn F (Icc 0 T) := by
    apply continuousOn_of_dominated (bound := fun _ ↦ D)
    · intro t ht
      exact (hX t).aestronglyMeasurable
    · intro t ht
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 t ω)]
      exact hω t ht
    · exact integrable_const _
    · exact hcont.mono fun ω hω ↦ hω.continuousOn
  have hmean (t : ℝ) (ht : t ∈ Icc 0 T) : F t ≤ (A + B) * ∫ s in (0 : ℝ)..t, F s := by
    let ν := volume.restrict (Ioc (0 : ℝ) t)
    have hprod : Integrable (Function.uncurry X) (ν.prod P) := by
      apply Integrable.of_bound (aestronglyMeasurable_uncurry_of_ae_continuous P ν X hX hcont) D
      have htime : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) t := ae_restrict_mem measurableSet_Ioc
      filter_upwards [(Measure.quasiMeasurePreserving_fst (ν := P)).ae htime,
        (Measure.quasiMeasurePreserving_snd (μ := ν)).ae hbound] with z hz hω
      change |X z.1 z.2| ≤ D
      rw [abs_of_nonneg (hX0 z.1 z.2)]
      exact hω z.1 ⟨hz.1.le, hz.2.trans ht.2⟩
    have hinner : Integrable (fun ω ↦ ∫ s in (0 : ℝ)..t, X s ω) P := by
      simpa only [intervalIntegral.integral_of_le ht.1, ν, Function.uncurry] using hprod.integral_prod_right
    have hswap : (∫ ω, (∫ s in (0 : ℝ)..t, X s ω) ∂P) = ∫ s in (0 : ℝ)..t, F s := by
      simpa only [intervalIntegral.integral_of_le ht.1, F, ν, Function.uncurry] using (integral_integral_swap hprod).symm
    calc F t ≤ ∫ ω, A * (∫ s in (0 : ℝ)..t, X s ω) + B * (∫ s in (0 : ℝ)..t, F s) ∂P :=
        integral_mono_ae (hInt t ht) ((hinner.const_mul A).add (integrable_const _))
          (hineq.mono fun ω hω ↦ hω t ht)
      _ = (A + B) * ∫ s in (0 : ℝ)..t, F s := by
        rw [integral_add (hinner.const_mul A) (integrable_const _), integral_const_mul, hswap]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        ring
  have hFzero (t : ℝ) (ht : t ∈ Icc 0 T) : F t = 0 := by
    have hgron := TauCeti.le_mul_exp_of_le_add_mul_integral hF (add_nonneg hA hB)
      (c := 0) (by simpa only [zero_add] using hmean) t ht
    simp only [zero_mul] at hgron
    exact le_antisymm hgron (integral_nonneg (hX0 t))
  have hzero (t : ℝ) (ht : t ∈ Icc 0 T) : ∀ᵐ ω ∂P, X t ω = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (hX0 t) (hInt t ht)).1 (hFzero t ht)
    exact h.mono fun ω hω ↦ by simpa only [Pi.zero_apply] using hω
  let c : ℝ → ℝ := fun t ↦ max 0 (min T t)
  have hc : Continuous c := by fun_prop
  have hcmem (t : ℝ) : c t ∈ Icc 0 T :=
    ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hcfix (t : ℝ) (ht : t ∈ Icc 0 T) : c t = t := by
    dsimp only [c]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, X (c q) ω = 0 := ae_all_iff.2 fun q ↦ hzero _ (hcmem _)
  filter_upwards [hcont, hrat] with ω hω hωrat
  have heq : (fun t : ℝ ↦ X (c t) ω) = fun _ ↦ (0 : ℝ) :=
    Rat.denseRange_cast.equalizer (hω.comp hc) continuous_const (funext hωrat)
  intro t ht
  have h := congrFun heq t
  rwa [hcfix t ht] at h

/-- Nonlinear same-forcing uniqueness for a bounded Lipschitz interaction. Neither independence
nor any assumption on the law of the common forcing is needed. -/
theorem ae_eq_of_interaction_integral_eq_on_Icc {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (b₀ : E → E) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀) (K : E → E → E) {L_K : ℝ≥0}
    (hK : LipschitzWith L_K (Function.uncurry K)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X Y : ℝ → Ω → E) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω))
    {T : ℝ} (hT : 0 ≤ T)
    (heq : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, X t ω - Y t ω = ∫ s in (0 : ℝ)..t,
      (b₀ (X s ω) + ∫ z, K (X s ω) (X s z) ∂P) -
        (b₀ (Y s ω) + ∫ z, K (Y s ω) (Y s z) ∂P))
    :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, X t ω = Y t ω := by
  let v : ℝ → E → E := fun t x ↦ ∫ z, K x (X t z) ∂P
  let w : ℝ → E → E := fun t x ↦ ∫ z, K x (Y t z) ∂P
  have hv : Continuous (Function.uncurry v) := continuous_integral_interaction P K hK.continuous hKb X hX hXc
  have hw : Continuous (Function.uncurry w) := continuous_integral_interaction P K hK.continuous hKb Y hY hYc
  have hvb : ∀ t x, ‖v t x‖ ≤ κ := fun t x ↦ norm_integral_interaction_le P K hKb (X t) x
  have hwb : ∀ t x, ‖w t x‖ ≤ κ := fun t x ↦ norm_integral_interaction_le P K hKb (Y t) x
  let δ : ℝ → Ω → ℝ := fun t ω ↦ ‖X t ω - Y t ω‖
  let F : ℝ → ℝ := fun t ↦ ∫ ω, δ t ω ∂P
  let D := 2 * κ * T * Real.exp (L₀ * T)
  have hδm : ∀ t, Measurable (δ t) := fun t ↦ ((hX t).sub (hY t)).norm
  have hδc : ∀ᵐ ω ∂P, Continuous (fun t ↦ δ t ω) := by
    filter_upwards [hXc, hYc] with ω hx hy
    exact (hx.sub hy).norm
  have hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, δ t ω ≤ D := by
    filter_upwards [hXc, hYc, heq] with ω hx hy hω
    exact norm_sub_le_of_bounded_interactions_on_Icc b₀ hb₀ v w hv hw hκ hvb hwb
      (fun t ↦ X t ω) (fun t ↦ Y t ω) hx hy hT hω
  have hδint (t : ℝ) (ht : t ∈ Icc 0 T) : Integrable (δ t) P :=
    Integrable.of_bound (hδm t).aestronglyMeasurable D (hbound.mono fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hω t ht)
  have hFc : ContinuousOn F (Icc 0 T) := by
    apply continuousOn_of_dominated (bound := fun _ ↦ D)
    · intro t ht
      exact (hδm t).aestronglyMeasurable
    · intro t ht
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hω t ht
    · exact integrable_const _
    · exact hδc.mono fun ω hω ↦ hω.continuousOn
  have hineq : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T,
      δ t ω ≤ ((L₀ : ℝ) + L_K) * (∫ s in (0 : ℝ)..t, δ s ω) +
        L_K * (∫ s in (0 : ℝ)..t, F s) := by
    filter_upwards [hXc, hYc, heq] with ω hx hy hω
    intro t ht
    let H : ℝ → E := fun s ↦ (b₀ (X s ω) + v s (X s ω)) - (b₀ (Y s ω) + w s (Y s ω))
    have hH : Continuous H := (hb₀.continuous.comp hx |>.add (hv.comp (continuous_id.prodMk hx))).sub
      (hb₀.continuous.comp hy |>.add (hw.comp (continuous_id.prodMk hy)))
    have hδcont : Continuous (fun s ↦ δ s ω) := (hx.sub hy).norm
    have hFi : IntervalIntegrable F volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1 (hFc.mono (Icc_subset_Icc_right ht.2))
    have hHi (s : ℝ) (hs : s ∈ Icc 0 t) :
        ‖H s‖ ≤ ((L₀ : ℝ) + L_K) * δ s ω + L_K * F s := by
      have hb := hb₀.norm_sub_le (X s ω) (Y s ω)
      have hk := norm_integral_interaction_sub_le P K hK hKb (X s) (Y s) (hX s) (hY s)
        (hδint s ⟨hs.1, hs.2.trans ht.2⟩) (X s ω) (Y s ω)
      have hn : ‖H s‖ ≤ ‖b₀ (X s ω) - b₀ (Y s ω)‖ + ‖v s (X s ω) - w s (Y s ω)‖ := by
        dsimp [H]
        rw [show b₀ (X s ω) + v s (X s ω) - (b₀ (Y s ω) + w s (Y s ω)) =
          (b₀ (X s ω) - b₀ (Y s ω)) + (v s (X s ω) - w s (Y s ω)) by abel]
        exact norm_add_le _ _
      change ‖v s (X s ω) - w s (Y s ω)‖ ≤ L_K * (δ s ω + F s) at hk
      change ‖b₀ (X s ω) - b₀ (Y s ω)‖ ≤ L₀ * δ s ω at hb
      linarith
    change ‖X t ω - Y t ω‖ ≤ _
    rw [hω t ht]
    calc ‖∫ s in (0 : ℝ)..t, H s‖ ≤ ∫ s in (0 : ℝ)..t, ‖H s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in (0 : ℝ)..t, ((L₀ : ℝ) + L_K) * δ s ω + L_K * F s :=
        intervalIntegral.integral_mono_on ht.1 (hH.norm.intervalIntegrable _ _)
          (((hδcont.intervalIntegrable _ _).const_mul _).add (hFi.const_mul _)) hHi
      _ = _ := by
        rw [intervalIntegral.integral_add ((hδcont.intervalIntegrable _ _).const_mul _)
            (hFi.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hzero := ae_eq_zero_of_le_integral_add_integral_mean P δ hδm
    (fun _ _ ↦ norm_nonneg _) hδc hT (by positivity) L_K.coe_nonneg hbound hineq
  filter_upwards [hzero] with ω hω
  intro t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (hω t ht))

/-- Nonlinear same-forcing uniqueness for a bounded Lipschitz interaction. Neither independence
nor any assumption on the law of the common forcing is needed. -/
theorem ae_eq_on_Icc_of_interaction_integral_eq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (b₀ : E → E) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀) (K : E → E → E) {L_K : ℝ≥0}
    (hK : LipschitzWith L_K (Function.uncurry K)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X Y : ℝ → Ω → E) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω))
    (heq : ∀ᵐ ω ∂P, ∀ t ≥ 0, X t ω - Y t ω = ∫ s in (0 : ℝ)..t,
      (b₀ (X s ω) + ∫ z, K (X s ω) (X s z) ∂P) -
        (b₀ (Y s ω) + ∫ z, K (Y s ω) (Y s z) ∂P))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, X t ω = Y t ω := by
  exact ae_eq_of_interaction_integral_eq_on_Icc P b₀ hb₀ K hK hκ hKb X Y hX hY hXc hYc hT
    (heq.mono fun ω hω t ht ↦ hω t ht.1)

end CKSD
