module

public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem

/-!
# Asymptotics: Estimators

Sources: `GAPS.md`, `SYNOPSIS102.md`, and `STRUCTURE102.md`.
Declarations adapted from this project's section drafts.
The delta method uses Mathlib's Lipschitz form of the portmanteau theorem,
`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`. The maximum-likelihood theorem uses
Mathlib's strong law `ProbabilityTheory.strong_law_ae` and central limit theorem
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. The Z-estimator theorem follows
van der Vaart, *Asymptotic Statistics*, Theorem 5.21; the stochastic equicontinuity of the empirical
process over the Lipschitz parameter family is proved by dyadic chaining with Chebyshev's
inequality at each level. The Bahadur representation of the sample quantile is proved by Ghosh's
crossing argument (Ghosh, *Ann. Math. Statist.* 42 (1971)), from Chebyshev's inequality for the
local empirical process; the asymptotic normality of the sample quantile follows by Slutsky.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Weak convergence of probability measures on a pseudometric space follows from convergence of
the integrals of all bounded Lipschitz functions. -/
theorem tendstoWeakly_of_forall_lipschitz {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μs : ℕ → Measure E) (hμs : ∀ n, IsProbabilityMeasure (μs n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (h : ∀ f : E → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
      Tendsto (fun n ↦ ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂ν))) :
    TendstoWeakly μs ν := by
  let μs' : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μs n, hμs n⟩
  let ν' : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have ht : Tendsto μs' atTop (𝓝 ν') :=
    tendsto_iff_forall_lipschitz_integral_tendsto.2 fun f hb hl ↦ h f hb hl
  exact fun f ↦ ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht f

/-- Continuous mapping for the CKSD convergence-in-law predicate. -/
theorem tendstoInDistribution_comp_of_continuous {Ω E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (hZ : ∀ n, Measurable (Z n)) (ν : Measure E)
    (φ : E → F) (hφ : Continuous φ) (h : TendstoInDistribution μ Z ν) :
    TendstoInDistribution μ (fun n ω ↦ φ (Z n ω)) (ν.map φ) := by
  intro f
  have hφm : Measurable φ := hφ.measurable
  have := h (f.compContinuous ⟨φ, hφ⟩)
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at this
  convert this using 1
  · funext n
    change ∫ x, f x ∂(μ.map (φ ∘ Z n)) = _
    rw [← Measure.map_map hφm (hZ n), integral_map hφm.aemeasurable (by fun_prop)]
  · rw [integral_map hφm.aemeasurable (by fun_prop)]

/-- Slutsky-type perturbation: if `Xₙ` converges in law and `Yₙ - Xₙ` converges to `0` in
probability, then `Yₙ` has the same limit law. No separability is assumed; the difference need
not be measurable, since convergence in probability is measured by the outer measure. -/
theorem tendstoInDistribution_of_tendstoInProbabilityConst_sub {Ω F : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ℕ → Ω → F)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ν : Measure F) [IsProbabilityMeasure ν] (hXν : TendstoInDistribution μ X ν)
    (hXY : TendstoInProbabilityConst μ (fun n ω ↦ Y n ω - X n ω) 0) :
    TendstoInDistribution μ Y ν := by
  refine tendstoWeakly_of_forall_lipschitz _
    (fun _ ↦ inferInstance) ν ?_
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  have hfc : Continuous f := hL.continuous
  let fb : BoundedContinuousFunction F ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hfc⟩ C hC
  have hfb : ∀ x, fb x = f x := fun _ ↦ rfl
  have hXf := hXν fb
  simp only [hfb] at hXf
  have hmapY : ∀ n, ∫ x, f x ∂(μ.map (Y n)) = ∫ ω, f (Y n ω) ∂μ := fun n ↦
    integral_map (hY n).aemeasurable hfc.aestronglyMeasurable
  have hmapX : ∀ n, ∫ x, f x ∂(μ.map (X n)) = ∫ ω, f (X n ω) ∂μ := fun n ↦
    integral_map (hX n).aemeasurable hfc.aestronglyMeasurable
  simp only [hmapX] at hXf
  simp only [hmapY]
  have hint : ∀ (Z : Ω → F), Measurable Z → Integrable (fun ω ↦ f (Z ω)) μ := fun Z hZ ↦
    Integrable.of_bound (hfc.measurable.comp hZ).aestronglyMeasurable ‖fb‖
      (ae_of_all _ fun ω ↦ fb.norm_coe_le_norm (Z ω))
  suffices hd : Tendsto (fun n ↦ ∫ ω, f (Y n ω) ∂μ - ∫ ω, f (X n ω) ∂μ) atTop (𝓝 0) by
    simpa using hd.add hXf
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε : ℝ := η / (2 * ((L : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hLε : (L : ℝ) * ε < η / 2 := by
    rw [hε, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [L.coe_nonneg]
  have hδ : 0 < η / (2 * (|C| + 1)) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hXY ε hεpos)) _ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  specialize hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hN
  set Sb : Set Ω := {ω | ε < dist (Y n ω - X n ω) 0} with hSb
  set S : Set Ω := {ω | (L : ℝ) * ε < |f (Y n ω) - f (X n ω)|} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((hfc.measurable.comp (hY n)).sub (hfc.measurable.comp (hX n))))
  have hSsub : S ⊆ Sb := by
    intro ω hω
    simp only [hS, hSb, mem_ofPred_eq, dist_zero_right] at hω ⊢
    by_contra hcon
    push Not at hcon
    have h1 : |f (Y n ω) - f (X n ω)| ≤ L * ‖Y n ω - X n ω‖ := by
      have := hL.dist_le_mul (Y n ω) (X n ω)
      rwa [Real.dist_eq, dist_eq_norm] at this
    have : (L : ℝ) * ‖Y n ω - X n ω‖ ≤ L * ε := mul_le_mul_of_nonneg_left hcon L.coe_nonneg
    linarith
  have hpt : ∀ ω, |f (Y n ω) - f (X n ω)| ≤ (L : ℝ) * ε + |C| * S.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
      have := hC (Y n ω) (X n ω)
      rw [Real.dist_eq] at this
      have : 0 ≤ (L : ℝ) * ε := by positivity
      linarith [le_abs_self C]
    · rw [indicator_of_notMem hω, mul_zero, add_zero]
      simpa [hS] using hω
  have hYi := hint _ (hY n)
  have hXi := hint _ (hX n)
  have hbound : |∫ ω, f (Y n ω) ∂μ - ∫ ω, f (X n ω) ∂μ| ≤ (L : ℝ) * ε + |C| * μ.real S := by
    rw [← integral_sub hYi hXi]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |f (Y n ω) - f (X n ω)| ∂μ ≤ ∫ ω, ((L : ℝ) * ε + |C| * S.indicator 1 ω) ∂μ :=
          integral_mono (hYi.sub hXi).abs
            ((integrable_const _).add ((integrable_const (1 : ℝ)).indicator hSm |>.const_mul _))
            hpt
      _ = (L : ℝ) * ε + |C| * μ.real S := by
          rw [integral_add (f := fun _ ↦ (L : ℝ) * ε) (g := fun ω ↦ |C| * S.indicator 1 ω)
            (integrable_const _)
            (((integrable_const (1 : ℝ)).indicator hSm).const_mul _),
            integral_const_mul |C| (fun ω ↦ S.indicator 1 ω), integral_indicator_one hSm]
          simp
  have hSle : μ.real S ≤ μ.real Sb := measureReal_mono hSsub
  have hC' : |C| * μ.real S < η / 2 := by
    calc |C| * μ.real S ≤ |C| * (η / (2 * (|C| + 1))) :=
          mul_le_mul_of_nonneg_left (hSle.trans hN.le) (abs_nonneg C)
      _ < η / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg C]
  rw [Real.dist_eq, sub_zero]
  linarith

/-- A sequence converging in law is bounded in probability in norm: for every `ε > 0` there is
`M > 0` with `P(‖Zₙ‖ > M) ≤ ε` eventually. -/
theorem exists_measureReal_lt_norm_le_of_tendstoInDistribution {Ω E : Type*}
    [MeasurableSpace Ω] [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E) (hZ : ∀ n, Measurable (Z n))
    (ν : Measure E) [IsProbabilityMeasure ν] (h : TendstoInDistribution μ Z ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∀ᶠ n in atTop, μ.real {ω | M < ‖Z n ω‖} ≤ ε := by
  have hms : ∀ c : ℝ, MeasurableSet {x : E | c < ‖x‖} := fun c ↦
    measurableSet_lt measurable_const continuous_norm.measurable
  have hlim : Tendsto (fun k : ℕ ↦ ν {x : E | (k : ℝ) < ‖x‖}) atTop
      (𝓝 (ν (⋂ k : ℕ, {x : E | (k : ℝ) < ‖x‖}))) :=
    tendsto_measure_iInter_atTop (fun k ↦ (hms k).nullMeasurableSet)
      (fun k l hkl x (hx : (l : ℝ) < ‖x‖) ↦
        (lt_of_le_of_lt (Nat.cast_le.2 hkl) hx : (k : ℝ) < ‖x‖)) ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ k : ℕ, {x : E | (k : ℝ) < ‖x‖}) = ∅ := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    exact ⟨k, hk⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  have hk' : ν.real {x : E | (k : ℝ) < ‖x‖} < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hk
  set M₀ : ℝ := (k : ℝ) with hM₀
  let f : E → ℝ := fun x ↦ max 0 (min (‖x‖ - M₀) 1)
  have hfc : Continuous f := by fun_prop
  have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x ↦
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let fb : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hfc⟩ 1
    (fun x y ↦ by
      rw [Real.dist_eq, abs_sub_le_iff]
      simp only [ContinuousMap.coe_mk]
      constructor <;> linarith [hf01 x, hf01 y])
  have hfb : ∀ x, fb x = f x := fun _ ↦ rfl
  have hlow : ∀ x, {x : E | M₀ + 1 < ‖x‖}.indicator (1 : E → ℝ) x ≤ f x := by
    intro x
    by_cases hx : x ∈ {x : E | M₀ + 1 < ‖x‖}
    · rw [indicator_of_mem hx, Pi.one_apply]
      simp only [mem_ofPred_eq] at hx
      simp only [f]
      rw [min_eq_right (by linarith)]
      exact le_max_right _ _
    · rw [indicator_of_notMem hx]; exact (hf01 x).1
  have hup : ∀ x, f x ≤ {x : E | M₀ < ‖x‖}.indicator (1 : E → ℝ) x := by
    intro x
    by_cases hx : x ∈ {x : E | M₀ < ‖x‖}
    · rw [indicator_of_mem hx, Pi.one_apply]; exact (hf01 x).2
    · rw [indicator_of_notMem hx]
      simp only [mem_ofPred_eq, not_lt] at hx
      simp only [f]
      exact max_le le_rfl ((min_le_left _ _).trans (by linarith))
  have hfint : ∀ ρ : Measure E, IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ ↦
    Integrable.of_bound hfc.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]; exact (hf01 x).2)
  have hν : ∫ x, f x ∂ν < ε := by
    calc ∫ x, f x ∂ν ≤ ∫ x, {x : E | M₀ < ‖x‖}.indicator (1 : E → ℝ) x ∂ν :=
          integral_mono (hfint ν inferInstance) ((integrable_const (1 : ℝ)).indicator (hms _)) hup
      _ = ν.real {x : E | M₀ < ‖x‖} := integral_indicator_one (hms _)
      _ < ε := by linarith
  have hev := (h fb).eventually_lt_const hν
  refine ⟨M₀ + 1, by positivity, hev.mono fun n hn ↦ ?_⟩
  simp only [hfb] at hn
  calc μ.real {ω | M₀ + 1 < ‖Z n ω‖} = (μ.map (Z n)).real {x : E | M₀ + 1 < ‖x‖} := by
        rw [map_measureReal_apply (hZ n) (hms _)]; rfl
    _ = ∫ x, {x : E | M₀ + 1 < ‖x‖}.indicator (1 : E → ℝ) x ∂(μ.map (Z n)) :=
        (integral_indicator_one (hms _)).symm
    _ ≤ ∫ x, f x ∂(μ.map (Z n)) :=
        integral_mono ((integrable_const (1 : ℝ)).indicator (hms _)) (hfint _ inferInstance) hlow
    _ ≤ ε := hn.le

/-- A nonnegative real sequence that is eventually below every positive level tends to `0`. -/
theorem tendsto_zero_of_forall_eventually_le {u : ℕ → ℝ} (h0 : ∀ n, 0 ≤ u n)
    (h : ∀ η > 0, ∀ᶠ n in atTop, u n ≤ η) : Tendsto u atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (h0 n),
    fun b hb ↦ (h (b / 2) (half_pos hb)).mono fun n hn ↦ hn.trans_lt (half_lt_self hb)⟩

/-- The remainder of the delta method is negligible in probability. -/
theorem tendstoInProbabilityConst_delta_method_remainder {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E)
    (hT : ∀ n, Measurable (T n)) (θ : E) (ν : Measure E) [IsProbabilityMeasure ν]
    (g : E → F) (D : E →L[ℝ] F) (hd : HasFDerivAt g D θ)
    (hlim : TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (T n ω - θ)) ν) :
    TendstoInProbabilityConst μ (fun n ω ↦
      Real.sqrt n • (g (T n ω) - g θ) - D (Real.sqrt n • (T n ω - θ))) 0 := by
  have hZm : ∀ n : ℕ, Measurable (fun ω ↦ Real.sqrt n • (T n ω - θ)) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hT n)
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨M, hM, hev⟩ :=
    exists_measureReal_lt_norm_le_of_tendstoInDistribution μ _ hZm ν hlim hη
  have hc : 0 < ε / M := div_pos hε hM
  obtain ⟨δ, hδ, hδg⟩ := Metric.eventually_nhds_iff.1 (hd.isLittleO.def hc)
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hev, hsqrt.eventually_gt_atTop (M / δ)] with n hn hnδ
  refine le_trans (measureReal_mono fun ω hω ↦ ?_) hn
  simp only [mem_ofPred_eq, dist_zero_right] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hspos : 0 < Real.sqrt n := (div_pos hM hδ).trans hnδ
  have hnorm : ‖Real.sqrt n • (T n ω - θ)‖ = Real.sqrt n * ‖T n ω - θ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  have hclose : dist (T n ω) θ < δ := by
    rw [dist_eq_norm]
    have h1 : Real.sqrt n * ‖T n ω - θ‖ ≤ M := hnorm ▸ hcon
    have h2 : M < δ * Real.sqrt n := by rwa [div_lt_iff₀ hδ, mul_comm] at hnδ
    nlinarith [norm_nonneg (T n ω - θ)]
  have hb := hδg hclose
  have hR : Real.sqrt n • (g (T n ω) - g θ) - D (Real.sqrt n • (T n ω - θ)) =
      Real.sqrt n • (g (T n ω) - g θ - D (T n ω - θ)) := by
    rw [map_smul, smul_sub, smul_sub, smul_sub]
  rw [hR, norm_smul, Real.norm_eq_abs, abs_of_pos hspos] at hω
  have : Real.sqrt n * ‖g (T n ω) - g θ - D (T n ω - θ)‖ ≤ ε := by
    calc Real.sqrt n * ‖g (T n ω) - g θ - D (T n ω - θ)‖
        ≤ Real.sqrt n * (ε / M * ‖T n ω - θ‖) := mul_le_mul_of_nonneg_left hb hspos.le
      _ = ε / M * (Real.sqrt n * ‖T n ω - θ‖) := by ring
      _ ≤ ε / M * M := mul_le_mul_of_nonneg_left (hnorm ▸ hcon) hc.le
      _ = ε := div_mul_cancel₀ ε hM.ne'
  linarith

/-- GAPS 102.1: the delta method and its stochastic linearization in Banach spaces. -/
theorem tendstoInDistribution_delta_method {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E)
    (hT : ∀ n, Measurable (T n)) (θ : E) (ν : Measure E) [IsProbabilityMeasure ν]
    (g : E → F) (hg : Measurable g) (D : E →L[ℝ] F) (hd : HasFDerivAt g D θ)
    (hlim : TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (T n ω - θ)) ν) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (g (T n ω) - g θ)) (ν.map D) ∧
      TendstoInProbabilityConst μ (fun n ω ↦
        Real.sqrt n • (g (T n ω) - g θ) - D (Real.sqrt n • (T n ω - θ))) 0 := by
  have hR := tendstoInProbabilityConst_delta_method_remainder μ T hT θ ν g D hd hlim
  refine ⟨?_, hR⟩
  have hZm : ∀ n : ℕ, Measurable (fun ω ↦ Real.sqrt n • (T n ω - θ)) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hT n)
  have hYm : ∀ n : ℕ, Measurable (fun ω ↦ Real.sqrt n • (g (T n ω) - g θ)) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hg.comp (hT n))
  exact tendstoInDistribution_of_tendstoInProbabilityConst_sub μ
    (fun n ω ↦ D (Real.sqrt n • (T n ω - θ))) _
    (fun n ↦ D.continuous.measurable.comp (hZm n)) hYm (ν.map D)
    (tendstoInDistribution_comp_of_continuous μ _ hZm ν D D.continuous hlim) hR


/-- GAPS 102.8: the nondegenerate U-statistic CLT, with its first projection. -/
theorem tendstoInDistribution_uStatistic_of_nondegenerate
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (m : ℕ)
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) :
    let θ := ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P);
    let g := fun x ↦ (∫ y, h (Fin.cases x y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ;
    ∀ (hv : 0 < variance P g),
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n *
      (uStatistic (m + 1) n h (fun i ↦ X i.val ω) - θ))
      (gaussianReal 0 (Real.toNNReal (((m + 1 : ℕ) : ℝ) ^ 2 * variance P g))) := by
  sorry

/-- Sum of two sequences tending to `0` in probability tends to `0` in probability. -/
theorem tendstoInProbabilityConst_add_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X Y : ℕ → Ω → ℝ) (hX : TendstoInProbabilityConst μ X 0)
    (hY : TendstoInProbabilityConst μ Y 0) :
    TendstoInProbabilityConst μ (fun n ω ↦ X n ω + Y n ω) 0 := by
  intro ε hε
  have h := (hX (ε / 2) (half_pos hε)).add (hY (ε / 2) (half_pos hε))
  rw [add_zero] at h
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) h
  refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
  intro ω hω
  simp only [Real.dist_eq, sub_zero, mem_union, mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := abs_add_le (X n ω) (Y n ω)
  linarith [hcon.1, hcon.2]

/-- Domination: if eventually, for almost every `ω`, `|Yₙ| ≤ |Xₙ|` whenever `|Uₙ| < δ`, and
`Xₙ, Uₙ → 0` in probability, then `Yₙ → 0` in probability. -/
theorem tendstoInProbabilityConst_zero_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y U : ℕ → Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hXY : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, |U n ω| < δ → |Y n ω| ≤ |X n ω|)
    (hX : TendstoInProbabilityConst μ X 0) (hU : TendstoInProbabilityConst μ U 0) :
    TendstoInProbabilityConst μ Y 0 := by
  intro ε hε
  have h := (hX ε hε).add (hU (δ / 2) (half_pos hδ))
  rw [add_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ h
  filter_upwards [hXY] with n hn
  rw [ae_iff] at hn
  calc μ.real {ω | ε < dist (Y n ω) 0}
      ≤ μ.real (({ω | ε < dist (X n ω) 0} ∪ {ω | δ / 2 < dist (U n ω) 0}) ∪
          {ω | ¬(|U n ω| < δ → |Y n ω| ≤ |X n ω|)}) := by
        refine measureReal_mono ?_
        intro ω hω
        simp only [Real.dist_eq, sub_zero, mem_union, mem_ofPred_eq] at hω ⊢
        by_contra hcon
        push Not at hcon
        obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
        linarith [h3 (by linarith)]
    _ ≤ μ.real ({ω | ε < dist (X n ω) 0} ∪ {ω | δ / 2 < dist (U n ω) 0}) + 0 := by
        refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
        rw [measureReal_def, hn, ENNReal.toReal_zero]
    _ ≤ _ := by rw [add_zero]; exact measureReal_union_le _ _

/-- A deterministic sequence tending to `0` tends to `0` in probability. -/
theorem tendstoInProbabilityConst_const_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    TendstoInProbabilityConst μ (fun n _ ↦ u n) 0 := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  have hu' : Tendsto (fun n ↦ |u n|) atTop (𝓝 0) := by simpa using hu.abs
  filter_upwards [hu'.eventually (gt_mem_nhds hε)] with n hn
  have : {ω : Ω | ε < dist (u n) 0} = ∅ := by
    ext ω
    simp only [Real.dist_eq, sub_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hn.le
  rw [this, measureReal_empty]

/-- Continuous mapping for convergence in probability to a constant. -/
theorem tendstoInProbabilityConst_comp_of_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : ℕ → Ω → ℝ) (θ : ℝ) (J : ℝ → ℝ)
    (hJ : ContinuousAt J θ)
    (hT : TendstoInProbabilityConst μ T θ) :
    TendstoInProbabilityConst μ (fun n ω ↦ J (T n ω)) (J θ) := by
  intro ε hε
  obtain ⟨δ, hδ, hδJ⟩ := Metric.continuousAt_iff.1 hJ ε hε
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) (hT (δ / 2) (half_pos hδ))
  refine measureReal_mono ?_
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact absurd (hδJ (by linarith)) (not_lt.2 hω.le)

/-- Constant multiples preserve convergence to `0` in probability. -/
theorem tendstoInProbabilityConst_const_mul_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : TendstoInProbabilityConst μ X 0) :
    TendstoInProbabilityConst μ (fun n ω ↦ c * X n ω) 0 := by
  intro ε hε
  have h := hX (ε / (|c| + 1)) (by positivity)
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ measureReal_mono fun ω hω ↦ ?_) h
  simp only [Real.dist_eq, sub_zero, mem_ofPred_eq, abs_mul] at hω ⊢
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [abs_nonneg (X n ω), abs_nonneg c]

/-- A real sequence converging in law is bounded in probability. -/
theorem isBoundedInProbability_of_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hZ : ∀ n, Measurable (Z n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : TendstoInDistribution μ Z ν) :
    IsBoundedInProbability μ Z := by
  intro ε hε
  obtain ⟨M, hM, hev⟩ := exists_measureReal_lt_norm_le_of_tendstoInDistribution μ Z hZ ν h hε
  exact ⟨M, hM, by simpa only [Real.norm_eq_abs] using hev⟩

/-- A real sequence converging in probability to a constant is bounded in probability. -/
theorem isBoundedInProbability_of_tendstoInProbabilityConst {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : ℕ → Ω → ℝ) (c : ℝ)
    (h : TendstoInProbabilityConst μ Z c) :
    IsBoundedInProbability μ Z := by
  intro ε hε
  refine ⟨|c| + 1, by positivity, ?_⟩
  filter_upwards [(h 1 one_pos).eventually (eventually_le_nhds hε)] with n hn
  refine le_trans (measureReal_mono fun ω (hω : |c| + 1 < |Z n ω|) ↦ ?_) hn
  simp only [Real.dist_eq, mem_ofPred_eq]
  have := abs_sub_abs_le_abs_sub (Z n ω) c
  linarith

/-- A sequence bounded in probability times a sequence tending to `0` in probability tends
to `0` in probability. -/
theorem tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (U V : ℕ → Ω → ℝ)
    (hU : IsBoundedInProbability μ U) (hV : TendstoInProbabilityConst μ V 0) :
    TendstoInProbabilityConst μ (fun n ω ↦ U n ω * V n ω) 0 := by
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨C, hC, hev⟩ := hU (η / 2) (half_pos hη)
  have hV' := (hV (ε / C) (div_pos hε hC)).eventually (eventually_le_nhds (half_pos hη))
  filter_upwards [hev, hV'] with n h1 h2
  calc μ.real {ω | ε < dist (U n ω * V n ω) 0}
      ≤ μ.real ({ω | C < |U n ω|} ∪ {ω | ε / C < dist (V n ω) 0}) := by
        refine measureReal_mono fun ω (hω : ε < dist (U n ω * V n ω) 0) ↦ ?_
        simp only [Real.dist_eq, sub_zero, mem_union, mem_ofPred_eq, abs_mul] at hω ⊢
        by_contra hcon
        push Not at hcon
        rw [le_div_iff₀ hC] at hcon
        nlinarith [abs_nonneg (U n ω), abs_nonneg (V n ω)]
    _ ≤ η / 2 + η / 2 := (measureReal_union_le _ _).trans (add_le_add h1 h2)
    _ = η := add_halves η

/-- Convergence in measure gives the CKSD convergence in probability to a constant. -/
theorem tendstoInProbabilityConst_of_tendstoInMeasure {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → E) (c : E)
    (h : TendstoInMeasure μ X atTop (fun _ ↦ c)) : TendstoInProbabilityConst μ X c := by
  intro ε hε
  have h' := (tendstoInMeasure_iff_measureReal_dist.1 h) ε hε
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun n ↦ measureReal_mono fun ω (hω : ε < dist (X n ω) c) ↦ (le_of_lt hω : ε ≤ _)) h'

/-- Measurable real statistics of an iid sequence are pairwise independent and identically
distributed. -/
theorem iid_comp_pairwise_identDistrib {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {P : Measure E} {X : ℕ → Ω → E}
    (hiid : IsIndependentIdenticallyDistributed μ X P) {s : E → ℝ} (hs : Measurable s) :
    Pairwise (fun i j ↦ IndepFun (s ∘ X i) (s ∘ X j) μ) ∧
      ∀ i, IdentDistrib (s ∘ X i) (s ∘ X 0) μ μ := by
  obtain ⟨hm, hind, hlaw⟩ := hiid
  refine ⟨fun i j hij ↦ ((hind.comp (fun _ ↦ s) (fun _ ↦ hs)).indepFun hij), fun i ↦ ?_⟩
  refine ⟨(hs.comp (hm i)).aemeasurable, (hs.comp (hm 0)).aemeasurable, ?_⟩
  rw [← Measure.map_map hs (hm i), ← Measure.map_map hs (hm 0), hlaw i, hlaw 0]

/-- Weak law of large numbers for a measurable integrable statistic of an iid sequence, in the
form of convergence in probability, deduced from Mathlib's strong law. -/
theorem tendstoInProbabilityConst_sampleMean_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (s : E → ℝ)
    (hs : Measurable s) (hint : Integrable s P) :
    TendstoInProbabilityConst μ (fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω))
      (∫ x, s x ∂P) := by
  obtain ⟨hindep, hident⟩ := iid_comp_pairwise_identDistrib hiid hs
  have hm := hiid.1
  have hlaw := hiid.2.2 0
  have hint0 : Integrable (s ∘ X 0) μ := by
    rw [← hlaw] at hint
    exact hint.comp_measurable (hm 0)
  have hslln := strong_law_ae (fun i ↦ s ∘ X i) hint0 hindep hident
  have hmean : μ[s ∘ X 0] = ∫ x, s x ∂P := by
    rw [← hlaw, integral_map (hm 0).aemeasurable hs.aestronglyMeasurable]; rfl
  rw [hmean] at hslln
  refine tendstoInProbabilityConst_of_tendstoInMeasure μ _ _
    (tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_)
  · exact (measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦ hs.comp (hm i))).aestronglyMeasurable
  · filter_upwards [hslln] with ω hω
    simpa [smul_eq_mul] using hω

/-- Central limit theorem for a centred square-integrable measurable statistic of an iid
sequence, in the CKSD convergence-in-law form, from Mathlib's
`tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem tendstoInDistribution_inv_sqrt_mul_sum_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (s : E → ℝ)
    (hs : Measurable s) (h2 : MemLp s 2 P) (h0 : (∫ x, s x ∂P) = 0) :
    TendstoInDistribution μ (fun n ω ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω))
      (gaussianReal 0 (Real.toNNReal (∫ x, s x ^ 2 ∂P))) := by
  obtain ⟨hindep, hident⟩ := iid_comp_pairwise_identDistrib hiid hs
  have hm := hiid.1
  have hlaw := hiid.2.2 0
  have hindep' : iIndepFun (fun i ↦ s ∘ X i) μ :=
    hiid.2.1.comp (fun _ ↦ s) (fun _ ↦ hs)
  have h2' : MemLp (s ∘ X 0) 2 μ := by
    rw [← hlaw] at h2
    exact h2.comp_of_map (hm 0).aemeasurable
  have hmean : μ[s ∘ X 0] = 0 := by
    rw [← h0, ← hlaw, integral_map (hm 0).aemeasurable hs.aestronglyMeasurable]; rfl
  have hsq : μ[(s ∘ X 0) ^ 2] = ∫ x, s x ^ 2 ∂P := by
    rw [← hlaw, integral_map (hm 0).aemeasurable (hs.pow_const 2).aestronglyMeasurable]; rfl
  have hvar : Var[s ∘ X 0; μ] = ∫ x, s x ^ 2 ∂P := by
    rw [variance_eq_sub h2', hsq, hmean]; ring
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ↦ s ∘ X i) (P := μ)
    (P' := gaussianReal 0 (Var[s ∘ X 0; μ]).toNNReal) (Y := id) HasLaw.id h2' hindep' hident
  have ht := hclt.tendsto
  intro f
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht f
  rw [hmean, hvar] at this
  simpa using this

/-- A real number `x` with `2 x ≤ δ A + B / δ` for every `δ > 0` satisfies `x ≤ √A √B`. -/
theorem le_sqrt_mul_sqrt_of_forall_two_mul_le {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ δ > 0, 2 * x ≤ δ * A + B / δ) : x ≤ Real.sqrt A * Real.sqrt B := by
  rcases hA.lt_or_eq with hA' | hA'
  · rcases hB.lt_or_eq with hB' | hB'
    · have hsA := Real.sqrt_pos.2 hA'
      have hsB := Real.sqrt_pos.2 hB'
      have := h (Real.sqrt B / Real.sqrt A) (div_pos hsB hsA)
      have e1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
        rw [div_mul_eq_mul_div, div_eq_iff hsA.ne',
          show Real.sqrt B * A = Real.sqrt B * (Real.sqrt A * Real.sqrt A) by
            rw [Real.mul_self_sqrt hA]]
        ring
      have e2 : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt A * Real.sqrt B := by
        rw [div_div_eq_mul_div, div_eq_iff hsB.ne',
          show B * Real.sqrt A = (Real.sqrt B * Real.sqrt B) * Real.sqrt A by
            rw [Real.mul_self_sqrt hB]]
        ring
      rw [e1, e2] at this
      linarith
    · subst hB'
      simp only [Real.sqrt_zero, mul_zero]
      by_contra hx
      push Not at hx
      have := h (x / (A + 1)) (by positivity)
      rw [zero_div, add_zero] at this
      have : x / (A + 1) * A < x := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  · subst hA'
    simp only [Real.sqrt_zero, zero_mul]
    by_contra hx
    push Not at hx
    have := h ((B + 1) / x) (by positivity)
    simp only [mul_zero, zero_add] at this
    rw [div_div_eq_mul_div] at this
    have : B * x / (B + 1) < x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- The Cauchy–Schwarz inequality for real integrals of square-integrable functions. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a b : α → ℝ) (ham : AEStronglyMeasurable a ν) (hbm : AEStronglyMeasurable b ν)
    (ha : Integrable (fun x ↦ a x ^ 2) ν) (hb : Integrable (fun x ↦ b x ^ 2) ν) :
    |∫ x, a x * b x ∂ν| ≤ Real.sqrt (∫ x, a x ^ 2 ∂ν) * Real.sqrt (∫ x, b x ^ 2 ∂ν) := by
  have hpt : ∀ δ > 0, ∀ x, 2 * |a x * b x| ≤ δ * a x ^ 2 + b x ^ 2 / δ := by
    intro δ hδ x
    rw [abs_mul, ← sq_abs (a x), ← sq_abs (b x)]
    have : 0 ≤ (δ * |a x| - |b x|) ^ 2 / δ := by positivity
    have e : (δ * |a x| - |b x|) ^ 2 / δ = δ * |a x| ^ 2 + |b x| ^ 2 / δ - 2 * (|a x| * |b x|) := by
      field_simp
      ring
    linarith
  have hab : Integrable (fun x ↦ a x * b x) ν := by
    refine ((ha.add hb).div_const 2).mono' (ham.mul hbm) (ae_of_all _ fun x ↦ ?_)
    have := hpt 1 one_pos x
    rw [Real.norm_eq_abs]
    simp only [one_mul, div_one] at this
    show |a x * b x| ≤ (a x ^ 2 + b x ^ 2) / 2
    linarith
  refine le_sqrt_mul_sqrt_of_forall_two_mul_le (integral_nonneg fun _ ↦ sq_nonneg _)
    (integral_nonneg fun _ ↦ sq_nonneg _) fun δ hδ ↦ ?_
  calc 2 * |∫ x, a x * b x ∂ν| ≤ ∫ x, 2 * |a x * b x| ∂ν := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by norm_num)
    _ ≤ ∫ x, (δ * a x ^ 2 + b x ^ 2 / δ) ∂ν :=
        integral_mono (hab.abs.const_mul 2) ((ha.const_mul δ).add (hb.div_const δ)) (hpt δ hδ)
    _ = δ * ∫ x, a x ^ 2 ∂ν + (∫ x, b x ^ 2 ∂ν) / δ := by
        rw [integral_add (ha.const_mul δ) (hb.div_const δ), integral_const_mul, integral_div]

/-- Chebyshev's inequality for a sum of a measurable square-integrable statistic of an iid
sequence. -/
theorem measureReal_le_abs_sum_sub_le_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : E → ℝ) (hφ : Measurable φ) (h2 : MemLp φ 2 P) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, φ (X i ω) - n * ∫ x, φ x ∂P|} ≤
      n * (∫ x, φ x ^ 2 ∂P) / ε ^ 2 := by
  obtain ⟨hindep, hident⟩ := iid_comp_pairwise_identDistrib hiid hφ
  have hm := hiid.1
  have h2i : ∀ i, MemLp (φ ∘ X i) 2 μ := fun i ↦ by
    have h := h2
    rw [← hiid.2.2 i] at h
    exact h.comp_of_map (hm i).aemeasurable
  set Y : Ω → ℝ := ∑ i ∈ Finset.range n, φ ∘ X i with hY
  have hYfun : ∀ ω, Y ω = ∑ i ∈ Finset.range n, φ (X i ω) := fun ω ↦ by
    simp [hY, Finset.sum_apply]
  have hY2 : MemLp Y 2 μ := memLp_finsetSum' _ fun i _ ↦ h2i i
  have hmeanY : μ[Y] = n * ∫ x, φ x ∂P := by
    rw [show μ[Y] = ∫ ω, ∑ i ∈ Finset.range n, (φ ∘ X i) ω ∂μ by simp only [hY, Finset.sum_apply],
      integral_finsetSum _ fun i _ ↦ (h2i i).integrable one_le_two]
    have : ∀ i, ∫ ω, (φ ∘ X i) ω ∂μ = ∫ x, φ x ∂P := fun i ↦ by
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable hφ.aestronglyMeasurable]; rfl
    rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hvarY : ProbabilityTheory.variance Y μ ≤ n * ∫ x, φ x ^ 2 ∂P := by
    rw [hY, IndepFun.variance_sum (fun i _ ↦ h2i i) (fun i _ j _ hij ↦ hindep hij)]
    have : ∀ i, ProbabilityTheory.variance (φ ∘ X i) μ ≤ ∫ x, φ x ^ 2 ∂P := fun i ↦ by
      refine (variance_le_expectation_sq (h2i i).aestronglyMeasurable).trans_eq ?_
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable (hφ.pow_const 2).aestronglyMeasurable]
      rfl
    calc ∑ i ∈ Finset.range n, ProbabilityTheory.variance (φ ∘ X i) μ
        ≤ ∑ _i ∈ Finset.range n, ∫ x, φ x ^ 2 ∂P := Finset.sum_le_sum fun i _ ↦ this i
      _ = n * ∫ x, φ x ^ 2 ∂P := by simp
  have hcheb := meas_ge_le_variance_div_sq hY2 hε
  rw [hmeanY] at hcheb
  have hset : {ω | ε ≤ |∑ i ∈ Finset.range n, φ (X i ω) - n * ∫ x, φ x ∂P|} =
      {ω | ε ≤ |Y ω - n * ∫ x, φ x ∂P|} := by
    ext ω; simp [hYfun]
  rw [hset, measureReal_def]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb).trans ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))]
  gcongr

/-- A triangular-array weak law: if `n ∫ φₙ² dP → 0`, then the centred sums
`∑_{i<n} (φₙ(Xᵢ) - ∫ φₙ dP)` of an iid sequence tend to zero in probability. -/
theorem tendstoInProbabilityConst_sum_sub_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n)) (h2 : ∀ n, MemLp (φ n) 2 P)
    (hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ
      (fun n ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) - n * ∫ x, φ n x ∂P) 0 := by
  intro ε hε
  have hb : Tendsto (fun n : ℕ ↦ n * (∫ x, φ n x ^ 2 ∂P) / ε ^ 2) atTop (𝓝 0) := by
    simpa using hlim.div_const (ε ^ 2)
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hb
  refine (measureReal_mono fun ω hω ↦ ?_).trans
    (measureReal_le_abs_sum_sub_le_of_iid μ P X hiid (φ n) (hφ n) (h2 n) n hε)
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.le

/-- Markov's inequality for sums of squares: if `n ∫ φₙ² dP → 0`, then `∑_{i<n} φₙ(Xᵢ)²` tends to
zero in probability. -/
theorem tendstoInProbabilityConst_sum_sq_of_iid {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n)) (h2 : ∀ n, Integrable (fun x ↦ φ n x ^ 2) P)
    (hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ (fun n ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2) 0 := by
  intro ε hε
  have hm := hiid.1
  have hb : Tendsto (fun n : ℕ ↦ n * (∫ x, φ n x ^ 2 ∂P) / ε) atTop (𝓝 0) := by
    simpa using hlim.div_const ε
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hb
  have hint : ∀ i, Integrable (fun ω ↦ φ n (X i ω) ^ 2) μ := fun i ↦ by
    have h := h2 n
    rw [← hiid.2.2 i] at h
    exact h.comp_measurable (hm i)
  have hsum : ∫ ω, ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2 ∂μ = n * ∫ x, φ n x ^ 2 ∂P := by
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    have : ∀ i, ∫ ω, φ n (X i ω) ^ 2 ∂μ = ∫ x, φ n x ^ 2 ∂P := fun i ↦ by
      rw [← hiid.2.2 i, integral_map (hm i).aemeasurable
        ((hφ n).pow_const 2).aestronglyMeasurable]
    simp [this]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω ↦ ∑ i ∈ Finset.range n, φ n (X i ω) ^ 2)
    (ae_of_all _ fun ω ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg (φ n (X i ω)))
    (integrable_finsetSum (Finset.range n) fun i _ ↦ hint i) ε
  rw [hsum] at hmk
  have hsub : μ.real {ω | ε < dist (∑ i ∈ Finset.range n, φ n (X i ω) ^ 2) 0} ≤
      μ.real {x | ε ≤ ∑ i ∈ Finset.range n, φ n (X i x) ^ 2} := by
    refine measureReal_mono ?_
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)] at hω
    exact hω.le
  rw [le_div_iff₀ hε]
  exact (mul_le_mul_of_nonneg_right hsub hε.le).trans ((mul_comm _ _).le.trans hmk)

/-- A one-term logarithmic expansion: for `|g| ≤ 1/2`,
`|2 log (1 + g) - (2 g - g²)| ≤ 4 |g|³`. -/
theorem abs_two_mul_log_one_add_sub_le {g : ℝ} (hg : |g| ≤ 1 / 2) :
    |2 * Real.log (1 + g) - (2 * g - g ^ 2)| ≤ 4 * |g| ^ 3 := by
  have h1 : |-g| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  have hden : |g| ^ (2 + 1) / (1 - |g|) ≤ 2 * |g| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |g| ^ 3 := by positivity
    norm_num
    nlinarith
  have e : 2 * Real.log (1 + g) - (2 * g - g ^ 2) =
      2 * (0 + (-g) ^ (0 + 1) / ((0 : ℕ) + 1) + (-g) ^ (1 + 1) / ((1 : ℕ) + 1) +
        Real.log (1 + g)) := by
    push_cast
    ring
  rw [e, abs_mul, abs_two]
  linarith

/-- Uniform integrability of a square-integrable function along `√n`: for `c > 0`,
`n P(|s| > c √n) → 0`. -/
theorem tendsto_mul_measureReal_lt_abs_of_integrable_sq {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsFiniteMeasure P] (s : E → ℝ) (hs : Measurable s)
    (h2 : Integrable (fun x ↦ s x ^ 2) P) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ n * P.real {x | c * Real.sqrt n < |s x|}) atTop (𝓝 0) := by
  set A : ℕ → Set E := fun n ↦ {x | c * Real.sqrt n < |s x|} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hs)
  have h1 : ∀ n : ℕ, n * P.real (A n) ≤ (∫ x, (A n).indicator (fun x ↦ s x ^ 2) x ∂P) / c ^ 2 := by
    intro n
    rw [le_div_iff₀ (by positivity), integral_indicator (hAm n)]
    calc (n : ℝ) * P.real (A n) * c ^ 2 = ∫ _x in A n, c ^ 2 * n ∂P := by
          rw [setIntegral_const, smul_eq_mul]; ring
      _ ≤ ∫ x in A n, s x ^ 2 ∂P := by
          refine setIntegral_mono_on (integrableOn_const (by simp)) h2.integrableOn (hAm n) ?_
          intro x hx
          simp only [hA, mem_ofPred_eq] at hx
          have h0 : 0 ≤ c * Real.sqrt n := by positivity
          have := mul_self_lt_mul_self h0 hx
          rw [← sq_abs (s x)]
          calc c ^ 2 * n = (c * Real.sqrt n) * (c * Real.sqrt n) := by
                rw [mul_mul_mul_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]; ring
            _ ≤ |s x| ^ 2 := by rw [sq]; exact this.le
  have h2' : Tendsto (fun n : ℕ ↦ ∫ x, (A n).indicator (fun x ↦ s x ^ 2) x ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun x ↦ s x ^ 2)
      (F := fun n : ℕ ↦ (A n).indicator (fun x ↦ s x ^ 2))
      (f := fun _ ↦ (0 : ℝ))
      (fun n ↦ ((hs.pow_const 2).indicator (hAm n)).aestronglyMeasurable) h2
      (fun n ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
        exact indicator_le_self' (fun _ _ ↦ sq_nonneg _) x)
      (ae_of_all _ fun x ↦ by
        have hsq : Tendsto (fun n : ℕ ↦ c * Real.sqrt n) atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hsq.eventually_ge_atTop (|s x|)] with n hn
        simp only [hA]
        rw [indicator_of_notMem]
        simp only [mem_ofPred_eq, not_lt]
        exact hn)
    simpa using this
  refine squeeze_zero (fun n ↦ by positivity) h1 ?_
  simpa using h2'.div_const (c ^ 2)

/-- For a law with a density, a real function is integrable iff its product with the density is
integrable for the reference measure, and the integrals agree. -/
theorem integrable_and_integral_eq_of_hasDensity {E : Type*} [MeasurableSpace E]
    {P ν : Measure E} {p : E → ℝ} (hp : HasDensity P ν p) (φ : E → ℝ) :
    (Integrable φ P ↔ Integrable (fun x ↦ p x * φ x) ν) ∧
      ∫ x, φ x ∂P = ∫ x, p x * φ x ∂ν := by
  obtain ⟨hpm, hp0, hPe⟩ := hp
  have hae : (fun x ↦ (ENNReal.ofReal (p x)).toReal • φ x) =ᵐ[ν] fun x ↦ p x * φ x := by
    filter_upwards [hp0] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  subst hPe
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hpm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integrable_congr hae
  · rw [integral_withDensity_eq_integral_toReal_smul hpm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integral_congr_ae hae

/-- The density of a probability law is integrable with integral one. -/
theorem integrable_and_integral_eq_one_of_hasDensity {E : Type*} [MeasurableSpace E]
    {P ν : Measure E} [IsProbabilityMeasure P] {p : E → ℝ} (hp : HasDensity P ν p) :
    Integrable p ν ∧ ∫ x, p x ∂ν = 1 := by
  obtain ⟨h1, h2⟩ := integrable_and_integral_eq_of_hasDensity hp (fun _ ↦ 1)
  simp only [mul_one] at h1 h2
  exact ⟨h1.1 (integrable_const 1), by rw [← h2]; simp⟩

/-- The derivative in a real parameter of a family of measurable functions, differentiable in the
parameter, is measurable in the observation. -/
theorem measurable_deriv_param {E : Type*} [MeasurableSpace E] (φ : ℝ → E → ℝ)
    (hm : ∀ t, Measurable (φ t)) (hd : ∀ x, Differentiable ℝ (fun t ↦ φ t x)) (t₀ : ℝ) :
    Measurable (fun x ↦ deriv (fun t ↦ φ t x) t₀) := by
  let u : ℕ → ℝ := fun k ↦ t₀ + 1 / ((k : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝[≠] t₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
    · simpa [u] using (tendsto_const_nhds (x := t₀)).add tendsto_one_div_add_atTop_nhds_zero_nat
    · simp only [u, mem_compl_iff, mem_singleton_iff, add_eq_left]
      positivity
  refine measurable_of_tendsto_metrizable (f := fun k x ↦ slope (fun t ↦ φ t x) t₀ (u k))
    (fun k ↦ ?_) (tendsto_pi_nhds.2 fun x ↦ ((hd x t₀).hasDerivAt.tendsto_slope).comp hu)
  simp only [slope_def_field]
  exact ((hm _).sub (hm _)).div_const _

/-- A second-order Taylor bound for the derivative of a `C³` function whose third derivative is
bounded by `M` on a ball. -/
theorem abs_deriv_sub_taylor_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (θ₀ r M : ℝ)
    (hM : ∀ t, |t - θ₀| < r → |deriv (deriv (deriv φ)) t| ≤ M) (t : ℝ) (ht : |t - θ₀| < r) :
    |deriv φ t - deriv φ θ₀ - (t - θ₀) * deriv (deriv φ) θ₀| ≤ M * (t - θ₀) ^ 2 := by
  have h3 : ContDiff ℝ (2 + 1) φ := hφ
  have h2 : ContDiff ℝ (1 + 1) (deriv φ) := (contDiff_succ_iff_deriv.1 h3).2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv φ)) := (contDiff_succ_iff_deriv.1 h2).2.2
  have hd1 : Differentiable ℝ (deriv φ) := (contDiff_succ_iff_deriv.1 h2).1
  have hd2 : Differentiable ℝ (deriv (deriv φ)) := h1.differentiable one_ne_zero
  have hball : ∀ s, |s - θ₀| < r → s ∈ Metric.ball θ₀ r := fun s hs ↦ by
    rwa [Metric.mem_ball, Real.dist_eq]
  have hstep : ∀ s, |s - θ₀| < r →
      |deriv (deriv φ) s - deriv (deriv φ) θ₀| ≤ M * |s - θ₀| := by
    intro s hs
    have := (convex_ball θ₀ r).norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv φ))
      (fun x _ ↦ hd2 x) (fun x hx ↦ by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        simpa [Real.norm_eq_abs] using hM x hx)
      (Metric.mem_ball_self (lt_of_le_of_lt (abs_nonneg _) ht)) (hball s hs)
    simpa [Real.norm_eq_abs] using this
  let ψ : ℝ → ℝ := fun s ↦ deriv φ s - deriv φ θ₀ - (s - θ₀) * deriv (deriv φ) θ₀
  have hψd : ∀ s, HasDerivAt ψ (deriv (deriv φ) s - deriv (deriv φ) θ₀) s := by
    intro s
    have := ((hd1 s).hasDerivAt.sub_const (deriv φ θ₀)).sub
      (((hasDerivAt_id s).sub_const θ₀).mul_const (deriv (deriv φ) θ₀))
    convert this using 1
    · funext y; simp [ψ]
    · ring
  have hseg : uIcc θ₀ t ⊆ {s | |s - θ₀| ≤ |t - θ₀|} := by
    intro s hs
    simp only [mem_ofPred_eq]
    rcases le_total θ₀ t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]; linarith [hs.2]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]; linarith [hs.1]
  have hmv := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_deriv_le (f := ψ)
    (C := M * |t - θ₀|) (fun x _ ↦ (hψd x).differentiableAt) (fun x hx ↦ by
      rw [(hψd x).deriv, Real.norm_eq_abs]
      have hx' : |x - θ₀| ≤ |t - θ₀| := hseg hx
      calc |deriv (deriv φ) x - deriv (deriv φ) θ₀| ≤ M * |x - θ₀| :=
            hstep x (lt_of_le_of_lt hx' ht)
        _ ≤ M * |t - θ₀| := by
            have hM0 : 0 ≤ M := by
              have := hM θ₀ (by simpa using lt_of_le_of_lt (abs_nonneg _) ht)
              exact (abs_nonneg _).trans this
            exact mul_le_mul_of_nonneg_left hx' hM0)
    left_mem_uIcc right_mem_uIcc
  have hψ0 : ψ θ₀ = 0 := by simp [ψ]
  rw [hψ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc |deriv φ t - deriv φ θ₀ - (t - θ₀) * deriv (deriv φ) θ₀| = |ψ t| := rfl
    _ ≤ M * |t - θ₀| * |t - θ₀| := hmv
    _ = M * (t - θ₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A second-order Taylor bound for a `C³` function whose third derivative is bounded by `M`
on a ball: the remainder is at most `M |t - θ₀|³`. -/
theorem abs_sub_taylor_two_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ 3 φ) (θ₀ r M : ℝ)
    (hM : ∀ t, |t - θ₀| < r → |deriv (deriv (deriv φ)) t| ≤ M) (t : ℝ) (ht : |t - θ₀| < r) :
    |φ t - φ θ₀ - (t - θ₀) * deriv φ θ₀ - (t - θ₀) ^ 2 / 2 * deriv (deriv φ) θ₀| ≤
      M * |t - θ₀| ^ 3 := by
  have h3 : ContDiff ℝ (2 + 1) φ := hφ
  have hd0 : Differentiable ℝ φ := (contDiff_succ_iff_deriv.1 h3).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM θ₀ (by simpa using lt_of_le_of_lt (abs_nonneg _) ht))
  let g : ℝ → ℝ := fun s ↦ φ s - φ θ₀ - (s - θ₀) * deriv φ θ₀ -
    (s - θ₀) ^ 2 / 2 * deriv (deriv φ) θ₀
  have hgd : ∀ s, HasDerivAt g (deriv φ s - deriv φ θ₀ - (s - θ₀) * deriv (deriv φ) θ₀) s := by
    intro s
    have h1 := (((hd0 s).hasDerivAt.sub_const (φ θ₀)).sub
      (((hasDerivAt_id s).sub_const θ₀).mul_const (deriv φ θ₀))).sub
      ((((hasDerivAt_id s).sub_const θ₀).pow 2).div_const 2 |>.mul_const (deriv (deriv φ) θ₀))
    convert h1 using 1
    · funext y; simp [g]
    · simp
  have hseg : ∀ s ∈ uIcc θ₀ t, |s - θ₀| ≤ |t - θ₀| := by
    intro s hs
    rcases le_total θ₀ t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]; linarith [hs.2]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]; linarith [hs.1]
  have hmv := (convex_uIcc θ₀ t).norm_image_sub_le_of_norm_deriv_le (f := g)
    (C := M * |t - θ₀| ^ 2) (fun x _ ↦ (hgd x).differentiableAt) (fun x hx ↦ by
      rw [(hgd x).deriv, Real.norm_eq_abs]
      have hx' := hseg x hx
      calc |deriv φ x - deriv φ θ₀ - (x - θ₀) * deriv (deriv φ) θ₀| ≤ M * (x - θ₀) ^ 2 :=
            abs_deriv_sub_taylor_le φ hφ θ₀ r M hM x (lt_of_le_of_lt hx' ht)
        _ ≤ M * |t - θ₀| ^ 2 := by
            rw [← sq_abs (x - θ₀)]
            gcongr)
    left_mem_uIcc right_mem_uIcc
  have hg0 : g θ₀ = 0 := by simp [g]
  rw [hg0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc _ = |g t| := rfl
    _ ≤ M * |t - θ₀| ^ 2 * |t - θ₀| := hmv
    _ = M * |t - θ₀| ^ 3 := by ring

/-- Deterministic core of Cramér's argument: from the linearized score equation
`Z + W B + q = 0` with `B` close to `-I` and a quadratic remainder `q`, the scaled error `W` is
within `4 κ |Z| / I²` of `Z / I`. -/
theorem abs_sub_div_le_of_score_equation {W Z B q d A I κ : ℝ} (hI : 0 < I) (hκ : κ ≤ I / 4)
    (heq : Z + W * B + q = 0) (hq : |q| ≤ |W| * (d * A)) (hB : |B + I| ≤ κ)
    (hdA : d * A ≤ κ) :
    |W - Z / I| ≤ 4 * κ * |Z| / I ^ 2 := by
  have hkey : W * I - Z = W * (B + I) + q := by linear_combination -heq
  have h1 : |W * I - Z| ≤ 2 * κ * |W| := by
    rw [hkey]
    calc |W * (B + I) + q| ≤ |W * (B + I)| + |q| := abs_add_le _ _
      _ ≤ |W| * κ + |W| * κ := by
          rw [abs_mul]
          gcongr
          exact hq.trans (mul_le_mul_of_nonneg_left hdA (abs_nonneg W))
      _ = 2 * κ * |W| := by ring
  have hW : |W| * I ≤ 2 * |Z| := by
    have : |W * I| ≤ |Z| + 2 * κ * |W| := by
      calc |W * I| = |(W * I - Z) + Z| := by ring_nf
        _ ≤ |W * I - Z| + |Z| := abs_add_le _ _
        _ ≤ 2 * κ * |W| + |Z| := by linarith
        _ = |Z| + 2 * κ * |W| := by ring
    rw [abs_mul, abs_of_pos hI] at this
    nlinarith [abs_nonneg W]
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hB
  have h2 : |W * I - Z| ≤ 4 * κ * |Z| / I := by
    rw [le_div_iff₀ hI]
    nlinarith [abs_nonneg W, abs_nonneg Z]
  have : W - Z / I = (W * I - Z) / I := by field_simp
  rw [this, abs_div, abs_of_pos hI, div_le_iff₀ hI]
  calc |W * I - Z| ≤ 4 * κ * |Z| / I := h2
    _ = 4 * κ * |Z| / I ^ 2 * I := by field_simp

/-- GAPS 102.3, scalar smooth likelihood-score roots and their efficient expansion.
`ell` is the per-observation log likelihood; the score/information moment
identities and the local third-derivative envelope are explicit hypotheses. -/
theorem mle_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (ell : ℝ → E → ℝ)
    (hm : ∀ theta, Measurable (ell theta)) (hsmooth : ∀ x, ContDiff ℝ 3 (fun theta ↦ ell theta x))
    (theta₀ I : ℝ) (hI : 0 < I) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M P)
    (henv : ∀ x theta, |theta - theta₀| < r →
      |deriv (deriv (deriv (fun t ↦ ell t x))) theta| ≤ M x)
    (hscore : MemLp (fun x ↦ deriv (fun t ↦ ell t x) theta₀) 2 P)
    (hmean : (∫ x, deriv (fun t ↦ ell t x) theta₀ ∂P) = 0)
    (hvar : (∫ x, deriv (fun t ↦ ell t x) theta₀ ^ 2 ∂P) = I)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀) P)
    (hinfo : (∫ x, deriv (deriv (fun t ↦ ell t x)) theta₀ ∂P) = -I)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : ∀ n : ℕ, 1 ≤ n → ∀ᵐ w ∂mu,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0) :
    TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        deriv (fun t ↦ ell t (X i w)) theta₀) 0 ∧
      TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hc3 : ∀ x, ContDiff ℝ (2 + 1) (fun t ↦ ell t x) := hsmooth
  have hdiff : ∀ x, Differentiable ℝ (fun t ↦ ell t x) := fun x ↦
    (contDiff_succ_iff_deriv.1 (hc3 x)).1
  have hdiff1 : ∀ x, Differentiable ℝ (fun t ↦ deriv (fun s ↦ ell s x) t) := fun x ↦
    ((contDiff_succ_iff_deriv.1 (hc3 x)).2.2).differentiable (by norm_num)
  set S : E → ℝ := fun x ↦ deriv (fun t ↦ ell t x) theta₀ with hSdef
  set H : E → ℝ := fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀ with hHdef
  have hSm : Measurable S := measurable_deriv_param ell hm hdiff theta₀
  have hℓ1m : ∀ t, Measurable (fun x ↦ deriv (fun s ↦ ell s x) t) :=
    measurable_deriv_param ell hm hdiff
  have hHm : Measurable H :=
    measurable_deriv_param (fun t x ↦ deriv (fun s ↦ ell s x) t) hℓ1m hdiff1 theta₀
  set M' : E → ℝ := hM.aestronglyMeasurable.mk M with hM'def
  have hM'm : Measurable M' := hM.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMM' : M =ᵐ[P] M' := hM.aestronglyMeasurable.ae_eq_mk
  have hM'i : Integrable M' P := hM.congr hMM'
  have hMae : ∀ᵐ w ∂mu, ∀ i, M (X i w) = M' (X i w) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ x ∂(mu.map (X i)), M x = M' x := by rw [hlaw i]; exact hMM'
    exact ae_of_ae_map (hXm i).aemeasurable this
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w) with hZ
  set B : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H (X i w) with hB
  set A : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M' (X i w) with hA
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ hSm.comp (hXm i)).const_mul _
  have hZlim : TendstoInDistribution mu Z (gaussianReal 0 (Real.toNNReal I)) := by
    have := tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu P X ⟨hXm, hind, hlaw⟩ S hSm
      hscore hmean
    rwa [hvar] at this
  have hBlim : TendstoInProbabilityConst mu B (-I) := by
    have := tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ H hHm hhess
    rwa [hinfo] at this
  have hAlim : TendstoInProbabilityConst mu A (∫ x, M' x ∂P) :=
    tendstoInProbabilityConst_sampleMean_of_iid mu P X ⟨hXm, hind, hlaw⟩ M' hM'm hM'i
  set m : ℝ := ∫ x, M' x ∂P with hmdef
  have hrem : TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0 := by
    intro ε hε
    refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
    have hη5 : 0 < η / 5 := by positivity
    obtain ⟨K, hK, hZev⟩ :=
      exists_measureReal_lt_norm_le_of_tendstoInDistribution mu Z hZm _ hZlim hη5
    set κ : ℝ := min (I / 4) (ε * I ^ 2 / (8 * K)) with hκ
    have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
    have hκI : κ ≤ I / 4 := min_le_left _ _
    have hκK : 4 * κ * K / I ^ 2 ≤ ε / 2 := by
      have : κ ≤ ε * I ^ 2 / (8 * K) := min_le_right _ _
      rw [div_le_iff₀ (by positivity)]
      calc 4 * κ * K ≤ 4 * (ε * I ^ 2 / (8 * K)) * K := by gcongr
        _ = ε / 2 * I ^ 2 := by field_simp; ring
    have ev : ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) → ∀ᶠ n in atTop, u n ≤ η / 5 :=
      fun hu ↦ hu.eventually (eventually_le_nhds hη5)
    have hm1 : 0 < κ / (|m| + 1) := by positivity
    filter_upwards [hZev, ev (hcons (r / 2) (by positivity)), ev (hBlim κ hκpos),
      ev (hAlim 1 one_pos), ev (hcons _ hm1), eventually_ge_atTop 1]
      with n hZn h1 h2 h3 h4 hn1
    set N : Set Ω := {w | ¬ ((∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0 ∧
      ∀ i, M (X i w) = M' (X i w))} with hN
    have hnull : mu N = 0 := by
      have := (hroot n hn1).and hMae
      rwa [ae_iff] at this
    have hsub : {w | ε < dist (Real.sqrt n * (T n w - theta₀) -
        (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0} ⊆
        N ∪ {w | r / 2 < dist (T n w) theta₀} ∪ {w | κ < dist (B n w) (-I)} ∪
          {w | 1 < dist (A n w) m} ∪ {w | κ / (|m| + 1) < dist (T n w) theta₀} ∪
            {w | K < ‖Z n w‖} := by
      intro w hw
      by_contra hcon
      simp only [mem_union, not_or, mem_ofPred_eq, not_lt, hN, not_not] at hcon
      obtain ⟨⟨⟨⟨⟨⟨hroot', hM'w⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩ := hcon
      simp only [mem_ofPred_eq] at hw
      refine (not_lt.2 ?_) hw
      rw [Real.dist_eq] at g1 g2 g3 g4
      rw [Real.norm_eq_abs] at g5
      set d : ℝ := |T n w - theta₀| with hd
      have hdr : d < r := by linarith
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
      have hnsq : ((n : ℝ))⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      set R : ℕ → ℝ := fun i ↦ deriv (fun t ↦ ell t (X i w)) (T n w) - S (X i w) -
        (T n w - theta₀) * H (X i w) with hR
      have hRb : ∀ i, |R i| ≤ M' (X i w) * (T n w - theta₀) ^ 2 := fun i ↦ by
        rw [← hM'w i]
        exact abs_deriv_sub_taylor_le (fun t ↦ ell t (X i w)) (hsmooth _) theta₀ r (M (X i w))
          (fun t ht ↦ henv _ t ht) (T n w) hdr
      set q : ℝ := (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, R i with hq
      have hsumR : ∑ i ∈ Finset.range n, R i = -(∑ i ∈ Finset.range n, S (X i w)) -
          (T n w - theta₀) * ∑ i ∈ Finset.range n, H (X i w) := by
        simp only [hR, Finset.sum_sub_distrib, ← Finset.mul_sum, hroot']
        ring
      have heq : Z n w + Real.sqrt n * (T n w - theta₀) * B n w + q = 0 := by
        simp only [hZ, hB, hq, hsumR]
        rw [hnsq]
        field_simp
        ring
      have hqb : |q| ≤ |Real.sqrt n * (T n w - theta₀)| * (d * A n w) := by
        have h1 : |∑ i ∈ Finset.range n, R i| ≤
            (T n w - theta₀) ^ 2 * ∑ i ∈ Finset.range n, M' (X i w) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ ↦ (hRb i).trans_eq (mul_comm _ _)
        rw [hq, abs_mul, abs_inv, abs_of_pos hsn, abs_mul, abs_of_pos hsn, hd]
        calc (Real.sqrt n)⁻¹ * |∑ i ∈ Finset.range n, R i|
            ≤ (Real.sqrt n)⁻¹ * ((T n w - theta₀) ^ 2 * ∑ i ∈ Finset.range n, M' (X i w)) :=
              mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hsn.le)
          _ = Real.sqrt n * |T n w - theta₀| * (|T n w - theta₀| * A n w) := by
              simp only [hA]
              rw [← sq_abs (T n w - theta₀), hnsq]
              field_simp
      have hBI : |B n w + I| ≤ κ := by simpa [sub_neg_eq_add] using g2
      have hdA : d * A n w ≤ κ := by
        have hAabs : |A n w| ≤ |m| + 1 := by
          have := abs_sub_abs_le_abs_sub (A n w) m
          linarith
        have hd0 : 0 ≤ d := abs_nonneg _
        have hdk : d ≤ κ / (|m| + 1) := g4
        calc d * A n w ≤ d * |A n w| := mul_le_mul_of_nonneg_left (le_abs_self _) hd0
          _ ≤ d * (|m| + 1) := mul_le_mul_of_nonneg_left hAabs hd0
          _ ≤ κ / (|m| + 1) * (|m| + 1) := mul_le_mul_of_nonneg_right hdk (by positivity)
          _ = κ := div_mul_cancel₀ κ (by positivity)
      have hmain := abs_sub_div_le_of_score_equation hI hκI heq hqb hBI hdA
      have hform : Real.sqrt n * (T n w - theta₀) -
          (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w) =
          Real.sqrt n * (T n w - theta₀) - Z n w / I := by
        simp only [hZ]; rw [mul_inv]; ring
      rw [Real.dist_eq, sub_zero, hform]
      calc |Real.sqrt n * (T n w - theta₀) - Z n w / I| ≤ 4 * κ * |Z n w| / I ^ 2 := hmain
        _ ≤ 4 * κ * K / I ^ 2 := by gcongr
        _ ≤ ε / 2 := hκK
        _ ≤ ε := by linarith
    calc mu.real {w | ε < dist (Real.sqrt n * (T n w - theta₀) -
          (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, S (X i w)) 0}
        ≤ mu.real (N ∪ {w | r / 2 < dist (T n w) theta₀} ∪ {w | κ < dist (B n w) (-I)} ∪
          {w | 1 < dist (A n w) m} ∪ {w | κ / (|m| + 1) < dist (T n w) theta₀} ∪
            {w | K < ‖Z n w‖}) := measureReal_mono hsub
      _ ≤ mu.real N + mu.real {w | r / 2 < dist (T n w) theta₀} +
          mu.real {w | κ < dist (B n w) (-I)} + mu.real {w | 1 < dist (A n w) m} +
          mu.real {w | κ / (|m| + 1) < dist (T n w) theta₀} + mu.real {w | K < ‖Z n w‖} := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measureReal_union_le _ _
      _ ≤ 0 + η / 5 + η / 5 + η / 5 + η / 5 + η / 5 := by
        rw [measureReal_def, hnull, ENNReal.toReal_zero]
        gcongr
      _ = η := by ring
  refine ⟨hrem, ?_⟩
  have hX' : TendstoInDistribution mu (fun n w ↦ I⁻¹ * Z n w)
      (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
    have := tendstoInDistribution_comp_of_continuous mu Z hZm _ (fun x ↦ I⁻¹ * x)
      (continuous_const.mul continuous_id) hZlim
    convert this using 1
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hI.le,
      Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]
    field_simp
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub mu _ _
    (fun n ↦ (hZm n).const_mul _) (fun n ↦ ((hT n).sub_const _).const_mul _) _ hX' ?_
  convert hrem using 3 with n w
  simp only [hZ]
  rw [mul_inv]
  ring


/-- The empirical distribution function as a normalised sum of indicators. -/
theorem empiricalCDF_eq_sum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    empiricalCDF X n ω t = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, if X i ω ≤ t then (1 : ℝ) else 0 := by
  rw [empiricalCDF, Finset.sum_boole, div_eq_inv_mul]

/-- The empirical distribution function is monotone. -/
theorem empiricalCDF_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (empiricalCDF X n ω) := by
  intro s t hst
  rw [empiricalCDF_eq_sum, empiricalCDF_eq_sum]
  gcongr with i hi
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hst) h2
  · norm_num
  · exact le_rfl

/-- The empirical distribution function is `1` at `∑ |Xᵢ|` and `0` below `-∑ |Xᵢ|`. -/
theorem empiricalCDF_extremes {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
    empiricalCDF X n ω (∑ i ∈ Finset.range n, |X i ω|) = 1 ∧
      ∀ s < -∑ i ∈ Finset.range n, |X i ω|, empiricalCDF X n ω s = 0 := by
  have hle : ∀ i ∈ Finset.range n, |X i ω| ≤ ∑ j ∈ Finset.range n, |X j ω| := fun i hi ↦
    Finset.single_le_sum (f := fun j ↦ |X j ω|) (fun j _ ↦ abs_nonneg _) hi
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  constructor
  · rw [empiricalCDF_eq_sum, Finset.sum_congr rfl fun i hi ↦
      (show (if X i ω ≤ ∑ j ∈ Finset.range n, |X j ω| then (1 : ℝ) else 0) = 1 by
        simp [(le_abs_self _).trans (hle i hi)])]
    simp [hn0]
  · intro s hs
    rw [empiricalCDF_eq_sum, Finset.sum_eq_zero fun i hi ↦ ?_, mul_zero]
    have := neg_abs_le (X i ω)
    have : ¬ X i ω ≤ s := by linarith [hle i hi]
    simp [this]

/-- Order characterisation of the left sample quantile, for `n ≥ 1` and `p ∈ (0, 1]`. -/
theorem le_empiricalCDF_of_sampleQuantile_lt {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ω : Ω) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ s, sampleQuantile X n ω p < s → p ≤ empiricalCDF X n ω s) ∧
      (∀ s, s < sampleQuantile X n ω p → empiricalCDF X n ω s < p) := by
  obtain ⟨h1, h0⟩ := empiricalCDF_extremes X n hn ω
  set A := {t | p ≤ empiricalCDF X n ω t} with hA
  have hne : A.Nonempty := ⟨∑ i ∈ Finset.range n, |X i ω|, by
    show p ≤ empiricalCDF X n ω _
    rw [h1]; exact hp1⟩
  have hbdd : BddBelow A := by
    refine ⟨-∑ i ∈ Finset.range n, |X i ω|, fun a ha ↦ ?_⟩
    by_contra h
    push Not at h
    have := h0 a h
    simp only [hA, mem_ofPred_eq, this] at ha
    linarith
  constructor
  · intro s hs
    obtain ⟨a, ha, has⟩ := exists_lt_of_csInf_lt hne hs
    exact le_trans ha (empiricalCDF_mono X n ω has.le)
  · intro s hs
    by_contra h
    push Not at h
    exact absurd (csInf_le hbdd h) (not_le.2 hs)

/-- Measurability of the empirical distribution function at a fixed point. -/
theorem measurable_empiricalCDF {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) (t : ℝ) : Measurable fun ω ↦ empiricalCDF X n ω t := by
  simp_rw [empiricalCDF_eq_sum]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _
  exact Measurable.ite (measurableSet_le (hX i) measurable_const) measurable_const
    measurable_const

/-- Measurability of the left sample quantile, for `p ∈ (0, 1]`. -/
theorem measurable_sampleQuantile {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Measurable fun ω ↦ sampleQuantile X n ω p := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    have : ∀ ω, sampleQuantile X 0 ω p = sInf {t : ℝ | p ≤ 0} := fun ω ↦ by
      simp [sampleQuantile, empiricalCDF]
    simp_rw [this]
    exact measurable_const
  refine measurable_of_Iio fun s ↦ ?_
  have hset : (fun ω ↦ sampleQuantile X n ω p) ⁻¹' Iio s =
      ⋃ a : ℚ, ⋃ (_ : (a : ℝ) < s), {ω | p ≤ empiricalCDF X n ω a} := by
    ext ω
    obtain ⟨hlt, hgt⟩ := le_empiricalCDF_of_sampleQuantile_lt X n hn ω hp0 hp1
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn h
      exact ⟨a, ha2, hlt _ ha1⟩
    · rintro ⟨a, ha, hpa⟩
      by_contra hcon
      push Not at hcon
      have := hgt a (lt_of_lt_of_le ha hcon)
      linarith
  rw [hset]
  exact MeasurableSet.iUnion fun a ↦ MeasurableSet.iUnion fun _ ↦
    measurableSet_le measurable_const (measurable_empiricalCDF X hX n a)

/-- The integral of the indicator of `(-∞, a]` is the distribution function at `a`. -/
theorem integral_ite_le_eq_cdf (P : Measure ℝ) [IsProbabilityMeasure P] (a : ℝ) :
    ∫ x, (if x ≤ a then (1 : ℝ) else 0) ∂P = cdf P a := by
  have : (fun x : ℝ ↦ if x ≤ a then (1 : ℝ) else 0) = (Iic a).indicator 1 := by
    ext x; simp [indicator, mem_Iic]
  rw [this, integral_indicator_one measurableSet_Iic]
  rfl

/-- `√n / n = 1 / √n`, in the form used for normalised sums. -/
theorem sqrt_mul_inv_natCast (n : ℕ) : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
  rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]

/-- Local increments of a distribution function differentiable at `q`:
`√n (F(q + t/√n) - F(q)) → f t`. -/
theorem tendsto_sqrt_mul_cdf_sub (P : Measure ℝ) [IsProbabilityMeasure P] (q f t : ℝ)
    (hd : HasDerivAt (cdf P) f q) :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (cdf P (q + t / Real.sqrt n) - cdf P q)) atTop
      (𝓝 (f * t)) := by
  by_cases ht : t = 0
  · simp [ht]
  have hsq : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ ↦ t / Real.sqrt n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop hsq, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    exact div_ne_zero ht this.ne'
  have hs := (hd.tendsto_slope_zero.comp hh).const_mul t
  rw [mul_comm f t]
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [Function.comp, smul_eq_mul]
  field_simp

/-- The local empirical process at `q`: `√n (Fₙ(q + t/√n) - Fₙ(q)) → f t` in probability when the
distribution function is differentiable at `q` with derivative `f`. -/
theorem tendstoInProbabilityConst_sqrt_mul_empiricalCDF_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (q f t : ℝ)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (empiricalCDF X n ω (q + t / Real.sqrt n) - empiricalCDF X n ω q)) (f * t) := by
  set a : ℕ → ℝ := fun n ↦ q + t / Real.sqrt n with ha
  set ind : ℝ → ℝ → ℝ := fun b x ↦ if x ≤ b then (1 : ℝ) else 0 with hind
  have hindm : ∀ b, Measurable (ind b) := fun b ↦
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  set φ : ℕ → ℝ → ℝ := fun n x ↦ (Real.sqrt n)⁻¹ * (ind (a n) x - ind q x) with hφ
  have hφm : ∀ n, Measurable (φ n) := fun n ↦ ((hindm _).sub (hindm _)).const_mul _
  have hbound : ∀ n x, |ind (a n) x - ind q x| ≤ 1 := fun n x ↦ by
    simp only [hind]; split_ifs <;> norm_num
  have hφ2 : ∀ n, MemLp (φ n) 2 P := fun n ↦
    MemLp.of_bound (hφm n).aestronglyMeasurable ((Real.sqrt n)⁻¹) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (hbound n x))
  have hsq : Tendsto (fun n : ℕ ↦ Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hat : Tendsto a atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds (x := q)).add ((tendsto_const_nhds (x := t)).div_atTop hsq)
  have hcont : ContinuousAt (cdf P) q := hd.continuousAt
  have hsqid : ∀ b c x, (ind b x - ind c x) ^ 2 = ind b x + ind c x - 2 * ind (min b c) x :=
    fun b c x ↦ by simp only [hind, le_min_iff]; split_ifs <;> simp_all; norm_num
  have hint : ∀ b, Integrable (ind b) P := fun b ↦
    (integrable_const (1 : ℝ)).mono (hindm b).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simp only [hind]; split_ifs <;> norm_num)
  have hlim : Tendsto (fun n : ℕ ↦ n * ∫ x, φ n x ^ 2 ∂P) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ cdf P (a n)) atTop (𝓝 (cdf P q)) := hcont.tendsto.comp hat
    have hmin : Tendsto (fun n ↦ min (a n) q) atTop (𝓝 q) := by
      simpa using hat.min (tendsto_const_nhds (x := q))
    have h2 : Tendsto (fun n ↦ cdf P (min (a n) q)) atTop (𝓝 (cdf P q)) :=
      hcont.tendsto.comp hmin
    have hm : Tendsto (fun n ↦ cdf P (a n) + cdf P q - 2 * cdf P (min (a n) q)) atTop
        (𝓝 (cdf P q + cdf P q - 2 * cdf P q)) :=
      (h1.add tendsto_const_nhds).sub (h2.const_mul 2)
    rw [show cdf P q + cdf P q - 2 * cdf P q = 0 by ring] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [hφ, mul_pow, hsqid]
    rw [integral_const_mul, integral_sub (f := fun x ↦ ind (a n) x + ind q x)
      (g := fun x ↦ 2 * ind (min (a n) q) x) ((hint _).add (hint _)) ((hint _).const_mul 2),
      integral_add (hint _) (hint _), integral_const_mul]
    simp only [hind, integral_ite_le_eq_cdf]
    rw [inv_pow, hs2]
    field_simp
  have hW := tendstoInProbabilityConst_sum_sub_of_iid μ P X hiid φ hφm hφ2 hlim
  have hD := tendstoInProbabilityConst_const_of_tendsto μ _
    (by simpa using (tendsto_sqrt_mul_cdf_sub P q f t hd).sub_const (f * t))
  have hsum := tendstoInProbabilityConst_add_zero μ _ _ hW hD
  intro ε hε
  refine (hsum ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero]
  rw [empiricalCDF_eq_sum, empiricalCDF_eq_sum]
  simp only [hφ, integral_const_mul]
  rw [integral_sub (hint _) (hint _)]
  simp only [hind, integral_ite_le_eq_cdf, ← Finset.mul_sum, Finset.sum_sub_distrib, ha]
  have e1 : (n : ℝ) * (Real.sqrt n)⁻¹ = Real.sqrt n := by
    rw [mul_comm, inv_mul_eq_div, Real.div_sqrt]
  have e2 := sqrt_mul_inv_natCast n
  rw [← mul_assoc (n : ℝ), e1]
  apply iff_of_eq
  congr 2
  linear_combination (-((∑ x ∈ Finset.range n, if X x ω ≤ q + t / Real.sqrt n then (1 : ℝ) else 0) -
    ∑ x ∈ Finset.range n, if X x ω ≤ q then (1 : ℝ) else 0)) * e2

/-- Central limit theorem for the empirical distribution function at a point `q` with
`F(q) = p`: `√n (p - Fₙ(q)) / f` converges in law to `N(0, p(1-p)/f²)`. -/
theorem tendstoInDistribution_sqrt_mul_sub_empiricalCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hq : cdf P q = p) (hf : 0 < f) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f)
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  set ind : ℝ → ℝ := fun x ↦ if x ≤ q then (1 : ℝ) else 0 with hind
  have hindm : Measurable ind := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hinti : Integrable ind P := (integrable_const (1 : ℝ)).mono hindm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simp only [hind]; split_ifs <;> norm_num)
  set s : ℝ → ℝ := fun x ↦ ind x - p with hs
  have hsm : Measurable s := hindm.sub measurable_const
  have hs2 : MemLp s 2 P := MemLp.of_bound hsm.aestronglyMeasurable (1 + |p|)
    (ae_of_all _ fun x ↦ by
      simp only [hs, hind, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      gcongr
      split_ifs <;> norm_num)
  have hs0 : ∫ x, s x ∂P = 0 := by
    simp only [hs]
    rw [integral_sub hinti (integrable_const p), hind, integral_ite_le_eq_cdf, hq]
    simp
  have hsq : ∫ x, s x ^ 2 ∂P = p * (1 - p) := by
    have : ∀ x, s x ^ 2 = (1 - 2 * p) * ind x + p ^ 2 := fun x ↦ by
      simp only [hs, hind]; split_ifs <;> ring
    simp_rw [this]
    rw [integral_add (hinti.const_mul _) (integrable_const _), integral_const_mul, hind,
      integral_ite_le_eq_cdf, hq]
    simp; ring
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid s hsm hs2 hs0
  rw [hsq] at hclt
  have hZm : ∀ n : ℕ, Measurable fun ω ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω) :=
    fun n ↦ (Finset.measurable_sum _ fun i _ ↦ hsm.comp (hiid.1 i)).const_mul _
  have := tendstoInDistribution_comp_of_continuous μ _ hZm _ (fun x ↦ -f⁻¹ * x)
    (continuous_const.mul continuous_id) hclt
  have hpp : 0 ≤ p * (1 - p) := by
    have h0 : 0 ≤ p := by rw [← hq]; exact measureReal_nonneg
    have h1 : p ≤ 1 := by rw [← hq]; exact measureReal_le_one
    nlinarith
  convert this using 1
  · funext n ω
    simp only [hs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      empiricalCDF_eq_sum, hind]
    have e1 : (Real.sqrt n)⁻¹ * ((n : ℝ) * p) = Real.sqrt n * p := by
      rw [← mul_assoc, mul_comm _ (n : ℝ), ← div_eq_mul_inv, Real.div_sqrt]
    have e2 := sqrt_mul_inv_natCast n
    rw [div_eq_mul_inv]
    linear_combination (-f⁻¹ * ∑ i ∈ Finset.range n, if X i ω ≤ q then (1 : ℝ) else 0) * e2 -
      f⁻¹ * e1
  · rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpp,
      Real.coe_toNNReal _ (div_nonneg hpp (sq_nonneg f))]
    field_simp

/-- Ghosh's crossing lemma: if `Wₙ` is bounded in probability and, for all `t` and `ε > 0`, the
probabilities of the crossing events `{Vₙ ≤ t, Wₙ ≥ t + ε}` and `{Vₙ ≥ t + ε, Wₙ ≤ t}` tend to `0`,
then `Vₙ - Wₙ → 0` in probability. -/
theorem tendstoInProbabilityConst_sub_of_crossing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V W : ℕ → Ω → ℝ) (hW : IsBoundedInProbability μ W)
    (h1 : ∀ t ε, 0 < ε → Tendsto (fun n ↦ μ.real {ω | V n ω ≤ t ∧ t + ε ≤ W n ω}) atTop (𝓝 0))
    (h2 : ∀ t ε, 0 < ε → Tendsto (fun n ↦ μ.real {ω | t + ε ≤ V n ω ∧ W n ω ≤ t}) atTop (𝓝 0)) :
    TendstoInProbabilityConst μ (fun n ω ↦ V n ω - W n ω) 0 := by
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun _ ↦ measureReal_nonneg) fun η hη ↦ ?_
  obtain ⟨C, hC, hev⟩ := hW (η / 2) (half_pos hη)
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := half_pos hε
  set N := ⌊2 * C / δ⌋₊ with hN
  set tk : ℕ → ℝ := fun k ↦ -C + k * δ with htk
  set E1 : ℕ → ℕ → Set Ω := fun n k ↦ {ω | tk (k + 1) + δ ≤ V n ω ∧ W n ω ≤ tk (k + 1)}
    with hE1
  set E2 : ℕ → ℕ → Set Ω := fun n k ↦ {ω | V n ω ≤ tk k - δ ∧ tk k - δ + δ ≤ W n ω} with hE2
  have hsum : Tendsto (fun n ↦ ∑ k ∈ Finset.range (N + 1), (μ.real (E1 n k) + μ.real (E2 n k)))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (N + 1)) fun k _ ↦
      (h2 (tk (k + 1)) δ hδ0).add (h1 (tk k - δ) δ hδ0)
    simp only [add_zero, Finset.sum_const_zero] at this
    exact this
  filter_upwards [hev, hsum.eventually (eventually_le_nhds (half_pos hη))] with n hn1 hn2
  have hsub : {ω | ε < dist (V n ω - W n ω) 0} ⊆
      {ω | C < |W n ω|} ∪ ⋃ k ∈ Finset.range (N + 1), (E1 n k ∪ E2 n k) := by
    intro ω hω
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    by_cases hWC : C < |W n ω|
    · exact Or.inl hWC
    right
    push Not at hWC
    rw [abs_le] at hWC
    have hnn : 0 ≤ (W n ω + C) / δ := div_nonneg (by linarith) hδ0.le
    set k := ⌊(W n ω + C) / δ⌋₊ with hk
    have hk1 : (k : ℝ) * δ ≤ W n ω + C := by
      have := Nat.floor_le hnn
      rwa [le_div_iff₀ hδ0] at this
    have hk2 : W n ω + C < ((k : ℝ) + 1) * δ := by
      have := Nat.lt_floor_add_one ((W n ω + C) / δ)
      rwa [div_lt_iff₀ hδ0] at this
    have hkN : k ≤ N := Nat.floor_mono (by gcongr; linarith)
    simp only [mem_iUnion, Finset.mem_range, mem_union, hE1, hE2, mem_ofPred_eq, htk]
    refine ⟨k, by omega, ?_⟩
    push_cast
    rcases lt_abs.1 hω with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ μ.real {ω | C < |W n ω|} +
        ∑ k ∈ Finset.range (N + 1), (μ.real (E1 n k) + μ.real (E2 n k)) := by
        refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
        exact (measureReal_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ measureReal_union_le _ _)
    _ ≤ η / 2 + η / 2 := add_le_add hn1 hn2
    _ = η := add_halves η

/-- GAPS 102.7: the first-order Bahadur representation. -/
theorem tendstoInProbabilityConst_bahadur_remainder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInProbabilityConst μ (fun n ω ↦ Real.sqrt n *
      (sampleQuantile X n ω p - q - (p - empiricalCDF X n ω q) / f)) 0 := by
  obtain ⟨hp0, hp1⟩ := hp
  set V : ℕ → Ω → ℝ := fun n ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q) with hV
  set W : ℕ → Ω → ℝ := fun n ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f with hW
  set G : ℕ → Ω → ℝ → ℝ := fun n ω s ↦ Real.sqrt n *
    (empiricalCDF X n ω (q + s / Real.sqrt n) - empiricalCDF X n ω q) with hG
  have hWm : ∀ n, Measurable (W n) := fun n ↦
    ((measurable_const.sub (measurable_empiricalCDF X hiid.1 n q)).const_mul _).div_const _
  have hWb : IsBoundedInProbability μ W :=
    isBoundedInProbability_of_tendstoInDistribution μ W hWm _
      (tendstoInDistribution_sqrt_mul_sub_empiricalCDF μ P X hiid p q f hq hf)
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ t s, (V n ω ≤ t → t < s → f * W n ω ≤ G n ω s) ∧
      (s < t → t ≤ V n ω → G n ω s < f * W n ω) := by
    intro n hn ω t s
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    obtain ⟨hlt, hgt⟩ := le_empiricalCDF_of_sampleQuantile_lt X n hn ω hp0 hp1.le
    have hfW : f * W n ω = Real.sqrt n * (p - empiricalCDF X n ω q) := by
      simp only [hW]; field_simp
    rw [hfW]
    constructor
    · intro hVt hts
      have : sampleQuantile X n ω p < q + s / Real.sqrt n := by
        have h1 : sampleQuantile X n ω p - q ≤ t / Real.sqrt n := by
          rw [le_div_iff₀ hsp, mul_comm]; exact hVt
        have h2 : t / Real.sqrt n < s / Real.sqrt n := div_lt_div_of_pos_right hts hsp
        linarith
      have := hlt _ this
      simp only [hG]
      gcongr
    · intro hst htV
      have : q + s / Real.sqrt n < sampleQuantile X n ω p := by
        have h1 : t / Real.sqrt n ≤ sampleQuantile X n ω p - q := by
          rw [div_le_iff₀ hsp, mul_comm]; exact htV
        have h2 : s / Real.sqrt n < t / Real.sqrt n := div_lt_div_of_pos_right hst hsp
        linarith
      have := hgt _ this
      simp only [hG]
      gcongr
  have hGlim : ∀ s, TendstoInProbabilityConst μ (fun n ω ↦ G n ω s) (f * s) := fun s ↦
    tendstoInProbabilityConst_sqrt_mul_empiricalCDF_sub μ P X hiid q f s hd
  have hmain := tendstoInProbabilityConst_sub_of_crossing μ V W hWb (fun t ε hε ↦ ?_)
    (fun t ε hε ↦ ?_)
  · convert hmain using 3 with n ω
    simp only [hV, hW]
    ring
  · have hc : 0 < f * ε / 4 := by positivity
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
      (hGlim (t + ε / 2) _ hc)
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measureReal_mono fun ω hω ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    have := (key n hn ω t (t + ε / 2)).1 h1 (by linarith)
    have hfw : f * (t + ε) ≤ f * W n ω := mul_le_mul_of_nonneg_left h2 hf.le
    simp only [mem_ofPred_eq, Real.dist_eq]
    rw [lt_abs]
    left
    nlinarith
  · have hc : 0 < f * ε / 4 := by positivity
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
      (hGlim (t + ε / 2) _ hc)
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measureReal_mono fun ω hω ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    have := (key n hn ω (t + ε) (t + ε / 2)).2 (by linarith) h1
    have hfw : f * W n ω ≤ f * t := mul_le_mul_of_nonneg_left h2 hf.le
    simp only [mem_ofPred_eq, Real.dist_eq]
    rw [lt_abs]
    right
    nlinarith

/-- GAPS 102.6: asymptotic normality of a sample quantile. -/
theorem tendstoInDistribution_sampleQuantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q))
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  have hWm : ∀ n : ℕ, Measurable fun ω ↦ Real.sqrt n * (p - empiricalCDF X n ω q) / f :=
    fun n ↦ ((measurable_const.sub (measurable_empiricalCDF X hiid.1 n q)).const_mul _).div_const _
  have hVm : ∀ n : ℕ, Measurable fun ω ↦ Real.sqrt n * (sampleQuantile X n ω p - q) := fun n ↦
    ((measurable_sampleQuantile X hiid.1 n hp.1 hp.2.le).sub_const _).const_mul _
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub μ _ _ hWm hVm _
    (tendstoInDistribution_sqrt_mul_sub_empiricalCDF μ P X hiid p q f hq hf) ?_
  convert tendstoInProbabilityConst_bahadur_remainder μ P X hiid p q f hp hq hf hd using 3 with n ω
  ring

/-- Square integrability of a parameter family with a square-integrable Lipschitz envelope, at
parameters within the Lipschitz radius. -/
theorem memLp_two_of_lipschitz_envelope {E : Type*} [MeasurableSpace E] (P : Measure E)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) :
    MemLp (fun x ↦ psi a x - psi b x) 2 P ∧ MemLp (psi a) 2 P ∧
      ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ (∫ x, M x ^ 2 ∂P) * (a - b) ^ 2 := by
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  have h0 : |theta₀ - theta₀| < r := by simpa using hr
  have hd : ∀ a b, |a - theta₀| < r → |b - theta₀| < r →
      MemLp (fun x ↦ psi a x - psi b x) 2 P := fun a b ha hb ↦ by
    refine (hM.const_mul |a - b|).of_le ((hmeas a).sub (hmeas b)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    have := hlip x a b ha hb
    have := le_abs_self (M x)
    nlinarith [abs_nonneg (a - b)]
  refine ⟨hd a b ha hb, ?_, ?_⟩
  · have := (hd a theta₀ ha h0).add hpsi
    convert this using 1
    ext x; simp
  · have hab := hd a b ha hb
    calc ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ ∫ x, M x ^ 2 * (a - b) ^ 2 ∂P := by
          refine integral_mono hab.integrable_sq (hM.integrable_sq.mul_const _) fun x ↦ ?_
          have h1 := hlip x a b ha hb
          have h2 : 0 ≤ |psi a x - psi b x| := abs_nonneg _
          have : (psi a x - psi b x) ^ 2 ≤ (M x * |a - b|) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ h2 h1 2
          simpa [mul_pow, sq_abs] using this
      _ = _ := integral_mul_const _ _

/-- Chebyshev's inequality for the increments of the centred partial-sum process of a parameter
family with a square-integrable Lipschitz envelope. -/
theorem measureReal_le_abs_centredSum_sub_le {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (n : ℕ) (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |(∑ i ∈ Finset.range n, psi a (X i ω) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (X i ω) - n * ∫ x, psi b x ∂P)|} ≤
      n * (∫ x, M x ^ 2 ∂P) * (a - b) ^ 2 / c ^ 2 := by
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hd, ha2, hK⟩ := memLp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    a b ha hb
  have hb2 := (memLp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    b a hb ha).2.1
  have hcheb := measureReal_le_abs_sum_sub_le_of_iid μ P X hiid _ ((hmeas a).sub (hmeas b))
    hd n hc
  have hint : ∫ x, (psi a x - psi b x) ∂P = ∫ x, psi a x ∂P - ∫ x, psi b x ∂P :=
    integral_sub (ha2.integrable one_le_two) (hb2.integrable one_le_two)
  have hset : {ω | c ≤ |(∑ i ∈ Finset.range n, psi a (X i ω) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (X i ω) - n * ∫ x, psi b x ∂P)|} =
      {ω | c ≤ |∑ i ∈ Finset.range n, (psi a (X i ω) - psi b (X i ω)) -
        n * ∫ x, (psi a x - psi b x) ∂P|} := by
    ext ω
    simp only [mem_ofPred_eq, hint, Finset.sum_sub_distrib]
    ring_nf
  rw [hset]
  refine hcheb.trans ?_
  simp only [Pi.sub_apply]
  rw [mul_assoc]
  gcongr

/-- Deterministic Lipschitz bound for the increments of the centred partial-sum process. -/
theorem abs_centredSum_sub_le {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P]
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (n : ℕ) (y : ℕ → E) (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) :
    |(∑ i ∈ Finset.range n, psi a (y i) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (y i) - n * ∫ x, psi b x ∂P)| ≤
      |a - b| * (∑ i ∈ Finset.range n, M (y i) + n * ∫ x, M x ∂P) := by
  have ha2 := (memLp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    a b ha hb).2.1
  have hb2 := (memLp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    b a hb ha).2.1
  have hMi : Integrable M P := hM.integrable one_le_two
  have hI : |∫ x, psi a x ∂P - ∫ x, psi b x ∂P| ≤ |a - b| * ∫ x, M x ∂P := by
    rw [← integral_sub (ha2.integrable one_le_two) (hb2.integrable one_le_two),
      ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      ((ha2.integrable one_le_two).sub (hb2.integrable one_le_two)).abs
      (hMi.const_mul _) fun x ↦ ?_)
    have := hlip x a b ha hb
    simp only
    linarith [mul_comm (M x) |a - b|]
  have hS : |∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)| ≤
      |a - b| * ∑ i ∈ Finset.range n, M (y i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    linarith [hlip (y i) a b ha hb, mul_comm (M (y i)) |a - b|]
  calc _ = |(∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)) -
        n * (∫ x, psi a x ∂P - ∫ x, psi b x ∂P)| := by ring_nf
    _ ≤ |∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)| +
        |(n : ℝ) * (∫ x, psi a x ∂P - ∫ x, psi b x ∂P)| := abs_sub _ _
    _ ≤ |a - b| * ∑ i ∈ Finset.range n, M (y i) + n * (|a - b| * ∫ x, M x ∂P) := by
        rw [abs_mul, Nat.abs_cast]
        gcongr
    _ = _ := by ring

/-- The left endpoint of the dyadic cell of level `j`, of width `δ / 2 ^ j`, containing `t` in the
grid anchored at `θ₀`. -/
def dyadicGridPoint (θ₀ δ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  θ₀ + ⌊(t - θ₀) * 2 ^ j / δ⌋ * (δ / 2 ^ j)

/-- The dyadic cell index of a point within `δ` of the anchor lies in `[-2 ^ j, 2 ^ j)`. -/
theorem dyadicGridPoint_index_mem {θ₀ δ t : ℝ} (hδ : 0 < δ) (ht : |t - θ₀| < δ) (j : ℕ) :
    ⌊(t - θ₀) * 2 ^ j / δ⌋ ∈ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j) := by
  rw [abs_lt] at ht
  have h1 : -1 < (t - θ₀) / δ := by rw [lt_div_iff₀ hδ]; linarith
  have h2 : (t - θ₀) / δ < 1 := by rw [div_lt_one hδ]; linarith
  have hx : (t - θ₀) * 2 ^ j / δ = (t - θ₀) / δ * 2 ^ j := by ring
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [Finset.mem_Ico, Int.le_floor, Int.floor_lt, hx]
  push_cast
  constructor <;> nlinarith

/-- A dyadic grid point lies within `δ` of the anchor, as does the midpoint of its cell. -/
theorem abs_dyadic_sub_le {θ₀ δ : ℝ} (hδ : 0 < δ) {j : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j)) :
    |θ₀ + k * (δ / 2 ^ j) - θ₀| ≤ δ ∧ |θ₀ + k * (δ / 2 ^ j) + δ / 2 ^ j / 2 - θ₀| ≤ δ := by
  rw [Finset.mem_Ico] at hk
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : -(2 : ℝ) ^ j ≤ k := by exact_mod_cast hk.1
  have h2 : (k : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast (Int.add_one_le_iff.2 hk.2)
  have hh : 0 < δ / 2 ^ j := div_pos hδ hp
  have e : (2 : ℝ) ^ j * (δ / 2 ^ j) = δ := by field_simp
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

/-- A point is within one cell width of its dyadic grid point. -/
theorem abs_sub_dyadicGridPoint_le {θ₀ δ : ℝ} (hδ : 0 < δ) (j : ℕ) (t : ℝ) :
    |t - dyadicGridPoint θ₀ δ j t| ≤ δ / 2 ^ j := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hh : 0 < δ / 2 ^ j := div_pos hδ hp
  set x := (t - θ₀) * 2 ^ j / δ
  have hx : t - θ₀ = x * (δ / 2 ^ j) := by simp only [x]; field_simp
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold dyadicGridPoint
  rw [abs_le]
  constructor <;> nlinarith

/-- Consecutive dyadic levels: the finer grid point is the coarser one or the midpoint of its
cell. -/
theorem dyadicGridPoint_succ (θ₀ δ : ℝ) (j : ℕ) (t : ℝ) :
    dyadicGridPoint θ₀ δ (j + 1) t = dyadicGridPoint θ₀ δ j t ∨
      dyadicGridPoint θ₀ δ (j + 1) t = dyadicGridPoint θ₀ δ j t + δ / 2 ^ j / 2 := by
  set x := (t - θ₀) * 2 ^ j / δ with hxdef
  have hx2 : (t - θ₀) * 2 ^ (j + 1) / δ = 2 * x := by rw [hxdef, pow_succ]; ring
  have hw : δ / 2 ^ (j + 1) = δ / 2 ^ j / 2 := by rw [pow_succ, div_div]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hk1 : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hk2 : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by rw [Int.floor_lt]; push_cast; linarith
  unfold dyadicGridPoint
  rw [hx2, hw, ← hxdef]
  rcases (by omega : ⌊2 * x⌋ = 2 * ⌊x⌋ ∨ ⌊2 * x⌋ = 2 * ⌊x⌋ + 1) with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring

/-- The level-zero dyadic grid point of a point within `δ` of the anchor is `θ₀ - δ` or `θ₀`. -/
theorem dyadicGridPoint_zero {θ₀ δ t : ℝ} (hδ : 0 < δ) (ht : |t - θ₀| < δ) :
    dyadicGridPoint θ₀ δ 0 t = θ₀ - δ ∨ dyadicGridPoint θ₀ δ 0 t = θ₀ := by
  have hk := dyadicGridPoint_index_mem hδ ht 0
  simp only [pow_zero, mul_one, Finset.mem_Ico] at hk
  unfold dyadicGridPoint
  simp only [pow_zero, mul_one, div_one]
  rcases (by omega : ⌊(t - θ₀) / δ⌋ = -1 ∨ ⌊(t - θ₀) / δ⌋ = 0) with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; simp

/-- Dyadic chaining bound: if the increments of a real process indexed by `[θ₀ - δ, θ₀ + δ]`
satisfy the Chebyshev bound `P(c ≤ |S a - S b|) ≤ L (a - b)² / c²`, then for any random
parameter `t` the process at the dyadic grid point of `t` of any level stays within `c` of its value
at `θ₀`, except on an event of probability at most `300 L δ² / c²` or where `|t - θ₀| ≥ δ`. -/
theorem measureReal_dyadic_chain_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : ℝ → Ω → ℝ) (θ₀ δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hS : ∀ a b, |a - θ₀| ≤ δ → |b - θ₀| ≤ δ → ∀ c, 0 < c →
      μ.real {ω | c ≤ |S a ω - S b ω|} ≤ L * (a - b) ^ 2 / c ^ 2)
    (t : Ω → ℝ) (J : ℕ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | |t ω - θ₀| < δ ∧ c ≤ |S (dyadicGridPoint θ₀ δ J (t ω)) ω - S θ₀ ω|} ≤
      300 * L * δ ^ 2 / c ^ 2 := by
  set thr : ℕ → ℝ := fun j ↦ c * (3 / 4) ^ j / 8 with hthr
  have hthr0 : ∀ j, 0 < thr j := fun j ↦ by simp only [hthr]; positivity
  set I : ℕ → Finset ℤ := fun j ↦ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j) with hI
  set B : ℕ → ℤ → Set Ω := fun j k ↦ {ω | thr j ≤
    |S (θ₀ + k * (δ / 2 ^ j) + δ / 2 ^ j / 2) ω - S (θ₀ + k * (δ / 2 ^ j)) ω|} with hB
  set A0 : Set Ω := {ω | c / 2 ≤ |S (θ₀ - δ) ω - S θ₀ ω|} with hA0
  have hgeo1 : ∑ j ∈ Finset.range J, thr j ≤ c / 2 := by
    have hg := geom_sum_eq (x := (3 / 4 : ℝ)) (by norm_num) J
    have hp : 0 ≤ (3 / 4 : ℝ) ^ J := by positivity
    have : ∑ j ∈ Finset.range J, thr j = c / 8 * ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_; simp only [hthr]; ring
    rw [this, hg]
    have : ((3 / 4 : ℝ) ^ J - 1) / (3 / 4 - 1) ≤ 4 := by
      rw [div_le_iff_of_neg (by norm_num)]; linarith
    nlinarith
  have hsub : {ω | |t ω - θ₀| < δ ∧ c ≤ |S (dyadicGridPoint θ₀ δ J (t ω)) ω - S θ₀ ω|} ⊆
      A0 ∪ ⋃ j ∈ Finset.range J, ⋃ k ∈ I j, B j k := by
    rintro ω ⟨h1, h2⟩
    by_contra hn
    simp only [mem_union, mem_iUnion, not_or, not_exists, hA0, hB, mem_ofPred_eq, not_le,
      Finset.mem_range] at hn
    obtain ⟨hA, hBn⟩ := hn
    set π : ℕ → ℝ := fun j ↦ dyadicGridPoint θ₀ δ j (t ω) with hπ
    have h0 : |S (π 0) ω - S θ₀ ω| < c / 2 := by
      rcases dyadicGridPoint_zero hδ h1 with h | h
      · simpa [hπ, h] using hA
      · simp only [hπ, h, sub_self, abs_zero]; positivity
    have hstep : ∀ j < J, |S (π (j + 1)) ω - S (π j) ω| < thr j := fun j hj ↦ by
      rcases dyadicGridPoint_succ θ₀ δ j (t ω) with h | h
      · simp only [hπ, h, sub_self, abs_zero]; exact hthr0 j
      · have := hBn j hj _ (dyadicGridPoint_index_mem hδ h1 j)
        simp only [hπ, h]
        exact this
    have htel : S (π J) ω - S θ₀ ω = (S (π 0) ω - S θ₀ ω) +
        ∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω) := by
      rw [Finset.sum_range_sub (fun j ↦ S (π j) ω)]; ring
    have hsum : |∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω)| ≤
        ∑ j ∈ Finset.range J, thr j :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj ↦
        (hstep j (Finset.mem_range.1 hj)).le)
    have := abs_add_le (S (π 0) ω - S θ₀ ω)
      (∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω))
    rw [← htel] at this
    simp only [hπ] at this h2 h0
    linarith
  have hcardI : ∀ j, ((I j).card : ℝ) = 2 * 2 ^ j := fun j ↦ by
    simp only [hI, Int.card_Ico]
    have : ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) := by push_cast; ring
    rw [this, show ((2 ^ j : ℕ) : ℤ) - -((2 ^ j : ℕ) : ℤ) = ((2 * 2 ^ j : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  have hBj : ∀ j, ∑ k ∈ I j, μ.real (B j k) ≤ 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
    intro j
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hw : (0 : ℝ) < (3 / 4) ^ j := by positivity
    have hrel : (8 / 9 : ℝ) ^ j = (2 ^ j * ((3 / 4) ^ j) ^ 2)⁻¹ := by
      rw [← pow_mul, show j * 2 = 2 * j by ring, pow_mul, ← mul_pow, ← inv_pow]
      norm_num
    calc ∑ k ∈ I j, μ.real (B j k)
        ≤ ∑ _k ∈ I j, L * (δ / 2 ^ j / 2) ^ 2 / thr j ^ 2 := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          obtain ⟨ha, hb⟩ := abs_dyadic_sub_le (θ₀ := θ₀) hδ hk
          have := hS _ _ hb ha (thr j) (hthr0 j)
          simp only [hB]
          refine this.trans (le_of_eq ?_)
          ring
      _ = 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardI, hrel]
          simp only [hthr]
          field_simp
          ring
  have hgeo2 : ∑ j ∈ Finset.range J, (8 / 9 : ℝ) ^ j ≤ 9 := by
    rw [geom_sum_eq (by norm_num)]
    have hp : 0 ≤ (8 / 9 : ℝ) ^ J := by positivity
    rw [div_le_iff_of_neg (by norm_num)]; linarith
  have hK : 0 ≤ 32 * L * δ ^ 2 / c ^ 2 := by positivity
  calc _ ≤ μ.real (A0 ∪ ⋃ j ∈ Finset.range J, ⋃ k ∈ I j, B j k) := measureReal_mono hsub
    _ ≤ μ.real A0 + ∑ j ∈ Finset.range J, ∑ k ∈ I j, μ.real (B j k) := by
        refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        exact measureReal_biUnion_finset_le _ _
    _ ≤ L * (θ₀ - δ - θ₀) ^ 2 / (c / 2) ^ 2 +
        ∑ j ∈ Finset.range J, 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
        gcongr with j
        · exact hS _ _ (by simp [abs_of_pos hδ]) (by simp [hδ.le]) _ (half_pos hc)
        · exact hBj j
    _ ≤ 4 * L * δ ^ 2 / c ^ 2 + 32 * L * δ ^ 2 / c ^ 2 * 9 := by
        have e : L * (θ₀ - δ - θ₀) ^ 2 / (c / 2) ^ 2 = 4 * L * δ ^ 2 / c ^ 2 := by
          field_simp; ring
        rw [e, ← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeo2 hK)
    _ ≤ 300 * L * δ ^ 2 / c ^ 2 := by
        have : 0 ≤ L * δ ^ 2 / c ^ 2 := by positivity
        have e1 : 4 * L * δ ^ 2 / c ^ 2 = 4 * (L * δ ^ 2 / c ^ 2) := by ring
        have e2 : 32 * L * δ ^ 2 / c ^ 2 * 9 = 288 * (L * δ ^ 2 / c ^ 2) := by ring
        have e3 : 300 * L * δ ^ 2 / c ^ 2 = 300 * (L * δ ^ 2 / c ^ 2) := by ring
        rw [e1, e2, e3]; linarith

/-- Stochastic equicontinuity of the empirical process of a scalar parameter family with a
square-integrable Lipschitz envelope: evaluated at a consistent random parameter `Tₙ`, the
normalised centred partial-sum increment `n^{-1/2} ∑ᵢ (ψ_{Tₙ} - ψ_{θ₀})(Xᵢ) - √n (P ψ_{Tₙ} - P ψ_{θ₀})`
tends to `0` in probability. The proof is a dyadic chaining argument with Chebyshev's inequality
at each level. -/
theorem tendstoInProbabilityConst_centredSum_sub_of_lipschitz {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hcons : TendstoInProbabilityConst μ T theta₀) :
    TendstoInProbabilityConst μ (fun n ω ↦ (Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P))) 0 := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hiid : IsIndependentIdenticallyDistributed μ X P := ⟨hXm, hind, hlaw⟩
  set S : ℕ → ℝ → Ω → ℝ := fun n θ ω ↦
    ∑ i ∈ Finset.range n, psi θ (X i ω) - n * ∫ x, psi θ x ∂P with hSdef
  set K : ℝ := ∫ x, M x ^ 2 ∂P with hK
  have hK0 : 0 ≤ K := integral_nonneg fun x ↦ sq_nonneg _
  have hMnn : ∀ x, 0 ≤ M x := fun x ↦ by
    have h := hlip x theta₀ (theta₀ + r / 2) (by simpa using hr)
      (by rw [add_sub_cancel_left, abs_of_pos (half_pos hr)]; linarith)
    have hp : 0 < |theta₀ - (theta₀ + r / 2)| := by
      rw [abs_pos]; linarith
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hp
    linarith [abs_nonneg (psi theta₀ x - psi (theta₀ + r / 2) x)]
  set M' : E → ℝ := hM.aestronglyMeasurable.mk M with hM'def
  have hM'm : Measurable M' := hM.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMM' : M =ᵐ[P] M' := hM.aestronglyMeasurable.ae_eq_mk
  have hMi : Integrable M P := hM.integrable one_le_two
  have hM'i : Integrable M' P := hMi.congr hMM'
  have hMae : ∀ᵐ w ∂μ, ∀ i, M (X i w) = M' (X i w) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ x ∂(μ.map (X i)), M x = M' x := by rw [hlaw i]; exact hMM'
    exact ae_of_ae_map (hXm i).aemeasurable this
  set G : Set Ω := {w | ∀ i, M (X i w) = M' (X i w)} with hG
  have hGc : μ.real Gᶜ = 0 := by
    rw [measureReal_def, hG, compl_ofPred, ae_iff.mp hMae, ENNReal.toReal_zero]
  set s : E → ℝ := fun x ↦ M' x + ∫ y, M y ∂P with hs
  have hsm : Measurable s := hM'm.add measurable_const
  set V : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, s (X i w) with hV
  have hVb : IsBoundedInProbability μ V :=
    isBoundedInProbability_of_tendstoInProbabilityConst μ V _
      (tendstoInProbabilityConst_sampleMean_of_iid μ P X hiid s hsm
        (hM'i.add (integrable_const _)))
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  have htδ : Tendsto (fun δ : ℝ ↦ 1200 * K * δ ^ 2 / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun δ : ℝ ↦ 1200 * K * δ ^ 2 / ε ^ 2) := by fun_prop
    have h := this.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hδη, hδ0, hδr⟩ :=
    ((htδ.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3))).and
      (Ioo_mem_nhdsGT hr)).exists
  set u : ℕ → ℝ := fun n ↦ δ * Real.sqrt n / 2 ^ n with hu
  have hulim : Tendsto u atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul δ
    rw [mul_zero] at h1
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    simp only [hu, pow_one]
    rw [mul_div_assoc]
    gcongr
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_one] at this
      nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  have hR := tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability μ V (fun n _ ↦ u n) hVb
    (tendstoInProbabilityConst_const_of_tendsto μ u hulim)
  filter_upwards [eventually_ge_atTop 1,
    (hcons (δ / 2) (half_pos hδ0)).eventually (eventually_le_nhds (by positivity : 0 < η / 3)),
    (hR (ε / 4) (by positivity)).eventually (eventually_le_nhds (by positivity : 0 < η / 3))]
    with n hn1 hn2 hn3
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : 0 < ε * Real.sqrt n / 2 := by positivity
  have hchain := measureReal_dyadic_chain_le μ (S n) theta₀ δ (n * K) hδ0 (by positivity)
    (fun a b ha hb c hc ↦ measureReal_le_abs_centredSum_sub_le μ P X hiid psi hm theta₀ r hr M hM
      hpsi hlip n a b (by linarith) (by linarith) hc) (T n) n hc
  have hcb : 300 * (n * K) * δ ^ 2 / (ε * Real.sqrt n / 2) ^ 2 = 1200 * K * δ ^ 2 / ε ^ 2 := by
    rw [div_pow, mul_pow, hsq]
    field_simp
    ring
  rw [hcb] at hchain
  have hsub : {ω | ε < dist ((Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P))) 0} ⊆
      (({ω | δ / 2 < dist (T n ω) theta₀} ∪
        {ω | |T n ω - theta₀| < δ ∧
          ε * Real.sqrt n / 2 ≤ |S n (dyadicGridPoint theta₀ δ n (T n ω)) ω - S n theta₀ ω|}) ∪
        {ω | ε / 4 < dist (V n ω * u n) 0}) ∪ Gᶜ := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, not_or, not_lt, not_and, not_le,
      not_not] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    rw [Real.dist_eq] at h1
    have hT : |T n ω - theta₀| < δ := by linarith
    have h2 := h2 hT
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul, abs_inv,
      abs_of_pos hsqn] at hω
    rw [Real.dist_eq, sub_zero] at h3
    set πT := dyadicGridPoint theta₀ δ n (T n ω)
    have hπ : |πT - theta₀| ≤ δ :=
      (abs_dyadic_sub_le (θ₀ := theta₀) hδ0 (dyadicGridPoint_index_mem hδ0 hT n)).1
    have hres := abs_centredSum_sub_le P psi hm theta₀ r hr M hM hpsi hlip n (fun i ↦ X i ω)
      (T n ω) πT (by linarith) (by linarith)
    have hQ : 0 ≤ ∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P :=
      add_nonneg (Finset.sum_nonneg fun i _ ↦ hMnn _)
        (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg hMnn))
    have hd := abs_sub_dyadicGridPoint_le (θ₀ := theta₀) hδ0 n (T n ω)
    have hVu : δ / 2 ^ n * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P) =
        Real.sqrt n * (V n ω * u n) := by
      have h4' : ∀ i, M (X i ω) = M' (X i ω) := h4
      rw [Finset.sum_congr rfl fun i _ ↦ h4' i]
      simp only [hV, hu, hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      rw [hsq]; ring
    have hres' : |S n (T n ω) ω - S n πT ω| ≤ Real.sqrt n * (ε / 4) := by
      refine hres.trans ?_
      calc |T n ω - πT| * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P)
          ≤ δ / 2 ^ n * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P) := by gcongr
        _ = Real.sqrt n * (V n ω * u n) := hVu
        _ ≤ Real.sqrt n * |V n ω * u n| := by gcongr; exact le_abs_self _
        _ ≤ Real.sqrt n * (ε / 4) := by gcongr
    have htri := abs_sub_le (S n (T n ω) ω) (S n πT ω) (S n theta₀ ω)
    have hω' : ε * Real.sqrt n < |S n (T n ω) ω - S n theta₀ ω| := by
      rw [inv_mul_eq_div, lt_div_iff₀ hsqn] at hω
      exact hω
    nlinarith
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ η / 3 + 1200 * K * δ ^ 2 / ε ^ 2 + η / 3 + μ.real Gᶜ := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ hn3)
        exact (measureReal_union_le _ _).trans (add_le_add hn2 hchain)
    _ ≤ η := by rw [hGc]; linarith

/-- GAPS 102.4, the scalar Z-estimator theorem under a square-integrable Lipschitz envelope. -/
theorem z_estimator_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (psi : ℝ → E → ℝ)
    (hm : Measurable (Function.uncurry psi)) (theta₀ D : ℝ) (hD : D ≠ 0)
    (hpsi : MemLp (psi theta₀) 2 P) (h0 : (∫ x, psi theta₀ x ∂P) = 0)
    (hd : HasDerivAt (fun theta ↦ ∫ x, psi theta x ∂P) D theta₀)
    (r : ℝ) (hr : 0 < r) (M : E → ℝ) (hM : MemLp M 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : TendstoInProbabilityConst mu T theta₀)
    (hroot : TendstoInProbabilityConst mu (fun n w ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, psi (T n w) (X i w)) 0) :
    TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) 0 ∧
      TendstoInDistribution mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal (variance P (psi theta₀) / D ^ 2))) := by
  have hXm := hiid.1
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  set F : ℝ → ℝ := fun θ ↦ ∫ x, psi θ x ∂P with hF
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)
    with hZ
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ (hmeas theta₀).comp (hXm i)).const_mul _
  have hZlim : TendstoInDistribution mu Z
      (gaussianReal 0 (Real.toNNReal (∫ x, psi theta₀ x ^ 2 ∂P))) :=
    tendstoInDistribution_inv_sqrt_mul_sum_of_iid mu P X hiid _ (hmeas theta₀) hpsi h0
  have hZb : IsBoundedInProbability mu Z :=
    isBoundedInProbability_of_tendstoInDistribution mu Z hZm _ hZlim
  have hsn : ∀ n : ℕ, (Real.sqrt n)⁻¹ * n = Real.sqrt n := fun n ↦ by
    rw [inv_mul_eq_div, Real.div_sqrt]
  have hSE := tendstoInProbabilityConst_centredSum_sub_of_lipschitz mu P X hiid psi hm theta₀ r hr
    M hM hpsi hlip T hcons
  -- `√n F(Tₙ) + Zₙ → 0`
  have hE1 : TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * F (T n w) + Z n w) 0 := by
    have := tendstoInProbabilityConst_add_zero mu _ _ hroot
      (tendstoInProbabilityConst_const_mul_zero mu _ (-1) hSE)
    convert this using 3 with n w
    simp only [hZ, hF]
    rw [h0]
    first
      | linear_combination (∫ x, psi (T n w) x ∂P) * hsn n
      | linear_combination (-(∫ x, psi (T n w) x ∂P)) * hsn n
  set ρ : ℝ → ℝ := Function.update (fun t ↦ slope F theta₀ t - D) theta₀ 0 with hρ
  have hρc : ContinuousAt ρ theta₀ := by
    rw [hρ, continuousAt_update_same]
    have := (hasDerivAt_iff_tendsto_slope.1 hd).sub_const D
    simpa using this
  have hρ0 : ρ theta₀ = 0 := by simp [hρ]
  have hρT : TendstoInProbabilityConst mu (fun n w ↦ ρ (T n w)) 0 := by
    have := tendstoInProbabilityConst_comp_of_continuousAt mu T theta₀ ρ hρc hcons
    rwa [hρ0] at this
  set W : ℕ → Ω → ℝ := fun n w ↦ Real.sqrt n * (T n w - theta₀) with hW
  have hF0 : F theta₀ = 0 := h0
  have hid : ∀ (n : ℕ) (w : Ω), Real.sqrt n * F (T n w) = D * W n w + W n w * ρ (T n w) := fun n w ↦ by
    by_cases h : T n w = theta₀
    · simp [hW, h, hF0]
    · have : ρ (T n w) = (T n w - theta₀)⁻¹ * (F (T n w) - F theta₀) - D := by
        rw [hρ, Function.update_of_ne h]
        simp [slope_def_field, div_eq_inv_mul]
      rw [this, hF0, sub_zero]
      have hne : T n w - theta₀ ≠ 0 := sub_ne_zero.2 h
      simp only [hW]
      field_simp
      ring
  set Ev : ℕ → Ω → ℝ := fun n w ↦ D * W n w + W n w * ρ (T n w) + Z n w with hEv
  have hE : TendstoInProbabilityConst mu Ev 0 := by
    convert hE1 using 3 with n w
    simp only [hEv]
    rw [hid]
  have hWb : IsBoundedInProbability mu W := by
    intro ε hε
    obtain ⟨C₁, hC₁, hZev⟩ := hZb (ε / 3) (by positivity)
    have hDp : 0 < |D| := abs_pos.2 hD
    refine ⟨2 * (1 + C₁) / |D|, by positivity, ?_⟩
    filter_upwards [hZev, (hE 1 one_pos).eventually (eventually_le_nhds (by positivity :
      0 < ε / 3)), (hρT (|D| / 4) (by positivity)).eventually (eventually_le_nhds (by positivity :
      0 < ε / 3))] with n h1 h2 h3
    have hsub : {w | 2 * (1 + C₁) / |D| < |W n w|} ⊆
        ({w | C₁ < |Z n w|} ∪ {w | 1 < dist (Ev n w) 0}) ∪
          {w | |D| / 4 < dist (ρ (T n w)) 0} := by
      intro w hw
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt, Real.dist_eq, sub_zero] at hcon hw
      obtain ⟨⟨c1, c2⟩, c3⟩ := hcon
      have hfac : W n w * (D + ρ (T n w)) = Ev n w - Z n w := by simp only [hEv]; ring
      have hlow : 3 * |D| / 4 ≤ |D + ρ (T n w)| := by
        have := abs_sub_abs_le_abs_sub D (-ρ (T n w))
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
      have hup : |W n w| * |D + ρ (T n w)| ≤ 1 + C₁ := by
        rw [← abs_mul, hfac]
        exact (abs_sub _ _).trans (by linarith)
      have hW0 := abs_nonneg (W n w)
      rw [div_lt_iff₀ hDp] at hw
      nlinarith
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ h3)
        exact (measureReal_union_le _ _).trans (add_le_add h1 h2)
      _ = ε := by ring
  have hWρ := tendstoInProbabilityConst_mul_zero_of_isBoundedInProbability mu W _ hWb hρT
  have hDWZ : TendstoInProbabilityConst mu (fun n w ↦ D * W n w + Z n w) 0 := by
    have := tendstoInProbabilityConst_add_zero mu _ _ hE
      (tendstoInProbabilityConst_const_mul_zero mu _ (-1) hWρ)
    convert this using 3 with n w
    simp only [hEv]; ring
  have hrem : TendstoInProbabilityConst mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) 0 := by
    have := tendstoInProbabilityConst_const_mul_zero mu _ D⁻¹ hDWZ
    convert this using 3 with n w
    simp only [hW, hZ]
    rw [mul_inv]
    field_simp
  refine ⟨hrem, ?_⟩
  have hvar : variance P (psi theta₀) = ∫ x, psi theta₀ x ^ 2 ∂P := by
    simp only [variance, h0, sub_zero]
  have hX' : TendstoInDistribution mu (fun n w ↦ -D⁻¹ * Z n w)
      (gaussianReal 0 (Real.toNNReal (variance P (psi theta₀) / D ^ 2))) := by
    have := tendstoInDistribution_comp_of_continuous mu Z hZm _ (fun x ↦ -D⁻¹ * x)
      (continuous_const.mul continuous_id) hZlim
    convert this using 1
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    have hI0 : 0 ≤ ∫ x, psi theta₀ x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    simp only [NNReal.coe_mul, NNReal.coe_mk, hvar, Real.coe_toNNReal _ hI0,
      Real.coe_toNNReal _ (div_nonneg hI0 (sq_nonneg D))]
    field_simp
  refine tendstoInDistribution_of_tendstoInProbabilityConst_sub mu _ _
    (fun n ↦ (hZm n).const_mul _) (fun n ↦ ((hT n).sub_const _).const_mul _) _ hX' ?_
  convert hrem using 3 with n w
  simp only [hZ]
  rw [mul_inv]
  ring


end CKSD
