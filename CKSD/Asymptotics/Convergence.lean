module

public import CKSD.Asymptotics.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Weak convergence and stochastic algebra

Finite-measure weak convergence, continuous mapping, nonseparable Slutsky perturbations,
boundedness in probability, stochastic algebra, and iid laws of large numbers and central
limit theorems. The probability-law adapters use Mathlib's portmanteau, strong-law and
central-limit APIs. Sources: the convergence framework of Section 102 of `GAPS.md` and
`SYNOPSIS102.md`.
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
  have : ∀ n, IsProbabilityMeasure (μs n) := hμs
  exact TendstoWeakly.of_forall_integral_tendsto
    (fun f ↦ ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht f)

/-- On probability spaces and for almost everywhere measurable random variables, CKSD's law
convergence is Mathlib's convergence to the identity random variable under the limiting law. -/
theorem tendstoInDistribution_iff_mathlib {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E)
    (ν : Measure E) [IsProbabilityMeasure ν] (hX : ∀ n, AEMeasurable (X n) μ) :
    TendstoInDistribution μ X ν ↔
      MeasureTheory.TendstoInDistribution X atTop id (fun _ ↦ μ) ν := by
  constructor
  · intro h
    refine ⟨hX, aemeasurable_id, ?_⟩
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
    intro f
    simpa using h.integral_tendsto f
  · intro h
    apply TendstoWeakly.of_forall_integral_tendsto
    intro f
    simpa using
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto f

/-- Continuous mapping for the CKSD convergence-in-law predicate. -/
theorem tendstoInDistribution_comp_of_continuous {Ω E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (hZ : ∀ n, Measurable (Z n)) (ν : Measure E)
    (φ : E → F) (hφ : Continuous φ) (h : TendstoInDistribution μ Z ν) :
    TendstoInDistribution μ (fun n ω ↦ φ (Z n ω)) (ν.map φ) := by
  have hφm : Measurable φ := hφ.measurable
  have : ∀ n, IsFiniteMeasure (μ.map (Z n)) := h.finite
  have : IsFiniteMeasure ν := h.finite_limit
  refine ⟨fun n ↦ ?_, inferInstance, ?_⟩
  · change IsFiniteMeasure (μ.map (φ ∘ Z n))
    rw [← Measure.map_map hφm (hZ n)]
    infer_instance
  intro f
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

/-- Measurable real statistics `s ∘ X i` of an i.i.d. sequence are pairwise independent. -/
theorem IsIndependentIdenticallyDistributed.pairwise_indepFun_comp {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω} {P : Measure E} {X : ℕ → Ω → E}
    (hiid : IsIndependentIdenticallyDistributed μ X P) {s : E → ℝ} (hs : Measurable s) :
    Pairwise (fun i j ↦ IndepFun (s ∘ X i) (s ∘ X j) μ) :=
  fun _ _ hij ↦ (hiid.2.1.comp (fun _ ↦ s) (fun _ ↦ hs)).indepFun hij

/-- Measurable real statistics `s ∘ X i` of an i.i.d. sequence are identically distributed. -/
theorem IsIndependentIdenticallyDistributed.identDistrib_comp {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω} {P : Measure E} {X : ℕ → Ω → E}
    (hiid : IsIndependentIdenticallyDistributed μ X P) {s : E → ℝ} (hs : Measurable s) (i : ℕ) :
    IdentDistrib (s ∘ X i) (s ∘ X 0) μ μ := by
  obtain ⟨hm, -, hlaw⟩ := hiid
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
  have hindep := hiid.pairwise_indepFun_comp hs
  have hident := hiid.identDistrib_comp hs
  have hm := hiid.1
  have hlaw := hiid.2.2 0
  have hint0 : Integrable (s ∘ X 0) μ := by
    rw [← hlaw] at hint
    exact hint.comp_measurable (hm 0)
  have hslln := strong_law_ae (fun i ↦ s ∘ X i) hint0 hindep hident
  have hmean : μ[s ∘ X 0] = ∫ x, s x ∂P := by
    rw [← hlaw, integral_map (hm 0).aemeasurable hs.aestronglyMeasurable]; rfl
  rw [hmean] at hslln
  refine tendstoInProbabilityConst_iff_tendstoInMeasure.2
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
  have hindep := hiid.pairwise_indepFun_comp hs
  have hident := hiid.identDistrib_comp hs
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
  refine TendstoWeakly.of_forall_integral_tendsto ?_
  intro f
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 ht f
  rw [hmean, hvar] at this
  simpa using this

end CKSD
