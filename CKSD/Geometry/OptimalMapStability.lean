module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.MeasureTheory.OptimalTransport.Stability
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Convergence
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment
public import TauCeti.MeasureTheory.Function.UniformIntegrable

/-!
# Stability of optimal quadratic transport maps

Optimal maps from a fixed absolutely continuous source converge in mean square when
their target laws converge in quadratic Wasserstein distance. The proof uses
TauCeti's compactness of optimal plans, Brenier uniqueness and the equivalence of
weak convergence of graph plans with convergence in measure. TauCeti's moment-tail
criterion and Mathlib's Vitali theorem upgrade this convergence to mean square.

## Main results

* `CKSD.tendsto_integral_sq_optimal_map_sub`: `L²` stability of optimal maps (GAPS 108.42).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
noncomputable section

/-- Eventually uniformly small quadratic tails, together with finite individual moments,
give uniform integrability; the finite initial segment causes no obstruction. -/
lemma unifIntegrable_of_eventually_small_tails
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {f : ℕ → Ω → E}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0, ∀ᶠ n in atTop,
      eLpNorm ({x | R ≤ ‖f n x‖₊}.indicator (f n)) 2 μ ≤ ε) :
    UnifIntegrable f 2 μ := by
  apply unifIntegrable_of (by norm_num) (by norm_num) (fun n ↦ (hf n).aestronglyMeasurable)
  intro ε hε
  obtain ⟨R, hR⟩ := htail ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hR
  have hh : UniformIntegrable (fun k : Fin N ↦ f k) 2 μ :=
    uniformIntegrable_finite (by norm_num) (by norm_num) fun k ↦ hf k
  obtain ⟨S, hS⟩ := hh.spec (by norm_num) (by norm_num) hε
  refine ⟨max R S, fun n ↦ ?_⟩
  have hmono : ∀ C D : ℝ≥0, C ≤ D →
      eLpNorm ({x | D ≤ ‖f n x‖₊}.indicator (f n)) 2 μ ≤
        eLpNorm ({x | C ≤ ‖f n x‖₊}.indicator (f n)) 2 μ := by
    intro C D hCD
    rw [eLpNorm_indicator_eq_eLpNorm_restrict,
      eLpNorm_indicator_eq_eLpNorm_restrict]
    · exact eLpNorm_mono_measure _ (Measure.restrict_mono_set μ fun x hx ↦ hCD.trans hx)
    all_goals exact (nullMeasurableSet_le aemeasurable_const (hf n).aestronglyMeasurable.nnnorm.aemeasurable)
  by_cases hn : N ≤ n
  · exact (hmono R _ (le_max_left _ _)).trans (hN n hn)
  · exact (hmono S _ (le_max_right _ _)).trans (hS ⟨n, by omega⟩)

/-- Maps whose laws converge in quadratic Wasserstein distance are uniformly integrable
in quadratic mean. The maps may be defined on any probability space. -/
lemma unifIntegrable_of_tendsto_wasserstein_law
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → E}
    (hf : ∀ n, Measurable (f n)) (νs : ℕ → TauCeti.WassersteinSpace 2 E)
    (ν : TauCeti.WassersteinSpace 2 E)
    (hlaw : ∀ n, μ.map (f n) = ((νs n : ProbabilityMeasure E) : Measure E))
    (hconv : Tendsto νs atTop (𝓝 ν)) : UnifIntegrable f 2 μ := by
  have hfm : ∀ n, MemLp (f n) 2 μ := fun n ↦
    TauCeti.memLp_of_hasFiniteMoment_map (hf n).aemeasurable
      (hlaw n ▸ (νs n).hasFiniteMoment)
  apply unifIntegrable_of_eventually_small_tails hfm
  intro ε hε
  obtain ⟨R, hR⟩ := TauCeti.WassersteinSpace.exists_setLIntegral_edist_rpow_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hconv (0 : E)
    (show 0 < ε ^ (2 : ℝ) from ENNReal.rpow_pos_of_nonneg hε (by norm_num))
  refine ⟨R, hR.mono fun n hn ↦ ?_⟩
  have hmeas : MeasurableSet {y : E | R ≤ ‖y‖₊} := measurableSet_le measurable_const (by fun_prop)
  have hnorm : eLpNorm ({x | R ≤ ‖f n x‖₊}.indicator (f n)) 2 μ =
      (∫⁻ y in {y : E | R ≤ nndist (0 : E) y}, edist (0 : E) y ^ (2 : ℝ≥0∞).toReal
        ∂((νs n : ProbabilityMeasure E) : Measure E)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [← hlaw n]
    calc _ = eLpNorm ({y : E | R ≤ ‖y‖₊}.indicator id) 2 (μ.map (f n)) := by
          symm
          exact eLpNorm_map_measure
            (measurable_id.indicator hmeas).aestronglyMeasurable (hf n).aemeasurable
      _ = _ := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hmeas.nullMeasurableSet,
          eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
            aestronglyMeasurable_id]
        simp [nndist_zero_left, edist_eq_enorm_sub]
  rw [hnorm]
  apply (ENNReal.rpow_le_rpow hn (by positivity)).trans_eq
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Convergence in measure and quadratic Wasserstein convergence of the laws imply
convergence in mean square. -/
lemma tendsto_integral_norm_sq_sub_of_tendstoInMeasure_of_tendsto_wasserstein_law
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → E} {g : Ω → E}
    (hf : ∀ n, Measurable (f n)) (hg : MemLp g 2 μ)
    (νs : ℕ → TauCeti.WassersteinSpace 2 E) (ν : TauCeti.WassersteinSpace 2 E)
    (hlaw : ∀ n, μ.map (f n) = ((νs n : ProbabilityMeasure E) : Measure E))
    (hconv : Tendsto νs atTop (𝓝 ν)) (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hUI := unifIntegrable_of_tendsto_wasserstein_law hf νs ν hlaw hconv
  have hLp := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    (by norm_num) (fun n ↦ (hf n).aestronglyMeasurable) hg hUI hfg
  have h := ((ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hLp).pow 2
  simp only [ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  apply h.congr fun n ↦ ?_
  have hfn : MemLp (f n - g) 2 μ :=
    (TauCeti.memLp_of_hasFiniteMoment_map (hf n).aemeasurable
      (hlaw n ▸ (νs n).hasFiniteMoment)).sub hg
  change (eLpNorm (f n - g) 2 μ).toReal ^ 2 = ∫ x, ‖(f n - g) x‖ ^ 2 ∂μ
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
    (hfn.norm.aestronglyMeasurable.pow 2)]
  rw [← ENNReal.toReal_pow]
  congr 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hfn.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Optimal graph plans from a fixed absolutely continuous Euclidean source converge weakly
when their target laws converge in quadratic Wasserstein distance. -/
lemma tendsto_graphPlan_of_isOptimalCoupling {d : ℕ}
    (μ ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (νs : ℕ → TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Ts : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hac : ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ≪ volume)
    (hopt : TauCeti.IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ))
      (TauCeti.graphPlan T ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))
      ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))
    (hoptn : ∀ n, TauCeti.IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ))
      (TauCeti.graphPlan (Ts n) ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))
      ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ((νs n : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))
    (hconv : Tendsto νs atTop (𝓝 ν)) :
    Tendsto (fun n ↦ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))).map fun x ↦ (x, Ts n x)) atTop
      (𝓝 ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))).map fun x ↦ (x, T x))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : E × E → ℝ≥0∞ := fun z ↦ edist z.1 z.2 ^ (2 : ℝ)
  have hc : Continuous c := ENNReal.continuous_rpow_const.comp (continuous_fst.edist continuous_snd)
  have hv : Tendsto (fun n ↦ TauCeti.transportCost c
      ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ((νs n : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))
      atTop (𝓝 (TauCeti.transportCost c ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))
        ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))))) := by
    simp only [c, ← ENNReal.toReal_ofNat 2,
      ← TauCeti.wassersteinEDist_rpow_eq_transportCost measurable_edist two_ne_zero
        ENNReal.ofNat_ne_top, ← TauCeti.WassersteinSpace.edist_def]
    exact ENNReal.continuous_rpow_const.continuousAt.tendsto.comp (tendsto_const_nhds.edist hconv)
  have hν : Tendsto (fun n ↦ (νs n : ProbabilityMeasure E)) atTop
      (𝓝 (ν : ProbabilityMeasure E)) :=
    TauCeti.WassersteinSpace.continuous_toProbabilityMeasure.continuousAt.tendsto.comp hconv
  have hfin : TauCeti.transportCost
      (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ≠ ⊤ := by
    have hs := TauCeti.wassersteinEDist_rpow_eq_transportCost measurable_edist
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
      ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d))) ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))
    rw [ENNReal.toReal_ofNat,
      funext TauCeti.edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two,
      TauCeti.transportCost_const_mul two_ne_zero ENNReal.ofNat_ne_top] at hs
    intro htop
    rw [htop, ENNReal.mul_top two_ne_zero] at hs
    have hW : TauCeti.wassersteinEDist 2
        ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) ≠ ⊤ := by
      rw [← TauCeti.WassersteinSpace.edist_def]
      exact edist_ne_top μ ν
    exact ENNReal.rpow_ne_top_of_nonneg zero_le_two hW hs
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨π, ms, hms, hπ, hπopt⟩ :=
    TauCeti.exists_isOptimalCoupling_tendsto_of_polishSpace
      (TauCeti.isCostLiminfStable_const hc.lowerSemicontinuous)
      (hv.comp hns).limsup_eq.le
      tendsto_const_nhds (hν.comp hns)
      (πs := fun n ↦ (μ : ProbabilityMeasure E).map fun x ↦ (x, Ts (ns n) x))
      (Eventually.of_forall fun n ↦ by
        simpa only [TauCeti.toMeasure_map_prodMk_self] using hoptn (ns n))
  have huniq := TauCeti.IsOptimalCoupling.unique hac
    (TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two hπopt)
    (TauCeti.isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two hopt) hfin
  have hπeq : π = (μ : ProbabilityMeasure E).map fun x ↦ (x, T x) := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [TauCeti.toMeasure_map_prodMk_self] using huniq
  refine ⟨ms, ?_⟩
  rw [hπeq] at hπ
  change Tendsto (fun n ↦ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))).map
    fun x ↦ (x, Ts (ns (ms n)) x)) atTop
    (𝓝 ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))).map fun x ↦ (x, T x))) at hπ
  exact hπ

/-- The real squared-displacement identity identifies an optimal quadratic graph coupling
between finite-second-moment probability laws. -/
lemma isOptimalCoupling_graphPlan_of_integral_norm_sq_eq
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : TauCeti.WassersteinSpace 2 E) (T : E → E) (hT : Measurable T)
    (hlaw : (((μ : ProbabilityMeasure E) : Measure E).map T) =
      ((ν : ProbabilityMeasure E) : Measure E))
    (hopt : (∫ x, ‖x - T x‖ ^ 2 ∂((μ : ProbabilityMeasure E) : Measure E)) =
      (TauCeti.wassersteinEDist 2 ((μ : ProbabilityMeasure E) : Measure E)
        ((ν : ProbabilityMeasure E) : Measure E)).toReal ^ 2) :
    TauCeti.IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ))
      (TauCeti.graphPlan T ((μ : ProbabilityMeasure E) : Measure E))
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) := by
  have hT2 : MemLp T 2 ((μ : ProbabilityMeasure E) : Measure E) :=
    TauCeti.memLp_of_hasFiniteMoment_map hT.aemeasurable (hlaw ▸ ν.hasFiniteMoment)
  have hi : Integrable (fun x : E ↦ ‖x - T x‖ ^ 2)
      ((μ : ProbabilityMeasure E) : Measure E) :=
    (μ.hasFiniteMoment.memLp_id.sub hT2).norm.integrable_sq
  refine ⟨TauCeti.isCoupling_graphPlan ⟨hT.aemeasurable, hlaw⟩, ?_⟩
  have hb := TauCeti.wassersteinEDist_rpow_eq_transportCost measurable_edist
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
    ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E)
  norm_num only [ENNReal.toReal_ofNat] at hb
  rw [← hb]
  rw [TauCeti.lintegral_graphPlan hT.aemeasurable (by fun_prop)]
  have hpt : (fun x ↦ edist x (T x) ^ (2 : ℝ)) =
      fun x ↦ ENNReal.ofReal (‖x - T x‖ ^ 2) := by
    ext x
    simp [edist_dist, dist_eq_norm,
      ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hpt, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x ↦ sq_nonneg _), hopt,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal,
    ENNReal.rpow_two]
  rw [← TauCeti.WassersteinSpace.edist_def]
  exact edist_ne_top μ ν

/-- GAPS 108.42: L2 stability of optimal maps with a fixed absolutely continuous source. Let `μ`
be an absolutely continuous law with finite second moment, `T` and `Tₙ` measurable optimal maps
from `μ` to laws `ν` and `νₙ` with finite second moments. If `W₂(νₙ, ν) → 0`, then
`∫ ‖Tₙ - T‖² dμ → 0`. The laws `νₙ = (Tₙ)_# μ` are probability measures automatically. -/
theorem tendsto_integral_sq_optimal_map_sub {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (νn : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (hac : μ ≪ volume) (hμ2 : MemLp id 2 μ) (hν2 : MemLp id 2 ν)
    (hνn2 : ∀ n, MemLp id 2 (νn n))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Tn : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hT : Measurable T) (hTn : ∀ n, Measurable (Tn n))
    (hpush : μ.map T = ν) (hpushn : ∀ n, μ.map (Tn n) = νn n)
    (hopt : (∫ x, ‖x - T x‖ ^ 2 ∂μ) = (TauCeti.wassersteinEDist 2 μ ν).toReal ^ 2)
    (hoptn : ∀ n, (∫ x, ‖x - Tn n x‖ ^ 2 ∂μ) =
      (TauCeti.wassersteinEDist 2 μ (νn n)).toReal ^ 2)
    (hconv : Tendsto (fun n ↦ (TauCeti.wassersteinEDist 2 (νn n) ν).toReal) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖Tn n x - T x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let E := EuclideanSpace ℝ (Fin d)
  have : ∀ n, IsProbabilityMeasure (νn n) :=
    fun n ↦ hpushn n ▸ inferInstance
  let μw : TauCeti.WassersteinSpace 2 E := TauCeti.WassersteinSpace.mk ⟨μ, inferInstance⟩
    (TauCeti.hasFiniteMoment_def.2 ⟨0, by simpa [edist_eq_enorm_sub] using hμ2.enorm⟩)
  let νw : TauCeti.WassersteinSpace 2 E := TauCeti.WassersteinSpace.mk ⟨ν, inferInstance⟩
    (TauCeti.hasFiniteMoment_def.2 ⟨0, by simpa [edist_eq_enorm_sub] using hν2.enorm⟩)
  let νws : ℕ → TauCeti.WassersteinSpace 2 E := fun n ↦
    TauCeti.WassersteinSpace.mk ⟨νn n, inferInstance⟩
      (TauCeti.hasFiniteMoment_def.2 ⟨0, by simpa [edist_eq_enorm_sub] using (hνn2 n).enorm⟩)
  have hs : ∀ n, ((νws n : ProbabilityMeasure E) : Measure E) = νn n := by
    intro n
    exact congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk _ _)
  have hv : ((νw : ProbabilityMeasure E) : Measure E) = ν :=
    congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk _ _)
  have hm : ((μw : ProbabilityMeasure E) : Measure E) = μ :=
    congrArg ProbabilityMeasure.toMeasure (TauCeti.WassersteinSpace.coe_mk _ _)
  have hw : Tendsto νws atTop (𝓝 νw) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [TauCeti.WassersteinSpace.dist_def, hs, hv] using hconv
  have hp : TauCeti.IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ))
      (TauCeti.graphPlan T ((μw : ProbabilityMeasure E) : Measure E))
      ((μw : ProbabilityMeasure E) : Measure E) ((νw : ProbabilityMeasure E) : Measure E) :=
    isOptimalCoupling_graphPlan_of_integral_norm_sq_eq μw νw T hT
      (by simpa only [hm, hv] using hpush) (by simpa only [hm, hv] using hopt)
  have hpn : ∀ n, TauCeti.IsOptimalCoupling (fun z ↦ edist z.1 z.2 ^ (2 : ℝ))
      (TauCeti.graphPlan (Tn n) ((μw : ProbabilityMeasure E) : Measure E))
      ((μw : ProbabilityMeasure E) : Measure E) ((νws n : ProbabilityMeasure E) : Measure E) :=
    fun n ↦ isOptimalCoupling_graphPlan_of_integral_norm_sq_eq μw (νws n) (Tn n) (hTn n)
      (by simpa only [hm, hs] using hpushn n) (by simpa only [hm, hs] using hoptn n)
  have hg := tendsto_graphPlan_of_isOptimalCoupling μw νw νws T Tn
    (by simpa only [hm] using hac) hp hpn hw
  have hmeas : TendstoInMeasure μ Tn atTop T := by
    have h := TauCeti.tendstoInMeasure_of_tendsto_map_prodMk_self
      (fun n ↦ (hTn n).aemeasurable) hT.aemeasurable hg
    simpa only [hm] using h
  have hT2 : MemLp T 2 μ := TauCeti.memLp_of_hasFiniteMoment_map hT.aemeasurable
    (hpush ▸ (hv ▸ νw.hasFiniteMoment))
  exact tendsto_integral_norm_sq_sub_of_tendstoInMeasure_of_tendsto_wasserstein_law
    hTn hT2 νws νw (fun n ↦ (hpushn n).trans (hs n).symm) hw hmeas

end
end CKSD
