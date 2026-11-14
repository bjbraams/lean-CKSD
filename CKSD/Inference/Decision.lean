module

public import CKSD.Inference.Model
public import CKSD.Inference.FiniteDecision
import CKSD.Inference.BlackwellFinite
import CKSD.Inference.BlackwellPosterior
import CKSD.Inference.BlackwellApproximation
import CKSD.Inference.BlackwellCoupling
import CKSD.Inference.BlackwellJoint
import CKSD.Inference.KernelDisintegration
public import CKSD.Inference.ConvexGames
public import CKSD.Inference.Sufficiency
public import CKSD.Inference.MeanParametrization
public import CKSD.Inference.ExponentialFamilyMLE
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv


/-!
# Decision theory: minimax, complete classes, admissibility, and comparison of experiments

## Main definitions

* `CKSD.IsMoreInformative P Q`: Blackwell's order on experiments through finite decision
  problems with bounded loss.

## Main results

* `CKSD.exists_statistical_game_saddle_point`: finite statistical games have a saddle point
  (GAPS 101.32).
* `CKSD.exists_admissible_bayes_risk_le_of_closed_convex`: the complete class theorem for a
  finite parameter set (GAPS 101.37), by separation of the risk set from a lower orthant.
* `CKSD.exists_equivariant_rule_risk_eq_average`: averaging over a finite group (GAPS 101.39).
* `CKSD.exists_analytic_inverse_exponential_family_mean`: the mean parametrization of a regular
  minimal exponential family (GAPS 101.42).
* `CKSD.is_admissible_risk_of_blyth`: Blyth's method for admissibility (GAPS 101.58).
* `CKSD.is_more_informative_iff_is_garbling`: Blackwell's comparison theorem (GAPS 101.62).

## References

* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, Chapter 5.
* D. Blackwell, Equivalent comparisons of experiments, *Ann. Math. Statist.* 24 (1953).
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.32: the minimax theorem for statistical games with finitely many parameters and
actions. There are a randomized rule `δ` and a prior `π` such that `δ` is a Bayes rule for `π`
and the risk of `δ` at every parameter is at most its Bayes risk; hence `δ` is minimax, `π` is
least favorable, and the minimax and maximin values agree. -/
theorem exists_statistical_game_saddle_point [Fintype Θ] [Nonempty Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (L : Θ → A → ℝ) :
    ∃ δ : RandomizedDecisionRule X A, ∃ π : ProbabilityMeasure Θ,
      IsBayesRule (risk P L) (π : Measure Θ) δ ∧
      ∀ θ, risk P L δ θ ≤ ∫ θ', risk P L δ θ' ∂(π : Measure Θ) := by
  classical
  let μ : Measure X := ∑ θ, P θ
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let := hμ
  have hdom (θ : Θ) : P θ ≤ μ := by
    intro s
    change P θ s ≤ (∑ θ', P θ') s
    simp only [FunLike.coe_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun θ' : Θ ↦ P θ' s)
      (fun _ _ ↦ (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ θ)
  obtain ⟨hcompact, hconv⟩ := is_compact_convex_range_risk μ P hdom L
  let a₀ : A := Classical.choice inferInstance
  let δ₀ : RandomizedDecisionRule X A := ⟨Kernel.const X (Measure.dirac a₀), inferInstance⟩
  obtain ⟨y, ⟨δ, hδ⟩, w, hwn, hws, hwmin, hwmax⟩ :=
    exists_compact_convex_game_saddle_point hcompact hconv ⟨risk P L δ₀, δ₀, rfl⟩
  let ν : Measure Θ := ∑ θ, ENNReal.ofReal (w θ) • Measure.dirac θ
  have hν : IsProbabilityMeasure ν := ⟨by
    change (∑ θ, ENNReal.ofReal (w θ) • Measure.dirac θ) univ = 1
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun θ _ ↦ hwn θ), hws, ENNReal.ofReal_one]⟩
  let := hν
  have hint (r : Θ → ℝ) : Integrable r ν :=
    ⟨(measurable_of_countable r).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
  have hint_eq (r : Θ → ℝ) : (∫ θ, r θ ∂ν) = ∑ θ, w θ * r θ := by
    change (∫ θ, r θ ∂(∑ θ, ENNReal.ofReal (w θ) • Measure.dirac θ)) = _
    rw [integral_finsetSum_measure fun θ _ ↦
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal (hwn _), integral_dirac,
      smul_eq_mul]
  refine ⟨δ, ⟨ν, hν⟩, ⟨hint _, fun δ' _ ↦ ?_⟩, fun θ ↦ ?_⟩
  · change (∫ θ, risk P L δ θ ∂ν) ≤ ∫ θ, risk P L δ' θ ∂ν
    rw [hint_eq, hint_eq, hδ]
    exact hwmin _ ⟨δ', rfl⟩
  · change risk P L δ θ ≤ ∫ θ', risk P L δ θ' ∂ν
    rw [hint_eq, hδ]
    exact hwmax θ

/-- GAPS 101.37: the complete class theorem for a finite parameter set, in risk-set form. Let `C`
be a closed convex set of risk vectors in `ℝ^d`, `d > 0`, bounded below. Every `x ∈ C` is
dominated by an admissible point `y ∈ C` (no point of `C` is at most `y` coordinatewise and
strictly smaller somewhere) that is Bayes for some prior `w` on the `d` parameter values. -/
theorem exists_admissible_bayes_risk_le_of_closed_convex {d : ℕ} (hd : 0 < d) (C : Set (Fin d → ℝ))
    (hc : Convex ℝ C) (hclosed : IsClosed C) (hb : ∃ b : Fin d → ℝ, ∀ x ∈ C, ∀ i, b i ≤ x i) :
    ∀ x ∈ C, ∃ y ∈ C, (∀ i, y i ≤ x i) ∧
      (¬ ∃ z ∈ C, (∀ i, z i ≤ y i) ∧ ∃ i, z i < y i) ∧
      ∃ w : Fin d → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        ∀ z ∈ C, (∑ i, w i * y i) ≤ ∑ i, w i * z i := by
  intro x hx
  obtain ⟨b, hb⟩ := hb
  -- a minimizer of the coordinate sum below `x`
  have hDc : IsCompact (C ∩ Iic x) :=
    (isCompact_Icc (a := b) (b := x)).of_isClosed_subset (hclosed.inter isClosed_Iic)
      fun z hz ↦ ⟨fun i ↦ hb z hz.1 i, hz.2⟩
  obtain ⟨y, ⟨hyC, hyx⟩, hymin⟩ := hDc.exists_isMinOn ⟨x, hx, mem_Iic.2 le_rfl⟩
    (f := fun z : Fin d → ℝ ↦ ∑ i, z i) (by fun_prop)
  have hadm : ¬ ∃ z ∈ C, (∀ i, z i ≤ y i) ∧ ∃ i, z i < y i := by
    rintro ⟨z, hzC, hzy, j, hj⟩
    have hle := hymin ⟨hzC, mem_Iic.2 (le_trans (fun i ↦ hzy i) hyx)⟩
    have hlt : ∑ i, z i < ∑ i, y i :=
      Finset.sum_lt_sum (fun i _ ↦ hzy i) ⟨j, Finset.mem_univ _, hj⟩
    exact absurd hle (not_le.2 hlt)
  refine ⟨y, hyC, fun i ↦ hyx i, hadm, ?_⟩
  -- separation of the open lower orthant at `y` from `C + ℝ^d_{≥0}`
  let O : Set (Fin d → ℝ) := univ.pi fun i ↦ Iio (y i)
  let E : Set (Fin d → ℝ) := {v | ∃ c ∈ C, ∀ i, c i ≤ v i}
  have hOo : IsOpen O := isOpen_set_pi finite_univ fun i _ ↦ isOpen_Iio
  have hOc : Convex ℝ O := convex_pi fun i _ ↦ convex_Iio (y i)
  have hEc : Convex ℝ E := by
    rintro v₁ ⟨c₁, hc₁, h₁⟩ v₂ ⟨c₂, hc₂, h₂⟩ a b' ha hb' hab
    refine ⟨a • c₁ + b' • c₂, hc hc₁ hc₂ ha hb' hab, fun i ↦ ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (h₁ i) ha, mul_le_mul_of_nonneg_left (h₂ i) hb']
  have hdisj : Disjoint O E := by
    rw [Set.disjoint_left]
    rintro v hvO ⟨c, hcC, hcv⟩
    have hvO' : ∀ i, v i < y i := fun i ↦ hvO i (mem_univ i)
    exact hadm ⟨c, hcC, fun i ↦ (hcv i).trans (hvO' i).le,
      ⟨⟨0, hd⟩, (hcv _).trans_lt (hvO' _)⟩⟩
  obtain ⟨f, u, hfO, hfE⟩ := geometric_hahn_banach_open hOc hOo hEc hdisj
  let e : Fin d → Fin d → ℝ := fun i j ↦ if i = j then 1 else 0
  let w' : Fin d → ℝ := fun i ↦ f (e i)
  have hexp (z : Fin d → ℝ) : f z = ∑ i, w' i * z i := by
    rw [show f z = (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) z from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul, w', e, mul_comm]
    rfl
  have hyE : y ∈ E := ⟨y, hyC, fun _ ↦ le_rfl⟩
  have hw' : ∀ i, 0 ≤ w' i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    let t := (|f y - u| + 1) / (-w' i)
    have ht : 0 < t := div_pos (by positivity) (by linarith)
    have hmem : y + t • e i ∈ E := ⟨y, hyC, fun j ↦ by
      by_cases h : i = j <;> simp [e, h, ht.le]⟩
    have h1 := hfE _ hmem
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 : t * w' i = -(|f y - u| + 1) := by
      simp only [t]
      rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hneg.ne, mul_one]
    have h3 := le_abs_self (f y - u)
    change u ≤ f y + t * w' i at h1
    linarith
  have hfy : f y ≤ u := by
    by_contra hlt
    rw [not_le] at hlt
    let one : Fin d → ℝ := fun _ ↦ 1
    let t := (f y - u) / (|f one| + 1)
    have ht : 0 < t := div_pos (by linarith) (by positivity)
    have hmem : y - t • one ∈ O := fun i _ ↦ by simp [one, ht]
    have h1 := hfO _ hmem
    rw [map_sub, map_smul, smul_eq_mul] at h1
    have h2 : t * (|f one| + 1) = f y - u := by simp only [t]; field_simp
    have h3 : t * f one ≤ t * |f one| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.le
    nlinarith
  have hsum : 0 < ∑ i, w' i := by
    rcases (Finset.sum_nonneg fun i _ ↦ hw' i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hzero : ∀ i, w' i = 0 := fun i ↦
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hw' j).1 h.symm i (Finset.mem_univ _)
      have hf0 (z : Fin d → ℝ) : f z = 0 := by simp [hexp, hzero]
      have h1 := hfE y hyE
      have h2 := hfO (y - fun _ ↦ 1) fun i _ ↦ by simp
      rw [hf0] at h1 h2
      linarith
  refine ⟨fun i ↦ w' i / ∑ j, w' j, fun i ↦ div_nonneg (hw' i) hsum.le, ?_, fun z hz ↦ ?_⟩
  · rw [← Finset.sum_div, div_self hsum.ne']
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_le_div_iff_of_pos_right hsum, ← hexp, ← hexp]
    exact hfy.trans (hfE z ⟨z, hz, fun _ ↦ le_rfl⟩)

/-- GAPS 101.39: the averaging (Hunt–Stein) construction for a finite group with its uniform Haar
measure. In an invariant decision problem with bounded measurable invariant loss, every
randomized rule `δ` has an equivariant rule `bar` whose risk at `θ` is the average of the risks
of `δ` over the orbit of `θ`. The minimax consequences are not included. -/
theorem exists_equivariant_rule_risk_eq_average {G A : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Θ] [MulAction G A] [MeasurableSpace A]
    (hX : ∀ g : G, Measurable (fun x : X ↦ g • x))
    (hA : ∀ g : G, Measurable (fun a : A ↦ g • a))
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (hmodel : ∀ (g : G) θ, (P θ).map (fun x ↦ g • x) = P (g • θ))
    (L : Θ → A → ℝ) (hm : ∀ θ, Measurable (L θ))
    (C : ℝ) (hb : ∀ θ a, |L θ a| ≤ C)
    (hloss : ∀ (g : G) θ a, L (g • θ) (g • a) = L θ a) (delta : RandomizedDecisionRule X A) :
    ∃ bar : RandomizedDecisionRule X A,
      (∀ (g : G) x, bar.val (g • x) = (bar.val x).map (fun a ↦ g • a)) ∧
      ∀ θ, risk P L bar θ = (∑ g : G, risk P L delta (g • θ)) / Fintype.card G := by
  obtain ⟨δ, hδ⟩ := delta
  have hcard : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let c : ℝ≥0∞ := (Fintype.card G : ℝ≥0∞)⁻¹
  let μ : X → Measure A := fun x ↦ c • ∑ g : G, (δ (g⁻¹ • x)).map (fun a ↦ g • a)
  have hμ (x : X) (s : Set A) (hs : MeasurableSet s) :
      μ x s = c * ∑ g : G, δ (g⁻¹ • x) ((fun a ↦ g • a) ⁻¹' s) := by
    simp only [μ, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (hA _) hs]
  have := hδ
  have hμm : Measurable μ := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [hμ _ s hs]
    exact (Finset.measurable_sum _ fun g _ ↦
      (Kernel.measurable_coe δ ((hA g) hs)).comp (hX g⁻¹)).const_mul c
  let K : Kernel X A := ⟨μ, hμm⟩
  have hK : IsMarkovKernel K := ⟨fun x ↦ ⟨by
    change μ x univ = 1
    rw [hμ x univ MeasurableSet.univ]
    simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, c]
    exact ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _)⟩⟩
  refine ⟨⟨K, hK⟩, fun g x ↦ ?_, fun θ ↦ ?_⟩
  · ext s hs
    change μ (g • x) s = (μ x).map (fun a ↦ g • a) s
    rw [Measure.map_apply (hA g) hs, hμ _ _ hs, hμ _ _ ((hA g) hs)]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h ↦ ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_smul]
    congr 1
    ext a
    simp
  · let F : G → X → ℝ := fun g y ↦ ∫ a, L (g⁻¹ • θ) a ∂δ y
    have hFm (g : G) : Measurable (F g) :=
      ((hm _).stronglyMeasurable.integral_kernel (κ := δ)).measurable
    have hFb (g : G) (y : X) : |F g y| ≤ C := by
      have := norm_integral_le_of_norm_le_const (μ := δ y) (C := C)
        (ae_of_all _ fun a ↦ by rw [Real.norm_eq_abs]; exact hb (g⁻¹ • θ) a)
      simpa [Real.norm_eq_abs, F] using this
    have hinner (x : X) : (∫ a, L θ a ∂μ x) = c.toReal * ∑ g : G, F g (g⁻¹ • x) := by
      simp only [μ]
      rw [integral_smul_measure, integral_finsetSum_measure (fun g _ ↦
        integrable_of_measurable_of_abs_le _ (hm θ) (hb θ)), smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [integral_map (hA g).aemeasurable (hm θ).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
      simp only
      rw [← hloss g (g⁻¹ • θ) a, smul_inv_smul]
    have := hP θ
    have hterm (g : G) : (∫ x, F g (g⁻¹ • x) ∂P θ) = risk P L ⟨δ, hδ⟩ (g⁻¹ • θ) := by
      rw [← integral_map (f := F g) (hX g⁻¹).aemeasurable (hFm g).aestronglyMeasurable,
        hmodel]
      rfl
    change (∫ x, ∫ a, L θ a ∂μ x ∂P θ) = _
    simp_rw [hinner]
    rw [integral_const_mul, integral_finsetSum (f := fun g x ↦ F g (g⁻¹ • x)) Finset.univ fun g _ ↦
      integrable_of_measurable_of_abs_le _ ((hFm g).comp (hX g⁻¹)) fun x ↦ hFb g _]
    simp_rw [hterm]
    rw [Fintype.sum_equiv (Equiv.inv G) (fun g ↦ risk P L ⟨δ, hδ⟩ (g⁻¹ • θ))
      (fun g ↦ risk P L ⟨δ, hδ⟩ (g • θ)) (fun g ↦ rfl)]
    simp only [c, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [div_eq_inv_mul]

/-- GAPS 101.42: the mean parametrization of a regular minimal natural exponential family. For a
nonzero σ-finite base measure `ν` on a finite-dimensional real inner product space `E` whose
natural parameter space `N` is open and nonempty, the mean map `η ↦ ∫ x d(P η)(x)` is real
analytic on `N` and is a bijection of `N` onto the interior `K` of the convex hull of the support
of `ν`, with real analytic inverse on `K`. -/
theorem exists_analytic_inverse_exponential_family_mean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [SigmaFinite ν] (hne : ν ≠ 0)
    (hminimal : IsMinimalExponentialFamily ν id) (hN : IsOpen (naturalParameterSpace ν id))
    (hNne : (naturalParameterSpace ν id).Nonempty) :
    ∃ g : E → E,
      AnalyticOnNhd ℝ (fun η ↦ ∫ x, x ∂exponentialFamilyMeasure ν id η)
          (naturalParameterSpace ν id) ∧
        AnalyticOnNhd ℝ g (interior (convexHull ℝ ν.support)) ∧
        (∀ η ∈ naturalParameterSpace ν id,
          (∫ x, x ∂exponentialFamilyMeasure ν id η) ∈ interior (convexHull ℝ ν.support) ∧
            g (∫ x, x ∂exponentialFamilyMeasure ν id η) = η) ∧
        ∀ m ∈ interior (convexHull ℝ ν.support),
          g m ∈ naturalParameterSpace ν id ∧ (∫ x, x ∂exponentialFamilyMeasure ν id (g m)) = m := by
  set N := naturalParameterSpace ν id
  set M : E → E := fun η ↦ ∫ x, x ∂exponentialFamilyMeasure ν id η with hMdef
  set K := interior (convexHull ℝ ν.support)
  have hMan : AnalyticOnNhd ℝ M N := analytic_on_nhd_mean_exponential_family_measure ν hne hN
  have hinj : InjOn M N := inj_on_mean_exponential_family_measure ν hne hminimal hN
  -- Every interior point of the convex hull is a mean (existence of the MLE).
  have hsurj : ∀ m ∈ K, ∃ η ∈ N, M η = m := by
    intro m hm
    obtain ⟨η, hη, hmax⟩ :=
      (exists_is_max_on_log_likelihood_iff_mem_interior_convex_hull_support ν hne hminimal hNne m).2 hm
    have h2 := (has_f_deriv_at_log_partition_and_eq_of_is_max_on ν hne hminimal hN hη hmax).1.unique
      (has_f_deriv_at_log_partition ν hne (hN.interior_eq.symm ▸ hη))
    refine ⟨η, hη, ?_⟩
    have := congrArg (fun f : E →L[ℝ] ℝ ↦ f (m - M η)) h2
    simp only [innerSL_apply_apply] at this
    have h3 : inner ℝ (m - M η) (m - M η) = 0 := by rw [inner_sub_left, this, sub_self]
    exact (sub_eq_zero.1 (inner_self_eq_zero.1 h3)).symm
  set g : E → E := fun m ↦ if h : ∃ η ∈ N, M η = m then h.choose else 0
  have hg : ∀ m ∈ K, g m ∈ N ∧ M (g m) = m := fun m hm ↦ by
    have h := hsurj m hm
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec
  have hmemK : ∀ η ∈ N, M η ∈ K := fun η hη ↦
    mean_exponential_family_measure_mem_interior_convex_hull_support ν hne hminimal hN hη
  have hgM : ∀ η ∈ N, g (M η) = η := fun η hη ↦
    hinj (hg _ (hmemK η hη)).1 hη (hg _ (hmemK η hη)).2
  refine ⟨g, hMan, fun m hm ↦ ?_, fun η hη ↦ ⟨hmemK η hη, hgM η hη⟩, hg⟩
  -- Analytic inverse function theorem at `η = g m`.
  obtain ⟨hη, hMη⟩ := hg m hm
  set η := g m
  obtain ⟨i, hfd, hstrict⟩ :=
    exists_has_strict_f_deriv_at_mean_exponential_family_measure ν hne hminimal hN hη
  set R := hstrict.toOpenPartialHomeomorph M
  have h0 : η ∈ R.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hRcoe : ⇑R = M := hstrict.toOpenPartialHomeomorph_coe
  have hRη : R η = m := by rw [hRcoe]; exact hMη
  have han : AnalyticAt ℝ R.symm (R η) := R.analyticAt_symm' h0
    (by rw [hRcoe]; exact hMan η hη) (by rw [hRcoe]; exact hfd)
  rw [hRη] at han
  refine han.congr ?_
  have hc : ContinuousAt R.symm m := hRη ▸ R.continuousAt_symm (R.map_source h0)
  have hsymm : R.symm m = η := by rw [← hRη, R.left_inv h0]
  filter_upwards [hc.preimage_mem_nhds (hsymm.symm ▸ hN.mem_nhds hη),
    R.open_target.mem_nhds (hRη ▸ R.map_source h0), isOpen_interior.mem_nhds hm]
    with m' h1 h2 h3
  have h4 : M (R.symm m') = m' := by rw [← hRcoe]; exact R.right_inv h2
  exact hinj h1 (hg m' h3).1 (h4.trans (hg m' h3).2.symm)

/-- GAPS 101.58: Blyth's method. Let `Θ` be a convex subset of Euclidean space with nonempty
interior and let the rules `δ` in a class `D` have continuous risk functions `R δ`. Suppose there
are finite measures `π n` on `Θ` with Bayes rules `δ n`, giving uniformly positive mass to every
convex subset with nonempty interior for large `n`, such that the Bayes risk excess
`∫ R δ₀ dπ n - ∫ R (δ n) dπ n` of `δ₀` tends to zero. Then `δ₀` is admissible. -/
theorem is_admissible_risk_of_blyth {d : ℕ} {D : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (hinterior : (interior Θ).Nonempty) (R : D → Θ → ℝ)
    (hc : ∀ δ, Continuous (R δ)) (δ₀ : D) (π : ℕ → Measure Θ)
    (hπ : ∀ n, IsFiniteMeasure (π n)) (δ : ℕ → D)
    (hbayes : ∀ n, IsBayesRule R (π n) (δ n))
    (hint : ∀ n a, Integrable (R a) (π n))
    (hmass : ∀ C : Set Θ, Convex ℝ (Subtype.val '' C) →
      (interior (Subtype.val '' C)).Nonempty →
      ∃ K > 0, ∀ᶠ n in atTop, K ≤ (π n).real C)
    (hgap : Tendsto (fun n ↦ (∫ θ, R δ₀ θ ∂π n) - ∫ θ, R (δ n) θ ∂π n) atTop (𝓝 0)) :
    IsAdmissibleRisk R δ₀ := by
  rintro ⟨δ', hle, θ₁, hlt⟩
  set ε := (R δ₀ θ₁ - R δ' θ₁) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  -- a ball around `θ₁` on which the risk gap exceeds `ε`
  have hcont : Continuous (fun θ ↦ R δ₀ θ - R δ' θ) := (hc δ₀).sub (hc δ')
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.1 hcont θ₁ ε hε0
  let C : Set Θ := {θ | dist θ θ₁ < ρ}
  have hCimg : Subtype.val '' C = Metric.ball θ₁.val ρ ∩ Θ := by
    ext z
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨hθ, θ.2⟩
    · rintro ⟨hz, hzΘ⟩
      exact ⟨⟨z, hzΘ⟩, hz, rfl⟩
  have hCconv : Convex ℝ (Subtype.val '' C) := by
    rw [hCimg]; exact (convex_ball _ _).inter hΘ
  have hCint : (interior (Subtype.val '' C)).Nonempty := by
    rw [hCimg, interior_inter, Metric.isOpen_ball.interior_eq]
    have hcl : θ₁.val ∈ closure (interior Θ) := by
      rw [hΘ.closure_interior_eq_closure_of_nonempty_interior hinterior]
      exact subset_closure θ₁.2
    obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
    exact ⟨z, by rw [Metric.mem_ball, dist_comm]; exact hdist, hz⟩
  obtain ⟨K, hK, hKev⟩ := hmass C hCconv hCint
  have hCm : MeasurableSet C :=
    measurableSet_lt (measurable_id.dist measurable_const) measurable_const
  have hlower : ∀ᶠ n in atTop,
      ε * K ≤ (∫ θ, R δ₀ θ ∂π n) - ∫ θ, R (δ n) θ ∂π n := by
    filter_upwards [hKev] with n hn
    have := hπ n
    have hb := (hbayes n).2 δ' (hint n δ')
    have hdiff : Integrable (fun θ ↦ R δ₀ θ - R δ' θ) (π n) := (hint n δ₀).sub (hint n δ')
    have hnn : 0 ≤ᵐ[π n] fun θ ↦ R δ₀ θ - R δ' θ :=
      ae_of_all _ fun θ ↦ sub_nonneg.2 (hle θ)
    have h1 := setIntegral_le_integral (s := C) hdiff hnn
    have h2 := setIntegral_ge_of_const_le_real (μ := π n) (c := ε) hCm (measure_ne_top _ _)
      (fun θ hθ ↦ by
        have := hball θ hθ
        rw [Real.dist_eq] at this
        have h3 := neg_abs_le (R δ₀ θ - R δ' θ - (R δ₀ θ₁ - R δ' θ₁))
        linarith) hdiff.integrableOn
    rw [integral_sub (hint n δ₀) (hint n δ')] at h1
    nlinarith [mul_le_mul_of_nonneg_left hn hε0.le]
  have hlim : ε * K ≤ 0 := ge_of_tendsto hgap hlower
  nlinarith [mul_pos hε0 hK]

/-- The experiment `P` is more informative than `Q` (Blackwell): for every finite decision problem
with bounded loss, every randomized rule based on `Q` is matched, at every parameter, by a rule
based on `P` with risk at most its risk. -/
def IsMoreInformative {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y) : Prop :=
  ∀ n : ℕ, ∀ L : Θ → Fin n → ℝ, (∃ C, ∀ θ a, |L θ a| ≤ C) →
    ∀ δ : RandomizedDecisionRule Y (Fin n), ∃ δ' : RandomizedDecisionRule X (Fin n),
      ∀ θ, risk P L δ' θ ≤ risk Q L δ θ

/-- Garbling cannot improve any finite-action bounded-loss decision problem. -/
theorem is_more_informative_of_is_garbling
    {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y)
    [∀ θ, IsProbabilityMeasure (P θ)] [∀ θ, IsProbabilityMeasure (Q θ)]
    (h : IsGarbling P Q) : IsMoreInformative P Q := by
  obtain ⟨K, hK, hPQ⟩ := h
  have := hK
  intro n L _ δ
  have := δ.property
  let δP : RandomizedDecisionRule X (Fin n) := ⟨δ.val ∘ₖ K, inferInstance⟩
  refine ⟨δP, fun θ ↦ le_of_eq ?_⟩
  have hcomp : δP.val ∘ₘ P θ = δ.val ∘ₘ Q θ := by
    -- Unpack the composed decision kernel before associating measure composition.
    change (δ.val ∘ₖ K) ∘ₘ P θ = δ.val ∘ₘ Q θ
    rw [← Measure.comp_assoc, ← hPQ θ]
  rw [risk_eq_sum_action_law P L δP θ, risk_eq_sum_action_law Q L δ θ, hcomp]

/-- GAPS 101.62: Blackwell's comparison theorem for a finite parameter set. A family of
probability laws `P` is more informative than `Q`, whose sample space is standard Borel, if and
only if `Q` is a garbling of `P`. Both families are dominated, by `∑ θ, P θ` and `∑ θ, Q θ`,
since the parameter set is finite. -/
theorem is_more_informative_iff_is_garbling {Θ X Y : Type*} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y)
    [∀ θ, IsProbabilityMeasure (P θ)] [∀ θ, IsProbabilityMeasure (Q θ)] :
    IsMoreInformative P Q ↔ IsGarbling P Q := by
  constructor
  · intro hmore
    classical
    rcases isEmpty_or_nonempty Θ with hΘ | hΘ
    · exact ⟨Kernel.const X (Measure.dirac (Classical.choice (inferInstance : Nonempty Y))),
        inferInstance, fun θ ↦ (hΘ.false θ).elim⟩
    have : Nonempty Θ := hΘ
    let C := finiteLikelihoodCube Θ
    have : Nonempty C := ⟨⟨0, le_rfl, fun _ ↦ zero_le_one⟩⟩
    let μ := finiteDominatingMeasure P
    have : IsFiniteMeasure μ := inferInstance
    let u : X → C := finiteLikelihoodMap P
    let v : Y → C := finiteLikelihoodMap Q
    have hu : Measurable u := measurable_finite_likelihood_map P
    have hv : Measurable v := measurable_finite_likelihood_map Q
    let w : Θ → BoundedContinuousFunction C ℝ := fun θ ↦
      BoundedContinuousFunction.mkOfCompact
        (⟨fun z ↦ z.val θ, (continuous_apply θ).comp continuous_subtype_val⟩ : C(C, ℝ))
    have hw (θ : Θ) (z : C) : 0 ≤ w θ z := z.property.1 θ
    have hP (θ : Θ) : P θ = μ.withDensity (fun x ↦ ENNReal.ofReal (w θ (u x))) :=
      (has_density_finite_likelihood_map P θ).2.2
    have hfinite (n : ℕ) (hn : 0 < n) (q : Y → Fin n) (hq : Measurable q) :
        ∃ δ : RandomizedDecisionRule X (Fin n), ∀ θ, δ.val ∘ₘ P θ = (Q θ).map q := by
      let δQ : RandomizedDecisionRule Y (Fin n) := ⟨Kernel.deterministic q hq, inferInstance⟩
      obtain ⟨δ, hδ⟩ := exists_finite_randomization_of_risk_dominance P Q n hn (hmore n) δQ
      refine ⟨δ, fun θ ↦ ?_⟩
      rw [hδ θ]
      exact Measure.deterministic_comp_eq_map hq
    obtain ⟨ρ, hfst, hweighted⟩ :=
      exists_joint_of_finite_randomizations μ P Q u hu v hv w hw hP hfinite
    obtain ⟨K, hK, hKmodel⟩ := exists_markov_kernel_of_map_eq_tilted_joint_laws
      (ρ : Measure (C × C)) (fun θ z ↦ ENNReal.ofReal (w θ z)) (fun θ ↦ by fun_prop)
      u hu P (fun θ ↦ (Q θ).map v)
      (fun θ ↦ by rw [hfst]; exact map_finite_likelihood_eq_with_density P θ)
      (fun θ ↦ (hweighted θ).symm)
    have := hK
    obtain ⟨J, hJ, hJmodel⟩ := is_garbling_of_finite_likelihood_map Q
    have := hJ
    refine ⟨J ∘ₖ K, inferInstance, fun θ ↦ ?_⟩
    calc
      Q θ = J ∘ₘ (Q θ).map v := hJmodel θ
      _ = J ∘ₘ (K ∘ₘ P θ) := by rw [hKmodel θ]
      _ = (J ∘ₖ K) ∘ₘ P θ := Measure.comp_assoc
  · exact is_more_informative_of_is_garbling P Q

end CKSD
