module

public import CKSD.Asymptotics.MEstimators
import CKSD.Asymptotics.ConvexRegression.Basic
import CKSD.Asymptotics.LipschitzExpansion
import CKSD.Asymptotics.MultivariateCLT
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import TauCeti.Probability.Distributions.Gaussian.Affine
public import CKSD.Asymptotics.MEstimatorNormality


/-!
# Fixed-design convex regression M-estimators

Asymptotic linearization and normality of fixed-design convex regression M-estimators
(GAPS 102.48), from the general convex-regression limit theorem
`CKSD.tendsto_in_measure_and_tendsto_in_distribution_convex_regression`.

## Main definitions

* `CKSD.regressionMObjective`, `CKSD.fixedDesignGramMatrix`.

## Main results

* `CKSD.regression_m_estimator_asymptotic_linearization_and_normality`: the fixed-design convex
  regression case (GAPS 102.48).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Fixed-design convex regression objective. -/
def regressionMObjective {d : ℕ} (ρ : ℝ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (y : ℕ → ℝ) (n : ℕ) (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ Finset.range n, ρ (y i - inner ℝ (x i) β)

/-- Empirical Gram matrix of the first `n` fixed-design rows. -/
def fixedDesignGramMatrix {d : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin d))
    (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ (∑ k ∈ Finset.range n, x k i * x k j) / n

/-- The truncated second moment `E[ψ² ; |ψ| > K]` of a square-integrable function tends to zero
as `K → ∞` (dominated convergence); in particular it is eventually at most any `η > 0`. -/
private lemma exists_integral_ite_lt_abs_sq_le {P : Measure ℝ} {ψ : ℝ → ℝ} (hψ2 : MemLp ψ 2 P)
    {η : ℝ} (hη : 0 < η) : ∃ K : ℝ, ∫ z, (if K < |ψ z| then ψ z ^ 2 else 0) ∂P ≤ η := by
  have hlim : Tendsto (fun K : ℕ ↦ ∫ z, (if (K : ℝ) < |ψ z| then ψ z ^ 2 else 0) ∂P) atTop
      (𝓝 (∫ _, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ ψ z ^ 2)
      (fun K ↦ (integrable_ite_lt_abs_sq hψ2 K).aestronglyMeasurable) hψ2.integrable_sq
      (fun K ↦ ae_of_all _ fun z ↦ ?_) (ae_of_all _ fun z ↦ ?_)
    · simp only [Real.norm_eq_abs]
      split_ifs <;> simp [sq_nonneg]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|ψ z|⌉₊] with K hK
      have : |ψ z| ≤ K := (Nat.le_ceil _).trans (Nat.cast_le.2 hK)
      simp [not_lt.2 this]
  rw [integral_zero] at hlim
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨K, hK.le⟩

/-- Under the `L²` continuity of the shifted scores, `z ↦ ψ(z - s)` is integrable for all small
`s` and the shifted scores satisfy a uniform second-moment bound. -/
private lemma exists_integrable_shift {P : Measure ℝ} [IsProbabilityMeasure P] {ψ : ℝ → ℝ}
    (hψ : Measurable ψ) (hψ2 : MemLp ψ 2 P)
    (hcont : Tendsto (fun t : ℝ ↦ ∫⁻ z, ENNReal.ofReal ((ψ (z - t) - ψ z) ^ 2) ∂P)
      (𝓝 0) (𝓝 0)) :
    ∃ δ > 0, ∀ s, |s| < δ → Integrable (fun z ↦ ψ (z - s)) P := by
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1
    (ENNReal.tendsto_nhds_zero.1 hcont 1 one_pos)
  refine ⟨δ, hδ, fun s hs ↦ ?_⟩
  have hgm : Measurable fun z ↦ ψ (z - s) - ψ z :=
    (hψ.comp (measurable_id.sub_const s)).sub hψ
  have hg2 : Integrable (fun z ↦ (ψ (z - s) - ψ z) ^ 2) P :=
    ⟨(hgm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ sq_nonneg _)).2
        ((hb (by rwa [Real.dist_eq, sub_zero])).trans_lt ENNReal.one_lt_top)⟩
  have hgL : MemLp (fun z ↦ ψ (z - s) - ψ z) 2 P :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hg2
  exact ((hgL.integrable one_le_two).add (hψ2.integrable one_le_two)).congr
    (ae_of_all _ fun z ↦ by simp)

/-- **Curvature of the expected loss** in GAPS 102.48: if `ρ` is convex with right derivative
`ψ`, `E ψ(Z) = 0`, the shifted scores are `L²`-continuous and `t ↦ E ψ(Z - t)` has derivative
`-γ` at zero, then `E [ρ(Z - t) - ρ(Z) + t ψ(Z)] = γ t² / 2 + o(t²)`. -/
private lemma exists_abs_integral_remainder_sub_le {P : Measure ℝ} [IsProbabilityMeasure P]
    {ρ ψ : ℝ → ℝ} (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hder : ∀ u, HasDerivWithinAt ρ (ψ u) (Ici u) u) (hψ2 : MemLp ψ 2 P)
    (hψ0 : (∫ z, ψ z ∂P) = 0)
    (hcont : Tendsto (fun t : ℝ ↦ ∫⁻ z, ENNReal.ofReal ((ψ (z - t) - ψ z) ^ 2) ∂P)
      (𝓝 0) (𝓝 0))
    {γ : ℝ} (hmean : HasDerivAt (fun t ↦ ∫ z, ψ (z - t) ∂P) (-γ) 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t, |t| < δ →
      |∫ z, (ρ (z - t) - ρ z + t * ψ z) ∂P - γ * t ^ 2 / 2| ≤ η * t ^ 2 := by
  obtain ⟨δ₀, hδ₀, hint⟩ := exists_integrable_shift hψ hψ2 hcont
  have hlo := (hasDerivAt_iff_isLittleO.1 hmean).def hη
  obtain ⟨δ₁, hδ₁, hG⟩ := Metric.eventually_nhds_iff.1 hlo
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun t ht ↦ ?_⟩
  have hs : ∀ s, |s| ≤ |t| → |s| < min δ₀ δ₁ := fun s hs ↦ hs.trans_lt ht
  refine abs_integral_remainder_sub_le P hconv (fun u ↦ (hder u).mono Ioi_subset_Ici_self) hψ
    (hψ2.integrable one_le_two) hψ0 hη.le
    (fun s hst ↦ hint s ((hs s hst).trans_le (min_le_left _ _))) fun s hst ↦ ?_
  have h := hG (show dist s 0 < δ₁ by
    rw [Real.dist_eq, sub_zero]; exact (hs s hst).trans_le (min_le_right _ _))
  simp only [sub_zero, hψ0, smul_eq_mul, Real.norm_eq_abs] at h
  rwa [show ∫ z, ψ (z - s) ∂P + γ * s = ∫ z, ψ (z - s) ∂P - s * -γ by ring]

/-- GAPS 102.48: asymptotic linearization and normality of fixed-design convex M-estimators.
The right derivative of `ρ` is `ψ`. The `L²` continuity of shifted scores is expressed by
nonnegative extended integrals, so nonintegrable remainders cannot be assigned value zero. -/
theorem regression_m_estimator_asymptotic_linearization_and_normality
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ ε P)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (hgram : Tendsto (fixedDesignGramMatrix x) atTop (𝓝 Q))
    (hleverage : Tendsto (fun n : ℕ ↦
      sSup (range fun i : Fin n ↦ ‖x i.val‖) / Real.sqrt n) atTop (𝓝 0))
    (ρ ψ : ℝ → ℝ) (hconv : ConvexOn ℝ univ ρ) (hψ : Measurable ψ)
    (hder : ∀ u, HasDerivWithinAt ρ (ψ u) (Ici u) u)
    (hψ2 : MemLp ψ 2 P) (hψ0 : (∫ z, ψ z ∂P) = 0)
    (hcont : Tendsto (fun t : ℝ ↦ ∫⁻ z, ENNReal.ofReal ((ψ (z - t) - ψ z) ^ 2) ∂P)
      (𝓝 0) (𝓝 0))
    (γ : ℝ) (hγ : 0 < γ)
    (hmean : HasDerivAt (fun t ↦ ∫ z, ψ (z - t) ∂P) (-γ) 0)
    (β : EuclideanSpace ℝ (Fin d)) (T : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hT : ∀ n, Measurable (T n))
    (hmin : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ b,
      regressionMObjective ρ x (fun i ↦ inner ℝ (x i) β + ε i ω) n (T n ω) ≤
        regressionMObjective ρ x (fun i ↦ inner ℝ (x i) β + ε i ω) n b) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - β) -
      (γ * Real.sqrt n)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹
        (∑ i ∈ Finset.range n, ψ (ε i ω) • x i)) atTop (fun _ ↦ 0) ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n • (T n ω - β)) atTop id (fun _ ↦ μ)
      (multivariateGaussian 0 (((∫ z, ψ z ^ 2 ∂P) / γ ^ 2) • Q⁻¹)) := by
  -- transfer of integrals from `μ` to the error law `P`
  have hlaw : ∀ i (g : ℝ → ℝ), Measurable g → ∫ ω, g (ε i ω) ∂μ = ∫ z, g z ∂P := by
    intro i g hg
    rw [← hiid.2.2 i, integral_map (hiid.1 i).aemeasurable hg.aestronglyMeasurable]
  have hρc : Continuous ρ := continuousOn_univ.1 (hconv.continuousOn isOpen_univ)
  have hψ2' : ∀ i, MemLp (fun ω ↦ ψ (ε i ω)) 2 μ := fun i ↦ by
    have hm : MemLp ψ 2 (μ.map (ε i)) := by rw [hiid.2.2 i]; exact hψ2
    exact (memLp_map_measure_iff hψ.aestronglyMeasurable (hiid.1 i).aemeasurable).1 hm
  set σ2 : ℝ := ∫ z, ψ z ^ 2 ∂P with hσ2
  have hdesign : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, x i j * x i k) atTop (𝓝 Q) := by
    convert hgram using 1
    funext n; ext j k
    simp [fixedDesignGramMatrix, div_eq_inv_mul]
  have hweighted : Tendsto (fun n : ℕ ↦ Matrix.of fun j k ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, (fun _ ↦ γ) i * x i j * x i k) atTop (𝓝 (γ • Q)) := by
    convert hdesign.const_smul γ using 1
    funext n; ext j k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hmin' : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂μ, ∀ b, ∑ i ∈ Finset.range n,
      ρ (ε i ω - inner ℝ (x i) (T n ω - β)) ≤
        ∑ i ∈ Finset.range n, ρ (ε i ω - inner ℝ (x i) (b - β)) := by
    intro n hn
    filter_upwards [hmin n hn] with ω hω b
    have hobj : ∀ c, regressionMObjective ρ x (fun i ↦ inner ℝ (x i) β + ε i ω) n c =
        ∑ i ∈ Finset.range n, ρ (ε i ω - inner ℝ (x i) (c - β)) := fun c ↦
      Finset.sum_congr rfl fun i _ ↦ by rw [inner_sub_right]; ring_nf
    simpa only [hobj] using hω b
  obtain ⟨hlin, -, hdist⟩ := tendsto_in_measure_and_tendsto_in_distribution_convex_regression μ ε
    hiid.1 hiid.2.1 hconv hψ
    (fun u v ↦ add_mul_sub_le_of_convex_on_of_has_deriv_within_at hconv
      ((hder u).mono Ioi_subset_Ici_self) v) hψ2'
    (fun i ↦ by rw [hlaw i ψ hψ, hψ0]) (σ2 := σ2)
    (fun i ↦ hlaw i (fun z ↦ ψ z ^ 2) (hψ.pow_const 2))
    (fun η hη ↦ by
      obtain ⟨K, hK⟩ := exists_integral_ite_lt_abs_sq_le hψ2 hη
      refine ⟨K, fun i ↦ ?_⟩
      rwa [hlaw i (fun z ↦ if K < |ψ z| then ψ z ^ 2 else 0)
        (Measurable.ite (measurableSet_lt measurable_const (continuous_abs.measurable.comp hψ))
          (hψ.pow_const 2) measurable_const)])
    (fun η hη ↦ by
      obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1
        (ENNReal.tendsto_nhds_zero.1 hcont (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη))
      refine ⟨δ, hδ, fun i t ht ↦ ?_⟩
      have hm : Measurable fun z ↦ ENNReal.ofReal ((ψ (z - t) - ψ z) ^ 2) :=
        ENNReal.measurable_ofReal.comp
          (((hψ.comp (measurable_id.sub_const t)).sub hψ).pow_const 2)
      rw [← lintegral_map hm (hiid.1 i), hiid.2.2 i]
      exact hb (by rwa [Real.dist_eq, sub_zero]))
    (fun _ ↦ γ)
    (fun η hη ↦ by
      obtain ⟨δ, hδ, hb⟩ := exists_abs_integral_remainder_sub_le hconv hψ hder hψ2 hψ0 hcont
        hmean hη
      refine ⟨δ, hδ, fun i t ht ↦ ?_⟩
      rw [hlaw i (fun z ↦ ρ (z - t) - ρ z + t * ψ z)
        (((hρc.measurable.comp (measurable_id.sub_const t)).sub hρc.measurable).add
          (hψ.const_mul t))]
      exact hb t ht)
    x hQ.posSemidef (hQ.smul hγ) hdesign hweighted hleverage β T hT hmin'
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).1 hQ.isUnit
  have hinv : (γ • Q)⁻¹ = γ⁻¹ • Q⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet, smul_smul,
      mul_inv_cancel₀ hγ.ne', one_smul]
  refine ⟨hlin.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl, ?_⟩
  · simp only [hinv, map_smul, FunLike.coe_smul, Pi.smul_apply, smul_smul, mul_inv]
    rw [mul_comm γ⁻¹]
  · convert hdist using 2
    rw [hinv]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
      smul_smul]
    congr 1
    field_simp

/-- The zero-sample convex regression objective has value zero. -/
@[simp] theorem regression_m_objective_zero {d : ℕ} (ρ : ℝ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (y : ℕ → ℝ) (β : EuclideanSpace ℝ (Fin d)) :
    regressionMObjective ρ x y 0 β = 0 := by simp [regressionMObjective]

end CKSD
