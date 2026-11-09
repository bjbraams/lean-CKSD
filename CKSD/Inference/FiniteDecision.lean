module

public import CKSD.Inference.Model
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.Analysis.Convex.Uniform.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# Compact risk sets for finite decision problems

Finite randomized action probabilities are represented as points of a product of weak `L²`
spaces. The simplex constraints define a compact convex subset, and each such point has a
measurable Markov-kernel representative, including on the exceptional null set. Pairing action
probabilities with bounded Radon–Nikodym densities makes the risk map weakly continuous.

The resulting compactness and convexity theorem supports the finite statistical minimax theorem
in `CKSD.Inference.Decision`. Observation spaces need only be measurable spaces.

The proof uses Mathlib's `L²`, Markov kernels, and Radon–Nikodym integration. Weak compactness
uses TauCeti's Milman–Pettis theorem and its compactness theorem for closed bounded convex
subsets of reflexive spaces.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CKSD
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- The nonnegative order interval in real `L²` is convex. -/
theorem convex_l2OrderInterval (u : Lp ℝ 2 μ) : Convex ℝ (Icc 0 u) := by
  intro f hf g hg a b ha hb hab
  rw [mem_Icc, ← Lp.coeFn_nonneg, ← Lp.coeFn_le]
  change (∀ᵐ x ∂μ, 0 ≤ (a • f + b • g) x) ∧
    (∀ᵐ x ∂μ, (a • f + b • g) x ≤ u x)
  rw [← eventually_and]
  filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul b g,
    Lp.coeFn_add (a • f) (b • g), Lp.coeFn_nonneg f |>.2 hf.1,
    Lp.coeFn_nonneg g |>.2 hg.1, Lp.coeFn_le f u |>.2 hf.2,
    Lp.coeFn_le g u |>.2 hg.2] with x h1 h2 h3 hf0 hg0 hfu hgu
  rw [h3, Pi.add_apply, h1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  change 0 ≤ f x at hf0
  change 0 ≤ g x at hg0
  exact ⟨add_nonneg (mul_nonneg ha hf0) (mul_nonneg hb hg0),
    (add_le_add (mul_le_mul_of_nonneg_left hfu ha)
      (mul_le_mul_of_nonneg_left hgu hb)).trans_eq (by rw [← add_mul, hab, one_mul])⟩

omit [IsFiniteMeasure μ] in
/-- Nonnegative order intervals in real `L²` are weakly compact, by reflexivity. -/
theorem isCompact_weak_l2OrderInterval (u : Lp ℝ 2 μ) (hu : 0 ≤ u) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 2 μ) '' Icc 0 u) := by
  apply TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded
    (TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ))
    isClosed_Icc (convex_l2OrderInterval μ u)
  apply Metric.isBounded_iff_subset_closedBall (0 : Lp ℝ 2 μ) |>.2
  refine ⟨‖u‖, fun f hf ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply norm_le_norm_of_abs_le_abs
  simpa [abs_of_nonneg hf.1, abs_of_nonneg hu] using hf.2

omit [IsFiniteMeasure μ] in
/-- Evaluation of an `L²` inner product is weakly continuous in its second argument. -/
theorem continuous_weak_l2Inner (z : Lp ℝ 2 μ) :
    Continuous (fun f : WeakSpace ℝ (Lp ℝ 2 μ) ↦ inner ℝ z ((toWeakSpace ℝ _).symm f)) := by
  exact WeakBilin.eval_continuous (topDualPairing ℝ (Lp ℝ 2 μ)).flip (innerSL ℝ z)

/-- The constant-one element of real `L²` is nonnegative. -/
theorem l2Const_one_nonneg : 0 ≤ Lp.const 2 μ (1 : ℝ) := by
  rw [← Lp.coeFn_nonneg]
  change ∀ᵐ x ∂μ, 0 ≤ (Lp.const 2 μ (1 : ℝ)) x
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with x hx
  rw [hx]
  norm_num

end CKSD

namespace CKSD
variable {X A : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [Fintype A]

/-- A probability decision rule represented in weak `L²` coordinates. -/
def weakDecisionSimplex : Set (A → WeakSpace ℝ (Lp ℝ 2 μ)) :=
  {f | ∀ a, f a ∈ toWeakSpace ℝ (Lp ℝ 2 μ) '' Icc 0 (Lp.const 2 μ (1 : ℝ))} ∩
    {f | ∑ a, f a = toWeakSpace ℝ _ (Lp.const 2 μ (1 : ℝ))}

/-- Weak compactness of finite randomized action probabilities. -/
theorem isCompact_weakDecisionSimplex {A : Type*} [Fintype A] :
    IsCompact (weakDecisionSimplex (A := A) μ) := by
  exact (isCompact_pi_infinite fun _ ↦
    isCompact_weak_l2OrderInterval μ _ (l2Const_one_nonneg μ)).inter_right
      (isClosed_eq (by fun_prop) continuous_const)

/-- The finite decision simplex is convex in the product weak topology. -/
theorem convex_weakDecisionSimplex {A : Type*} [Fintype A] :
    Convex ℝ (weakDecisionSimplex (A := A) μ) := by
  apply Convex.inter
  · intro f hf g hg a b ha hb hab i
    exact ((convex_l2OrderInterval μ (Lp.const 2 μ (1 : ℝ))).linear_image
      (toWeakSpace ℝ (Lp ℝ 2 μ)).toLinearMap) (hf i) (hg i) ha hb hab
  · intro f hf g hg a b ha hb hab
    change ∑ i, (a • f i + b • g i) = _
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf, hg, ← add_smul,
      hab, one_smul]

end CKSD

namespace CKSD
variable {X A : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] in
/-- Each action probability of a decision rule is square integrable under a finite measure. -/
theorem memLp_decision_weight (δ : RandomizedDecisionRule X A) (a : A) :
    MemLp (fun x ↦ (δ.val x).real {a}) 2 μ := by
  let := δ.property
  apply MemLp.of_bound
    ((Kernel.measurable_coe δ.val (measurableSet_singleton a)).ennreal_toReal.aestronglyMeasurable) 1
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one

/-- The weak `L²` coordinates of the action probabilities of a randomized decision rule. -/
def decisionWeights (δ : RandomizedDecisionRule X A) : A → WeakSpace ℝ (Lp ℝ 2 μ) :=
  fun a ↦ toWeakSpace ℝ _ ((memLp_decision_weight μ δ a).toLp (fun x ↦ (δ.val x).real {a}))

/-- A decision rule has weak `L²` action probabilities in the simplex. -/
theorem decisionWeights_mem_weakDecisionSimplex (δ : RandomizedDecisionRule X A) :
    decisionWeights μ δ ∈ weakDecisionSimplex μ := by
  let := δ.property
  constructor
  · intro a
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · rw [← Lp.coeFn_nonneg]
      change ∀ᵐ x ∂μ, 0 ≤ ((memLp_decision_weight μ δ a).toLp _) x
      filter_upwards [MemLp.coeFn_toLp (memLp_decision_weight μ δ a)] with x hx
      rw [hx]
      exact measureReal_nonneg
    · rw [← Lp.coeFn_le]
      change ∀ᵐ x ∂μ, ((memLp_decision_weight μ δ a).toLp _) x ≤ (Lp.const 2 μ (1 : ℝ)) x
      filter_upwards [MemLp.coeFn_toLp (memLp_decision_weight μ δ a), Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hy
      rw [hx, hy]
      exact measureReal_le_one
  · change ∑ a, toWeakSpace ℝ _ _ = _
    rw [← map_sum]
    congr 1
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun a ↦ (memLp_decision_weight μ δ a).toLp _),
      (ae_all_iff.2 fun a ↦ MemLp.coeFn_toLp (memLp_decision_weight μ δ a)),
      Lp.coeFn_const 2 μ (1 : ℝ)] with x hsum heq hc
    rw [hsum, hc]
    simp only [Finset.sum_apply, heq]
    simp

end CKSD

namespace CKSD
variable {X A : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Every weak `L²` point of the decision simplex is represented by a Markov kernel. -/
theorem exists_decisionRule_of_weakDecisionSimplex (f : A → WeakSpace ℝ (Lp ℝ 2 μ)) (hf : f ∈ weakDecisionSimplex μ) :
    ∃ δ : RandomizedDecisionRule X A, decisionWeights μ δ = f := by
  classical
  let g : A → Lp ℝ 2 μ := fun a ↦ (toWeakSpace ℝ _).symm (f a)
  have hg (a : A) : g a ∈ Icc 0 (Lp.const 2 μ (1 : ℝ)) := by
    obtain ⟨u, hu, heq⟩ := hf.1 a
    simpa [g, ← heq] using hu
  have hsum : ∑ a, g a = Lp.const 2 μ (1 : ℝ) := by
    have h := congrArg (toWeakSpace ℝ (Lp ℝ 2 μ)).symm hf.2
    simpa [g] using h
  let E : Set X := {x | (∀ a, 0 ≤ g a x) ∧ ∑ a, g a x = 1}
  have hEm : MeasurableSet E := by
    have hp : MeasurableSet {x | ∀ a, 0 ≤ g a x} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun a ↦
        measurableSet_le measurable_const (Lp.stronglyMeasurable (g a)).measurable
    exact hp.inter
        (measurableSet_eq_fun (Finset.measurable_sum _ fun a _ ↦
          (Lp.stronglyMeasurable (g a)).measurable) measurable_const)
  have hEae : ∀ᵐ x ∂μ, x ∈ E := by
    filter_upwards [(ae_all_iff.2 fun a ↦ (Lp.coeFn_nonneg (g a)).2 (hg a).1),
      Lp.coeFn_finsetSum Finset.univ g, Lp.coeFn_const 2 μ (1 : ℝ)] with x hnon hsum' hconst
    refine ⟨hnon, ?_⟩
    have h := hsum' 
    rw [hsum, hconst] at h
    simpa only [Finset.sum_apply, Function.const_apply] using h.symm
  let a₀ : A := Classical.choice inferInstance
  let w : X → A → ℝ := fun x a ↦ if x ∈ E then g a x else if a = a₀ then 1 else 0
  have hwm (a : A) : Measurable (fun x ↦ w x a) :=
    Measurable.ite hEm (Lp.stronglyMeasurable (g a)).measurable measurable_const
  have hwn (x : X) (a : A) : 0 ≤ w x a := by
    by_cases hx : x ∈ E
    · simpa only [w, ite_eq_left hx] using hx.1 a
    · simp only [w, ite_eq_right hx]; split <;> norm_num
  have hws (x : X) : ∑ a, w x a = 1 := by
    by_cases hx : x ∈ E
    · simpa only [w, ite_eq_left hx] using hx.2
    · simp [w, hx]
  let K : Kernel X A :=
    ⟨fun x ↦ ∑ a, ENNReal.ofReal (w x a) • Measure.dirac a,
      Measure.measurable_of_measurable_coe _ fun s hs ↦ by
        simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
        exact Finset.measurable_sum _ fun a _ ↦ (hwm a).ennreal_ofReal.mul_const _⟩
  have hK : IsMarkovKernel K := ⟨fun x ↦ ⟨by
    change (∑ a, ENNReal.ofReal (w x a) • Measure.dirac a) univ = 1
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ hwn x a), hws, ENNReal.ofReal_one]⟩⟩
  have hweight (x : X) (a : A) : (K x).real {a} = w x a := by
    change ((∑ b, ENNReal.ofReal (w x b) • Measure.dirac b) {a}).toReal = _
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
    simp [Pi.single_apply, mul_ite, ENNReal.toReal_ofReal (hwn x a)]
  refine ⟨⟨K, hK⟩, funext fun a ↦ ?_⟩
  apply (toWeakSpace ℝ _).symm.injective
  change (memLp_decision_weight μ ⟨K, hK⟩ a).toLp _ = g a
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_decision_weight μ ⟨K, hK⟩ a), hEae] with x hx hE
  rw [hx, hweight]
  exact ite_eq_left hE

end CKSD

namespace CKSD
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The density of a measure bounded by a finite measure is in `L²`, with values in `[0,1]`. -/
theorem memLp_rnDeriv_of_le (P : Measure X) (hP : P ≤ μ) :
    MemLp (fun x ↦ (P.rnDeriv μ x).toReal) 2 μ := by
  apply MemLp.of_bound (P.measurable_rnDeriv μ).ennreal_toReal.aestronglyMeasurable 1
  filter_upwards [Measure.rnDeriv_le_one_of_le hP] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hx

/-- The `L²` Radon–Nikodym density of a measure dominated by a finite measure. -/
def l2DominatedDensity (P : Measure X) (hP : P ≤ μ) : Lp ℝ 2 μ :=
  (memLp_rnDeriv_of_le μ P hP).toLp (fun x ↦ (P.rnDeriv μ x).toReal)

/-- Risk for a finite action space is a finite sum of `L²` pairings with model densities. -/
theorem risk_eq_sum_l2Inner {Θ A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)]
    (hP : ∀ θ, P θ ≤ μ) (L : Θ → A → ℝ) (δ : RandomizedDecisionRule X A) (θ : Θ) :
    risk P L δ θ = ∑ a, L θ a * inner ℝ (l2DominatedDensity μ (P θ) (hP θ))
      ((toWeakSpace ℝ _).symm (decisionWeights μ δ a)) := by
  let := δ.property
  have hi (a : A) : Integrable (fun x ↦ (δ.val x).real {a}) (P θ) :=
    (memLp_decision_weight (P θ) δ a).integrable one_le_two
  have hin (x : X) : (∫ a, L θ a ∂δ.val x) = ∑ a, L θ a * (δ.val x).real {a} := by
    have hint : Integrable (L θ) (δ.val x) :=
      ⟨(measurable_of_countable (L θ)).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
    simpa only [smul_eq_mul, mul_comm] using integral_fintype hint
  change (∫ x, ∫ a, L θ a ∂δ.val x ∂P θ) = _
  simp_rw [hin]
  rw [integral_finsetSum _ (fun a _ ↦ (hi a).const_mul (L θ a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  congr 1
  change (∫ x, (δ.val x).real {a} ∂P θ) = inner ℝ (l2DominatedDensity μ (P θ) (hP θ))
    ((memLp_decision_weight μ δ a).toLp _)
  rw [L2.inner_def]
  have hcong : (∫ x, inner ℝ ((l2DominatedDensity μ (P θ) (hP θ)) x)
      (((memLp_decision_weight μ δ a).toLp _) x) ∂μ) =
      ∫ x, ((P θ).rnDeriv μ x).toReal * (δ.val x).real {a} ∂μ := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_rnDeriv_of_le μ (P θ) (hP θ)),
      MemLp.coeFn_toLp (memLp_decision_weight μ δ a)] with x h1 h2
    rw [show (l2DominatedDensity μ (P θ) (hP θ)) x = _ from h1, h2]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hcong, integral_toReal_rnDeriv_mul (Measure.absolutelyContinuous_of_le (hP θ))]

end CKSD

namespace CKSD
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Finite-action risk vectors form a compact convex set when a finite measure dominates
all model laws with bounded densities. The compactness uses weak `L²` randomizations. -/
theorem isCompact_convex_range_risk {Θ A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] (hP : ∀ θ, P θ ≤ μ)
    (L : Θ → A → ℝ) :
    IsCompact (range (risk P L)) ∧ Convex ℝ (range (risk P L)) := by
  let ρ : Θ → Lp ℝ 2 μ := fun θ ↦ l2DominatedDensity μ (P θ) (hP θ)
  let R : (A → WeakSpace ℝ (Lp ℝ 2 μ)) →ₗ[ℝ] (Θ → ℝ) :=
    { toFun := fun f θ ↦ ∑ a, L θ a * inner ℝ (ρ θ) ((toWeakSpace ℝ _).symm (f a))
      map_add' := by
        intro f g
        ext θ
        simp only [Pi.add_apply, map_add, inner_add_right, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext θ
        simp only [Pi.smul_apply, map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring }
  have hR : Continuous R := by
    apply continuous_pi
    intro θ
    exact continuous_finsetSum _ fun a _ ↦
      ((continuous_weak_l2Inner μ (ρ θ)).comp (continuous_apply a)).const_mul (L θ a)
  have himage : R '' weakDecisionSimplex μ = range (risk P L) := by
    ext r
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨δ, hδ⟩ := exists_decisionRule_of_weakDecisionSimplex μ f hf
      refine ⟨δ, funext fun θ ↦ ?_⟩
      rw [risk_eq_sum_l2Inner μ P hP L δ θ, hδ]
      rfl
    · rintro ⟨δ, rfl⟩
      refine ⟨decisionWeights μ δ, decisionWeights_mem_weakDecisionSimplex μ δ,
        funext fun θ ↦ ?_⟩
      exact (risk_eq_sum_l2Inner μ P hP L δ θ).symm
  rw [← himage]
  exact ⟨(isCompact_weakDecisionSimplex μ).image hR,
    (convex_weakDecisionSimplex μ).linear_image R⟩

end CKSD
