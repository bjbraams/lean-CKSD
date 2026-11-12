module
public import CKSD.Inference.Basic
public import Mathlib.Analysis.Convex.Basic
import CKSD.Inference.FiniteDecision
import CKSD.Inference.KernelDisintegration
import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Finite randomizations from comparison of risks

For finitely many parameter values and actions, comparison of every bounded decision problem
forces exact simulation of every randomized finite-action decision rule. The attainable matrix
of action probabilities is compact and convex by weak `L²` compactness. If a proposed matrix is
outside it, strict separation supplies a loss contradicting the assumed risk comparison.

This is the finite-dimensional separation step of Blackwell's comparison theorem, GAPS 101.62.
Mathlib supplies strict Hahn–Banach separation and kernel integration. The compact convex
decision simplex is developed in `CKSD.Inference.FiniteDecision`.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace CKSD

/-- Risk with finite actions is the loss paired with the randomized action-law masses. -/
theorem risk_eq_sum_actionLaw {Θ X A : Type* } [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)]
    (L : Θ → A → ℝ) (δ : RandomizedDecisionRule X A) (θ : Θ) :
    risk P L δ θ = ∑ a, L θ a * (δ.val ∘ₘ P θ).real {a} := by
  let := δ.property
  have hi (a : A) : Integrable (fun x ↦ (δ.val x).real {a}) (P θ) :=
    (memLp_decision_weight (P θ) δ a).integrable one_le_two
  have he (x : X) : (∫ a, L θ a ∂δ.val x) = ∑ a, L θ a * (δ.val x).real {a} := by
    have hint : Integrable (L θ) (δ.val x) :=
      ⟨(measurable_of_countable (L θ)).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
    simpa only [smul_eq_mul, mul_comm] using integral_fintype hint
  unfold risk
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ ↦ (hi a).const_mul (L θ a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul, integral_kernel_real_apply _ _ (measurableSet_singleton a)]

/-- A finite experiment's attainable action-probability matrices form a compact convex set. -/
theorem isCompact_convex_range_actionLaw {Θ X A : Type* } [Fintype Θ]
    [MeasurableSpace X] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] :
    IsCompact (range (fun δ : RandomizedDecisionRule X A ↦
      fun p : Θ × A ↦ (δ.val ∘ₘ P p.1).real {p.2})) ∧
    Convex ℝ (range (fun δ : RandomizedDecisionRule X A ↦
      fun p : Θ × A ↦ (δ.val ∘ₘ P p.1).real {p.2})) := by
  classical
  let μ : Measure X := ∑ θ, P θ
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let PP : Θ × A → Measure X := fun p ↦ P p.1
  have : ∀ p, IsProbabilityMeasure (PP p) := fun p ↦ by dsimp [PP]; infer_instance
  have hdom (p : Θ × A) : PP p ≤ μ := by
    intro s
    -- Evaluate the domination inequality at a set before expanding the finite measure sum.
    change P p.1 s ≤ (∑ θ, P θ) s
    simp only [FunLike.coe_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun θ ↦ P θ s)
      (fun _ _ ↦ (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ p.1)
  let loss : Θ × A → A → ℝ := fun p a ↦ if a = p.2 then 1 else 0
  have he : risk PP loss = fun δ : RandomizedDecisionRule X A ↦
      fun p : Θ × A ↦ (δ.val ∘ₘ P p.1).real {p.2} := by
    funext δ p
    rw [risk_eq_sum_actionLaw]
    simp [loss, PP]
  rw [← he]
  exact isCompact_convex_range_risk μ PP hdom loss

/-- Finite-action risk comparison forces exact simulation of any finite-action rule. -/
theorem exists_finite_randomization_of_risk_dominance
    {Θ X Y : Type* } [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y)
    [∀ θ, IsProbabilityMeasure (P θ)] [∀ θ, IsProbabilityMeasure (Q θ)]
    (n : ℕ) (hn : 0 < n)
    (hmore : ∀ L : Θ → Fin n → ℝ, (∃ C, ∀ θ a, |L θ a| ≤ C) →
      ∀ δ : RandomizedDecisionRule Y (Fin n), ∃ δ' : RandomizedDecisionRule X (Fin n),
        ∀ θ, risk P L δ' θ ≤ risk Q L δ θ)
    (δ : RandomizedDecisionRule Y (Fin n)) :
    ∃ δ' : RandomizedDecisionRule X (Fin n), ∀ θ, δ'.val ∘ₘ P θ = δ.val ∘ₘ Q θ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let R : RandomizedDecisionRule X (Fin n) → (Θ × Fin n → ℝ) :=
    fun δ' p ↦ (δ'.val ∘ₘ P p.1).real {p.2}
  let q : Θ × Fin n → ℝ := fun p ↦ (δ.val ∘ₘ Q p.1).real {p.2}
  obtain ⟨hcompact, hconv⟩ := isCompact_convex_range_actionLaw (A := Fin n) P
  have hq : q ∈ range R := by
    by_contra hnot
    obtain ⟨f, u, hfu, huf⟩ := geometric_hahn_banach_point_closed hconv hcompact.isClosed hnot
    let w : Θ × Fin n → ℝ := fun p ↦ f (Pi.single p 1)
    have hf (r : Θ × Fin n → ℝ) : f r = ∑ p, w p * r p := by
      -- The coordinate expansion is stated for the underlying linear map of the dual.
      rw [show f r = (f : (Θ × Fin n → ℝ) →ₗ[ℝ] ℝ) r from rfl,
        LinearMap.pi_apply_eq_sum_univ]
      simp only [smul_eq_mul, w, mul_comm]
      apply Finset.sum_congr rfl
      intro p _
      have hbasis : (fun j : Θ × Fin n ↦ if p = j then (1 : ℝ) else 0) = Pi.single p 1 := by
        funext a
        simp [Pi.single_apply, eq_comm]
      rw [hbasis]
      rfl
    let L : Θ → Fin n → ℝ := fun θ a ↦ w (θ, a)
    have hb : ∃ C, ∀ θ a, |L θ a| ≤ C :=
      ⟨∑ p : Θ × Fin n, |w p|, fun θ a ↦
        Finset.single_le_sum (f := fun p ↦ |w p|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ (θ, a))⟩
    obtain ⟨δ', hδ'⟩ := hmore L hb δ
    have hle : f (R δ') ≤ f q := by
      rw [hf, hf, Fintype.sum_prod_type, Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro θ _
      simpa only [risk_eq_sum_actionLaw, L, R, q] using hδ' θ
    exact (not_lt_of_ge hle) (hfu.trans (huf _ ⟨δ', rfl⟩))
  obtain ⟨δ', hδ'⟩ := hq
  refine ⟨δ', fun θ ↦ ?_⟩
  have := δ'.property
  have := δ.property
  apply Measure.ext_of_singleton
  intro a
  have hr := congrFun hδ' (θ, a)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hr

end CKSD
