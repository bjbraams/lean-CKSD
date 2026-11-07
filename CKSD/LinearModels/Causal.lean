module

public import CKSD.LinearModels.Basic
public import Mathlib.Probability.Independence.Conditional

/-!
# Regression criteria and finite causal graphs

Potential outcomes are ordinary random variables; finite causal graphs are acyclic relations.
The intervention mass is the truncated product of the supplied local conditional masses.
Sources: GAPS 105.3, 105.5, 105.26, 105.48, 105.55–105.71.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Quantile-regression check loss, with the conventional left/right value zero at the origin. -/
def quantileCheckLoss (τ u : ℝ) : ℝ := u * (τ - if u < 0 then 1 else 0)

/-- Fixed-design quantile-regression objective. -/
def quantileRegressionObjective {n p : ℕ} (τ : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin p))
    (y : Fin n → ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, quantileCheckLoss τ (y i - inner ℝ (x i) β)

/-- A quantile-regression estimate minimizes the check-loss objective. -/
def IsQuantileRegressionEstimator {n p : ℕ} (τ : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (y : Fin n → ℝ)
    (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ b, quantileRegressionObjective τ x y β ≤ quantileRegressionObjective τ x y b

/-- An exponential-dispersion log density. -/
def exponentialDispersionLogDensity (b : ℝ → ℝ) (c : ℝ → ℝ → ℝ)
    (y θ φ : ℝ) : ℝ := (y * θ - b θ) / φ + c y φ

/-- Generalized-linear-model information matrix for a specified diagonal weight vector. -/
def glmInformationMatrix {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (w : Fin n → ℝ) (φ : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  φ⁻¹ • (X.transpose * Matrix.diagonal w * X)

/-- Two-stage least-squares coefficient, using the instrument projection. -/
def twoStageLeastSquares {n p k : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  let P := Z * (Z.transpose * Z)⁻¹ * Z.transpose
  (X.transpose * P * X)⁻¹.mulVec ((X.transpose * P).mulVec y)

/-- Average-treatment-effect efficient influence function, with observed outcome as argument. -/
def treatmentEffectInfluence {X : Type*} (m₀ m₁ e : X → ℝ) (ate : ℝ)
    (x : X) (a : Bool) (y : ℝ) : ℝ :=
  m₁ x - m₀ x - ate + if a then (y - m₁ x) / e x else -(y - m₀ x) / (1 - e x)

/-- Finite directed acyclic causal graph; acyclicity excludes every nonempty directed cycle. -/
structure CausalGraph (V : Type*) where
  /-- Directed edge relation. -/
  edge : V → V → Prop
  /-- No nonempty directed path returns to its initial vertex. -/
  acyclic : ∀ v, ¬ Relation.TransGen edge v v

/-- Parents of a vertex in a causal graph. -/
def CausalGraph.parents {V : Type*} (G : CausalGraph V) (v : V) : Set V :=
  {u | G.edge u v}

/-- Proper descendant relation in a causal graph. -/
def CausalGraph.IsDescendant {V : Type*} (G : CausalGraph V) (u v : V) : Prop :=
  Relation.TransGen G.edge u v

/-- A path is active when each noncollider is unconditioned and each collider has an observed
descendant. -/
def CausalGraph.IsActivePath {V : Type*} (G : CausalGraph V) (Z : Set V)
    {n : ℕ} (p : Fin (n + 1) → V) : Prop :=
  Function.Injective p ∧
    (∀ i : Fin n, G.edge (p i.castSucc) (p i.succ) ∨ G.edge (p i.succ) (p i.castSucc)) ∧
    ∀ i : Fin (n - 1),
      let a : Fin (n + 1) := ⟨i.val, by omega⟩;
      let b : Fin (n + 1) := ⟨i.val + 1, by omega⟩;
      let c : Fin (n + 1) := ⟨i.val + 2, by omega⟩;
      if G.edge (p a) (p b) ∧ G.edge (p c) (p b)
      then ∃ z ∈ Z, z = p b ∨ G.IsDescendant (p b) z
      else p b ∉ Z

/-- Graphical d-separation by absence of an active path. -/
def CausalGraph.DSeparated {V : Type*} (G : CausalGraph V) (A B Z : Set V) : Prop :=
  ∀ n : ℕ, ∀ p : Fin (n + 1) → V, p 0 ∈ A → p (Fin.last n) ∈ B → ¬ G.IsActivePath Z p

/-- Two causal graphs are Markov equivalent if all their d-separation statements agree. -/
def CausalGraph.MarkovEquivalent {V : Type*} (G H : CausalGraph V) : Prop :=
  ∀ A B Z, G.DSeparated A B Z ↔ H.DSeparated A B Z

/-- Undirected skeleton adjacency. -/
def CausalGraph.Adjacent {V : Type*} (G : CausalGraph V) (u v : V) : Prop :=
  G.edge u v ∨ G.edge v u

/-- An unshielded collider is an inward-facing triple with nonadjacent endpoints. -/
def CausalGraph.IsUnshieldedCollider {V : Type*} (G : CausalGraph V) (u v w : V) : Prop :=
  u ≠ w ∧ G.edge u v ∧ G.edge w v ∧ ¬ G.Adjacent u w

/-- Local mass functions obey the parent restriction of a specified graph. -/
def CausalGraph.RespectsParents {V S : Type*} (G : CausalGraph V)
    (localMass : V → (V → S) → S → ℝ) : Prop :=
  ∀ v x y, (∀ u ∈ G.parents v, x u = y u) → localMass v x = localMass v y

/-- Recursive product mass from local conditional masses. -/
def directedFactorizationMass {V S : Type*} [Fintype V]
    (localMass : V → (V → S) → S → ℝ) (x : V → S) : ℝ :=
  ∏ v, localMass v x (x v)

/-- Truncated factorization for an intervention on a finite set of vertices. -/
def interventionMass {V S : Type*} [Fintype V] [DecidableEq V] [DecidableEq S]
    (localMass : V → (V → S) → S → ℝ) (A : Finset V) (a x : V → S) : ℝ :=
  if ∀ v ∈ A, x v = a v then ∏ v ∈ Aᶜ, localMass v x (x v) else 0

/-- GAPS 105.67: skeleton and unshielded colliders characterize Markov equivalence. -/
theorem markovEquivalent_iff_skeleton_and_colliders {V : Type*} [Fintype V]
    (G H : CausalGraph V) :
    G.MarkovEquivalent H ↔
      (∀ u v, G.Adjacent u v ↔ H.Adjacent u v) ∧
        ∀ u v w, G.IsUnshieldedCollider u v w ↔ H.IsUnshieldedCollider u v w := by
  sorry

/-- Check loss is nonnegative for a probability level. -/
theorem quantileCheckLoss_nonneg (τ u : ℝ) (hτ : τ ∈ Icc 0 1) :
    0 ≤ quantileCheckLoss τ u := by
  unfold quantileCheckLoss
  split_ifs with h
  · exact mul_nonneg_of_nonpos_of_nonpos h.le (by linarith [hτ.2])
  · exact mul_nonneg (le_of_not_gt h) (by simpa using hτ.1)

/-- Graphical Markov equivalence is reflexive. -/
theorem CausalGraph.markovEquivalent_refl {V : Type*} (G : CausalGraph V) :
    G.MarkovEquivalent G := fun _ _ _ ↦ Iff.rfl

/-- The propensity score as a conditional expectation on the original sample space. -/
def propensityScore {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (A : Ω → Bool) (X : Ω → S) : Ω → ℝ :=
  P[(fun ω ↦ if A ω then (1 : ℝ) else 0) | (inferInstance : MeasurableSpace S).comap X]

/-- GAPS 105.48: the propensity score is a balancing score, in the standard Borel setting. -/
theorem condIndepFun_propensityScore {Ω S : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → Bool) (hA : Measurable A) (X : Ω → S) (hX : Measurable X)
    (he : Measurable (propensityScore P A X)) :
    CondIndepFun ((inferInstance : MeasurableSpace ℝ).comap (propensityScore P A X))
      he.comap_le A X P := by
  sorry

/-- GAPS 105.48: ignorability descends from the covariates to their propensity score. -/
theorem condIndepFun_of_propensityScore {Ω S : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → Bool) (hA : Measurable A) (X : Ω → S) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hind : CondIndepFun ((inferInstance : MeasurableSpace S).comap X) hX.comap_le Y A P)
    (he : Measurable (propensityScore P A X)) :
    CondIndepFun ((inferInstance : MeasurableSpace ℝ).comap (propensityScore P A X))
      he.comap_le Y A P := by
  sorry

end CKSD
