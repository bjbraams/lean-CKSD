module

public import CKSD.LinearModels.Causal

/-!
# Identifiability of restricted structural equation models

A structural equation model along a directed acyclic graph `G` on a finite vertex set `V` is
described at the level of laws on `V → ℝ`: the noise vector has the product law of its
coordinate laws, and the observed vector is the image of the noise under the solution map of
the structural equations. In the linear case `X = B X + N`, with `B j k ≠ 0` exactly on the
edges `k → j`, the solution map is `N ↦ (1 - B)⁻¹ N`.

Conditional independence for laws on `V → ℝ` is Mathlib's `CondIndepFun` of coordinate
projections. Source: GAPS 105.71.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace CKSD

variable {V : Type*}

/-- A coefficient matrix of a linear structural equation model along `G`: the coefficient of
`X_k` in the equation of `X_j` is nonzero exactly when `k → j` is an edge. -/
def CausalGraph.IsLinearSEMMatrix (G : CausalGraph V) (B : Matrix V V ℝ) : Prop :=
  ∀ j k, B j k ≠ 0 ↔ G.edge k j

/-- The law of the solution `X = (1 - B)⁻¹ N` of a linear structural equation model with
independent noises of laws `ν j`. -/
def linearSEMLaw [Fintype V] [DecidableEq V] (B : Matrix V V ℝ) (ν : V → Measure ℝ) :
    Measure (V → ℝ) :=
  (Measure.pi ν).map fun n ↦ ((1 - B)⁻¹).mulVec n

/-- The law of a linear structural equation model with noise laws that are probability measures
is a probability measure. -/
instance isProbabilityMeasure_linearSEMLaw [Fintype V] [DecidableEq V] (B : Matrix V V ℝ)
    (ν : V → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] :
    IsProbabilityMeasure (linearSEMLaw B ν) := by
  unfold linearSEMLaw
  infer_instance

/-- A real law is non-Gaussian with a strictly positive density. -/
def IsNonGaussianPositiveDensityLaw (ν : Measure ℝ) : Prop :=
  (∃ f : ℝ → ℝ, HasDensity ν volume f ∧ ∀ t, 0 < f t) ∧
    ∀ (m : ℝ) (v : ℝ≥0), ν ≠ gaussianReal m v

/-- Restriction of a vector to the coordinates in `B`. -/
def coordinateRestriction (B : Finset V) (x : V → ℝ) : B → ℝ := fun b ↦ x b

/-- Coordinate restrictions are measurable. -/
@[fun_prop] theorem measurable_coordinateRestriction (B : Finset V) :
    Measurable (coordinateRestriction B : (V → ℝ) → B → ℝ) := by
  unfold coordinateRestriction
  fun_prop

/-- A law on `V → ℝ` is faithful to `G` when, for disjoint `A`, `B`, `C`, the coordinates in
`A` and `B` are conditionally independent given those in `C` exactly when `A` and `B` are
d-separated by `C`. -/
def CausalGraph.IsFaithfulLaw [Fintype V] (G : CausalGraph V) (μ : Measure (V → ℝ))
    [IsFiniteMeasure μ] : Prop :=
  ∀ A B C : Finset V, Disjoint A B → Disjoint A C → Disjoint B C →
    (G.DSeparated A B C ↔
      CondIndepFun ((inferInstance : MeasurableSpace (C → ℝ)).comap (coordinateRestriction C))
        (measurable_coordinateRestriction C).comap_le (coordinateRestriction A)
        (coordinateRestriction B) μ)

/-- The structural functions of an additive-noise model respect the parents of `G`. -/
def CausalGraph.RespectsParentsReal (G : CausalGraph V) (f : V → (V → ℝ) → ℝ) : Prop :=
  ∀ j x y, (∀ k, G.edge k j → x k = y k) → f j x = f j y

/-- The law of an additive-noise model `X_j = f_j(X_{pa(j)}) + N_j` with independent noises
of laws `ν j`: the image of the noise law under a measurable solution map of the equations. -/
def IsAdditiveNoiseLaw [Fintype V] (f : V → (V → ℝ) → ℝ) (ν : V → Measure ℝ)
    (μ : Measure (V → ℝ)) : Prop :=
  ∃ Φ : (V → ℝ) → V → ℝ, Measurable Φ ∧ (∀ n j, Φ n j = f j (Φ n) + n j) ∧
    μ = (Measure.pi ν).map Φ

/-- Each structural function is nonlinear in each of its parent arguments: along every line in
the direction of a parent coordinate it is not affine. -/
def CausalGraph.IsNonlinearInParents [DecidableEq V] (G : CausalGraph V)
    (f : V → (V → ℝ) → ℝ) : Prop :=
  ∀ j k, G.edge k j → ∀ x : V → ℝ, ¬ ∃ c d : ℝ, ∀ t, f j (Function.update x k t) = c * t + d

/-- GAPS 105.71, linear non-Gaussian models: if two linear structural equation models along
`G` and `H`, with nonzero coefficients on the edges and independent non-Gaussian noises with
strictly positive densities, have the same law, then `G = H`. -/
theorem CausalGraph.edge_eq_of_linearSEMLaw_eq_of_nonGaussian [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B B' : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B)
    (hB' : H.IsLinearSEMMatrix B') (ν ν' : V → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, IsProbabilityMeasure (ν' j)]
    (hν : ∀ j, IsNonGaussianPositiveDensityLaw (ν j))
    (hν' : ∀ j, IsNonGaussianPositiveDensityLaw (ν' j))
    (hlaw : linearSEMLaw B ν = linearSEMLaw B' ν') :
    G.edge = H.edge := by
  sorry

/-- GAPS 105.71, linear Gaussian models with equal noise variances: if two linear structural
equation models along `G` and `H`, with nonzero coefficients on the edges and independent
Gaussian noises of one common positive variance within each model, have the same law, then
`G = H`. The noise means are arbitrary. -/
theorem CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B B' : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B)
    (hB' : H.IsLinearSEMMatrix B') (m m' : V → ℝ) (σ2 σ2' : ℝ≥0) (hσ : 0 < σ2) (hσ' : 0 < σ2')
    (hlaw : linearSEMLaw B (fun j ↦ gaussianReal (m j) σ2) =
      linearSEMLaw B' (fun j ↦ gaussianReal (m' j) σ2')) :
    G.edge = H.edge := by
  sorry

/-- GAPS 105.71, nonlinear additive Gaussian-noise models: if two additive-noise models along
`G` and `H`, with three times continuously differentiable structural functions that respect
the parents and are nonlinear in each parent argument, and independent Gaussian noises of
positive variances, have the same law, then `G = H`. -/
theorem CausalGraph.edge_eq_of_additiveNoiseLaw_eq [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (f g : V → (V → ℝ) → ℝ)
    (hfG : G.RespectsParentsReal f) (hgH : H.RespectsParentsReal g)
    (hf : ∀ j, ContDiff ℝ 3 (f j)) (hg : ∀ j, ContDiff ℝ 3 (g j))
    (hfn : G.IsNonlinearInParents f) (hgn : H.IsNonlinearInParents g)
    (m m' : V → ℝ) (σ2 σ2' : V → ℝ≥0) (hσ : ∀ j, 0 < σ2 j) (hσ' : ∀ j, 0 < σ2' j)
    (μ : Measure (V → ℝ))
    (hμ : IsAdditiveNoiseLaw f (fun j ↦ gaussianReal (m j) (σ2 j)) μ)
    (hμ' : IsAdditiveNoiseLaw g (fun j ↦ gaussianReal (m' j) (σ2' j)) μ) :
    G.edge = H.edge := by
  sorry

/-- GAPS 105.71, linear Gaussian models with unrestricted variances identify only the Markov
equivalence class: for a linear Gaussian model along `G` whose law is faithful to `G`, a
directed acyclic graph `H` carries a linear Gaussian model (nonzero edge coefficients,
positive noise variances) with the same law exactly when `H` is Markov equivalent to `G`.
Faithfulness is the hypothesis under which the equivalence class is the precise answer. -/
theorem CausalGraph.exists_linearGaussianSEM_iff_markovEquivalent [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B) (m : V → ℝ)
    (σ2 : V → ℝ≥0) (hσ : ∀ j, 0 < σ2 j)
    (hfaith : G.IsFaithfulLaw (linearSEMLaw B fun j ↦ gaussianReal (m j) (σ2 j))) :
    (∃ (B' : Matrix V V ℝ) (m' : V → ℝ) (σ2' : V → ℝ≥0), H.IsLinearSEMMatrix B' ∧
        (∀ j, 0 < σ2' j) ∧
        linearSEMLaw B' (fun j ↦ gaussianReal (m' j) (σ2' j)) =
          linearSEMLaw B fun j ↦ gaussianReal (m j) (σ2 j)) ↔
      H.MarkovEquivalent G := by
  sorry

end CKSD
