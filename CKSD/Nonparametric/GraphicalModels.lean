module

public import CKSD.Nonparametric.EmpiricalCovariance
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Gaussian graphical model selection

The precision matrix is `Θ = Σ⁻¹`, and the neighbourhood of a vertex `j` is the set of
`k ≠ j` with `Θ j k ≠ 0`. Neighbourhood selection runs, for each vertex `j`, a lasso of
coordinate `j` on the other coordinates with the `1/(2n)` squared-error normalization, and
joins the estimated neighbourhoods by the "and" or the "or" rule. The graphical lasso
minimizes `tr(Θ Σ̂) - log det Θ + λ ∑_{j ≠ k} |Θ j k|` over positive definite `Θ`, where
`Σ̂ = n⁻¹ ∑ xᵢ xᵢᵀ` is the second-moment matrix of a centered sample.
Source: GAPS 103.53 (Wainwright, Theorem 11.12 and Proposition 11.9).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The neighbourhood `N(j) = {k ≠ j | Θ j k ≠ 0}` of a vertex in the graph of a matrix. -/
def precisionNeighbourhood {p : ℕ} (Θ : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    Finset (Fin p) :=
  Finset.univ.filter fun k ↦ k ≠ j ∧ Θ j k ≠ 0

/-- The principal submatrix of a matrix on a set of indices. -/
def principalSubmatrix {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Fin p)) :
    Matrix S S ℝ :=
  A.submatrix Subtype.val Subtype.val

/-- Incoherence at vertex `j`: every `k ∉ S ∪ {j}` has
`‖Σ_{k S} (Σ_{S S})⁻¹‖₁ ≤ 1 - α`. When `S` avoids `j` this is the incoherence of the
covariance of the coordinates other than `j` with respect to `S`. -/
def IsIncoherentAt {p : ℕ} (Sig : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Fin p)) (j : Fin p)
    (α : ℝ) : Prop :=
  ∀ k, k ≠ j → k ∉ S →
    ∑ l : S, |∑ m : S, Sig k m * (principalSubmatrix Sig S)⁻¹ m l| ≤ 1 - α

/-- The bound `‖A‖_{∞→∞} ≤ b` on the maximal absolute row sum. -/
def RowSumNormLE {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (b : ℝ) : Prop :=
  ∀ i, ∑ l, |A i l| ≤ b

/-- The lasso objective for regressing coordinate `j` on the other coordinates. -/
def nodeLassoObjective {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) (j : Fin p)
    (lambda : ℝ) (β : Fin p → ℝ) : ℝ :=
  (∑ i, (x i j - ∑ k, β k * x i k) ^ 2) / (2 * n) + lambda * ∑ k, |β k|

/-- `β` is a neighbourhood-lasso estimate for vertex `j`: it has zero `j`-th coefficient and
minimizes the node lasso objective among such coefficient vectors. -/
def IsNodeLassoEstimate {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) (j : Fin p)
    (lambda : ℝ) (β : Fin p → ℝ) : Prop :=
  β j = 0 ∧ ∀ β' : Fin p → ℝ, β' j = 0 →
    nodeLassoObjective x j lambda β ≤ nodeLassoObjective x j lambda β'

/-- The "and" rule: `{j, k}` is an estimated edge when each lies in the other's estimated
neighbourhood; `B j` are the coefficients of the regression of coordinate `j`. -/
def andRuleEdge {p : ℕ} (B : Fin p → Fin p → ℝ) (j k : Fin p) : Prop :=
  j ≠ k ∧ B j k ≠ 0 ∧ B k j ≠ 0

/-- The "or" rule: `{j, k}` is an estimated edge when one lies in the other's estimated
neighbourhood. -/
def orRuleEdge {p : ℕ} (B : Fin p → Fin p → ℝ) (j k : Fin p) : Prop :=
  j ≠ k ∧ (B j k ≠ 0 ∨ B k j ≠ 0)

/-- GAPS 103.53, neighbourhood selection: with universal constants, under incoherence, the
row-sum bound, unit-bounded variances, maximal degree `m`, and `n ≥ c₁ m log p`, the "or" rule
includes no false edge and the "and" rule includes every edge with
`|Θ j k| ≥ 7 b λ max (Θ j j) (Θ k k)`, with the stated probability; since the "and" edges are
"or" edges, both rules have both properties. The edge condition bounds the regression
coefficients `-Θ j k / Θ j j` and `-Θ k j / Θ k k` below by `7 b λ`; this is the bound proved by
Wainwright (2019), Theorem 11.12, whose statement puts `|Θ j k|` in its place although `Θ j j ≥ 1`
is not bounded above. The lasso estimates `B x j` are arbitrary minimizers. -/
theorem neighbourhoodSelection_graph_recovery :
    ∃ c₀ > (0 : ℝ), ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∃ c₃ > (0 : ℝ),
      ∀ (p n m : ℕ), 0 < n → c₁ * m * Real.log p ≤ n →
      ∀ Sig : Matrix (Fin p) (Fin p) ℝ, Sig.PosDef → (∀ j, Sig j j ≤ 1) →
      (∀ j, (precisionNeighbourhood Sig⁻¹ j).card ≤ m) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ b : ℝ, 1 ≤ b →
      (∀ j, IsIncoherentAt Sig (precisionNeighbourhood Sig⁻¹ j) j α) →
      (∀ j, RowSumNormLE (principalSubmatrix Sig (precisionNeighbourhood Sig⁻¹ j))⁻¹ b) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ B : (Fin n → EuclideanSpace ℝ (Fin p)) → Fin p → Fin p → ℝ,
      (∀ x j, IsNodeLassoEstimate x j (c₀ / α * (Real.sqrt (Real.log p / n) + δ)) (B x j)) →
      1 - c₂ * Real.exp (-(c₃ * n * min (δ ^ 2) (1 / m))) ≤
        (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 Sig).real
          {x | ∀ j k, (orRuleEdge (B x) j k → Sig⁻¹ j k ≠ 0) ∧
            (j ≠ k → 7 * b * (c₀ / α * (Real.sqrt (Real.log p / n) + δ)) *
                max (Sig⁻¹ j j) (Sig⁻¹ k k) ≤ |Sig⁻¹ j k| →
              andRuleEdge (B x) j k)} := by
  sorry

/-- The second-moment matrix `n⁻¹ ∑ xᵢ xᵢᵀ` of a centered sample. -/
def centeredSampleCovariance {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k ↦ (∑ i, x i j * x i k) / n

/-- The graphical lasso objective `tr(Θ S) - log det Θ + λ ∑_{j ≠ k} |Θ j k|`. -/
def graphicalLassoObjective {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (lambda : ℝ)
    (Θ : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (Θ * S).trace - Real.log Θ.det + lambda * ∑ j, ∑ k, if j = k then 0 else |Θ j k|

/-- `Θ` is a graphical lasso estimate: a positive definite minimizer of the objective. -/
def IsGraphicalLassoEstimate {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (lambda : ℝ)
    (Θ : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Θ.PosDef ∧ ∀ Θ' : Matrix (Fin p) (Fin p) ℝ, Θ'.PosDef →
    graphicalLassoObjective S lambda Θ ≤ graphicalLassoObjective S lambda Θ'

/-- GAPS 103.53, graphical lasso: the Frobenius error bound under `σ`-sub-Gaussian centered
coordinates and at most `m` nonzero entries per row of `Θ = Σ⁻¹`. The estimator `T x` is
required to be a graphical lasso estimate whenever one exists; the operator norm is the
Euclidean one. -/
theorem graphicalLasso_frobenius_error_bound {p n : ℕ} (hn : 0 < n)
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P] (σ : ℝ≥0)
    (hsub : ∀ j, HasSubgaussianMGF (fun x ↦ x j) (σ ^ 2) P)
    (hcov : (euclideanCovarianceMatrix P).PosDef) (m : ℕ)
    (hrow : ∀ j, (Finset.univ.filter fun k ↦ (euclideanCovarianceMatrix P)⁻¹ j k ≠ 0).card ≤ m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (lambda : ℝ)
    (hlambda : lambda = 8 * (σ : ℝ) ^ 2 * (Real.sqrt (Real.log p / n) + δ))
    (hside : 6 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P)⁻¹‖ + 1) ^ 2 *
      lambda * Real.sqrt (m * p) < 1)
    (T : (Fin n → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) (Fin p) ℝ)
    (hT : ∀ x, (∃ Θ, IsGraphicalLassoEstimate (centeredSampleCovariance x) lambda Θ) →
      IsGraphicalLassoEstimate (centeredSampleCovariance x) lambda (T x)) :
    1 - 8 * Real.exp (-(n * δ ^ 2 / 16)) ≤
      (Measure.pi fun _ : Fin n ↦ P).real
        {x | ∑ j, ∑ k, (T x j k - (euclideanCovarianceMatrix P)⁻¹ j k) ^ 2 ≤
          9 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P)⁻¹‖ + 1) ^ 4 *
            m * p * lambda ^ 2} := by
  sorry

end CKSD
