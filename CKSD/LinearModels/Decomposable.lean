module

public import CKSD.LinearModels.DirectedGraphical
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decomposable graphical models

Undirected graphs are Mathlib's `SimpleGraph`. A graph is chordal when every cycle of length at
least four has a chord. A perfect sequence lists the maximal cliques `C₀, …, C_{k-1}` so that
each separator `S_j = C_j ∩ (C₀ ∪ ⋯ ∪ C_{j-1})`, `j ≥ 1`, lies in an earlier clique; separators
are then counted with their multiplicities `ν(S)` by running over `j`.

The factorization statement is in the discrete form, for a positive probability mass function
on finitely many finite-valued variables, with the marginal masses of
`CKSD.LinearModels.DirectedGraphical`. The Gaussian statements concern the deterministic
maximization of the Gaussian likelihood of a concentration matrix. Source: GAPS 105.36.
-/

@[expose] public section

noncomputable section

open Set Matrix
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {V S : Type*}

/-- A chordal (decomposable) graph: every cycle of length at least four has a chord, an edge
between two vertices of the cycle that are not consecutive on it. -/
def IsChordalGraph (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ i j, i + 1 < j ∧ j < c.length ∧ ¬ (i = 0 ∧ j + 1 = c.length) ∧
      G.Adj (c.getVert i) (c.getVert j)

/-- `S` separates `A` from `B` in an undirected graph: every walk from `A` to `B` meets `S`. -/
def GraphSeparates (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ w : G.Walk a b, ∃ v ∈ w.support, v ∈ S

/-- The separator `C_j ∩ (C₀ ∪ ⋯ ∪ C_{j-1})` of a sequence of cliques. -/
def cliqueSeparator {k : ℕ} (C : Fin k → Finset V) (j : Fin k) : Finset V :=
  C j ∩ (Finset.univ.filter fun i : Fin k ↦ i < j).biUnion C

/-- A perfect sequence of the maximal cliques of `G`: every maximal clique occurs exactly once,
and each separator is contained in an earlier clique. -/
def IsPerfectCliqueSequence (G : SimpleGraph V) {k : ℕ} (C : Fin k → Finset V) :
    Prop :=
  Function.Injective C ∧ (∀ j, Maximal G.IsClique (C j : Set V)) ∧
    (∀ D : Finset V, Maximal G.IsClique (D : Set V) → ∃ j, C j = D) ∧
    ∀ j : Fin k, 0 < (j : ℕ) → ∃ i < j, cliqueSeparator C j ⊆ C i

/-- The undirected global Markov property for a probability mass function: separation of
disjoint sets implies conditional independence. -/
def IsUndirectedGlobalMarkovMass [Fintype V] [Fintype S] (G : SimpleGraph V)
    (p : (V → S) → ℝ) : Prop :=
  ∀ A B C : Finset V, Disjoint A B → Disjoint A C → Disjoint B C →
    GraphSeparates G A B C → CondIndepMass p A B C

/-- GAPS 105.36, discrete form: for a decomposable graph with a perfect sequence of its maximal
cliques, a positive probability mass function is globally Markov exactly when
`p(x) = ∏_C p_C(x_C) / ∏_S p_S(x_S)^{ν(S)}`, written here without division. -/
theorem isUndirectedGlobalMarkovMass_iff_clique_factorization [Fintype V] [Fintype S]
    (G : SimpleGraph V) (hG : IsChordalGraph G) {k : ℕ} (C : Fin k → Finset V)
    (hC : IsPerfectCliqueSequence G C) (p : (V → S) → ℝ) (hp : IsProbabilityMass p)
    (hpos : ∀ x, 0 < p x) :
    IsUndirectedGlobalMarkovMass G p ↔
      ∀ x, p x * ∏ j : Fin k, (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) =
        ∏ j, marginalMass p (C j) x := by
  sorry

/-- The block `B_{CC}` of a square matrix indexed by a finite set `C` of coordinates. -/
def principalBlock {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (C : Finset (Fin p)) :
    Matrix C C ℝ :=
  B.submatrix Subtype.val Subtype.val

/-- `[B]^V`: a matrix indexed by `C`, padded with zeros to a `p × p` matrix. -/
def padBlock {p : ℕ} (C : Finset (Fin p)) (B : Matrix C C ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ if h : i ∈ C ∧ j ∈ C then B ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The Gaussian log likelihood of a concentration matrix `K` for `n` observations with centred
sum-of-squares matrix `ssd`, up to an additive constant and the factor `n / 2`:
`log det K - tr(K ssd) / n`. -/
def gaussianConcentrationLogLikelihood {p : ℕ} (n : ℕ) (ssd K : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Real.log K.det - Matrix.trace (K * ssd) / n

/-- Concentration matrices of the Gaussian graphical model of `G`: positive definite with zero
entries off the edges. -/
def concentrationModel {p : ℕ} (G : SimpleGraph (Fin p)) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {K | K.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → K i j = 0}

/-- GAPS 105.36, Gaussian decomposable model: if every clique block of `ssd` is positive
definite (which holds almost surely when `n > max_C |C|` for a Gaussian sample), the maximum
likelihood estimator of the concentration matrix exists, is unique, and equals
`n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`. The almost-sure existence criterion
`n > max_C |C|` as a necessary condition is not stated. -/
theorem isGreatest_gaussianConcentrationLogLikelihood_decomposable {p : ℕ}
    (G : SimpleGraph (Fin p)) (hG : IsChordalGraph G) {k : ℕ} (C : Fin k → Finset (Fin p))
    (hC : IsPerfectCliqueSequence G C) (n : ℕ) (hn : 0 < n) (ssd : Matrix (Fin p) (Fin p) ℝ)
    (hssd : ssd.PosSemidef) (hblock : ∀ j, (principalBlock ssd (C j)).PosDef) :
    let K := (n : ℝ) • (∑ j, padBlock (C j) (principalBlock ssd (C j))⁻¹ -
      ∑ j : Fin k, if (j : ℕ) = 0 then 0 else
        padBlock (cliqueSeparator C j) (principalBlock ssd (cliqueSeparator C j))⁻¹)
    K ∈ concentrationModel G ∧
      ∀ K' ∈ concentrationModel G, K' ≠ K →
        gaussianConcentrationLogLikelihood n ssd K' <
          gaussianConcentrationLogLikelihood n ssd K := by
  sorry

/-- GAPS 105.36, general graph: if `ssd` is positive definite, there is a unique positive
definite `Σ̂` that agrees with `ssd / n` on the diagonal and on the edges and whose inverse
vanishes off the edges, and `Σ̂⁻¹` is the unique maximizer of the likelihood over the
concentration model. Convergence of iterative proportional scaling is not stated. -/
theorem existsUnique_gaussianConcentration_mle {p : ℕ} (G : SimpleGraph (Fin p)) (n : ℕ)
    (hn : 0 < n) (ssd : Matrix (Fin p) (Fin p) ℝ) (hssd : ssd.PosDef) :
    ∃! Sig : Matrix (Fin p) (Fin p) ℝ, Sig.PosDef ∧
      (∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n) ∧
      (∀ i j, i ≠ j → ¬ G.Adj i j → Sig⁻¹ i j = 0) ∧
      ∀ K ∈ concentrationModel G, K ≠ Sig⁻¹ →
        gaussianConcentrationLogLikelihood n ssd K <
          gaussianConcentrationLogLikelihood n ssd Sig⁻¹ := by
  sorry

end CKSD
