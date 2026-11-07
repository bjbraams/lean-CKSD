module

public import CKSD.Geometry.Persistence
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Topology.MetricSpace.GromovHausdorff
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Sublevel persistence of monotone functions on finite simplicial complexes

A finite simplicial complex is a Mathlib `PreAbstractSimplicialComplex` on a finite, linearly
ordered vertex type; the order orients simplices. Chains with coefficients in a field `𝕜` are
functions on finite vertex sets, and the boundary is the alternating deleted-vertex sum. For a
function `f` on simplices that is monotone along faces, the sublevel subcomplexes `K_a` form a
filtration, and the persistent Betti number in degree `p` is the rank
`dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))` of the map `H_p(K_a) → H_p(K_b)`.

A persistence diagram of the filtration in degree `p` is described by its finite bars `[b, d)`
(a `FiniteDeathDiagram`, zero-length bars discarded) and the births of its essential bars
`[b, ∞)`, subject to the requirement that for `a ≤ b` the persistent Betti number counts the bars
containing `[a, b]`. The rank invariant determines the diagram, so this pins down the diagram up
to reindexing.

Full diagrams are compared by matching finite bars partially (unmatched points go to the
diagonal) and essential bars bijectively, in the bottleneck and in the `q`-Wasserstein sense.

The Rips filtration of a finite metric space is the monotone function `σ ↦ diam σ / 2` on the full
simplex, in the diameter-`2r` convention of GAPS 108.21.

Sources: GAPS 108.19, 108.35, 108.36.
-/

@[expose] public section

noncomputable section

open Module Set
open scoped ENNReal NNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

section Chains

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

/-- Signed incidence number of the face `τ` in the simplex `σ`: nonzero exactly when `τ` is a
nonempty codimension-one face, with sign `(-1)^k` where the deleted vertex is the `k`th vertex of
`σ` in increasing order (counting from `0`). -/
def simplexIncidence (τ σ : Finset ι) : 𝕜 :=
  if τ.Nonempty ∧ τ ⊆ σ ∧ τ.card + 1 = σ.card then
    (-1) ^ (σ.filter fun w ↦ ∃ v ∈ σ \ τ, w < v).card
  else 0

/-- The simplicial boundary on chains, which are functions on finite vertex sets. Vertices have
zero boundary (no augmentation). -/
def simplicialBoundary : (Finset ι → 𝕜) →ₗ[𝕜] (Finset ι → 𝕜) :=
  (Matrix.of fun τ σ : Finset ι ↦ simplexIncidence 𝕜 τ σ).mulVecLin

/-- A function on simplices is monotone along faces of `K`. -/
def IsMonotoneOnFaces (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) : Prop :=
  ∀ τ σ, σ ∈ K → τ.Nonempty → τ ⊆ σ → f τ ≤ f σ

/-- Chains of dimension `p` of the sublevel subcomplex `K_a = {σ ∈ K : f σ ≤ a}`. -/
def sublevelChains (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ) (a : ℝ) :
    Submodule 𝕜 (Finset ι → 𝕜) where
  carrier := {c | ∀ σ, c σ ≠ 0 → σ ∈ K ∧ σ.card = p + 1 ∧ f σ ≤ a}
  zero_mem' := by simp
  add_mem' := by
    intro c c' hc hc' σ hσ
    by_cases h : c σ = 0
    · exact hc' σ (by simpa [h] using hσ)
    · exact hc σ h
  smul_mem' := by
    intro r c hc σ hσ
    exact hc σ (right_ne_zero_of_mul (by simpa using hσ))

/-- Cycles of dimension `p` of `K_a`. -/
def sublevelCycles (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ) (a : ℝ) :
    Submodule 𝕜 (Finset ι → 𝕜) :=
  sublevelChains 𝕜 K f p a ⊓ LinearMap.ker (simplicialBoundary 𝕜)

/-- Boundaries of dimension `p` of `K_b`. -/
def sublevelBoundaries (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (b : ℝ) : Submodule 𝕜 (Finset ι → 𝕜) :=
  (sublevelChains 𝕜 K f (p + 1) b).map (simplicialBoundary 𝕜)

/-- Persistent Betti number: the rank of `H_p(K_a) → H_p(K_b)`, computed as
`dim Z_p(K_a) - dim (Z_p(K_a) ∩ B_p(K_b))`. -/
def sublevelPersistentBetti (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (a b : ℝ) : ℕ :=
  finrank 𝕜 (sublevelCycles 𝕜 K f p a) -
    finrank 𝕜 ↥(sublevelCycles 𝕜 K f p a ⊓ sublevelBoundaries 𝕜 K f p b)

/-- The persistent homology group in degree `p`, the image of `H_p(K_a) → H_p(K_b)`, realized
as `Z_p(K_a) / (Z_p(K_a) ∩ B_p(K_b))`. -/
abbrev sublevelPersistentHomology (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    (a b : ℝ) : Type _ :=
  ↥(sublevelCycles 𝕜 K f p a) ⧸
    (sublevelBoundaries 𝕜 K f p b).comap (sublevelCycles 𝕜 K f p a).subtype

/-- `(D, e)` is the degree-`p` persistence diagram of the sublevel filtration of `f`: finite bars
`[D.birth i, D.death i)` and essential bars `[e k, ∞)`, such that for `a ≤ b` the persistent
Betti number counts the bars containing `[a, b]`. -/
def IsSublevelDiagram (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ) (p : ℕ)
    {α κ : Type*} [Fintype α] [Fintype κ] (D : FiniteDeathDiagram α) (e : κ → ℝ) : Prop :=
  ∀ a b, a ≤ b → sublevelPersistentBetti 𝕜 K f p a b =
    (Finset.univ.filter fun i ↦ D.birth i ≤ a ∧ b < D.death i).card +
      (Finset.univ.filter fun k ↦ e k ≤ a).card

/-- GAPS 108.18, finite sublevel form: persistence diagrams of monotone sublevel filtrations of
finite simplicial complexes exist. This is the interval decomposition of the finite-type
persistence module `a ↦ H_p(K_a)`, read through its rank invariant. -/
theorem exists_isSublevelDiagram (K : PreAbstractSimplicialComplex ι) (f : Finset ι → ℝ)
    (hf : IsMonotoneOnFaces K f) (p : ℕ) :
    ∃ (n r : ℕ) (D : FiniteDeathDiagram (Fin n)) (e : Fin r → ℝ), IsSublevelDiagram 𝕜 K f p D e := by
  sorry

end Chains

section Distances

/-- Bottleneck distance between essential parts: the best bijection of essential births, and
`∞` when the numbers of essential bars differ. -/
def essentialBottleneckEDist {κ κ' : Type*} (e : κ → ℝ) (e' : κ' → ℝ) : ℝ≥0∞ :=
  ⨅ σ : κ ≃ κ', ⨆ k, ENNReal.ofReal |e k - e' (σ k)|

/-- Bottleneck distance between full diagrams with finite parts `D, E` and essential parts
`e, e'`. Finite and essential points are at infinite distance, so the two parts are matched
separately. -/
def fullBottleneckEDist {α β κ κ' : Type*} (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  max (bottleneckEDist D E) (essentialBottleneckEDist e e')

/-- `q`-th power cost of a partial matching of finite parts together with a bijection of essential
parts, with `ℓ^∞` distances between matched points and distance `(d - b)/2` of an unmatched point
to the diagonal. -/
def diagramWassersteinCost {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (M : DiagramMatching α β) (σ : κ ≃ κ') (D : FiniteDeathDiagram α) (e : κ → ℝ)
    (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  (∑ i, (if h : ∃ j, M.relates i j then
      ENNReal.ofReal (max |D.birth i - E.birth h.choose| |D.death i - E.death h.choose|)
    else ENNReal.ofReal ((D.death i - D.birth i) / 2)) ^ q) +
  (∑ j, (if ∃ i, M.relates i j then 0 else ENNReal.ofReal ((E.death j - E.birth j) / 2)) ^ q) +
  ∑ k, ENNReal.ofReal |e k - e' (σ k)| ^ q

/-- The `q`-Wasserstein distance between full persistence diagrams, `∞` when the numbers of
essential bars differ. -/
def diagramWassersteinEDist {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] (q : ℝ)
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ) : ℝ≥0∞ :=
  ⨅ M : DiagramMatching α β, ⨅ σ : κ ≃ κ', diagramWassersteinCost q M σ D e E e' ^ (1 / q)

end Distances

section Stability

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (𝕜 : Type*) [Field 𝕜]

/-- GAPS 108.19, simplicial form: for monotone functions `f, g` on the simplices of a finite
simplicial complex, the degree-`p` persistence diagrams of the sublevel filtrations (finite and
essential parts) are within bottleneck distance `‖f - g‖_∞ = max_{σ ∈ K} |f σ - g σ|`. The
statement for tame functions on triangulable spaces, with singular homology of sublevel sets,
is not formalized; for piecewise-linear functions it reduces to this case. -/
theorem fullBottleneckEDist_le_of_isSublevelDiagram (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (δ : ℝ) (hδ : ∀ σ ∈ K, |f σ - g σ| ≤ δ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal δ := by
  sorry

/-- GAPS 108.35, the finite-complex clause: for monotone functions `f, g` on the simplices of a
finite simplicial complex `K` and `1 ≤ q < ∞`, the `q`-Wasserstein distance between the full
degree-`p` diagrams is at most `(∑_{σ ∈ K} |f σ - g σ|^q)^{1/q}`. The clauses for tame Lipschitz
functions on triangulable spaces with polynomially growing triangulations are not formalized. -/
theorem diagramWassersteinEDist_le_of_isSublevelDiagram
    (K : PreAbstractSimplicialComplex ι)
    (f g : Finset ι → ℝ) (hf : IsMonotoneOnFaces K f) (hg : IsMonotoneOnFaces K g) (p : ℕ)
    (q : ℝ) (hq : 1 ≤ q)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 K f p D e) (hE : IsSublevelDiagram 𝕜 K g p E e') :
    diagramWassersteinEDist q D e E e' ≤
      (∑ σ ∈ Finset.univ.filter (· ∈ K), ENNReal.ofReal |f σ - g σ| ^ q) ^ (1 / q) := by
  sorry

/-- The full simplex on a finite vertex type: all nonempty vertex sets. -/
def fullSimplexComplex (X : Type*) : PreAbstractSimplicialComplex X := ⊤

/-- The Rips filtration value of a simplex in the diameter-`2r` convention: `σ ∈ Rips(r)` exactly
when `diam σ ≤ 2r`. -/
def ripsFiltrationValue {X : Type*} [PseudoMetricSpace X] (σ : Finset X) : ℝ :=
  Metric.diam (σ : Set X) / 2

/-- GAPS 108.36, for finite metric spaces: the degree-`p` persistence diagrams of the Rips
filtrations of two nonempty finite metric spaces, in the diameter-`2r` parameter, are within
bottleneck distance `d_GH(X, Y)`. In the maximum-edge parameter the filtration values double, and
the bound becomes `2 d_GH(X, Y)`. The linear orders on the points only orient simplices. Totally
bounded spaces (where `q`-tameness is needed) and the Čech variants are not formalized. -/
theorem fullBottleneckEDist_rips_le_ghDist {X Y : Type*} [MetricSpace X] [Fintype X] [Nonempty X]
    [LinearOrder X] [MetricSpace Y] [Fintype Y] [Nonempty Y] [LinearOrder Y] (p : ℕ)
    {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype κ']
    (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (hD : IsSublevelDiagram 𝕜 (fullSimplexComplex X) ripsFiltrationValue p D e)
    (hE : IsSublevelDiagram 𝕜 (fullSimplexComplex Y) ripsFiltrationValue p E e') :
    fullBottleneckEDist D e E e' ≤ ENNReal.ofReal (GromovHausdorff.ghDist X Y) := by
  sorry

/-- Diameters are monotone, so the Rips filtration is a monotone filtration of the full simplex. -/
theorem isMonotoneOnFaces_ripsFiltrationValue {X : Type*} [PseudoMetricSpace X] [Fintype X]
    [LinearOrder X] : IsMonotoneOnFaces (fullSimplexComplex X) (ripsFiltrationValue (X := X)) := by
  intro τ σ _ _ hτσ
  unfold ripsFiltrationValue
  gcongr
  exact Metric.diam_mono (by exact_mod_cast hτσ) σ.finite_toSet.isBounded

end Stability

end CKSD
