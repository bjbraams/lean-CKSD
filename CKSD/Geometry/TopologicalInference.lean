module

public import CKSD.Geometry.PersistenceModules
public import CKSD.Geometry.SimplicialPersistence.Stability
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.Convex.Hull

/-!
# Topological inference: reach, weak feature size, and Morse persistence

Singular homology with coefficients in a field is TauCeti's simplicial singular chain complex
functor followed by homology; maps induced by continuous maps are
`ContinuousMap.singularHomologyMap`. Offsets of a set `P` are closed thickenings
`P^r = {x : d(x, P) ≤ r}`.

A compact smooth submanifold of `ℝ^D` without boundary is the image of a smooth embedding of a
compact boundaryless smooth manifold modeled on `ℝ^d`. The reach of a set is the supremum of the
radii `r` such that every point at distance less than `r` has a unique nearest point in the set.

Sources: GAPS 108.22, 108.34, 108.37.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric CategoryTheory
open scoped ENNReal NNReal Manifold ContDiff Topology

namespace CKSD

attribute [local instance] Classical.propDecidable

section Homology

universe u

/-- Degree-`n` singular homology of a topological space with coefficients in `k`. -/
abbrev singularHomologyModule (k : Type u) [Ring k] (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} k :=
  ((TauCeti.singularChains k).obj (TopCat.of X)).homology n

/-- The filtration of a space by the sublevel sets `{f ≤ t}` of a real function, as a functor
from `ℝ` to topological spaces. -/
def sublevelSetFunctor {X : Type u} [TopologicalSpace X] (f : X → ℝ) : ℝ ⥤ TopCat.{u} where
  obj t := TopCat.of {x | f x ≤ t}
  map {s t} h := TopCat.ofHom (ContinuousMap.inclusion fun _ hx ↦ le_trans hx h.le)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The sublevel persistence module `t ↦ H_n({f ≤ t}; k)` of a real function. -/
def sublevelHomologyModule (k : Type u) [Field k] (n : ℕ) {X : Type u} [TopologicalSpace X]
    (f : X → ℝ) : PersistenceModule k :=
  sublevelSetFunctor f ⋙ TauCeti.singularChains k ⋙ HomologicalComplex.homologyFunctor _ _ n

end Homology

section Euclidean

variable {D : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The reach of a set: the supremum of the radii `r` such that every point at distance less than
`r` from the set has a unique nearest point in it. -/
def reach (S : Set E) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : ∀ x, infDist x S < r → ∃! y, y ∈ S ∧ dist x y = infDist x S), (r : ℝ≥0∞)

/-- A point outside `K` is critical for the distance function to `K` when it lies in the convex
hull of its nearest points in `K`. -/
def IsDistanceCriticalPoint (K : Set E) (x : E) : Prop :=
  x ∉ K ∧ x ∈ convexHull ℝ {y | y ∈ K ∧ dist x y = infDist x K}

/-- The weak feature size: the infimum of the positive critical values of the distance function,
`∞` when there are none. -/
def weakFeatureSize (K : Set E) : ℝ≥0∞ :=
  ⨅ (x : E) (_ : IsDistanceCriticalPoint K x) (_ : 0 < infDist x K), ENNReal.ofReal (infDist x K)

/-- Inclusion of offsets of a set. -/
def offsetInclusion (P : Set E) {i j : ℝ} (h : i ≤ j) : C(cthickening i P, cthickening j P) :=
  ContinuousMap.inclusion (cthickening_mono h P)

/-- GAPS 108.22, deformation retraction of offsets. Let `M = j(N) ⊂ ℝ^D` be a compact smooth
`d`-dimensional submanifold without boundary with reach at least `τ > 0`, and `P ⊆ M` finite and nonempty with
`d_H(P, M) = ε < √(3/20) τ`. For `r ∈ (2ε, √(3/5) τ)` the offset `P^r` contains `M` and strongly
deformation retracts onto it. By the nerve theorem the Čech complex of radius `r` then has the
homotopy type of `M`; the nerve theorem is not part of this statement. -/
theorem exists_deformationRetraction_offset_of_hausdorffDist_lt
    {d : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    [IsManifold (𝓡 d) ∞ N] [CompactSpace N] {j : N → E}
    (hj : Manifold.IsSmoothEmbedding (𝓡 d) 𝓘(ℝ, E) ∞ j)
    (τ : ℝ) (hτ : 0 < τ) (hreach : ENNReal.ofReal τ ≤ reach (range j))
    (P : Finset E) (hP : P.Nonempty) (hPM : (P : Set E) ⊆ range j) (ε : ℝ)
    (hε : hausdorffDist (P : Set E) (range j) = ε) (hετ : ε < Real.sqrt (3 / 20) * τ)
    (r : ℝ) (hr : r ∈ Ioo (2 * ε) (Real.sqrt (3 / 5) * τ)) :
    ∃ hM : range j ⊆ cthickening r (P : Set E), ∃ ρ : C(cthickening r (P : Set E), range j),
      (∀ x, ρ (inclusion hM x) = x) ∧
      (ContinuousMap.id _).HomotopicRel ((ContinuousMap.inclusion hM).comp ρ)
        (range (inclusion hM)) := by
  sorry

/-- GAPS 108.22, the sampling bound. Let `M = j(N) ⊂ ℝ^D` be a compact smooth `d`-dimensional
submanifold without boundary and `c > 0`. There are `C, ε₀ > 0` such that for every law `μ`
concentrated on `M` with density at least `c` with respect to the `d`-dimensional Hausdorff
measure on `M` (the Riemannian volume), all `ε ∈ (0, ε₀)`, `δ ∈ (0, 1)` and
`n ≥ C ε^{-d} (log(1/ε) + log(1/δ))`, an independent sample of size `n` is `ε`-close to `M` in
Hausdorff distance with probability at least `1 - δ`. -/
theorem exists_sample_size_hausdorffDist_le
    {d : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    [IsManifold (𝓡 d) ∞ N] [CompactSpace N] {j : N → E}
    (hj : Manifold.IsSmoothEmbedding (𝓡 d) 𝓘(ℝ, E) ∞ j) (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ μ : Measure E, IsProbabilityMeasure μ → μ (range j)ᶜ = 0 →
      (∀ s, MeasurableSet s → ENNReal.ofReal c * μH[d] (s ∩ range j) ≤ μ s) →
      ∀ ε ∈ Ioo 0 ε₀, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ,
        C * ε ^ (-(d : ℝ)) * (Real.log (1 / ε) + Real.log (1 / δ)) ≤ n →
        1 - δ ≤ (Measure.pi fun _ : Fin n ↦ μ).real
          {x | hausdorffDist (range x) (range j) ≤ ε} := by
  sorry

/-- GAPS 108.37, offsets: let `K ⊂ ℝ^D` be compact and nonempty with weak feature size at least
`τ > 0`, and `P` finite and nonempty with `d_H(K, P) = ε < τ/4`. If `ε < i` and
`i + 2ε ≤ j < τ - ε`, the image of `H_n(P^i) → H_n(P^j)` is isomorphic to `H_n(K^r)` for every
`r ∈ (0, τ)`, in every degree `n` and over every field. Taking `τ = wfs(K)` when it is finite
gives the source statement. The Čech-complex form follows by the nerve theorem and is not stated
separately. -/
theorem nonempty_range_offsetHomology_equiv_of_weakFeatureSize (k : Type) [Field k]
    (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty) (τ : ℝ) (hτ : 0 < τ)
    (hwfs : ENNReal.ofReal τ ≤ weakFeatureSize K) (P : Finset E) (hPne : (P : Set E).Nonempty)
    (ε : ℝ) (hε : hausdorffDist K P = ε) (hετ : ε < τ / 4) (i j : ℝ) (hi : ε < i)
    (hij : i + 2 * ε ≤ j) (hj : j < τ - ε) (hle : i ≤ j) (r : ℝ) (hr : r ∈ Ioo 0 τ) (n : ℕ) :
    Nonempty (LinearMap.range (ContinuousMap.singularHomologyMap k n
      (offsetInclusion (P : Set E) hle)) ≃ₗ[k] singularHomologyModule k n (cthickening r K)) := by
  sorry

/-- The Rips filtration of a finite indexed sample, in the diameter-`2r` convention. -/
def sampleRipsFiltrationValue {N : ℕ} (x : Fin N → E) (σ : Finset (Fin N)) : ℝ :=
  Metric.diam (x '' σ) / 2

/-- GAPS 108.37, Rips complexes: let `K ⊂ ℝ^D` be compact and nonempty with weak feature size at
least `τ > 0`, and `x` a finite sample with `d_H(K, {x_i}) < ε` for some `ε < τ/9`. If
`2ε ≤ α ≤ (τ - ε)/4`, the image of `H_n(Rips(α/2)) → H_n(Rips(2α))` (diameter-`2r` parameter,
simplicial homology over a field) is isomorphic to `H_n(K^r)` for every `r ∈ (0, τ)`. -/
theorem nonempty_ripsPersistentHomology_equiv_of_weakFeatureSize (k : Type) [Field k]
    (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty) (τ : ℝ) (hτ : 0 < τ)
    (hwfs : ENNReal.ofReal τ ≤ weakFeatureSize K) {N : ℕ} (hN : 0 < N) (x : Fin N → E)
    (ε : ℝ) (hε : hausdorffDist K (range x) < ε) (hετ : ε < τ / 9) (α : ℝ) (hα : 2 * ε ≤ α)
    (hατ : α ≤ (τ - ε) / 4) (r : ℝ) (hr : r ∈ Ioo 0 τ) (n : ℕ) :
    Nonempty (sublevelPersistentHomology k (fullSimplexComplex (Fin N))
      (sampleRipsFiltrationValue x) n (α / 2) (2 * α) ≃ₗ[k]
        singularHomologyModule k n (cthickening r K)) := by
  sorry

end Euclidean

section Morse

variable {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M] [CompactSpace M]

variable (m) in
/-- Critical points of a real function on a manifold modeled on `ℝ^m`: the points where the
manifold derivative vanishes. -/
def manifoldCriticalPoints (f : M → ℝ) : Set M :=
  {x | mfderiv (𝓡 m) 𝓘(ℝ, ℝ) f x = 0}

variable (m) in
/-- The number of critical points of Morse index `q`, in `ℕ∞`. -/
def manifoldCriticalCount (f : M → ℝ) (q : ℕ) : ℕ∞ :=
  {x ∈ manifoldCriticalPoints m f | TauCeti.manifoldMorseIndex (𝓡 m) f x = q}.encard

/-- GAPS 108.34, diagrams of the sublevel persistence of a Morse function. Let `f` be a Morse
function with distinct critical values on a closed smooth `m`-manifold and `k` a field, and for
each degree `q` let `B q` be an interval decomposition of `t ↦ H_q({f ≤ t}; k)` into finitely
many closed-open bars, finite ones `[(D q).birth i, (D q).death i)` and essential ones
`[e q i, ∞)`. Then every endpoint is a critical value; the number `c_q` of index-`q` critical
points is the number of degree-`q` bars plus the number of finite degree-`(q-1)` bars; there
are exactly `β_q(M)` essential degree-`q` bars; and each critical value is an endpoint of exactly
one bar. The homotopy-theoretic description (cell attachment at critical values) is not
restated. -/
theorem sublevelHomologyModule_bars_of_isMorse (k : Type) [Field k] {f : M → ℝ}
    (hf : TauCeti.IsMorse (𝓡 m) f) (hinj : InjOn f (manifoldCriticalPoints m f))
    (α κ : ℕ → Type) [∀ q, Fintype (α q)] [∀ q, Fintype (κ q)]
    (D : ∀ q, FiniteDeathDiagram (α q)) (e : ∀ q, κ q → ℝ)
    (B : ∀ q, IntervalBasis (sublevelHomologyModule k q f) (α q ⊕ κ q))
    (hB : ∀ q i, (B q).support (.inl i) = Ico ((D q).birth i) ((D q).death i))
    (hB' : ∀ q i, (B q).support (.inr i) = Ici (e q i)) :
    (∀ q i, (D q).birth i ∈ f '' manifoldCriticalPoints m f ∧
      (D q).death i ∈ f '' manifoldCriticalPoints m f) ∧
    (∀ q i, e q i ∈ f '' manifoldCriticalPoints m f) ∧
    (∀ q, manifoldCriticalCount m f q =
      (Fintype.card (α q) + Fintype.card (κ q) +
        if q = 0 then 0 else Fintype.card (α (q - 1)) : ℕ)) ∧
    (∀ q, Fintype.card (κ q) = Module.finrank k (singularHomologyModule k q M)) ∧
    ∀ x ∈ manifoldCriticalPoints m f,
      ∑ q ∈ Finset.range (m + 1),
        ((Finset.univ.filter fun i ↦ (D q).birth i = f x).card +
          (Finset.univ.filter fun i ↦ (D q).death i = f x).card +
          (Finset.univ.filter fun i ↦ e q i = f x).card) = 1 := by
  sorry

end Morse

end CKSD
