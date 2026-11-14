module

public import CKSD.Geometry.TopologicalInference
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Connected.PathConnected


/-!
# Geodesic approximation from neighbourhood graphs

The intrinsic distance of a set `M ⊆ ℝ^D` is the infimum of the lengths (total variations) of
paths in `M`. The neighbourhood graph on a finite sample joins points at Euclidean distance at
most `ε`, with edges weighted by Euclidean length; its shortest-path distance is the infimum of
lengths of walks through the sample.

The definitions are stated for a general (pseudo)metric space.

## Main definitions

* `CKSD.intrinsicEDist`: the intrinsic path-length distance of a set.
* `CKSD.IsSampleWalk`, `CKSD.walkLength`, `CKSD.sampleGraphEDist`: walks, their lengths and the
  shortest-path distance of the neighbourhood graph.

## Main results

* `CKSD.eventually_sample_graph_e_dist_intrinsic_e_dist_le`: convergence of graph geodesics on a
  submanifold of positive reach (GAPS 108.4).
* `CKSD.intrinsic_e_dist_eq_edist_of_length_preserving`: the flat case (GAPS 108.4).
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped ENNReal NNReal Manifold ContDiff Topology

namespace CKSD

variable {X : Type*}

/-- The intrinsic (path-length) distance of a set: the infimum of the lengths of paths from `x`
to `y` that stay in `M`, `∞` when there is none. -/
def intrinsicEDist [PseudoEMetricSpace X] (M : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ∀ t, γ t ∈ M), eVariationOn γ univ

/-- A walk from `x` through the sample `S` with steps of length at most `ε`, ending at `y`; the
list records the vertices after `x`. -/
def IsSampleWalk [PseudoMetricSpace X] (S : Finset X) (ε : ℝ) (x y : X) (l : List X) : Prop :=
  (∀ z ∈ l, z ∈ S) ∧ List.IsChain (fun a b ↦ dist a b ≤ ε) (x :: l) ∧
    (x :: l).getLast (List.cons_ne_nil x l) = y

/-- Euclidean length of the walk from `x` along `l`. -/
def walkLength [PseudoMetricSpace X] (x : X) (l : List X) : ℝ :=
  (((x :: l).zip l).map fun p ↦ dist p.1 p.2).sum

/-- Shortest-path distance in the `ε`-neighbourhood graph on `S` with Euclidean edge lengths,
`∞` between different components. Its graph interpretation applies to endpoints in `S`;
the definition also permits an ambient starting point outside `S`. -/
def sampleGraphEDist [PseudoMetricSpace X] (S : Finset X) (ε : ℝ) (x y : X) : ℝ≥0∞ :=
  ⨅ (l : List X) (_ : IsSampleWalk S ε x y l), ENNReal.ofReal (walkLength x l)

/-- GAPS 108.4, convergence of graph geodesics. Let `M = j(N) ⊂ ℝ^D` be a compact connected
smooth submanifold of positive reach, and let the samples `S n ⊆ M` be `δ n`-nets of `M` in its
intrinsic distance. If `ε n → 0` and `δ n / ε n → 0`, then the shortest-path distances of the
`ε n`-neighbourhood graphs converge to the intrinsic distances uniformly over pairs of sample
points: for every `η > 0`, eventually `|d_{G_n}(x, y) - d_M(x, y)| ≤ η` for all `x, y ∈ S n`
(stated as two one-sided bounds in `ℝ≥0∞`). -/
theorem eventually_sample_graph_e_dist_intrinsic_e_dist_le
    {D d : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    [IsManifold (𝓡 d) ∞ N] [CompactSpace N] [ConnectedSpace N]
    {j : N → EuclideanSpace ℝ (Fin D)}
    (hj : Manifold.IsSmoothEmbedding (𝓡 d) 𝓘(ℝ, EuclideanSpace ℝ (Fin D)) ∞ j)
    (hreach : 0 < reach (range j)) (S : ℕ → Finset (EuclideanSpace ℝ (Fin D)))
    (hS : ∀ n, (S n : Set (EuclideanSpace ℝ (Fin D))) ⊆ range j) (δ ε : ℕ → ℝ)
    (hδ : ∀ n, 0 < δ n) (hε : ∀ n, 0 < ε n)
    (hnet : ∀ n, ∀ y ∈ range j, ∃ x ∈ S n, intrinsicEDist (range j) x y ≤ ENNReal.ofReal (δ n))
    (hε0 : Tendsto ε atTop (𝓝 0)) (hδε : Tendsto (fun n ↦ δ n / ε n) atTop (𝓝 0)) :
    ∀ η > 0, ∀ᶠ n in atTop, ∀ x ∈ S n, ∀ y ∈ S n,
      sampleGraphEDist (S n) (ε n) x y ≤ intrinsicEDist (range j) x y + ENNReal.ofReal η ∧
      intrinsicEDist (range j) x y ≤ sampleGraphEDist (S n) (ε n) x y + ENNReal.ofReal η := by
  sorry

/-- GAPS 108.4, flat case. Let `φ` map `M` into a real normed space with convex image `Ω`, have a
left inverse `ψ` on `M` that is continuous on `Ω`, and preserve the lengths of paths in `M` (an
isometry for the intrinsic length structure). Then `d_M(x, y) = ‖φ x - φ y‖` on `M`.

Remark, not part of the statement: for `Ω ⊆ ℝ^d`, classical multidimensional scaling of the
squared intrinsic distances of a finite sample then returns the points `φ(x_i)` up to a Euclidean
isometry, by the Schoenberg criterion of Section 108.8. -/
theorem intrinsic_e_dist_eq_edist_of_length_preserving [PseudoEMetricSpace X] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (M : Set X) (φ : X → F) (ψ : F → X)
    (hconv : Convex ℝ (φ '' M)) (hψφ : ∀ x ∈ M, ψ (φ x) = x)
    (hψ : ContinuousOn ψ (φ '' M))
    (hlen : ∀ x y (γ : Path x y), (∀ t, γ t ∈ M) → eVariationOn (φ ∘ γ) univ = eVariationOn γ univ)
    {x y : X} (hx : x ∈ M) (hy : y ∈ M) :
    intrinsicEDist M x y = edist (φ x) (φ y) := by
  set Ω := φ '' M
  have hψM : ∀ z ∈ Ω, ψ z ∈ M ∧ φ (ψ z) = z := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨by rw [hψφ m hm]; exact hm, by rw [hψφ m hm]⟩
  apply le_antisymm
  · -- the lifted straight segment is a path in `M` of length at most `‖φ y - φ x‖`
    set a := φ x
    set v := φ y - φ x
    let seg : unitInterval → F := fun t ↦ a + (t : ℝ) • v
    have hseg : ∀ t, seg t ∈ Ω := fun t ↦
      hconv.add_smul_sub_mem (mem_image_of_mem φ hx) (mem_image_of_mem φ hy) t.2
    have hsegc : Continuous seg := by fun_prop
    let γ : Path x y :=
      { toFun := fun t ↦ ψ (seg t)
        continuous_toFun := hψ.comp_continuous hsegc hseg
        source' := by simp [seg, a, hψφ x hx]
        target' := by simp [seg, a, v, hψφ y hy] }
    have hγM : ∀ t, γ t ∈ M := fun t ↦ (hψM _ (hseg t)).1
    have hφγ : φ ∘ γ = seg := funext fun t ↦ (hψM _ (hseg t)).2
    have hlip : LipschitzOnWith ‖v‖₊ (fun r : ℝ ↦ a + r • v) univ := by
      refine (LipschitzWith.of_dist_le_mul fun r r' ↦ ?_).lipschitzOnWith
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm,
        Real.dist_eq]
      simp
    have hvar : eVariationOn seg univ ≤ ‖v‖₊ := by
      have h1 := hlip.comp_eVariationOn_le (g := fun t : unitInterval ↦ (t : ℝ))
        (s := univ) (mapsTo_univ _ _)
      have h2 : eVariationOn (fun t : unitInterval ↦ (t : ℝ)) univ ≤ 1 := by
        have hmono : MonotoneOn (fun t : unitInterval ↦ (t : ℝ)) univ :=
          fun _ _ _ _ h ↦ h
        have := hmono.eVariationOn_eq (a := 0) (b := 1) (mem_univ _) (mem_univ _)
        have hIcc : (univ : Set unitInterval) ∩ Icc 0 1 = univ := by
          ext t; simpa using unitInterval.le_one' (t := t)
        rw [hIcc] at this
        rw [this]
        simp
      calc eVariationOn seg univ = eVariationOn ((fun r : ℝ ↦ a + r • v) ∘
            fun t : unitInterval ↦ (t : ℝ)) univ := rfl
        _ ≤ ‖v‖₊ * eVariationOn (fun t : unitInterval ↦ (t : ℝ)) univ := h1
        _ ≤ ‖v‖₊ * 1 := by gcongr
        _ = ‖v‖₊ := mul_one _
    calc intrinsicEDist M x y ≤ eVariationOn γ univ := iInf₂_le γ hγM
      _ = eVariationOn (φ ∘ γ) univ := (hlen x y γ hγM).symm
      _ = eVariationOn seg univ := by rw [hφγ]
      _ ≤ ‖v‖₊ := hvar
      _ = edist (φ x) (φ y) := by rw [edist_nndist, nndist_comm, nndist_eq_nnnorm]
  · refine le_iInf₂ fun γ hγ ↦ ?_
    calc edist (φ x) (φ y) = edist ((φ ∘ γ) 0) ((φ ∘ γ) 1) := by simp
      _ ≤ eVariationOn (φ ∘ γ) univ := eVariationOn.edist_le _ (mem_univ _) (mem_univ _)
      _ = eVariationOn γ univ := hlen x y γ hγ

end CKSD
