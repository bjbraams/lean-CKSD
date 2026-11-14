module

public import CKSD.Learning.Basic
public import CKSD.Learning.RandomGraphs.Subcritical
public import CKSD.Learning.RandomGraphs.ConnectivityThreshold
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Mixture


/-!
# Block models, binomial random graphs, and exchangeable graphs

The symmetric two-group stochastic block model on `Fin n` draws a uniformly random labelling
with `n / 2` vertices labelled `true` (natural division, so the groups differ by at most one
vertex when `n` is odd) and then includes each unordered pair independently, with probability
`p` within groups and `q` between groups. All its probabilities are finite sums. Edge
probabilities outside `[0,1]`, which can occur for small `n` in the scalings `a log n / n`, are
clamped to `[0,1]`; this does not affect any limit.

The binomial random graph is Mathlib's `SimpleGraph.binomialRandom`. Graphon models, joint
sampling laws, and the Diaconis–Janson mixture theorem for laws invariant under all permutations
of `ℕ` are TauCeti's (`TauCeti.DenseGraphLimits`).

Sources: GAPS 107.41, 107.42, 107.43, and 107.47.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A real number clamped to the unit interval (Mathlib's projection `Set.projIcc`), used as an
edge probability. -/
def clampUnitInterval (x : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one x

/-- Labellings of `Fin n` with exactly `n / 2` vertices in the group `true`. -/
def balancedLabelings (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun σ ↦ (Finset.univ.filter fun i ↦ σ i = true).card = n / 2

/-- Probability of the graph `G` under the two-group block model given the labelling `σ`:
independent edges with probability `p` within and `q` between groups (both clamped). -/
def blockModelGraphProb {n : ℕ} (p q : ℝ) (σ : Fin n → Bool) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ e ∈ (Finset.univ.filter fun e : Fin n × Fin n ↦ e.1 < e.2),
    let r : ℝ := (clampUnitInterval (if σ e.1 = σ e.2 then p else q) : ℝ)
    if G.Adj e.1 e.2 then r else 1 - r

/-- Joint mass of a labelling and a graph under the symmetric two-group block model. -/
def blockModelMass {n : ℕ} (p q : ℝ) (σ : Fin n → Bool) (G : SimpleGraph (Fin n)) : ℝ :=
  (if σ ∈ balancedLabelings n then ((balancedLabelings n).card : ℝ)⁻¹ else 0) *
    blockModelGraphProb p q σ G

/-- Law of the observed graph of the symmetric two-group block model. -/
def blockModelGraphLaw (n : ℕ) (p q : ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n),
    ENNReal.ofReal (∑ σ : Fin n → Bool, blockModelMass p q σ G) • Measure.dirac G

/-- Probability that an estimator recovers the labelling exactly, up to a global flip. -/
def exactRecoveryProbability {n : ℕ} (p q : ℝ) (est : SimpleGraph (Fin n) → Fin n → Bool) : ℝ :=
  ∑ σ : Fin n → Bool, ∑ G : SimpleGraph (Fin n),
    blockModelMass p q σ G * if est G = σ ∨ est G = (fun i ↦ !σ i) then 1 else 0

/-- Normalized overlap `|∑ᵢ σᵢ τᵢ| / n` of two labellings in `±1` coding. -/
def labelingOverlap {n : ℕ} (σ τ : Fin n → Bool) : ℝ :=
  |∑ i, if σ i = τ i then (1 : ℝ) else -1| / n

/-- Probability that an estimator has overlap at least `ε` with the planted labelling. -/
def weakRecoveryProbability {n : ℕ} (p q ε : ℝ) (est : SimpleGraph (Fin n) → Fin n → Bool) :
    ℝ :=
  ∑ σ : Fin n → Bool, ∑ G : SimpleGraph (Fin n),
    blockModelMass p q σ G * if ε ≤ labelingOverlap σ (est G) then 1 else 0

/-- GAPS 107.41: the exact-recovery threshold of the logarithmic-degree two-group block model,
for `a, b > 0`. Recovery up to a global flip with probability tending to one is possible
exactly when `(√a - √b)² ≥ 2`. The polynomial-time achievability claim is not formalized. -/
theorem exists_exact_recovery_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ est : ∀ n, SimpleGraph (Fin n) → Fin n → Bool,
      Tendsto (fun n : ℕ ↦ exactRecoveryProbability (a * Real.log n / n) (b * Real.log n / n)
        (est n)) atTop (𝓝 1)) ↔ 2 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by
  sorry

/-- GAPS 107.41, the case `b = 0`: exact recovery is possible exactly when `a > 2`. -/
theorem exists_exact_recovery_iff_of_zero (a : ℝ) (ha : 0 < a) :
    (∃ est : ∀ n, SimpleGraph (Fin n) → Fin n → Bool,
      Tendsto (fun n : ℕ ↦ exactRecoveryProbability (a * Real.log n / n) 0 (est n))
        atTop (𝓝 1)) ↔ 2 < a := by
  sorry

/-- GAPS 107.42: the Kesten–Stigum threshold for weak recovery in the sparse two-group block
model with `p = a/n`, `q = b/n`, `a, b > 0`. The efficiency claim is not formalized. -/
theorem exists_weak_recovery_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ ε > (0 : ℝ), ∃ est : ∀ n, SimpleGraph (Fin n) → Fin n → Bool,
      Tendsto (fun n : ℕ ↦ weakRecoveryProbability (a / n) (b / n) ε (est n)) atTop (𝓝 1)) ↔
      2 * (a + b) < (a - b) ^ 2 := by
  sorry

/-- GAPS 107.42: below the Kesten–Stigum threshold the sparse block model and the binomial
random graph with the same average degree are mutually contiguous, stated directly on
sequences of events (every set of graphs on `Fin n` is measurable). -/
theorem block_model_binomial_random_mutually_contiguous (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbelow : (a - b) ^ 2 < 2 * (a + b))
    (A : ∀ n : ℕ, Set (SimpleGraph (Fin n))) :
    Tendsto (fun n : ℕ ↦ blockModelGraphLaw n (a / n) (b / n) (A n)) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ ↦ SimpleGraph.binomialRandom (Fin n)
        (clampUnitInterval ((a + b) / (2 * n))) (A n)) atTop (𝓝 0) := by
  sorry

/-- Number of vertices in the connected component of `v`. -/
def componentSize {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (G.connectedComponentMk v).supp.ncard

/-- Number of vertices of a largest connected component (zero for the empty vertex set). -/
def largestComponentSize {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (componentSize G)

/-- GAPS 107.47, subcritical phase: for `p = c/n` with `0 ≤ c < 1`, all components have at
most `C log n` vertices with probability tending to one. -/
theorem exists_tendsto_binomial_random_components_le_log (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) :
    ∃ C > (0 : ℝ), Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
      (clampUnitInterval (c / n))).real {G | ∀ v, (componentSize G v : ℝ) ≤ C * Real.log n})
      atTop (𝓝 1) :=
  exists_tendsto_binomialRandom_components_le_log' c hc0 hc

/-- GAPS 107.47, supercritical phase: for `p = c/n` with `c > 1`, the largest component has
size `ζ n + o(n)` in probability, with `ζ ∈ (0,1)` the root of `1 - ζ = e^{-cζ}`, and any two
distinct components have the smaller one of size at most `C log n` with probability tending
to one. -/
theorem binomial_random_giant_component (c : ℝ) (hc : 1 < c) (ζ : ℝ) (hζ : ζ ∈ Ioo 0 1)
    (hroot : 1 - ζ = Real.exp (-c * ζ)) :
    (∀ δ > (0 : ℝ), Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
      (clampUnitInterval (c / n))).real {G | δ < |(largestComponentSize G : ℝ) / n - ζ|})
      atTop (𝓝 0)) ∧
    ∃ C > (0 : ℝ), Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
      (clampUnitInterval (c / n))).real {G | ∀ v w, ¬ G.Reachable v w →
        (min (componentSize G v) (componentSize G w) : ℝ) ≤ C * Real.log n})
      atTop (𝓝 1) := by
  sorry

/-- GAPS 107.47, connectivity threshold: for `p = (log n + xₙ)/n`, connectivity has probability
tending to one if `xₙ → ∞`, isolated vertices have probability tending to one if `xₙ → -∞`,
and for constant `xₙ = x` the probability of connectivity tends to `exp(-e^{-x})`. -/
theorem binomial_random_connectivity_threshold :
    (∀ x : ℕ → ℝ, Tendsto x atTop atTop →
      Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (clampUnitInterval ((Real.log n + x n) / n))).real {G | G.Connected}) atTop (𝓝 1)) ∧
    (∀ x : ℕ → ℝ, Tendsto x atTop atBot →
      Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (clampUnitInterval ((Real.log n + x n) / n))).real {G | ∃ v, ∀ w, ¬ G.Adj v w})
        atTop (𝓝 1)) ∧
    ∀ x : ℝ, Tendsto (fun n : ℕ ↦ (SimpleGraph.binomialRandom (Fin n)
        (clampUnitInterval ((Real.log n + x) / n))).real {G | G.Connected})
        atTop (𝓝 (Real.exp (-Real.exp (-x)))) :=
  ⟨tendsto_binomial_random_connected_of_tendsto_at_top,
    tendsto_binomial_random_exists_isolated_of_tendsto_at_bot,
    tendsto_binomial_random_connected_threshold⟩

/-! ### Exchangeable random graphs on `ℕ` -/

/-- The permutation of `ℕ` acting as `σ` on the first `n` labels and fixing all others. -/
def finitePermOfFin {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ :=
  σ.extendDomain Fin.equivSubtype

/-- Every permutation of `ℕ` agrees on the first `n` labels with a permutation moving only
finitely many labels. -/
theorem exists_finite_perm_of_fin_eq_on (σ : Equiv.Perm ℕ) (n : ℕ) :
    ∃ (m : ℕ) (τ : Equiv.Perm (Fin m)), ∀ a < n, finitePermOfFin τ a = σ a := by
  let m := (Finset.range n).sup σ + n + 1
  have hσm : ∀ a < n, σ a < m := fun a ha ↦ by
    have := Finset.le_sup (f := σ) (Finset.mem_range.mpr ha)
    omega
  have hnm : n ≤ m := by omega
  let p : Fin m → Prop := fun x ↦ x.val < n
  let q : Fin m → Prop := fun y ↦ ∃ a < n, y.val = σ a
  let f : {x // p x} → {y // q y} := fun x ↦
    ⟨⟨σ x.1.val, hσm _ x.2⟩, x.1.val, x.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : σ x.1.val = σ y.1.val := congrArg (fun z : {y // q y} ↦ z.1.val) hxy
      exact Subtype.ext (Fin.ext (σ.injective h1))
    · rintro ⟨y, a, ha, hy⟩
      exact ⟨⟨⟨a, lt_of_lt_of_le ha hnm⟩, ha⟩, Subtype.ext (Fin.ext hy.symm)⟩
  let e : {x // p x} ≃ {y // q y} := Equiv.ofBijective f hf
  refine ⟨m, e.extendSubtype, fun a ha ↦ ?_⟩
  have ham : a < m := lt_of_lt_of_le ha hnm
  unfold finitePermOfFin
  rw [Equiv.Perm.extendDomain_apply_subtype e.extendSubtype Fin.equivSubtype (b := a) ham]
  have hsymm : Fin.equivSubtype.symm ⟨a, ham⟩ = (⟨a, ham⟩ : Fin m) := rfl
  rw [hsymm, Equiv.extendSubtype_apply_of_mem e _ (show p ⟨a, ham⟩ from ha)]
  rfl

/-- A law on graphs on `ℕ` invariant under every permutation of finitely many labels is
invariant under every permutation of `ℕ`. -/
theorem map_comap_eq_of_finite_perm_invariant (law : Measure (SimpleGraph ℕ))
    [IsProbabilityMeasure law]
    (hinv : ∀ n (σ : Equiv.Perm (Fin n)),
      law.map (SimpleGraph.comap ⇑(finitePermOfFin σ)) = law)
    (σ : Equiv.Perm ℕ) : law.map (SimpleGraph.comap ⇑σ) = law := by
  refine (SimpleGraph.measure_ext_of_map_restrictFin fun n ↦ ?_).symm
  obtain ⟨m, τ, hτ⟩ := exists_finite_perm_of_fin_eq_on σ n
  have hfun : (fun G : SimpleGraph ℕ ↦ G.restrictFin n) ∘ SimpleGraph.comap ⇑σ =
      (fun G : SimpleGraph ℕ ↦ G.restrictFin n) ∘ SimpleGraph.comap ⇑(finitePermOfFin τ) := by
    funext G
    ext a b
    simp only [Function.comp_apply, SimpleGraph.restrictFin_adj, SimpleGraph.comap_adj,
      hτ a a.2, hτ b b.2]
  calc law.map (fun G ↦ G.restrictFin n)
      = (law.map (SimpleGraph.comap ⇑(finitePermOfFin τ))).map (fun G ↦ G.restrictFin n) := by
        rw [hinv m τ]
    _ = law.map ((fun G : SimpleGraph ℕ ↦ G.restrictFin n) ∘
          SimpleGraph.comap ⇑(finitePermOfFin τ)) :=
        Measure.map_map (SimpleGraph.measurable_restrictFin n) (SimpleGraph.measurable_comap _)
    _ = (law.map (SimpleGraph.comap ⇑σ)).map (fun G ↦ G.restrictFin n) := by
        rw [← hfun]
        exact (Measure.map_map (SimpleGraph.measurable_restrictFin n)
          (SimpleGraph.measurable_comap _)).symm

/-- GAPS 107.43: a law on graphs on `ℕ` invariant under permutations of finitely many labels is
a mixture of graphon models, with a unique mixing measure on TauCeti's unit-interval graphon
space (graphons modulo cut distance zero). The all-permutations case is TauCeti's
`InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace`. -/
theorem exists_unique_graphon_mixture_of_finite_perm_invariant (law : Measure (SimpleGraph ℕ))
    [IsProbabilityMeasure law]
    (hinv : ∀ n (σ : Equiv.Perm (Fin n)),
      law.map (SimpleGraph.comap ⇑(finitePermOfFin σ)) = law) :
    ∃! P : ProbabilityMeasure TauCeti.DenseGraphLimits.GraphonSpaceI,
      (P : Measure TauCeti.DenseGraphLimits.GraphonSpaceI).bind
        TauCeti.DenseGraphLimits.infiniteSampleLawOnSpace = law :=
  TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.existsUnique_bind_infiniteSampleLawOnSpace
    ⟨law, inferInstance, map_comap_eq_of_finite_perm_invariant law hinv⟩

/-- GAPS 107.43, uniqueness in the attained form (Borgs–Chayes–Lovász): two graphons on the
unit interval have the same joint sampling law exactly when they have almost everywhere equal
pullbacks under two measure-preserving self-maps of the unit interval. -/
theorem infinite_sample_law_eq_iff_exists_measure_preserving
    (U W : TauCeti.DenseGraphLimits.Graphon unitInterval volume) :
    TauCeti.DenseGraphLimits.infiniteSampleLaw U =
        TauCeti.DenseGraphLimits.infiniteSampleLaw W ↔
      ∃ φ ψ : unitInterval → unitInterval, MeasurePreserving φ volume volume ∧
        MeasurePreserving ψ volume volume ∧
        ∀ᵐ z ∂(volume : Measure (unitInterval × unitInterval)),
          U (φ z.1) (φ z.2) = W (ψ z.1) (ψ z.2) := by
  sorry

end CKSD
