module

public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import TauCeti.Combinatorics.SimpleGraph.Measurable
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Connectivity estimates for the binomial random graph

For `p = (log n + xₙ)/n` (clamped to `[0,1]`) the binomial random graph `G(n, p)` is connected
with probability tending to one if `xₙ → ∞`, has an isolated vertex with probability tending to
one if `xₙ → -∞`, and for constant `xₙ = x` is connected with probability tending to
`exp (-e^{-x})` (Erdős–Rényi).

The proof is elementary. Edge events have product probabilities (from Mathlib's description of
`G(V, p)` as a product of Bernoulli laws). The factorial moments `Sⱼ` of the number of isolated
vertices are explicit sums, the Bonferroni inequalities bound `P(no isolated vertex)` by
alternating partial sums of the `Sⱼ`, and `Sⱼ → e^{-jx}/j!` gives the Poisson limit. A
disconnected graph without isolated vertices has a vertex set `S` with `2 ≤ |S| ≤ n/2`, no edge
leaving `S` and `|S| - 1` edges inside `S`; the union bound over such sets tends to zero.

## Main results

* `CKSD.binomialRandom_real_edges`: probability of prescribed present and absent edges.
* `CKSD.bonferroni_isolatedVertices`: Bonferroni inequalities for isolated vertices.
* `CKSD.binomialRandom_real_not_connected_le`: union bound for disconnected graphs without
  isolated vertices.
* `CKSD.tendsto_disconnSum`, `CKSD.binomialRandom_real_connected_mem_Icc`: the analytic
  estimates and the two-sided bound on the connection probability.

The limits along the threshold sequence, and the three parts of the connectivity threshold
(GAPS 107.47), are in `CKSD.Learning.RandomGraphs.ConnectivityThreshold`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set unitInterval
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the binomial random graph `G(V, p)`, a set `A` of prescribed edges is present and a
disjoint set `B` of prescribed edges is absent with probability `p ^ |A| (1 - p) ^ |B|`. -/
theorem binomialRandom_real_edges (p : I) (A B : Finset (Sym2 V)) (hA : ∀ e ∈ A, ¬ e.IsDiag)
    (hB : ∀ e ∈ B, ¬ e.IsDiag) (hAB : Disjoint A B) :
    (SimpleGraph.binomialRandom V p).real
        {G | (∀ e ∈ A, e ∈ G.edgeSet) ∧ ∀ e ∈ B, e ∉ G.edgeSet} =
      (p : ℝ) ^ A.card * (1 - p) ^ B.card := by
  classical
  set t : Sym2 V → Set Prop := fun e ↦ {P | (e ∈ A → P) ∧ (e ∈ B → ¬ P) ∧ (e.IsDiag → ¬ P)}
  have himage : (fun G : SimpleGraph V ↦ fun e ↦ e ∈ G.edgeSet) ''
      {G | (∀ e ∈ A, e ∈ G.edgeSet) ∧ ∀ e ∈ B, e ∉ G.edgeSet} =
      Set.pi (↑(Finset.univ : Finset (Sym2 V))) t := by
    ext f
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_pi, Set.mem_univ,
      true_implies, t]
    constructor
    · rintro ⟨G, ⟨hGA, hGB⟩, rfl⟩ e
      exact ⟨hGA e, hGB e, fun hd he ↦ G.not_isDiag_of_mem_edgeSet he hd⟩
    · intro hf
      refine ⟨SimpleGraph.fromEdgeSet {e | f e}, ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩, ?_⟩
      · rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨(hf e).1 he, hA e he⟩
      · rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact fun h ↦ (hf e).2.1 he h.1
      · funext e
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        apply propext
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hd ↦ (hf e).2.2 hd h⟩⟩
  have hfac : ∀ e : Sym2 V, (bernoulliMeasure (¬ e.IsDiag) False p (t e)).toReal =
      (if e ∈ A then (p : ℝ) else 1) * (if e ∈ B then 1 - (p : ℝ) else 1) := by
    intro e
    have hmeas : MeasurableSet (t e) := trivial
    by_cases hd : e.IsDiag
    · have hnA : e ∉ A := fun h ↦ hA e h hd
      have hnB : e ∉ B := fun h ↦ hB e h hd
      have h1 : (¬ e.IsDiag) ∈ t e := by simp [t, hnA, hnB, hd]
      have h2 : False ∈ t e := by simp [t, hnA, hnB]
      simp [bernoulliMeasure_apply_of_mem_of_mem p hmeas h1 h2, hnA, hnB]
    · by_cases heA : e ∈ A
      · have hnB : e ∉ B := Finset.disjoint_left.mp hAB heA
        have h1 : (¬ e.IsDiag) ∈ t e := by simp [t, hnB, hd]
        have h2 : False ∉ t e := by simp [t, heA]
        simp [bernoulliMeasure_apply_of_mem_of_notMem p hmeas h1 h2, heA, hnB]
      · by_cases heB : e ∈ B
        · have h1 : (¬ e.IsDiag) ∉ t e := by simp [t, heB, hd]
          have h2 : False ∈ t e := by simp [t, heA]
          simp [bernoulliMeasure_apply_of_notMem_of_mem p hmeas h1 h2, heA, heB]
        · have h1 : (¬ e.IsDiag) ∈ t e := by simp [t, heA, heB, hd]
          have h2 : False ∈ t e := by simp [t, heA]
          simp [bernoulliMeasure_apply_of_mem_of_mem p hmeas h1 h2, heA, heB]
  rw [measureReal_def, SimpleGraph.binomialRandom_apply, himage,
    Measure.infinitePi_pi (μ := fun e : Sym2 V ↦ bernoulliMeasure (¬ e.IsDiag) False p)
      (fun _ _ ↦ trivial), ENNReal.toReal_prod]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.univ_inter, Finset.prod_const, Finset.prod_const]

/-! ### Isolated vertices -/

open scoped Classical in
/-- The set of isolated vertices of a graph. -/
def isolatedVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v ↦ ∀ w, ¬ G.Adj v w

/-- The non-loop pairs incident to a vertex set `J`. -/
def incidentEdges (J : Finset V) : Finset (Sym2 V) :=
  ((J ×ˢ (Finset.univ : Finset V)).image fun x : V × V ↦ s(x.1, x.2)).filter fun e ↦ ¬ e.IsDiag

/-- A vertex set `J` consists of isolated vertices exactly when no pair incident to `J` is an
edge. -/
theorem subset_isolatedVertices_iff (G : SimpleGraph V) (J : Finset V) :
    J ⊆ isolatedVertices G ↔ ∀ e ∈ incidentEdges J, e ∉ G.edgeSet := by
  constructor
  · intro h e he hG
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, and_true] at he
    obtain ⟨⟨⟨v, w⟩, hv, rfl⟩, -⟩ := he
    have := h hv
    simp only [isolatedVertices, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this w hG
  · intro h v hv
    simp only [isolatedVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hvw
    refine h s(v, w) ?_ hvw
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, and_true, Sym2.mk_isDiag_iff]
    exact ⟨⟨(v, w), hv, rfl⟩, hvw.ne⟩

/-- A vertex set `J` consists of isolated vertices with probability
`(1 - p) ^ |incidentEdges J|`. -/
theorem binomialRandom_real_subset_isolatedVertices (p : I) (J : Finset V) :
    (SimpleGraph.binomialRandom V p).real {G | J ⊆ isolatedVertices G} =
      (1 - p) ^ (incidentEdges J).card := by
  have h := binomialRandom_real_edges p ∅ (incidentEdges J) (by simp)
    (fun e he ↦ (Finset.mem_filter.mp he).2) (Finset.disjoint_empty_left _)
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    Finset.card_empty, pow_zero, one_mul] at h
  rw [← h]
  congr 1
  ext G
  exact subset_isolatedVertices_iff G J

/-- The number of pairs incident to `J` is at most `|J| |V|`. -/
theorem card_incidentEdges_le (J : Finset V) :
    (incidentEdges J).card ≤ J.card * Fintype.card V := by
  unfold incidentEdges
  refine (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans ?_)
  rw [Finset.card_product, Finset.card_univ]

/-- The pairs joining `J` to its complement are pairwise distinct non-loops. -/
private theorem injOn_mk_product_compl (J : Finset V) :
    Set.InjOn (fun x : V × V ↦ s(x.1, x.2)) ↑(J ×ˢ Jᶜ) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hab hcd
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hcd.1 hab.2

/-- The number of pairs incident to `J` is at least `|J| (|V| - |J|)`. -/
theorem le_card_incidentEdges (J : Finset V) :
    J.card * (Fintype.card V - J.card) ≤ (incidentEdges J).card := by
  have hsub : (J ×ˢ Jᶜ).image (fun x : V × V ↦ s(x.1, x.2)) ⊆ incidentEdges J := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_compl] at he
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := he
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, and_true, Sym2.mk_isDiag_iff]
    exact ⟨⟨(a, b), ha, rfl⟩, fun h ↦ hb (h ▸ ha)⟩
  calc J.card * (Fintype.card V - J.card) = (J ×ˢ Jᶜ).card := by
        rw [Finset.card_product, Finset.card_compl]
    _ = ((J ×ˢ Jᶜ).image (fun x : V × V ↦ s(x.1, x.2))).card :=
        (Finset.card_image_of_injOn (injOn_mk_product_compl J)).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The `j`-th factorial moment of the number of isolated vertices of `G(V, p)`:
`Sⱼ = ∑_{|J| = j} P(J consists of isolated vertices)`. -/
def isolatedMoment (p : I) (j : ℕ) : ℝ :=
  ∑ J ∈ Finset.powersetCard j (Finset.univ : Finset V), (1 - (p : ℝ)) ^ (incidentEdges J).card

/-- The `j`-th binomial moment of the number of isolated vertices is `isolatedMoment p j`. -/
theorem integral_choose_card_isolatedVertices (p : I) (j : ℕ) :
    ∫ G, ((isolatedVertices G).card.choose j : ℝ) ∂SimpleGraph.binomialRandom V p =
      isolatedMoment (V := V) p j := by
  have hpt : ∀ G : SimpleGraph V, ((isolatedVertices G).card.choose j : ℝ) =
      ∑ J ∈ Finset.powersetCard j (Finset.univ : Finset V),
        Set.indicator {G | J ⊆ isolatedVertices G} 1 G := by
    intro G
    rw [← Finset.card_powersetCard, Finset.sum_indicator_eq_sum_filter]
    simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
    congr 1
    ext J
    simp [Finset.mem_powersetCard, and_comm]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun J _ ↦ Integrable.of_finite]
  refine Finset.sum_congr rfl fun J _ ↦ ?_
  rw [integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _),
    binomialRandom_real_subset_isolatedVertices]

/-- Pointwise Bonferroni inequality: `(-1)^M (∑_{j ≤ M} (-1)^j C(N, j) - 1{N = 0}) ≥ 0`. -/
private theorem bonferroni_pointwise (N M : ℕ) :
    0 ≤ (-1 : ℝ) ^ M * ((∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (N.choose j : ℝ)) -
      if N = 0 then 1 else 0) := by
  rcases N with _ | N
  · simp [Finset.sum_range_succ', Nat.choose_zero_succ]
  · have h := Int.alternating_sum_range_choose_eq_choose (n := N) (m := M)
    have h' : (∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * ((N + 1).choose j : ℝ)) =
        (-1) ^ M * (N.choose M : ℝ) := by exact_mod_cast h
    rw [ite_eq_right (Nat.succ_ne_zero N), sub_zero, h', ← mul_assoc, ← pow_add, ← two_mul,
      pow_mul]
    norm_num

/-- Bonferroni inequalities for the absence of isolated vertices: the alternating partial sums
of the factorial moments bound `P(no isolated vertex)` alternately from above and below. -/
theorem bonferroni_isolatedVertices (p : I) (M : ℕ) :
    0 ≤ (-1 : ℝ) ^ M * ((∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * isolatedMoment (V := V) p j) -
      (SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅}) := by
  have h : 0 ≤ ∫ G, (-1 : ℝ) ^ M * ((∑ j ∈ Finset.range (M + 1),
      (-1 : ℝ) ^ j * ((isolatedVertices G).card.choose j : ℝ)) -
      Set.indicator {G | isolatedVertices G = ∅} 1 G) ∂SimpleGraph.binomialRandom V p := by
    refine integral_nonneg fun G ↦ ?_
    have := bonferroni_pointwise (isolatedVertices G).card M
    simp only [Finset.card_eq_zero] at this
    convert this using 3
    by_cases hG : isolatedVertices G = ∅ <;> simp [hG]
  rw [integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_finsetSum _ fun j _ ↦ Integrable.of_finite,
    integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _)] at h
  simp_rw [integral_const_mul, integral_choose_card_isolatedVertices] at h
  exact h

/-- Second-moment inequality for isolated vertices:
`P(no isolated vertex) S₁² ≤ S₁ + 2 S₂ - S₁²`. -/
theorem binomialRandom_real_isolatedVertices_eq_empty_mul_le (p : I) :
    (SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅} *
        isolatedMoment (V := V) p 1 ^ 2 ≤
      isolatedMoment (V := V) p 1 + 2 * isolatedMoment (V := V) p 2 -
        isolatedMoment (V := V) p 1 ^ 2 := by
  set s := isolatedMoment (V := V) p 1
  set μ := SimpleGraph.binomialRandom V p
  have hpt : ∀ G : SimpleGraph V, Set.indicator {G | isolatedVertices G = ∅} 1 G * s ^ 2 ≤
      ((isolatedVertices G).card.choose 1 : ℝ) + 2 * ((isolatedVertices G).card.choose 2 : ℝ) -
        2 * s * ((isolatedVertices G).card.choose 1 : ℝ) + s ^ 2 := by
    intro G
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    by_cases hG : isolatedVertices G = ∅
    · simp [hG]
    · simp only [Set.indicator, Set.mem_ofPred_eq, hG, ite_false, zero_mul]
      nlinarith [sq_nonneg ((isolatedVertices G).card - s)]
  have h := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpt
  rw [integral_mul_const, integral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _),
    integral_add Integrable.of_finite (integrable_const _),
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const_mul, integral_const, integral_choose_card_isolatedVertices,
    integral_choose_card_isolatedVertices] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  linarith

/-! ### Disconnected graphs without isolated vertices -/

/-- The non-loop pairs with both ends in `S`. -/
def internalPairs (S : Finset V) : Finset (Sym2 V) :=
  ((S ×ˢ S).image (fun x : V × V ↦ s(x.1, x.2))).filter fun e ↦ ¬ e.IsDiag

/-- The pairs joining `S` to its complement. -/
def boundaryPairs (S : Finset V) : Finset (Sym2 V) :=
  (S ×ˢ Sᶜ).image (fun x : V × V ↦ s(x.1, x.2))

omit [Fintype V] in
/-- There are at most `|S|²` internal pairs. -/
theorem card_internalPairs_le (S : Finset V) : (internalPairs S).card ≤ S.card ^ 2 := by
  unfold internalPairs
  refine (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans ?_)
  rw [Finset.card_product, sq]

/-- There are exactly `|S| (|V| - |S|)` boundary pairs. -/
theorem card_boundaryPairs (S : Finset V) :
    (boundaryPairs S).card = S.card * (Fintype.card V - S.card) := by
  rw [boundaryPairs, Finset.card_image_of_injOn (injOn_mk_product_compl S), Finset.card_product,
    Finset.card_compl]

/-- Boundary pairs are not loops. -/
theorem not_isDiag_of_mem_boundaryPairs {S : Finset V} {e : Sym2 V}
    (he : e ∈ boundaryPairs S) : ¬ e.IsDiag := by
  simp only [boundaryPairs, Finset.mem_image, Finset.mem_product, Finset.mem_compl] at he
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := he
  rw [Sym2.mk_isDiag_iff]
  exact fun h ↦ hb (h ▸ ha)

/-- Internal and boundary pairs of the same set are disjoint. -/
theorem disjoint_internalPairs_boundaryPairs (S : Finset V) :
    Disjoint (internalPairs S) (boundaryPairs S) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [internalPairs, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at he
  simp only [boundaryPairs, Finset.mem_image, Finset.mem_product, Finset.mem_compl] at he'
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, -⟩ := he
  obtain ⟨⟨c, d⟩, ⟨hc, hd⟩, h⟩ := he'
  rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hd hb
  · exact hd ha

/-- The vertices reachable from `a`. -/
private def reachableFinset (G : SimpleGraph V) (a : V) : Finset V :=
  open scoped Classical in Finset.univ.filter (G.Reachable a)

omit [DecidableEq V] in
/-- Membership in `reachableFinset` is reachability. -/
private theorem mem_reachableFinset {G : SimpleGraph V} {a v : V} :
    v ∈ reachableFinset G a ↔ G.Reachable a v := by
  simp [reachableFinset]

/-- A connected component with `k` vertices contains at least `k - 1` edges. -/
private theorem exists_edges_reachableFinset (G : SimpleGraph V) (a : V) :
    ∃ T ⊆ internalPairs (reachableFinset G a), (reachableFinset G a).card ≤ T.card + 1 ∧
      ∀ e ∈ T, e ∈ G.edgeSet := by
  classical
  set S := reachableFinset G a
  set C := G.connectedComponentMk a
  have hsupp : C.supp = (↑S : Set V) := by
    ext v
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Finset.mem_coe, S,
      mem_reachableFinset, C, SimpleGraph.ConnectedComponent.eq]
    exact SimpleGraph.reachable_comm
  have h := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have h1 : Nat.card C.supp = S.card := by
    rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hmem : ∀ e : Sym2 C.supp, e ∈ C.toSimpleGraph.edgeSet →
      Sym2.map Subtype.val e ∈ (internalPairs S).filter (· ∈ G.edgeSet) := by
    intro e
    induction e using Sym2.ind with
    | h x y =>
      intro he
      have hadj : G.Adj x.1 y.1 := he
      have hx : x.1 ∈ S := by rw [← Finset.mem_coe, ← hsupp]; exact x.2
      have hy : y.1 ∈ S := by rw [← Finset.mem_coe, ← hsupp]; exact y.2
      simp only [Sym2.map_mk, Finset.mem_filter, internalPairs, Finset.mem_image,
        Finset.mem_product, Sym2.mk_isDiag_iff, SimpleGraph.mem_edgeSet]
      exact ⟨⟨⟨(x.1, y.1), ⟨hx, hy⟩, rfl⟩, hadj.ne⟩, hadj⟩
  have h2 : Nat.card C.toSimpleGraph.edgeSet ≤
      ((internalPairs S).filter (· ∈ G.edgeSet)).card := by
    have hinj : Function.Injective fun e : C.toSimpleGraph.edgeSet ↦
        (⟨Sym2.map Subtype.val e.1, hmem e.1 e.2⟩ :
          ↥((internalPairs S).filter (· ∈ G.edgeSet))) := by
      intro e e' hee'
      exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val hee'))
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := ↥((internalPairs S).filter (· ∈ G.edgeSet))),
      Fintype.card_coe] at this
  have h1' : Nat.card C.supp ≤ Nat.card C.toSimpleGraph.edgeSet + 1 := h
  refine ⟨(internalPairs S).filter (· ∈ G.edgeSet), Finset.filter_subset _ _, by omega,
    fun e he ↦ (Finset.mem_filter.mp he).2⟩

/-- A disconnected graph without isolated vertices on a nonempty vertex set has a vertex set `S`
with `2 ≤ |S| ≤ |V| / 2`, no edge leaving `S`, and `|S| - 1` edges inside `S`. -/
theorem exists_closed_set_of_not_connected [Nonempty V] (G : SimpleGraph V)
    (hiso : isolatedVertices G = ∅) (hG : ¬ G.Connected) :
    ∃ k ∈ Finset.Icc 2 (Fintype.card V / 2), ∃ S ∈ Finset.powersetCard k Finset.univ,
      ∃ T ∈ Finset.powersetCard (k - 1) (internalPairs S),
        (∀ e ∈ T, e ∈ G.edgeSet) ∧ ∀ e ∈ boundaryPairs S, e ∉ G.edgeSet := by
  classical
  have hpre : ¬ G.Preconnected := fun h ↦ hG ((SimpleGraph.connected_iff G).mpr ⟨h, ‹_›⟩)
  obtain ⟨u, w, huw⟩ : ∃ u w, ¬ G.Reachable u w := by
    by_contra h
    push Not at h
    exact hpre h
  have hdisj : Disjoint (reachableFinset G u) (reachableFinset G w) := by
    rw [Finset.disjoint_left]
    intro v hu hw
    rw [mem_reachableFinset] at hu hw
    exact huw (hu.trans hw.symm)
  have hsum : (reachableFinset G u).card + (reachableFinset G w).card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  -- the smaller of the two components
  obtain ⟨a, ha⟩ : ∃ a, 2 * (reachableFinset G a).card ≤ Fintype.card V := by
    rcases le_total (reachableFinset G u).card (reachableFinset G w).card with h | h
    · exact ⟨u, by omega⟩
    · exact ⟨w, by omega⟩
  set S := reachableFinset G a with hS
  have hnb : ∃ b, G.Adj a b := by
    by_contra h
    push Not at h
    have : a ∈ isolatedVertices G := by simp [isolatedVertices, h]
    rw [hiso] at this
    exact Finset.notMem_empty a this
  obtain ⟨b, hab⟩ := hnb
  have hk : 2 ≤ S.card := by
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    exact ⟨a, mem_reachableFinset.mpr SimpleGraph.Reachable.rfl, b,
      mem_reachableFinset.mpr hab.reachable, hab.ne⟩
  obtain ⟨T₀, hT₀S, hT₀card, hT₀G⟩ := exists_edges_reachableFinset G a
  rw [← hS] at hT₀S hT₀card
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := T₀) (n := S.card - 1)
    (by omega)
  refine ⟨S.card, Finset.mem_Icc.mpr ⟨hk, by omega⟩, S,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, T,
    Finset.mem_powersetCard.mpr ⟨hTsub.trans hT₀S, hTcard⟩,
    fun e he ↦ hT₀G e (hTsub he), ?_⟩
  intro e he hGe
  simp only [boundaryPairs, Finset.mem_image, Finset.mem_product, Finset.mem_compl] at he
  obtain ⟨⟨c, d⟩, ⟨hc, hd⟩, rfl⟩ := he
  rw [hS, mem_reachableFinset] at hc hd
  exact hd (hc.trans (SimpleGraph.Adj.reachable hGe))

/-- Union bound for disconnected graphs without isolated vertices:
`P(no isolated vertex, not connected) ≤ ∑_{k=2}^{|V|/2} C(|V|, k) C(k², k-1) p^{k-1}
(1-p)^{k(|V|-k)}`. -/
theorem binomialRandom_real_not_connected_le [Nonempty V] (p : I) :
    (SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅ ∧ ¬ G.Connected} ≤
      ∑ k ∈ Finset.Icc 2 (Fintype.card V / 2), ((Fintype.card V).choose k : ℝ) *
        ((k ^ 2).choose (k - 1) : ℝ) * (p : ℝ) ^ (k - 1) *
          (1 - (p : ℝ)) ^ (k * (Fintype.card V - k)) := by
  set μ := SimpleGraph.binomialRandom V p
  set E : Finset V → Finset (Sym2 V) → Set (SimpleGraph V) := fun S T ↦
    {G | (∀ e ∈ T, e ∈ G.edgeSet) ∧ ∀ e ∈ boundaryPairs S, e ∉ G.edgeSet}
  have hsub : {G | isolatedVertices G = ∅ ∧ ¬ G.Connected} ⊆
      ⋃ k ∈ Finset.Icc 2 (Fintype.card V / 2), ⋃ S ∈ Finset.powersetCard k Finset.univ,
        ⋃ T ∈ Finset.powersetCard (k - 1) (internalPairs S), E S T := by
    rintro G ⟨hiso, hG⟩
    obtain ⟨k, hk, S, hS, T, hT, h1, h2⟩ := exists_closed_set_of_not_connected G hiso hG
    simp only [Set.mem_iUnion]
    exact ⟨k, hk, S, hS, T, hT, h1, h2⟩
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hq0 : 0 ≤ 1 - (p : ℝ) := by linarith [p.2.2]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ S ∈ Finset.powersetCard k (Finset.univ : Finset V),
      μ.real (⋃ T ∈ Finset.powersetCard (k - 1) (internalPairs S), E S T) ≤
        ((k ^ 2).choose (k - 1) : ℝ) * (p : ℝ) ^ (k - 1) *
          (1 - (p : ℝ)) ^ (k * (Fintype.card V - k)) := by
    intro S hS
    have hSk : S.card = k := (Finset.mem_powersetCard.mp hS).2
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have hET : ∀ T ∈ Finset.powersetCard (k - 1) (internalPairs S),
        μ.real (E S T) = (p : ℝ) ^ (k - 1) * (1 - (p : ℝ)) ^ (k * (Fintype.card V - k)) := by
      intro T hT
      obtain ⟨hTS, hTc⟩ := Finset.mem_powersetCard.mp hT
      rw [binomialRandom_real_edges p T (boundaryPairs S)
        (fun e he ↦ (Finset.mem_filter.mp (hTS he)).2)
        (fun e he ↦ not_isDiag_of_mem_boundaryPairs he)
        ((disjoint_internalPairs_boundaryPairs S).mono_left hTS), hTc, card_boundaryPairs,
        hSk]
    rw [Finset.sum_congr rfl hET, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
      mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Nat.choose_le_choose _ (hSk ▸ card_internalPairs_le S)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ### Analytic estimates for the union bound -/

/-- The real power `(1 - p) ^ m` is at most `exp (-p m)` for `p ≤ 1`. -/
theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ Real.exp (-(p * m)) := by
  calc (1 - p) ^ m ≤ Real.exp (-p) ^ m :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) m
    _ = Real.exp (-(p * m)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `C(n, k) C(k², k - 1) ≤ n^k e^{2k}` for `k ≥ 1`. -/
private theorem choose_mul_choose_sq_le (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℝ) * ((k ^ 2).choose (k - 1) : ℝ) ≤ (n : ℝ) ^ k * Real.exp (2 * k) := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) k n
  have h2 := Nat.choose_le_pow_div (α := ℝ) (k - 1) (k ^ 2)
  have hfac : (k : ℝ) * ((k - 1).factorial : ℝ) = k.factorial := by
    exact_mod_cast Nat.mul_factorial_pred (by omega : k ≠ 0)
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkk : ((k : ℝ) ^ 2) ^ (k - 1) * k ≤ ((k : ℝ) ^ k) ^ 2 := by
    calc ((k : ℝ) ^ 2) ^ (k - 1) * k ≤ ((k : ℝ) ^ 2) ^ (k - 1) * (k : ℝ) ^ 2 := by
          gcongr; nlinarith
      _ = ((k : ℝ) ^ k) ^ 2 := by
          rw [← pow_succ, Nat.sub_add_cancel hk, ← pow_mul, ← pow_mul, mul_comm]
  have hexp : (k : ℝ) ^ k / k.factorial ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg k) k
  have hf0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hf1 : (0 : ℝ) < (k - 1).factorial := by exact_mod_cast Nat.factorial_pos (k - 1)
  calc (n.choose k : ℝ) * ((k ^ 2).choose (k - 1) : ℝ)
      ≤ ((n : ℝ) ^ k / k.factorial) * (((k ^ 2 : ℕ) : ℝ) ^ (k - 1) / (k - 1).factorial) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (n : ℝ) ^ k * (((k : ℝ) ^ 2) ^ (k - 1) * k) / (k.factorial : ℝ) ^ 2 := by
        rw [← hfac]; push_cast; field_simp
    _ ≤ (n : ℝ) ^ k * ((k : ℝ) ^ k) ^ 2 / (k.factorial : ℝ) ^ 2 := by gcongr
    _ = (n : ℝ) ^ k * ((k : ℝ) ^ k / k.factorial) ^ 2 := by ring
    _ ≤ (n : ℝ) ^ k * Real.exp k ^ 2 := by gcongr
    _ = (n : ℝ) ^ k * Real.exp (2 * k) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- The term `k = 2` of the union bound is at most `2 e⁴ n y e^{-2y}` with `y = np`. -/
private theorem term_two_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 2 ≤ n) :
    (n.choose 2 : ℝ) * ((2 ^ 2).choose (2 - 1) : ℝ) * p ^ (2 - 1) * (1 - p) ^ (2 * (n - 2)) ≤
      2 * Real.exp 4 * n * (n * p) * Real.exp (-(2 * (n * p))) := by
  have hc : (n.choose 2 : ℝ) ≤ n ^ 2 / 2 := by
    have := Nat.choose_le_pow_div (α := ℝ) 2 n
    simpa using this
  have h4 : ((2 ^ 2).choose (2 - 1) : ℝ) = 4 := by norm_num
  have hq := one_sub_pow_le_exp hp1 (2 * (n - 2))
  have hcast : ((2 * (n - 2) : ℕ) : ℝ) = 2 * n - 4 := by
    rw [Nat.cast_mul, Nat.cast_sub hn]; push_cast; ring
  rw [hcast] at hq
  have he : Real.exp (-(p * (2 * n - 4))) ≤ Real.exp 4 * Real.exp (-(2 * (n * p))) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  rw [h4, pow_one]
  have hq0 : 0 ≤ 1 - p := by linarith
  calc (n.choose 2 : ℝ) * 4 * p * (1 - p) ^ (2 * (n - 2))
      ≤ (n ^ 2 / 2) * 4 * p * (Real.exp 4 * Real.exp (-(2 * (n * p)))) :=
        mul_le_mul (by gcongr) (hq.trans he) (pow_nonneg hq0 _) (by positivity)
    _ = 2 * Real.exp 4 * n * (n * p) * Real.exp (-(2 * (n * p))) := by ring

/-- For `2 ≤ k` and `2k ≤ n`, the `k`-th term of the union bound is at most `D a^{k-1}` with
`y = np`, `D = n e² e^{-y/2}` and `a = e² y e^{-y/2}`. -/
private theorem term_le (n k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hk : 2 ≤ k)
    (hkn : 2 * k ≤ n) :
    (n.choose k : ℝ) * ((k ^ 2).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (k * (n - k)) ≤
      (n : ℝ) * Real.exp 2 * Real.exp (-(n * p) / 2) *
        (Real.exp 2 * (n * p) * Real.exp (-(n * p) / 2)) ^ (k - 1) := by
  have hc := choose_mul_choose_sq_le n k (by omega)
  have hq := one_sub_pow_le_exp hp1 (k * (n - k))
  have hcast : ((k * (n - k) : ℕ) : ℝ) = k * (n - k) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
  rw [hcast] at hq
  have hkn' : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
  have he : Real.exp (-(p * (k * (n - k)))) ≤ Real.exp (-(p * k * n / 2)) := by
    apply Real.exp_le_exp.mpr
    have : (k : ℝ) * n / 2 ≤ k * (n - k) := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hq0 : 0 ≤ 1 - p := by linarith
  simp only [Nat.add_sub_cancel] at hc ⊢
  calc (n.choose (j + 1) : ℝ) * (((j + 1) ^ 2).choose j : ℝ) * p ^ j *
        (1 - p) ^ ((j + 1) * (n - (j + 1)))
      ≤ ((n : ℝ) ^ (j + 1) * Real.exp (2 * ((j + 1 : ℕ) : ℝ))) * p ^ j *
          Real.exp (-(p * ((j + 1 : ℕ) : ℝ) * n / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc (pow_nonneg hp0 j)) (hq.trans he)
          (pow_nonneg hq0 _) (by positivity)
    _ = (n : ℝ) * Real.exp 2 * Real.exp (-(n * p) / 2) *
          (Real.exp 2 * (n * p) * Real.exp (-(n * p) / 2)) ^ j := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        have h1 : Real.exp (2 * ((j + 1 : ℕ) : ℝ)) = Real.exp 2 * Real.exp (j * 2) := by
          rw [← Real.exp_add]; push_cast; ring_nf
        have h2 : Real.exp (-(p * ((j + 1 : ℕ) : ℝ) * n / 2)) =
            Real.exp (-(n * p) / 2) * Real.exp (j * (-(n * p) / 2)) := by
          rw [← Real.exp_add]; push_cast; ring_nf
        rw [h1, h2]
        ring

/-- Explicit bound for the union bound: if `n ≥ 4` and `a = e² y e^{-y/2} ≤ 1/2` with `y = np`,
the sum is at most `2 e⁴ n y e^{-2y} + 2 e⁶ n y² e^{-3y/2}`. -/
private theorem disconnSum_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 4 ≤ n)
    (ha : Real.exp 2 * (n * p) * Real.exp (-(n * p) / 2) ≤ 1 / 2) :
    ∑ k ∈ Finset.Icc 2 (n / 2), (n.choose k : ℝ) * ((k ^ 2).choose (k - 1) : ℝ) *
        p ^ (k - 1) * (1 - p) ^ (k * (n - k)) ≤
      2 * Real.exp 4 * n * (n * p) * Real.exp (-(2 * (n * p))) +
        2 * Real.exp 6 * n * (n * p) ^ 2 * Real.exp (-(3 * (n * p) / 2)) := by
  set a := Real.exp 2 * (n * p) * Real.exp (-(n * p) / 2) with ha_def
  set D := (n : ℝ) * Real.exp 2 * Real.exp (-(n * p) / 2) with hD
  have ha0 : 0 ≤ a := by positivity
  have hD0 : 0 ≤ D := by positivity
  have h2mem : 2 ∈ Finset.Icc 2 (n / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← Finset.add_sum_erase _ _ h2mem]
  refine add_le_add (term_two_le n hp0 hp1 (by omega)) ?_
  set s := (Finset.Icc 2 (n / 2)).erase 2
  have hs : ∀ k ∈ s, 3 ≤ k ∧ 2 * k ≤ n := by
    intro k hk
    simp only [s, Finset.mem_erase, Finset.mem_Icc] at hk
    omega
  calc ∑ k ∈ s, (n.choose k : ℝ) * ((k ^ 2).choose (k - 1) : ℝ) * p ^ (k - 1) *
        (1 - p) ^ (k * (n - k))
      ≤ ∑ k ∈ s, D * a ^ (k - 1) := Finset.sum_le_sum fun k hk ↦
        term_le n k hp0 hp1 (by linarith [(hs k hk).1]) (hs k hk).2
    _ = ∑ i ∈ s.image (· - 1), D * a ^ i := by
        rw [Finset.sum_image]
        intro k hk k' hk' h
        have := (hs k hk).1
        have := (hs k' hk').1
        simp only at h
        omega
    _ ≤ ∑ i ∈ Finset.Ico 2 n, D * a ^ i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
        intro i hi
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
        have := hs k hk
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    _ = D * ∑ i ∈ Finset.Ico 2 n, a ^ i := by rw [Finset.mul_sum]
    _ ≤ D * (a ^ 2 / (1 - a)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one ha0 (by linarith)) hD0
    _ ≤ D * (2 * a ^ 2) := by
        gcongr
        rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg a]
    _ = 2 * Real.exp 6 * n * (n * p) ^ 2 * Real.exp (-(3 * (n * p) / 2)) := by
        rw [hD, ha_def, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        have : Real.exp 6 = Real.exp 2 * Real.exp ((2 : ℕ) * 2) := by
          rw [← Real.exp_add]; norm_num
        rw [this]
        have : Real.exp (-(3 * (n * p) / 2)) =
            Real.exp (-(n * p) / 2) * Real.exp ((2 : ℕ) * (-(n * p) / 2)) := by
          rw [← Real.exp_add]; push_cast; ring_nf
        rw [this]
        ring

/-- If `y n ≥ log n - M` eventually and `c > 1`, then `n y(n)^m e^{-c y(n)} → 0`. -/
private theorem tendsto_mul_pow_mul_exp_neg (m : ℕ) {c : ℝ} (hc : 1 < c) (y : ℕ → ℝ) (M : ℝ)
    (hy : ∀ᶠ n : ℕ in atTop, Real.log n - M ≤ y n) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * y n ^ m * Real.exp (-(c * y n))) atTop (𝓝 0) := by
  set δ := (c - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K := (m.factorial : ℝ) / δ ^ m with hK
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ ↦ K * Real.exp ((c - δ) * M) *
      Real.exp ((1 - (c - δ)) * Real.log n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ Real.exp ((1 - (c - δ)) * Real.log n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by linarith) hlog)
    simpa using this.const_mul (K * Real.exp ((c - δ) * M))
  have hy0 : ∀ᶠ n : ℕ in atTop, 0 ≤ y n := by
    filter_upwards [hy, hlog.eventually_ge_atTop M] with n h1 h2
    linarith
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hy0] with n hn
    positivity
  · filter_upwards [hy, hy0, eventually_ge_atTop 1] with n h1 h2 h3
    have hn : (0 : ℝ) < n := by exact_mod_cast h3
    have hpow : y n ^ m ≤ K * Real.exp (δ * y n) := by
      have := Real.pow_div_factorial_le_exp _ (mul_nonneg hδ0.le h2) m
      rw [div_le_iff₀ (by positivity), mul_pow] at this
      rw [hK, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hkey : (n : ℝ) * Real.exp (-((c - δ) * (Real.log n - M))) =
        Real.exp ((c - δ) * M) * Real.exp ((1 - (c - δ)) * Real.log n) := by
      nth_rewrite 1 [← Real.exp_log hn]
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    calc (n : ℝ) * y n ^ m * Real.exp (-(c * y n))
        ≤ n * (K * Real.exp (δ * y n)) * Real.exp (-(c * y n)) := by gcongr
      _ = K * (n * Real.exp (-((c - δ) * y n))) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ K * (n * Real.exp (-((c - δ) * (Real.log n - M)))) := by
          gcongr
          nlinarith
      _ = K * Real.exp ((c - δ) * M) * Real.exp ((1 - (c - δ)) * Real.log n) := by
          rw [hkey]; ring

/-- The union bound for disconnected graphs without isolated vertices tends to zero as soon as
`n pₙ ≥ log n - M` eventually. -/
theorem tendsto_disconnSum (p : ℕ → I) (M : ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, Real.log n - M ≤ n * (p n : ℝ)) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 2 (n / 2), (n.choose k : ℝ) *
        ((k ^ 2).choose (k - 1) : ℝ) * (p n : ℝ) ^ (k - 1) * (1 - (p n : ℝ)) ^ (k * (n - k)))
      atTop (𝓝 0) := by
  set y : ℕ → ℝ := fun n ↦ n * (p n : ℝ) with hy
  have h1 := (tendsto_mul_pow_mul_exp_neg 1 (c := 2) (by norm_num) y M hp).const_mul
    (2 * Real.exp 4)
  have h2 := (tendsto_mul_pow_mul_exp_neg 2 (c := 3 / 2) (by norm_num) y M hp).const_mul
    (2 * Real.exp 6)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyt : Tendsto y atTop atTop :=
    tendsto_atTop_mono' atTop hp (tendsto_atTop_add_const_right _ (-M) hlog)
  have ha : Tendsto (fun n ↦ Real.exp 2 * y n * Real.exp (-(y n) / 2)) atTop (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (hyt.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul (2 * Real.exp 2)
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, pow_one]
    ring_nf
  have hsum := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun n ↦ Finset.sum_nonneg fun k _ ↦ ?_) ?_ hsum
  · have := (p n).2.1
    have : 0 ≤ 1 - (p n : ℝ) := by linarith [(p n).2.2]
    positivity
  · filter_upwards [ha.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_ge_atTop 4] with n han hn
    refine (disconnSum_le n (p n).2.1 (p n).2.2 hn han).trans (le_of_eq ?_)
    simp only [hy, pow_one]
    ring_nf

/-! ### Moments of the number of isolated vertices -/

/-- The zeroth factorial moment is one. -/
theorem isolatedMoment_zero (p : I) : isolatedMoment (V := V) p 0 = 1 := by
  simp [isolatedMoment, incidentEdges]

/-- Two-sided bounds `C(|V|, j) (1-p)^{j|V|} ≤ Sⱼ ≤ C(|V|, j) (1-p)^{j(|V|-j)}`. -/
theorem isolatedMoment_mem_Icc (p : I) (j : ℕ) :
    isolatedMoment (V := V) p j ∈ Set.Icc
      (((Fintype.card V).choose j : ℝ) * (1 - (p : ℝ)) ^ (j * Fintype.card V))
      (((Fintype.card V).choose j : ℝ) * (1 - (p : ℝ)) ^ (j * (Fintype.card V - j))) := by
  have hq0 : 0 ≤ 1 - (p : ℝ) := by linarith [p.2.2]
  have hq1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.2.1]
  have hcard : (Finset.powersetCard j (Finset.univ : Finset V)).card =
      (Fintype.card V).choose j := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  constructor
  · calc ((Fintype.card V).choose j : ℝ) * (1 - (p : ℝ)) ^ (j * Fintype.card V)
        = ∑ _J ∈ Finset.powersetCard j (Finset.univ : Finset V),
            (1 - (p : ℝ)) ^ (j * Fintype.card V) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ isolatedMoment (V := V) p j := Finset.sum_le_sum fun J hJ ↦ by
          refine pow_le_pow_of_le_one hq0 hq1 ?_
          rw [← (Finset.mem_powersetCard.mp hJ).2]
          exact card_incidentEdges_le J
  · calc isolatedMoment (V := V) p j
        ≤ ∑ _J ∈ Finset.powersetCard j (Finset.univ : Finset V),
            (1 - (p : ℝ)) ^ (j * (Fintype.card V - j)) := Finset.sum_le_sum fun J hJ ↦ by
          refine pow_le_pow_of_le_one hq0 hq1 ?_
          rw [← (Finset.mem_powersetCard.mp hJ).2]
          exact le_card_incidentEdges J
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- In a connected graph on at least two vertices no vertex is isolated. -/
theorem isolatedVertices_eq_empty_of_connected (h2 : 2 ≤ Fintype.card V) {G : SimpleGraph V}
    (hG : G.Connected) : isolatedVertices G = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  simp only [isolatedVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
    by_contra h
    push Not at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b ↦ (h a).trans (h b).symm
    omega
  obtain ⟨q⟩ := hG.preconnected v w
  cases q with
  | nil => exact hw rfl
  | cons h _ => exact hv _ h

/-- Connectivity and the absence of isolated vertices differ by at most the union bound:
`P(no isolated vertex) - T ≤ P(connected) ≤ P(no isolated vertex)` on at least two vertices. -/
theorem binomialRandom_real_connected_mem_Icc (h2 : 2 ≤ Fintype.card V) (p : I) :
    (SimpleGraph.binomialRandom V p).real {G | G.Connected} ∈ Set.Icc
      ((SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅} -
        ∑ k ∈ Finset.Icc 2 (Fintype.card V / 2), ((Fintype.card V).choose k : ℝ) *
          ((k ^ 2).choose (k - 1) : ℝ) * (p : ℝ) ^ (k - 1) *
            (1 - (p : ℝ)) ^ (k * (Fintype.card V - k)))
      ((SimpleGraph.binomialRandom V p).real {G | isolatedVertices G = ∅}) := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hsub : {G : SimpleGraph V | G.Connected} ⊆ {G | isolatedVertices G = ∅} :=
    fun G hG ↦ isolatedVertices_eq_empty_of_connected h2 hG
  constructor
  · have hcov : {G : SimpleGraph V | isolatedVertices G = ∅} ⊆
        {G | G.Connected} ∪ {G | isolatedVertices G = ∅ ∧ ¬ G.Connected} := by
      intro G hG
      by_cases hc : G.Connected
      · exact Or.inl hc
      · exact Or.inr ⟨hG, hc⟩
    have h1 := measureReal_mono (μ := SimpleGraph.binomialRandom V p) hcov (measure_ne_top _ _)
    have h3 := measureReal_union_le (μ := SimpleGraph.binomialRandom V p)
      {G : SimpleGraph V | G.Connected} {G | isolatedVertices G = ∅ ∧ ¬ G.Connected}
    have h4 := binomialRandom_real_not_connected_le (V := V) p
    linarith
  · exact measureReal_mono hsub (measure_ne_top _ _)

end CKSD
