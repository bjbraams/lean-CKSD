module

public import CKSD.LinearModels.DirectedGraphical
public import CKSD.LinearModels.GaussianGraphical
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CKSD.LinearModels.Multivariate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-!
# Decomposable graphical models

Undirected graphs are Mathlib's `SimpleGraph`. A graph is chordal (decomposable) when every
cycle of length at least four has a chord. A perfect sequence lists the maximal cliques
`C₀, …, C_{k-1}` so that each separator `S_j = C_j ∩ (C₀ ∪ ⋯ ∪ C_{j-1})`, `j ≥ 1`, lies in an
earlier clique; separators are then counted with their multiplicities `ν(S)` by running over
`j`. A finite graph admits a perfect sequence of its maximal cliques exactly when it is chordal,
so the results below are stated for a perfect sequence only.

## Main definitions

* `CKSD.IsChordalGraph`, `CKSD.GraphSeparates`, `CKSD.IsPerfectCliqueSequence`,
  `CKSD.cliqueSeparator`.
* `CKSD.IsUndirectedGlobalMarkovMass`: separation of disjoint sets implies conditional
  independence, for a probability mass function.
* `CKSD.decomposableConcentrationMLE`: the explicit Gaussian concentration estimate
  `n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`.

## Main results

* `CKSD.isUndirectedGlobalMarkovMass_of_factorization`: a clique factorization implies the
  undirected global Markov property.
* `CKSD.graphSeparates_cliqueSeparator`: in a perfect sequence, `S_j` separates `C_j \ S_j` from
  the earlier vertices.
* `CKSD.isUndirectedGlobalMarkovMass_iff_clique_factorization`: a positive mass function is
  globally Markov exactly when `p(x) ∏_S p_S(x_S)^{ν(S)} = ∏_C p_C(x_C)`.
* `CKSD.isConcentrationMLE_decomposableConcentrationMLE` and
  `CKSD.existsUnique_isConcentrationMLE_inv`: the Gaussian maximum likelihood estimate of the
  concentration matrix for a decomposable and for a general graph.
* `CKSD.isConcentrationMLE_inv_of_apply_eq`: a positive definite `Σ` that agrees with `ssd / n`
  on the diagonal and the edges and whose inverse vanishes off the edges gives the estimate.

The general-graph estimate is obtained by maximizing `det Σ` over the compact convex set of
positive semidefinite completions of the observed entries of `ssd / n`; the first-order condition
along the non-edge directions shows that the maximizer has inverse in the concentration model,
and the strict inequality `log det S + dim < log det C + tr(S C⁻¹)` for `C ≠ S` gives strict
optimality of the likelihood.

## References

* S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996, Ch. 2, §3.2, §5.3.

Source: GAPS 105.36.
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

/-- In a finite graph every clique lies in a maximal clique. -/
theorem exists_maximal_isClique_superset [Fintype V] (G : SimpleGraph V) {T : Finset V}
    (hT : G.IsClique (T : Set V)) : ∃ D : Finset V, T ⊆ D ∧ Maximal G.IsClique (D : Set V) := by
  obtain ⟨D, hTD, hD⟩ := Finset.exists_le_maximal
    (Finset.univ.filter fun D : Finset V ↦ G.IsClique (D : Set V)) (by simpa using hT)
  refine ⟨D, hTD, ?_⟩
  have hDc : G.IsClique (D : Set V) := by simpa using hD.prop
  refine ⟨hDc, fun t ht hDt v hv ↦ ?_⟩
  have h := hD.2 (y := t.toFinset) (by simpa using ht) (fun u hu ↦ by simpa using hDt hu)
  simpa using h (show v ∈ t.toFinset by simpa using hv)

/-- The undirected global Markov property follows from a factorization of the mass function
into factors each depending only on the coordinates in a clique. -/
theorem isUndirectedGlobalMarkovMass_of_factorization [Fintype V] [Fintype S]
    (G : SimpleGraph V) {ι : Type*} [Fintype ι] (K : ι → Finset V)
    (hK : ∀ i, G.IsClique (K i : Set V)) (f : ι → (V → S) → ℝ)
    (hf : ∀ i y y', (∀ v ∈ K i, y v = y' v) → f i y = f i y') (p : (V → S) → ℝ)
    (hp : ∀ y, p y = ∏ i, f i y) : IsUndirectedGlobalMarkovMass G p := by
  intro A B C hAB hAC hBC hsep x
  -- the vertices reachable from `A` by walks avoiding `C`
  let R : Finset V := Finset.univ.filter fun v ↦ v ∉ C ∧
    ∃ a ∈ A, ∃ w : G.Walk a v, ∀ u ∈ w.support, u ∉ C
  have hext : ∀ u v, u ∈ R → v ∉ C → G.Adj u v → v ∈ R := by
    intro u v hu hv hadj
    obtain ⟨-, a, ha, w, hw⟩ := (Finset.mem_filter.1 hu).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, a, ha, w.concat hadj, fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hw z hz
    · exact hv
  let good : ι → Prop := fun i ↦ ∀ v ∈ K i, v ∈ R ∨ v ∈ C
  have hbad : ∀ i, ¬ good i → ∀ v ∈ K i, v ∉ R := by
    intro i hi v hv hvR
    simp only [good, not_forall, not_or] at hi
    obtain ⟨w, hw, hwR, hwC⟩ := hi
    have hne : v ≠ w := fun h ↦ hwR (h ▸ hvR)
    exact hwR (hext v w hvR hwC (hK i hv hw hne))
  let F : (V → S) → ℝ := fun y ↦ ∏ i ∈ Finset.univ.filter good, f i y
  let H : (V → S) → ℝ := fun y ↦ ∏ i ∈ Finset.univ.filter (fun i ↦ ¬ good i), f i y
  have hg : ∀ y, p y = F y * H y := fun y ↦ by
    rw [hp]
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hF : ∀ y y', (∀ v, v ∈ R ∨ v ∈ C → y v = y' v) → F y = F y' := fun y y' h ↦
    Finset.prod_congr rfl fun i hi ↦ hf i y y' fun v hv ↦ h v ((Finset.mem_filter.1 hi).2 v hv)
  have hH : ∀ y y', (∀ v, v ∉ R → y v = y' v) → H y = H y' := fun y y' h ↦
    Finset.prod_congr rfl fun i hi ↦ hf i y y' fun v hv ↦
      h v (hbad i (Finset.mem_filter.1 hi).2 v hv)
  have hAR : A ⊆ R := fun a ha ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    Finset.disjoint_left.1 hAC ha, a, ha, SimpleGraph.Walk.nil, by
      simpa using Finset.disjoint_left.1 hAC ha⟩
  have hBR : Disjoint B R := Finset.disjoint_left.2 fun b hb hbR ↦ by
    obtain ⟨-, a, ha, w, hw⟩ := (Finset.mem_filter.1 hbR).2
    obtain ⟨v, hv, hvC⟩ := hsep a ha b hb w
    exact hw v hv hvC
  have hCR : Disjoint C R :=
    Finset.disjoint_left.2 fun c hc hcR ↦ (Finset.mem_filter.1 hcR).2.1 hc
  exact sum_ite_mul_sum_ite_of_factor p F H A B C R x hg hF hH hAR hBR hCR

/-- The union `C₀ ∪ ⋯ ∪ C_{m-1}` of the first `m` cliques of a sequence. -/
def cliqueHistory {k : ℕ} (C : Fin k → Finset V) (m : ℕ) : Finset V :=
  (Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < m).biUnion C

/-- For a perfect sequence of the maximal cliques, the separator `S_j` separates the new
vertices `C_j \ S_j` from the earlier vertices `(C₀ ∪ ⋯ ∪ C_{j-1}) \ S_j`. -/
theorem graphSeparates_cliqueSeparator [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (C : Fin k → Finset V) (hC : IsPerfectCliqueSequence G C) (j : Fin k) :
    GraphSeparates G ↑(C j \ cliqueSeparator C j) ↑(cliqueHistory C j \ cliqueSeparator C j)
      ↑(cliqueSeparator C j) := by
  obtain ⟨-, hmax, hall, hrip⟩ := hC
  have hsepH : ∀ m : Fin k, cliqueSeparator C m = C m ∩ cliqueHistory C m := fun _ ↦ rfl
  -- a parent of each clique in the running intersection property
  let par : Fin k → Fin k := fun m ↦ if h : 0 < (m : ℕ) then Classical.choose (hrip m h) else m
  have hpar : ∀ m : Fin k, 0 < (m : ℕ) → par m < m ∧ cliqueSeparator C m ⊆ C (par m) := by
    intro m hm
    simp only [par, dite_eq_left hm]
    exact Classical.choose_spec (hrip m hm)
  have hparle : ∀ m, par m ≤ m := by
    intro m
    by_cases hm : 0 < (m : ℕ)
    · exact (hpar m hm).1.le
    · simp only [par, dite_eq_right hm, le_refl]
  have hiter_le : ∀ n m, par^[n] m ≤ m := by
    intro n
    induction n with
    | zero => intro m; exact le_rfl
    | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply]
      exact (ih (par m)).trans (hparle m)
  let Sub : Fin k → Prop := fun m ↦ ∃ n, par^[n] m = j
  have hSub_le : ∀ m, Sub m → j ≤ m := by
    rintro m ⟨n, hn⟩
    rw [← hn]
    exact hiter_le n m
  -- the cliques containing a vertex form a subtree
  have hL2 : ∀ v a b, v ∈ C a → Sub a → v ∈ C b → ¬ Sub b →
      v ∈ cliqueSeparator C j := by
    intro v a b hva hSa hvb hSb
    have hne : (Finset.univ.filter fun i ↦ v ∈ C i).Nonempty := ⟨a, by simp [hva]⟩
    set f := (Finset.univ.filter fun i ↦ v ∈ C i).min' hne with hf
    have hfv : v ∈ C f := by
      have := Finset.min'_mem _ hne
      simpa [← hf] using this
    have hfmin : ∀ i, v ∈ C i → f ≤ i := fun i hi ↦ Finset.min'_le _ _ (by simp [hi])
    have chain : ∀ N : ℕ, ∀ m : Fin k, (m : ℕ) = N → v ∈ C m →
        ∃ n, par^[n] m = f ∧ ∀ n' ≤ n, v ∈ C (par^[n'] m) := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
      intro m hmN hvm
      by_cases hmf : m = f
      · exact ⟨0, hmf, fun n' hn' ↦ by
          obtain rfl : n' = 0 := by omega
          exact hvm⟩
      have hfm : f < m := lt_of_le_of_ne (hfmin m hvm) (Ne.symm hmf)
      have hm0 : 0 < (m : ℕ) := lt_of_le_of_lt (Nat.zero_le _) (Fin.lt_def.1 hfm)
      have hvS : v ∈ cliqueSeparator C m := by
        rw [hsepH]
        refine Finset.mem_inter.2 ⟨hvm, ?_⟩
        simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, Fin.lt_def.1 hfm, hfv⟩
      obtain ⟨hlt, hsub⟩ := hpar m hm0
      obtain ⟨n, hn, hall'⟩ := ih (par m) (by rw [← hmN]; exact Fin.lt_def.1 hlt) _ rfl
        (hsub hvS)
      refine ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn, fun n' hn' ↦ ?_⟩
      rcases n' with _ | n'
      · exact hvm
      · rw [Function.iterate_succ_apply]
        exact hall' n' (by omega)
    obtain ⟨na, hna⟩ := hSa
    obtain ⟨n1, hn1, hv1⟩ := chain _ a rfl hva
    obtain ⟨n2, hn2, -⟩ := chain _ b rfl hvb
    have hfj : ¬ Sub f := by
      rintro ⟨t, ht⟩
      exact hSb ⟨t + n2, by rw [Function.iterate_add_apply, hn2, ht]⟩
    have hna1 : na ≤ n1 := by
      by_contra hlt
      apply hfj
      refine ⟨na - n1, ?_⟩
      rw [← hn1, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega), hna]
    have hvj : v ∈ C j := hna ▸ hv1 na hna1
    have hfj' : f < j := lt_of_le_of_ne (hfmin j hvj) fun h ↦ hfj ⟨0, h⟩
    rw [hsepH]
    refine Finset.mem_inter.2 ⟨hvj, ?_⟩
    simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, Fin.lt_def.1 hfj', hfv⟩
  -- labels: lying in a clique of the subtree of `j`
  let L : V → Prop := fun v ↦ ∃ m, Sub m ∧ v ∈ C m
  intro a ha b hb w
  by_contra hno
  push Not at hno
  have hLa : L a := ⟨j, ⟨0, rfl⟩, (Finset.mem_sdiff.1 ha).1⟩
  have hLb : ¬ L b := by
    rintro ⟨m, hSm, hbm⟩
    obtain ⟨hbH, hbS⟩ := Finset.mem_sdiff.1 hb
    simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at hbH
    obtain ⟨i, hi, hbi⟩ := hbH
    exact hbS (hL2 b m i hbm hSm hbi fun hSi ↦ absurd (hSub_le i hSi) (by
      rw [not_le, Fin.lt_def]; exact hi))
  obtain ⟨d, hd, hLu, hLv⟩ := w.exists_boundary_dart {v | L v} hLa hLb
  have hu : d.fst ∈ w.support := w.dart_fst_mem_support_of_mem_darts hd
  set u := d.fst
  set v := d.snd
  have huv : G.Adj u v := d.adj
  have hpair : G.IsClique (({u, v} : Finset V) : Set V) := by
    rw [Finset.coe_pair]
    exact SimpleGraph.isClique_pair.2 fun _ ↦ huv
  obtain ⟨D, hD, hDmax⟩ := exists_maximal_isClique_superset G hpair
  obtain ⟨m, rfl⟩ := hall D hDmax
  by_cases hSm : Sub m
  · exact hLv ⟨m, hSm, hD (by simp)⟩
  · obtain ⟨m', hSm', hum'⟩ := hLu
    exact hno u hu (hL2 u m' m hum' hSm' (hD (by simp)) hSm)

/-- For a perfect sequence of the maximal cliques, the global Markov property implies the
clique factorization of the marginal masses. -/
theorem clique_factorization_of_isUndirectedGlobalMarkovMass [Fintype V] [Fintype S]
    (G : SimpleGraph V) {k : ℕ} (C : Fin k → Finset V) (hC : IsPerfectCliqueSequence G C)
    (p : (V → S) → ℝ) (hp : IsProbabilityMass p) (hGM : IsUndirectedGlobalMarkovMass G p)
    (x : V → S) :
    p x * ∏ j : Fin k, (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) =
      ∏ j, marginalMass p (C j) x := by
  have hsepH : ∀ m : Fin k, cliqueSeparator C m = C m ∩ cliqueHistory C m := fun _ ↦ rfl
  have key : ∀ m, m ≤ k →
      marginalMass p (cliqueHistory C m) x *
          ∏ j ∈ Finset.univ.filter (fun j : Fin k ↦ (j : ℕ) < m),
            (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin k ↦ (j : ℕ) < m), marginalMass p (C j) x := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : cliqueHistory C 0 = ∅ := by simp [cliqueHistory]
      simp only [h0, Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, mul_one]
      unfold marginalMass
      simpa using hp.2
    | succ m ih =>
      intro hm
      set j : Fin k := ⟨m, by omega⟩ with hjdef
      have hfil : Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < m + 1) =
          insert j (Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < m) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hjdef,
          Fin.ext_iff]
        omega
      have hjn : j ∉ Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < m := by simp [hjdef]
      have hH : cliqueHistory C (m + 1) = cliqueHistory C m ∪ C j := by
        rw [cliqueHistory, hfil, Finset.biUnion_insert, Finset.union_comm]
        rfl
      have hstep : marginalMass p (cliqueHistory C (m + 1)) x *
          (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) =
          marginalMass p (cliqueHistory C m) x * marginalMass p (C j) x := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · have h0 : cliqueHistory C m = ∅ := by
            subst hm0
            simp [cliqueHistory]
          have hj0 : (j : ℕ) = 0 := hm0
          rw [hH, h0, Finset.empty_union, ite_eq_left hj0]
          have h1 : marginalMass p ∅ x = 1 := by
            unfold marginalMass
            simpa using hp.2
          rw [h1]
          ring
        · have hjm : (j : ℕ) = m := rfl
          rw [ite_eq_right (by omega)]
          have hsepj : cliqueSeparator C j = C j ∩ cliqueHistory C m := by
            rw [hsepH, hjm]
          have hci := hGM (C j \ cliqueSeparator C j) (cliqueHistory C m \ cliqueSeparator C j)
            (cliqueSeparator C j)
            (by
              rw [Finset.disjoint_left]
              intro v hv hv'
              exact (Finset.mem_sdiff.1 hv).2 (by
                rw [hsepj]
                exact Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hv).1, (Finset.mem_sdiff.1 hv').1⟩))
            Finset.sdiff_disjoint Finset.sdiff_disjoint
            (by
              have := graphSeparates_cliqueSeparator G C hC j
              rwa [hjm] at this) x
          have e1 : C j \ cliqueSeparator C j ∪ (cliqueHistory C m \ cliqueSeparator C j) ∪
              cliqueSeparator C j = cliqueHistory C (m + 1) := by
            rw [hH, hsepj]
            ext v
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
            tauto
          have e2 : C j \ cliqueSeparator C j ∪ cliqueSeparator C j = C j := by
            rw [hsepj]
            ext v
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
            tauto
          have e3 : cliqueHistory C m \ cliqueSeparator C j ∪ cliqueSeparator C j =
              cliqueHistory C m := by
            rw [hsepj]
            ext v
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
            tauto
          rw [e1, e2, e3] at hci
          rw [hci]
          ring
      rw [hfil, Finset.prod_insert hjn, Finset.prod_insert hjn, ← ih (by omega)]
      calc marginalMass p (cliqueHistory C (m + 1)) x *
            ((if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) *
              ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < m),
                (if (i : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C i) x))
          = (marginalMass p (cliqueHistory C (m + 1)) x *
              (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x)) *
            ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < m),
              (if (i : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C i) x) := by ring
        _ = _ := by rw [hstep]; ring
  have hall : cliqueHistory C k = Finset.univ := by
    refine Finset.eq_univ_of_forall fun v ↦ ?_
    obtain ⟨D, hD, hDmax⟩ := exists_maximal_isClique_superset G
      (T := {v}) (by simp)
    obtain ⟨m, rfl⟩ := hC.2.2.1 D hDmax
    simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, m.isLt, hD (by simp)⟩
  have hfk : Finset.univ.filter (fun j : Fin k ↦ (j : ℕ) < k) = Finset.univ := by
    ext j
    simp
  have := key k le_rfl
  rwa [hall, hfk, marginalMass_univ] at this

/-- GAPS 105.36, discrete form: for a decomposable graph with a perfect sequence of its maximal
cliques, a positive probability mass function is globally Markov exactly when
`p(x) = ∏_C p_C(x_C) / ∏_S p_S(x_S)^{ν(S)}`, written here without division. -/
theorem isUndirectedGlobalMarkovMass_iff_clique_factorization [Fintype V] [Fintype S]
    (G : SimpleGraph V) {k : ℕ} (C : Fin k → Finset V)
    (hC : IsPerfectCliqueSequence G C) (p : (V → S) → ℝ) (hp : IsProbabilityMass p)
    (hpos : ∀ x, 0 < p x) :
    IsUndirectedGlobalMarkovMass G p ↔
      ∀ x, p x * ∏ j : Fin k, (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) x) =
        ∏ j, marginalMass p (C j) x := by
  constructor
  · exact fun hGM x ↦ clique_factorization_of_isUndirectedGlobalMarkovMass G C hC p hp hGM x
  · intro hfac
    have hp0 : ∀ y, 0 ≤ p y := hp.1
    have hMpos : ∀ (E : Finset V) y, 0 < marginalMass p E y := fun E y ↦ by
      have := marginalMass_anti hp0 (Finset.subset_univ E) y
      rw [marginalMass_univ] at this
      exact lt_of_lt_of_le (hpos y) this
    have hsepC : ∀ j, cliqueSeparator C j ⊆ C j := fun j ↦ Finset.inter_subset_left
    let K : Fin k ⊕ Fin k → Finset V := Sum.elim C (cliqueSeparator C)
    let f : Fin k ⊕ Fin k → (V → S) → ℝ := Sum.elim (fun j y ↦ marginalMass p (C j) y)
      (fun j y ↦ if (j : ℕ) = 0 then 1 else (marginalMass p (cliqueSeparator C j) y)⁻¹)
    refine isUndirectedGlobalMarkovMass_of_factorization G K ?_ f ?_ p ?_
    · rintro (j | j)
      · exact (hC.2.1 j).prop
      · exact (hC.2.1 j).prop.subset (Finset.coe_subset.2 (hsepC j))
    · rintro (j | j) y y' h
      · exact marginalMass_congr_point p _ h
      · simp only [f, Sum.elim_inr]
        rw [marginalMass_congr_point p (cliqueSeparator C j) (x := y) (x' := y') h]
    · intro y
      rw [Fintype.prod_sum_type]
      simp only [f, Sum.elim_inl, Sum.elim_inr]
      rw [← hfac y, mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ j : Fin k, (if (j : ℕ) = 0 then 1 else marginalMass p (cliqueSeparator C j) y) *
          (if (j : ℕ) = 0 then 1 else (marginalMass p (cliqueSeparator C j) y)⁻¹) = 1 := by
        intro j
        split_ifs
        · ring
        · exact mul_inv_cancel₀ (hMpos _ y).ne'
      simp only [this, Finset.prod_const_one, mul_one]

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block `B_{CC}` of a square matrix indexed by a finite set `C` of coordinates. -/
def principalBlock (B : Matrix ι ι ℝ) (C : Finset ι) : Matrix C C ℝ :=
  B.submatrix Subtype.val Subtype.val

/-- `[B]^V`: a matrix indexed by `C`, padded with zeros to a square matrix indexed by `ι`. -/
def padBlock (C : Finset ι) (B : Matrix C C ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if h : i ∈ C ∧ j ∈ C then B ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The explicit maximum likelihood estimate of the concentration matrix in a decomposable
Gaussian graphical model with perfect sequence of cliques `C`:
`n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`, the separators being counted with
multiplicity. -/
def decomposableConcentrationMLE {k : ℕ} (C : Fin k → Finset ι) (n : ℕ)
    (ssd : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (n : ℝ) • (∑ j, padBlock (C j) (principalBlock ssd (C j))⁻¹ -
    ∑ j : Fin k, if (j : ℕ) = 0 then 0 else
      padBlock (cliqueSeparator C j) (principalBlock ssd (cliqueSeparator C j))⁻¹)

/-- GAPS 105.36, Gaussian decomposable model: for a perfect sequence `C` of the maximal cliques
of `G` (so that `G` is decomposable) and `n > 0` observations, if every clique block of the
sum-of-squares matrix `ssd` is positive definite (which holds almost surely when
`n > max_C |C|` for a Gaussian sample), the maximum likelihood estimate of the concentration
matrix exists, is unique, and equals `n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`.
The likelihood involves `ssd` only through its clique blocks, so no condition on `ssd` outside
them is needed. The almost-sure existence criterion `n > max_C |C|` as a necessary condition
is not stated. -/
theorem isConcentrationMLE_decomposableConcentrationMLE (G : SimpleGraph ι) {k : ℕ}
    (C : Fin k → Finset ι) (hC : IsPerfectCliqueSequence G C) (n : ℕ) (hn : 0 < n)
    (ssd : Matrix ι ι ℝ) (hblock : ∀ j, (principalBlock ssd (C j)).PosDef) :
    IsConcentrationMLE G n ssd (decomposableConcentrationMLE C n ssd) := by
  sorry

/-- Strict form of the Gaussian covariance criterion on a general finite index type: for positive
definite `S ≠ C`, `log det S + dim < log det C + tr(S C⁻¹)`. -/
theorem log_det_add_card_lt_log_det_add_trace_mul_inv {S C : Matrix ι ι ℝ} (hS : S.PosDef)
    (hC : C.PosDef) (hne : C ≠ S) :
    Real.log S.det + Fintype.card ι < Real.log C.det + (S * C⁻¹).trace := by
  let e := Fintype.equivFin ι
  have hS' : (reindex e e S).PosDef := hS.submatrix e.symm.injective
  have hC' : (reindex e e C).PosDef := hC.submatrix e.symm.injective
  have hle := log_det_add_card_le_log_det_add_trace_mul_inv _ _ hS' hC'
  have hiff := log_det_add_card_eq_log_det_add_trace_mul_inv_iff _ _ hS' hC'
  have htr : (reindex e e S * (reindex e e C)⁻¹).trace = (S * C⁻¹).trace := by
    rw [inv_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv]
    simp only [trace]
    exact Equiv.sum_comp e.symm (fun i ↦ (S * C⁻¹) i i)
  rw [det_reindex_self, det_reindex_self, htr] at hle hiff
  have hne' : reindex e e C ≠ reindex e e S := fun h ↦ hne ((reindex e e).injective h)
  exact lt_of_le_of_ne hle fun h ↦ hne' (hiff.1 h)

/-- Sufficiency of the likelihood equations: if `Σ` is positive definite, agrees with `ssd / n` on
the diagonal and on the edges of `G`, and `Σ⁻¹` vanishes off the edges, then `Σ⁻¹` is the
maximum likelihood estimate of the concentration matrix. -/
theorem isConcentrationMLE_inv_of_apply_eq (G : SimpleGraph ι) {n : ℕ}
    (ssd Sig : Matrix ι ι ℝ) (hSig : Sig.PosDef)
    (hmatch : ∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n)
    (hzero : ∀ i j, i ≠ j → ¬ G.Adj i j → Sig⁻¹ i j = 0) :
    IsConcentrationMLE G n ssd Sig⁻¹ := by
  have hmem : Sig⁻¹ ∈ concentrationModel G := ⟨hSig.inv, hzero⟩
  have htr : ∀ K ∈ concentrationModel G, trace (K * ssd) / n = trace (K * Sig) := by
    intro K hK
    simp only [trace, diag_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases h : i = j ∨ G.Adj i j
    · rw [hmatch j i (h.imp Eq.symm fun hij ↦ hij.symm)]
      ring
    · push Not at h
      rw [hK.2 i j h.1 h.2]
      simp
  refine ⟨hmem, fun K' hK' hne ↦ ?_⟩
  have hdet (A : Matrix ι ι ℝ) (hA : A.PosDef) : Real.log A⁻¹.det = - Real.log A.det := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
  have hne' : K'⁻¹ ≠ Sig := fun h ↦
    hne (by rw [← h, nonsing_inv_nonsing_inv _ hK'.1.det_pos.ne'.isUnit])
  have key := log_det_add_card_lt_log_det_add_trace_mul_inv hSig hK'.1.inv hne'
  rw [nonsing_inv_nonsing_inv _ hK'.1.det_pos.ne'.isUnit, hdet K' hK'.1, trace_mul_comm] at key
  unfold gaussianConcentrationLogLikelihood
  rw [htr K' hK', htr _ hmem, nonsing_inv_mul _ hSig.det_pos.ne'.isUnit, trace_one,
    hdet Sig hSig]
  linarith

open scoped MatrixOrder in
/-- A positive definite matrix dominates a positive multiple of the identity. -/
theorem exists_pos_posSemidef_sub_smul_one {Sig : Matrix ι ι ℝ} [Nonempty ι] (hSig : Sig.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (Sig - c • (1 : Matrix ι ι ℝ)).PosSemidef := by
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff Sig hSig.isHermitian.isSelfAdjoint).2
    fun x hx ↦ hSig.isStrictlyPositive.spectrum_pos hx
  refine ⟨r, hr, ?_⟩
  rw [← Matrix.le_iff]
  simpa [Algebra.algebraMap_eq_smul_one] using hle

/-- The symmetric matrix with ones at `(i, j)` and `(j, i)`. -/
private def symmSingle (i j : ι) : Matrix ι ι ℝ := single i j 1 + single j i 1

/-- `(E_{ij} + E_{ji}) x = x_j eᵢ + x_i eⱼ`. -/
private theorem symmSingle_mulVec (i j : ι) (x : ι → ℝ) :
    symmSingle i j *ᵥ x = Pi.single i (x j) + Pi.single j (x i) := by
  simp [symmSingle, add_mulVec, single_mulVec]
  rfl

/-- A small symmetric perturbation at `(i, j)` and `(j, i)` keeps a positive definite matrix
positive semidefinite. -/
private theorem posSemidef_add_smul_symmSingle {Sig : Matrix ι ι ℝ} (hSig : Sig.PosDef) {i j : ι}
    (hij : i ≠ j) : ∃ δ > 0, ∀ t : ℝ, |t| ≤ δ → (Sig + t • symmSingle i j).PosSemidef := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨c, hc, hpsd⟩ := exists_pos_posSemidef_sub_smul_one hSig
  refine ⟨c, hc, fun t ht ↦ ?_⟩
  have hE : (symmSingle i j).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, symmSingle, transpose_add,
      transpose_single, transpose_single, add_comm]
  have h2 : (c • (1 : Matrix ι ι ℝ) + t • symmSingle i j).PosSemidef := by
    have hH : (c • (1 : Matrix ι ι ℝ) + t • symmSingle i j).IsHermitian := by
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
        conjTranspose_one, hE.eq]
      simp
    refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x ↦ ?_
    have hsq : x i * x i + x j * x j ≤ x ⬝ᵥ x := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k ↦ x k * x k)
        (Finset.subset_univ {i, j}) fun k _ _ ↦ mul_self_nonneg (x k)
      simpa [dotProduct, Finset.sum_pair hij] using this
    simp only [star_trivial, add_mulVec, smul_mulVec, one_mulVec, symmSingle_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul]
    have h1 : -(c * (x i * x i + x j * x j)) ≤ t * (x i * x j + x j * x i) := by
      have habs : |t * (x i * x j + x j * x i)| ≤ c * (x i * x i + x j * x j) := by
        rw [abs_mul]
        have : |x i * x j + x j * x i| ≤ x i * x i + x j * x j := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
        calc |t| * |x i * x j + x j * x i| ≤ c * |x i * x j + x j * x i| :=
              mul_le_mul_of_nonneg_right ht (abs_nonneg _)
          _ ≤ c * (x i * x i + x j * x j) := mul_le_mul_of_nonneg_left this hc.le
      exact (abs_le.1 habs).1
    nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
  have := hpsd.add h2
  rwa [show Sig - c • 1 + (c • 1 + t • symmSingle i j) = Sig + t • symmSingle i j by abel]
    at this

/-- The determinant along the line `Σ + t (E_{ij} + E_{ji})`, by the matrix determinant lemma:
`det Σ · ((1 + t K_{ji})(1 + t K_{ij}) - t² K_{jj} K_{ii})` with `K = Σ⁻¹`. -/
private theorem det_add_smul_symmSingle {Sig : Matrix ι ι ℝ} (hSig : Sig.PosDef) {i j : ι}
    (hij : i ≠ j) (t : ℝ) : (Sig + t • symmSingle i j).det = Sig.det *
      ((1 + t * Sig⁻¹ j i) * (1 + t * Sig⁻¹ i j) - t * Sig⁻¹ j j * (t * Sig⁻¹ i i)) := by
  let U : Matrix ι (Fin 2) ℝ := t • (1 : Matrix ι ι ℝ).submatrix id ![i, j]
  let V : Matrix (Fin 2) ι ℝ := (1 : Matrix ι ι ℝ).submatrix ![j, i] id
  have hUV : U * V = t • symmSingle i j := by
    simp only [U, V, Matrix.smul_mul]
    congr 1
    ext k l
    simp only [Matrix.mul_apply, Fin.sum_univ_two, submatrix_apply, id, symmSingle,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h1 : k = i <;> by_cases h2 : k = j <;> by_cases h3 : l = i <;>
      by_cases h4 : l = j <;> simp_all [Ne.symm hij, eq_comm]
  have hVKU : V * Sig⁻¹ * U = t • Sig⁻¹.submatrix ![j, i] ![i, j] := by
    simp only [U, V, Matrix.mul_smul]
    congr 1
    have hV : (1 : Matrix ι ι ℝ).submatrix ![j, i] id * Sig⁻¹ = Sig⁻¹.submatrix ![j, i] id :=
      one_submatrix_mul ![j, i] (Equiv.refl ι) Sig⁻¹
    rw [hV]
    exact mul_submatrix_one (Equiv.refl ι) ![i, j] _
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) + V * Sig⁻¹ * U =
      !![1 + t * Sig⁻¹ j i, t * Sig⁻¹ j j; t * Sig⁻¹ i i, 1 + t * Sig⁻¹ i j] := by
    rw [hVKU]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
    fin_cases a <;> fin_cases b <;> simp
  rw [← hUV, det_add_mul U V hSig.det_pos.ne'.isUnit, h2, det_fin_two_of]

/-- An entry of a positive semidefinite matrix is bounded by the mean of the two diagonal
entries. -/
private theorem abs_apply_le_of_posSemidef {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    |S i j| ≤ (S i i + S j j) / 2 := by
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hS.diag_nonneg)]
    linarith
  have hsymm : S j i = S i j := by
    simpa using (hS.isHermitian.apply j i).symm
  have h1 := hS.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hS.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    mulVec_single, single_dotProduct, hsymm] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Existence of the solution of the likelihood equations: maximizing `det Σ` over the compact
set of positive semidefinite `Σ` that agree with `ssd / n` on the diagonal and on the edges gives
a positive definite `Σ` whose inverse vanishes off the edges, by the first-order condition along
each direction `E_{ij} + E_{ji}` for a non-edge `{i, j}`. -/
private theorem exists_posDef_apply_eq_of_inv_apply_eq_zero (G : SimpleGraph ι) {n : ℕ}
    (hn : 0 < n) (ssd : Matrix ι ι ℝ) (hssd : ssd.PosDef) :
    ∃ Sig : Matrix ι ι ℝ, Sig.PosDef ∧
      (∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n) ∧
      ∀ i j, i ≠ j → ¬ G.Adj i j → Sig⁻¹ i j = 0 := by
  let F : Set (Matrix ι ι ℝ) :=
    {S | S.PosSemidef ∧ ∀ i j, (i = j ∨ G.Adj i j) → S i j = ssd i j / n}
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  let T : Matrix ι ι ℝ := (n : ℝ)⁻¹ • ssd
  have hT : T.PosDef := hssd.smul (inv_pos.2 hn')
  have hTF : T ∈ F := ⟨hT.posSemidef, fun i j _ ↦ by simp [T, div_eq_inv_mul]⟩
  have hclosed : IsClosed F := by
    have hF : F = {S : Matrix ι ι ℝ | S.PosSemidef} ∩
        ⋂ i, ⋂ j, {S : Matrix ι ι ℝ | (i = j ∨ G.Adj i j) → S i j = ssd i j / n} := by
      ext S
      simp [F]
    rw [hF]
    refine isClosed_setOfPred_posSemidef.inter
      (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_)
    by_cases h : i = j ∨ G.Adj i j
    · simp only [h, true_implies]
      exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
    · simp [h]
  let R : ℝ := ∑ k, |ssd k k / n|
  have hR (k : ι) : |ssd k k / n| ≤ R :=
    Finset.single_le_sum (f := fun k ↦ |ssd k k / n|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ k)
  have hsub : F ⊆ Set.pi univ fun _ : ι ↦ Set.pi univ fun _ : ι ↦ Icc (-R) R := by
    intro S hS i _ j _
    have h := abs_apply_le_of_posSemidef hS.1 i j
    rw [hS.2 i i (Or.inl rfl), hS.2 j j (Or.inl rfl)] at h
    have := (le_abs_self (ssd i i / n)).trans (hR i)
    have := (le_abs_self (ssd j j / n)).trans (hR j)
    exact abs_le.1 (h.trans (by linarith))
  have hcompact : IsCompact F :=
    (isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset
      hclosed hsub
  obtain ⟨S, hSF, hmax⟩ := hcompact.exists_isMaxOn ⟨T, hTF⟩
    (continuous_id.matrix_det).continuousOn
  have hdetS : 0 < S.det := hT.det_pos.trans_le (hmax hTF)
  have hS : S.PosDef := hSF.1.posDef_iff_isUnit.2
    ((isUnit_iff_isUnit_det S).2 hdetS.ne'.isUnit)
  refine ⟨S, hS, hSF.2, fun i j hij hadj ↦ ?_⟩
  by_contra hq
  obtain ⟨δ, hδ, hpsd⟩ := posSemidef_add_smul_symmSingle hS hij
  set q := S⁻¹ i j with hqdef
  have hqji : S⁻¹ j i = q := by
    simpa using (hS.inv.isHermitian.apply i j)
  set D := q ^ 2 - S⁻¹ i i * S⁻¹ j j with hD
  have hq' : 0 < |q| := abs_pos.2 hq
  set s := min (δ / |q|) (1 / (|D| + 1)) with hsdef
  have hs : 0 < s := lt_min (div_pos hδ hq') (div_pos one_pos (by positivity))
  have hs1 : s ≤ δ / |q| := min_le_left _ _
  have hs2 : s ≤ 1 / (|D| + 1) := min_le_right _ _
  have ht : |s * q| ≤ δ := by
    rw [abs_mul, abs_of_pos hs]
    calc s * |q| ≤ δ / |q| * |q| := mul_le_mul_of_nonneg_right hs1 hq'.le
      _ = δ := div_mul_cancel₀ δ hq'.ne'
  have hmem : S + (s * q) • symmSingle i j ∈ F := by
    refine ⟨hpsd _ ht, fun a b hab ↦ ?_⟩
    have hE : symmSingle i j a b = 0 := by
      simp only [symmSingle, Matrix.add_apply, single_apply]
      have h1 : ¬ (i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        rcases hab with h | h
        · exact hij h
        · exact hadj h
      have h2 : ¬ (j = a ∧ i = b) := by
        rintro ⟨rfl, rfl⟩
        rcases hab with h | h
        · exact hij h.symm
        · exact hadj h.symm
      simp [h1, h2]
    simp [Matrix.add_apply, Matrix.smul_apply, hE, hSF.2 a b hab]
  have hle : (S + (s * q) • symmSingle i j).det ≤ S.det := hmax hmem
  rw [det_add_smul_symmSingle hS hij, hqji, ← hqdef] at hle
  have hsD : -1 < s * D := by
    have h1 : s * |D| < 1 := by
      calc s * |D| ≤ 1 / (|D| + 1) * |D| := mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
        _ < 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
          linarith
    have := neg_abs_le D
    nlinarith
  have hf : 1 < (1 + s * q * q) * (1 + s * q * q) - s * q * S⁻¹ j j * (s * q * S⁻¹ i i) := by
    have : (1 + s * q * q) * (1 + s * q * q) - s * q * S⁻¹ j j * (s * q * S⁻¹ i i) =
        1 + s * q ^ 2 * (2 + s * D) := by
      rw [hD]
      ring
    rw [this]
    have : 0 < s * q ^ 2 * (2 + s * D) := by
      have : 0 < q ^ 2 := by positivity
      exact mul_pos (mul_pos hs this) (by linarith)
    linarith
  nlinarith

/-- GAPS 105.36, general graph: if `ssd` is positive definite and `n > 0`, there is a unique
positive definite `Σ̂` that agrees with `ssd / n` on the diagonal and on the edges and whose
inverse is the maximum likelihood estimate of the concentration matrix (in particular `Σ̂⁻¹`
vanishes off the edges). Convergence of iterative proportional scaling is not stated. -/
theorem existsUnique_isConcentrationMLE_inv (G : SimpleGraph ι) (n : ℕ) (hn : 0 < n)
    (ssd : Matrix ι ι ℝ) (hssd : ssd.PosDef) :
    ∃! Sig : Matrix ι ι ℝ, Sig.PosDef ∧
      (∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n) ∧
      IsConcentrationMLE G n ssd Sig⁻¹ := by
  obtain ⟨Sig, hpd, hmatch, hzero⟩ := exists_posDef_apply_eq_of_inv_apply_eq_zero G hn ssd hssd
  have hMLE := isConcentrationMLE_inv_of_apply_eq G ssd Sig hpd hmatch hzero
  refine ⟨Sig, ⟨hpd, hmatch, hMLE⟩, ?_⟩
  rintro Sig' ⟨hpd', -, hMLE'⟩
  by_contra hne
  have hne' : Sig'⁻¹ ≠ Sig⁻¹ := fun h ↦ hne (by
    rw [← nonsing_inv_nonsing_inv Sig' hpd'.det_pos.ne'.isUnit, h,
      nonsing_inv_nonsing_inv Sig hpd.det_pos.ne'.isUnit])
  have h1 := hMLE.2 _ hMLE'.1 hne'
  have h2 := hMLE'.2 _ hMLE.1 hne'.symm
  linarith

end Gaussian

end CKSD
