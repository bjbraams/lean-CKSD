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
  have hwalk : ∀ {a b : V} (w : G.Walk a b), L a → ¬ L b →
      ∃ u v, G.Adj u v ∧ u ∈ w.support ∧ L u ∧ ¬ L v := by
    intro a b w
    induction w with
    | nil => intro h h'; exact absurd h h'
    | @cons a c b hac w ih =>
      intro ha hb
      by_cases hc : L c
      · obtain ⟨u, v, huv, hu, hLu, hLv⟩ := ih hc hb
        exact ⟨u, v, huv, by simp [hu], hLu, hLv⟩
      · exact ⟨a, c, hac, by simp, ha, hc⟩
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
  obtain ⟨u, v, huv, hu, hLu, hLv⟩ := hwalk w hLa hLb
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
