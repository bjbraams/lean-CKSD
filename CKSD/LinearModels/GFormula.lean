module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Data.Fin.Tuple.Basic


/-!
# The longitudinal g-formula for discrete covariates

Covariates `L t` take values in a finite type and treatments `A t` in an arbitrary type; both
are given as sequences, of which only the times `0, …, T` are used. A covariate record is a
tuple `l : Fin m → 𝓛`. Conditional probabilities and conditional means given an event are
quotients by the probability of the event, with Lean's convention `x / 0 = 0`.

The proof first establishes the inverse-probability-weighted representation by induction on
the number of time points, partitioning each regime-adherent past by the next covariate value,
and then telescopes the weights into the sequential factorization of the g-formula.

## Main definitions

* `CKSD.gHistoryEvent`: the observed history `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}`.
* `CKSD.gRegimeEvent`: the regime-adherent past `{L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1}}`.

## Main results

* `CKSD.integral_eq_sum_g_inverse_weight`: the inverse-probability-weighted representation of
  the mean of a potential outcome.
* `CKSD.integral_potential_outcome_eq_g_formula`: Robins' g-formula for the mean of the
  potential outcome under a static treatment regime (GAPS 105.65).

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Math. Modelling 7 (1986).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace CKSD

variable {Ω 𝓛 𝓐 : Type*}

/-- The observed-history event `{L̄_k = l̄_k, Ā_{k-1} = ā_{k-1}}` for a covariate record `l`:
the covariates up to time `k` take the recorded values and the treatments before time `k`
follow the regime `a`. -/
def gHistoryEvent (L : ℕ → Ω → 𝓛) (A : ℕ → Ω → 𝓐) (a : ℕ → 𝓐) {m : ℕ} (l : Fin m → 𝓛)
    (k : ℕ) : Set Ω :=
  {ω | ∀ s : Fin m, (s : ℕ) < k + 1 → L s ω = l s ∧ ((s : ℕ) < k → A s ω = a s)}

/-- The regime-adherent past `{L̄_{k-1} = l̄_{k-1}, Ā_{k-1} = ā_{k-1}}` before time `k`;
it is the whole space for `k = 0`. -/
def gRegimeEvent (L : ℕ → Ω → 𝓛) (A : ℕ → Ω → 𝓐) (a : ℕ → 𝓐) {m : ℕ} (l : Fin m → 𝓛)
    (k : ℕ) : Set Ω :=
  {ω | ∀ s : Fin m, (s : ℕ) < k → L s ω = l s ∧ A s ω = a s}

section Events

variable (L : ℕ → Ω → 𝓛) (A : ℕ → Ω → 𝓐) (a : ℕ → 𝓐)

/-- History events depend only on the recorded covariates up to the current time. -/
theorem g_history_event_congr {m m' : ℕ} (l : Fin m → 𝓛) (l' : Fin m' → 𝓛) (k : ℕ)
    (hm : k < m) (hm' : k < m')
    (hl : ∀ i (hi : i < k + 1), l ⟨i, by omega⟩ = l' ⟨i, by omega⟩) :
    gHistoryEvent L A a l k = gHistoryEvent L A a l' k := by
  ext ω
  simp only [gHistoryEvent, mem_ofPred_eq]
  constructor
  · intro h s hs
    have := h ⟨s, by omega⟩ hs
    rw [← hl s hs] at *
    exact this
  · intro h s hs
    have := h ⟨s, by omega⟩ hs
    rw [hl s hs]
    exact this

/-- Regime-adherent pasts depend only on the recorded covariates before the current time. -/
theorem g_regime_event_congr {m m' : ℕ} (l : Fin m → 𝓛) (l' : Fin m' → 𝓛) (k : ℕ)
    (hm : k ≤ m) (hm' : k ≤ m')
    (hl : ∀ i (hi : i < k), l ⟨i, by omega⟩ = l' ⟨i, by omega⟩) :
    gRegimeEvent L A a l k = gRegimeEvent L A a l' k := by
  ext ω
  simp only [gRegimeEvent, mem_ofPred_eq]
  constructor
  · intro h s hs
    have := h ⟨s, by omega⟩ hs
    rw [← hl s hs] at *
    exact this
  · intro h s hs
    have := h ⟨s, by omega⟩ hs
    rw [hl s hs]
    exact this

/-- The history event at time `k` is contained in the regime-adherent past before `k`. -/
theorem g_history_event_subset_g_regime_event {m : ℕ} (l : Fin m → 𝓛) (k : ℕ) :
    gHistoryEvent L A a l k ⊆ gRegimeEvent L A a l k := by
  intro ω h s hs
  exact ⟨(h s (by omega)).1, (h s (by omega)).2 hs⟩

/-- Appending the next covariate value splits the regime-adherent past. -/
theorem g_history_event_snoc {n : ℕ} (l : Fin n → 𝓛) (x : 𝓛) :
    gHistoryEvent L A a (Fin.snoc l x : Fin (n + 1) → 𝓛) n =
      gRegimeEvent L A a l n ∩ {ω | L n ω = x} := by
  ext ω
  simp only [gHistoryEvent, gRegimeEvent, mem_inter_iff, mem_ofPred_eq]
  rw [Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, Fin.snoc_last, lt_irrefl,
    IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨fun s _ ↦ ⟨(h s (by omega)).1, (h s (by omega)).2 s.isLt⟩, h' (by omega)⟩
  · rintro ⟨h, h'⟩
    exact ⟨fun s _ ↦ ⟨(h s s.isLt).1, fun _ ↦ (h s s.isLt).2⟩, fun _ ↦ h'⟩

variable {L A} [MeasurableSpace Ω]

/-- History events are measurable when the coordinate events are. -/
theorem measurable_set_g_history_event (hL : ∀ t x, MeasurableSet {ω | L t ω = x})
    (hA : ∀ t x, MeasurableSet {ω | A t ω = x}) {m : ℕ} (l : Fin m → 𝓛) (k : ℕ) :
    MeasurableSet (gHistoryEvent L A a l k) := by
  simp only [gHistoryEvent, ofPred_forall]
  refine MeasurableSet.iInter fun s ↦ ?_
  by_cases h₁ : (s : ℕ) < k + 1
  · by_cases h₂ : (s : ℕ) < k
    · simpa [h₁, h₂, ofPred_and] using (hL s (l s)).inter (hA s (a s))
    · simpa [h₁, h₂] using hL s (l s)
  · simp [h₁]

/-- Regime-adherent pasts are measurable when the coordinate events are. -/
theorem measurable_set_g_regime_event (hL : ∀ t x, MeasurableSet {ω | L t ω = x})
    (hA : ∀ t x, MeasurableSet {ω | A t ω = x}) {m : ℕ} (l : Fin m → 𝓛) (k : ℕ) :
    MeasurableSet (gRegimeEvent L A a l k) := by
  simp only [gRegimeEvent, ofPred_forall]
  refine MeasurableSet.iInter fun s ↦ ?_
  by_cases h₁ : (s : ℕ) < k
  · simpa [h₁, ofPred_and] using (hL s (l s)).inter (hA s (a s))
  · simp [h₁]

end Events

/-- Telescoping of sequential weights: for real weights with the zero pattern of
probabilities of nested events, the inverse treatment weights times the final probability
equal the product of the conditional covariate probabilities. -/
theorem prod_div_succ_mul_eq_prod_div (h g : ℕ → ℝ) (N : ℕ) (hg0 : g 0 = 1)
    (hg : ∀ k, g k = 0 → h k = 0) (hg' : ∀ k < N, g (k + 1) = 0 → h k = 0) :
    ∀ n ≤ N, (∏ k ∈ Finset.range n, h k / g (k + 1)) * g n =
      ∏ k ∈ Finset.range n, h k / g k := by
  intro n
  induction n with
  | zero => intro _; simp [hg0]
  | succ n ih =>
    intro hn
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih (by omega)]
    by_cases h₁ : g (n + 1) = 0
    · simp [h₁, hg' n (by omega) h₁]
    by_cases h₀ : g n = 0
    · simp [h₀, hg n h₀]
    field_simp

/-- Inverse-probability-weighted representation over the first `n` time points. If at each
time `k < N` the potential outcome is mean-exchangeable with the treatment given the observed
history, and regime-adherent continuations of histories of positive probability have positive
probability, then for `n ≤ N` the mean of `Ya` is the sum over covariate records of the
inverse treatment weights times the integral of `Ya` over the regime-adherent event. -/
theorem integral_eq_sum_g_inverse_weight [MeasurableSpace Ω] [Fintype 𝓛] (P : Measure Ω)
    [IsFiniteMeasure P] (L : ℕ → Ω → 𝓛) (A : ℕ → Ω → 𝓐) (a : ℕ → 𝓐)
    (hL : ∀ t x, MeasurableSet {ω | L t ω = x}) (hA : ∀ t x, MeasurableSet {ω | A t ω = x})
    (Ya : Ω → ℝ) (hYa : Integrable Ya P) (N : ℕ)
    (hexch : ∀ n < N, ∀ l : Fin (n + 1) → 𝓛,
      (∫ ω in gRegimeEvent L A a l (n + 1), Ya ω ∂P) * P.real (gHistoryEvent L A a l n) =
        (∫ ω in gHistoryEvent L A a l n, Ya ω ∂P) * P.real (gRegimeEvent L A a l (n + 1)))
    (hpos : ∀ n < N, ∀ l : Fin (n + 1) → 𝓛,
      P.real (gRegimeEvent L A a l (n + 1)) = 0 → P.real (gHistoryEvent L A a l n) = 0) :
    ∀ n ≤ N, ∫ ω, Ya ω ∂P = ∑ l : Fin n → 𝓛,
      (∏ k ∈ Finset.range n,
        P.real (gHistoryEvent L A a l k) / P.real (gRegimeEvent L A a l (k + 1))) *
        ∫ ω in gRegimeEvent L A a l n, Ya ω ∂P := by
  intro n
  induction n with
  | zero =>
    intro _
    have : gRegimeEvent L A a (fun i : Fin 0 ↦ (Fin.elim0 i : 𝓛)) 0 = univ := by
      ext ω; simp [gRegimeEvent]
    simp [gRegimeEvent]
  | succ n ih =>
    intro hn
    rw [ih (by omega)]
    -- decompose the sum over records of length `n + 1`
    rw [← (Fin.snocEquiv fun _ : Fin (n + 1) ↦ 𝓛).sum_comp, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Fin.snocEquiv_apply]
    -- partition the regime-adherent past by the next covariate value
    have hpart : gRegimeEvent L A a l n =
        ⋃ x, gHistoryEvent L A a (Fin.snoc l x : Fin (n + 1) → 𝓛) n := by
      ext ω
      simp only [g_history_event_snoc, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h ↦ ⟨L n ω, h, rfl⟩, fun ⟨_, h, _⟩ ↦ h⟩
    rw [hpart, integral_iUnion_fintype
      (fun x ↦ measurable_set_g_history_event a hL hA _ n)
      (fun x y hxy ↦ by
        rw [Function.onFun, g_history_event_snoc, g_history_event_snoc]
        exact Disjoint.inter_left' _ (Disjoint.inter_right' _
          (disjoint_left.2 fun ω hx hy ↦ hxy (hx.symm.trans hy))))
      (fun x ↦ hYa.integrableOn), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    set l' : Fin (n + 1) → 𝓛 := Fin.snoc l x
    have hprod : ∀ k ∈ Finset.range n,
        P.real (gHistoryEvent L A a l' k) / P.real (gRegimeEvent L A a l' (k + 1)) =
          P.real (gHistoryEvent L A a l k) / P.real (gRegimeEvent L A a l (k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [g_history_event_congr L A a l' l k (by omega) hk (fun i hi ↦ by
          simp only [l']
          exact Fin.snoc_castSucc (α := fun _ ↦ 𝓛) (p := l) (x := x) (i := ⟨i, by omega⟩)),
        g_regime_event_congr L A a l' l (k + 1) (by omega) hk (fun i hi ↦ by
          simp only [l']
          exact Fin.snoc_castSucc (α := fun _ ↦ 𝓛) (p := l) (x := x) (i := ⟨i, by omega⟩))]
    rw [Finset.prod_range_succ, Finset.prod_congr rfl hprod, mul_assoc]
    congr 1
    -- exchangeability at time `n`
    have he := hexch n (by omega) l'
    by_cases h0 : P.real (gRegimeEvent L A a l' (n + 1)) = 0
    · have hh := hpos n (by omega) l' h0
      rw [h0, hh]
      simp only [div_zero, zero_mul]
      exact setIntegral_measure_zero (f := Ya) ((measureReal_eq_zero_iff).1 hh)
    · field_simp
      linarith

/-- GAPS 105.65: the longitudinal g-formula for discrete covariates.
Covariates `L t` take values in a finite type and treatments `A t` in any type, at times
`t = 0, …, T`; `l` ranges over covariate records `(l_0, …, l_T)`, `Ya` is the potential
outcome under the regime `a` and `Y` the observed outcome. Consistency is `Y = Ya` whenever the
observed treatments follow the regime. Sequential exchangeability is used in its mean form,
`E[Ya 1{A_t = a_t} | H_t, Ā_{t-1} = ā_{t-1}] = E[Ya | H_t, Ā_{t-1} = ā_{t-1}] P(A_t = a_t | …)`,
written without division; it is implied by `Ya ⊥ A_t | H_t, Ā_{t-1} = ā_{t-1}`. Sequential
positivity is `P(A_t = a_t | H_t, Ā_{t-1} = ā_{t-1}) > 0` for every observed history of positive
probability, written as: a regime-adherent continuation of probability zero comes from a
history of probability zero (it follows from any uniform lower bound on these conditional
probabilities). The
`t = 0` factor of the product is `P(L_0 = l_0)`, since the regime-adherent past before time
`0` is the whole space. The iterated-conditional-expectation form and the general kernel form
are not stated. -/
theorem integral_potential_outcome_eq_g_formula [MeasurableSpace Ω] [Fintype 𝓛] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (L : ℕ → Ω → 𝓛) (A : ℕ → Ω → 𝓐) (a : ℕ → 𝓐)
    (hL : ∀ t x, MeasurableSet {ω | L t ω = x}) (hA : ∀ t x, MeasurableSet {ω | A t ω = x})
    (Y Ya : Ω → ℝ) (hYa : Integrable Ya P)
    (hcons : ∀ ω, (∀ t ≤ T, A t ω = a t) → Y ω = Ya ω)
    (hexch : ∀ t ≤ T, ∀ l : Fin (T + 1) → 𝓛,
      (∫ ω in gRegimeEvent L A a l (t + 1), Ya ω ∂P) * P.real (gHistoryEvent L A a l t) =
        (∫ ω in gHistoryEvent L A a l t, Ya ω ∂P) * P.real (gRegimeEvent L A a l (t + 1)))
    (hpos : ∀ t ≤ T, ∀ l : Fin (T + 1) → 𝓛,
      P.real (gRegimeEvent L A a l (t + 1)) = 0 → P.real (gHistoryEvent L A a l t) = 0) :
    ∫ ω, Ya ω ∂P = ∑ l : Fin (T + 1) → 𝓛,
      (∫ ω in gRegimeEvent L A a l (T + 1), Y ω ∂P) / P.real (gRegimeEvent L A a l (T + 1)) *
        ∏ t ∈ Finset.range (T + 1),
          P.real (gHistoryEvent L A a l t) / P.real (gRegimeEvent L A a l t) := by
  -- extension of a record of length `n + 1 ≤ T + 1` to a full record
  have hext : ∀ n ≤ T, ∀ l : Fin (n + 1) → 𝓛, ∃ l' : Fin (T + 1) → 𝓛,
      gHistoryEvent L A a l n = gHistoryEvent L A a l' n ∧
        gRegimeEvent L A a l (n + 1) = gRegimeEvent L A a l' (n + 1) := by
    intro n hn l
    refine ⟨fun s ↦ if h : (s : ℕ) < n + 1 then l ⟨s, h⟩ else l 0, ?_, ?_⟩
    · exact g_history_event_congr L A a _ _ n (by omega) (by omega) fun i hi ↦ by simp [hi]
    · exact g_regime_event_congr L A a _ _ (n + 1) le_rfl (by omega) fun i hi ↦ by simp [hi]
  have hipw := integral_eq_sum_g_inverse_weight P L A a hL hA Ya hYa (T + 1)
    (fun n hn l ↦ by
      obtain ⟨l', h₁, h₂⟩ := hext n (by omega) l
      rw [h₁, h₂]; exact hexch n (by omega) l')
    (fun n hn l ↦ by
      obtain ⟨l', h₁, h₂⟩ := hext n (by omega) l
      rw [h₁, h₂]; exact hpos n (by omega) l')
    (T + 1) le_rfl
  rw [hipw]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hmeas := measurable_set_g_regime_event a hL hA l (T + 1)
  have hY : (∫ ω in gRegimeEvent L A a l (T + 1), Y ω ∂P) =
      ∫ ω in gRegimeEvent L A a l (T + 1), Ya ω ∂P :=
    setIntegral_congr_fun hmeas fun ω hω ↦ hcons ω fun t ht ↦ (hω ⟨t, by omega⟩ (by simp; omega)).2
  rw [hY]
  have htel := prod_div_succ_mul_eq_prod_div (fun k ↦ P.real (gHistoryEvent L A a l k))
    (fun k ↦ P.real (gRegimeEvent L A a l k)) (T + 1)
    (by simp [gRegimeEvent])
    (fun k hk ↦ le_antisymm (hk ▸ measureReal_mono
      (g_history_event_subset_g_regime_event L A a l k)) measureReal_nonneg)
    (fun k hk ↦ hpos k (by omega) l) (T + 1) le_rfl
  rw [← htel]
  by_cases h0 : P.real (gRegimeEvent L A a l (T + 1)) = 0
  · rw [setIntegral_measure_zero (f := Ya) ((measureReal_eq_zero_iff).1 h0)]
    simp
  · field_simp

end CKSD
