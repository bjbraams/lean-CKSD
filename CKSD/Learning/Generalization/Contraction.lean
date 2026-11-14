module

public import CKSD.Learning.Basic

/-!
# The Ledoux–Talagrand contraction inequality for finite classes

Composing the coordinates of a finite class of vectors with an `L`-Lipschitz function
multiplies the summed Rademacher suprema by at most `L`. The proof replaces one coordinate at a
time, pairing each sign vector with the vector that flips the current coordinate.

## Main results

* `CKSD.sSup_add_sSup_le_of_lipschitz`: the one-coordinate contraction step.
* `CKSD.sum_sSup_rademacher_comp_le`: the contraction inequality.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace CKSD

/-- One-coordinate contraction step: for an `L`-Lipschitz `φ` and `c ≥ 0`,
`sup(a + cφ(u)) + sup(a - cφ(u)) ≤ sup(a + cLu) + sup(a - cLu)` over a finite index. -/
theorem sSup_add_sSup_le_of_lipschitz {H : Type*} [Fintype H] [Nonempty H] (a u : H → ℝ)
    (φ : ℝ → ℝ) {L c : ℝ} (hc : 0 ≤ c) (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) :
    sSup (range fun h ↦ a h + c * φ (u h)) + sSup (range fun h ↦ a h - c * φ (u h)) ≤
      sSup (range fun h ↦ a h + c * (L * u h)) + sSup (range fun h ↦ a h - c * (L * u h)) := by
  obtain ⟨h₁, h₁eq⟩ := exists_eq_ciSup_of_finite (f := fun h ↦ a h + c * φ (u h))
  obtain ⟨h₂, h₂eq⟩ := exists_eq_ciSup_of_finite (f := fun h ↦ a h - c * φ (u h))
  rw [show sSup (range fun h ↦ a h + c * φ (u h)) = _ from h₁eq.symm,
    show sSup (range fun h ↦ a h - c * φ (u h)) = _ from h₂eq.symm]
  have hb1 := fun k ↦ le_csSup (finite_range fun h ↦ a h + c * (L * u h)).bddAbove ⟨k, rfl⟩
  have hb2 := fun k ↦ le_csSup (finite_range fun h ↦ a h - c * (L * u h)).bddAbove ⟨k, rfl⟩
  have hlip : c * (φ (u h₁) - φ (u h₂)) ≤ c * (L * |u h₁ - u h₂|) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hφ _ _)) hc
  rcases le_total (u h₂) (u h₁) with hu | hu
  · rw [abs_of_nonneg (sub_nonneg.mpr hu)] at hlip
    have := hb1 h₁; have := hb2 h₂
    simp only at *
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hu)] at hlip
    have := hb1 h₂; have := hb2 h₁
    simp only at *
    nlinarith

/-- Ledoux–Talagrand contraction for a finite class: composing the coordinates with an
`L`-Lipschitz function multiplies the summed Rademacher suprema by at most `L`. -/
theorem sum_sSup_rademacher_comp_le {H : Type*} [Fintype H] [Nonempty H] (n : ℕ)
    (t : H → Fin n → ℝ) (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) :
    ∑ σ : Fin n → Bool, sSup (range fun h ↦
        (∑ i, (if σ i then (1 : ℝ) else -1) * φ (t h i)) / n) ≤
      L * ∑ σ : Fin n → Bool, sSup (range fun h ↦
        (∑ i, (if σ i then (1 : ℝ) else -1) * t h i) / n) := by
  set w : ℕ → H → Fin n → ℝ := fun k h i ↦ if (i : ℕ) < k then L * t h i else φ (t h i)
  set Q : ℕ → (Fin n → Bool) → ℝ := fun k σ ↦ sSup (range fun h ↦
    (∑ i, (if σ i then (1 : ℝ) else -1) * w k h i) / n)
  have hQ0 : ∀ σ, Q 0 σ = sSup (range fun h ↦
      (∑ i, (if σ i then (1 : ℝ) else -1) * φ (t h i)) / n) := fun σ ↦ by
    simp [Q, w]
  have hstep : ∀ k, k < n → ∑ σ, Q k σ ≤ ∑ σ, Q (k + 1) σ := by
    intro k hk
    set j : Fin n := ⟨k, hk⟩
    set fl : (Fin n → Bool) → (Fin n → Bool) := fun σ ↦ Function.update σ j (!σ j)
    have hfl : Function.Involutive fl := fun σ ↦ by
      funext i
      by_cases hi : i = j
      · subst hi; simp [fl]
      · simp [fl, Function.update_of_ne hi]
    have hsum_fl : ∀ F : (Fin n → Bool) → ℝ, ∑ σ, F (fl σ) = ∑ σ, F σ := fun F ↦
      Fintype.sum_equiv (hfl.toPerm fl) _ _ fun σ ↦ rfl
    -- decomposition at coordinate `j`
    set A : (Fin n → Bool) → H → ℝ := fun σ h ↦
      ∑ i ∈ Finset.univ.erase j, (if σ i then (1 : ℝ) else -1) * w k h i
    have hA : ∀ σ h, A (fl σ) h = A σ h := fun σ h ↦
      Finset.sum_congr rfl fun i hi ↦ by
        simp [fl, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hw : ∀ h, ∀ i ∈ Finset.univ.erase j, w (k + 1) h i = w k h i := by
      intro h i hi
      have hij : (i : ℕ) ≠ k := fun h' ↦ Finset.ne_of_mem_erase hi (Fin.ext h')
      simp only [w]
      congr 1
      exact propext ⟨fun h' ↦ by omega, fun h' ↦ by omega⟩
    have hAk1 : ∀ σ h, ∑ i ∈ Finset.univ.erase j,
        (if σ i then (1 : ℝ) else -1) * w (k + 1) h i = A σ h := fun σ h ↦
      Finset.sum_congr rfl fun i hi ↦ by rw [hw h i hi]
    have hdec : ∀ (k' : ℕ) (σ : Fin n → Bool) (h : H),
        (∑ i, (if σ i then (1 : ℝ) else -1) * w k' h i) / n =
        (∑ i ∈ Finset.univ.erase j, (if σ i then (1 : ℝ) else -1) * w k' h i) / n +
          (1 / n) * ((if σ j then (1 : ℝ) else -1) * w k' h j) := by
      intro k' σ h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      ring
    have hwk : ∀ h, w k h j = φ (t h j) := fun h ↦ by simp [w, j]
    have hwk1 : ∀ h, w (k + 1) h j = L * t h j := fun h ↦ by simp [w, j]
    have hflj : ∀ σ, fl σ j = !σ j := fun σ ↦ by simp [fl]
    have hpair : ∀ σ, Q k σ + Q k (fl σ) ≤ Q (k + 1) σ + Q (k + 1) (fl σ) := by
      intro σ
      simp only [Q]
      simp_rw [hdec k, hdec (k + 1), hAk1]
      change sSup (range fun h ↦ A σ h / n + 1 / n * ((if σ j then (1 : ℝ) else -1) *
          w k h j)) + sSup (range fun h ↦ A (fl σ) h / n + 1 / n *
          ((if fl σ j then (1 : ℝ) else -1) * w k h j)) ≤
        sSup (range fun h ↦ A σ h / n + 1 / n * ((if σ j then (1 : ℝ) else -1) *
          w (k + 1) h j)) + sSup (range fun h ↦ A (fl σ) h / n + 1 / n *
          ((if fl σ j then (1 : ℝ) else -1) * w (k + 1) h j))
      simp only [hA, hflj, hwk, hwk1]
      have hc : (0 : ℝ) ≤ 1 / n := by positivity
      have key := sSup_add_sSup_le_of_lipschitz (fun h ↦ A σ h / n) (fun h ↦ t h j) φ hc hφ
      cases σ j
      · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, neg_one_mul,
          one_mul, mul_neg, ← sub_eq_add_neg]
        linarith
      · simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false, neg_one_mul,
          one_mul, mul_neg, ← sub_eq_add_neg]
        linarith
    have h2 : 2 * ∑ σ, Q k σ = ∑ σ, (Q k σ + Q k (fl σ)) := by
      rw [Finset.sum_add_distrib, hsum_fl (Q k)]; ring
    have h3 : 2 * ∑ σ, Q (k + 1) σ = ∑ σ, (Q (k + 1) σ + Q (k + 1) (fl σ)) := by
      rw [Finset.sum_add_distrib, hsum_fl (Q (k + 1))]; ring
    have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) ↦ hpair σ
    linarith
  have hmono : ∀ k, k ≤ n → ∑ σ, Q 0 σ ≤ ∑ σ, Q k σ := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact (ih (by omega)).trans (hstep k (by omega))
  have hQn : ∀ σ, Q n σ ≤ L * sSup (range fun h ↦
      (∑ i, (if σ i then (1 : ℝ) else -1) * t h i) / n) := by
    intro σ
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    beta_reduce
    have : (∑ i, (if σ i then (1 : ℝ) else -1) * w n h i) / n =
        L * ((∑ i, (if σ i then (1 : ℝ) else -1) * t h i) / n) := by
      simp only [w, Fin.is_lt, ite_true]
      rw [mul_div_assoc', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (finite_range _).bddAbove ⟨h, rfl⟩) hL
  have h1 : ∑ σ : Fin n → Bool, sSup (range fun h ↦
      (∑ i, (if σ i then (1 : ℝ) else -1) * φ (t h i)) / n) = ∑ σ, Q 0 σ :=
    Finset.sum_congr rfl fun σ _ ↦ (hQ0 σ).symm
  rw [h1, Finset.mul_sum]
  exact (hmono n le_rfl).trans (Finset.sum_le_sum fun σ _ ↦ hQn σ)

end CKSD
