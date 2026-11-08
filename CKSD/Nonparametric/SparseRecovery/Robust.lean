module

public import CKSD.Nonparametric.SparseRecovery.Nullspace

/-!
# Stable sparse recovery from restricted isometry

The robust null space property, deduced from the restricted isometry property by the block
argument with the sharpened restricted orthogonality bound, and the resulting stable recovery
guarantee for basis pursuit with noisy measurements.

## Main definitions

* `CKSD.HasRobustNullspaceProperty A s ρ τ`: for every `v` and every set `S` of at most `s`
  coordinates, `‖v_S‖₂ ≤ ρ / √s ‖v_{Sᶜ}‖₁ + τ ‖A v‖`.

## Main results

* `CKSD.hasRobustNullspaceProperty_of_hasRestrictedIsometry`: the restricted isometry property
  of order `2 s` with constant `δ < 4 / √41` gives the robust null space property with
  constants `ρ(δ) < 1` and `τ(δ)`.
* `CKSD.exists_basisPursuit_error_bound`: stable recovery by basis pursuit,
  `‖b - β‖₁ ≤ C σ_s(β)₁ + D √s η` and `‖b - β‖₂ ≤ C σ_s(β)₁ / √s + D η`, with constants
  depending only on `δ`.

Source: GAPS 103.49.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The robust null space property of order `s` with constants `ρ` and `τ`: for every `v` and
every set `S` of at most `s` coordinates, `‖v_S‖₂ ≤ ρ / √s ‖v_{Sᶜ}‖₁ + τ ‖A v‖`. -/
def HasRobustNullspaceProperty {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n)) (s : ℕ) (ρ τ : ℝ) : Prop :=
  ∀ (v : EuclideanSpace ℝ (Fin p)) (S : Finset (Fin p)), S.card ≤ s →
    Real.sqrt (∑ j ∈ S, v j ^ 2) ≤ ρ / Real.sqrt s * restrictedL1Norm Sᶜ v + τ * ‖A v‖

/-- The tail blocks of a decreasing block decomposition are controlled by the lifting bound:
`∑_{k ≥ 1} ‖v_{B_k}‖ ≤ (‖v‖₁ - ‖v_{B_0}‖₁) / √s + ‖v_{B_0}‖ / 4`. -/
theorem sum_norm_blockVector_succ_le {p s : ℕ} (hs : 0 < s) (v : EuclideanSpace ℝ (Fin p))
    {ℓ : Fin p → ℕ} (hcmp : ∀ i j, ℓ j < ℓ i → |v i| ≤ |v j|)
    (hcard : ∀ k, (Finset.univ.filter fun j ↦ ℓ j = k).card ≤ s)
    (hfull : ∀ k, (∃ i, k < ℓ i) → (Finset.univ.filter fun j ↦ ℓ j = k).card = s)
    (hℓlt : ∀ j, ℓ j < p) :
    ∑ k ∈ Finset.range p, ‖blockVector ℓ v (k + 1)‖ ≤
      (restrictedL1Norm Finset.univ v - ∑ j ∈ Finset.univ.filter (fun j ↦ ℓ j = 0), |v j|) /
        Real.sqrt s + ‖blockVector ℓ v 0‖ / 4 := by
  classical
  set lev : ℕ → Finset (Fin p) := fun k ↦ Finset.univ.filter fun j ↦ ℓ j = k with hlev
  have hmemlev : ∀ k j, j ∈ lev k ↔ ℓ j = k := fun k j ↦ by simp [lev]
  set vk : ℕ → EuclideanSpace ℝ (Fin p) := blockVector ℓ v with hvk
  have hnorm_sq : ∀ k, ‖vk k‖ ^ 2 = ∑ j ∈ lev k, v j ^ 2 := norm_blockVector_sq ℓ v
  have hnorm : ∀ k, ‖vk k‖ = Real.sqrt (∑ j ∈ lev k, |v j| ^ 2) := by
    intro k
    simp only [sq_abs]
    rw [← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  set L : ℕ → ℝ := fun k ↦ ∑ j ∈ lev k, |v j| with hL
  have hsumL : ∑ k ∈ Finset.range p, L k = restrictedL1Norm Finset.univ v :=
    sum_range_sum_abs_eq_restrictedL1Norm ℓ hℓlt v
  have hLp : L p = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have := hℓlt j
    rw [hmemlev] at hj; omega
  have hsumL1 : ∑ k ∈ Finset.range p, L (k + 1) = restrictedL1Norm Finset.univ v - L 0 := by
    have := Finset.sum_range_succ' L p
    rw [Finset.sum_range_succ, hLp, add_zero, hsumL] at this
    linarith
  -- block maxima and minima
  set Mx : ℕ → ℝ := fun k ↦ if h : (lev k).Nonempty then (lev k).sup' h (fun j ↦ |v j|) else 0
    with hMx
  set Mn : ℕ → ℝ := fun k ↦ if h : (lev k).Nonempty ∧ (lev k).card = s then
    (lev k).inf' h.1 (fun j ↦ |v j|) else 0 with hMn
  have hMx_ge : ∀ k, ∀ j ∈ lev k, |v j| ≤ Mx k := by
    intro k j hj
    have hne : (lev k).Nonempty := ⟨j, hj⟩
    simp only [hMx]
    rw [dite_eq_left hne]
    exact Finset.le_sup' (fun j ↦ |v j|) hj
  have hMn_le : ∀ k, ∀ j ∈ lev k, Mn k ≤ |v j| := by
    intro k j hj
    simp only [hMn]
    split_ifs with h
    · exact Finset.inf'_le (fun j ↦ |v j|) hj
    · exact abs_nonneg _
  have hMn0 : ∀ k, 0 ≤ Mn k := by
    intro k
    simp only [hMn]
    split_ifs with h
    · exact Finset.le_inf' _ _ fun j _ ↦ abs_nonneg _
    · exact le_rfl
  have hMnMx : ∀ k, Mn k ≤ Mx k := by
    intro k
    by_cases h : (lev k).Nonempty
    · obtain ⟨j, hj⟩ := h
      exact (hMn_le k j hj).trans (hMx_ge k j hj)
    · have h1 : Mx k = 0 := by simp only [hMx]; rw [dite_eq_right h]
      have h2 : Mn k = 0 := by
        simp only [hMn]
        rw [dite_eq_right (fun h' : (lev k).Nonempty ∧ (lev k).card = s ↦ h h'.1)]
      rw [h1, h2]
  have hMn_full : ∀ k, (lev k).card < s → Mn k = 0 := by
    intro k hk
    simp only [hMn]
    rw [dite_eq_right (fun h' : (lev k).Nonempty ∧ (lev k).card = s ↦ by omega)]
  have hstep : ∀ k, Mx (k + 1) ≤ Mn k := by
    intro k
    by_cases h : (lev (k + 1)).Nonempty
    · obtain ⟨i, hi⟩ := h
      have hc : (lev k).card = s := hfull k ⟨i, by rw [hmemlev] at hi; omega⟩
      have hne : (lev k).Nonempty := Finset.card_pos.mp (by omega)
      have hne1 : (lev (k + 1)).Nonempty := ⟨i, hi⟩
      have hne2 : (lev k).Nonempty ∧ (lev k).card = s := ⟨hne, hc⟩
      simp only [hMx, hMn]
      rw [dite_eq_left hne1, dite_eq_left hne2]
      refine Finset.sup'_le _ _ fun a ha ↦ Finset.le_inf' _ _ fun b hb ↦ ?_
      rw [hmemlev] at ha hb
      exact hcmp a b (by omega)
    · simp only [hMx]; rw [dite_eq_right h]; exact hMn0 k
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
  have hMx1 : Real.sqrt s * Mx 1 ≤ ‖vk 0‖ := by
    by_cases h : (lev 1).Nonempty
    · obtain ⟨i, hi⟩ := h
      have hc : (lev 0).card = s := hfull 0 ⟨i, by rw [hmemlev] at hi; omega⟩
      have hMx0 : 0 ≤ Mx 1 := (abs_nonneg _).trans (hMx_ge 1 i hi)
      have hb : ∀ b ∈ lev 0, Mx 1 ≤ |v b| := by
        intro b hb
        have hne1 : (lev 1).Nonempty := ⟨i, hi⟩
        simp only [hMx]
        rw [dite_eq_left hne1]
        refine Finset.sup'_le _ _ fun a ha ↦ ?_
        rw [hmemlev] at ha hb
        exact hcmp a b (by omega)
      refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
      rw [hnorm_sq, mul_pow, hss]
      calc (s : ℝ) * Mx 1 ^ 2 = ∑ _j ∈ lev 0, Mx 1 ^ 2 := by
            rw [Finset.sum_const, hc, nsmul_eq_mul]
        _ ≤ ∑ j ∈ lev 0, v j ^ 2 := Finset.sum_le_sum fun j hj ↦ by
            rw [← sq_abs (v j)]
            exact pow_le_pow_left₀ hMx0 (hb j hj) 2
    · simp only [hMx]; rw [dite_eq_right h, mul_zero]; exact norm_nonneg _
  have htele : ∀ K, ∑ k ∈ Finset.range (K + 1), (Mx (k + 1) - Mn (k + 1)) ≤ Mx 1 - Mn (K + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have := hstep (K + 1)
      linarith
  have htele' : ∑ k ∈ Finset.range p, (Mx (k + 1) - Mn (k + 1)) ≤ Mx 1 := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · rw [hp]; simp only [Finset.range_zero, Finset.sum_empty]
      exact (hMn0 1).trans (hMnMx 1)
    · have := htele (p - 1)
      rw [Nat.sub_add_cancel hp] at this
      linarith [hMn0 p]
  set Sc := restrictedL1Norm Finset.univ v - L 0 with hSc
  have hblock : ∀ k ∈ Finset.range p, ‖vk (k + 1)‖ ≤
      L (k + 1) / Real.sqrt s + Real.sqrt s / 4 * (Mx (k + 1) - Mn (k + 1)) := by
    intro k _
    rw [hnorm]
    exact sqrt_sum_sq_le_sum_div_sqrt_add (lev (k + 1)) (fun j ↦ |v j|) hs (hcard (k + 1))
      (hMn0 _) (hMnMx _) (fun j hj ↦ ⟨hMn_le _ j hj, hMx_ge _ j hj⟩) (hMn_full _)
  calc ∑ k ∈ Finset.range p, ‖vk (k + 1)‖ ≤ ∑ k ∈ Finset.range p,
        (L (k + 1) / Real.sqrt s + Real.sqrt s / 4 * (Mx (k + 1) - Mn (k + 1))) :=
        Finset.sum_le_sum hblock
    _ = Sc / Real.sqrt s + Real.sqrt s / 4 * ∑ k ∈ Finset.range p, (Mx (k + 1) - Mn (k + 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hsumL1]
    _ ≤ Sc / Real.sqrt s + Real.sqrt s / 4 * Mx 1 := by gcongr
    _ ≤ Sc / Real.sqrt s + ‖vk 0‖ / 4 := by linarith

/-- The restricted isometry step for the leading block. Let `A` have the restricted isometry
property of order `2 s` with constant `δ < 4 / √41`, let `u` and the `w k` be `s`-sparse with
the support of `u` disjoint from those of the `w k`, and suppose that
`⟪A u, z⟫ = ‖A u‖² + ∑_{k < K} ⟪A u, A w_k⟫` (as for `z = A v` with `v = u + ∑ w_k`) and
`∑_{k < K} ‖w_k‖ ≤ c / √s + ‖u‖ / 4`. Then `‖u‖ ≤ ρ(δ) c / √s + τ(δ) ‖z‖`. -/
theorem norm_le_ripNullspaceRho_mul_add_of_hasRestrictedIsometry {n p s : ℕ} (hs : 0 < s)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) (hrip : HasRestrictedIsometry A (2 * s) δ)
    (u : EuclideanSpace ℝ (Fin p)) (w : ℕ → EuclideanSpace ℝ (Fin p)) (K : ℕ)
    (hu : sparsity u ≤ s) (hw : ∀ k, sparsity (w k) ≤ s) (hdisj : ∀ k j, u j = 0 ∨ w k j = 0)
    (z : EuclideanSpace ℝ (Fin n))
    (hz : ⟪A u, z⟫ = ‖A u‖ ^ 2 + ∑ k ∈ Finset.range K, ⟪A u, A (w k)⟫)
    {Sc : ℝ} (hSc0 : 0 ≤ Sc) (hX : ∑ k ∈ Finset.range K, ‖w k‖ ≤ Sc / Real.sqrt s + ‖u‖ / 4) :
    ‖u‖ ≤ ripNullspaceRho δ / Real.sqrt s * Sc + ripNullspaceTau δ * ‖z‖ := by
  obtain ⟨hden, hρ0, hρ1, hτ0, hδ1⟩ := ripNullspace_constants hδ
  have hδ0 : 0 ≤ δ := hδ.1
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  set X := ∑ k ∈ Finset.range K, ‖w k‖ with hXdef
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ ↦ norm_nonneg _
  set N0 := ‖u‖ with hN0
  rcases (norm_nonneg u).eq_or_lt with h0 | h0
  · rw [hN0, ← h0]
    exact add_nonneg (mul_nonneg (div_nonneg hρ0 hsqrt.le) hSc0)
      (mul_nonneg hτ0.le (norm_nonneg _))
  rw [← hN0] at h0
  set t := ‖A u‖ ^ 2 / N0 ^ 2 - 1 with htdef
  have ht : ‖A u‖ ^ 2 = (1 + t) * N0 ^ 2 := by rw [htdef]; field_simp; ring
  have hrip0 := hrip u (hu.trans (by omega))
  rw [ht] at hrip0
  have hN2 : 0 < N0 ^ 2 := by positivity
  have htlo : -δ ≤ t := by
    have := le_of_mul_le_mul_right hrip0.1 hN2; linarith
  have hthi : t ≤ δ := by
    have := le_of_mul_le_mul_right hrip0.2 hN2; linarith
  set D := δ ^ 2 - t ^ 2 with hD
  have hinner_k : ∀ k ∈ Finset.range K,
      |⟪A u, A (w k)⟫| ≤ Real.sqrt D * N0 * ‖w k‖ := by
    intro k _
    rcases hδ0.eq_or_lt with hδz | hδpos
    · have := abs_inner_apply_le_of_hasRestrictedIsometry A δ hrip _ _ hu (hw k) (hdisj k)
      rw [← hδz, zero_mul, zero_mul] at this
      exact this.trans (by positivity)
    · exact abs_inner_apply_le_sqrt_of_hasRestrictedIsometry A hδpos hrip _ _ hu (hw k)
        (hdisj k) t ht
  have hAsq : ‖A u‖ ^ 2 ≤ ‖A u‖ * ‖z‖ + Real.sqrt D * N0 * X := by
    have h0' := hz
    have hle1 : ⟪A u, z⟫ ≤ ‖A u‖ * ‖z‖ := real_inner_le_norm _ _
    have hb : ∀ k ∈ Finset.range K, -(Real.sqrt D * N0 * ‖w k‖) ≤
        ⟪A u, A (w k)⟫ := fun k hk ↦ (abs_le.mp (hinner_k k hk)).1
    have := Finset.sum_le_sum hb
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at this
    linarith
  have h1t : 0 < 1 + t := by linarith
  set q := Real.sqrt (1 + t) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr h1t
  have hq2 : q ^ 2 = 1 + t := Real.sq_sqrt h1t.le
  have hAv0 : ‖A u‖ = q * N0 := by
    rw [← Real.sqrt_sq (norm_nonneg (A u)), ht, Real.sqrt_mul h1t.le,
      Real.sqrt_sq h0.le]
  rw [hAv0] at hAsq
  have hstep1 : q ^ 2 * N0 ≤ q * ‖z‖ + Real.sqrt D * X := by
    have : N0 * (q ^ 2 * N0) ≤ N0 * (q * ‖z‖ + Real.sqrt D * X) := by
      have e1 : N0 * (q ^ 2 * N0) = (q * N0) ^ 2 := by ring
      have e2 : N0 * (q * ‖z‖ + Real.sqrt D * X) =
          q * N0 * ‖z‖ + Real.sqrt D * N0 * X := by ring
      rw [e1, e2]; exact hAsq
    exact le_of_mul_le_mul_left this h0
  set r := Real.sqrt (1 - δ ^ 2) with hr
  have hδsq : δ ^ 2 < 1 := pow_lt_one₀ hδ0 hδ1 two_ne_zero
  have hr2 : r ^ 2 = 1 - δ ^ 2 := Real.sq_sqrt (by linarith)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hDr : Real.sqrt D * r ≤ q ^ 2 * δ := by
    rcases le_or_gt D 0 with hDn | hDp
    · rw [Real.sqrt_eq_zero'.mpr hDn, zero_mul]; positivity
    have hsD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDp.le
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, hsD, hr2, hq2, hD]
    have e : (1 + t) ^ 2 * δ ^ 2 - (δ ^ 2 - t ^ 2) * (1 - δ ^ 2) = (t + δ ^ 2) ^ 2 := by ring
    linarith [sq_nonneg (t + δ ^ 2)]
  have hstep2 : N0 ≤ ‖z‖ / q + δ / r * X := by
    have hsDle : Real.sqrt D ≤ q ^ 2 * δ / r := by rw [le_div_iff₀ hr0]; exact hDr
    have : q ^ 2 * N0 ≤ q ^ 2 * (‖z‖ / q + δ / r * X) := by
      have e : q ^ 2 * (‖z‖ / q + δ / r * X) = q * ‖z‖ + q ^ 2 * δ / r * X := by
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_right hsDle hX0
      linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have h1δ : 0 < 1 - δ := by linarith
  have hqge : Real.sqrt (1 - δ) ≤ q := Real.sqrt_le_sqrt (by linarith)
  have hsq1δ : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr h1δ
  have hstep3 : ‖z‖ / q ≤ ‖z‖ / Real.sqrt (1 - δ) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hsq1δ hqge
  have hstep4 : N0 ≤ ‖z‖ / Real.sqrt (1 - δ) + δ / r * (Sc / Real.sqrt s + N0 / 4) := by
    have : δ / r * X ≤ δ / r * (Sc / Real.sqrt s + N0 / 4) :=
      mul_le_mul_of_nonneg_left hX (div_nonneg hδ0 hr0.le)
    linarith
  have hkey : (4 * r - δ) * N0 ≤
      4 * r * (‖z‖ / Real.sqrt (1 - δ)) + 4 * δ * (Sc / Real.sqrt s) := by
    have e : 4 * r * (δ / r * (Sc / Real.sqrt s + N0 / 4)) =
        4 * δ * (Sc / Real.sqrt s) + δ * N0 := by field_simp
    have := mul_le_mul_of_nonneg_left hstep4 (by positivity : (0:ℝ) ≤ 4 * r)
    rw [mul_add, e] at this
    linarith
  have hfinal : N0 ≤ (4 * r * (‖z‖ / Real.sqrt (1 - δ)) + 4 * δ * (Sc / Real.sqrt s)) /
      (4 * r - δ) := by
    rw [le_div_iff₀ hden]; linarith
  refine hfinal.trans (le_of_eq ?_)
  unfold ripNullspaceRho ripNullspaceTau
  rw [← hr]
  field_simp
  ring

/-- GAPS 103.49, robust null space property: if `A` has the RIP of order `2 s` with constant
`0 ≤ δ < 4 / √41`, then `‖v_S‖₂ ≤ ρ(δ) / √s ‖v_{Sᶜ}‖₁ + τ(δ) ‖A v‖` for every `v` and every set
`S` of at most `s` coordinates. -/
theorem hasRobustNullspaceProperty_of_hasRestrictedIsometry {n p s : ℕ} (hs : 0 < s)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) (hrip : HasRestrictedIsometry A (2 * s) δ) :
    HasRobustNullspaceProperty A s (ripNullspaceRho δ) (ripNullspaceTau δ) := by
  classical
  intro v S hS
  obtain ⟨-, hρ0, -, -, -⟩ := ripNullspace_constants hδ
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast hs)
  obtain ⟨ℓ, hcmp, hcard, hfull, hℓlt⟩ := exists_decreasing_blocks (fun j ↦ v j) hs
  set B₀ := Finset.univ.filter fun j ↦ ℓ j = 0 with hB₀
  set L₀ := ∑ j ∈ B₀, |v j| with hL₀
  set Sc := restrictedL1Norm Finset.univ v - L₀ with hSc
  have hSc0 : 0 ≤ Sc := by
    have : L₀ ≤ restrictedL1Norm Finset.univ v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ abs_nonneg _
    linarith
  have hmain := norm_le_ripNullspaceRho_mul_add_of_hasRestrictedIsometry hs A hδ hrip
    (blockVector ℓ v 0) (fun k ↦ blockVector ℓ v (k + 1)) p
    (sparsity_blockVector_le ℓ v 0 (hcard 0))
    (fun k ↦ sparsity_blockVector_le ℓ v (k + 1) (hcard (k + 1)))
    (fun k j ↦ blockVector_eq_zero_or_eq_zero ℓ v (by omega) j) (A v)
    (inner_apply_blockVector_zero_apply A ℓ hℓlt v) hSc0
    (sum_norm_blockVector_succ_le hs v hcmp hcard hfull hℓlt)
  -- comparison with an arbitrary set of at most `s` coordinates
  have h2 : ∑ j ∈ S, v j ^ 2 ≤ ∑ j ∈ B₀, v j ^ 2 :=
    sum_le_sum_filter_eq_zero_of_decreasing_blocks hcmp hfull S hS (fun j ↦ v j ^ 2)
      (fun j ↦ sq_nonneg _) fun i j h ↦ by
        rw [← sq_abs (v i), ← sq_abs (v j)]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h1 : restrictedL1Norm S v ≤ L₀ :=
    sum_le_sum_filter_eq_zero_of_decreasing_blocks hcmp hfull S hS (fun j ↦ |v j|)
      (fun j ↦ abs_nonneg _) fun _ _ h ↦ h
  have hSc_le : Sc ≤ restrictedL1Norm Sᶜ v := by
    have := restrictedL1Norm_add_compl S v
    rw [hSc]; linarith
  calc Real.sqrt (∑ j ∈ S, v j ^ 2) ≤ Real.sqrt (∑ j ∈ B₀, v j ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖blockVector ℓ v 0‖ := by rw [← norm_blockVector_sq, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := hmain
    _ ≤ _ := by gcongr

/-- GAPS 103.49: stable basis pursuit, with constants depending only on the RIP bound. For
`0 ≤ δ < 4 / √41` there are `C, D > 0` such that whenever `A` has the RIP of order `2 s` with
constant `δ`, `‖A β - y‖ ≤ η`, and `b` is a basis pursuit estimate with residual bound `η`,
`‖b - β‖₁ ≤ C σ_s(β)₁ + D √s η` and `‖b - β‖₂ ≤ C σ_s(β)₁ / √s + D η`. -/
theorem exists_basisPursuit_error_bound
    (δ : ℝ) (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) :
    ∃ C > 0, ∃ D > 0, ∀ (n p s : ℕ), 0 < s →
      ∀ A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n),
        HasRestrictedIsometry A (2 * s) δ → ∀ (β b : EuclideanSpace ℝ (Fin p))
        (y : EuclideanSpace ℝ (Fin n)) (η : ℝ), ‖A β - y‖ ≤ η →
        IsBasisPursuitEstimator A y η b →
        restrictedL1Norm Finset.univ (b - β) ≤ C * bestSparseL1Error s β + D * Real.sqrt s * η ∧
        ‖b - β‖ ≤ C / Real.sqrt s * bestSparseL1Error s β + D * η := by
  classical
  obtain ⟨_, hρ0, hρ1, hτ0, _⟩ := ripNullspace_constants hδ
  set ρ := ripNullspaceRho δ with hρ
  set τ := ripNullspaceTau δ with hτ
  have h1ρ : 0 < 1 - ρ := by linarith
  set C₁ := 2 * (1 + ρ) / (1 - ρ) with hC₁
  set D₁ := 4 * τ / (1 - ρ) with hD₁
  have hC₁0 : 0 < C₁ := by positivity
  have hD₁0 : 0 < D₁ := by positivity
  refine ⟨(1 + ρ) * C₁, by positivity, (1 + ρ) * D₁ + 2 * τ, by positivity, ?_⟩
  intro n p s hs A hrip β b y η hβ ⟨hb, hmin⟩
  have hη : 0 ≤ η := (norm_nonneg _).trans hβ
  set v := b - β with hv
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hAv : ‖A v‖ ≤ 2 * η := by
    have : A v = (A b - y) - (A β - y) := by rw [hv, map_sub]; abel
    rw [this]
    calc ‖(A b - y) - (A β - y)‖ ≤ ‖A b - y‖ + ‖A β - y‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith
  have hbβ := hmin β hβ
  have hnsp := hasRobustNullspaceProperty_of_hasRestrictedIsometry hs A hδ hrip
  -- the `ℓ¹` bound against an arbitrary `s`-sparse vector
  have hl1w : ∀ w : EuclideanSpace ℝ (Fin p), sparsity w ≤ s →
      restrictedL1Norm Finset.univ v ≤
        C₁ * restrictedL1Norm Finset.univ (β - w) + D₁ * Real.sqrt s * η := by
    intro w hw
    set S := Finset.univ.filter fun j ↦ w j ≠ 0 with hS
    have hScard : S.card ≤ s := hw
    have hvS : restrictedL1Norm S v ≤ ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * (2 * η) := by
      have h1 := hnsp v S hScard
      have hCS : restrictedL1Norm S v ≤ Real.sqrt s * Real.sqrt (∑ j ∈ S, v j ^ 2) := by
        have hsq : restrictedL1Norm S v ^ 2 ≤ S.card * ∑ j ∈ S, v j ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun j ↦ |v j|)
          simp only [sq_abs] at this
          exact this
        have hle : (S.card : ℝ) * ∑ j ∈ S, v j ^ 2 ≤ s * ∑ j ∈ S, v j ^ 2 := by
          gcongr
        rw [← Real.sqrt_mul hspos.le]
        refine Real.le_sqrt_of_sq_le (hsq.trans hle)
      have h2 : Real.sqrt s * Real.sqrt (∑ j ∈ S, v j ^ 2) ≤
          ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * ‖A v‖ := by
        have := mul_le_mul_of_nonneg_left h1 hsqrt.le
        have e : Real.sqrt s * (ρ / Real.sqrt s * restrictedL1Norm Sᶜ v + τ * ‖A v‖) =
            ρ * restrictedL1Norm Sᶜ v + τ * Real.sqrt s * ‖A v‖ := by field_simp
        linarith
      have h3 : τ * Real.sqrt s * ‖A v‖ ≤ τ * Real.sqrt s * (2 * η) :=
        mul_le_mul_of_nonneg_left hAv (by positivity)
      linarith
    have hβSc : restrictedL1Norm Sᶜ β ≤ restrictedL1Norm Finset.univ (β - w) := by
      calc restrictedL1Norm Sᶜ β = restrictedL1Norm Sᶜ (β - w) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            have : w j = 0 := by
              simpa [hS] using hj
            simp [this]
        _ ≤ restrictedL1Norm Finset.univ (β - w) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
    have t1 := restrictedL1Norm_le_add_sub S β b
    have t2 := restrictedL1Norm_le_add_sub Sᶜ v b
    have e2 : b - v = β := by rw [hv]; abel
    rw [e2] at t2
    have s1 := restrictedL1Norm_add_compl S β
    have s2 := restrictedL1Norm_add_compl S b
    have s3 := restrictedL1Norm_add_compl S v
    have hvSc : (1 - ρ) * restrictedL1Norm Sᶜ v ≤
        2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η) := by
      linarith
    have hvSc' : restrictedL1Norm Sᶜ v ≤
        (2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η)) / (1 - ρ) := by
      rw [le_div_iff₀ h1ρ]; linarith
    have hfin :
        restrictedL1Norm Finset.univ v ≤ C₁ * restrictedL1Norm Sᶜ β + D₁ * Real.sqrt s * η := by
      have e : C₁ * restrictedL1Norm Sᶜ β + D₁ * Real.sqrt s * η =
          (1 + ρ) * ((2 * restrictedL1Norm Sᶜ β + τ * Real.sqrt s * (2 * η)) / (1 - ρ)) +
            τ * Real.sqrt s * (2 * η) := by
        rw [hC₁, hD₁]; field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hvSc' (by linarith : (0:ℝ) ≤ 1 + ρ)
      linarith
    exact hfin.trans (by gcongr)
  have : Nonempty {w : EuclideanSpace ℝ (Fin p) // sparsity w ≤ s} :=
    ⟨⟨0, by simp [sparsity]⟩⟩
  have hσ0 : 0 ≤ bestSparseL1Error s β :=
    le_ciInf fun w ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hl1 :
      restrictedL1Norm Finset.univ v ≤ C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η := by
    have : (restrictedL1Norm Finset.univ v - D₁ * Real.sqrt s * η) / C₁ ≤
        bestSparseL1Error s β := by
      refine le_ciInf fun w ↦ ?_
      rw [div_le_iff₀ hC₁0]
      have := hl1w w.val w.property
      linarith
    rw [div_le_iff₀ hC₁0] at this
    linarith
  refine ⟨?_, ?_⟩
  · calc restrictedL1Norm Finset.univ v ≤ C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η := hl1
      _ ≤ (1 + ρ) * C₁ * bestSparseL1Error s β + ((1 + ρ) * D₁ + 2 * τ) * Real.sqrt s * η := by
          gcongr
          · nlinarith
          · nlinarith
  · -- the `ℓ²` bound
    obtain ⟨ℓ, hcmp, hcard, hfull, -⟩ := exists_decreasing_blocks (fun j ↦ v j) hs
    set S0 := Finset.univ.filter fun j ↦ ℓ j = 0 with hS0
    have hmem : ∀ j, j ∈ S0 ↔ ℓ j = 0 := fun j ↦ by simp [hS0]
    have hL1nn : 0 ≤ restrictedL1Norm Finset.univ v := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    have hpt : ∀ j ∉ S0, |v j| ≤ restrictedL1Norm Finset.univ v / s := by
      intro j hj
      have hj0 : 0 < ℓ j := by rw [hmem] at hj; omega
      have hc : S0.card = s := hfull 0 ⟨j, hj0⟩
      rw [le_div_iff₀ hspos]
      calc |v j| * s = ∑ _i ∈ S0, |v j| := by rw [Finset.sum_const, hc, nsmul_eq_mul]; ring
        _ ≤ ∑ i ∈ S0, |v i| := Finset.sum_le_sum fun i hi ↦ by
            rw [hmem] at hi; exact hcmp j i (by omega)
        _ ≤ restrictedL1Norm Finset.univ v :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
    have htail : Real.sqrt (∑ j ∈ S0ᶜ, v j ^ 2) ≤ restrictedL1Norm Finset.univ v / Real.sqrt s := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, Real.sq_sqrt hspos.le]
      calc ∑ j ∈ S0ᶜ, v j ^ 2 ≤ ∑ j ∈ S0ᶜ, (restrictedL1Norm Finset.univ v / s) * |v j| :=
            Finset.sum_le_sum fun j hj ↦ by
              rw [← sq_abs, sq]
              exact mul_le_mul_of_nonneg_right (hpt j (Finset.mem_compl.mp hj)) (abs_nonneg _)
        _ = restrictedL1Norm Finset.univ v / s * restrictedL1Norm S0ᶜ v := by
            rw [← Finset.mul_sum]; rfl
        _ ≤ restrictedL1Norm Finset.univ v / s * restrictedL1Norm Finset.univ v := by
            gcongr
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun j _ _ ↦ abs_nonneg _
        _ = _ := by ring
    have hhead : Real.sqrt (∑ j ∈ S0, v j ^ 2) ≤ ρ / Real.sqrt s * restrictedL1Norm Finset.univ v +
        τ * (2 * η) := by
      have h1 := hnsp v S0 (hcard 0)
      have h2 : restrictedL1Norm S0ᶜ v ≤ restrictedL1Norm Finset.univ v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ abs_nonneg _
      have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hρ0 hsqrt.le)
      have h4 := mul_le_mul_of_nonneg_left hAv hτ0.le
      linarith
    have hnorm : ‖v‖ = Real.sqrt (∑ j ∈ S0, v j ^ 2 + ∑ j ∈ S0ᶜ, v j ^ 2) := by
      rw [Finset.sum_add_sum_compl, ← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    have hl2 : ‖v‖ ≤ (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η := by
      rw [hnorm]
      -- subadditivity of the square root, from Mathlib's `Real.rpow_add_le_add_rpow`
      have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
        fun a b ha hb ↦ by
          simpa only [Real.sqrt_eq_rpow] using Real.rpow_add_le_add_rpow ha hb
            (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      refine (hsub _ _ (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
        (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).trans ?_
      have e : (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η =
          (ρ / Real.sqrt s * restrictedL1Norm Finset.univ v + τ * (2 * η)) +
            restrictedL1Norm Finset.univ v / Real.sqrt s := by ring
      rw [e]
      exact add_le_add hhead htail
    calc ‖v‖ ≤ (1 + ρ) / Real.sqrt s * restrictedL1Norm Finset.univ v + 2 * τ * η := hl2
      _ ≤ (1 + ρ) / Real.sqrt s * (C₁ * bestSparseL1Error s β + D₁ * Real.sqrt s * η) +
            2 * τ * η := by
          gcongr
      _ = (1 + ρ) * C₁ / Real.sqrt s * bestSparseL1Error s β +
            ((1 + ρ) * D₁ + 2 * τ) * η := by
          field_simp
          ring

end CKSD
