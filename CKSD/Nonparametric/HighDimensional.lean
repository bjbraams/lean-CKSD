module

public import CKSD.Nonparametric.LowerBounds

/-!
# Nonparametric: HighDimensional

Sources: `GAPS.md`, `SYNOPSIS103.md`, and `STRUCTURE103.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common rank measurable structure.
attribute [local instance] rankMeasurableSpace

/-- GAPS 103.29, the separable-Hilbert-space CLT, characterized by scalar variances. -/
theorem tendstoInDistribution_hilbert_sampleAverage {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure H) [IsProbabilityMeasure P]
    (X : ℕ → Ω → H) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P) :
    let m := ∫ x, x ∂P;
    ∃ G : Measure H, IsProbabilityMeasure G ∧
      (∀ u : H, G.map (fun x ↦ inner ℝ u x) =
        gaussianReal 0 (Real.toNNReal (∫ x, (inner ℝ u (x - m)) ^ 2 ∂P))) ∧
      TendstoInDistribution μ (fun n ω ↦ Real.sqrt n • (sampleAverage X n ω - m)) G := by
  sorry

/-- Pythagoras for the projection onto the span of an orthonormal family. -/
theorem norm_sub_sum_inner_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (q : Fin k → E) (hq : Orthonormal ℝ q) (y : E) :
    ‖y - ∑ j, inner ℝ y (q j) • q j‖ ^ 2 = ‖y‖ ^ 2 - ∑ j, inner ℝ y (q j) ^ 2 := by
  have h1 : inner ℝ y (∑ j, inner ℝ y (q j) • q j) = ∑ j, inner ℝ y (q j) ^ 2 := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [real_inner_smul_right, sq]
  have h2 : ‖∑ j, inner ℝ y (q j) • q j‖ ^ 2 = ∑ j, inner ℝ y (q j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_left, hq.inner_right_fintype, sq]
  rw [norm_sub_sq_real, h1, h2]
  ring

/-- GAPS 103.31, finite-dimensional PCA minimizes expected reconstruction error: no projection
onto the span of `k` orthonormal vectors has risk below the tail eigenvalue sum. Attainment by
the leading eigenvectors, uniqueness, and the Hilbert-space case are not asserted. -/
theorem pca_reconstruction_risk_bound {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ (Fin d))
    (hX : MemLp X 2 μ) (m : EuclideanSpace ℝ (Fin d))
    (hm : (∫ ω, X ω ∂μ) = m) (e : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (lambda : Fin d → ℝ) (hlambda : Antitone lambda)
    (hcov : ∀ i j, (∫ ω, inner ℝ (X ω - m) (e i) * inner ℝ (X ω - m) (e j) ∂μ) =
      if i = j then lambda i else 0) (hk : k ≤ d)
    (q : Fin k → EuclideanSpace ℝ (Fin d)) (hq : Orthonormal ℝ q) :
    (∑ j : Fin d, if k ≤ j.val then lambda j else 0) ≤
      ∫ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 ∂μ := by
  set y := fun (j : Fin d) (ω : Ω) ↦ inner ℝ (X ω - m) (e j) with hy
  set w := fun (i : Fin k) (j : Fin d) ↦ inner ℝ (e j) (q i) with hw
  have hY : MemLp (fun ω ↦ X ω - m) 2 μ := hX.sub (memLp_const m)
  have hyL2 : ∀ j, MemLp (y j) 2 μ := fun j ↦ MemLp.inner_const (𝕜 := ℝ) hY (e j)
  have hint : ∀ j l, Integrable (fun ω ↦ y j ω * y l ω) μ := fun j l ↦
    (hyL2 j).integrable_mul (hyL2 l)
  -- pointwise expansion in the eigenbasis
  have hpt : ∀ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 =
      ∑ j, y j ω * y j ω - ∑ i, ∑ j, ∑ l, w i j * w i l * (y j ω * y l ω) := by
    intro ω
    rw [norm_sub_sum_inner_smul_sq q hq, ← e.sum_sq_inner_left]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [sq]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← e.sum_inner_mul_inner, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [hy, hw]; ring
  have hInt : ∫ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 ∂μ =
      ∑ j, lambda j - ∑ j, lambda j * ∑ i, w i j ^ 2 := by
    simp_rw [hpt]
    rw [integral_sub (integrable_finsetSum _ fun j _ ↦ hint j j)
      (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        integrable_finsetSum _ fun l _ ↦ (hint j l).const_mul _),
      integral_finsetSum _ fun j _ ↦ hint j j,
      integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        integrable_finsetSum _ fun l _ ↦ (hint j l).const_mul _]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [hcov j j]; simp
    · have hi : ∀ i, ∫ a, ∑ j, ∑ l, w i j * w i l * (y j a * y l a) ∂μ =
          ∑ j, lambda j * w i j ^ 2 := by
        intro i
        rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun l _ ↦
          (hint j l).const_mul _]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [integral_finsetSum _ fun l _ ↦ (hint j l).const_mul _]
        simp_rw [integral_const_mul]
        simp only [hy, hcov, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
      simp_rw [hi]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
  rcases hk.lt_or_eq with hlt | heq
  swap
  · have hzero : (∑ j : Fin d, if k ≤ j.val then lambda j else 0) = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by simp only [show ¬ k ≤ j.val by omega, ↓reduceIte]
    rw [hzero]
    exact integral_nonneg fun ω ↦ by positivity
  rw [hInt]
  have hc1 : ∀ j, ∑ i, w i j ^ 2 ≤ 1 := by
    intro j
    have := hq.sum_inner_products_le (x := e j) (s := Finset.univ)
    simpa [hw, real_inner_comm, e.orthonormal.1 j] using this
  have hc0 : ∀ j, 0 ≤ ∑ i, w i j ^ 2 := fun j ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hcsum : ∑ j, ∑ i, w i j ^ 2 = k := by
    rw [Finset.sum_comm]
    have : ∀ i, ∑ j, w i j ^ 2 = 1 := by
      intro i
      simp only [hw]
      rw [e.sum_sq_inner_right (q i), hq.1 i]
      norm_num
    simp [this]
  set t := lambda ⟨k, hlt⟩ with ht
  have hterm : ∀ j : Fin d,
      0 ≤ (lambda j - t) * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) := by
    intro j
    by_cases hj : j.val < k
    · simp only [hj, ↓reduceIte]
      apply mul_nonneg
      · exact sub_nonneg.mpr (hlambda (Fin.le_def.mpr (by simpa using hj.le)))
      · linarith [hc1 j]
    · simp only [hj, ↓reduceIte]
      apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (hlambda (by simp [Fin.le_def]; omega))
      · linarith [hc0 j]
  have hsumind : ∑ j : Fin d, (if j.val < k then (1 : ℝ) else 0) = k := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_filter_val_lt,
      min_eq_right hk]
  have hexp : ∀ j : Fin d, (lambda j - t) * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) =
      ((if j.val < k then lambda j else 0) - lambda j * ∑ i, w i j ^ 2) -
        t * ((if j.val < k then 1 else 0) - ∑ i, w i j ^ 2) := by
    intro j; split_ifs <;> ring
  have htot := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hterm j
  rw [Finset.sum_congr rfl fun j _ ↦ hexp j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hsumind, hcsum, sub_self, mul_zero,
    sub_zero] at htot
  have hsplit : ∑ j, lambda j = ∑ j : Fin d, (if j.val < k then lambda j else 0) +
      ∑ j : Fin d, (if k ≤ j.val then lambda j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j.val < k
    · simp only [hj, show ¬ k ≤ j.val by omega, ↓reduceIte, add_zero]
    · simp only [hj, show k ≤ j.val by omega, ↓reduceIte, zero_add]
  linarith

/-- The coordinatewise L1 norm is convex along segments. -/
theorem restrictedL1Norm_convex_comb {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    restrictedL1Norm S (x - h • (x - y)) ≤
      (1 - h) * restrictedL1Norm S x + h * restrictedL1Norm S y := by
  unfold restrictedL1Norm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have : (x - h • (x - y)) j = (1 - h) * x j + h * y j := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this]
  calc |(1 - h) * x j + h * y j| ≤ |(1 - h) * x j| + |h * y j| := abs_add_le _ _
    _ = (1 - h) * |x j| + h * |y j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]

/-- GAPS 103.34, deterministic lasso prediction/L1 bounds and the cone condition. -/
theorem lasso_cone_and_error_bounds {n p : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (β b : EuclideanSpace ℝ (Fin p)) (ε : EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) (hne : S.Nonempty) (lambda κ : ℝ) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * restrictedL1Norm Finset.univ δ)
    (hcompat : ∀ δ, restrictedL1Norm Sᶜ δ ≤ 3 * restrictedL1Norm S δ →
      κ ^ 2 * (restrictedL1Norm S δ) ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n)
    (hmin : ∀ t, ‖A β + ε - A b‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b ≤
      ‖A β + ε - A t‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ t) :
    restrictedL1Norm Sᶜ (b - β) ≤ 3 * restrictedL1Norm S (b - β) ∧
      ‖A (b - β)‖ ^ 2 / n ≤ 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) ∧
      restrictedL1Norm Finset.univ (b - β) ≤ 6 * lambda * S.card / κ ^ 2 := by
  set δ := b - β with hδ
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set u' := ‖A δ‖ ^ 2 with hu'
  set e := inner ℝ ε (A δ) with he
  -- first-order condition of the lasso along the segment towards `β`
  have hvar : ∀ h : ℝ, 0 < h → h ≤ 1 →
      u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
        restrictedL1Norm Finset.univ b) + h * u' / (2 * n) := by
    intro h h0 h1
    have hm := hmin (b - h • δ)
    have hr : A β + ε - A b = ε - A δ := by rw [hδ, map_sub]; abel
    have hr' : A β + ε - A (b - h • δ) = (ε - A δ) + h • A δ := by
      rw [map_sub, map_smul, hδ, map_sub]; abel
    rw [hr, hr', norm_add_sq_real, norm_smul, inner_smul_right, inner_sub_left,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos h0] at hm
    have hl1 := restrictedL1Norm_convex_comb Finset.univ b β h h0.le h1
    rw [← hδ] at hl1
    have key : 0 ≤ h * ((e - u') / n + h * u' / (2 * n) +
        lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) := by
      have : h * ((e - u') / n + h * u' / (2 * n) +
          lambda * (restrictedL1Norm Finset.univ β - restrictedL1Norm Finset.univ b)) =
          ((‖ε - A δ‖ ^ 2 + 2 * (h * (e - u')) + (h * ‖A δ‖) ^ 2) / (2 * n) +
            lambda * ((1 - h) * restrictedL1Norm Finset.univ b +
              h * restrictedL1Norm Finset.univ β)) -
          (‖ε - A δ‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ b) := by
        rw [hu']; field_simp; ring
      rw [this, sub_nonneg]
      refine hm.trans ?_
      gcongr
    have := (mul_nonneg_iff_of_pos_left h0).mp key
    have h2 : (e - u') / n = e / n - u' / n := by ring
    linarith
  have hvar' : u' / n ≤ e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b) := by
    by_contra hcon
    rw [not_le] at hcon
    set gapv := u' / n - (e / n + lambda * (restrictedL1Norm Finset.univ β -
      restrictedL1Norm Finset.univ b)) with hgap
    have hgpos : 0 < gapv := by linarith
    have hc : 0 ≤ u' / (2 * n) := by positivity
    set h := min 1 (gapv / (2 * (u' / (2 * n) + 1))) with hh
    have hpos : 0 < h := lt_min one_pos (by positivity)
    have hle : h ≤ 1 := min_le_left _ _
    have hle2 : h ≤ gapv / (2 * (u' / (2 * n) + 1)) := min_le_right _ _
    have := hvar h hpos hle
    have hmul : h * (u' / (2 * n)) ≤ gapv / 2 := by
      calc h * (u' / (2 * n)) ≤ gapv / (2 * (u' / (2 * n) + 1)) * (u' / (2 * n) + 1) := by
            apply mul_le_mul hle2 (by linarith) hc (by positivity)
        _ = gapv / 2 := by
            have hgen : ∀ g q : ℝ, q ≠ 0 → g / (2 * q) * q = g / 2 := by
              intro g q hq; field_simp
            exact hgen _ _ (by positivity)
    have : h * u' / (2 * n) = h * (u' / (2 * n)) := by ring
    linarith
  -- split the `L1` norms over `S` and its complement
  have hβc : restrictedL1Norm Sᶜ β = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsupp j (Finset.mem_compl.mp hj), abs_zero]
  have hcomp : restrictedL1Norm Sᶜ δ = restrictedL1Norm Sᶜ b := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hδ, PiLp.sub_apply, hsupp j (Finset.mem_compl.mp hj), sub_zero]
  have htri := restrictedL1Norm_le_add_sub S β b
  have hsβ := restrictedL1Norm_add_compl S β
  have hsb := restrictedL1Norm_add_compl S b
  have hsδ := restrictedL1Norm_add_compl S δ
  have hnz := hnoise δ
  have habs := neg_abs_le e
  have habs' := le_abs_self e
  set a := restrictedL1Norm S δ
  set c := restrictedL1Norm Sᶜ δ
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have he' : e / n ≤ |e| / n := div_le_div_of_nonneg_right habs' hN.le
  have hu0 : 0 ≤ u' / n := by positivity
  -- the main inequality `u ≤ (3λ/2) a - (λ/2) c`
  have hmain : u' / n ≤ 3 * lambda / 2 * a - lambda / 2 * c := by
    rw [← hsδ] at hnz
    nlinarith
  have hcone : c ≤ 3 * a := by nlinarith
  have hcomp' := hcompat δ hcone
  have hs : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hcomp'' : κ ^ 2 * a ^ 2 ≤ S.card * (u' / n) := by
    rw [hu'] at *; calc κ ^ 2 * a ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n := hcomp'
      _ = _ := by ring
  have hka : κ ^ 2 * a ≤ 3 * lambda * S.card / 2 := by
    rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · have : κ ^ 2 * a ^ 2 ≤ S.card * (3 * lambda / 2 * a) := by
        calc κ ^ 2 * a ^ 2 ≤ S.card * (u' / n) := hcomp''
          _ ≤ S.card * (3 * lambda / 2 * a) := by
            apply mul_le_mul_of_nonneg_left _ hs.le; nlinarith
      nlinarith
  have hκ2 : 0 < κ ^ 2 := by positivity
  have ha_le : a ≤ 3 * lambda * S.card / (2 * κ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨hcone, ?_, ?_⟩
  · calc u' / n ≤ 3 * lambda / 2 * a := by nlinarith
      _ ≤ 3 * lambda / 2 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
      _ = 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) := by field_simp; ring
  · rw [← hsδ]
    calc a + c ≤ 4 * a := by linarith
      _ ≤ 4 * (3 * lambda * S.card / (2 * κ ^ 2)) := by gcongr
      _ = 6 * lambda * S.card / κ ^ 2 := by field_simp; ring

/-- GAPS 103.37, FDR control for mutually independent p-values. -/
theorem benjamini_hochberg_false_discovery_rate_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hrange : ∀ i ω, p i ω ∈ Icc 0 1) (hind : iIndepFun p μ)
    (H₀ : Finset (Fin m)) (hvalid : ∀ i ∈ H₀, ∀ t ∈ Icc (0 : ℝ) 1,
      μ.real {ω | p i ω ≤ t} ≤ t) (α : ℝ) (hα : α ∈ Ioo 0 1) :
    (∫ ω, ((H₀.filter fun i ↦ p i ω ≤
      (benjaminiHochbergCount (fun j ↦ p j ω) α : ℝ) * α / m).card : ℝ) /
        max (benjaminiHochbergCount (fun j ↦ p j ω) α : ℝ) 1 ∂μ) ≤ α * H₀.card / m := by
  sorry


end CKSD
