module

public import CKSD.Nonparametric.Models
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Shape constraints and penalized projection models

The isotonic risk bounds are in the Gaussian-noise scope, with the empirical squared norm
normalization `1/n`. The model-selection statement permits a countable collection of linear
models, specifies the measurable selected index, and uses actual orthogonal projections.
Sources: GAPS 103.27 and 103.35.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Cone of nondecreasing finite real vectors. -/
def isotonicCone (n : ℕ) : Set (Fin n → ℝ) := {θ | Monotone θ}

/-- Variation of a finite real vector, including the empty-vector value zero. -/
def finiteVectorVariation {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  sSup (range θ) - sInf (range θ)

/-- Gaussian isotonic regression risk, divided by sample size. -/
def isotonicGaussianRisk {n : ℕ} (θ : Fin n → ℝ)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((∑ i, (T y i - θ i) ^ 2) / n)
    ∂(Measure.pi fun i : Fin n ↦ gaussianReal (θ i) 1)

/-- The bounded monotone class used in the isotonic minimax lower bound. -/
def isotonicUnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {θ | Monotone θ ∧ ∀ i, |θ i| ≤ 1}

/-- Gaussian isotonic minimax risk on the bounded monotone class. -/
def isotonicGaussianMinimaxRisk (n : ℕ) : ℝ≥0∞ :=
  ⨅ T : {T : (Fin n → ℝ) → (Fin n → ℝ) // Measurable T},
    ⨆ θ : isotonicUnitBall n, isotonicGaussianRisk θ.val T.val

/-- Mean response over a contiguous block of indices. -/
def blockAverage {n : ℕ} (y : Fin n → ℝ) (a b : Fin n) : ℝ :=
  (∑ j ∈ Finset.Icc a b, y j) / (b.val - a.val + 1 : ℕ)

/-- Isotonic least squares in its explicit max–min block-average form. -/
def isotonicLeastSquares {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  ⨆ a : {a : Fin n // a ≤ i}, ⨅ b : {b : Fin n // i ≤ b}, blockAverage y a.val b.val

/-- GAPS 103.27: existence and uniqueness of the isotonic least-squares fit. -/
theorem existsUnique_isIsotonicRegressionEstimator {n : ℕ} (y : Fin n → ℝ) :
    ∃! θ : Fin n → ℝ, IsIsotonicRegressionEstimator y θ := by
  let K : Set (EuclideanSpace ℝ (Fin n)) := {x | Monotone (fun i ↦ x i)}
  have hclosed : IsClosed K :=
    isClosed_monotone.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ))
  have hconv : Convex ℝ K := by
    intro x hx z hz a b ha hb _ i j hij
    change a * x i + b * z i ≤ a * x j + b * z j
    have hx' := hx hij
    have hz' := hz hij
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hz')]
  have hne : K.Nonempty := ⟨0, fun _ _ _ ↦ le_rfl⟩
  letI : Nonempty K := hne.to_subtype
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hsq (a : EuclideanSpace ℝ (Fin n)) :
      ‖u - a‖ ^ 2 = ∑ i, (y i - a i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [u, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  obtain ⟨v, hv, hvnorm⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv u
  have hbelow (a : K) : (⨅ w : K, ‖u - w‖) ≤ ‖u - a‖ :=
    ciInf_le ⟨0, fun _ ⟨_, heq⟩ ↦ heq ▸ norm_nonneg _⟩ a
  refine ⟨fun i ↦ v i, ⟨hv, ?_⟩, ?_⟩
  · intro θ hθ
    have hnorm : ‖u - v‖ ≤ ‖u - WithLp.toLp 2 θ‖ :=
      hvnorm.trans_le (hbelow ⟨WithLp.toLp 2 θ, hθ⟩)
    have hnormsq := mul_self_le_mul_self (norm_nonneg (u - v)) hnorm
    rw [← sq, ← sq] at hnormsq
    rw [hsq v, hsq (WithLp.toLp 2 θ)] at hnormsq
    exact hnormsq
  · intro z hz
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
    have hw : w ∈ K := hz.1
    have hwmin (a : K) : ‖u - w‖ ≤ ‖u - a‖ := by
      apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      rw [← sq, ← sq]
      rw [hsq w, hsq a]
      exact hz.2 (fun i ↦ a.val i) a.property
    have hwnorm : ‖u - w‖ = ⨅ a : K, ‖u - a‖ :=
      le_antisymm (le_ciInf hwmin) (hbelow ⟨w, hw⟩)
    have hvw := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hvnorm w hw
    have hwv := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).mp hwnorm v hv
    have hid : inner ℝ (u - v) (w - v) + inner ℝ (u - w) (v - w) = ‖w - v‖ ^ 2 := by
      rw [show u - v = (u - w) + (w - v) by abel,
        show v - w = -(w - v) by abel, inner_add_left, inner_neg_right,
        real_inner_self_eq_norm_sq]
      ring
    have hnormzero : ‖w - v‖ = 0 := by nlinarith [sq_nonneg ‖w - v‖]
    have heq : w = v := sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    funext i
    exact congrArg (fun a : EuclideanSpace ℝ (Fin n) ↦ a i) heq

/-- Variational inequality for isotonic least squares: the residual of the fit has
nonpositive inner product with every monotone direction `φ - θ`. -/
theorem IsIsotonicRegressionEstimator.sum_mul_sub_nonpos {n : ℕ} {y θ : Fin n → ℝ}
    (hθ : IsIsotonicRegressionEstimator y θ) (φ : Fin n → ℝ) (hφ : Monotone φ) :
    ∑ i, (y i - θ i) * (φ i - θ i) ≤ 0 := by
  set c := ∑ i, (y i - θ i) * (φ i - θ i) with hc
  set W := ∑ i, (φ i - θ i) ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  by_contra hpos
  push Not at hpos
  set t := c / (c + W) with ht
  have ht0 : 0 < t := div_pos hpos (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hmono : Monotone fun i ↦ θ i + t * (φ i - θ i) := by
    intro i j hij
    have h1 := hθ.1 hij
    have h2 := hφ hij
    nlinarith
  have hmin := hθ.2 _ hmono
  have hexp : ∑ i, (y i - (θ i + t * (φ i - θ i))) ^ 2 =
      ∑ i, (y i - θ i) ^ 2 - 2 * t * c + t ^ 2 * W := by
    rw [hc, hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hexp] at hmin
  -- `2 c ≤ t W < c`
  have h1 : 2 * c ≤ t * W := by nlinarith
  have h2 : t * W < c := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Suffix sums of the isotonic residual are nonpositive, vanish at `0`, and vanish at
every jump of the fit. -/
theorem IsIsotonicRegressionEstimator.suffix_sum_props {n : ℕ} {y θ : Fin n → ℝ}
    (hθ : IsIsotonicRegressionEstimator y θ) :
    (∀ k : ℕ, ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) ≤ 0) ∧
    0 ≤ ∑ j : Fin n, (y j - θ j) ∧
    ∀ (k : ℕ) (hk : 0 < k) (hkn : k < n), θ ⟨k - 1, by omega⟩ < θ ⟨k, hkn⟩ →
      0 ≤ ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) := by
  refine ⟨fun k ↦ ?_, ?_, fun k hk hkn hjump ↦ ?_⟩
  · have := hθ.sum_mul_sub_nonpos (fun j ↦ θ j + if k ≤ (j : ℕ) then 1 else 0) (by
      intro i j hij
      have h1 := hθ.1 hij
      have h2 : (i : ℕ) ≤ j := hij
      simp only
      split_ifs with ha hb hb <;> linarith)
    convert this using 2 with j
    split_ifs <;> ring
  · have := hθ.sum_mul_sub_nonpos (fun j ↦ θ j - 1) (fun i j hij ↦ by
      have := hθ.1 hij; simp only; linarith)
    have e : ∑ i, (y i - θ i) * (θ i - 1 - θ i) = -∑ j, (y j - θ j) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ ↦ ?_; ring
    linarith
  · set g := θ ⟨k, hkn⟩ - θ ⟨k - 1, by omega⟩ with hg
    have hg0 : 0 < g := by linarith
    have := hθ.sum_mul_sub_nonpos (fun j ↦ θ j - if k ≤ (j : ℕ) then g else 0) (by
      intro i j hij
      have h1 := hθ.1 hij
      have h2 : (i : ℕ) ≤ j := hij
      simp only
      split_ifs with ha hb hb
      · linarith
      · omega
      · have hi : θ i ≤ θ ⟨k - 1, by omega⟩ := hθ.1 (show (i : ℕ) ≤ k - 1 by omega)
        have hj : θ ⟨k, hkn⟩ ≤ θ j := hθ.1 (show k ≤ (j : ℕ) by omega)
        linarith
      · linarith)
    have e : ∑ i, (y i - θ i) * (θ i - (if k ≤ (i : ℕ) then g else 0) - θ i) =
        -g * ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_; split_ifs <;> ring
    rw [e] at this
    nlinarith

/-- GAPS 103.27: the max–min block-average formula is the isotonic least-squares fit. -/
theorem isIsotonicRegressionEstimator_isotonicLeastSquares {n : ℕ} (y : Fin n → ℝ) :
    IsIsotonicRegressionEstimator y (isotonicLeastSquares y) := by
  classical
  obtain ⟨θ, hθ, -⟩ := existsUnique_isIsotonicRegressionEstimator y
  suffices h : isotonicLeastSquares y = θ by rw [h]; exact hθ
  obtain ⟨hneg, htot, hjump⟩ := hθ.suffix_sum_props
  set Sfx : ℕ → ℝ := fun k ↦ ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) with hSfx
  have hS0 : Sfx 0 = 0 := le_antisymm (hneg 0) (by simpa [Sfx] using htot)
  have hSn : ∀ k, n ≤ k → Sfx k = 0 := fun k hk ↦
    Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by have := j.isLt; omega)
  -- interval sums of the residual
  have hIcc : ∀ a b : Fin n, a ≤ b → ∑ j ∈ Finset.Icc a b, (y j - θ j) =
      Sfx a - Sfx (b + 1) := by
    intro a b hab
    have hset : Finset.Icc a b = Finset.univ.filter fun j : Fin n ↦ a ≤ j ∧ j ≤ b := by
      ext j; simp
    rw [hset, Finset.sum_filter, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hab' : (a : ℕ) ≤ b := hab
    by_cases h1 : (a : ℕ) ≤ j <;> by_cases h2 : (j : ℕ) ≤ b
    · have : a ≤ j ∧ j ≤ b := ⟨h1, h2⟩
      simp [this, h1, show ¬ ((b : ℕ) + 1 ≤ j) by omega]
    · have : ¬ (a ≤ j ∧ j ≤ b) := fun h ↦ h2 h.2
      simp [this, h1, show (b : ℕ) + 1 ≤ j by omega]
    · have : ¬ (a ≤ j ∧ j ≤ b) := fun h ↦ h1 h.1
      simp [this, h1, show ¬ ((b : ℕ) + 1 ≤ j) by omega]
    · have : ¬ (a ≤ j ∧ j ≤ b) := fun h ↦ h1 h.1
      simp [this, h1, show ¬ ((b : ℕ) + 1 ≤ j) by omega]
  have hcardIcc : ∀ a b : Fin n, a ≤ b →
      ((Finset.Icc a b).card : ℝ) = ((b.val - a.val + 1 : ℕ) : ℝ) := by
    intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    rw [Fin.card_Icc]
    congr 1
    omega
  have hcardpos : ∀ a b : Fin n, a ≤ b → (0 : ℝ) < ((b.val - a.val + 1 : ℕ) : ℝ) := by
    intro a b _; positivity
  funext i
  set E := Finset.univ.filter fun j ↦ θ j = θ i with hE
  have hiE : i ∈ E := by simp [E]
  set a₀ := E.min' ⟨i, hiE⟩ with ha₀
  set b₀ := E.max' ⟨i, hiE⟩ with hb₀
  have ha₀E : θ a₀ = θ i := by
    have := E.min'_mem ⟨i, hiE⟩; simp only [E, Finset.mem_filter] at this; exact this.2
  have hb₀E : θ b₀ = θ i := by
    have := E.max'_mem ⟨i, hiE⟩; simp only [E, Finset.mem_filter] at this; exact this.2
  have ha₀i : a₀ ≤ i := E.min'_le i hiE
  have hib₀ : i ≤ b₀ := E.le_max' i hiE
  have hSa : Sfx a₀ = 0 := by
    rcases Nat.eq_zero_or_pos (a₀ : ℕ) with h | h
    · rw [h]; exact hS0
    refine le_antisymm (hneg _) (hjump _ h a₀.isLt ?_)
    set q : Fin n := ⟨(a₀ : ℕ) - 1, by omega⟩
    have hq : q < a₀ := by change (a₀ : ℕ) - 1 < a₀; omega
    have hqE : q ∉ E := fun hq' ↦ absurd (E.min'_le q hq') (not_le.mpr hq)
    have hne : θ q ≠ θ i := by simpa [E] using hqE
    have hle : θ q ≤ θ a₀ := hθ.1 hq.le
    rw [ha₀E] at hle ⊢
    exact lt_of_le_of_ne hle hne
  have hSb : Sfx ((b₀ : ℕ) + 1) = 0 := by
    by_cases h : (b₀ : ℕ) + 1 < n
    · refine le_antisymm (hneg _) (hjump _ (by omega) h ?_)
      set q : Fin n := ⟨(b₀ : ℕ) + 1, h⟩
      have hq : b₀ < q := by change (b₀ : ℕ) < b₀ + 1; omega
      have hqE : q ∉ E := fun hq' ↦ absurd (E.le_max' q hq') (not_le.mpr hq)
      have hne : θ q ≠ θ i := by simpa [E] using hqE
      have hle : θ b₀ ≤ θ q := hθ.1 hq.le
      have e : (⟨(b₀ : ℕ) + 1 - 1, by omega⟩ : Fin n) = b₀ := Fin.ext (by simp)
      rw [e, hb₀E]
      rw [hb₀E] at hle
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · exact hSn _ (by omega)
  -- lower bound for blocks starting at `a₀`
  have hlow : ∀ b : Fin n, i ≤ b → θ i ≤ blockAverage y a₀ b := by
    intro b hb
    have hab : a₀ ≤ b := ha₀i.trans hb
    unfold blockAverage
    rw [le_div_iff₀ (hcardpos a₀ b hab), ← hcardIcc a₀ b hab]
    have h1 := hIcc a₀ b hab
    rw [hSa, Finset.sum_sub_distrib] at h1
    have h2 := Finset.card_nsmul_le_sum (Finset.Icc a₀ b) θ (θ i) (fun j hj ↦ by
      rw [← ha₀E]; exact hθ.1 (Finset.mem_Icc.mp hj).1)
    rw [nsmul_eq_mul] at h2
    have h3 := hneg ((b : ℕ) + 1)
    linarith
  -- upper bound for blocks ending at `b₀`
  have hup : ∀ a : Fin n, a ≤ i → blockAverage y a b₀ ≤ θ i := by
    intro a ha
    have hab : a ≤ b₀ := ha.trans hib₀
    unfold blockAverage
    rw [div_le_iff₀ (hcardpos a b₀ hab), ← hcardIcc a b₀ hab]
    have h1 := hIcc a b₀ hab
    rw [hSb, Finset.sum_sub_distrib] at h1
    have h2 := Finset.sum_le_card_nsmul (Finset.Icc a b₀) θ (θ i) (fun j hj ↦ by
      rw [← hb₀E]; exact hθ.1 (Finset.mem_Icc.mp hj).2)
    rw [nsmul_eq_mul] at h2
    have h3 := hneg a
    linarith
  have : Nonempty {a : Fin n // a ≤ i} := ⟨⟨i, le_rfl⟩⟩
  have : Nonempty {b : Fin n // i ≤ b} := ⟨⟨i, le_rfl⟩⟩
  have hbdd : ∀ a : Fin n, BddBelow (range fun b : {b : Fin n // i ≤ b} ↦ blockAverage y a b.val) :=
    fun a ↦ (finite_range _).bddBelow
  have hinner : ∀ a : {a : Fin n // a ≤ i},
      (⨅ b : {b : Fin n // i ≤ b}, blockAverage y a.val b.val) ≤ θ i := fun a ↦
    (ciInf_le (hbdd a.val) ⟨b₀, hib₀⟩).trans (hup a.val a.property)
  have hinner₀ : θ i ≤ ⨅ b : {b : Fin n // i ≤ b}, blockAverage y a₀ b.val :=
    le_ciInf fun b ↦ hlow b.val b.property
  unfold isotonicLeastSquares
  refine le_antisymm (ciSup_le hinner) ?_
  exact le_ciSup_of_le (finite_range _).bddAbove ⟨a₀, ha₀i⟩ hinner₀

/-- GAPS 103.27: the adaptive variation risk bound for Gaussian isotonic least squares.
The more general independent finite-variance-error version is not asserted here. -/
theorem isotonicGaussianRisk_le :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ θ : Fin n → ℝ, Monotone θ →
      ∀ T : (Fin n → ℝ) → (Fin n → ℝ), Measurable T →
      (∀ y, IsIsotonicRegressionEstimator y (T y)) →
      isotonicGaussianRisk θ T ≤ ENNReal.ofReal
        (C * (Real.rpow (finiteVectorVariation θ / n) (2 / 3 : ℝ) +
          Real.log (Real.exp 1 * n) / n)) := by
  sorry

/-- GAPS 103.27: no estimator improves the Gaussian bounded-isotonic minimax rate. -/
theorem isotonicGaussianMinimaxRisk_lower_bound :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 / 3 : ℝ)) ≤
        isotonicGaussianMinimaxRisk n := by
  sorry

/-- Orthogonal least-squares fit within a selected linear model. -/
def projectionModelFit {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (S m).starProjection y

/-- Penalized empirical residual criterion for linear model selection. -/
def penalizedModelCriterion {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (pen : M → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (m : M) : ℝ :=
  ‖y - projectionModelFit S m y‖ ^ 2 / n + pen m

/-- Normalized prediction risk of a selected projection fit in Gaussian regression. -/
def selectedProjectionRisk {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (select : EuclideanSpace ℝ (Fin n) → M)
    (f : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖projectionModelFit S (select y) y - f‖ ^ 2 / n)
    ∂(multivariateGaussian f (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))

/-- GAPS 103.35: the countable-model oracle inequality for penalized least squares.
The prior weights, dimension penalty, and empirical minimizer are explicit. -/
theorem selectedProjectionRisk_oracle_bound :
    ∃ κ₀ > (0 : ℝ), ∀ κ > κ₀, ∃ C > (0 : ℝ),
      ∀ n : ℕ, 0 < n → ∀ (M : Type*) [Countable M] [Nonempty M]
      [MeasurableSpace M] [MeasurableSingletonClass M],
      ∀ S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ π : M → ℝ≥0, (∀ m, 0 < π m) → (∑' m, (π m : ℝ≥0∞)) ≤ 1 →
      ∀ σ : ℝ, 0 < σ → ∀ pen : M → ℝ,
      (∀ m, κ * σ ^ 2 / n *
        (Module.finrank ℝ (S m) + Real.log (1 / (π m : ℝ))) ≤ pen m) →
      ∀ select : EuclideanSpace ℝ (Fin n) → M, Measurable select →
      (∀ y m, penalizedModelCriterion S pen y (select y) ≤ penalizedModelCriterion S pen y m) →
      ∀ f : EuclideanSpace ℝ (Fin n),
      selectedProjectionRisk S select f σ ≤ ENNReal.ofReal
        (C * ((⨅ m, ‖f - projectionModelFit S m f‖ ^ 2 / n + pen m) + σ ^ 2 / n)) := by
  sorry

/-- The isotonic cone is convex. -/
theorem convex_isotonicCone (n : ℕ) : Convex ℝ (isotonicCone n) := by
  intro x hx y hy a b ha hb _ i j hij
  change a * x i + b * y i ≤ a * x j + b * y j
  have hx' := hx hij
  have hy' := hy hij
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hy')]

/-- The fitted value is unchanged when the response already lies in the selected model. -/
theorem projectionModelFit_of_mem {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ S m) : projectionModelFit S m y = y := by
  exact Submodule.starProjection_eq_self_iff.mpr hy

end CKSD
