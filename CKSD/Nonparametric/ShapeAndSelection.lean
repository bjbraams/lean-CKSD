module

public import CKSD.Nonparametric.Models
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import CKSD.Nonparametric.LowerBounds.Testing
public import CKSD.Nonparametric.LowerBounds.Gaussian

/-!
# Isotonic regression and penalized model selection

Isotonic least squares fits a nondecreasing vector to responses `y₁, …, yₙ`. This file proves
that the fit exists and is unique, characterizes it by its variational inequality, and shows
that it is given by the max–min formula `θ̂ᵢ = max_{a ≤ i} min_{b ≥ i} ȳ[a, b]` of block
averages. It also states the Gaussian adaptive risk bound and the matching minimax lower bound,
with the empirical squared norm normalized by `1/n`, and the oracle inequality for penalized
least-squares selection among countably many linear models with orthogonal-projection fits.

## Main definitions

* `CKSD.isotonicCone n`: the cone of nondecreasing vectors in `ℝⁿ`.
* `CKSD.isotonicLeastSquares y`: the max–min block-average formula.
* `CKSD.isotonicGaussianRisk`, `CKSD.isotonicGaussianMinimaxRisk`: Gaussian risks.
* `CKSD.projectionModelFit`, `CKSD.penalizedModelCriterion`, `CKSD.selectedProjectionRisk`:
  projection fits, the penalized residual criterion, and the risk of the selected fit.

## Main results

* `CKSD.existsUnique_isIsotonicRegressionEstimator`: existence and uniqueness of the fit.
* `CKSD.IsIsotonicRegressionEstimator.sum_mul_sub_nonpos`: the variational inequality.
* `CKSD.isIsotonicRegressionEstimator_isotonicLeastSquares`: the max–min formula.
* `CKSD.isotonicGaussianRisk_le`: the `n^{-2/3}` adaptive upper bound (stated).
* `CKSD.isotonicGaussianMinimaxRisk_lower_bound`: the matching minimax lower bound, by Assouad's
  lemma over a hypercube of block-constant monotone vectors, with the Gaussian total variation
  bound `CKSD.totalVariationDistance_pi_gaussianReal_le`.
* `CKSD.selectedProjectionRisk_oracle_bound`: the oracle inequality for penalized model
  selection (stated).

Sources: GAPS 103.27 and 103.35.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Cone of nondecreasing finite real vectors. -/
def isotonicCone (n : ℕ) : Set (Fin n → ℝ) := {θ | Monotone θ}

/-- The isotonic cone is convex. -/
theorem convex_isotonicCone (n : ℕ) : Convex ℝ (isotonicCone n) := by
  intro x hx y hy a b ha hb _ i j hij
  change a * x i + b * y i ≤ a * x j + b * y j
  have hx' := hx hij
  have hy' := hy hij
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hy')]

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
  have hconv : Convex ℝ K :=
    (convex_isotonicCone n).linear_preimage (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
  have hne : K.Nonempty := ⟨0, fun _ _ _ ↦ le_rfl⟩
  have : Nonempty K := hne.to_subtype
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hsq (a : EuclideanSpace ℝ (Fin n)) :
      ‖u - a‖ ^ 2 = ∑ i, (y i - a i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [u, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
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

/-- Suffix sums of the isotonic residual are nonpositive: `∑_{j ≥ k} (yⱼ - θ̂ⱼ) ≤ 0`. -/
theorem IsIsotonicRegressionEstimator.sum_ite_le_sub_nonpos {n : ℕ} {y θ : Fin n → ℝ}
    (hθ : IsIsotonicRegressionEstimator y θ) (k : ℕ) :
    ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) ≤ 0 := by
  have := hθ.sum_mul_sub_nonpos (fun j ↦ θ j + if k ≤ (j : ℕ) then 1 else 0) (by
    intro i j hij
    have h1 := hθ.1 hij
    have h2 : (i : ℕ) ≤ j := hij
    simp only
    split_ifs with ha hb hb <;> linarith)
  convert this using 2 with j
  split_ifs <;> ring

/-- The total isotonic residual is nonnegative: `0 ≤ ∑ⱼ (yⱼ - θ̂ⱼ)`. Together with
`IsIsotonicRegressionEstimator.sum_ite_le_sub_nonpos` for `k = 0` it vanishes. -/
theorem IsIsotonicRegressionEstimator.sum_sub_nonneg {n : ℕ} {y θ : Fin n → ℝ}
    (hθ : IsIsotonicRegressionEstimator y θ) : 0 ≤ ∑ j : Fin n, (y j - θ j) := by
  have := hθ.sum_mul_sub_nonpos (fun j ↦ θ j - 1) (fun i j hij ↦ by
    have := hθ.1 hij; simp only; linarith)
  have e : ∑ i, (y i - θ i) * (θ i - 1 - θ i) = -∑ j, (y j - θ j) := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ ↦ ?_; ring
  linarith

/-- At a jump `θ̂_{k-1} < θ̂_k` of the isotonic fit, the suffix sum of the residual from `k` on is
nonnegative, hence zero by `IsIsotonicRegressionEstimator.sum_ite_le_sub_nonpos`. -/
theorem IsIsotonicRegressionEstimator.sum_ite_le_sub_nonneg_of_lt {n : ℕ} {y θ : Fin n → ℝ}
    (hθ : IsIsotonicRegressionEstimator y θ) (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hjump : θ ⟨k - 1, by omega⟩ < θ ⟨k, hkn⟩) :
    0 ≤ ∑ j : Fin n, (if k ≤ (j : ℕ) then y j - θ j else 0) := by
  set g := θ ⟨k, hkn⟩ - θ ⟨k - 1, by omega⟩ with hg
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
  have hneg := hθ.sum_ite_le_sub_nonpos
  have htot := hθ.sum_sub_nonneg
  have hjump := hθ.sum_ite_le_sub_nonneg_of_lt
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

/-- GAPS 103.27: the adaptive variation risk bound for Gaussian isotonic least squares. There
is a universal constant `C` such that for every nondecreasing `θ ∈ ℝⁿ` and observations
`yᵢ = θᵢ + εᵢ` with independent standard Gaussian errors, the isotonic least-squares fit `θ̂`
satisfies `E[n⁻¹ ‖θ̂ - θ‖²] ≤ C ((V(θ)/n)^{2/3} + log(e n)/n)`, where `V(θ) = θₙ - θ₁`. The more
general independent finite-variance-error version is not asserted here. -/
theorem isotonicGaussianRisk_le :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ θ : Fin n → ℝ, Monotone θ →
      ∀ T : (Fin n → ℝ) → (Fin n → ℝ),
      (∀ y, IsIsotonicRegressionEstimator y (T y)) →
      isotonicGaussianRisk θ T ≤ ENNReal.ofReal
        (C * (Real.rpow (finiteVectorVariation θ / n) (2 / 3 : ℝ) +
          Real.log (Real.exp 1 * n) / n)) := by
  sorry

section IsotonicLowerBound

open InformationTheory Real

/-- The block of indices `i < m³` with `i / m² = j` has exactly `m²` elements. -/
private theorem card_block {n m : ℕ} (hmn : m ^ 3 ≤ n) (j : Fin m) :
    (Finset.univ.filter fun i : Fin n ↦ i.val < m ^ 3 ∧ i.val / m ^ 2 = j.val).card = m ^ 2 := by
  have hm : 0 < m := j.pos
  have hm2 : 0 < m ^ 2 := by positivity
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range
    (fun i ↦ if i < m ^ 3 ∧ i / m ^ 2 = j.val then 1 else 0) n, ← Finset.card_filter]
  have hj : (j.val + 1) * m ^ 2 ≤ m ^ 3 := by
    calc (j.val + 1) * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ j.isLt
      _ = m ^ 3 := by ring
  have : (Finset.range n).filter (fun i ↦ i < m ^ 3 ∧ i / m ^ 2 = j.val) =
      Finset.Ico (j.val * m ^ 2) ((j.val + 1) * m ^ 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rw [Nat.eq_iff_le_and_ge, Nat.le_div_iff_mul_le hm2, ← Nat.lt_succ_iff,
      Nat.div_lt_iff_lt_mul hm2]
    constructor
    · rintro ⟨-, -, h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega, h2, h1⟩
  rw [this, Nat.card_Ico]
  rw [add_mul, one_mul]; omega

/-- An index below `m³` lies in one of the `m` blocks of length `m²`. -/
private theorem div_sq_lt_of_lt_cube {m i : ℕ} (h : i < m ^ 3) : i / m ^ 2 < m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
    · exact hm
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc i < m ^ 3 := h
    _ = m * m ^ 2 := by ring

/-- The level `-1 + (2j + b) / m` of block `j` of the isotonic lower-bound construction, with
the binary perturbation `b`. -/
private def isoLevel (m : ℕ) (j : ℕ) (b : Bool) : ℝ :=
  -1 + (2 * (j : ℝ) + (if b then 1 else 0)) / m

/-- The nondecreasing vector of the isotonic lower-bound hypercube indexed by `w ∈ {0,1}^m`:
constant `isoLevel m j (w j)` on the `j`-th block of length `m²`, and `1` beyond `m³`. -/
private def isoVertex (n m : ℕ) (w : Fin m → Bool) (i : Fin n) : ℝ :=
  if h : i.val < m ^ 3 then isoLevel m (i.val / m ^ 2) (w ⟨i.val / m ^ 2, div_sq_lt_of_lt_cube h⟩)
  else 1

/-- Levels of distinct blocks are ordered as the blocks, whatever the perturbations. -/
private theorem isoLevel_le_isoLevel {m j j' : ℕ} (hm : 0 < m) (hj : j < j') (b b' : Bool) :
    isoLevel m j b ≤ isoLevel m j' b' := by
  unfold isoLevel
  have hjj : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hj
  have : (2 * (j : ℝ) + (if b then 1 else 0)) ≤ 2 * (j' : ℝ) + (if b' then 1 else 0) := by
    split_ifs <;> linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  linarith [div_le_div_of_nonneg_right this hmR.le]

/-- Block levels are at most `1`. -/
private theorem isoLevel_le_one {m j : ℕ} (hj : j < m) (b : Bool) : isoLevel m j b ≤ 1 := by
  unfold isoLevel
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hjj : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have : (2 * (j : ℝ) + (if b then 1 else 0)) / m ≤ 2 := by
    rw [div_le_iff₀ hm]; split_ifs <;> linarith
  linarith

/-- Block levels are at least `-1`. -/
private theorem neg_one_le_isoLevel (m j : ℕ) (b : Bool) : -1 ≤ isoLevel m j b := by
  unfold isoLevel
  have : 0 ≤ (2 * (j : ℝ) + (if b then 1 else 0)) / m := by
    apply div_nonneg _ (Nat.cast_nonneg _); split_ifs <;> positivity
  linarith

/-- Every vertex of the isotonic lower-bound hypercube is nondecreasing. -/
private theorem monotone_isoVertex (n m : ℕ) (w : Fin m → Bool) : Monotone (isoVertex n m w) := by
  intro i i' hii
  unfold isoVertex
  by_cases h' : i'.val < m ^ 3
  · have h : i.val < m ^ 3 := lt_of_le_of_lt hii h'
    simp only [h, h', ↓reduceDIte]
    have hm : 0 < m := Nat.zero_lt_of_lt (div_sq_lt_of_lt_cube h)
    have hdiv : i.val / m ^ 2 ≤ i'.val / m ^ 2 := Nat.div_le_div_right hii
    rcases hdiv.lt_or_eq with hlt | heq
    · exact isoLevel_le_isoLevel hm hlt _ _
    · have : (⟨i.val / m ^ 2, div_sq_lt_of_lt_cube h⟩ : Fin m) =
          ⟨i'.val / m ^ 2, div_sq_lt_of_lt_cube h'⟩ := Fin.ext heq
      rw [this, heq]
  · simp only [h', ↓reduceDIte]
    split_ifs with h
    · exact isoLevel_le_one (div_sq_lt_of_lt_cube h) _
    · exact le_rfl

/-- Every vertex of the isotonic lower-bound hypercube has entries in `[-1, 1]`. -/
private theorem abs_isoVertex_le (n m : ℕ) (w : Fin m → Bool) (i : Fin n) :
    |isoVertex n m w i| ≤ 1 := by
  unfold isoVertex
  split_ifs with h
  · exact abs_le.mpr ⟨neg_one_le_isoLevel _ _ _, isoLevel_le_one (div_sq_lt_of_lt_cube h) _⟩
  · simp

/-- The `j`-th block of indices, `{i < m³ | i / m² = j}`. -/
private def isoBlock (n m : ℕ) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n ↦ i.val < m ^ 3 ∧ i.val / m ^ 2 = j.val

/-- On the `j`-th block a vertex takes the value `isoLevel m j (w j)`. -/
private theorem isoVertex_of_mem_isoBlock {n m : ℕ} (w : Fin m → Bool) {j : Fin m} {i : Fin n}
    (hi : i ∈ isoBlock n m j) : isoVertex n m w i = isoLevel m j (w j) := by
  simp only [isoBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [isoVertex, hi.1, ↓reduceDIte, hi.2]

/-- The two perturbations of a block level differ by at most `1 / m`. -/
private theorem isoLevel_sub_isoLevel_sq_le (m j : ℕ) (b b' : Bool) :
    (isoLevel m j b' - isoLevel m j b) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
  unfold isoLevel
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [show -1 + (2 * (j : ℝ) + (if b' then 1 else 0)) / m - (-1 + (2 * (j : ℝ) +
    (if b then 1 else 0)) / m) = ((if b' then 1 else 0) - (if b then 1 else 0)) / m by
    field_simp; ring, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

/-- Neighbouring vertices of the hypercube are at squared Euclidean distance at most `1`. -/
private theorem sum_sq_isoVertex_sub_le {n m : ℕ} (hmn : m ^ 3 ≤ n) (w w' : Fin m → Bool)
    (hww : hammingDist w w' = 1) :
    ∑ i, (isoVertex n m w' i - isoVertex n m w i) ^ 2 ≤ 1 := by
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hww
  have hdiff : ∀ j, j ≠ j₀ → w j = w' j := by
    intro j hj
    by_contra h
    have : j ∈ (Finset.univ.filter fun i ↦ w i ≠ w' i) := by simp [h]
    rw [show (Finset.univ.filter fun i ↦ w i ≠ w' i) = {j₀} from hj₀] at this
    exact hj (Finset.mem_singleton.mp this)
  have hpt : ∀ i : Fin n, (isoVertex n m w' i - isoVertex n m w i) ^ 2 ≤
      if i ∈ isoBlock n m j₀ then 1 / (m : ℝ) ^ 2 else 0 := by
    intro i
    by_cases h : i.val < m ^ 3
    · set j : Fin m := ⟨i.val / m ^ 2, div_sq_lt_of_lt_cube h⟩
      have hij : i ∈ isoBlock n m j := by simp [isoBlock, h, j]
      rw [isoVertex_of_mem_isoBlock w hij, isoVertex_of_mem_isoBlock w' hij]
      by_cases hj : j = j₀
      · simp only [← hj, hij, ↓reduceIte]; exact isoLevel_sub_isoLevel_sq_le _ _ _ _
      · have : i ∉ isoBlock n m j₀ := by
          intro h'
          simp only [isoBlock, Finset.mem_filter, Finset.mem_univ, true_and] at h'
          exact hj (Fin.ext h'.2)
        simp only [this, ↓reduceIte, hdiff j hj]; simp
    · have : i ∉ isoBlock n m j₀ := by simp [isoBlock, h]
      simp [isoVertex, h, this]
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans (le_of_eq ?_)
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, isoBlock,
    card_block hmn]
  have hm : (0 : ℝ) < m := by exact_mod_cast j₀.pos
  push_cast
  field_simp

/-- The hypercube vertex decoded from a vector `t`: on each block, the nearer of the two levels
in squared distance. -/
private def isoDecode (n m : ℕ) (t : Fin n → ℝ) (j : Fin m) : Bool :=
  decide (∑ i ∈ isoBlock n m j, (t i - isoLevel m j true) ^ 2 <
    ∑ i ∈ isoBlock n m j, (t i - isoLevel m j false) ^ 2)

/-- A wrongly decoded block contributes at least `1 / 4` to the squared loss. -/
private theorem le_sum_isoBlock {n m : ℕ} (hmn : m ^ 3 ≤ n) (t : Fin n → ℝ) (w : Fin m → Bool)
    (j : Fin m) :
    (if isoDecode n m t j ≠ w j then (1 / 4 : ℝ) else 0) ≤
      ∑ i ∈ isoBlock n m j, (t i - isoVertex n m w i) ^ 2 := by
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [isoVertex_of_mem_isoBlock w hi]]
  set A := ∑ i ∈ isoBlock n m j, (t i - isoLevel m j true) ^ 2
  set Z := ∑ i ∈ isoBlock n m j, (t i - isoLevel m j false) ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hm : (0 : ℝ) < m := by exact_mod_cast j.pos
  have hlev : (isoLevel m j true - isoLevel m j false) ^ 2 = 1 / (m : ℝ) ^ 2 := by
    unfold isoLevel; simp only [↓reduceIte, Bool.false_eq_true]; field_simp; ring
  have hsum : (1 : ℝ) ≤ 2 * A + 2 * Z := by
    have : ∑ i ∈ isoBlock n m j, (isoLevel m j true - isoLevel m j false) ^ 2 = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, isoBlock, card_block hmn, hlev]
      push_cast; field_simp
    have h2 : ∑ i ∈ isoBlock n m j, (isoLevel m j true - isoLevel m j false) ^ 2 ≤
        ∑ i ∈ isoBlock n m j, (2 * (t i - isoLevel m j true) ^ 2 +
          2 * (t i - isoLevel m j false) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (t i - isoLevel m j true +
        (t i - isoLevel m j false))]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, this] at h2
    exact h2
  by_cases hAZ : A < Z
  · have hd : isoDecode n m t j = true := decide_eq_true hAZ
    rw [hd]
    cases w j
    · simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte]; linarith
    · simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact hA
  · have hd : isoDecode n m t j = false := decide_eq_false hAZ
    rw [hd]
    cases w j
    · simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact hZ
    · simp only [ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]; linarith

/-- The squared loss of `t` at a vertex `w` dominates a quarter of the Hamming distance
between the decoded vertex and `w`. -/
private theorem hammingDist_isoDecode_div_four_le {n m : ℕ} (hmn : m ^ 3 ≤ n) (t : Fin n → ℝ)
    (w : Fin m → Bool) :
    (hammingDist (isoDecode n m t) w : ℝ) / 4 ≤ ∑ i, (t i - isoVertex n m w i) ^ 2 := by
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (isoBlock n m) := by
    intro j _ j' _ hjj
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    simp only [isoBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact hjj (Fin.ext (hi.2.symm.trans hi'.2))
  have hham : (hammingDist (isoDecode n m t) w : ℝ) / 4 =
      ∑ j, (if isoDecode n m t j ≠ w j then (1 / 4 : ℝ) else 0) := by
    rw [hammingDist, Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> norm_num
  rw [hham]
  calc ∑ j, (if isoDecode n m t j ≠ w j then (1 / 4 : ℝ) else 0)
      ≤ ∑ j, ∑ i ∈ isoBlock n m j, (t i - isoVertex n m w i) ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ le_sum_isoBlock hmn t w j
    _ = ∑ i ∈ Finset.univ.biUnion (isoBlock n m), (t i - isoVertex n m w i) ^ 2 :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ i, (t i - isoVertex n m w i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ ↦ sq_nonneg _

/-- The decoding map is measurable. -/
private theorem measurable_isoDecode (n m : ℕ) : Measurable (isoDecode n m) := by
  rw [measurable_pi_iff]
  intro j
  apply measurable_to_bool
  show MeasurableSet {t | isoDecode n m t j = true}
  simp only [isoDecode, decide_eq_true_eq]
  exact measurableSet_lt (by fun_prop) (by fun_prop)

/-- Assouad's bound for isotonic regression: with `m³ ≤ n`, every measurable estimator has
worst-case risk at least `m / (16 n)` on the bounded monotone class. -/
private theorem ofReal_le_iSup_isotonicGaussianRisk {n m : ℕ} (hm : 1 ≤ m) (hmn : m ^ 3 ≤ n)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) (hT : Measurable T) :
    ENNReal.ofReal (m / (16 * n)) ≤ ⨆ θ : isotonicUnitBall n, isotonicGaussianRisk θ.val T := by
  have hn : (0 : ℝ) < n := by
    have : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ hm
    exact_mod_cast (lt_of_lt_of_le this hmn)
  set P : (Fin m → Bool) → Measure (Fin n → ℝ) :=
    fun w ↦ Measure.pi fun i ↦ gaussianReal (isoVertex n m w i) 1 with hP
  have hnear : ∀ w w', hammingDist w w' = 1 → totalVariationDistance (P w) (P w') ≤ 1 / 2 := by
    intro w w' hww
    refine (totalVariationDistance_pi_gaussianReal_le _ _ one_ne_zero).trans ?_
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have := sum_sq_isoVertex_sub_le hmn w w' hww
    push_cast
    linarith
  set D : (Fin n → ℝ) → (Fin m → Bool) := fun y ↦ isoDecode n m (T y)
  have hD : Measurable D := (measurable_isoDecode n m).comp hT
  have hA := mul_one_sub_div_two_le_sSup_integral_hammingDist m P (1 / 2) hnear D hD
  obtain ⟨w₀, hw₀⟩ := (Set.range_nonempty fun w ↦ ∫ x, (hammingDist (D x) w : ℝ) ∂P w).csSup_mem
    (Set.finite_range _)
  rw [← hw₀] at hA
  set θ : Fin n → ℝ := isoVertex n m w₀
  have hθ : θ ∈ isotonicUnitBall n := ⟨monotone_isoVertex n m w₀, abs_isoVertex_le n m w₀⟩
  refine le_trans ?_ (le_iSup (fun θ : isotonicUnitBall n ↦ isotonicGaussianRisk θ.val T)
    ⟨θ, hθ⟩)
  have hint : Integrable (fun x ↦ (hammingDist (D x) w₀ : ℝ) / (4 * n)) (P w₀) := by
    refine Integrable.of_bound (C := m / (4 * n)) ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact (((measurable_of_countable (fun v ↦ (hammingDist v w₀ : ℝ))).comp hD)
        |>.div_const _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hammingDist_le_card_fintype.trans (by simp)
  calc ENNReal.ofReal (m / (16 * n))
      ≤ ENNReal.ofReal (∫ x, (hammingDist (D x) w₀ : ℝ) / (4 * n) ∂P w₀) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div]
        rw [le_div_iff₀ (by positivity)]
        have : (m : ℝ) / (16 * n) * (4 * n) = m * (1 - 1 / 2) / 2 := by field_simp; ring
        rw [this]; exact hA
    _ = ∫⁻ x, ENNReal.ofReal ((hammingDist (D x) w₀ : ℝ) / (4 * n)) ∂P w₀ :=
        ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ ↦ by positivity)
    _ ≤ isotonicGaussianRisk θ T := by
        unfold isotonicGaussianRisk
        refine lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ (by positivity) hn]
        have := hammingDist_isoDecode_div_four_le hmn (T y) w₀
        have h4 : (hammingDist (D y) w₀ : ℝ) * n = (hammingDist (D y) w₀ : ℝ) / 4 * (4 * n) := by
          ring
        rw [h4]
        exact mul_le_mul_of_nonneg_right this (by positivity) |>.trans_eq (by ring)

/-- If `n < (m + 1)³` then `n^(-2/3) / 32 ≤ m / (16 n)`. -/
private theorem rpow_neg_two_thirds_le {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (hlt : n < (m + 1) ^ 3) :
    (1 / 32) * Real.rpow (n : ℝ) (-2 / 3 : ℝ) ≤ m / (16 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcube : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]; norm_num
  have hroot : (n : ℝ) ^ (1 / 3 : ℝ) < m + 1 := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by positivity) h 3
    rw [hcube] at this
    have : ((m + 1 : ℕ) : ℝ) ^ 3 ≤ n := by push_cast; linarith
    exact absurd (by exact_mod_cast this : (m + 1) ^ 3 ≤ n) (not_le.mpr hlt)
  have hsplit : Real.rpow (n : ℝ) (-2 / 3 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) / n := by
    rw [Real.rpow_eq_pow, show (-2 / 3 : ℝ) = 1 / 3 + (-1 : ℤ) by norm_num,
      Real.rpow_add hnR, Real.rpow_intCast, zpow_neg_one, ← div_eq_mul_inv]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [hsplit, show 1 / 32 * ((n : ℝ) ^ (1 / 3 : ℝ) / n) = ((n : ℝ) ^ (1 / 3 : ℝ) / 2) /
    (16 * n) by field_simp; ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end IsotonicLowerBound

/-- GAPS 103.27: no estimator improves the Gaussian bounded-isotonic minimax rate. There is a
universal `c > 0` such that the minimax risk `inf_T sup_θ E[n⁻¹ ‖T(y) - θ‖²]`, over measurable
estimators and nondecreasing `θ` with `|θᵢ| ≤ 1`, is at least `c n^{-2/3}`. -/
theorem isotonicGaussianMinimaxRisk_lower_bound :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ENNReal.ofReal (c * Real.rpow (n : ℝ) (-2 / 3 : ℝ)) ≤
        isotonicGaussianMinimaxRisk n := by
  refine ⟨1 / 32, by norm_num, fun n hn ↦ ?_⟩
  set m := Nat.findGreatest (fun k ↦ k ^ 3 ≤ n) n
  have hm : 1 ≤ m := Nat.le_findGreatest hn (by simpa using Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hmn : m ^ 3 ≤ n := Nat.findGreatest_spec (P := fun k ↦ k ^ 3 ≤ n) (m := 1) hn
    (by simpa using Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlt : n < (m + 1) ^ 3 := by
    by_contra h
    push Not at h
    have hle : m + 1 ≤ n := le_trans (Nat.le_self_pow (by norm_num) _) h
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hle h
  unfold isotonicGaussianMinimaxRisk
  refine le_iInf fun T ↦ ?_
  exact (ENNReal.ofReal_le_ofReal (rpow_neg_two_thirds_le hn hm hlt)).trans
    (ofReal_le_iSup_isotonicGaussianRisk hm hmn T.val T.property)

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

/-- GAPS 103.35: the countable-model oracle inequality for penalized least squares. For a
countable family of linear models `S m ⊆ ℝⁿ` with prior weights `π m > 0`, `∑ π m ≤ 1`,
Gaussian noise of variance `σ²`, and a penalty
`pen m ≥ κ σ² (dim S m + log (1 / π m)) / n` with `κ > κ₀`, the measurable minimizer `m̂` of the
penalized residual criterion satisfies
`E[n⁻¹ ‖Π_{m̂} y - f‖²] ≤ C (inf_m (n⁻¹ ‖f - Π_m f‖² + pen m) + σ² / n)`. -/
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

/-- The fitted value equals the response exactly when the response lies in the selected
model. -/
theorem projectionModelFit_eq_self_iff {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) : projectionModelFit S m y = y ↔ y ∈ S m :=
  Submodule.starProjection_eq_self_iff

end CKSD
