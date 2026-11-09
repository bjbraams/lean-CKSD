module

public import CKSD.Nonparametric.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Analysis.Complex.ExponentialBounds
public import CKSD.Nonparametric.LowerBounds.Testing
public import CKSD.Nonparametric.LowerBounds.Gaussian
public import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Gaussian sequence, regression, and sparse estimation models

The Gaussian sequence model `y_j = θ_j + ε ξ_j` with its ellipsoid parameter sets, the
Nadaraya–Watson smoother, isotonic least squares, the lasso with the compatibility condition, and
the sparse Gaussian location model. Losses that may be infinite take values in `ℝ≥0∞`, and
minimax risks are infima over measurable estimators of suprema of such risks.

## Main definitions

* `CKSD.gaussianSequenceLaw`, `CKSD.sequenceEllipsoid`, `CKSD.sobolevEllipsoid`,
  `CKSD.gaussianSequenceMinimaxRisk`, `CKSD.gaussianSequenceLinearMinimaxRisk`: the Gaussian
  sequence experiment, the ellipsoids `∑ (a_j θ_j)² ≤ R`, and the minimax and linear minimax
  squared risks.
* `CKSD.nadarayaWatson`: the Nadaraya–Watson estimator, with value `0` where all weights vanish.
* `CKSD.IsIsotonicRegressionEstimator`: a least-squares fit over nondecreasing vectors.
* `CKSD.lassoObjective`, `CKSD.IsLassoEstimator`, `CKSD.HasCompatibility`: the lasso criterion
  `‖y - A β‖² / (2n) + λ ‖β‖₁`, its minimizers, and the compatibility condition on a cone.
* `CKSD.sparseGaussianLaw`, `CKSD.sparseGaussianMinimaxRisk`: the Gaussian location model and
  the minimax squared risk over `s`-sparse means.
* `CKSD.softThreshold`: the soft-thresholding map `y ↦ sign y (|y| - λ)₊`.

## Main results

* `CKSD.tendsto_gaussianSequenceMinimaxRisk_div_linear` (Pinsker): on an ellipsoid the minimax
  risk is asymptotically equivalent to the linear minimax risk as `ε → 0`.
* `CKSD.sparseGaussianMinimaxRisk_bounds`: the minimax risk over `s`-sparse means is of order
  `σ² s log(p / s)`, with constants `c = 1 / 512` and `C = 17`. The upper bound is attained by
  soft thresholding at `σ √(2 log (p / s))`; the lower bound places one spike in each of `s`
  disjoint blocks of `m = ⌊p / s⌋` coordinates and combines an averaged Fano inequality (for
  `m ≥ 1024`) or a two-point bound (otherwise) in each block with averaging over the product of
  the block hypotheses.
* `CKSD.sparseGaussianLaw_eq_map_pi`: `N(θ, σ² I_p)` is the product of its coordinate laws, from
  TauCeti's `TauCeti.Probability.map_affine_multivariateGaussian` and
  `TauCeti.Probability.multivariateGaussian_one_eq_map_pi`.
* `CKSD.sum_measureReal_le_of_klDiv_le`: Fano's inequality in averaged form,
  `∑_j P_j(A_j) ≤ m / 4 + m (K + log 2) / log (m / 4)` for disjoint events.
* `CKSD.lintegral_softThreshold_sub_sq_le`, `CKSD.lintegral_softThreshold_sq_le`: the Gaussian
  risk of soft thresholding at a nonzero and at a zero mean.

Sources: GAPS 103.7, 103.9, 103.21, 103.33, and 103.34.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Gaussian sequence observation law with noise standard deviation `ε`. -/
def gaussianSequenceLaw (θ : ℕ → ℝ) (ε : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun j ↦ gaussianReal (θ j) (Real.toNNReal (ε ^ 2)))

/-- Squared sequence error, taking value infinity when the difference is not square summable. -/
def sequenceSquaredError (a b : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal ((a j - b j) ^ 2)

/-- Weighted ellipsoid; the radius convention is `sum (a_j theta_j)^2 ≤ R`. -/
def sequenceEllipsoid (a : ℕ → ℝ) (R : ℝ≥0∞) : Set (ℕ → ℝ) :=
  {θ | (∑' j, ENNReal.ofReal ((a j * θ j) ^ 2)) ≤ R}

/-- Sobolev ellipsoid indexed from frequency one. -/
def sobolevEllipsoid (β : ℝ) (R : ℝ≥0∞) : Set (ℕ → ℝ) :=
  sequenceEllipsoid (fun j ↦ Real.rpow (j + 1) β) R

/-- Minimax squared risk over measurable Gaussian-sequence estimators. -/
def gaussianSequenceMinimaxRisk (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : (ℕ → ℝ) → (ℕ → ℝ) // Measurable T},
    ⨆ θ : Θ, ∫⁻ y, sequenceSquaredError (T.val y) θ.val ∂gaussianSequenceLaw θ.val ε

/-- Linear minimax risk with coordinatewise shrinkage estimators. -/
def gaussianSequenceLinearMinimaxRisk (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℕ → ℝ, ⨆ θ : Θ,
    ∫⁻ y, sequenceSquaredError (fun j ↦ c j * y j) θ.val ∂gaussianSequenceLaw θ.val ε

/-- GAPS 103.9: Pinsker's theorem. On the ellipsoid `∑ (a_j θ_j)² ≤ R` with positive
nondecreasing `a_j → ∞`, the ratio of the minimax squared risk to the linear minimax squared
risk tends to `1` as the noise level `ε` decreases to `0`. -/
theorem tendsto_gaussianSequenceMinimaxRisk_div_linear (a : ℕ → ℝ)
    (ha : ∀ j, 0 < a j) (hmono : Monotone a) (hlim : Tendsto a atTop atTop)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun ε ↦
      (gaussianSequenceMinimaxRisk (sequenceEllipsoid a (ENNReal.ofReal R)) ε).toReal /
      (gaussianSequenceLinearMinimaxRisk (sequenceEllipsoid a (ENNReal.ofReal R)) ε).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  sorry

/-- Nadaraya–Watson estimator; the value when all weights vanish is zero. -/
def nadarayaWatson {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (y : Fin n → ℝ)
    (t : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ i, K (h⁻¹ • (x i - t)) * y i) / (∑ i, K (h⁻¹ • (x i - t)))

/-- Squared regression prediction error under the feature law. -/
def regressionPredictionError {X : Type*} [MeasurableSpace X]
    (P : Measure X) (m estimate : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((estimate x - m x) ^ 2) ∂P

/-- An isotonic least-squares estimator is a minimizer over the monotone cone. -/
def IsIsotonicRegressionEstimator {n : ℕ} (y estimate : Fin n → ℝ) : Prop :=
  Monotone estimate ∧ ∀ θ : Fin n → ℝ, Monotone θ →
    (∑ i, (y i - estimate i) ^ 2) ≤ ∑ i, (y i - θ i) ^ 2

/-- The lasso objective, with the `1/(2n)` squared-error normalization. -/
def lassoObjective {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (β : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ‖y - A β‖ ^ 2 / (2 * n) + lambda * restrictedL1Norm Finset.univ β

/-- A lasso estimate minimizes the lasso objective. -/
def IsLassoEstimator {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (β : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ b, lassoObjective A y lambda β ≤ lassoObjective A y lambda b

/-- The compatibility condition with constant `κ` on the cone `‖δ_{Sᶜ}‖₁ ≤ L ‖δ_S‖₁`:
`κ² ‖δ_S‖₁² ≤ |S| ‖A δ‖² / n` for every `δ` in the cone. -/
def HasCompatibility {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) (L κ : ℝ) : Prop :=
  ∀ δ, restrictedL1Norm Sᶜ δ ≤ L * restrictedL1Norm S δ →
    κ ^ 2 * (restrictedL1Norm S δ) ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n

/-- Gaussian finite-dimensional sparse estimation experiment. -/
def sparseGaussianLaw {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin p)) :=
  multivariateGaussian θ (σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))

/-- Minimax squared risk over the `s`-sparse vectors. -/
def sparseGaussianMinimaxRisk (p s : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) // Measurable T},
    ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
      ∫⁻ y, ENNReal.ofReal (‖T.val y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ

section SparseMinimax

variable {p s m : ℕ}

/-- The sparse Gaussian law `N(θ, σ² I_p)` is the product of the coordinate laws
`N(θ_i, σ²)`, transported to Euclidean space. -/
theorem sparseGaussianLaw_eq_map_pi {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) (σ : ℝ) :
    sparseGaussianLaw θ σ =
      (Measure.pi fun i ↦ gaussianReal (θ i) (Real.toNNReal (σ ^ 2))).map (WithLp.toLp 2) := by
  have haff := TauCeti.Probability.map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
    Matrix.PosSemidef.one (σ • (1 : Matrix (Fin p) (Fin p) ℝ)) θ
  have hcov : σ • (1 : Matrix (Fin p) (Fin p) ℝ) * 1 *
      (σ • (1 : Matrix (Fin p) (Fin p) ℝ)).transpose
      = σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_one, smul_mul_smul,
      Matrix.mul_one, sq]
  rw [hcov, map_zero, zero_add] at haff
  rw [sparseGaussianLaw, ← haff, TauCeti.Probability.multivariateGaussian_one_eq_map_pi,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hpi : (Measure.pi fun i : Fin p ↦ gaussianReal ((0 : EuclideanSpace ℝ (Fin p)) i) 1).map
      (fun x i ↦ σ * x i + θ i) =
        Measure.pi fun i ↦ gaussianReal (θ i) (Real.toNNReal (σ ^ 2)) := by
    rw [Measure.pi_map_pi (f := fun i (x : ℝ) ↦ σ * x + θ i) (fun _ ↦ by fun_prop)]
    congr 1; funext i
    have : (fun x : ℝ ↦ σ * x + θ i) = (fun x ↦ x + θ i) ∘ (fun x ↦ σ * x) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    simp only [PiLp.zero_apply, mul_zero, zero_add, mul_one]
    congr 1
    ext; simp [sq_nonneg]
  rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i
  simp [Matrix.toEuclideanLin, add_comm]

/-- Position of coordinate `j` of block `b` among the first `s m` coordinates. -/
private def blockIndex (h : s * m ≤ p) (b : Fin s) (j : Fin m) : Fin p :=
  Fin.castLE h (finProdFinEquiv (b, j))

/-- Distinct block positions are distinct coordinates. -/
private theorem blockIndex_inj (h : s * m ≤ p) {b b' : Fin s} {j j' : Fin m} :
    blockIndex h b j = blockIndex h b' j' ↔ b = b' ∧ j = j' := by
  constructor
  · intro hb
    have := finProdFinEquiv.injective (Fin.castLE_injective h hb)
    simpa [Prod.ext_iff] using this
  · rintro ⟨rfl, rfl⟩; rfl

/-- The mean with one spike of height `a` in each block, at position `J b` of block `b`. -/
private def blockMean (h : s * m ≤ p) (a : ℝ) (J : Fin s → Fin m) : Fin p → ℝ :=
  fun i ↦ ∑ b, if blockIndex h b (J b) = i then a else 0

/-- Block `b` of the spike mean is the spike `a e_{J b}`. -/
private theorem blockMean_blockIndex (h : s * m ≤ p) (a : ℝ) (J : Fin s → Fin m) (b : Fin s)
    (j : Fin m) :
    blockMean h a J (blockIndex h b j) = if J b = j then a else 0 := by
  rw [blockMean, Finset.sum_eq_single b]
  · simp [blockIndex_inj]
  · intro b' _ hb'; simp [blockIndex_inj, hb']
  · simp

/-- A spike mean with one spike per block is `s`-sparse. -/
private theorem sparsity_blockMean_le (h : s * m ≤ p) (a : ℝ) (J : Fin s → Fin m) :
    sparsity (WithLp.toLp 2 (blockMean h a J)) ≤ s := by
  unfold sparsity
  calc (Finset.univ.filter fun i ↦ (WithLp.toLp 2 (blockMean h a J)) i ≠ 0).card
      ≤ (Finset.univ.image fun b ↦ blockIndex h b (J b)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        by_contra hne
        push Not at hne
        exact hi (Finset.sum_eq_zero fun b _ ↦ by simp [hne b])
    _ ≤ s := Finset.card_image_le.trans (by simp)

/-- Two spike means that differ only in block `b` differ by `a (e_{(b, j)} - e_{(b, k)})`. -/
private theorem blockMean_update_sub (h : s * m ≤ p) (a : ℝ) (J : Fin s → Fin m) (b : Fin s)
    (j k : Fin m) (i : Fin p) :
    blockMean h a (Function.update J b j) i - blockMean h a (Function.update J b k) i =
      (if blockIndex h b j = i then a else 0) - (if blockIndex h b k = i then a else 0) := by
  rw [blockMean, blockMean, ← Finset.sum_sub_distrib, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [Function.update_of_ne hb']
  · simp

/-- Two spike means that differ only in block `b` are at squared distance at most `2 a²`. -/
private theorem sum_sq_blockMean_update_sub_le (h : s * m ≤ p) (a : ℝ) (J : Fin s → Fin m)
    (b : Fin s) (j k : Fin m) :
    ∑ i, (blockMean h a (Function.update J b j) i -
      blockMean h a (Function.update J b k) i) ^ 2 ≤ 2 * a ^ 2 := by
  simp_rw [blockMean_update_sub]
  have hpt : ∀ i, ((if blockIndex h b j = i then a else 0) -
      (if blockIndex h b k = i then a else 0)) ^ 2 ≤
      (if blockIndex h b j = i then a ^ 2 else 0) +
        (if blockIndex h b k = i then a ^ 2 else 0) := by
    intro i
    split_ifs <;> nlinarith [sq_nonneg a]
  refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  simp; ring

/-- Averaging over the product of block hypotheses: if, in each block and for each choice of the
other blocks, the success probabilities sum to at most `β m`, some hypothesis has at least
`s (1 - β)` expected block failures. -/
private theorem exists_mul_one_sub_le_sum_measureReal_compl {X : Type*} [MeasurableSpace X]
    [NeZero m]
    (P : (Fin s → Fin m) → Measure X) [∀ J, IsProbabilityMeasure (P J)]
    (A : Fin s → Fin m → Set X) (hA : ∀ b j, MeasurableSet (A b j)) (β : ℝ)
    (hH : ∀ b J, ∑ j, (P (Function.update J b j)).real (A b j) ≤ β * m) :
    ∃ J, (s : ℝ) * (1 - β) ≤ ∑ b, (P J).real (A b (J b))ᶜ := by
  set N : ℝ := (Fintype.card (Fin s → Fin m) : ℝ) with hN
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hblock : ∀ b, ∑ J, (P J).real (A b (J b)) ≤ β * N := by
    intro b
    set f : (Fin s → Fin m) → ℝ := fun J ↦ (P J).real (A b (J b)) with hf
    have hshift : ∀ k : Fin m, ∑ J, f J = ∑ J, f (Function.update J b (J b + k)) := by
      intro k
      let e : (Fin s → Fin m) ≃ (Fin s → Fin m) :=
        { toFun := fun J ↦ Function.update J b (J b + k)
          invFun := fun J ↦ Function.update J b (J b - k)
          left_inv := fun J ↦ by simp
          right_inv := fun J ↦ by simp }
      exact (Fintype.sum_equiv e _ _ fun J ↦ rfl).symm
    have hsum : (m : ℝ) * ∑ J, f J = ∑ J, ∑ j, (P (Function.update J b j)).real (A b j) := by
      calc (m : ℝ) * ∑ J, f J = ∑ _k : Fin m, ∑ J, f J := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ k : Fin m, ∑ J, f (Function.update J b (J b + k)) :=
            Finset.sum_congr rfl fun k _ ↦ hshift k
        _ = ∑ J, ∑ k : Fin m, f (Function.update J b (J b + k)) := Finset.sum_comm
        _ = ∑ J, ∑ j, (P (Function.update J b j)).real (A b j) := by
            refine Finset.sum_congr rfl fun J _ ↦ ?_
            exact Fintype.sum_equiv (Equiv.addLeft (J b)) _ _ fun k ↦ by simp [hf]
    have hle : (m : ℝ) * ∑ J, f J ≤ (m : ℝ) * (β * N) := by
      rw [hsum]
      calc ∑ J, ∑ j, (P (Function.update J b j)).real (A b j) ≤ ∑ _J : Fin s → Fin m, β * m :=
            Finset.sum_le_sum fun J _ ↦ hH b J
        _ = (m : ℝ) * (β * N) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]; ring
    exact le_of_mul_le_mul_left hle hm
  have htotal : ∑ _J : Fin s → Fin m, (s : ℝ) * (1 - β) ≤
      ∑ J, ∑ b, (P J).real (A b (J b))ᶜ := by
    simp_rw [probReal_compl_eq_one_sub (hA _ _)]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) ↦ hblock b
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [← hN]
    nlinarith
  obtain ⟨J, -, hJ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htotal
  exact ⟨J, hJ⟩

/-- Two-point bound on success probabilities: for disjoint events,
`P₀(A₀) + P₁(A₁) ≤ 1 + TV(P₀, P₁)`. -/
theorem sum_measureReal_le_one_add_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P : Fin 2 → Measure X) [∀ j, IsProbabilityMeasure (P j)] (A : Fin 2 → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (hdisj : Disjoint (A 0) (A 1)) :
    ∑ j, (P j).real (A j) ≤ 1 + totalVariationDistance (P 0) (P 1) := by
  rw [Fin.sum_univ_two]
  have h1 := abs_measureReal_sub_le_totalVariationDistance (P 0) (P 1) (A 1) (hA 1)
  have h2 : (P 0).real (A 0) + (P 0).real (A 1) ≤ 1 := by
    rw [← measureReal_union hdisj (hA 1)]; exact measureReal_le_one
  have := neg_abs_le ((P 0).real (A 1) - (P 1).real (A 1))
  linarith

/-- Fano's inequality in averaged form: for `m > 4` laws at Kullback–Leibler divergence at most
`K` from a reference law `Q` and pairwise disjoint events, the success probabilities satisfy
`∑_j P_j(A_j) ≤ m / 4 + m (K + log 2) / log (m / 4)`. -/
theorem sum_measureReal_le_of_klDiv_le {X : Type*} [MeasurableSpace X] (hm : 4 < m)
    (P : Fin m → Measure X) [∀ j, IsProbabilityMeasure (P j)] (Q : Measure X)
    [IsProbabilityMeasure Q] (K : ℝ) (hKL : ∀ j, InformationTheory.klDiv (P j) Q ≠ ∞)
    (hK : ∀ j, (InformationTheory.klDiv (P j) Q).toReal ≤ K) (A : Fin m → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    ∑ j, (P j).real (A j) ≤ m / 4 + m * (K + Real.log 2) / Real.log (m / 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm4 : (1 : ℝ) < m / 4 := by
    rw [lt_div_iff₀ (by norm_num)]; exact_mod_cast (show 4 < m by omega)
  have hlog : 0 < Real.log (m / 4) := Real.log_pos hm4
  have hK0 : 0 ≤ K := (ENNReal.toReal_nonneg).trans (hK ⟨0, by omega⟩)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set G := Finset.univ.filter fun j ↦ Q.real (A j) ≤ 4 / m with hG
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ Q.real (A j) ≤ 4 / m)]
  -- few events have large reference mass
  have hbad : ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ Q.real (A j) ≤ 4 / m), (P j).real (A j) ≤
      m / 4 := by
    set B := Finset.univ.filter (fun j ↦ ¬ Q.real (A j) ≤ 4 / m)
    have hQ : ∑ j, Q.real (A j) ≤ 1 := by
      rw [← measureReal_iUnion_fintype hdisj hA]; exact measureReal_le_one
    have hQB : (B.card : ℝ) * (4 / m) ≤ ∑ j ∈ B, Q.real (A j) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j hj ↦ by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj; exact hj.le
    have hBQ : ∑ j ∈ B, Q.real (A j) ≤ ∑ j, Q.real (A j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ measureReal_nonneg
    have hcard : (B.card : ℝ) ≤ m / 4 := by
      have := hQB.trans (hBQ.trans hQ)
      rw [mul_div_assoc'] at this
      rw [le_div_iff₀ (by norm_num)]
      rw [div_le_one hm0] at this
      linarith
    calc ∑ j ∈ B, (P j).real (A j) ≤ ∑ _j ∈ B, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ measureReal_le_one
      _ = B.card := by simp
      _ ≤ m / 4 := hcard
  have hgood : ∀ j ∈ G, (P j).real (A j) ≤ (K + Real.log 2) / Real.log (m / 4) := by
    intro j hj
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [le_div_iff₀ hlog]
    rcases (measureReal_nonneg (μ := Q) (s := A j)).eq_or_lt with hq | hq
    · have hac := (InformationTheory.klDiv_ne_top_iff.mp (hKL j)).1
      have hQ0 : Q (A j) = 0 := by
        rw [← ofReal_measureReal (measure_ne_top Q _), ← hq, ENNReal.ofReal_zero]
      have hP0 : (P j).real (A j) = 0 := by simp [Measure.real, hac hQ0]
      rw [hP0, zero_mul]; positivity
    have hev := measureReal_mul_neg_log_sub_log_two_le_klDiv (P j) Q (hKL j) (A j) (hA j)
    have hlq : Real.log (m / 4) ≤ -Real.log (Q.real (A j)) := by
      rw [← Real.log_inv]
      apply Real.log_le_log (by positivity)
      rw [le_inv_comm₀ (by positivity) hq, inv_div]; exact hj
    have := mul_le_mul_of_nonneg_left hlq (measureReal_nonneg (μ := P j) (s := A j))
    linarith [hK j]
  have hgoodsum : ∑ j ∈ G, (P j).real (A j) ≤ m * (K + Real.log 2) / Real.log (m / 4) := by
    calc ∑ j ∈ G, (P j).real (A j) ≤ ∑ _j ∈ G, (K + Real.log 2) / Real.log (m / 4) :=
          Finset.sum_le_sum hgood
      _ = G.card * ((K + Real.log 2) / Real.log (m / 4)) := by simp
      _ ≤ m * ((K + Real.log 2) / Real.log (m / 4)) := by
          gcongr
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      _ = _ := by ring
  linarith

/-- The spike `a e_j` in `ℝ^m`. -/
private def blockSpike (a : ℝ) (j : Fin m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j' ↦ if j = j' then a else 0

/-- Distinct spikes of height `a ≥ 0` are at distance at least `a`. -/
private theorem le_dist_blockSpike {a : ℝ} (ha : 0 ≤ a) {j k : Fin m} (hjk : j ≠ k) :
    a ≤ dist (blockSpike a j) (blockSpike a k) := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (blockSpike a j - blockSpike a k) j
  simpa [blockSpike, Ne.symm hjk, abs_of_nonneg ha] using this

/-- The block-`b` coordinates of an estimate computed from raw coordinates `x`. -/
private def blockEstimate (h : s * m ≤ p) (T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (b : Fin s) (x : Fin p → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j ↦ T (WithLp.toLp 2 x) (blockIndex h b j)

/-- The block coordinates of a measurable estimate are measurable. -/
private theorem measurable_blockEstimate (h : s * m ≤ p)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T) (b : Fin s) :
    Measurable (blockEstimate h T b) := by
  have h1 : Measurable fun x : Fin p → ℝ ↦ T (WithLp.toLp 2 x) :=
    hT.comp (PiLp.continuous_toLp 2 _).measurable
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun j ↦
    (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) ↦ z (blockIndex h b j)).comp h1)

/-- The squared error dominates the sum over blocks of the squared block errors. -/
private theorem sum_dist_blockEstimate_sq_le (h : s * m ≤ p) (a : ℝ)
    (T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (J : Fin s → Fin m)
    (x : Fin p → ℝ) :
    ∑ b, dist (blockEstimate h T b x) (blockSpike a (J b)) ^ 2 ≤
      ‖T (WithLp.toLp 2 x) - WithLp.toLp 2 (blockMean h a J)‖ ^ 2 := by
  have hb : ∀ b, dist (blockEstimate h T b x) (blockSpike a (J b)) ^ 2 =
      ∑ j, (T (WithLp.toLp 2 x) (blockIndex h b j) - blockMean h a J (blockIndex h b j)) ^ 2 := by
    intro b
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [blockMean_blockIndex]
    simp only [blockEstimate, blockSpike, Real.dist_eq, sq_abs, eq_comm (a := J b)]
  simp_rw [hb]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hinj : Set.InjOn (fun q : Fin s × Fin m ↦ blockIndex h q.1 q.2)
      (Finset.univ : Finset (Fin s × Fin m)) := by
    intro q _ q' _ hq
    have := (blockIndex_inj h).mp hq
    exact Prod.ext this.1 this.2
  set g : Fin p → ℝ := fun i ↦ (T (WithLp.toLp 2 x) i - blockMean h a J i) ^ 2 with hg
  change ∑ b, ∑ j, g (blockIndex h b j) ≤ ∑ i, g i
  calc ∑ b, ∑ j, g (blockIndex h b j) = ∑ q : Fin s × Fin m, g (blockIndex h q.1 q.2) :=
        (Fintype.sum_prod_type (fun q : Fin s × Fin m ↦ g (blockIndex h q.1 q.2))).symm
    _ = ∑ i ∈ Finset.univ.image (fun q : Fin s × Fin m ↦ blockIndex h q.1 q.2), g i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i, g i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ ↦ sq_nonneg _

/-- The Gaussian product law of the observations under the block hypothesis `J`. -/
private def blockLaw (h : s * m ≤ p) (a σ : ℝ) (J : Fin s → Fin m) : Measure (Fin p → ℝ) :=
  Measure.pi fun i ↦ gaussianReal (blockMean h a J i) (Real.toNNReal (σ ^ 2))

/-- The block hypothesis laws are probability measures. -/
private instance (h : s * m ≤ p) (a σ : ℝ) (J : Fin s → Fin m) :
    IsProbabilityMeasure (blockLaw h a σ J) := by
  unfold blockLaw; infer_instance

/-- The success events of block `b`: the block estimate is within `a / 2` of the spike `a e_j`. -/
private def blockEvent (h : s * m ≤ p) (T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : ℝ) (b : Fin s) (j : Fin m) : Set (Fin p → ℝ) :=
  {x | dist (blockEstimate h T b x) (blockSpike a j) < a / 2}

/-- The block success events of a measurable estimator are measurable. -/
private theorem measurableSet_blockEvent (h : s * m ≤ p)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T) (a : ℝ)
    (b : Fin s) (j : Fin m) : MeasurableSet (blockEvent h T a b j) :=
  measurableSet_lt ((measurable_blockEstimate h hT b).dist measurable_const) measurable_const

/-- The success events of one block are pairwise disjoint, the spikes being `a`-separated. -/
private theorem pairwise_disjoint_blockEvent (h : s * m ≤ p)
    (T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) {a : ℝ} (ha : 0 ≤ a) (b : Fin s) :
    Pairwise (Function.onFun Disjoint (blockEvent h T a b)) := by
  intro j k hjk
  refine Set.disjoint_left.mpr fun x hj hk ↦ ?_
  have h1 : dist (blockEstimate h T b x) (blockSpike a j) < a / 2 := hj
  have h2 : dist (blockEstimate h T b x) (blockSpike a k) < a / 2 := hk
  have := dist_triangle_left (blockSpike a j) (blockSpike a k) (blockEstimate h T b x)
  have := le_dist_blockSpike ha hjk
  linarith

/-- The risk at a block hypothesis dominates `a² / 4` times the expected number of failed
blocks. -/
private theorem ofReal_mul_sum_le_lintegral_blockMean (h : s * m ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (σ : ℝ)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T)
    (J : Fin s → Fin m) :
    ENNReal.ofReal (a ^ 2 / 4 * ∑ b, (blockLaw h a σ J).real (blockEvent h T a b (J b))ᶜ) ≤
      ∫⁻ y, ENNReal.ofReal (‖T y - WithLp.toLp 2 (blockMean h a J)‖ ^ 2)
        ∂sparseGaussianLaw (WithLp.toLp 2 (blockMean h a J)) σ := by
  have hlaw : sparseGaussianLaw (WithLp.toLp 2 (blockMean h a J)) σ =
      (blockLaw h a σ J).map (WithLp.toLp 2) := by
    rw [sparseGaussianLaw_eq_map_pi]; rfl
  have hF : Measurable fun y : EuclideanSpace ℝ (Fin p) ↦
      ENNReal.ofReal (‖T y - WithLp.toLp 2 (blockMean h a J)‖ ^ 2) := by
    fun_prop
  rw [hlaw, lintegral_map hF (by fun_prop)]
  have hpt : ∀ x : Fin p → ℝ, ∑ b, (blockEvent h T a b (J b))ᶜ.indicator
      (fun _ ↦ ENNReal.ofReal (a ^ 2 / 4)) x ≤
      ENNReal.ofReal (‖T (WithLp.toLp 2 x) - WithLp.toLp 2 (blockMean h a J)‖ ^ 2) := by
    intro x
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (sum_dist_blockEstimate_sq_le h a T J x))
    rw [ENNReal.ofReal_sum_of_nonneg fun b _ ↦ sq_nonneg _]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    by_cases hx : x ∈ (blockEvent h T a b (J b))ᶜ
    · rw [Set.indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      have : a / 2 ≤ dist (blockEstimate h T b x) (blockSpike a (J b)) := by
        simpa [blockEvent] using hx
      nlinarith
    · rw [Set.indicator_of_notMem hx]; positivity
  refine le_trans (le_of_eq ?_) (lintegral_mono hpt)
  rw [lintegral_finsetSum _ fun b _ ↦ (measurable_const.indicator
    (measurableSet_blockEvent h hT a b (J b)).compl)]
  simp_rw [lintegral_indicator_const (measurableSet_blockEvent h hT a _ _).compl]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun b _ ↦ by positivity]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal (measure_ne_top _ _)]

/-- Block lower bound: if every block's success probabilities sum to at most `β m`, the minimax
risk over `s`-sparse means is at least `s (1 - β) a² / 4`. -/
private theorem ofReal_le_iSup_lintegral_of_block (h : s * m ≤ p) [NeZero m] {a : ℝ}
    (ha : 0 ≤ a)
    (σ β : ℝ) (hH : ∀ (b : Fin s) (J : Fin s → Fin m) (A : Fin m → Set (Fin p → ℝ)),
      (∀ j, MeasurableSet (A j)) → Pairwise (Function.onFun Disjoint A) →
      ∑ j, (blockLaw h a σ (Function.update J b j)).real (A j) ≤ β * m)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T) :
    ENNReal.ofReal (s * (1 - β) * (a ^ 2 / 4)) ≤
      ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
        ∫⁻ y, ENNReal.ofReal (‖T y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ := by
  obtain ⟨J, hJ⟩ := exists_mul_one_sub_le_sum_measureReal_compl (blockLaw h a σ)
    (blockEvent h T a) (measurableSet_blockEvent h hT a) β fun b J ↦
      hH b J _ (measurableSet_blockEvent h hT a b) (pairwise_disjoint_blockEvent h T ha b)
  refine le_iSup_of_le ⟨WithLp.toLp 2 (blockMean h a J), sparsity_blockMean_le h a J⟩ ?_
  refine le_trans ?_ (ofReal_mul_sum_le_lintegral_blockMean h ha σ hT J)
  apply ENNReal.ofReal_le_ofReal
  have : 0 ≤ a ^ 2 / 4 := by positivity
  nlinarith

/-- Squared mean differences between neighbouring block hypotheses, in units of the
variance, are at most `2 a² / σ²`. -/
private theorem sum_sq_blockMean_sub_div_le (h : s * m ≤ p) {a σ : ℝ} (hσ : 0 < σ)
    (J : Fin s → Fin m)
    (b : Fin s) (j k : Fin m) :
    (∑ i, (blockMean h a (Function.update J b j) i -
      blockMean h a (Function.update J b k) i) ^ 2) / (Real.toNNReal (σ ^ 2) : ℝ) ≤
      2 * a ^ 2 / σ ^ 2 := by
  rw [Real.coe_toNNReal _ (sq_nonneg σ)]
  exact div_le_div_of_nonneg_right (sum_sq_blockMean_update_sub_le h a J b j k) (by positivity)

/-- Small-ratio regime: two spikes per block of height `σ / 2` give the bound `s σ² / 64`. -/
private theorem ofReal_le_iSup_lintegral_two (h : s * 2 ≤ p) {σ : ℝ} (hσ : 0 < σ)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T) :
    ENNReal.ofReal (s * σ ^ 2 / 64) ≤
      ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
        ∫⁻ y, ENNReal.ofReal (‖T y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ := by
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by simp [hσ.ne']
  have key := ofReal_le_iSup_lintegral_of_block h (a := σ / 2) (by positivity) σ (3 / 4) ?_ hT
  · refine le_trans (le_of_eq ?_) key
    congr 1; ring
  intro b J A hA hdisj
  have htv : totalVariationDistance (blockLaw h (σ / 2) σ (Function.update J b 0))
      (blockLaw h (σ / 2) σ (Function.update J b 1)) ≤ 1 / 2 := by
    refine (totalVariationDistance_pi_gaussianReal_le _ _ hv).trans ?_
    rw [Real.sqrt_le_left (by norm_num)]
    have := sum_sq_blockMean_sub_div_le h (a := σ / 2) hσ J b 1 0
    rw [mul_comm (4 : ℝ), ← div_div]
    calc _ ≤ 2 * (σ / 2) ^ 2 / σ ^ 2 / 4 := by gcongr
      _ ≤ (1 / 2) ^ 2 := by field_simp; norm_num
  have := sum_measureReal_le_one_add_totalVariationDistance
    (fun j ↦ blockLaw h (σ / 2) σ (Function.update J b j)) A hA (hdisj (by decide))
  push_cast
  linarith

/-- Large-ratio regime: for `m ≥ 1024`, `m` spikes per block of height
`σ √(log (m / 4) / 8)` give the bound `s σ² log (m / 4) / 64`. -/
private theorem ofReal_le_iSup_lintegral_many (hm : 1024 ≤ m) (h : s * m ≤ p) {σ : ℝ}
    (hσ : 0 < σ)
    {T : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hT : Measurable T) :
    ENNReal.ofReal (s * σ ^ 2 * Real.log ((m : ℝ) / 4) / 64) ≤
      ⨆ θ : {θ : EuclideanSpace ℝ (Fin p) // sparsity θ ≤ s},
        ∫⁻ y, ENNReal.ofReal (‖T y - θ.val‖ ^ 2) ∂sparseGaussianLaw θ.val σ := by
  have : NeZero m := ⟨by omega⟩
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by simp [hσ.ne']
  set L := Real.log ((m : ℝ) / 4) with hL
  have hm4 : (256 : ℝ) ≤ m / 4 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (show 256 * 4 ≤ m by omega)
  have hL8 : 8 * Real.log 2 ≤ L := by
    rw [hL, ← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 < L := by linarith
  set a := σ * Real.sqrt (L / 8) with ha
  have ha2 : a ^ 2 = σ ^ 2 * (L / 8) := by rw [ha, mul_pow, Real.sq_sqrt (by positivity)]
  have key := ofReal_le_iSup_lintegral_of_block h (a := a) (by positivity) σ (1 / 2) ?_ hT
  · refine le_trans (le_of_eq ?_) key
    congr 1; rw [ha2]; ring
  intro b J A hA hdisj
  have hKL : ∀ j, InformationTheory.klDiv (blockLaw h a σ (Function.update J b j))
      (blockLaw h a σ (Function.update J b 0)) =
      ∑ i, ENNReal.ofReal ((blockMean h a (Function.update J b 0) i -
        blockMean h a (Function.update J b j) i) ^ 2 / (2 * (Real.toNNReal (σ ^ 2) : ℝ))) :=
    fun j ↦ klDiv_pi_gaussianReal _ _ hv
  have hfin : ∀ j, InformationTheory.klDiv (blockLaw h a σ (Function.update J b j))
      (blockLaw h a σ (Function.update J b 0)) ≠ ∞ := by
    intro j; rw [hKL]; exact ENNReal.sum_ne_top.mpr fun i _ ↦ ENNReal.ofReal_ne_top
  have hK : ∀ j, (InformationTheory.klDiv (blockLaw h a σ (Function.update J b j))
      (blockLaw h a σ (Function.update J b 0))).toReal ≤ L / 8 := by
    intro j
    rw [hKL, ENNReal.toReal_sum fun i _ ↦ ENNReal.ofReal_ne_top]
    rw [Finset.sum_congr rfl fun i _ ↦ ENNReal.toReal_ofReal (by positivity), ← Finset.sum_div,
      mul_comm (2 : ℝ), ← div_div]
    have := sum_sq_blockMean_sub_div_le h (a := a) hσ J b 0 j
    calc _ ≤ 2 * a ^ 2 / σ ^ 2 / 2 := by gcongr
      _ = L / 8 := by rw [ha2]; field_simp
  have hF := sum_measureReal_le_of_klDiv_le (by omega)
    (fun j ↦ blockLaw h a σ (Function.update J b j)) (blockLaw h a σ (Function.update J b 0))
    (L / 8) hfin hK A hA hdisj
  refine hF.trans ?_
  rw [← hL]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have : (L / 8 + Real.log 2) / L ≤ 1 / 4 := by
    rw [div_le_iff₀ hL0]; linarith
  calc (m : ℝ) / 4 + m * (L / 8 + Real.log 2) / L = m / 4 + m * ((L / 8 + Real.log 2) / L) := by
        ring
    _ ≤ m / 4 + m * (1 / 4) := by gcongr
    _ = 1 / 2 * m := by ring

/-- Soft thresholding at level `λ`: `y ↦ y - max (-λ) (min λ y)`, which is `sign y (|y| - λ)₊`
for `λ ≥ 0`. -/
def softThreshold (l y : ℝ) : ℝ := y - max (-l) (min l y)

/-- Soft thresholding is continuous. -/
theorem continuous_softThreshold (l : ℝ) : Continuous (softThreshold l) := by
  unfold softThreshold; fun_prop

/-- Soft thresholding at level `λ ≥ 0` moves each point by at most `λ`. -/
theorem abs_softThreshold_sub_le {l : ℝ} (hl : 0 ≤ l) (y : ℝ) : |softThreshold l y - y| ≤ l := by
  unfold softThreshold
  rw [sub_sub_cancel_left, abs_neg, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Soft thresholding at level `λ ≥ 0` satisfies `|η_λ(y)| ≤ (|y| - λ)₊`. -/
theorem abs_softThreshold_le {l : ℝ} (hl : 0 ≤ l) (y : ℝ) :
    |softThreshold l y| ≤ max (|y| - l) 0 := by
  unfold softThreshold
  rcases le_total l y with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact le_max_left _ _
  rcases le_total y (-l) with h' | h'
  · rw [min_eq_right h, max_eq_left h', abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    exact le_max_of_le_left (by linarith)
  · rw [min_eq_right h, max_eq_right h', sub_self, abs_zero]
    exact le_max_right _ _

/-- Risk of soft thresholding at a nonzero mean. -/
theorem lintegral_softThreshold_sub_sq_le {l : ℝ} (hl : 0 ≤ l) (μ : ℝ) (v : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal ((softThreshold l y - μ) ^ 2) ∂gaussianReal μ v ≤
      ENNReal.ofReal (2 * l ^ 2 + 2 * v) := by
  have hpt : ∀ y, (softThreshold l y - μ) ^ 2 ≤ 2 * l ^ 2 + 2 * (y - μ) ^ 2 := by
    intro y
    have h1 := abs_softThreshold_sub_le hl y
    have h2 : (softThreshold l y - y) ^ 2 ≤ l ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (softThreshold l y - y - (y - μ))]
  have hsq : Integrable (fun y ↦ (y - μ) ^ 2) (gaussianReal μ v) :=
    ((memLp_id_gaussianReal (μ := μ) (v := v) 2).sub (memLp_const μ)).integrable_sq
  have hint : Integrable (fun y ↦ 2 * l ^ 2 + 2 * (y - μ) ^ 2) (gaussianReal μ v) :=
    (integrable_const _).add (hsq.const_mul 2)
  calc ∫⁻ y, ENNReal.ofReal ((softThreshold l y - μ) ^ 2) ∂gaussianReal μ v
      ≤ ∫⁻ y, ENNReal.ofReal (2 * l ^ 2 + 2 * (y - μ) ^ 2) ∂gaussianReal μ v :=
        lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal (2 * l ^ 2 + 2 * v) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y ↦ by positivity),
          integral_add (integrable_const _) (hsq.const_mul 2)]
        have hv := variance_fun_id_gaussianReal (μ := μ) (v := v)
        rw [variance_eq_integral (X := fun x : ℝ ↦ x) aemeasurable_id'] at hv
        simp only [integral_id_gaussianReal] at hv
        rw [integral_const_mul (2 : ℝ) (fun a ↦ (a - μ) ^ 2), hv]; simp

/-- Risk of soft thresholding at the level `t σ` at a zero mean: `≤ 4 σ² e^{1/2 - t²/2}`. -/
theorem lintegral_softThreshold_sq_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    ∫⁻ y, ENNReal.ofReal (softThreshold (t * σ) y ^ 2) ∂gaussianReal 0 (Real.toNNReal (σ ^ 2)) ≤
      ENNReal.ofReal (4 * σ ^ 2 * Real.exp (1 / 2 - t ^ 2 / 2)) := by
  set c := (1 + t) / σ with hc
  set K := 2 * σ ^ 2 * Real.exp (-((1 + t) * t)) with hK
  have hpt : ∀ y, softThreshold (t * σ) y ^ 2 ≤
      K * (Real.exp (c * y) + Real.exp ((-c) * y)) := by
    intro y
    have h0 := abs_softThreshold_le (by positivity : 0 ≤ t * σ) y
    have hKpos : 0 ≤ K := by positivity
    rcases le_total (|y| - t * σ) 0 with hy | hy
    · rw [max_eq_right hy] at h0
      have : softThreshold (t * σ) y = 0 := abs_nonpos_iff.mp h0
      rw [this, sq, zero_mul]; positivity
    rw [max_eq_left hy] at h0
    set u := (|y| - t * σ) / σ with hu
    have hu0 : 0 ≤ u := div_nonneg hy hσ.le
    have hyu : |y| - t * σ = σ * u := by rw [hu]; field_simp
    have hsq : softThreshold (t * σ) y ^ 2 ≤ σ ^ 2 * u ^ 2 := by
      rw [← sq_abs, ← mul_pow, ← hyu]
      exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have hq := Real.quadratic_le_exp_of_nonneg hu0
    have hexp : Real.exp u ≤ Real.exp ((1 + t) * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsplit : (1 + t) * u = -((1 + t) * t) + c * |y| := by
      rw [hu, hc]; field_simp; ring
    have habs : Real.exp (c * |y|) ≤ Real.exp (c * y) + Real.exp ((-c) * y) := by
      rcases le_total 0 y with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos ((-c) * y)]
      · rw [abs_of_nonpos h]; rw [show c * -y = -c * y by ring]
        linarith [Real.exp_pos (c * y)]
    calc softThreshold (t * σ) y ^ 2 ≤ σ ^ 2 * u ^ 2 := hsq
      _ ≤ 2 * σ ^ 2 * Real.exp ((1 + t) * u) := by nlinarith [sq_nonneg σ]
      _ = K * Real.exp (c * |y|) := by rw [hsplit, Real.exp_add, hK]; ring
      _ ≤ K * (Real.exp (c * y) + Real.exp ((-c) * y)) := by gcongr
  have hint : Integrable (fun y ↦ K * (Real.exp (c * y) + Real.exp ((-c) * y)))
      (gaussianReal 0 (Real.toNNReal (σ ^ 2))) :=
    ((integrable_exp_mul_gaussianReal c).add (integrable_exp_mul_gaussianReal (-c))).const_mul K
  have hmgf : ∀ r : ℝ, ∫ y, Real.exp (r * y) ∂gaussianReal 0 (Real.toNNReal (σ ^ 2)) =
      Real.exp (σ ^ 2 * r ^ 2 / 2) := by
    intro r
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := Real.toNNReal (σ ^ 2))) r
    simp only [mgf, id, zero_mul, zero_add] at this
    rw [this, Real.coe_toNNReal _ (sq_nonneg σ)]
  calc ∫⁻ y, ENNReal.ofReal (softThreshold (t * σ) y ^ 2) ∂gaussianReal 0 (Real.toNNReal (σ ^ 2))
      ≤ ∫⁻ y, ENNReal.ofReal (K * (Real.exp (c * y) + Real.exp ((-c) * y)))
          ∂gaussianReal 0 (Real.toNNReal (σ ^ 2)) :=
        lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal (4 * σ ^ 2 * Real.exp (1 / 2 - t ^ 2 / 2)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y ↦ by positivity),
          integral_const_mul, integral_add (integrable_exp_mul_gaussianReal c)
            (integrable_exp_mul_gaussianReal (-c)), hmgf, hmgf]
        congr 1
        rw [hK, hc, neg_sq, div_pow, ← two_mul]
        have : σ ^ 2 * ((1 + t) ^ 2 / σ ^ 2) / 2 = (1 + t) ^ 2 / 2 := by field_simp
        rw [this, show (4 : ℝ) * σ ^ 2 * Real.exp (1 / 2 - t ^ 2 / 2) =
          2 * σ ^ 2 * 2 * (Real.exp (-((1 + t) * t)) * Real.exp ((1 + t) ^ 2 / 2)) by
            rw [← Real.exp_add]; ring_nf]
        ring

/-- The numerical bound `e^{1/2} ≤ 7 / 4`. -/
private theorem exp_one_half_le : Real.exp (1 / 2) ≤ 7 / 4 := by
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

/-- Soft thresholding at `σ √(2 log (p / s))` has risk at most `17 σ² s log (p / s)` at every
`s`-sparse mean. -/
private theorem lintegral_softThreshold_risk_le {p s : ℕ} (hs : 1 ≤ s) (hsp : 2 * s ≤ p)
    {σ : ℝ}
    (hσ : 0 < σ) (θ : EuclideanSpace ℝ (Fin p)) (hθ : sparsity θ ≤ s) :
    ∫⁻ y, ENNReal.ofReal (‖WithLp.toLp 2 (fun i ↦ softThreshold
        (Real.sqrt (2 * Real.log ((p : ℝ) / s)) * σ) (y i)) - θ‖ ^ 2) ∂sparseGaussianLaw θ σ ≤
      ENNReal.ofReal (17 * σ ^ 2 * s * Real.log ((p : ℝ) / s)) := by
  set L := Real.log ((p : ℝ) / s) with hL
  set t := Real.sqrt (2 * L) with ht
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hps : (2 : ℝ) ≤ p / s := by
    rw [le_div_iff₀ hs0]; exact_mod_cast (by omega : 2 * s ≤ p)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hps
  have hlog2 := Real.log_two_gt_d9
  have hL0 : 0 ≤ L := by linarith
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
  set l := t * σ with hl
  have hl0 : 0 ≤ l := by positivity
  set B0 := 4 * σ ^ 2 * Real.exp (1 / 2 - t ^ 2 / 2) with hB0
  set B1 := 2 * l ^ 2 + 2 * σ ^ 2 with hB1
  have hS : (σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sq_nonneg σ)
  -- coordinatewise risks
  have hcoord : ∀ i, ∫⁻ y, ENNReal.ofReal ((softThreshold l (y i) - θ i) ^ 2)
      ∂sparseGaussianLaw θ σ ≤ ENNReal.ofReal (if θ i = 0 then B0 else B1) := by
    intro i
    have hmp := measurePreserving_eval_multivariateGaussian (μ := θ) hS (i := i)
    have hii : ((σ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) i i).toNNReal = Real.toNNReal (σ ^ 2) := by
      simp
    rw [hii] at hmp
    have hmeas : Measurable fun x : ℝ ↦ ENNReal.ofReal ((softThreshold l x - θ i) ^ 2) :=
      ENNReal.measurable_ofReal.comp
        (((continuous_softThreshold l).sub continuous_const).pow 2).measurable
    rw [sparseGaussianLaw, hmp.lintegral_comp hmeas]
    split_ifs with h0
    · rw [h0]
      simp only [sub_zero]
      exact lintegral_softThreshold_sq_le hσ ht0
    · refine (lintegral_softThreshold_sub_sq_le hl0 (θ i) _).trans ?_
      rw [Real.coe_toNNReal _ (sq_nonneg σ)]
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin p),
      ENNReal.ofReal (‖WithLp.toLp 2 (fun i ↦ softThreshold l (y i)) - θ‖ ^ 2) =
        ∑ i, ENNReal.ofReal ((softThreshold l (y i) - θ i) ^ 2) := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
    simp
  simp_rw [hnorm]
  rw [lintegral_finsetSum _ fun i _ ↦ by
    have : Continuous fun y : EuclideanSpace ℝ (Fin p) ↦ (softThreshold l (y i) - θ i) ^ 2 := by
      have := continuous_softThreshold l; fun_prop
    exact ENNReal.measurable_ofReal.comp this.measurable]
  refine (Finset.sum_le_sum fun i _ ↦ hcoord i).trans ?_
  have hB0n : 0 ≤ B0 := by positivity
  have hB1n : 0 ≤ B1 := by positivity
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by split_ifs <;> assumption]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hc0 : ((Finset.univ.filter fun i ↦ θ i = 0).card : ℝ) ≤ p := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hc1 : ((Finset.univ.filter fun i ↦ ¬ θ i = 0).card : ℝ) ≤ s := by
    exact_mod_cast hθ
  have hexp : Real.exp (1 / 2 - t ^ 2 / 2) ≤ 7 / 4 * (s / p) := by
    rw [ht2, show 1 / 2 - 2 * L / 2 = 1 / 2 + (-L) by ring, Real.exp_add, hL, Real.exp_neg,
      Real.exp_log (by positivity), inv_div]
    exact mul_le_mul_of_nonneg_right exp_one_half_le (by positivity)
  have hB0p : (p : ℝ) * B0 ≤ 7 * σ ^ 2 * s := by
    calc (p : ℝ) * B0 ≤ p * (4 * σ ^ 2 * (7 / 4 * (s / p))) := by
          rw [hB0]; gcongr
      _ = 7 * σ ^ 2 * s := by field_simp
  have hB1v : B1 = σ ^ 2 * (4 * L + 2) := by rw [hB1, hl, mul_pow, ht2]; ring
  calc _ ≤ (p : ℝ) * B0 + s * B1 := by gcongr
    _ ≤ 7 * σ ^ 2 * s + s * (σ ^ 2 * (4 * L + 2)) := by rw [hB1v]; gcongr
    _ ≤ 17 * σ ^ 2 * s * L := by nlinarith [mul_pos (pow_pos hσ 2) hs0]

/-- GAPS 103.33: the sparse minimax rate. There are universal constants `0 < c ≤ C` such that
for `1 ≤ s` and `2 s ≤ p` the minimax squared risk over `s`-sparse means in `N(θ, σ² I_p)` lies
between `c σ² s log(p / s)` and `C σ² s log(p / s)`. -/
theorem sparseGaussianMinimaxRisk_bounds :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p s : ℕ, 1 ≤ s → 2 * s ≤ p → ∀ σ : ℝ, 0 < σ →
      ENNReal.ofReal (c * σ ^ 2 * s * Real.log ((p : ℝ) / s)) ≤ sparseGaussianMinimaxRisk p s σ ∧
      sparseGaussianMinimaxRisk p s σ ≤
        ENNReal.ofReal (C * σ ^ 2 * s * Real.log ((p : ℝ) / s)) := by
  refine ⟨1 / 512, by norm_num, 17, by norm_num, fun p s hs hsp σ hσ ↦ ⟨?_, ?_⟩⟩
  · refine le_iInf fun T ↦ ?_
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hlog2 := Real.log_two_lt_d9
    have hlog2' := Real.log_two_gt_d9
    -- `p / s < m + 1 ≤ 2 m` for `m = ⌊p / s⌋ ≥ 2`
    set m := p / s with hm
    have hdiv : s * m + p % s = p := Nat.div_add_mod p s
    have hmod := Nat.mod_lt p (show 0 < s by omega)
    have hm2 : 2 ≤ m := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
    have hlt : (p : ℝ) / s ≤ 2 * m := by
      rw [div_le_iff₀ hs0]
      have : p ≤ s * m + s := by omega
      have : (p : ℝ) ≤ s * m + s := by exact_mod_cast this
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith
    have hps : (0 : ℝ) < p / s := by
      have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      positivity
    have hlogle : Real.log ((p : ℝ) / s) ≤ Real.log (2 * m) := Real.log_le_log hps hlt
    rcases le_or_gt 1024 m with hbig | hsmall
    · refine le_trans ?_ (ofReal_le_iSup_lintegral_many hbig (Nat.mul_div_le p s) hσ T.2)
      apply ENNReal.ofReal_le_ofReal
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have h2m : Real.log (2 * m) = Real.log 8 + Real.log ((m : ℝ) / 4) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have hm4 : (256 : ℝ) ≤ m / 4 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (show 256 * 4 ≤ m by omega)
      have hL8 : 8 * Real.log 2 ≤ Real.log ((m : ℝ) / 4) := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_le_log (by positivity) (by norm_num; linarith)
      have hσ2 : 0 < σ ^ 2 * s := by positivity
      nlinarith
    · refine le_trans ?_ (ofReal_le_iSup_lintegral_two (by omega) hσ T.2)
      apply ENNReal.ofReal_le_ofReal
      have hm' : (2 * m : ℝ) ≤ 2 ^ 11 := by
        have : (m : ℝ) ≤ 1024 := by exact_mod_cast hsmall.le
        linarith
      have h11 : Real.log (2 * m) ≤ 11 * Real.log 2 := by
        have h := Real.log_pow (2 : ℝ) 11
        push_cast at h
        rw [← h]
        exact Real.log_le_log (by positivity) (by norm_num at hm' ⊢; linarith)
      have hσ2 : 0 < σ ^ 2 * s := by positivity
      nlinarith
  · have hTm : Measurable fun y : EuclideanSpace ℝ (Fin p) ↦ WithLp.toLp 2 (fun i ↦
        softThreshold (Real.sqrt (2 * Real.log ((p : ℝ) / s)) * σ) (y i)) :=
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦
        (continuous_softThreshold _).comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)).measurable
    unfold sparseGaussianMinimaxRisk
    refine iInf_le_of_le ⟨_, hTm⟩ (iSup_le fun θ ↦ ?_)
    exact lintegral_softThreshold_risk_le hs hsp hσ θ.val θ.2

end SparseMinimax

/-- Any sequence has zero squared error against itself, including nonsummable sequences. -/
@[simp] theorem sequenceSquaredError_self (θ : ℕ → ℝ) : sequenceSquaredError θ θ = 0 := by
  simp [sequenceSquaredError]

/-- A zero bandwidth gives the unweighted mean when the kernel is nonzero at the origin. -/
theorem nadarayaWatson_zero_bandwidth {d n : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : K 0 ≠ 0) (x : Fin n → EuclideanSpace ℝ (Fin d)) (y : Fin n → ℝ)
    (t : EuclideanSpace ℝ (Fin d)) :
    nadarayaWatson K 0 x y t = (∑ i, y i) / n := by
  simp only [nadarayaWatson, inv_zero, zero_smul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end CKSD
