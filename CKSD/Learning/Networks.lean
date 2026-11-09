module

public import CKSD.Learning.Algorithms
public import CKSD.Learning.Generalization.Contraction
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Dense networks: estimation, capacity, depth, and wide limits

Dense networks are parameterized by a width function `w : ℕ → ℕ` with input width `w 0`, a
number `H` of hidden layers, weight matrices `W ℓ : w (ℓ+1) × w ℓ` and bias vectors `b ℓ` for
`ℓ < H`, and an affine scalar output read from the last hidden layer. Hidden activations are
`a₀ = x` and `a_{ℓ+1} = σ(W ℓ aℓ + b ℓ)` coordinatewise; the output is `v ⬝ a_H + c`. Coordinates
of `w` beyond `H` are unused. Depth (number of affine maps) is `H + 1`.

Hölder classes are stated for smoothness indices in `(0,1]`, where the Hölder ball is the set of
functions with `sup |g| + sup_{x ≠ y} |g x - g y| / ‖x - y‖_∞^β ≤ K`; no derivatives occur.
Vectors in `Fin d → ℝ` carry the sup norm. Gaussian laws are Mathlib's `gaussianReal` and
`multivariateGaussian`; convergence in distribution is Mathlib's `TendstoInDistribution`.

## Main definitions

* `CKSD.DenseNetParams`, `CKSD.denseActivation`, `CKSD.denseNetOutput`: dense networks.
* `CKSD.IsInHolderBall`, `CKSD.compositionalHolderClass`: Hölder balls and the compositional
  Hölder class of Schmidt-Hieber.

## Main results

* `CKSD.card_le_of_shatters_denseSignClass`: VC dimension of network sign classes (GAPS 107.35).
* `CKSD.empiricalRademacherComplexity_biasFree_le`: norm-based capacity (GAPS 107.35).
* `CKSD.relu_depth_lower_bound`, `CKSD.relu_eldan_shamir_separation`: depth lower bounds and
  depth separation (GAPS 107.37).
* `CKSD.compositionalHolder_minimax_lower_bound`: the minimax lower bound (GAPS 107.29).
* `CKSD.tendstoInDistribution_wide_network_gaussian`: the Gaussian-process limit
  (GAPS 107.39).

Sources: GAPS 107.29, 107.35, 107.37, and 107.39.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Parameters of a dense network with hidden widths `w 1, …, w H` and scalar output. -/
structure DenseNetParams (w : ℕ → ℕ) (H : ℕ) where
  /-- Hidden weight matrices. -/
  weight : ∀ ℓ : ℕ, Matrix (Fin (w (ℓ + 1))) (Fin (w ℓ)) ℝ
  /-- Hidden bias vectors. -/
  bias : ∀ ℓ : ℕ, Fin (w (ℓ + 1)) → ℝ
  /-- Output weights on the last hidden layer. -/
  outWeight : Fin (w H) → ℝ
  /-- Output bias. -/
  outBias : ℝ

/-- Hidden activations of a dense network. -/
def denseActivation {w : ℕ → ℕ} {H : ℕ} (σ : ℝ → ℝ) (θ : DenseNetParams w H)
    (x : Fin (w 0) → ℝ) : ∀ ℓ : ℕ, Fin (w ℓ) → ℝ
  | 0 => x
  | ℓ + 1 => fun j ↦ σ ((θ.weight ℓ *ᵥ denseActivation σ θ x ℓ) j + θ.bias ℓ j)

/-- Scalar output of a dense network. -/
def denseNetOutput {w : ℕ → ℕ} {H : ℕ} (σ : ℝ → ℝ) (θ : DenseNetParams w H)
    (x : Fin (w 0) → ℝ) : ℝ :=
  θ.outWeight ⬝ᵥ denseActivation σ θ x H + θ.outBias

/-- Number of scalar parameters of the architecture, including biases. -/
def denseParamCount (w : ℕ → ℕ) (H : ℕ) : ℕ :=
  (∑ ℓ ∈ Finset.range H, (w ℓ * w (ℓ + 1) + w (ℓ + 1))) + w H + 1

/-- Number of hidden neurons of the architecture. -/
def denseHiddenNeurons (w : ℕ → ℕ) (H : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range H, w (ℓ + 1)

/-- A real activation is piecewise polynomial: on each of the finitely many half-open pieces
cut out by a finite set of breakpoints it agrees with a polynomial. -/
def IsPiecewisePolynomial (σ : ℝ → ℝ) : Prop :=
  ∃ (s : Finset ℝ) (p : ℕ → Polynomial ℝ), ∀ x, σ x = (p (s.filter (· ≤ x)).card).eval x

/-- A class of Boolean functions shatters a finite set if it realizes every labelling of it. -/
def BooleanClassShatters {X : Type*} (F : Set (X → Bool)) (S : Finset X) : Prop :=
  ∀ lab : X → Bool, ∃ f ∈ F, ∀ x ∈ S, f x = lab x

/-- GAPS 107.35, VC dimension of network sign classifiers: for a fixed piecewise-polynomial
activation there is `c` such that every finite set shattered by the sign classifiers of one
dense architecture with `P ≥ 2` parameters and depth `L = H + 1` has at most
`c (P L log P + P L²)` points. Architectures are layered and fully connected. -/
theorem card_le_of_shatters_denseSignClass (σ : ℝ → ℝ) (hσ : IsPiecewisePolynomial σ) :
    ∃ c > (0 : ℝ), ∀ (w : ℕ → ℕ) (H : ℕ), 2 ≤ denseParamCount w H →
      ∀ S : Finset (Fin (w 0) → ℝ),
      BooleanClassShatters (range fun θ : DenseNetParams w H ↦
        fun x ↦ decide (0 ≤ denseNetOutput σ θ x)) S →
      let P : ℝ := denseParamCount w H
      let L : ℝ := H + 1
      (S.card : ℝ) ≤ c * (P * L * Real.log P + P * L ^ 2) := by
  sorry

section Rademacher

variable {w : ℕ → ℕ} {H : ℕ}

/-- The sign `±1` of a Boolean. -/
private def sgnR {n : ℕ} (s : Fin n → Bool) (i : Fin n) : ℝ := if s i then 1 else -1

/-- Hidden activations as Euclidean vectors. -/
private def actE (σ : ℝ → ℝ) (θ : DenseNetParams w H) (y : Fin (w 0) → ℝ) (ℓ : ℕ) :
    EuclideanSpace ℝ (Fin (w ℓ)) :=
  WithLp.toLp 2 (denseActivation σ θ y ℓ)

/-- A `1`-Lipschitz positively homogeneous activation vanishes at `0` and is bounded by the
absolute value. -/
private theorem abs_le_of_lipschitz_hom {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) (z : ℝ) : |σ z| ≤ |z| := by
  have h0 : σ 0 = 0 := by simpa using hhom 0 le_rfl 0
  have := hσ.dist_le_mul z 0
  simpa [Real.dist_eq, h0] using this

/-- One bias-free layer with Frobenius norm at most `C` multiplies Euclidean norms by at most
`C`. -/
private theorem norm_actE_succ_le {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C)
    (θ : DenseNetParams w H) (ℓ : ℕ) (hb : θ.bias ℓ = 0)
    (hW : ∑ i, ∑ j, θ.weight ℓ i j ^ 2 ≤ C ^ 2) (y : Fin (w 0) → ℝ) :
    ‖actE σ θ y (ℓ + 1)‖ ≤ C * ‖actE σ θ y ℓ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp only [actE, PiLp.toLp_apply, denseActivation, hb, Pi.zero_apply, add_zero]
  calc ∑ i, σ ((θ.weight ℓ *ᵥ denseActivation σ θ y ℓ) i) ^ 2
      ≤ ∑ i, ((θ.weight ℓ *ᵥ denseActivation σ θ y ℓ) i) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ sq_le_sq.mpr (abs_le_of_lipschitz_hom hσ hhom _)
    _ ≤ ∑ i, (∑ j, θ.weight ℓ i j ^ 2) * ∑ j, denseActivation σ θ y ℓ j ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [Matrix.mulVec, dotProduct]; exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ j, θ.weight ℓ i j ^ 2) * ∑ j, denseActivation σ θ y ℓ j ^ 2 :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ C ^ 2 * ∑ j, denseActivation σ θ y ℓ j ^ 2 :=
        mul_le_mul_of_nonneg_right hW (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)


/-- The bias-free parameter set with Frobenius-norm constraints of the capacity bound. -/
private def biasFreeSet (w : ℕ → ℕ) (H : ℕ) (C : ℝ) : Set (DenseNetParams w H) :=
  {θ | (∀ ℓ, θ.bias ℓ = 0) ∧ θ.outBias = 0 ∧
    (∀ ℓ < H, ∑ i, ∑ j, θ.weight ℓ i j ^ 2 ≤ C ^ 2) ∧ ∑ j, θ.outWeight j ^ 2 ≤ C ^ 2}

/-- The zero network lies in the bias-free parameter set. -/
private theorem zero_mem_biasFreeSet {C : ℝ} :
    (⟨fun _ ↦ 0, fun _ ↦ 0, 0, 0⟩ : DenseNetParams w H) ∈ biasFreeSet w H C := by
  refine ⟨fun _ ↦ rfl, rfl, fun ℓ _ ↦ ?_, ?_⟩ <;> simp [sq_nonneg]

/-- Hidden activations of a constrained network grow by at most `C` per layer. -/
private theorem norm_actE_le {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C)
    {θ : DenseNetParams w H} (hθ : θ ∈ biasFreeSet w H C) (y : Fin (w 0) → ℝ) :
    ∀ ℓ ≤ H, ‖actE σ θ y ℓ‖ ≤ C ^ ℓ * ‖actE σ θ y 0‖ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    calc ‖actE σ θ y (ℓ + 1)‖ ≤ C * ‖actE σ θ y ℓ‖ :=
          norm_actE_succ_le hσ hhom hC θ ℓ (hθ.1 ℓ) (hθ.2.2.1 ℓ (by omega)) y
      _ ≤ C * (C ^ ℓ * ‖actE σ θ y 0‖) := mul_le_mul_of_nonneg_left (ih (by omega)) hC
      _ = C ^ (ℓ + 1) * ‖actE σ θ y 0‖ := by ring

/-- Signed sum of the hidden activations at layer `ℓ` over the sample. -/
private def sumAct (σ : ℝ → ℝ) {n : ℕ} (x : Fin n → Fin (w 0) → ℝ) (ℓ : ℕ)
    (θ : DenseNetParams w H) (s : Fin n → Bool) : EuclideanSpace ℝ (Fin (w ℓ)) :=
  ∑ i, sgnR s i • actE σ θ (x i) ℓ

/-- Supremum over the constrained networks of the norm of the signed activation sum. -/
private def layerSup (σ : ℝ → ℝ) {n : ℕ} (x : Fin n → Fin (w 0) → ℝ) (C : ℝ) (ℓ : ℕ)
    (s : Fin n → Bool) : ℝ :=
  sSup ((fun θ ↦ ‖sumAct (H := H) σ x ℓ θ s‖) '' biasFreeSet w H C)

/-- Signs have absolute value one. -/
private theorem abs_sgnR {n : ℕ} (s : Fin n → Bool) (i : Fin n) : |sgnR s i| = 1 := by
  unfold sgnR; split_ifs <;> simp

/-- The norms of the signed activation sums are bounded over the constrained networks. -/
private theorem bddAbove_layerSup {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (x : Fin n → Fin (w 0) → ℝ) {ℓ : ℕ} (hℓ : ℓ ≤ H) (s : Fin n → Bool) :
    BddAbove ((fun θ ↦ ‖sumAct (H := H) σ x ℓ θ s‖) '' biasFreeSet w H C) := by
  refine ⟨∑ i, C ^ ℓ * ‖actE σ (⟨fun _ ↦ 0, fun _ ↦ 0, 0, 0⟩ : DenseNetParams w H) (x i) 0‖, ?_⟩
  rintro _ ⟨θ, hθ, rfl⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_sgnR, one_mul]
  exact (norm_actE_le hσ hhom hC hθ (x i) ℓ hℓ).trans_eq rfl

/-- Each constrained network is dominated by the layer supremum. -/
private theorem le_layerSup {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (x : Fin n → Fin (w 0) → ℝ) {ℓ : ℕ} (hℓ : ℓ ≤ H) (s : Fin n → Bool)
    {θ : DenseNetParams w H} (hθ : θ ∈ biasFreeSet w H C) :
    ‖sumAct σ x ℓ θ s‖ ≤ layerSup (H := H) σ x C ℓ s :=
  le_csSup (bddAbove_layerSup hσ hhom hC x hℓ s) ⟨θ, hθ, rfl⟩

/-- Layer suprema are nonnegative. -/
private theorem layerSup_nonneg {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (x : Fin n → Fin (w 0) → ℝ) {ℓ : ℕ} (hℓ : ℓ ≤ H) (s : Fin n → Bool) :
    0 ≤ layerSup (H := H) σ x C ℓ s :=
  (norm_nonneg _).trans (le_layerSup hσ hhom hC x hℓ s zero_mem_biasFreeSet)


/-- Coordinates of the signed activation sum. -/
private theorem sumAct_apply (σ : ℝ → ℝ) {n : ℕ} (x : Fin n → Fin (w 0) → ℝ) (ℓ : ℕ)
    (θ : DenseNetParams w H) (s : Fin n → Bool) (k : Fin (w ℓ)) :
    sumAct σ x ℓ θ s k = ∑ i, sgnR s i * denseActivation σ θ (x i) ℓ k := by
  simp [sumAct, actE]

/-- The Euclidean norm of the signed activation sum in coordinates. -/
private theorem norm_sumAct (σ : ℝ → ℝ) {n : ℕ} (x : Fin n → Fin (w 0) → ℝ) (ℓ : ℕ)
    (θ : DenseNetParams w H) (s : Fin n → Bool) :
    ‖sumAct σ x ℓ θ s‖ = Real.sqrt (∑ k, (∑ i, sgnR s i * denseActivation σ θ (x i) ℓ k) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp_rw [sumAct_apply, Real.norm_eq_abs, sq_abs]

/-- Cauchy–Schwarz against a vector of Euclidean norm at most one. -/
private theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) (hu : ∑ k, u k ^ 2 ≤ 1) :
    ∑ k, u k * v k ≤ Real.sqrt (∑ k, v k ^ 2) := by
  have hv : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc ∑ k, u k * v k ≤ |∑ k, u k * v k| := le_abs_self _
    _ = Real.sqrt ((∑ k, u k * v k) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ k, u k ^ 2) * ∑ k, v k ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ ≤ Real.sqrt (1 * ∑ k, v k ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hu hv)
    _ = Real.sqrt (∑ k, v k ^ 2) := by rw [one_mul]

/-- A real row normalized by its Euclidean norm (zero rows stay zero). -/
private def unitRow {κ : Type*} [Fintype κ] (a : κ → ℝ) (k : κ) : ℝ :=
  a k / Real.sqrt (∑ k, a k ^ 2)

/-- A normalized row has Euclidean norm at most one. -/
private theorem sum_unitRow_sq_le {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    ∑ k, unitRow a k ^ 2 ≤ 1 := by
  unfold unitRow
  simp_rw [div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  exact div_self_le_one _

/-- A row acts as its Euclidean norm times its normalized row. -/
private theorem sum_mul_eq_sqrt_mul_unitRow {κ : Type*} [Fintype κ] (a h : κ → ℝ) :
    ∑ k, a k * h k = Real.sqrt (∑ k, a k ^ 2) * ∑ k, unitRow a k * h k := by
  unfold unitRow
  by_cases h0 : Real.sqrt (∑ k, a k ^ 2) = 0
  · have hz : ∀ k, a k = 0 := by
      intro k
      rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h0
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h0 k
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    simp [hz]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    field_simp

/-- Suprema of a finite range commute with division by a positive constant. -/
private theorem sSup_range_div {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) {c : ℝ}
    (hc : 0 < c) : sSup (range fun h ↦ f h / c) = sSup (range f) / c := by
  apply le_antisymm
  · refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    exact div_le_div_of_nonneg_right (le_csSup (finite_range f).bddAbove ⟨h, rfl⟩) hc.le
  · rw [div_le_iff₀ hc]
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    rw [← div_le_iff₀ hc]
    exact le_csSup (finite_range (fun h ↦ f h / c)).bddAbove ⟨h, rfl⟩


/-- Peeling one layer: the summed layer suprema grow by at most `2C` per bias-free layer. This
combines the Frobenius bound on a layer, the symmetrization of absolute values, and the
Ledoux–Talagrand contraction inequality for finite classes, applied to a finite family of
near-maximizers. -/
private theorem sum_layerSup_succ_le {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (hn : 0 < n) (x : Fin n → Fin (w 0) → ℝ) {ℓ : ℕ} (hℓ : ℓ < H) :
    ∑ s, layerSup (H := H) σ x C (ℓ + 1) s ≤ 2 * C * ∑ s, layerSup (H := H) σ x C ℓ s := by
  have hσ0 : σ 0 = 0 := by simpa using hhom 0 le_rfl 0
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ : ℝ := ε / 2 ^ n
  have hδ : 0 < δ := by positivity
  have hchoose : ∀ s, ∃ θ ∈ biasFreeSet w H C,
      layerSup (H := H) σ x C (ℓ + 1) s - δ < ‖sumAct σ x (ℓ + 1) θ s‖ := by
    intro s
    obtain ⟨_, ⟨θ, hθ, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
      (Set.Nonempty.image _ ⟨_, zero_mem_biasFreeSet⟩) (sub_lt_self _ hδ)
    exact ⟨θ, hθ, hlt⟩
  choose θs hθs hlt using hchoose
  let t : Option ((Fin n → Bool) × Fin (w (ℓ + 1))) → Fin n → ℝ := fun h i ↦
    h.elim 0 fun p ↦ ∑ k, unitRow ((θs p.1).weight ℓ p.2) k *
      denseActivation σ (θs p.1) (x i) ℓ k
  let A : (Fin n → Bool) → Option ((Fin n → Bool) × Fin (w (ℓ + 1))) → ℝ :=
    fun s h ↦ ∑ i, sgnR s i * σ (t h i)
  let B : (Fin n → Bool) → Option ((Fin n → Bool) × Fin (w (ℓ + 1))) → ℝ :=
    fun s h ↦ ∑ i, sgnR s i * t h i
  have hA0 : ∀ s, A s none = 0 := fun s ↦ by simp [A, t, hσ0]
  -- (a) one layer against the finite family
  have ha : ∀ s, ‖sumAct σ x (ℓ + 1) (θs s) s‖ ≤ C * sSup (range fun h ↦ |A s h|) := by
    intro s
    set M := sSup (range fun h ↦ |A s h|)
    have hM : ∀ h, |A s h| ≤ M := fun h ↦ le_csSup (finite_range _).bddAbove ⟨h, rfl⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM none)
    have hcoord : ∀ r, (∑ i, sgnR s i * denseActivation σ (θs s) (x i) (ℓ + 1) r) =
        Real.sqrt (∑ k, (θs s).weight ℓ r k ^ 2) * A s (some (s, r)) := by
      intro r
      simp only [A, t, Option.elim, denseActivation, (hθs s).1 ℓ, Pi.zero_apply, add_zero,
        Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [sum_mul_eq_sqrt_mul_unitRow, hhom _ (Real.sqrt_nonneg _)]
      ring
    rw [norm_sumAct]
    simp_rw [hcoord]
    calc Real.sqrt (∑ r, (Real.sqrt (∑ k, (θs s).weight ℓ r k ^ 2) * A s (some (s, r))) ^ 2)
        ≤ Real.sqrt (C ^ 2 * M ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc ∑ r, (Real.sqrt (∑ k, (θs s).weight ℓ r k ^ 2) * A s (some (s, r))) ^ 2
              ≤ ∑ r, (∑ k, (θs s).weight ℓ r k ^ 2) * M ^ 2 := by
                refine Finset.sum_le_sum fun r _ ↦ ?_
                rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
                exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.mp (hM _)).1
                  (abs_le.mp (hM _)).2) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
            _ = (∑ r, ∑ k, (θs s).weight ℓ r k ^ 2) * M ^ 2 := (Finset.sum_mul _ _ _).symm
            _ ≤ C ^ 2 * M ^ 2 :=
                mul_le_mul_of_nonneg_right ((hθs s).2.2.1 ℓ hℓ) (sq_nonneg _)
      _ = C * M := by
          rw [← mul_pow, Real.sqrt_sq (mul_nonneg hC hM0)]
  -- (b) absolute values by symmetrization
  let fl : (Fin n → Bool) → (Fin n → Bool) := fun s i ↦ !s i
  have hfl : Function.Involutive fl := fun s ↦ by funext i; simp [fl]
  have hAfl : ∀ s h, A (fl s) h = -A s h := by
    intro s h
    simp only [A, sgnR, fl, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hsi : s i <;> simp [hsi]
  have hb : ∀ s, sSup (range fun h ↦ |A s h|) ≤
      sSup (range (A s)) + sSup (range (A (fl s))) := by
    intro s
    have h1 : ∀ h, A s h ≤ sSup (range (A s)) := fun h ↦
      le_csSup (finite_range _).bddAbove ⟨h, rfl⟩
    have h2 : ∀ h, A (fl s) h ≤ sSup (range (A (fl s))) := fun h ↦
      le_csSup (finite_range _).bddAbove ⟨h, rfl⟩
    have h10 := h1 none; have h20 := h2 none
    rw [hA0] at h10 h20
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    show |A s h| ≤ _
    rcases abs_cases (A s h) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he]; linarith [h1 h]
    · rw [he, ← hAfl]; linarith [h2 h]
  have hc : ∑ s, sSup (range (A (fl s))) = ∑ s, sSup (range (A s)) :=
    Fintype.sum_equiv (hfl.toPerm fl) _ _ fun s ↦ rfl
  -- (d) contraction
  have hd : ∑ s, sSup (range (A s)) ≤ ∑ s, sSup (range (B s)) := by
    have hlip : ∀ a b, |σ a - σ b| ≤ 1 * |a - b| := fun a b ↦ by
      simpa [Real.dist_eq] using hσ.dist_le_mul a b
    have := sum_sSup_rademacher_comp_le n t σ zero_le_one hlip
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have e1 : ∀ s : Fin n → Bool, sSup (range fun h ↦
        (∑ i, (if s i then (1 : ℝ) else -1) * σ (t h i)) / n) = sSup (range (A s)) / n :=
      fun s ↦ sSup_range_div (A s) hn'
    have e2 : ∀ s : Fin n → Bool, sSup (range fun h ↦
        (∑ i, (if s i then (1 : ℝ) else -1) * t h i) / n) = sSup (range (B s)) / n :=
      fun s ↦ sSup_range_div (B s) hn'
    simp_rw [e1, e2, one_mul, ← Finset.sum_div] at this
    exact (div_le_div_iff_of_pos_right hn').mp this
  -- (e) back to the previous layer
  have he : ∀ s, sSup (range (B s)) ≤ layerSup (H := H) σ x C ℓ s := by
    intro s
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    cases h with
    | none => simpa [B, t] using layerSup_nonneg hσ hhom hC x hℓ.le s
    | some p =>
      obtain ⟨s', r⟩ := p
      refine le_trans ?_ (le_layerSup hσ hhom hC x hℓ.le s (hθs s'))
      rw [norm_sumAct]
      show ∑ i, sgnR s i * ∑ k, unitRow ((θs s').weight ℓ r) k *
        denseActivation σ (θs s') (x i) ℓ k ≤ _
      have hre : ∑ i, sgnR s i * ∑ k, unitRow ((θs s').weight ℓ r) k *
          denseActivation σ (θs s') (x i) ℓ k = ∑ k, unitRow ((θs s').weight ℓ r) k *
          ∑ i, sgnR s i * denseActivation σ (θs s') (x i) ℓ k := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hre]
      exact sum_mul_le_sqrt _ _ (sum_unitRow_sq_le _)
  calc ∑ s, layerSup (H := H) σ x C (ℓ + 1) s
      ≤ ∑ s, (‖sumAct σ x (ℓ + 1) (θs s) s‖ + δ) :=
        Finset.sum_le_sum fun s _ ↦ by linarith [hlt s]
    _ = ∑ s, ‖sumAct σ x (ℓ + 1) (θs s) s‖ + ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
        simp only [δ]; push_cast; field_simp
    _ ≤ ∑ s, C * (sSup (range (A s)) + sSup (range (A (fl s)))) + ε := by
        gcongr with s
        exact (ha s).trans (mul_le_mul_of_nonneg_left (hb s) hC)
    _ = 2 * C * ∑ s, sSup (range (A s)) + ε := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hc]; ring
    _ ≤ 2 * C * ∑ s, layerSup (H := H) σ x C ℓ s + ε :=
        add_le_add_left (mul_le_mul_of_nonneg_left
          (hd.trans (Finset.sum_le_sum fun s _ ↦ he s)) (by positivity)) _


/-- Products of distinct Rademacher signs average to zero. -/
private theorem sum_sgnR_mul_sgnR {n : ℕ} (i i' : Fin n) :
    ∑ s : Fin n → Bool, sgnR s i * sgnR s i' = if i = i' then 2 ^ n else 0 := by
  split_ifs with h
  · subst h
    have : ∀ s : Fin n → Bool, sgnR s i * sgnR s i = 1 := fun s ↦ by
      unfold sgnR; split_ifs <;> norm_num
    simp [this]
  · let fl : (Fin n → Bool) → (Fin n → Bool) := fun s ↦ Function.update s i (!s i)
    have hfl : Function.Involutive fl := fun s ↦ by
      funext k
      by_cases hk : k = i
      · subst hk; simp [fl]
      · simp [fl, Function.update_of_ne hk]
    have hneg : ∀ s, sgnR (fl s) i * sgnR (fl s) i' = -(sgnR s i * sgnR s i') := by
      intro s
      simp only [sgnR, fl, Function.update_self, Function.update_of_ne (Ne.symm h)]
      cases s i <;> cases s i' <;> norm_num
    have := Fintype.sum_equiv (hfl.toPerm fl) (fun s ↦ sgnR (fl s) i * sgnR (fl s) i')
      (fun s ↦ sgnR s i * sgnR s i') fun s ↦ by simp
    simp_rw [hneg, Finset.sum_neg_distrib] at this
    linarith

/-- Cauchy–Schwarz for finite real sums. -/
private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ k, u k * v k ≤ Real.sqrt (∑ k, u k ^ 2) * Real.sqrt (∑ k, v k ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  calc ∑ k, u k * v k ≤ |∑ k, u k * v k| := le_abs_self _
    _ = Real.sqrt ((∑ k, u k * v k) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The input layer: summed over sign patterns, the norm of the signed sum of `n` points of the
unit ball is at most `2ⁿ √n`. -/
private theorem sum_layerSup_zero_le (σ : ℝ → ℝ) {C : ℝ} {n : ℕ} (x : Fin n → Fin (w 0) → ℝ)
    (hx : ∀ i, ∑ j, x i j ^ 2 ≤ 1) :
    ∑ s, layerSup (H := H) σ x C 0 s ≤ 2 ^ n * Real.sqrt n := by
  have hconst : ∀ s, layerSup (H := H) σ x C 0 s =
      Real.sqrt (∑ k, (∑ i, sgnR s i * x i k) ^ 2) := by
    intro s
    unfold layerSup
    have : (fun θ : DenseNetParams w H ↦ ‖sumAct σ x 0 θ s‖) =
        fun _ ↦ Real.sqrt (∑ k, (∑ i, sgnR s i * x i k) ^ 2) := by
      funext θ; rw [norm_sumAct]; rfl
    rw [this, Set.Nonempty.image_const ⟨_, zero_mem_biasFreeSet⟩, csSup_singleton]
  simp_rw [hconst]
  set a : (Fin n → Bool) → ℝ := fun s ↦ Real.sqrt (∑ k, (∑ i, sgnR s i * x i k) ^ 2)
  have ha2 : ∑ s, a s ^ 2 = 2 ^ n * ∑ i, ∑ k, x i k ^ 2 := by
    simp only [a]
    simp_rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (γ := Fin n → Bool) (s := Finset.univ)]
    have : ∀ k (i i' : Fin n), ∑ s : Fin n → Bool, sgnR s i * x i k * (sgnR s i' * x i' k) =
        x i k * x i' k * if i = i' then 2 ^ n else 0 := by
      intro k i i'
      rw [← sum_sgnR_mul_sgnR i i', Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp_rw [this]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [Finset.mul_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.mul_sum]; ring_nf
  have hsum : ∑ i, ∑ k, x i k ^ 2 ≤ n := by
    calc ∑ i, ∑ k, x i k ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hx i
      _ = n := by simp
  have hcs : (∑ s, a s) ^ 2 ≤ 2 ^ n * ∑ s, a s ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → Bool))
      (fun _ ↦ (1 : ℝ)) a
    simpa using this
  rw [ha2] at hcs
  have hnn : 0 ≤ ∑ s, a s := Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
  rw [← Real.sqrt_sq hnn, show (2 : ℝ) ^ n * Real.sqrt n = Real.sqrt ((2 ^ n) ^ 2 * n) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt (hcs.trans ?_)
  calc (2 : ℝ) ^ n * (2 ^ n * ∑ i, ∑ k, x i k ^ 2) ≤ 2 ^ n * (2 ^ n * n) := by gcongr
    _ = (2 ^ n) ^ 2 * n := by ring


/-- The output layer: a signed empirical average of a constrained bias-free network is at most
`C` times the last layer supremum divided by `n`. -/
private theorem sSup_output_le {σ : ℝ → ℝ} (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (x : Fin n → Fin (w 0) → ℝ) (s : Fin n → Bool) :
    sSup ((fun f ↦ (∑ i, (if s i then (1 : ℝ) else -1) * f (x i)) / n) ''
      ((fun θ : DenseNetParams w H ↦ denseNetOutput σ θ) '' biasFreeSet w H C)) ≤
      C * layerSup (H := H) σ x C H s / n := by
  refine csSup_le ((Set.Nonempty.image _ ⟨_, zero_mem_biasFreeSet⟩).image _) ?_
  rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  have hre : ∑ i, (if s i then (1 : ℝ) else -1) * denseNetOutput σ θ (x i) =
      ∑ j, θ.outWeight j * ∑ i, sgnR s i * denseActivation σ θ (x i) H j := by
    simp only [denseNetOutput, hθ.2.1, add_zero, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by simp [sgnR]
  rw [hre]
  refine (sum_mul_le_sqrt_mul_sqrt _ _).trans ?_
  rw [← norm_sumAct]
  refine mul_le_mul ?_ (le_layerSup hσ hhom hC x le_rfl s hθ) (norm_nonneg _) hC
  rw [← Real.sqrt_sq hC]
  exact Real.sqrt_le_sqrt hθ.2.2.2

end Rademacher

/-- GAPS 107.35, norm-based capacity: bias-free networks of depth `L = H + 1` on the unit ball,
with a `1`-Lipschitz positively homogeneous activation and all weight matrices of Frobenius
norm at most `C` (the squared Frobenius norm `∑ᵢ ∑ⱼ Wᵢⱼ²` being at most `C²`), have empirical
Rademacher complexity at most `2^{L-1} C^L / √n`, independently of the widths. (For `n = 0`
both sides vanish.) -/
theorem empiricalRademacherComplexity_biasFree_le (σ : ℝ → ℝ) (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) (w : ℕ → ℕ) (H : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (x : Fin n → Fin (w 0) → ℝ) (hx : ∀ i, ∑ j, x i j ^ 2 ≤ 1) :
    empiricalRademacherComplexityOfSet n
      ((fun θ : DenseNetParams w H ↦ denseNetOutput σ θ) ''
        {θ | (∀ ℓ, θ.bias ℓ = 0) ∧ θ.outBias = 0 ∧
          (∀ ℓ < H, ∑ i, ∑ j, θ.weight ℓ i j ^ 2 ≤ C ^ 2) ∧ ∑ j, θ.outWeight j ^ 2 ≤ C ^ 2}) x ≤
      2 ^ H * C ^ (H + 1) / Real.sqrt n := by
  change empiricalRademacherComplexityOfSet n
    ((fun θ : DenseNetParams w H ↦ denseNetOutput σ θ) '' biasFreeSet w H C) x ≤ _
  unfold empiricalRademacherComplexityOfSet
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, Real.sqrt_zero]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun s _ ↦ ?_)
    exact Real.sSup_nonpos fun _ ⟨_, _, h⟩ ↦ h ▸ le_rfl
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hiter : ∀ ℓ ≤ H, ∑ s, layerSup (H := H) σ x C ℓ s ≤
      (2 * C) ^ ℓ * ∑ s, layerSup (H := H) σ x C 0 s := by
    intro ℓ hℓ
    induction ℓ with
    | zero => simp
    | succ ℓ ih =>
      calc ∑ s, layerSup (H := H) σ x C (ℓ + 1) s
          ≤ 2 * C * ∑ s, layerSup (H := H) σ x C ℓ s :=
            sum_layerSup_succ_le hσ hhom hC hn x (by omega)
        _ ≤ 2 * C * ((2 * C) ^ ℓ * ∑ s, layerSup (H := H) σ x C 0 s) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
        _ = (2 * C) ^ (ℓ + 1) * ∑ s, layerSup (H := H) σ x C 0 s := by ring
  calc (2 : ℝ)⁻¹ ^ n * ∑ s : Fin n → Bool, sSup ((fun f ↦
        (∑ i, (if s i then (1 : ℝ) else -1) * f (x i)) / n) ''
          ((fun θ : DenseNetParams w H ↦ denseNetOutput σ θ) '' biasFreeSet w H C))
      ≤ (2 : ℝ)⁻¹ ^ n * ∑ s, C * layerSup (H := H) σ x C H s / n :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ ↦
          sSup_output_le hσ hhom hC x s) (by positivity)
    _ = (2 : ℝ)⁻¹ ^ n * (C / n) * ∑ s, layerSup (H := H) σ x C H s := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ (2 : ℝ)⁻¹ ^ n * (C / n) * ((2 * C) ^ H * (2 ^ n * Real.sqrt n)) := by
        refine mul_le_mul_of_nonneg_left ((hiter H le_rfl).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (sum_layerSup_zero_le σ x hx) (by positivity)
    _ = 2 ^ H * C ^ (H + 1) / Real.sqrt n := by
        have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
        have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
        have h2 : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
        rw [eq_div_iff hs]
        calc (2 : ℝ)⁻¹ ^ n * (C / n) * ((2 * C) ^ H * (2 ^ n * Real.sqrt n)) * Real.sqrt n
            = ((2 : ℝ)⁻¹ ^ n * 2 ^ n) * (C * (2 * C) ^ H) * (Real.sqrt n ^ 2 / n) := by ring
          _ = 2 ^ H * C ^ (H + 1) := by
            rw [h2, hsq, div_self hn'.ne', mul_pow]; ring

/-- The unit cube `[0,1]^d` in `Fin d → ℝ`. -/
def holderUnitCube (d : ℕ) : Set (Fin d → ℝ) := Icc 0 1

/-- GAPS 107.37, depth lower bound (Yarotsky): a `C²` function on `[0,1]^d` that is not affine
there cannot be approximated uniformly within `ε` by ReLU networks with `H ≥ 1` hidden layers
and at most `c ε^{-1/(2H)}` hidden neurons, for all small `ε`. The restriction to small `ε`
is necessary, since constants approximate within any large `ε`. -/
theorem relu_depth_lower_bound (d : ℕ) (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiffOn ℝ 2 g (holderUnitCube d))
    (hna : ¬ ∃ (a : Fin d → ℝ) (b : ℝ), ∀ x ∈ holderUnitCube d, g x = a ⬝ᵥ x + b)
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Ioo 0 ε₀, ∀ w : ℕ → ℕ, ∀ hw : w 0 = d,
      (denseHiddenNeurons w H : ℝ) ≤ c * ε ^ (-(1 / (2 * H : ℝ))) →
      ∀ θ : DenseNetParams w H, ∃ x ∈ holderUnitCube d,
        ε ≤ |denseNetOutput relu θ (fun j ↦ x (Fin.cast hw j)) - g x| := by
  sorry

/-- GAPS 107.37, depth separation (Eldan–Shamir) for the ReLU: for `d ≥ C` there are a
probability measure on `ℝ^d` and a function bounded by `2` computed by a two-hidden-layer ReLU
network of width at most `C d⁵` and parameters at most `C d^C` in absolute value, at squared
`L²` distance at least `c` from every one-hidden-layer ReLU network of width at most
`c e^{cd}` (the squared distance is an extended nonnegative integral, so no integrability is
presupposed). The logistic and Heaviside cases are not formalized. -/
theorem relu_eldan_shamir_separation :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ d : ℕ, C ≤ d →
      ∃ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ ∧
      ∃ (w : ℕ → ℕ) (hw : w 0 = d) (θ : DenseNetParams w 2),
        (w 1 : ℝ) ≤ C * d ^ 5 ∧ (w 2 : ℝ) ≤ C * d ^ 5 ∧
        (∀ ℓ < 2, ∀ i j, |θ.weight ℓ i j| ≤ C * d ^ C ∧ |θ.bias ℓ i| ≤ C * d ^ C) ∧
        (∀ j, |θ.outWeight j| ≤ C * d ^ C) ∧ |θ.outBias| ≤ C * d ^ C ∧
        (∀ x : Fin d → ℝ, |denseNetOutput relu θ (fun j ↦ x (Fin.cast hw j))| ≤ 2) ∧
        ∀ (w' : ℕ → ℕ) (hw' : w' 0 = d), (w' 1 : ℝ) ≤ c * Real.exp (c * d) →
          ∀ θ' : DenseNetParams w' 1,
            ENNReal.ofReal c ≤ ∫⁻ x, ENNReal.ofReal ((denseNetOutput relu θ'
              (fun j ↦ x (Fin.cast hw' j)) - denseNetOutput relu θ (fun j ↦ x (Fin.cast hw j))) ^ 2)
              ∂μ := by
  sorry

/-- Membership in the Hölder ball of smoothness `β ∈ (0,1]` and radius `K` on a domain `D`:
`sup_D |g| + sup_{x ≠ y} |g x - g y| / ‖x - y‖^β ≤ K`, with the sup norm on `S → ℝ`. -/
def IsInHolderBall {S : Type*} [Fintype S] (β K : ℝ) (D : Set (S → ℝ)) (g : (S → ℝ) → ℝ) :
    Prop :=
  ∃ A ≥ (0 : ℝ), ∃ B ≥ (0 : ℝ), A + B ≤ K ∧ (∀ x ∈ D, |g x| ≤ A) ∧
    ∀ x ∈ D, ∀ y ∈ D, |g x - g y| ≤ B * ‖x - y‖ ^ β

/-- Composition `g (k-1) ∘ ⋯ ∘ g 0` of a chain of maps between coordinate spaces. -/
def chainComp {d : ℕ → ℕ} (g : ∀ i, (Fin (d i) → ℝ) → (Fin (d (i + 1)) → ℝ)) :
    ∀ k : ℕ, (Fin (d 0) → ℝ) → (Fin (d k) → ℝ)
  | 0 => id
  | k + 1 => g k ∘ chainComp g k

/-- The compositional Hölder class of Schmidt-Hieber with smoothness indices in `(0,1]`:
compositions `g q ∘ ⋯ ∘ g 0` with `g i : [a i, b i]^{d i} → [a (i+1), b (i+1)]^{d (i+1)}`,
`[a 0, b 0] = [0,1]`, `|a i|, |b i| ≤ K`, each coordinate of `g i` depending on at most `t i`
arguments and lying, as a function of those, in the Hölder ball of smoothness `β i` and
radius `K`. The scalar output is the unique coordinate of `d (q+1) = 1`. -/
def compositionalHolderClass (q : ℕ) (d t : ℕ → ℕ) (hd : d (q + 1) = 1) (β a b : ℕ → ℝ)
    (K : ℝ) : Set ((Fin (d 0) → ℝ) → ℝ) :=
  {f | ∃ g : ∀ i, (Fin (d i) → ℝ) → (Fin (d (i + 1)) → ℝ),
    (∀ x, f x = chainComp g (q + 1) x ⟨0, by rw [hd]; exact one_pos⟩) ∧
    ∀ i ≤ q, ∀ x ∈ Icc (fun _ ↦ a i) (fun _ ↦ b i),
      g i x ∈ Icc (fun _ ↦ a (i + 1)) (fun _ ↦ b (i + 1)) ∧
      ∀ j, ∃ s : Finset (Fin (d i)), s.card ≤ t i ∧ ∃ h : (s → ℝ) → ℝ,
        IsInHolderBall (β i) K (Icc (fun _ ↦ a i) (fun _ ↦ b i)) h ∧
        ∀ y ∈ Icc (fun _ ↦ a i) (fun _ ↦ b i), g i y j = h fun k ↦ y k}

/-- Law of one observation `(X, f X + ε)` with `X` uniform on `[0,1]^d` and standard normal
noise. -/
def uniformDesignRegressionLaw {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Measure ((Fin d → ℝ) × ℝ) :=
  ((volume.restrict (holderUnitCube d)).prod (gaussianReal 0 1)).map fun z ↦ (z.1, f z.1 + z.2)

/-- GAPS 107.29, minimax lower bound for compositional Hölder classes (Schmidt-Hieber), for
smoothness indices in `(0,1]` and the uniform design on `[0,1]^d` (a density bounded above and
below). With `β*ᵢ = βᵢ ∏_{j > i} βⱼ` and `φₙ = maxᵢ n^{-2β*ᵢ/(2β*ᵢ + tᵢ)}`, if
`tᵢ ≤ min(d₀, …, dᵢ₋₁)`, then for all large `K` every measurable estimator has risk at least
`c φₙ` at some member of the class. Risk is an extended nonnegative integral, allowing
infinite risk for unrestricted estimators. The upper bound by sparse ReLU least squares is
not formalized here. -/
theorem compositionalHolder_minimax_lower_bound (q : ℕ) (d t : ℕ → ℕ) (hd : d (q + 1) = 1)
    (ht : ∀ i ≤ q, 1 ≤ t i ∧ t i ≤ d i) (hmin : ∀ i ≤ q, ∀ j < i, t i ≤ d j)
    (β : ℕ → ℝ) (hβ : ∀ i ≤ q, β i ∈ Ioc 0 1) (a b : ℕ → ℝ) (ha0 : a 0 = 0) (hb0 : b 0 = 1)
    (hab : ∀ i ≤ q + 1, a i < b i) :
    let βstar := fun i ↦ β i * ∏ j ∈ Finset.Ioc i q, β j
    let φ := fun n : ℕ ↦ (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one
      fun i ↦ (n : ℝ) ^ (-(2 * βstar i / (2 * βstar i + t i)))
    ∃ K₀ : ℝ, ∀ K ≥ K₀, (∀ i ≤ q + 1, |a i| ≤ K ∧ |b i| ≤ K) → ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      ∀ fhat : (Fin n → (Fin (d 0) → ℝ) × ℝ) → (Fin (d 0) → ℝ) → ℝ,
        Measurable (fun z : (Fin n → (Fin (d 0) → ℝ) × ℝ) × (Fin (d 0) → ℝ) ↦ fhat z.1 z.2) →
        ∃ f ∈ compositionalHolderClass q d t hd β a b K,
          ENNReal.ofReal (c * φ n) ≤
            ∫⁻ z, ∫⁻ x, ENNReal.ofReal ((fhat z x - f x) ^ 2)
              ∂volume.restrict (holderUnitCube (d 0))
            ∂Measure.pi fun _ : Fin n ↦ uniformDesignRegressionLaw f := by
  sorry

/-- Preactivation of one first-layer unit with parameters `θ = (weights, bias)` at input `y`,
for `N(0, C_W/d)` weights and `N(0, C_b)` bias written as scaled standard normals. -/
def gpFirstLayerPreactivation {d : ℕ} (Cb CW : ℝ) (θ : Fin d ⊕ Unit → ℝ) (y : Fin d → ℝ) : ℝ :=
  Real.sqrt Cb * θ (Sum.inr ()) + Real.sqrt (CW / d) * ∑ j, θ (Sum.inl j) * y j

/-- Scalar output preactivation of a one-hidden-layer network of width `N` with independent
standard normal parameters scaled to `N(0, C_b)` biases and `N(0, C_W / N)` output weights. -/
def gpSecondLayerPreactivation {d : ℕ} (N : ℕ) (Cb CW : ℝ) (σ : ℝ → ℝ)
    (θ : (Fin N × (Fin d ⊕ Unit)) ⊕ (Fin N ⊕ Unit) → ℝ) (y : Fin d → ℝ) : ℝ :=
  Real.sqrt Cb * θ (Sum.inr (Sum.inr ())) + Real.sqrt (CW / N) *
    ∑ k, θ (Sum.inr (Sum.inl k)) *
      σ (gpFirstLayerPreactivation Cb CW (fun i ↦ θ (Sum.inl (k, i))) y)

/-- GAPS 107.39, Gaussian-process limit at initialization for one hidden layer: at finitely
many inputs the output preactivations converge jointly in distribution, as the width tends to
infinity, to the centered Gaussian vector with covariance
`K²(x,x') = C_b + C_W 𝔼[σ(U)σ(U')]`, where `(U,U')` is the pair of preactivations of one
first-layer unit at `x, x'`, centered Gaussian with covariance
`K¹(x,x') = C_b + C_W ⟨x,x'⟩/d`. Deeper networks iterate this step. -/
theorem tendstoInDistribution_wide_network_gaussian (d m : ℕ) (Cb CW : ℝ)
    (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ) (hσ : Continuous σ) (A B : ℝ)
    (hgrowth : ∀ u, |σ u| ≤ A + B * |u|) (x : Fin m → Fin d → ℝ) :
    let unitLaw := Measure.pi fun _ : Fin d ⊕ Unit ↦ gaussianReal 0 1
    let K2 : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Cb + CW *
      ∫ θ, σ (gpFirstLayerPreactivation Cb CW θ (x i)) *
        σ (gpFirstLayerPreactivation Cb CW θ (x j)) ∂unitLaw
    TendstoInDistribution
      (fun (N : ℕ) (θ : (Fin N × (Fin d ⊕ Unit)) ⊕ (Fin N ⊕ Unit) → ℝ) ↦
        WithLp.toLp 2 fun i ↦ gpSecondLayerPreactivation N Cb CW σ θ (x i))
      atTop id (fun N ↦ Measure.pi fun _ ↦ gaussianReal 0 1)
      (multivariateGaussian 0 K2) := by
  sorry

end CKSD
