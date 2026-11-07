module

public import CKSD.Learning.Algorithms
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

/-- Empirical Rademacher complexity of an arbitrary class of real functions. -/
def empiricalRademacherComplexityOfSet {X : Type*} (n : ℕ) (F : Set (X → ℝ))
    (x : Fin n → X) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ∑ s : Fin n → Bool,
    sSup ((fun f ↦ (∑ i, (if s i then (1 : ℝ) else -1) * f (x i)) / n) '' F)

/-- Squared Frobenius norm of a real matrix. -/
def frobeniusSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- GAPS 107.35, norm-based capacity: bias-free networks of depth `L = H + 1` on the unit ball,
with a `1`-Lipschitz positively homogeneous activation and all weight matrices of Frobenius
norm at most `C`, have empirical Rademacher complexity at most `2^{L-1} C^L / √n`,
independently of the widths. -/
theorem empiricalRademacherComplexity_biasFree_le (σ : ℝ → ℝ) (hσ : LipschitzWith 1 σ)
    (hhom : ∀ a ≥ (0 : ℝ), ∀ u, σ (a * u) = a * σ u) (w : ℕ → ℕ) (H : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (hn : 0 < n) (x : Fin n → Fin (w 0) → ℝ) (hx : ∀ i, ∑ j, x i j ^ 2 ≤ 1) :
    empiricalRademacherComplexityOfSet n
      ((fun θ : DenseNetParams w H ↦ denseNetOutput σ θ) ''
        {θ | (∀ ℓ, θ.bias ℓ = 0) ∧ θ.outBias = 0 ∧
          (∀ ℓ < H, frobeniusSq (θ.weight ℓ) ≤ C ^ 2) ∧ ∑ j, θ.outWeight j ^ 2 ≤ C ^ 2}) x ≤
      2 ^ H * C ^ (H + 1) / Real.sqrt n := by
  sorry

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
`c e^{cd}`. The logistic and Heaviside cases are not formalized. -/
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
            c ≤ ∫ x, (denseNetOutput relu θ' (fun j ↦ x (Fin.cast hw' j)) -
              denseNetOutput relu θ (fun j ↦ x (Fin.cast hw j))) ^ 2 ∂μ := by
  sorry

/-- Membership in the Hölder ball of smoothness `β ∈ (0,1]` and radius `K` on a domain. -/
def IsInCompositionHolderBall {S : Type*} [Fintype S] (β K : ℝ) (D : Set (S → ℝ)) (g : (S → ℝ) → ℝ) :
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
        IsInCompositionHolderBall (β i) K (Icc (fun _ ↦ a i) (fun _ ↦ b i)) h ∧
        ∀ y ∈ Icc (fun _ ↦ a i) (fun _ ↦ b i), g i y j = h fun k ↦ y k}

/-- Law of one observation `(X, f X + ε)` with `X` uniform on `[0,1]^d` and standard normal
noise. -/
def uniformDesignRegressionLaw {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Measure ((Fin d → ℝ) × ℝ) :=
  ((volume.restrict (holderUnitCube d)).prod (gaussianReal 0 1)).map fun z ↦ (z.1, f z.1 + z.2)

/-- GAPS 107.29, minimax lower bound for compositional Hölder classes (Schmidt-Hieber), for
smoothness indices in `(0,1]` and the uniform design on `[0,1]^d` (a density bounded above and
below). With `β*ᵢ = βᵢ ∏_{j > i} βⱼ` and `φₙ = maxᵢ n^{-2β*ᵢ/(2β*ᵢ + tᵢ)}`, if
`tᵢ ≤ min(d₀, …, dᵢ₋₁)`, then for all large `K` every measurable estimator has risk at least
`c φₙ` at some member of the class. The upper bound by sparse ReLU least squares is not
formalized here. -/
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
          c * φ n ≤ ∫ z, ∫ x, (fhat z x - f x) ^ 2 ∂volume.restrict (holderUnitCube (d 0))
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
theorem tendstoInDistribution_wide_network_gaussian (d m : ℕ) (hd : 0 < d) (Cb CW : ℝ)
    (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ) (hσ : Continuous σ) (A B : ℝ)
    (hgrowth : ∀ u, |σ u| ≤ A + B * |u|) (x : Fin m → Fin d → ℝ) :
    let unitLaw := Measure.pi fun _ : Fin d ⊕ Unit ↦ gaussianReal 0 1
    let K2 : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Cb + CW *
      ∫ θ, σ (gpFirstLayerPreactivation Cb CW θ (x i)) *
        σ (gpFirstLayerPreactivation Cb CW θ (x j)) ∂unitLaw
    MeasureTheory.TendstoInDistribution
      (fun (N : ℕ) (θ : (Fin N × (Fin d ⊕ Unit)) ⊕ (Fin N ⊕ Unit) → ℝ) ↦
        WithLp.toLp 2 fun i ↦ gpSecondLayerPreactivation N Cb CW σ θ (x i))
      atTop id (fun N ↦ Measure.pi fun _ ↦ gaussianReal 0 1)
      (multivariateGaussian 0 K2) := by
  sorry

end CKSD
