module

public import Suggested102

/-!
# Suggested statements for Section 103

Sources: `GAPS.md`, `SYNOPSIS103.md`, `STRUCTURE103.md`.
Every theorem is admitted. Scoped parts are identified in their docstrings.
The total variation convention is `sup_A |P(A)-Q(A)|`, with values in `[0,1]`.

Not represented: 103.7 (universal regression consistency), 103.9, 103.22 and 103.26 (infinite sequence/Sobolev/Hölder
minimax parameter spaces and estimator measurability), 103.11 (the least
concave majorant and Chernoff-law interface), 103.17 (process-valued weak
limits), 103.27 (isotonic risk), 103.28 (extended log-density maximization and canonical density
versions), 103.30 (infinite-dimensional eigenvector perturbation), 103.33 (sparse minimax risk), 103.35
(countable measurable model selection), 103.38 (Tracy–Widom law), 103.53
(neighborhood-selection conventions), 103.54 (residual-form eigenvector
perturbation and spiked-model bounds). Partial entries below do not include
their additional assertions about random designs, rates, or spline spaces.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section103

attribute [local instance] Classical.propDecidable

/-- Total variation in the statistical convention. -/
def tv {X : Type*} [MeasurableSpace X] (P Q : Measure X) : ℝ :=
  sSup {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |P.real A - Q.real A|}

/-- Kolmogorov–Smirnov discrepancy, using a countable determining set. -/
def ks {Ω : Type*} (X : ℕ → Ω → ℝ) (P : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  sSup (range fun t : ℚ ↦ |Section102.ecdf X n ω t - cdf P t|)

/-- Kernel density estimator in one dimension. -/
def kde {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℝ → ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, K ((t - X i ω) / h n)) / ((n : ℝ) * h n)

/-- Coordinatewise L1 norm restricted to a set of coordinates. -/
def l1 {p : ℕ} (S : Finset (Fin p)) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j ∈ S, |x j|

/-- Support size of a finite-dimensional vector. -/
def sparsity {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) : ℕ :=
  (Finset.univ.filter fun j ↦ x j ≠ 0).card

/-- The best `s`-term L1 approximation error. -/
def bestSparseError {p : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⨅ y : {y : EuclideanSpace ℝ (Fin p) // sparsity y ≤ s}, l1 Finset.univ (x - y.val)

/-- A restricted-isometry bound, expressed without taking an infimum over constants. -/
def RIP {p n : ℕ} (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x, sparsity x ≤ s →
    (1 - δ) * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 ∧ ‖A x‖ ^ 2 ≤ (1 + δ) * ‖x‖ ^ 2

/-- GAPS 103.1, finite-sample Dvoretzky–Kiefer–Wolfowitz–Massart bound. -/
theorem gap103_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < Real.sqrt n * ks X P n ω} ≤ 2 * Real.exp (-2 * t ^ 2) := by
  sorry

/-- GAPS 103.4, pointwise bias-corrected kernel-density central limit theorem. -/
theorem gap103_4 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hf2 : ContDiff ℝ 2 f)
    (hL2 : MemLp f 2 volume) (hD2 : MemLp (deriv (deriv f)) 2 volume)
    (hDb : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C)
    (hKm : Measurable K) (hKpos : ∀ x, 0 ≤ K x) (hKsym : ∀ x, K (-x) = K x)
    (hKb : ∃ C, ∀ x, K x ≤ C) (hKi : Integrable K volume)
    (hK1 : (∫ x, K x) = 1) (hK2 : Integrable (fun x ↦ x ^ 2 * K x) volume)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop)
    (hnh5 : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * h n ^ 5 ≤ C)
    (t : ℝ) (ht : 0 < f t) :
    InLaw μ (fun n ω ↦ Real.sqrt ((n : ℝ) * h n) *
      (kde X K h n ω t - f t - h n ^ 2 / 2 *
        (∫ u, u ^ 2 * K u) * deriv (deriv f) t))
      (gaussianReal 0 (Real.toNNReal ((∫ u, K u ^ 2) * f t))) := by
  sorry

/-- GAPS 103.5, one-dimensional universal almost-sure L1 consistency. -/
theorem gap103_5 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (f K : ℝ → ℝ)
    (hf : HasDensity P volume f) (hKm : Measurable K) (hKi : Integrable K volume)
    (hK1 : (∫ x, K x) = 1) (hKb : ∃ C, ∀ x, |K x| ≤ C)
    (hKc : ∃ R > 0, ∀ x, R < |x| → K x = 0)
    (h : ℕ → ℝ) (hh : ∀ n : ℕ, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ t, |kde X K h n ω t - f t|) atTop (𝓝 0) := by
  sorry

/-- GAPS 103.8, representer theorem in its Hilbert feature-vector formulation. -/
theorem gap103_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {n : ℕ} (v : Fin n → H) (y : Fin n → ℝ)
    (L : ℝ → ℝ → ℝ) (lambda : ℝ) (hlambda : 0 < lambda) (f : H)
    (hmin : ∀ g : H, (∑ i, L (y i) (inner ℝ f (v i))) + lambda * ‖f‖ ^ 2 ≤
      (∑ i, L (y i) (inner ℝ g (v i))) + lambda * ‖g‖ ^ 2) :
    f ∈ Submodule.span ℝ (range v) := by
  sorry

/-- Discrete measurable structure for the finite uniform-rank law. -/
local instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- GAPS 103.14, the exact mean and variance under uniform ranks. -/
theorem gap103_14 (n : ℕ) (hn : 2 ≤ n) (a c : Fin n → ℝ) :
    let P := ((Nat.factorial n : ℝ≥0∞)⁻¹) •
      (Measure.count : Measure (Equiv.Perm (Fin n)));
    let abar := (∑ i, a i) / n;
    let cbar := (∑ i, c i) / n;
    let T := fun σ : Equiv.Perm (Fin n) ↦ ∑ i, c i * a (σ i);
    (∫ σ, T σ ∂P) = (n : ℝ) * abar * cbar ∧
      variance P T = (∑ i, (c i - cbar) ^ 2) *
        (∑ i, (a i - abar) ^ 2) / (n - 1 : ℕ) := by
  sorry

/-- GAPS 103.29, the separable-Hilbert-space CLT, characterized by scalar variances. -/
theorem gap103_29 {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure H) [IsProbabilityMeasure P]
    (X : ℕ → Ω → H) (hiid : IID μ X P) (h2 : MemLp id 2 P) :
    let m := ∫ x, x ∂P;
    ∃ G : Measure H, IsProbabilityMeasure G ∧
      (∀ u : H, G.map (fun x ↦ inner ℝ u x) =
        gaussianReal 0 (Real.toNNReal (∫ x, (inner ℝ u (x - m)) ^ 2 ∂P))) ∧
      InLaw μ (fun n ω ↦ Real.sqrt n • (average X n ω - m)) G := by
  sorry

/-- GAPS 103.31, finite-dimensional PCA minimizes expected reconstruction error. -/
theorem gap103_31 {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ (Fin d))
    (hX : MemLp X 2 μ) (m : EuclideanSpace ℝ (Fin d))
    (hm : (∫ ω, X ω ∂μ) = m) (e : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (lambda : Fin d → ℝ) (hlambda : Antitone lambda)
    (hcov : ∀ i j, (∫ ω, inner ℝ (X ω - m) (e i) * inner ℝ (X ω - m) (e j) ∂μ) =
      if i = j then lambda i else 0) (hk : k ≤ d)
    (q : Fin k → EuclideanSpace ℝ (Fin d)) (hq : Orthonormal ℝ q) :
    (∑ j : Fin d, if k ≤ j.val then lambda j else 0) ≤
      ∫ ω, ‖X ω - m - ∑ j, inner ℝ (X ω - m) (q j) • q j‖ ^ 2 ∂μ := by
  sorry

/-- GAPS 103.34, deterministic lasso prediction/L1 bounds and the cone condition. -/
theorem gap103_34 {n p : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (β b : EuclideanSpace ℝ (Fin p)) (ε : EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) (hne : S.Nonempty) (lambda κ : ℝ) (hlambda : 0 < lambda) (hκ : 0 < κ)
    (hsupp : ∀ j ∉ S, β j = 0)
    (hnoise : ∀ δ, |inner ℝ ε (A δ)| / n ≤ lambda / 2 * l1 Finset.univ δ)
    (hcompat : ∀ δ, l1 Sᶜ δ ≤ 3 * l1 S δ →
      κ ^ 2 * (l1 S δ) ^ 2 ≤ (S.card : ℝ) * ‖A δ‖ ^ 2 / n)
    (hmin : ∀ t, ‖A β + ε - A b‖ ^ 2 / (2 * n) + lambda * l1 Finset.univ b ≤
      ‖A β + ε - A t‖ ^ 2 / (2 * n) + lambda * l1 Finset.univ t) :
    l1 Sᶜ (b - β) ≤ 3 * l1 S (b - β) ∧
      ‖A (b - β)‖ ^ 2 / n ≤ 9 * lambda ^ 2 * S.card / (4 * κ ^ 2) ∧
      l1 Finset.univ (b - β) ≤ 6 * lambda * S.card / κ ^ 2 := by
  sorry

/-- Benjamini–Hochberg rejection count, including the zero-rejection case. -/
def bhCount {m : ℕ} (p : Fin m → ℝ) (α : ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ ↦
    k ≤ (Finset.univ.filter fun i ↦ p i ≤ (k : ℝ) * α / m).card).sup id

/-- GAPS 103.37, FDR control for mutually independent p-values. -/
theorem gap103_37 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hrange : ∀ i ω, p i ω ∈ Icc 0 1) (hind : iIndepFun p μ)
    (H₀ : Finset (Fin m)) (hvalid : ∀ i ∈ H₀, ∀ t ∈ Icc (0 : ℝ) 1,
      μ.real {ω | p i ω ≤ t} ≤ t) (α : ℝ) (hα : α ∈ Ioo 0 1) :
    (∫ ω, ((H₀.filter fun i ↦ p i ω ≤
      (bhCount (fun j ↦ p j ω) α : ℝ) * α / m).card : ℝ) /
        max (bhCount (fun j ↦ p j ω) α : ℝ) 1 ∂μ) ≤ α * H₀.card / m := by
  sorry

/-- GAPS 103.39: Le Cam's two-point lower bound with the statistical TV normalization. -/
theorem gap103_39 {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (θ₀ θ₁ : Θ) (s : ℝ) (hs : 0 < s) (hsep : 2 * s ≤ dist θ₀ θ₁)
    (T : X → Θ) (hT : Measurable T) :
    (1 - tv P₀ P₁) / 2 ≤ max (P₀.real {x | s ≤ dist (T x) θ₀})
      (P₁.real {x | s ≤ dist (T x) θ₁}) := by
  sorry

/-- GAPS 103.40: Fano's bound in its finite-reference-KL form. -/
theorem gap103_40 {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (M : ℕ) (hM : 2 ≤ M)
    (θ : Fin M → Θ) (P : Fin M → Measure X) (hP : ∀ j, IsProbabilityMeasure (P j))
    (Q : Measure X) [IsProbabilityMeasure Q] (hKL : ∀ j, InformationTheory.klDiv (P j) Q ≠ ∞)
    (s : ℝ) (hs : 0 < s) (hsep : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    (T : X → Θ) (hT : Measurable T) :
    1 - (((∑ j, (InformationTheory.klDiv (P j) Q).toReal) / M + Real.log 2) / Real.log M) ≤
      sSup (range fun j ↦ (P j).real {x | s ≤ dist (T x) (θ j)}) := by
  sorry

/-- GAPS 103.45: a separated binary packing containing zero. -/
theorem gap103_45 (m : ℕ) (hm : 8 ≤ m) :
    ∃ C : Finset (Fin m → Bool), (fun _ ↦ false) ∈ C ∧
      Real.rpow 2 ((m : ℝ) / 8) ≤ (C.card : ℝ) - 1 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        (m : ℝ) / 8 ≤ ((Finset.univ.filter fun i ↦ x i ≠ y i).card : ℝ) := by
  sorry

/-- GAPS 103.46, TV version of Assouad's lemma for binary-valued estimators. -/
theorem gap103_46 {X : Type*} [MeasurableSpace X] (m : ℕ)
    (P : (Fin m → Bool) → Measure X) (hP : ∀ w, IsProbabilityMeasure (P w))
    (α : ℝ) (hα : α ∈ Icc 0 1)
    (hnear : ∀ w w', (Finset.univ.filter fun i ↦ w i ≠ w' i).card = 1 → tv (P w) (P w') ≤ α)
    (T : X → (Fin m → Bool)) (hT : Measurable T) :
    (m : ℝ) * (1 - α) / 2 ≤ sSup (range fun w ↦
      ∫ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) ∂P w) := by
  sorry

/-- GAPS 103.48, equivalence between the nullspace property and unique basis pursuit. -/
theorem gap103_48 {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) :
    (∀ δ, A δ = 0 → δ ≠ 0 → l1 S δ < l1 Sᶜ δ) ↔
    ∀ β, (∀ j ∉ S, β j = 0) → ∀ b, A b = A β → b ≠ β →
      l1 Finset.univ β < l1 Finset.univ b := by
  sorry

/-- GAPS 103.48, restricted-isometry sufficient condition for exact sparse recovery. -/
theorem gap103_48_rip {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : δ ∈ Ico 0 (1 / 3 : ℝ)) (hrip : RIP A (2 * s) δ)
    (S : Finset (Fin p)) (hS : S.card ≤ s) :
    ∀ v, A v = 0 → v ≠ 0 → l1 S v < l1 Sᶜ v := by
  sorry

/-- GAPS 103.49: stable basis pursuit, with constants depending only on the RIP bound. -/
theorem gap103_49 (δ : ℝ) (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) :
    ∃ C > 0, ∃ D > 0, ∀ (n p s : ℕ), 0 < s →
      ∀ A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n),
        RIP A (2 * s) δ → ∀ (β b : EuclideanSpace ℝ (Fin p))
        (y : EuclideanSpace ℝ (Fin n)) (η : ℝ), 0 ≤ η → ‖A β - y‖ ≤ η →
        ‖A b - y‖ ≤ η →
        (∀ t, ‖A t - y‖ ≤ η → l1 Finset.univ b ≤ l1 Finset.univ t) →
        l1 Finset.univ (b - β) ≤ C * bestSparseError s β + D * Real.sqrt s * η ∧
        ‖b - β‖ ≤ C / Real.sqrt s * bestSparseError s β + D * η := by
  sorry

/-- GAPS 103.52, deterministic sparse-row bound for hard covariance thresholding. -/
theorem gap103_52 {p : ℕ} (Sigma S : Matrix (Fin p) (Fin p) ℝ)
    (hSigma : Sigma.IsSymm) (hS : S.IsSymm) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (herr : ∀ i j, |S i j - Sigma i j| ≤ lambda) (s : ℕ)
    (hs : ∀ i, (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card ≤ s) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma)‖ ≤ 2 * s * lambda := by
  sorry

end CKSD.Section103
