module

public import Suggested104
public import TauCeti.Probability.Distributions.Wishart.Basic

/-!
# Suggested statements for Section 105

Sources: `GAPS.md`, `SYNOPSIS105.md`, `STRUCTURE105.md`.
All proofs are admitted. Real covariance matrices use Euclidean coordinates;
finite-population values are fixed and the assignment or sample alone is random.

Not represented: 105.3 and 105.5 (differentiable GLM and regression asymptotics),
105.6 (identifiability of mixtures with varying component counts), 105.16
(invariant/similar test classes), 105.23–24 and 105.33–34 (matrix-variate
sampling asymptotics), 105.26 and 105.36 (graphical Markov properties),
105.29 (successive canonical variates), 105.35 (factor-model identification),
105.48 (the general measurable balancing-score theorem), 105.55–56
(IV/semiparametric efficiency frameworks), and 105.62–65, 105.67, 105.70–71
(graphical interventions, d-separation and structural identifiability).
Only the explicitly stated parts of 105.42, 105.44 and 105.49 are represented.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section105

attribute [local instance] Classical.propDecidable

/-- Quadratic form of a real matrix on Euclidean space. -/
def quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A x)

/-- Mean of a finite Euclidean sample. -/
def sampleMean {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- Centered scatter matrix of a finite Euclidean sample. -/
def scatter {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k ↦ ∑ i, (x i j - sampleMean x j) * (x i k - sampleMean x k)

/-- Negative Gaussian log-likelihood up to its constant term. -/
def gaussianNLL {n d : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (n : ℝ) / 2 * Real.log C.det + (∑ i, quad C⁻¹ (x i - m)) / 2

/-- Discrete measurable structure on finite samples of population units. -/
local instance (N : ℕ) : MeasurableSpace (Finset (Fin N)) := ⊤

/-- Uniform sampling of exactly `n` units from `N`. -/
def sampleDesign (N n : ℕ) : Measure (Finset (Fin N)) :=
  (Nat.choose N n : ℝ≥0∞)⁻¹ • Measure.count.restrict {s | s.card = n}

/-- Finite-population mean. -/
def popMean {N : ℕ} (y : Fin N → ℝ) : ℝ := (∑ i, y i) / N

/-- Finite-population variance with divisor `N-1`. -/
def popVariance {N : ℕ} (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i - popMean y) ^ 2) / (N - 1 : ℕ)

/-- A Latin square on `Fin s`. -/
def Latin {s : ℕ} (L : Fin s → Fin s → Fin s) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective (fun i ↦ L i j)

/-- Orthogonality of two Latin squares. -/
def OrthogonalLatin {s : ℕ} (L M : Fin s → Fin s → Fin s) : Prop :=
  Function.Injective (fun z : Fin s × Fin s ↦ (L z.1 z.2, M z.1 z.2))

/-- GAPS 105.1, scalar Gauss–Markov comparison by projecting an unbiased coefficient. -/
theorem gap105_1 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → EuclideanSpace ℝ (Fin n))
    (hY : MemLp Y 2 μ) (v : ℝ) (hv : 0 ≤ v)
    (hcov : ∀ i j, covariance μ (fun ω ↦ Y ω i) (fun ω ↦ Y ω j) = if i = j then v else 0)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hm : P (∫ ω, Y ω ∂μ) = ∫ ω, Y ω ∂μ) (a : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (P a) (Y ω) ∂μ) = ∫ ω, inner ℝ a (Y ω) ∂μ ∧
      variance μ (fun ω ↦ inner ℝ (P a) (Y ω)) ≤
        variance μ (fun ω ↦ inner ℝ a (Y ω)) := by
  sorry

/-- GAPS 105.2, residual chi-squared law and projection independence. -/
theorem gap105_2 {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hPid : ∀ x, P (P x) = P x)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (hm : P m = m) :
    let r := Module.finrank ℝ (LinearMap.range P.toLinearMap);
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ ‖x - P x‖ ^ 2 / v) = TauCeti.Probability.chiSquaredMeasure (n - r : ℕ) ∧
      IndepFun P (fun x ↦ ‖x - P x‖ ^ 2) G := by
  sorry

/-- GAPS 105.10, exact null F law for nested Gaussian projection models. -/
theorem gap105_10 {n : ℕ} (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hid : ∀ x, P₀ (P₀ x) = P₀ x ∧ P₁ (P₁ x) = P₁ x)
    (hsym : ∀ x y, inner ℝ (P₀ x) y = inner ℝ x (P₀ y) ∧
      inner ℝ (P₁ x) y = inner ℝ x (P₁ y))
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x) (hm : P₀ m = m) :
    let r₀ := Module.finrank ℝ (LinearMap.range P₀.toLinearMap);
    let r₁ := Module.finrank ℝ (LinearMap.range P₁.toLinearMap);
    ∀ (hr : r₀ < r₁),
    ∀ (hrn : r₁ < n),
    let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ));
    G.map (fun x ↦ (‖P₁ x - P₀ x‖ ^ 2 / (r₁ - r₀ : ℕ)) /
      (‖x - P₁ x‖ ^ 2 / (n - r₁ : ℕ))) =
      TauCeti.Probability.fisherSnedecorMeasure (r₁ - r₀ : ℕ) (n - r₁ : ℕ) := by
  sorry

/-- GAPS 105.15, Craig–Sakamoto criterion for centered quadratic forms. -/
theorem gap105_15 {n : ℕ} (Sigma A B : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sigma.PosDef) (hA : A.IsSymm) (hB : B.IsSymm) :
    IndepFun (quad A) (quad B) (multivariateGaussian 0 Sigma) ↔ A * Sigma * B = 0 := by
  sorry

/-- GAPS 105.22, normal sample mean/covariance independence and Hotelling's exact law. -/
theorem gap105_22 {n p : ℕ} (hp : 0 < p) (hn : p + 1 ≤ n)
    (m : EuclideanSpace ℝ (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (hS : Sigma.PosDef) :
    let P := Measure.pi (fun _ : Fin n ↦ multivariateGaussian m Sigma);
    let S := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ ((n - 1 : ℕ) : ℝ)⁻¹ • scatter x;
    IndepFun sampleMean scatter P ∧
      P.map scatter = (TauCeti.Probability.wishartGramMeasure (n - 1) Sigma).map
        (fun W ↦ (W.val : Matrix (Fin p) (Fin p) ℝ)) ∧
      P.map (fun x ↦ ((n - p : ℕ) : ℝ) / (((n - 1 : ℕ) : ℝ) * p) *
        ((n : ℝ) * quad (S x)⁻¹ (sampleMean x - m))) =
        TauCeti.Probability.fisherSnedecorMeasure p (n - p : ℕ) := by
  sorry

/-- GAPS 105.28, the full-rank Gaussian covariance likelihood has a unique minimum. -/
theorem gap105_28 {n p : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    let S := (n : ℝ)⁻¹ • scatter x;
    ∀ (hS : S.PosDef),
    ∀ (m : EuclideanSpace ℝ (Fin p)),
    ∀ (C : Matrix (Fin p) (Fin p) ℝ),
    ∀ (hC : C.PosDef),
    gaussianNLL x (sampleMean x) S ≤ gaussianNLL x m C ∧
      (gaussianNLL x (sampleMean x) S = gaussianNLL x m C ↔ m = sampleMean x ∧ C = S) := by
  sorry

/-- GAPS 105.31, determinant law obtained from Bartlett's decomposition. -/
theorem gap105_31 {p : ℕ} (n : ℕ) (hn : p ≤ n)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hS : Sigma.PosDef) :
    (TauCeti.Probability.wishartGramMeasure n Sigma).map (fun W ↦ Matrix.det W.val) =
      (Measure.pi (fun i : Fin p ↦ TauCeti.Probability.chiSquaredMeasure (n - i.val : ℕ))).map
        (fun z ↦ Sigma.det * ∏ i, z i) := by
  sorry

/-- GAPS 105.32, exact correlation t law for independent standard-normal coordinates. -/
theorem gap105_32 (N : ℕ) (hN : 2 < N) :
    let P := Measure.pi (fun _ : Fin N ↦ (gaussianReal 0 1).prod (gaussianReal 0 1));
    let a := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).1) / N;
    let b := fun x : Fin N → ℝ × ℝ ↦ (∑ i, (x i).2) / N;
    let r := fun x : Fin N → ℝ × ℝ ↦
      (∑ i, ((x i).1 - a x) * ((x i).2 - b x)) /
        Real.sqrt ((∑ i, ((x i).1 - a x) ^ 2) * (∑ i, ((x i).2 - b x) ^ 2));
    P.map (fun x ↦ Real.sqrt (N - 2 : ℕ) * r x / Real.sqrt (1 - r x ^ 2)) =
      TauCeti.Probability.studentTMeasure (N - 2 : ℕ) := by
  sorry

/-- GAPS 105.37, Kiefer–Wolfowitz equivalence for a finite design space. -/
theorem gap105_37 {s p : ℕ} (hp : 0 < p)
    (f : Fin s → EuclideanSpace ℝ (Fin p)) (w : Fin s → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    let M := fun a : Fin s → ℝ ↦ Matrix.of (fun j k ↦ ∑ i, a i * f i j * f i k);
    ∀ (hM : (M w).PosDef),
    (∀ a, (∀ i, 0 ≤ a i) → (∑ i, a i = 1) → (M a).det ≤ (M w).det) ↔
      (∀ i, quad (M w)⁻¹ (f i) ≤ p) ∧
        ∀ i, 0 < w i → quad (M w)⁻¹ (f i) = p := by
  sorry

/-- GAPS 105.38, conservative finite randomization p-values, including ties. -/
theorem gap105_38 {s : ℕ} (w T : Fin s → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (α : ℝ) (hα : α ∈ Icc 0 1) :
    let p := fun i ↦ ∑ j, if T i ≤ T j then w j else 0;
    (∑ i, if p i ≤ α then w i else 0) ≤ α := by
  sorry

/-- GAPS 105.42, Fisher's inequality for nontrivial balanced incomplete blocks. -/
theorem gap105_42 (v b k r ell : ℕ) (hv : 2 ≤ v) (hk : 0 < k) (hkv : k < v)
    (hr : 0 < r) (hell : 0 < ell) (B : Fin b → Finset (Fin v))
    (hsize : ∀ j, (B j).card = k)
    (hrep : ∀ i, (Finset.univ.filter fun j ↦ i ∈ B j).card = r)
    (hpair : ∀ i i', i ≠ i' → (Finset.univ.filter fun j ↦ i ∈ B j ∧ i' ∈ B j).card = ell) :
    v ≤ b := by
  sorry

/-- GAPS 105.44, the upper bound on a family of mutually orthogonal Latin squares. -/
theorem gap105_44 (s k : ℕ) (hs : 2 ≤ s)
    (L : Fin k → Fin s → Fin s → Fin s)
    (hLatin : ∀ i, Latin (L i))
    (hortho : ∀ i j, i ≠ j → OrthogonalLatin (L i) (L j)) : k ≤ s - 1 := by
  sorry

/-- GAPS 105.44, existence of a complete family at prime-power orders. -/
theorem gap105_44_primePower (s : ℕ) (hs : IsPrimePow s) :
    ∃ L : Fin (s - 1) → Fin s → Fin s → Fin s,
      (∀ i, Latin (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatin (L i) (L j) := by
  sorry

/-- GAPS 105.46, Neyman's exact design variance in a completely randomized experiment. -/
theorem gap105_46 {N : ℕ} (n₁ n₀ : ℕ) (hn : n₁ + n₀ = N)
    (h₁ : 0 < n₁) (h₀ : 0 < n₀) (y₁ y₀ : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y₁ i) / n₁ - (∑ i ∈ sᶜ, y₀ i) / n₀;
    (∫ s, T s ∂sampleDesign N n₁) = popMean (y₁ - y₀) ∧
      variance (sampleDesign N n₁) T = popVariance y₁ / n₁ + popVariance y₀ / n₀ -
        popVariance (y₁ - y₀) / N := by
  sorry

/-- GAPS 105.47, finite-stratum potential-outcome identification under mean ignorability. -/
theorem gap105_47 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Bool → Ω → ℝ)
    (hY : ∀ a, Integrable (Y a) P) (a : Bool) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e := fun x ↦ P.real {ω | X ω = x ∧ A ω = a} / p x;
    let m := fun x ↦ (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) / (p x * e x);
    ∀ (hp : ∀ x, 0 < p x),
    ∀ (he : ∀ x, 0 < e x),
    ∀ (hign : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = a}, Y a ω ∂P) =
      e x * ∫ ω in {ω | X ω = x}, Y a ω ∂P),
    (∫ ω, Y a ω ∂P) = ∑ x, p x * m x ∧
      (∫ ω, Y a ω ∂P) = ∫ ω, (if A ω = a then Y (A ω) ω else 0) / e (X ω) ∂P := by
  sorry

/-- GAPS 105.49, finite-stratum double-robustness bias identity.
The causal identification and cross-fitting conclusions require the additional
frameworks described in the source; this is the observable-moment identity. -/
theorem gap105_49 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin k) (A : Ω → Bool)
    (hX : Measurable X) (hA : Measurable A) (Y : Ω → ℝ) (hY : Integrable Y P)
    (m₁ m₀ a₁ a₀ e : Fin k → ℝ) :
    let p := fun x ↦ P.real {ω | X ω = x};
    let e₀ := fun x ↦ P.real {ω | X ω = x ∧ A ω = true} / p x;
    ∀ (hp : ∀ x, 0 < p x),
    ∀ (he : ∀ x, e x ∈ Ioo 0 1),
    ∀ (hcond₁ : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = true}, Y ω ∂P) = p x * e₀ x * m₁ x),
    ∀ (hcond₀ : ∀ x, (∫ ω in {ω | X ω = x ∧ A ω = false}, Y ω ∂P) = p x * (1 - e₀ x) * m₀ x),
    (∫ ω, a₁ (X ω) - a₀ (X ω) +
      (if A ω then (Y ω - a₁ (X ω)) / e (X ω)
        else -(Y ω - a₀ (X ω)) / (1 - e (X ω))) ∂P) -
      (∑ x, p x * (m₁ x - m₀ x)) =
      ∑ x, p x * (e x - e₀ x) * ((a₁ x - m₁ x) / e x + (a₀ x - m₀ x) / (1 - e x)) := by
  sorry

/-- GAPS 105.50: the Wald ratio identifies the complier average effect. -/
theorem gap105_50 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → Bool) (A : Bool → Ω → Bool)
    (Y : Bool → Ω → ℝ) (hZ : Measurable Z) (hA : ∀ z, Measurable (A z))
    (hY : ∀ a, Integrable (Y a) P)
    (hind : IndepFun (fun ω ↦ (Y false ω, Y true ω, A false ω, A true ω)) Z P)
    (hmon : ∀ᵐ ω ∂P, A false ω = true → A true ω = true)
    (hp : ∀ z : Bool, 0 < P {ω | Z ω = z}) :
    let obsA := fun ω ↦ if A (Z ω) ω then (1 : ℝ) else 0;
    let obsY := fun ω ↦ Y (A (Z ω) ω) ω;
    let mean := fun (f : Ω → ℝ) z ↦ (∫ ω in {ω | Z ω = z}, f ω ∂P) / P.real {ω | Z ω = z};
    ∀ (hstage : mean obsA true ≠ mean obsA false),
    let C := {ω | A false ω = false ∧ A true ω = true};
    (mean obsY true - mean obsY false) / (mean obsA true - mean obsA false) =
      (∫ ω in C, Y true ω - Y false ω ∂P) / P.real C := by
  sorry

/-- GAPS 105.72, Horvitz–Thompson unbiasedness and exact design variance. -/
theorem gap105_72 {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i, 0 < pi i),
    let T := fun s : Finset (Fin N) ↦ ∑ i ∈ s, y i / pi i;
    (∫ s, T s ∂P) = ∑ i, y i ∧
      variance P T = ∑ i, ∑ j, (pij i j - pi i * pi j) * y i * y j / (pi i * pi j) := by
  sorry

/-- GAPS 105.72, unbiased estimation of the Horvitz–Thompson design variance. -/
theorem gap105_72_variance {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i j, 0 < pij i j),
    (∫ s, ∑ i ∈ s, ∑ j ∈ s,
      (pij i j - pi i * pi j) / pij i j * y i * y j / (pi i * pi j) ∂P) =
      variance P (fun s ↦ ∑ i ∈ s, y i / pi i) := by
  sorry

/-- GAPS 105.72, Sen–Yates–Grundy identity for a fixed-size sampling design. -/
theorem gap105_72_syg {N : ℕ} (P : Measure (Finset (Fin N))) [IsProbabilityMeasure P]
    (n : ℕ) (hn : ∀ᵐ s ∂P, s.card = n) (y : Fin N → ℝ) :
    let pi := fun i ↦ P.real {s | i ∈ s};
    let pij := fun i j ↦ P.real {s | i ∈ s ∧ j ∈ s};
    ∀ (hp : ∀ i, 0 < pi i),
    variance P (fun s ↦ ∑ i ∈ s, y i / pi i) =
      -(1 / 2 : ℝ) * ∑ i, ∑ j, (pij i j - pi i * pi j) * (y i / pi i - y j / pi j) ^ 2 := by
  sorry

/-- GAPS 105.73, finite-population correction for a simple random sample mean. -/
theorem gap105_73 {N : ℕ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (y : Fin N → ℝ) :
    let T := fun s : Finset (Fin N) ↦ (∑ i ∈ s, y i) / n;
    (∫ s, T s ∂sampleDesign N n) = popMean y ∧
      variance (sampleDesign N n) T = (1 - (n : ℝ) / N) * popVariance y / n := by
  sorry

/-- GAPS 105.73, the continuous Neyman allocation optimization. -/
theorem gap105_73_allocation {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (n : ℝ) (hn : 0 < n) (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hxsum : ∑ i, x i = n) :
    (∑ i, a i) ^ 2 / n ≤ ∑ i, a i ^ 2 / x i ∧
      ((∑ i, a i) ^ 2 / n = ∑ i, a i ^ 2 / x i ↔
        ∀ i, x i = n * a i / ∑ j, a j) := by
  sorry

end CKSD.Section105
