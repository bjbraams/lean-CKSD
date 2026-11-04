module

public import Suggested101

/-!
# Suggested statements for Section 102

Sources: `GAPS.md`, `SYNOPSIS102.md`, `STRUCTURE102.md`.
All proofs are `sorry`. Each docstring gives its gap identifier and scope.
The finite-rank quadratic-kernel limit below does not cover infinite Gaussian
chaos. The compact argmax statement covers a deterministic limiting criterion.

Not represented: 102.2 (Wald consistency); the vector versions of 102.3–4;
102.11 (constrained likelihood geometry), 102.15–17 and 102.34 (limit
experiments and regular estimators), 102.24–25 (outer-probability empirical
process hypotheses), 102.28 (tangential Hadamard differentiation of possibly
nonmeasurable processes), 102.39 (training sigma-algebras for cross-fitting),
102.41 (adaptive estimator construction), 102.48 (convex regression processes),
102.50 (moment-indexed Edgeworth coefficients), 102.52 (outer weak convergence
of conditional process laws), 102.55 (canonical density versions in the
saddlepoint expansion), 102.58 (a category of congruent simplex embeddings),
102.60 (conditional higher-order expansion and quantile conventions).
These families need a specified formal statistical/process framework.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section102

attribute [local instance] Classical.propDecidable

/-- Empirical distribution function of the first `n` real observations. -/
def ecdf {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  ((Finset.range n).filter (fun i ↦ X i ω ≤ t)).card / (n : ℝ)

/-- Left empirical quantile; only used for nonempty samples and probabilities in `(0,1)`. -/
def quantile {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (p : ℝ) : ℝ :=
  sInf {t | p ≤ ecdf X n ω t}

/-- The ordered-injection formula for a symmetric U-statistic of order `m`. -/
def ustat {E : Type*} (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) : ℝ :=
  ((n.descFactorial m : ℕ) : ℝ)⁻¹ *
    ∑ f ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective,
      h (x ∘ f)

/-- Contiguity of sequences of laws on a common measurable space. -/
def Contiguous {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) : Prop :=
  ∀ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) →
    Tendsto (fun n ↦ (P n).real (A n)) atTop (𝓝 0) →
    Tendsto (fun n ↦ (Q n).real (A n)) atTop (𝓝 0)

/-- The Kolmogorov distance, with the CDF normalization for probability laws. -/
def kolmogorov (P Q : Measure ℝ) : ℝ := sSup (range fun t ↦ |cdf P t - cdf Q t|)

/-- The clipped Huber score. -/
def huber (k x : ℝ) : ℝ := max (-k) (min k x)

/-- GAPS 102.1: the delta method and its stochastic linearization in Banach spaces. -/
theorem gap102_1 {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E)
    (hT : ∀ n, Measurable (T n)) (θ : E) (ν : Measure E) [IsProbabilityMeasure ν]
    (g : E → F) (hg : Measurable g) (D : E →L[ℝ] F) (hd : HasFDerivAt g D θ)
    (hlim : InLaw μ (fun n ω ↦ Real.sqrt n • (T n ω - θ)) ν) :
    InLaw μ (fun n ω ↦ Real.sqrt n • (g (T n ω) - g θ)) (ν.map D) ∧
      InProbability μ (fun n ω ↦
        Real.sqrt n • (g (T n ω) - g θ) - D (Real.sqrt n • (T n ω - θ))) 0 := by
  sorry

/-- GAPS 102.6: asymptotic normality of a sample quantile. -/
theorem gap102_6 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    InLaw μ (fun n ω ↦ Real.sqrt n * (quantile X n ω p - q))
      (gaussianReal 0 (Real.toNNReal (p * (1 - p) / f ^ 2))) := by
  sorry

/-- GAPS 102.7: the first-order Bahadur representation. -/
theorem gap102_7 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (p q f : ℝ)
    (hp : p ∈ Ioo 0 1) (hq : cdf P q = p) (hf : 0 < f)
    (hd : HasDerivAt (cdf P) f q) :
    InProbability μ (fun n ω ↦ Real.sqrt n *
      (quantile X n ω p - q - (p - ecdf X n ω q) / f)) 0 := by
  sorry

/-- GAPS 102.8: the nondegenerate U-statistic CLT, with its first projection. -/
theorem gap102_8 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IID μ X P) (m : ℕ)
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) :
    let θ := ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P);
    let g := fun x ↦ (∫ y, h (Fin.cases x y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ;
    ∀ (hv : 0 < variance P g),
    InLaw μ (fun n ω ↦ Real.sqrt n *
      (ustat (m + 1) n h (fun i ↦ X i.val ω) - θ))
      (gaussianReal 0 (Real.toNNReal (((m + 1 : ℕ) : ℝ) ^ 2 * variance P g))) := by
  sorry

/-- GAPS 102.12: Le Cam's first lemma, for absolutely continuous alternatives. -/
theorem gap102_12 {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (hac : ∀ n, Q n ≪ P n)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlim : Weakly (fun n ↦ (P n).map (fun ω ↦ ((Q n).rnDeriv (P n) ω).toReal)) ν)
    (hint : Integrable id ν) (hmean : (∫ x, x ∂ν) = 1) :
    Contiguous P Q := by
  sorry

/-- GAPS 102.14: the change-of-law form of the third lemma.
Taking a joint Gaussian limit gives the mean shift stated in GAPS. -/
theorem gap102_14 {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P Q : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (hQ : ∀ n, IsProbabilityMeasure (Q n)) (S : ℕ → Ω → E) (Λ : ℕ → Ω → ℝ)
    (hS : ∀ n, Measurable (S n)) (hΛ : ∀ n, Measurable (Λ n))
    (hrn : ∀ n, Q n = (P n).withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (Λ n ω))))
    (ν : Measure (E × ℝ)) [IsProbabilityMeasure ν]
    (hlim : Weakly (fun n ↦ (P n).map (fun ω ↦ (S n ω, Λ n ω))) ν)
    (hint : Integrable (fun z ↦ Real.exp z.2) ν)
    (hmean : (∫ z, Real.exp z.2 ∂ν) = 1) :
    Weakly (fun n ↦ (Q n).map (S n))
      ((ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp z.2)).map Prod.fst) := by
  sorry

/-- GAPS 102.21, local power calculation for a normal limit with mean shift. -/
theorem gap102_21 {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → Measure Ω) (hP : ∀ n, IsProbabilityMeasure (P n))
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (a z : ℝ)
    (hlim : Weakly (fun n ↦ (P n).map (T n)) (gaussianReal a 1)) :
    Tendsto (fun n ↦ (P n).real {ω | z < T n ω}) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) (z - a))) := by
  sorry

/-- GAPS 102.23: consistency from uniform convergence and a separated maximum.
Pointwise bounds avoid any unmentioned measurability of a supremum. -/
theorem gap102_23 {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace Θ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Θ → ℝ) (Mn : ℕ → Ω → Θ → ℝ) (θ₀ : Θ) (T : ℕ → Ω → Θ)
    (hT : ∀ n, Measurable (T n)) (e r : ℕ → Ω → ℝ)
    (he : InProbability μ e 0) (hr : InProbability μ r 0)
    (hsep : ∀ ε > 0, ∃ δ > 0, ∀ θ, ε ≤ dist θ θ₀ → M θ ≤ M θ₀ - δ)
    (hunif : ∀ n, ∀ᵐ ω ∂μ, ∀ θ, |Mn n ω θ - M θ| ≤ e n ω)
    (hopt : ∀ n, ∀ᵐ ω ∂μ, Mn n ω θ₀ - r n ω ≤ Mn n ω (T n ω)) :
    InProbability μ T θ₀ := by
  sorry

/-- GAPS 102.29: order-two Hoeffding decomposition, including the exact variance. -/
theorem gap102_29 {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (h : E × E → ℝ)
    (hm : Measurable h) (h2 : MemLp h 2 (P.prod P)) (hs : ∀ x y, h (x,y) = h (y,x))
    (n : ℕ) (hn : 2 ≤ n) :
    let θ := ∫ z, h z ∂P.prod P;
    let g := fun x ↦ (∫ y, h (x,y) ∂P) - θ;
    let q := fun z : E × E ↦ h z - θ - g z.1 - g z.2;
    let U := fun x : Fin n → E ↦ ustat 2 n (fun z ↦ h (z 0, z 1)) x;
    (∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P),
      U x - θ = 2 / n * (∑ i, g (x i)) +
        ustat 2 n (fun z ↦ q (z 0, z 1)) x) ∧
    variance (Measure.pi fun _ : Fin n ↦ P) U =
      4 / n * variance P g + 2 / ((n : ℝ) * (n - 1 : ℕ)) * ∫ z, q z ^ 2 ∂P.prod P := by
  sorry

/-- GAPS 102.30: finite-rank degenerate quadratic kernels have Gaussian-chaos limits. -/
theorem gap102_30 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IID μ X P) (r : ℕ) (a : Fin r → ℝ)
    (e : Fin r → E → ℝ) (he : ∀ j, MemLp (e j) 2 P)
    (he0 : ∀ j, (∫ x, e j x ∂P) = 0)
    (hortho : ∀ i j, (∫ x, e i x * e j x ∂P) = if i = j then 1 else 0) :
    InLaw μ (fun n ω ↦ (n : ℝ) * ustat 2 n
      (fun z ↦ ∑ j, a j * e j (z 0) * e j (z 1)) (fun i ↦ X i.val ω))
      ((Measure.pi fun _ : Fin r ↦ gaussianReal 0 1).map
        (fun z ↦ ∑ j, a j * (z j ^ 2 - 1))) := by
  sorry

/-- GAPS 102.31: Pearson's test for a simple multinomial null. -/
theorem gap102_31 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (X : ℕ → Ω → Fin k)
    (hiid : IID μ X (∑ i, ENNReal.ofReal (p i) • Measure.dirac i)) :
    InLaw μ (fun n ω ↦ ∑ i : Fin k,
      (((Finset.range n).filter (fun j ↦ X j ω = i)).card - (n : ℝ) * p i) ^ 2 /
        ((n : ℝ) * p i)) (TauCeti.Probability.chiSquaredMeasure (k - 1 : ℕ)) := by
  sorry

/-- GAPS 102.33, compact deterministic-limit scope of the argmax theorem. -/
theorem gap102_33 {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [MetricSpace H] [CompactSpace H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : H → ℝ) (hc : Continuous M) (θ : H) (huniq : ∀ h, h ≠ θ → M h < M θ)
    (Mn : ℕ → Ω → H → ℝ) (T : ℕ → Ω → H) (hT : ∀ n, Measurable (T n))
    (e : ℕ → Ω → ℝ) (he : InProbability μ e 0)
    (hu : ∀ n, ∀ᵐ ω ∂μ, ∀ h, |Mn n ω h - M h| ≤ e n ω)
    (ho : ∀ n, ∀ᵐ ω ∂μ, ∀ h, Mn n ω h ≤ Mn n ω (T n ω)) :
    InProbability μ T θ := by
  sorry

/-- GAPS 102.44, Hampel optimality part of the Huber statement. -/
theorem gap102_44 (k : ℝ) (hk : 0 < k) :
    let G := gaussianReal 0 1;
    let a := 2 * cdf G k - 1;
    ∀ (φ : ℝ → ℝ),
    ∀ (hm : Measurable φ),
    ∀ (hbound : ∀ x, |φ x| ≤ k / a),
    ∀ (h0 : (∫ x, φ x ∂G) = 0),
    ∀ (h1 : (∫ x, x * φ x ∂G) = 1),
    (∫ x, (huber k x / a) ^ 2 ∂G) ≤ ∫ x, φ x ^ 2 ∂G := by
  sorry

/-- GAPS 102.49: uniform one-term Edgeworth expansion under the stated nonlattice condition. -/
theorem gap102_49 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (h3 : Integrable (fun x ↦ |x| ^ 3) P)
    (h0 : (∫ x, x ∂P) = 0) (h1 : (∫ x, x ^ 2 ∂P) = 1)
    (hnonlattice : ∀ a : ℝ, ∀ b > 0, P (range fun j : ℤ ↦ a + b * j) < 1) :
    let ρ := ∫ x, x ^ 3 ∂P;
    ∃ e : ℕ → ℝ, Tendsto (fun n : ℕ ↦ Real.sqrt n * e n) atTop (𝓝 0) ∧
      ∀ (n : ℕ), n ≥ 1 → ∀ t, |μ.real {ω | Real.sqrt n * average X n ω ≤ t} -
        (cdf (gaussianReal 0 1) t - gaussianPDFReal 0 1 t * (t ^ 2 - 1) *
          ρ / (6 * Real.sqrt n))| ≤ e n := by
  sorry

/-- GAPS 102.51: conditional bootstrap consistency of the mean, for positive variance. -/
theorem gap102_51 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) :
    InProbability μ (fun n ω ↦ kolmogorov
      ((Measure.pi fun _ : Fin n ↦ empirical n (fun i ↦ X i.val ω)).map
        (fun y : Fin n → ℝ ↦ Real.sqrt n * ((∑ i, y i) / n - average X n ω)))
      (gaussianReal 0 (Real.toNNReal (variance P id)))) 0 := by
  sorry

/-- GAPS 102.3, scalar smooth likelihood-score roots and their efficient expansion.
`ell` is the per-observation log likelihood; the score/information moment
identities and the local third-derivative envelope are explicit hypotheses. -/
theorem gap102_3 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IID mu X P) (ell : ℝ → E → ℝ)
    (hm : ∀ theta, Measurable (ell theta)) (hsmooth : ∀ x, ContDiff ℝ 3 (fun theta ↦ ell theta x))
    (theta₀ I : ℝ) (hI : 0 < I) (r : ℝ) (hr : 0 < r) (M : E → ℝ)
    (hM : Integrable M P)
    (henv : ∀ x theta, |theta - theta₀| < r →
      |deriv (deriv (deriv (fun t ↦ ell t x))) theta| ≤ M x)
    (hscore : MemLp (fun x ↦ deriv (fun t ↦ ell t x) theta₀) 2 P)
    (hmean : (∫ x, deriv (fun t ↦ ell t x) theta₀ ∂P) = 0)
    (hvar : (∫ x, deriv (fun t ↦ ell t x) theta₀ ^ 2 ∂P) = I)
    (hhess : Integrable (fun x ↦ deriv (deriv (fun t ↦ ell t x)) theta₀) P)
    (hinfo : (∫ x, deriv (deriv (fun t ↦ ell t x)) theta₀ ∂P) = -I)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : InProbability mu T theta₀)
    (hroot : ∀ n : ℕ, 1 ≤ n → ∀ᵐ w ∂mu,
      (∑ i ∈ Finset.range n, deriv (fun t ↦ ell t (X i w)) (T n w)) = 0) :
    InProbability mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) -
      (I * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        deriv (fun t ↦ ell t (X i w)) theta₀) 0 ∧
      InLaw mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal I⁻¹)) := by
  sorry

/-- GAPS 102.4, the scalar Z-estimator theorem under a square-integrable Lipschitz envelope. -/
theorem gap102_4 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IID mu X P) (psi : ℝ → E → ℝ)
    (hm : Measurable (Function.uncurry psi)) (theta₀ D : ℝ) (hD : D ≠ 0)
    (hpsi : MemLp (psi theta₀) 2 P) (h0 : (∫ x, psi theta₀ x ∂P) = 0)
    (hd : HasDerivAt (fun theta ↦ ∫ x, psi theta x ∂P) D theta₀)
    (r : ℝ) (hr : 0 < r) (M : E → ℝ) (hM : MemLp M 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n)) (hcons : InProbability mu T theta₀)
    (hroot : InProbability mu (fun n w ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, psi (T n w) (X i w)) 0) :
    InProbability mu (fun n w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) 0 ∧
      InLaw mu (fun n w ↦ Real.sqrt n * (T n w - theta₀))
        (gaussianReal 0 (Real.toNNReal (variance P (psi theta₀) / D ^ 2))) := by
  sorry

/-- GAPS 102.13, scalar DQM implies LAN, with common strictly positive densities. -/
theorem gap102_13 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (nu : Measure E) [SigmaFinite nu]
    (P : ℝ → Measure E) (hP : ∀ theta, IsProbabilityMeasure (P theta))
    (f : ℝ → E → ℝ) (hf : ∀ theta, HasDensity (P theta) nu (f theta))
    (hpos : ∀ theta x, 0 < f theta x) (theta₀ : ℝ) (score : E → ℝ)
    (hs : Measurable score) (hs2 : MemLp score 2 (P theta₀))
    (hs0 : (∫ x, score x ∂P theta₀) = 0)
    (hdqm : Asymptotics.IsLittleO (𝓝 0)
      (fun h : ℝ ↦ ∫ x, (Real.sqrt (f (theta₀ + h) x) - Real.sqrt (f theta₀ x) -
        h / 2 * score x * Real.sqrt (f theta₀ x)) ^ 2 ∂nu) (fun h : ℝ ↦ h ^ 2))
    (X : ℕ → Ω → E) (hiid : IID mu X (P theta₀)) :
    let I := ∫ x, score x ^ 2 ∂P theta₀;
    0 < I →
      InLaw mu (fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, score (X i w))
        (gaussianReal 0 (Real.toNNReal I)) ∧
      ∀ h : ℝ, InProbability mu (fun n w ↦
        (∑ i ∈ Finset.range n, Real.log (f (theta₀ + h / Real.sqrt n) (X i w) / f theta₀ (X i w))) -
          h / Real.sqrt n * (∑ i ∈ Finset.range n, score (X i w)) + h ^ 2 * I / 2) 0 := by
  sorry

end CKSD.Section102
