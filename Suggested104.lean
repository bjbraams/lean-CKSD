module

public import Suggested103
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Suggested statements for Section 104

Sources: `GAPS.md`, `SYNOPSIS104.md`, `STRUCTURE104.md`.
All theorem proofs are admitted. Finite-state sampler results and scalar score
matching are explicit scoped versions. No undefined SDE or particle-system
predicate is used in a theorem hypothesis.

Not represented: the general LAN version of 104.1 and the random expansion of 104.5;
104.15–20 (random probability measures, posterior consistency and inverse
sequence models), 104.31 (general Harris convergence), 104.37–39, 104.43–45 and 104.47–48 in their diffusion-law
forms (SDE and Fokker–Planck solution concepts), 104.49 (chain-transitive
limit sets), 104.51 and 104.53–60 (interacting particle/filter laws),
104.63 and 104.68 (reversed SDEs and Girsanov path laws), 104.75–76
(diffusion samplers and prescribed marginals), and 104.77 (path-space IPF).
The deterministic contraction and entropy-decay implications below do not
assert existence of a diffusion. The Langevin generator identity is an
infinitesimal statement, not an invariant-law construction.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section104

attribute [local instance] Classical.propDecidable

/-- Poisson likelihood as a real nonnegative mass, for a nonnegative intensity. -/
def poissonMass (θ : ℝ) (x : ℕ) : ℝ := Real.exp (-θ) * θ ^ x / Nat.factorial x

/-- Finite-state Metropolis acceptance, with acceptance one for a zero denominator. -/
def acceptance {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ)
    (x y : Fin s) : ℝ :=
  if π x * q x y = 0 then 1 else min 1 (π y * q y x / (π x * q x y))

/-- Finite-state Metropolis transition, including rejected proposals on the diagonal. -/
def metropolis {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  fun x y ↦ q x y * acceptance π q x y +
    if x = y then 1 - ∑ z, q x z * acceptance π q x z else 0

/-- One leapfrog step with identity mass matrix and a specified force. -/
def leapfrog {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : ℝ) (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  let p := z.2 - (h / 2) • g z.1
  let x := z.1 + h • p
  (x, p - (h / 2) • g x)

/-- GAPS 104.10, volume minimality of a highest-density region. -/
theorem gap104_10 {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : HasDensity P volume f) (k : ℝ) (hk : 0 < k)
    (C D : Set (EuclideanSpace ℝ (Fin d))) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hlow : {x | k < f x} ⊆ C) (hhigh : C ⊆ {x | k ≤ f x})
    (hmass : P C ≤ P D) : volume C ≤ volume D := by
  sorry

/-- GAPS 104.14, Tweedie's formula for normal means under an arbitrary probability prior. -/
theorem gap104_14_tweedie (π : Measure ℝ) [IsProbabilityMeasure π]
    (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    let m := fun t ↦ ∫ θ, gaussianPDFReal θ v t ∂π;
    (∫ θ, θ * gaussianPDFReal θ v x ∂π) / m x =
      x + (v : ℝ) * deriv (fun t ↦ Real.log (m t)) x := by
  sorry

/-- GAPS 104.14, the Poisson posterior-mean identity. -/
theorem gap104_14_poisson (π : Measure ℝ) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ θ ∂π, 0 < θ) (x : ℕ) :
    let m := fun j ↦ ∫ θ, poissonMass θ j ∂π;
    (∫ θ, θ * poissonMass θ x ∂π) / m x = (x + 1 : ℕ) * m (x + 1) / m x := by
  sorry

/-- GAPS 104.14, almost-sure consistency of Robbins' count-ratio estimator. -/
theorem gap104_14_robbins {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℕ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hiid : IID μ X P) (x : ℕ) (hx : 0 < P {x}) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((x + 1 : ℕ) : ℝ) *
      ((Finset.range n).filter (fun i ↦ X i ω = x + 1)).card /
      ((Finset.range n).filter (fun i ↦ X i ω = x)).card) atTop
      (𝓝 (((x + 1 : ℕ) : ℝ) * P.real {x + 1} / P.real {x})) := by
  sorry

/-- GAPS 104.22, finite-state Metropolis–Hastings: stochasticity, balance and invariance. -/
theorem gap104_22 {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1) :
    (∀ x y, 0 ≤ metropolis π q x y) ∧
      (∀ x, ∑ y, metropolis π q x y = 1) ∧
      (∀ x y, π x * metropolis π q x y = π y * metropolis π q y x) ∧
      ∀ y, (∑ x, π x * metropolis π q x y) = π y := by
  sorry

/-- GAPS 104.24, stationary finite-state Markov chain CLT with a positive transition matrix. -/
theorem gap104_24 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ}
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n))
    (π : Fin s → ℝ) (K : Matrix (Fin s) (Fin s) ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hK : ∀ x y, 0 < K x y) (hK1 : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, (∑ x, π x * K x y) = π y)
    (hlaw : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n, X i ω = path i} = π (path 0) *
        ∏ i ∈ Finset.range n, K (path i) (path (i + 1)))
    (f : Fin s → ℝ) :
    let m := ∑ x, π x * f x;
    let sigmaSq := variance μ (f ∘ X 0) +
      2 * ∑' k : ℕ, covariance μ (f ∘ X 0) (f ∘ X (k + 1));
    Summable (fun k : ℕ ↦ |covariance μ (f ∘ X 0) (f ∘ X (k + 1))|) ∧
      InLaw μ (fun n ω ↦ Real.sqrt n * (average (fun i ω ↦ f (X i ω)) n ω - m))
        (gaussianReal 0 (Real.toNNReal sigmaSq)) := by
  sorry

/-- GAPS 104.32, uniform convergence rate of a finite independence sampler. -/
theorem gap104_32 {s : ℕ} (π g : Fin s → ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hg : ∀ x, 0 < g x) (hg1 : ∑ x, g x = 1)
    (M : ℝ) (hM : 1 ≤ M) (hdom : ∀ x, π x ≤ M * g x)
    (n : ℕ) (x : Fin s) (A : Finset (Fin s)) :
    |(∑ y ∈ A, (metropolis π (fun _ y ↦ g y) ^ n) x y) - ∑ y ∈ A, π y| ≤
      (1 - 1 / M) ^ n := by
  sorry

/-- GAPS 104.35, reversibility and volume preservation of repeated leapfrog steps. -/
theorem gap104_35 {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (h : ℝ) (L : ℕ) :
    let R := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ (z.1, -z.2);
    MeasurePreserving ((leapfrog g h)^[L]) volume volume ∧
      ∀ z, (leapfrog g h)^[L] (R ((leapfrog g h)^[L] z)) = R z := by
  sorry

/-- GAPS 104.37, the scalar Langevin generator has zero Gibbs expectation on smooth tests. -/
theorem gap104_37_generator (V f : ℝ → ℝ) (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    let Z := ∫ x, Real.exp (-V x);
    ∀ (hZ : 0 < Z),
    ∀ (hi : Integrable (fun x ↦ Real.exp (-V x)) volume),
    (∫ x, (deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x) / Z) = 0 := by
  sorry

/-- GAPS 104.38, pathwise synchronous contraction from a common additive forcing. -/
theorem gap104_38 {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hb : Continuous b)
    (m : ℝ) (hm : 0 < m)
    (hmono : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (b x - b y) (x - y))
    (x y : ℝ → EuclideanSpace ℝ (Fin d)) (hx : Continuous x) (hy : Continuous y)
    (heq : ∀ t ≥ 0, x t - y t = x 0 - y 0 - ∫ s in (0 : ℝ)..t, b (x s) - b (y s)) :
    ∀ t ≥ 0, ‖x t - y t‖ ≤ Real.exp (-m * t) * ‖x 0 - y 0‖ := by
  sorry

/-- GAPS 104.40, almost-sure Robbins–Monro convergence under bounded conditional noise variance. -/
theorem gap104_40 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (θ M : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (ha : ∀ n, Measurable[F n] (θ n)) (hM : ∀ n, Measurable[F n] (M n))
    (hθ2 : MemLp (θ 0) 2 μ) (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hzero : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0)
    (K : ℝ) (hnoise : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ] fun _ ↦ K)
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ≥0) (hL : LipschitzWith L h) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hz : h θ₀ = 0) (m : ℝ) (hm : 0 < m)
    (hdrift : ∀ x, m * ‖x - θ₀‖ ^ 2 ≤ inner ℝ (x - θ₀) (h x))
    (a : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (ha2 : Summable (fun n ↦ a n ^ 2))
    (haDiverges : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ θ n ω) atTop (𝓝 θ₀) := by
  sorry

/-- GAPS 104.41, the entropy-decay consequence of dissipation and a log-Sobolev bound. -/
theorem gap104_41 (E I : ℝ → ℝ) (m : ℝ) (hm : 0 < m)
    (hE : ContinuousOn E (Ici 0))
    (hder : ∀ t > 0, HasDerivAt E (-I t) t)
    (hlsi : ∀ t > 0, 2 * m * E t ≤ I t) :
    ∀ t ≥ 0, E t ≤ Real.exp (-2 * m * t) * E 0 := by
  sorry

/-- GAPS 104.64, scalar score-matching identity for compactly supported fitted scores. -/
theorem gap104_64 (P : Measure ℝ) [IsProbabilityMeasure P] (p g : ℝ → ℝ)
    (hp : HasDensity P volume p) (hpos : ∀ x, 0 < p x)
    (hp1 : ContDiff ℝ 1 p) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hscore : Integrable (fun x ↦ (deriv p x / p x) ^ 2) P) :
    (∫ x, (g x - deriv p x / p x) ^ 2 / 2 ∂P) =
      (∫ x, g x ^ 2 / 2 + deriv g x ∂P) +
        ∫ x, (deriv p x / p x) ^ 2 / 2 ∂P := by
  sorry

/-- GAPS 104.72: action bounds for the barycentric velocity of an arbitrary straight coupling. -/
theorem gap104_72 {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure π] (h2 : MemLp id 2 π)
    (v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hv : Measurable (Function.uncurry v)) :
    let Xt := fun t (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      (1 - t) • z.1 + t • z.2;
    ∀ (hcond : ∀ t ∈ Icc (0 : ℝ) 1,
      (fun z ↦ v t (Xt t z)) =ᵐ[π]
        π[(fun z ↦ z.2 - z.1) | (inferInstance : MeasurableSpace
          (EuclideanSpace ℝ (Fin d))).comap (Xt t)]),
    (TauCeti.wassersteinEDist 2 (π.map Prod.fst) (π.map Prod.snd)).toReal ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π ∧
    (∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) ≤
      ∫ z, ‖z.2 - z.1‖ ^ 2 ∂π := by
  sorry

/-- Posterior of a normal location with known variance, given a proper prior density.
Likelihood factors independent of the parameter cancel in this normalization. -/
def normalPosterior (prior : ℝ → ℝ) (v : ℝ≥0) (n : ℕ) (mean : ℝ) : Measure ℝ :=
  let density := fun theta ↦ prior theta * Real.exp (-(n : ℝ) * (theta - mean) ^ 2 / (2 * v))
  (ENNReal.ofReal (∫ theta, density theta))⁻¹ • volume.withDensity (fun theta ↦ ENNReal.ofReal (density theta))

/-- GAPS 104.1, Bernstein–von Mises for the scalar normal location model with any
proper prior density continuous and positive at the true mean. -/
theorem gap104_1 {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (theta₀ : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (X : ℕ → Ω → ℝ) (hiid : IID mu X (gaussianReal theta₀ v))
    (prior : ℝ → ℝ) (hm : Measurable prior) (hi : Integrable prior volume)
    (hpos : ∀ theta, 0 ≤ prior theta) (h1 : (∫ theta, prior theta) = 1)
    (hc : ContinuousAt prior theta₀) (htrue : 0 < prior theta₀) :
    InProbability mu (fun n w ↦ Section103.tv
      ((normalPosterior prior v n (average X n w)).map
        (fun theta ↦ Real.sqrt n * (theta - average X n w)))
      (gaussianReal 0 v)) 0 := by
  sorry

/-- GAPS 104.5, deterministic Laplace core on a compact parameter region.
This states the analytic approximation; the random-likelihood and BIC
conclusions of the source require its additional probabilistic hypotheses. -/
theorem gap104_5 {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (m : EuclideanSpace ℝ (Fin d)) (hm : m ∈ interior K)
    (f a : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiff ℝ 2 f)
    (ha : ContinuousOn a K) (hapos : 0 < a m) (hmin : f m = 0)
    (huniq : ∀ x ∈ K, x ≠ m → 0 < f x)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosDef)
    (hhess : ∀ u v, fderiv ℝ (fderiv ℝ f) m u v =
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) H v)) :
    Tendsto (fun n : ℕ ↦ Real.rpow n ((d : ℝ) / 2) *
      ∫ x in K, a x * Real.exp (-(n : ℝ) * f x)) atTop
      (𝓝 (a m * Real.rpow (2 * Real.pi) ((d : ℝ) / 2) / Real.sqrt H.det)) := by
  sorry

end CKSD.Section104
