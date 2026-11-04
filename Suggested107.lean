module

public import Suggested106

/-!
# Suggested statements for Section 107

Sources: `GAPS.md`, `SYNOPSIS107.md`, `STRUCTURE107.md`.
All proofs are admitted. Learning-theoretic statements specify their measurable
losses and sampling law. Results for finite classes, finite-width differentiable
models, or fixed-policy planning are explicitly scoped; they do not claim the
VC, infinite-width, or generative-sampling conclusions of a larger entry.

Not represented: the general PAC equivalence in 107.1; 107.10 (margin-class
contraction), 107.13–14 (localized kernel and nearest-neighbor estimators),
107.16 (unordered k-means center sets), 107.19–20 and 107.23 (graphical/forest
models), 107.24 (the full adaptive boosting algorithm), 107.27 (junction trees),
107.28–29 and 107.35–37 (network/Sobolev architecture classes), 107.39
(infinite-width random initialization), 107.41–43 and 107.47 (random-graph
models and recovery criteria), 107.49 and 107.51–52 (sequential bandit laws),
107.59's sampling rate, 107.60's stochastic TD convergence, 107.61–63
(policy-gradient and bandit interaction models), 107.65's advanced adaptive
composition, 107.66 (private minimax experiments), 107.74 (adaptive threshold
query streams). The single-release part of 107.75 is included.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD.Section107

attribute [local instance] Classical.propDecidable

/-- Finite-class empirical Rademacher complexity, using a uniform sign vector. -/
def rad {H X : Type*} [Fintype H] (n : ℕ) (f : H → X → ℝ) (x : Fin n → X) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * ∑ σ : Fin n → Bool,
    sSup (range fun h ↦ (∑ i, (if σ i then (1 : ℝ) else -1) * f h (x i)) / n)

/-- Conditional binary-classification risk under a specified regression function. -/
def classRisk {X : Type*} [MeasurableSpace X] (P : Measure X)
    (η : X → ℝ) (g : X → Bool) : ℝ :=
  ∫ x, if g x then 1 - η x else η x ∂P

/-- Exponential-weights probabilities after `t` losses. -/
def hedge {K : ℕ} (loss : ℕ → Fin K → ℝ) (eta : ℝ) (t : ℕ) (i : Fin K) : ℝ :=
  Real.exp (-eta * ∑ s ∈ Finset.range t, loss s i) /
    (∑ j, Real.exp (-eta * ∑ s ∈ Finset.range t, loss s j))

/-- Privacy of a kernel for a supplied symmetric neighboring-data relation. -/
def Private {D Y : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    (R : D → D → Prop) (epsilon delta : ℝ) (M : Kernel D Y) : Prop :=
  ∀ d d', R d d' → ∀ A : Set Y, MeasurableSet A →
    M d A ≤ ENNReal.ofReal (Real.exp epsilon) * M d' A + ENNReal.ofReal delta

/-- A finite discounted decision model, using real stochastic transition rows. -/
structure MDP (s a : ℕ) where
  /-- Discount in the open unit interval. -/
  gamma : ℝ
  /-- Positive discount. -/
  gamma_pos : 0 < gamma
  /-- Strict discount. -/
  gamma_lt_one : gamma < 1
  /-- Expected one-step reward. -/
  reward : Fin s → Fin a → ℝ
  /-- Transition probabilities. -/
  transition : Fin s → Fin a → Fin s → ℝ
  /-- Nonnegative transition probabilities. -/
  transition_nonneg : ∀ i b j, 0 ≤ transition i b j
  /-- Transition rows sum to one. -/
  transition_sum : ∀ i b, ∑ j, transition i b j = 1

/-- The state-value Bellman optimality operator of a finite model. -/
def bellman {s a : ℕ} (M : MDP s a) (V : Fin s → ℝ) (i : Fin s) : ℝ :=
  sSup (range fun b : Fin a ↦ M.reward i b + M.gamma * ∑ j, M.transition i b j * V j)

/-- GAPS 107.1, finite-class uniform risk concentration (a scoped PAC upper bound). -/
theorem gap107_1 {H X : Type*} [Fintype H] [Nonempty H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (he : 0 < epsilon) :
    (Measure.pi fun _ : Fin n ↦ P).real {x | ∃ h,
      |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} ≤
      2 * Fintype.card H * Real.exp (-2 * n * epsilon ^ 2) := by
  sorry

/-- GAPS 107.2, symmetrization and the expected-complexity bound for a finite class. -/
theorem gap107_2 {H X : Type*} [Fintype H] [Nonempty H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    let Pn := Measure.pi fun _ : Fin n ↦ P;
    let R := ∫ x, rad n f x ∂Pn;
    (∫ x, sSup (range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P) ∂Pn) ≤ 2 * R ∧
      Pn.real {x | 2 * R + Real.sqrt (Real.log (2 / delta) / (2 * n)) <
        sSup (range fun h ↦ |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P|)} ≤ delta := by
  sorry

/-- GAPS 107.5: the exponential-weights regret bound, for any positive learning rate. -/
theorem gap107_5 {K : ℕ} (hK : 0 < K) (loss : ℕ → Fin K → ℝ)
    (hloss : ∀ t i, loss t i ∈ Icc 0 1) (eta : ℝ) (he : 0 < eta)
    (T : ℕ) (i : Fin K) :
    (∑ t ∈ Finset.range T, ∑ j, hedge loss eta t j * loss t j) -
      (∑ t ∈ Finset.range T, loss t i) ≤ Real.log K / eta + eta * T / 8 := by
  sorry

/-- GAPS 107.6: the exchangeable-rank coverage assertion, with ties allowed. -/
theorem gap107_6 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin (n + 1) → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      P.map (fun ω i ↦ S (σ i) ω) = P.map (fun ω i ↦ S i ω))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let C := {ω | ((Finset.univ : Finset (Fin n)).filter
      (fun i ↦ S i.castSucc ω < S (Fin.last n) ω)).card < k};
    (k : ℝ) / (n + 1) ≤ P.real C ∧
      ((∀ᵐ ω ∂P, Function.Injective (fun i ↦ S i ω)) → P.real C = (k : ℝ) / (n + 1)) := by
  sorry

/-- GAPS 107.7, finite-support no-free-lunch bound; taking arbitrarily large `m`
gives the infinite-feature-space assertion. -/
theorem gap107_7 (n m : ℕ) (hm : 0 < m)
    (learn : (Fin n → Fin m × Bool) → Fin m → Bool) :
    ∃ label : Fin m → Bool,
      (1 - (n : ℝ) / m) / 2 ≤
        (∑ x : Fin n → Fin m,
          ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) / m) /
          (m : ℝ) ^ n := by
  sorry

/-- GAPS 107.8: the exact excess Bayes classification risk identity. -/
theorem gap107_8 {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η : X → ℝ) (hη : Measurable η)
    (hrange : ∀ x, η x ∈ Icc 0 1) (g : X → Bool) (hg : Measurable g) :
    let star := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x);
    classRisk P η g - classRisk P η star =
      ∫ x, if g x ≠ star x then |2 * η x - 1| else 0 ∂P := by
  sorry

/-- GAPS 107.8: the plugin classification risk bound. -/
theorem gap107_8_plugin {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η a : X → ℝ)
    (hη : Measurable η) (ha : Measurable a) (hi : Integrable a P)
    (hrange : ∀ x, η x ∈ Icc 0 1) :
    classRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ a x)) -
      classRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)) ≤
        2 * ∫ x, |a x - η x| ∂P := by
  sorry

/-- GAPS 107.11, pointwise classification calibration of a convex surrogate. -/
theorem gap107_11 (phi : ℝ → ℝ) (hc : ConvexOn ℝ univ phi)
    (hmono : Monotone phi) (d : ℝ) (hd : HasDerivAt phi d 0) (hdpos : 0 < d)
    (eta : ℝ) (he : eta ∈ Ioo 0 1) (hne : eta ≠ 1 / 2)
    (u : ℝ) (hmin : ∀ v, eta * phi (-u) + (1 - eta) * phi u ≤
      eta * phi (-v) + (1 - eta) * phi v) : 0 < (eta - 1 / 2) * u := by
  sorry

/-- GAPS 107.12: generalization of a measurable uniformly stable algorithm. -/
theorem gap107_12 {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (loss : (Fin n → X) → X → ℝ) (hm : Measurable (Function.uncurry loss))
    (beta M : ℝ) (hb : 0 ≤ beta) (hM : 0 ≤ M) (hl : ∀ x z, loss x z ∈ Icc 0 M)
    (hstable : ∀ x y, (∃ i : Fin n, ∀ j, j ≠ i → x j = y j) →
      ∀ z, |loss x z - loss y z| ≤ beta)
    (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    (Measure.pi fun _ : Fin n ↦ P).real {x |
      (∑ i, loss x (x i)) / n + beta + (2 * n * beta + M) *
        Real.sqrt (Real.log (1 / delta) / (2 * n)) < ∫ z, loss x z ∂P} ≤ delta := by
  sorry

/-- GAPS 107.26, finite-state entropy variational formula for the log partition function. -/
theorem gap107_26 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    let Z := ∑ i, Real.exp (a i);
    (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      (∑ i, (w i * a i - w i * Real.log (w i))) ≤ Real.log Z) ∧
      (∑ i, ((Real.exp (a i) / Z) * a i -
        (Real.exp (a i) / Z) * Real.log (Real.exp (a i) / Z))) = Real.log Z := by
  sorry

/-- GAPS 107.26, the zero-temperature limit of a finite log partition function. -/
theorem gap107_26_zeroTemperature {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    Tendsto (fun beta : ℝ ↦ Real.log (∑ i, Real.exp (beta * a i)) / beta)
      atTop (𝓝 (sSup (range a))) := by
  sorry

/-- GAPS 107.30, finite-width tangent-kernel training dynamics for a differentiable model. -/
theorem gap107_30 {p n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n))
    (theta : ℝ → EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (D : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf : HasFDerivAt f D (theta t))
    (hflow : HasDerivAt theta (-((n : ℝ)⁻¹) • D.adjoint (f (theta t) - y)) t) :
    HasDerivAt (f ∘ theta) (-((n : ℝ)⁻¹) • D (D.adjoint (f (theta t) - y))) t := by
  sorry

/-- GAPS 107.31, the underparameterized ridgeless risk with Gaussian noise. -/
theorem gap107_31 {n p : ℕ} (hn : p + 1 < n)
    (beta : EuclideanSpace ℝ (Fin p)) (v : ℝ≥0) :
    let P := (Measure.pi fun _ : Fin n ↦ stdGaussian (EuclideanSpace ℝ (Fin p))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)));
    let A := fun x : Fin n → EuclideanSpace ℝ (Fin p) ↦ Matrix.of (fun i j ↦ x i j);
    let fit := fun z : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin n) ↦
      Matrix.toEuclideanLin (𝕜 := ℝ) (((A z.1).transpose) * A z.1)⁻¹
        (Matrix.toEuclideanLin (𝕜 := ℝ) ((A z.1).transpose)
          (Matrix.toEuclideanLin (𝕜 := ℝ) (A z.1) beta + Real.sqrt v • z.2));
    (∫ z, ‖fit z - beta‖ ^ 2 ∂P) = (v : ℝ) * p / (n - p - 1 : ℕ) := by
  sorry

/-- GAPS 107.40, least-squares gradient descent and the preserved nullspace component. -/
theorem gap107_40 {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) (theta₀ : EuclideanSpace ℝ (Fin p))
    (eta : ℝ) (he : 0 < eta) (hstep : eta * ‖A‖ ^ 2 < 2) :
    let update := fun x ↦ x - eta • A.adjoint (A x - y);
    ∃ thetaStar, A.adjoint (A thetaStar - y) = 0 ∧
      thetaStar - theta₀ ∈ LinearMap.range A.adjoint.toLinearMap ∧
      Tendsto (fun t : ℕ ↦ update^[t] theta₀) atTop (𝓝 thetaStar) := by
  sorry

/-- Number of plays of an arm before time `t`. -/
def plays {Ω : Type*} {K : ℕ} (A : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter fun j ↦ A j ω = i).card

/-- Prefix empirical reward average for one arm. -/
def armAverage {Ω : Type*} {K : ℕ} (R : Fin K → ℕ → Ω → ℝ)
    (i : Fin K) (n : ℕ) (ω : Ω) : ℝ := (∑ j ∈ Finset.range n, R i j ω) / n

/-- GAPS 107.50: UCB1 regret, with prefix rewards and all tie choices explicit. -/
theorem gap107_50 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (hK : 2 ≤ K)
    (R : Fin K → ℕ → Ω → ℝ) (hm : ∀ i j, Measurable (R i j))
    (hb : ∀ i j ω, R i j ω ∈ Icc 0 1)
    (hind : iIndepFun (fun z : Fin K × ℕ ↦ R z.1 z.2) P)
    (hlaw : ∀ i j, P.map (R i j) = P.map (R i 0)) :
    let mu := fun i ↦ ∫ ω, R i 0 ω ∂P;
    ∀ (star : Fin K),
    ∀ (hstar : ∀ i, mu i ≤ mu star),
    ∀ (A : ℕ → Ω → Fin K),
    ∀ (hA : ∀ t, Measurable (A t)),
    ∀ (hinit : ∀ t : ℕ, ∀ ht : t < K, ∀ ω, A t ω = ⟨t, ht⟩),
    let index := fun t i ω ↦ armAverage R i (plays A i t ω) ω +
      Real.sqrt (2 * Real.log t / plays A i t ω);
    ∀ (hucb : ∀ t ≥ K, ∀ ω i, index t i ω ≤ index t (A t ω) ω),
    ∀ (T : ℕ),
    ∀ (hT : K ≤ T),
    (∫ ω, ∑ t ∈ Finset.range T, (mu star - mu (A t ω)) ∂P) ≤
      8 * (∑ i, if mu i < mu star then Real.log T / (mu star - mu i) else 0) +
        (1 + Real.pi ^ 2 / 3) * ∑ i, (mu star - mu i) := by
  sorry

/-- GAPS 107.54, bounded-noise asynchronous stochastic approximation for a contraction.
The tabular Q-learning application uses the Bellman operator and visited-pair steps. -/
theorem gap107_54 {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (T : (Fin p → ℝ) → (Fin p → ℝ)) (gamma : ℝ≥0) (hg : gamma < 1)
    (hc : LipschitzWith gamma T) (star : Fin p → ℝ) (hstar : T star = star)
    (Q E alpha : ℕ → Ω → Fin p → ℝ)
    (hQ : ∀ n, Measurable[F n] (Q n)) (hE : ∀ n, Measurable[F (n + 1)] (E n))
    (ha : ∀ n, Measurable[F n] (alpha n)) (ha01 : ∀ n ω i, alpha n ω i ∈ Icc 0 1)
    (hE2 : ∀ n i, MemLp (fun ω ↦ E n ω i) 2 P)
    (hE0 : ∀ n i, P[(fun ω ↦ E n ω i) | F n] =ᵐ[P] fun _ ↦ 0)
    (C : ℝ) (hvar : ∀ n i, P[(fun ω ↦ E n ω i ^ 2) | F n] ≤ᵐ[P] fun _ ↦ C)
    (hsteps : ∀ i, ∀ᵐ ω ∂P, Summable (fun n ↦ alpha n ω i ^ 2) ∧
      Tendsto (fun n ↦ ∑ t ∈ Finset.range n, alpha t ω i) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂P, ∀ i, Q (n + 1) ω i =
      (1 - alpha n ω i) * Q n ω i + alpha n ω i * (T (Q n ω) i + E n ω i)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ Q n ω) atTop (𝓝 star) := by
  sorry

/-- GAPS 107.58, Bellman optimality, a greedy stationary policy, and the primal LP. -/
theorem gap107_58 {s a : ℕ} (ha : 0 < a) (M : MDP s a) :
    ∃ V : Fin s → ℝ, bellman M V = V ∧
      (∃ pi : Fin s → Fin a, ∀ i,
        V i = M.reward i (pi i) + M.gamma * ∑ j, M.transition i (pi i) j * V j) ∧
      (∀ U : Fin s → ℝ, (∀ i b,
        M.reward i b + M.gamma * ∑ j, M.transition i b j * U j ≤ U i) → ∀ i, V i ≤ U i) ∧
      ∀ rho : Fin s → ℝ, (∀ i, 0 < rho i) → ∀ U : Fin s → ℝ,
        (∀ i b, M.reward i b + M.gamma * ∑ j, M.transition i b j * U j ≤ U i) →
        (∑ i, rho i * V i) ≤ (∑ i, rho i * U i) ∧
          ((∑ i, rho i * V i) = (∑ i, rho i * U i) ↔ V = U) := by
  sorry

/-- GAPS 107.59, the fixed-policy resolvent identity and sup-norm error bound. -/
theorem gap107_59 {s : ℕ} (P H : Matrix (Fin s) (Fin s) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hH : ∀ i j, 0 ≤ H i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hH1 : ∀ i, ∑ j, H i j = 1)
    (gamma : ℝ) (hg : gamma ∈ Ioo 0 1) (r : Fin s → ℝ) :
    let V : Fin s → ℝ := ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • P)⁻¹.mulVec r;
    let W : Fin s → ℝ := ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • H)⁻¹.mulVec r;
    V - W = gamma • ((1 : Matrix (Fin s) (Fin s) ℝ) - gamma • H)⁻¹.mulVec ((P - H).mulVec V) ∧
      ‖V - W‖ ≤ gamma / (1 - gamma) * ‖(P - H).mulVec V‖ := by
  sorry

/-- GAPS 107.60, deterministic projected-contraction error bound underlying TD(lambda). -/
theorem gap107_60 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H →L[ℝ] H) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (gamma lambda : ℝ) (hg : gamma ∈ Ioo 0 1) (hl : lambda ∈ Icc 0 1)
    (T : H → H)
    (hc : ∀ x y, ‖T x - T y‖ ≤ gamma * (1 - lambda) / (1 - gamma * lambda) * ‖x - y‖)
    (V w : H) (hV : T V = V) (hw : P (T w) = w) :
    ‖w - V‖ ≤ (1 - gamma * lambda) / (1 - gamma) * ‖P V - V‖ := by
  sorry

/-- GAPS 107.65, basic composition of two adaptive private releases. -/
theorem gap107_65 {D Y Z : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    [MeasurableSpace Z] (R : D → D → Prop) (hR : ∀ d d', R d d' → R d' d)
    (M : Kernel D Y) [IsMarkovKernel M] (N : Kernel (D × Y) Z) [IsMarkovKernel N]
    (e₁ e₂ d₁ d₂ : ℝ) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hM : Private R e₁ d₁ M)
    (hN : ∀ y, ∀ d d', R d d' → ∀ A : Set Z, MeasurableSet A →
      N (d,y) A ≤ ENNReal.ofReal (Real.exp e₂) * N (d',y) A + ENNReal.ofReal d₂) :
    Private R (e₁ + e₂) (d₁ + d₂) (M ⊗ₖ N) := by
  sorry

/-- GAPS 107.75, the single-release KL contraction under local privacy. -/
theorem gap107_75 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Kernel X Y) [IsMarkovKernel Q] (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hpriv : Private (fun _ _ : X ↦ True) epsilon 0 Q)
    (P₁ P₂ : Measure X) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    InformationTheory.klDiv (Q ∘ₘ P₁) (Q ∘ₘ P₂) +
      InformationTheory.klDiv (Q ∘ₘ P₂) (Q ∘ₘ P₁) ≤
      ENNReal.ofReal (4 * (Real.exp epsilon - 1) ^ 2 * Section103.tv P₁ P₂ ^ 2) := by
  sorry

end CKSD.Section107
