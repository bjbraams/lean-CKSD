module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic

/-!
# McKean–Vlasov systems and mean-field limits

Interacting diffusions with additive noise `dXₜ = b(Xₜ, μₜ) dt + dWₜ` are stated pathwise: given
continuous Brownian paths, the equation is the integral equation
`Xₜ = X₀ + ∫₀ᵗ b(Xₛ, μₛ) ds + Wₜ`, so no stochastic integral is needed. A `d`-dimensional Brownian
motion has independent coordinates that are real Brownian motions in Mathlib's sense. Particle
systems are indexed by `ℕ`, the `N`-particle system using its first `N` particles, so that the
first `k` particles make sense for every `N`. Paths on `[0, T]` live in `C([0, T], ℝᵈ)` with
Mathlib's Borel σ-algebra. The mean-field gradient flow is a system of ordinary differential
equations, and its limit is a solution of TauCeti's continuity equation.

## Main definitions

* `CKSD.IsMcKeanVlasovSolution`, `CKSD.IsParticleSystem`: the McKean–Vlasov equation and its
  `N`-particle approximation, driven by the same Brownian motions.
* `CKSD.meanFieldRisk`, `CKSD.meanFieldVelocity`: the population risk of a two-layer network in
  mean-field parametrization and the velocity field of its gradient flow.

## Main results

* `CKSD.exists_unique_mcKeanVlasov_and_particleSystem`: well-posedness.
* `CKSD.tendsto_particle_paths`: propagation of chaos, as weak convergence of path laws in
  Mathlib's `MeasureTheory.ProbabilityMeasure` topology.
* `CKSD.exists_lintegral_sup_particle_sub_le`: quantitative propagation of chaos.
* `CKSD.meanFieldRisk_eq`, `CKSD.exists_meanField_limit`: the quadratic expansion of the risk and
  the mean-field limit of network training.

Sources: GAPS 104.51, 104.53, and 104.56.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

universe u

attribute [local instance] Classical.propDecidable

/-- A standard Brownian motion in `ℝᵈ`: independent coordinates, each a real Brownian motion. -/
def IsBrownianEuclidean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (P : Measure Ω) : Prop :=
  (∀ j, IsBrownianReal (fun t ω ↦ W t ω j) P) ∧ iIndepFun (fun j ω t ↦ W t ω j) P

/-- The path of `x` on `[0, T]`, as a continuous map, or `0` if `x` is not continuous there. -/
def pathOn {F : Type*} [TopologicalSpace F] [Zero F] (T : ℝ) (x : ℝ → F) :
    C(Icc (0 : ℝ) T, F) :=
  if h : ContinuousOn x (Icc 0 T) then ⟨fun t ↦ x t, h.domRestrict⟩ else 0

/-- Lipschitz continuity of a drift in position and in `W₁` of the measure, on probability
measures with a finite first moment. -/
def IsWassersteinLipschitzDrift {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d)) (L : ℝ) : Prop :=
  ∀ x y μ ν, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun z ↦ ‖z‖) μ → Integrable (fun z ↦ ‖z‖) ν →
    ‖b x μ - b y ν‖ ≤ L * (‖x - y‖ + (TauCeti.wassersteinEDist 1 μ ν).toReal)

/-- Independent identically distributed initial states and Brownian drivers, the initial states
independent of the drivers. -/
def IsIIDInitialAndDrivers {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ i, Measurable (X₀ i)) ∧ (∀ i, P.map (X₀ i) = μ₀) ∧ (∀ i, IsBrownianEuclidean (W i) P) ∧
    (∀ i, IndepFun (X₀ i) (fun ω t ↦ W i t ω) P) ∧
    iIndepFun (fun i ω ↦ (X₀ i ω, fun t ↦ W i t ω)) P

/-- The `N`-particle system: particles `i < N` solve `Xⁱₜ = X₀ⁱ + ∫₀ᵗ b(Xⁱₛ, μᴺₛ) ds + Wⁱₜ`
with continuous paths, `μᴺₛ` the empirical measure of the first `N` particles. -/
def IsParticleSystem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d))
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (N : ℕ) (X : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)) (P : Measure Ω) : Prop :=
  (∀ i t, Measurable (X i t)) ∧ ∀ i < N, ∀ᵐ ω ∂P, Continuous (fun t ↦ X i t ω) ∧
    ∀ t ≥ 0, X i t ω = X₀ i ω +
      (∫ s in (0 : ℝ)..t, b (X i s ω) (empiricalMeasure N fun j : Fin N ↦ X j s ω)) +
        W i t.toNNReal ω

/-- A solution of the McKean–Vlasov equation `Yₜ = ξ + ∫₀ᵗ b(Yₛ, Law(Yₛ)) ds + Bₜ` with
continuous paths. -/
def IsMcKeanVlasovSolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d))
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (P : Measure Ω) : Prop :=
  (∀ t, Measurable (Y t)) ∧ (∀ t ≥ 0, Integrable (fun ω ↦ ‖Y t ω‖) P) ∧
    ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) ∧
      ∀ t ≥ 0, Y t ω = ξ ω + (∫ s in (0 : ℝ)..t, b (Y s ω) (P.map (Y s))) + B t.toNNReal ω

/-- GAPS 104.51: well-posedness. Under a Lipschitz drift, the McKean–Vlasov equation has a solution,
unique up to indistinguishability among solutions with integrable marginals, and every particle
system has a pathwise unique solution. -/
theorem exists_unique_mcKeanVlasov_and_particleSystem {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d)) (L : ℝ) (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (h2 : MemLp (X₀ 0) 2 P) :
    (∀ i, ∃ Y, IsMcKeanVlasovSolution b (X₀ i) (W i) Y P ∧
      ∀ Y', IsMcKeanVlasovSolution b (X₀ i) (W i) Y' P → ∀ᵐ ω ∂P, ∀ t ≥ 0, Y' t ω = Y t ω) ∧
    ∀ N, ∃ X, IsParticleSystem b X₀ W N X P ∧
      ∀ X', IsParticleSystem b X₀ W N X' P → ∀ i < N, ∀ᵐ ω ∂P, ∀ t ≥ 0, X' i t ω = X i t ω := by
  sorry

/-- GAPS 104.51: propagation of chaos. For every horizon `T` and every `k`, the joint path law on
`[0, T]` of the first `k` particles converges weakly to the `k`-fold product of the
McKean–Vlasov path law. The hypotheses do not make the path maps measurable (particles of index
at least `N` are unconstrained), so the statement is convergence of the image measures in the
`ProbabilityMeasure` topology rather than `TendstoInDistribution`. -/
theorem tendsto_particle_paths {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin d)) (L : ℝ) (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (h2 : MemLp (X₀ 0) 2 P)
    (X : ℕ → ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : ∀ N, IsParticleSystem b X₀ W N (X N) P)
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d)) (hY : IsMcKeanVlasovSolution b (X₀ 0) (W 0) Y P)
    (T : ℝ) (hT : 0 < T) (k : ℕ) :
    Tendsto (β := ProbabilityMeasure (Fin k → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d))))
      (fun N ↦ ⟨P.map fun ω (i : Fin k) ↦ pathOn T fun t ↦ X N i t ω, inferInstance⟩) atTop
      (𝓝 ⟨Measure.pi fun _ : Fin k ↦ P.map fun ω ↦ pathOn T fun t ↦ Y t ω, inferInstance⟩) := by
  sorry

/-- Drift `b₀(x) + ∫ K(x, y) μ(dy)` of an interaction model. -/
def interactionDrift {d : ℕ} (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  b₀ x + ∫ y, K x y ∂μ

/-- GAPS 104.56: quantitative propagation of chaos for a bounded Lipschitz interaction, by
synchronous coupling with independent nonlinear copies driven by the same initial values and
Brownian motions. The constant depends only on `T`, the Lipschitz constants, and `sup |K|`. -/
theorem exists_lintegral_sup_particle_sub_le (T : ℝ) (L₀ L_K κ : ℝ≥0) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (d : ℕ) (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      LipschitzWith L₀ b₀ → (∀ x y, ‖K x y‖ ≤ κ) → LipschitzWith L_K (Function.uncurry K) →
      ∀ (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
        (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (μ₀ : Measure (EuclideanSpace ℝ (Fin d))),
        IsIIDInitialAndDrivers P X₀ W μ₀ → MemLp (X₀ 0) 2 P →
      ∀ (X : ℕ → ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
        (Y : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d)),
        (∀ N, IsParticleSystem (interactionDrift b₀ K) X₀ W N (X N) P) →
        (∀ i, IsMcKeanVlasovSolution (interactionDrift b₀ K) (X₀ i) (W i) (Y i) P) →
        ∀ N i, i < N →
          ∫⁻ ω, ⨆ t ∈ Icc 0 T, ‖X N i t ω - Y i t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C / N) := by
  sorry

/-- Correlation `V(θ) = 𝔼[Y φ(X, θ)]` of a feature with the response. -/
def meanFieldV {Z Θ : Type*} [MeasurableSpace Z] (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ)
    (θ : Θ) : ℝ :=
  ∫ w, w.2 * φ w.1 θ ∂ν

/-- Feature kernel `U(θ, θ') = 𝔼[φ(X, θ) φ(X, θ')]`. -/
def meanFieldU {Z Θ : Type*} [MeasurableSpace Z] (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ)
    (θ θ' : Θ) : ℝ :=
  ∫ w, φ w.1 θ * φ w.1 θ' ∂ν

/-- Population risk `½ 𝔼(Y - f_ρ(X))²` of the mean-field predictor `f_ρ = ∫ φ(·, θ) ρ(dθ)`. -/
def meanFieldRisk {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (ν : Measure (Z × ℝ)) (φ : Z → Θ → ℝ) (ρ : Measure Θ) : ℝ :=
  (1 / 2 : ℝ) * ∫ w, (w.2 - ∫ θ, φ w.1 θ ∂ρ) ^ 2 ∂ν

/-- Velocity `-∇_θΨ(θ; ρ) = ∇V(θ) - ∫ ∇_θU(θ, θ') ρ(dθ')` of the mean-field gradient flow. -/
def meanFieldVelocity {p : ℕ} (gradV : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (gradU : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (ρ : Measure (EuclideanSpace ℝ (Fin p))) (θ : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  gradV θ - ∫ θ', gradU θ θ' ∂ρ

/-- GAPS 104.53: the elementary expansion
`R(ρ) = ½𝔼Y² - ∫ V dρ + ½ ∫∫ U dρ dρ` for a bounded measurable feature map. -/
theorem meanFieldRisk_eq {Z Θ : Type*} [MeasurableSpace Z] [MeasurableSpace Θ]
    (ν : Measure (Z × ℝ)) [IsProbabilityMeasure ν] (φ : Z → Θ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (B : ℝ) (hB : ∀ z θ, |φ z θ| ≤ B)
    (hY : Integrable (fun w : Z × ℝ ↦ w.2 ^ 2) ν) (ρ : Measure Θ) [IsProbabilityMeasure ρ] :
    meanFieldRisk ν φ ρ = (1 / 2 : ℝ) * ∫ w, w.2 ^ 2 ∂ν - ∫ θ, meanFieldV ν φ θ ∂ρ +
      (1 / 2 : ℝ) * ∫ θ, ∫ θ', meanFieldU ν φ θ θ' ∂ρ ∂ρ := by
  set f : Z → ℝ := fun z ↦ ∫ θ, φ z θ ∂ρ with hfdef
  have hfm : Measurable f := hφ.stronglyMeasurable.integral_prod_right'.measurable
  have hfB (z : Z) : |f z| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun θ ↦ φ z θ) (C := B)
      (ae_of_all _ fun θ ↦ by simpa [Real.norm_eq_abs] using hB z θ)
    simpa [Real.norm_eq_abs] using this
  have hφm (z : Z) : Measurable (φ z) := hφ.comp (measurable_const.prodMk measurable_id)
  -- Integrability of the pieces.
  have hY1 : Integrable (fun w : Z × ℝ ↦ w.2) ν := by
    refine ((integrable_const (1 : ℝ)).add hY).div_const 2 |>.mono'
      measurable_snd.aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs]
    have : 0 ≤ (|w.2| - 1) ^ 2 := sq_nonneg _
    have hsq : |w.2| ^ 2 = w.2 ^ 2 := sq_abs _
    simp only [Pi.add_apply]
    nlinarith
  have hyf : Integrable (fun w : Z × ℝ ↦ w.2 * f w.1) ν := by
    refine (hY1.abs.const_mul B).mono' (measurable_snd.mul (hfm.comp measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hfB w.1) (abs_nonneg _)
  have hf2 : Integrable (fun w : Z × ℝ ↦ f w.1 ^ 2) ν := by
    refine Integrable.of_bound ((hfm.comp measurable_fst).pow_const 2).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hfB w.1) 2
  -- The cross term.
  have hcross : ∫ w, w.2 * f w.1 ∂ν = ∫ θ, meanFieldV ν φ θ ∂ρ := by
    have h1 : (fun w : Z × ℝ ↦ w.2 * f w.1) = fun w ↦ ∫ θ, w.2 * φ w.1 θ ∂ρ := by
      funext w; rw [integral_const_mul]
    rw [h1]
    refine integral_integral_swap ?_
    refine (((hY1.abs.const_mul B).comp_fst ρ)).mono' ?_ (ae_of_all _ fun q ↦ ?_)
    · exact (measurable_fst.snd.mul (hφ.comp (measurable_fst.fst.prodMk
        measurable_snd))).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _ _) (abs_nonneg _)
  -- The quadratic term.
  have hquad : ∫ w, f w.1 ^ 2 ∂ν = ∫ θ, ∫ θ', meanFieldU ν φ θ θ' ∂ρ ∂ρ := by
    have h1 : (fun w : Z × ℝ ↦ f w.1 ^ 2) = fun w ↦ ∫ θ, φ w.1 θ * f w.1 ∂ρ := by
      funext w; rw [integral_mul_const, sq]
    rw [h1, integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
      have h2 : (fun w : Z × ℝ ↦ φ w.1 θ * f w.1) =
          fun w ↦ ∫ θ', φ w.1 θ * φ w.1 θ' ∂ρ := by
        funext w; rw [integral_const_mul]
      simp only
      rw [h2, integral_integral_swap]
      · rfl
      refine Integrable.of_bound ?_ (B * B) (ae_of_all _ fun q ↦ ?_)
      · exact ((hφ.comp (measurable_fst.fst.prodMk measurable_const)).mul
          (hφ.comp (measurable_fst.fst.prodMk measurable_snd))).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB _ _) (hB _ _) (abs_nonneg _) ((abs_nonneg _).trans (hB q.1.1 θ))
    · refine Integrable.of_bound ?_ (B * B) (ae_of_all _ fun q ↦ ?_)
      · exact ((hφ.comp (measurable_fst.fst.prodMk measurable_snd)).mul
          (hfm.comp measurable_fst.fst)).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB _ _) (hfB _) (abs_nonneg _) ((abs_nonneg _).trans (hB q.1.1 q.2))
  have hpt (w : Z × ℝ) : (w.2 - f w.1) ^ 2 = w.2 ^ 2 - 2 * (w.2 * f w.1) + f w.1 ^ 2 := by
    ring
  show (1 / 2 : ℝ) * ∫ w, (w.2 - f w.1) ^ 2 ∂ν = _
  simp_rw [hpt]
  have hsum := integral_add (hY.sub (hyf.const_mul 2)) hf2
  have hdif := integral_sub hY (hyf.const_mul 2)
  simp only [Pi.sub_apply] at hsum hdif
  rw [hsum, hdif, integral_const_mul, hcross, hquad]
  ring

/-- GAPS 104.53: mean-field limit of two-layer network training. With bounded Lipschitz gradients
of `V` and `U`, the nonlinear continuity equation `∂ₜρ = ∇·(ρ∇_θΨ(·; ρ))` has a unique narrowly
continuous probability solution with datum `ρ₀`, and the empirical measures of the time-scaled
gradient flow from independent `ρ₀`-distributed initial particles converge to it in `W₁`, almost
surely and uniformly on bounded time intervals. -/
theorem exists_meanField_limit {Z : Type*} [MeasurableSpace Z] {p : ℕ}
    (ν : Measure (Z × ℝ)) [IsProbabilityMeasure ν] (φ : Z → EuclideanSpace ℝ (Fin p) → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (hY : Integrable (fun w : Z × ℝ ↦ w.2 ^ 2) ν)
    (gradV : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (gradU : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (hgV : ∀ θ, HasGradientAt (meanFieldV ν φ) (gradV θ) θ)
    (hgU : ∀ θ θ', HasGradientAt (fun η ↦ meanFieldU ν φ η θ') (gradU θ θ') θ)
    (B L : ℝ) (hVb : ∀ θ, ‖gradV θ‖ ≤ B) (hUb : ∀ θ θ', ‖gradU θ θ'‖ ≤ B)
    (hVl : ∀ θ η, ‖gradV θ - gradV η‖ ≤ L * ‖θ - η‖)
    (hUl : ∀ θ θ' η η', ‖gradU θ θ' - gradU η η'‖ ≤ L * (‖θ - η‖ + ‖θ' - η'‖))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure ρ₀]
    (hρ₀ : Integrable (fun θ ↦ ‖θ‖) ρ₀) :
    let IsSolution := fun ρ : ℝ → Measure (EuclideanSpace ℝ (Fin p)) ↦
      (∀ t ≥ 0, IsProbabilityMeasure (ρ t)) ∧ ρ 0 = ρ₀ ∧
      (∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ,
        ContinuousOn (fun t ↦ ∫ θ, g θ ∂ρ t) (Ici 0)) ∧
      ∀ T > 0, TauCeti.IsContinuityEquation ρ
        (fun t θ ↦ meanFieldVelocity gradV gradU (ρ t) θ) 0 T
    ∃ ρ, IsSolution ρ ∧ (∀ σ, IsSolution σ → ∀ t ≥ 0, σ t = ρ t) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin p)), IsIndependentIdenticallyDistributed P ξ ρ₀ →
        ∀ θ : ℕ → ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin p),
          (∀ N, ∀ i < N, ∀ ω, θ N i 0 ω = ξ i ω ∧ ∀ t, HasDerivAt (fun s ↦ θ N i s ω)
            (meanFieldVelocity gradV gradU
              (empiricalMeasure N fun j : Fin N ↦ θ N j t ω) (θ N i t ω)) t) →
          ∀ᵐ ω ∂P, ∀ T > 0, Tendsto (fun N ↦ ⨆ t ∈ Icc 0 T,
            TauCeti.wassersteinEDist 1 (empiricalMeasure N fun j : Fin N ↦ θ N j t ω) (ρ t))
            atTop (𝓝 0) := by
  sorry

end CKSD
