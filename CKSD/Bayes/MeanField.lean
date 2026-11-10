module

public import CKSD.Bayes.Basic
public import CKSD.Bayes.MeanFieldCoupling
public import CKSD.Bayes.MeanFieldPathMap
public import CKSD.Bayes.MeanFieldFluctuation
public import CKSD.Bayes.MeanFieldVariance
public import CKSD.Bayes.MeanFieldQuantitative
public import CKSD.Bayes.MeanFieldRateIntegration
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Probability.IdentDistribIndep
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

/-- Countable collections of evaluations of two real Brownian motions have the same law. -/
theorem identDistrib_countable_evals_of_isPreBrownianReal {Ω I : Type*} [MeasurableSpace Ω]
    [Countable I] (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (t : I → ℝ≥0) :
    IdentDistrib (fun ω i ↦ B (t i) ω) (fun ω i ↦ C (t i) ω) P P := by
  apply (identDistrib_iff_forall_finset_identDistrib
    (AEMeasurable.of_eval fun i ↦ hB.aemeasurable (t i))
    (AEMeasurable.of_eval fun i ↦ hC.aemeasurable (t i))).2
  intro J
  classical
  let K := J.image t
  let g : (K → ℝ) → (J → ℝ) := fun x i ↦ x ⟨t i, Finset.mem_image_of_mem _ i.2⟩
  have hg : Measurable g := measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  simpa only [g, K, Function.comp_def, Finset.restrict_def] using
    ((hB.hasLaw K).identDistrib (hC.hasLaw K)).comp hg

/-- Countable evaluations of Euclidean Brownian drivers have a law independent of the chosen
Brownian realization. -/
theorem IsBrownianEuclidean.identDistrib_countable_evals {Ω I : Type*} [MeasurableSpace Ω]
    [Countable I] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianEuclidean B P) (hC : IsBrownianEuclidean C P) (t : I → ℝ≥0) :
    IdentDistrib (fun ω i ↦ B (t i) ω) (fun ω i ↦ C (t i) ω) P P := by
  have hcoord (j : Fin d) : IdentDistrib (fun ω i ↦ B (t i) ω j) (fun ω i ↦ C (t i) ω j) P P :=
    identDistrib_countable_evals_of_isPreBrownianReal P _ _ (hB.1 j).toIsPreBrownianReal
      (hC.1 j).toIsPreBrownianReal t
  have hpost : Measurable (fun z : ℝ≥0 → ℝ ↦ fun i ↦ z (t i)) :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  have hindB := hB.2.comp (fun _ z i ↦ z (t i)) (fun _ ↦ hpost)
  have hindC := hC.2.comp (fun _ z i ↦ z (t i)) (fun _ ↦ hpost)
  have hpair := IdentDistrib.pi hcoord hindB hindC
  let F : (Fin d → I → ℝ) → (I → EuclideanSpace ℝ (Fin d)) :=
    fun z i ↦ WithLp.toLp 2 (fun j ↦ z j i)
  have hF : Measurable F := by
    apply measurable_pi_iff.2
    intro i
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun j ↦
      (measurable_pi_apply i).comp (measurable_pi_apply j))
  convert hpair.comp hF using 1 <;> ext ω i j <;> rfl

/-- Countably many evaluations of the initial state plus its Brownian driver are identically
distributed across the independent input particles. -/
theorem IsIIDInitialAndDrivers.identDistrib_forcing_evals
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (hiid : IsIIDInitialAndDrivers P X₀ W μ₀) (t : I → ℝ≥0) (i j : ℕ) :
    IdentDistrib (fun ω q ↦ X₀ i ω + W i (t q) ω) (fun ω q ↦ X₀ j ω + W j (t q) ω) P P := by
  have hinit : IdentDistrib (X₀ i) (X₀ j) P P :=
    ⟨(hiid.1 i).aemeasurable, (hiid.1 j).aemeasurable, (hiid.2.1 i).trans (hiid.2.1 j).symm⟩
  have hdriver := IsBrownianEuclidean.identDistrib_countable_evals P (W i) (W j)
    (hiid.2.2.1 i) (hiid.2.2.1 j) t
  have hpost : Measurable (fun z : ℝ≥0 → EuclideanSpace ℝ (Fin d) ↦ fun q ↦ z (t q)) :=
    measurable_pi_iff.2 fun q ↦ measurable_pi_apply _
  have hind (k : ℕ) : IndepFun (X₀ k) (fun ω q ↦ W k (t q) ω) P :=
    (hiid.2.2.2.1 k).comp measurable_id hpost
  have hpair := hinit.prodMk hdriver (hind i) (hind j)
  have hsum : Measurable (fun p : EuclideanSpace ℝ (Fin d) × (I → EuclideanSpace ℝ (Fin d)) ↦
      fun q ↦ p.1 + p.2 q) := measurable_pi_iff.2 fun q ↦
    measurable_fst.add ((measurable_pi_apply q).comp measurable_snd)
  exact hpair.comp hsum

/-- Countably sampled additive forcings are independent across the input particles. -/
theorem IsIIDInitialAndDrivers.iIndepFun_forcing_evals
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (hiid : IsIIDInitialAndDrivers P X₀ W μ₀) (t : I → ℝ≥0) :
    iIndepFun (fun i ω q ↦ X₀ i ω + W i (t q) ω) P := by
  have hpost : Measurable (fun p : EuclideanSpace ℝ (Fin d) × (ℝ≥0 → EuclideanSpace ℝ (Fin d)) ↦
      fun q ↦ p.1 + p.2 (t q)) := measurable_pi_iff.2 fun q ↦
    measurable_fst.add ((measurable_pi_apply _).comp measurable_snd)
  exact hiid.2.2.2.2.comp (fun _ p q ↦ p.1 + p.2 (t q)) (fun _ ↦ hpost)


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

/-- With a bounded Lipschitz interaction, nonlinear solutions sharing the initial condition
and Brownian forcing are indistinguishable; the Brownian property itself is not needed. -/
theorem IsMcKeanVlasovSolution.ae_eq_of_interactionDrift
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {L_K κ : ℝ≥0} (hK : LipschitzWith L_K (Function.uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (X Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : IsMcKeanVlasovSolution (interactionDrift b₀ K) ξ B X P)
    (hY : IsMcKeanVlasovSolution (interactionDrift b₀ K) ξ B Y P) :
    ∀ᵐ ω ∂P, ∀ t ≥ 0, X t ω = Y t ω := by
  let v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun t x ↦ ∫ z, K x (X t z) ∂P
  let w : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun t x ↦ ∫ z, K x (Y t z) ∂P
  have hXc := hX.2.2.mono fun _ hω ↦ hω.1
  have hYc := hY.2.2.mono fun _ hω ↦ hω.1
  have hv : Continuous (Function.uncurry v) := continuous_integral_interaction P K hK.continuous hKb X hX.1 hXc
  have hw : Continuous (Function.uncurry w) := continuous_integral_interaction P K hK.continuous hKb Y hY.1 hYc
  have hmapX (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
      interactionDrift b₀ K x (P.map (X s)) = b₀ x + v s x := by
    rw [interactionDrift, integral_map (hX.1 s).aemeasurable
      (f := fun y ↦ K x y) (hK.continuous.measurable.comp
        ((measurable_const : Measurable fun _ : EuclideanSpace ℝ (Fin d) ↦ x).prodMk measurable_id)).aestronglyMeasurable]
  have hmapY (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
      interactionDrift b₀ K x (P.map (Y s)) = b₀ x + w s x := by
    rw [interactionDrift, integral_map (hY.1 s).aemeasurable
      (f := fun y ↦ K x y) (hK.continuous.measurable.comp
        ((measurable_const : Measurable fun _ : EuclideanSpace ℝ (Fin d) ↦ x).prodMk measurable_id)).aestronglyMeasurable]
  have heq : ∀ᵐ ω ∂P, ∀ t ≥ 0, X t ω - Y t ω = ∫ s in (0 : ℝ)..t,
      (b₀ (X s ω) + v s (X s ω)) - (b₀ (Y s ω) + w s (Y s ω)) := by
    filter_upwards [hX.2.2, hY.2.2] with ω hx hy
    intro t ht
    have hxc : Continuous (fun s ↦ b₀ (X s ω) + v s (X s ω)) :=
      (hb₀.continuous.comp hx.1).add (hv.comp (continuous_id.prodMk hx.1))
    have hyc : Continuous (fun s ↦ b₀ (Y s ω) + w s (Y s ω)) :=
      (hb₀.continuous.comp hy.1).add (hw.comp (continuous_id.prodMk hy.1))
    rw [intervalIntegral.integral_sub (hxc.intervalIntegrable _ _) (hyc.intervalIntegrable _ _)]
    have hx' := hx.2 t ht
    have hy' := hy.2 t ht
    simp_rw [hmapX] at hx'
    simp_rw [hmapY] at hy'
    rw [hx', hy']
    abel
  have hzero (N : ℕ) : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) N, X t ω = Y t ω :=
    ae_eq_on_Icc_of_interaction_integral_eq P b₀ hb₀ K hK κ.coe_nonneg hKb X Y hX.1 hY.1
      hXc hYc heq (Nat.cast_nonneg N)
  filter_upwards [ae_all_iff.2 hzero] with ω hω
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact hω N t ⟨ht, hN⟩



/-- A measurable inverse solution map transports one solution path to an iid family of input
forcings, giving iid solution paths and retaining the forcing equations. -/
theorem exists_iid_paths_of_forcing_coordinates {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T)
    (v : ℝ → E → E) (hv : Continuous (Function.uncurry v)) {L : ℝ≥0}
    (hvL : ∀ s, LipschitzWith L (v s))
    (U : ℕ → Ω → ℚ → E) (hUind : iIndepFun U P)
    (hUid : ∀ i, IdentDistrib (U 0) (U i) P P)
    (Y₀ : Ω → C(Icc (0 : ℝ) T, E))
    (hU₀ : (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (Y₀ ω))) =ᵐ[P] U 0) :
    ∃ Z : ℕ → Ω → C(Icc (0 : ℝ) T, E),
      (∀ i, Measurable (Z i)) ∧ iIndepFun Z P ∧ (∀ i, IdentDistrib (Z i) Y₀ P P) ∧
        ∀ i, (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (Z i ω))) =ᵐ[P] U i := by
  let emb := measurableEmbedding_pathForcingMap hT v hv hvL
  let S : (ℚ → E) → C(Icc (0 : ℝ) T, E) := fun u ↦ emb.invFun (pathOfRationalCoordinates hT u)
  have hS : Measurable S := emb.measurable_invFun.comp (measurable_pathOfRationalCoordinates hT)
  let R : ℕ → Ω → C(Icc (0 : ℝ) T, E) := fun i ω ↦ S (U i ω)
  have hR (i : ℕ) : AEMeasurable (R i) P := hS.comp_aemeasurable (hUid i).aemeasurable_snd
  have hR₀ : R 0 =ᵐ[P] Y₀ := by
    filter_upwards [hU₀] with ω hω
    dsimp [R, S]
    rw [← hω, pathOfRationalCoordinates_apply]
    exact emb.leftInverse_invFun (Y₀ ω)
  let Z : ℕ → Ω → C(Icc (0 : ℝ) T, E) := fun i ↦ (hR i).mk (R i)
  have hZ (i : ℕ) : Measurable (Z i) := (hR i).measurable_mk
  have hZae (i : ℕ) : R i =ᵐ[P] Z i := (hR i).ae_eq_mk
  have hindR : iIndepFun R P := hUind.comp (fun _ ↦ S) (fun _ ↦ hS)
  have hindZ : iIndepFun Z P := hindR.congr hZae
  have hZid (i : ℕ) : IdentDistrib (Z i) Y₀ P P := by
    have hRi : IdentDistrib (R 0) (R i) P P := (hUid i).comp hS
    exact (IdentDistrib.of_ae_eq (hR i) (hZae i)).symm.trans
      (hRi.symm.trans (IdentDistrib.of_ae_eq (hR 0) hR₀))
  have hCoords : Measurable (pathRationalCoordinates (E := E) hT) :=
    (measurableEmbedding_pathRationalCoordinates hT).measurable
  have hΦ : Measurable (pathForcingMap hT v hv) := emb.measurable
  have hGood : MeasurableSet {u : ℚ → E | pathRationalCoordinates hT (pathForcingMap hT v hv (S u)) = u} :=
    measurableSet_eq_fun (hCoords.comp (hΦ.comp hS)) measurable_id
  have hGood₀ : ∀ᵐ ω ∂P, pathRationalCoordinates hT (pathForcingMap hT v hv (S (U 0 ω))) = U 0 ω := by
    filter_upwards [hR₀, hU₀] with ω hω hUω
    change pathRationalCoordinates hT (pathForcingMap hT v hv (R 0 ω)) = U 0 ω
    rw [hω]
    exact hUω
  refine ⟨Z, hZ, hindZ, hZid, fun i ↦ ?_⟩
  have hGoodi := (hUid i).ae_snd hGood hGood₀
  filter_upwards [hGoodi, hZae i] with ω hω hZω
  rw [← hZω]
  exact hω

/-- Euclidean Brownian paths remain almost surely continuous after the nonnegative-time projection. -/
theorem IsBrownianEuclidean.ae_continuous_toNNReal {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianEuclidean B P) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ ↦ B t.toNNReal ω) := by
  filter_upwards [ae_all_iff.2 (fun j : Fin d ↦ (hB.1 j).cont)] with ω hω
  have hc : Continuous (fun t : ℝ ↦ fun j : Fin d ↦ B t.toNNReal ω j) :=
    continuous_pi fun j ↦ (hω j).comp continuous_real_toNNReal
  convert (PiLp.continuous_toLp 2 _).comp hc using 1
  ext t j
  rfl

/-- Averaging a bounded Lipschitz interaction preserves its Lipschitz constant in position. -/
theorem lipschitzWith_integral_interaction {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : E → E → E)
    {L : ℝ≥0} (hK : LipschitzWith L (Function.uncurry K)) {κ : ℝ}
    (hKb : ∀ x y, ‖K x y‖ ≤ κ) (Y : Ω → E) (hY : Measurable Y) :
    LipschitzWith L (fun x ↦ ∫ z, K x (Y z) ∂P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_self, norm_zero, integral_zero, add_zero] using
    norm_integral_interaction_sub_le P K hK hKb Y Y hY hY
      (by simpa only [sub_self, norm_zero] using (integrable_const (0 : ℝ) : Integrable (fun _ : Ω ↦ (0 : ℝ)) P)) x y

/-- Equality of the forcing at projected rational times yields the whole pathwise integral equation. -/
theorem eq_integral_of_forcing_coordinates {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {T : ℝ} (hT : 0 ≤ T) (v : ℝ → E → E) (hv : Continuous (Function.uncurry v))
    (f : C(Icc (0 : ℝ) T, E)) (ξ : E) (B : ℝ → E) (hB : Continuous B)
    (heq : pathRationalCoordinates hT (pathForcingMap hT v hv f) =
      fun q : ℚ ↦ ξ + B (Set.projIcc 0 T hT q)) :
    ∀ t ∈ Icc (0 : ℝ) T, (f.IccExtend hT) t =
      ξ + (∫ s in (0 : ℝ)..t, v s ((f.IccExtend hT) s)) + B t := by
  let g : C(Icc (0 : ℝ) T, E) := ⟨fun t ↦ ξ + B t, continuous_const.add (hB.comp continuous_subtype_val)⟩
  have hΦ : pathForcingMap hT v hv f = g :=
    (measurableEmbedding_pathRationalCoordinates hT).injective heq
  intro t ht
  have hpoint := congrArg (fun z : C(Icc (0 : ℝ) T, E) ↦ z ⟨t, ht⟩) hΦ
  change f ⟨t, ht⟩ - (∫ s in (0 : ℝ)..t, v s ((f.IccExtend hT) s)) = ξ + B t at hpoint
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ f z) ht]
  have h := sub_eq_iff_eq_add.mp hpoint
  rw [h]
  abel

/-- On a continuous path, the continuous-map path constructor agrees with evaluation. -/
theorem pathOn_apply_of_continuousOn {E : Type*} [TopologicalSpace E] [Zero E]
    (T : ℝ) (f : ℝ → E) (hf : ContinuousOn f (Icc 0 T)) (t : Icc (0 : ℝ) T) :
    pathOn T f t = f t := by
  simp only [pathOn, dite_eq_left hf]
  rfl

/-- Extending a constructed continuous path agrees with the original path on its interval. -/
theorem pathOn_IccExtend_of_continuousOn {E : Type*} [TopologicalSpace E] [Zero E]
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → E) (hf : ContinuousOn f (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) : (pathOn T f).IccExtend hT t = f t := by
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ pathOn T f z) ht]
  exact pathOn_apply_of_continuousOn T f hf ⟨t, ht⟩

/-- One nonlinear solution can be transported along the iid input forcings to iid continuous
solution paths with the same marginal laws, on any fixed bounded time interval. -/
theorem exists_iid_nonlinear_copies_on_Icc {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {L_K κ : ℝ≥0} (hK : LipschitzWith L_K (Function.uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (Y : ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsMcKeanVlasovSolution (interactionDrift b₀ K) (X₀ 0) (W 0) Y P)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ Z : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d),
      (∀ i t, Measurable (Z i t)) ∧ (∀ i ω, Continuous (fun t ↦ Z i t ω)) ∧
      (∀ t, iIndepFun (fun i ↦ Z i t) P) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) T → P.map (Z i t) = P.map (Y t)) ∧
      ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
        Z i t ω = X₀ i ω + (∫ s in (0 : ℝ)..t,
          interactionDrift b₀ K (Z i s ω) (P.map (Z i s))) + W i t.toNNReal ω := by
  let v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun t x ↦ b₀ x + ∫ z, K x (Y t z) ∂P
  have hYc : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω) := hY.2.2.mono fun ω hω ↦ hω.1
  have hv : Continuous (Function.uncurry v) :=
    (hb₀.continuous.comp continuous_snd).add (continuous_integral_interaction P K hK.continuous hKb Y hY.1 hYc)
  have hvL (s : ℝ) : LipschitzWith (L₀ + L_K) (v s) :=
    hb₀.add (lipschitzWith_integral_interaction P K hK hKb (Y s) (hY.1 s))
  have hmap (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
      interactionDrift b₀ K x (P.map (Y s)) = v s x := by
    rw [interactionDrift, integral_map (hY.1 s).aemeasurable (f := fun y ↦ K x y)
      (hK.continuous.measurable.comp ((measurable_const : Measurable fun _ : EuclideanSpace ℝ (Fin d) ↦ x).prodMk measurable_id)).aestronglyMeasurable]
  let times : ℚ → ℝ≥0 := fun q ↦ (Set.projIcc 0 T hT q : ℝ).toNNReal
  let U : ℕ → Ω → ℚ → EuclideanSpace ℝ (Fin d) := fun i ω q ↦ X₀ i ω + W i (times q) ω
  let Ypath : Ω → C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)) := fun ω ↦ pathOn T (fun t ↦ Y t ω)
  have hU₀ : (fun ω ↦ pathRationalCoordinates hT (pathForcingMap hT v hv (Ypath ω))) =ᵐ[P] U 0 := by
    filter_upwards [hY.2.2] with ω hω
    funext q
    let t := Set.projIcc 0 T hT q
    change pathOn T (fun s ↦ Y s ω) t - (∫ s in (0 : ℝ)..t,
      v s ((pathOn T (fun s ↦ Y s ω)).IccExtend hT s)) = X₀ 0 ω + W 0 (times q) ω
    rw [pathOn_apply_of_continuousOn T (fun s ↦ Y s ω) hω.1.continuousOn t]
    have hint : (∫ s in (0 : ℝ)..t, v s ((pathOn T (fun s ↦ Y s ω)).IccExtend hT s)) =
        ∫ s in (0 : ℝ)..t, interactionDrift b₀ K (Y s ω) (P.map (Y s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.2.1] at hs
      dsimp only
      rw [pathOn_IccExtend_of_continuousOn hT (fun s ↦ Y s ω) hω.1.continuousOn
        s ⟨hs.1, hs.2.trans t.2.2⟩, hmap]
    rw [hint, hω.2 t t.2.1]
    dsimp [times, t]
    abel
  obtain ⟨Zpath, hZm, hZind, hZid, hZeq⟩ := exists_iid_paths_of_forcing_coordinates P hT v hv hvL U
    (hiid.iIndepFun_forcing_evals P X₀ W μ₀ times)
    (fun i ↦ hiid.identDistrib_forcing_evals P X₀ W μ₀ times 0 i) Ypath hU₀
  let Z : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d) := fun i t ω ↦ (Zpath i ω).IccExtend hT t
  have hEval (t : ℝ) : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d)) ↦ f.IccExtend hT t) :=
    ContinuousMap.measurable_eval (Set.projIcc 0 T hT t)
  have hZmap (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) : P.map (Z i t) = P.map (Y t) := by
    have h := (hZid i).comp (hEval t)
    have hae : (fun ω ↦ (Ypath ω).IccExtend hT t) =ᵐ[P] Y t :=
      hYc.mono fun ω hω ↦ pathOn_IccExtend_of_continuousOn hT (fun s ↦ Y s ω) hω.continuousOn t ht
    exact (h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd hae)).map_eq
  refine ⟨Z, fun i t ↦ (hEval t).comp (hZm i), fun i ω ↦ (Zpath i ω).IccExtend hT |>.continuous,
    fun t ↦ hZind.comp (fun _ f ↦ f.IccExtend hT t) (fun _ ↦ hEval t), hZmap, fun i ↦ ?_⟩
  filter_upwards [hZeq i, (hiid.2.2.1 i).ae_continuous_toNNReal] with ω hω hB
  have heq := eq_integral_of_forcing_coordinates hT v hv (Zpath i ω) (X₀ i ω)
    (fun t ↦ W i t.toNNReal ω) hB hω
  intro t ht
  change (Zpath i ω).IccExtend hT t = _
  rw [heq t ht]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  change v s (Z i s ω) = interactionDrift b₀ K (Z i s ω) (P.map (Z i s))
  rw [hZmap i s ⟨hs.1, hs.2.trans ht.2⟩, hmap]

/-- For bounded Lipschitz interactions, separately given nonlinear solutions with iid initial
conditions and Brownian drivers are independent and identically distributed at each time. -/
theorem IsMcKeanVlasovSolution.iIndepFun_interactionDrift {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {L_K κ : ℝ≥0} (hK : LipschitzWith L_K (Function.uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (Y : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : ∀ i, IsMcKeanVlasovSolution (interactionDrift b₀ K) (X₀ i) (W i) (Y i) P)
    (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun (fun i ↦ Y i t) P ∧ ∀ i, P.map (Y i t) = P.map (Y 0 t) := by
  obtain ⟨Z, hZm, hZc, hZind, hZmap, hZeq⟩ :=
    exists_iid_nonlinear_copies_on_Icc P b₀ hb₀ K hK hKb X₀ W μ₀ hiid (Y 0) (hY 0) ht
  have hae (i : ℕ) : ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) t, Y i s ω = Z i s ω := by
    let v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun s x ↦ ∫ z, K x (Y i s z) ∂P
    let w : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun s x ↦ ∫ z, K x (Z i s z) ∂P
    have hYc := (hY i).2.2.mono fun _ hω ↦ hω.1
    have hZc' : ∀ᵐ ω ∂P, Continuous (fun s ↦ Z i s ω) := ae_of_all _ (hZc i)
    have hv := continuous_integral_interaction P K hK.continuous hKb (Y i) (hY i).1 hYc
    have hw := continuous_integral_interaction P K hK.continuous hKb (Z i) (hZm i) hZc'
    have hmapY (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
        interactionDrift b₀ K x (P.map (Y i s)) = b₀ x + v s x := by
      rw [interactionDrift, integral_map ((hY i).1 s).aemeasurable
        (f := fun y ↦ K x y) (hK.continuous.measurable.comp
          ((measurable_const : Measurable fun _ : EuclideanSpace ℝ (Fin d) ↦ x).prodMk measurable_id)).aestronglyMeasurable]
    have hmapZ (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
        interactionDrift b₀ K x (P.map (Z i s)) = b₀ x + w s x := by
      rw [interactionDrift, integral_map (hZm i s).aemeasurable
        (f := fun y ↦ K x y) (hK.continuous.measurable.comp
          ((measurable_const : Measurable fun _ : EuclideanSpace ℝ (Fin d) ↦ x).prodMk measurable_id)).aestronglyMeasurable]
    apply ae_eq_of_interaction_integral_eq_on_Icc P b₀ hb₀ K hK κ.coe_nonneg hKb
      (Y i) (Z i) (hY i).1 (hZm i) hYc hZc' ht
    filter_upwards [(hY i).2.2, hZeq i] with ω hω hZω
    intro s hs
    have hvc : Continuous (fun r ↦ b₀ (Y i r ω) + v r (Y i r ω)) :=
      (hb₀.continuous.comp hω.1).add (hv.comp (continuous_id.prodMk hω.1))
    have hwc : Continuous (fun r ↦ b₀ (Z i r ω) + w r (Z i r ω)) :=
      (hb₀.continuous.comp (hZc i ω)).add (hw.comp (continuous_id.prodMk (hZc i ω)))
    have hYi : (∫ r in (0 : ℝ)..s, interactionDrift b₀ K (Y i r ω) (P.map (Y i r))) =
        ∫ r in (0 : ℝ)..s, b₀ (Y i r ω) + v r (Y i r ω) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hmapY r _
    have hZi : (∫ r in (0 : ℝ)..s, interactionDrift b₀ K (Z i r ω) (P.map (Z i r))) =
        ∫ r in (0 : ℝ)..s, b₀ (Z i r ω) + w r (Z i r ω) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hmapZ r _
    rw [hω.2 s hs.1, hZω s hs, hYi, hZi,
      intervalIntegral.integral_sub (hvc.intervalIntegrable _ _) (hwc.intervalIntegrable _ _)]
    abel
  have haet (i : ℕ) : Y i t =ᵐ[P] Z i t := (hae i).mono fun ω hω ↦ hω t ⟨ht, le_rfl⟩
  refine ⟨(hZind t).congr (fun i ↦ (haet i).symm), fun i ↦ ?_⟩
  exact (Measure.map_congr (haet i)).trans (hZmap i t ⟨ht, le_rfl⟩)

/-- Integrability and mean bound for time-integrated interaction fluctuations of nonlinear
solutions driven by iid initial conditions and Brownian motions. -/
theorem integrable_integral_sq_interactionFluctuation_le_of_solutions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {L_K κ : ℝ≥0} (hK : LipschitzWith L_K (Function.uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (hiid : IsIIDInitialAndDrivers P X₀ W μ₀)
    (Y : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : ∀ i, IsMcKeanVlasovSolution (interactionDrift b₀ K) (X₀ i) (W i) (Y i) P)
    {N : ℕ} (hN : 0 < N) (i : Fin N) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω ↦ ∫ t in (0 : ℝ)..T, ‖interactionFluctuation P K Y N i t ω‖ ^ 2) P ∧
      (∫ ω, (∫ t in (0 : ℝ)..T, ‖interactionFluctuation P K Y N i t ω‖ ^ 2) ∂P) ≤
        T * (16 * (κ : ℝ) ^ 2 / (N : ℝ)) := by
  apply integrable_integral_sq_interactionFluctuation_le P K hK.continuous hKb Y
    (fun j ↦ (hY j).1) (fun j ↦ (hY j).2.2.mono fun _ hω ↦ hω.1) hN i hT
  intro s hs
  have hi := IsMcKeanVlasovSolution.iIndepFun_interactionDrift P b₀ hb₀ K hK hKb X₀ W μ₀ hiid Y hY s hs.1
  let μ := P.map (Y 0 s)
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff ((hY 0).1 s).aemeasurable).mpr inferInstance
  have hvar := integral_norm_empiricalInteraction_sub_sq_le P μ K hK.continuous.measurable κ hKb hN
    (fun j : Fin N ↦ Y j s) (fun j ↦ (hY j).1 s)
    (iIndepFun.precomp Fin.val_injective hi.1) (fun j ↦ hi.2 j) i
  have hmap (x : EuclideanSpace ℝ (Fin d)) : (∫ z, K x z ∂μ) = ∫ z, K x (Y 0 s z) ∂P := by
    exact integral_map ((hY 0).1 s).aemeasurable
      (hK.continuous.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  simpa only [interactionFluctuation, hmap] using hvar

/-- Integration of a vector-valued function against the empirical measure. -/
theorem integral_empiricalMeasure_vector {E F : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {N : ℕ} (x : Fin N → E) (f : E → F) :
    (∫ y, f y ∂empiricalMeasure N x) = (N : ℝ)⁻¹ • ∑ j, f (x j) := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp
  · intro j _
    exact integrable_dirac (by finiteness)

/-- Same-forcing particle and nonlinear solutions satisfy the residual coupling equation. -/
theorem IsParticleSystem.ae_residual_integral_eq
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀)
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {L_K κ : ℝ≥0} (hK : LipschitzWith L_K (Function.uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ κ)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    {N : ℕ} (X Y : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : IsParticleSystem (interactionDrift b₀ K) X₀ W N X P)
    (hY : ∀ i, IsMcKeanVlasovSolution (interactionDrift b₀ K) (X₀ i) (W i) (Y i) P)
    (hmap : ∀ i s, 0 ≤ s → P.map (Y i s) = P.map (Y 0 s)) :
    ∀ᵐ ω ∂P, ∀ i : Fin N, ∀ t ≥ 0, X i t ω - Y i t ω = ∫ s in (0 : ℝ)..t,
      b₀ (X i s ω) - b₀ (Y i s ω) +
        (N : ℝ)⁻¹ • ∑ j : Fin N, (K (X i s ω) (X j s ω) - K (Y i s ω) (Y j s ω)) +
          interactionFluctuation P K Y N i s ω := by
  have hcY (i : ℕ) := (hY i).2.2.mono fun _ hω ↦ hω.1
  have hmean (i : ℕ) := continuous_integral_interaction P K hK.continuous hKb
    (Y i) (hY i).1 (hcY i)
  have hmc (i : ℕ) (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
      interactionDrift b₀ K z (P.map (Y i s)) = b₀ z + ∫ ω, K z (Y i s ω) ∂P := by
    rw [interactionDrift, integral_map ((hY i).1 s).aemeasurable
      (by exact (hK.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)]
  have hsame (i : ℕ) (s : ℝ) (hs : 0 ≤ s) (z : EuclideanSpace ℝ (Fin d)) :
      (∫ ω, K z (Y i s ω) ∂P) = ∫ ω, K z (Y 0 s ω) ∂P := by
    rw [← integral_map ((hY i).1 s).aemeasurable
      (by exact (hK.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable),
      hmap i s hs, integral_map ((hY 0).1 s).aemeasurable
      (by exact (hK.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)]
  have hxall : ∀ i : Fin N, ∀ᵐ ω ∂P, Continuous (fun t ↦ X i t ω) ∧
      ∀ t ≥ 0, X i t ω = X₀ i ω +
        (∫ s in (0 : ℝ)..t, interactionDrift b₀ K (X i s ω)
          (empiricalMeasure N fun j : Fin N ↦ X j s ω)) + W i t.toNNReal ω :=
    fun i ↦ hX.2 i i.isLt
  filter_upwards [ae_all_iff.2 hxall, ae_all_iff.2 (fun i : ℕ ↦ (hY i).2.2)] with ω hx hy
  intro i t ht
  let F : ℝ → EuclideanSpace ℝ (Fin d) := fun s ↦ b₀ (X i s ω) +
    (N : ℝ)⁻¹ • ∑ j : Fin N, K (X i s ω) (X j s ω)
  let G : ℝ → EuclideanSpace ℝ (Fin d) := fun s ↦ b₀ (Y i s ω) + ∫ z, K (Y i s ω) (Y i s z) ∂P
  have hFc : Continuous F := by
    have hsum : Continuous (fun s ↦ ∑ j : Fin N, K (X i s ω) (X j s ω)) := by
      exact continuous_finsetSum _ fun j _ ↦ hK.continuous.comp ((hx i).1.prodMk (hx j).1)
    exact (hb₀.continuous.comp (hx i).1).add (hsum.const_smul ((N : ℝ)⁻¹))
  have hGc : Continuous G := (hb₀.continuous.comp (hy i).1).add
    ((hmean i).comp (continuous_id.prodMk (hy i).1))
  have heqX := (hx i).2 t ht
  have heqY := (hy i).2 t ht
  have hXi : (∫ s in (0 : ℝ)..t, interactionDrift b₀ K (X i s ω)
      (empiricalMeasure N fun j : Fin N ↦ X j s ω)) = ∫ s in (0 : ℝ)..t, F s := by
    apply intervalIntegral.integral_congr
    intro s _
    change b₀ (X i s ω) + (∫ z, K (X i s ω) z ∂empiricalMeasure N (fun j : Fin N ↦ X j s ω)) = _
    rw [integral_empiricalMeasure_vector]
  have hYi : (∫ s in (0 : ℝ)..t, interactionDrift b₀ K (Y i s ω)
      (P.map (Y i s))) = ∫ s in (0 : ℝ)..t, G s := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hmc i s _
  rw [hXi] at heqX
  rw [hYi] at heqY
  calc X i t ω - Y i t ω = (∫ s in (0 : ℝ)..t, F s) - ∫ s in (0 : ℝ)..t, G s := by
        rw [heqX, heqY]
        abel
    _ = ∫ s in (0 : ℝ)..t, F s - G s :=
      (intervalIntegral.integral_sub (hFc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by rw [uIcc_of_le ht] at hs; exact hs.1
      dsimp only [F, G]
      rw [hsame i s hs0, interactionFluctuation, Finset.sum_sub_distrib, smul_sub]
      abel

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
  let R := max T 1
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right T 1)
  have hTR : T ≤ R := le_max_left T 1
  let A := 2 * R * Real.exp (((L₀ : ℝ) + L_K) * R) ^ 2 *
    (1 + ((L_K : ℝ) * R * Real.exp (((L₀ : ℝ) + L_K + L_K) * R)) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨32 * A * R * (κ : ℝ) ^ 2, ?_⟩
  intro Ω _ P _ d b₀ K hb₀ hKb hK X₀ W μ₀ hiid h2 X Y hX hY N i hi
  clear h2
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  let i' : Fin N := ⟨i, hi⟩
  let f : Fin N → Ω → ℝ := fun j ω ↦ ∫ s in (0 : ℝ)..R, ‖interactionFluctuation P K Y N j s ω‖ ^ 2
  have hfe (j : Fin N) := integrable_integral_sq_interactionFluctuation_le_of_solutions
    P b₀ hb₀ K hK hKb X₀ W μ₀ hiid Y hY hN j hR
  have hfnn (j : Fin N) : ∀ᵐ ω ∂P, 0 ≤ f j ω :=
    ae_of_all _ fun ω ↦ intervalIntegral.integral_nonneg_of_forall hR (fun _ ↦ sq_nonneg _)
  have hmap (j : ℕ) (s : ℝ) (hs : 0 ≤ s) : P.map (Y j s) = P.map (Y 0 s) :=
    (IsMcKeanVlasovSolution.iIndepFun_interactionDrift P b₀ hb₀ K hK hKb X₀ W μ₀ hiid Y hY s hs).2 j
  have heq := IsParticleSystem.ae_residual_integral_eq P b₀ hb₀ K hK hKb X₀ W (X N) Y (hX N) hY hmap
  have hcR := interactionFluctuation_measurable_ae_continuous P K hK.continuous hKb Y
    (fun j ↦ (hY j).1) (fun j ↦ (hY j).2.2.mono fun _ hω ↦ hω.1) N
  have hbound : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, ‖X N i t ω - Y i t ω‖ ^ 2 ≤
      A * (f i' ω + (N : ℝ)⁻¹ * ∑ j, f j ω) := by
    filter_upwards [heq, ae_all_iff.2 (fun j : Fin N ↦ (hX N).2 j j.isLt),
      ae_all_iff.2 (fun j : ℕ ↦ (hY j).2.2), ae_all_iff.2 hcR.2] with ω hω hx hy hr
    have hdet := norm_sub_sq_le_residual_energy hN b₀ hb₀ K hK
      (fun j : Fin N ↦ fun t ↦ X N j t ω) (fun j : Fin N ↦ fun t ↦ Y j t ω)
      (fun j t ↦ interactionFluctuation P K Y N j t ω)
      (fun j ↦ (hx j).1) (fun j ↦ (hy j).1) hr hR (fun j t ht ↦ hω j t ht.1)
    intro t ht
    exact hdet i' t ⟨ht.1, ht.2.trans hTR⟩
  have hfin := lintegral_iSup_enorm_sq_le_of_individual_add_average_bound P i' f
    (fun j ↦ (hfe j).1) hfnn A (R * (16 * (κ : ℝ) ^ 2 / (N : ℝ))) hA
    (fun j ↦ (hfe j).2) (fun ω t ↦ X N i t ω - Y i t ω) (Icc (0 : ℝ) T) hbound
  convert hfin using 1
  congr 1
  ring

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
