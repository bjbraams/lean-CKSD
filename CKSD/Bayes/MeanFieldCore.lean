module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-!
# Core definitions for McKean–Vlasov and finite-particle equations

Additive Brownian forcing permits a pathwise integral formulation. This module defines the
nonlinear and finite-particle solution predicates, Wasserstein-Lipschitz drifts and iid input
families, and compares their countably sampled Brownian forcing laws using Mathlib's Gaussian
finite-dimensional distributions and independence APIs.

Sources: GAPS 104.51 and 104.56.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
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
theorem ident_distrib_countable_evals_of_is_pre_brownian_real {Ω I : Type*} [MeasurableSpace Ω]
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
theorem IsBrownianEuclidean.ident_distrib_countable_evals {Ω I : Type*} [MeasurableSpace Ω]
    [Countable I] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hB : IsBrownianEuclidean B P) (hC : IsBrownianEuclidean C P) (t : I → ℝ≥0) :
    IdentDistrib (fun ω i ↦ B (t i) ω) (fun ω i ↦ C (t i) ω) P P := by
  have hcoord (j : Fin d) : IdentDistrib (fun ω i ↦ B (t i) ω j) (fun ω i ↦ C (t i) ω j) P P :=
    ident_distrib_countable_evals_of_is_pre_brownian_real P _ _ (hB.1 j).toIsPreBrownianReal
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
theorem IsIIDInitialAndDrivers.ident_distrib_forcing_evals
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (hiid : IsIIDInitialAndDrivers P X₀ W μ₀) (t : I → ℝ≥0) (i j : ℕ) :
    IdentDistrib (fun ω q ↦ X₀ i ω + W i (t q) ω) (fun ω q ↦ X₀ j ω + W j (t q) ω) P P := by
  have hinit : IdentDistrib (X₀ i) (X₀ j) P P :=
    ⟨(hiid.1 i).aemeasurable, (hiid.1 j).aemeasurable, (hiid.2.1 i).trans (hiid.2.1 j).symm⟩
  have hdriver := IsBrownianEuclidean.ident_distrib_countable_evals P (W i) (W j)
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
theorem IsIIDInitialAndDrivers.i_indep_fun_forcing_evals
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

/-- Drift `b₀(x) + ∫ K(x, y) μ(dy)` of an interaction model. -/
def interactionDrift {d : ℕ} (b₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  b₀ x + ∫ y, K x y ∂μ

/-- Euclidean Brownian paths remain almost surely continuous after the nonnegative-time projection. -/
theorem IsBrownianEuclidean.ae_continuous_to_nn_real {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : IsBrownianEuclidean B P) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ ↦ B t.toNNReal ω) := by
  filter_upwards [ae_all_iff.2 (fun j : Fin d ↦ (hB.1 j).cont)] with ω hω
  have hc : Continuous (fun t : ℝ ↦ fun j : Fin d ↦ B t.toNNReal ω j) :=
    continuous_pi fun j ↦ (hω j).comp continuous_real_toNNReal
  convert (PiLp.continuous_toLp 2 _).comp hc using 1
  ext t j
  rfl

/-- On a continuous path, the continuous-map path constructor agrees with evaluation. -/
theorem path_on_apply_of_continuous_on {E : Type*} [TopologicalSpace E] [Zero E]
    (T : ℝ) (f : ℝ → E) (hf : ContinuousOn f (Icc 0 T)) (t : Icc (0 : ℝ) T) :
    pathOn T f t = f t := by
  simp only [pathOn, dite_eq_left hf]
  rfl

/-- Extending a constructed continuous path agrees with the original path on its interval. -/
theorem path_on_icc_extend_of_continuous_on {E : Type*} [TopologicalSpace E] [Zero E]
    {T : ℝ} (hT : 0 ≤ T) (f : ℝ → E) (hf : ContinuousOn f (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) : (pathOn T f).IccExtend hT t = f t := by
  rw [ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem (h := hT) (fun z ↦ pathOn T f z) ht]
  exact path_on_apply_of_continuous_on T f hf ⟨t, ht⟩

end CKSD
