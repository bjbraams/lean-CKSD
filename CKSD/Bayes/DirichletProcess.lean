module

public import CKSD.Bayes.Nonparametric
public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Probability.Distributions.Dirichlet.Moments

/-!
# Dirichlet process: conjugacy, prediction, and stick breaking

A Dirichlet process law is a law on probability measures whose partition marginals are the
finite-dimensional Dirichlet laws of TauCeti (`IsDirichletProcess` with the identity map).
Posterior laws are specified as disintegrations (`IsPosteriorKernel`), so the statements apply to
every version of the posterior. The mean of a partition cell uses TauCeti's
`integral_eval_dirichletMeasure`. Sources: GAPS 104.15.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- A law on probability measures is the law of a Dirichlet process with base measure `α`. -/
def IsDirichletProcessLaw {X : Type*} [MeasurableSpace X]
    (Q : Measure (ProbabilityMeasure X)) (α : Measure X) : Prop :=
  IsDirichletProcess Q id α

/-- The mean of a cell of a Dirichlet process is its share of the base measure.
TauCeti's Dirichlet mean is applied to the two-cell partition `{A, Aᶜ}`. -/
theorem integral_measureReal_of_isDirichletProcess {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → ProbabilityMeasure X)
    (α : Measure X) [IsFiniteMeasure α] (hα : α ≠ 0) (hP : IsDirichletProcess μ P α)
    (A : Set X) (hA : MeasurableSet A) :
    ∫ ω, (P ω : Measure X).real A ∂μ = α.real A / α.real univ := by
  obtain ⟨hmeas, hnull, hlaw⟩ := hP
  have huniv : α.real univ ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(Measure.measure_univ_ne_zero).2 hα, measure_ne_top α univ⟩
  have hsplit : α.real A + α.real Aᶜ = α.real univ := measureReal_add_measureReal_compl hA
  by_cases h0 : α A = 0
  · have hae : ∀ᵐ ω ∂μ, (P ω : Measure X).real A = 0 := by
      filter_upwards [hnull A hA h0] with ω hω
      simp [measureReal_def, hω]
    rw [integral_congr_ae hae, integral_zero, measureReal_def, h0, ENNReal.toReal_zero,
      zero_div]
  by_cases h1 : α Aᶜ = 0
  · have hae : ∀ᵐ ω ∂μ, (P ω : Measure X).real A = 1 := by
      filter_upwards [hnull Aᶜ hA.compl h1] with ω hω
      have := measureReal_add_measureReal_compl (μ := (P ω : Measure X)) hA
      rw [measureReal_def (s := Aᶜ), hω, ENNReal.toReal_zero, add_zero, probReal_univ] at this
      exact this
    have hc : α.real Aᶜ = 0 := by rw [measureReal_def, h1, ENNReal.toReal_zero]
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul, ← hsplit, hc, add_zero,
      div_self (by rwa [← hsplit, hc, add_zero] at huniv)]
  -- Both cells have positive base mass: use the two-cell Dirichlet marginal.
  set B : Fin 2 → Set X := ![A, Aᶜ] with hB
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i; fin_cases i
    exacts [hA, hA.compl]
  have hBd : Pairwise (Disjoint on B) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact absurd rfl hij
  have hBu : (⋃ i, B i)ᶜ = ∅ := by
    rw [compl_empty_iff, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ A
    · exact mem_iUnion.2 ⟨0, hx⟩
    · exact mem_iUnion.2 ⟨1, hx⟩
  have hBpos : ∀ i, 0 < α (B i) := by
    intro i; fin_cases i
    exacts [pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 h1]
  have hmap := hlaw 2 (by norm_num) B hBm hBd (by rw [hBu, measure_empty]) hBpos
  set F : Ω → EuclideanSpace ℝ (Fin 2) :=
    fun ω ↦ WithLp.toLp 2 (fun i ↦ (P ω : Measure X).real (B i)) with hF
  have hFm : Measurable F := by
    refine (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i ↦ ?_)
    exact (hmeas (B i) (hBm i)).ennreal_toReal
  have hapos : ∀ i, 0 < α.real (B i) := by
    intro i
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hBpos i).ne' (measure_ne_top α _)
  calc
    ∫ ω, (P ω : Measure X).real A ∂μ = ∫ ω, F ω 0 ∂μ := rfl
    _ = ∫ v, v 0 ∂(μ.map F) := by
      rw [integral_map hFm.aemeasurable (by fun_prop)]
    _ = α.real A / α.real univ := by
      rw [hmap, TauCeti.Probability.integral_eval_dirichletMeasure hapos, Fin.sum_univ_two]
      simp [hB, hsplit]

/-- GAPS 104.15: conjugacy of the Dirichlet process. For every version of the posterior given `n`
conditionally independent observations, the posterior is a.s. a Dirichlet process with base
`α + ∑ δ_{xᵢ}`. -/
theorem ae_isDirichletProcessLaw_posterior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (α : Measure X) [IsFiniteMeasure α] (hα : α ≠ 0)
    (prior : Measure (ProbabilityMeasure X)) [IsProbabilityMeasure prior]
    (hprior : IsDirichletProcessLaw prior α) (n : ℕ)
    (Q : Kernel (ProbabilityMeasure X) (Fin n → X))
    (hQ : ∀ θ, Q θ = Measure.pi fun _ : Fin n ↦ (θ : Measure X))
    (post : Kernel (Fin n → X) (ProbabilityMeasure X)) (hpost : IsPosteriorKernel prior Q post) :
    ∀ᵐ x ∂(Q ∘ₘ prior), IsDirichletProcessLaw (post x) (dirichletPosteriorBase α x) := by
  sorry

/-- GAPS 104.15: the Blackwell–MacQueen predictive law is the posterior mean of the random
measure, granted posterior conjugacy (`ae_isDirichletProcessLaw_posterior`). -/
theorem ae_integral_posterior_eq_polyaPredictiveLaw {X : Type*} [MeasurableSpace X]
    (α : Measure X) [IsFiniteMeasure α] (hα : α ≠ 0) {n : ℕ}
    (post : Kernel (Fin n → X) (ProbabilityMeasure X)) [IsMarkovKernel post]
    (ν : Measure (Fin n → X))
    (hconj : ∀ᵐ x ∂ν, IsDirichletProcessLaw (post x) (dirichletPosteriorBase α x)) :
    ∀ᵐ x ∂ν, ∀ A, MeasurableSet A →
      ∫ θ, (θ : Measure X).real A ∂(post x) = (polyaPredictiveLaw α x).real A := by
  filter_upwards [hconj] with x hx A hA
  have hβne : dirichletPosteriorBase α x ≠ 0 := by
    intro h
    apply hα
    have : α ≤ dirichletPosteriorBase α x := Measure.le_add_right le_rfl
    rw [h] at this
    exact le_antisymm this (Measure.zero_le _)
  have hfin : IsFiniteMeasure (dirichletPosteriorBase α x) := by
    unfold dirichletPosteriorBase; infer_instance
  have hmean := integral_measureReal_of_isDirichletProcess (post x) id _ hβne hx A hA
  simp only [id] at hmean
  rw [hmean]
  have hu : dirichletPosteriorBase α x univ = α univ + n := by
    simp [dirichletPosteriorBase]
  simp only [polyaPredictiveLaw, measureReal_def, smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, hu]
  rw [div_eq_inv_mul]

/-- GAPS 104.15: Sethuraman's stick-breaking representation. With independent `Beta(1, |α|)`
fractions and independent atoms of law `α / |α|`, independent of each other, every measurable
random probability measure agreeing a.s. with `∑ πₖ δ_{θₖ}` is a Dirichlet process. -/
theorem isDirichletProcess_stickBreaking {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α : Measure X) [IsFiniteMeasure α] (hα : α ≠ 0) (V : ℕ → Ω → ℝ) (θ : ℕ → Ω → X)
    (hV : IsIndependentIdenticallyDistributed μ V (betaMeasure 1 (α.real univ)))
    (hθ : IsIndependentIdenticallyDistributed μ θ ((α univ)⁻¹ • α))
    (hind : IndepFun (fun ω k ↦ V k ω) (fun ω k ↦ θ k ω) μ)
    (P : Ω → ProbabilityMeasure X)
    (hPm : ∀ A, MeasurableSet A → Measurable fun ω ↦ (P ω : Measure X) A)
    (hP : ∀ᵐ ω ∂μ, (P ω : Measure X) = stickBreakingMeasure (fun k ↦ V k ω) (fun k ↦ θ k ω)) :
    IsDirichletProcess μ P α := by
  sorry

end CKSD
