module

public import CKSD.Bayes.Nonparametric
public import CKSD.Bayes.StickBreaking
public import CKSD.Bayes.DirichletConjugacy
public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Probability.Distributions.Dirichlet.Moments

/-!
# Dirichlet process: conjugacy, prediction, and stick breaking

A Dirichlet process law is a law on probability measures whose partition marginals are the
finite-dimensional Dirichlet laws of TauCeti (`IsDirichletProcess` with the identity map).
Posterior laws are specified as disintegrations (`IsPosteriorKernel`), so the statements apply to
every version of the posterior. The mean of a partition cell uses TauCeti's
`integral_eval_dirichletMeasure`.

## Main results

* `CKSD.integral_measureReal_of_isDirichletProcess`: the mean of `P(A)` is `α(A) / α(X)`.
* `CKSD.ae_isDirichletProcessLaw_posterior`: conjugacy.
* `CKSD.ae_integral_posterior_eq_polyaPredictiveLaw`: the Blackwell–MacQueen predictive law.
* `CKSD.isDirichletProcess_stickBreaking`: Sethuraman's stick-breaking representation.

Sethuraman's theorem is reduced to its canonical-space form
`CKSD.map_stickBreakingMeasure_cells_eq_dirichletMeasure` in `CKSD.Bayes.StickBreaking`: the
independent i.i.d. fraction and atom sequences have the law of the product of two infinite
product measures (`ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map`). The canonical
construction also yields the existence of Dirichlet process laws
(`CKSD.exists_isDirichletProcessLaw`), which completes the conjugacy theorem
`CKSD.ae_isDirichletProcess_posterior` of `CKSD.Bayes.DirichletConjugacy`.

Sources: GAPS 104.15.
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
  obtain ⟨hVm, hVi, hVl⟩ := hV
  obtain ⟨hθm, hθi, hθl⟩ := hθ
  refine ⟨hPm, fun A hA hA0 ↦ ?_, fun k hk A hAm hAd hAc hApos ↦ ?_⟩
  · -- A null set of the base measure receives no atom, almost surely.
    have hnot : ∀ n, ∀ᵐ ω ∂μ, θ n ω ∉ A := fun n ↦ by
      have h0 : μ (θ n ⁻¹' A) = 0 := by
        rw [← Measure.map_apply (hθm n) hA, hθl n, smul_apply, hA0, smul_zero]
      exact measure_eq_zero_iff_ae_notMem.mp h0
    filter_upwards [hP, ae_all_iff.mpr hnot] with ω hω hω'
    rw [hω, stickBreakingMeasure, Measure.sum_apply _ hA]
    simp [Measure.dirac_apply' _ hA, hω']
  · -- The partition masses are a measurable image of the two i.i.d. sequences.
    set W : Ω → (ℕ → ℝ) × (ℕ → X) := fun ω ↦ (fun n ↦ V n ω, fun n ↦ θ n ω)
    have hVm' : Measurable fun ω n ↦ V n ω := Measurable.of_eval hVm
    have hθm' : Measurable fun ω n ↦ θ n ω := Measurable.of_eval hθm
    have hW : μ.map W = (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 (α.real univ)).prod
        (Measure.infinitePi fun _ : ℕ ↦ (α univ)⁻¹ • α) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hVm'.aemeasurable hθm'.aemeasurable).mp hind,
        hVi.map_fun_eq_infinitePi_map hVm, hθi.map_fun_eq_infinitePi_map hθm]
      simp_rw [hVl, hθl]
    have hΦm : Measurable fun w : (ℕ → ℝ) × (ℕ → X) ↦
        WithLp.toLp 2 fun i ↦ (stickBreakingMeasure w.1 w.2).real (A i) :=
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦
        (measurable_stickBreakingMeasure_apply (hAm i)).ennreal_toReal)
    calc μ.map (fun ω ↦ WithLp.toLp 2 fun i ↦ (P ω : Measure X).real (A i))
        = μ.map ((fun w : (ℕ → ℝ) × (ℕ → X) ↦
            WithLp.toLp 2 fun i ↦ (stickBreakingMeasure w.1 w.2).real (A i)) ∘ W) :=
          Measure.map_congr (hP.mono fun ω hω ↦ by simp only [comp_apply, W, hω])
      _ = (μ.map W).map (fun w : (ℕ → ℝ) × (ℕ → X) ↦
            WithLp.toLp 2 fun i ↦ (stickBreakingMeasure w.1 w.2).real (A i)) :=
          (Measure.map_map hΦm (hVm'.prodMk hθm')).symm
      _ = _ := by
          rw [hW]
          exact map_stickBreakingMeasure_cells_eq_dirichletMeasure α hα hk hAm hAd hAc hApos

/-- **Existence of the Dirichlet process.** For every finite nonzero base measure there is a law of
a Dirichlet process: the law of Sethuraman's stick-breaking measure on the product of the
i.i.d. fraction and atom spaces, where the stick-breaking measure is almost surely a probability
measure (`CKSD.ae_tsum_stickBreakingWeight_eq_one`). -/
theorem exists_isDirichletProcessLaw {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (α : Measure X) [IsFiniteMeasure α] (hα : α ≠ 0) :
    ∃ Q : Measure (ProbabilityMeasure X), IsProbabilityMeasure Q ∧ IsDirichletProcessLaw Q α := by
  have : NeZero α := ⟨hα⟩
  have hs : 0 < α.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((Measure.measure_univ_ne_zero).2 hα) (measure_ne_top α univ)
  have := isProbabilityMeasureBeta one_pos hs
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra h
    have := not_nonempty_iff.mp h
    exact hα (Measure.eq_zero_of_isEmpty α)
  set β := betaMeasure 1 (α.real univ) with hβdef
  set G : Measure X := (α univ)⁻¹ • α
  set M := (Measure.infinitePi fun _ : ℕ ↦ β).prod (Measure.infinitePi fun _ : ℕ ↦ G)
  have hβ : ∀ᵐ x ∂β, x ∈ Icc (0 : ℝ) 1 := TauCeti.Probability.ae_mem_Icc_betaMeasure 1 (α.real univ)
  have hq : ∫ x, (1 - x) ∂β < 1 := by
    have hxint : Integrable (fun x : ℝ ↦ x) β :=
      Integrable.of_bound aestronglyMeasurable_id 1 (hβ.mono fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hx.1, hx.2])
    rw [integral_sub (integrable_const 1) hxint, integral_const, probReal_univ, one_smul, hβdef,
      TauCeti.Probability.integral_id_betaMeasure one_pos hs]
    have : 0 < 1 / (1 + α.real univ) := by positivity
    linarith
  have hmass : ∀ᵐ w ∂M, stickBreakingMeasure w.1 w.2 univ = 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_tsum_stickBreakingWeight_eq_one β hβ hq)] with w hw
    simpa [stickBreakingMeasure, Measure.sum_apply _ MeasurableSet.univ] using hw
  classical
  set P : (ℕ → ℝ) × (ℕ → X) → ProbabilityMeasure X := fun w ↦
    if h : stickBreakingMeasure w.1 w.2 univ = 1 then ⟨stickBreakingMeasure w.1 w.2, ⟨h⟩⟩
    else ⟨Measure.dirac x₀, inferInstance⟩ with hPdef
  have hPm : ∀ A, MeasurableSet A → Measurable fun w ↦ (P w : Measure X) A := by
    intro A hA
    have : (fun w ↦ (P w : Measure X) A) = fun w ↦
        if stickBreakingMeasure w.1 w.2 univ = 1 then stickBreakingMeasure w.1 w.2 A
        else Measure.dirac x₀ A := by
      funext w
      by_cases h : stickBreakingMeasure w.1 w.2 univ = 1 <;> simp [P, h]
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun
      (measurable_stickBreakingMeasure_apply MeasurableSet.univ) measurable_const)
      (measurable_stickBreakingMeasure_apply hA) measurable_const
  have hPmeas : Measurable P := by
    have h' : Measurable fun w ↦ (P w : Measure X) := Measure.measurable_of_measurable_coe _ hPm
    exact h'.subtype_mk
  have hP : ∀ᵐ w ∂M, (P w : Measure X) =
      stickBreakingMeasure (fun k ↦ w.1 k) (fun k ↦ w.2 k) := by
    filter_upwards [hmass] with w hw
    simp [P, hw]
  have hfst : M.map Prod.fst = Measure.infinitePi fun _ : ℕ ↦ β := by
    simp [M, Measure.map_fst_prod]
  have hsnd : M.map Prod.snd = Measure.infinitePi fun _ : ℕ ↦ G := by
    simp [M, Measure.map_snd_prod]
  have hV : IsIndependentIdenticallyDistributed M (fun k w ↦ w.1 k) β := by
    have hlaw : ∀ k, M.map (fun w : (ℕ → ℝ) × (ℕ → X) ↦ w.1 k) = β := fun k ↦ by
      rw [show (fun w : (ℕ → ℝ) × (ℕ → X) ↦ w.1 k) = Function.eval k ∘ Prod.fst from rfl,
        ← Measure.map_map (measurable_pi_apply k) measurable_fst, hfst,
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ β) k).map_eq]
    refine ⟨fun k ↦ (measurable_pi_apply k).comp measurable_fst,
      (iIndepFun_iff_map_fun_eq_infinitePi_map
        (X := fun k (w : (ℕ → ℝ) × (ℕ → X)) ↦ w.1 k)
        (fun k ↦ (measurable_pi_apply k).comp measurable_fst)).mpr ?_, hlaw⟩
    simp_rw [hlaw]
    exact hfst
  have hθ : IsIndependentIdenticallyDistributed M (fun k w ↦ w.2 k) G := by
    have hlaw : ∀ k, M.map (fun w : (ℕ → ℝ) × (ℕ → X) ↦ w.2 k) = G := fun k ↦ by
      rw [show (fun w : (ℕ → ℝ) × (ℕ → X) ↦ w.2 k) = Function.eval k ∘ Prod.snd from rfl,
        ← Measure.map_map (measurable_pi_apply k) measurable_snd, hsnd,
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ G) k).map_eq]
    refine ⟨fun k ↦ (measurable_pi_apply k).comp measurable_snd,
      (iIndepFun_iff_map_fun_eq_infinitePi_map
        (X := fun k (w : (ℕ → ℝ) × (ℕ → X)) ↦ w.2 k)
        (fun k ↦ (measurable_pi_apply k).comp measurable_snd)).mpr ?_, hlaw⟩
    simp_rw [hlaw]
    exact hsnd
  have hind : IndepFun (fun w k ↦ w.1 k) (fun w k ↦ w.2 k) M :=
    (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).mpr (by
        change M.map id = (M.map Prod.fst).prod (M.map Prod.snd)
        rw [Measure.map_id, hfst, hsnd])
  have hDP := isDirichletProcess_stickBreaking M α hα _ _ hV hθ hind P hPm hP
  have hcoe : ∀ A, MeasurableSet A →
      Measurable fun θ : ProbabilityMeasure X ↦ (θ : Measure X) A := fun A hA ↦
    (Measure.measurable_coe hA).comp measurable_subtype_coe
  refine ⟨M.map P, (Measure.isProbabilityMeasure_map_iff hPmeas.aemeasurable).mpr inferInstance,
    hcoe, fun A hA h0 ↦ ?_, fun k hk A hAm hAd hAc hApos ↦ ?_⟩
  · exact (ae_map_iff hPmeas.aemeasurable (measurableSet_eq_fun (hcoe A hA)
      measurable_const)).mpr (hDP.2.1 A hA h0)
  · have hg : Measurable fun θ : ProbabilityMeasure X ↦
        WithLp.toLp 2 fun i ↦ (θ : Measure X).real (A i) :=
      (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦
        (hcoe _ (hAm i)).ennreal_toReal)
    simp only [id_eq]
    rw [Measure.map_map hg hPmeas]
    exact hDP.2.2 k hk A hAm hAd hAc hApos

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
  refine ae_isDirichletProcess_posterior α hα prior hprior Q hQ post hpost fun x ↦ ?_
  have : IsFiniteMeasure (dirichletPosteriorBase α x) := by
    unfold dirichletPosteriorBase
    infer_instance
  refine exists_isDirichletProcessLaw _ fun h ↦ hα ?_
  have : α ≤ dirichletPosteriorBase α x := Measure.le_add_right le_rfl
  rw [h] at this
  exact le_antisymm this (Measure.zero_le _)

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

end CKSD
