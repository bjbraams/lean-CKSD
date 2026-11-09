module

public import CKSD.Bayes.Nonparametric
public import CKSD.Asymptotics.Basic
public import Statlib.Divergence.Hellinger.Basic
public import CKSD.Bayes.ExponentialTests
public import CKSD.Bayes.EvidenceBounds
public import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Dominated posteriors and posterior contraction

For a dominated model with densities `f θ`, the posterior after `n` observations is the prior
reweighted by the product likelihood and normalized. Its value at samples with zero evidence
follows the zero-measure normalization convention; the consistency theorems only control it
under the true sampling law. Hellinger distance reuses Statlib's `sqHellinger`, with a factor
two to obtain the convention `h² = ∫ (√p - √q)²` of `GAPS.md`.

## Main definitions

* `CKSD.dominatedPosterior`: the posterior of a dominated model.
* `CKSD.statisticalHellingerDistance`: Hellinger distance in the convention `h² = ∫ (√p - √q)²`.
* `CKSD.HasUniformlyConsistentTests`, `CKSD.HasHellingerSieveCover`: uniformly consistent tests
  and finite Hellinger covers of sieves with an entropy bound.

## Main results

* `CKSD.tendstoInMeasure_posterior_compl_of_kl_support`: Schwartz's posterior
  consistency theorem (GAPS 104.18).
* `CKSD.exists_posterior_hellinger_contraction`: the Ghosal–Ghosh–van der Vaart contraction
  theorem in Hellinger distance (GAPS 104.19).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Posterior measure obtained by multiplying a prior by the finite-sample likelihood. -/
def dominatedPosterior {Θ X : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) (f : Θ → X → ℝ) {n : ℕ} (x : Fin n → X) : Measure Θ :=
  let unnormalized := π.withDensity (fun θ ↦ ENNReal.ofReal (∏ i, f θ (x i)))
  (unnormalized univ)⁻¹ • unnormalized

/-- Real Hellinger adapter in the convention `h² = integral (sqrt p - sqrt q)²`
for probability measures. For arbitrary measures an infinite squared divergence is totalized to
zero by `ENNReal.toReal`; distance interpretations require finite divergence. -/
def statisticalHellingerDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ := Real.sqrt (2 * (ProbabilityTheory.sqHellinger P Q).toReal)

/-- Existence of uniformly consistent tests against a fixed parameter set. -/
def HasUniformlyConsistentTests {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (θ₀ : Θ) (A : Set Θ) : Prop :=
  ∃ φ : ∀ n : ℕ, (Fin n → X) → ℝ,
    (∀ n : ℕ, IsStatisticalTest (φ n)) ∧
    Tendsto (fun n : ℕ ↦ ∫ x, φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ ∈ A,
      (∫ x, 1 - φ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ ε

/-- The integrated likelihood `x ↦ ∫ ofReal (∏ᵢ f θ (xᵢ)) dπ(θ)` is measurable. -/
private theorem measurable_lintegral_ofReal_prod {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] (π : Measure Θ) [SFinite π] (f : Θ → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (n : ℕ) :
    Measurable fun x : Fin n → X ↦ ∫⁻ θ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π :=
  Measurable.lintegral_prod_right' (f := fun p : (Fin n → X) × Θ ↦
    ENNReal.ofReal (∏ i, f p.2 (p.1 i)))
    (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      hf.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))))

/-- The `n`-fold product of a dominated law has the product density with respect to `μ^n`,
almost everywhere equal to `ofReal (∏ᵢ f θ (xᵢ))`. This uses TauCeti's `pi_withDensity`. -/
private theorem pi_eq_withDensity_ofReal_prod {Θ X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ : Θ) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ P θ) =
      (Measure.pi fun _ : Fin n ↦ μ).withDensity fun x ↦ ENNReal.ofReal (∏ i, f θ (x i)) := by
  have : SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (f θ x)) := by
    rw [← (hdensity θ).2.2]; infer_instance
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), ∀ i, 0 ≤ f θ (x i) := by
    rw [ae_all_iff]
    exact fun i ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i).ae (hdensity θ).2.1
  rw [(hdensity θ).2.2, TauCeti.pi_withDensity _ fun _ ↦ (hdensity θ).1.ennreal_ofReal]
  refine withDensity_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hx i]

/-- **Change of measure for the posterior numerator.** If a test `ψ` has type II error at most
`b` at every `θ ∈ Uᶜ`, then under the true law the expectation of `(1 - ψ)` times the unnormalized
posterior mass of `Uᶜ`, divided by the true likelihood, is at most `b`. -/
private theorem lintegral_one_sub_test_mul_numerator_le {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ) (U : Set Θ) (n : ℕ)
    (ψ : (Fin n → X) → ℝ) (hψ : IsStatisticalTest ψ) {b : ℝ}
    (hb : ∀ θ ∈ Uᶜ, ∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ) ≤ b) :
    ∫⁻ x, ENNReal.ofReal (1 - ψ x) *
        ((∫⁻ θ in Uᶜ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) /
          ENNReal.ofReal (∏ i, f θ₀ (x i))) ∂(Measure.pi fun _ : Fin n ↦ P θ₀) ≤
      ENNReal.ofReal b := by
  set ν := Measure.pi fun _ : Fin n ↦ μ
  have hL : Measurable fun p : (Fin n → X) × Θ ↦ ENNReal.ofReal (∏ i, f p.2 (p.1 i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      hf.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)))
  have hL0 : Measurable fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ₀ (x i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      (hdensity θ₀).1.comp (measurable_pi_apply i))
  have hψm : Measurable fun x ↦ ENNReal.ofReal (1 - ψ x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub hψ.1)
  have hN : Measurable fun x : Fin n → X ↦ ∫⁻ θ in Uᶜ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π :=
    hL.lintegral_prod_right'
  have hG : Measurable fun x ↦ ENNReal.ofReal (1 - ψ x) *
      ((∫⁻ θ in Uᶜ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) / ENNReal.ofReal (∏ i, f θ₀ (x i))) :=
    hψm.mul (hN.div hL0)
  rw [pi_eq_withDensity_ofReal_prod μ P f hdensity θ₀ n,
    lintegral_withDensity_eq_lintegral_mul _ hL0 hG]
  calc ∫⁻ x, ((fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ₀ (x i))) *
        fun x : Fin n → X ↦ ENNReal.ofReal (1 - ψ x) *
          ((∫⁻ θ in Uᶜ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) /
            ENNReal.ofReal (∏ i, f θ₀ (x i)))) x ∂ν
      ≤ ∫⁻ x, ∫⁻ θ in Uᶜ, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂π ∂ν := by
        refine lintegral_mono fun x ↦ ?_
        have hLx : Measurable fun θ ↦ ENNReal.ofReal (∏ i, f θ (x i)) :=
          hL.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ hLx]
        simp only [Pi.mul_apply]
        rw [mul_left_comm]
        exact mul_le_mul_right ENNReal.mul_div_le _
    _ = ∫⁻ θ in Uᶜ, ∫⁻ x, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂ν ∂π :=
        lintegral_lintegral_swap ((hψm.comp measurable_fst).mul hL).aemeasurable
    _ ≤ ∫⁻ _ in Uᶜ, ENNReal.ofReal b ∂π := by
        refine setLIntegral_mono measurable_const fun θ hθ ↦ ?_
        have hint : Integrable (fun x ↦ 1 - ψ x) (Measure.pi fun _ : Fin n ↦ P θ) :=
          Integrable.of_mem_Icc 0 1 (measurable_const.sub hψ.1).aemeasurable
            (ae_of_all _ fun x ↦ ⟨by linarith [(hψ.2 x).2], by linarith [(hψ.2 x).1]⟩)
        calc ∫⁻ x, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂ν
            = ∫⁻ x, ENNReal.ofReal (1 - ψ x) ∂(Measure.pi fun _ : Fin n ↦ P θ) := by
              have hLθ : Measurable fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ (x i)) :=
                hL.comp (measurable_id.prodMk measurable_const)
              rw [pi_eq_withDensity_ofReal_prod μ P f hdensity θ n,
                lintegral_withDensity_eq_lintegral_mul _ hLθ hψm]
              exact lintegral_congr fun x ↦ mul_comm _ _
          _ = ENNReal.ofReal (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ)) :=
              (ofReal_integral_eq_lintegral_ofReal hint
                (ae_of_all _ fun x ↦ sub_nonneg.2 (hψ.2 x).2)).symm
          _ ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal (hb θ hθ)
    _ ≤ ENNReal.ofReal b := by
        rw [setLIntegral_const]
        exact mul_le_of_le_one_right' prob_le_one

/-- GAPS 104.18: Schwartz's posterior consistency theorem. If the prior charges every
Kullback–Leibler neighbourhood `{θ | KL(P θ₀ ‖ P θ) < ε}` of the true parameter and there are
uniformly consistent tests of `θ₀` against `Uᶜ`, then the posterior mass of `Uᶜ` tends to zero in
probability under the true law. -/
theorem tendstoInMeasure_posterior_compl_of_kl_support
    {Θ X : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ)
    (hKLmeas : ∀ ε > 0, MeasurableSet {θ | klDiv (P θ₀) (P θ) < ENNReal.ofReal ε})
    (hKL : ∀ ε > 0, 0 < π {θ | klDiv (P θ₀) (P θ) < ENNReal.ofReal ε})
    (U : Set Θ) (hU : MeasurableSet U)
    (htests : HasUniformlyConsistentTests P θ₀ Uᶜ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun (n : ℕ) x ↦ (dominatedPosterior π f (fun i : Fin n ↦ x i.val)).real Uᶜ)
          atTop (fun _ ↦ 0) := by
  classical
  obtain ⟨φ, hφ, h0, h1⟩ := htests
  obtain ⟨β, hβ, ψ, hψ, hψb⟩ := exists_exponentiallyConsistent_tests P θ₀ Uᶜ φ hφ h0 h1
  set Pinf := Measure.infinitePi fun _ : ℕ ↦ P θ₀
  set γ := β / 2 with hγ
  set B := {θ | klDiv (P θ₀) (P θ) < ENNReal.ofReal γ}
  have hBm : MeasurableSet B := hKLmeas γ (by positivity)
  have hπB : 0 < π B := hKL γ (by positivity)
  have hπBtop : π B ≠ ∞ := measure_ne_top _ _
  have hπBr : 0 < π.real B := ENNReal.toReal_pos hπB.ne' hπBtop
  have hev := tendsto_infinitePi_evidence_lt π μ P f hf hdensity θ₀ hBm (fun θ hθ ↦ hθ)
  set C := Real.exp (1 / 8)
  have hexpto : ∀ a > 0, ∀ c : ℝ, Tendsto (fun n : ℕ ↦ c * Real.exp (-a * n)) atTop (𝓝 0) := by
    intro a ha c
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos ha)))
    simpa using (tendsto_const_nhds (x := c)).mul this
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let N : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦
    ∫⁻ θ in Uᶜ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π
  let D : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦ ∫⁻ θ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π
  let L₀ : ∀ n : ℕ, (Fin n → X) → ℝ := fun n x ↦ ∏ i, f θ₀ (x i)
  let r : ∀ n : ℕ, (ℕ → X) → (Fin n → X) := fun n ω i ↦ ω i
  have hr : ∀ n, Measurable (r n) := fun n ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_apply _
  let K : ℕ → ℝ := fun n ↦ ε / 4 * π.real B * Real.exp (-γ * n)
  have hKpos : ∀ n, 0 < K n := fun n ↦ by positivity
  let G : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦
    ENNReal.ofReal (1 - ψ n x) * (N n x / ENNReal.ofReal (L₀ n x))
  have hG : ∀ n, Measurable (G n) := fun n ↦
    (ENNReal.measurable_ofReal.comp (measurable_const.sub (hψ n).1)).mul
      ((measurable_lintegral_ofReal_prod _ f hf n).div
        (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
          (hdensity θ₀).1.comp (measurable_pi_apply i))))
  have hpost : ∀ n (x : Fin n → X),
      (dominatedPosterior π f x).real Uᶜ = ((D n x)⁻¹ * N n x).toReal := by
    intro n x
    simp [dominatedPosterior, measureReal_def, withDensity_apply _ hU.compl, D, N]
  let E1 : ℕ → Set (ℕ → X) := fun n ↦ {ω | 1 / 2 ≤ ψ n (r n ω)}
  let E2 : ℕ → Set (ℕ → X) := fun n ↦
    {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
        π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n))}
  let E3 : Set (ℕ → X) := {ω | ∃ i, f θ₀ (ω i) ≤ 0}
  let E4 : ℕ → Set (ℕ → X) := fun n ↦ {ω | ENNReal.ofReal (K n) ≤ G n (r n ω)}
  have hsub : ∀ n : ℕ, {ω : ℕ → X | ε ≤ dist
      ((dominatedPosterior π f (fun i : Fin n ↦ ω i.val)).real Uᶜ) 0} ⊆
      E1 n ∪ E2 n ∪ E3 ∪ E4 n := by
    intro n ω hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    rw [hpost, abs_of_nonneg ENNReal.toReal_nonneg] at hω
    by_contra hcon
    simp only [E1, E2, E3, E4, Set.mem_union, not_or, Set.mem_ofPred_eq, not_le, not_lt,
      not_exists] at hcon
    obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hcon
    have hL0pos : 0 < L₀ n (r n ω) := Finset.prod_pos fun i _ ↦ hc3 i
    have hlow : 0 < π B / 2 * ENNReal.ofReal (L₀ n (r n ω) * Real.exp (-γ * n)) :=
      ENNReal.mul_pos (by simp [hπB.ne'])
        (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact mul_pos hL0pos (Real.exp_pos _))
    have hDpos : D n (r n ω) ≠ 0 := (hlow.trans_le hc2).ne'
    have hDtop : D n (r n ω) ≠ ∞ := by
      intro h
      change ε ≤ ((D n (r n ω))⁻¹ * N n (r n ω)).toReal at hω
      rw [h] at hω
      simp at hω
      linarith
    have hNge : ENNReal.ofReal ε * D n (r n ω) ≤ N n (r n ω) := by
      have := ENNReal.ofReal_le_of_le_toReal hω
      calc ENNReal.ofReal ε * D n (r n ω)
          ≤ ((D n (r n ω))⁻¹ * N n (r n ω)) * D n (r n ω) := mul_le_mul_left this _
        _ = N n (r n ω) := by
          rw [mul_comm _ (N n (r n ω)), mul_assoc, ENNReal.inv_mul_cancel hDpos hDtop,
            mul_one]
    have hK : ENNReal.ofReal (K n) = ENNReal.ofReal (1 / 2) *
        (ENNReal.ofReal ε * (π B / 2 * ENNReal.ofReal (Real.exp (-γ * n)))) := by
      have hB2 : π B / 2 = ENNReal.ofReal (π.real B / 2) := by
        rw [ENNReal.ofReal_div_of_pos two_pos, measureReal_def, ENNReal.ofReal_toReal hπBtop]
        simp
      rw [hB2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      simp only [K]
      ring
    refine absurd hc4 (not_lt.2 ?_)
    rw [hK]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hL0pos])) (Or.inl ENNReal.ofReal_ne_top)]
    calc ENNReal.ofReal ε * (π B / 2 * ENNReal.ofReal (Real.exp (-γ * n))) *
          ENNReal.ofReal (L₀ n (r n ω))
        = ENNReal.ofReal ε * (π B / 2 * ENNReal.ofReal (L₀ n (r n ω) * Real.exp (-γ * n))) := by
          rw [ENNReal.ofReal_mul hL0pos.le]; ring
      _ ≤ ENNReal.ofReal ε * D n (r n ω) := mul_le_mul_right hc2 _
      _ ≤ N n (r n ω) := hNge
  have hmap : ∀ n, Pinf.map (r n) = Measure.pi fun _ : Fin n ↦ P θ₀ := fun n ↦
    infinitePi_map_fin_val (P θ₀) n
  have hE1 : ∀ n : ℕ, Pinf (E1 n) ≤
      ENNReal.ofReal (C * Real.exp (-β * n)) / ENNReal.ofReal (1 / 2) := by
    intro n
    have hm : Measurable fun ω ↦ ENNReal.ofReal (ψ n (r n ω)) :=
      ENNReal.measurable_ofReal.comp ((hψ n).1.comp (hr n))
    have hint : Integrable (ψ n) (Measure.pi fun _ : Fin n ↦ P θ₀) :=
      Integrable.of_mem_Icc 0 1 (hψ n).1.aemeasurable (ae_of_all _ (hψ n).2)
    calc Pinf (E1 n) ≤ Pinf {ω | ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (ψ n (r n ω))} :=
          measure_mono fun ω hω ↦ ENNReal.ofReal_le_ofReal hω
      _ ≤ (∫⁻ ω, ENNReal.ofReal (ψ n (r n ω)) ∂Pinf) / ENNReal.ofReal (1 / 2) :=
          meas_ge_le_lintegral_div hm.aemeasurable (by norm_num) ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine ENNReal.div_le_div_right ?_ _
          have hm' : Measurable fun x ↦ ENNReal.ofReal (ψ n x) :=
            ENNReal.measurable_ofReal.comp (hψ n).1
          rw [← lintegral_map hm' (hr n), hmap n,
            ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ ((hψ n).2 x).1)]
          exact ENNReal.ofReal_le_ofReal (hψb n).1
  have hE4 : ∀ n : ℕ, Pinf (E4 n) ≤ ENNReal.ofReal (C * Real.exp (-β * n) / K n) := by
    intro n
    rw [ENNReal.ofReal_div_of_pos (hKpos n)]
    calc Pinf (E4 n) ≤ (∫⁻ ω, G n (r n ω) ∂Pinf) / ENNReal.ofReal (K n) :=
          meas_ge_le_lintegral_div ((hG n).comp (hr n)).aemeasurable (by simp [hKpos n])
            ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← lintegral_map (hG n) (hr n), hmap n]
          exact lintegral_one_sub_test_mul_numerator_le π μ P f hf hdensity θ₀ U n (ψ n) (hψ n)
            fun θ hθ ↦ (hψb n).2 θ hθ
  have hE3 : Pinf E3 = 0 := by
    have : E3 = ⋃ i, (fun ω : ℕ → X ↦ ω i) ⁻¹' {x | f θ₀ x ≤ 0} := by ext ω; simp [E3]
    rw [this, measure_iUnion_null_iff]
    intro i
    rw [← Measure.map_apply (measurable_pi_apply i)
      (measurableSet_le (hdensity θ₀).1 measurable_const), Measure.infinitePi_map_eval]
    exact (hdensity θ₀).measure_nonpos_eq_zero
  have hlim1 : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (C * Real.exp (-β * n)) / ENNReal.ofReal (1 / 2)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal (hexpto β hβ C))
      (b := ENNReal.ofReal (1 / 2)) (Or.inr (by norm_num))
    simpa using this
  have hlim4 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C * Real.exp (-β * n) / K n))
      atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, C * Real.exp (-β * n) / K n =
        (4 * C / (ε * π.real B)) * Real.exp (-(β / 2) * n) := by
      intro n
      simp only [K, hγ]
      have : Real.exp (-β * n) = Real.exp (-(β / 2) * n) * Real.exp (-(β / 2) * n) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      field_simp
    simp_rw [heq]
    simpa using ENNReal.tendsto_ofReal (hexpto (β / 2) (by positivity) (4 * C / (ε * π.real B)))
  have htot := (hlim1.add hev).add hlim4
  simp only [add_zero] at htot
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htot (fun n ↦ zero_le)
    (fun n ↦ (measure_mono (hsub n)).trans ?_)
  calc Pinf (E1 n ∪ E2 n ∪ E3 ∪ E4 n) ≤ Pinf (E1 n) + Pinf (E2 n) + Pinf E3 + Pinf (E4 n) :=
        (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _)) _)
    _ ≤ _ := by
        rw [hE3, add_zero]
        exact add_le_add (add_le_add (hE1 n) le_rfl) (hE4 n)

/-- Finite internal Hellinger cover of a sieve, with an explicit entropy cardinality bound. -/
def HasHellingerSieveCover {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (sieve : Set Θ) (ε entropy : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ Real.exp entropy ∧ ∃ center : Fin m → Θ,
    (∀ i, center i ∈ sieve) ∧ ∀ θ ∈ sieve,
      ∃ i, statisticalHellingerDistance (P θ) (P (center i)) ≤ ε

/-- GAPS 104.19: the Ghosal–Ghosh–van der Vaart theorem. Suppose `εₙ → 0` with `n εₙ² → ∞`, the
sieves `Θₙ` have `εₙ/2`-Hellinger covers of cardinality at most `e^{n εₙ²}`, the prior mass outside
`Θₙ` is at most `e^{-(C+4) n εₙ²}`, and the prior mass of the Kullback–Leibler neighbourhood
`{KL ≤ εₙ², V₂ ≤ εₙ²}` is at least `e^{-C n εₙ²}`. Then the posterior contracts at rate `εₙ` in
Hellinger distance. The finite-cover condition spells out the entropy bound without imposing a
metric on parameter labels. -/
theorem exists_posterior_hellinger_contraction
    {Θ X : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ)
    (ε : ℕ → ℝ) (hε : ∀ n : ℕ, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hnε : Tendsto (fun n : ℕ ↦ (n : ℝ) * ε n ^ 2) atTop atTop)
    (C : ℝ) (hC : 0 < C) (sieve : ℕ → Set Θ) (hsieve : ∀ n : ℕ, MeasurableSet (sieve n))
    (hcover : ∀ n : ℕ, HasHellingerSieveCover P (sieve n) (ε n / 2) ((n : ℝ) * ε n ^ 2))
    (htail : ∀ n : ℕ, π (sieve n)ᶜ ≤ ENNReal.ofReal (Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2)))
    (hBmeas : ∀ n : ℕ, MeasurableSet {θ | klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2) ∧
      logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2)})
    (hprior : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-C * (n : ℝ) * ε n ^ 2)) ≤
      π {θ | klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2) ∧
        logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2)})
    (hHmeas : Measurable (fun θ ↦ statisticalHellingerDistance (P θ) (P θ₀))) :
    HasPosteriorContractionRate (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun n x ↦ dominatedPosterior π f (fun i : Fin n ↦ x i.val))
      (fun θ ↦ statisticalHellingerDistance (P θ) (P θ₀)) ε := by
  sorry

/-- Statistical Hellinger distance is nonnegative by its definition. -/
theorem statisticalHellingerDistance_nonneg {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : 0 ≤ statisticalHellingerDistance P Q := Real.sqrt_nonneg _

/-- The Hellinger adapter vanishes when its two laws agree, by Statlib. -/
@[simp] theorem statisticalHellingerDistance_self {X : Type*} [MeasurableSpace X]
    (P : Measure X) [SigmaFinite P] : statisticalHellingerDistance P P = 0 := by
  simp [statisticalHellingerDistance]

/-- Symmetry of the Hellinger adapter follows from Statlib's symmetry theorem. -/
theorem statisticalHellingerDistance_comm {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [SigmaFinite P] [SigmaFinite Q] :
    statisticalHellingerDistance P Q = statisticalHellingerDistance Q P := by
  simp only [statisticalHellingerDistance, ProbabilityTheory.sqHellinger_comm P Q]

/-- Before any observations, a probability prior is its own dominated posterior. -/
@[simp] theorem dominatedPosterior_empty {Θ X : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (f : Θ → X → ℝ) (x : Fin 0 → X) :
    dominatedPosterior π f x = π := by
  simp [dominatedPosterior]

end CKSD
