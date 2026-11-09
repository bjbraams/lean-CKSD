module

public import CKSD.Bayes.Nonparametric
public import CKSD.Asymptotics.Basic
public import CKSD.Bayes.HellingerGeometry
public import CKSD.Bayes.HellingerTests
public import CKSD.Bayes.ExponentialTests
public import CKSD.Bayes.EvidenceBounds
public import CKSD.Bayes.EvidenceConcentration
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

/-- A test with type II error at most `b` on an exceptional set inside a sieve bounds the
expected tested likelihood numerator by `b` plus the prior mass outside the sieve. -/
theorem lintegral_tested_numerator_le_add_prior_compl {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ) (A S : Set Θ)
    (hS : MeasurableSet S) (n : ℕ) (ψ : (Fin n → X) → ℝ) (hψ : IsStatisticalTest ψ)
    {b : ℝ} (hb : ∀ θ ∈ A, θ ∈ S →
      ∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ) ≤ b) :
    ∫⁻ x, ENNReal.ofReal (1 - ψ x) *
        ((∫⁻ θ in A, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) /
          ENNReal.ofReal (∏ i, f θ₀ (x i))) ∂(Measure.pi fun _ : Fin n ↦ P θ₀) ≤
      ENNReal.ofReal b + π Sᶜ := by
  set ν := Measure.pi fun _ : Fin n ↦ μ
  have hL : Measurable fun p : (Fin n → X) × Θ ↦ ENNReal.ofReal (∏ i, f p.2 (p.1 i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      hf.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)))
  have hL0 : Measurable fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ₀ (x i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      (hdensity θ₀).1.comp (measurable_pi_apply i))
  have hψm : Measurable fun x ↦ ENNReal.ofReal (1 - ψ x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub hψ.1)
  have hN : Measurable fun x : Fin n → X ↦ ∫⁻ θ in A, ENNReal.ofReal (∏ i, f θ (x i)) ∂π :=
    hL.lintegral_prod_right'
  have hG : Measurable fun x ↦ ENNReal.ofReal (1 - ψ x) *
      ((∫⁻ θ in A, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) / ENNReal.ofReal (∏ i, f θ₀ (x i))) :=
    hψm.mul (hN.div hL0)
  rw [pi_eq_withDensity_ofReal_prod μ P f hdensity θ₀ n,
    lintegral_withDensity_eq_lintegral_mul _ hL0 hG]
  calc ∫⁻ x, ((fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ₀ (x i))) *
        fun x : Fin n → X ↦ ENNReal.ofReal (1 - ψ x) *
          ((∫⁻ θ in A, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) /
            ENNReal.ofReal (∏ i, f θ₀ (x i)))) x ∂ν
      ≤ ∫⁻ x, ∫⁻ θ in A, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂π ∂ν := by
        refine lintegral_mono fun x ↦ ?_
        have hLx : Measurable fun θ ↦ ENNReal.ofReal (∏ i, f θ (x i)) :=
          hL.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ hLx]
        simp only [Pi.mul_apply]
        rw [mul_left_comm]
        exact mul_le_mul_right ENNReal.mul_div_le _
    _ = ∫⁻ θ in A, ∫⁻ x, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂ν ∂π :=
        lintegral_lintegral_swap ((hψm.comp measurable_fst).mul hL).aemeasurable
    _ ≤ ∫⁻ θ in A, ENNReal.ofReal b + Sᶜ.indicator (fun _ ↦ 1) θ ∂π := by
        have hupper : Measurable (fun θ : Θ ↦ ENNReal.ofReal b +
            Sᶜ.indicator (fun _ : Θ ↦ (1 : ℝ≥0∞)) θ) :=
          (measurable_const : Measurable (fun _ : Θ ↦ ENNReal.ofReal b)).add
            (measurable_const.indicator hS.compl :
              Measurable (Sᶜ.indicator (fun _ : Θ ↦ (1 : ℝ≥0∞))))
        refine setLIntegral_mono hupper fun θ hθ ↦ ?_
        have hint : Integrable (fun x ↦ 1 - ψ x) (Measure.pi fun _ : Fin n ↦ P θ) :=
          Integrable.of_mem_Icc 0 1 (measurable_const.sub hψ.1).aemeasurable
            (ae_of_all _ fun x ↦ ⟨by linarith [(hψ.2 x).2], by linarith [(hψ.2 x).1]⟩)
        have heq : (∫⁻ x, ENNReal.ofReal (1 - ψ x) * ENNReal.ofReal (∏ i, f θ (x i)) ∂ν) =
            ENNReal.ofReal (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ)) := by
          have hLθ : Measurable fun x : Fin n → X ↦ ENNReal.ofReal (∏ i, f θ (x i)) :=
            hL.comp (measurable_id.prodMk measurable_const)
          rw [ofReal_integral_eq_lintegral_ofReal hint
            (ae_of_all _ fun x ↦ sub_nonneg.2 (hψ.2 x).2),
            pi_eq_withDensity_ofReal_prod μ P f hdensity θ n,
            lintegral_withDensity_eq_lintegral_mul _ hLθ hψm]
          exact lintegral_congr fun x ↦ mul_comm _ _
        rw [heq]
        by_cases hθS : θ ∈ S
        · rw [Set.indicator_of_notMem (notMem_compl_iff.2 hθS), add_zero]
          exact ENNReal.ofReal_le_ofReal (hb θ hθ hθS)
        · rw [Set.indicator_of_mem hθS]
          have herror : (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ 1 := by
            calc _ ≤ ∫ _x, (1 : ℝ) ∂(Measure.pi fun _ : Fin n ↦ P θ) :=
                integral_mono hint (integrable_const 1) fun x ↦ by linarith [(hψ.2 x).1]
              _ = 1 := by simp
          exact (ENNReal.ofReal_le_ofReal herror).trans (by simp)
    _ ≤ ∫⁻ θ, ENNReal.ofReal b + Sᶜ.indicator (fun _ ↦ 1) θ ∂π :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal b + π Sᶜ := by
        rw [lintegral_add_left measurable_const]
        simp [lintegral_indicator hS.compl]

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
  simpa only [Set.compl_univ, measure_empty, add_zero] using
    lintegral_tested_numerator_le_add_prior_compl π μ P f hf hdensity θ₀ Uᶜ univ
      MeasurableSet.univ n ψ hψ (fun θ hθ _ ↦ hb θ hθ)

/-- Vanishing test error and a tested likelihood numerator small relative to an evidence lower
bound imply vanishing posterior mass for varying measurable exceptional sets. -/
theorem tendstoInMeasure_posterior_of_testedNumerator
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) [IsFiniteMeasure π] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (f : Θ → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (θ₀ : Θ)
    (hfpos : (P θ₀) {x | f θ₀ x ≤ 0} = 0)
    (A : ℕ → Set Θ) (hA : ∀ n, MeasurableSet (A n))
    (ψ : ∀ n : ℕ, (Fin n → X) → ℝ) (hψ : ∀ n, IsStatisticalTest (ψ n))
    (τ b : ℕ → ℝ) (hτ : ∀ n, 0 < τ n)
    (htest : Tendsto (fun n ↦ ∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0))
    (hnum : ∀ n, (∫⁻ x, ENNReal.ofReal (1 - ψ n x) *
      ((∫⁻ θ in A n, ENNReal.ofReal (∏ i, f θ (x i)) ∂π) /
        ENNReal.ofReal (∏ i, f θ₀ (x i))) ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤
      ENNReal.ofReal (b n))
    (hratio : Tendsto (fun n ↦ b n / τ n) atTop (𝓝 0))
    (hev : Tendsto (fun n : ℕ ↦ (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
        ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * τ n)}) atTop (𝓝 0)) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun (n : ℕ) ω ↦ (dominatedPosterior π f (fun i : Fin n ↦ ω i)).real (A n))
      atTop (fun _ ↦ 0) := by
  classical
  set Pinf := Measure.infinitePi fun _ : ℕ ↦ P θ₀
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let N : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦
    ∫⁻ θ in A n, ENNReal.ofReal (∏ i, f θ (x i)) ∂π
  let D : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦
    ∫⁻ θ, ENNReal.ofReal (∏ i, f θ (x i)) ∂π
  let L₀ : ∀ n : ℕ, (Fin n → X) → ℝ := fun n x ↦ ∏ i, f θ₀ (x i)
  let r : ∀ n : ℕ, (ℕ → X) → (Fin n → X) := fun n ω i ↦ ω i
  have hr : ∀ n, Measurable (r n) := fun n ↦ measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  let K : ℕ → ℝ := fun n ↦ ε / 2 * τ n
  have hKpos : ∀ n, 0 < K n := fun n ↦ mul_pos (div_pos hε (by norm_num)) (hτ n)
  let G : ∀ n : ℕ, (Fin n → X) → ℝ≥0∞ := fun n x ↦
    ENNReal.ofReal (1 - ψ n x) * (N n x / ENNReal.ofReal (L₀ n x))
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have hN : Measurable (N n) := Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → X) × Θ ↦ ENNReal.ofReal (∏ i, f p.2 (p.1 i)))
      (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
        hf.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))))
    exact (ENNReal.measurable_ofReal.comp (measurable_const.sub (hψ n).1)).mul
      (hN.div (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
        (hf.comp (measurable_const.prodMk measurable_id)).comp (measurable_pi_apply i))))
  have hpost : ∀ n (x : Fin n → X),
      (dominatedPosterior π f x).real (A n) = ((D n x)⁻¹ * N n x).toReal := by
    intro n x
    simp [dominatedPosterior, measureReal_def, withDensity_apply _ (hA n), D, N]
  let E1 : ℕ → Set (ℕ → X) := fun n ↦ {ω | 1 / 2 ≤ ψ n (r n ω)}
  let E2 : ℕ → Set (ℕ → X) := fun n ↦
    {ω | D n (r n ω) < ENNReal.ofReal (L₀ n (r n ω) * τ n)}
  let E3 : Set (ℕ → X) := {ω | ∃ i, f θ₀ (ω i) ≤ 0}
  let E4 : ℕ → Set (ℕ → X) := fun n ↦ {ω | ENNReal.ofReal (K n) ≤ G n (r n ω)}
  have hsub : ∀ n : ℕ, {ω : ℕ → X | ε ≤ dist
      ((dominatedPosterior π f (fun i : Fin n ↦ ω i)).real (A n)) 0} ⊆
      E1 n ∪ E2 n ∪ E3 ∪ E4 n := by
    intro n ω hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω
    rw [hpost, abs_of_nonneg ENNReal.toReal_nonneg] at hω
    by_contra hcon
    simp only [E1, E2, E3, E4, Set.mem_union, not_or, Set.mem_ofPred_eq, not_le, not_lt,
      not_exists] at hcon
    obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hcon
    have hL0pos : 0 < L₀ n (r n ω) := Finset.prod_pos fun i _ ↦ hc3 i
    have hlow : 0 < ENNReal.ofReal (L₀ n (r n ω) * τ n) :=
      ENNReal.ofReal_pos.2 (mul_pos hL0pos (hτ n))
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
        (ENNReal.ofReal ε * ENNReal.ofReal (τ n)) := by
      rw [← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [K]
      ring
    refine absurd hc4 (not_lt.2 ?_)
    rw [hK]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hL0pos])) (Or.inl ENNReal.ofReal_ne_top)]
    calc ENNReal.ofReal ε * ENNReal.ofReal (τ n) * ENNReal.ofReal (L₀ n (r n ω))
        = ENNReal.ofReal ε * ENNReal.ofReal (L₀ n (r n ω) * τ n) := by
          rw [ENNReal.ofReal_mul hL0pos.le]; ring
      _ ≤ ENNReal.ofReal ε * D n (r n ω) := mul_le_mul_right hc2 _
      _ ≤ N n (r n ω) := hNge
  have hmap : ∀ n, Pinf.map (r n) = Measure.pi fun _ : Fin n ↦ P θ₀ := fun n ↦
    infinitePi_map_fin_val (P θ₀) n
  have hE1 : ∀ n : ℕ, Pinf (E1 n) ≤
      ENNReal.ofReal (∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) /
        ENNReal.ofReal (1 / 2) := by
    intro n
    have hm : Measurable fun ω ↦ ENNReal.ofReal (ψ n (r n ω)) :=
      ENNReal.measurable_ofReal.comp ((hψ n).1.comp (hr n))
    have hint : Integrable (ψ n) (Measure.pi fun _ : Fin n ↦ P θ₀) :=
      Integrable.of_mem_Icc 0 1 (hψ n).1.aemeasurable (ae_of_all _ (hψ n).2)
    calc Pinf (E1 n) ≤ Pinf {ω | ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (ψ n (r n ω))} :=
          measure_mono fun ω hω ↦ ENNReal.ofReal_le_ofReal hω
      _ ≤ (∫⁻ ω, ENNReal.ofReal (ψ n (r n ω)) ∂Pinf) / ENNReal.ofReal (1 / 2) :=
          meas_ge_le_lintegral_div hm.aemeasurable (by norm_num) ENNReal.ofReal_ne_top
      _ = _ := by
          have hm' : Measurable fun x ↦ ENNReal.ofReal (ψ n x) :=
            ENNReal.measurable_ofReal.comp (hψ n).1
          rw [← lintegral_map hm' (hr n), hmap n,
            ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ ((hψ n).2 x).1)]
  have hE4 : ∀ n : ℕ, Pinf (E4 n) ≤ ENNReal.ofReal (b n / K n) := by
    intro n
    rw [ENNReal.ofReal_div_of_pos (hKpos n)]
    calc Pinf (E4 n) ≤ (∫⁻ ω, G n (r n ω) ∂Pinf) / ENNReal.ofReal (K n) :=
          meas_ge_le_lintegral_div ((hG n).comp (hr n)).aemeasurable (by simp [hKpos n])
            ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← lintegral_map (hG n) (hr n), hmap n]
          exact hnum n
  have hE3 : Pinf E3 = 0 := by
    have hf0m : Measurable (f θ₀) := hf.comp (measurable_const.prodMk measurable_id)
    have : E3 = ⋃ i, (fun ω : ℕ → X ↦ ω i) ⁻¹' {x | f θ₀ x ≤ 0} := by ext ω; simp [E3]
    rw [this, measure_iUnion_null_iff]
    intro i
    rw [← Measure.map_apply (measurable_pi_apply i)
      (measurableSet_le hf0m measurable_const),
      Measure.infinitePi_map_eval]
    exact hfpos
  have hlim1 : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) /
        ENNReal.ofReal (1 / 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, ENNReal.zero_div] using
      ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal htest)
        (b := ENNReal.ofReal (1 / 2)) (Or.inr (by norm_num))
  have hlim4 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (b n / K n)) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, b n / K n = (2 / ε) * (b n / τ n) := by
      intro n
      dsimp [K]
      field_simp
    simp_rw [heq]
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := 2 / ε)).mul hratio)
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
    have := Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos ha))
    simpa using (tendsto_const_nhds (x := c)).mul this
  let τ : ℕ → ℝ := fun n ↦ π.real B / 2 * Real.exp (-γ * n)
  let b : ℕ → ℝ := fun n ↦ C * Real.exp (-β * n)
  refine tendstoInMeasure_posterior_of_testedNumerator π P f hf θ₀
    (hdensity θ₀).measure_nonpos_eq_zero (fun _ ↦ Uᶜ) (fun _ ↦ hU.compl)
    ψ hψ τ b (fun n ↦ mul_pos (div_pos hπBr two_pos) (Real.exp_pos _)) ?_ ?_ ?_ ?_
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hexpto β hβ C)
      (fun n ↦ integral_nonneg fun x ↦ ((hψ n).2 x).1) (fun n ↦ (hψb n).1)
  · intro n
    exact lintegral_one_sub_test_mul_numerator_le π μ P f hf hdensity θ₀ U n (ψ n) (hψ n)
      fun θ hθ ↦ (hψb n).2 θ hθ
  · have heq : ∀ n : ℕ, b n / τ n =
        (2 * C / π.real B) * Real.exp (-γ * n) := by
      intro n
      simp only [b, τ]
      have he : Real.exp (-β * n) = Real.exp (-γ * n) * Real.exp (-γ * n) := by
        rw [← Real.exp_add]; congr 1; dsimp [γ]; ring
      rw [he]
      field_simp
    simp_rw [heq]
    exact hexpto γ (by positivity) _
  · have hB2 : π B / 2 = ENNReal.ofReal (π.real B / 2) := by
      rw [ENNReal.ofReal_div_of_pos two_pos, measureReal_def, ENNReal.ofReal_toReal hπBtop]
      simp
    have heq (n : ℕ) (ω : ℕ → X) :
        ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * τ n) =
          π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n)) := by
      rw [hB2, ← ENNReal.ofReal_mul (div_nonneg hπBr.le two_pos.le)]
      congr 1
      dsimp [τ]
      ring
    simp_rw [heq]
    exact hev

/-- Finite internal Hellinger cover of a sieve, with an explicit entropy cardinality bound. -/
def HasHellingerSieveCover {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (sieve : Set Θ) (ε entropy : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ Real.exp entropy ∧ ∃ center : Fin m → Θ,
    (∀ i, center i ∈ sieve) ∧ ∀ θ ∈ sieve,
      ∃ i, statisticalHellingerDistance (P θ) (P (center i)) ≤ ε

/-- Exponentially small type II errors on a sieve, small prior tails, and KL/second-moment
prior mass imply posterior contraction. The test construction is separated from the evidence
and likelihood-ratio argument. -/
theorem hasPosteriorContractionRate_of_sieve_tests
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hnε : Tendsto (fun n : ℕ ↦ (n : ℝ) * ε n ^ 2) atTop atTop)
    (C : ℝ) (sieve B : ℕ → Set Θ) (hsieve : ∀ n, MeasurableSet (sieve n))
    (hBmeas : ∀ n, MeasurableSet (B n))
    (hKL : ∀ n, ∀ θ ∈ B n, klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2))
    (hsecond : ∀ n, ∀ θ ∈ B n,
      logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2))
    (htail : ∀ n, π (sieve n)ᶜ ≤ ENNReal.ofReal (Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2)))
    (hprior : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-C * (n : ℝ) * ε n ^ 2)) ≤ π (B n))
    (ρ : Θ → ℝ) (hρ : Measurable ρ)
    (htests : ∃ M₀ > 0, ∀ M ≥ M₀, ∃ ψ : ∀ n : ℕ, (Fin n → X) → ℝ,
      (∀ n, IsStatisticalTest (ψ n)) ∧
      Tendsto (fun n ↦ ∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0) ∧
      ∀ n θ, θ ∈ sieve n → M * ε n ≤ ρ θ →
        (∫ x, 1 - ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤
          Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2)) :
    HasPosteriorContractionRate (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      (fun n x ↦ dominatedPosterior π f (fun i : Fin n ↦ x i)) ρ ε := by
  classical
  obtain ⟨M₀, hM₀, htests⟩ := htests
  refine ⟨M₀, hM₀, fun M hM ↦ ?_⟩
  obtain ⟨ψ, hψ, htest, htypeII⟩ := htests M hM
  have hπBr (n : ℕ) : 0 < π.real (B n) := by
    apply ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    exact ((ENNReal.ofReal_pos.2 (Real.exp_pos _)).trans_le (hprior n)).ne'
  have hpriorr (n : ℕ) : Real.exp (-C * (n : ℝ) * ε n ^ 2) ≤ π.real (B n) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hprior n)
    simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  let τ : ℕ → ℝ := fun n ↦ π.real (B n) / 2 * Real.exp (-(2 * ε n ^ 2) * n)
  let b : ℕ → ℝ := fun n ↦ 2 * Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2)
  have hτ (n : ℕ) : 0 < τ n := mul_pos (div_pos (hπBr n) two_pos) (Real.exp_pos _)
  refine tendstoInMeasure_posterior_of_testedNumerator π P f hf θ₀
    (hdensity θ₀).measure_nonpos_eq_zero (fun n ↦ {θ | M * ε n ≤ ρ θ})
    (fun n ↦ measurableSet_le measurable_const hρ) ψ hψ τ b hτ htest ?_ ?_ ?_
  · intro n
    have hnum := lintegral_tested_numerator_le_add_prior_compl π μ P f hf hdensity θ₀
      {θ | M * ε n ≤ ρ θ} (sieve n) (hsieve n) n (ψ n) (hψ n)
      (b := Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2))
      (fun θ hθA hθS ↦ htypeII n θ hθS hθA)
    refine hnum.trans ((add_le_add le_rfl (htail n)).trans_eq ?_)
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    congr 1
    dsimp [b]
    ring
  · have hlim : Tendsto (fun n : ℕ ↦ 4 * Real.exp (-2 * ((n : ℝ) * ε n ^ 2)))
        atTop (𝓝 0) := by
      have hexp := Real.tendsto_exp_atBot.comp
        (hnε.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
      simpa only [Function.comp_apply, mul_zero] using (tendsto_const_nhds (x := (4 : ℝ))).mul hexp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n ↦ div_nonneg (by positivity) (hτ n).le) fun n ↦ ?_
    have hlow : Real.exp (-C * (n : ℝ) * ε n ^ 2) / 2 *
        Real.exp (-(2 * ε n ^ 2) * n) ≤ τ n :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hpriorr n) two_pos.le)
        (Real.exp_pos _).le
    refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hlow).trans_eq ?_
    have he : Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2) =
        Real.exp (-C * (n : ℝ) * ε n ^ 2) * Real.exp (-(2 * ε n ^ 2) * n) *
          Real.exp (-2 * ((n : ℝ) * ε n ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    dsimp [b]
    rw [he]
    field_simp
    ring
  · have hev := tendsto_infinitePi_evidence_lt_of_secondMoment π μ P f hf hdensity θ₀ B
      hBmeas (fun n ↦ ε n ^ 2) (fun n ↦ sq_pos_of_pos (hε n)) hnε hKL hsecond
    have heq (n : ℕ) (ω : ℕ → X) :
        ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * τ n) =
          π (B n) / 2 * ENNReal.ofReal
            ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-(2 * ε n ^ 2) * n)) := by
      have hB2 : π (B n) / 2 = ENNReal.ofReal (π.real (B n) / 2) := by
        rw [ENNReal.ofReal_div_of_pos two_pos, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
        simp
      rw [hB2, ← ENNReal.ofReal_mul (div_nonneg (hπBr n).le two_pos.le)]
      congr 1
      dsimp [τ]
      ring
    simp_rw [heq]
    exact hev


/-- Robust tests of Hellinger balls and finite sieve covers give exponentially consistent sieve
tests at a sufficiently large multiple of the covering radius. -/
theorem exists_hellinger_sieve_tests_of_ball_tests
    {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (θ₀ : Θ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hnε : Tendsto (fun n : ℕ ↦ (n : ℝ) * ε n ^ 2) atTop atTop)
    (C : ℝ) (hC : 0 < C) (sieve : ℕ → Set Θ)
    (hcover : ∀ n, HasHellingerSieveCover P (sieve n) (ε n / 2) ((n : ℝ) * ε n ^ 2))
    (htri : ∀ θ η, statisticalHellingerDistance (P θ) (P θ₀) ≤
      statisticalHellingerDistance (P θ) (P η) + statisticalHellingerDistance (P η) (P θ₀))
    (hball : ∀ θ (n : ℕ), 0 < statisticalHellingerDistance (P θ) (P θ₀) →
      ∃ ψ : (Fin n → X) → ℝ, IsStatisticalTest ψ ∧
        (∫ x, ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤
          Real.exp (-(n : ℝ) * statisticalHellingerDistance (P θ) (P θ₀) ^ 2 / 256) ∧
        ∀ η, statisticalHellingerDistance (P η) (P θ) ≤
            statisticalHellingerDistance (P θ) (P θ₀) / 8 →
          (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P η)) ≤
            Real.exp (-(n : ℝ) * statisticalHellingerDistance (P θ) (P θ₀) ^ 2 / 256)) :
    ∃ M₀ > 0, ∀ M ≥ M₀, ∃ ψ : ∀ n : ℕ, (Fin n → X) → ℝ,
      (∀ n, IsStatisticalTest (ψ n)) ∧
      Tendsto (fun n ↦ ∫ x, ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) atTop (𝓝 0) ∧
      ∀ n θ, θ ∈ sieve n → M * ε n ≤ statisticalHellingerDistance (P θ) (P θ₀) →
        (∫ x, 1 - ψ n x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤
          Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2) := by
  classical
  let M₀ := 256 * (C + 6) + 2
  refine ⟨M₀, by dsimp [M₀]; linarith, fun M hM ↦ ?_⟩
  have hM5 : 5 ≤ M := by dsimp [M₀] at hM; linarith
  have hcoef : 256 * (C + 6) ≤ (M - 1) ^ 2 := by
    have hmul := mul_nonneg (by linarith : 0 ≤ M - 1) (by linarith : 0 ≤ M - 2)
    dsimp [M₀] at hM
    nlinarith
  have hpern (n : ℕ) : ∃ ψ : (Fin n → X) → ℝ, IsStatisticalTest ψ ∧
      (∫ x, ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤
        Real.exp (-(C + 5) * ((n : ℝ) * ε n ^ 2)) ∧
      ∀ θ, θ ∈ sieve n → M * ε n ≤ statisticalHellingerDistance (P θ) (P θ₀) →
        (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤
          Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2) := by
    obtain ⟨m, hm, center, hcenter, hcov⟩ := hcover n
    let d : Fin m → ℝ := fun i ↦ statisticalHellingerDistance (P (center i)) (P θ₀)
    let E := Real.exp (-(C + 6) * (n : ℝ) * ε n ^ 2)
    have hsmall (i : Fin m) (hi : (M - 1) * ε n ≤ d i) :
        Real.exp (-(n : ℝ) * d i ^ 2 / 256) ≤ E := by
      have hsq : 256 * (C + 6) * ε n ^ 2 ≤ d i ^ 2 := by
        calc _ ≤ (M - 1) ^ 2 * ε n ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
          _ = ((M - 1) * ε n) ^ 2 := by ring
          _ ≤ d i ^ 2 := pow_le_pow_left₀ (mul_nonneg (by linarith) (hε n).le) hi 2
      apply Real.exp_le_exp.2
      have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)
      nlinarith
    have hper (i : Fin m) : ∃ u : (Fin n → X) → ℝ, IsStatisticalTest u ∧
        (∫ x, u x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤ E ∧
        ((M - 1) * ε n ≤ d i → ∀ θ,
          statisticalHellingerDistance (P θ) (P (center i)) ≤ d i / 8 →
          (∫ x, 1 - u x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤ E) := by
      by_cases hi : (M - 1) * ε n ≤ d i
      · have hd : 0 < d i := (mul_pos (by linarith) (hε n)).trans_le hi
        obtain ⟨u, hu, hI, hII⟩ := hball (center i) n hd
        exact ⟨u, hu, hI.trans (hsmall i hi), fun _ θ hθ ↦ (hII θ hθ).trans (hsmall i hi)⟩
      · refine ⟨fun _ ↦ 0, ⟨measurable_const, fun _ ↦ ⟨le_rfl, zero_le_one⟩⟩,
          by simp only [integral_zero]; exact (Real.exp_pos _).le, fun h ↦ (hi h).elim⟩
    choose u hu hI hII using hper
    let ψ : (Fin n → X) → ℝ := fun x ↦ min 1 (∑ i, u i x)
    have hψ : IsStatisticalTest ψ := by
      refine ⟨measurable_const.min (Finset.measurable_sum _ fun i _ ↦ (hu i).1), fun x ↦ ?_⟩
      exact ⟨le_min zero_le_one (Finset.sum_nonneg fun i _ ↦ ((hu i).2 x).1), min_le_left _ _⟩
    have huint (i : Fin m) (θ : Θ) : Integrable (u i) (Measure.pi fun _ : Fin n ↦ P θ) :=
      Integrable.of_mem_Icc 0 1 (hu i).1.aemeasurable (ae_of_all _ (hu i).2)
    have hψint (θ : Θ) : Integrable ψ (Measure.pi fun _ : Fin n ↦ P θ) :=
      Integrable.of_mem_Icc 0 1 hψ.1.aemeasurable (ae_of_all _ hψ.2)
    refine ⟨ψ, hψ, ?_, ?_⟩
    · calc (∫ x, ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ₀)) ≤
            ∫ x, ∑ i, u i x ∂(Measure.pi fun _ : Fin n ↦ P θ₀) :=
              integral_mono (hψint θ₀) (integrable_finsetSum _ fun i _ ↦ huint i θ₀)
                fun x ↦ min_le_right _ _
        _ = ∑ i, ∫ x, u i x ∂(Measure.pi fun _ : Fin n ↦ P θ₀) :=
              integral_finsetSum _ fun i _ ↦ huint i θ₀
        _ ≤ ∑ _i : Fin m, E := Finset.sum_le_sum fun i _ ↦ hI i
        _ = (m : ℝ) * E := by simp
        _ ≤ Real.exp ((n : ℝ) * ε n ^ 2) * E :=
              mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (-(C + 5) * ((n : ℝ) * ε n ^ 2)) := by
              dsimp [E]
              rw [← Real.exp_add]
              congr 1
              ring
    · intro θ hθ hout
      obtain ⟨i, hi⟩ := hcov θ hθ
      have hact : (M - 1) * ε n ≤ d i := by
        have h := htri θ (center i)
        dsimp [d]
        nlinarith [hε n]
      have hrad : statisticalHellingerDistance (P θ) (P (center i)) ≤ d i / 8 := by
        nlinarith [hε n]
      have hψge (x : Fin n → X) : u i x ≤ ψ x := by
        refine le_min ((hu i).2 x).2 ?_
        exact Finset.single_le_sum (fun j _ ↦ ((hu j).2 x).1) (Finset.mem_univ i)
      have hintψ : Integrable (fun x ↦ 1 - ψ x) (Measure.pi fun _ : Fin n ↦ P θ) :=
        (integrable_const 1).sub (hψint θ)
      have hintu : Integrable (fun x ↦ 1 - u i x) (Measure.pi fun _ : Fin n ↦ P θ) :=
        (integrable_const 1).sub (huint i θ)
      calc (∫ x, 1 - ψ x ∂(Measure.pi fun _ : Fin n ↦ P θ)) ≤
            ∫ x, 1 - u i x ∂(Measure.pi fun _ : Fin n ↦ P θ) :=
              integral_mono hintψ hintu fun x ↦ sub_le_sub_left (hψge x) 1
        _ ≤ E := hII i hact θ hrad
        _ ≤ Real.exp (-(C + 4) * (n : ℝ) * ε n ^ 2) := by
              apply Real.exp_le_exp.2
              have hnδ := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (ε n))
              nlinarith
  choose ψ hψ hI hII using hpern
  refine ⟨ψ, hψ, ?_, hII⟩
  have hElim : Tendsto (fun n : ℕ ↦ Real.exp (-(C + 5) * ((n : ℝ) * ε n ^ 2)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp
      (hnε.const_mul_atTop_of_neg (by linarith : -(C + 5) < 0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hElim
    (fun n ↦ integral_nonneg fun x ↦ ((hψ n).2 x).1) hI


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
  refine hasPosteriorContractionRate_of_sieve_tests π μ P f hf hdensity θ₀ ε hε hnε C
    sieve (fun n ↦ {θ | klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2) ∧
      logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (ε n ^ 2)})
    hsieve hBmeas (fun n θ hθ ↦ hθ.1) (fun n θ hθ ↦ hθ.2) htail hprior
    (fun θ ↦ statisticalHellingerDistance (P θ) (P θ₀)) hHmeas ?_
  refine exists_hellinger_sieve_tests_of_ball_tests P θ₀ ε hε hnε C hC sieve hcover
    (fun θ η ↦ statisticalHellingerDistance_triangle_of_hasDensity
      (hdensity θ) (hdensity η) (hdensity θ₀)) ?_
  intro θ n hpos
  have hsym : statisticalHellingerDistance (P θ₀) (P θ) =
      statisticalHellingerDistance (P θ) (P θ₀) := by
    simp only [statisticalHellingerDistance, ProbabilityTheory.sqHellinger_comm]
  have hpos' : 0 < statisticalHellingerDistance (P θ₀) (P θ) := hsym.symm ▸ hpos
  obtain ⟨ψ, hψ, hI, hII⟩ := exists_hellinger_ball_test μ (P θ₀) (P θ)
    (f θ₀) (f θ) (hdensity θ₀) (hdensity θ) hpos' n
  refine ⟨ψ, hψ, ?_, fun η hη ↦ ?_⟩
  · simpa only [hsym, neg_div, neg_mul] using hI
  · have hη' : statisticalHellingerDistance (P η) (P θ) ≤
        statisticalHellingerDistance (P θ₀) (P θ) / 8 := by rwa [hsym]
    have h := hII (P η) (f η) inferInstance (hdensity η) hη'
    simpa only [hsym, neg_div, neg_mul] using h

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
