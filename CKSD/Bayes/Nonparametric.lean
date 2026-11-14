module

public import CKSD.Bayes.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.StrongLaw


/-!
# Random probability measures and posterior consistency

Vocabulary for Bayesian nonparametrics: Dirichlet processes through their finite-dimensional
partition laws, the Blackwell–MacQueen predictive law, stick breaking, posterior kernels given as
disintegrations, posterior consistency, and posterior contraction rates.

The finite-dimensional Dirichlet laws are those of TauCeti. Zero-parameter cells in a partition
are required to have random mass zero; the Dirichlet law is tested on positive-mass cells.
Posterior kernels are specified by disintegration, so statements apply to any chosen version.

## Main definitions

* `CKSD.IsDirichletProcess μ P α`: the random measure `P` is a Dirichlet process with base `α`.
* `CKSD.dirichletPosteriorBase`, `CKSD.polyaPredictiveLaw`: the posterior base `α + ∑ δ_{xᵢ}` and
  the predictive law `(α + ∑ δ_{xᵢ}) / (|α| + n)`.
* `CKSD.stickBreakingWeight`, `CKSD.stickBreakingMeasure`: Sethuraman's stick-breaking weights
  and random atomic measure.
* `CKSD.IsPosteriorKernel`, `CKSD.IsPosteriorConsistent`, `CKSD.HasPosteriorContractionRate`:
  posterior kernels, consistency, and contraction at a rate.

## Main results

* `CKSD.ae_is_posterior_consistent_of_identifiable`: Doob's consistency theorem (GAPS 104.17).

Doob's theorem is proved on the joint law of parameter and sample. Identifiability makes the
parameter a measurable function of the sample almost surely: the empirical distribution function
along a Borel embedding into `ℝ` recovers the sampling law by TauCeti's
`strong_law_ae_infinitePi`, and the injective parameter map is a measurable embedding. The
posterior is identified with a conditional expectation through `condDistrib`, and Lévy's upward
theorem `MeasureTheory.Integrable.tendsto_ae_condExp` gives convergence on a countable basis.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Finite-dimensional partition characterization of a Dirichlet process.
`A` partitions a set of full base mass; this includes partitions with null cells after deleting
them. -/
def IsDirichletProcess {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (P : Ω → ProbabilityMeasure X) (α : Measure X) : Prop :=
  (∀ A, MeasurableSet A → Measurable (fun ω ↦ (P ω : Measure X) A)) ∧
    (∀ A, MeasurableSet A → α A = 0 → ∀ᵐ ω ∂μ, (P ω : Measure X) A = 0) ∧
    ∀ k : ℕ, 0 < k → ∀ A : Fin k → Set X,
      (∀ i, MeasurableSet (A i)) → Pairwise (Disjoint on A) →
      α (⋃ i, A i)ᶜ = 0 → (∀ i, 0 < α (A i)) →
      μ.map (fun ω ↦ WithLp.toLp 2 (fun i ↦ (P ω : Measure X).real (A i))) =
        TauCeti.Probability.dirichletMeasure (fun i ↦ α.real (A i))

/-- Posterior base measure after a finite sample from a Dirichlet process. -/
def dirichletPosteriorBase {X : Type*} [MeasurableSpace X] {n : ℕ}
    (α : Measure X) (x : Fin n → X) : Measure X := α + ∑ i, Measure.dirac (x i)

/-- Blackwell–MacQueen one-step predictive law. -/
def polyaPredictiveLaw {X : Type*} [MeasurableSpace X] {n : ℕ}
    (α : Measure X) (x : Fin n → X) : Measure X :=
  (α univ + n)⁻¹ • dirichletPosteriorBase α x

/-- Infinite stick-breaking weights in their size-biased order. -/
def stickBreakingWeight (V : ℕ → ℝ) (k : ℕ) : ℝ :=
  V k * ∏ j ∈ Finset.range k, (1 - V j)

/-- Random atomic measure associated to a sequence of atoms and stick-breaking fractions. -/
def stickBreakingMeasure {X : Type*} [MeasurableSpace X]
    (V : ℕ → ℝ) (θ : ℕ → X) : Measure X :=
  Measure.sum (fun k ↦ ENNReal.ofReal (stickBreakingWeight V k) • Measure.dirac (θ k))

/-- A chosen posterior kernel is a disintegration of the joint parameter-data law. -/
def IsPosteriorKernel {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) (P : Kernel Θ X) (post : Kernel X Θ) : Prop :=
  IsMarkovKernel post ∧
    (π ⊗ₘ P).map Prod.swap = (P ∘ₘ π) ⊗ₘ post

/-- Posterior consistency at a parameter, with data given as an infinite sequence. -/
def IsPosteriorConsistent {Θ X : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [MeasurableSpace X]
    (law : Measure (ℕ → X)) (post : ∀ n, Kernel (Fin n → X) Θ) (θ : Θ) : Prop :=
  ∀ U ∈ 𝓝 θ, ∀ᵐ x ∂law, Tendsto (fun n ↦ (post n (fun i ↦ x i.val)).real U) atTop (𝓝 1)

/-- The i.i.d. sampling kernel `θ ↦ (P θ)^{⊗ℕ}`. -/
private def iidKernel {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (P : Kernel Θ X) [IsMarkovKernel P] : Kernel Θ (ℕ → X) where
  toFun θ := Measure.infinitePi fun _ : ℕ ↦ P θ
  measurable' := by
    have h : Measurable fun θ ↦ (⟨P θ, inferInstance⟩ : ProbabilityMeasure X) :=
      P.measurable.subtype_mk
    exact TauCeti.MeasureTheory.measurable_infinitePi_const.comp h

/-- The i.i.d. sampling kernel is Markov. -/
private instance {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (P : Kernel Θ X) [IsMarkovKernel P] : IsMarkovKernel (iidKernel P) :=
  ⟨fun θ ↦ by
    change IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ ↦ P θ)
    infer_instance⟩

/-- Values `ν(e ⁻¹' (-∞, q])`, `q ∈ ℚ`, of the distribution function of `ν` pushed forward by
`e : X → ℝ`. -/
private def cdfCoord {X : Type*} [MeasurableSpace X] (e : X → ℝ) (ν : Measure X) : ℚ → ℝ :=
  fun q ↦ ν.real (e ⁻¹' Iic (q : ℝ))

/-- For a Borel embedding `e` into `ℝ`, a probability measure is determined by its rational
distribution-function values. -/
private theorem eq_of_cdf_coord_eq {X : Type*} [MeasurableSpace X] {e : X → ℝ}
    (he : MeasurableEmbedding e) {ν ν' : Measure X} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (h : cdfCoord e ν = cdfCoord e ν') : ν = ν' := by
  have hmap : ν.map e = ν'.map e := by
    refine ext_of_generate_finite _ (by rw [← Real.borel_eq_generateFrom_Iic_rat,
      BorelSpace.measurable_eq (α := ℝ)]) Real.isPiSystem_Iic_rat ?_ ?_
    · simp only [mem_iUnion, mem_singleton_iff]
      rintro s ⟨q, rfl⟩
      have := congrFun h q
      simp only [cdfCoord, measureReal_def] at this
      rw [he.map_apply, he.map_apply]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
    · rw [he.map_apply, he.map_apply]; simp
  ext s hs
  have h1 := congrArg (fun μ ↦ μ (e '' s)) hmap
  simp only [he.map_apply, he.injective.preimage_image] at h1
  exact h1


/-- Empirical CDF coordinates of a sample, as limit superiors of running frequencies. -/
private def empiricalCdfCoord {X : Type*} [MeasurableSpace X] (e : X → ℝ) (x : ℕ → X) : ℚ → ℝ :=
  fun q ↦ limsup (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
    (e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (x i)) atTop

/-- The empirical distribution-function coordinates are measurable in the sample. -/
private theorem measurable_empirical_cdf_coord {X : Type*} [MeasurableSpace X] {e : X → ℝ}
    (he : Measurable e) : Measurable (empiricalCdfCoord e) := by
  refine measurable_pi_iff.mpr fun q ↦ ?_
  refine Measurable.limsup fun n ↦ ?_
  have hs : Measurable fun x : ℕ → X ↦ ∑ i ∈ Finset.range n,
      (e ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (x i) :=
    Finset.measurable_sum (Finset.range n) fun i _ ↦
      (measurable_const.indicator (he measurableSet_Iic)).comp (measurable_pi_apply i)
  exact hs.const_smul ((n : ℝ)⁻¹)

/-- By the strong law of large numbers, the empirical distribution-function coordinates of an
i.i.d. sample recover those of the sampling law almost surely. -/
private theorem ae_empirical_cdf_coord_eq {X : Type*} [MeasurableSpace X] {e : X → ℝ}
    (he : Measurable e) (ν : Measure X) [IsProbabilityMeasure ν] :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ ν), empiricalCdfCoord e x = cdfCoord e ν := by
  have h : ∀ q : ℚ, ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ ν),
      empiricalCdfCoord e x q = cdfCoord e ν q := by
    intro q
    have hm : MeasurableSet (e ⁻¹' Iic (q : ℝ)) := he measurableSet_Iic
    filter_upwards [TauCeti.Probability.strong_law_ae_infinitePi ν
      (measurable_const.indicator hm) ((integrable_const (1 : ℝ)).indicator hm)] with x hx
    rw [integral_indicator_const _ hm, smul_eq_mul, mul_one] at hx
    exact hx.limsup_eq
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact funext hx


/-- For an identifiable model on standard Borel spaces, the parameter is a measurable function of
an i.i.d. sample, almost surely under every sampling law. -/
private theorem exists_measurable_ae_eq_param {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    [StandardBorelSpace Θ] [StandardBorelSpace X] [Nonempty Θ] (P : Kernel Θ X)
    [IsMarkovKernel P] (hinj : Injective P) :
    ∃ G : (ℕ → X) → Θ, Measurable G ∧ ∀ θ, ∀ᵐ x ∂iidKernel P θ, G x = θ := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := X)
  set Φ : Θ → ℚ → ℝ := fun θ ↦ cdfCoord e (P θ) with hΦ
  have hΦm : Measurable Φ := measurable_pi_iff.mpr fun q ↦ by
    simp only [hΦ, cdfCoord, measureReal_def]
    exact (P.measurable_coe (he.measurable measurableSet_Iic)).ennreal_toReal
  have hΦi : Injective Φ := fun θ θ' h ↦ hinj (eq_of_cdf_coord_eq he h)
  have hemb := hΦm.measurableEmbedding hΦi
  refine ⟨extend Φ id (fun _ ↦ Classical.arbitrary Θ) ∘ empiricalCdfCoord e,
    (hemb.measurable_extend measurable_id measurable_const).comp
      (measurable_empirical_cdf_coord he.measurable), fun θ ↦ ?_⟩
  change ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ P θ), _
  filter_upwards [ae_empirical_cdf_coord_eq he.measurable (P θ)] with x hx
  simp only [comp_apply, hx]
  exact hΦi.extend_apply id _ θ


/-- The first `n` observations of a parameter-sample pair. -/
private def samplePrefix {Θ X : Type*} (n : ℕ) (z : Θ × (ℕ → X)) : Fin n → X := fun i ↦ z.2 i

/-- The first `n` observations depend measurably on the pair. -/
private theorem measurable_sample_prefix {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (n : ℕ) : Measurable (samplePrefix (Θ := Θ) (X := X) n) :=
  Measurable.of_eval fun i ↦ (measurable_pi_apply (i : ℕ)).comp measurable_snd

/-- The joint law of the first `n` observations and the parameter is the reversed joint law of the
Bayesian model with `n` observations. -/
private theorem map_sample_prefix_fst {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P] (n : ℕ)
    (Q : Kernel Θ (Fin n → X)) (hQ : ∀ θ, Q θ = Measure.pi (fun _ : Fin n ↦ P θ)) :
    (π ⊗ₘ iidKernel P).map (fun z ↦ (samplePrefix n z, z.1)) = (π ⊗ₘ Q).map Prod.swap := by
  have hr : Measurable fun x : ℕ → X ↦ fun i : Fin n ↦ x i :=
    Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hk : (iidKernel P).map (fun x : ℕ → X ↦ fun i : Fin n ↦ x i) = Q := by
    ext1 θ
    rw [Kernel.map_apply _ hr, hQ]
    exact TauCeti.MeasureTheory.map_prefixProj_infinitePi_const ⟨P θ, inferInstance⟩ n
  rw [← hk, Measure.compProd_map hr, Measure.map_map measurable_swap (by fun_prop)]
  rfl

/-- The posterior probability of a measurable set is a version of the conditional probability of
the parameter lying in it given the first `n` observations. -/
private theorem cond_exp_indicator_ae_eq_posterior {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace Θ] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P] (n : ℕ)
    (Q : Kernel Θ (Fin n → X)) (hQ : ∀ θ, Q θ = Measure.pi (fun _ : Fin n ↦ P θ))
    (post : Kernel (Fin n → X) Θ) (hpost : IsPosteriorKernel π Q post)
    {B : Set Θ} (hB : MeasurableSet B) :
    (π ⊗ₘ iidKernel P)[fun z ↦ B.indicator (fun _ ↦ (1 : ℝ)) z.1 |
        MeasurableSpace.comap (samplePrefix n) inferInstance] =ᵐ[π ⊗ₘ iidKernel P]
      fun z ↦ (post (samplePrefix n z)).real B := by
  obtain ⟨hmk, hdis⟩ := hpost
  have : IsMarkovKernel Q := ⟨fun θ ↦ by rw [hQ]; infer_instance⟩
  set J := π ⊗ₘ iidKernel P with hJ
  have hX := measurable_sample_prefix (Θ := Θ) (X := X) n
  have hjoint : J.map (fun z ↦ (samplePrefix n z, z.1)) = J.map (samplePrefix n) ⊗ₘ post := by
    have h1 : J.map (fun z ↦ (samplePrefix n z, z.1)) = (Q ∘ₘ π) ⊗ₘ post := by
      rw [hJ, map_sample_prefix_fst π P n Q hQ, hdis]
    have h2 : J.map (samplePrefix n) = Q ∘ₘ π := by
      rw [← Measure.fst_map_prodMk (Y := Prod.fst) hX, h1, Measure.fst_compProd]
      exact measurable_fst
    rw [h1, h2]
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX measurable_fst hjoint
  have hcd' := ae_of_ae_map hX.aemeasurable hcd
  have hf : StronglyMeasurable (B.indicator fun _ : Θ ↦ (1 : ℝ)) :=
    (measurable_const.indicator hB).stronglyMeasurable
  have hint : Integrable (fun z : Θ × (ℕ → X) ↦ B.indicator (fun _ ↦ (1 : ℝ)) z.1) J :=
    (integrable_const (1 : ℝ)).indicator (measurable_fst hB) |>.congr
      (ae_of_all _ fun z ↦ rfl)
  filter_upwards [condExp_ae_eq_integral_condDistrib hX measurable_fst.aemeasurable hf hint, hcd']
    with z hz hz'
  rw [hz, hz', integral_indicator_const _ hB, smul_eq_mul, mul_one]


/-- The filtration of the first `n` observations on parameter-sample pairs. -/
private def sampleFiltration (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (Θ × (ℕ → X))) where
  seq n := MeasurableSpace.comap (samplePrefix n) inferInstance
  mono' m n hmn := by
    have hr : Measurable fun y : Fin n → X ↦ fun i : Fin m ↦ y (Fin.castLE hmn i) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply _
    have : samplePrefix (Θ := Θ) (X := X) m =
        (fun y : Fin n → X ↦ fun i : Fin m ↦ y (Fin.castLE hmn i)) ∘ samplePrefix n := rfl
    show MeasurableSpace.comap (samplePrefix m) inferInstance ≤
      MeasurableSpace.comap (samplePrefix n) inferInstance
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  le' n := (measurable_sample_prefix n).comap_le

/-- The whole sample is measurable for the limit of the observation filtration. -/
private theorem measurable_snd_i_sup_sample_filtration {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] :
    Measurable[⨆ n, sampleFiltration Θ X n] fun z : Θ × (ℕ → X) ↦ z.2 := by
  refine (@measurable_pi_iff _ _ _ (⨆ n, sampleFiltration Θ X n) _).mpr fun i ↦ ?_
  have h : Measurable[sampleFiltration Θ X (i + 1)] fun z : Θ × (ℕ → X) ↦ z.2 i := by
    have : (fun z : Θ × (ℕ → X) ↦ z.2 i) =
        (fun y : Fin (i + 1) → X ↦ y (Fin.last i)) ∘ samplePrefix (i + 1) := rfl
    rw [this]
    exact (measurable_pi_apply _).comp (comap_measurable _)
  exact h.mono (le_iSup (fun n ↦ sampleFiltration Θ X n) (i + 1)) le_rfl


/-- Doob's martingale argument for one measurable set: under the joint law, the posterior
probability of `B` converges almost surely to the indicator of the parameter lying in `B`. -/
private theorem ae_tendsto_posterior_indicator {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] [StandardBorelSpace Θ] [StandardBorelSpace X] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P]
    (Q : ∀ n, Kernel Θ (Fin n → X))
    (hQ : ∀ n θ, Q n θ = Measure.pi (fun _ : Fin n ↦ P θ))
    (post : ∀ n, Kernel (Fin n → X) Θ) (hpost : ∀ n, IsPosteriorKernel π (Q n) (post n))
    {G : (ℕ → X) → Θ} (hGm : Measurable G) (hGJ : ∀ᵐ z ∂π ⊗ₘ iidKernel P, G z.2 = z.1)
    {B : Set Θ} (hBm : MeasurableSet B) :
    ∀ᵐ z ∂π ⊗ₘ iidKernel P, Tendsto (fun n ↦ (post n (samplePrefix n z)).real B) atTop
      (𝓝 (B.indicator (fun _ ↦ (1 : ℝ)) z.1)) := by
  set J := π ⊗ₘ iidKernel P with hJ
  set g : Θ × (ℕ → X) → ℝ := fun z ↦ B.indicator (fun _ ↦ (1 : ℝ)) (G z.2) with hg
  have hgm' : Measurable (B.indicator fun _ : Θ ↦ (1 : ℝ)) := measurable_const.indicator hBm
  have hgm : StronglyMeasurable[⨆ n, sampleFiltration Θ X n] g :=
    ((hgm'.comp hGm).comp measurable_snd_i_sup_sample_filtration).stronglyMeasurable
  have hgint : Integrable g J := by
    refine (integrable_const (1 : ℝ)).mono'
      ((hgm'.comp hGm).comp measurable_snd).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    by_cases h : G z.2 ∈ B <;> simp [hg, h]
  have hge : g =ᵐ[J] fun z ↦ B.indicator (fun _ ↦ (1 : ℝ)) z.1 := by
    filter_upwards [hGJ] with z hz
    simp only [hg, hz]
  have hlevy := hgint.tendsto_ae_condExp (ℱ := sampleFiltration Θ X) hgm
  have hn : ∀ n, J[g | sampleFiltration Θ X n] =ᵐ[J]
      fun z ↦ (post n (samplePrefix n z)).real B := fun n ↦
    (condExp_congr_ae hge).trans
      (cond_exp_indicator_ae_eq_posterior π P n (Q n) (hQ n) (post n) (hpost n) hBm)
  filter_upwards [hlevy, ae_all_iff.mpr hn, hge] with z h1 h2 h3
  have e : (fun n ↦ J[g | sampleFiltration Θ X n] z) =
      fun n ↦ (post n (samplePrefix n z)).real B := funext h2
  rw [e, h3] at h1
  exact h1

/-- GAPS 104.17: Doob's consistency theorem. For an identifiable model (`P` injective) on standard
Borel spaces, any versions of the posteriors given the first `n` i.i.d. observations are
consistent at `π`-almost every parameter. -/
theorem ae_is_posterior_consistent_of_identifiable
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    [TopologicalSpace Θ] [PolishSpace Θ] [BorelSpace Θ]
    [StandardBorelSpace X] [Nonempty Θ]
    (π : Measure Θ) [IsProbabilityMeasure π] (P : Kernel Θ X) [IsMarkovKernel P]
    (hinj : Function.Injective P)
    (Q : ∀ n, Kernel Θ (Fin n → X))
    (hQ : ∀ n θ, Q n θ = Measure.pi (fun _ : Fin n ↦ P θ))
    (post : ∀ n, Kernel (Fin n → X) Θ)
    (hpost : ∀ n, IsPosteriorKernel π (Q n) (post n)) :
    ∀ᵐ θ ∂π, IsPosteriorConsistent (Measure.infinitePi (fun _ : ℕ ↦ P θ)) post θ := by
  obtain ⟨G, hGm, hG⟩ := exists_measurable_ae_eq_param P hinj
  have hGJ : ∀ᵐ z ∂π ⊗ₘ iidKernel P, G z.2 = z.1 :=
    Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun (hGm.comp measurable_snd) measurable_fst)
      (ae_of_all _ hG)
  set 𝓑 := TopologicalSpace.countableBasis Θ
  have hbasis := TopologicalSpace.isBasis_countableBasis Θ
  have hall : ∀ᵐ z ∂π ⊗ₘ iidKernel P, ∀ B ∈ 𝓑,
      Tendsto (fun n ↦ (post n (samplePrefix n z)).real B) atTop
        (𝓝 (B.indicator (fun _ ↦ (1 : ℝ)) z.1)) :=
    (ae_ball_iff (TopologicalSpace.countable_countableBasis Θ)).mpr fun B hB ↦
      ae_tendsto_posterior_indicator π P Q hQ post hpost hGm hGJ
        (hbasis.isOpen hB).measurableSet
  filter_upwards [Measure.ae_ae_of_ae_compProd hall] with θ hθ U hU
  obtain ⟨B, hB𝓑, hθB, hBU⟩ := hbasis.mem_nhds_iff.mp hU
  change ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ P θ), _ at hθ
  filter_upwards [hθ] with x hx
  have h1 := hx B hB𝓑
  rw [Set.indicator_of_mem hθB] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n ↦ ?_) fun n ↦ ?_
  · have := (hpost n).1
    exact measureReal_mono hBU (measure_ne_top _ _)
  · have := (hpost n).1
    exact measureReal_le_one

/-- Second moment `∫ (log dP/dQ)² dP` of the log-likelihood ratio, used in the Kullback–Leibler
neighbourhoods of posterior contraction theory. -/
def logLikelihoodRatioSecondMoment {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.log ((P.rnDeriv Q x).toReal) ^ 2) ∂P

/-- Posterior contraction at the deterministic rate `ε` with respect to a loss `ρ` on parameters
(typically `ρ θ = d(θ, θ₀)` for a true parameter `θ₀`): there is `M₀ > 0` such that for every
`M ≥ M₀` the posterior mass `post n ω {θ | M εₙ ≤ ρ θ}` tends to zero in `μ`-probability. -/
def HasPosteriorContractionRate {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure Ω) (post : ℕ → Ω → Measure Θ) (ρ : Θ → ℝ) (ε : ℕ → ℝ) : Prop :=
  ∃ M₀ > 0, ∀ M ≥ M₀,
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (post n ω).real {θ | M * ε n ≤ ρ θ}) atTop (fun _ ↦ 0)

/-- The initial empty sample leaves the Dirichlet base measure unchanged. -/
@[simp] theorem dirichlet_posterior_base_empty {X : Type*} [MeasurableSpace X]
    (α : Measure X) (x : Fin 0 → X) : dirichletPosteriorBase α x = α := by
  simp [dirichletPosteriorBase]

/-- Zeroth stick-breaking weight. -/
@[simp] theorem stick_breaking_weight_zero (V : ℕ → ℝ) : stickBreakingWeight V 0 = V 0 := by
  simp [stickBreakingWeight]

end CKSD
