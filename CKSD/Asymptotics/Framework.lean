module

public import CKSD.Asymptotics.Basic
public import CKSD.Inference.Model
public import Statlib.Contiguity.Def
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Asymptotic statistical interfaces

Outer expectation, stochastic orders, tangential Hadamard differentiation, and local experiments.
The local parameter `h` of an experiment denotes the displacement `h / sqrt n` from its centre;
its estimator is already scaled by `sqrt n`. This permits observation spaces depending on `n`.
Contiguity for probability measures is Statlib's `Contiguous5` (direct set formulation).
Sources: Sections 102 and 103 of `GAPS.md`.
The functional delta method uses Mathlib's closed-set portmanteau theorem
(`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`, `tendsto_of_forall_isClosed_limsup_le'`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Outer expectation of a nonnegative function, as the infimum over measurable majorants. -/
def outerExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : ∀ ω, f ω ≤ g ω), ∫⁻ ω, g ω ∂μ

/-- Weak convergence in the outer-expectation sense, allowing nonmeasurable random elements.
Shifting a bounded continuous test by its norm makes the integrand nonnegative. -/
def TendstoInOuterDistribution {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    Tendsto (fun n ↦ (outerExpectation μ (fun ω ↦ ENNReal.ofReal (f (X n ω) + ‖f‖))).toReal)
      atTop (𝓝 (∫ x, f x + ‖f‖ ∂ν))

/-- Convergence to zero in probability for a sequence of varying observation spaces and laws. -/
def TendstoInProbabilityZero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n ↦ (P n).real {ω | ε < |X n ω|}) atTop (𝓝 0)

/-- Stochastic little-o with a deterministic positive scale. -/
def IsLittleOInProbability {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (r : ℕ → ℝ) : Prop :=
  TendstoInProbabilityConst μ (fun n ω ↦ ‖X n ω‖ / r n) 0

/-- Stochastic big-O with a deterministic positive scale. -/
def IsBigOInProbability {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : ℕ → Ω → E) (r : ℕ → ℝ) : Prop :=
  IsBoundedInProbability μ (fun n ω ↦ ‖X n ω‖ / r n)

/-- Sequential tangential Hadamard differentiability, with a continuous linear extension. -/
def HasHadamardFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (domain : Set E)
    (D₀ : Submodule ℝ E) (D : E →L[ℝ] F) (θ : E) : Prop :=
  θ ∈ domain ∧ ∀ (t : ℕ → ℝ) (h : ℕ → E) (v : E),
    (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) → Tendsto h atTop (𝓝 v) → v ∈ D₀ →
    (∀ n, θ + t n • h n ∈ domain) →
    Tendsto (fun n ↦ (t n)⁻¹ • (g (θ + t n • h n) - g θ)) atTop (𝓝 (D v))

/-- A local experiment with observation space depending on sample size. -/
abbrev LocalExperiment (d : ℕ) (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] :=
  ∀ n, EuclideanSpace ℝ (Fin d) → ProbabilityMeasure (Ω n)

/-- Local asymptotic normality: Gaussian central sequence and log-likelihood expansion. -/
def IsLocallyAsymptoticallyNormal {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) : Prop :=
  I.PosDef ∧ (∀ n, Measurable (Δ n)) ∧
    TendstoWeakly (fun n ↦ (P n 0 : Measure (Ω n)).map (Δ n)) (multivariateGaussian 0 I) ∧
    ∀ h, TendstoInProbabilityZero (fun n ↦ (P n 0 : Measure (Ω n)))
      (fun n ω ↦ Real.log (((P n h : Measure (Ω n)).rnDeriv (P n 0) ω).toReal) -
        inner ℝ h (Δ n ω) + inner ℝ h (Matrix.toEuclideanCLM (𝕜 := ℝ) I h) / 2)

/-- Regularity of a locally scaled estimator: its centred limit is independent of the local
parameter. -/
def IsRegularEstimator {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ n, Measurable (T n)) ∧ ∀ h,
    TendstoWeakly (fun n ↦ (P n h : Measure (Ω n)).map (fun ω ↦ T n ω - h)) L

/-- Convolution of two vector laws, using the pushforward of independent addition. -/
def convolutionLaw {E : Type*} [MeasurableSpace E] [Add E] (P Q : Measure E) : Measure E :=
  (P.prod Q).map (fun z ↦ z.1 + z.2)

/-- GAPS 102.15: representation of limit procedures by a kernel in the Gaussian shift experiment. -/
theorem exists_gaussian_shift_kernel_of_local_limits
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [TopologicalSpace S] [PolishSpace S] [BorelSpace S]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → S) (hT : ∀ n, Measurable (T n))
    (L : EuclideanSpace ℝ (Fin d) → Measure S) (hL : ∀ h, IsProbabilityMeasure (L h))
    (hlim : ∀ h, TendstoWeakly (fun n ↦ (P n h : Measure (Ω n)).map (T n)) (L h)) :
    ∃ K : Kernel (EuclideanSpace ℝ (Fin d)) S, IsMarkovKernel K ∧
      ∀ h, L h = K ∘ₘ multivariateGaussian h I⁻¹ := by
  sorry

/-- GAPS 102.16: convolution theorem for a regular estimator in a LAN experiment. -/
theorem exists_convolution_of_isRegularEstimator
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure L]
    (hreg : IsRegularEstimator P T L) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure M ∧
      L = convolutionLaw (multivariateGaussian 0 I⁻¹) M := by
  sorry

/-- GAPS 102.17: local asymptotic minimax lower bound for a bowl-shaped nonnegative loss. -/
theorem gaussian_risk_le_local_asymptotic_minimax
    {d : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : LocalExperiment d Ω) (I : Matrix (Fin d) (Fin d) ℝ)
    (Δ : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hLAN : IsLocallyAsymptoticallyNormal P I Δ)
    (T : ∀ n, Ω n → EuclideanSpace ℝ (Fin d)) (hT : ∀ n, Measurable (T n))
    (loss : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hl : LowerSemicontinuous loss)
    (hsym : ∀ x, loss (-x) = loss x) (hconv : ∀ c, Convex ℝ {x | loss x ≤ c}) :
    (∫⁻ x, loss x ∂multivariateGaussian 0 I⁻¹) ≤
      ⨆ c : ℝ≥0, Filter.liminf (fun n ↦ ⨆ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ c},
        ∫⁻ ω, loss (T n ω - h.val) ∂(P n h.val : Measure (Ω n))) atTop := by
  sorry

/-- GAPS 102.28: functional delta method for measurable maps and a closed tangent space.
The outer version for nonmeasurable empirical processes uses `TendstoInOuterDistribution`. -/
theorem tendstoInDistribution_of_hasHadamardFDerivAt
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E) (hT : ∀ n, Measurable (T n))
    (θ : E) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop atTop)
    (G : Measure E) [IsProbabilityMeasure G] (D₀ : Submodule ℝ E) (hclosed : IsClosed (D₀ : Set E))
    (hsupp : G D₀ = 1) (g : E → F) (hg : Measurable g) (domain : Set E)
    (hdomain : ∀ n ω, T n ω ∈ domain) (D : E →L[ℝ] F)
    (hd : HasHadamardFDerivAt g domain D₀ D θ)
    (hlim : TendstoInDistribution μ (fun n ω ↦ r n • (T n ω - θ)) G) :
    TendstoInDistribution μ (fun n ω ↦ r n • (g (T n ω) - g θ)) (G.map D) := by
  set Z : ℕ → Ω → E := fun n ω ↦ r n • (T n ω - θ) with hZ
  set Y : ℕ → Ω → F := fun n ω ↦ r n • (g (T n ω) - g θ) with hY
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hT n)
  have hYm : ∀ n, Measurable (Y n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hg.comp (hT n))
  -- Probability-measure versions of the laws.
  let PZ : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μ.map (Z n), inferInstance⟩
  let PY : ℕ → ProbabilityMeasure F := fun n ↦ ⟨μ.map (Y n), inferInstance⟩
  let PG : ProbabilityMeasure E := ⟨G, inferInstance⟩
  let PGD : ProbabilityMeasure F := ⟨G.map D, inferInstance⟩
  have hZlim : Tendsto PZ atTop (𝓝 PG) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 hlim
  suffices hYlim : Tendsto PY atTop (𝓝 PGD) from
    fun f ↦ ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hYlim f
  refine tendsto_of_forall_isClosed_limsup_le' fun Fc hFc ↦ ?_
  -- The sets of local increments mapped into `Fc` at stage `m`.
  let A : ℕ → Set E := fun m ↦
    {h | θ + (r m)⁻¹ • h ∈ domain ∧ r m • (g (θ + (r m)⁻¹ • h) - g θ) ∈ Fc}
  let C : ℕ → Set E := fun k ↦ closure (⋃ m ≥ k, A m)
  have hCc : ∀ k, IsClosed (C k) := fun k ↦ isClosed_closure
  have hCanti : Antitone C := fun k l hkl ↦
    closure_mono (iUnion₂_subset fun m hm ↦ subset_iUnion₂_of_subset m (hkl.trans hm) le_rfl)
  have hTZ : ∀ n ω, θ + (r n)⁻¹ • Z n ω = T n ω := fun n ω ↦ by
    simp only [hZ, smul_smul, inv_mul_cancel₀ (hr n).ne', one_smul, add_sub_cancel]
  -- Step 1: bound the laws of `Yₙ` on `Fc` by those of `Zₙ` on `C k`.
  have hstep : ∀ k, limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (C k) := by
    intro k
    have hle : ∀ n ≥ k, (PY n : Measure F) Fc ≤ (PZ n : Measure E) (C k) := by
      intro n hn
      change μ.map (Y n) Fc ≤ μ.map (Z n) (C k)
      rw [Measure.map_apply (hYm n) hFc.measurableSet,
        Measure.map_apply (hZm n) (hCc k).measurableSet]
      refine measure_mono fun ω hω ↦ subset_closure ?_
      refine mem_iUnion₂.2 ⟨n, hn, ?_⟩
      simp only [A, mem_ofPred_eq, hTZ]
      exact ⟨hdomain n ω, hω⟩
    calc limsup (fun n ↦ (PY n : Measure F) Fc) atTop
        ≤ limsup (fun n ↦ (PZ n : Measure E) (C k)) atTop :=
          limsup_le_limsup (eventually_atTop.2 ⟨k, hle⟩)
      _ ≤ G (C k) := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hZlim (hCc k)
  -- Step 2: pass to the intersection.
  have hInter : Tendsto (fun k ↦ G (C k)) atTop (𝓝 (G (⋂ k, C k))) :=
    tendsto_measure_iInter_atTop (fun k ↦ (hCc k).measurableSet.nullMeasurableSet) hCanti
      ⟨0, measure_ne_top _ _⟩
  have hlimsup : limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (⋂ k, C k) :=
    ge_of_tendsto hInter (Eventually.of_forall hstep)
  -- Step 3: on `D₀`, the intersection maps into `Fc`.
  have hsub : (⋂ k, C k) ∩ D₀ ⊆ D ⁻¹' Fc := by
    rintro v ⟨hv, hvD⟩
    have hvk : ∀ k : ℕ, ∃ m, k ≤ m ∧ ∃ h ∈ A m, dist h v < 1 / ((k : ℝ) + 1) := by
      intro k
      have hk := mem_iInter.1 hv k
      obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.1 hk _ Nat.one_div_pos_of_nat
      obtain ⟨m, hm, hhm⟩ := mem_iUnion₂.1 hh
      exact ⟨m, hm, h, hhm, by rwa [dist_comm]⟩
    choose m hm h hhA hhd using hvk
    have hmlim : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
    have ht : Tendsto (fun k ↦ (r (m k))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hrlim.comp hmlim)
    have hh : Tendsto h atTop (𝓝 v) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hhd k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := hd.2 (fun k ↦ (r (m k))⁻¹) h v (fun k ↦ inv_pos.2 (hr _)) ht hh hvD
      (fun k ↦ (hhA k).1)
    simp only [inv_inv] at hconv
    exact hFc.mem_of_tendsto hconv (Eventually.of_forall fun k ↦ (hhA k).2)
  -- Step 4: conclude.
  have hD0c : G (D₀ : Set E)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hclosed.measurableSet, hsupp, tsub_self]
  refine hlimsup.trans ?_
  change G (⋂ k, C k) ≤ G.map D Fc
  rw [Measure.map_apply D.continuous.measurable hFc.measurableSet]
  calc G (⋂ k, C k) ≤ G (((⋂ k, C k) ∩ D₀) ∪ (D₀ : Set E)ᶜ) := by
        refine measure_mono fun v hv ↦ ?_
        by_cases hvD : v ∈ (D₀ : Set E)
        · exact Or.inl ⟨hv, hvD⟩
        · exact Or.inr hvD
    _ ≤ G ((⋂ k, C k) ∩ D₀) + G (D₀ : Set E)ᶜ := measure_union_le _ _
    _ ≤ G (D ⁻¹' Fc) := by rw [hD0c, add_zero]; exact measure_mono hsub


/-- Fisher–Rao bilinear form on the open finite probability simplex. -/
def fisherRaoMetric {m : ℕ} (p u v : Fin m → ℝ) : ℝ := ∑ i, u i * v i / p i

/-- Amari–Chentsov symmetric cubic tensor on the open probability simplex. -/
def amariChentsovTensor {m : ℕ} (p u v w : Fin m → ℝ) : ℝ :=
  ∑ i, u i * v i * w i / p i ^ 2

/-- The open probability simplex. -/
def openProbabilitySimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- Tangent space of the probability simplex, represented by zero-sum vectors. -/
def simplexTangentSpace (m : ℕ) : Submodule ℝ (Fin m → ℝ) where
  carrier := {u | ∑ i, u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    change (∑ i, u i) = 0 at hu
    change (∑ i, v i) = 0 at hv
    change (∑ i, (u i + v i)) = 0
    rw [Finset.sum_add_distrib, hu, hv, add_zero]
  smul_mem' := by
    intro a u hu
    change (∑ i, u i) = 0 at hu
    change (∑ i, a * u i) = 0
    rw [← Finset.mul_sum, hu, mul_zero]

/-- A congruent embedding splits each input category into a nonempty block of output categories. -/
structure CongruentSimplexEmbedding (m n : ℕ) where
  /-- Block label of an output category. -/
  block : Fin n → Fin m
  /-- Every input category has a block. -/
  surjective_block : Function.Surjective block
  /-- Conditional probability of each output category within its block. -/
  weight : Fin n → ℝ
  /-- Strictly positive weights. -/
  weight_pos : ∀ j, 0 < weight j
  /-- Weights in a block sum to one. -/
  sum_weight : ∀ i, ∑ j, (if block j = i then weight j else 0) = 1

/-- Linear map underlying a congruent simplex embedding and its derivative. -/
def CongruentSimplexEmbedding.map {m n : ℕ} (f : CongruentSimplexEmbedding m n)
    (p : Fin m → ℝ) : Fin n → ℝ := fun j ↦ p (f.block j) * f.weight j

/-- GAPS 102.58, defining invariance of Fisher–Rao under congruent embeddings. -/
theorem fisherRaoMetric_congruent_embedding {m n : ℕ} (f : CongruentSimplexEmbedding m n)
    (p : Fin m → ℝ) (hp : p ∈ openProbabilitySimplex m) (u v : Fin m → ℝ) :
    fisherRaoMetric (f.map p) (f.map u) (f.map v) = fisherRaoMetric p u v := by
  let a := fun i ↦ u i * v i / p i
  have hterm (j : Fin n) : f.map u j * f.map v j / f.map p j = a (f.block j) * f.weight j := by
    dsimp [CongruentSimplexEmbedding.map, a]
    field_simp [ne_of_gt (hp.1 (f.block j)), ne_of_gt (f.weight_pos j)]

  unfold fisherRaoMetric
  simp_rw [hterm]
  calc
    (∑ j, a (f.block j) * f.weight j) =
        ∑ j, ∑ i, if f.block j = i then a i * f.weight j else 0 := by simp
    _ = ∑ i, ∑ j, if f.block j = i then a i * f.weight j else 0 := Finset.sum_comm
    _ = ∑ i, a i * (∑ j, if f.block j = i then f.weight j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ i, u i * v i / p i := by simp_rw [f.sum_weight, mul_one]; rfl

/-- CKSD's measure-sequence contiguity adapter agrees with Statlib's direct set formulation. -/
theorem isContiguous_iff_contiguous5 {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → ProbabilityMeasure Ω) :
    IsContiguous (fun n ↦ (P n : Measure Ω)) (fun n ↦ (Q n : Measure Ω)) ↔
      _root_.Contiguous5 atTop P Q := by
  constructor
  · intro h A hA hP
    apply NNReal.tendsto_coe.mp
    have hp := NNReal.tendsto_coe.mpr hP
    have hq := h A hA (by simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hp)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hq
  · intro h A hA hP
    have hp : Tendsto (fun n ↦ P n (A n)) atTop (𝓝 0) := by
      apply NNReal.tendsto_coe.mp
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hP
    have hq := NNReal.tendsto_coe.mpr (h hA hp)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, NNReal.coe_zero] using hq

end CKSD
