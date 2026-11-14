module

public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.UStatistics
public import Mathlib.Topology.Order.Compact
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Chi.Gaussian
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic


/-!
# Consistency, argmax and multinomial asymptotics

Consistency from outer uniform convergence and a separated maximum, the compact deterministic
argmax theorem, and Pearson's multinomial limit. U-statistic projection and variance interfaces
are re-exported from `CKSD.Asymptotics.UStatistics`.
Sources: GAPS 102.23, 102.31 and 102.33, `SYNOPSIS102.md`, and `STRUCTURE102.md`.

Pearson's limit combines the Euclidean central limit theorem of
`CKSD.Asymptotics.MultivariateCLT`, Mathlib's uniqueness of characteristic functions
(`Measure.ext_of_charFun`), and TauCeti's `stdGaussian_map_norm_sq` for the chi-squared law of a
standard Gaussian radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Constant random variables converge in probability to their constant value. -/
theorem tendsto_in_measure_const {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (μ : Measure Ω) (x : E) :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) ↦ x) atTop (fun _ ↦ x) := by
  intro ε hε
  simp [hε.ne']

/-- GAPS 102.23: consistency from uniform convergence and a separated maximum.
Pointwise bounds avoid any unmentioned measurability of a supremum. -/
theorem tendsto_in_measure_m_estimator {Ω Θ : Type*} [MeasurableSpace Ω]
    [MetricSpace Θ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Θ → ℝ) (Mn : ℕ → Ω → Θ → ℝ) (θ₀ : Θ) (T : ℕ → Ω → Θ)
    (e r : ℕ → Ω → ℝ)
    (he : TendstoInMeasure μ e atTop (fun _ ↦ 0)) (hr : TendstoInMeasure μ r atTop (fun _ ↦ 0))
    (hsep : ∀ ε > 0, ∃ δ > 0, ∀ θ, ε ≤ dist θ θ₀ → M θ ≤ M θ₀ - δ)
    (hunif : ∀ n, ∀ᵐ ω ∂μ, ∀ θ, |Mn n ω θ - M θ| ≤ e n ω)
    (hopt : ∀ n, ∀ᵐ ω ∂μ, Mn n ω θ₀ - r n ω ≤ Mn n ω (T n ω)) :
    TendstoInMeasure μ T atTop (fun _ ↦ θ₀) := by
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at he hr ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsepδ⟩ := hsep ε hε
  have he' := he (δ / 8) (by positivity)
  have hr' := hr (δ / 4) (by positivity)
  simp only [Real.dist_eq, sub_zero] at he' hr'
  have hbound (n : ℕ) : μ.real {ω | ε < dist (T n ω) θ₀} ≤
      μ.real {ω | δ / 8 < |e n ω|} + μ.real {ω | δ / 4 < |r n ω|} := by
    have hsub : {ω | ε < dist (T n ω) θ₀} ≤ᵐ[μ]
        {ω | δ / 8 < |e n ω|} ∪ {ω | δ / 4 < |r n ω|} := by
      filter_upwards [hunif n, hopt n] with ω hu ho
      intro hdist
      change δ / 8 < |e n ω| ∨ δ / 4 < |r n ω|
      by_contra hfalse
      have heabs : |e n ω| ≤ δ / 8 := le_of_not_gt fun h ↦ hfalse (Or.inl h)
      have hrabs : |r n ω| ≤ δ / 4 := le_of_not_gt fun h ↦ hfalse (Or.inr h)
      have heup : e n ω ≤ δ / 8 := (le_abs_self _).trans heabs
      have hrup : r n ω ≤ δ / 4 := (le_abs_self _).trans hrabs
      have hu₀ := (abs_le.mp (hu θ₀)).1
      have huT := (abs_le.mp (hu (T n ω))).2
      have hgap := hsepδ (T n ω) hdist.le
      linarith
    exact (ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)).trans
      (measureReal_union_le _ _)
  exact squeeze_zero (fun _ ↦ measureReal_nonneg) hbound
    (by simpa using he'.add hr')

/-- The orthogonal projection of a standard Gaussian vector onto a subspace `K` is standard
Gaussian on `K`. -/
private theorem std_gaussian_map_orthogonal_projection_onto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) :
    (stdGaussian E).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply Measure.ext_of_charFun
  ext s
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_stdGaussian]
  have : ∀ y : E, inner ℝ (K.orthogonalProjectionOnto y) s = inner ℝ y (s : E) := fun y ↦ by
    rw [real_inner_comm, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, real_inner_comm]
  simp_rw [this]
  rw [← charFun_apply, charFun_stdGaussian]
  simp

open scoped Matrix in
/-- A centred Gaussian vector in `ℝᵏ` whose covariance form is `‖x‖² - ⟪u, x⟫²` for a unit vector
`u` (the projection onto `u⊥`) has squared norm with law `χ²_{k-1}`. -/
private theorem multivariate_gaussian_map_norm_sq_of_quadratic_eq {k : ℕ} (hk : 1 ≤ k)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) (u : EuclideanSpace ℝ (Fin k))
    (hu : ‖u‖ = 1) (hq : ∀ x : EuclideanSpace ℝ (Fin k),
      x ⬝ᵥ C *ᵥ x = ‖x‖ ^ 2 - inner ℝ u x ^ 2) :
    (multivariateGaussian 0 C).map (fun x ↦ ‖x‖ ^ 2) =
      TauCeti.Probability.chiSquaredMeasure (k - 1 : ℕ) := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin k)) := (ℝ ∙ u)ᗮ
  have hsp : ∀ x : EuclideanSpace ℝ (Fin k), K.starProjection x = x - inner ℝ u x • u := fun x ↦ by
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, hu]
    simp
  have hQ : multivariateGaussian 0 C =
      (stdGaussian (EuclideanSpace ℝ (Fin k))).map K.starProjection := by
    apply Measure.ext_of_charFun
    ext x
    rw [charFun_multivariateGaussian hC, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [Submodule.inner_starProjection_left_eq_right]
    rw [← charFun_apply, charFun_stdGaussian, hq]
    congr 1
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
    congr 2
    rw [hsp]
    have h1 : ‖x - inner ℝ u x • u‖ ^ 2 = ‖x‖ ^ 2 - inner ℝ u x ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, real_inner_smul_right, hu, Real.norm_eq_abs, mul_one,
        sq_abs, real_inner_comm]
      ring
    rw [← Complex.ofReal_pow, h1]
  have hfin : Module.finrank ℝ K = k - 1 := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1) := ⟨by simp; omega⟩
    exact Submodule.finrank_orthogonal_span_singleton (by rintro rfl; simp at hu)
  rw [hQ, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (fun x : EuclideanSpace ℝ (Fin k) ↦ ‖x‖ ^ 2) ∘ K.starProjection =
      (fun y : K ↦ ‖y‖ ^ 2) ∘ K.orthogonalProjectionOnto := by
    funext y; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
    std_gaussian_map_orthogonal_projection_onto, TauCeti.Probability.stdGaussian_map_norm_sq, hfin]


/-- Integrals against the categorical law `∑ᵢ pᵢ δᵢ` on `Fin k` are finite weighted sums. -/
private theorem integral_categorical {k : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (f : Fin k → F) :
    ∫ x, f x ∂(∑ i, ENNReal.ofReal (p i) • Measure.dirac i) = ∑ i, p i • f i := by
  rw [integral_finsetSum_measure]
  · simp [ENNReal.toReal_ofReal (hp _)]
  · intro i _
    exact (integrable_dirac (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Convergence in distribution to `Z` under `μ'` is convergence to the identity under the law of
`Z`. -/
private theorem tendsto_in_distribution_id_of_map_eq {Ω E Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {X : ℕ → Ω → E}
    {Z : Ω' → E} {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {ν : Measure E} [IsProbabilityMeasure ν]
    (h : TendstoInDistribution X atTop Z μ μ') (hZ : μ'.map Z = ν) :
    TendstoInDistribution X atTop id μ ν where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    convert h.tendsto using 3
    simp [hZ]

open scoped Matrix in
/-- GAPS 102.31: Pearson's chi-squared statistic `∑ (Nᵢ - n pᵢ)² / (n pᵢ)` for i.i.d. observations
with `k ≥ 2` categories of positive probabilities `pᵢ` converges in law to `χ²_{k-1}`. -/
theorem tendsto_in_distribution_pearson_statistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (X : ℕ → Ω → Fin k)
    (hiid : IsIndependentIdenticallyDistributed μ X (∑ i, ENNReal.ofReal (p i) • Measure.dirac i)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ ∑ i : Fin k,
      (((Finset.range n).filter (fun j ↦ X j ω = i)).card - (n : ℝ) * p i) ^ 2 /
        ((n : ℝ) * p i))
      atTop id (fun _ ↦ μ) (TauCeti.Probability.chiSquaredMeasure (k - 1 : ℕ)) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  set Pk : Measure (Fin k) := ∑ i, ENNReal.ofReal (p i) • Measure.dirac i with hPk
  set r : Fin k → ℝ := fun i ↦ Real.sqrt (p i) with hr
  have hr0 : ∀ i, 0 < r i := fun i ↦ Real.sqrt_pos.2 (hp i)
  have hrr : ∀ i, r i ^ 2 = p i := fun i ↦ Real.sq_sqrt (hp i).le
  set u : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 r with hu
  have hu1 : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [u, Real.norm_eq_abs, sq_abs, hrr, hsum]
  set φ : Fin k → EuclideanSpace ℝ (Fin k) := fun l ↦ (r l)⁻¹ • EuclideanSpace.single l 1 - u
    with hφ
  have hφm : Measurable φ := measurable_of_finite φ
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin k) := fun j ω ↦ φ (X j ω) with hY
  have hYm : ∀ j, Measurable (Y j) := fun j ↦ hφm.comp (hXm j)
  have hYlaw : ∀ j, μ.map (Y j) = Pk.map φ := fun j ↦ by
    change μ.map (φ ∘ X j) = _
    rw [← Measure.map_map hφm (hXm j), hlaw j]
  have hYind : iIndepFun Y μ := hind.comp (fun _ ↦ φ) (fun _ ↦ hφm)
  have hYid : ∀ j, IdentDistrib (Y j) (Y 0) μ μ := fun j ↦
    ⟨(hYm j).aemeasurable, (hYm 0).aemeasurable, by rw [hYlaw, hYlaw]⟩
  have h2 : MemLp (Y 0) 2 μ := MemLp.of_bound (hYm 0).aestronglyMeasurable (∑ l, ‖φ l‖)
    (ae_of_all _ fun ω ↦ Finset.single_le_sum (f := fun l ↦ ‖φ l‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _))
  have hinner : ∀ x l, inner ℝ x (φ l) = (r l)⁻¹ * x l - inner ℝ x u := fun x l ↦ by
    simp [φ, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right]
  have hmean : ∫ ω, Y 0 ω ∂μ = 0 := by
    change ∫ ω, φ (X 0 ω) ∂μ = 0
    rw [← integral_map (hXm 0).aemeasurable hφm.aestronglyMeasurable, hlaw 0,
      integral_categorical p (fun i ↦ (hp i).le)]
    ext i
    simp only [φ, u, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.zero_apply]
    simp
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, ← Finset.sum_mul, hsum, one_mul]
    rw [← hrr i]
    field_simp [(hr0 i).ne']
    ring
  have h2P : MemLp id 2 (μ.map (Y 0)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hYm 0).aemeasurable).mpr h2
  set C := TauCeti.covMatrix (μ.map (Y 0)) with hCdef
  have hC : C.PosSemidef := TauCeti.posSemidef_covMatrix _ h2P
  have hq : ∀ x : EuclideanSpace ℝ (Fin k), x ⬝ᵥ C *ᵥ x = ‖x‖ ^ 2 - inner ℝ u x ^ 2 := by
    intro x
    have hb := TauCeti.covarianceBilin_eq_covMatrix _ h2P x x
    rw [covarianceBilin_self h2P] at hb
    have hlhs : inner ℝ x (C.toEuclideanLin x) = x ⬝ᵥ C *ᵥ x := by
      simp [Matrix.toEuclideanLin, PiLp.inner_apply, dotProduct, mul_comm]
    rw [← hlhs, ← hb, hYlaw 0, variance_map (by fun_prop) hφm.aemeasurable]
    have hs : inner ℝ x u = ∑ l, r l * x l := by simp [PiLp.inner_apply, u]
    have hm0 : ∫ l, ((fun z ↦ inner ℝ x z) ∘ φ) l ∂Pk = 0 := by
      rw [integral_categorical p (fun i ↦ (hp i).le)]
      simp only [Function.comp_apply, hinner, smul_eq_mul]
      have hterm : ∀ l, p l * ((r l)⁻¹ * x l - inner ℝ x u) = r l * x l - p l * inner ℝ x u :=
        fun l ↦ by rw [← hrr l]; field_simp [(hr0 l).ne']
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, ← hs]
      ring
    rw [variance_of_integral_eq_zero (by fun_prop) hm0, integral_categorical p (fun i ↦ (hp i).le)]
    simp only [Function.comp_apply, hinner, smul_eq_mul]
    have hterm : ∀ l, p l * ((r l)⁻¹ * x l - inner ℝ x u) ^ 2 =
        x l ^ 2 - 2 * inner ℝ x u * (r l * x l) + p l * inner ℝ x u ^ 2 :=
      fun l ↦ by rw [← hrr l]; field_simp [(hr0 l).ne']; ring
    rw [Finset.sum_congr rfl fun l _ ↦ hterm l]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hsum, ← hs, EuclideanSpace.real_norm_sq_eq]
    rw [real_inner_comm u x]
    ring
  have hclt := tendsto_in_distribution_inv_sqrt_smul_sum_sub_of_iid μ Y h2 hYind hYid
  simp only [hmean, smul_zero, sub_zero] at hclt
  have hcomp := hclt.continuous_comp (g := fun x : EuclideanSpace ℝ (Fin k) ↦ ‖x‖ ^ 2)
    (by fun_prop)
  have hlim := multivariate_gaussian_map_norm_sq_of_quadratic_eq (by omega) C hC u hu1 hq
  refine (tendsto_in_distribution_id_of_map_eq hcomp (by rw [Function.comp_id]; exact hlim)).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  have hcoord : ∀ i, (∑ j ∈ Finset.range n, Y j ω) i =
      (r i)⁻¹ * (((Finset.range n).filter (fun j ↦ X j ω = i)).card : ℝ) - n * r i := by
    intro i
    simp [Y, φ, u, Finset.sum_sub_distrib]
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases h : X j ω = i
    · simp [h]
    · simp [h, Ne.symm h]
  simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq, PiLp.smul_apply, smul_eq_mul,
    hcoord]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [mul_pow, inv_pow, Real.sq_sqrt hn'.le, ← hrr i]
  field_simp [(hr0 i).ne', hn'.ne']

/-- GAPS 102.33, the argmax theorem with a deterministic limit on a compact space. If the
criteria `Mₙ` converge uniformly in probability to a continuous `M` with a unique maximizer `θ`,
then maximizers `Tₙ` of `Mₙ` converge in probability to `θ`. -/
theorem tendsto_in_measure_argmax_of_compact
    {Ω H : Type*} [MeasurableSpace Ω]
    [MetricSpace H] [CompactSpace H] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : H → ℝ) (hc : Continuous M) (θ : H) (huniq : ∀ h, h ≠ θ → M h < M θ)
    (Mn : ℕ → Ω → H → ℝ) (T : ℕ → Ω → H)
    (e : ℕ → Ω → ℝ) (he : TendstoInMeasure μ e atTop (fun _ ↦ 0))
    (hu : ∀ n, ∀ᵐ ω ∂μ, ∀ h, |Mn n ω h - M h| ≤ e n ω)
    (ho : ∀ n, ∀ᵐ ω ∂μ, ∀ h, Mn n ω h ≤ Mn n ω (T n ω)) :
    TendstoInMeasure μ T atTop (fun _ ↦ θ) := by
  have hsep : ∀ ε > 0, ∃ δ > 0, ∀ h, ε ≤ dist h θ → M h ≤ M θ - δ := by
    intro ε hε
    let K := {h : H | ε ≤ dist h θ}
    have hclosed : IsClosed K := isClosed_le continuous_const
      (continuous_id.dist continuous_const)
    by_cases hne : K.Nonempty
    · obtain ⟨m, hm, hmax⟩ := hclosed.isCompact.exists_isMaxOn hne hc.continuousOn
      have hmne : m ≠ θ := by
        intro heq
        change ε ≤ dist m θ at hm
        rw [heq, dist_self] at hm
        exact (not_le_of_gt hε) hm
      refine ⟨M θ - M m, sub_pos.mpr (huniq m hmne), ?_⟩
      intro h hh
      have hMh : M h ≤ M m := hmax hh
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro h hh
      exact (hne ⟨h, hh⟩).elim
  apply tendsto_in_measure_m_estimator μ M Mn θ T e (fun _ _ ↦ 0)
    he (tendsto_in_measure_const μ 0) hsep hu
  intro n
  filter_upwards [ho n] with ω hω
  simpa only [sub_zero] using hω θ


end CKSD
