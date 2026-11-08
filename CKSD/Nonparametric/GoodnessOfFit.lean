module

public import CKSD.Nonparametric.Models
public import TauCeti.Probability.Distributions.OrderStatistic.Joint
public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Quantile

/-!
# Distribution-free goodness-of-fit statistics and residual eigenvector bounds

Sources: GAPS 103.17 and 103.54; the scopes are the finite-sample distribution-freeness and
deterministic residual-bound parts described in `GAPS_EASY.md`.

The Cramér–von Mises argument uses TauCeti's inverse transform sampling
(`MeasureTheory.Measure.map_quantile_volume_Ioo`), the quantile–CDF relations
`MeasureTheory.Measure.quantile_le_iff` and `MeasureTheory.Measure.cdf_quantile`, CDF continuity
`MeasureTheory.Measure.continuous_cdf_of_noAtoms`, and the uniform law
`TauCeti.Probability.uniformMeasure` with `TauCeti.Probability.cdf_uniformMeasure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Empirical distribution function of a finite sample. -/
def finiteEmpiricalCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun i ↦ x i ≤ t).card : ℝ) / n

/-- Cramér–von Mises statistic, with the factor `n` normalization. -/
def cramerVonMisesStatistic {n : ℕ} (P : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∫ t, (finiteEmpiricalCDF x t - cdf P t) ^ 2 ∂P

/-- Two-sample Kolmogorov–Smirnov statistic, without the asymptotic scaling factor. -/
def twoSampleKolmogorovSmirnovStatistic {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sSup (range fun t : ℚ ↦ |finiteEmpiricalCDF x t - finiteEmpiricalCDF y t|)

/-- The finite empirical distribution function is jointly measurable in the sample and the
argument. -/
theorem measurable_finiteEmpiricalCDF_uncurry (n : ℕ) :
    Measurable fun z : (Fin n → ℝ) × ℝ ↦ finiteEmpiricalCDF z.1 z.2 := by
  unfold finiteEmpiricalCDF
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ ↦ ?_) _
  exact Measurable.ite (measurableSet_le ((measurable_pi_apply i).comp measurable_fst)
    measurable_snd) measurable_const measurable_const

/-- The distribution function `t ↦ P (-∞, t]` of a finite measure is measurable. -/
theorem measurable_cdf_of_isFiniteMeasure (P : Measure ℝ) [IsFiniteMeasure P] :
    Measurable (cdf P) :=
  Monotone.measurable fun _ _ h ↦ measureReal_mono (Iic_subset_Iic.mpr h)

/-- The Cramér–von Mises statistic is a measurable function of the sample. -/
theorem measurable_cramerVonMisesStatistic (P : Measure ℝ) [IsFiniteMeasure P] (n : ℕ) :
    Measurable (cramerVonMisesStatistic (n := n) P) := by
  unfold cramerVonMisesStatistic
  refine measurable_const.mul ?_
  have h : Measurable fun z : (Fin n → ℝ) × ℝ ↦ (finiteEmpiricalCDF z.1 z.2 - cdf P z.2) ^ 2 :=
    ((measurable_finiteEmpiricalCDF_uncurry n).sub ((measurable_cdf_of_isFiniteMeasure P).comp measurable_snd)).pow_const 2
  exact (h.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- GAPS 103.17: finite-sample distribution-freeness of the Cramér–von Mises statistic.
The reference law `U` is the uniform probability law on the unit interval. -/
theorem map_cramerVonMisesStatistic_eq_uniform (P : Measure ℝ) [IsProbabilityMeasure P]
    [NullSingletonClass P] (n : ℕ)  :
    let U := TauCeti.Probability.uniformMeasure 0 1;
    (Measure.pi fun _ : Fin n ↦ P).map (cramerVonMisesStatistic P) =
      (Measure.pi fun _ : Fin n ↦ U).map (cramerVonMisesStatistic U) := by
  intro U
  set V : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hV
  have hVprob : IsProbabilityMeasure V := ⟨by simp [V]⟩
  have hUV : U = V := by
    simp only [U, V, TauCeti.Probability.uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one,
      inv_one, one_smul]
    exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hcdfV : ∀ s ∈ Ioo (0 : ℝ) 1, cdf V s = s := by
    intro s hs
    have : cdf V s = ProbabilityTheory.cdf V s := (ProbabilityTheory.cdf_eq_real (μ := V) s).symm
    rw [this, ← hUV, TauCeti.Probability.cdf_uniformMeasure zero_lt_one, if_neg (not_le.mpr hs.1),
      if_neg (not_le.mpr hs.2)]
    simp
  set Q := P.quantile with hQ
  have hQm : Measurable Q := Measure.measurable_quantile P
  have hmap : V.map Q = P := Measure.map_quantile_volume_Ioo P
  have hcont := Measure.continuous_cdf_of_noAtoms P
  -- the pointwise identity
  have hpt : ∀ u : Fin n → ℝ, (∀ i, u i ∈ Ioo (0 : ℝ) 1) →
      cramerVonMisesStatistic P (fun i ↦ Q (u i)) = cramerVonMisesStatistic V u := by
    intro u hu
    unfold cramerVonMisesStatistic
    congr 1
    have hg : Measurable fun t ↦ (finiteEmpiricalCDF (fun i ↦ Q (u i)) t - cdf P t) ^ 2 :=
      (((measurable_finiteEmpiricalCDF_uncurry n).comp (measurable_const.prodMk measurable_id)).sub
        (measurable_cdf_of_isFiniteMeasure P)).pow_const 2
    calc ∫ t, (finiteEmpiricalCDF (fun i ↦ Q (u i)) t - cdf P t) ^ 2 ∂P
        = ∫ t, (finiteEmpiricalCDF (fun i ↦ Q (u i)) t - cdf P t) ^ 2 ∂(V.map Q) := by
          rw [hmap]
      _ = ∫ s, (finiteEmpiricalCDF (fun i ↦ Q (u i)) (Q s) - cdf P (Q s)) ^ 2 ∂V :=
          integral_map hQm.aemeasurable hg.aestronglyMeasurable
      _ = ∫ s, (finiteEmpiricalCDF u s - cdf V s) ^ 2 ∂V := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          have hFQ' : ProbabilityTheory.cdf P (Q s) = s := Measure.cdf_quantile P hcont hs.1 hs.2
          have hFQ : cdf P (Q s) = s :=
            (ProbabilityTheory.cdf_eq_real (μ := P) (Q s)).symm.trans hFQ'
          rw [hFQ, hcdfV s hs]
          congr 2
          unfold finiteEmpiricalCDF
          congr 2
          refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
          show Q (u i) ≤ Q s ↔ u i ≤ s
          rw [hQ, Measure.quantile_le_iff P (hu i).1 (hu i).2, ← hQ, hFQ']
  -- assemble
  have hQn : Measurable fun (u : Fin n → ℝ) (i : Fin n) ↦ Q (u i) :=
    measurable_pi_iff.mpr fun i ↦ hQm.comp (measurable_pi_apply i)
  have hpi : (Measure.pi fun _ : Fin n ↦ P) =
      (Measure.pi fun _ : Fin n ↦ V).map fun u i ↦ Q (u i) := by
    rw [Measure.pi_map_pi (fun _ ↦ hQm.aemeasurable)]
    simp only [hmap]
  have hae : ∀ᵐ u ∂(Measure.pi fun _ : Fin n ↦ V), ∀ i, u i ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n ↦ V) i).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioo)
  rw [hpi, Measure.map_map (measurable_cramerVonMisesStatistic P n) hQn, hUV]
  exact Measure.map_congr (hae.mono fun u hu ↦ hpt u hu)

/-- The finite empirical distribution function takes values in `[0, 1]`. -/
theorem finiteEmpiricalCDF_mem_Icc {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    finiteEmpiricalCDF x t ∈ Icc (0 : ℝ) 1 := by
  unfold finiteEmpiricalCDF
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [div_le_one (by exact_mod_cast hn)]
  exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

/-- Two finite empirical distribution functions take at every real point the same pair of
values as at some rational point slightly to the right. -/
theorem exists_rat_finiteEmpiricalCDF_eq {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) (r : ℝ) :
    ∃ q : ℚ, finiteEmpiricalCDF x q = finiteEmpiricalCDF x r ∧
      finiteEmpiricalCDF y q = finiteEmpiricalCDF y r := by
  -- a gap to the right of `r` that contains no sample point
  set Sx := (Finset.univ.filter fun i ↦ r < x i).image fun i ↦ x i - r
  set Sy := (Finset.univ.filter fun j ↦ r < y j).image fun j ↦ y j - r
  set S := insert 1 (Sx ∪ Sy)
  have hSpos : ∀ d ∈ S, 0 < d := by
    intro d hd
    simp only [S, Sx, Sy, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at hd
    rcases hd with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · exact one_pos
    · linarith
    · linarith
  set δ := S.min' ⟨1, Finset.mem_insert_self _ _⟩
  have hδ : 0 < δ := hSpos _ (Finset.min'_mem _ _)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r < r + δ by linarith)
  refine ⟨q, ?_, ?_⟩
  · unfold finiteEmpiricalCDF
    congr 1
    refine congrArg (fun s : Finset _ ↦ (s.card : ℝ)) (Finset.filter_congr fun i _ ↦
      ⟨fun (h : x i ≤ (q : ℝ)) ↦ ?_, fun (h : x i ≤ r) ↦ h.trans hq1.le⟩)
    by_contra hr
    push Not at hr
    have : x i - r ∈ S := by
      simp only [S, Sx, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr (Or.inl ⟨i, hr, rfl⟩)
    have := Finset.min'_le S _ this
    linarith
  · unfold finiteEmpiricalCDF
    congr 1
    refine congrArg (fun s : Finset _ ↦ (s.card : ℝ)) (Finset.filter_congr fun j _ ↦
      ⟨fun (h : y j ≤ (q : ℝ)) ↦ ?_, fun (h : y j ≤ r) ↦ h.trans hq1.le⟩)
    by_contra hr
    push Not at hr
    have : y j - r ∈ S := by
      simp only [S, Sy, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr (Or.inr ⟨j, hr, rfl⟩)
    have := Finset.min'_le S _ this
    linarith

/-- The finite empirical distribution function at a fixed point is measurable in the sample. -/
theorem measurable_finiteEmpiricalCDF {k : ℕ} (t : ℝ) :
    Measurable fun x : Fin k → ℝ ↦ finiteEmpiricalCDF x t := by
  unfold finiteEmpiricalCDF
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ ↦ ?_) _
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const

/-- The two-sample Kolmogorov–Smirnov statistic is a measurable function of the two samples. -/
theorem measurable_twoSampleKolmogorovSmirnovStatistic (m n : ℕ) :
    Measurable fun z : (Fin m → ℝ) × (Fin n → ℝ) ↦
      twoSampleKolmogorovSmirnovStatistic z.1 z.2 := by
  have hf : ∀ t : ℚ, Measurable fun z : (Fin m → ℝ) × (Fin n → ℝ) ↦
      |finiteEmpiricalCDF z.1 (t : ℝ) - finiteEmpiricalCDF z.2 (t : ℝ)| := fun t ↦
    continuous_abs.measurable.comp
      (((measurable_finiteEmpiricalCDF (t : ℝ)).comp measurable_fst).sub
        ((measurable_finiteEmpiricalCDF (t : ℝ)).comp measurable_snd))
  exact Measurable.iSup hf

/-- The range defining the two-sample Kolmogorov–Smirnov statistic is bounded above by one. -/
theorem bddAbove_range_abs_finiteEmpiricalCDF_sub {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    BddAbove (range fun t : ℚ ↦ |finiteEmpiricalCDF x t - finiteEmpiricalCDF y t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1 := finiteEmpiricalCDF_mem_Icc x t
  have h2 := finiteEmpiricalCDF_mem_Icc y t
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Composing a sample in `(0, 1)` with the quantile function of `P` turns its empirical
distribution function into the original one evaluated along the CDF of `P`. -/
theorem finiteEmpiricalCDF_quantile_comp (P : Measure ℝ) {k : ℕ} (u : Fin k → ℝ)
    (hu : ∀ i, u i ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    finiteEmpiricalCDF (fun i ↦ P.quantile (u i)) t =
      finiteEmpiricalCDF u (ProbabilityTheory.cdf P t) := by
  unfold finiteEmpiricalCDF
  congr 1
  refine congrArg (fun s : Finset _ ↦ (s.card : ℝ)) (Finset.filter_congr fun i _ ↦ ?_)
  exact Measure.quantile_le_iff P (hu i).1 (hu i).2

/-- GAPS 103.17: finite-sample distribution-freeness of the two-sample KS statistic.
The reference law `U` is the uniform probability law on the unit interval. -/
theorem map_twoSampleKolmogorovSmirnovStatistic_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let U := TauCeti.Probability.uniformMeasure 0 1;
    ((Measure.pi fun _ : Fin m ↦ P).prod (Measure.pi fun _ : Fin n ↦ P)).map
      (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) =
      ((Measure.pi fun _ : Fin m ↦ U).prod (Measure.pi fun _ : Fin n ↦ U)).map
        (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) := by
  intro U
  set V : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hV
  have hVprob : IsProbabilityMeasure V := ⟨by simp [V]⟩
  have hUV : U = V := by
    simp only [U, V, TauCeti.Probability.uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one,
      inv_one, one_smul]
    exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  set Q := P.quantile with hQ
  have hQm : Measurable Q := Measure.measurable_quantile P
  have hmap : V.map Q = P := Measure.map_quantile_volume_Ioo P
  have hcont := Measure.continuous_cdf_of_noAtoms P
  -- edge values of the empirical distribution function of a sample in `(0, 1)`
  have hedge : ∀ {k : ℕ}, 0 < k → ∀ u : Fin k → ℝ, (∀ i, u i ∈ Ioo (0 : ℝ) 1) →
      ∀ q : ℝ, q ∉ Ioo (0 : ℝ) 1 → finiteEmpiricalCDF u q = if q ≤ 0 then 0 else 1 := by
    intro k hk u hu q hq
    unfold finiteEmpiricalCDF
    split_ifs with h0
    · rw [Finset.filter_false_of_mem fun i _ ↦ not_le.mpr ((h0.trans_lt (hu i).1))]
      simp
    · have h1 : 1 ≤ q := by
        by_contra h; exact hq ⟨not_le.mp h0, not_le.mp h⟩
      rw [Finset.filter_true_of_mem fun i _ ↦ ((hu i).2.le.trans h1)]
      simp [(Nat.cast_pos.mpr hk).ne']
  -- the pointwise identity
  have hpt : ∀ u : Fin m → ℝ, (∀ i, u i ∈ Ioo (0 : ℝ) 1) → ∀ w : Fin n → ℝ,
      (∀ j, w j ∈ Ioo (0 : ℝ) 1) →
      twoSampleKolmogorovSmirnovStatistic (fun i ↦ Q (u i)) (fun j ↦ Q (w j)) =
        twoSampleKolmogorovSmirnovStatistic u w := by
    intro u hu w hw
    unfold twoSampleKolmogorovSmirnovStatistic
    refine le_antisymm (csSup_le (range_nonempty _) ?_) (csSup_le (range_nonempty _) ?_)
    · rintro _ ⟨t, rfl⟩
      simp only [hQ, finiteEmpiricalCDF_quantile_comp P u hu, finiteEmpiricalCDF_quantile_comp P w hw]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_finiteEmpiricalCDF_eq u w (ProbabilityTheory.cdf P t)
      rw [← hq1, ← hq2]
      exact le_csSup (bddAbove_range_abs_finiteEmpiricalCDF_sub u w) (mem_range_self q)
    · rintro _ ⟨q, rfl⟩
      beta_reduce
      by_cases hq : (q : ℝ) ∈ Ioo (0 : ℝ) 1
      · have hFQ : ProbabilityTheory.cdf P (Q q) = q := Measure.cdf_quantile P hcont hq.1 hq.2
        obtain ⟨q', hq1, hq2⟩ := exists_rat_finiteEmpiricalCDF_eq (fun i ↦ Q (u i))
          (fun j ↦ Q (w j)) (Q q)
        have e1 := finiteEmpiricalCDF_quantile_comp P u hu (Q q)
        have e2 := finiteEmpiricalCDF_quantile_comp P w hw (Q q)
        rw [← hQ, hFQ] at e1 e2
        rw [← e1, ← e2, ← hq1, ← hq2]
        exact le_csSup (bddAbove_range_abs_finiteEmpiricalCDF_sub _ _) (mem_range_self q')
      · rw [hedge hm u hu _ hq, hedge hn w hw _ hq, sub_self, abs_zero]
        exact le_csSup_of_le (bddAbove_range_abs_finiteEmpiricalCDF_sub _ _) (mem_range_self 0)
          (abs_nonneg _)
  -- assemble
  have hQn : ∀ k : ℕ, Measurable fun (u : Fin k → ℝ) (i : Fin k) ↦ Q (u i) := fun k ↦
    measurable_pi_iff.mpr fun i ↦ hQm.comp (measurable_pi_apply i)
  have hpi : ∀ k : ℕ, (Measure.pi fun _ : Fin k ↦ P) =
      (Measure.pi fun _ : Fin k ↦ V).map fun u i ↦ Q (u i) := by
    intro k
    rw [Measure.pi_map_pi (fun _ ↦ hQm.aemeasurable)]
    simp only [hmap]
  have hae : ∀ k : ℕ, ∀ᵐ u ∂(Measure.pi fun _ : Fin k ↦ V), ∀ i, u i ∈ Ioo (0 : ℝ) 1 := by
    intro k
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin k ↦ V) i).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Ioo)
  have hae2 : ∀ᵐ z ∂((Measure.pi fun _ : Fin m ↦ V).prod (Measure.pi fun _ : Fin n ↦ V)),
      (∀ i, z.1 i ∈ Ioo (0 : ℝ) 1) ∧ ∀ j, z.2 j ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst.ae (hae m)).and
      (Measure.quasiMeasurePreserving_snd.ae (hae n))
  rw [hpi m, hpi n, Measure.map_prod_map _ _ (hQn m) (hQn n),
    Measure.map_map (measurable_twoSampleKolmogorovSmirnovStatistic m n)
      ((hQn m).prodMap (hQn n)), hUV]
  exact Measure.map_congr (hae2.mono fun z hz ↦ hpt z.1 hz.1 z.2 hz.2)

/-- A self-adjoint operator on a finite-dimensional real Euclidean space has a unit
eigenvector whose eigenvalue dominates the Rayleigh quotient. -/
theorem exists_unit_eigenvector_rayleigh_le {p : ℕ}
    (M : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (hM : IsSelfAdjoint M)
    (x : EuclideanSpace ℝ (Fin p)) (hx : ‖x‖ = 1) :
    ∃ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 ∧ ∃ b : ℝ, M w = b • w ∧
      ∀ u, inner ℝ u (M u) ≤ b * ‖u‖ ^ 2 := by
  have hcpt : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1) := isCompact_sphere _ _
  obtain ⟨w, hw, hmax⟩ := hcpt.exists_isMaxOn ⟨x, by simp [hx]⟩
    M.reApplyInnerSelf_continuous.continuousOn
  have hw1 : ‖w‖ = 1 := by simpa using hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hmax' : IsMaxOn M.reApplyInnerSelf (Metric.sphere 0 ‖w‖) w := by rw [hw1]; exact hmax
  have hev := hM.hasEigenvector_of_isMaxOn hw0 hmax'
  set lam := (⨆ x : { x : EuclideanSpace ℝ (Fin p) // x ≠ 0 }, M.rayleighQuotient x : ℝ)
  have hMw : M w = lam • w := Module.End.mem_eigenspace_iff.mp hev.1
  refine ⟨w, hw1, lam, hMw, fun u ↦ ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set u' := ‖u‖⁻¹ • u
  have hu' : u' ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1 := by
    simp [u', norm_smul, hun.ne']
  have h1 : M.reApplyInnerSelf u' ≤ M.reApplyInnerSelf w := hmax hu'
  simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real] at h1
  rw [hMw, inner_smul_left, real_inner_self_eq_norm_sq, hw1] at h1
  simp only [u', map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at h1
  rw [real_inner_comm] at h1
  have : inner ℝ u (M u) = ‖u‖ ^ 2 * (‖u‖⁻¹ * (‖u‖⁻¹ * inner ℝ u (M u))) := by
    field_simp
  rw [this]
  nlinarith [sq_nonneg ‖u‖]

/-- GAPS 103.54: residual perturbation bound, with the gap specified by a Rayleigh bound.
The probabilistic spiked-covariance bound is outside this deterministic statement. -/
theorem leading_eigenvector_residual_bound {p : ℕ}
    (A E : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hA : IsSelfAdjoint A) (hE : IsSelfAdjoint E)
    (v : EuclideanSpace ℝ (Fin p)) (hv : ‖v‖ = 1) (a gap : ℝ)
    (heig : A v = a • v)
    (hother : ∀ u, inner ℝ u v = 0 → inner ℝ u (A u) ≤ (a - gap) * ‖u‖ ^ 2)
    (hsmall : 2 * ‖E‖ < gap) :
    ∃ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v ∧
      (∃ b : ℝ, (A + E) w = b • w ∧
        (∀ u, inner ℝ u ((A + E) u) ≤ b * ‖u‖ ^ 2) ∧
        ∀ z, (A + E) z = b • z → z ∈ Submodule.span ℝ {w}) ∧
      ‖w - v‖ ≤ 2 * ‖E v - inner ℝ v (E v) • v‖ / (gap - 2 * ‖E‖) := by
  set M := A + E with hMdef
  have hM : IsSelfAdjoint M := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA hE ⊢
    rw [hMdef, ContinuousLinearMap.toLinearMap_add]; exact hA.add hE
  have hEle : ∀ u, |inner ℝ u (E u)| ≤ ‖E‖ * ‖u‖ ^ 2 := fun u ↦ by
    calc |inner ℝ u (E u)| ≤ ‖u‖ * ‖E u‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖E‖ * ‖u‖) := by gcongr; exact E.le_opNorm u
      _ = ‖E‖ * ‖u‖ ^ 2 := by ring
  have hMu : ∀ u, inner ℝ u (M u) = inner ℝ u (A u) + inner ℝ u (E u) := fun u ↦ by
    simp [hMdef, inner_add_right]
  obtain ⟨w₀, hw₀, b, hMw₀, hray⟩ := exists_unit_eigenvector_rayleigh_le M hM v hv
  obtain ⟨w, hw1, hwv, hMw⟩ : ∃ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v ∧
      M w = b • w := by
    by_cases h : 0 ≤ inner ℝ w₀ v
    · exact ⟨w₀, hw₀, h, hMw₀⟩
    · refine ⟨-w₀, by rw [norm_neg, hw₀], ?_, by rw [map_neg, hMw₀, smul_neg]⟩
      rw [inner_neg_left]; linarith
  -- eigenvalue lower bound and the Rayleigh bound off `v`
  have hblow : a - ‖E‖ ≤ b := by
    have h1 := hray v
    rw [hMu, heig, inner_smul_right, real_inner_self_eq_norm_sq, hv] at h1
    have := (abs_le.mp (hEle v)).1
    rw [hv] at this
    nlinarith
  have hperp : ∀ u, inner ℝ u v = 0 → inner ℝ u (M u) ≤ (a - gap + ‖E‖) * ‖u‖ ^ 2 := by
    intro u hu
    rw [hMu]
    have := (abs_le.mp (hEle u)).2
    have := hother u hu
    nlinarith
  have hdel : 0 < gap - 2 * ‖E‖ := by linarith
  -- an eigenvector for `b` orthogonal to `v` is zero
  have hzero : ∀ u, inner ℝ u v = 0 → M u = b • u → u = 0 := by
    intro u hu hMu'
    have h1 := hperp u hu
    rw [hMu', inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 : (gap - 2 * ‖E‖) * ‖u‖ ^ 2 ≤ 0 := by nlinarith
    have h3 : ‖u‖ ^ 2 ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
  refine ⟨w, hw1, hwv, ⟨b, hMw, hray, fun z hz ↦ ?_⟩, ?_⟩
  · -- simplicity of the top eigenvalue
    obtain ⟨z', hz'⟩ : ∃ z', z' = z - inner ℝ w z • w := ⟨_, rfl⟩
    have hz'w : inner ℝ w z' = 0 := by
      rw [hz', inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hw1]; ring
    have hMz' : M z' = b • z' := by
      rw [hz', map_sub, map_smul, hz, hMw, smul_sub, smul_comm]
    have hz'0 : z' = 0 := by
      by_cases hwv0 : inner ℝ w v = 0
      · -- then `w` itself would be orthogonal to `v`
        exact absurd (hzero w hwv0 hMw) (by rintro rfl; simp at hw1)
      · obtain ⟨u, hu⟩ : ∃ u, u = inner ℝ z' v • w - inner ℝ w v • z' := ⟨_, rfl⟩
        have huv : inner ℝ u v = 0 := by
          rw [hu, inner_sub_left, inner_smul_left, inner_smul_left]
          simp only [RCLike.conj_to_real]; ring
        have hMu' : M u = b • u := by
          rw [hu, map_sub, map_smul, map_smul, hMw, hMz', smul_sub, smul_comm b (inner ℝ z' v),
            smul_comm b (inner ℝ w v)]
        have hu0 := hzero u huv hMu'
        have := congrArg (fun t ↦ inner ℝ z' t) hu0
        simp only [hu, inner_sub_right, inner_smul_right, inner_zero_right] at this
        rw [real_inner_comm w z', hz'w, real_inner_self_eq_norm_sq] at this
        have h' : inner ℝ w v * ‖z'‖ ^ 2 = 0 := by linarith
        rcases mul_eq_zero.mp h' with h | h
        · exact absurd h hwv0
        · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    rw [Submodule.mem_span_singleton]
    exact ⟨inner ℝ w z, by rw [hz', sub_eq_zero] at hz'0; exact hz'0.symm⟩
  · -- the distance bound
    obtain ⟨c, hc⟩ : ∃ c, c = inner ℝ w v := ⟨_, rfl⟩
    have hc' : inner ℝ v w = c := by rw [real_inner_comm]; exact hc.symm
    rw [← hc] at hwv
    obtain ⟨r, hr⟩ : ∃ r, r = E v - inner ℝ v (E v) • v := ⟨_, rfl⟩
    rw [← hr]
    obtain ⟨u, hu⟩ : ∃ u, u = w - c • v := ⟨_, rfl⟩
    have hwu : w = u + c • v := by rw [hu]; abel
    have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have huv : inner ℝ u v = 0 := by
      rw [hu, inner_sub_left, inner_smul_left, hvv, ← hc]; simp
    have hvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
    have hc1 : c ≤ 1 := by
      have := real_inner_le_norm w v; rw [hw1, hv, ← hc] at this; linarith
    have hnu : ‖u‖ ^ 2 = 1 - c ^ 2 := by
      rw [hu, norm_sub_sq_real, inner_smul_right, norm_smul, hw1, hv, ← hc, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    have huw : inner ℝ u w = ‖u‖ ^ 2 := by
      rw [hwu, inner_add_right, inner_smul_right, huv, real_inner_self_eq_norm_sq]; ring
    have hMv : inner ℝ u (M v) = inner ℝ u r := by
      rw [hMdef, add_apply, inner_add_right, heig, inner_smul_right, huv, hr, inner_sub_right,
        inner_smul_right, huv]; ring
    have hMw' : inner ℝ u (M w) = inner ℝ u (M u) + c * inner ℝ u r := by
      rw [hwu, map_add, map_smul, inner_add_right, inner_smul_right, hMv]
    have hkey : b * ‖u‖ ^ 2 ≤ (a - gap + ‖E‖) * ‖u‖ ^ 2 + c * (‖u‖ * ‖r‖) := by
      have h1 : inner ℝ u (M w) = b * ‖u‖ ^ 2 := by rw [hMw, inner_smul_right, huw]
      have h2 := hperp u huv
      have h3 : inner ℝ u r ≤ ‖u‖ * ‖r‖ := real_inner_le_norm u r
      have h4 := mul_le_mul_of_nonneg_left h3 hwv
      linarith
    have hur : (gap - 2 * ‖E‖) * ‖u‖ ≤ ‖r‖ := by
      rcases (norm_nonneg u).eq_or_lt with h | h
      · rw [← h, mul_zero]; exact norm_nonneg _
      · have s1 : (gap - 2 * ‖E‖) * ‖u‖ ^ 2 ≤ (b - (a - gap + ‖E‖)) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        have s2 : c * (‖u‖ * ‖r‖) ≤ ‖u‖ * ‖r‖ :=
          mul_le_of_le_one_left (mul_nonneg h.le (norm_nonneg r)) hc1
        have s3 : ‖u‖ * ((gap - 2 * ‖E‖) * ‖u‖) ≤ ‖u‖ * ‖r‖ := by
          have : ‖u‖ * ((gap - 2 * ‖E‖) * ‖u‖) = (gap - 2 * ‖E‖) * ‖u‖ ^ 2 := by ring
          linarith
        exact le_of_mul_le_mul_left s3 h
    have hwv2 : ‖w - v‖ ^ 2 ≤ (2 * ‖u‖) ^ 2 := by
      rw [norm_sub_sq_real, hw1, hv, ← hc, mul_pow, hnu]
      nlinarith [mul_nonneg hwv (sub_nonneg.mpr hc1)]
    have hwv' : ‖w - v‖ ≤ 2 * ‖u‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hwv2
    rw [le_div_iff₀ hdel]
    calc ‖w - v‖ * (gap - 2 * ‖E‖) ≤ 2 * ‖u‖ * (gap - 2 * ‖E‖) :=
          mul_le_mul_of_nonneg_right hwv' hdel.le
      _ = 2 * ((gap - 2 * ‖E‖) * ‖u‖) := by ring
      _ ≤ 2 * ‖r‖ := by linarith

end CKSD
