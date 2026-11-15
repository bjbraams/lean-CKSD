module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Quantile

/-!
# Distribution-free goodness-of-fit statistics

For a continuous distribution `P` on the line, the laws of the Cramér–von Mises statistic and
of the two-sample Kolmogorov–Smirnov statistic under `P` coincide with their laws under the
uniform distribution on `[0, 1]`. The proofs transport samples by inverse transform sampling,
`u ↦ P.quantile u`, under which the empirical distribution function becomes `F_n ∘ F`.

## Main definitions

* `CKSD.finiteEmpiricalCDF x`: the empirical distribution function of a finite sample.
* `CKSD.cramerVonMisesStatistic P x`: `n ∫ (F_n - F)² dF`.
* `CKSD.twoSampleKolmogorovSmirnovStatistic x y`: `sup_t |F_m(t) - G_n(t)|`.

## Main results

* `CKSD.map_cramerVonMisesStatistic_eq_uniform`,
  `CKSD.map_twoSampleKolmogorovSmirnovStatistic_eq_uniform`: finite-sample distribution-freeness.

The Cramér–von Mises and Kolmogorov–Smirnov arguments use TauCeti's inverse transform sampling
(`MeasureTheory.Measure.map_quantile_volume_Ioo`), the quantile–CDF relations
`MeasureTheory.Measure.quantile_le_iff` and `MeasureTheory.Measure.cdf_quantile`, CDF continuity
`MeasureTheory.Measure.continuous_cdf_of_noAtoms`, and the uniform law
`TauCeti.Probability.uniformMeasure` with `TauCeti.Probability.cdf_uniformMeasure`.

Source: GAPS 103.17 (the finite-sample part described in `GAPS_EASY.md`).

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 19.
-/

public section

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

/-- The finite empirical distribution function at a fixed point is measurable in the sample. -/
theorem measurable_finiteEmpiricalCDF {k : ℕ} (t : ℝ) :
    Measurable fun x : Fin k → ℝ ↦ finiteEmpiricalCDF x t :=
  (measurable_finiteEmpiricalCDF_uncurry k).comp
    (f := fun x : Fin k → ℝ ↦ (x, t)) (measurable_id.prodMk measurable_const)

/-- The uniform law on `[0, 1]` is Lebesgue measure restricted to `(0, 1)`. -/
theorem uniformMeasure_zero_one_eq_restrict_Ioo :
    TauCeti.Probability.uniformMeasure 0 1 = volume.restrict (Ioo (0 : ℝ) 1) := by
  simp only [TauCeti.Probability.uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one,
    inv_one, one_smul]
  exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm

/-- Coordinatewise application of the quantile function is measurable. -/
theorem measurable_pi_quantile (P : Measure ℝ) (k : ℕ) :
    Measurable fun (u : Fin k → ℝ) (i : Fin k) ↦ P.quantile (u i) :=
  measurable_pi_iff.mpr fun i ↦ (Measure.measurable_quantile P).comp (measurable_pi_apply i)

/-- Inverse transform sampling for samples: `P^k` is the image of the uniform law on `(0, 1)^k`
under coordinatewise application of the quantile function of `P`. -/
theorem pi_eq_map_pi_quantile (P : Measure ℝ) [IsProbabilityMeasure P] (k : ℕ) :
    (Measure.pi fun _ : Fin k ↦ P) =
      (Measure.pi fun _ : Fin k ↦ volume.restrict (Ioo (0 : ℝ) 1)).map
        fun u i ↦ P.quantile (u i) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  rw [Measure.pi_map_pi (fun _ ↦ (Measure.measurable_quantile P).aemeasurable)]
  simp only [Measure.map_quantile_volume_Ioo P]

/-- Almost every sample from the uniform law on `(0, 1)` has all its values in `(0, 1)`. -/
theorem ae_forall_mem_Ioo_pi_restrict (k : ℕ) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin k ↦ volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ i, u i ∈ Ioo (0 : ℝ) 1 := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin k ↦ volume.restrict (Ioo (0 : ℝ) 1)) i)
    |>.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Ioo)

/-- The Cramér–von Mises statistic is a measurable function of the sample. -/
theorem measurable_cramerVonMisesStatistic (P : Measure ℝ) [IsFiniteMeasure P] (n : ℕ) :
    Measurable (cramerVonMisesStatistic (n := n) P) := by
  unfold cramerVonMisesStatistic
  refine measurable_const.mul ?_
  have h : Measurable fun z : (Fin n → ℝ) × ℝ ↦ (finiteEmpiricalCDF z.1 z.2 - cdf P z.2) ^ 2 :=
    ((measurable_finiteEmpiricalCDF_uncurry n).sub
      ((cdf P).mono.measurable.comp measurable_snd)).pow_const 2
  exact (h.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- GAPS 103.17: finite-sample distribution-freeness of the Cramér–von Mises statistic. For a
probability measure `P` without atoms, the law of `n ∫ (F_n - F)² dF` under `P^n` equals its law
under the uniform distribution on `[0, 1]`. -/
theorem map_cramerVonMisesStatistic_eq_uniform (P : Measure ℝ) [IsProbabilityMeasure P]
    [NullSingletonClass P] (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ P).map (cramerVonMisesStatistic P) =
      (Measure.pi fun _ : Fin n ↦ TauCeti.Probability.uniformMeasure 0 1).map
        (cramerVonMisesStatistic (TauCeti.Probability.uniformMeasure 0 1)) := by
  set U := TauCeti.Probability.uniformMeasure 0 1 with hU
  set V : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hV
  have hVprob : IsProbabilityMeasure V := ⟨by simp [V]⟩
  have hUV : U = V := uniformMeasure_zero_one_eq_restrict_Ioo
  have hcdfV : ∀ s ∈ Ioo (0 : ℝ) 1, cdf V s = s := by
    intro s hs
    rw [← hUV, TauCeti.Probability.cdf_uniformMeasure zero_lt_one,
      ite_eq_right (not_le.mpr hs.1), ite_eq_right (not_le.mpr hs.2)]
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
        (cdf P).mono.measurable).pow_const 2
    calc ∫ t, (finiteEmpiricalCDF (fun i ↦ Q (u i)) t - cdf P t) ^ 2 ∂P
        = ∫ t, (finiteEmpiricalCDF (fun i ↦ Q (u i)) t - cdf P t) ^ 2 ∂(V.map Q) := by
          rw [hmap]
      _ = ∫ s, (finiteEmpiricalCDF (fun i ↦ Q (u i)) (Q s) - cdf P (Q s)) ^ 2 ∂V :=
          integral_map hQm.aemeasurable hg.aestronglyMeasurable
      _ = ∫ s, (finiteEmpiricalCDF u s - cdf V s) ^ 2 ∂V := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          have hFQ : cdf P (Q s) = s := Measure.cdf_quantile P hcont hs.1 hs.2
          rw [hFQ, hcdfV s hs]
          congr 2
          unfold finiteEmpiricalCDF
          congr 2
          refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
          rw [hQ, Measure.quantile_le_iff P (hu i).1 (hu i).2, ← hQ, hFQ]
  -- assemble
  rw [pi_eq_map_pi_quantile P n, Measure.map_map (measurable_cramerVonMisesStatistic P n)
    (measurable_pi_quantile P n), hUV]
  exact Measure.map_congr ((ae_forall_mem_Ioo_pi_restrict n).mono fun u hu ↦ hpt u hu)

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

/-- GAPS 103.17: finite-sample distribution-freeness of the two-sample Kolmogorov–Smirnov
statistic. For a probability measure `P` without atoms and nonempty samples, the law of
`sup_t |F_m(t) - G_n(t)|` under `P^m ⊗ P^n` equals its law under the uniform distribution on
`[0, 1]`. -/
theorem map_twoSampleKolmogorovSmirnovStatistic_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P] [NullSingletonClass P]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ((Measure.pi fun _ : Fin m ↦ P).prod (Measure.pi fun _ : Fin n ↦ P)).map
      (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) =
      ((Measure.pi fun _ : Fin m ↦ TauCeti.Probability.uniformMeasure 0 1).prod
        (Measure.pi fun _ : Fin n ↦ TauCeti.Probability.uniformMeasure 0 1)).map
        (fun z ↦ twoSampleKolmogorovSmirnovStatistic z.1 z.2) := by
  set V : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hV
  have hVprob : IsProbabilityMeasure V := ⟨by simp [V]⟩
  set Q := P.quantile with hQ
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
      simp only [hQ, finiteEmpiricalCDF_quantile_comp P u hu,
        finiteEmpiricalCDF_quantile_comp P w hw]
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
  have hae2 : ∀ᵐ z ∂((Measure.pi fun _ : Fin m ↦ V).prod (Measure.pi fun _ : Fin n ↦ V)),
      (∀ i, z.1 i ∈ Ioo (0 : ℝ) 1) ∧ ∀ j, z.2 j ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_forall_mem_Ioo_pi_restrict m)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_forall_mem_Ioo_pi_restrict n))
  rw [pi_eq_map_pi_quantile P m, pi_eq_map_pi_quantile P n,
    Measure.map_prod_map _ _ (measurable_pi_quantile P m) (measurable_pi_quantile P n),
    Measure.map_map (measurable_twoSampleKolmogorovSmirnovStatistic m n)
      ((measurable_pi_quantile P m).prodMap (measurable_pi_quantile P n)),
    uniformMeasure_zero_one_eq_restrict_Ioo]
  exact Measure.map_congr (hae2.mono fun z hz ↦ hpt z.1 hz.1 z.2 hz.2)

end CKSD
