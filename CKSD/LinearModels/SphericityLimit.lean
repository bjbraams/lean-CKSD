module

public import CKSD.LinearModels.BetaProductLimit
public import TauCeti.Probability.Distributions.ChiSquared.Basic
/-!
# Logarithmic limits from eventual Beta-product laws

A finite product with affine growing first Beta shapes has a logarithmic Gamma limit.
Lower truncation makes every auxiliary law a probability measure while preserving all
sufficiently large sample laws. The transfer uses Mathlib weak convergence and continuous
mapping and pinned TauCeti Gamma scaling; the finite Beta-product limit is local theory.
-/
@[expose] public section
noncomputable section
open Filter Set Real MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace CKSD

/-- Convergence in distribution transfers across eventually equal laws. -/
theorem tendsto_in_distribution_of_eventually_map_eq
    {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℕ → Measure Ω') [∀ n, IsProbabilityMeasure (Q n)]
    (R : Measure Ω'') [IsProbabilityMeasure R]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ω' → ℝ) (Z : Ω'' → ℝ)
    (hXm : ∀ n, AEMeasurable (X n) P)
    (hmap : ∀ᶠ n in atTop, P.map (X n) = (Q n).map (Y n))
    (hY : TendstoInDistribution Y atTop Z Q R) :
    TendstoInDistribution X atTop Z (fun _ ↦ P) R := by
  refine ⟨hXm, hY.aemeasurable_limit, ?_⟩
  apply hY.tendsto.congr'
  filter_upwards [hmap] with n hn
  exact Subtype.ext hn.symm

/-- A lower truncation of an affine growing Beta shape tends to infinity. -/
theorem tendsto_max_one_nat_cast_sub_div_two (c : ℝ) :
    Tendsto (fun n : ℕ ↦ max 1 (((n : ℝ) - c) / 2)) atTop atTop := by
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ) - c) / 2) atTop atTop :=
    by
      simpa only [sub_eq_add_neg] using
        ((tendsto_atTop_add_const_right atTop (-c) tendsto_natCast_atTop_atTop)).atTop_div_const (by norm_num : (0:ℝ)<2)
  exact tendsto_atTop_mono (fun n ↦ le_max_right _ _) h

/-- Two affine shape sequences with the same leading scale have asymptotic ratio one. -/
theorem tendsto_max_one_nat_cast_div_two_ratio (c : ℝ) :
    Tendsto (fun n : ℕ ↦ max 1 ((n : ℝ) / 2) / max 1 (((n : ℝ) - c) / 2))
      atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) - c) atTop atTop :=
    by simpa only [sub_eq_add_neg] using (tendsto_atTop_add_const_right atTop (-c) tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ ↦ 1 + c / ((n : ℝ) - c)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add ((tendsto_const_nhds (x := c)).div_atTop hn)
  apply hlim.congr'
  have hlarge : ∀ᶠ n : ℕ in atTop, max 2 (c + 2) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlarge] with n hn'
  have hn2 : 2 ≤ (n : ℝ) := (le_max_left _ _).trans hn'
  have hnc : c + 2 ≤ (n : ℝ) := (le_max_right _ _).trans hn'
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ (n : ℝ) / 2),
    max_eq_right (by linarith : (1 : ℝ) ≤ ((n : ℝ) - c) / 2)]
  field_simp [(show (n : ℝ) - c ≠ 0 by linarith)]
  ring

/-- A statistic with the growing-shape Beta-product law has the corresponding logarithmic
Gamma limit; only eventual equality of laws is needed. -/
theorem tendsto_in_distribution_neg_nat_cast_mul_log_of_beta_product_law
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (Z : ℕ → Ω → ℝ) (hZm : ∀ n, Measurable (Z n))
    (hmap : ∀ᶠ n in atTop, P.map (Z n) =
      (Measure.pi fun i ↦ betaMeasure (max 1 (((n : ℝ) - c i) / 2)) (b i)).map
        (fun x : ι → ℝ ↦ ∏ i, x i)) :
    let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) (1 / 2)) :=
      isProbabilityMeasure_gammaMeasure (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty) (by norm_num);
    TendstoInDistribution (fun (n : ℕ) ω ↦ -(n : ℝ) * Real.log (Z n ω)) atTop id
      (fun _ ↦ P) (gammaMeasure (∑ i, b i) (1 / 2)) := by
  let a : ι → ℕ → ℝ := fun i n ↦ max 1 (((n : ℝ) - c i) / 2)
  let t : ℕ → ℝ := fun n ↦ max 1 ((n : ℝ) / 2)
  have ha (i : ι) (n : ℕ) : 0 < a i n := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ht (n : ℕ) : 0 < t n := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbS : 0 < ∑ i, b i := Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty
  let Q : ℕ → Measure (ι → ℝ) := fun n ↦ Measure.pi fun i ↦ betaMeasure (a i n) (b i)
  let : ∀ n, IsProbabilityMeasure (Q n) := fun n ↦ is_probability_measure_pi_beta _ _ (fun i ↦ ha i n) hb
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) 1) := isProbabilityMeasure_gammaMeasure hbS zero_lt_one
  let : IsProbabilityMeasure (gammaMeasure (∑ i, b i) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hbS (by norm_num)
  have hbeta := tendsto_in_distribution_neg_mul_log_beta_product a b t ha hb ht
    (fun i ↦ tendsto_max_one_nat_cast_sub_div_two (c i))
    (fun i ↦ tendsto_max_one_nat_cast_div_two_ratio (c i))
  have hdouble := hbeta.continuous_comp (g := fun x : ℝ ↦ 2 * x) (by fun_prop)
  have hdouble' : TendstoInDistribution (fun (n : ℕ) (x : ι → ℝ) ↦ 2 * (-(t n) * Real.log (∏ i, x i)))
      atTop id Q (gammaMeasure (∑ i, b i) (1 / 2)) := by
    refine ⟨fun _ ↦ by fun_prop, measurable_id.aemeasurable, ?_⟩
    have hscale := TauCeti.Probability.gammaMeasure_map_const_mul hbS zero_lt_one
      (c := 2) (by norm_num)
    have hlimit : (gammaMeasure (∑ i, b i) 1).map ((fun x : ℝ ↦ 2 * x) ∘ id) =
        (gammaMeasure (∑ i, b i) (1 / 2)).map id := by
      simpa only [Function.comp_id, Measure.map_id] using hscale
    have hd := hdouble.tendsto
    have hlimitP : (⟨(gammaMeasure (∑ i, b i) 1).map ((fun x : ℝ ↦ 2 * x) ∘ id), inferInstance⟩ : ProbabilityMeasure ℝ) =
        ⟨(gammaMeasure (∑ i, b i) (1 / 2)).map id, inferInstance⟩ := Subtype.ext hlimit
    rw [hlimitP] at hd
    exact hd
  apply tendsto_in_distribution_of_eventually_map_eq P Q _
    (fun (n : ℕ) ω ↦ -(n : ℝ) * Real.log (Z n ω)) _ id (fun n ↦ (by fun_prop : Measurable _).aemeasurable) _ hdouble'
  have hlarge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ n :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hmap, hlarge] with n hn hn2
  have hg : Measurable (fun x : ι → ℝ ↦ ∏ i, x i) := by fun_prop
  have hl : Measurable (fun x : ℝ ↦ -(n : ℝ) * Real.log x) := by fun_prop
  have h := congrArg (Measure.map (fun x : ℝ ↦ -(n : ℝ) * Real.log x)) hn
  rw [Measure.map_map hl (hZm n), Measure.map_map hl hg] at h
  have hfun : (fun x : ι → ℝ ↦ 2 * (-(t n) * Real.log (∏ i, x i))) =
      (fun x : ι → ℝ ↦ -(n : ℝ) * Real.log (∏ i, x i)) := by
    funext x
    dsimp [t]
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ (n : ℝ) / 2)]
    ring
  rw [hfun]
  exact h
/-- The sum of the spherical Beta second shapes equals half the dimension deficit. -/
theorem sum_sphericity_beta_second_shape {p : ℕ} (hp : 2 ≤ p) :
    (∑ i : Fin (p - 1), (((i.val : ℝ) + 1) / 2 + ((i.val : ℝ) + 1) / p)) =
      ((p * (p + 1) / 2 - 1 : ℕ) : ℝ) / 2 := by
  have hsum (q : ℕ) : (∑ i : Fin q, ((i.val : ℝ) + 1)) = (q : ℝ) * (q + 1) / 2 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring
  have hp0 : p ≠ 0 := by omega
  have hnat : 2 * (p * (p + 1) / 2) = p * (p + 1) := Nat.mul_div_cancel' p.two_dvd_mul_add_one
  have hdim : (1 : ℕ) ≤ p * (p + 1) / 2 := by nlinarith
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hsum]
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one, Nat.cast_sub hdim, Nat.cast_one]
  have hnatR : 2 * ((p * (p + 1) / 2 : ℕ) : ℝ) = (p : ℝ) * (p + 1) := by exact_mod_cast hnat
  field_simp [hp0]
  nlinarith

end CKSD
