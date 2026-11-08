module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import TauCeti.Probability.McDiarmid

/-!
# Empirical risk concentration and Rademacher bounds

Uniform concentration of empirical means over a finite class, symmetrization, and the
high-probability Rademacher complexity bound. The concentration steps use Mathlib's
sub-Gaussian bounds (Hoeffding) and TauCeti's bounded-differences inequality (McDiarmid).

## Main results

* `CKSD.measure_uniform_empirical_risk_deviation_le`: uniform concentration over a finite class
  (GAPS 107.1).
* `CKSD.integral_sSup_sub_le_two_mul_rademacher`: symmetrization, the expected uniform
  deviation is at most twice the expected Rademacher complexity (GAPS 107.2).
* `CKSD.measureReal_integral_add_le_sSup_le`: McDiarmid tail for the uniform deviation.
* `CKSD.measureReal_two_mul_rademacher_add_lt_sSup_le`: the high-probability Rademacher bound
  (GAPS 107.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 107.1, finite-class uniform risk concentration (a scoped PAC upper bound): for a
finite class of `[0,1]`-valued functions and an i.i.d. sample of size `n`, the probability that
some empirical mean deviates from its expectation by more than `ε` is at most
`2 |H| exp(-2 n ε²)`. (For `n = 0` the bound is at least `2 |H|`, and trivial.) -/
theorem measure_uniform_empirical_risk_deviation_le
    {H X : Type*} [Fintype H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    (Measure.pi fun _ : Fin n ↦ P).real {x | ∃ h,
      |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} ≤
      2 * Fintype.card H * Real.exp (-2 * n * epsilon ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases isEmpty_or_nonempty H with hH | hH
    · simp
    · have h1 : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos
      calc _ ≤ (1 : ℝ) := measureReal_le_one
        _ ≤ _ := by simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero]; linarith
  let Q : Measure (Fin n → X) := Measure.pi (fun _ ↦ P)
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have htail (h : H) :
      Q.real {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} ≤
        2 * Real.exp (-2 * n * epsilon ^ 2) := by
    let m := ∫ z, f h z ∂P
    let Z : Fin n → (Fin n → X) → ℝ := fun i x ↦ f h (x i) - m
    have hbase : HasSubgaussianMGF (fun z ↦ f h z - m) (1 / 4) P := by
      have hs := hasSubgaussianMGF_of_mem_Icc (μ := P) (hm h).aemeasurable
        (Filter.Eventually.of_forall (hb h))
      norm_num at hs
      exact hs
    have hZ : ∀ i, HasSubgaussianMGF (Z i) (1 / 4) Q := by
      intro i
      have hp := measurePreserving_eval (fun _ : Fin n ↦ P) i
      exact HasSubgaussianMGF.of_map (X := fun z ↦ f h z - m)
        (Y := fun x : Fin n → X ↦ x i) hp.measurable.aemeasurable (hp.map_eq.symm ▸ hbase)
    have hindep : iIndepFun Z Q :=
      iIndepFun_pi (fun _ : Fin n ↦ ((hm h).sub_const m).aemeasurable)
    have hsum : HasSubgaussianMGF (fun x ↦ ∑ i, Z i x)
        (∑ _ : Fin n, (1 / 4 : ℝ≥0)) Q :=
      HasSubgaussianMGF.sum_of_iIndepFun hindep (fun i _ ↦ hZ i)
    have hden : (↑(∑ _ : Fin n, (1 / 4 : ℝ≥0)) : ℝ) = (n : ℝ) / 4 := by
      norm_num [Finset.sum_const, nsmul_eq_mul]
      ring
    have hexp : -((n : ℝ) * epsilon) ^ 2 / (2 * ((n : ℝ) / 4)) =
        -2 * n * epsilon ^ 2 := by
      field_simp [ne_of_gt hnreal]
      ring
    have hup := hsum.measure_ge_le (mul_nonneg hnreal.le he.le)
    have hlow := hsum.neg.measure_ge_le (mul_nonneg hnreal.le he.le)
    rw [hden, hexp] at hup hlow
    simp only [Pi.neg_apply] at hlow
    have hsum_eq (x : Fin n → X) :
        (∑ i, Z i x) = (∑ i, f h (x i)) - (n : ℝ) * m := by
      simp only [Z, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsub : {x | epsilon < |(∑ i, f h (x i)) / n - m|} ⊆
        {x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} ∪
          {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)} := by
      intro x hx
      change epsilon < |(∑ i, f h (x i)) / n - m| at hx
      change (n : ℝ) * epsilon ≤ ∑ i, Z i x ∨ (n : ℝ) * epsilon ≤ -(∑ i, Z i x)
      have hid : (∑ i, f h (x i)) / n - m = (∑ i, Z i x) / n := by
        rw [hsum_eq]
        field_simp [ne_of_gt hnreal]
      rw [hid, abs_div, abs_of_pos hnreal] at hx
      have ha : (n : ℝ) * epsilon < |∑ i, Z i x| := by
        nlinarith [(lt_div_iff₀ hnreal).mp hx]
      by_cases hz : 0 ≤ ∑ i, Z i x
      · left
        rw [abs_of_nonneg hz] at ha
        exact ha.le
      · right
        rw [abs_of_neg (lt_of_not_ge hz)] at ha
        exact ha.le
    calc
      _ ≤ Q.real ({x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} ∪
          {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)}) := measureReal_mono hsub
      _ ≤ Q.real {x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} +
          Q.real {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)} := measureReal_union_le _ _
      _ ≤ _ := by linarith
  change Q.real _ ≤ _
  rw [show {x : Fin n → X | ∃ h, |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} =
    ⋃ h, {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} by ext x; simp]
  calc
    _ ≤ ∑ h, Q.real {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : H, 2 * Real.exp (-2 * n * epsilon ^ 2) :=
      Finset.sum_le_sum (fun h _ ↦ htail h)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Suprema over a finite nonempty index of pointwise `c`-close families are `c`-close. -/
theorem abs_sSup_range_sub_sSup_range_le {H : Type*} [Finite H] [Nonempty H] {u v : H → ℝ}
    {c : ℝ} (h : ∀ k, |u k - v k| ≤ c) : |sSup (range u) - sSup (range v)| ≤ c := by
  have hu : BddAbove (range u) := (finite_range u).bddAbove
  have hv : BddAbove (range v) := (finite_range v).bddAbove
  rw [abs_le]
  constructor
  · have : sSup (range v) ≤ sSup (range u) + c := csSup_le (range_nonempty v) <| by
      rintro _ ⟨k, rfl⟩
      linarith [(abs_le.mp (h k)).1, le_csSup hu ⟨k, rfl⟩]
    linarith
  · have : sSup (range u) ≤ sSup (range v) + c := csSup_le (range_nonempty u) <| by
      rintro _ ⟨k, rfl⟩
      linarith [(abs_le.mp (h k)).2, le_csSup hv ⟨k, rfl⟩]
    linarith

/-- The supremum over a finite nonempty index of a sum is at most the sum of the suprema. -/
theorem sSup_range_add_le {H : Type*} [Finite H] [Nonempty H] (u v : H → ℝ) :
    sSup (range fun k ↦ u k + v k) ≤ sSup (range u) + sSup (range v) :=
  csSup_le (range_nonempty _) <| by
    rintro _ ⟨k, rfl⟩
    exact add_le_add (le_csSup (finite_range u).bddAbove ⟨k, rfl⟩)
      (le_csSup (finite_range v).bddAbove ⟨k, rfl⟩)

/-- The empirical Rademacher complexity is unchanged when the class is negated. -/
theorem empiricalRademacherComplexity_neg {H X : Type*} (n : ℕ) (f : H → X → ℝ)
    (x : Fin n → X) :
    empiricalRademacherComplexity n (fun h z ↦ -f h z) x = empiricalRademacherComplexity n f x := by
  rw [empiricalRademacherComplexity_eq, empiricalRademacherComplexity_eq]
  congr 1
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    Function.Involutive.toPerm (fun σ i ↦ !σ i) fun σ ↦ by funext i; simp
  have he : ∀ τ : Fin n → Bool, ∀ j, e τ j = !τ j := fun _ _ ↦ rfl
  refine Fintype.sum_equiv e _ _ fun σ ↦ ?_
  congr 2
  funext h
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [he]
  cases σ i <;> simp

/-- Measure preservation of the coordinatewise swap of a ghost sample: for a sign pattern `σ`,
coordinates with `σ i = false` are exchanged between the two samples. -/
theorem measurePreserving_ghostSwap {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (σ : Fin n → Bool) :
    MeasurePreserving (fun p : (Fin n → X) × (Fin n → X) ↦
        ((fun i ↦ if σ i then p.1 i else p.2 i), (fun i ↦ if σ i then p.2 i else p.1 i)))
      ((Measure.pi fun _ : Fin n ↦ P).prod (Measure.pi fun _ : Fin n ↦ P))
      ((Measure.pi fun _ : Fin n ↦ P).prod (Measure.pi fun _ : Fin n ↦ P)) := by
  set E := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n)
  have hE := measurePreserving_arrowProdEquivProdArrow X X (Fin n) (fun _ ↦ P) (fun _ ↦ P)
  have hS : MeasurePreserving (fun (y : Fin n → X × X) i ↦ if σ i then y i else (y i).swap)
      (Measure.pi fun _ ↦ P.prod P) (Measure.pi fun _ ↦ P.prod P) := by
    refine measurePreserving_pi (ι := Fin n) (fun _ ↦ P.prod P) (fun _ ↦ P.prod P)
      (f := fun i (q : X × X) ↦ if σ i then q else q.swap) fun i ↦ ?_
    by_cases hσ : σ i = true
    · simp only [hσ, ite_true]
      exact MeasurePreserving.id _
    · simp only [hσ]
      exact Measure.measurePreserving_swap
  have hcomp := (hE.comp hS).comp hE.symm
  convert hcomp using 1
  funext p
  simp only [Function.comp_apply, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, MeasurableEquiv.symm_mk, Equiv.arrowProdEquivProdArrow]
  ext i <;> by_cases hσ : σ i = true <;> simp [hσ]

/-- A supremum over a finite nonempty index of values bounded by `C` is bounded by `C`. -/
theorem abs_sSup_range_le {H : Type*} [Finite H] [Nonempty H] {u : H → ℝ} {C : ℝ}
    (h : ∀ k, |u k| ≤ C) : |sSup (range u)| ≤ C := by
  have := abs_sSup_range_sub_sSup_range_le (v := fun _ : H ↦ (0 : ℝ)) (c := C)
    fun k ↦ by simpa using h k
  rwa [range_const, csSup_singleton, sub_zero] at this

/-- A measurable function bounded in absolute value is integrable for a finite measure. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs]; exact hb x)

/-- An average `(∑ᵢ aᵢ uᵢ)/n` with `|aᵢ| ≤ 1` and `|uᵢ| ≤ C`, `C ≥ 0`, lies in `[-C,C]`. -/
theorem abs_sum_mul_div_le {n : ℕ} (a u : Fin n → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ 1) (hu : ∀ i, |u i| ≤ C) : |(∑ i, a i * u i) / n| ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hC
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hnr, div_le_iff₀ hnr]
  calc |∑ i, a i * u i| ≤ ∑ i, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ ↦ by
        rw [abs_mul]
        calc |a i| * |u i| ≤ 1 * C := mul_le_mul (ha i) (hu i) (abs_nonneg _) zero_le_one
          _ = C := one_mul C
    _ = C * n := by simp [mul_comm]

/-- Measurability of the empirical Rademacher complexity of a measurable finite class. -/
theorem measurable_empiricalRademacherComplexity {H X : Type*} [Fintype H] [MeasurableSpace X]
    (n : ℕ) (f : H → X → ℝ) (hm : ∀ h, Measurable (f h)) :
    Measurable fun x : Fin n → X ↦ empiricalRademacherComplexity n f x := by
  simp only [empiricalRademacherComplexity_eq]
  refine Measurable.const_mul (Finset.measurable_sum _ fun σ _ ↦ ?_) _
  exact Measurable.iSup fun h ↦ (Finset.measurable_sum _ fun i _ ↦
    ((hm h).comp (measurable_pi_apply i)).const_mul _).div_const _

/-- The empirical Rademacher complexity of a nonempty finite class bounded by `C` is bounded
by `C`. -/
theorem abs_empiricalRademacherComplexity_le {H X : Type*} [Fintype H] [Nonempty H] (n : ℕ)
    (f : H → X → ℝ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ h x, |f h x| ≤ C) (x : Fin n → X) :
    |empiricalRademacherComplexity n f x| ≤ C := by
  rw [empiricalRademacherComplexity_eq]
  have hsig : ∀ σ : Fin n → Bool, ∀ i, |(if σ i then (1 : ℝ) else -1)| ≤ 1 := fun σ i ↦ by
    split_ifs <;> simp
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc (2 : ℝ)⁻¹ ^ n * |∑ σ : Fin n → Bool, sSup (range fun h ↦
        (∑ i, (if σ i then (1 : ℝ) else -1) * f h (x i)) / n)|
      ≤ (2 : ℝ)⁻¹ ^ n * ∑ _σ : Fin n → Bool, C := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
        exact abs_sSup_range_le fun h ↦
          abs_sum_mul_div_le _ _ hC (hsig σ) fun i ↦ hb h (x i)
    _ = C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_pow, one_mul]

/-- GAPS 107.2, symmetrization: the expected supremum of the centered empirical means of a
finite class with values in `[-1,1]` is at most twice the expected empirical Rademacher
complexity. -/
theorem integral_sSup_sub_le_two_mul_rademacher {H X : Type*} [Fintype H] [Nonempty H]
    [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, |f h x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    ∫ x, sSup (range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      2 * ∫ x, empiricalRademacherComplexity n f x ∂(Measure.pi fun _ : Fin n ↦ P) := by
  set Pn := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set g : H → (Fin n → X) → ℝ := fun h x ↦ (∑ i, f h (x i)) / n with hg_def
  have hgm : ∀ h, Measurable (g h) := fun h ↦
    (Finset.measurable_sum _ fun i _ ↦ (hm h).comp (measurable_pi_apply i)).div_const _
  have hgb : ∀ h x, |g h x| ≤ 1 := fun h x ↦ by
    have := abs_sum_mul_div_le (fun _ ↦ (1 : ℝ)) (fun i ↦ f h (x i)) zero_le_one
      (fun _ ↦ by simp) fun i ↦ hb h (x i)
    simpa using this
  have hmean : ∀ h, ∫ x, g h x ∂Pn = ∫ z, f h z ∂P := by
    intro h
    have hi : ∀ i, ∫ x, f h (x i) ∂Pn = ∫ z, f h z ∂P := by
      intro i
      have hp := measurePreserving_eval (fun _ : Fin n ↦ P) i
      have heq := (integral_map hp.measurable.aemeasurable
        (by rw [hp.map_eq]; exact (hm h).aestronglyMeasurable)).symm
      rw [hp.map_eq] at heq
      exact heq
    have hint : ∀ i, Integrable (fun x : Fin n → X ↦ f h (x i)) Pn := fun i ↦
      integrable_of_abs_le _ ((hm h).comp (measurable_pi_apply i)) fun x ↦ hb h (x i)
    simp only [g]
    rw [integral_div, integral_finsetSum _ fun i _ ↦ hint i]
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the ghost-sample supremum
  set G : (Fin n → X) × (Fin n → X) → ℝ := fun p ↦ sSup (range fun h ↦ g h p.1 - g h p.2)
    with hG_def
  have hGm : Measurable G := Measurable.iSup fun h ↦
    ((hgm h).comp measurable_fst).sub ((hgm h).comp measurable_snd)
  have hGb : ∀ p, |G p| ≤ 2 := fun p ↦ abs_sSup_range_le fun h ↦ by
    calc |g h p.1 - g h p.2| ≤ |g h p.1| + |g h p.2| := abs_sub _ _
      _ ≤ 2 := by linarith [hgb h p.1, hgb h p.2]
  have hGi : Integrable G (Pn.prod Pn) := integrable_of_abs_le _ hGm hGb
  -- step 1: replace the mean by the ghost sample
  have hstep1 : ∀ x, sSup (range fun h ↦ g h x - ∫ z, f h z ∂P) ≤ ∫ x', G (x, x') ∂Pn := by
    intro x
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    have hgi : Integrable (g h) Pn := integrable_of_abs_le _ (hgm h) (hgb h)
    have : g h x - ∫ z, f h z ∂P = ∫ x', (g h x - g h x') ∂Pn := by
      rw [integral_sub (integrable_const _) hgi, integral_const, probReal_univ, one_smul, hmean]
    change g h x - ∫ z, f h z ∂P ≤ _
    rw [this]
    refine integral_mono ((integrable_const _).sub hgi)
      (integrable_of_abs_le _ (hGm.comp measurable_prodMk_left) fun x' ↦ hGb _) fun x' ↦ ?_
    exact le_csSup (finite_range _).bddAbove ⟨h, rfl⟩
  have hlhs : ∫ x, sSup (range fun h ↦ g h x - ∫ z, f h z ∂P) ∂Pn ≤ ∫ p, G p ∂(Pn.prod Pn) := by
    rw [integral_prod _ hGi]
    refine integral_mono (integrable_of_abs_le _ (C := 2) (Measurable.iSup fun h ↦
      (hgm h).sub measurable_const) fun x ↦ abs_sSup_range_le fun h ↦ ?_)
      (hGi.integral_prod_left) hstep1
    have hI : |∫ z, f h z ∂P| ≤ 1 := by
      have := norm_integral_le_of_norm_le_const (μ := P) (C := 1)
        (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hb h z)
      simpa [Real.norm_eq_abs] using this
    calc |g h x - ∫ z, f h z ∂P| ≤ |g h x| + |∫ z, f h z ∂P| := abs_sub _ _
      _ ≤ 2 := by linarith [hgb h x]
  -- step 2: average over sign patterns
  set T : (Fin n → Bool) → (Fin n → X) × (Fin n → X) → (Fin n → X) × (Fin n → X) :=
    fun σ p ↦ ((fun i ↦ if σ i then p.1 i else p.2 i), (fun i ↦ if σ i then p.2 i else p.1 i))
  have hT : ∀ σ, ∫ p, G p ∂(Pn.prod Pn) = ∫ p, G (T σ p) ∂(Pn.prod Pn) := by
    intro σ
    have hmp := measurePreserving_ghostSwap P n σ
    rw [← integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hGm.aestronglyMeasurable), hmp.map_eq]
  set Rad : (Fin n → X) → ℝ := fun x ↦ empiricalRademacherComplexity n f x with hRad_def
  have hsupm : ∀ (u : (Fin n → Bool) → H → (Fin n → X) → ℝ), (∀ σ h, Measurable (u σ h)) →
      ∀ σ, Measurable fun x ↦ sSup (range fun h ↦ u σ h x) := fun u hu σ ↦
    Measurable.iSup fun h ↦ hu σ h
  have hRm : Measurable Rad := measurable_empiricalRademacherComplexity n f hm
  have hRb : ∀ x, |Rad x| ≤ 1 := abs_empiricalRademacherComplexity_le n f zero_le_one hb
  have hRi : Integrable Rad Pn := integrable_of_abs_le _ hRm hRb
  -- pointwise bound of the sign average
  have hpt : ∀ p, (2 : ℝ)⁻¹ ^ n * ∑ σ : Fin n → Bool, G (T σ p) ≤ Rad p.1 + Rad p.2 := by
    intro p
    have hRneg := empiricalRademacherComplexity_neg n f p.2
    simp only [Rad]
    rw [← hRneg]
    simp only [empiricalRademacherComplexity_eq]
    rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with σ _
    simp only [G]
    refine le_of_eq_of_le ?_ (sSup_range_add_le _ _)
    congr 2
    funext h
    simp only [g, T]
    rw [← add_div, ← sub_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases σ i <;> simp <;> ring
  -- assemble
  have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by
    simp [Finset.card_univ, Fintype.card_bool]
  have hTi : ∀ σ, Integrable (fun p ↦ G (T σ p)) (Pn.prod Pn) := fun σ ↦
    integrable_of_abs_le _ (g := fun p ↦ G (T σ p))
      (hGm.comp (measurePreserving_ghostSwap P n σ).measurable) fun p ↦ hGb _
  have havg : ∫ p, G p ∂(Pn.prod Pn) =
      ∫ p, (2 : ℝ)⁻¹ ^ n * ∑ σ : Fin n → Bool, G (T σ p) ∂(Pn.prod Pn) := by
    rw [integral_const_mul, integral_finsetSum _ fun σ _ ↦ hTi σ, ← Finset.sum_congr rfl
      fun σ _ ↦ hT σ, Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]
  have hfinal : ∫ p, (Rad p.1 + Rad p.2) ∂(Pn.prod Pn) = 2 * ∫ x, Rad x ∂Pn := by
    have h1 : ∫ p, Rad p.1 ∂(Pn.prod Pn) = ∫ x, Rad x ∂Pn := by
      have hmp : MeasurePreserving Prod.fst (Pn.prod Pn) Pn := measurePreserving_fst
      rw [← integral_map hmp.measurable.aemeasurable
        (by rw [hmp.map_eq]; exact hRm.aestronglyMeasurable), hmp.map_eq]
    have h2 : ∫ p, Rad p.2 ∂(Pn.prod Pn) = ∫ x, Rad x ∂Pn := by
      have hmp : MeasurePreserving Prod.snd (Pn.prod Pn) Pn := measurePreserving_snd
      rw [← integral_map hmp.measurable.aemeasurable
        (by rw [hmp.map_eq]; exact hRm.aestronglyMeasurable), hmp.map_eq]
    rw [integral_add
      (integrable_of_abs_le _ (g := fun p : (Fin n → X) × (Fin n → X) ↦ Rad p.1)
        (hRm.comp measurable_fst) fun p ↦ hRb _)
      (integrable_of_abs_le _ (g := fun p : (Fin n → X) × (Fin n → X) ↦ Rad p.2)
        (hRm.comp measurable_snd) fun p ↦ hRb _), h1, h2]
    ring
  calc _ ≤ ∫ p, G p ∂(Pn.prod Pn) := hlhs
    _ = _ := havg
    _ ≤ ∫ p, (Rad p.1 + Rad p.2) ∂(Pn.prod Pn) := by
        refine integral_mono ?_ ?_ hpt
        · exact (integrable_finsetSum _ fun σ _ ↦ hTi σ).const_mul _
        · exact (integrable_of_abs_le _ (g := fun p : (Fin n → X) × (Fin n → X) ↦ Rad p.1)
            (hRm.comp measurable_fst) fun p ↦ hRb _).add
              (integrable_of_abs_le _ (g := fun p : (Fin n → X) × (Fin n → X) ↦ Rad p.2)
                (hRm.comp measurable_snd) fun p ↦ hRb _)
    _ = 2 * ∫ x, Rad x ∂Pn := hfinal

/-- McDiarmid tail for the supremum of the centered empirical means of a finite class whose
members oscillate by at most `1`: the supremum exceeds its mean by `t ≥ 0` with probability
at most `exp(-2 n t²)`. -/
theorem measureReal_integral_add_le_sSup_le {H X : Type*} [Fintype H] [Nonempty H]
    [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hosc : ∀ h x y, |f h x - f h y| ≤ 1) (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n ↦ P).real {x | ∫ y, sSup (range fun h ↦
        (∑ i, f h (y i)) / n - ∫ z, f h z ∂P) ∂(Measure.pi fun _ : Fin n ↦ P) + t ≤
          sSup (range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P)} ≤
      Real.exp (-2 * n * t ^ 2) := by
  set Pn := Measure.pi fun _ : Fin n ↦ P
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set F : (Fin n → X) → ℝ := fun x ↦ sSup (range fun h ↦
    (∑ i, f h (x i)) / n - ∫ z, f h z ∂P) with hF_def
  have hFm : Measurable F := Measurable.iSup fun h ↦
    ((Finset.measurable_sum _ fun i _ ↦ (hm h).comp (measurable_pi_apply i)).div_const _).sub
      measurable_const
  have hbd : ∀ (i : Fin n) (x x' : Fin n → X), (∀ l, l ≠ i → x l = x' l) →
      |F x - F x'| ≤ 1 / n := by
    intro i x x' hxx'
    refine abs_sSup_range_sub_sSup_range_le fun h ↦ ?_
    have hs : ∑ j, f h (x j) - ∑ j, f h (x' j) = f h (x i) - f h (x' i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_single i (fun j _ hj ↦ by rw [hxx' j hj, sub_self]) (by simp)
    have : (∑ j, f h (x j)) / n - ∫ z, f h z ∂P - ((∑ j, f h (x' j)) / n - ∫ z, f h z ∂P) =
        (f h (x i) - f h (x' i)) / n := by
      rw [← hs]; ring
    rw [this, abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right (hosc h _ _) hnr.le
  have hsub := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences P F hFm
    (fun _ ↦ 1 / n) hbd
  have hset : {x | ∫ y, F y ∂Pn + t ≤ F x} = {x | t ≤ F x - ∫ y, F y ∂Pn} := by
    ext x; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  change Pn.real {x | ∫ y, F y ∂Pn + t ≤ F x} ≤ _
  rw [hset]
  refine (hsub.measure_ge_le ht).trans_eq ?_
  congr 1
  have hcoe : ((∑ _i : Fin n, (1 / (n : ℝ)).toNNReal ^ 2 / 4 : ℝ≥0) : ℝ) = 1 / (4 * n) := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.coe_toNNReal _ (by positivity)]
    field_simp
  rw [hcoe]
  field_simp
  ring

/-- GAPS 107.2, high-probability Rademacher bound for a finite class of `[0,1]`-valued
functions: with probability at least `1 - δ`, the uniform deviation
`sup_h |n⁻¹ ∑ᵢ f h (xᵢ) - ∫ f h dP|` is at most `2 𝔼 R̂ₙ + √(log(2/δ) / (2n))`, where `𝔼 R̂ₙ`
is the expected empirical Rademacher complexity. The expectation bound of GAPS 107.2 is
`integral_sSup_sub_le_two_mul_rademacher`. -/
theorem measureReal_two_mul_rademacher_add_lt_sSup_le
    {H X : Type*} [Fintype H] [Nonempty H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    (Measure.pi fun _ : Fin n ↦ P).real {x |
      2 * ∫ y, empiricalRademacherComplexity n f y ∂(Measure.pi fun _ : Fin n ↦ P) +
          Real.sqrt (Real.log (2 / delta) / (2 * n)) <
        sSup (range fun h ↦ |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P|)} ≤ delta := by
  set Pn := Measure.pi fun _ : Fin n ↦ P
  set R := ∫ x, empiricalRademacherComplexity n f x ∂Pn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : ∀ h x, |f h x| ≤ 1 := fun h x ↦ by
    rw [abs_le]; constructor <;> linarith [(hb h x).1, (hb h x).2]
  have hosc : ∀ h x y, |f h x - f h y| ≤ 1 := fun h x y ↦ by
    rw [abs_le]; constructor <;> linarith [(hb h x).1, (hb h x).2, (hb h y).1, (hb h y).2]
  have hsym := integral_sSup_sub_le_two_mul_rademacher P f hm hab n hn
  -- the negated class
  have hsymneg := integral_sSup_sub_le_two_mul_rademacher P (fun h z ↦ -f h z)
    (fun h ↦ (hm h).neg) (fun h x ↦ by rw [abs_neg]; exact hab h x) n hn
  simp only [empiricalRademacherComplexity_neg] at hsymneg
  set tt := Real.sqrt (Real.log (2 / delta) / (2 * n)) with htt
  have htt0 : 0 ≤ tt := Real.sqrt_nonneg _
  have htail := measureReal_integral_add_le_sSup_le P f hm hosc n hn htt0
  have htailneg := measureReal_integral_add_le_sSup_le P (fun h z ↦ -f h z)
    (fun h ↦ (hm h).neg) (fun h x y ↦ by
      rw [show -f h x - -f h y = f h y - f h x by ring]; exact hosc h y x) n hn htt0
  have hexp : Real.exp (-2 * n * tt ^ 2) = delta / 2 := by
    have hlog : 0 ≤ Real.log (2 / delta) / (2 * n) := by
      refine div_nonneg (Real.log_nonneg ?_) (by positivity)
      rw [le_div_iff₀ hd.1]; linarith [hd.2]
    rw [htt, Real.sq_sqrt hlog]
    have : -2 * (n : ℝ) * (Real.log (2 / delta) / (2 * n)) = -Real.log (2 / delta) := by
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (div_pos two_pos hd.1), inv_div]
  rw [hexp] at htail htailneg
  -- the two one-sided events cover the event
  have hsub : {x : Fin n → X | 2 * R + tt <
      sSup (range fun h ↦ |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P|)} ⊆
      {x | ∫ y, sSup (range fun h ↦ (∑ i, f h (y i)) / n - ∫ z, f h z ∂P) ∂Pn + tt ≤
          sSup (range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P)} ∪
        {x | ∫ y, sSup (range fun h ↦ (∑ i, -f h (y i)) / n - ∫ z, -f h z ∂P) ∂Pn + tt ≤
          sSup (range fun h ↦ (∑ i, -f h (x i)) / n - ∫ z, -f h z ∂P)} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    obtain ⟨_, ⟨h, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (range_nonempty _) hx
    beta_reduce at hlt
    rcases le_total 0 ((∑ i, f h (x i)) / n - ∫ z, f h z ∂P) with hs | hs
    · left
      rw [abs_of_nonneg hs] at hlt
      have := le_csSup (finite_range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P).bddAbove
        ⟨h, rfl⟩
      simp only [mem_ofPred_eq]
      linarith
    · right
      rw [abs_of_nonpos hs] at hlt
      have := le_csSup (finite_range fun h ↦ (∑ i, -f h (x i)) / n - ∫ z, -f h z ∂P).bddAbove
        ⟨h, rfl⟩
      have heq : (∑ i, -f h (x i)) / n - ∫ z, -f h z ∂P =
          -((∑ i, f h (x i)) / n - ∫ z, f h z ∂P) := by
        rw [Finset.sum_neg_distrib, integral_neg]; ring
      simp only [mem_ofPred_eq]
      linarith
  calc Pn.real _ ≤ Pn.real (_ ∪ _) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ delta / 2 + delta / 2 := add_le_add htail htailneg
    _ = delta := by ring

end CKSD
