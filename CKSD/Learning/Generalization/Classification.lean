module

public import CKSD.Learning.Generalization.Concentration

/-!
# Classification lower bounds and convex calibration

Label-flip lower bounds, Bayes classification risk, plug-in excess risk, and the sign of
minimizers of convex surrogate risks. Sources: GAPS 107.7, 107.8, and 107.11.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Flipping one label is an involution, so a label-blind guess at that coordinate is wrong for
exactly half of all labellings. -/
theorem sum_flip_ne {m : ℕ} (j : Fin m) (g : (Fin m → Bool) → Bool)
    (hg : ∀ lab, g (Function.update lab j (!lab j)) = g lab) :
    ∑ lab : Fin m → Bool, (if g lab ≠ lab j then (1 : ℝ) else 0) = 2 ^ m / 2 := by
  have hinv : Function.Involutive fun lab : Fin m → Bool ↦ Function.update lab j (!lab j) := by
    intro lab; ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  set e := hinv.toPerm
  have hcomp := Equiv.sum_comp e (fun lab ↦ if g lab ≠ lab j then (1 : ℝ) else 0)
  have hpt : ∀ lab : Fin m → Bool, (if g (e lab) ≠ (e lab) j then (1 : ℝ) else 0) =
      1 - if g lab ≠ lab j then 1 else 0 := by
    intro lab
    simp only [e, Function.Involutive.coe_toPerm, hg, Function.update_self]
    cases g lab <;> cases lab j <;> simp
  simp_rw [hpt] at hcomp
  rw [Finset.sum_sub_distrib] at hcomp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcomp
  push_cast at hcomp
  linarith

/-- GAPS 107.7, finite-support no-free-lunch bound; taking arbitrarily large `m`
gives the infinite-feature-space assertion. -/
theorem no_free_lunch_lower_bound (n m : ℕ) (hm : 0 < m)
    (learn : (Fin n → Fin m × Bool) → Fin m → Bool) :
    ∃ label : Fin m → Bool,
      (1 - (n : ℝ) / m) / 2 ≤
        (∑ x : Fin n → Fin m,
          ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label
            (x i))) j ≠ label j).card : ℝ) / m) /
          (m : ℝ) ^ n := by
  set F : (Fin m → Bool) → ℝ := fun label ↦ (∑ x : Fin n → Fin m,
      ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) /
        m) / (m : ℝ) ^ n
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- per sample: the label sum over unseen points
  have hx : ∀ x : Fin n → Fin m, (2 : ℝ) ^ m / 2 * (m - n) ≤
      ∑ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) := by
    intro x
    have hcard : ∀ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) =
          ∑ j, if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 := by
      intro label; rw [Finset.natCast_card_filter]
    simp_rw [hcard]
    rw [Finset.sum_comm]
    set U := Finset.univ \ Finset.univ.image x
    have hU : (m : ℝ) - n ≤ U.card := by
      have h1 : U.card = m - (Finset.univ.image x).card := by
        rw [Finset.card_univ_sdiff, Fintype.card_fin]
      have h2 : (Finset.univ.image x).card ≤ n := by
        simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := x)
      have h3 : (Finset.univ.image x).card ≤ m := by
        simpa using Finset.card_le_univ (Finset.univ.image x)
      rw [h1, Nat.cast_sub h3]
      have h2' : ((Finset.univ.image x).card : ℝ) ≤ n := by exact_mod_cast h2
      linarith
    calc (2 : ℝ) ^ m / 2 * (m - n) ≤ (2 : ℝ) ^ m / 2 * U.card :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ = ∑ j ∈ U, ∑ label : Fin m → Bool,
            if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 := by
          rw [Finset.sum_congr rfl fun j hj ↦ sum_flip_ne j
            (fun label ↦ learn (fun i ↦ (x i, label (x i))) j) fun lab ↦ ?_]
          · simp [mul_comm]
          · have hj' : ∀ i, x i ≠ j := fun i hi ↦ by
              simp only [U, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and,
                not_exists] at hj
              exact hj i hi
            simp only [Function.update_of_ne (hj' _)]
      _ ≤ ∑ j, ∑ label : Fin m → Bool,
            if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦
            Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
  have hsum : (2 : ℝ) ^ m * ((1 - (n : ℝ) / m) / 2) ≤ ∑ label, F label := by
    have hF : ∑ label, F label = (∑ x : Fin n → Fin m, ∑ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card :
          ℝ)) / (m ^ n * m) := by
      simp only [F, div_div, ← Finset.sum_div]
      rw [Finset.sum_comm, mul_comm]
    rw [hF, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ m * ((1 - (n : ℝ) / m) / 2) * ((m : ℝ) ^ n * m)
        = ∑ _x : Fin n → Fin m, (2 : ℝ) ^ m / 2 * (m - n) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ hx x
  by_contra hcon
  push Not at hcon
  have : ∑ label, F label < ∑ _label : Fin m → Bool, (1 - (n : ℝ) / m) / 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun label _ ↦ hcon label
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

/-- Binary conditional classification loss is integrable under a probability law. -/
theorem integrable_classificationLoss {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η : X → ℝ) (hη : Measurable η)
    (hrange : ∀ x, η x ∈ Icc 0 1) (g : X → Bool) (hg : Measurable g) :
    Integrable (fun x ↦ if g x then 1 - η x else η x) P := by
  have hs : MeasurableSet {x | g x = true} := hg (measurableSet_singleton true)
  apply Integrable.of_bound
    (Measurable.ite hs (measurable_const.sub hη) hη).aestronglyMeasurable 1
  filter_upwards with x
  simp only [Pi.sub_apply]
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  split_ifs <;> constructor <;> linarith [(hrange x).1, (hrange x).2]

/-- GAPS 107.8: the exact excess Bayes classification risk identity. -/
theorem classificationRisk_sub_bayes_risk_eq {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η : X → ℝ) (hη : Measurable η)
    (hrange : ∀ x, η x ∈ Icc 0 1) (g : X → Bool) (hg : Measurable g) :
    let star := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x);
    classificationRisk P η g - classificationRisk P η star =
      ∫ x, if g x ≠ star x then |2 * η x - 1| else 0 ∂P := by
  dsimp only
  let star : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)
  have hstar : Measurable star := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ η x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const hη)
  change (∫ x, (if g x then 1 - η x else η x) ∂P) -
      (∫ x, (if star x then 1 - η x else η x) ∂P) =
    ∫ x, if g x ≠ star x then |2 * η x - 1| else 0 ∂P
  rw [← integral_sub (integrable_classificationLoss P η hη hrange g hg)
    (integrable_classificationLoss P η hη hrange star hstar)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : (1 / 2 : ℝ) ≤ η x
  · cases hx : g x <;>
      simp [star, abs_of_nonneg (by linarith : 0 ≤ 2 * η x - 1)] <;>
        split_ifs <;> linarith
  · cases hx : g x <;>
      simp [star, abs_of_nonpos (by linarith : 2 * η x - 1 ≤ 0)] <;>
        split_ifs <;> linarith

/-- GAPS 107.8: the plugin classification risk bound. -/
theorem classificationRisk_plugin_sub_bayes_risk_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η a : X → ℝ)
    (hη : Measurable η) (ha : Measurable a) (hi : Integrable a P)
    (hrange : ∀ x, η x ∈ Icc 0 1) :
    classificationRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ a x)) -
      classificationRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)) ≤
        2 * ∫ x, |a x - η x| ∂P := by
  let ga : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ a x)
  let star : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)
  have hga : Measurable ga := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ a x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const ha)
  have hstar : Measurable star := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ η x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const hη)
  have hiη : Integrable η P := by
    simpa only [Bool.false_eq_true, ite_false] using
      integrable_classificationLoss P η hη hrange (fun _ ↦ false) measurable_const
  change (∫ x, (if ga x then 1 - η x else η x) ∂P) -
      (∫ x, (if star x then 1 - η x else η x) ∂P) ≤ _
  rw [← integral_sub (integrable_classificationLoss P η hη hrange ga hga)
    (integrable_classificationLoss P η hη hrange star hstar), ← integral_const_mul]
  apply integral_mono
    ((integrable_classificationLoss P η hη hrange ga hga).sub
      (integrable_classificationLoss P η hη hrange star hstar))
    ((hi.sub hiη).abs.const_mul 2)
  intro x
  dsimp only [ga, star]
  simp only [decide_eq_true_eq, Pi.sub_apply]
  have hlo := neg_abs_le (a x - η x)
  have hhi := le_abs_self (a x - η x)
  split_ifs <;> linarith [abs_nonneg (a x - η x)]

/-- GAPS 107.11, pointwise classification calibration of a convex surrogate. -/
theorem surrogate_minimizer_sign_of_convex (phi : ℝ → ℝ) (hc : ConvexOn ℝ univ phi)
    (d : ℝ) (hd : HasDerivAt phi d 0) (hdpos : 0 < d)
    (eta : ℝ) (he : eta ∈ Icc 0 1) (hne : eta ≠ 1 / 2)
    (u : ℝ) (hmin : ∀ v, eta * phi (-u) + (1 - eta) * phi u ≤
      eta * phi (-v) + (1 - eta) * phi v) : 0 < (eta - 1 / 2) * u := by
  let C : ℝ → ℝ := fun v ↦ eta * phi (-v) + (1 - eta) * phi v
  change ∀ v, C u ≤ C v at hmin
  have hcneg : ConvexOn ℝ univ (fun v ↦ phi (-v)) := by
    simpa only [preimage_univ, Function.comp_def, LinearMap.neg_apply, LinearMap.id_apply] using
      hc.comp_linearMap (-(LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have hC : ConvexOn ℝ univ C := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hneg := hcneg.2 (mem_univ x) (mem_univ y) ha hb hab
    have hpos := hc.2 (mem_univ x) (mem_univ y) ha hb hab
    dsimp only [C]
    simp only [smul_eq_mul] at hneg hpos ⊢
    calc
      _ ≤ eta * (a * phi (-x) + b * phi (-y)) +
          (1 - eta) * (a * phi x + b * phi y) :=
        add_le_add (mul_le_mul_of_nonneg_left hneg he.1)
          (mul_le_mul_of_nonneg_left hpos (sub_nonneg.mpr he.2))
      _ = _ := by ring
  have hdneg : HasDerivAt (fun v ↦ phi (-v)) (-d) 0 := by
    have hd' : HasDerivAt phi d (-(0 : ℝ)) := by simpa only [neg_zero] using hd
    have h := hd'.comp (0 : ℝ) (hasDerivAt_neg 0)
    simpa only [Function.comp_def, neg_zero, mul_neg_one] using h
  have hD : HasDerivAt C (eta * (-d) + (1 - eta) * d) 0 :=
    (hdneg.const_mul eta).add (hd.const_mul (1 - eta))
  by_cases hu : u = 0
  · subst u
    have hlocal : IsLocalMin C 0 := Filter.Eventually.of_forall hmin
    have hz := hlocal.hasDerivAt_eq_zero hD
    exfalso
    apply hne
    have hmul : (1 - 2 * eta) * d = 0 := by nlinarith
    have hzeta := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hdpos)
    linarith
  · rcases lt_or_gt_of_ne hu with hneg | hpos
    · have hs := hC.slope_le_of_hasDerivAt (mem_univ u) (mem_univ 0) hneg hD
      have hsl : 0 ≤ slope C u 0 := by
        rw [slope_def_field]
        exact div_nonneg (sub_nonneg.mpr (hmin 0)) (by linarith)
      have hmul : 0 ≤ (1 - 2 * eta) * d := by nlinarith
      have hηle : eta ≤ 1 / 2 := by
        have := (mul_nonneg_iff_of_pos_right hdpos).mp hmul
        linarith
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (lt_of_le_of_ne hηle hne)) hneg
    · have hs := hC.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ u) hpos hD
      have hsl : slope C 0 u ≤ 0 := by
        rw [slope_def_field]
        exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmin 0)) (by linarith)
      have hmul : (1 - 2 * eta) * d ≤ 0 := by nlinarith
      have hηge : 1 / 2 ≤ eta := by
        have hh : 0 ≤ (2 * eta - 1) * d := by nlinarith
        have := (mul_nonneg_iff_of_pos_right hdpos).mp hh
        linarith
      exact mul_pos (sub_pos.mpr (lt_of_le_of_ne hηge hne.symm)) hpos

end CKSD
