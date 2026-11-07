module

public import CKSD.Nonparametric.Basic

/-!
# Nonparametric: LowerBounds

Sources: `GAPS.md`, `SYNOPSIS103.md`, and `STRUCTURE103.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

-- Use the common rank measurable structure.
attribute [local instance] rankMeasurableSpace

/-- Every measurable event difference is bounded by statistical total variation. -/
theorem abs_measureReal_sub_le_totalVariationDistance {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set X) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ totalVariationDistance P Q := by
  apply le_csSup (show BddAbove {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ?_)
    (show |P.real A - Q.real A| ∈ {r : ℝ | ∃ B : Set X,
      MeasurableSet B ∧ r = |P.real B - Q.real B|} from ⟨A, hA, rfl⟩)
  refine ⟨1, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  apply abs_le.mpr
  constructor <;> linarith [measureReal_nonneg (μ := P) (s := B),
    measureReal_nonneg (μ := Q) (s := B),
    measureReal_le_one (μ := P) (s := B), measureReal_le_one (μ := Q) (s := B)]

/-- GAPS 103.39: Le Cam's two-point lower bound with the statistical TV normalization. -/
theorem le_cam_two_point_lower_bound {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (θ₀ θ₁ : Θ) (s : ℝ) (hs : 0 < s) (hsep : 2 * s ≤ dist θ₀ θ₁)
    (T : X → Θ) (hT : Measurable T) :
    (1 - totalVariationDistance P₀ P₁) / 2 ≤ max (P₀.real {x | s ≤ dist (T x) θ₀})
      (P₁.real {x | s ≤ dist (T x) θ₁}) := by
  let B := {x | dist (T x) θ₀ < s}
  have hB : MeasurableSet B := measurableSet_lt
    ((show Continuous (fun t : Θ ↦ dist t θ₀) from
      continuous_id.dist continuous_const).measurable.comp hT) measurable_const
  have hBc : Bᶜ = {x | s ≤ dist (T x) θ₀} := by
    ext x
    simp only [B, mem_compl_iff, mem_ofPred_eq, not_lt]
  have hsubset : B ⊆ {x | s ≤ dist (T x) θ₁} := by
    intro x hx
    have hdist := dist_triangle θ₀ (T x) θ₁
    rw [dist_comm θ₀ (T x)] at hdist
    change dist (T x) θ₀ < s at hx
    change s ≤ dist (T x) θ₁
    linarith
  have htv := abs_measureReal_sub_le_totalVariationDistance P₀ P₁ B hB
  have hmass := measureReal_add_measureReal_compl (μ := P₀) hB
  rw [probReal_univ, hBc] at hmass
  have hother := measureReal_mono (μ := P₁) hsubset
  have hdiff := le_abs_self (P₀.real B - P₁.real B)
  have hmax₀ := le_max_left (P₀.real {x | s ≤ dist (T x) θ₀})
    (P₁.real {x | s ≤ dist (T x) θ₁})
  have hmax₁ := le_max_right (P₀.real {x | s ≤ dist (T x) θ₀})
    (P₁.real {x | s ≤ dist (T x) θ₁})
  linarith

/-- GAPS 103.40: Fano's bound in its finite-reference-KL form. -/
theorem fano_lower_bound {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (M : ℕ) (hM : 2 ≤ M)
    (θ : Fin M → Θ) (P : Fin M → Measure X) (hP : ∀ j, IsProbabilityMeasure (P j))
    (Q : Measure X) [IsProbabilityMeasure Q] (hKL : ∀ j, InformationTheory.klDiv (P j) Q ≠ ∞)
    (s : ℝ) (hs : 0 < s) (hsep : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    (T : X → Θ) (hT : Measurable T) :
    1 - (((∑ j, (InformationTheory.klDiv (P j) Q).toReal) / M + Real.log 2) / Real.log M) ≤
      sSup (range fun j ↦ (P j).real {x | s ≤ dist (T x) (θ j)}) := by
  sorry

/-- GAPS 103.45: a separated binary packing containing zero. -/
theorem exists_hamming_packing (m : ℕ) (hm : 8 ≤ m) :
    ∃ C : Finset (Fin m → Bool), (fun _ ↦ false) ∈ C ∧
      Real.rpow 2 ((m : ℝ) / 8) ≤ (C.card : ℝ) - 1 ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        (m : ℝ) / 8 ≤ ((Finset.univ.filter fun i ↦ x i ≠ y i).card : ℝ) := by
  sorry

/-- GAPS 103.46, TV version of Assouad's lemma for binary-valued estimators. -/
theorem assouad_lower_bound {X : Type*} [MeasurableSpace X] (m : ℕ)
    (P : (Fin m → Bool) → Measure X) (hP : ∀ w, IsProbabilityMeasure (P w))
    (α : ℝ) (hα : α ∈ Icc 0 1)
    (hnear : ∀ w w', (Finset.univ.filter fun i ↦ w i ≠ w' i).card = 1 → totalVariationDistance (P w)
      (P w') ≤ α)
    (T : X → (Fin m → Bool)) (hT : Measurable T) :
    (m : ℝ) * (1 - α) / 2 ≤ sSup (range fun w ↦
      ∫ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) ∂P w) := by
  set f := fun w : Fin m → Bool ↦
    ∫ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) ∂P w with hf
  -- the events on which the `j`-th coordinate is wrong
  have hmeas : ∀ (j : Fin m) (b : Bool), MeasurableSet {x | T x j ≠ b} := by
    intro j b
    exact (measurableSet_singleton b).compl.preimage ((measurable_pi_apply j).comp hT)
  have hfeq : ∀ w, f w = ∑ j, (P w).real {x | T x j ≠ w j} := by
    intro w
    have hpt : ∀ x, ((Finset.univ.filter fun i ↦ T x i ≠ w i).card : ℝ) =
        ∑ j, {x | T x j ≠ w j}.indicator (fun _ ↦ (1 : ℝ)) x := by
      intro x
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : T x j ≠ w j <;> simp [h, Set.indicator]
    simp only [hf, hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_indicator_const _ (hmeas j (w j)), smul_eq_mul, mul_one]
    · intro j _
      exact (integrable_const (1 : ℝ)).indicator (hmeas j (w j))
  -- flipping one coordinate
  let flip : Fin m → (Fin m → Bool) → (Fin m → Bool) := fun j w ↦ Function.update w j (!w j)
  have hflip_inv : ∀ j, Function.Involutive (flip j) := by
    intro j w
    ext i
    by_cases h : i = j
    · subst h; simp [flip]
    · simp [flip, Function.update_of_ne h]
  have hflip_j : ∀ j w, flip j w j = !w j := by intro j w; simp [flip]
  have hflip_card : ∀ j w, (Finset.univ.filter fun i ↦ w i ≠ flip j w i).card = 1 := by
    intro j w
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    by_cases h : i = j
    · subst h; simp [flip]
    · simp [flip, h]
  have hpair : ∀ j w, 1 - α ≤ (P w).real {x | T x j ≠ w j} +
      (P (flip j w)).real {x | T x j ≠ flip j w j} := by
    intro j w
    have hset : {x | T x j ≠ flip j w j} = {x | T x j ≠ w j}ᶜ := by
      ext x
      simp only [hflip_j, mem_ofPred_eq, mem_compl_iff]
      cases T x j <;> cases w j <;> simp
    rw [hset, probReal_compl_eq_one_sub (hmeas j (w j))]
    have htv := abs_measureReal_sub_le_totalVariationDistance (P w) (P (flip j w))
      {x | T x j ≠ w j} (hmeas j (w j))
    have := hnear w (flip j w) (hflip_card j w)
    have := neg_abs_le ((P w).real {x | T x j ≠ w j} - (P (flip j w)).real {x | T x j ≠ w j})
    linarith
  have hcoord : ∀ j, (Fintype.card (Fin m → Bool) : ℝ) * (1 - α) / 2 ≤
      ∑ w, (P w).real {x | T x j ≠ w j} := by
    intro j
    have hre : ∑ w, (P w).real {x | T x j ≠ w j} =
        ∑ w, (P (flip j w)).real {x | T x j ≠ flip j w j} :=
      (Fintype.sum_equiv (hflip_inv j).toPerm _ _ fun w ↦ rfl).symm
    have hsum : ∑ _w : Fin m → Bool, (1 - α) ≤ ∑ w, ((P w).real {x | T x j ≠ w j} +
        (P (flip j w)).real {x | T x j ≠ flip j w j}) :=
      Finset.sum_le_sum fun w _ ↦ hpair j w
    rw [Finset.sum_add_distrib, ← hre, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    linarith
  have htotal : (Fintype.card (Fin m → Bool) : ℝ) * ((m : ℝ) * (1 - α) / 2) ≤ ∑ w, f w := by
    simp only [hfeq]
    rw [Finset.sum_comm]
    calc (Fintype.card (Fin m → Bool) : ℝ) * ((m : ℝ) * (1 - α) / 2)
        = ∑ _j : Fin m, (Fintype.card (Fin m → Bool) : ℝ) * (1 - α) / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hcoord j
  have hbdd : BddAbove (range f) := (finite_range f).bddAbove
  have hle : ∑ w, f w ≤ (Fintype.card (Fin m → Bool) : ℝ) * sSup (range f) := by
    calc ∑ w, f w ≤ ∑ _w : Fin m → Bool, sSup (range f) :=
          Finset.sum_le_sum fun w _ ↦ le_csSup hbdd (mem_range_self w)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card (Fin m → Bool) := by
    exact_mod_cast Fintype.card_pos
  exact le_of_mul_le_mul_left (htotal.trans hle) hcard

/-- The coordinatewise L1 norm splits over complementary coordinate sets. -/
theorem restrictedL1Norm_add_compl {p : ℕ} (S : Finset (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x + restrictedL1Norm Sᶜ x = restrictedL1Norm Finset.univ x := by
  exact S.sum_add_sum_compl (fun j ↦ |x j|)

/-- A restricted reverse triangle bound for coordinatewise L1 norms. -/
theorem restrictedL1Norm_le_add_sub {p : ℕ} (S : Finset (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) :
    restrictedL1Norm S x ≤ restrictedL1Norm S y + restrictedL1Norm S (y - x) := by
  unfold restrictedL1Norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  change |x j| ≤ |y j| + |y j - x j|
  calc
    |x j| = |y j + (x j - y j)| := by congr 1; ring
    _ ≤ |y j| + |x j - y j| := abs_add_le _ _
    _ = |y j| + |y j - x j| := by rw [abs_sub_comm]

/-- GAPS 103.48, equivalence between the nullspace property and unique basis pursuit. -/
theorem nullspace_property_iff_basis_pursuit_unique {n p : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Finset (Fin p)) :
    (∀ δ, A δ = 0 → δ ≠ 0 → restrictedL1Norm S δ < restrictedL1Norm Sᶜ δ) ↔
    ∀ β, (∀ j ∉ S, β j = 0) → ∀ b, A b = A β → b ≠ β →
      restrictedL1Norm Finset.univ β < restrictedL1Norm Finset.univ b := by
  constructor
  · intro hnsp β hβ b hab hne
    have hnull : A (b - β) = 0 := by rw [map_sub, hab, sub_self]
    have hstrict := hnsp (b - β) hnull (sub_ne_zero.mpr hne)
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hβ j (Finset.mem_compl.mp hj), abs_zero]
    have hcomp : restrictedL1Norm Sᶜ (b - β) = restrictedL1Norm Sᶜ b := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [PiLp.sub_apply, hβ j (Finset.mem_compl.mp hj), sub_zero]
    have htriangle := restrictedL1Norm_le_add_sub S β b
    have hsplitβ := restrictedL1Norm_add_compl S β
    have hsplitb := restrictedL1Norm_add_compl S b
    rw [hβc, add_zero] at hsplitβ
    rw [hcomp] at hstrict
    linarith
  · intro hunique δ hnull hne
    let β : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (fun j ↦ if j ∈ S then δ j else 0)
    let b := β - δ
    have hβ : ∀ j ∉ S, β j = 0 := by
      intro j hj
      simp [β, hj]
    have hab : A b = A β := by
      change A (β - δ) = A β
      rw [map_sub, hnull, sub_zero]
    have hbne : b ≠ β := by
      intro h
      change β - δ = β at h
      exact hne (sub_eq_self.mp h)
    have hlt := hunique β hβ b hab hbne
    have hβs : restrictedL1Norm S β = restrictedL1Norm S δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [β, hj]
    have hβc : restrictedL1Norm Sᶜ β = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [β, Finset.mem_compl.mp hj]
    have hbs : restrictedL1Norm S b = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [b, β, PiLp.sub_apply, hj]
    have hbc : restrictedL1Norm Sᶜ b = restrictedL1Norm Sᶜ δ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [b, β, PiLp.sub_apply, Finset.mem_compl.mp hj]
    rw [← restrictedL1Norm_add_compl S β, ← restrictedL1Norm_add_compl S b,
      hβs, hβc, hbs, hbc, add_zero, zero_add] at hlt
    exact hlt

/-- GAPS 103.48, restricted-isometry sufficient condition for exact sparse recovery. -/
theorem nullspace_property_of_hasRestrictedIsometry {n p s : ℕ}
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : δ ∈ Ico 0 (1 / 3 : ℝ)) (hrip : HasRestrictedIsometry A (2 * s) δ)
    (S : Finset (Fin p)) (hS : S.card ≤ s) :
    ∀ v, A v = 0 → v ≠ 0 → restrictedL1Norm S v < restrictedL1Norm Sᶜ v := by
  sorry

/-- GAPS 103.49: stable basis pursuit, with constants depending only on the RIP bound. -/
theorem basis_pursuit_error_bound_of_hasRestrictedIsometry
    (δ : ℝ) (hδ : δ ∈ Ico 0 (4 / Real.sqrt 41)) :
    ∃ C > 0, ∃ D > 0, ∀ (n p s : ℕ), 0 < s →
      ∀ A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n),
        HasRestrictedIsometry A (2 * s) δ → ∀ (β b : EuclideanSpace ℝ (Fin p))
        (y : EuclideanSpace ℝ (Fin n)) (η : ℝ), 0 ≤ η → ‖A β - y‖ ≤ η →
        ‖A b - y‖ ≤ η →
        (∀ t, ‖A t - y‖ ≤ η → restrictedL1Norm Finset.univ b ≤ restrictedL1Norm Finset.univ t) →
        restrictedL1Norm Finset.univ (b - β) ≤ C * bestSparseL1Error s β + D * Real.sqrt s * η ∧
        ‖b - β‖ ≤ C / Real.sqrt s * bestSparseL1Error s β + D * η := by
  sorry

/-- Schur test for a symmetric matrix: the Euclidean operator norm is at most any bound on
the absolute row sums. -/
theorem norm_toEuclideanCLM_le_of_rowSum_le {p : ℕ} (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : D.IsSymm) (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, |D i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D‖ ≤ R := by
  have hsymm : ∀ i j, D i j = D j i := fun i j ↦ by
    simpa using congrFun (congrFun hD.eq j) i
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun x ↦ ?_
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) D x‖ ^ 2 ≤ (R * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
    calc ∑ i, (∑ j, D i j * x j) ^ 2
        ≤ ∑ i, (∑ j, |D i j|) * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ ↦ abs_nonneg _)
            (fun j _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun j _ ↦ ?_)
          rw [mul_pow, ← mul_assoc, ← sq, sq_abs]
      _ ≤ ∑ i, R * ∑ j, |D i j| * x j ^ 2 := by
          gcongr with i
          exact hrow i
      _ = R * ∑ j, x j ^ 2 * ∑ i, |D j i| := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hsymm i j]; ring
      _ ≤ R * ∑ j, x j ^ 2 * R := by
          gcongr with j
          exact hrow j
      _ = R ^ 2 * ∑ j, x j ^ 2 := by rw [← Finset.sum_mul]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- GAPS 103.52, deterministic sparse-row bound for hard covariance thresholding. -/
theorem norm_thresholded_covariance_sub_le {p : ℕ} (Sigma S : Matrix (Fin p) (Fin p) ℝ)
    (hSigma : Sigma.IsSymm) (hS : S.IsSymm) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (herr : ∀ i j, |S i j - Sigma i j| ≤ lambda) (s : ℕ)
    (hs : ∀ i, (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card ≤ s) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma)‖ ≤ 2 * s * lambda := by
  classical
  set D := Matrix.of (fun i j ↦ if lambda < |S i j| then S i j else 0) - Sigma with hDdef
  have hSs : ∀ i j, S i j = S j i := fun i j ↦ by simpa using congrFun (congrFun hS.eq j) i
  have hSigs : ∀ i j, Sigma i j = Sigma j i := fun i j ↦ by
    simpa using congrFun (congrFun hSigma.eq j) i
  have hDsymm : D.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, hDdef, Matrix.sub_apply, Matrix.of_apply, hSs i j,
      hSigs i j]
  have hentry : ∀ i j, |D i j| ≤ if Sigma i j ≠ 0 then 2 * lambda else 0 := by
    intro i j
    have he := herr i j
    simp only [hDdef, Matrix.sub_apply, Matrix.of_apply]
    by_cases hz : Sigma i j = 0
    · have : ¬ lambda < |S i j| := by rw [hz, sub_zero] at he; exact not_lt.mpr he
      simp [hz, this]
    · simp only [ne_eq, hz, not_false_eq_true, ite_true]
      split_ifs with ht
      · linarith
      · rw [zero_sub, abs_neg]
        have h1 := abs_sub_abs_le_abs_sub (Sigma i j) (S i j)
        rw [abs_sub_comm] at h1
        linarith [not_lt.mp ht]
  refine norm_toEuclideanCLM_le_of_rowSum_le D hDsymm _ (by positivity) fun i ↦ ?_
  calc ∑ j, |D i j| ≤ ∑ j, (if Sigma i j ≠ 0 then 2 * lambda else 0) :=
        Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = (Finset.univ.filter fun j ↦ Sigma i j ≠ 0).card * (2 * lambda) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ s * (2 * lambda) := by gcongr; exact_mod_cast hs i
    _ = 2 * s * lambda := by ring


end CKSD
