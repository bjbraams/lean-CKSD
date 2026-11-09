module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.Matrix.FunctionalCalculus
public import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint

/-!
# The fixed-point equation of Gaussian barycenters

For nonnegative weights `w i` summing to one and positive definite real matrices `A i`, the
covariance of the Wasserstein barycenter of the Gaussian laws `N(m_i, A_i)` solves
`S = ∑ i, w i • (S^{1/2} A_i S^{1/2})^{1/2}`. This file proves that the equation has a positive
definite solution, by Brouwer's fixed-point theorem (TauCeti) on an order interval of scalar
matrices, using the continuity of the matrix functional calculus (TauCeti) and operator bounds
read off the spectrum.

## Main results

* `CKSD.abs_apply_le_of_nonneg_of_le_algebraMap`: entry bounds for `0 ≤ S ≤ b I`.
* `CKSD.exists_posDef_eq_sum_smul_sqrt_mul_mul_sqrt`: existence of a positive definite solution
  of the Gaussian barycenter fixed-point equation.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904–924, Theorem 6.1.
-/

@[expose] public section

noncomputable section

open scoped MatrixOrder
open Set Matrix

namespace CKSD

variable {n : Type*} [Fintype n] [DecidableEq n]


/-- Entries of a real positive semidefinite matrix `S ≤ b I` are bounded by `b` in absolute
value. -/
private theorem abs_apply_le_of_nonneg_of_le_algebraMap {S : Matrix n n ℝ} {b : ℝ} (h0 : 0 ≤ S)
    (hb : S ≤ algebraMap ℝ _ b) (i j : n) : |S i j| ≤ b := by
  have hS : S.PosSemidef := by simpa [Matrix.le_iff] using h0
  have hT : (algebraMap ℝ (Matrix n n ℝ) b - S).PosSemidef := Matrix.le_iff.1 hb
  have hQ : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ S *ᵥ x := fun x ↦ by
    simpa using hS.dotProduct_mulVec_nonneg x
  have hQ' : ∀ x : n → ℝ, x ⬝ᵥ S *ᵥ x ≤ b * (x ⬝ᵥ x) := fun x ↦ by
    have := hT.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at this
    linarith
  have hsym : S j i = S i j := by simpa using hS.1.apply i j
  have hii : ∀ k, 0 ≤ S k k ∧ S k k ≤ b := fun k ↦ by
    have h1 := hQ (Pi.single k 1)
    have h2 := hQ' (Pi.single k 1)
    simp at h1 h2
    exact ⟨h1, h2⟩
  by_cases hij : i = j
  · subst hij; rw [abs_of_nonneg (hii i).1]; exact (hii i).2
  have key : ∀ s : ℝ, s ^ 2 = 1 →
      (Pi.single i 1 + s • Pi.single j 1 : n → ℝ) ⬝ᵥ S *ᵥ (Pi.single i 1 + s • Pi.single j 1) =
        S i i + 2 * s * S i j + S j j := by
    intro s hs
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, hsym]
    linear_combination (S j j) * hs
  have h1 := (key 1 (by norm_num)) ▸ hQ' (Pi.single i 1 + (1 : ℝ) • Pi.single j 1)
  have h2 := (key (-1) (by norm_num)) ▸ hQ' (Pi.single i 1 + (-1 : ℝ) • Pi.single j 1)
  simp [dotProduct_add, hij, Ne.symm hij] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith [hii i, hii j]


/-- If `c I ≤ M` for a positive semidefinite matrix `M`, then `√c I ≤ M^{1/2}`. -/
private lemma algebraMap_sqrt_le_sqrt {M : Matrix n n ℝ} {c : ℝ} (hc : algebraMap ℝ _ c ≤ M)
    (hM : 0 ≤ M) : algebraMap ℝ _ (Real.sqrt c) ≤ CFC.sqrt M := by
  rw [CFC.sqrt_eq_real_sqrt M hM, cfcₙ_eq_cfc]
  exact algebraMap_le_cfc _ _ M fun x hx ↦ Real.sqrt_le_sqrt
    ((algebraMap_le_iff_le_spectrum (a := M)).1 hc x hx)

/-- If `M ≤ c I` for a positive semidefinite matrix `M`, then `M^{1/2} ≤ √c I`. -/
private lemma sqrt_le_algebraMap_sqrt {M : Matrix n n ℝ} {c : ℝ} (hc : M ≤ algebraMap ℝ _ c)
    (hM : 0 ≤ M) : CFC.sqrt M ≤ algebraMap ℝ _ (Real.sqrt c) := by
  rw [CFC.sqrt_eq_real_sqrt M hM, cfcₙ_eq_cfc]
  exact cfc_le_algebraMap _ _ M fun x hx ↦ Real.sqrt_le_sqrt
    ((le_algebraMap_iff_spectrum_le (a := M)).1 hc x hx)

/-- A positive definite real matrix satisfies `α I ≤ A ≤ β I` for some `0 < α ≤ β`. -/
private lemma exists_bounds_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ algebraMap ℝ _ α ≤ A ∧ A ≤ algebraMap ℝ _ β := by
  have hsa : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  have hfin := Matrix.finite_real_spectrum (A := A)
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < x := fun x hx ↦ hA.isStrictlyPositive.spectrum_pos hx
  rcases (spectrum ℝ A).eq_empty_or_nonempty with he | hne
  · refine ⟨1, 1, one_pos, le_rfl, (algebraMap_le_iff_le_spectrum (a := A) hsa).2 ?_,
      (le_algebraMap_iff_spectrum_le (a := A) hsa).2 ?_⟩ <;> simp [he]
  · obtain ⟨a, ha, hamin⟩ := Set.exists_min_image _ id hfin hne
    obtain ⟨b, hb, hbmax⟩ := Set.exists_max_image _ id hfin hne
    exact ⟨a, b, hpos a ha, hamin b hb, (algebraMap_le_iff_le_spectrum (a := A) hsa).2 hamin,
      (le_algebraMap_iff_spectrum_le (a := A) hsa).2 hbmax⟩

/-- Conjugating a scalar matrix: `X (c I) X = c X²`. -/
private lemma conj_algebraMap {X : Matrix n n ℝ} (c : ℝ) :
    X * algebraMap ℝ _ c * X = c • (X * X) := by
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]

/-- A weighted sum of scalar matrices is the scalar matrix of the weighted sum. -/
private lemma sum_smul_algebraMap {ι : Type*} [Fintype ι] (w x : ι → ℝ) :
    ∑ i, w i • algebraMap ℝ (Matrix n n ℝ) (x i) = algebraMap ℝ _ (∑ i, w i * x i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul]

/-- Existence of a solution of the Gaussian barycenter fixed-point equation: for nonnegative
weights `w` summing to one and positive definite real matrices `A i`, there is a positive definite
`S` with `S = ∑ i, w i • (S^{1/2} A i S^{1/2})^{1/2}`. If `α_i I ≤ A_i ≤ β_i I`, the map on the
right sends the order interval `[(∑ w_i √α_i)² I, (∑ w_i √β_i)² I]`, a nonempty compact convex
set of positive definite matrices, into itself, and Brouwer's fixed-point theorem applies. -/
theorem exists_posDef_eq_sum_smul_sqrt_mul_mul_sqrt {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (A : ι → Matrix n n ℝ) (hA : ∀ i, (A i).PosDef) :
    ∃ S : Matrix n n ℝ, S.PosDef ∧
      S = ∑ i, w i • CFC.sqrt (CFC.sqrt S * A i * CFC.sqrt S) := by
  choose α β hα hαβ hαA hAβ using fun i ↦ exists_bounds_of_posDef (hA i)
  set α' := ∑ i, w i * Real.sqrt (α i)
  set β' := ∑ i, w i * Real.sqrt (β i)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw1.trans_ne one_ne_zero)
  have hα' : 0 < α' := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i ↦ w i * Real.sqrt (α i))
      (fun i _ ↦ mul_nonneg (hw i) (Real.sqrt_nonneg _)) (Finset.mem_univ i₀))
    exact mul_pos ((hw i₀).lt_of_ne' hi₀) (Real.sqrt_pos.2 (hα i₀))
  have hαβ' : α' ≤ β' := Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hαβ i)) (hw i)
  set a := α' ^ 2
  set b := β' ^ 2
  have ha : 0 < a := by positivity
  have hab : a ≤ b := pow_le_pow_left₀ hα'.le hαβ' 2
  set K : Set (Matrix n n ℝ) := Icc (algebraMap ℝ _ a) (algebraMap ℝ _ b)
  set Φ : Matrix n n ℝ → Matrix n n ℝ :=
    fun S ↦ ∑ i, w i • CFC.sqrt (CFC.sqrt S * A i * CFC.sqrt S)
  have hnonneg : ∀ {c : ℝ}, 0 ≤ c → 0 ≤ algebraMap ℝ (Matrix n n ℝ) c := fun hc ↦ by
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_nonneg hc (Matrix.nonneg_iff_posSemidef.2 Matrix.PosSemidef.one)
  -- bounds for the inner matrices
  have hinner : ∀ S ∈ K, ∀ i, algebraMap ℝ _ (α i * a) ≤ CFC.sqrt S * A i * CFC.sqrt S ∧
      CFC.sqrt S * A i * CFC.sqrt S ≤ algebraMap ℝ _ (β i * b) := by
    rintro S ⟨haS, hSb⟩ i
    have hS0 : 0 ≤ S := (hnonneg ha.le).trans haS
    have hX : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
    have hXX : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS0
    constructor
    · calc algebraMap ℝ _ (α i * a) = α i • algebraMap ℝ (Matrix n n ℝ) a := by
            rw [Algebra.smul_def, map_mul]
        _ ≤ α i • S := smul_le_smul_of_nonneg_left haS (hα i).le
        _ = CFC.sqrt S * algebraMap ℝ _ (α i) * CFC.sqrt S := by rw [conj_algebraMap, hXX]
        _ ≤ _ := hX.conjugate_le_conjugate (hαA i)
    · calc CFC.sqrt S * A i * CFC.sqrt S ≤ CFC.sqrt S * algebraMap ℝ _ (β i) * CFC.sqrt S :=
            hX.conjugate_le_conjugate (hAβ i)
        _ = β i • S := by rw [conj_algebraMap, hXX]
        _ ≤ β i • algebraMap ℝ (Matrix n n ℝ) b :=
            smul_le_smul_of_nonneg_left hSb ((hα i).le.trans (hαβ i))
        _ = _ := by rw [Algebra.smul_def, map_mul]
  have hmaps : MapsTo Φ K K := by
    intro S hS
    have hlow : ∀ i, algebraMap ℝ _ (Real.sqrt (α i) * α') ≤
        CFC.sqrt (CFC.sqrt S * A i * CFC.sqrt S) := fun i ↦ by
      have h := hinner S hS i
      have h0 := (hnonneg (mul_nonneg (hα i).le ha.le)).trans h.1
      have := algebraMap_sqrt_le_sqrt h.1 h0
      rwa [Real.sqrt_mul (hα i).le, Real.sqrt_sq hα'.le] at this
    have hup : ∀ i, CFC.sqrt (CFC.sqrt S * A i * CFC.sqrt S) ≤
        algebraMap ℝ _ (Real.sqrt (β i) * β') := fun i ↦ by
      have h := hinner S hS i
      have h0 := (hnonneg (mul_nonneg (hα i).le ha.le)).trans h.1
      have := sqrt_le_algebraMap_sqrt h.2 h0
      rwa [Real.sqrt_mul ((hα i).le.trans (hαβ i)), Real.sqrt_sq (hα'.le.trans hαβ')] at this
    constructor
    · calc algebraMap ℝ _ a = ∑ i, w i • algebraMap ℝ (Matrix n n ℝ) (Real.sqrt (α i) * α') := by
            rw [sum_smul_algebraMap]; congr 1; simp only [a, α', sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ ↦ by ring
        _ ≤ Φ S := Finset.sum_le_sum fun i _ ↦ smul_le_smul_of_nonneg_left (hlow i) (hw i)
    · calc Φ S ≤ ∑ i, w i • algebraMap ℝ (Matrix n n ℝ) (Real.sqrt (β i) * β') :=
            Finset.sum_le_sum fun i _ ↦ smul_le_smul_of_nonneg_left (hup i) (hw i)
        _ = algebraMap ℝ _ b := by
            rw [sum_smul_algebraMap]; congr 1; simp only [b, β', sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ ↦ by ring
  -- continuity of `Φ` on `K`
  have hK0 : ∀ S ∈ K, 0 ≤ S := fun S hS ↦ (hnonneg ha.le).trans hS.1
  have hsq : ContinuousOn (cfc Real.sqrt : Matrix n n ℝ → Matrix n n ℝ) {A | A.IsHermitian} :=
    TauCeti.continuousOn_matrix_cfc Real.continuous_sqrt
  have hherm : ∀ S ∈ K, S.IsHermitian := fun S hS ↦ (hK0 S hS).isSelfAdjoint
  have hcont : ContinuousOn Φ K := by
    have h1 : ContinuousOn (fun S ↦ cfc Real.sqrt S) K := hsq.mono hherm
    have heq : EqOn Φ (fun S ↦ ∑ i, w i • cfc Real.sqrt
        (cfc Real.sqrt S * A i * cfc Real.sqrt S)) K := by
      intro S hS
      simp only [Φ]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have h0 := (hnonneg (mul_nonneg (hα i).le ha.le)).trans (hinner S hS i).1
      rw [CFC.sqrt_eq_real_sqrt _ h0, cfcₙ_eq_cfc, CFC.sqrt_eq_real_sqrt S (hK0 S hS),
        cfcₙ_eq_cfc]
    have hterm : ∀ i, ContinuousOn
        (fun S ↦ cfc Real.sqrt (cfc Real.sqrt S * A i * cfc Real.sqrt S)) K := by
      intro i
      refine hsq.comp ((h1.mul continuousOn_const).mul h1) fun S _ ↦ ?_
      have hX : IsSelfAdjoint (cfc Real.sqrt S) := cfc_predicate _ _
      exact ((hA i).isHermitian.isSelfAdjoint.conjugate_self hX : _)
    have hterm' : ∀ i, ContinuousOn
        (fun S ↦ w i • cfc Real.sqrt (cfc Real.sqrt S * A i * cfc Real.sqrt S)) K :=
      fun i ↦ (hterm i).const_smul (w i)
    exact (continuousOn_finsetSum Finset.univ fun i _ ↦ hterm' i).congr heq
  -- compactness and convexity of `K`
  have hKc : IsCompact K := by
    set P : Set (Matrix n n ℝ) := {S | ∀ i j, S i j ∈ Icc (-b) b}
    have hP : IsCompact P := by
      have h : IsCompact (Set.pi univ fun _ : n ↦ Set.pi univ fun _ : n ↦ Icc (-b) b) :=
        isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
      have hPeq : P = (Set.pi univ fun _ : n ↦ Set.pi univ fun _ : n ↦ Icc (-b) b :
          Set (Matrix n n ℝ)) := by
        ext S; exact ⟨fun h i _ j _ ↦ h i j, fun h i j ↦ h i trivial j trivial⟩
      rw [hPeq]; exact h
    have hsub : K ⊆ P := fun S hS i j ↦
      abs_le.1 (abs_apply_le_of_nonneg_of_le_algebraMap (hK0 S hS) hS.2 i j)
    exact hP.of_isClosed_subset isClosed_Icc hsub
  have hKne : K.Nonempty := ⟨algebraMap ℝ _ a, le_rfl, by
    rw [← sub_nonneg, ← map_sub]; exact hnonneg (sub_nonneg.2 hab)⟩
  let _ : NormedAddCommGroup (Matrix n n ℝ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix n n ℝ) := Matrix.normedSpace
  obtain ⟨S, hSK, hfix⟩ := TauCeti.brouwerFixedPoint_compactConvex_continuousOn hKc
    (convex_Icc _ _) hKne hcont hmaps
  refine ⟨S, ?_, hfix.symm⟩
  have h1 : (S - algebraMap ℝ _ a).PosSemidef := Matrix.le_iff.1 hSK.1
  have h2 : (algebraMap ℝ (Matrix n n ℝ) a).PosDef := by
    rw [Algebra.algebraMap_eq_smul_one]; exact Matrix.PosDef.one.smul ha
  simpa using h2.add_posSemidef h1

end CKSD
