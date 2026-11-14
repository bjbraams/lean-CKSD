module

public import CKSD.LinearModels.Basic
public import CKSD.LinearModels.Multivariate
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import Mathlib.FieldTheory.Finite.GaloisField


/-!
# Optimal and combinatorial experimental design

Results on the design of experiments: approximate D-optimal designs on a finite design space,
randomization tests, balanced incomplete block designs, and mutually orthogonal Latin squares.

## Main definitions

* `CKSD.designInformationMatrix`: the information matrix `M(a) = ∑ᵢ aᵢ fᵢ fᵢᵀ` of a design
  `a` (weights on a finite design space with regression vectors `fᵢ`).
* `CKSD.randomizationPValue`: the randomization p-value `∑_{j : T_j ≥ T_i} w_j` of the
  observed arrangement `i` under randomization weights `w`.

## Main results

* `CKSD.kiefer_wolfowitz_equivalence`: a design maximizes `det M(a)` if and only if the
  standardized variance `fᵢᵀ M(w)⁻¹ fᵢ` is at most `p` everywhere, with equality on the support
  (Kiefer–Wolfowitz equivalence theorem).
* `CKSD.sum_ite_randomization_p_value_le`: randomization p-values are conservative,
  `P(p ≤ α) ≤ α`, ties included.
* `CKSD.fisher_inequality`: a balanced incomplete block design has at least as many blocks as
  points (Fisher's inequality).
* `CKSD.card_le_sub_one_of_orthogonal_latin_squares`: at most `s - 1` mutually orthogonal Latin
  squares of order `s ≥ 2` exist, and `CKSD.exists_orthogonal_latin_squares_of_is_prime_pow`: for a
  prime power `s` this bound is attained.

The Kiefer–Wolfowitz theorem uses Mathlib's matrix determinant lemma
`Matrix.det_add_replicateCol_mul_replicateRow` and the Gaussian likelihood inequality
`CKSD.log_det_add_card_le_log_det_add_trace_mul_inv`. The proof of Fisher's inequality uses
Mathlib's rank bounds `Matrix.rank_mul_le_left` and `Matrix.rank_le_width`; the complete families of orthogonal Latin squares use Mathlib's
`GaloisField` and its cardinality `GaloisField.card`.

## References

* J. Kiefer and J. Wolfowitz, *The equivalence of two extremum problems*, Canad. J. Math. 12
  (1960).
* R. A. Fisher, *An examination of the different possible solutions of a problem in incomplete
  blocks*, Ann. Eugenics 10 (1940).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

open scoped CKSD

attribute [local instance] Classical.propDecidable

/-- The information matrix `M(a) = ∑ᵢ aᵢ fᵢ fᵢᵀ` of a design with weights `a` on a finite
design space whose points have regression vectors `f`. -/
def designInformationMatrix {ι : Type*} [Fintype ι] {p : ℕ} (f : ι → EuclideanSpace ℝ (Fin p))
    (a : ι → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k ↦ ∑ i, a i * f i j * f i k

open Matrix in
/-- The information matrix is the weighted sum `∑ᵢ aᵢ fᵢ fᵢᵀ` of rank-one matrices. -/
theorem design_information_matrix_eq_sum {ι : Type*} [Fintype ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (a : ι → ℝ) :
    designInformationMatrix f a = ∑ i, a i • vecMulVec (f i : Fin p → ℝ) (f i : Fin p → ℝ) := by
  ext j k
  simp [designInformationMatrix, Matrix.sum_apply, vecMulVec_apply, mul_assoc]

open Matrix in
/-- `tr(M(a) N) = ∑ᵢ aᵢ fᵢᵀ N fᵢ`. -/
theorem trace_design_information_matrix_mul {ι : Type*} [Fintype ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (a : ι → ℝ) (N : Matrix (Fin p) (Fin p) ℝ) :
    (designInformationMatrix f a * N).trace = ∑ i, a i * matrixQuadraticForm N (f i) := by
  simp only [matrix_quadratic_form_eq_dot_product, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    designInformationMatrix, Matrix.of_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun i _ ↦ ?_
  ring

open Matrix in
/-- The information matrix of a design with nonnegative weights is positive semidefinite. -/
theorem pos_semidef_design_information_matrix {ι : Type*} [Fintype ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (designInformationMatrix f a).PosSemidef := by
  rw [design_information_matrix_eq_sum]
  refine posSemidef_sum _ fun i _ ↦ ?_
  have h := posSemidef_vecMulVec_self_star (f i : Fin p → ℝ)
  rw [star_trivial] at h
  exact h.smul (ha i)

open Matrix in
/-- Sufficiency in the Kiefer–Wolfowitz theorem: if `fᵢᵀ M(w)⁻¹ fᵢ ≤ p` everywhere, then
`det M(a) ≤ det M(w)` for every probability design `a`, by the Gaussian likelihood inequality
`log det S + p ≤ log det C + tr(S C⁻¹)`. -/
private theorem det_design_information_matrix_le_of_forall_le {ι : Type*} [Fintype ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (w : ι → ℝ) (hM : (designInformationMatrix f w).PosDef)
    (hle : ∀ i, matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f i) ≤ p)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) :
    (designInformationMatrix f a).det ≤ (designInformationMatrix f w).det := by
  by_cases hdet : (designInformationMatrix f a).det = 0
  · rw [hdet]
    exact hM.det_pos.le
  have hpd := (pos_semidef_design_information_matrix f a ha).posDef_iff_det_ne_zero.2 hdet
  have h := log_det_add_card_le_log_det_add_trace_mul_inv _ _ hpd hM
  rw [trace_design_information_matrix_mul] at h
  have hsum : ∑ i, a i * matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f i) ≤ p :=
    calc _ ≤ ∑ i, a i * (p : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) (ha i)
      _ = p := by rw [← Finset.sum_mul, ha1, one_mul]
  exact (Real.log_le_log_iff hpd.det_pos hM.det_pos).1 (by linarith)
open Matrix in
/-- Necessity in the Kiefer–Wolfowitz theorem: at a D-optimal design `w`, moving the mass `t`
towards a design point `i` gives `det M = (1 - t)^{p-1} (1 + (q - 1) t) det M(w)` with
`q = fᵢᵀ M(w)⁻¹ fᵢ` (matrix determinant lemma), which exceeds `det M(w)` for small `t > 0`
unless `q ≤ p`. -/
private theorem matrix_quadratic_form_inv_le_of_forall_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hM : (designInformationMatrix f w).PosDef)
    (hmax : ∀ a, (∀ i, 0 ≤ a i) → (∑ i, a i = 1) →
        (designInformationMatrix f a).det ≤ (designInformationMatrix f w).det) (i : ι) :
    matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f i) ≤ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [matrix_quadratic_form_eq_dot_product]
  set M := designInformationMatrix f w with hMdef
  set q := matrixQuadraticForm M⁻¹ (f i) with hqdef
  by_contra hlt
  push Not at hlt
  have hP1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set D := 2 * ((p : ℝ) - 1) * (q - 1) + 2 * (q - p) with hDdef
  have hD : 0 < D := by nlinarith
  set t := (q - p) / D with htdef
  have ht0 : 0 < t := div_pos (by linarith) hD
  have htD : t * D = q - p := div_mul_cancel₀ _ hD.ne'
  have ht1 : t ≤ 1 / 2 := by nlinarith
  set a : ι → ℝ := fun j ↦ (1 - t) * w j + t * (if j = i then 1 else 0) with hadef
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    have := hw j
    simp only [hadef]
    split_ifs <;> nlinarith
  have ha1 : ∑ j, a j = 1 := by
    simp [hadef, Finset.sum_add_distrib, ← Finset.mul_sum, hw1]
  have hMa : designInformationMatrix f a = (1 - t) • M +
      replicateCol Unit (t • (f i : Fin p → ℝ)) * replicateRow Unit (f i : Fin p → ℝ) := by
    ext j k
    simp [hMdef, designInformationMatrix, hadef, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
      Matrix.mul_apply]
    congr 1
    · exact Finset.sum_congr rfl fun x _ ↦ by ring
    · ring
  have h := hmax a ha ha1
  have h1t : (1 - t) ≠ 0 := by linarith
  have hMu : IsUnit M.det := hM.isUnit.map Matrix.detMonoidHom
  have hdetA : IsUnit ((1 - t) • M).det := by
    rw [det_smul]
    exact (IsUnit.pow _ (Ne.isUnit h1t)).mul hMu
  have hinv : ((1 - t) • M)⁻¹ = (1 - t)⁻¹ • M⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h1t, one_smul,
      Matrix.nonsing_inv_mul _ hMu]
  have hq' : (f i : Fin p → ℝ) ⬝ᵥ (M⁻¹ *ᵥ (f i : Fin p → ℝ)) = q := by
    rw [hqdef, matrix_quadratic_form_eq_dot_product, dotProduct_comm]
  have hdetMa : (designInformationMatrix f a).det =
      (1 - t) ^ p * M.det * (1 + (1 - t)⁻¹ * t * q) := by
    rw [hMa, det_add_replicateCol_mul_replicateRow hdetA, hinv, det_smul, Fintype.card_fin,
      det_unique (n := Unit), ← hq']
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, dotProduct, mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [hdetMa] at h
  have hdetpos := hM.det_pos
  have hpow : (1 - t) ^ p = (1 - t) ^ (p - 1) * (1 - t) := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hB : 1 - ((p : ℝ) - 1) * t ≤ (1 - t) ^ (p - 1) := by
    have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -t) (p - 1)
    rw [Nat.cast_sub hp, Nat.cast_one, ← sub_eq_add_neg] at hb
    linarith
  have hE : (1 - t) ^ p * (1 + (1 - t)⁻¹ * t * q) = (1 - t) ^ (p - 1) * (1 + (q - 1) * t) := by
    rw [hpow]
    field_simp
    ring
  have h' : (1 - t) ^ (p - 1) * (1 + (q - 1) * t) ≤ 1 := by
    rw [← hE]
    have := le_of_mul_le_mul_left (a := M.det) (by nlinarith) hdetpos
    nlinarith
  have hq1 : 0 ≤ (q - 1) * t := mul_nonneg (by linarith) ht0.le
  have h'' : (1 - ((p : ℝ) - 1) * t) * (1 + (q - 1) * t) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hB (by linarith)).trans h'
  have hk : ((p : ℝ) - 1) * (q - 1) * t = (q - p) * (1 / 2 - t) := by
    rw [hDdef] at htD
    linarith
  have h3 : t * ((q - p) - ((p : ℝ) - 1) * (q - 1) * t) ≤ 0 := by nlinarith
  have h4 : (q - p) - ((p : ℝ) - 1) * (q - 1) * t ≤ 0 :=
    nonpos_of_mul_nonpos_right (by linarith) ht0
  rw [hk] at h4
  nlinarith

/-- GAPS 105.37, Kiefer–Wolfowitz equivalence for a finite design space: a probability design
`w` with nonsingular information matrix maximizes `det M(a)` over all probability designs if and
only if `fᵢᵀ M(w)⁻¹ fᵢ ≤ p` at every design point, with equality at the points of positive
weight. -/
theorem kiefer_wolfowitz_equivalence {ι : Type*} [Fintype ι] {p : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin p)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hM : (designInformationMatrix f w).PosDef) :
    (∀ a, (∀ i, 0 ≤ a i) → (∑ i, a i = 1) →
        (designInformationMatrix f a).det ≤ (designInformationMatrix f w).det) ↔
      (∀ i, matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f i) ≤ p) ∧
        ∀ i, 0 < w i → matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f i) = p := by
  constructor
  · intro hmax
    have hle := matrix_quadratic_form_inv_le_of_forall_det_le f w hw hw1 hM hmax
    refine ⟨hle, fun i hi ↦ ?_⟩
    have htr := trace_design_information_matrix_mul f w (designInformationMatrix f w)⁻¹
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM.isUnit),
      Matrix.trace_one, Fintype.card_fin] at htr
    have hzero : ∑ j, w j * ((p : ℝ) -
        matrixQuadraticForm (designInformationMatrix f w)⁻¹ (f j)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, ← htr,
        sub_self]
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      mul_nonneg (hw j) (sub_nonneg.2 (hle j))).1 hzero i (Finset.mem_univ _)
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · rintro ⟨hle, -⟩ a ha ha1
    exact det_design_information_matrix_le_of_forall_le f w hM hle a ha ha1

/-- The randomization p-value of arrangement `i`: the total randomization weight of the
arrangements `j` whose statistic `T j` is at least `T i`. -/
def randomizationPValue {ι : Type*} [Fintype ι] (w T : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, if T i ≤ T j then w j else 0

/-- GAPS 105.38, conservative finite randomization p-values, including ties: for nonnegative
randomization weights `w` (of total mass at most one, in applications) and `0 ≤ α`, the total
weight of the arrangements whose randomization p-value is at most `α` is at most `α`. -/
theorem sum_ite_randomization_p_value_le {ι : Type*} [Fintype ι] (w T : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {α : ℝ} (hα : 0 ≤ α) :
    (∑ i, if randomizationPValue w T i ≤ α then w i else 0) ≤ α := by
  classical
  set p := randomizationPValue w T
  by_cases hs : ({i | p i ≤ α} : Set ι).Nonempty
  · obtain ⟨i, hi, hmin⟩ :=
      Set.exists_min_image {i | p i ≤ α} T (Set.toFinite _) hs
    calc
      (∑ j, if p j ≤ α then w j else 0) ≤
          ∑ j, if T i ≤ T j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : p j ≤ α
        · simp [hj, hmin j hj]
        · simp only [ite_eq_right hj]
          exact ite_nonneg (hw j) (le_refl 0)
      _ = p i := rfl
      _ ≤ α := hi
  · have hz : (∑ i, if p i ≤ α then w i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi ↦ hs ⟨i, hi⟩)
    rw [hz]
    exact hα

/-- GAPS 105.42, Fisher's inequality: in a balanced incomplete block design on `v` points with
`b` blocks of size `k < v`, every point in `r > 0` blocks and every pair of distinct points in
`ell` blocks, there are at least as many blocks as points, `v ≤ b`. -/
theorem fisher_inequality
    (v b k r ell : ℕ) (hkv : k < v)
    (hr : 0 < r) (B : Fin b → Finset (Fin v))
    (hsize : ∀ j, (B j).card = k)
    (hrep : ∀ i, (Finset.univ.filter fun j ↦ i ∈ B j).card = r)
    (hpair : ∀ i i', i ≠ i' → (Finset.univ.filter fun j ↦ i ∈ B j ∧ i' ∈ B j).card = ell) :
    v ≤ b := by
  classical
  -- `ell < r`: some block through a point misses another point
  have hlt : ell < r := by
    let i : Fin v := ⟨0, by omega⟩
    obtain ⟨j₀, hj₀⟩ : (Finset.univ.filter fun j ↦ i ∈ B j).Nonempty := by
      rw [← Finset.card_pos, hrep]; exact hr
    have hj₀' : i ∈ B j₀ := (Finset.mem_filter.1 hj₀).2
    obtain ⟨i', -, hi'⟩ : ∃ i' ∈ Finset.univ, i' ∉ B j₀ := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset (Fin v)) ⊆ B j₀ := fun x _ ↦ hcon x (Finset.mem_univ x)
      have := Finset.card_le_card this
      simp [hsize] at this
      omega
    have hii' : i ≠ i' := fun h ↦ hi' (h ▸ hj₀')
    rw [← hpair i i' hii', ← hrep i]
    refine Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.1⟩
    · have := hsub hj₀
      simp only [Finset.mem_filter] at this
      exact hi' this.2.2
  let N : Matrix (Fin v) (Fin b) ℝ := Matrix.of fun i j ↦ if i ∈ B j then 1 else 0
  have hM : ∀ i i', (N * N.transpose) i i' = if i = i' then (r : ℝ) else ell := by
    intro i i'
    simp only [N, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_ite, mul_one,
      mul_zero]
    split_ifs with h
    · subst h
      rw [← hrep i]
      simp [Finset.sum_ite, Finset.filter_filter]
    · rw [← hpair i i' h]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one, Finset.filter_filter]
      congr 2
      ext j
      simp [and_comm]
  have hdet : (N * N.transpose).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ i, ((r : ℝ) - ell) * x i + ell * ∑ i', x i' = 0 := by
      intro i
      have := congrFun hx i
      simp only [Matrix.mulVec, dotProduct, hM, Pi.zero_apply] at this
      have e : ∀ i', (if i = i' then (r : ℝ) else ell) * x i' =
          ell * x i' + if i = i' then ((r : ℝ) - ell) * x i' else 0 := by
        intro i'; split_ifs <;> ring
      simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        ← Finset.mul_sum] at this
      linarith
    have hpos : (0 : ℝ) < r - ell := by
      have : (ell : ℝ) < r := by exact_mod_cast hlt
      linarith
    have hsum : ∑ i', x i' = 0 := by
      generalize hS : ∑ i', x i' = S at hrow
      have hconst : ∀ i, x i = -(ell * S) / (r - ell) := by
        intro i
        field_simp
        linarith [hrow i]
      have : ∑ i', x i' = ∑ _i : Fin v, (-(ell * S) / (r - ell) : ℝ) :=
        Finset.sum_congr rfl fun i _ ↦ hconst i
      rw [hS] at this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      have hv0 : (0 : ℝ) ≤ v * ell := by positivity
      field_simp at this
      nlinarith
    apply hx0
    funext i
    have := hrow i
    rw [hsum, mul_zero, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hpos.ne'
  have hrank : (N * N.transpose).rank = v := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)),
      Fintype.card_fin]
  calc v = (N * N.transpose).rank := hrank.symm
    _ ≤ N.rank := Matrix.rank_mul_le_left _ _
    _ ≤ b := Matrix.rank_le_width N

/-- GAPS 105.44, the upper bound on a family of mutually orthogonal Latin squares: there are at
most `s - 1` pairwise orthogonal Latin squares of order `s ≥ 2`. -/
theorem card_le_sub_one_of_orthogonal_latin_squares (s k : ℕ) (hs : 2 ≤ s)
    (L : Fin k → Fin s → Fin s → Fin s)
    (hLatin : ∀ i, IsLatinSquare (L i))
    (hortho : ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j)) : k ≤ s - 1 := by
  classical
  let r₀ : Fin s := ⟨0, by omega⟩
  let r₁ : Fin s := ⟨1, by omega⟩
  have h01 : r₀ ≠ r₁ := by simp [r₀, r₁, Fin.ext_iff]
  -- the column of row `r₀` carrying the symbol in cell `(r₁, r₀)`
  let t : Fin k → Fin s := fun i ↦
    (Equiv.ofBijective (L i r₀) ((hLatin i).1 r₀)).symm (L i r₁ r₀)
  have ht : ∀ i, L i r₀ (t i) = L i r₁ r₀ := fun i ↦
    Equiv.ofBijective_apply_symm_apply (L i r₀) ((hLatin i).1 r₀) _
  have hne : ∀ i, t i ≠ r₀ := by
    intro i h
    have := ht i
    rw [h] at this
    exact h01 (((hLatin i).2 r₀).1 this)
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne'
    have h := hortho i j hne' (a₁ := (r₀, t i)) (a₂ := (r₁, r₀)) (by
      simp only [Prod.mk.injEq]
      exact ⟨ht i, hij ▸ ht j⟩)
    exact h01 (congrArg Prod.fst h)
  have := Finset.card_le_card_of_injOn t (s := Finset.univ) (t := Finset.univ.erase r₀)
    (fun i _ ↦ Finset.mem_erase.2 ⟨hne i, Finset.mem_univ _⟩) hinj.injOn
  simpa [Finset.card_erase_of_mem] using this

/-- Over a finite field `F` identified with `Fin s`, the squares `(x, y) ↦ a x + y` for the
nonzero elements `a` form a complete family of mutually orthogonal Latin squares. -/
theorem exists_orthogonal_latin_squares_of_equiv {F : Type*} [Field F] {t : ℕ}
    (e : F ≃ Fin (t + 1)) :
    ∃ L : Fin t → Fin (t + 1) → Fin (t + 1) → Fin (t + 1),
      (∀ i, IsLatinSquare (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j) := by
  let a : Fin t → F := fun i ↦ e.symm ((e 0).succAbove i)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have := congrArg e h
    simp only [a, Equiv.apply_symm_apply] at this
    exact Fin.succAbove_ne _ _ this
  have ha_inj : Function.Injective a := fun i j h ↦
    Fin.succAbove_right_injective (e.symm.injective h)
  refine ⟨fun i x y ↦ e (a i * e.symm x + e.symm y), fun i ↦ ⟨fun x ↦ ?_, fun y ↦ ?_⟩,
    fun i j hij ↦ ?_⟩
  · refine Finite.injective_iff_bijective.1 fun y y' h ↦ ?_
    simpa using h
  · refine Finite.injective_iff_bijective.1 fun x x' h ↦ ?_
    simpa [ha i] using h
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨h₁, h₂⟩ := h
    have hx : e.symm x = e.symm x' := by
      have : (a i - a j) * (e.symm x - e.symm x') = 0 := by linear_combination h₁ - h₂
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (ha_inj (sub_eq_zero.1 h0)) hij
      · exact sub_eq_zero.1 h0
    have hy : e.symm y = e.symm y' := by
      rw [hx] at h₁
      exact add_left_cancel h₁
    simp only [Prod.mk.injEq]
    exact ⟨e.symm.injective hx, e.symm.injective hy⟩

/-- GAPS 105.44, existence of a complete family at prime-power orders: for a prime power `s`
there are `s - 1` pairwise orthogonal Latin squares of order `s`. -/
theorem exists_orthogonal_latin_squares_of_is_prime_pow (s : ℕ) (hs : IsPrimePow s) :
    ∃ L : Fin (s - 1) → Fin s → Fin s → Fin s,
      (∀ i, IsLatinSquare (L i)) ∧ ∀ i j, i ≠ j → OrthogonalLatinSquares (L i) (L j) := by
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff s).1 hs
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn.ne'
  obtain ⟨t, ht⟩ : ∃ t, p ^ n = t + 1 :=
    ⟨p ^ n - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)).symm⟩
  have e : GaloisField p n ≃ Fin (t + 1) := (Finite.equivFin _).trans (finCongr (hcard.trans ht))
  obtain ⟨L, hL⟩ := exists_orthogonal_latin_squares_of_equiv e
  rw [ht, Nat.add_sub_cancel]
  exact ⟨L, hL⟩

end CKSD
