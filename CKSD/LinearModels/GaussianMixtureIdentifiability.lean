module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Linear independence of Gaussian exponentials

The exponential functions attached to distinct means and Hermitian covariance matrices are
linearly independent. A nonzero multivariate polynomial selects a line on which every Gaussian
parameter pair is distinct. On that line, lexicographic comparison of the quadratic and linear
coefficients isolates the largest term at infinity.

This supplies the algebraic uniqueness step for finite Gaussian-mixture identifiability.
Polynomial separation uses Mathlib's `MvPolynomial.funext`, and covariance recovery uses
Mathlib's symmetric linear-map interface and polarization of quadratic forms.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology BigOperators RealInnerProductSpace

namespace CKSD

/-- A quadratic exponential tends to zero when its coefficient pair is lexicographically negative. -/
theorem tendsto_exp_quadratic_atTop_zero {a b : ℝ}
    (h : a < 0 ∨ a = 0 ∧ b < 0) :
    Tendsto (fun t : ℝ ↦ Real.exp (a*t^2+b*t)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  rcases h with ha | ⟨rfl, hb⟩
  · have hlin : Tendsto (fun t : ℝ ↦ a*t+b) atTop atBot :=
      (tendsto_id.const_mul_atTop_of_neg ha).atBot_add tendsto_const_nhds
    convert tendsto_id.atTop_mul_atBot₀ hlin using 1
    funext t
    simp only [id_eq]
    ring
  · simpa using tendsto_id.const_mul_atTop_of_neg hb

/-- Distinct quadratic exponentials are linearly independent: normalize by the largest
lexicographic exponent among the nonzero coefficients and take the limit at infinity. -/
theorem coefficients_eq_zero_of_sum_exp_quadratic_eq_zero {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : Function.Injective fun i ↦ (a i, b i))
    (heq : ∀ t : ℝ, ∑ i, c i * Real.exp (a i*t^2+b i*t) = 0) : ∀ i, c i = 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i₀, hi₀⟩ := h
  let s := Finset.univ.filter fun i ↦ c i ≠ 0
  have hs : s.Nonempty := ⟨i₀, by simp [s,hi₀]⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun i ↦ toLex (a i,b i)) hs
  have hci : c i ≠ 0 := (Finset.mem_filter.1 hi).2
  have hjlt (j : ι) (hj : j ∈ s) (hne : j ≠ i) :
      a j < a i ∨ a j = a i ∧ b j < b i := by
    have hle := hmax j hj
    have hne' : toLex (a j, b j) ≠ toLex (a i,b i) := by
      intro he
      exact hne (hab (congrArg ofLex he))
    exact Prod.Lex.lt_iff.1 (lt_of_le_of_ne hle hne')
  have hlim (j : ι) : Tendsto
      (fun t : ℝ ↦ c j * Real.exp ((a j - a i)*t^2+(b j-b i)*t)) atTop
      (𝓝 (if j = i then c i else 0)) := by
    by_cases hji : j = i
    · subst j
      simp only [sub_self, zero_mul, add_zero, Real.exp_zero, mul_one, ↓reduceIte]
      exact tendsto_const_nhds
    by_cases hj : j ∈ s
    · have hlt := hjlt j hj hji
      have hlt' : a j - a i < 0 ∨ a j-a i = 0 ∧ b j - b i < 0 := by
        rcases hlt with ha | ⟨ha,hb⟩
        · exact Or.inl (sub_neg.2 ha)
        · exact Or.inr ⟨sub_eq_zero.2 ha, sub_neg.2 hb⟩
      simpa only [ite_eq_right hji, mul_zero] using
        (tendsto_exp_quadratic_atTop_zero hlt').const_mul (c j)
    · have hcj : c j = 0 := by simpa [s] using hj
      simp only [hcj, zero_mul, ite_eq_right hji]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum Finset.univ (fun j _ ↦ hlim j)
  have hsumeq (t : ℝ) : ∑ j, c j * Real.exp ((a j-a i)*t^2+(b j-b i)*t) = 0 := by
    have hp (j : ι) : Real.exp ((a j-a i)*t^2+(b j-b i)*t) =
        Real.exp (a j*t^2+b j*t) / Real.exp (a i*t^2+b i*t) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    simp_rw [hp, ← mul_div_assoc]
    rw [← Finset.sum_div, heq, zero_div]
  have hzero : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 (c i)) := by
    simpa only [hsumeq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hsum
  exact hci (tendsto_nhds_unique hzero tendsto_const_nhds)

end CKSD

namespace CKSD

/-- The polynomial recording the linear mean term and the quadratic covariance term. -/
noncomputable def gaussianParameterPolynomial {d : ℕ} (m : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  (∑ i, MvPolynomial.C (m i) * MvPolynomial.X i) +
    ∑ i, ∑ j, MvPolynomial.C (S i j) * MvPolynomial.X i * MvPolynomial.X j

/-- Evaluating the Gaussian parameter polynomial gives its mean and covariance quadratic form. -/
theorem eval_gaussianParameterPolynomial {d : ℕ} (m x : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial.eval (fun i ↦ x i) (gaussianParameterPolynomial m S) =
      ⟪x,m⟫ + ⟪x,S.toEuclideanLin x⟫ := by
  simp only [gaussianParameterPolynomial, map_add, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end CKSD

namespace CKSD

/-- The parameter polynomial determines the mean and every Hermitian covariance matrix.
The odd part determines the mean, and polarization determines the covariance. -/
theorem gaussianParameterPolynomial_injective {d : ℕ}
    (m n : EuclideanSpace ℝ (Fin d)) (S T : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hp : gaussianParameterPolynomial m S = gaussianParameterPolynomial n T) : m = n ∧ S = T := by
  have he (x : EuclideanSpace ℝ (Fin d)) :
      ⟪x,m⟫ + ⟪x,S.toEuclideanLin x⟫ = ⟪x,n⟫ + ⟪x,T.toEuclideanLin x⟫ := by
    simpa only [eval_gaussianParameterPolynomial] using congrArg (MvPolynomial.eval (fun i ↦ x i)) hp
  have hm (x : EuclideanSpace ℝ (Fin d)) : ⟪x,m⟫ = ⟪x,n⟫ := by
    have hneg := he (-x)
    simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at hneg
    linarith [he x]
  have hmn : m = n := by
    apply ext_inner_left ℝ
    exact hm
  refine ⟨hmn, ?_⟩
  have hq (x : EuclideanSpace ℝ (Fin d)) : ⟪x,S.toEuclideanLin x⟫ = ⟪x,T.toEuclideanLin x⟫ := by
    linarith [he x, hm x]
  have hsymS : LinearMap.IsSymmetric S.toEuclideanLin := Matrix.isSymmetric_toEuclideanLin_iff.2 hS
  have hsymT : LinearMap.IsSymmetric T.toEuclideanLin := Matrix.isSymmetric_toEuclideanLin_iff.2 hT
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  have hxy := hq (x+y)
  simp only [map_add, inner_add_left, inner_add_right] at hxy
  have hsy : ⟪y,S.toEuclideanLin x⟫ = ⟪x,S.toEuclideanLin y⟫ := by
    rw [← hsymS x y, real_inner_comm]
  have hty : ⟪y,T.toEuclideanLin x⟫ = ⟪x,T.toEuclideanLin y⟫ := by
    rw [← hsymT x y, real_inner_comm]
  rw [hsy,hty] at hxy
  linarith [hq x,hq y]

end CKSD

namespace CKSD

/-- A finite family of distinct real multivariate polynomials has an evaluation at which all
values are distinct, since the product of their nonzero pairwise differences is nonzero. -/
theorem exists_injective_eval_mvPolynomial {ι σ : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℝ) (hp : Function.Injective p) :
    ∃ x : σ → ℝ, Function.Injective fun i ↦ MvPolynomial.eval x (p i) := by
  classical
  let s : Finset (ι × ι) := Finset.univ.filter fun ij ↦ ij.1 ≠ ij.2
  let Q := ∏ ij ∈ s, (p ij.1 - p ij.2)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro ij hij
    exact sub_ne_zero.2 (fun he ↦ (Finset.mem_filter.1 hij).2 (hp he))
  obtain ⟨x, hx⟩ : ∃ x : σ → ℝ, MvPolynomial.eval x Q ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using h x
  refine ⟨x, fun i j hij ↦ ?_⟩
  by_contra hne
  have hx' : (∏ ij ∈ s, MvPolynomial.eval x (p ij.1 - p ij.2)) ≠ 0 := by
    simpa only [Q, map_prod] using hx
  have hfactor := Finset.prod_ne_zero_iff.1 hx' (i,j) (by simp [s,hne])
  apply hfactor
  rw [map_sub]
  exact sub_eq_zero.2 hij

end CKSD

namespace CKSD

/-- Distinct means and Hermitian covariance matrices give linearly independent Gaussian
exponentials. A polynomial evaluation selects a separating line, and quadratic exponential
growth proves linear independence on that line. -/
theorem linearIndependent_gaussianExponents {ι : Type*} {d : ℕ}
    (m : ι → EuclideanSpace ℝ (Fin d)) (S : ι → Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ i, (S i).IsHermitian) (hinj : Function.Injective fun i ↦ (m i,S i)) :
    LinearIndependent ℝ (fun i ↦ fun v : EuclideanSpace ℝ (Fin d) ↦
      Real.exp (⟪v,m i⟫ + ⟪v,(S i).toEuclideanLin v⟫ / 2)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hrel i hi
  let p : s → MvPolynomial (Fin d) ℝ := fun j ↦ gaussianParameterPolynomial (m j) (S j)
  have hp : Function.Injective p := by
    intro j k he
    apply Subtype.ext
    obtain ⟨hm,hmat⟩ := gaussianParameterPolynomial_injective (m j) (m k) (S j) (S k)
      (hS j) (hS k) he
    exact hinj (Prod.ext hm hmat)
  obtain ⟨x,hx⟩ := exists_injective_eval_mvPolynomial p hp
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  let a : s → ℝ := fun j ↦ ⟪v,(S j).toEuclideanLin v⟫ / 2
  let b : s → ℝ := fun j ↦ ⟪v,m j⟫
  have heval (j : s) : MvPolynomial.eval x (p j) = b j + 2 * a j := by
    have h := eval_gaussianParameterPolynomial (m j) v (S j)
    change MvPolynomial.eval x (p j) = _ at h
    rw [h]
    simp only [a,b]
    ring
  have hab : Function.Injective fun j : s ↦ (a j,b j) := by
    intro j k he
    apply hx
    change MvPolynomial.eval x (p j) = MvPolynomial.eval x (p k)
    rw [heval,heval]
    rw [show a j = a k from congrArg Prod.fst he, show b j = b k from congrArg Prod.snd he]
  have heq (t : ℝ) : ∑ j : s, c j * Real.exp (a j * t^2+b j*t) = 0 := by
    have ht := congrFun hrel (t • v)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht
    rw [← Finset.sum_coe_sort] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    congr 1
    simp only [inner_smul_left, inner_smul_right, map_smul, conj_trivial, a,b]
    ring
  exact coefficients_eq_zero_of_sum_exp_quadratic_eq_zero a b (fun j : s ↦ c j) hab heq ⟨i,hi⟩

end CKSD
