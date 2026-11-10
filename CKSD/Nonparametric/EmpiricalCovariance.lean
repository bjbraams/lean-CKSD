module

public import CKSD.Nonparametric.EmpiricalCovariance.Basic

/-!
# Empirical covariance and simple leading principal components

The covariance uses the empirical mean and divisor `n`. The results concern a simple leading
component in finite-dimensional Euclidean space under a fourth-moment hypothesis; they do not
assert the infinite-dimensional spectral expansion of GAPS 103.30. The spectral gap is specified
by a Rayleigh bound on the orthogonal complement, without choosing an ordering of eigenbases.
Population covariance reuses `TauCeti.covMatrix`.

## Main definitions

* `CKSD.empiricalCovarianceMatrix X n ω`: the empirical covariance with divisor `n`.
* `CKSD.leadingRayleighValue A`: `sup_{‖u‖ = 1} ⟪u, A u⟫`, the largest eigenvalue of a symmetric
  matrix.

## Main results

* `CKSD.leading_empirical_covariance_eigenvalue_asymptotics`,
  `CKSD.isBoundedInProbability_leading_empirical_eigenvector_error`: the root-`n` asymptotics of
  a simple leading eigenvalue and eigenvector. The proofs combine a deterministic perturbation
  bound for the leading Rayleigh value and its maximizer (in the entrywise `ℓ¹` norm of
  `Σ̂ₙ - Σ`) with the entrywise root-`n` consistency of `Σ̂ₙ`, the central limit theorem for
  `⟪X - E X, v⟫²`, and Slutsky's lemma (`CKSD.Asymptotics.Basic`).

Source: GAPS 103.30.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.L2Operator

namespace CKSD

/-- Largest Rayleigh value of a real matrix; the intended spectral interpretation is symmetric.
The empty unit sphere in dimension zero gives the usual real `sSup ∅ = 0` convention. -/
def leadingRayleighValue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
    r = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)}

/-- The bilinear form of a matrix is bounded by its entrywise `ℓ¹` norm:
`|⟪x, A y⟫| ≤ (∑ |Aᵢⱼ|) ‖x‖ ‖y‖`. -/
private theorem abs_inner_toEuclideanCLM_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A y)| ≤ entrySum A * (‖x‖ * ‖y‖) := by
  rw [inner_toEuclideanCLM_eq_sum, entrySum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul, abs_mul]
  have hx : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have hy : |y j| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y j
  calc |x i| * |A i j| * |y j| = |A i j| * (|x i| * |y j|) := by ring
    _ ≤ |A i j| * (‖x‖ * ‖y‖) := by gcongr

/-- For a symmetric matrix, `⟪x, A y⟫ = ⟪y, A x⟫`. -/
private theorem inner_toEuclideanCLM_comm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ i j, A i j = A j i) (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) =
      inner ℝ y (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) := by
  rw [inner_toEuclideanCLM_eq_sum, inner_toEuclideanCLM_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hA]; ring

/-- Rayleigh quotients of a perturbed matrix with a simple top eigenvector: if `S` is symmetric,
`S v = λ v` with `‖v‖ = 1`, `S` has Rayleigh values at most `λ - gap` on `v⊥`, and the
perturbation `E` has `4 ∑ |Eᵢⱼ| ≤ gap`, then for every unit `u` with component `b` orthogonal to
`v`, `⟪u, (S + E) u⟫ - ⟪v, (S + E) v⟫ ≤ -(gap / 2) ‖b‖² + 2 (∑ |Eᵢⱼ|) ‖b‖`. -/
private theorem rayleigh_perturbation_le {d : ℕ} {S E : Matrix (Fin d) (Fin d) ℝ}
    (hS : ∀ i j, S i j = S j i) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {lam gap : ℝ}
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) S v = lam • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) S u) ≤ (lam - gap) * ‖u‖ ^ 2)
    (hε : 4 * entrySum E ≤ gap) {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) :
    inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (S + E) u) -
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (S + E) v) ≤
      -(gap / 2) * ‖u - inner ℝ u v • v‖ ^ 2 + 2 * entrySum E * ‖u - inner ℝ u v • v‖ := by
  set a := inner ℝ u v
  set b := u - a • v
  set Sf := Matrix.toEuclideanCLM (𝕜 := ℝ) S
  set F := Matrix.toEuclideanCLM (𝕜 := ℝ) E
  set ε := entrySum E
  have hε0 : 0 ≤ ε := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hvv : inner ℝ v v = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hbv : inner ℝ b v = (0 : ℝ) := by
    simp only [b, inner_sub_left, real_inner_smul_left, hvv, mul_one, a, sub_self]
  have hub : u = a • v + b := by simp [b]
  have hnorm : a ^ 2 + ‖b‖ ^ 2 = 1 := by
    have h := norm_add_sq_real (a • v) b
    rw [← hub, hu, norm_smul, hv, real_inner_smul_left, real_inner_comm, hbv] at h
    simp only [Real.norm_eq_abs, mul_one, sq_abs, mul_zero] at h
    linarith
  have ha1 : |a| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg ‖b‖]
  have hSv : inner ℝ v (Sf v) = lam := by rw [heig, real_inner_smul_right, hvv, mul_one]
  have hbSv : inner ℝ b (Sf v) = 0 := by rw [heig, real_inner_smul_right, hbv, mul_zero]
  have hvSb : inner ℝ v (Sf b) = 0 := by rw [inner_toEuclideanCLM_comm hS]; exact hbSv
  have hbSb := hother b hbv
  have hFvv := abs_inner_toEuclideanCLM_le E v v
  have hFvb := abs_inner_toEuclideanCLM_le E v b
  have hFbv := abs_inner_toEuclideanCLM_le E b v
  have hFbb := abs_inner_toEuclideanCLM_le E b b
  rw [hv] at hFvv hFvb hFbv
  have hadd : Matrix.toEuclideanCLM (𝕜 := ℝ) (S + E) = Sf + F := map_add _ _ _
  have hexp : inner ℝ u ((Sf + F) u) = a ^ 2 * (inner ℝ v (Sf v) + inner ℝ v (F v)) +
      a * (inner ℝ v (Sf b) + inner ℝ v (F b)) + a * (inner ℝ b (Sf v) + inner ℝ b (F v)) +
      (inner ℝ b (Sf b) + inner ℝ b (F b)) := by
    rw [hub]
    simp only [add_apply, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hadd, hexp, add_apply, inner_add_right, hSv, hbSv, hvSb]
  set β := ‖b‖
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hab : ∀ x : ℝ, |x| ≤ ε * (1 * β) → a * x ≤ ε * β := fun x hx ↦ by
    have := abs_mul a x
    have : |a * x| ≤ ε * β := by
      rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg x]
    exact (le_abs_self _).trans this
  have k1 := hab _ hFvb
  have k2 := hab _ (by rw [mul_comm β 1] at hFbv; exact hFbv)
  have k3 : -(β ^ 2 * inner ℝ v (F v)) ≤ ε * β ^ 2 := by
    have := neg_abs_le (inner ℝ v (F v))
    nlinarith [sq_nonneg β]
  have k4 : inner ℝ b (F b) ≤ ε * β ^ 2 := by
    have := (le_abs_self _).trans hFbb; nlinarith
  have ha2 : a ^ 2 = 1 - β ^ 2 := by linarith
  rw [ha2]
  nlinarith

/-- Rayleigh values at unit vectors are bounded by the entrywise `ℓ¹` norm. -/
private theorem inner_toEuclideanCLM_le_entrySum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) :
    inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) ≤ entrySum A := by
  have := (le_abs_self _).trans (abs_inner_toEuclideanCLM_le A u u)
  rwa [hu, mul_one, mul_one] at this

/-- Every Rayleigh value at a unit vector is at most the leading Rayleigh value. -/
private theorem le_leadingRayleighValue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) :
    inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) ≤ leadingRayleighValue A := by
  refine le_csSup ⟨entrySum A, ?_⟩ ⟨u, hu, rfl⟩
  rintro r ⟨w, hw, rfl⟩
  exact inner_toEuclideanCLM_le_entrySum A hw

/-- An upper bound for all Rayleigh values at unit vectors bounds the leading Rayleigh value,
provided a unit vector exists. -/
private theorem leadingRayleighValue_le {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {c : ℝ}
    (h : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) ≤ c) :
    leadingRayleighValue A ≤ c := by
  refine csSup_le ⟨_, v, hv, rfl⟩ ?_
  rintro r ⟨w, hw, rfl⟩
  exact h w hw

/-- Without unit vectors (dimension zero) the leading Rayleigh value is `0`. -/
private theorem leadingRayleighValue_eq_zero {d : ℕ} (hne : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≠ 1)
    (A : Matrix (Fin d) (Fin d) ℝ) : leadingRayleighValue A = 0 := by
  unfold leadingRayleighValue
  have : {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      r = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)} = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun r hr ↦ ?_
    obtain ⟨u, hu, -⟩ := hr
    exact hne u hu
  rw [this, Real.sSup_empty]

/-- The leading Rayleigh value is Lipschitz for the entrywise `ℓ¹` norm (one-sided form). -/
private theorem leadingRayleighValue_le_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    leadingRayleighValue A ≤ leadingRayleighValue B + entrySum (A - B) := by
  by_cases hne : ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1
  · obtain ⟨v, hv⟩ := hne
    refine leadingRayleighValue_le hv fun u hu ↦ ?_
    have e : A = B + (A - B) := by abel
    have h1 := le_leadingRayleighValue B hu
    have h2 := inner_toEuclideanCLM_le_entrySum (A - B) hu
    calc inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)
        = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) B u) +
          inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (A - B) u) := by
          conv_lhs => rw [e]
          rw [map_add, add_apply, inner_add_right]
      _ ≤ _ := add_le_add h1 h2
  · push Not at hne
    have hA := leadingRayleighValue_eq_zero hne A
    have hB := leadingRayleighValue_eq_zero hne B
    rw [hA, hB, zero_add]
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _

/-- The leading Rayleigh value is a continuous function of the matrix. -/
private theorem continuous_leadingRayleighValue (d : ℕ) :
    Continuous (leadingRayleighValue (d := d)) := by
  have hes : Continuous (fun A : Matrix (Fin d) (Fin d) ℝ ↦ entrySum A) := by
    unfold entrySum
    exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      ((continuous_apply j).comp (continuous_apply i)).abs
  rw [continuous_iff_continuousAt]
  intro A
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun B ↦ entrySum (B - A)) (fun B ↦ ?_) ?_
  · rw [Real.norm_eq_abs, abs_le]
    have h1 := leadingRayleighValue_le_add B A
    have h2 := leadingRayleighValue_le_add A B
    have e : entrySum (A - B) = entrySum (B - A) := by
      unfold entrySum
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Matrix.sub_apply, Matrix.sub_apply, abs_sub_comm]
    constructor <;> linarith
  · have : Continuous fun B : Matrix (Fin d) (Fin d) ℝ ↦ entrySum (B - A) :=
      hes.comp (continuous_id.sub continuous_const)
    simpa [entrySum] using this.tendsto A

/-- Leading eigenvalue perturbation: under the hypotheses of `rayleigh_perturbation_le`, the
leading Rayleigh value of `A` exceeds `⟪v, A v⟫` by at most `2 ε² / gap`, `ε = ∑ |(A - S)ᵢⱼ|`. -/
private theorem leadingRayleighValue_sub_inner_le {d : ℕ} {S A : Matrix (Fin d) (Fin d) ℝ}
    (hS : ∀ i j, S i j = S j i) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {lam gap : ℝ}
    (hgap : 0 < gap) (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) S v = lam • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) S u) ≤ (lam - gap) * ‖u‖ ^ 2)
    (hε : 4 * entrySum (A - S) ≤ gap) :
    0 ≤ leadingRayleighValue A - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ∧
      leadingRayleighValue A - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ≤
        2 * entrySum (A - S) ^ 2 / gap := by
  have hA : S + (A - S) = A := add_sub_cancel _ _
  refine ⟨sub_nonneg.mpr (le_leadingRayleighValue A hv), ?_⟩
  rw [sub_le_iff_le_add']
  refine leadingRayleighValue_le hv fun u hu ↦ ?_
  have h := rayleigh_perturbation_le hS hv heig hother hε hu
  rw [hA] at h
  set β := ‖u - inner ℝ u v • v‖
  set ε := entrySum (A - S)
  have key : -(gap / 2) * β ^ 2 + 2 * ε * β ≤ 2 * ε ^ 2 / gap := by
    rw [le_div_iff₀ hgap]
    nlinarith [sq_nonneg (gap * β - 2 * ε)]
  linarith

/-- Leading eigenvector perturbation: a unit vector `w` with `⟪w, v⟫ ≥ 0` whose Rayleigh value
for `A` is at least that of `v` satisfies `‖w - v‖ ≤ 8 ε / gap`, `ε = ∑ |(A - S)ᵢⱼ|`. -/
private theorem norm_sub_le_of_inner_le {d : ℕ} {S A : Matrix (Fin d) (Fin d) ℝ}
    (hS : ∀ i j, S i j = S j i) {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {lam gap : ℝ}
    (hgap : 0 < gap) (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) S v = lam • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) S u) ≤ (lam - gap) * ‖u‖ ^ 2)
    (hε : 4 * entrySum (A - S) ≤ gap) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ = 1)
    (hsign : 0 ≤ inner ℝ w v)
    (hlead : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ≤
      inner ℝ w (Matrix.toEuclideanCLM (𝕜 := ℝ) A w)) :
    ‖w - v‖ ≤ 8 * entrySum (A - S) / gap := by
  have hA : S + (A - S) = A := add_sub_cancel _ _
  have h := rayleigh_perturbation_le hS hv heig hother hε hw
  rw [hA] at h
  set a := inner ℝ w v
  set b := w - a • v
  set β := ‖b‖
  set ε := entrySum (A - S)
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hε0 : 0 ≤ ε := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hβ : β ≤ 4 * ε / gap := by
    rw [le_div_iff₀ hgap]
    by_contra hc
    push Not at hc
    nlinarith
  have hvv : inner ℝ v v = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hbv : inner ℝ b v = (0 : ℝ) := by
    simp only [b, inner_sub_left, real_inner_smul_left, hvv, mul_one, a, sub_self]
  have hwb : w = a • v + b := by simp [b]
  have hnorm : a ^ 2 + β ^ 2 = 1 := by
    have h := norm_add_sq_real (a • v) b
    rw [← hwb, hw, norm_smul, hv, real_inner_smul_left, real_inner_comm, hbv] at h
    simp only [Real.norm_eq_abs, mul_one, sq_abs, mul_zero] at h
    linarith
  have hdiff : w - v = (a - 1) • v + b := by rw [hwb, sub_smul, one_smul]; abel
  have hsq : ‖w - v‖ ^ 2 = (a - 1) ^ 2 + β ^ 2 := by
    rw [hdiff, norm_add_sq_real, norm_smul, hv, real_inner_smul_left, real_inner_comm, hbv]
    simp only [Real.norm_eq_abs, mul_one, sq_abs, mul_zero, add_zero]
    rfl
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg β]
  have hle : ‖w - v‖ ^ 2 ≤ (2 * β) ^ 2 := by rw [hsq]; nlinarith
  have h2 : ‖w - v‖ ≤ 2 * β :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle
  calc ‖w - v‖ ≤ 2 * β := h2
    _ ≤ 2 * (4 * ε / gap) := by gcongr
    _ = 8 * ε / gap := by ring

section Entries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
  {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]
  {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

/-- The first part of `leading_empirical_covariance_eigenvalue_asymptotics`: the remainder of the
linear expansion of the leading empirical eigenvalue is `o_P(n^{-1/2})`. -/
private theorem tendstoInMeasure_leading_eigenvalue_remainder
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ) (hgap : 0 < gap)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) u) ≤
        (lambda - gap) * ‖u‖ ^ 2) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n *
      (leadingRayleighValue (empiricalCovarianceMatrix X n ω) - lambda -
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) v))) atTop
      (fun _ ↦ 0) := by
  have hS := euclideanCovarianceMatrix_symm (P := P)
  refine tendstoInMeasure_zero_of_abs_le μ (fun (n : ℕ) ω ↦ 2 / gap * (Real.sqrt n * entrySum
      (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) ^ 2)) _
    (fun n ω ↦ entrySum (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P))
    (by positivity : 0 < gap / 4) (Filter.Eventually.of_forall fun n ↦
      Filter.Eventually.of_forall fun ω hω ↦ ?_)
    (tendstoInMeasure_const_mul_zero μ _ _ (tendstoInMeasure_sqrt_mul_entrySum_sq hiid h4))
    (tendstoInMeasure_entrySum hiid h4)
  set A := empiricalCovarianceMatrix X n ω
  have hε : 4 * entrySum (A - euclideanCovarianceMatrix P) ≤ gap := by
    have := (le_abs_self _).trans hω.le; linarith
  obtain ⟨h0, h1⟩ := leadingRayleighValue_sub_inner_le hS hv hgap heig hother hε
  have hsub : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (A - euclideanCovarianceMatrix P) v) =
      inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) - lambda := by
    rw [map_sub, sub_apply, inner_sub_right,
      inner_euclideanCovarianceMatrix_self hv heig]
  rw [hsub, show leadingRayleighValue A - lambda -
    (inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) - lambda) =
      leadingRayleighValue A - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) by ring]
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  rw [abs_of_nonneg (mul_nonneg hsq h0), abs_of_nonneg (by positivity)]
  calc Real.sqrt n * (leadingRayleighValue A - inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v))
      ≤ Real.sqrt n * (2 * entrySum (A - euclideanCovarianceMatrix P) ^ 2 / gap) :=
        mul_le_mul_of_nonneg_left h1 hsq
    _ = _ := by ring


end Entries



/-- GAPS 103.30: leading empirical covariance eigenvalue expansion and CLT in finite dimension.
Let `X₁, X₂, …` be independent with law `P` on `ℝ^d` with finite fourth moment, and let the
covariance `Σ` of `P` have a unit eigenvector `v`, `Σ v = λ v`, with
`⟪u, Σ u⟫ ≤ (λ - gap) ‖u‖²` for `u ⊥ v` and `gap > 0`. Then the largest eigenvalue `λ̂ₙ` of the
empirical covariance `Σ̂ₙ` satisfies `√n (λ̂ₙ - λ - ⟪v, (Σ̂ₙ - Σ) v⟫) → 0` in probability, and
`√n (λ̂ₙ - λ)` converges in law to `N(0, Var ⟪X - E X, v⟫²)`. The Gaussian variance formula is
not needed for this non-Gaussian fourth-moment version. Positivity of `λ` is not assumed (it
follows from the gap when `d ≥ 2`). -/
theorem leading_empirical_covariance_eigenvalue_asymptotics
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ)
    (hgap : 0 < gap)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) u) ≤
        (lambda - gap) * ‖u‖ ^ 2) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt n *
      (leadingRayleighValue (empiricalCovarianceMatrix X n ω) - lambda -
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (empiricalCovarianceMatrix X n ω - euclideanCovarianceMatrix P) v))) atTop (fun _ ↦ 0) ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
      (leadingRayleighValue (empiricalCovarianceMatrix X n ω) - lambda)) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal
        (Var[fun x ↦ inner ℝ (x - ∫ z, z ∂P) v ^ 2; P]))) := by
  have hrem := tendstoInMeasure_leading_eigenvalue_remainder hiid h4 v hv lambda gap hgap heig
    hother
  refine ⟨hrem, ?_⟩
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_of_iid μ P X hiid (quadStat P v)
    (measurable_quadStat v) (memLp_quadStat h4 v) (integral_quadStat h4 v)
  rw [integral_quadStat_sq_eq_variance h4 hv heig] at hclt
  have hmeasA := measurable_empiricalCovarianceMatrix hiid.1
  refine tendstoInDistribution_of_tendstoInMeasure_sub_of_measurable μ _ _
    (fun n ↦ measurable_const.mul (Finset.measurable_fun_sum _ fun k _ ↦
      (measurable_quadStat v).comp (hiid.1 k)))
    (fun n ↦ measurable_const.mul
      (((continuous_leadingRayleighValue d).measurable.comp (hmeasA n)).sub_const _)) hclt ?_
  -- the difference is the remainder plus a negligible quadratic term
  have hR : TendstoInMeasure μ (fun (n : ℕ) ω ↦ ∑ i, ∑ j, (-(v i * v j)) *
      (Real.sqrt n * sampleCoordMean P X i n ω * sampleCoordMean P X j n ω)) atTop
      (fun _ ↦ 0) :=
    tendstoInMeasure_finsetSum_zero _ fun i _ ↦ tendstoInMeasure_finsetSum_zero _ fun j _ ↦
      tendstoInMeasure_const_mul_zero μ _ _
        (tendstoInMeasure_sqrt_mul_sampleCoordMean_mul hiid h4 i j)
  refine tendstoInMeasure_zero_of_abs_le' (tendstoInMeasure_add_zero μ _ _ hrem hR) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  apply le_of_eq
  congr 1
  set A := empiricalCovarianceMatrix X n ω
  have hQ : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (A - euclideanCovarianceMatrix P) v) =
      ∑ i, ∑ j, v i * (sampleProdMean P X i j n ω -
        sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) * v j := by
    rw [inner_toEuclideanCLM_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.sub_apply, empiricalCovarianceMatrix_sub_eq P X hn ω i j]
  have hW : (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, quadStat P v (X k ω) =
      ∑ i, ∑ j, v i * (Real.sqrt n * sampleProdMean P X i j n ω) * v j := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
      rw [show (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ by
        rw [← mul_inv, Real.mul_self_sqrt hnR.le]]
      field_simp
    simp only [quadStat, sampleProdMean, ← mul_assoc, hs]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hsum : Real.sqrt n * (∑ i, ∑ j, v i * (sampleProdMean P X i j n ω -
        sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) * v j) =
      ∑ i, ∑ j, v i * (Real.sqrt n * sampleProdMean P X i j n ω) * v j +
        ∑ i, ∑ j, (-(v i * v j)) *
          (Real.sqrt n * sampleCoordMean P X i n ω * sampleCoordMean P X j n ω) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hQ, hW]
  linear_combination hsum

/-- GAPS 103.30: the root-`n` bound for a leading empirical eigenvector. Under the hypotheses of
`CKSD.leading_empirical_covariance_eigenvalue_asymptotics`, any choice of unit eigenvector `ŵₙ` of
`Σ̂ₙ` for its largest eigenvalue, with sign fixed by `⟪ŵₙ, v⟫ ≥ 0`, satisfies
`√n ‖ŵₙ - v‖ = O_P(1)`; the choice need not be measurable. -/
theorem isBoundedInProbability_leading_empirical_eigenvector_error
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hiid : IsIndependentIdenticallyDistributed μ X P) (h4 : MemLp id 4 P)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) (lambda gap : ℝ)
    (hgap : 0 < gap)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) v = lambda • v)
    (hother : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ u v = 0 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (euclideanCovarianceMatrix P) u) ≤
        (lambda - gap) * ‖u‖ ^ 2)
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hwunit : ∀ n ω, ‖w n ω‖ = 1) (hsign : ∀ n ω, 0 ≤ inner ℝ (w n ω) v)
    (hwleading : ∀ n ω, Matrix.toEuclideanCLM (𝕜 := ℝ) (empiricalCovarianceMatrix X n ω)
      (w n ω) = leadingRayleighValue (empiricalCovarianceMatrix X n ω) • w n ω) :
    IsBoundedInProbability μ (fun n ω ↦ Real.sqrt n * ‖w n ω - v‖) := by
  have hS := euclideanCovarianceMatrix_symm (P := P)
  refine (isBoundedInProbability_sqrt_mul_entrySum hiid h4).of_abs_le_of_tendstoInMeasure
    (tendstoInMeasure_entrySum hiid h4) (by positivity : 0 < gap / 4)
    (by positivity : 0 ≤ 8 / gap) fun n ω hω ↦ ?_
  set A := empiricalCovarianceMatrix X n ω
  have hε : 4 * entrySum (A - euclideanCovarianceMatrix P) ≤ gap := by
    have := (le_abs_self _).trans hω.le; linarith
  have hlead : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ≤
      inner ℝ (w n ω) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (w n ω)) := by
    rw [hwleading n ω, real_inner_smul_right, real_inner_self_eq_norm_sq, hwunit, one_pow,
      mul_one]
    exact le_leadingRayleighValue A hv
  have h := norm_sub_le_of_inner_le hS hv hgap heig hother hε (hwunit n ω) (hsign n ω) hlead
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hes : 0 ≤ entrySum (A - euclideanCovarianceMatrix P) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  rw [abs_of_nonneg (mul_nonneg hsq (norm_nonneg _)), abs_of_nonneg (mul_nonneg hsq hes)]
  calc Real.sqrt n * ‖w n ω - v‖ ≤ Real.sqrt n * (8 * entrySum (A - euclideanCovarianceMatrix P) /
        gap) := mul_le_mul_of_nonneg_left h hsq
    _ = _ := by ring

/-- The empirical covariance of the empty sample is the zero matrix. -/
@[simp] theorem empiricalCovarianceMatrix_zero {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    empiricalCovarianceMatrix X 0 ω = 0 := by
  ext i j
  simp [empiricalCovarianceMatrix]

/-- An empirical covariance matrix is symmetric, for every sample including the empty one. -/
theorem empiricalCovarianceMatrix_isSymm {Ω : Type*} {d : ℕ}
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) :
    (empiricalCovarianceMatrix X n ω).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, empiricalCovarianceMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end CKSD
