module

public import CKSD.LinearModels.Multivariate
public import CKSD.LinearModels.MultivariateTests
public import Mathlib.Order.Hom.Set
public import TauCeti.Analysis.Matrix.GramFactorization.Uniqueness

/-!
# Orthogonal factor models

The orthogonal factor model `X = μ + L F + ε` with `m` common factors has covariance
`Σ = L Lᵀ + Ψ`, where `L` is the `p × m` loading matrix and `Ψ = diag ψ` the diagonal matrix of
unique variances. The loadings are determined by `Σ` only up to an orthogonal rotation; under
the normalization that `Lᵀ Ψ⁻¹ L` is diagonal with distinct positive decreasing entries they
are determined up to the signs of the columns.

## Main definitions

* `CKSD.factorCovariance`: the implied covariance `L Lᵀ + diag ψ`.
* `CKSD.factorLikelihoodCriterion`: the Gaussian criterion `log det Σ + tr(C Σ⁻¹)`.
* `CKSD.IsNormalizedFactorLoading`: `Lᵀ Ψ⁻¹ L` is diagonal with distinct positive decreasing
  entries.
* `CKSD.factorColumnSigns`, `CKSD.loadingSignDistance`: sign changes of the factor columns and
  the operator-norm distance of two loading matrices modulo such sign changes.

## Main results

* `CKSD.factorCovariance_mul_orthogonal`: rotating the factors does not change the covariance.
* `CKSD.IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns`: normalized loadings with the
  same common covariance agree up to column signs. The proof uses TauCeti's uniqueness of Gram
  factors and Mathlib's uniqueness of order embeddings with equal ranges.
* `CKSD.tendstoInMeasure_factor_mle_of_compact`: consistency of the Gaussian
  maximum-likelihood estimator on a compact identified parameter set. The proof combines a
  uniform criterion gap on the compact set, from the project inequality
  `log det S + p ≤ log det C + tr(S C⁻¹)` and its equality case, with the uniform
  closeness of the criteria for nearby sample covariances.

The identification result concerns the normalized-loading regime with known unique variances; it
does not assert identifiability of the decomposition of `Σ` into its common and unique parts.
Sources: GAPS 105.35 and SYNOPSIS105, item 35.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 14.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Covariance `L Lᵀ + diag ψ` of an orthogonal factor model with loadings `L` and unique
variances `ψ`. -/
def factorCovariance {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ := L * L.transpose + Matrix.diagonal psi

/-- The Gaussian covariance criterion `log det Σ + tr(C Σ⁻¹)` at `Σ = L Lᵀ + diag ψ`, for a sample
covariance `C`; it is the negative log-likelihood up to a constant and the factor `n / 2`. -/
def factorLikelihoodCriterion {p m : ℕ} (C : Matrix (Fin p) (Fin p) ℝ)
    (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ) : ℝ :=
  Real.log (factorCovariance L psi).det + Matrix.trace (C * (factorCovariance L psi)⁻¹)

/-- Normalized loadings: `Lᵀ (diag ψ)⁻¹ L` is a diagonal matrix with distinct positive entries in
decreasing order. -/
def IsNormalizedFactorLoading {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (psi : Fin p → ℝ) : Prop :=
  ∃ a : Fin m → ℝ, StrictAnti a ∧ (∀ i, 0 < a i) ∧
    L.transpose * (Matrix.diagonal psi)⁻¹ * L = Matrix.diagonal a

/-- The diagonal sign matrix changing the signs of the factor columns `j` with `s j = false`. -/
def factorColumnSigns {m : ℕ} (s : Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun j ↦ if s j then (1 : ℝ) else -1)

/-- Distance between two loading matrices modulo factor-column signs: the least operator norm of
`L S - M` over the sign matrices `S`. -/
def loadingSignDistance {p m : ℕ} (L M : Matrix (Fin p) (Fin m) ℝ) : ℝ :=
  sInf (range fun s : Fin m → Bool ↦
    ‖LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℝ) (L * factorColumnSigns s - M))‖)

/-- Orthogonal rotations of factors do not change their implied covariance. -/
theorem factorCovariance_mul_orthogonal {p m : ℕ}
    (L : Matrix (Fin p) (Fin m) ℝ) (psi : Fin p → ℝ)
    (O : Matrix (Fin m) (Fin m) ℝ) (hO : O * O.transpose = 1) :
    factorCovariance (L * O) psi = factorCovariance L psi := by
  simp only [factorCovariance, Matrix.transpose_mul]
  congr 1
  calc
    (L * O) * (O.transpose * L.transpose) = L * (O * O.transpose) * L.transpose := by
      simp only [Matrix.mul_assoc]
    _ = L * L.transpose := by rw [hO, Matrix.mul_one]

/-- GAPS 105.35: normalized loadings are identified up to column signs once both their common
covariance `L Lᵀ` and the diagonal unique covariance `diag ψ` are specified: if `L` and `M` are
normalized for `ψ` and `L Lᵀ = M Mᵀ`, then `M = L S` for a diagonal sign matrix `S`. -/
theorem IsNormalizedFactorLoading.exists_eq_mul_factorColumnSigns {p m : ℕ}
    {L M : Matrix (Fin p) (Fin m) ℝ} {psi : Fin p → ℝ}
    (hL : IsNormalizedFactorLoading L psi) (hM : IsNormalizedFactorLoading M psi)
    (hcov : L * L.transpose = M * M.transpose) :
    ∃ s : Fin m → Bool, M = L * factorColumnSigns s := by
  classical
  obtain ⟨a, ha, _, hLa⟩ := hL
  obtain ⟨b, hb, _, hMb⟩ := hM
  have hgram : L.transpose.conjTranspose * L.transpose = M.transpose.conjTranspose * M.transpose := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hcov
  obtain ⟨U, hU⟩ := TauCeti.conjTranspose_mul_self_eq_iff_exists_unitary_mul.mp hgram
  let Q : Matrix (Fin m) (Fin m) ℝ := (U : Matrix (Fin m) (Fin m) ℝ).transpose
  have hMQ : M = L * Q := by
    have ht := congrArg Matrix.transpose hU
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using ht
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff'.mp U.property)
  have hQQ' : Q.transpose * Q = 1 := by
    simpa only [Q, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp U.property)
  have hab : Matrix.diagonal a * Q = Q * Matrix.diagonal b := by
    calc
      Matrix.diagonal a * Q = Q * (Q.transpose * Matrix.diagonal a * Q) := by
        simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      _ = Q * Matrix.diagonal b := by
        rw [← hLa, ← hMb, hMQ, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
  have hentry : ∀ i j, Q i j ≠ 0 → a i = b j := by
    intro i j hq
    have he := congrArg (fun A ↦ A i j) hab
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    exact (mul_right_cancel₀ hq (he.trans (mul_comm _ _)))
  have hrow : ∀ i, ∃ j, Q i j ≠ 0 := by
    intro i
    by_contra! h
    have he := congrArg (fun A ↦ A i i) hQQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, h, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at he
    exact zero_ne_one he
  have hcol : ∀ j, ∃ i, Q i j ≠ 0 := by
    intro j
    by_contra! h
    have he := congrArg (fun A ↦ A j j) hQQ'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, h, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at he
    exact zero_ne_one he
  have hrange : Set.range a = Set.range b := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hrow i
      exact ⟨j, (hentry i j hj).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hcol j
      exact ⟨i, hentry i j hi⟩
  have heq : a = b := ha.dual_right.eq_of_range_eq hb.dual_right hrange
  have hoff : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    by_contra hq
    exact hij (ha.injective ((hentry i j hq).trans (congrFun heq j).symm))
  have hdiag : Q = Matrix.diagonal (fun i ↦ Q i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij, hoff i j hij]
  have hsign : ∀ i, Q i i = 1 ∨ Q i i = -1 := by
    intro i
    have he := congrArg (fun A ↦ A i i) hQQ
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at he
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at he
    rcases mul_self_eq_one_iff.mp he with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨fun i ↦ decide (Q i i = 1), hMQ.trans ?_⟩
  congr 1
  rw [hdiag]
  apply congrArg Matrix.diagonal
  funext i
  rcases hsign i with h | h <;> simp [h]

/-- Entries of a square matrix are bounded by its `L²` operator norm. -/
private theorem abs_apply_le_l2_opNorm {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    |A i j| ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j 1)
  set x := (EuclideanSpace.equiv (Fin p) ℝ).symm (A.mulVec (EuclideanSpace.single j (1 : ℝ)).ofLp)
  have h1 : x i = A i j := by simp [x]
  have h2 := PiLp.norm_apply_le x i
  rw [h1, Real.norm_eq_abs] at h2
  rw [show ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 by simp, mul_one] at h
  exact h2.trans h

/-- `|tr(Δ M)| ≤ p ‖Δ‖ ‖M‖` for the `L²` operator norm. -/
private theorem abs_trace_mul_le {p : ℕ} (Δ M : Matrix (Fin p) (Fin p) ℝ) :
    |(Δ * M).trace| ≤ p * (‖Δ‖ * ‖M‖) := by
  calc |(Δ * M).trace| ≤ ∑ i, |(Δ * M) i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin p, ‖Δ * M‖ := Finset.sum_le_sum fun i _ ↦ abs_apply_le_l2_opNorm _ i i
    _ = p * ‖Δ * M‖ := by simp
    _ ≤ p * (‖Δ‖ * ‖M‖) := by gcongr; exact Matrix.l2_opNorm_mul Δ M

/-- The implied covariance with positive unique variances is positive definite. -/
private theorem posDef_factorCovariance {p m : ℕ} (L : Matrix (Fin p) (Fin m) ℝ)
    (psi : Fin p → ℝ) (h : ∀ i, 0 < psi i) : (factorCovariance L psi).PosDef := by
  have hL := Matrix.posSemidef_self_mul_conjTranspose L
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hL
  exact Matrix.PosDef.posSemidef_add hL (Matrix.posDef_diagonal_iff.2 h)

/-- The loading distance modulo signs is nonnegative. -/
private theorem loadingSignDistance_nonneg {p m : ℕ} (L M : Matrix (Fin p) (Fin m) ℝ) :
    0 ≤ loadingSignDistance L M :=
  le_csInf (range_nonempty _) (by rintro _ ⟨s, rfl⟩; exact norm_nonneg _)

/-- The loading distance modulo signs is at most the distance for any one sign matrix. -/
private theorem loadingSignDistance_le {p m : ℕ} (L M : Matrix (Fin p) (Fin m) ℝ)
    (s : Fin m → Bool) : loadingSignDistance L M ≤ ‖L * factorColumnSigns s - M‖ :=
  csInf_le ⟨0, by rintro _ ⟨s, rfl⟩; exact norm_nonneg _⟩ ⟨s, rfl⟩

/-- Superlevel sets of the loading distance modulo signs are closed. -/
private theorem isClosed_le_loadingSignDistance {p m : ℕ} (M : Matrix (Fin p) (Fin m) ℝ)
    (ε : ℝ) : IsClosed {L : Matrix (Fin p) (Fin m) ℝ | ε ≤ loadingSignDistance L M} := by
  have h : {L : Matrix (Fin p) (Fin m) ℝ | ε ≤ loadingSignDistance L M} =
      ⋂ s : Fin m → Bool, {L | ε ≤ ‖L * factorColumnSigns s - M‖} := by
    ext L
    simp only [mem_ofPred_eq, mem_iInter, loadingSignDistance]
    rw [le_csInf_iff ⟨0, by rintro _ ⟨s, rfl⟩; exact norm_nonneg _⟩ (range_nonempty _)]
    exact ⟨fun h s ↦ h _ ⟨s, rfl⟩, by rintro h _ ⟨s, rfl⟩; exact h s⟩
  rw [h]
  exact isClosed_iInter fun s ↦ isClosed_le continuous_const
    ((continuous_id.matrix_mul continuous_const).sub continuous_const).norm

/-- Sign matrices square to the identity. -/
private theorem factorColumnSigns_mul_self {m : ℕ} (s : Fin m → Bool) :
    factorColumnSigns s * factorColumnSigns s = 1 := by
  rw [factorColumnSigns, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

/-- The implied covariance depends continuously on the parameter. -/
private theorem continuous_factorCovariance {p m : ℕ} :
    Continuous fun z : Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ) ↦ factorCovariance z.1 z.2 :=
  (continuous_fst.matrix_mul continuous_fst.matrix_transpose).add continuous_snd.matrix_diagonal

/-- The inverse of the implied covariance is continuous where the covariance is nonsingular. -/
private theorem continuousAt_factorCovariance_inv {p m : ℕ}
    (z : Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ)) (hz : (factorCovariance z.1 z.2).det ≠ 0) :
    ContinuousAt (fun z : Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ) ↦
      (factorCovariance z.1 z.2)⁻¹) z := by
  refine (continuousAt_matrix_inv _ ?_).comp continuous_factorCovariance.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hz

/-- Identification gap of the factor criterion at the true covariance: parameters in `K` at
distance at least `ε` from `(L₀, ψ₀)` (modulo column signs) have criterion value larger by a
fixed `η > 0`. It combines compactness with the Gaussian likelihood inequality
`log det S + p ≤ log det C + tr(S C⁻¹)` and its equality case. -/
private theorem exists_factorLikelihoodCriterion_gap {p m : ℕ}
    (K : Set (Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ))) (hK : IsCompact K)
    (hpd : ∀ z ∈ K, (factorCovariance z.1 z.2).PosDef)
    (L₀ : Matrix (Fin p) (Fin m) ℝ) (psi₀ : Fin p → ℝ) (hmem : (L₀, psi₀) ∈ K)
    (hidentified : ∀ z ∈ K, factorCovariance z.1 z.2 = factorCovariance L₀ psi₀ →
      z.2 = psi₀ ∧ ∃ s : Fin m → Bool, z.1 = L₀ * factorColumnSigns s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ z ∈ K, (ε ≤ dist z.2 psi₀ ∨ ε ≤ loadingSignDistance z.1 L₀) →
      factorLikelihoodCriterion (factorCovariance L₀ psi₀) L₀ psi₀ + η ≤
        factorLikelihoodCriterion (factorCovariance L₀ psi₀) z.1 z.2 := by
  set S₀ := factorCovariance L₀ psi₀ with hS₀
  set f := fun z : Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ) ↦
    factorLikelihoodCriterion S₀ z.1 z.2 with hf
  have hfc : ContinuousOn f K := by
    intro z hz
    have hlog := (continuous_factorCovariance.matrix_det.continuousAt (x := z)).log
      (hpd z hz).det_pos.ne'
    have hM : Continuous fun M : Matrix (Fin p) (Fin p) ℝ ↦ (S₀ * M).trace :=
      (continuous_const.matrix_mul continuous_id).matrix_trace
    have htr : ContinuousAt (fun z : Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ) ↦
        (S₀ * (factorCovariance z.1 z.2)⁻¹).trace) z :=
      hM.continuousAt.comp (continuousAt_factorCovariance_inv z (hpd z hz).det_pos.ne')
    exact (hlog.add htr).continuousWithinAt
  set B := K ∩ {z | ε ≤ dist z.2 psi₀ ∨ ε ≤ loadingSignDistance z.1 L₀}
  have hBc : IsCompact B := hK.inter_right
    ((isClosed_le continuous_const (continuous_snd.dist continuous_const)).union
      ((isClosed_le_loadingSignDistance L₀ ε).preimage continuous_fst))
  rcases B.eq_empty_or_nonempty with hB | hB
  · refine ⟨1, one_pos, fun z hz hbad ↦ ?_⟩
    have : z ∈ B := ⟨hz, hbad⟩
    rw [hB] at this
    exact absurd this (notMem_empty z)
  obtain ⟨z₁, hz₁, hmin⟩ := hBc.exists_isMinOn hB (hfc.mono inter_subset_left)
  have hS₀pd := hpd _ hmem
  have hf₀ : f (L₀, psi₀) = Real.log S₀.det + p := by
    simp only [hf, factorLikelihoodCriterion, ← hS₀]
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hS₀pd.isUnit),
      Matrix.trace_one, Fintype.card_fin]
  have hle := log_det_add_card_le_log_det_add_trace_mul_inv S₀ _ hS₀pd (hpd z₁ hz₁.1)
  refine ⟨f z₁ - f (L₀, psi₀), ?_, fun z hz hbad ↦ ?_⟩
  · rcases hle.lt_or_eq with hlt | heq
    · rw [hf₀]
      simp only [hf, factorLikelihoodCriterion]
      linarith
    · exfalso
      have hS := (log_det_add_card_eq_log_det_add_trace_mul_inv_iff _ _ hS₀pd
        (hpd z₁ hz₁.1)).1 heq
      obtain ⟨hψ, s, hL⟩ := hidentified z₁ hz₁.1 hS
      rcases hz₁.2 with h | h
      · rw [hψ, dist_self] at h
        linarith
      · have h' := loadingSignDistance_le z₁.1 L₀ s
        rw [hL] at h
        rw [hL, Matrix.mul_assoc, factorColumnSigns_mul_self, Matrix.mul_one, sub_self,
          norm_zero] at h'
        linarith
  · have := hmin ⟨hz, hbad⟩
    simp only [mem_ofPred_eq] at this
    linarith

/-- GAPS 105.35: consistency of factor maximum likelihood on a compact identified parameter set:
if the sample covariances `Cₙ` converge in probability to `Σ₀ = L₀ L₀ᵀ + diag ψ₀`, the parameter
`(L₀, ψ₀)` lies in a compact set `K` on which the unique variances are bounded below by `a > 0`
and on which `Σ₀` determines `ψ₀` and `L₀` up to column signs, then every minimizer `Tₙ` of the
criterion over `K` has `ψ̂ₙ → ψ₀` and `L̂ₙ → L₀` modulo column signs, in probability.
Compactness and the uniform lower bound on the unique variances are restrictions of this
formulation; the unrestricted parameter space and asymptotic normality are not included. -/
theorem tendstoInMeasure_factor_mle_of_compact
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set (Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ))) (hK : IsCompact K)
    (a : ℝ) (ha : 0 < a) (hpos : ∀ z ∈ K, ∀ i, a ≤ z.2 i)
    (L₀ : Matrix (Fin p) (Fin m) ℝ) (psi₀ : Fin p → ℝ) (hmem : (L₀, psi₀) ∈ K)
    (hidentified : ∀ z ∈ K, factorCovariance z.1 z.2 = factorCovariance L₀ psi₀ →
      z.2 = psi₀ ∧ ∃ s : Fin m → Bool, z.1 = L₀ * factorColumnSigns s)
    (C : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hClim : TendstoInMeasure P C atTop (fun _ ↦ factorCovariance L₀ psi₀))
    (T : ℕ → Ω → Matrix (Fin p) (Fin m) ℝ × (Fin p → ℝ))
    (hTK : ∀ n ω, T n ω ∈ K)
    (hopt : ∀ n, ∀ᵐ ω ∂P, ∀ z ∈ K,
      factorLikelihoodCriterion (C n ω) (T n ω).1 (T n ω).2 ≤
        factorLikelihoodCriterion (C n ω) z.1 z.2) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (T n ω).2) atTop (fun _ ↦ psi₀) ∧
      TendstoInMeasure P (fun (n : ℕ) ω ↦ loadingSignDistance (T n ω).1 L₀) atTop (fun _ ↦ 0) := by
  set S₀ := factorCovariance L₀ psi₀ with hS₀
  have hpd : ∀ z ∈ K, (factorCovariance z.1 z.2).PosDef := fun z hz ↦
    posDef_factorCovariance _ _ fun i ↦ ha.trans_le (hpos z hz i)
  obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn fun z hz ↦
    (continuousAt_factorCovariance_inv z (hpd z hz).det_pos.ne').continuousWithinAt
  have hbad : ∀ ε > 0, Tendsto (fun n ↦ P {ω | ε ≤ dist (T n ω).2 psi₀ ∨
      ε ≤ loadingSignDistance (T n ω).1 L₀}) atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨η, hη, hgap⟩ := exists_factorLikelihoodCriterion_gap K hK hpd L₀ psi₀ hmem
      hidentified ε hε
    set δ := η / (2 * (p * |Bd| + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hclose : ∀ Cm : Matrix (Fin p) (Fin p) ℝ, dist Cm S₀ < δ → ∀ z ∈ K,
        |factorLikelihoodCriterion Cm z.1 z.2 - factorLikelihoodCriterion S₀ z.1 z.2| < η / 2 := by
      intro Cm hCm z hz
      have heq : factorLikelihoodCriterion Cm z.1 z.2 - factorLikelihoodCriterion S₀ z.1 z.2 =
          ((Cm - S₀) * (factorCovariance z.1 z.2)⁻¹).trace := by
        simp only [factorLikelihoodCriterion, Matrix.sub_mul, Matrix.trace_sub]
        ring
      rw [heq]
      refine (abs_trace_mul_le _ _).trans_lt ?_
      rw [← dist_eq_norm]
      have hB := (hBd z hz).trans (le_abs_self Bd)
      have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      calc (p : ℝ) * (dist Cm S₀ * ‖(factorCovariance z.1 z.2)⁻¹‖) ≤ p * (δ * |Bd|) := by
            gcongr
        _ = η / 2 * (p * |Bd| / (p * |Bd| + 1)) := by
            rw [hδ]
            field_simp
        _ < η / 2 := by
            refine mul_lt_of_lt_one_right (half_pos hη) ?_
            rw [div_lt_one (by positivity)]
            linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendstoInMeasure_iff_dist.1 hClim δ hδpos) (fun _ ↦ bot_le) fun n ↦ ?_
    have hnull := ae_iff.1 (hopt n)
    calc P {ω | ε ≤ dist (T n ω).2 psi₀ ∨ ε ≤ loadingSignDistance (T n ω).1 L₀}
        ≤ P ({ω | δ ≤ dist (C n ω) S₀} ∪ {ω | ¬ ∀ z ∈ K,
            factorLikelihoodCriterion (C n ω) (T n ω).1 (T n ω).2 ≤
              factorLikelihoodCriterion (C n ω) z.1 z.2}) := by
          refine measure_mono fun ω hω ↦ ?_
          by_contra hcon
          simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_le] at hcon hω
          obtain ⟨hdist, hmin⟩ := hcon
          have h1 := hgap (T n ω) (hTK n ω) hω
          have h2 := abs_lt.1 (hclose (C n ω) hdist (T n ω) (hTK n ω))
          have h3 := abs_lt.1 (hclose (C n ω) hdist (L₀, psi₀) hmem)
          have h4 := hmin (L₀, psi₀) hmem
          simp only at h1 h3 h4
          linarith [h2.1, h3.2]
      _ ≤ P {ω | δ ≤ dist (C n ω) S₀} + P {ω | ¬ ∀ z ∈ K,
            factorLikelihoodCriterion (C n ω) (T n ω).1 (T n ω).2 ≤
              factorLikelihoodCriterion (C n ω) z.1 z.2} := measure_union_le _ _
      _ = P {ω | δ ≤ dist (C n ω) S₀} := by rw [hnull, add_zero]
  refine ⟨?_, ?_⟩
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbad ε hε)
      (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ Or.inl hω
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbad ε hε)
      (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ Or.inr ?_
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (loadingSignDistance_nonneg _ _)] at hω
    exact hω

end CKSD
