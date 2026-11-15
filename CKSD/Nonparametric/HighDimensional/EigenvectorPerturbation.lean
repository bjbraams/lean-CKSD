module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import CKSD.Nonparametric.Basic

/-!
# Perturbation of a leading eigenvector

A deterministic residual bound for the leading eigenvector of a perturbed self-adjoint operator
on a finite-dimensional real inner product space.

## Main results

* `CKSD.exists_unit_eigenvector_rayleigh_le`: a self-adjoint operator on a finite-dimensional
  inner product space has a unit eigenvector whose eigenvalue bounds the Rayleigh quotient.
* `CKSD.mem_span_singleton_of_eigenvector_of_forall_inner_eq_zero`: if every eigenvector for
  the eigenvalue `b` orthogonal to `v` vanishes, the `b`-eigenspace is spanned by any unit
  eigenvector for `b`.
* `CKSD.exists_eigenvector_norm_sub_le_of_rayleigh_gap`: if `A v = a v` and the Rayleigh
  quotient of `A` on `v^⊥` is at most `a - gap`, then for `2 ‖E‖ < gap` the top eigenvalue of
  `A + E` is simple, with a unit eigenvector `w` satisfying
  `‖w - v‖ ≤ 2 ‖E v - ⟪v, E v⟫ v‖ / (gap - 2 ‖E‖)`.

Source: GAPS 103.54 (the deterministic part described in `GAPS_EASY.md`).

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
  Press, 2019, Theorem 8.5 and Corollary 8.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

section Eigenvector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A self-adjoint operator `M` on a nonzero finite-dimensional real inner product space has a
unit eigenvector `w`, `M w = b w`, whose eigenvalue bounds the quadratic form:
`⟪u, M u⟫ ≤ b ‖u‖²` for all `u`. The unit vector `x` only witnesses that the space is nonzero. -/
theorem exists_unit_eigenvector_rayleigh_le
    (M : F →L[ℝ] F) (hM : IsSelfAdjoint M) (x : F) (hx : ‖x‖ = 1) :
    ∃ w : F, ‖w‖ = 1 ∧ ∃ b : ℝ, M w = b • w ∧
      ∀ u, inner ℝ u (M u) ≤ b * ‖u‖ ^ 2 := by
  have hcpt : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere _ _
  obtain ⟨w, hw, hmax⟩ := hcpt.exists_isMaxOn ⟨x, by simp [hx]⟩
    M.reApplyInnerSelf_continuous.continuousOn
  have hw1 : ‖w‖ = 1 := by simpa using hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hmax' : IsMaxOn M.reApplyInnerSelf (Metric.sphere 0 ‖w‖) w := by rw [hw1]; exact hmax
  have hev := hM.hasEigenvector_of_isMaxOn hw0 hmax'
  set lam := (⨆ x : { x : F // x ≠ 0 }, M.rayleighQuotient x : ℝ)
  have hMw : M w = lam • w := Module.End.mem_eigenspace_iff.mp hev.1
  refine ⟨w, hw1, lam, hMw, fun u ↦ ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set u' := ‖u‖⁻¹ • u
  have hu' : u' ∈ Metric.sphere (0 : F) 1 := by
    simp [u', norm_smul, hun.ne']
  have h1 : M.reApplyInnerSelf u' ≤ M.reApplyInnerSelf w := hmax hu'
  simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real] at h1
  rw [hMw, inner_smul_left, real_inner_self_eq_norm_sq, hw1] at h1
  simp only [u', map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at h1
  rw [real_inner_comm] at h1
  have : inner ℝ u (M u) = ‖u‖ ^ 2 * (‖u‖⁻¹ * (‖u‖⁻¹ * inner ℝ u (M u))) := by
    field_simp
  rw [this]
  nlinarith [sq_nonneg ‖u‖]

omit [FiniteDimensional ℝ F] in
/-- If every eigenvector of `M` for the eigenvalue `b` orthogonal to `v` vanishes, then the
`b`-eigenspace is spanned by any unit eigenvector `w` for `b`: the eigenvalue `b` is simple. -/
theorem mem_span_singleton_of_eigenvector_of_forall_inner_eq_zero (M : F →L[ℝ] F) {b : ℝ}
    {v w : F} (hw1 : ‖w‖ = 1) (hMw : M w = b • w)
    (hzero : ∀ u, inner ℝ u v = 0 → M u = b • u → u = 0) {z : F} (hz : M z = b • z) :
    z ∈ Submodule.span ℝ {w} := by
  obtain ⟨z', hz'⟩ : ∃ z', z' = z - inner ℝ w z • w := ⟨_, rfl⟩
  have hz'w : inner ℝ w z' = 0 := by
    rw [hz', inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hw1]; ring
  have hMz' : M z' = b • z' := by
    rw [hz', map_sub, map_smul, hz, hMw, smul_sub, smul_comm]
  have hz'0 : z' = 0 := by
    by_cases hwv0 : inner ℝ w v = 0
    · -- then `w` itself would be orthogonal to `v`
      exact absurd (hzero w hwv0 hMw) (by rintro rfl; simp at hw1)
    · obtain ⟨u, hu⟩ : ∃ u, u = inner ℝ z' v • w - inner ℝ w v • z' := ⟨_, rfl⟩
      have huv : inner ℝ u v = 0 := by
        rw [hu, inner_sub_left, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real]; ring
      have hMu' : M u = b • u := by
        rw [hu, map_sub, map_smul, map_smul, hMw, hMz', smul_sub, smul_comm b (inner ℝ z' v),
          smul_comm b (inner ℝ w v)]
      have hu0 := hzero u huv hMu'
      have := congrArg (fun t ↦ inner ℝ z' t) hu0
      simp only [hu, inner_sub_right, inner_smul_right, inner_zero_right] at this
      rw [real_inner_comm w z', hz'w, real_inner_self_eq_norm_sq] at this
      have h' : inner ℝ w v * ‖z'‖ ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · exact absurd h hwv0
      · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  rw [Submodule.mem_span_singleton]
  exact ⟨inner ℝ w z, by rw [hz', sub_eq_zero] at hz'0; exact hz'0.symm⟩

/-- GAPS 103.54: deterministic residual perturbation bound for the leading eigenvector. Let `A`
and `E` be self-adjoint operators on a finite-dimensional real inner product space, and let `v`
be a unit vector with `A v = a v` such that `⟪u, A u⟫ ≤ (a - gap) ‖u‖²` for all `u ⊥ v`. If
`2 ‖E‖ < gap`, then the top eigenvalue `b` of `A + E` is simple, and it has a unit eigenvector
`w` with `⟪w, v⟫ ≥ 0` and `‖w - v‖ ≤ 2 ‖E v - ⟪v, E v⟫ v‖ / (gap - 2 ‖E‖)`. The probabilistic
spiked-covariance bound is outside this deterministic statement. -/
theorem exists_eigenvector_norm_sub_le_of_rayleigh_gap
    (A E : F →L[ℝ] F)
    (hA : IsSelfAdjoint A) (hE : IsSelfAdjoint E)
    (v : F) (hv : ‖v‖ = 1) (a gap : ℝ)
    (heig : A v = a • v)
    (hother : ∀ u, inner ℝ u v = 0 → inner ℝ u (A u) ≤ (a - gap) * ‖u‖ ^ 2)
    (hsmall : 2 * ‖E‖ < gap) :
    ∃ w : F, ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v ∧
      (∃ b : ℝ, (A + E) w = b • w ∧
        (∀ u, inner ℝ u ((A + E) u) ≤ b * ‖u‖ ^ 2) ∧
        ∀ z, (A + E) z = b • z → z ∈ Submodule.span ℝ {w}) ∧
      ‖w - v‖ ≤ 2 * ‖E v - inner ℝ v (E v) • v‖ / (gap - 2 * ‖E‖) := by
  set M := A + E with hMdef
  have hM : IsSelfAdjoint M := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA hE ⊢
    rw [hMdef, ContinuousLinearMap.toLinearMap_add]; exact hA.add hE
  have hEle : ∀ u, |inner ℝ u (E u)| ≤ ‖E‖ * ‖u‖ ^ 2 := fun u ↦ by
    calc |inner ℝ u (E u)| ≤ ‖u‖ * ‖E u‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖E‖ * ‖u‖) := by gcongr; exact E.le_opNorm u
      _ = ‖E‖ * ‖u‖ ^ 2 := by ring
  have hMu : ∀ u, inner ℝ u (M u) = inner ℝ u (A u) + inner ℝ u (E u) := fun u ↦ by
    simp [hMdef, inner_add_right]
  obtain ⟨w₀, hw₀, b, hMw₀, hray⟩ := exists_unit_eigenvector_rayleigh_le M hM v hv
  obtain ⟨w, hw1, hwv, hMw⟩ : ∃ w : F, ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v ∧
      M w = b • w := by
    by_cases h : 0 ≤ inner ℝ w₀ v
    · exact ⟨w₀, hw₀, h, hMw₀⟩
    · refine ⟨-w₀, by rw [norm_neg, hw₀], ?_, by rw [map_neg, hMw₀, smul_neg]⟩
      rw [inner_neg_left]; linarith
  -- eigenvalue lower bound and the Rayleigh bound off `v`
  have hblow : a - ‖E‖ ≤ b := by
    have h1 := hray v
    rw [hMu, heig, inner_smul_right, real_inner_self_eq_norm_sq, hv] at h1
    have := (abs_le.mp (hEle v)).1
    rw [hv] at this
    nlinarith
  have hperp : ∀ u, inner ℝ u v = 0 → inner ℝ u (M u) ≤ (a - gap + ‖E‖) * ‖u‖ ^ 2 := by
    intro u hu
    rw [hMu]
    have := (abs_le.mp (hEle u)).2
    have := hother u hu
    nlinarith
  have hdel : 0 < gap - 2 * ‖E‖ := by linarith
  -- an eigenvector for `b` orthogonal to `v` is zero
  have hzero : ∀ u, inner ℝ u v = 0 → M u = b • u → u = 0 := by
    intro u hu hMu'
    have h1 := hperp u hu
    rw [hMu', inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have h2 : (gap - 2 * ‖E‖) * ‖u‖ ^ 2 ≤ 0 := by nlinarith
    have h3 : ‖u‖ ^ 2 ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
  refine ⟨w, hw1, hwv, ⟨b, hMw, hray, fun z hz ↦
    mem_span_singleton_of_eigenvector_of_forall_inner_eq_zero M hw1 hMw hzero hz⟩, ?_⟩
  -- the distance bound
  obtain ⟨c, hc⟩ : ∃ c, c = inner ℝ w v := ⟨_, rfl⟩
  have hc' : inner ℝ v w = c := by rw [real_inner_comm]; exact hc.symm
  rw [← hc] at hwv
  obtain ⟨r, hr⟩ : ∃ r, r = E v - inner ℝ v (E v) • v := ⟨_, rfl⟩
  rw [← hr]
  obtain ⟨u, hu⟩ : ∃ u, u = w - c • v := ⟨_, rfl⟩
  have hwu : w = u + c • v := by rw [hu]; abel
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have huv : inner ℝ u v = 0 := by
    rw [hu, inner_sub_left, inner_smul_left, hvv, ← hc]; simp
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  have hc1 : c ≤ 1 := by
    have := real_inner_le_norm w v; rw [hw1, hv, ← hc] at this; linarith
  have hnu : ‖u‖ ^ 2 = 1 - c ^ 2 := by
    rw [hu, norm_sub_sq_real, inner_smul_right, norm_smul, hw1, hv, ← hc, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have huw : inner ℝ u w = ‖u‖ ^ 2 := by
    rw [hwu, inner_add_right, inner_smul_right, huv, real_inner_self_eq_norm_sq]; ring
  have hMv : inner ℝ u (M v) = inner ℝ u r := by
    rw [hMdef, add_apply, inner_add_right, heig, inner_smul_right, huv, hr, inner_sub_right,
      inner_smul_right, huv]; ring
  have hMw' : inner ℝ u (M w) = inner ℝ u (M u) + c * inner ℝ u r := by
    rw [hwu, map_add, map_smul, inner_add_right, inner_smul_right, hMv]
  have hkey : b * ‖u‖ ^ 2 ≤ (a - gap + ‖E‖) * ‖u‖ ^ 2 + c * (‖u‖ * ‖r‖) := by
    have h1 : inner ℝ u (M w) = b * ‖u‖ ^ 2 := by rw [hMw, inner_smul_right, huw]
    have h2 := hperp u huv
    have h3 : inner ℝ u r ≤ ‖u‖ * ‖r‖ := real_inner_le_norm u r
    have h4 := mul_le_mul_of_nonneg_left h3 hwv
    linarith
  have hur : (gap - 2 * ‖E‖) * ‖u‖ ≤ ‖r‖ := by
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h, mul_zero]; exact norm_nonneg _
    · have s1 : (gap - 2 * ‖E‖) * ‖u‖ ^ 2 ≤ (b - (a - gap + ‖E‖)) * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have s2 : c * (‖u‖ * ‖r‖) ≤ ‖u‖ * ‖r‖ :=
        mul_le_of_le_one_left (mul_nonneg h.le (norm_nonneg r)) hc1
      have s3 : ‖u‖ * ((gap - 2 * ‖E‖) * ‖u‖) ≤ ‖u‖ * ‖r‖ := by
        have : ‖u‖ * ((gap - 2 * ‖E‖) * ‖u‖) = (gap - 2 * ‖E‖) * ‖u‖ ^ 2 := by ring
        linarith
      exact le_of_mul_le_mul_left s3 h
  have hwv2 : ‖w - v‖ ^ 2 ≤ (2 * ‖u‖) ^ 2 := by
    rw [norm_sub_sq_real, hw1, hv, ← hc, mul_pow, hnu]
    nlinarith [mul_nonneg hwv (sub_nonneg.mpr hc1)]
  have hwv' : ‖w - v‖ ≤ 2 * ‖u‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hwv2
  rw [le_div_iff₀ hdel]
  calc ‖w - v‖ * (gap - 2 * ‖E‖) ≤ 2 * ‖u‖ * (gap - 2 * ‖E‖) :=
        mul_le_mul_of_nonneg_right hwv' hdel.le
    _ = 2 * ((gap - 2 * ‖E‖) * ‖u‖) := by ring
    _ ≤ 2 * ‖r‖ := by linarith

end Eigenvector

end CKSD
