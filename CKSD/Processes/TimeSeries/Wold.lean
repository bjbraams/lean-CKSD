module

public import CKSD.Processes.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearCombination

/-!
# Hilbert-space Wold decomposition

For a weakly stationary sequence `X : ℤ → H` in a real Hilbert space, with closed pasts
`past X t = closure (span {X s : s ≤ t})`, orthogonal projections `P t` onto them, and
innovations `e t = X t - P (t - 1) (X t)` with `e 0 ≠ 0`, the sequence decomposes as
`X t = ∑_{j ≥ 0} a_j e (t - j) + V t` with `a 0 = 1`, `∑ a_j² < ∞`, and `V` in the remote past
`⋂_s past X s` and orthogonal to all innovations. Applied to `L²` random variables this is the
Wold decomposition of a weakly stationary process.

The proof constructs the shift `X t ↦ X (t + 1)` as a linear isometry of the closed span (by
extension from finite linear combinations), shows that it commutes with the projections, so
that the innovations are shifts of each other and have constant norm, and expands
`X t - P (t - k) (X t)` in the orthogonal innovations.

## Main definitions

* `CKSD.Wold.past`, `CKSD.Wold.hull`: the closed pasts and the closed span.
* `CKSD.Wold.shiftIsometry`, `CKSD.Wold.shift`: the shift of a weakly stationary sequence.
* `CKSD.Wold.innov`: the innovations `X t - P (t - 1) (X t)`.

## Main results

* `CKSD.Wold.wold`: the decomposition in terms of the innovations.
* `CKSD.exists_wold_decomposition` (GAPS 106.2): the decomposition for a weakly stationary
  sequence (`CKSD.IsWeaklyStationary`).

The causal autoregression part of GAPS 106.2 is not covered.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open scoped RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

namespace Wold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The closed linear span of `X s`, `s ≤ t`. -/
def past (X : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ {x | ∃ s : ℤ, s ≤ t ∧ x = X s}).topologicalClosure

/-- The closed linear span of the whole sequence. -/
def hull (X : ℤ → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range X)).topologicalClosure

variable (X : ℤ → H)

/-- The closed pasts increase with time. -/
theorem past_mono {s t : ℤ} (h : s ≤ t) : past X s ≤ past X t := by
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, hr.trans h, rfl⟩

/-- `X_t` lies in the closed past at time `t`. -/
theorem mem_past_self (t : ℤ) : X t ∈ past X t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, le_rfl, rfl⟩)

/-- The closed past is closed. -/
theorem isClosed_past (t : ℤ) : IsClosed (past X t : Set H) :=
  Submodule.isClosed_topologicalClosure _

/-- The closed past lies in the closed span. -/
theorem past_le_hull (t : ℤ) : past X t ≤ hull X := by
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨r, -, rfl⟩
  exact ⟨r, rfl⟩

/-- A vector orthogonal to `X s` for every `s ≤ t` is orthogonal to the closed past. -/
theorem inner_eq_zero_of_forall_le {z : H} {t : ℤ} (hz : ∀ s ≤ t, ⟪z, X s⟫ = 0) :
    ∀ y ∈ past X t, ⟪z, y⟫ = 0 := by
  have hle : past X t ≤ (Submodule.span ℝ {z})ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hz s hs
  intro y hy
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hy)

/-- The closed span is closed. -/
theorem isClosed_hull : IsClosed (hull X : Set H) := Submodule.isClosed_topologicalClosure _

/-- `X_t` lies in the closed span. -/
theorem mem_hull (t : ℤ) : X t ∈ hull X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)

section Shift

variable [CompleteSpace H]

/-- The closed span of a sequence in a Hilbert space is complete. -/
instance : CompleteSpace (hull X) := (isClosed_hull X).completeSpace_coe

/-- The coefficient map `c ↦ ∑ c_t X_t` into the closed span. -/
def coeffMap : (ℤ →₀ ℝ) →ₗ[ℝ] hull X :=
  Finsupp.linearCombination ℝ fun t ↦ (⟨X t, mem_hull X t⟩ : hull X)

/-- The shifted coefficient map `c ↦ ∑ c_t X_{t+1}` into the closed span. -/
def shiftedCoeffMap : (ℤ →₀ ℝ) →ₗ[ℝ] hull X :=
  Finsupp.linearCombination ℝ fun t ↦ (⟨X (t + 1), mem_hull X (t + 1)⟩ : hull X)

omit [CompleteSpace H] in
/-- The finite linear combinations of the `X_t` are dense in the closed span. -/
theorem denseRange_coeffMap : DenseRange (coeffMap X) := by
  intro k
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  have himage :
      Subtype.val '' Set.range (coeffMap X) = (Submodule.span ℝ (Set.range X) : Set H) := by
    have h1 : ∀ f, ((coeffMap X f : hull X) : H) = Finsupp.linearCombination ℝ X f := by
      intro f
      change (hull X).subtype (Finsupp.linearCombination ℝ _ f) = _
      rw [Finsupp.apply_linearCombination]
      rfl
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, h1, SetLike.mem_coe]
    rw [← Finsupp.range_linearCombination, LinearMap.mem_range]
  have hk : (k : H) ∈ closure (Submodule.span ℝ (Set.range X) : Set H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact k.2
  convert hk

variable {X}

omit [CompleteSpace H] in
/-- Under a stationary Gram matrix, shifting the coefficients preserves norms. -/
theorem norm_shiftedCoeffMap (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) (f : ℤ →₀ ℝ) :
    ‖shiftedCoeffMap X f‖ = ‖coeffMap X f‖ :=
  f.norm_linearCombination_eq_of_inner_eq fun a b ↦ by
    change ⟪X (a + 1), X (b + 1)⟫ = ⟪X a, X b⟫
    rw [hstat, hstat a b]
    congr 2
    ring

omit [CompleteSpace H] in
/-- The shifted coefficient map is bounded by the coefficient map. -/
theorem exists_bound_shiftedCoeffMap (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) :
    ∃ C, ∀ f, ‖shiftedCoeffMap X f‖ ≤ C * ‖coeffMap X f‖ :=
  ⟨1, fun f ↦ by rw [norm_shiftedCoeffMap hstat f, one_mul]⟩

/-- With a stationary Gram matrix, the shift `X_t ↦ X_{t+1}` is a linear isometry of the
closed span. -/
def shiftIsometry (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) : hull X →ₗᵢ[ℝ] hull X :=
  LinearIsometry.mk ((shiftedCoeffMap X).extendOfNorm (coeffMap X)).toLinearMap fun x ↦ by
    refine (denseRange_coeffMap X).induction_on x
      (isClosed_eq ((shiftedCoeffMap X).extendOfNorm (coeffMap X)).continuous.norm
        continuous_norm) ?_
    intro f
    exact calc
      ‖(shiftedCoeffMap X).extendOfNorm (coeffMap X) (coeffMap X f)‖ = ‖shiftedCoeffMap X f‖ :=
        congrArg norm (LinearMap.extendOfNorm_eq (denseRange_coeffMap X)
          (exists_bound_shiftedCoeffMap hstat) f)
      _ = ‖coeffMap X f‖ := norm_shiftedCoeffMap hstat f

/-- The shift isometry sends `X_t` to `X_{t+1}`. -/
theorem shiftIsometry_apply (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) (t : ℤ) :
    shiftIsometry hstat ⟨X t, mem_hull X t⟩ = ⟨X (t + 1), mem_hull X (t + 1)⟩ := by
  have h := LinearMap.extendOfNorm_eq (denseRange_coeffMap X) (exists_bound_shiftedCoeffMap hstat)
    (Finsupp.single t 1)
  simp only [coeffMap, shiftedCoeffMap, Finsupp.linearCombination_single, one_smul] at h
  exact h

/-- The shift extended by zero on the orthogonal complement of the closed span. -/
def shift (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) : H →L[ℝ] H :=
  (hull X).subtypeL ∘L (shiftIsometry hstat).toContinuousLinearMap ∘L
    (hull X).orthogonalProjectionOnto

variable (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫)
include hstat

/-- On the closed span, the shift is the shift isometry. -/
theorem shift_apply_of_mem {x : H} (hx : x ∈ hull X) :
    shift hstat x = shiftIsometry hstat ⟨x, hx⟩ := by
  simp [shift, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩]

/-- The shift sends `X_t` to `X_{t+1}`. -/
theorem shift_apply_X (t : ℤ) : shift hstat (X t) = X (t + 1) := by
  rw [shift_apply_of_mem hstat (mem_hull X t), shiftIsometry_apply]

/-- The shift preserves inner products on the closed span. -/
theorem inner_shift_shift {x y : H} (hx : x ∈ hull X) (hy : y ∈ hull X) :
    ⟪shift hstat x, shift hstat y⟫ = ⟪x, y⟫ := by
  rw [shift_apply_of_mem hstat hx, shift_apply_of_mem hstat hy]
  exact (shiftIsometry hstat).inner_map_map ⟨x, hx⟩ ⟨y, hy⟩

/-- The shift maps the closed past at time `t` into the closed past at time `t + 1`. -/
theorem shift_mem_past {x : H} {t : ℤ} (hx : x ∈ past X t) : shift hstat x ∈ past X (t + 1) := by
  have hle : past X t ≤ (past X (t + 1)).comap (shift hstat).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_
      ((isClosed_past X (t + 1)).preimage (shift hstat).continuous)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    change shift hstat (X s) ∈ past X (t + 1)
    rw [shift_apply_X]
    exact past_mono X (by omega) (mem_past_self X (s + 1))
  exact hle hx

/-- The shift of a vector of the closed span orthogonal to the closed past at time `t` is
orthogonal to the closed past at time `t + 1`. -/
theorem inner_shift_eq_zero {a : H} (ha : a ∈ hull X) {t : ℤ}
    (h : ∀ y ∈ past X t, ⟪a, y⟫ = 0) : ∀ z ∈ past X (t + 1), ⟪shift hstat a, z⟫ = 0 := by
  refine inner_eq_zero_of_forall_le X fun s hs ↦ ?_
  have hXs : X s = shift hstat (X (s - 1)) := by rw [shift_apply_X, sub_add_cancel]
  rw [hXs, inner_shift_shift hstat ha (mem_hull X _)]
  exact h _ (past_mono X (by omega) (mem_past_self X (s - 1)))

end Shift

section Projection

variable {X} (P : ℤ → H →L[ℝ] H)
  (hproj : ∀ t x, P t x ∈ past X t ∧ ∀ y ∈ past X t, ⟪x - P t x, y⟫ = 0)
include hproj

/-- The orthogonal projection is characterized by membership and orthogonality. -/
theorem proj_eq_of_mem_of_inner_eq_zero {t : ℤ} {x y : H} (hy : y ∈ past X t)
    (h : ∀ z ∈ past X t, ⟪x - y, z⟫ = 0) : P t x = y := by
  have hd : P t x - y ∈ past X t := sub_mem (hproj t x).1 hy
  have hsplit : P t x - y = (x - y) - (x - P t x) := by abel
  have h0 : ⟪P t x - y, P t x - y⟫ = 0 := by
    calc ⟪P t x - y, P t x - y⟫ = ⟪(x - y) - (x - P t x), P t x - y⟫ := by rw [← hsplit]
      _ = 0 := by rw [inner_sub_left, h _ hd, (hproj t x).2 _ hd, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- The projection fixes the closed past. -/
theorem proj_of_mem {t : ℤ} {x : H} (hx : x ∈ past X t) : P t x = x :=
  proj_eq_of_mem_of_inner_eq_zero P hproj hx fun z _ ↦ by simp

/-- Tower property of the projections onto the closed pasts. -/
theorem proj_proj {s t : ℤ} (hst : s ≤ t) (x : H) : P s (P t x) = P s x := by
  refine proj_eq_of_mem_of_inner_eq_zero P hproj (hproj s x).1 fun z hz ↦ ?_
  have hsplit : P t x - P s x = (x - P s x) - (x - P t x) := by abel
  rw [hsplit, inner_sub_left, (hproj s x).2 z hz, (hproj t x).2 z (past_mono X hst hz),
    sub_zero]

/-- The innovation at time `t` lies in the closed past at time `t`. -/
theorem innov_mem (t : ℤ) : X t - P (t - 1) (X t) ∈ past X t :=
  sub_mem (mem_past_self X t) (past_mono X (by omega) (hproj (t - 1) (X t)).1)

/-- The innovation at time `t` is orthogonal to the closed past at time `t - 1`. -/
theorem inner_innov_eq_zero (t : ℤ) {y : H} (hy : y ∈ past X (t - 1)) :
    ⟪X t - P (t - 1) (X t), y⟫ = 0 :=
  (hproj (t - 1) (X t)).2 y hy

/-- Innovations at different times are orthogonal. -/
theorem inner_innov_innov {s t : ℤ} (hst : s < t) :
    ⟪X s - P (s - 1) (X s), X t - P (t - 1) (X t)⟫ = 0 := by
  rw [real_inner_comm]
  exact inner_innov_eq_zero P hproj t (past_mono X (by omega) (innov_mem P hproj s))

/-- One step of the innovations decomposition, for a vector `e ≠ 0` in the closed past at time
`t`, orthogonal to the closed past at time `t - 1`, with `X_t - e` in the latter: for `x` in
the closed past at time `t`, `x - P_{t-1} x` is the component of `x` along `e`. -/
theorem sub_proj_eq_smul_of {t : ℤ} {x e q : H} (hx : x ∈ past X t) (he0 : e ≠ 0)
    (hXt : X t = e + q) (hq : q ∈ past X (t - 1)) (he : e ∈ past X t)
    (horth : ∀ y ∈ past X (t - 1), ⟪e, y⟫ = 0) :
    x - P (t - 1) x = (⟪x, e⟫ / ‖e‖ ^ 2) • e := by
  set c := ⟪x, e⟫ / ‖e‖ ^ 2
  have hr : x - P (t - 1) x - c • e ∈ past X t :=
    sub_mem (sub_mem hx (past_mono X (by omega) (hproj (t - 1) x).1))
      (Submodule.smul_mem _ _ he)
  have hPx : P (t - 1) x ∈ past X (t - 1) := (hproj (t - 1) x).1
  have h₁ : ⟪x - P (t - 1) x, q⟫ = 0 := (hproj (t - 1) x).2 _ hq
  have h₂ : ⟪x - P (t - 1) x, e⟫ = ⟪x, e⟫ := by
    rw [inner_sub_left, real_inner_comm e ((P (t - 1)) x), horth _ hPx, sub_zero]
  have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 he0)
  have hc : c * ‖e‖ ^ 2 = ⟪x, e⟫ := by simp only [c]; field_simp
  have hrX : ∀ s ≤ t, ⟪x - P (t - 1) x - c • e, X s⟫ = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hlt
    · rw [hXt, inner_sub_left, inner_add_right, inner_add_right, h₁, h₂, inner_smul_left,
        inner_smul_left, horth _ hq, real_inner_self_eq_norm_sq]
      simp [hc]
    · have hXs : X s ∈ past X (t - 1) := past_mono X (by omega) (mem_past_self X s)
      rw [inner_sub_left, (hproj (t - 1) x).2 _ hXs, inner_smul_left, horth _ hXs]
      simp
  have h0 := inner_eq_zero_of_forall_le X hrX _ hr
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- One step of the innovations decomposition: for `x` in the closed past at time `t`,
`x - P_{t-1} x` is the component of `x` along the innovation at time `t`. -/
theorem sub_proj_eq_smul_innov {t : ℤ} {x : H} (hx : x ∈ past X t)
    (he : X t - P (t - 1) (X t) ≠ 0) :
    x - P (t - 1) x = (⟪x, X t - P (t - 1) (X t)⟫ / ‖X t - P (t - 1) (X t)‖ ^ 2) •
      (X t - P (t - 1) (X t)) :=
  sub_proj_eq_smul_of P hproj hx he (by abel) (hproj (t - 1) (X t)).1 (innov_mem P hproj t)
    fun _ hy ↦ inner_innov_eq_zero P hproj t hy

end Projection

/-- The innovation `X_t - P_{t-1} X_t`. -/
def innov (P : ℤ → H →L[ℝ] H) (X : ℤ → H) (t : ℤ) : H := X t - P (t - 1) (X t)

/-- A real sequence on `ℤ` that is invariant under the unit shift is constant. -/
theorem eq_apply_zero_of_succ {g : ℤ → ℝ} (h : ∀ t, g (t + 1) = g t) (t : ℤ) : g t = g 0 := by
  induction t using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [h, ih]
  | pred n ih => rw [← h (-(n : ℤ) - 1), sub_add_cancel, ih]

section Innovations

variable [CompleteSpace H] {X} (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫)
  (P : ℤ → H →L[ℝ] H)
  (hproj : ∀ t x, P t x ∈ past X t ∧ ∀ y ∈ past X t, ⟪x - P t x, y⟫ = 0)

include hstat in
/-- The shift preserves norms on the closed span. -/
theorem norm_shift {x : H} (hx : x ∈ hull X) : ‖shift hstat x‖ = ‖x‖ := by
  rw [shift_apply_of_mem hstat hx]
  exact (shiftIsometry hstat).norm_map ⟨x, hx⟩

include hstat hproj

/-- The projections onto the closed pasts commute with the shift. -/
theorem proj_shift {s : ℤ} {x : H} (hx : x ∈ hull X) :
    P (s + 1) (shift hstat x) = shift hstat (P s x) := by
  refine proj_eq_of_mem_of_inner_eq_zero P hproj (shift_mem_past hstat (hproj s x).1) fun z hz ↦ ?_
  rw [← map_sub]
  exact inner_shift_eq_zero hstat (sub_mem hx (past_le_hull X s (hproj s x).1))
    (hproj s x).2 z hz

/-- The innovation at time `t + 1` is the shift of the innovation at time `t`. -/
theorem innov_succ (t : ℤ) : innov P X (t + 1) = shift hstat (innov P X t) := by
  have h := proj_shift hstat P hproj (s := t - 1) (mem_hull X t)
  rw [sub_add_cancel, shift_apply_X] at h
  simp only [innov]
  rw [add_sub_cancel_right, h, map_sub, shift_apply_X]

omit [CompleteSpace H] hstat in
/-- The innovations lie in the closed span. -/
theorem innov_mem_hull (t : ℤ) : innov P X t ∈ hull X :=
  past_le_hull X t (innov_mem P hproj t)

/-- The innovations have constant norm. -/
theorem norm_innov (t : ℤ) : ‖innov P X t‖ = ‖innov P X 0‖ :=
  eq_apply_zero_of_succ (g := fun t ↦ ‖innov P X t‖) (fun t ↦ by
    rw [innov_succ hstat P hproj, norm_shift hstat (innov_mem_hull P hproj t)]) t

/-- The inner product of `X_t` with the innovation at time `t - j` does not depend on `t`. -/
theorem inner_innov_shift (j : ℕ) (t : ℤ) :
    ⟪X t, innov P X (t - j)⟫ = ⟪X 0, innov P X (-j)⟫ := by
  have := eq_apply_zero_of_succ (g := fun t ↦ ⟪X t, innov P X (t - j)⟫) (fun t ↦ by
    rw [show t + 1 - (j : ℤ) = t - j + 1 by ring, innov_succ hstat P hproj,
      ← shift_apply_X hstat t,
      inner_shift_shift hstat (mem_hull X t) (innov_mem_hull P hproj _)]) t
  simpa using this

omit [CompleteSpace H] hstat in
/-- Iterated innovations decomposition: `X_t - P_{t-k} X_t` is the sum of the components of
`X_t` along the innovations at times `t, …, t - k + 1`. -/
theorem sub_proj_eq_sum (hne : ∀ s, innov P X s ≠ 0) (t : ℤ) (k : ℕ) :
    X t - P (t - k) (X t) = ∑ j ∈ Finset.range k,
      (⟪X t, innov P X (t - j)⟫ / ‖innov P X (t - j)‖ ^ 2) • innov P X (t - j) := by
  induction k with
  | zero => simp [proj_of_mem P hproj (mem_past_self X t)]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hy : P (t - k) (X t) ∈ past X (t - k) := (hproj _ _).1
    have h1 : P (t - k) (X t) - P (t - k - 1) (P (t - k) (X t)) =
        (⟪P (t - k) (X t), innov P X (t - k)⟫ / ‖innov P X (t - k)‖ ^ 2) •
          innov P X (t - k) :=
      sub_proj_eq_smul_innov P hproj hy (hne (t - k))
    have h2 : P (t - k - 1) (P (t - k) (X t)) = P (t - ↑(k + 1)) (X t) := by
      rw [proj_proj P hproj (by omega)]
      congr 2
      push_cast
      ring
    have h3 : ⟪P (t - k) (X t), innov P X (t - k)⟫ = ⟪X t, innov P X (t - k)⟫ := by
      have := (hproj (t - k) (X t)).2 _ (innov_mem P hproj (t - k))
      rw [inner_sub_left, sub_eq_zero] at this
      exact this.symm
    calc X t - P (t - ↑(k + 1)) (X t)
        = (X t - P (t - k) (X t)) +
          (P (t - k) (X t) - P (t - k - 1) (P (t - k) (X t))) := by rw [h2]; abel
      _ = _ := by rw [h1, h3]

omit [CompleteSpace H] hstat hproj in
/-- A countable sum of elements of a closed past lies in that closed past. -/
theorem tsum_mem_past {f : ℕ → H} {t : ℤ} (hf : ∀ j, f j ∈ past X t) : ∑' j, f j ∈ past X t := by
  by_cases h : Summable f
  · exact (isClosed_past X t).mem_of_tendsto h.hasSum
      (Eventually.of_forall fun s ↦ Submodule.sum_mem _ fun j _ ↦ hf j)
  · rw [tsum_eq_zero_of_not_summable h]
    exact Submodule.zero_mem _

/-- Wold decomposition, in terms of the innovations. -/
theorem wold (he : 0 < ‖innov P X 0‖) :
    ∃ (a : ℕ → ℝ) (V : ℤ → H), a 0 = 1 ∧ Summable (fun j ↦ a j ^ 2) ∧
      (∀ t s, V t ∈ past X s) ∧ (∀ t s, ⟪V t, innov P X s⟫ = 0) ∧
      ∀ t, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j • innov P X (t - j)) + V t) atTop
        (𝓝 (X t)) := by
  set c := ‖innov P X 0‖ with hc
  have hc0 : c ≠ 0 := he.ne'
  have hnorm := norm_innov hstat P hproj
  have hne : ∀ s, innov P X s ≠ 0 := fun s ↦ by
    rw [← norm_pos_iff, hnorm]
    exact he
  let a : ℕ → ℝ := fun j ↦ ⟪X 0, innov P X (-j)⟫ / c ^ 2
  have hcoef : ∀ (t : ℤ) (j : ℕ),
      ⟪X t, innov P X (t - j)⟫ / ‖innov P X (t - j)‖ ^ 2 = a j := fun t j ↦ by
    rw [hnorm, inner_innov_shift hstat P hproj]
  have hdec : ∀ (t : ℤ) (k : ℕ),
      X t - P (t - k) (X t) = ∑ j ∈ Finset.range k, a j • innov P X (t - j) := fun t k ↦ by
    rw [sub_proj_eq_sum P hproj hne]
    simp only [hcoef]
  -- orthonormal family of normalized innovations
  have hu : ∀ t : ℤ, Orthonormal ℝ fun j : ℕ ↦ c⁻¹ • innov P X (t - j) := fun t ↦ by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right]
    split_ifs with hij
    · subst hij
      rw [real_inner_self_eq_norm_sq, hnorm, ← hc]
      field_simp
    · have h0 : ⟪innov P X (t - i), innov P X (t - j)⟫ = 0 := by
        rcases lt_or_gt_of_ne hij with h | h
        · rw [real_inner_comm]
          exact inner_innov_innov P hproj (by omega)
        · exact inner_innov_innov P hproj (by omega)
      rw [h0, mul_zero, mul_zero]
  have hA : Summable fun j ↦ a j ^ 2 := by
    refine ((hu 0).inner_products_summable (x := X 0)).mul_left (c⁻¹ ^ 2) |>.congr fun j ↦ ?_
    show c⁻¹ ^ 2 * ‖⟪c⁻¹ • innov P X (0 - j), X 0⟫‖ ^ 2 = (⟪X 0, innov P X (-j)⟫ / c ^ 2) ^ 2
    rw [zero_sub, real_inner_smul_left, real_inner_comm, Real.norm_eq_abs, sq_abs]
    field_simp
  have hS : ∀ t : ℤ, Summable fun j : ℕ ↦ a j • innov P X (t - j) := fun t ↦ by
    have key := ((hu t).orthogonalFamily.summable_iff_norm_sq_summable
      (fun j : ℕ ↦ a j * c)).2
      ((hA.mul_right (c ^ 2)).congr fun j ↦ by rw [Real.norm_eq_abs, sq_abs, mul_pow])
    refine key.congr fun j ↦ ?_
    rw [LinearIsometry.toSpanSingleton_apply, smul_smul, mul_assoc, mul_inv_cancel₀ hc0,
      mul_one]
  let V : ℤ → H := fun t ↦ X t - ∑' j, a j • innov P X (t - j)
  have hV : ∀ t s, V t ∈ past X s := by
    intro t s
    set n := (t - s).toNat
    have hsplit := (hS t).sum_add_tsum_nat_add n
    have hVt : V t = P (t - n) (X t) - ∑' j, a (j + n) • innov P X (t - ↑(j + n)) := by
      simp only [V]
      rw [← hsplit, ← hdec]
      abel
    rw [hVt]
    refine past_mono X (by omega) (sub_mem (hproj _ _).1 (tsum_mem_past fun j ↦ ?_))
    exact Submodule.smul_mem _ _
      (past_mono X (by push_cast; omega) (innov_mem P hproj (t - ↑(j + n))))
  refine ⟨a, V, ?_, ?_, hV, ?_, ?_⟩
  · have h0 : ⟪innov P X 0, P (0 - 1) (X 0)⟫ = 0 :=
      inner_innov_eq_zero P hproj 0 (hproj (0 - 1) (X 0)).1
    have hX0 : X 0 = innov P X 0 + P (0 - 1) (X 0) := by simp [innov]
    simp only [a, Nat.cast_zero, neg_zero]
    rw [hX0, inner_add_left, real_inner_comm (innov P X 0) (P (0 - 1) (X 0)), h0, add_zero,
      real_inner_self_eq_norm_sq, ← hc]
    field_simp
  · exact hA
  · intro t s
    rw [real_inner_comm]
    exact inner_innov_eq_zero P hproj s (hV t (s - 1))
  · intro t
    have h := ((hS t).hasSum.tendsto_sum_nat).add_const (V t)
    have hX : ∑' j, a j • innov P X (t - j) + V t = X t := by simp only [V]; abel
    rwa [hX] at h

end Innovations

end Wold

/-- GAPS 106.2, Wold decomposition of a weakly stationary sequence `X` in a real Hilbert space.
Let `P t` be the orthogonal projections onto the closed pasts `past X t` and
`e t = X t - P (t - 1) (X t)` the innovations, with `e 0 ≠ 0`. There are coefficients `a` with
`a 0 = 1` and `∑ a_j² < ∞`, and a sequence `V` lying in every closed past (the remote past) and
orthogonal to every innovation, such that `X t = ∑_j a_j e (t - j) + V t`. -/
theorem exists_wold_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (X : ℤ → H) (hstat : IsWeaklyStationary ℝ X) (P : ℤ → H →L[ℝ] H)
    (hproj : ∀ t x, P t x ∈ Wold.past X t ∧ ∀ y ∈ Wold.past X t, inner ℝ (x - P t x) y = 0)
    (he : 0 < ‖Wold.innov P X 0‖) :
    ∃ (a : ℕ → ℝ) (V : ℤ → H), a 0 = 1 ∧ Summable (fun j ↦ a j ^ 2) ∧
      (∀ t s, V t ∈ Wold.past X s) ∧ (∀ t s, inner ℝ (V t) (Wold.innov P X s) = 0) ∧
      ∀ t, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j • Wold.innov P X (t - j)) + V t) atTop
        (𝓝 (X t)) :=
  Wold.wold (fun s t ↦ hstat.inner_eq_inner_sub_zero s t) P hproj he

end CKSD
