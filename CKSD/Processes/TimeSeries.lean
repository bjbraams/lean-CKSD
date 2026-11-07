module

public import CKSD.Processes.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import CKSD.Processes.Dependence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearCombination

/-!
# Processes: TimeSeries

Sources: `GAPS.md`, `SYNOPSIS106.md`, and `STRUCTURE106.md`.
Declarations adapted from this project's section drafts.
The long-run variance limit regroups the double covariance sum by lag and applies Mathlib's
dominated convergence theorem for series (Tannery's theorem).
The stationary Gaussian sequence is the Kolmogorov extension (Mathlib's `projectiveLimit`) of
the finite-dimensional Gaussian laws; its stationarity follows from uniqueness of projective
limits.
The GARCH$(1,1)$ moments use independence of the noise from its strict past
(`pastSigmaAlgebra`) and monotone convergence for the series of products.
The Wold decomposition follows the innovations approach. Under a stationary Gram matrix the
unit shift `X_t ↦ X_{t+1}` extends to a linear isometry of the closed span (Mathlib's
`LinearMap.extendOfNorm` with TauCeti's `Finsupp.norm_linearCombination_eq_of_inner_eq`, in the
pattern of TauCeti's `kolmogorovIsometry`). The shift commutes with the projections onto the
closed pasts, so the innovations have constant norm and the coefficients do not depend on time.
The coefficients are square summable by Bessel's inequality, and the moving-average series
converges by Mathlib's `OrthogonalFamily.summable_iff_norm_sq_summable`.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 106.1: triangular-array martingale central limit theorem. -/
theorem tendstoInDistribution_martingale_array_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ha : ∀ n j, Measurable[F n (j + 1)] (X n j))
    (h2 : ∀ n j, MemLp (X n j) 2 μ)
    (h0 : ∀ n j, μ[X n j | F n j] =ᵐ[μ] fun _ ↦ 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hvar : TendstoInProbabilityConst μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n), μ[(fun ω ↦ X n j ω ^ 2) | F n j] ω) v)
    (hlin : ∀ ε > 0, TendstoInProbabilityConst μ (fun n ω ↦
      ∑ j ∈ Finset.range (k n),
        μ[(fun ω ↦ if ε < |X n j ω| then X n j ω ^ 2 else 0) | F n j] ω) 0) :
    TendstoInDistribution μ (fun n ω ↦ ∑ j ∈ Finset.range (k n), X n j ω)
      (gaussianReal 0 (Real.toNNReal v)) := by
  sorry

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
def canon : (ℤ →₀ ℝ) →ₗ[ℝ] hull X :=
  Finsupp.linearCombination ℝ fun t ↦ (⟨X t, mem_hull X t⟩ : hull X)

/-- The shifted coefficient map `c ↦ ∑ c_t X_{t+1}` into the closed span. -/
def shiftedCanon : (ℤ →₀ ℝ) →ₗ[ℝ] hull X :=
  Finsupp.linearCombination ℝ fun t ↦ (⟨X (t + 1), mem_hull X (t + 1)⟩ : hull X)

omit [CompleteSpace H] in
/-- The finite linear combinations of the `X_t` are dense in the closed span. -/
theorem denseRange_canon : DenseRange (canon X) := by
  intro k
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  have himage : Subtype.val '' Set.range (canon X) = (Submodule.span ℝ (Set.range X) : Set H) := by
    have h1 : ∀ f, ((canon X f : hull X) : H) = Finsupp.linearCombination ℝ X f := by
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
theorem norm_shiftedCanon (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) (f : ℤ →₀ ℝ) :
    ‖shiftedCanon X f‖ = ‖canon X f‖ :=
  f.norm_linearCombination_eq_of_inner_eq fun a b ↦ by
    change ⟪X (a + 1), X (b + 1)⟫ = ⟪X a, X b⟫
    rw [hstat, hstat a b]
    congr 2
    ring

omit [CompleteSpace H] in
/-- The shifted coefficient map is bounded by the coefficient map. -/
theorem exists_bound_shiftedCanon (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) :
    ∃ C, ∀ f, ‖shiftedCanon X f‖ ≤ C * ‖canon X f‖ :=
  ⟨1, fun f ↦ by rw [norm_shiftedCanon hstat f, one_mul]⟩

/-- With a stationary Gram matrix, the shift `X_t ↦ X_{t+1}` is a linear isometry of the
closed span. -/
def shiftIsometry (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) : hull X →ₗᵢ[ℝ] hull X :=
  LinearIsometry.mk ((shiftedCanon X).extendOfNorm (canon X)).toLinearMap fun x ↦ by
    refine (denseRange_canon X).induction_on x
      (isClosed_eq ((shiftedCanon X).extendOfNorm (canon X)).continuous.norm
        continuous_norm) ?_
    intro f
    exact calc
      ‖(shiftedCanon X).extendOfNorm (canon X) (canon X f)‖ = ‖shiftedCanon X f‖ :=
        congrArg norm (LinearMap.extendOfNorm_eq (denseRange_canon X)
          (exists_bound_shiftedCanon hstat) f)
      _ = ‖canon X f‖ := norm_shiftedCanon hstat f

/-- The shift isometry sends `X_t` to `X_{t+1}`. -/
theorem shiftIsometry_apply (hstat : ∀ s t, ⟪X s, X t⟫ = ⟪X (s - t), X 0⟫) (t : ℤ) :
    shiftIsometry hstat ⟨X t, mem_hull X t⟩ = ⟨X (t + 1), mem_hull X (t + 1)⟩ := by
  have h := LinearMap.extendOfNorm_eq (denseRange_canon X) (exists_bound_shiftedCanon hstat)
    (Finsupp.single t 1)
  simp only [canon, shiftedCanon, Finsupp.linearCombination_single, one_smul] at h
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
theorem proj_eq_of {t : ℤ} {x y : H} (hy : y ∈ past X t)
    (h : ∀ z ∈ past X t, ⟪x - y, z⟫ = 0) : P t x = y := by
  have hd : P t x - y ∈ past X t := sub_mem (hproj t x).1 hy
  have hsplit : P t x - y = (x - y) - (x - P t x) := by abel
  have h0 : ⟪P t x - y, P t x - y⟫ = 0 := by
    calc ⟪P t x - y, P t x - y⟫ = ⟪(x - y) - (x - P t x), P t x - y⟫ := by rw [← hsplit]
      _ = 0 := by rw [inner_sub_left, h _ hd, (hproj t x).2 _ hd, sub_zero]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- The projection fixes the closed past. -/
theorem proj_of_mem {t : ℤ} {x : H} (hx : x ∈ past X t) : P t x = x :=
  proj_eq_of P hproj hx fun z _ ↦ by simp

/-- Tower property of the projections onto the closed pasts. -/
theorem proj_proj {s t : ℤ} (hst : s ≤ t) (x : H) : P s (P t x) = P s x := by
  refine proj_eq_of P hproj (hproj s x).1 fun z hz ↦ ?_
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
  refine proj_eq_of P hproj (shift_mem_past hstat (hproj s x).1) fun z hz ↦ ?_
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

/-- GAPS 106.2, Wold decomposition of a stationary sequence in a real Hilbert space. -/
theorem exists_wold_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (X : ℤ → H)
    (hstat : ∀ s t, inner ℝ (X s) (X t) = inner ℝ (X (s - t)) (X 0)) :
    let past := fun t ↦ (Submodule.span ℝ {x | ∃ s : ℤ, s ≤ t ∧ x = X s}).topologicalClosure;
    ∀ (P : ℤ → H →L[ℝ] H),
    ∀ (hproj : ∀ t x, P t x ∈ past t ∧ ∀ y ∈ past t, inner ℝ (x - P t x) y = 0),
    let e := fun t ↦ X t - P (t - 1) (X t);
    ∀ (he : 0 < ‖e 0‖),
    ∃ (a : ℕ → ℝ) (V : ℤ → H), a 0 = 1 ∧ Summable (fun j ↦ a j ^ 2) ∧
      (∀ t s, V t ∈ past s) ∧ (∀ t s, inner ℝ (V t) (e s) = 0) ∧
      ∀ t, Tendsto (fun n ↦ (∑ j ∈ Finset.range n, a j • e (t - j)) + V t) atTop (𝓝 (X t)) := by
  intro past P hproj e he
  exact Wold.wold hstat P hproj he

/-- GAPS 106.4, independent-observation special case of Bartlett's theorem. -/
theorem tendstoInDistribution_sample_autocorrelations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hiid : IsIndependentIdenticallyDistributed μ X P) (h2 : MemLp id 2 P)
    (hv : 0 < variance P id) (m : ℕ) :
    TendstoInDistribution μ (fun n ω ↦ (WithLp.toLp 2 fun i : Fin m ↦
      Real.sqrt n * sampleAutocovariance X (i.val + 1) n ω / sampleAutocovariance X 0 n ω))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  sorry

/-- The lag-counting weight `#{(i, j) : i, j < n, i - j = h} / n`. -/
def lagCountWeight (n : ℕ) (h : ℤ) : ℝ :=
  (((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card : ℝ) / n

/-- A normalized double sum over `i, j < n` of a function of `i - j`, regrouped by lag. -/
theorem sum_sum_eq_tsum_lagCountWeight (γ : ℤ → ℝ) (n : ℕ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ ((i : ℤ) - j) =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
  classical
  let s := Finset.range n ×ˢ Finset.range n
  let g : ℕ × ℕ → ℤ := fun p ↦ (p.1 : ℤ) - p.2
  have hsupp : ∀ h ∉ s.image g, lagCountWeight n h * γ h = 0 := by
    intro h hh
    have : (s.filter fun p ↦ g p = h) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hp hgp
      exact hh (Finset.mem_image.2 ⟨p, hp, hgp⟩)
    simp [lagCountWeight, s, g, this]
  have hfib : ∑ p ∈ s, γ (g p) =
      ∑ h ∈ s.image g, ((s.filter fun p ↦ g p = h).card : ℝ) * γ h := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun p hp ↦ Finset.mem_image_of_mem g hp)]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [Finset.sum_congr rfl (g := fun _ ↦ γ h) (fun p hp ↦ by
      show γ (g p) = γ h
      rw [(Finset.mem_filter.1 hp).2])]
    simp
  rw [tsum_eq_sum hsupp, ← Finset.sum_product']
  change (n : ℝ)⁻¹ * ∑ p ∈ s, γ (g p) = _
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [lagCountWeight, s, g]
  ring

/-- Lag-counting weights are nonnegative. -/
theorem lagCountWeight_nonneg (n : ℕ) (h : ℤ) : 0 ≤ lagCountWeight n h := by
  unfold lagCountWeight; positivity

/-- Lag-counting weights are at most one. -/
theorem lagCountWeight_le_one (n : ℕ) (h : ℤ) : lagCountWeight n h ≤ 1 := by
  unfold lagCountWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [div_le_one (by exact_mod_cast hn)]
  have : ((Finset.range n ×ˢ Finset.range n).filter fun p : ℕ × ℕ ↦ (p.1 : ℤ) - p.2 = h).card
      ≤ (Finset.range n).card := by
    refine Finset.card_le_card_of_injOn Prod.snd (fun p hp ↦ ?_) ?_
    · simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range] at hp
      simpa using hp.1.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      have : (p.1 : ℤ) = q.1 := by rw [← hpq] at hq; linarith [hp.2, hq.2]
      exact Prod.ext (by exact_mod_cast this) hpq
  simpa using (Nat.cast_le (α := ℝ)).2 this

/-- The lower bound `(n - |h|)/n` for the lag-counting weight. -/
theorem le_lagCountWeight (n : ℕ) (h : ℤ) :
    ((n - (h.toNat + (-h).toNat) : ℕ) : ℝ) / n ≤ lagCountWeight n h := by
  unfold lagCountWeight
  gcongr
  refine (Finset.card_range _).symm.le.trans ?_
  refine Finset.card_le_card_of_injOn (fun j ↦ (j + h.toNat, j + (-h).toNat)) (fun j hj ↦ ?_) ?_
  · simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, by push_cast; omega⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    omega

/-- Lag-counting weights tend to one at each fixed lag. -/
theorem tendsto_lagCountWeight (h : ℤ) : Tendsto (fun n ↦ lagCountWeight n h) atTop (𝓝 1) := by
  set a := h.toNat + (-h).toNat
  have hlow : Tendsto (fun n : ℕ ↦ ((n - a : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 - (a : ℝ) / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)).const_sub 1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (a + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Nat.cast_sub (by omega)]
    field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n ↦ le_lagCountWeight n h) (fun n ↦ lagCountWeight_le_one n h)


/-- GAPS 106.12, long-run variance from summable autocovariances. -/
theorem tendsto_normalized_variance_eq_tsum_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ)
    (h2 : ∀ t, MemLp (X t) 2 μ) (γ : ℤ → ℝ) (hγ : Summable (fun t ↦ |γ t|))
    (hcov : ∀ s t, covariance μ (X s) (X t) = γ (s - t)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * variance μ (sampleAverage (fun j ↦ X j) n))
      atTop (𝓝 (∑' h : ℤ, γ h)) := by
  have hrepr : ∀ n : ℕ, 0 < n → (n : ℝ) * variance μ (sampleAverage (fun j ↦ X j) n) =
      ∑' h : ℤ, lagCountWeight n h * γ h := by
    intro n hn
    rw [← sum_sum_eq_tsum_lagCountWeight]
    have havg : sampleAverage (fun j : ℕ ↦ X j) n =
        fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [sampleAverage, smul_eq_mul]
    have hvar : variance μ (sampleAverage (fun j : ℕ ↦ X j) n) =
        ProbabilityTheory.covariance (sampleAverage (fun j : ℕ ↦ X j) n)
          (sampleAverage (fun j : ℕ ↦ X j) n) μ := by
      simp only [variance, ProbabilityTheory.covariance, sq]
    rw [hvar, havg, covariance_const_mul_left, covariance_const_mul_right,
      covariance_fun_sum_fun_sum' (X := fun i : ℕ ↦ X i) (Y := fun i : ℕ ↦ X i)
      (fun i _ ↦ h2 i) (fun i _ ↦ h2 i)]
    simp only [show ∀ s t, ProbabilityTheory.covariance (X s) (X t) μ = γ (s - t) from hcov]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun n h ↦ lagCountWeight n h * γ h)
    (g := γ) (bound := fun h ↦ |γ h|) hγ
    (fun h ↦ by simpa using (tendsto_lagCountWeight h).mul_const (γ h))
    (Eventually.of_forall fun n h ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lagCountWeight_nonneg n h)]
      exact mul_le_of_le_one_left (abs_nonneg _) (lagCountWeight_le_one n h))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn using (hrepr n hn).symm

/-- Coordinate selection `x ↦ (x (σ k))_k` as a continuous linear map of Euclidean spaces. -/
def euclideanSelect {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k ↦ EuclideanSpace.proj (σ k))

/-- Coordinates of a coordinate selection. -/
@[simp] theorem euclideanSelect_apply {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : κ → ι)
    (x : EuclideanSpace ℝ ι) (k : κ) : euclideanSelect σ x k = x (σ k) := rfl

/-- The image of a centred multivariate Gaussian law under the coordinate selection
`x ↦ (x (σ k))_k`, with `σ` not necessarily injective, is the centred Gaussian law with covariance
`S.submatrix σ σ`. This generalizes Mathlib's `measurePreserving_restrict₂_multivariateGaussian`,
whose proof it follows. -/
theorem map_euclideanSelect_multivariateGaussian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (σ : κ → ι) :
    (multivariateGaussian 0 S).map (euclideanSelect σ) =
      multivariateGaussian 0 (S.submatrix σ σ) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have (i : κ) : (fun u ↦ ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
        euclideanSelect σ = fun u ↦ u (σ i) := by ext; simp [PiLp.inner_apply]
    simp_rw [this, covariance_eval_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian (hS.submatrix _)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id


/-- The stationary covariance matrix `(γ (t k - t l))_{k,l}` at times `t`. -/
def stationaryCovMatrix {κ : Type*} (γ : ℤ → ℝ) (t : κ → ℤ) : Matrix κ κ ℝ :=
  Matrix.of fun k l ↦ γ (t k - t l)

/-- A symmetric positive-definite sequence gives positive-semidefinite covariance matrices at
every finite family of times. -/
theorem posSemidef_stationaryCovMatrix (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j)
    {κ : Type*} [Fintype κ] (t : κ → ℤ) : (stationaryCovMatrix γ t).PosSemidef := by
  classical
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · ext k l
    simp only [Matrix.conjTranspose_apply, stationaryCovMatrix, Matrix.of_apply, star_trivial]
    rw [← hsym, neg_sub]
  · let e := Fintype.equivFin κ
    have h1 := hpd (Fintype.card κ) (t ∘ e.symm) (x ∘ e.symm)
    have h2 : (∑ i : Fin (Fintype.card κ), ∑ j : Fin (Fintype.card κ),
        (x ∘ e.symm) i * γ ((t ∘ e.symm) i - (t ∘ e.symm) j) * (x ∘ e.symm) j) =
          ∑ k, ∑ l, x k * γ (t k - t l) * x l := by
      rw [← e.symm.sum_comp (fun k ↦ ∑ l, x k * γ (t k - t l) * x l)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← e.symm.sum_comp (fun l ↦ x (e.symm i) * γ (t (e.symm i) - t l) * x l)]
      rfl
    rw [h2] at h1
    simp only [dotProduct, Matrix.mulVec, stationaryCovMatrix, Matrix.of_apply, star_trivial,
      Finset.mul_sum]
    refine h1.trans_eq (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
    ring

/-- The finite-dimensional Gaussian laws with stationary covariance `γ`, indexed by finite sets
of times. -/
def stationaryGaussianFamily (γ : ℤ → ℝ) (J : Finset ℤ) : Measure (J → ℝ) :=
  (multivariateGaussian 0 (stationaryCovMatrix γ (fun j : J ↦ (j : ℤ)))).map (WithLp.ofLp)

/-- The stationary Gaussian laws are probability measures. -/
instance (γ : ℤ → ℝ) (J : Finset ℤ) : IsProbabilityMeasure (stationaryGaussianFamily γ J) :=
  by unfold stationaryGaussianFamily; infer_instance


/-- The stationary Gaussian laws form a projective family. -/
theorem isProjectiveMeasureFamily_stationaryGaussianFamily (γ : ℤ → ℝ)
    (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ) := by
  intro I J hJI
  let σ : J → I := fun j ↦ ⟨j, hJI j.2⟩
  have hfun : Finset.restrict₂ (π := fun _ : ℤ ↦ ℝ) hJI ∘ WithLp.ofLp =
      WithLp.ofLp ∘ euclideanSelect (ι := I) σ := by
    funext x; rfl
  have h1 : (stationaryGaussianFamily γ I).map (Finset.restrict₂ (π := fun _ : ℤ ↦ ℝ) hJI) =
      ((multivariateGaussian 0 (stationaryCovMatrix γ (fun i : I ↦ (i : ℤ)))).map
        (euclideanSelect σ)).map WithLp.ofLp := by
    rw [stationaryGaussianFamily, Measure.map_map, hfun, Measure.map_map]
    all_goals first | fun_prop | exact Finset.measurable_restrict₂ _
  rw [h1, map_euclideanSelect_multivariateGaussian (posSemidef_stationaryCovMatrix γ hsym hpd _)]
  rfl

/-- The Kolmogorov extension of the stationary Gaussian family has centred Gaussian
finite-dimensional laws with covariance `γ (t k - t l)`, for any finite family of times, with
repetitions allowed. -/
theorem map_eval_projectiveLimit_stationaryGaussianFamily (γ : ℤ → ℝ)
    (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℤ) :
    (projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ)
        (isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd)).map
      (fun x ↦ WithLp.toLp 2 (fun k ↦ x (t k))) =
      multivariateGaussian 0 (stationaryCovMatrix γ t) := by
  set hP := isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd
  let J : Finset ℤ := Finset.univ.image t
  let σ : κ → J := fun k ↦ ⟨t k, Finset.mem_image_of_mem t (Finset.mem_univ k)⟩
  have hfun : (fun x : ℤ → ℝ ↦ WithLp.toLp 2 (fun k ↦ x (t k))) =
      euclideanSelect σ ∘ WithLp.toLp 2 ∘ J.restrict := by
    funext x; rfl
  rw [hfun, ← Measure.map_map, ← Measure.map_map, isProjectiveLimit_projectiveLimit hP J,
    stationaryGaussianFamily, Measure.map_map (WithLp.measurable_toLp _ _)
    (WithLp.measurable_ofLp _ _)]
  rotate_left
  any_goals fun_prop
  have : (WithLp.toLp 2 ∘ WithLp.ofLp : EuclideanSpace ℝ J → EuclideanSpace ℝ J) = id := by
    funext x; rfl
  rw [this, Measure.map_id,
    map_euclideanSelect_multivariateGaussian (posSemidef_stationaryCovMatrix γ hsym hpd _)]
  rfl

/-- GAPS 106.14, real Gaussian realization of a positive-definite stationary covariance. -/
theorem exists_stationary_gaussian_process_of_posSemidef (γ : ℤ → ℝ) (hsym : ∀ t, γ (-t) = γ t)
    (hpd : ∀ n : ℕ, ∀ (t : Fin n → ℤ) (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i * γ (t i - t j) * a j) :
    ∃ P : Measure (ℤ → ℝ), IsProbabilityMeasure P ∧
      (∀ h : ℤ, P.map (fun x t ↦ x (t + h)) = P) ∧
      ∀ n : ℕ, ∀ t : Fin n → ℤ,
        P.map (fun x ↦ WithLp.toLp 2 (fun i : Fin n ↦ x (t i))) =
          multivariateGaussian 0 (fun i j ↦ γ (t i - t j)) := by
  set hP := isProjectiveMeasureFamily_stationaryGaussianFamily γ hsym hpd
  set Q := projectiveLimit (α := fun _ : ℤ ↦ ℝ) (stationaryGaussianFamily γ) hP
  refine ⟨Q, inferInstance, fun h ↦ ?_, fun n t ↦
    map_eval_projectiveLimit_stationaryGaussianFamily γ hsym hpd t⟩
  have hshift : Measurable fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h) :=
    Measurable.of_eval fun t ↦ measurable_pi_apply (t + h)
  refine IsProjectiveLimit.unique (α := fun _ : ℤ ↦ ℝ) (P := stationaryGaussianFamily γ) (fun J ↦ ?_)
    (isProjectiveLimit_projectiveLimit hP)
  rw [Measure.map_map (Finset.measurable_restrict J) hshift]
  have hfun : (J.restrict ∘ fun (x : ℤ → ℝ) (t : ℤ) ↦ x (t + h)) =
      WithLp.ofLp ∘ fun x ↦ WithLp.toLp 2 (fun j : J ↦ x ((j : ℤ) + h)) := by
    funext x; rfl
  rw [hfun, ← Measure.map_map, map_eval_projectiveLimit_stationaryGaussianFamily γ hsym hpd,
    stationaryGaussianFamily]
  rotate_left
  · exact WithLp.measurable_ofLp _ _
  · exact (WithLp.measurable_toLp _ _).comp (Measurable.of_eval fun j ↦ measurable_pi_apply _)
  congr 2
  ext i j
  simp [stationaryCovMatrix]

/-- A function measurable with respect to `σ(ε_s : s ∈ S)` is independent of `ε_k` for `k ∉ S`,
for an independent family `ε`. -/
theorem indepFun_of_measurable_iSup {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    {S : Set ℤ} {k : ℤ} (hk : k ∉ S) {Y : Ω → ℝ}
    (hY : Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] Y) :
    IndepFun Y (ε k) μ := by
  have h := indep_iSup_of_disjoint (m := fun s ↦ MeasurableSpace.comap (ε s) inferInstance)
    (fun s ↦ (hm s).comap_le) hind.iIndep (S := S) (T := {k})
    (Set.disjoint_singleton_right.2 hk)
  rw [iSup_singleton] at h
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left h hY.comap_le

/-- A function of the strict past `σ(ε_s : s < t)` of an independent sequence is independent
of `ε_t`. -/
theorem indepFun_of_measurable_pastSigmaAlgebra {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (t : ℤ) {Y : Ω → ℝ} (hY : Measurable[pastSigmaAlgebra ε (t - 1)] Y) :
    IndepFun Y (ε t) μ :=
  indepFun_of_measurable_iSup hm hind (S := {s | s ≤ t - 1}) (by simp) hY

/-- The coordinate `ε_s` is measurable with respect to the past `σ(ε_r : r ≤ t)` when `s ≤ t`. -/
theorem measurable_pastSigmaAlgebra_of_le {Ω : Type*} [MeasurableSpace Ω]
    {ε : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    Measurable[pastSigmaAlgebra ε t] (ε s) :=
  Measurable.of_comap_le (le_iSup₂_of_le s hst le_rfl)

/-- The past σ-algebras increase with time. -/
theorem pastSigmaAlgebra_mono {Ω : Type*} (ε : ℤ → Ω → ℝ) {s t : ℤ} (hst : s ≤ t) :
    pastSigmaAlgebra ε s ≤ pastSigmaAlgebra ε t :=
  iSup₂_le fun r hr ↦ le_iSup₂_of_le r (hr.trans hst) le_rfl

/-- The past σ-algebras of a measurable process are sub-σ-algebras. -/
theorem pastSigmaAlgebra_le {Ω : Type*} [MeasurableSpace Ω] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (t : ℤ) : pastSigmaAlgebra ε t ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun r _ ↦ (hm r).comap_le

/-- The GARCH coefficient `b + a ε_{t-j-1}²`. -/
def garchCoeff {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  b + a * ε (t - j - 1) ω ^ 2

/-- The GARCH product `∏_{j<n} (b + a ε_{t-j-1}²)`. -/
def garchTerm {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range n, garchCoeff a b ε t j ω

/-- The GARCH products are nonnegative. -/
theorem garchTerm_nonneg {Ω : Type*} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℤ → Ω → ℝ)
    (t : ℤ) (n : ℕ) (ω : Ω) : 0 ≤ garchTerm a b ε t n ω :=
  Finset.prod_nonneg fun j _ ↦ by unfold garchCoeff; positivity

/-- The GARCH product at time `t` is a function of the strict past of the noise. -/
theorem measurable_garchTerm {Ω : Type*} [MeasurableSpace Ω] (a b : ℝ) (ε : ℤ → Ω → ℝ)
    (t : ℤ) (n : ℕ) : Measurable[pastSigmaAlgebra ε (t - 1)] (garchTerm a b ε t n) := by
  unfold garchTerm garchCoeff
  refine Finset.measurable_prod _ fun j _ ↦ ?_
  have := measurable_pastSigmaAlgebra_of_le (ε := ε) (s := t - j - 1) (t := t - 1) (by omega)
  exact measurable_const.add (measurable_const.mul (this.pow_const 2))

/-- The GARCH product at time `t` is measurable with respect to the noise at any set of times
containing `t - j - 1` for `j < n`. -/
theorem measurable_garchTerm_iSup {Ω : Type*} [MeasurableSpace Ω] (a b : ℝ)
    (ε : ℤ → Ω → ℝ) (t : ℤ) (n : ℕ) {S : Set ℤ} (hS : ∀ j < n, t - j - 1 ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (garchTerm a b ε t n) := by
  unfold garchTerm garchCoeff
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  have : Measurable[⨆ s ∈ S, MeasurableSpace.comap (ε s) inferInstance] (ε (t - j - 1)) :=
    Measurable.of_comap_le (le_iSup₂_of_le (t - j - 1) (hS j (Finset.mem_range.1 hj)) le_rfl)
  exact measurable_const.add (measurable_const.mul (this.pow_const 2))

/-- The GARCH product of length `n` is integrable with mean `(b + a)^n`, by independence of the
noise at distinct times. -/
theorem integrable_garchTerm_and_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) (a b : ℝ) (t : ℤ) (n : ℕ) :
    Integrable (garchTerm a b ε t n) μ ∧ ∫ ω, garchTerm a b ε t n ω ∂μ = (b + a) ^ n := by
  have hsq : ∀ k, Integrable (fun ω ↦ ε k ω ^ 2) μ ∧ ∫ ω, ε k ω ^ 2 ∂μ = 1 := by
    intro k
    have hid : IdentDistrib (ε k) (ε 0) μ μ :=
      ⟨(hm k).aemeasurable, (hm 0).aemeasurable, hlaw k⟩
    have hid2 := hid.comp (measurable_id.pow_const 2)
    refine ⟨?_, ?_⟩
    · exact hid2.integrable_iff.2 (h2.integrable_sq)
    · rw [← h1]; exact hid2.integral_eq
  have hcoeff : ∀ j, Integrable (garchCoeff a b ε t j) μ ∧
      ∫ ω, garchCoeff a b ε t j ω ∂μ = b + a := by
    intro j
    obtain ⟨hi, he⟩ := hsq (t - j - 1)
    refine ⟨(integrable_const b).add (hi.const_mul a), ?_⟩
    simp only [garchCoeff]
    rw [integral_add (integrable_const b) (hi.const_mul a), integral_const_mul, he]
    simp
  induction n with
  | zero =>
    have : garchTerm a b ε t 0 = fun _ ↦ 1 := by funext ω; simp [garchTerm]
    rw [this]
    exact ⟨integrable_const _, by simp⟩
  | succ n ih =>
    have hfun : garchTerm a b ε t (n + 1) = garchTerm a b ε t n * garchCoeff a b ε t n := by
      funext ω; simp [garchTerm, Finset.prod_range_succ]
    have hY := measurable_garchTerm_iSup a b ε t n (S := {s | t - n ≤ s})
      (fun j hj ↦ by simp only [mem_ofPred_eq]; omega)
    have hindep : IndepFun (garchTerm a b ε t n) (garchCoeff a b ε t n) μ := by
      have := (indepFun_of_measurable_iSup hm hind (k := t - n - 1)
        (by simp only [mem_ofPred_eq]; omega) hY).comp measurable_id
          (measurable_const.add (measurable_const.mul (measurable_id.pow_const 2)) :
            Measurable fun x : ℝ ↦ b + a * x ^ 2)
      exact this
    rw [hfun]
    refine ⟨hindep.integrable_mul ih.1 (hcoeff n).1, ?_⟩
    rw [IndepFun.integral_mul_eq_mul_integral hindep ih.1.aestronglyMeasurable
      (hcoeff n).1.aestronglyMeasurable, ih.2, (hcoeff n).2, pow_succ]


/-- When `a + b < 1`, the GARCH series `∑_n ∏_{j<n} (b + a ε_{t-j-1}²)` converges almost surely,
is integrable, and has mean `(1 - (b + a))⁻¹`; the proof uses monotone convergence. -/
theorem garch_tsum_properties {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (t : ℤ) :
    (∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω) ∧
      Integrable (fun ω ↦ ∑' n, garchTerm a b ε t n ω) μ ∧
      ∫ ω, ∑' n, garchTerm a b ε t n ω ∂μ = (1 - (b + a))⁻¹ := by
  have hI := integrable_garchTerm_and_integral hm hind hlaw h2 h1 a b t
  have h0 := garchTerm_nonneg ha hb ε t
  have hmeas : ∀ n, Measurable (garchTerm a b ε t n) := fun n ↦
    (measurable_garchTerm a b ε t n).mono (pastSigmaAlgebra_le hm _) le_rfl
  have hgeo0 : 0 ≤ b + a := by linarith
  have hgeo1 : b + a < 1 := by linarith
  have hsum : Summable fun n : ℕ ↦ (b + a) ^ n := summable_geometric_of_lt_one hgeo0 hgeo1
  have hlin : ∫⁻ ω, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) ∂μ =
      ENNReal.ofReal (∑' n : ℕ, (b + a) ^ n) := by
    rw [lintegral_tsum fun n ↦ (hmeas n).ennreal_ofReal.aemeasurable,
      ENNReal.ofReal_tsum_of_nonneg (fun n ↦ pow_nonneg hgeo0 n) hsum]
    congr 1
    funext n
    rw [← (hI n).2, ofReal_integral_eq_lintegral_ofReal (hI n).1 (ae_of_all _ (h0 n))]
  have hfin : ∀ᵐ ω ∂μ, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun n ↦ (hmeas n).ennreal_ofReal.aemeasurable)
      (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  have hsumm : ∀ᵐ ω ∂μ, Summable fun n ↦ garchTerm a b ε t n ω := by
    filter_upwards [hfin] with ω hω
    have : Summable fun n ↦ ((garchTerm a b ε t n ω).toNNReal : ℝ) :=
      NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hω.ne)
    simpa only [Real.coe_toNNReal _ (h0 _ ω)] using this
  have hVmeas : Measurable fun ω ↦ ∑' n, garchTerm a b ε t n ω := Measurable.tsum hmeas
  refine ⟨hsumm, ⟨hVmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ tsum_nonneg fun n ↦ h0 n ω)]
    calc ∫⁻ ω, ENNReal.ofReal (∑' n, garchTerm a b ε t n ω) ∂μ
        = ∫⁻ ω, ∑' n, ENNReal.ofReal (garchTerm a b ε t n ω) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsumm] with ω hω
          exact ENNReal.ofReal_tsum_of_nonneg (fun n ↦ h0 n ω) hω
      _ < ∞ := by rw [hlin]; exact ENNReal.ofReal_lt_top
  · rw [← integral_tsum_of_summable_integral_norm (fun n ↦ (hI n).1)]
    · simp_rw [(hI _).2]
      exact tsum_geometric_of_lt_one hgeo0 hgeo1
    · refine hsum.congr fun n ↦ ?_
      rw [← (hI n).2]
      exact (integral_congr_ae (ae_of_all _ fun ω ↦ Real.norm_of_nonneg (h0 n ω))).symm


/-- First and second moments of the GARCH noise at every time. -/
theorem garch_noise_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1) (k : ℤ) :
    Integrable (ε k) μ ∧ ∫ ω, ε k ω ∂μ = 0 ∧
      Integrable (fun ω ↦ ε k ω ^ 2) μ ∧ ∫ ω, ε k ω ^ 2 ∂μ = 1 := by
  have hid : IdentDistrib (ε k) (ε 0) μ μ :=
    ⟨(hm k).aemeasurable, (hm 0).aemeasurable, hlaw k⟩
  have hid2 := hid.comp (measurable_id.pow_const 2)
  refine ⟨hid.integrable_iff.2 (h2.integrable one_le_two), by rw [← h0]; exact hid.integral_eq,
    hid2.integrable_iff.2 h2.integrable_sq, ?_⟩
  rw [← h1]; exact hid2.integral_eq

/-- The GARCH series at time `t` is a function of the strict past of the noise. -/
theorem measurable_tsum_garchTerm_past {Ω : Type*} (a b : ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) :
    Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ ∑' n, garchTerm a b ε t n ω := by
  let _ := pastSigmaAlgebra ε (t - 1)
  exact Measurable.tsum fun n ↦ measurable_garchTerm a b ε t n

/-- GAPS 106.18, finite-variance GARCH series when `alpha + beta < 1`. -/
theorem garch_series_summable_and_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε μ)
    (hlaw : ∀ t, μ.map (ε t) = μ.map (ε 0)) (h2 : MemLp (ε 0) 2 μ)
    (h0 : (∫ ω, ε 0 ω ∂μ) = 0) (h1 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1)
    (a₀ a b : ℝ) (ha₀ : 0 < a₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) :
    let V := fun t ω ↦ a₀ * ∑' n : ℕ,
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2);
    let X := fun t ω ↦ Real.sqrt (V t ω) * ε t ω;
    (∀ t, ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦
      ∏ j ∈ Finset.range n, (b + a * ε (t - j - 1) ω ^ 2))) ∧
      (∀ t, (∫ ω, V t ω ∂μ) = a₀ / (1 - a - b)) ∧
      (∀ t, ∀ᵐ ω ∂μ, V t ω = a₀ + a * X (t - 1) ω ^ 2 + b * V (t - 1) ω) ∧
      ∀ s t, covariance μ (X s) (X t) = if s = t then a₀ / (1 - a - b) else 0 := by
  intro V X
  have props := garch_tsum_properties hm hind hlaw h2 h1 ha hb hab
  have hV : ∀ t, V t = fun ω ↦ a₀ * ∑' n, garchTerm a b ε t n ω := fun t ↦ rfl
  have hab' : 1 - a - b ≠ 0 := by linarith
  have hVint : ∀ t, ∫ ω, V t ω ∂μ = a₀ / (1 - a - b) := fun t ↦ by
    rw [hV, integral_const_mul, (props t).2.2, div_eq_mul_inv]
    ring_nf
  have hVnn : ∀ t ω, 0 ≤ V t ω := fun t ω ↦
    mul_nonneg ha₀.le (tsum_nonneg fun n ↦ garchTerm_nonneg ha hb ε t n ω)
  refine ⟨fun t ↦ (props t).1, hVint, fun t ↦ ?_, fun s t ↦ ?_⟩
  · filter_upwards [(props (t - 1)).1] with ω hω
    have hshift : ∀ n, garchTerm a b ε t (n + 1) ω =
        garchTerm a b ε (t - 1) n ω * (b + a * ε (t - 1) ω ^ 2) := by
      intro n
      simp only [garchTerm, Finset.prod_range_succ']
      congr 1
      · refine Finset.prod_congr rfl fun j _ ↦ ?_
        simp only [garchCoeff]
        rw [show t - ((j + 1 : ℕ) : ℤ) - 1 = t - 1 - (j : ℤ) - 1 by push_cast; ring]
      · simp [garchCoeff]
    have hsumt : Summable fun n ↦ garchTerm a b ε t n ω := by
      rw [← summable_nat_add_iff 1]
      simp_rw [hshift]
      exact hω.mul_right _
    have hX2 : X (t - 1) ω ^ 2 = V (t - 1) ω * ε (t - 1) ω ^ 2 := by
      simp only [X, mul_pow, Real.sq_sqrt (hVnn _ _)]
    rw [hX2, hV, hV]
    simp only
    rw [hsumt.tsum_eq_zero_add]
    simp_rw [hshift]
    rw [tsum_mul_right]
    simp only [garchTerm, Finset.range_zero, Finset.prod_empty]
    ring
  have hVmeasP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] (V t) := fun t ↦
    (measurable_tsum_garchTerm_past a b ε t).const_mul a₀
  have hVmeas : ∀ t, Measurable (V t) := fun t ↦
    (hVmeasP t).mono (pastSigmaAlgebra_le hm _) le_rfl
  have hVint' : ∀ t, Integrable (V t) μ := fun t ↦ (props t).2.1.const_mul a₀
  have hnoise := garch_noise_moments hm hlaw h2 h0 h1
  have hsqrtP : ∀ t, Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ Real.sqrt (V t ω) :=
    fun t ↦ Real.continuous_sqrt.measurable.comp (hVmeasP t)
  have hXmeas : ∀ t, Measurable (X t) := fun t ↦
    (Real.continuous_sqrt.measurable.comp (hVmeas t)).mul (hm t)
  have hXP : ∀ s t, s < t → Measurable[pastSigmaAlgebra ε (t - 1)] (X s) := fun s t hst ↦
    (Real.continuous_sqrt.measurable.comp
      ((hVmeasP s).mono (pastSigmaAlgebra_mono ε (by omega)) le_rfl)).mul
      (measurable_pastSigmaAlgebra_of_le (by omega))
  have hEX : ∀ t, ∫ ω, X t ω ∂μ = 0 := fun t ↦ by
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t (hsqrtP t)
    rw [show X t = (fun ω ↦ Real.sqrt (V t ω)) * ε t from rfl,
      IndepFun.integral_mul_eq_mul_integral hind'
        (Real.continuous_sqrt.measurable.comp (hVmeas t)).aestronglyMeasurable
        (hm t).aestronglyMeasurable, (hnoise t).2.1, mul_zero]
  have hX2 : ∀ t, (fun ω ↦ X t ω * X t ω) = V t * fun ω ↦ ε t ω ^ 2 := fun t ↦ by
    funext ω
    simp only [X, Pi.mul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hVnn _ _), sq]
  have hindV2 : ∀ t, IndepFun (V t) (fun ω ↦ ε t ω ^ 2) μ := fun t ↦
    (indepFun_of_measurable_pastSigmaAlgebra hm hind t (hVmeasP t)).comp measurable_id
      (measurable_id.pow_const 2)
  have hXL2 : ∀ t, MemLp (X t) 2 μ := fun t ↦ by
    refine (memLp_two_iff_integrable_sq (hXmeas t).aestronglyMeasurable).2 ?_
    have := (hindV2 t).integrable_mul (hVint' t) (hnoise t).2.2.1
    rw [← hX2 t] at this
    simpa only [sq] using this
  have hEX2 : ∀ t, ∫ ω, X t ω * X t ω ∂μ = a₀ / (1 - a - b) := fun t ↦ by
    rw [hX2 t, IndepFun.integral_mul_eq_mul_integral (hindV2 t) (hVmeas t).aestronglyMeasurable
      ((hm t).pow_const 2).aestronglyMeasurable, hVint, (hnoise t).2.2.2, mul_one]
  have hcross : ∀ s t, s < t → ∫ ω, X s ω * X t ω ∂μ = 0 := fun s t hst ↦ by
    have hmeasP : Measurable[pastSigmaAlgebra ε (t - 1)] fun ω ↦ X s ω * Real.sqrt (V t ω) :=
      (hXP s t hst).mul (hsqrtP t)
    have hind' := indepFun_of_measurable_pastSigmaAlgebra hm hind t hmeasP
    have hfun : (fun ω ↦ X s ω * X t ω) =
        (fun ω ↦ X s ω * Real.sqrt (V t ω)) * ε t := by
      funext ω; simp only [X, Pi.mul_apply]; ring
    rw [hfun, IndepFun.integral_mul_eq_mul_integral hind'
      ((hmeasP.mono (pastSigmaAlgebra_le hm _) le_rfl).aestronglyMeasurable)
      (hm t).aestronglyMeasurable, (hnoise t).2.1, mul_zero]
  change ProbabilityTheory.covariance (X s) (X t) μ = _
  rw [covariance_eq_sub (hXL2 s) (hXL2 t), hEX s, hEX t, mul_zero, sub_zero]
  simp only [Pi.mul_apply]
  split_ifs with hst
  · subst hst; exact hEX2 s
  · rcases lt_or_gt_of_ne hst with h | h
    · exact hcross s t h
    · simp_rw [mul_comm (X s _)]
      exact hcross t s h


end CKSD
