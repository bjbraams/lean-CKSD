module

public import CKSD.Learning.Algorithms
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Probability.Moments.SampleMean

/-!
# Neural approximation and Fourier moment classes

Fourier transforms and logistic activation are Mathlib constructions. A finite network uses the
one-hidden-layer realization already defined in `CKSD.Learning.Algorithms`, with an output bias.
The Barron statement covers the logistic activation. The ReLU statement is a distinct elementary
one-dimensional interpolation scope and does not assert the full multivariate Sobolev theorem.
Sources: GAPS 107.28 and 107.36.
The feature-sampling argument uses TauCeti's Hilbert-space sample-mean variance theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators FourierTransform

namespace CKSD

/-- First absolute Fourier moment in Mathlib's `exp(-2πi⟨x,ω⟩)` normalization. -/
def barronFourierMoment {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ w, ‖w‖ * ‖𝓕 (fun x ↦ (f x : ℂ)) w‖

/-- One-hidden-layer logistic network with a separate output bias. -/
def logisticNetwork {d N : ℕ} (a : Fin N → ℝ)
    (w : Fin N → EuclideanSpace ℝ (Fin d)) (b : Fin N → ℝ)
    (bias : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  bias + twoLayerPredictor Real.sigmoid a w b x

/-- GAPS 107.28: Barron's `N⁻¹/²` logistic approximation rate on the unit ball.
The squared-error form uses a universal constant and the first absolute Fourier moment.
The target is continuous on the whole space, which fixes its representative on singular laws. -/
theorem exists_logisticNetwork_sq_error_le_barron_moment :
    ∃ C > (0 : ℝ), ∀ d N : ℕ, 0 < d → 0 < N →
      ∀ μ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ →
      μ (Metric.closedBall 0 1) = 1 →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Continuous f → Integrable f volume →
      Integrable (fun w ↦ ‖w‖ * ‖𝓕 (fun x ↦ (f x : ℂ)) w‖) volume →
      ∃ (a : Fin N → ℝ) (w : Fin N → EuclideanSpace ℝ (Fin d)) (b : Fin N → ℝ) (bias : ℝ),
        (∫ x, (logisticNetwork a w b bias x - f x) ^ 2 ∂μ) ≤
          C * barronFourierMoment f ^ 2 / N := by
  sorry

/-- Centering a square-integrable Hilbert-space function reduces its second moment. -/
theorem integral_norm_sub_integral_sq_le {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] (ν : Measure S) [IsProbabilityMeasure ν]
    (f : S → H) (hf : MemLp f 2 ν) :
    (∫ s, ‖f s - ∫ t, f t ∂ν‖ ^ 2 ∂ν) ≤ ∫ s, ‖f s‖ ^ 2 ∂ν := by
  let m := ∫ s, f s ∂ν
  have hi := hf.integrable one_le_two
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hin : Integrable (fun s ↦ inner ℝ m (f s)) ν := hi.const_inner m
  have hmul : Integrable (fun s ↦ 2 * inner ℝ m (f s)) ν := hin.const_mul 2
  have hsub : Integrable (fun s ↦ ‖f s‖ ^ 2 - 2 * inner ℝ m (f s)) ν := hs.sub hmul
  have hpoint : ∀ s, ‖f s - m‖ ^ 2 =
      ‖f s‖ ^ 2 - 2 * inner ℝ m (f s) + ‖m‖ ^ 2 := by
    intro s
    rw [norm_sub_sq_real, real_inner_comm]
  have hexp : (∫ s, ‖f s - m‖ ^ 2 ∂ν) =
      (∫ s, ‖f s‖ ^ 2 ∂ν) - ‖m‖ ^ 2 := by
    simp_rw [hpoint]
    rw [integral_add hsub (integrable_const _),
      integral_sub hs hmul, integral_const_mul, integral_inner hi]
    simp only [m, integral_const, probReal_univ, one_smul, real_inner_self_eq_norm_sq]
    ring
  change (∫ s, ‖f s - m‖ ^ 2 ∂ν) ≤ _
  rw [hexp]
  exact sub_le_self _ (sq_nonneg _)

/-- GAPS 107.28, Hilbert-space sampling step: an integral feature mean admits a finite average
with squared error bounded by its second moment divided by the number of features. -/
theorem exists_feature_average_sq_error_le {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ν : Measure S) [IsProbabilityMeasure ν] (feature : S → H)
    (hf : MemLp feature 2 ν) (N : ℕ) (hN : 0 < N) :
    ∃ x : Fin N → S,
      ‖(N : ℝ)⁻¹ • (∑ j, feature (x j)) - ∫ s, feature s ∂ν‖ ^ 2 ≤
        (∫ s, ‖feature s‖ ^ 2 ∂ν) / N := by
  let : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let P : Measure (Fin N → S) := Measure.pi (fun _ ↦ ν)
  let X : Fin N → (Fin N → S) → H := fun i x ↦ feature (x i)
  let m := ∫ s, feature s ∂ν
  have hX : ∀ i, MemLp (X i) 2 P := fun i ↦
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N ↦ ν) i)
  have hmean : ∀ i, (∫ x, X i x ∂P) = m := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin N ↦ ν) i
    have heq := (integral_map hp.measurable.aemeasurable
      (hp.map_eq.symm ▸ hf.aestronglyMeasurable)).symm
    rw [hp.map_eq] at heq
    exact heq
  have hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) P :=
    fun i j hij ↦ (iIndepFun_pi (fun _ : Fin N ↦ hf.aemeasurable)).indepFun hij
  have hvar : ∀ i, (∫ x, ‖X i x - m‖ ^ 2 ∂P) ≤ ∫ s, ‖feature s‖ ^ 2 ∂ν := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin N ↦ ν) i
    have hasm := (hf.sub (memLp_const m)).aestronglyMeasurable.norm.pow 2
    have heq := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hasm)
    simp only [Pi.pow_apply, Pi.sub_apply] at heq
    rw [hp.map_eq] at heq
    exact heq.symm.le.trans (integral_norm_sub_integral_sq_le ν feature hf)
  have hbound := TauCeti.integral_norm_finiteMean_sub_sq_le_of_forall_le
    hX hmean hindep hvar
  have havg : MemLp (fun x ↦ TauCeti.finiteMean ℝ (X · x) - m) 2 P := by
    simp only [TauCeti.finiteMean_eq_inv_smul_sum]
    exact ((memLp_finsetSum Finset.univ (fun i _ ↦ hX i)).const_smul _).sub (memLp_const m)
  obtain ⟨x, hx⟩ := exists_le_integral
    ((memLp_two_iff_integrable_sq_norm havg.aestronglyMeasurable).1 havg)
  refine ⟨x, ?_⟩
  simpa only [TauCeti.finiteMean_eq_inv_smul_sum, Fintype.card_fin] using hx.trans hbound

/-- Slope between consecutive points of the uniform grid on `[0,1]`. -/
def uniformGridSlope (f : ℝ → ℝ) (N j : ℕ) : ℝ :=
  (N : ℝ) * (f (((j + 1 : ℕ) : ℝ) / N) - f ((j : ℝ) / N))

/-- Uniform-grid piecewise linear interpolant in its affine-plus-ReLU representation. -/
def reluLinearInterpolant (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  f 0 + uniformGridSlope f N 0 * x +
    ∑ j ∈ Finset.range (N - 1), (uniformGridSlope f N (j + 1) - uniformGridSlope f N j) *
      relu (x - ((j + 1 : ℕ) : ℝ) / N)

/-- One-sided chord bound: if `f` is `C²` with `f'' ≥ -B` on `[0,1]`, then on a subinterval
`[u, v]` the function exceeds its chord by at most `B (x - u)(v - x) / 2`. -/
theorem sub_chord_le_of_deriv2_ge (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ)
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, -B ≤ deriv (deriv f) x) {u v x : ℝ} (hu : 0 ≤ u)
    (huv : u < v) (hv : v ≤ 1) (hx : x ∈ Icc u v) :
    f x - (f u + (f v - f u) / (v - u) * (x - u)) ≤ B / 2 * ((x - u) * (v - x)) := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf' : Differentiable ℝ (deriv f) := by
    have hf2 : ContDiff ℝ (1 + 1) f := by convert hf; norm_num
    exact (contDiff_succ_iff_deriv.mp hf2).2.2.differentiable (by norm_num)
  set g : ℝ → ℝ := fun y ↦ f y + B / 2 * y ^ 2 with hg_def
  have hdg : deriv g = fun y ↦ deriv f y + B * y := by
    funext y
    have h := ((hdf y).hasDerivAt.add ((hasDerivAt_pow 2 y).const_mul (B / 2))).deriv
    rw [hg_def]
    refine h.trans ?_
    simp only [Nat.cast_ofNat]
    ring
  have hconv : ConvexOn ℝ (Icc 0 1) g := by
    refine convexOn_of_deriv2_nonneg' (convex_Icc 0 1) ?_ ?_ fun y hy ↦ ?_
    · exact (hdf.add (by fun_prop)).differentiableOn
    · rw [hdg]
      exact (hdf'.add (by fun_prop)).differentiableOn
    · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      have h := ((hdf' y).hasDerivAt.add ((hasDerivAt_id y).const_mul B)).deriv
      rw [hdg]
      have h' : deriv (fun y ↦ deriv f y + B * y) y = deriv (deriv f) y + B * 1 := h
      rw [h']
      linarith [hlow y hy]
  have hvu : 0 < v - u := sub_pos.mpr huv
  set θ := (v - x) / (v - u) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hx.2]) hvu.le
  have hθ1 : 0 ≤ 1 - θ := by
    rw [hθ, one_sub_div hvu.ne']
    exact div_nonneg (by linarith [hx.1]) hvu.le
  have hxθ : θ • u + (1 - θ) • v = x := by
    simp only [smul_eq_mul, hθ]
    field_simp
    ring
  have h := hconv.2 (⟨hu, huv.le.trans hv⟩ : u ∈ Icc (0 : ℝ) 1)
    (⟨hu.trans huv.le, hv⟩ : v ∈ Icc (0 : ℝ) 1) hθ0 hθ1 (by ring)
  rw [hxθ] at h
  simp only [smul_eq_mul, hg_def] at h
  have hθ' : 1 - θ = (x - u) / (v - u) := by
    rw [hθ]; field_simp; ring
  rw [hθ'] at h
  have key : f x - (f u + (f v - f u) / (v - u) * (x - u)) - B / 2 * ((x - u) * (v - x)) =
      f x + B / 2 * x ^ 2 - (θ * (f u + B / 2 * u ^ 2) +
        (x - u) / (v - u) * (f v + B / 2 * v ^ 2)) := by
    rw [hθ]
    field_simp
    ring
  linarith

/-- Linear interpolation error on a subinterval of `[0,1]` for a `C²` function with
`|f''| ≤ B` there: `|chord(x) - f(x)| ≤ B (v - u)² / 8`. -/
theorem abs_chord_sub_le (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv f) x| ≤ B) {u v x : ℝ} (hu : 0 ≤ u)
    (huv : u < v) (hv : v ≤ 1) (hx : x ∈ Icc u v) :
    |f u + (f v - f u) / (v - u) * (x - u) - f x| ≤ B * (v - u) ^ 2 / 8 := by
  have h1 := sub_chord_le_of_deriv2_ge f hf B (fun y hy ↦ (abs_le.mp (hbound y hy)).1)
    hu huv hv hx
  have hnf : ContDiff ℝ 2 (-f) := hf.neg
  have hdd : ∀ y, deriv (deriv (-f)) y = -deriv (deriv f) y := fun y ↦ by
    rw [deriv.neg']
    exact deriv.neg (f := deriv f)
  have h2 := sub_chord_le_of_deriv2_ge (-f) hnf B
    (fun y hy ↦ by rw [hdd]; linarith [(abs_le.mp (hbound y hy)).2]) hu huv hv hx
  simp only [Pi.neg_apply] at h2
  have hq : (x - u) * (v - x) ≤ (v - u) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - u - v)]
  have hq' : B / 2 * ((x - u) * (v - x)) ≤ B * (v - u) ^ 2 / 8 := by
    nlinarith
  rw [abs_le]
  constructor
  · linarith
  · have : -f x - (-f u + (-f v - -f u) / (v - u) * (x - u)) =
        f u + (f v - f u) / (v - u) * (x - u) - f x := by ring
    linarith

/-- Telescoping form of the ReLU interpolant's affine pieces: the affine term plus the first
`j` hinge corrections is the line through `(j/N, f(j/N))` with slope `s_j`. -/
theorem affine_add_sum_hinge_eq (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (x : ℝ) (j : ℕ) :
    f 0 + uniformGridSlope f N 0 * x +
      ∑ k ∈ Finset.range j, (uniformGridSlope f N (k + 1) - uniformGridSlope f N k) *
        (x - ((k + 1 : ℕ) : ℝ) / N) =
      f ((j : ℝ) / N) + uniformGridSlope f N j * (x - (j : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have hs : f (((j + 1 : ℕ) : ℝ) / N) = f ((j : ℝ) / N) + uniformGridSlope f N j / N := by
      simp only [uniformGridSlope]
      field_simp
      ring
    rw [hs]
    push_cast
    field_simp
    ring

/-- On the grid cell `[j/N, (j+1)/N]`, `j < N`, the ReLU interpolant is the chord of `f`. -/
theorem reluLinearInterpolant_eq_of_mem (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j < N)
    {x : ℝ} (hx : x ∈ Icc ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N)) :
    reluLinearInterpolant f N x =
      f ((j : ℝ) / N) + uniformGridSlope f N j * (x - (j : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← affine_add_sum_hinge_eq f hN x j, reluLinearInterpolant,
    ← Finset.sum_range_add_sum_Ico _ (Nat.le_sub_one_of_lt hj)]
  have hzero : ∑ k ∈ Finset.Ico j (N - 1),
      (uniformGridSlope f N (k + 1) - uniformGridSlope f N k) *
        relu (x - ((k + 1 : ℕ) : ℝ) / N) = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk : j + 1 ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
    have : x ≤ ((k + 1 : ℕ) : ℝ) / N :=
      hx.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hk) hNr.le)
    rw [relu, max_eq_left (by linarith), mul_zero]
  rw [hzero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k + 1 ≤ j := Finset.mem_range.mp hk
  have : ((k + 1 : ℕ) : ℝ) / N ≤ x :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hk) hNr.le).trans hx.1
  rw [relu, max_eq_right (by linarith)]

/-- GAPS 107.36, one-dimensional `C²` scope: a fixed-grid ReLU network has uniform `N⁻²` error.
The architecture has `N-1` hinges plus an affine term. General Sobolev spaces, dimensions, and
fractional target smoothness require additional approximation theory. -/
theorem abs_reluLinearInterpolant_sub_le (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv f) x| ≤ B)
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : x ∈ Icc 0 1) :
    |reluLinearInterpolant f N x - f x| ≤ B / (8 * (N : ℝ) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set j : ℕ := min ⌊x * N⌋₊ (N - 1) with hj_def
  have hjN : j < N := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN one_pos)
  have hxj : x ∈ Icc ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N) := by
    constructor
    · rw [div_le_iff₀ hNr]
      calc (j : ℝ) ≤ (⌊x * N⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
        _ ≤ x * N := Nat.floor_le (mul_nonneg hx.1 hNr.le)
    · rw [le_div_iff₀ hNr]
      rcases le_total ⌊x * N⌋₊ (N - 1) with h | h
      · rw [hj_def, min_eq_left h]
        push_cast; exact (Nat.lt_floor_add_one (x * N)).le
      · rw [hj_def, min_eq_right h]
        have : ((N - 1 + 1 : ℕ) : ℝ) = N := by
          rw [Nat.sub_add_cancel hN]
        rw [this]
        nlinarith [hx.2]
  rw [reluLinearInterpolant_eq_of_mem f hN hjN hxj]
  have hu : (0 : ℝ) ≤ (j : ℝ) / N := by positivity
  have huv : (j : ℝ) / N < ((j + 1 : ℕ) : ℝ) / N :=
    div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self j) hNr
  have hv : ((j + 1 : ℕ) : ℝ) / N ≤ 1 := by
    rw [div_le_one hNr]; exact_mod_cast hjN
  have h := abs_chord_sub_le f hf hB hbound hu huv hv hxj
  have hlen : ((j + 1 : ℕ) : ℝ) / N - (j : ℝ) / N = 1 / N := by
    push_cast; ring
  have hslope : (f (((j + 1 : ℕ) : ℝ) / N) - f ((j : ℝ) / N)) /
      (((j + 1 : ℕ) : ℝ) / N - (j : ℝ) / N) = uniformGridSlope f N j := by
    rw [hlen, uniformGridSlope]
    field_simp
  rw [hslope, hlen] at h
  calc _ ≤ B * (1 / (N : ℝ)) ^ 2 / 8 := h
    _ = B / (8 * (N : ℝ) ^ 2) := by field_simp

/-- Fourier moment integrands are nonnegative, independently of integrability. -/
theorem barronFourierMoment_nonneg {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    0 ≤ barronFourierMoment f :=
  integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The ReLU interpolant agrees with the target at the left endpoint of the grid. -/
@[simp] theorem reluLinearInterpolant_zero (f : ℝ → ℝ) (N : ℕ) :
    reluLinearInterpolant f N 0 = f 0 := by
  unfold reluLinearInterpolant
  simp only [mul_zero, add_zero]
  have hz : ∑ j ∈ Finset.range (N - 1),
      (uniformGridSlope f N (j + 1) - uniformGridSlope f N j) *
        relu (0 - ((j + 1 : ℕ) : ℝ) / N) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hnonneg : 0 ≤ (((j + 1 : ℕ) : ℝ) / N) := by positivity
    have hrelu : relu (0 - ((j + 1 : ℕ) : ℝ) / N) = 0 := by
      unfold relu
      exact max_eq_left (by linarith)
    rw [hrelu, mul_zero]
  rw [hz, add_zero]

end CKSD
