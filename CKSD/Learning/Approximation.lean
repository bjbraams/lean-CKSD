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

/-- GAPS 107.36, one-dimensional `C²` scope: a fixed-grid ReLU network has uniform `N⁻²` error.
The architecture has `N-1` hinges plus an affine term. General Sobolev spaces, dimensions, and
fractional target smoothness require additional approximation theory. -/
theorem abs_reluLinearInterpolant_sub_le (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv f) x| ≤ B)
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : x ∈ Icc 0 1) :
    |reluLinearInterpolant f N x - f x| ≤ B / (8 * (N : ℝ) ^ 2) := by
  sorry

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
