module

public import CKSD.Bayes.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut


/-!
# Almost-sure convergence of square-integrable martingale-difference series

Orthogonality gives an exact second-moment identity for the partial sums. Summability of
expected squared increments then bounds the partial sums in `L¹`, so Mathlib's almost-everywhere
submartingale convergence theorem applies.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real martingale-difference series converges almost surely when the expected squares of its
increments are summable. -/
theorem ae_exists_tendsto_sum_martingale_difference
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (D : ℕ → Ω → ℝ)
    (hDm : ∀ n, StronglyMeasurable[F (n + 1)] (D n))
    (hD2 : ∀ n, MemLp (D n) 2 μ)
    (hc : ∀ n, μ[D n | F n] =ᵐ[μ] fun _ ↦ 0)
    (hs : Summable fun n ↦ ∫ ω, D n ω ^ 2 ∂μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, D k ω) atTop (𝓝 c) := by
  classical
  let S : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, D k ω
  have hsum (n : ℕ) : S (n + 1) = fun ω ↦ S n ω + D n ω := by
    funext ω
    exact Finset.sum_range_succ _ _
  have hS2 (n : ℕ) : MemLp (S n) 2 μ := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      rw [hsum]
      exact ih.add (hD2 n)
  have hSm (n : ℕ) : StronglyMeasurable[F n] (S n) := by
    have hh : ∀ k ∈ Finset.range n, StronglyMeasurable[F n] (D k) := by
      intro k hk
      exact (hDm k).mono (F.mono (by simpa using Finset.mem_range.1 hk))
    convert Finset.stronglyMeasurable_sum (Finset.range n) hh using 1
    funext ω
    simp [S]
  have hSi (n : ℕ) : Integrable (S n) μ := (hS2 n).integrable one_le_two
  have hMart : Martingale S F μ := by
    apply martingale_nat hSm hSi
    intro n
    rw [hsum]
    have hh := condExp_add (hSi n) ((hD2 n).integrable one_le_two) (F n)
    change (fun ω ↦ S n ω) =ᵐ[μ] μ[S n + D n | F n]
    filter_upwards [hh, hc n] with ω hω hzero
    rw [hω]
    change S n ω = μ[S n | F n] ω + μ[D n | F n] ω
    rw [hzero, add_zero,
      condExp_of_stronglyMeasurable (F.le n) (hSm n) (hSi n)]
  have hintSq (n : ℕ) : Integrable (fun ω ↦ S n ω ^ 2) μ := (hS2 n).integrable_sq
  have horth (n : ℕ) : ∫ ω, S n ω * D n ω ∂μ = 0 := by
    have hint : Integrable (fun ω ↦ S n ω * D n ω) μ := (hS2 n).integrable_mul (hD2 n)
    rw [← integral_condExp (F.le n)]
    have hh := condExp_mul_of_stronglyMeasurable_left (hSm n) hint
      ((hD2 n).integrable one_le_two)
    change (∫ ω, μ[S n * D n | F n] ω ∂μ) = 0
    rw [integral_congr_ae hh]
    change (∫ ω, S n ω * μ[D n | F n] ω ∂μ) = 0
    have hz : (fun ω ↦ S n ω * μ[D n | F n] ω) =ᵐ[μ] fun _ ↦ 0 := by
      filter_upwards [hc n] with ω hω
      rw [hω, mul_zero]
    rw [integral_congr_ae hz, integral_zero]
  have hsecond (n : ℕ) : (∫ ω, S n ω ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, D k ω ^ 2 ∂μ := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      rw [hsum]
      have hpoint : (fun ω ↦ (S n ω + D n ω) ^ 2) =
          fun ω ↦ S n ω ^ 2 + 2 * (S n ω * D n ω) + D n ω ^ 2 := by
        funext ω
        ring
      have hp : Integrable (fun ω ↦ S n ω * D n ω) μ := (hS2 n).integrable_mul (hD2 n)
      rw [hpoint]
      have ha := integral_add ((hintSq n).add (hp.const_mul 2)) ((hD2 n).integrable_sq)
      have hb := integral_add (hintSq n) (hp.const_mul 2)
      simp only [Pi.add_apply] at ha hb
      rw [ha, hb, integral_const_mul, horth, mul_zero, add_zero, ih,
        Finset.sum_range_succ]
  have hbound (n : ℕ) : eLpNorm (S n) 1 μ ≤
      ENNReal.ofReal ((∑' k, ∫ ω, D k ω ^ 2 ∂μ) + 1) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hSi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hSi n)]
    apply ENNReal.ofReal_le_ofReal
    calc (∫ ω, ‖S n ω‖ ∂μ) ≤ ∫ ω, S n ω ^ 2 + 1 ∂μ :=
          integral_mono (hSi n).norm ((hintSq n).add (integrable_const 1)) fun ω ↦ by
            rw [Real.norm_eq_abs]
            have := sq_nonneg (|S n ω| - 1)
            nlinarith [abs_nonneg (S n ω), sq_abs (S n ω)]
      _ = (∫ ω, S n ω ^ 2 ∂μ) + 1 := by
        rw [integral_add (hintSq n) (integrable_const 1)]
        simp
      _ ≤ (∑' k, ∫ ω, D k ω ^ 2 ∂μ) + 1 := by
        rw [hsecond]
        exact add_le_add (hs.sum_le_tsum _ fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) le_rfl
  exact hMart.submartingale.exists_ae_tendsto_of_bdd hbound

end CKSD
