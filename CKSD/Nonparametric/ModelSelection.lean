module

import CKSD.Nonparametric.Basic
import CKSD.Nonparametric.GaussianProjection
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Penalized model selection

The oracle inequality for penalized least-squares selection among countably many linear models
with orthogonal-projection fits, in Gaussian noise, with the empirical squared norm normalized by
`1/n`.

## Main definitions

* `CKSD.projectionModelFit`, `CKSD.penalizedModelCriterion`, `CKSD.selectedProjectionRisk`:
  projection fits, the penalized residual criterion, and the risk of the selected fit.

## Main results

* `CKSD.selectedProjectionRisk_oracle_bound`: the oracle inequality for penalized model
  selection, with `κ₀ = 8` and `C = 23`. The selection criterion gives a pointwise inequality in
  which the cost of the selected model is controlled by `∑_m (4 W_m - 2 n pen m)₊`, where `W_m`
  is the squared norm of the projection of the noise on `S m` plus one orthogonal direction; the
  exponential moment `E exp(W_m / (4σ²)) ≤ √2 ^ (dim S m + 1)` of
  `CKSD.lintegral_exp_norm_starProjection_sq_le` bounds each term by `16 √2 σ² π m`.

Source: GAPS 103.35.

## References

* P. Massart, *Concentration Inequalities and Model Selection*, Lecture Notes in Mathematics 1896,
  Springer, 2007.
* C. Giraud, *Introduction to High-Dimensional Statistics*, 2nd ed., Chapman and Hall/CRC, 2021.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace

namespace CKSD

/-- Orthogonal least-squares fit within a selected linear model. -/
def projectionModelFit {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (S m).starProjection y

/-- Penalized empirical residual criterion for linear model selection. -/
def penalizedModelCriterion {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (pen : M → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (m : M) : ℝ :=
  ‖y - projectionModelFit S m y‖ ^ 2 / n + pen m

/-- Normalized prediction risk of a selected projection fit in Gaussian regression. -/
def selectedProjectionRisk {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (select : EuclideanSpace ℝ (Fin n) → M)
    (f : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖projectionModelFit S (select y) y - f‖ ^ 2 / n)
    ∂(multivariateGaussian f (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))

/-- `-2t ≤ a² / 2 + 2 t² / a²` for real `t` and `a = ‖g‖`, with `t = ⟪g, ε⟫`. -/
private theorem neg_two_mul_inner_le {n : ℕ} (g ε : EuclideanSpace ℝ (Fin n)) :
    -2 * ⟪g, ε⟫ ≤ ‖g‖ ^ 2 / 2 + 2 * (⟪g, ε⟫ ^ 2 / ‖g‖ ^ 2) := by
  by_cases hg : g = 0
  · subst hg; simp
  have ha : 0 < ‖g‖ ^ 2 := by positivity
  have h : 0 ≤ (‖g‖ ^ 2 + 2 * ⟪g, ε⟫) ^ 2 / (2 * ‖g‖ ^ 2) := by positivity
  have he : (‖g‖ ^ 2 + 2 * ⟪g, ε⟫) ^ 2 / (2 * ‖g‖ ^ 2) =
      ‖g‖ ^ 2 / 2 + 2 * ⟪g, ε⟫ + 2 * (⟪g, ε⟫ ^ 2 / ‖g‖ ^ 2) := by
    field_simp; ring
  linarith

/-- The pointwise oracle inequality: with `y = f + ε`, selected model `mh` and any model `m`,
`‖Π_{mh} y - f‖² ≤ 2 (‖f - Π_m f‖² + n pen m) + 4 ⟪f - Π_m f, ε⟫ + z_{mh}(ε)`, where
`z_{m'}(ε) = 4 (‖Π_{m'} ε‖² + ⟪g, ε⟫² / ‖g‖²) - 2 n pen m'` with `g = f - Π_{m'} f`. -/
private theorem norm_projectionModelFit_select_sub_sq_le {M : Type*} {n : ℕ} (hn : 0 < n)
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (pen : M → ℝ) (mh m : M)
    (f ε : EuclideanSpace ℝ (Fin n))
    (hsel : penalizedModelCriterion S pen (f + ε) mh ≤ penalizedModelCriterion S pen (f + ε) m) :
    ‖projectionModelFit S mh (f + ε) - f‖ ^ 2 ≤
      2 * (‖f - (S m).starProjection f‖ ^ 2 + n * pen m) +
        4 * ⟪f - (S m).starProjection f, ε⟫ +
        (4 * (‖(S mh).starProjection ε‖ ^ 2 + ⟪f - (S mh).starProjection f, ε⟫ ^ 2 /
          ‖f - (S mh).starProjection f‖ ^ 2) - 2 * n * pen mh) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold penalizedModelCriterion projectionModelFit at hsel
  unfold projectionModelFit
  rw [div_add' _ _ _ hnR.ne', div_add' _ _ _ hnR.ne', div_le_div_iff_of_pos_right hnR,
    norm_sub_starProjection_add_sq, norm_sub_starProjection_add_sq] at hsel
  rw [norm_starProjection_add_sub_sq]
  have h1 := neg_two_mul_inner_le (f - (S mh).starProjection f) ε
  have h2 := sq_nonneg ‖(S m).starProjection ε‖
  have h3 := sq_nonneg ‖(S mh).starProjection ε‖
  nlinarith

/-- Expected positive part of the excess `z(ε) = 4 (‖Π_K ε‖² + ⟪g, ε⟫² / ‖g‖²) - 2 n p` of one
model with prior weight `q` and penalty `p ≥ κ σ² (dim K + log (1 / q)) / n`, `κ ≥ 8`: at most
`16 √2 σ² q`. -/
private theorem lintegral_ofReal_selectionExcess_le {n : ℕ} (hn : 0 < n)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n)) {σ κ p : ℝ}
    (hσ : 0 < σ) (hκ : 8 ≤ κ) (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hp : κ * σ ^ 2 / n * (Module.finrank ℝ K + Real.log (1 / (q : ℝ))) ≤ p) :
    ∫⁻ ε, ENNReal.ofReal (4 * (‖K.starProjection ε‖ ^ 2 + ⟪f - K.starProjection f, ε⟫ ^ 2 /
        ‖f - K.starProjection f‖ ^ 2) - 2 * n * p)
        ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤
      ENNReal.ofReal (16 * Real.sqrt 2 * σ ^ 2) * q := by
  set g := f - K.starProjection f with hg
  set D := Module.finrank ℝ K with hD
  set c := 2 * n * p with hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ2 : 0 < σ ^ 2 := by positivity
  set W : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun ε ↦ ‖K.starProjection ε‖ ^ 2 + ⟪g, ε⟫ ^ 2 / ‖g‖ ^ 2 with hW
  have hpt : ∀ ε, ENNReal.ofReal (4 * W ε - c) ≤
      ENNReal.ofReal (16 * σ ^ 2 * Real.exp (-c / (16 * σ ^ 2))) *
        ENNReal.ofReal (Real.exp (W ε / (4 * σ ^ 2))) := by
    intro ε
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := Real.add_one_le_exp ((4 * W ε - c) / (16 * σ ^ 2))
    have h2 : (4 * W ε - c) / (16 * σ ^ 2) = -c / (16 * σ ^ 2) + W ε / (4 * σ ^ 2) := by
      field_simp; ring
    rw [h2, Real.exp_add] at h1
    have h3 : 4 * W ε - c = 16 * σ ^ 2 * ((4 * W ε - c) / (16 * σ ^ 2)) := by field_simp
    rw [h3, h2]
    have : 0 < 16 * σ ^ 2 := by positivity
    nlinarith
  have hG := lintegral_exp_norm_starProjection_sq_le K g
    (Submodule.sub_starProjection_mem_orthogonal f) hσ.ne'
  have hWm : Measurable fun ε ↦ ENNReal.ofReal (Real.exp (W ε / (4 * σ ^ 2))) := by
    simp only [hW]; fun_prop
  calc ∫⁻ ε, ENNReal.ofReal (4 * W ε - c)
        ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
      ≤ ∫⁻ ε, ENNReal.ofReal (16 * σ ^ 2 * Real.exp (-c / (16 * σ ^ 2))) *
          ENNReal.ofReal (Real.exp (W ε / (4 * σ ^ 2)))
          ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) := lintegral_mono hpt
    _ = ENNReal.ofReal (16 * σ ^ 2 * Real.exp (-c / (16 * σ ^ 2))) *
          ∫⁻ ε, ENNReal.ofReal (Real.exp (W ε / (4 * σ ^ 2)))
          ∂multivariateGaussian 0 (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
        lintegral_const_mul _ hWm
    _ ≤ ENNReal.ofReal (16 * σ ^ 2 * Real.exp (-c / (16 * σ ^ 2))) *
          ENNReal.ofReal (Real.sqrt 2) ^ (D + 1) := by gcongr
    _ ≤ ENNReal.ofReal (16 * Real.sqrt 2 * σ ^ 2) * q := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set x := Real.log (1 / (q : ℝ)) with hx
        have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
        have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
        have hx0 : 0 ≤ x := Real.log_nonneg (by rw [le_div_iff₀ hq0']; linarith)
        have hDx : 16 * σ ^ 2 * (D + x) ≤ c := by
          have h1 : κ * σ ^ 2 * (D + x) ≤ n * p := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hnR] at hp; linarith
          have h2 : 8 * σ ^ 2 * (D + x) ≤ κ * σ ^ 2 * (D + x) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
          rw [hc]; linarith
        have hexp : Real.exp (-c / (16 * σ ^ 2)) ≤ Real.exp (-(D : ℝ)) * q := by
          rw [show (q : ℝ) = Real.exp (-x) by
            rw [hx, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv], ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        have hsq : Real.sqrt 2 ^ D ≤ Real.exp D := by
          rw [← Real.exp_one_pow]
          refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ D
          have := Real.add_one_le_exp (1 : ℝ)
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [Real.add_one_le_exp (1 : ℝ)]
        have hED : Real.exp (-(D : ℝ)) * Real.sqrt 2 ^ D ≤ 1 := by
          rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]; exact hsq
        rw [pow_succ]
        calc 16 * σ ^ 2 * Real.exp (-c / (16 * σ ^ 2)) * (Real.sqrt 2 ^ D * Real.sqrt 2)
            ≤ 16 * σ ^ 2 * (Real.exp (-(D : ℝ)) * q) * (Real.sqrt 2 ^ D * Real.sqrt 2) := by
              gcongr
          _ = 16 * Real.sqrt 2 * σ ^ 2 * q * (Real.exp (-(D : ℝ)) * Real.sqrt 2 ^ D) := by ring
          _ ≤ 16 * Real.sqrt 2 * σ ^ 2 * q * 1 := by gcongr
          _ = 16 * Real.sqrt 2 * σ ^ 2 * q := mul_one _

/-- GAPS 103.35: the countable-model oracle inequality for penalized least squares. For a
countable family of linear models `S m ⊆ ℝⁿ` with prior weights `π m > 0`, `∑ π m ≤ 1`,
Gaussian noise of variance `σ²`, and a penalty
`pen m ≥ κ σ² (dim S m + log (1 / π m)) / n` with `κ > κ₀`, the measurable minimizer `m̂` of the
penalized residual criterion satisfies
`E[n⁻¹ ‖Π_{m̂} y - f‖²] ≤ C (inf_m (n⁻¹ ‖f - Π_m f‖² + pen m) + σ² / n)`. -/
theorem selectedProjectionRisk_oracle_bound :
    ∃ κ₀ > (0 : ℝ), ∀ κ > κ₀, ∃ C > (0 : ℝ),
      ∀ n : ℕ, 0 < n → ∀ (M : Type*) [Countable M] [Nonempty M]
      [MeasurableSpace M] [MeasurableSingletonClass M],
      ∀ S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ π : M → ℝ≥0, (∀ m, 0 < π m) → (∑' m, (π m : ℝ≥0∞)) ≤ 1 →
      ∀ σ : ℝ, 0 < σ → ∀ pen : M → ℝ,
      (∀ m, κ * σ ^ 2 / n *
        (Module.finrank ℝ (S m) + Real.log (1 / (π m : ℝ))) ≤ pen m) →
      ∀ select : EuclideanSpace ℝ (Fin n) → M, Measurable select →
      (∀ y m, penalizedModelCriterion S pen y (select y) ≤ penalizedModelCriterion S pen y m) →
      ∀ f : EuclideanSpace ℝ (Fin n),
      selectedProjectionRisk S select f σ ≤ ENNReal.ofReal
        (C * ((⨅ m, ‖f - projectionModelFit S m f‖ ^ 2 / n + pen m) + σ ^ 2 / n)) := by
  refine ⟨8, by norm_num, fun κ hκ ↦ ⟨23, by norm_num, ?_⟩⟩
  intro n hn M _ _ _ _ S π hπ hπsum σ hσ pen hpen select _ hsel f
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set μ₀ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
    (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) with hμ₀
  set z : M → EuclideanSpace ℝ (Fin n) → ℝ := fun m' ε ↦
    4 * (‖(S m').starProjection ε‖ ^ 2 + ⟪f - (S m').starProjection f, ε⟫ ^ 2 /
      ‖f - (S m').starProjection f‖ ^ 2) - 2 * n * pen m' with hz
  have hzc : ∀ m', Continuous (z m') := fun m' ↦ by simp only [hz]; fun_prop
  have hπ1 : ∀ m, π m ≤ 1 := fun m ↦ by
    have := (le_tsum (fun m ↦ (π m : ℝ≥0∞)) m).trans hπsum
    exact_mod_cast this
  have hzint : ∀ m', ∫⁻ ε, ENNReal.ofReal (z m' ε) ∂μ₀ ≤
      ENNReal.ofReal (16 * Real.sqrt 2 * σ ^ 2) * π m' := fun m' ↦
    lintegral_ofReal_selectionExcess_le hn (S m') f hσ hκ.le (π m') (hπ m') (hπ1 m') (hpen m')
  set Z : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun ε ↦ ∑' m', ENNReal.ofReal (z m' ε) with hZ
  have hZm : Measurable Z :=
    Measurable.tsum fun m' ↦ ENNReal.measurable_ofReal.comp (hzc m').measurable
  have hZint : ∫⁻ ε, Z ε ∂μ₀ ≤ ENNReal.ofReal (16 * Real.sqrt 2 * σ ^ 2) :=
    lintegral_tsum_le_of_le_mul (fun m' ↦
      (ENNReal.measurable_ofReal.comp (hzc m').measurable).aemeasurable) hπsum hzint
  have hZfin : ∫⁻ ε, Z ε ∂μ₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZint
  have hZae : ∀ᵐ ε ∂μ₀, Z ε < ∞ := ae_lt_top hZm hZfin
  -- change of variables `y = f + ε`
  have hlaw : multivariateGaussian f (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      μ₀.map (Homeomorph.addLeft f).toMeasurableEquiv := by
    have := TauCeti.Probability.map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.PosSemidef.one.smul (sq_nonneg σ)) (1 : Matrix (Fin n) (Fin n) ℝ) f
    simp only [map_zero, zero_add, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
    rw [← this]
    congr 1
    funext x
    simp [add_comm]
  have hrisk : selectedProjectionRisk S select f σ = ∫⁻ ε,
      ENNReal.ofReal (‖projectionModelFit S (select (f + ε)) (f + ε) - f‖ ^ 2 / n) ∂μ₀ := by
    rw [selectedProjectionRisk, hlaw, lintegral_map_equiv]
    rfl
  -- the bound for each comparison model
  have hB : ∀ m, 0 ≤ ‖f - projectionModelFit S m f‖ ^ 2 / n + pen m := by
    intro m
    have hlog : 0 ≤ Real.log (1 / (π m : ℝ)) := Real.log_nonneg (by
      rw [le_div_iff₀ (by exact_mod_cast hπ m)]; simpa using (show (π m : ℝ) ≤ 1 by
        exact_mod_cast hπ1 m))
    have := hpen m
    have : 0 ≤ κ * σ ^ 2 / n * (Module.finrank ℝ (S m) + Real.log (1 / (π m : ℝ))) := by
      have : 0 < κ := by linarith
      positivity
    have := div_nonneg (sq_nonneg ‖f - projectionModelFit S m f‖) hnR.le
    linarith
  have hsqrt : Real.sqrt 2 ≤ 23 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hm : ∀ m, selectedProjectionRisk S select f σ ≤ ENNReal.ofReal
      (23 * ((‖f - projectionModelFit S m f‖ ^ 2 / n + pen m) + σ ^ 2 / n)) := by
    intro m
    set g := f - (S m).starProjection f with hg
    set A := ‖g‖ ^ 2 + n * pen m with hA
    set H : EuclideanSpace ℝ (Fin n) → ℝ := fun ε ↦ 2 * A + 4 * ⟪g, ε⟫ + (Z ε).toReal with hH
    have hpt : ∀ᵐ ε ∂μ₀, ‖projectionModelFit S (select (f + ε)) (f + ε) - f‖ ^ 2 ≤ H ε := by
      filter_upwards [hZae] with ε hε
      have h1 := norm_projectionModelFit_select_sub_sq_le hn S pen (select (f + ε)) m f ε
        (hsel (f + ε) m)
      have h2 : z (select (f + ε)) ε ≤ (Z ε).toReal := by
        refine (le_max_left _ 0).trans ?_
        rw [← ENNReal.toReal_ofReal']
        exact ENNReal.toReal_mono hε.ne (le_tsum (fun m' ↦ ENNReal.ofReal (z m' ε)) _)
      simp only [hH, hA, hg]
      simp only [hz] at h2
      linarith
    have hTint : Integrable (fun ε ↦ (Z ε).toReal) μ₀ :=
      integrable_toReal_of_lintegral_ne_top hZm.aemeasurable hZfin
    have hXint : Integrable (fun ε ↦ ⟪g, ε⟫) μ₀ := IsGaussian.integrable_id.const_inner g
    have hHint : Integrable H μ₀ := ((integrable_const _).add (hXint.const_mul 4)).add hTint
    have hX0 : ∫ ε, ⟪g, ε⟫ ∂μ₀ = 0 := by
      have := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id (μ := μ₀)) g
      simp only [id] at this
      rw [this, hμ₀, integral_id_multivariateGaussian, inner_zero_right]
    have hT : ∫ ε, (Z ε).toReal ∂μ₀ ≤ 16 * Real.sqrt 2 * σ ^ 2 := by
      rw [integral_toReal hZm.aemeasurable hZae]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hZint
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hH0 : 0 ≤ᵐ[μ₀] fun ε ↦ H ε / n :=
      hpt.mono fun ε hε ↦ div_nonneg ((sq_nonneg _).trans hε) hnR.le
    rw [hrisk]
    calc ∫⁻ ε, ENNReal.ofReal (‖projectionModelFit S (select (f + ε)) (f + ε) - f‖ ^ 2 / n) ∂μ₀
        ≤ ∫⁻ ε, ENNReal.ofReal (H ε / n) ∂μ₀ :=
          lintegral_mono_ae (hpt.mono fun ε hε ↦ ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right hε hnR.le))
      _ = ENNReal.ofReal (∫ ε, H ε / n ∂μ₀) :=
          (ofReal_integral_eq_lintegral_ofReal (hHint.div_const _) hH0).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hIH : ∫ ε, H ε ∂μ₀ = 2 * A + 4 * ∫ ε, ⟪g, ε⟫ ∂μ₀ + ∫ ε, (Z ε).toReal ∂μ₀ := by
            have h1 : Integrable (fun ε ↦ 2 * A + 4 * ⟪g, ε⟫) μ₀ :=
              (integrable_const _).add (hXint.const_mul 4)
            have h2 : Integrable (fun ε ↦ 4 * ⟪g, ε⟫) μ₀ := hXint.const_mul 4
            simp only [hH]
            rw [integral_add h1 hTint, integral_add (integrable_const _) h2,
              integral_const_mul (4 : ℝ) (fun ε ↦ ⟪g, ε⟫), integral_const]
            simp
          rw [integral_div, hIH, hX0, mul_zero, add_zero, div_le_iff₀ hnR]
          have hfit : projectionModelFit S m f = (S m).starProjection f := rfl
          rw [hfit, ← hg]
          have hb := hB m
          rw [hfit, ← hg] at hb
          have : ‖g‖ ^ 2 / n * n = ‖g‖ ^ 2 := by field_simp
          have : σ ^ 2 / n * n = σ ^ 2 := by field_simp
          nlinarith [mul_nonneg hb hnR.le, sq_nonneg σ]
  -- optimize over the comparison model
  exact le_ofReal_mul_iInf_add (by norm_num) (by positivity) _ hB hm

/-- The fitted value equals the response exactly when the response lies in the selected
model. -/
theorem projectionModelFit_eq_self_iff {M : Type*} {n : ℕ}
    (S : M → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (m : M)
    (y : EuclideanSpace ℝ (Fin n)) : projectionModelFit S m y = y ↔ y ∈ S m :=
  Submodule.starProjection_eq_self_iff

end CKSD
