module
public import TauCeti.MeasureTheory.Integral.PrekopaLeindler
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Gaussian.Symmetry
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Group.Convolution
/-!
# Anderson's inequality and Gaussian bowl-loss domination

A centrally symmetric convex set has maximal centered Gaussian mass among its translates.
The proof uses pinned TauCeti's central-slice Prékopa–Leindler theorem: a Gaussian has the
Prékopa–Leindler property because its density is log-concave, and the property is preserved by
its covariance square-root map. Degenerate covariances and dimension zero are included.

Mathlib's extended-valued layer-cake formula then shows that a measurable symmetric
bowl-shaped loss has minimal Gaussian risk at zero shift. Averaging over an independent
residual law gives the corresponding convolution-risk domination. The losses may be
unbounded or infinite. This is the Gaussian decision-theoretic component of GAPS 102.17;
it does not establish the transfer from arbitrary finite-experiment estimators to the
Gaussian limit experiment.

Pinned TauCeti supplies Prékopa–Leindler, Gaussian densities and Gaussian symmetry;
Mathlib supplies covariance-square-root Gaussian laws, layer cake and measure convolution.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology MatrixOrder
namespace CKSD
/-- For a symmetric measure with the Prékopa–Leindler property, a symmetric convex set has
maximum mass when centered at zero. -/
theorem measure_add_preimage_le_of_convex_symmetric
    {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    [MeasurableAdd₂ E] [MeasurableNeg E] (μ : Measure E) [μ.IsNegInvariant]
    (hPL : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → μ.HasPrekopaLeindler θ)
    {C : Set E} (hCm : MeasurableSet C) (hCc : Convex ℝ C)
    (hCs : ∀ x ∈ C, -x ∈ C) (a : E) :
    μ ((fun x ↦ a + x) ⁻¹' C) ≤ μ C := by
  let S : Set (E × E) := (fun p ↦ p.1 + p.2) ⁻¹' C
  have hSm : MeasurableSet S := (measurable_fst.add measurable_snd) hCm
  have hSc : Convex ℝ S := hCc.linear_preimage (LinearMap.fst ℝ E E + LinearMap.snd ℝ E E)
  have hSs : ∀ p ∈ S, -p ∈ S := by
    intro p hp
    change -p.1 + -p.2 ∈ C
    rw [← neg_add]
    exact hCs _ hp
  have hh := hSc.measure_preimage_prodMk_le_measure_preimage_prodMk_zero hPL hSm hSs a
  have haS : Prod.mk a ⁻¹' S = (fun x ↦ a+x) ⁻¹' C := rfl
  have h0S : Prod.mk 0 ⁻¹' S = C := by
    ext x
    change 0+x ∈ C ↔ x ∈ C
    rw [zero_add]
  rwa [haS,h0S] at hh

/-- Standard Gaussian measures satisfy Prékopa–Leindler, including in dimension zero. -/
theorem hasPrekopaLeindler_stdGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (stdGaussian E).HasPrekopaLeindler θ := by
  rw [TauCeti.Probability.stdGaussian_eq_withDensity_norm]
  apply (TauCeti.hasPrekopaLeindler_volume E hθ₀ hθ₁).withDensity hθ₀ hθ₁ (by fun_prop)
  have hc := TauCeti.logConcave_const (E := E)
    (ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)))
  have hg := TauCeti.logConcave_ofReal_exp_neg_mul_sq_norm (G := E) (c := (1 / 2 : ℝ)) (by norm_num)
  convert hc.mul hg using 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  congr 2
  congr 1
  ring
/-- A centered multivariate Gaussian inherits Prékopa–Leindler from the standard Gaussian
through its covariance square-root map. Degenerate covariance is allowed. -/
theorem hasPrekopaLeindler_multivariateGaussian_zero {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).HasPrekopaLeindler θ := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hm : MeasurePreserving A (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (multivariateGaussian 0 S) := by
    refine ⟨A.continuous.measurable,?_⟩
    simp only [multivariateGaussian,zero_add,A]
  exact (hasPrekopaLeindler_stdGaussian hθ₀ hθ₁).map A hm (fun x y ↦ by simp)

/-- Anderson's inequality: translating a symmetric convex set cannot increase its mass under
a centered multivariate Gaussian. -/
theorem multivariateGaussian_add_preimage_le {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) {C : Set (EuclideanSpace ℝ (Fin d))}
    (hCm : MeasurableSet C) (hCc : Convex ℝ C) (hCs : ∀ x ∈ C, -x ∈ C)
    (a : EuclideanSpace ℝ (Fin d)) :
    multivariateGaussian 0 S ((fun x ↦ a+x) ⁻¹' C) ≤ multivariateGaussian 0 S C := by
  have : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).IsNegInvariant :=
    ⟨IsGaussian.map_neg_eq_self _ (by simp only [integral_id_multivariateGaussian])⟩
  exact measure_add_preimage_le_of_convex_symmetric _
    (fun {_} hθ₀ hθ₁ ↦ hasPrekopaLeindler_multivariateGaussian_zero S hθ₀ hθ₁) hCm hCc hCs a
/-- A measurable symmetric bowl-shaped loss has minimal Gaussian risk at zero shift. The
loss may be unbounded or take the value infinity. -/
theorem lintegral_multivariateGaussian_loss_le_shift {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (loss : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hm : Measurable loss) (hsym : ∀ x, loss (-x) = loss x)
    (hconv : ∀ c, Convex ℝ {x | loss x ≤ c}) (a : EuclideanSpace ℝ (Fin d)) :
    (∫⁻ x, loss x ∂multivariateGaussian 0 S) ≤
      ∫⁻ x, loss (a+x) ∂multivariateGaussian 0 S := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  have hma : Measurable (fun x ↦ loss (a+x)) := hm.comp (measurable_const.add measurable_id)
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hm.aemeasurable,
    lintegral_eq_lintegral_measure_ofReal_le μ hma.aemeasurable]
  apply lintegral_mono
  intro t
  let C : Set (EuclideanSpace ℝ (Fin d)) := {x | loss x < ENNReal.ofReal t}
  have hCm : MeasurableSet C := measurableSet_lt hm measurable_const
  have hCc : Convex ℝ C := by
    intro x hx y hy b c hb hc hbc
    change loss x < ENNReal.ofReal t at hx
    change loss y < ENNReal.ofReal t at hy
    have hh := hconv (max (loss x) (loss y)) (x := x) (y := y)
      (le_max_left (loss x) (loss y)) (le_max_right (loss x) (loss y)) hb hc hbc
    exact lt_of_le_of_lt hh (max_lt_iff.mpr ⟨hx,hy⟩)
  have hCs : ∀ x ∈ C, -x ∈ C := by intro x hx; change loss (-x) < _; rwa [hsym]
  have hmass := multivariateGaussian_add_preimage_le S hCm hCc hCs a
  have hpre : MeasurableSet ((fun x ↦ a+x) ⁻¹' C) := (measurable_const.add measurable_id) hCm
  have hh : μ Cᶜ ≤ μ ((fun x ↦ a+x) ⁻¹' C)ᶜ := by
    rw [measure_compl hCm (measure_ne_top _ _),measure_compl hpre (measure_ne_top _ _)]
    exact tsub_le_tsub_left hmass _
  simpa only [C,compl_ofPred,not_lt,preimage_ofPred_eq] using hh

/-- Adding independent residual noise cannot reduce the Gaussian risk of a symmetric
bowl-shaped loss. -/
theorem lintegral_multivariateGaussian_loss_le_convolution {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (loss : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hm : Measurable loss) (hsym : ∀ x, loss (-x) = loss x)
    (hconv : ∀ c, Convex ℝ {x | loss x ≤ c})
    (M : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure M] :
    (∫⁻ x, loss x ∂multivariateGaussian 0 S) ≤
      ∫⁻ x, loss x ∂(multivariateGaussian 0 S).conv M := by
  rw [Measure.conv_comm,Measure.lintegral_conv hm]
  calc
    _ = ∫⁻ _a, (∫⁻ x, loss x ∂multivariateGaussian 0 S) ∂M := by simp
    _ ≤ _ := lintegral_mono (fun a ↦ lintegral_multivariateGaussian_loss_le_shift S loss hm hsym hconv a)
end CKSD
