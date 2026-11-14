module

public import CKSD.LinearModels.Basic
public import CKSD.Asymptotics.Basic
public import Mathlib.Probability.CramerWold
public import TauCeti.Probability.Distributions.Gaussian.Transforms
import CKSD.Asymptotics.ConvexRegression.Basic
public import CKSD.LinearModels.RegressionLimits
import TauCeti.Analysis.Matrix.MeasurableSpace


/-!
# Two-stage least squares in the instrumental-variable model

Observations `(x, z, ε)` with outcome `y = ⟪x, β⟫ + ε`, and the limit theory of the two-stage
least-squares estimator `CKSD.twoStageLeastSquares`.

## Main definitions

* `CKSD.InstrumentalVariableObservation`, `CKSD.instrumentalVariableSampleEstimator`,
  `CKSD.instrumentalVariableCovariance`: observations `(x, z, ε)`, the resulting estimator, and
  the sandwich covariance `H⁻¹ Dᵀ Σ_Z⁻¹ Ω Σ_Z⁻¹ D H⁻¹` with `Σ_Z = E[z zᵀ]`, `D = E[z xᵀ]`,
  `H = Dᵀ Σ_Z⁻¹ D` and `Ω = E[ε² z zᵀ]`.

## Main results

* `CKSD.tendsto_in_measure_two_stage_least_squares`,
  `CKSD.tendsto_in_distribution_two_stage_least_squares`: consistency and asymptotic normality of
  two-stage least squares.

The limits use Mathlib's strong law, central limit theorem and Cramér–Wold theorem
(`TendstoInDistribution.of_inner`), and TauCeti's `map_inner_multivariateGaussian`.

## References

* J. M. Wooldridge, *Econometric Analysis of Cross Section and Panel Data*, 2nd ed., MIT Press,
  2010, §5.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

/-- Structural observation in an instrumental-variable model: regressor, instrument, error. -/
abbrev InstrumentalVariableObservation (p k : ℕ) :=
  EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin k) × ℝ

/-- Second moment of the instruments. -/
def instrumentSecondMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin k) ℝ := fun i j ↦ ∫ z, z.2.1 i * z.2.1 j ∂Q

/-- Cross second moment between instruments and regressors. -/
def instrumentRegressorMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin p) ℝ := fun i j ↦ ∫ z, z.2.1 i * z.1 j ∂Q

/-- Instrument-score covariance in the correctly specified structural model. -/
def instrumentErrorMoment {p k : ℕ} (Q : Measure (InstrumentalVariableObservation p k)) :
    Matrix (Fin k) (Fin k) ℝ := fun i j ↦ ∫ z, z.2.2 ^ 2 * z.2.1 i * z.2.1 j ∂Q

/-- Two-stage least-squares sample estimator under the structural equation. -/
def instrumentalVariableSampleEstimator {p k n : ℕ} (beta : EuclideanSpace ℝ (Fin p))
    (sample : Fin n → InstrumentalVariableObservation p k) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (twoStageLeastSquares
    (fun i j ↦ (sample i).1 j) (fun i j ↦ (sample i).2.1 j)
    (fun i ↦ inner ℝ (sample i).1 beta + (sample i).2.2))

/-- Asymptotic two-stage least-squares covariance from the population instrument moments. -/
def instrumentalVariableCovariance {p k : ℕ}
    (Q : Measure (InstrumentalVariableObservation p k)) : Matrix (Fin p) (Fin p) ℝ :=
  let Z := instrumentSecondMoment Q
  let D := instrumentRegressorMoment Q
  let H := D.transpose * Z⁻¹ * D
  H⁻¹ * D.transpose * Z⁻¹ * instrumentErrorMoment Q * Z⁻¹ * D * H⁻¹

open Matrix in
/-- Coordinatewise convergence in probability to a constant in a finite product. -/
private theorem tendsto_in_measure_pi_const {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {X : ℕ → Ω → ι → ℝ} {c : ι → ℝ}
    (h : ∀ i, TendstoInMeasure μ (fun n ω ↦ X n ω i) atTop (fun _ ↦ c i)) :
    TendstoInMeasure μ X atTop (fun _ ↦ c) := by
  have h' := fun i ↦ tendstoInMeasure_iff_dist.1 (h i)
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Tendsto (fun n ↦ ∑ i, μ {ω | ε ≤ dist (X n ω i) (c i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset ι) fun i _ ↦ h' i ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ bot_le) fun n ↦ ?_
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_iUnion_fintype_le μ _)
  simp only [mem_ofPred_eq, mem_iUnion] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact (not_le.2 ((dist_pi_lt_iff hε).2 hcon)) hω

open Matrix in
/-- Continuous mapping for convergence in probability to a constant, in metric spaces. -/
private theorem tendsto_in_measure_comp_const {Ω E F : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {μ : Measure Ω} {X : ℕ → Ω → E} {c : E} (g : E → F) (hg : ContinuousAt g c)
    (h : TendstoInMeasure μ X atTop (fun _ ↦ c)) :
    TendstoInMeasure μ (fun n ω ↦ g (X n ω)) atTop (fun _ ↦ g c) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  exact (not_le.2 (hδg (not_le.1 hcon))) hω

open Matrix in
/-- Two-stage least squares in terms of rescaled moment matrices. -/
private theorem two_stage_least_squares_eq_smul {n p k : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (Z : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    twoStageLeastSquares X Z y =
      ((c • (Zᵀ * X))ᵀ * (c • (Zᵀ * Z))⁻¹ * (c • (Zᵀ * X)))⁻¹ *ᵥ
        (((c • (Zᵀ * X))ᵀ * (c • (Zᵀ * Z))⁻¹) *ᵥ (c • (Zᵀ *ᵥ y))) := by
  rw [matrix_inv_smul_of_ne_zero hc]
  have h1 : (c • (Zᵀ * X))ᵀ * (c⁻¹ • (Zᵀ * Z)⁻¹) * (c • (Zᵀ * X)) =
      c • (Xᵀ * (Z * (Zᵀ * Z)⁻¹ * Zᵀ) * X) := by
    simp only [transpose_smul, transpose_mul, transpose_transpose, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [show c * (c⁻¹ * c) = c by field_simp]
  have h2 : ((c • (Zᵀ * X))ᵀ * (c⁻¹ • (Zᵀ * Z)⁻¹)) *ᵥ (c • (Zᵀ *ᵥ y)) =
      c • ((Xᵀ * (Z * (Zᵀ * Z)⁻¹ * Zᵀ)) *ᵥ y) := by
    simp only [transpose_smul, transpose_mul, transpose_transpose, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.smul_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [inv_mul_cancel₀ hc, mul_one]
  rw [h1, h2, matrix_inv_smul_of_ne_zero hc, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]
  rfl

open Matrix in
/-- Products of continuous-at matrix functions are continuous at the point. -/
private theorem continuous_at_matrix_mul {X : Type*} [TopologicalSpace X] {m n l : Type*}
    [Fintype n] {A : X → Matrix m n ℝ} {B : X → Matrix n l ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) : ContinuousAt (fun y ↦ A y * B y) x :=
  ContinuousAt.comp₂ (f := fun q : Matrix m n ℝ × Matrix n l ℝ ↦ q.1 * q.2)
    (continuous_fst.matrix_mul continuous_snd).continuousAt hA hB

open Matrix in
/-- Matrix-vector products of continuous-at functions are continuous at the point. -/
private theorem continuous_at_matrix_mul_vec {X : Type*} [TopologicalSpace X] {m n : Type*}
    [Fintype n] {A : X → Matrix m n ℝ} {b : X → n → ℝ} {x : X}
    (hA : ContinuousAt A x) (hb : ContinuousAt b x) : ContinuousAt (fun y ↦ A y *ᵥ b y) x :=
  ContinuousAt.comp₂ (f := fun q : Matrix m n ℝ × (n → ℝ) ↦ q.1 *ᵥ q.2)
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt hA hb

open Matrix in
/-- Matrix inversion composed with a continuous-at function, at a point of nonzero
determinant. -/
private theorem continuous_at_matrix_inv_comp {X : Type*} [TopologicalSpace X] {n : Type*}
    [Fintype n] [DecidableEq n] {A : X → Matrix n n ℝ} {x : X}
    (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) : ContinuousAt (fun y ↦ (A y)⁻¹) x := by
  refine (continuousAt_matrix_inv (A x) ?_).comp hA
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

open Matrix in
/-- The index set of the instrument moments `z zᵀ`, `z xᵀ` and `z y`. -/
private abbrev InstrumentMomentIndex (p k : ℕ) := (Fin k × Fin k) ⊕ (Fin k × Fin p) ⊕ Fin k

open Matrix in
/-- The instrument moment statistics `zᵢ zⱼ`, `zᵢ xⱼ` and `zᵢ (⟪x, β⟫ + ε)`. -/
private def instrumentMomentStatistic {p k : ℕ} (beta : EuclideanSpace ℝ (Fin p)) :
    InstrumentMomentIndex p k → InstrumentalVariableObservation p k → ℝ
  | .inl q, z => z.2.1 q.1 * z.2.1 q.2
  | .inr (.inl q), z => z.2.1 q.1 * z.1 q.2
  | .inr (.inr i), z => z.2.1 i * (inner ℝ z.1 beta + z.2.2)

/-- The instrument second-moment block `A` of a moment vector. -/
private def instrumentMomentA {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j ↦ v (.inl (i, j))

/-- The instrument-regressor block `B` of a moment vector. -/
private def instrumentMomentB {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) :
    Matrix (Fin k) (Fin p) ℝ :=
  Matrix.of fun i j ↦ v (.inr (.inl (i, j)))

/-- The instrument-response block `b` of a moment vector. -/
private def instrumentMomentCross {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) : Fin k → ℝ :=
  fun i ↦ v (.inr (.inr i))

open Matrix in
/-- The normal matrix `Bᵀ A⁻¹ B` of a moment vector. -/
private def instrumentMomentNormal {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (instrumentMomentB v)ᵀ * (instrumentMomentA v)⁻¹ * instrumentMomentB v

open Matrix in
/-- The gain `(Bᵀ A⁻¹ B)⁻¹ Bᵀ A⁻¹` of a moment vector. -/
private def instrumentMomentGain {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) :
    Matrix (Fin p) (Fin k) ℝ :=
  (instrumentMomentNormal v)⁻¹ * ((instrumentMomentB v)ᵀ * (instrumentMomentA v)⁻¹)

open Matrix in
/-- The two-stage least-squares map from instrument moments to the coefficient. -/
private def instrumentMomentEstimator {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (instrumentMomentGain v *ᵥ instrumentMomentCross v)

open Matrix in
/-- The gain is a left inverse of `B` when the normal matrix is invertible. -/
private theorem instrument_moment_gain_mul_b {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ)
    (h : IsUnit (instrumentMomentNormal v).det) :
    instrumentMomentGain v * instrumentMomentB v = 1 := by
  rw [instrumentMomentGain, Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ h

open Matrix in
/-- For `n ≥ 1` observations, the two-stage least-squares estimator is the moment map applied
to the sample instrument moments. -/
private theorem instrumental_variable_sample_estimator_eq {p k : ℕ}
    (beta : EuclideanSpace ℝ (Fin p)) (X : ℕ → InstrumentalVariableObservation p k) (n : ℕ)
    (hn : n ≠ 0) :
    instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val) =
      instrumentMomentEstimator (fun q ↦ (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i)) := by
  set c : ℝ := (n : ℝ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn)
  let Xm : Matrix (Fin n) (Fin p) ℝ := fun i j ↦ (X i.val).1 j
  let Zm : Matrix (Fin n) (Fin k) ℝ := fun i j ↦ (X i.val).2.1 j
  let y : Fin n → ℝ := fun i ↦ inner ℝ (X i.val).1 beta + (X i.val).2.2
  set v : InstrumentMomentIndex p k → ℝ :=
    fun q ↦ c * ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i)
  have hA : instrumentMomentA v = c • (Zmᵀ * Zm) := by
    ext i j
    rw [instrumentMomentA, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    exact congrArg (c * ·) (Fin.sum_univ_eq_sum_range (fun l ↦ (X l).2.1 i * (X l).2.1 j) n).symm
  have hB : instrumentMomentB v = c • (Zmᵀ * Xm) := by
    ext i j
    rw [instrumentMomentB, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    exact congrArg (c * ·) (Fin.sum_univ_eq_sum_range (fun l ↦ (X l).2.1 i * (X l).1 j) n).symm
  have hb : instrumentMomentCross v = c • (Zmᵀ *ᵥ y) := by
    ext i
    rw [instrumentMomentCross, Pi.smul_apply, mulVec, dotProduct, smul_eq_mul]
    exact congrArg (c * ·) (Fin.sum_univ_eq_sum_range
      (fun l ↦ (X l).2.1 i * (inner ℝ (X l).1 beta + (X l).2.2)) n).symm
  rw [instrumentMomentEstimator, instrumentMomentGain, instrumentMomentNormal, hA, hB, hb,
    ← Matrix.mulVec_mulVec]
  exact congrArg (WithLp.toLp 2) (two_stage_least_squares_eq_smul Xm Zm y c hc)

open Matrix in
/-- The gain and the determinant of the normal matrix are continuous at every moment vector
with invertible `A` and invertible normal matrix. -/
private theorem continuous_at_instrument_moment_gain {p k : ℕ} (v : InstrumentMomentIndex p k → ℝ)
    (hA : (instrumentMomentA v).det ≠ 0) (hN : (instrumentMomentNormal v).det ≠ 0) :
    ContinuousAt instrumentMomentGain v ∧
      ContinuousAt (fun w ↦ (instrumentMomentNormal w).det) v := by
  have hAc : Continuous (instrumentMomentA (p := p) (k := k)) :=
    continuous_matrix fun i j ↦ continuous_apply _
  have hBc : Continuous (instrumentMomentB (p := p) (k := k)) :=
    continuous_matrix fun i j ↦ continuous_apply _
  have hAi := continuous_at_matrix_inv_comp hAc.continuousAt hA
  have hK := continuous_at_matrix_mul hBc.matrix_transpose.continuousAt hAi
  have hNc : ContinuousAt (instrumentMomentNormal (p := p) (k := k)) v :=
    continuous_at_matrix_mul hK hBc.continuousAt
  exact ⟨continuous_at_matrix_mul (continuous_at_matrix_inv_comp hNc hN) hK,
    (continuous_id.matrix_det).continuousAt.comp hNc⟩

/-- Coordinates of an observation are square integrable when the observation is. -/
private theorem mem_lp_instrumental_variable_coordinates {p k : ℕ}
    {Q : Measure (InstrumentalVariableObservation p k)} (h2 : MemLp id 2 Q) :
    (∀ i : Fin k, MemLp (fun z : InstrumentalVariableObservation p k ↦ z.2.1 i) 2 Q) ∧
      (∀ j : Fin p, MemLp (fun z : InstrumentalVariableObservation p k ↦ z.1 j) 2 Q) ∧
        MemLp (fun z : InstrumentalVariableObservation p k ↦ z.2.2) 2 Q :=
  ⟨fun i ↦ h2.of_le (by fun_prop) (ae_of_all _ fun z ↦
      (PiLp.norm_apply_le z.2.1 i).trans ((norm_fst_le z.2).trans (norm_snd_le z))),
    fun j ↦ h2.of_le (by fun_prop) (ae_of_all _ fun z ↦
      (PiLp.norm_apply_le z.1 j).trans (norm_fst_le z)),
    h2.of_le (by fun_prop) (ae_of_all _ fun z ↦ (norm_snd_le z.2).trans (norm_snd_le z))⟩

/-- The instrument-response statistic splits into regressor and error parts. -/
private theorem instrument_moment_statistic_inr_inr {p k : ℕ} (beta : EuclideanSpace ℝ (Fin p))
    (i : Fin k) (z : InstrumentalVariableObservation p k) :
    instrumentMomentStatistic beta (.inr (.inr i)) z =
      ∑ j, z.2.1 i * z.1 j * beta j + z.2.1 i * z.2.2 := by
  simp only [instrumentMomentStatistic, PiLp.inner_apply, mul_add, Finset.mul_sum,
    RCLike.inner_apply, conj_trivial]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

open Matrix in
/-- Weak law of large numbers for the instrument moments, and the population value of the
instrument-response block. -/
private theorem tendsto_in_measure_instrument_moments {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (InstrumentalVariableObservation p k)) [IsProbabilityMeasure Q]
    (h2 : MemLp id 2 Q) (horthogonal : ∀ i : Fin k, (∫ z, z.2.1 i * z.2.2 ∂Q) = 0)
    (X : ℕ → Ω → InstrumentalVariableObservation p k)
    (hiid : IsIndependentIdenticallyDistributed P X Q) (beta : EuclideanSpace ℝ (Fin p)) :
    TendstoInMeasure P (fun (n : ℕ) ω q ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i ω)) atTop
        (fun _ q ↦ ∫ z, instrumentMomentStatistic beta q z ∂Q) ∧
      instrumentMomentCross (fun q ↦ ∫ z, instrumentMomentStatistic beta q z ∂Q) =
        instrumentRegressorMoment Q *ᵥ beta.ofLp := by
  obtain ⟨hZ2, hX2, hE2⟩ := mem_lp_instrumental_variable_coordinates h2
  have hZX : ∀ i j, Integrable (fun z : InstrumentalVariableObservation p k ↦
      z.2.1 i * z.1 j) Q := fun i j ↦ (hZ2 i).integrable_mul (hX2 j)
  have hsum : ∀ i, Integrable (fun z : InstrumentalVariableObservation p k ↦
      ∑ j, z.2.1 i * z.1 j * beta j) Q :=
    fun i ↦ integrable_finsetSum _ fun j _ ↦ (hZX i j).mul_const (beta j)
  have hZE : ∀ i, Integrable (fun z : InstrumentalVariableObservation p k ↦
      z.2.1 i * z.2.2) Q := fun i ↦ (hZ2 i).integrable_mul hE2
  refine ⟨tendsto_in_measure_pi_const fun q ↦ tendsto_in_measure_sample_mean_of_iid P Q X hiid _
    ?_ ?_, ?_⟩
  · rcases q with ⟨i, j⟩ | ⟨i, j⟩ | i
    · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦
        z.2.1 i * z.2.1 j)
    · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦
        z.2.1 i * z.1 j)
    · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦ z.2.1 i).mul
        ((continuous_fst.inner continuous_const).measurable.add (by fun_prop))
  · rcases q with ⟨i, j⟩ | ⟨i, j⟩ | i
    · exact (hZ2 i).integrable_mul (hZ2 j)
    · exact hZX i j
    · exact ((hsum i).add (hZE i)).congr
        (ae_of_all _ fun z ↦ (instrument_moment_statistic_inr_inr beta i z).symm)
  · ext i
    change (∫ z, instrumentMomentStatistic beta (.inr (.inr i)) z ∂Q) = _
    simp_rw [instrument_moment_statistic_inr_inr]
    rw [integral_add (hsum i) (hZE i), horthogonal i, add_zero,
      integral_finsetSum _ fun j _ ↦ (hZX i j).mul_const (beta j)]
    simp only [integral_mul_const, mulVec, dotProduct, instrumentRegressorMoment]

open Matrix in
/-- GAPS 105.55: consistency of two-stage least squares. For independent identically
distributed observations `(xᵢ, zᵢ, εᵢ)` with finite second moments, instruments orthogonal to
the error (`E[z ε] = 0`), `E[z zᵀ]` positive definite, and the rank condition that
`Dᵀ E[z zᵀ]⁻¹ D` with `D = E[z xᵀ]` is positive definite, the estimator computed from
`yᵢ = ⟪xᵢ, β⟫ + εᵢ` converges in probability to `β`. -/
theorem tendsto_in_measure_two_stage_least_squares
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (InstrumentalVariableObservation p k)) [IsProbabilityMeasure Q]
    (h2 : MemLp id 2 Q)
    (horthogonal : ∀ i : Fin k, (∫ z, z.2.1 i * z.2.2 ∂Q) = 0)
    (hZ : (instrumentSecondMoment Q).PosDef)
    (hH : ((instrumentRegressorMoment Q).transpose * (instrumentSecondMoment Q)⁻¹ *
      instrumentRegressorMoment Q).PosDef)
    (X : ℕ → Ω → InstrumentalVariableObservation p k)
    (hiid : IsIndependentIdenticallyDistributed P X Q) (beta : EuclideanSpace ℝ (Fin p)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val ω))
          atTop (fun _ ↦ beta) := by
  obtain ⟨hV, hb₀⟩ := tendsto_in_measure_instrument_moments P Q h2 horthogonal X hiid beta
  set c₀ : InstrumentMomentIndex p k → ℝ := fun q ↦ ∫ z, instrumentMomentStatistic beta q z ∂Q
  have hN₀ : instrumentMomentNormal c₀ = (instrumentRegressorMoment Q)ᵀ *
      (instrumentSecondMoment Q)⁻¹ * instrumentRegressorMoment Q := rfl
  have hB₀ : instrumentMomentB c₀ = instrumentRegressorMoment Q := rfl
  obtain ⟨hG, -⟩ := continuous_at_instrument_moment_gain c₀ hZ.det_pos.ne'
    (by rw [hN₀]; exact hH.det_pos.ne')
  have hcross : Continuous (instrumentMomentCross (p := p) (k := k)) :=
    continuous_pi fun i ↦ continuous_apply _
  have hcont : ContinuousAt instrumentMomentEstimator c₀ :=
    (PiLp.continuous_toLp 2 _).continuousAt.comp
      (continuous_at_matrix_mul_vec hG hcross.continuousAt)
  have hval : instrumentMomentEstimator c₀ = beta := by
    rw [instrumentMomentEstimator, hb₀, ← hB₀, Matrix.mulVec_mulVec,
      instrument_moment_gain_mul_b c₀
        (by rw [hN₀]; exact (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit),
      Matrix.one_mulVec]
  have h := tendsto_in_measure_comp_const _ hcont hV
  rw [hval] at h
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact ae_of_all _ fun ω ↦
    (instrumental_variable_sample_estimator_eq beta (fun i ↦ X i ω) n hn).symm

open Matrix in
/-- The moment map of two-stage least squares is measurable. -/
private theorem measurable_instrument_moment_estimator {p k : ℕ} :
    Measurable (instrumentMomentEstimator (p := p) (k := k)) := by
  have hA : Measurable (instrumentMomentA (p := p) (k := k)) :=
    Measurable.of_eval_matrix _ fun i j ↦ measurable_pi_apply _
  have hB : Measurable (instrumentMomentB (p := p) (k := k)) :=
    Measurable.of_eval_matrix _ fun i j ↦ measurable_pi_apply _
  have hBt : Measurable fun v : InstrumentMomentIndex p k → ℝ ↦ (instrumentMomentB v)ᵀ :=
    Measurable.of_eval_matrix _ fun i j ↦ hB.eval_matrix
  have hK := TauCeti.measurable_matrix_mul.comp (hBt.prodMk (TauCeti.measurable_matrix_inv.comp hA))
  have hG : Measurable (instrumentMomentGain (p := p) (k := k)) :=
    TauCeti.measurable_matrix_mul.comp ((TauCeti.measurable_matrix_inv.comp
      (TauCeti.measurable_matrix_mul.comp (hK.prodMk hB))).prodMk hK)
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun j ↦ ?_)
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun i _ ↦ hG.eval_matrix.mul (measurable_pi_apply _)

/-- The instrument moment statistics are measurable. -/
private theorem measurable_instrument_moment_statistic {p k : ℕ}
    (beta : EuclideanSpace ℝ (Fin p)) (q : InstrumentMomentIndex p k) :
    Measurable (instrumentMomentStatistic beta q) := by
  rcases q with ⟨i, j⟩ | ⟨i, j⟩ | i
  · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦
      z.2.1 i * z.2.1 j)
  · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦
      z.2.1 i * z.1 j)
  · exact (by fun_prop : Measurable fun z : InstrumentalVariableObservation p k ↦ z.2.1 i).mul
      ((continuous_fst.inner continuous_const).measurable.add (by fun_prop))

open Matrix in
/-- `∫ (∑ᵢ aᵢ zᵢ ε)² = aᵀ Ω a` with `Ω = E[ε² z zᵀ]`. -/
private theorem integral_sum_score_sq {p k : ℕ} {Q : Measure (InstrumentalVariableObservation p k)}
    (hS : ∀ i : Fin k, MemLp (fun z : InstrumentalVariableObservation p k ↦ z.2.1 i * z.2.2) 2 Q)
    (a : Fin k → ℝ) :
    (∫ z, (∑ i, a i * (z.2.1 i * z.2.2)) ^ 2 ∂Q) = a ⬝ᵥ (instrumentErrorMoment Q *ᵥ a) := by
  have hint : ∀ i j, Integrable (fun z : InstrumentalVariableObservation p k ↦
      a i * (z.2.1 i * z.2.2) * (a j * (z.2.1 j * z.2.2))) Q := fun i j ↦
    (((hS i).integrable_mul (hS j)).const_mul (a i * a j)).congr
      (ae_of_all _ fun z ↦ by simp only [Pi.mul_apply]; ring)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hfun : (fun z : InstrumentalVariableObservation p k ↦
      a i * (z.2.1 i * z.2.2) * (a j * (z.2.1 j * z.2.2))) =
      fun z ↦ (a i * a j) * (z.2.2 ^ 2 * z.2.1 i * z.2.1 j) := by
    funext z
    ring
  rw [hfun, integral_const_mul, instrumentErrorMoment]
  ring

open Matrix in
/-- The score covariance `Ω = E[ε² z zᵀ]` is positive semidefinite. -/
private theorem pos_semidef_instrument_error_moment {p k : ℕ}
    {Q : Measure (InstrumentalVariableObservation p k)}
    (hS : ∀ i : Fin k, MemLp (fun z : InstrumentalVariableObservation p k ↦ z.2.1 i * z.2.2) 2 Q) :
    (instrumentErrorMoment Q).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨IsHermitian.ext fun i j ↦ ?_, fun x ↦ ?_⟩
  · simp only [instrumentErrorMoment, star_trivial]
    congr 1
    funext z
    ring
  · rw [star_trivial, ← integral_sum_score_sq hS x]
    exact integral_nonneg fun z ↦ sq_nonneg _

/-- Inner products of a matrix-vector product with a fixed vector. -/
private theorem inner_to_lp_mul_vec {p k : ℕ} (G : Matrix (Fin p) (Fin k) ℝ) (s : Fin k → ℝ)
    (t : EuclideanSpace ℝ (Fin p)) :
    inner ℝ (WithLp.toLp 2 (G.mulVec s)) t = ∑ i, (∑ j, t j * G j i) * s i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

open Matrix in
/-- On the event that the sample normal matrix is invertible, the scaled two-stage
least-squares error is the sample gain applied to the normalized score sum
`n^{-1/2} ∑ zᵢ εᵢ`. -/
private theorem sqrt_smul_instrumental_variable_sample_estimator_sub {p k : ℕ}
    (beta : EuclideanSpace ℝ (Fin p)) (X : ℕ → InstrumentalVariableObservation p k) (n : ℕ)
    (hn : n ≠ 0) (hu : IsUnit (instrumentMomentNormal fun q ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i)).det) :
    Real.sqrt n • (instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val) - beta) =
      WithLp.toLp 2 ((instrumentMomentGain fun q ↦ (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i)) *ᵥ
          fun i ↦ (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, (X l).2.1 i * (X l).2.2) := by
  set v : InstrumentMomentIndex p k → ℝ := fun q ↦ (n : ℝ)⁻¹ *
    ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i) with hv
  set S : Fin k → ℝ := fun i ↦ (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, (X l).2.1 i * (X l).2.2
    with hS
  have hsq : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  have hcr : instrumentMomentCross v = instrumentMomentB v *ᵥ beta.ofLp + (Real.sqrt n)⁻¹ • S := by
    ext i
    simp only [instrumentMomentCross, instrumentMomentB, hv, hS,
      instrument_moment_statistic_inr_inr, Finset.sum_add_distrib, mulVec, dotProduct,
      Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ by
        simp only [instrumentMomentStatistic]
        ring
    · have h' : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← mul_assoc (Real.sqrt n)⁻¹, h']
  rw [instrumental_variable_sample_estimator_eq beta X n hn, instrumentMomentEstimator, hcr,
    Matrix.mulVec_add, Matrix.mulVec_mulVec, instrument_moment_gain_mul_b _ hu, Matrix.one_mulVec,
    Matrix.mulVec_smul]
  ext j
  simp [hsq, hv]

/-- If random vectors converge in probability to `c` and `f` is continuous at `c` with
`f c ≠ 0`, then the probability that `f` vanishes at the vectors tends to `0`. -/
private theorem tendsto_measure_not_is_unit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {V : ℕ → Ω → ι → ℝ} {c : ι → ℝ}
    (hV : TendstoInMeasure P V atTop (fun _ ↦ c)) {f : (ι → ℝ) → ℝ} (hf : ContinuousAt f c)
    (hc : f c ≠ 0) : Tendsto (fun n ↦ P {ω | ¬ IsUnit (f (V n ω))}) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδd⟩ := Metric.continuousAt_iff.1 hf _ (abs_pos.2 hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoInMeasure_iff_dist.1 hV δ hδ) (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hlt
  have h := hδd (not_le.1 hlt)
  rw [Real.dist_eq] at h
  refine hω (isUnit_iff_ne_zero.2 fun h0 ↦ ?_)
  rw [h0, zero_sub, abs_neg] at h
  exact lt_irrefl _ h

open Matrix in
/-- The sandwich covariance of two-stage least squares is `M Ω Mᵀ` with the population gain
`M = H⁻¹ Dᵀ Σ_Z⁻¹`. -/
private theorem instrumental_variable_covariance_eq {p k : ℕ}
    (Q : Measure (InstrumentalVariableObservation p k)) (beta : EuclideanSpace ℝ (Fin p))
    (hZ : (instrumentSecondMoment Q).PosDef)
    (hH : ((instrumentRegressorMoment Q).transpose * (instrumentSecondMoment Q)⁻¹ *
      instrumentRegressorMoment Q).PosDef) :
    let c₀ : InstrumentMomentIndex p k → ℝ := fun q ↦ ∫ z, instrumentMomentStatistic beta q z ∂Q
    instrumentalVariableCovariance Q =
      instrumentMomentGain c₀ * instrumentErrorMoment Q * (instrumentMomentGain c₀)ᵀ := by
  intro c₀
  have hN₀ : instrumentMomentNormal c₀ = (instrumentRegressorMoment Q)ᵀ *
      (instrumentSecondMoment Q)⁻¹ * instrumentRegressorMoment Q := rfl
  have hZt : (instrumentMomentA c₀)⁻¹ᵀ = (instrumentMomentA c₀)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, ← conjTranspose_eq_transpose_of_trivial]
    exact congrArg Inv.inv hZ.isHermitian.eq
  have hHt : (instrumentMomentNormal c₀)⁻¹ᵀ = (instrumentMomentNormal c₀)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, ← conjTranspose_eq_transpose_of_trivial]
    exact congrArg Inv.inv hH.isHermitian.eq
  rw [instrumentMomentGain, transpose_mul, transpose_mul, transpose_transpose, hHt, hZt]
  simp only [instrumentalVariableCovariance]
  rw [← hN₀]
  simp only [Matrix.mul_assoc]
  rfl

open Matrix in
/-- GAPS 105.55: heteroscedasticity-robust two-stage least-squares central limit theorem.
Under the hypotheses of `tendsto_in_measure_two_stage_least_squares` and square
integrability of the score `ε z`, `√n (β̂ - β) ⇒ N(0, H⁻¹ Dᵀ Σ_Z⁻¹ Ω Σ_Z⁻¹ D H⁻¹)` with
`Ω = E[ε² z zᵀ]`. No fourth moments are needed. -/
theorem tendsto_in_distribution_two_stage_least_squares
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure (InstrumentalVariableObservation p k)) [IsProbabilityMeasure Q]
    (h2 : MemLp id 2 Q)
    (hscore : MemLp (fun z ↦ z.2.2 • z.2.1) 2 Q)
    (horthogonal : ∀ i : Fin k, (∫ z, z.2.1 i * z.2.2 ∂Q) = 0)
    (hZ : (instrumentSecondMoment Q).PosDef)
    (hH : ((instrumentRegressorMoment Q).transpose * (instrumentSecondMoment Q)⁻¹ *
      instrumentRegressorMoment Q).PosDef)
    (X : ℕ → Ω → InstrumentalVariableObservation p k)
    (hiid : IsIndependentIdenticallyDistributed P X Q) (beta : EuclideanSpace ℝ (Fin p)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n •
      (instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val ω) - beta))
      atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (instrumentalVariableCovariance Q)) := by
  obtain ⟨hV, hb₀⟩ := tendsto_in_measure_instrument_moments P Q h2 horthogonal X hiid beta
  set c₀ : InstrumentMomentIndex p k → ℝ := fun q ↦ ∫ z, instrumentMomentStatistic beta q z ∂Q
  have hN₀ : instrumentMomentNormal c₀ = (instrumentRegressorMoment Q)ᵀ *
      (instrumentSecondMoment Q)⁻¹ * instrumentRegressorMoment Q := rfl
  obtain ⟨hG, hdet⟩ := continuous_at_instrument_moment_gain c₀ hZ.det_pos.ne'
    (by rw [hN₀]; exact hH.det_pos.ne')
  set M₀ := instrumentMomentGain c₀ with hM₀
  have hS : ∀ i : Fin k, MemLp (fun z : InstrumentalVariableObservation p k ↦
      z.2.1 i * z.2.2) 2 Q := fun i ↦ hscore.of_le (by fun_prop) (ae_of_all _ fun z ↦ by
    have h := PiLp.norm_apply_le (z.2.2 • z.2.1) i
    rwa [PiLp.smul_apply, smul_eq_mul, mul_comm] at h)
  set Sn : ℕ → Ω → Fin k → ℝ := fun n ω i ↦
    (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, (X l ω).2.1 i * (X l ω).2.2 with hSn
  have hSbdd : ∀ i, IsBoundedInProbability P (fun n ω ↦ Sn n ω i) := fun i ↦
    is_bounded_in_probability_of_tendsto_in_distribution P _
      (tendsto_in_distribution_inv_sqrt_mul_sum_of_iid P Q X hiid _ (by fun_prop) (hS i)
        (horthogonal i))
  set Vn : ℕ → Ω → InstrumentMomentIndex p k → ℝ := fun n ω q ↦ (n : ℝ)⁻¹ *
    ∑ i ∈ Finset.range n, instrumentMomentStatistic beta q (X i ω) with hVn
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦ Real.sqrt n •
    (instrumentalVariableSampleEstimator beta (fun i : Fin n ↦ X i.val ω) - beta) with hTdef
  have hest : ∀ n ω, n ≠ 0 → instrumentalVariableSampleEstimator beta
      (fun i : Fin n ↦ X i.val ω) = instrumentMomentEstimator (Vn n ω) :=
    fun n ω hn ↦ instrumental_variable_sample_estimator_eq beta (fun i ↦ X i ω) n hn
  have hT : ∀ n ω, n ≠ 0 → IsUnit (instrumentMomentNormal (Vn n ω)).det →
      T n ω = WithLp.toLp 2 (instrumentMomentGain (Vn n ω) *ᵥ Sn n ω) :=
    fun n ω hn hu ↦ sqrt_smul_instrumental_variable_sample_estimator_sub beta (fun i ↦ X i ω) n hn hu
  have hVm : ∀ n, Measurable (Vn n) := fun n ↦ measurable_pi_iff.2 fun q ↦
    measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      (measurable_instrument_moment_statistic beta q).comp (hiid.1 i))
  have hTm : ∀ n, Measurable (T n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [hTdef, Nat.cast_zero, Real.sqrt_zero, zero_smul]
      exact measurable_const
    · have : T n = fun ω ↦ Real.sqrt n • (instrumentMomentEstimator (Vn n ω) - beta) :=
        funext fun ω ↦ by
          show Real.sqrt n • (_ - beta) = _
          rw [hest n ω hn]
      rw [this]
      exact ((measurable_instrument_moment_estimator.comp (hVm n)).sub_const _).const_smul
        (Real.sqrt n)
  have hbad := tendsto_measure_not_is_unit hV hdet (by rw [hN₀]; exact hH.det_pos.ne')
  -- Cramér–Wold
  have hΩ := pos_semidef_instrument_error_moment hS
  have hVeq : instrumentalVariableCovariance Q = M₀ * instrumentErrorMoment Q * M₀ᵀ :=
    instrumental_variable_covariance_eq Q beta hZ hH
  have hVpsd : (instrumentalVariableCovariance Q).PosSemidef := by
    have h := hΩ.mul_mul_conjTranspose_same M₀
    rwa [conjTranspose_eq_transpose_of_trivial, ← hVeq] at h
  refine TendstoInDistribution.of_inner aemeasurable_id (fun n ↦ (hTm n).aemeasurable)
    fun t ↦ ?_
  set a₀ : Fin k → ℝ := fun i ↦ ∑ j, t j * M₀ j i with ha₀
  set s : InstrumentalVariableObservation p k → ℝ := fun z ↦ ∑ i, a₀ i * (z.2.1 i * z.2.2)
    with hsdef
  have hsm : Measurable s := Finset.measurable_sum _ fun i _ ↦ measurable_const.mul
    (by fun_prop)
  have hs2 : MemLp s 2 Q := memLp_finsetSum _ fun i _ ↦ (hS i).const_mul (a₀ i)
  have hs0 : (∫ z, s z ∂Q) = 0 := by
    rw [hsdef, integral_finsetSum _ fun i _ ↦ ((hS i).integrable one_le_two).const_mul _]
    simp [integral_const_mul, horthogonal]
  have hF := tendsto_in_distribution_inv_sqrt_mul_sum_of_iid P Q X hiid s hsm hs2 hs0
  have hlaw : (multivariateGaussian 0 (instrumentalVariableCovariance Q)).map
      (fun x ↦ inner ℝ (id x) t) =
      (gaussianReal 0 (Real.toNNReal (∫ z, s z ^ 2 ∂Q))).map id := by
    rw [Measure.map_id]
    have hf : (fun x : EuclideanSpace ℝ (Fin p) ↦ inner ℝ (id x) t) = fun x ↦ inner ℝ t x :=
      funext fun x ↦ real_inner_comm _ _
    rw [hf, TauCeti.Probability.map_inner_multivariateGaussian 0 t hVpsd, inner_zero_right,
      hsdef, integral_sum_score_sq hS]
    congr 2
    rw [hVeq]
    have ha : a₀ = M₀ᵀ *ᵥ t.ofLp :=
      funext fun i ↦ Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    have hlin : ∀ (A : Matrix (Fin p) (Fin p) ℝ) (x : EuclideanSpace ℝ (Fin p)),
        (Matrix.toEuclideanLin A x).ofLp = A *ᵥ x.ofLp := fun A x ↦ rfl
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hlin]
    rw [ha, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hFm : ∀ n : ℕ, Measurable fun ω ↦ (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, s (X l ω) :=
    fun n ↦ measurable_const.mul (Finset.measurable_sum _ fun l _ ↦ hsm.comp (hiid.1 l))
  have hYm : ∀ n, Measurable fun ω ↦ inner ℝ (T n ω) t :=
    fun n ↦ (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin p) ↦ inner ℝ x t).comp
      (hTm n)
  refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable P _ _ hFm hYm
    (tendsto_in_distribution_of_map_eq hF (by fun_prop) hlaw) ?_
  set a : (InstrumentMomentIndex p k → ℝ) → Fin k → ℝ :=
    fun v i ↦ ∑ j, t j * instrumentMomentGain v j i with hadef
  have hcoef : ∀ i, TendstoInMeasure P (fun n ω ↦ a (Vn n ω) i - a₀ i) atTop (fun _ ↦ 0) := by
    intro i
    have hφ : Continuous fun M : Matrix (Fin p) (Fin k) ℝ ↦ ∑ j, t j * M j i - a₀ i :=
      (continuous_finsetSum _ fun j _ ↦ continuous_const.mul
        (continuous_id.matrix_elem j i)).sub continuous_const
    have h := tendsto_in_measure_comp_const _ (hφ.continuousAt.comp hG) hV
    simpa only [Function.comp_apply, ← hM₀, ha₀, sub_self] using h
  have hR : TendstoInMeasure P (fun n ω ↦ ∑ i, Sn n ω i * (a (Vn n ω) i - a₀ i)) atTop
      (fun _ ↦ 0) := by
    have hpi : TendstoInMeasure P (fun n ω i ↦ Sn n ω i * (a (Vn n ω) i - a₀ i)) atTop
        (fun _ ↦ 0) := tendsto_in_measure_pi_const (c := 0) fun i ↦
      tendsto_in_measure_mul_zero_of_is_bounded_in_probability P _ _ (hSbdd i) (hcoef i)
    have h := tendsto_in_measure_comp_const (fun w : Fin k → ℝ ↦ ∑ i, w i)
      (continuous_finsetSum _ fun i _ ↦ continuous_apply i).continuousAt hpi
    simpa only [Pi.zero_apply, Finset.sum_const_zero] using h
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum := (tendstoInMeasure_iff_dist.1 hR ε hε).add hbad
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  by_cases hu : IsUnit (instrumentMomentNormal (Vn n ω)).det
  · left
    have hFeq : (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, s (X l ω) = ∑ i, a₀ i * Sn n ω i := by
      simp only [hsdef, hSn, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
    have hdiff : inner ℝ (T n ω) t - (Real.sqrt n)⁻¹ * ∑ l ∈ Finset.range n, s (X l ω) =
        ∑ i, Sn n ω i * (a (Vn n ω) i - a₀ i) := by
      rw [hT n ω hn hu, inner_to_lp_mul_vec, hFeq, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hadef]; ring
    simp only [mem_ofPred_eq] at hω ⊢
    rwa [hdiff] at hω
  · exact Or.inr hu

end CKSD
