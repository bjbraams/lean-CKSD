module

public import CKSD.Bayes.ParticleMixing
/-!
# Normalized Feynman–Kac telescoping and deterministic test functions

Normalized transport of the empirical particle law minus the filtering expectation is the sum
of transported one-step sampling discrepancies. Each discrepancy can be written with two
deterministic bounded test functions: a normalized backward potential and a centered
transported test. Their bounds involve only the mixing comparison and geometric oscillation
decay, and therefore remain uniform in time.

This follows Del Moral, *Feynman–Kac Formulae*, equations (7.24)–(7.25), printed pages 244–245
(PDF pages 257–258 of the local 2004 copy). Splitting into two deterministic empirical errors
keeps conditional integration with respect to the prediction law explicit. Mathlib supplies
finite-sum and Bochner integral identities; mixing estimates are local project theory.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- A bounded terminal test has an integrable backward image under any probability measure. -/
theorem FeynmanKacModel.integrable_backward_operator
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (μ : Measure X) [IsProbabilityMeasure μ]
    (p m : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) :
    Integrable (M.backwardOperator p m f) μ := by
  obtain ⟨a,b,ha,hab⟩ := M.exists_backward_operator_one_bounds p m
  apply Integrable.of_bound (M.measurable_backward_operator p m hf).aestronglyMeasurable (C*b)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  exact (M.abs_backward_operator_le_mul_one p m hC hfb x).trans
    (mul_le_mul_of_nonneg_left (hab x).2 hC)

/-- The backward normalizer has positive expectation under every probability measure. -/
theorem FeynmanKacModel.integral_backward_operator_one_pos
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (μ : Measure X) [IsProbabilityMeasure μ]
    (p m : ℕ) : 0 < ∫ x, M.backwardOperator p m (fun _ ↦ 1) x ∂μ := by
  obtain ⟨a,b,ha,hab⟩ := M.exists_backward_operator_one_bounds p m
  apply ha.trans_le
  simpa using integral_mono_ae (integrable_const a)
    (M.integrable_backward_operator μ p m (f := fun _ : X ↦ (1:ℝ)) measurable_const zero_le_one (fun _ ↦ by norm_num))
    (ae_of_all _ fun x ↦ (hab x).1)

/-- Normalized Feynman–Kac transport starting from an arbitrary finite law. -/
def FeynmanKacModel.normalizedTransport {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p m : ℕ) (μ : Measure X) (f : X → ℝ) : ℝ :=
  (∫ x, M.backwardOperator p m f x ∂μ) / (∫ x, M.backwardOperator p m (fun _ ↦ 1) x ∂μ)

/-- Zero-step normalized transport is ordinary expectation under a probability law. -/
theorem FeynmanKacModel.normalized_transport_zero
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (μ : Measure X) [IsProbabilityMeasure μ]
    (p : ℕ) (f : X → ℝ) : M.normalizedTransport p 0 μ f = ∫ x, f x ∂μ := by
  simp [FeynmanKacModel.normalizedTransport, FeynmanKacModel.backwardOperator]

/-- Normalized transport of the initial law is the filtering expectation. -/
theorem FeynmanKacModel.normalized_transport_initial
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    (n : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hfb : ∀ x, |f x| ≤ C) :
    M.normalizedTransport 0 n (M.initial : Measure X) f = ∫ x, f x ∂M.filterLaw n := by
  have hfγ := M.integral_backward_operator 0 n hf hfb
  have h1γ := M.integral_backward_operator 0 n (f := fun _ : X ↦ (1:ℝ)) measurable_const (C := 1) (fun _ ↦ by norm_num)
  simp only [zero_add, FeynmanKacModel.unnormalized_law_zero] at hfγ h1γ
  rw [FeynmanKacModel.normalizedTransport, hfγ, h1γ, M.integral_filter_law,
    integral_const, smul_eq_mul, mul_one, div_eq_mul_inv, mul_comm]

/-- Normalized transport of the empirical law is the ratio of the two backward sums. -/
theorem FeynmanKacModel.normalized_transport_empirical_measure
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N) (p m : ℕ) (x : Fin N → X) (f : X → ℝ) :
    M.normalizedTransport p m (empiricalMeasure N x) f =
      (∑ i, M.backwardOperator p m f (x i)) / (∑ i, M.backwardOperator p m (fun _ ↦ 1) (x i)) := by
  rw [FeynmanKacModel.normalizedTransport, integral_empirical_measure_vector,
    integral_empirical_measure_vector, smul_eq_mul, smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero (Nat.cast_ne_zero.2 hN.ne'))

/-- Prediction law at a generation, conditional on its preceding particle generations. -/
def FeynmanKacModel.pathPredictionLaw {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (x : ℕ → Fin N → X) : ℕ → Measure X
  | 0 => M.initial
  | p+1 => M.particlePredictionLaw p (x p)

/-- Every path prediction law is a probability law for a nonempty particle population. -/
theorem FeynmanKacModel.is_probability_measure_path_prediction_law
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N)
    (x : ℕ → Fin N → X) (p : ℕ) : IsProbabilityMeasure (M.pathPredictionLaw x p) := by
  cases p with
  | zero => exact M.initial.prop
  | succ p => exact M.is_probability_measure_particle_prediction_law hN p (x p)

/-- Prediction integrals agree with the existing path prediction mean. -/
theorem FeynmanKacModel.integral_path_prediction_law
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) {N : ℕ}
    (x : ℕ → Fin N → X) (p : ℕ) (f : X → ℝ) :
    (∫ y, f y ∂M.pathPredictionLaw x p) = M.pathPredMean x p f := by
  cases p <;> rfl

/-- The normalized prediction transport joins the previous empirical transport. -/
theorem FeynmanKacModel.normalized_transport_particle_prediction_law
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N) (p m : ℕ) (x : Fin N → X)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ y, |f y| ≤ C) :
    M.normalizedTransport (p+1) m (M.particlePredictionLaw p x) f =
      M.normalizedTransport p (m+1) (empiricalMeasure N x) f := by
  obtain ⟨a,b,ha,hab⟩ := M.exists_backward_operator_one_bounds (p+1) m
  have h1b (y : X) : |M.backwardOperator (p+1) m (fun _ ↦ 1) y| ≤ b := by
    rw [abs_of_pos (ha.trans_le (hab y).1)]
    exact (hab y).2
  have hfb' (y : X) : |M.backwardOperator (p+1) m f y| ≤ C*b :=
    (M.abs_backward_operator_le_mul_one _ _ hC hfb y).trans
      (mul_le_mul_of_nonneg_left (hab y).2 hC)
  have hsum : 0 < ∑ i, M.potential p (x i) := by
    have : Nonempty (Fin N) := Fin.pos_iff_nonempty.1 hN
    exact Finset.sum_pos (fun _ _ ↦ M.potential_pos p _) Finset.univ_nonempty
  rw [FeynmanKacModel.normalizedTransport,
    M.integral_particle_prediction_law p x (M.measurable_backward_operator _ _ hf) hfb',
    M.integral_particle_prediction_law p x (M.measurable_backward_operator _ _ measurable_const) h1b,
    M.normalized_transport_empirical_measure hN]
  simp only [FeynmanKacModel.backwardOperator]
  field_simp [hsum.ne']

/-- Normalized transport preserves a uniform bound on the terminal test. -/
theorem FeynmanKacModel.abs_normalized_transport_le
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (μ : Measure X) [IsProbabilityMeasure μ]
    (p m : ℕ) {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) :
    |M.normalizedTransport p m μ f| ≤ C := by
  have hgi := M.integrable_backward_operator μ p m (f := fun _ : X ↦ (1:ℝ)) measurable_const zero_le_one (fun _ ↦ by norm_num)
  rw [FeynmanKacModel.normalizedTransport, abs_div,
    abs_of_pos (M.integral_backward_operator_one_pos μ p m),
    div_le_iff₀ (M.integral_backward_operator_one_pos μ p m)]
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hgi.const_mul C)
  exact ae_of_all _ fun x ↦ by
    simpa only [Real.norm_eq_abs] using M.abs_backward_operator_le_mul_one p m hC hfb x

/-- The normalized particle error is a telescoping sum of transported local sampling errors. -/
theorem FeynmanKacModel.particle_average_sub_filter_eq_sum_normalized_transport
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
    (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N) (x : ℕ → Fin N → X)
    (n : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) :
    (∑ i, f (x n i))/(N:ℝ) - (∫ y, f y ∂M.filterLaw n) =
      ∑ p ∈ Finset.range (n+1),
        (M.normalizedTransport p (n-p) (empiricalMeasure N (x p)) f -
          M.normalizedTransport p (n-p) (M.pathPredictionLaw x p) f) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfb (Classical.arbitrary X))
  let _ (p : ℕ) : IsProbabilityMeasure (empiricalMeasure N (x p)) :=
    is_probability_measure_empirical_measure hN _
  have htel (a b : ℕ → ℝ) (k : ℕ) :
      (∀ p < k, b (p+1) = a p) → (∑ p ∈ Finset.range (k+1), (a p-b p)) = a k-b 0 := by
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro h
      rw [Finset.sum_range_succ, ih (fun p hp ↦ h p (by omega)), h k (by omega)]
      ring
  have hs := htel
    (fun p ↦ M.normalizedTransport p (n-p) (empiricalMeasure N (x p)) f)
    (fun p ↦ M.normalizedTransport p (n-p) (M.pathPredictionLaw x p) f) n
    (fun p hp ↦ by
      change M.normalizedTransport (p+1) (n-(p+1)) (M.particlePredictionLaw p (x p)) f = _
      rw [show n-p = n-(p+1)+1 by omega]
      exact M.normalized_transport_particle_prediction_law hN p (n-(p+1)) (x p) hf hC hfb)
  simp only [Nat.sub_self, Nat.sub_zero, FeynmanKacModel.pathPredictionLaw] at hs
  rw [M.normalized_transport_zero, M.normalized_transport_initial n hf hfb,
    integral_empirical_measure_vector, smul_eq_mul] at hs
  simpa only [FeynmanKacModel.pathPredictionLaw, div_eq_mul_inv, mul_comm] using hs.symm
/-- A first-order ratio estimate with a common positive denominator lower bound. -/
theorem abs_div_sub_div_le_of_bound {a u v u' v' D : ℝ}
    (ha : 0 < a) (hv : a ≤ v) (hv' : a ≤ v') (hu' : |u'| ≤ D*v') :
    |u/v-u'/v'| ≤ (|u-u'|+D*|v-v'|)/a := by
  have hv0 := ha.trans_le hv
  have hv'0 := ha.trans_le hv'
  let r := u'/v'
  have hr : |r| ≤ D := by
    rw [show r=u'/v' from rfl,abs_div,abs_of_pos hv'0,div_le_iff₀ hv'0]
    exact hu'
  have heq : u/v-u'/v' = ((u-u')-r*(v-v'))/v := by
    dsimp [r]
    field_simp
    ring
  rw [heq,abs_div,abs_of_pos hv0]
  have hnum : |(u-u')-r*(v-v')| ≤ |u-u'|+D*|v-v'| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hr (abs_nonneg _))
  have hD0 : 0 ≤ D := (abs_nonneg r).trans hr
  exact div_le_div₀ (by positivity) hnum ha hv

/-- Deterministic bounded test functions reduce each normalized transport discrepancy to
ordinary empirical discrepancies, with constants uniform in the horizon. -/
theorem FeynmanKacModel.exists_normalized_transport_test_pair
    {X : Type*} [MeasurableSpace X] [Nonempty X] (M : FeynmanKacModel X)
    {εG εM : ℝ} (hG : εG ∈ Ioc 0 1) (hM : εM ∈ Ioc 0 1)
    (hpotential : ∀ n x y, εG * M.potential n y ≤ M.potential n x)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal εM * M.transition n y A ≤ M.transition n x A)
    (p m : ℕ) {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) (hosc : ∀ x y, |f x-f y| ≤ 1) :
    ∃ a : ℝ, ∃ g v : X → ℝ, Measurable g ∧ Measurable v ∧
      (∀ x, g x ∈ Icc (εM*εG) (1/(εM*εG))) ∧
      (∀ x, |v x| ≤ (1-εM^2)^m * g x) ∧
      (∀ μ : Measure X, IsProbabilityMeasure μ →
        M.normalizedTransport p m μ f = a + (∫ x, v x ∂μ)/(∫ x, g x ∂μ)) := by
  let x₀ := Classical.arbitrary X
  let g₀ := M.backwardOperator p m (fun _ ↦ 1) x₀
  let a := M.normalizedBackwardOperator p m f x₀
  let g : X → ℝ := fun x ↦ M.backwardOperator p m (fun _ ↦ 1) x/g₀
  let v : X → ℝ := fun x ↦ g x*(M.normalizedBackwardOperator p m f x-a)
  have hg₀ : 0 < g₀ := M.backward_operator_one_pos p m x₀
  have hα : 0 < εM*εG := mul_pos hM.1 hG.1
  have hg (x : X) : g x ∈ Icc (εM*εG) (1/(εM*εG)) := by
    constructor
    · rw [show g x=M.backwardOperator p m (fun _ ↦ 1) x/g₀ from rfl,le_div_iff₀ hg₀]
      exact M.mul_backward_operator_one_le hG hM hpotential htransition p m x x₀
    · rw [show g x=M.backwardOperator p m (fun _ ↦ 1) x/g₀ from rfl,div_le_iff₀ hg₀]
      have h := M.mul_backward_operator_one_le hG hM hpotential htransition p m x₀ x
      calc
        M.backwardOperator p m (fun _ ↦ 1) x ≤ g₀/(εM*εG) := by
          apply (le_div_iff₀ hα).2
          dsimp only [g₀]
          nlinarith [h]
        _ = (1/(εM*εG))*g₀ := by ring
  have hgpos (x : X) : 0 < g x := hα.trans_le (hg x).1
  have hgm : Measurable g := (M.measurable_backward_operator p m measurable_const).div_const g₀
  have hKm : Measurable (M.normalizedBackwardOperator p m f) :=
    (M.measurable_backward_operator p m hf).div (M.measurable_backward_operator p m measurable_const)
  have hvm : Measurable v := hgm.mul (hKm.sub_const a)
  refine ⟨a,g,v,hgm,hvm,hg,fun x ↦ ?_,fun μ hμ ↦ ?_⟩
  · dsimp only [v]
    rw [abs_mul,abs_of_pos (hgpos x),mul_comm]
    have h := M.abs_normalized_backward_operator_sub_le hM htransition p m hf hC hfb hosc x x₀
    simpa only [mul_one] using mul_le_mul_of_nonneg_right h (hgpos x).le
  · let _ : IsProbabilityMeasure μ := hμ
    have hQfi := M.integrable_backward_operator μ p m hf hC hfb
    have hQ1i := M.integrable_backward_operator μ p m (f := fun _ : X ↦ (1:ℝ)) measurable_const zero_le_one (fun _ ↦ by norm_num)
    have hQ1pos := M.integral_backward_operator_one_pos μ p m
    have hvEq : v = fun x ↦ (M.backwardOperator p m f x-a*M.backwardOperator p m (fun _ ↦ 1) x)/g₀ := by
      funext x
      dsimp only [v,g,FeynmanKacModel.normalizedBackwardOperator]
      field_simp [(M.backward_operator_one_pos p m x).ne',hg₀.ne']
    have hgiEq : (∫ x, g x ∂μ) = (∫ x, M.backwardOperator p m (fun _ ↦ 1) x ∂μ)/g₀ := by
      exact integral_div g₀ _
    have hviEq : (∫ x, v x ∂μ) =
        ((∫ x, M.backwardOperator p m f x ∂μ)-a*(∫ x, M.backwardOperator p m (fun _ ↦ 1) x ∂μ))/g₀ := by
      rw [hvEq,integral_div,integral_sub hQfi (hQ1i.const_mul a),integral_const_mul]
    rw [hgiEq,hviEq,FeynmanKacModel.normalizedTransport]
    field_simp [hg₀.ne',hQ1pos.ne']
    ring

end CKSD
