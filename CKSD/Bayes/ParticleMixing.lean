module
public import CKSD.Bayes.ParticleLimitCore
public import CKSD.Bayes.ParticleOscillation
/-!
# Mixing bounds for normalized Feynman–Kac transport

The backward normalizer is strictly positive and bounded above and below on every finite
horizon. Mutual transition comparison gives geometric oscillation decay of the normalized
backward operator with ratio `1-εM²`. Potential comparison also gives a time-uniform pairwise
ratio bound for the backward normalizer.

These are the one-step mixing estimates of Del Moral, *Feynman–Kac Formulae*, Proposition
4.3.3 and Corollary 4.3.3, printed pages 140–142 (PDF pages 154–156 of the local 2004 copy),
used in Theorem 7.4.4. The oscillation argument uses the local weighted-probability contraction
lemma; Mathlib supplies bounded Bochner integrals and measure monotonicity.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD
/-- Backward integration preserves measurability. -/
theorem FeynmanKacModel.measurable_backwardOperator
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ)
    {f : X → ℝ} (hf : Measurable f) : Measurable (M.backwardOperator p m f) := by
  induction m generalizing p with
  | zero => exact hf
  | succ m ih => exact (M.measurable_potential p).mul (M.measurable_integral_transition p (ih (p+1)))

/-- A positive lower and finite upper bound for the backward normalizing function. -/
theorem FeynmanKacModel.exists_backwardOperator_one_bounds
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x, M.backwardOperator p m (fun _ ↦ 1) x ∈ Icc a b := by
  induction m generalizing p with
  | zero => exact ⟨1,1,zero_lt_one, fun _ ↦ ⟨le_rfl,le_rfl⟩⟩
  | succ m ih =>
    obtain ⟨a,b,ha,hab⟩ := ih (p+1)
    obtain ⟨aG,bG,haG,hGb⟩ := M.potential_bounds p
    have := M.isMarkov_transition p
    have hgm : Measurable (M.backwardOperator (p+1) m (fun _ ↦ 1)) := by
      exact M.measurable_backwardOperator (p+1) m measurable_const
    have hgi (x : X) : Integrable (M.backwardOperator (p+1) m (fun _ ↦ 1)) (M.transition p x) :=
      Integrable.of_bound hgm.aestronglyMeasurable b (ae_of_all _ fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le (hab y).1)]
        exact (hab y).2)
    have hIb (x : X) : (∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x) ∈ Icc a b := by
      constructor
      · simpa using integral_mono_ae (integrable_const a) (hgi x) (ae_of_all _ fun y ↦ (hab y).1)
      · simpa using integral_mono_ae (hgi x) (integrable_const b) (ae_of_all _ fun y ↦ (hab y).2)
    refine ⟨aG*a,bG*b,mul_pos haG ha,fun x ↦ ?_⟩
    change aG*a ≤ M.potential p x * (∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x) ∧
      M.potential p x * (∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x) ≤ bG*b
    exact ⟨mul_le_mul (hGb x).1 (hIb x).1 ha.le (M.potential_pos p x).le,
      mul_le_mul (hGb x).2 (hIb x).2 (ha.trans_le (hIb x).1).le
        ((M.potential_pos p x).le.trans (hGb x).2)⟩

/-- Strict positivity of the backward normalizing function. -/
theorem FeynmanKacModel.backwardOperator_one_pos
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ) (x : X) :
    0 < M.backwardOperator p m (fun _ ↦ 1) x := by
  obtain ⟨a,b,ha,hab⟩ := M.exists_backwardOperator_one_bounds p m
  exact ha.trans_le (hab x).1

/-- The absolute backward integral is dominated by its normalizer times a terminal bound. -/
theorem FeynmanKacModel.abs_backwardOperator_le_mul_one
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ)
    {f : X → ℝ} {C : ℝ} (_hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) (x : X) :
    |M.backwardOperator p m f x| ≤ C * M.backwardOperator p m (fun _ ↦ 1) x := by
  induction m generalizing p x with
  | zero => simpa only [FeynmanKacModel.backwardOperator, mul_one] using hfb x
  | succ m ih =>
    have := M.isMarkov_transition p
    obtain ⟨a,b,ha,hab⟩ := M.exists_backwardOperator_one_bounds (p+1) m
    have hgi : Integrable (M.backwardOperator (p+1) m (fun _ ↦ 1)) (M.transition p x) :=
      Integrable.of_bound (M.measurable_backwardOperator _ _ measurable_const).aestronglyMeasurable b
        (ae_of_all _ fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le (hab y).1)]
          exact (hab y).2)
    have hInt : |∫ y, M.backwardOperator (p+1) m f y ∂M.transition p x| ≤
        C * ∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x := by
      rw [← integral_const_mul, ← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hgi.const_mul C)
      exact ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs] using ih (p+1) y
    change |M.potential p x * ∫ y, M.backwardOperator (p+1) m f y ∂M.transition p x| ≤ _
    rw [abs_mul, abs_of_pos (M.potential_pos p x)]
    change _ ≤ C * (M.potential p x * ∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x)
    nlinarith [mul_le_mul_of_nonneg_left hInt (M.potential_pos p x).le]

/-- The backward Feynman–Kac operator normalized at each starting state. -/
def FeynmanKacModel.normalizedBackwardOperator {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p m : ℕ) (f : X → ℝ) (x : X) : ℝ :=
  M.backwardOperator p m f x / M.backwardOperator p m (fun _ ↦ 1) x

/-- The normalized backward operator preserves a uniform terminal bound. -/
theorem FeynmanKacModel.abs_normalizedBackwardOperator_le
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ)
    {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) (x : X) :
    |M.normalizedBackwardOperator p m f x| ≤ C := by
  rw [FeynmanKacModel.normalizedBackwardOperator, abs_div,
    abs_of_pos (M.backwardOperator_one_pos p m x), div_le_iff₀ (M.backwardOperator_one_pos p m x)]
  exact M.abs_backwardOperator_le_mul_one p m hC hfb x

/-- Normalization cancels the current potential and gives a common positive weighted mean. -/
theorem FeynmanKacModel.normalizedBackwardOperator_succ
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (p m : ℕ) (f : X → ℝ) (x : X) :
    M.normalizedBackwardOperator p (m+1) f x =
      (∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y *
        M.normalizedBackwardOperator (p+1) m f y ∂M.transition p x) /
      (∫ y, M.backwardOperator (p+1) m (fun _ ↦ 1) y ∂M.transition p x) := by
  have heq : (fun y ↦ M.backwardOperator (p+1) m (fun _ ↦ 1) y *
      M.normalizedBackwardOperator (p+1) m f y) = M.backwardOperator (p+1) m f := by
    funext y
    unfold FeynmanKacModel.normalizedBackwardOperator
    field_simp [(M.backwardOperator_one_pos (p+1) m y).ne']
  rw [heq]
  exact mul_div_mul_left _ _ (M.potential_pos p x).ne'
/-- Mutual comparison of transitions gives geometric oscillation decay of normalized transport. -/
theorem FeynmanKacModel.abs_normalizedBackwardOperator_sub_le
    {X : Type*} [MeasurableSpace X] [Nonempty X] (M : FeynmanKacModel X)
    {ε : ℝ} (hε : ε ∈ Ioc 0 1)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal ε * M.transition n y A ≤ M.transition n x A)
    (p m : ℕ) {f : X → ℝ} (hf : Measurable f) {C D : ℝ}
    (hC : 0 ≤ C) (hfb : ∀ x, |f x| ≤ C) (hosc : ∀ x y, |f x-f y| ≤ D) (x y : X) :
    |M.normalizedBackwardOperator p m f x - M.normalizedBackwardOperator p m f y| ≤
      (1-ε^2)^m * D := by
  induction m generalizing p x y with
  | zero => simpa only [FeynmanKacModel.normalizedBackwardOperator, FeynmanKacModel.backwardOperator,
      div_one, pow_zero, one_mul] using hosc x y
  | succ m ih =>
    have := M.isMarkov_transition p
    have hxy : ENNReal.ofReal ε • M.transition p y ≤ M.transition p x := by
      exact (Measure.le_iff).2 fun A hA ↦ htransition p x y A hA
    have hyx : ENNReal.ofReal ε • M.transition p x ≤ M.transition p y := by
      exact (Measure.le_iff).2 fun A hA ↦ htransition p y x A hA
    obtain ⟨a,b,ha,hab⟩ := M.exists_backwardOperator_one_bounds (p+1) m
    have hKmeas : Measurable (M.normalizedBackwardOperator (p+1) m f) :=
      (M.measurable_backwardOperator _ _ hf).div (M.measurable_backwardOperator _ _ measurable_const)
    have h := abs_weighted_mean_sub_weighted_mean_le_of_minorization
      (M.transition p x) (M.transition p y) hε hxy hyx
      (M.measurable_backwardOperator _ _ measurable_const) hKmeas ha hab
      (fun z ↦ M.abs_normalizedBackwardOperator_le (p+1) m hC hfb z)
      (fun z w ↦ ih (p+1) z w)
    rw [M.normalizedBackwardOperator_succ p m f x,
      M.normalizedBackwardOperator_succ p m f y]
    convert h using 1; ring

/-- Pairwise potential and transition comparison gives a uniform normalizer ratio. -/
theorem FeynmanKacModel.mul_backwardOperator_one_le
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    {εG εM : ℝ} (hG : εG ∈ Ioc 0 1) (hM : εM ∈ Ioc 0 1)
    (hpotential : ∀ n x y, εG * M.potential n y ≤ M.potential n x)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal εM * M.transition n y A ≤ M.transition n x A)
    (p m : ℕ) (x y : X) :
    (εM*εG) * M.backwardOperator p m (fun _ ↦ 1) y ≤
      M.backwardOperator p m (fun _ ↦ 1) x := by
  cases m with
  | zero =>
    change εM*εG*1 ≤ 1
    nlinarith [mul_le_mul hM.2 hG.2 hG.1.le zero_le_one]
  | succ m =>
    have := M.isMarkov_transition p
    obtain ⟨a,b,ha,hab⟩ := M.exists_backwardOperator_one_bounds (p+1) m
    have hgi (z : X) : Integrable (M.backwardOperator (p+1) m (fun _ ↦ 1)) (M.transition p z) :=
      Integrable.of_bound (M.measurable_backwardOperator _ _ measurable_const).aestronglyMeasurable b
        (ae_of_all _ fun w ↦ by rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le (hab w).1)]; exact (hab w).2)
    have hxy : ENNReal.ofReal εM • M.transition p y ≤ M.transition p x :=
      (Measure.le_iff).2 fun A hA ↦ htransition p x y A hA
    have hcomp := integral_mono_measure hxy
      (ae_of_all _ fun z ↦ (M.backwardOperator_one_pos (p+1) m z).le) (hgi x)
    rw [integral_smul_measure, ENNReal.toReal_ofReal hM.1.le, smul_eq_mul] at hcomp
    have hIy : 0 ≤ ∫ z, M.backwardOperator (p+1) m (fun _ ↦ 1) z ∂M.transition p y :=
      integral_nonneg fun z ↦ (M.backwardOperator_one_pos (p+1) m z).le
    have hp := hpotential p x y
    have hmul := mul_le_mul hp hcomp (mul_nonneg hM.1.le hIy) (M.potential_pos p x).le
    change (εM*εG) * (M.potential p y * ∫ z,
      M.backwardOperator (p+1) m (fun _ ↦ 1) z ∂M.transition p y) ≤
      M.potential p x * ∫ z, M.backwardOperator (p+1) m (fun _ ↦ 1) z ∂M.transition p x
    convert hmul using 1; ring

end CKSD
