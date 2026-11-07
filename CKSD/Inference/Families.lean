module

public import CKSD.Inference.Model
public import CKSD.Inference.Sufficiency
public import CKSD.Asymptotics.Basic
public import TauCeti.Probability.Distributions.OrderStatistic.Joint
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
public import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Statistical families, order statistics, and comparison of experiments

Concrete interfaces for the families in Section 101 of `GAPS.md`. Sorting and single order
statistics are TauCeti constructions; decision rules and mixtures are Mathlib kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- A regular scalar natural exponential family on an open convex parameter domain. -/
structure RealExponentialFamily (X : Type*) [MeasurableSpace X] where
  /-- Base measure, including any parameter-free carrier density. -/
  base : Measure X
  /-- The base measure is sigma finite. -/
  sigmaFinite : SigmaFinite base
  /-- Real natural statistic. -/
  statistic : X → ℝ
  /-- Measurability of the statistic. -/
  measurable_statistic : Measurable statistic
  /-- Parameter domain. -/
  domain : Set ℝ
  /-- Regularity of the domain. -/
  isOpen_domain : IsOpen domain
  /-- Interval property of the domain. -/
  convex_domain : Convex ℝ domain
  /-- The parameter domain is nonempty. -/
  nonempty_domain : domain.Nonempty
  /-- Exponential integrability at each parameter. -/
  integrable_exp : ∀ η ∈ domain, Integrable (fun x ↦ Real.exp (η * statistic x)) base
  /-- The base measure is nonzero. -/
  base_ne_zero : base ≠ 0
  /-- Nondegeneracy of the statistic. -/
  nonconstant : ∀ c : ℝ, ¬ (∀ᵐ x ∂base, statistic x = c)

/-- Log normalizer of a scalar exponential family. -/
def RealExponentialFamily.cumulant {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η : ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (η * F.statistic x) ∂F.base)

/-- The family law at a natural parameter. -/
def RealExponentialFamily.law {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η : F.domain) : Measure X :=
  F.base.withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (η.val * F.statistic x - F.cumulant η.val)))

/-- A statistic on a finite sample is symmetric under all coordinate permutations. -/
def IsSymmetricStatistic {X Y : Type*} {n : ℕ} (T : (Fin n → X) → Y) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) x, T (x ∘ σ) = T x

/-- Completeness restricted to the symmetric sample statistics. -/
def IsSymmetricallyComplete {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (n : ℕ) : Prop :=
  ∀ g : (Fin n → X) → ℝ, Measurable g → IsSymmetricStatistic g →
    (∀ θ, Integrable g (Measure.pi fun _ : Fin n ↦ P θ) ∧
      (∫ x, g x ∂(Measure.pi fun _ : Fin n ↦ P θ)) = 0) →
    ∀ θ, g =ᵐ[Measure.pi fun _ : Fin n ↦ P θ] 0

/-- GAPS 101.13: completeness of permutation-invariant statistics in a convex complete model. -/
theorem isSymmetricallyComplete_of_complete_convex_family
    {X : Type*} [MeasurableSpace X] (C : Set (ProbabilityMeasure X))
    (hc : IsCompleteStatistic (fun P : C ↦ (P.val : Measure X)) id)
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure X) = (a : ℝ≥0∞) • (P : Measure X) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure X)) (n : ℕ) :
    IsSymmetricallyComplete (fun P : C ↦ (P.val : Measure X)) n := by
  sorry

/-- GAPS 101.21: joint order-statistic density for an absolutely continuous law.
The proof combines TauCeti's chamber formula `TauCeti.Probability.map_orderStatistics_pi` with
TauCeti's product-density identity `TauCeti.pi_withDensity`. -/
theorem map_orderStatistics_eq_withDensity {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f) :
    (Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ TauCeti.orderStatistic i x) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x ↦
        if StrictMono x then ENNReal.ofReal ((n.factorial : ℝ) * ∏ i, f (x i)) else 0) := by
  have hPeq := hf.2.2
  have hns : NullSingletonClass P := by rw [hPeq]; infer_instance
  have hsf : SigmaFinite (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) := by
    rw [← hPeq]; infer_instance
  have hC : MeasurableSet {x : Fin n → ℝ | StrictMono x} :=
    TauCeti.measurableSet_setOf_strictMono
  rw [TauCeti.Probability.map_orderStatistics_pi, hPeq,
    TauCeti.pi_withDensity (fun _ ↦ (volume : Measure ℝ)) (fun _ ↦ hf.1.ennreal_ofReal),
    ← volume_pi, restrict_withDensity hC, ← withDensity_indicator hC, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    ← withDensity_smul]
  swap
  · exact (Finset.measurable_prod _ fun i _ ↦
      hf.1.ennreal_ofReal.comp (measurable_pi_apply i)).indicator hC
  refine withDensity_congr_ae ?_
  have hnn : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ∀ i, 0 ≤ f (x i) := by
    rw [volume_pi, ae_all_iff]
    exact fun i ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ (volume : Measure ℝ))
      (i := i)).eventually (p := fun t ↦ 0 ≤ f t) hf.2.1
  filter_upwards [hnn] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, indicator, mem_ofPred_eq]
  split_ifs
  · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hx i,
      ENNReal.ofReal_natCast]
  · simp

/-- GAPS 101.21: the marginal density of the zero-indexed `j`th order statistic. -/
theorem map_orderStatistic_eq_withDensity {n : ℕ} (j : Fin n) (P : Measure ℝ)
    [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f) :
    (Measure.pi fun _ : Fin n ↦ P).map (TauCeti.orderStatistic j) =
      volume.withDensity (fun x ↦ ENNReal.ofReal
        ((n.factorial : ℝ) / (j.val.factorial * (n - j.val - 1).factorial) *
          cdf P x ^ j.val * (1 - cdf P x) ^ (n - j.val - 1) * f x)) := by
  sorry

/-- GAPS 101.21: ranks are uniform and independent of the sorted atomless sample. -/
theorem sorting_permutation_uniform_and_indep {n : ℕ} (P : Measure ℝ)
    [IsProbabilityMeasure P] [NullSingletonClass P] :
    letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤;
    let μ := Measure.pi fun _ : Fin n ↦ P;
    μ.map Tuple.sort = (n.factorial : ℝ≥0∞)⁻¹ • Measure.count ∧
      IndepFun Tuple.sort (fun x i ↦ TauCeti.orderStatistic i x) μ := by
  sorry

/-- Location-equivariance of a real estimator on a finite sample. -/
def IsLocationEquivariant {n : ℕ} (δ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x a, δ (fun i ↦ x i + a) = δ x + a

/-- The Pitman location estimator, using an improper Lebesgue prior. -/
def pitmanEstimator {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ u, u * ∏ i, f (x i - u)) / (∫ u, ∏ i, f (x i - u))

/-- GAPS 101.40: the Pitman estimator minimizes equivariant squared-error risk.
The normalizing and first-moment integrals are assumed to exist almost surely explicitly. -/
theorem pitmanEstimator_minimum_equivariant_risk {n : ℕ} (hn : 0 < n)
    (P : Measure ℝ) [IsProbabilityMeasure P] (f : ℝ → ℝ) (hf : HasDensity P volume f)
    (δ : (Fin n → ℝ) → ℝ) (hm : Measurable δ) (heq : IsLocationEquivariant δ)
    (h2 : MemLp δ 2 (Measure.pi fun _ : Fin n ↦ P))
    (hint : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P),
      Integrable (fun u ↦ ∏ i, f (x i - u)) volume ∧
      Integrable (fun u ↦ u * ∏ i, f (x i - u)) volume ∧
      0 < ∫ u, ∏ i, f (x i - u)) :
    (∫ x, pitmanEstimator f x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P)) ≤
      ∫ x, δ x ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) := by
  sorry

/-- Interval-rejection test with arbitrary randomization at the endpoints. -/
def intervalTest (T : ℝ) (c₁ c₂ γ₁ γ₂ : ℝ) : ℝ :=
  if c₁ < T ∧ T < c₂ then 1 else if T = c₁ then γ₁ else if T = c₂ then γ₂ else 0

/-- GAPS 101.50: the UMP test for the complement of an interval in a scalar exponential family. -/
theorem exists_ump_interval_test {X : Type*} [MeasurableSpace X]
    (F : RealExponentialFamily X) (η₁ η₂ : F.domain) (hη : η₁.val < η₂.val)
    (α : ℝ) (hα : α ∈ Ioo 0 1) :
    ∃ c₁ c₂ γ₁ γ₂ : ℝ, c₁ ≤ c₂ ∧ γ₁ ∈ Icc 0 1 ∧ γ₂ ∈ Icc 0 1 ∧
      let φ := fun x ↦ intervalTest (F.statistic x) c₁ c₂ γ₁ γ₂;
      testPower F.law φ η₁ = α ∧ testPower F.law φ η₂ = α ∧
      IsUniformlyMostPowerfulTest F.law {η | η.val ≤ η₁.val ∨ η₂.val ≤ η.val}
        {η | η₁.val < η.val ∧ η.val < η₂.val} α φ := by
  sorry

/-- GAPS 101.53: essentially complete one-sided tests in the mutually equivalent, positive-density
case. -/
theorem exists_one_sided_test_risk_le {X : Type*} [MeasurableSpace X]
    (P : ℝ → Measure X) (μ : Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (f : ℝ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    (hpos : ∀ θ x, 0 < f θ x) (T : X → ℝ) (hT : Measurable T)
    (hmlr : ∀ a b, a < b → ∃ r : ℝ → ℝ, Monotone r ∧ ∀ x, f b x / f a x = r (T x))
    (L : ℝ → Bool → ℝ) (θ₀ : ℝ)
    (hlow : ∀ θ < θ₀, 0 < L θ true - L θ false)
    (hhigh : ∀ θ > θ₀, L θ true - L θ false < 0)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ) :
    ∃ c : EReal, ∃ γ ∈ Icc (0 : ℝ) 1,
      let ψ := fun x ↦ if c < (T x : EReal) then 1 else if (T x : EReal) = c then γ else 0;
      IsStatisticalTest ψ ∧ ∀ θ,
        L θ false + (L θ true - L θ false) * testPower P ψ θ ≤
          L θ false + (L θ true - L θ false) * testPower P φ θ := by
  sorry

/-- GAPS 101.54: a level-valid mixture-optimal test is most powerful of level `α` for the composite
null. The least-favorability and concentration statements are not included. -/
theorem most_powerful_of_mixture_null {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (P : Kernel Θ X) [IsMarkovKernel P] (Λ : Measure Θ) [IsProbabilityMeasure Λ]
    (Q : Measure X) [IsProbabilityMeasure Q] (α : ℝ) (φ : X → ℝ)
    (hφ : IsStatisticalTest φ) (hlevel : ∀ θ, (∫ x, φ x ∂P θ) ≤ α)
    (hopt : ∀ ψ, IsStatisticalTest ψ → (∫ x, ψ x ∂P ∘ₘ Λ) ≤ α →
      (∫ x, ψ x ∂Q) ≤ ∫ x, φ x ∂Q) :
    HasTestLevel P univ α φ ∧ ∀ ψ, IsStatisticalTest ψ → (∀ θ, (∫ x, ψ x ∂P θ) ≤ α) →
      (∫ x, ψ x ∂Q) ≤ ∫ x, φ x ∂Q := by
  refine ⟨⟨hφ, fun θ _ ↦ hlevel θ⟩, ?_⟩
  intro ψ hψ hψlevel
  apply hopt ψ hψ
  have hint : Integrable ψ (P ∘ₘ Λ) := by
    refine Integrable.of_bound (C := 1) hψ.1.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hψ.2 x).1], (hψ.2 x).2⟩
  rw [integral_comp_eq_integral_integral P Λ ψ hint]
  calc (∫ θ, ∫ x, ψ x ∂P θ ∂Λ) ≤ ∫ _θ, α ∂Λ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun θ ↦ integral_nonneg fun x ↦ (hψ.2 x).1
        · exact integrable_const α
        · exact ae_of_all _ hψlevel
    _ = α := by simp

/-- GAPS 101.56: ratio is maximal invariant on the reduced mean/positive-scale space. -/
theorem mean_scale_ratio_eq_iff (x y s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    x / s = y / t ↔ ∃ c > 0, y = c * x ∧ t = c * s := by
  constructor
  · intro h
    refine ⟨t / s, div_pos ht hs, ?_, ?_⟩
    · have hcross := (div_eq_div_iff (ne_of_gt hs) (ne_of_gt ht)).mp h
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (ne_of_gt hs)).mpr
      nlinarith
    · exact (div_mul_cancel₀ t (ne_of_gt hs)).symm
  · rintro ⟨c, hc, rfl, rfl⟩
    field_simp

/-- GAPS 101.58: Blyth's admissibility criterion in a class with continuous risks. -/
theorem isAdmissibleRisk_of_blyth {d : ℕ} {D : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (hinterior : (interior Θ).Nonempty) (R : D → Θ → ℝ)
    (hc : ∀ δ, Continuous (R δ)) (δ₀ : D) (π : ℕ → Measure Θ)
    (hπ : ∀ n, IsFiniteMeasure (π n)) (δ : ℕ → D)
    (hbayes : ∀ n, IsBayesRule R (π n) (δ n))
    (hint : ∀ n a, Integrable (R a) (π n))
    (hmass : ∀ C : Set Θ, Convex ℝ (Subtype.val '' C) →
      (interior (Subtype.val '' C)).Nonempty →
      ∃ K > 0, ∀ᶠ n in atTop, K ≤ (π n).real C)
    (hgap : Tendsto (fun n ↦ (∫ θ, R δ₀ θ ∂π n) - ∫ θ, R (δ n) θ ∂π n) atTop (𝓝 0)) :
    IsAdmissibleRisk R δ₀ := by
  rintro ⟨δ', hle, θ₁, hlt⟩
  set ε := (R δ₀ θ₁ - R δ' θ₁) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  -- a ball around `θ₁` on which the risk gap exceeds `ε`
  have hcont : Continuous (fun θ ↦ R δ₀ θ - R δ' θ) := (hc δ₀).sub (hc δ')
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.1 hcont θ₁ ε hε0
  let C : Set Θ := {θ | dist θ θ₁ < ρ}
  have hCimg : Subtype.val '' C = Metric.ball θ₁.val ρ ∩ Θ := by
    ext z
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨hθ, θ.2⟩
    · rintro ⟨hz, hzΘ⟩
      exact ⟨⟨z, hzΘ⟩, hz, rfl⟩
  have hCconv : Convex ℝ (Subtype.val '' C) := by
    rw [hCimg]; exact (convex_ball _ _).inter hΘ
  have hCint : (interior (Subtype.val '' C)).Nonempty := by
    rw [hCimg, interior_inter, Metric.isOpen_ball.interior_eq]
    have hcl : θ₁.val ∈ closure (interior Θ) := by
      rw [hΘ.closure_interior_eq_closure_of_nonempty_interior hinterior]
      exact subset_closure θ₁.2
    obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
    exact ⟨z, by rw [Metric.mem_ball, dist_comm]; exact hdist, hz⟩
  obtain ⟨K, hK, hKev⟩ := hmass C hCconv hCint
  have hCm : MeasurableSet C :=
    measurableSet_lt (measurable_id.dist measurable_const) measurable_const
  have hlower : ∀ᶠ n in atTop,
      ε * K ≤ (∫ θ, R δ₀ θ ∂π n) - ∫ θ, R (δ n) θ ∂π n := by
    filter_upwards [hKev] with n hn
    have := hπ n
    have hb := hbayes n δ'
    have hdiff : Integrable (fun θ ↦ R δ₀ θ - R δ' θ) (π n) := (hint n δ₀).sub (hint n δ')
    have hnn : 0 ≤ᵐ[π n] fun θ ↦ R δ₀ θ - R δ' θ :=
      ae_of_all _ fun θ ↦ sub_nonneg.2 (hle θ)
    have h1 := setIntegral_le_integral (s := C) hdiff hnn
    have h2 := setIntegral_ge_of_const_le_real (μ := π n) (c := ε) hCm (measure_ne_top _ _)
      (fun θ hθ ↦ by
        have := hball θ hθ
        rw [Real.dist_eq] at this
        have h3 := neg_abs_le (R δ₀ θ - R δ' θ - (R δ₀ θ₁ - R δ' θ₁))
        linarith) hdiff.integrableOn
    rw [integral_sub (hint n δ₀) (hint n δ')] at h1
    nlinarith [mul_le_mul_of_nonneg_left hn hε0.le]
  have hlim : ε * K ≤ 0 := ge_of_tendsto hgap hlower
  nlinarith [mul_pos hε0 hK]

/-- Finite-decision risk comparison, the decision side of Blackwell's theorem. -/
def IsMoreInformative {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y) : Prop :=
  ∀ n : ℕ, ∀ L : Θ → Fin n → ℝ, (∃ C, ∀ θ a, |L θ a| ≤ C) →
    ∀ δ : RandomizedDecisionRule Y (Fin n), ∃ δ' : RandomizedDecisionRule X (Fin n),
      ∀ θ, risk P L δ' θ ≤ risk Q L δ θ

/-- GAPS 101.62: Blackwell's comparison theorem for finite parameter, dominated experiments. -/
theorem isMoreInformative_iff_isGarbling {Θ X Y : Type*} [Fintype Θ]
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Θ → Measure X) (Q : Θ → Measure Y)
    (hP : ∀ θ, IsProbabilityMeasure (P θ)) (hQ : ∀ θ, IsProbabilityMeasure (Q θ))
    (μ : Measure X) [SigmaFinite μ] (ν : Measure Y) [SigmaFinite ν]
    (hPac : ∀ θ, P θ ≪ μ) (hQac : ∀ θ, Q θ ≪ ν) :
    IsMoreInformative P Q ↔ IsGarbling P Q := by
  sorry

end CKSD
