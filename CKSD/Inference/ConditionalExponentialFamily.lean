module

public import CKSD.Inference.Basic
public import Mathlib.Probability.Kernel.WithDensity
public import CKSD.Inference.Factorization
public import CKSD.Inference.LaplaceDeterminacy


/-!
# Conditional exponential families and conditional tests

Natural exponential families whose natural statistic splits as a pair `(T, S)`: the conditional
law of `T` given `S` and the conditional UMPU tests in the presence of a nuisance parameter.

## Main definitions

* `CKSD.splitLogPartition`, `CKSD.splitExponentialFamilyMeasure`: the family with density
  `exp (⟪η, T⟫ + ⟪ζ, S⟫ - A(η, ζ))`.
* `CKSD.conditionalExponentialKernel κ η`: the kernel `s ↦ exp (⟪η, t⟫ - A_s(η)) κ s (dt)`.
* `CKSD.IsMinimalSplitStatistic`.

## Main results

* `CKSD.exists_kernel_conditional_exponential_family`: the conditional law of `T` given `S` is a
  parameter-free exponential tilt depending only on `η` (GAPS 101.43).
* `CKSD.is_uniformly_most_powerful_unbiased_test_conditional_two_sided` and
  `CKSD.is_uniformly_most_powerful_unbiased_test_conditional_one_sided`: conditional UMPU tests with a
  nuisance parameter (GAPS 101.46).

## Implementation notes

Conditional laws are expressed by Mathlib's measure-kernel composition `⊗ₘ` and conditional
sizes by Mathlib's conditional expectation.
-/
@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Log partition function of a natural exponential family whose natural statistic is the pair
`(T, S)`, with natural parameter `(η, ζ)`. -/
def splitLogPartition (ν : Measure X) (T : X → E) (S : X → F) (η : E) (ζ : F) : ℝ :=
  Real.log (∫ x, Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x)) ∂ν)

/-- The natural exponential law with density `exp(η·T + ζ·S - A(η, ζ))` with respect to the
base measure `ν`; it is a probability measure on the natural parameter space when `ν ≠ 0`. -/
def splitExponentialFamilyMeasure (ν : Measure X) (T : X → E) (S : X → F) (η : E) (ζ : F) :
    Measure X :=
  ν.withDensity (fun x ↦ ENNReal.ofReal
    (Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x) - splitLogPartition ν T S η ζ)))

/-- The exponential tilt of a family of measures `ν_s` by the parameter `η`, normalized in each
fibre: the kernel `s ↦ exp(η·t - A_s(η)) ν_s(dt)` with `A_s(η) = log ∫ exp(η·t) ν_s(dt)`. -/
def conditionalExponentialKernel [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel F E) [IsSFiniteKernel κ] (η : E) : Kernel F E :=
  Kernel.withDensity κ (fun s t ↦ ENNReal.ofReal
    (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ η t') ∂κ s))))

/-- Exponential tilting of a composition product. If `μ` is a finite measure and `κ` a Markov
kernel, and the tilt of `μ ⊗ₘ κ` by `exp (a t + b s)` is finite, then this tilt is its first
marginal composed with the fibrewise normalized tilt `s ↦ exp (a t - log ∫ exp (a t') κ s) κ s`. -/
theorem with_density_exp_comp_prod_eq_fst_comp_prod {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {a : β → ℝ} {b : α → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hfin : IsFiniteMeasure
      ((μ ⊗ₘ κ).withDensity fun p ↦ ENNReal.ofReal (Real.exp (a p.2 + b p.1)))) :
    (μ ⊗ₘ κ).withDensity (fun p ↦ ENNReal.ofReal (Real.exp (a p.2 + b p.1))) =
      ((μ ⊗ₘ κ).withDensity fun p ↦ ENNReal.ofReal (Real.exp (a p.2 + b p.1))).fst ⊗ₘ
        κ.withDensity (fun s t ↦ ENNReal.ofReal
          (Real.exp (a t - Real.log (∫ t', Real.exp (a t') ∂κ s)))) := by
  set Q' := (μ ⊗ₘ κ).withDensity fun p ↦ ENNReal.ofReal (Real.exp (a p.2 + b p.1))
  set ρ : α → β → ℝ≥0∞ := fun s t ↦ ENNReal.ofReal (Real.exp (a t + b s))
  have hρ : Measurable (Function.uncurry ρ) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((ha.comp measurable_snd).add (hb.comp measurable_fst)))
  set Z : α → ℝ := fun s ↦ ∫ t, Real.exp (a t) ∂κ s
  have hZm : Measurable Z :=
    ((Real.measurable_exp.comp ha).stronglyMeasurable.integral_kernel (κ := κ)).measurable
  set d : α → β → ℝ≥0∞ := fun s t ↦ ENNReal.ofReal (Real.exp (a t - Real.log (Z s)))
  have hd : Measurable (Function.uncurry d) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((ha.comp measurable_snd).sub ((Real.measurable_log.comp hZm).comp measurable_fst)))
  set K := κ.withDensity d
  have : IsSFiniteKernel K := Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ ENNReal.ofReal_ne_top
  have : IsSFiniteKernel (κ.withDensity ρ) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ ENNReal.ofReal_ne_top
  set m : α → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (Real.exp (b s) * Z s)
  have hm : Measurable m :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hb).mul hZm)
  have hm' : Measurable (Function.uncurry fun (s : α) (_ : β) ↦ m s) := hm.comp measurable_fst
  have : IsSFiniteKernel (K.withDensity fun s _ ↦ m s) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ ENNReal.ofReal_ne_top
  -- Step 1: the tilt is `μ` composed with the tilted kernel.
  have h1 : Q' = μ ⊗ₘ κ.withDensity ρ := (Measure.compProd_withDensity hρ).symm
  -- Fibrewise integrability.
  have hint : ∀ᵐ s ∂μ, Integrable (fun t ↦ Real.exp (a t)) (κ s) := by
    have hlt : ∫⁻ s, ∫⁻ t, ρ s t ∂κ s ∂μ < ∞ := by
      rw [← Measure.lintegral_compProd (f := fun p : α × β ↦ ρ p.1 p.2) hρ]
      have := measure_lt_top Q' univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    filter_upwards [ae_lt_top' (hρ.lintegral_kernel_prod_right'.aemeasurable) hlt.ne] with s hs
    refine ⟨(Real.measurable_exp.comp ha).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
    have heq : (fun t ↦ ENNReal.ofReal (Real.exp (a t))) =
        fun t ↦ ENNReal.ofReal (Real.exp (-b s)) * ρ s t := by
      funext t
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    rw [heq, lintegral_const_mul _ (show Measurable (ρ s) from
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ha.add measurable_const)))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs
  have hZpos : ∀ᵐ s ∂μ, 0 < Z s := hint.mono fun s hs ↦ integral_exp_pos hs
  -- Step 2: the tilted kernel is the normalized tilt times the fibre mass.
  have h2 : ∀ᵐ s ∂μ, κ.withDensity ρ s = K.withDensity (fun s _ ↦ m s) s := by
    filter_upwards [hZpos] with s hs
    rw [Kernel.withDensity_apply _ hρ, Kernel.withDensity_apply _ hm',
      Kernel.withDensity_apply _ hd, ← withDensity_mul _
        (show Measurable (d s) from
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ha.sub measurable_const)))
          measurable_const]
    congr 1
    funext t
    simp only [Pi.mul_apply, ρ, d, m]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sub, Real.exp_log hs, Real.exp_add]
    congr 1
    field_simp
  -- Step 3: move the fibre mass to the first marginal.
  have h3 : μ ⊗ₘ K.withDensity (fun s _ ↦ m s) = (μ.withDensity m) ⊗ₘ K := by
    rw [Measure.compProd_withDensity hm', Measure.withDensity_compProd hm]
  have hQ' : Q' = μ.withDensity m ⊗ₘ K := h1.trans ((Measure.compProd_congr h2).trans h3)
  -- Step 4: the normalized tilt is Markov almost everywhere, so the first marginal is right.
  have hK1 : ∀ᵐ s ∂μ, K s univ = 1 := by
    filter_upwards [hint, hZpos] with s hs hZ
    rw [Kernel.withDensity_apply' _ hd, Measure.restrict_univ]
    have hfun : (fun t ↦ Real.exp (a t - Real.log (Z s))) = fun t ↦ Real.exp (a t) / Z s := by
      funext t; rw [Real.exp_sub, Real.exp_log hZ]
    simp only [d]
    rw [← ofReal_integral_eq_lintegral_ofReal (by rw [hfun]; exact hs.div_const _)
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), hfun, integral_div, div_self hZ.ne',
      ENNReal.ofReal_one]
  have h4 : (μ.withDensity m ⊗ₘ K).fst = μ.withDensity m := by
    ext B hB
    have hae : ∀ᵐ s ∂(μ.withDensity m), K s univ = 1 := withDensity_absolutelyContinuous _ _ hK1
    rw [Measure.fst_apply hB, ← prod_univ, Measure.compProd_apply_prod hB MeasurableSet.univ,
      lintegral_congr_ae (ae_restrict_of_ae hae), lintegral_one, Measure.restrict_apply
      MeasurableSet.univ, univ_inter]
  calc Q' = μ.withDensity m ⊗ₘ K := hQ'
    _ = (μ.withDensity m ⊗ₘ K).fst ⊗ₘ K := by rw [h4]
    _ = Q'.fst ⊗ₘ K := by rw [← hQ']

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- Tilting a kernel by `exp (-η₁ · t)` and then forming the conditional exponential kernel at
`η` is the conditional exponential kernel of the untilted kernel at `η - η₁`. -/
theorem conditional_exponential_kernel_with_density_exp_neg [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] (κ : Kernel F E) [IsSFiniteKernel κ] (η₁ η : E) :
    have : IsSFiniteKernel (κ.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₁ t))) :=
      Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ ENNReal.ofReal_ne_top
    conditionalExponentialKernel
        (κ.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₁ t))) η =
      κ.withDensity (fun s t ↦ ENNReal.ofReal
        (Real.exp (inner ℝ (η - η₁) t -
          Real.log (∫ t', Real.exp (inner ℝ (η - η₁) t') ∂κ s)))) := by
  intro hκ
  have hin : ∀ ζ : E, Measurable fun t : E ↦ inner ℝ ζ t := fun ζ ↦
    (continuous_const.inner continuous_id).measurable
  set w : F → E → ℝ≥0∞ := fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₁ t))
  have hw : Measurable (Function.uncurry w) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hin η₁).comp measurable_snd).neg)
  set κw := κ.withDensity w
  have hZ : ∀ ζ : E, ∀ (L : Kernel F E), IsSFiniteKernel L →
      Measurable fun s ↦ ∫ t', Real.exp (inner ℝ ζ t') ∂L s := fun ζ L _ ↦
    ((Real.measurable_exp.comp (hin ζ)).stronglyMeasurable.integral_kernel (κ := L)).measurable
  have hd : ∀ ζ : E, ∀ (L : Kernel F E), IsSFiniteKernel L →
      Measurable (Function.uncurry fun s t ↦ ENNReal.ofReal
        (Real.exp (inner ℝ ζ t - Real.log (∫ t', Real.exp (inner ℝ ζ t') ∂L s)))) :=
    fun ζ L hL ↦ ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hin ζ).comp measurable_snd).sub ((Real.measurable_log.comp (hZ ζ L hL)).comp
        measurable_fst)))
  have hint : ∀ s, ∫ t', Real.exp (inner ℝ η t') ∂κw s =
      ∫ t', Real.exp (inner ℝ (η - η₁) t') ∂κ s := by
    intro s
    rw [Kernel.withDensity_apply _ hw, integral_with_density_of_real (h := fun t ↦
      Real.exp (-inner ℝ η₁ t)) _ (Real.measurable_exp.comp (hin η₁).neg)
      (fun _ ↦ (Real.exp_pos _).le)]
    congr 1
    funext t
    rw [← Real.exp_add, inner_sub_left]
    ring_nf
  ext1 s
  rw [conditionalExponentialKernel, Kernel.withDensity_apply _ (hd η κw hκ),
    Kernel.withDensity_apply _ (hd (η - η₁) κ inferInstance)]
  simp only [hint]
  rw [Kernel.withDensity_apply _ hw, ← withDensity_mul (f := w s) (g := fun t ↦ ENNReal.ofReal
      (Real.exp (inner ℝ η t - Real.log (∫ t', Real.exp (inner ℝ (η - η₁) t') ∂κ s)))) _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hin η₁).neg))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hin η).sub measurable_const)))]
  congr 1
  funext t
  simp only [Pi.mul_apply, w]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, inner_sub_left]
  ring_nf

/-- The split exponential law has finite total mass where its density is integrable. -/
theorem is_finite_measure_split_exponential_family_measure (ν : Measure X) (T : X → E) (S : X → F)
    (η : E) (ζ : F) (h : Integrable (fun x ↦ Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x))) ν) :
    IsFiniteMeasure (splitExponentialFamilyMeasure ν T S η ζ) := by
  refine ⟨?_⟩
  rw [splitExponentialFamilyMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h' := h.mul_const (Real.exp (-splitLogPartition ν T S η ζ))
  have heq : (fun x ↦ Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x) - splitLogPartition ν T S η ζ))
      = fun x ↦ Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x)) *
        Real.exp (-splitLogPartition ν T S η ζ) := by
    funext x; rw [← Real.exp_add, sub_eq_add_neg]
  convert h'.lintegral_lt_top using 4 with x
  exact congrFun heq x

/-- Two split exponential laws differ by an exponential tilt in `(S, T)`; here `c` is the
difference of the two log partition functions. -/
theorem split_exponential_family_measure_eq_with_density [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure X) {T : X → E} {S : X → F}
    (hT : Measurable T) (hS : Measurable S) (η η₁ : E) (ζ ζ₁ : F) {c : ℝ}
    (hc : c = splitLogPartition ν T S η ζ - splitLogPartition ν T S η₁ ζ₁) :
    splitExponentialFamilyMeasure ν T S η ζ =
      (splitExponentialFamilyMeasure ν T S η₁ ζ₁).withDensity ((fun p : F × E ↦ ENNReal.ofReal
        (Real.exp (inner ℝ (η - η₁) p.2 + (inner ℝ (ζ - ζ₁) p.1 - c)))) ∘
          fun x ↦ (S x, T x)) := by
  subst hc
  have hinT : ∀ y : E, Measurable fun x ↦ inner ℝ y (T x) := fun y ↦
    (continuous_const.inner continuous_id).measurable.comp hT
  have hinS : ∀ y : F, Measurable fun x ↦ inner ℝ y (S x) := fun y ↦
    (continuous_const.inner continuous_id).measurable.comp hS
  unfold splitExponentialFamilyMeasure
  rw [← withDensity_mul]
  · congr 1
    funext x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, inner_sub_left, inner_sub_left]
    ring_nf
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hinT η₁).add (hinS ζ₁)).sub measurable_const))
  · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((((continuous_const.inner continuous_id).measurable.comp measurable_snd).add
        (((continuous_const.inner continuous_id).measurable.comp measurable_fst).sub
          measurable_const)))) |>.comp (hS.prodMk hT)

/-- GAPS 101.43: conditional exponential families. For a natural exponential family with natural
statistic `(T, S)` with values in Euclidean spaces, there is one s-finite kernel `s ↦ ν_s`, free of
the parameter, such that at every natural parameter `(η, ζ)` the joint law of `(S, T)` is the law
of `S` composed with the kernel `s ↦ exp(η·t - A_s(η)) ν_s(dt)`; that is, the conditional law of
`T` given `S = s` has this density for almost every `s`, and it is free of `ζ`. -/
theorem exists_kernel_conditional_exponential_family {k l : ℕ} (ν : Measure X)
    (T : X → EuclideanSpace ℝ (Fin k)) (S : X → EuclideanSpace ℝ (Fin l))
    (hT : Measurable T) (hS : Measurable S) :
    ∃ κ : Kernel (EuclideanSpace ℝ (Fin l)) (EuclideanSpace ℝ (Fin k)), ∃ _ : IsSFiniteKernel κ,
      ∀ η ζ, Integrable (fun x ↦ Real.exp (inner ℝ η (T x) + inner ℝ ζ (S x))) ν →
        (splitExponentialFamilyMeasure ν T S η ζ).map (fun x ↦ (S x, T x)) =
          (splitExponentialFamilyMeasure ν T S η ζ).map S ⊗ₘ
            conditionalExponentialKernel κ η := by
  by_cases hex : ∃ η₁ ζ₁, Integrable (fun x ↦ Real.exp (inner ℝ η₁ (T x) + inner ℝ ζ₁ (S x))) ν
  swap
  · exact ⟨0, inferInstance, fun η ζ h ↦ absurd ⟨η, ζ, h⟩ hex⟩
  obtain ⟨η₁, ζ₁, h₁⟩ := hex
  have hST : Measurable fun x ↦ (S x, T x) := hS.prodMk hT
  set P₁ := splitExponentialFamilyMeasure ν T S η₁ ζ₁
  have := is_finite_measure_split_exponential_family_measure ν T S η₁ ζ₁ h₁
  set Q := P₁.map fun x ↦ (S x, T x)
  set κ₁ := Q.condKernel
  have hκ : IsSFiniteKernel
      (κ₁.withDensity fun _ t ↦ ENNReal.ofReal (Real.exp (-inner ℝ η₁ t))) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦ ENNReal.ofReal_ne_top
  refine ⟨_, hκ, fun η ζ hint ↦ ?_⟩
  rw [conditional_exponential_kernel_with_density_exp_neg κ₁ η₁ η]
  obtain ⟨c, hc⟩ : ∃ c, c = splitLogPartition ν T S η ζ - splitLogPartition ν T S η₁ ζ₁ :=
    ⟨_, rfl⟩
  have ha : Measurable fun t : EuclideanSpace ℝ (Fin k) ↦ inner ℝ (η - η₁) t :=
    (continuous_const.inner continuous_id).measurable
  have hb : Measurable fun s : EuclideanSpace ℝ (Fin l) ↦ inner ℝ (ζ - ζ₁) s - c :=
    (continuous_const.inner continuous_id).measurable.sub measurable_const
  have hk : Measurable fun p : EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin k) ↦
      ENNReal.ofReal (Real.exp (inner ℝ (η - η₁) p.2 + (inner ℝ (ζ - ζ₁) p.1 - c))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((ha.comp measurable_snd).add (hb.comp measurable_fst)))
  have hPmap : (splitExponentialFamilyMeasure ν T S η ζ).map (fun x ↦ (S x, T x)) =
      Q.withDensity fun p ↦
        ENNReal.ofReal (Real.exp (inner ℝ (η - η₁) p.2 + (inner ℝ (ζ - ζ₁) p.1 - c))) := by
    rw [split_exponential_family_measure_eq_with_density ν hT hS η η₁ ζ ζ₁ hc,
      map_with_density_comp P₁ hST hk]
  have hQ : Q = Q.fst ⊗ₘ κ₁ := (Q.disintegrate Q.condKernel).symm
  have := is_finite_measure_split_exponential_family_measure ν T S η ζ hint
  have hfin : IsFiniteMeasure ((Q.fst ⊗ₘ κ₁).withDensity fun p ↦
      ENNReal.ofReal (Real.exp (inner ℝ (η - η₁) p.2 + (inner ℝ (ζ - ζ₁) p.1 - c)))) := by
    rw [← hQ, ← hPmap]
    infer_instance
  have key := with_density_exp_comp_prod_eq_fst_comp_prod Q.fst κ₁ ha hb hfin
  rw [← hQ, ← hPmap, Measure.fst_map_prodMk hS hT] at key
  exact key

/-- Minimality of a split natural statistic `(T, S)` with real `T`: no nontrivial affine function
`a T + b·S` is almost everywhere constant under the base measure. -/
def IsMinimalSplitStatistic {l : ℕ} (ν : Measure X) (T : X → ℝ)
    (S : X → EuclideanSpace ℝ (Fin l)) : Prop :=
  ∀ (a : ℝ) (b : EuclideanSpace ℝ (Fin l)), (a, b) ≠ 0 → ∀ c : ℝ,
    ¬ (∀ᵐ x ∂ν, a * T x + inner ℝ b (S x) = c)

/-- GAPS 101.46, two-sided part: conditional tests with a nuisance parameter. In a minimal
exponential family with real natural statistic `T`, nuisance statistic `S`, and natural parameter
`(η, ζ)` ranging over an open convex set `U` on which the family is defined and which meets the
hyperplane `η = η₀`, a test that rejects for values of `T` outside the conditional interval
`[c₁(S), c₂(S)]`, accepts inside it, and has conditional size `α` and conditional first-moment
constraint `E[Tφ | S] = α E[T | S]` at one point of the hyperplane, is UMPU of level `α` for
`η = η₀` against `η ≠ η₀`. The randomization at the conditional critical points is
unrestricted. -/
theorem is_uniformly_most_powerful_unbiased_test_conditional_two_sided {l : ℕ} (ν : Measure X)
    (T : X → ℝ) (S : X → EuclideanSpace ℝ (Fin l)) (hT : Measurable T) (hS : Measurable S)
    (hmin : IsMinimalSplitStatistic ν T S)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin l))) (hU : IsOpen U) (hc : Convex ℝ U)
    (hint : ∀ θ ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ θ.1 (T x) + inner ℝ θ.2 (S x))) ν)
    (η₀ : ℝ) (θ₀ : U) (hθ₀ : θ₀.val.1 = η₀) (α : ℝ) (hα : α ∈ Ioo 0 1)
    (c₁ c₂ : EuclideanSpace ℝ (Fin l) → ℝ) (hcrit : ∀ s, c₁ s ≤ c₂ s)
    (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (htail : ∀ x, (T x < c₁ (S x) ∨ c₂ (S x) < T x → φ x = 1) ∧
      (c₁ (S x) < T x ∧ T x < c₂ (S x) → φ x = 0)) :
    let P := fun θ : U ↦ splitExponentialFamilyMeasure ν T S θ.val.1 θ.val.2;
    (P θ₀)[φ | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun _ ↦ α) →
    (P θ₀)[fun x ↦ T x * φ x | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun x ↦ α * (P θ₀)[T | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] x) →
    IsUniformlyMostPowerfulUnbiasedTest P {θ | θ.val.1 = η₀} {θ | θ.val.1 ≠ η₀} α φ := by
  sorry

/-- GAPS 101.46, one-sided part: in the setting of
`is_uniformly_most_powerful_unbiased_test_conditional_two_sided`, a test that rejects for
`T > c(S)`, accepts for `T < c(S)`, and has conditional size `α` at one point of the hyperplane
`η = η₀` is UMPU of level `α` for `η ≤ η₀` against `η > η₀`. -/
theorem is_uniformly_most_powerful_unbiased_test_conditional_one_sided {l : ℕ} (ν : Measure X)
    (T : X → ℝ) (S : X → EuclideanSpace ℝ (Fin l)) (hT : Measurable T) (hS : Measurable S)
    (hmin : IsMinimalSplitStatistic ν T S)
    (U : Set (ℝ × EuclideanSpace ℝ (Fin l))) (hU : IsOpen U) (hc : Convex ℝ U)
    (hint : ∀ θ ∈ U, Integrable (fun x ↦ Real.exp (inner ℝ θ.1 (T x) + inner ℝ θ.2 (S x))) ν)
    (η₀ : ℝ) (θ₀ : U) (hθ₀ : θ₀.val.1 = η₀) (α : ℝ) (hα : α ∈ Ioo 0 1)
    (c : EuclideanSpace ℝ (Fin l) → ℝ) (φ : X → ℝ) (hφ : IsStatisticalTest φ)
    (htail : ∀ x, (c (S x) < T x → φ x = 1) ∧ (T x < c (S x) → φ x = 0)) :
    let P := fun θ : U ↦ splitExponentialFamilyMeasure ν T S θ.val.1 θ.val.2;
    (P θ₀)[φ | (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin l))).comap S] =ᵐ[P θ₀] (fun _ ↦ α) →
    IsUniformlyMostPowerfulUnbiasedTest P {θ | θ.val.1 ≤ η₀} {θ | η₀ < θ.val.1} α φ := by
  sorry

end CKSD
