module

public import CKSD.Inference.Moments
public import CKSD.Inference.Sufficiency
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Inference: Estimation

Sources: `GAPS.md`, `SYNOPSIS101.md`, and `STRUCTURE101.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {Θ X S V : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace V]

/-- GAPS 101.7: one parameter-independent Rao–Blackwell rule, with convex risk reduction at each
parameter value, so the loss may depend on the parameter. The rule is `s ↦ ∫ δ dK(s)` for the
kernel `K` witnessing sufficiency. -/
theorem exists_rao_blackwell_estimator (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (hT : IsSufficientStatistic P T) (δ : X → ℝ) (hδ : Measurable δ)
    (hint : ∀ θ, Integrable δ (P θ)) :
    ∃ r : S → ℝ, Measurable r ∧ ∀ θ,
      Integrable (r ∘ T) (P θ) ∧ (∫ x, r (T x) ∂P θ) = ∫ x, δ x ∂P θ ∧
      ∀ L : ℝ → ℝ, ConvexOn ℝ univ L →
        Integrable (fun x ↦ L (δ x)) (P θ) →
        Integrable (fun x ↦ L (r (T x))) (P θ) ∧
        (∫ x, L (r (T x)) ∂P θ) ≤ ∫ x, L (δ x) ∂P θ := by
  obtain ⟨hTm, K, hKm, hK⟩ := hT
  let r : S → ℝ := fun s ↦ ∫ y, δ y ∂K s
  have hr : Measurable r := (hδ.stronglyMeasurable.integral_kernel (κ := K)).measurable
  refine ⟨r, hr, fun θ ↦ ?_⟩
  have := hP θ
  have hcomp := comp_map_eq_of_map_prodMk_eq_compProd (P θ) hTm K (hK θ)
  -- integrability of kernel integrals of a `P θ`-integrable function
  have hkint (f : X → ℝ) (hfm : Measurable f) (hf : Integrable f (P θ)) :
      Integrable (fun s ↦ ∫ y, f y ∂K s) ((P θ).map T) := by
    rw [← hcomp] at hf
    refine (Measure.integrable_integral_norm_of_integrable_comp hf).mono' ?_
      (ae_of_all _ fun s ↦ norm_integral_le_integral_norm _)
    exact (hfm.stronglyMeasurable.integral_kernel (κ := K)).aestronglyMeasurable
  have hδK : ∀ᵐ s ∂(P θ).map T, Integrable δ (K s) :=
    Measure.ae_integrable_of_integrable_comp (hcomp.symm ▸ hint θ)
  have hrν := hkint δ hδ (hint θ)
  have hmapint (g : S → ℝ) (hg : Measurable g) :
      (∫ x, g (T x) ∂P θ) = ∫ s, g s ∂(P θ).map T :=
    (integral_map (f := g) hTm.aemeasurable hg.aestronglyMeasurable).symm
  have hmix (f : X → ℝ) (hf : Integrable f (P θ)) :
      (∫ s, ∫ y, f y ∂K s ∂(P θ).map T) = ∫ x, f x ∂P θ := by
    rw [← integral_comp_eq_integral_integral K ((P θ).map T) f (hcomp.symm ▸ hf), hcomp]
  refine ⟨(integrable_map_measure hr.aestronglyMeasurable hTm.aemeasurable).1 hrν,
    by rw [hmapint r hr, hmix δ (hint θ)], fun L hL hLi ↦ ?_⟩
  have hLc : Continuous L := continuousOn_univ.1 (hL.continuousOn isOpen_univ)
  have hLδ : Measurable (fun x ↦ L (δ x)) := hLc.measurable.comp hδ
  have hLK : ∀ᵐ s ∂(P θ).map T, Integrable (fun x ↦ L (δ x)) (K s) :=
    Measure.ae_integrable_of_integrable_comp (hcomp.symm ▸ hLi)
  have hJ : ∀ᵐ s ∂(P θ).map T, L (r s) ≤ ∫ y, L (δ y) ∂K s := by
    filter_upwards [hδK, hLK] with s h1 h2
    exact hL.map_integral_le (hL.continuousOn isOpen_univ) isClosed_univ
      (ae_of_all _ fun _ ↦ mem_univ _) h1 h2
  obtain ⟨c, hc0, hcL⟩ := exists_sub_mul_abs_le_of_convexOn hL
  have hu := hkint (fun x ↦ L (δ x)) hLδ hLi
  have hLr : Integrable (fun s ↦ L (r s)) ((P θ).map T) := by
    refine Integrable.mono' ((hu.norm.add (integrable_const |L 0|)).add (hrν.norm.const_mul c))
      (hLc.measurable.comp hr).aestronglyMeasurable ?_
    filter_upwards [hJ] with s hs
    have h1 := hcL (r s)
    have h2 := neg_abs_le (L 0)
    have h3 := le_abs_self (∫ y, L (δ y) ∂K s)
    have h4 := abs_nonneg (∫ y, L (δ y) ∂K s)
    have h5 : 0 ≤ c * |r s| := mul_nonneg hc0 (abs_nonneg _)
    have h6 := abs_nonneg (L 0)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    simp only [r] at hs h1 h5 ⊢
    constructor <;> linarith
  refine ⟨(integrable_map_measure (f := T) (g := fun s ↦ L (r s))
    (hLc.measurable.comp hr).aestronglyMeasurable hTm.aemeasurable).1 hLr, ?_⟩
  rw [hmapint (fun s ↦ L (r s)) (hLc.measurable.comp hr), ← hmix _ hLi]
  exact integral_mono_ae hLr hu hJ

/-- GAPS 101.8, uniqueness part: unbiased functions of a complete statistic agree. -/
theorem ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator
    (P : Θ → Measure X) (T : X → S) (hc : IsCompleteStatistic P T)
    (a b : S → ℝ) (ha : Measurable a) (hb : Measurable b) (g : Θ → ℝ)
    (hua : IsUnbiasedEstimator P (a ∘ T) g) (hub : IsUnbiasedEstimator P (b ∘ T) g) :
    ∀ θ, ∀ᵐ x ∂P θ, a (T x) = b (T x) := by
  have hz := hc (fun s ↦ a s - b s) (ha.sub hb)
  apply fun θ ↦ (hz ?_ θ).mono (fun _ h ↦ sub_eq_zero.mp h)
  intro θ
  refine ⟨(hua.2 θ).1.sub (hub.2 θ).1, ?_⟩
  calc
    (∫ x, a (T x) - b (T x) ∂P θ) =
        (∫ x, (a ∘ T) x ∂P θ) - ∫ x, (b ∘ T) x ∂P θ :=
      integral_sub (hua.2 θ).1 (hub.2 θ).1
    _ = 0 := by rw [(hua.2 θ).2, (hub.2 θ).2, sub_self]

/-- GAPS 101.9: Basu's theorem. -/
theorem indepFun_of_isSufficientStatistic_of_isBoundedlyCompleteStatistic
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (T : X → S) (A : X → V) (hA : Measurable A)
    (hs : IsSufficientStatistic P T) (hc : IsBoundedlyCompleteStatistic P T)
    (ha : ∀ θ θ', (P θ).map A = (P θ').map A) (θ : Θ) :
    IndepFun T A (P θ) := by
  obtain ⟨hT, K, hKm, hK⟩ := hs
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro C B hC hB
  have := hP θ
  let φ : X → ℝ := fun x ↦ B.indicator 1 (A x)
  have hφ : Measurable φ := (measurable_one.indicator hB).comp hA
  have hφb : ∀ x, |φ x| ≤ 1 := fun x ↦ abs_indicator_one_le_one B (A x)
  have hint (θ' : Θ) : (∫ x, φ x ∂P θ') = (P θ').real (A ⁻¹' B) := by
    rw [← integral_indicator_one (hA hB)]
    rfl
  have hconst (θ' : Θ) : (∫ x, φ x ∂P θ') = (P θ).real (A ⁻¹' B) := by
    rw [hint, measureReal_def, measureReal_def, ← Measure.map_apply hA hB,
      ← Measure.map_apply hA hB, ha θ' θ]
  have hzero := ae_integral_kernel_eq_of_isBoundedlyCompleteStatistic P hP hT hc K hK hφ hφb
    _ hconst θ
  have hkey := integral_indicator_comp_mul_eq (P θ) hT K (hK θ) hC hφ hφb
  have hleft : (∫ x, C.indicator 1 (T x) * φ x ∂P θ) = (P θ).real (T ⁻¹' C ∩ A ⁻¹' B) := by
    rw [← integral_indicator_one ((hT hC).inter (hA hB))]
    congr 1
    funext x
    by_cases h1 : T x ∈ C <;> by_cases h2 : A x ∈ B <;> simp [φ, indicator, h1, h2]
  have hright : (∫ x, C.indicator 1 (T x) * ∫ y, φ y ∂K (T x) ∂P θ) =
      (P θ).real (T ⁻¹' C) * (P θ).real (A ⁻¹' B) := by
    rw [integral_congr_ae (hzero.mono fun x hx ↦ by rw [hx]), integral_mul_const,
      ← integral_indicator_one (hT hC)]
    rfl
  rw [hleft, hright] at hkey
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
  exact hkey

/-- GAPS 101.10, scalar score-moment form of the information inequality.
The derivative-under-integral assumptions give the displayed cross-moment identity. -/
theorem sq_div_information_le_variance (P : Measure X) [IsProbabilityMeasure P]
    (W score : X → ℝ) (hW : MemLp W 2 P) (hs : MemLp score 2 P)
    (_hs0 : (∫ x, score x ∂P) = 0) (g' : ℝ)
    (hcross : (∫ x, (W x - ∫ y, W y ∂P) * score x ∂P) = g')
    (hI : 0 < ∫ x, score x ^ 2 ∂P) :
    g' ^ 2 / (∫ x, score x ^ 2 ∂P) ≤ variance P W := by
  let c := ∫ x, W x ∂P
  let a := g' / (∫ x, score x ^ 2 ∂P)
  have hWc : MemLp (fun x ↦ W x - c) 2 P := hW.sub (memLp_const c)
  have hprod := hWc.integrable_mul hs
  have hnonneg : 0 ≤ ∫ x, ((W x - c) - a * score x) ^ 2 ∂P :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hexpand : (∫ x, ((W x - c) - a * score x) ^ 2 ∂P) =
      variance P W - 2 * a * g' + a ^ 2 * (∫ x, score x ^ 2 ∂P) := by
    have heq : (fun x ↦ ((W x - c) - a * score x) ^ 2) =
        (fun x ↦ ((W x - c) ^ 2 - (2 * a) * ((W x - c) * score x)) +
          a ^ 2 * score x ^ 2) := by funext x; ring
    have hlin : Integrable (fun x ↦ (2 * a) * ((W x - c) * score x)) P :=
      hprod.const_mul (2 * a)
    have hsq : Integrable (fun x ↦ a ^ 2 * score x ^ 2) P := hs.integrable_sq.const_mul _
    have hadd := integral_add (hWc.integrable_sq.sub hlin) hsq
    have hsub := integral_sub hWc.integrable_sq hlin
    simp only [Pi.sub_apply] at hadd hsub
    rw [heq, hadd, hsub]
    simp only [integral_const_mul]
    rw [show (∫ x, (W x - c) * score x ∂P) = g' from hcross]
    rfl
  rw [hexpand] at hnonneg
  have ha : a * (∫ x, score x ^ 2 ∂P) = g' := div_mul_cancel₀ _ hI.ne'
  have ha2 : a ^ 2 * (∫ x, score x ^ 2 ∂P) = a * g' := by
    calc
      _ = a * (a * (∫ x, score x ^ 2 ∂P)) := by ring
      _ = a * g' := by rw [ha]
  calc
    g' ^ 2 / (∫ x, score x ^ 2 ∂P) = a * g' := by dsimp [a]; ring
    _ ≤ variance P W := by rw [ha2] at hnonneg; linarith

/-- GAPS 101.12: covariance characterization of uniformly minimum variance unbiasedness. -/
theorem is_minimum_variance_unbiased_iff_covariance_eq_zero
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (W : X → ℝ) (g : Θ → ℝ) (hW : IsUnbiasedEstimator P W g)
    (hW2 : ∀ θ, MemLp W 2 (P θ)) :
    (∀ W', IsUnbiasedEstimator P W' g → (∀ θ, MemLp W' 2 (P θ)) →
      ∀ θ, variance (P θ) W ≤ variance (P θ) W') ↔
    (∀ U, IsUnbiasedEstimator P U (fun _ ↦ 0) → (∀ θ, MemLp U 2 (P θ)) →
      ∀ θ, covariance (P θ) W U = 0) := by
  constructor
  · intro hmin U hU hU2 θ
    have := hP θ
    have hquad (a : ℝ) :
        0 ≤ ProbabilityTheory.variance U (P θ) * (a * a) +
          (2 * covariance (P θ) W U) * a + 0 := by
      have hWa : IsUnbiasedEstimator P (fun x ↦ W x + a * U x) g := by
        refine ⟨hW.1.add (measurable_const.mul hU.1), fun t ↦ ?_⟩
        refine ⟨(hW.2 t).1.add ((hU.2 t).1.const_mul a), ?_⟩
        rw [integral_add (hW.2 t).1 ((hU.2 t).1.const_mul a), integral_const_mul,
          (hW.2 t).2, (hU.2 t).2, mul_zero, add_zero]
      have hWa2 (t : Θ) : MemLp (fun x ↦ W x + a * U x) 2 (P t) :=
        (hW2 t).add ((hU2 t).const_mul a)
      have h := hmin _ hWa hWa2 θ
      rw [variance_eq_mathlib _ _ (hW2 θ).aemeasurable,
        variance_eq_mathlib _ _ (hWa2 θ).aemeasurable,
        ProbabilityTheory.variance_fun_add (hW2 θ) ((hU2 θ).const_mul a),
        ProbabilityTheory.covariance_const_mul_right,
        ProbabilityTheory.variance_const_mul] at h
      nlinarith
    have hd := discrim_le_zero hquad
    simp only [discrim, mul_zero, sub_zero] at hd
    nlinarith [sq_nonneg (covariance (P θ) W U)]
  · intro hcov W' hW' hW'2 θ
    have := hP θ
    let U : X → ℝ := fun x ↦ W' x - W x
    have hU : IsUnbiasedEstimator P U (fun _ ↦ 0) := by
      refine ⟨hW'.1.sub hW.1, fun t ↦ ?_⟩
      refine ⟨(hW'.2 t).1.sub (hW.2 t).1, ?_⟩
      dsimp [U]
      rw [integral_sub (hW'.2 t).1 (hW.2 t).1, (hW'.2 t).2, (hW.2 t).2, sub_self]
    have hU2 (t : Θ) : MemLp U 2 (P t) := (hW'2 t).sub (hW2 t)
    have hzero := hcov U hU hU2 θ
    change ProbabilityTheory.covariance W U (P θ) = 0 at hzero
    have hadd := ProbabilityTheory.variance_fun_add (hW2 θ) (hU2 θ)
    have hid : (fun x ↦ W x + U x) = W' := by
      funext x
      dsimp [U]
      ring
    rw [hid, hzero, mul_zero, add_zero] at hadd
    rw [variance_eq_mathlib _ _ (hW2 θ).aemeasurable,
      variance_eq_mathlib _ _ (hW'2 θ).aemeasurable, hadd]
    exact le_add_of_nonneg_right (ProbabilityTheory.variance_nonneg U (P θ))


end CKSD
