module

public import CKSD.Inference.Sufficiency

/-!
# Inference: Decision

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

/-- GAPS 101.32: finite statistical games have a saddle point in rules and priors. -/
theorem exists_statistical_game_saddle_point [Fintype Θ] [Nonempty Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ)) (L : Θ → A → ℝ) :
    ∃ δ : RandomizedDecisionRule X A, ∃ π : ProbabilityMeasure Θ,
      (∀ δ', (∫ θ, risk P L δ θ ∂(π : Measure Θ)) ≤
        ∫ θ, risk P L δ' θ ∂(π : Measure Θ)) ∧
      ∀ θ, risk P L δ θ ≤ ∫ θ', risk P L δ θ' ∂(π : Measure Θ) := by
  sorry

/-- GAPS 101.37, the closed-convex-risk-set form of the finite complete-class theorem. -/
theorem exists_admissible_bayes_risk_le_of_closed_convex {d : ℕ} (hd : 0 < d) (C : Set (Fin d → ℝ))
    (hc : Convex ℝ C) (hclosed : IsClosed C) (hb : ∃ b : Fin d → ℝ, ∀ x ∈ C, ∀ i, b i ≤ x i) :
    ∀ x ∈ C, ∃ y ∈ C, (∀ i, y i ≤ x i) ∧
      (¬ ∃ z ∈ C, (∀ i, z i ≤ y i) ∧ ∃ i, z i < y i) ∧
      ∃ w : Fin d → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        ∀ z ∈ C, (∑ i, w i * y i) ≤ ∑ i, w i * z i := by
  intro x hx
  obtain ⟨b, hb⟩ := hb
  -- a minimizer of the coordinate sum below `x`
  have hDc : IsCompact (C ∩ Iic x) :=
    (isCompact_Icc (a := b) (b := x)).of_isClosed_subset (hclosed.inter isClosed_Iic)
      fun z hz ↦ ⟨fun i ↦ hb z hz.1 i, hz.2⟩
  obtain ⟨y, ⟨hyC, hyx⟩, hymin⟩ := hDc.exists_isMinOn ⟨x, hx, mem_Iic.2 le_rfl⟩
    (f := fun z : Fin d → ℝ ↦ ∑ i, z i) (by fun_prop)
  have hadm : ¬ ∃ z ∈ C, (∀ i, z i ≤ y i) ∧ ∃ i, z i < y i := by
    rintro ⟨z, hzC, hzy, j, hj⟩
    have hle := hymin ⟨hzC, mem_Iic.2 (le_trans (fun i ↦ hzy i) hyx)⟩
    have hlt : ∑ i, z i < ∑ i, y i :=
      Finset.sum_lt_sum (fun i _ ↦ hzy i) ⟨j, Finset.mem_univ _, hj⟩
    exact absurd hle (not_le.2 hlt)
  refine ⟨y, hyC, fun i ↦ hyx i, hadm, ?_⟩
  -- separation of the open lower orthant at `y` from `C + ℝ^d_{≥0}`
  let O : Set (Fin d → ℝ) := univ.pi fun i ↦ Iio (y i)
  let E : Set (Fin d → ℝ) := {v | ∃ c ∈ C, ∀ i, c i ≤ v i}
  have hOo : IsOpen O := isOpen_set_pi finite_univ fun i _ ↦ isOpen_Iio
  have hOc : Convex ℝ O := convex_pi fun i _ ↦ convex_Iio (y i)
  have hEc : Convex ℝ E := by
    rintro v₁ ⟨c₁, hc₁, h₁⟩ v₂ ⟨c₂, hc₂, h₂⟩ a b' ha hb' hab
    refine ⟨a • c₁ + b' • c₂, hc hc₁ hc₂ ha hb' hab, fun i ↦ ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (h₁ i) ha, mul_le_mul_of_nonneg_left (h₂ i) hb']
  have hdisj : Disjoint O E := by
    rw [Set.disjoint_left]
    rintro v hvO ⟨c, hcC, hcv⟩
    have hvO' : ∀ i, v i < y i := fun i ↦ hvO i (mem_univ i)
    exact hadm ⟨c, hcC, fun i ↦ (hcv i).trans (hvO' i).le,
      ⟨⟨0, hd⟩, (hcv _).trans_lt (hvO' _)⟩⟩
  obtain ⟨f, u, hfO, hfE⟩ := geometric_hahn_banach_open hOc hOo hEc hdisj
  let e : Fin d → Fin d → ℝ := fun i j ↦ if i = j then 1 else 0
  let w' : Fin d → ℝ := fun i ↦ f (e i)
  have hexp (z : Fin d → ℝ) : f z = ∑ i, w' i * z i := by
    rw [show f z = (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) z from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul, w', e, mul_comm]
    rfl
  have hyE : y ∈ E := ⟨y, hyC, fun _ ↦ le_rfl⟩
  have hw' : ∀ i, 0 ≤ w' i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    let t := (|f y - u| + 1) / (-w' i)
    have ht : 0 < t := div_pos (by positivity) (by linarith)
    have hmem : y + t • e i ∈ E := ⟨y, hyC, fun j ↦ by
      by_cases h : i = j <;> simp [e, h, ht.le]⟩
    have h1 := hfE _ hmem
    rw [map_add, map_smul, smul_eq_mul] at h1
    have h2 : t * w' i = -(|f y - u| + 1) := by
      simp only [t]
      rw [div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hneg.ne, mul_one]
    have h3 := le_abs_self (f y - u)
    change u ≤ f y + t * w' i at h1
    linarith
  have hfy : f y ≤ u := by
    by_contra hlt
    rw [not_le] at hlt
    let one : Fin d → ℝ := fun _ ↦ 1
    let t := (f y - u) / (|f one| + 1)
    have ht : 0 < t := div_pos (by linarith) (by positivity)
    have hmem : y - t • one ∈ O := fun i _ ↦ by simp [one, ht]
    have h1 := hfO _ hmem
    rw [map_sub, map_smul, smul_eq_mul] at h1
    have h2 : t * (|f one| + 1) = f y - u := by simp only [t]; field_simp
    have h3 : t * f one ≤ t * |f one| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.le
    nlinarith
  have hsum : 0 < ∑ i, w' i := by
    rcases (Finset.sum_nonneg fun i _ ↦ hw' i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hzero : ∀ i, w' i = 0 := fun i ↦
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hw' j).1 h.symm i (Finset.mem_univ _)
      have hf0 (z : Fin d → ℝ) : f z = 0 := by simp [hexp, hzero]
      have h1 := hfE y hyE
      have h2 := hfO (y - fun _ ↦ 1) fun i _ ↦ by simp
      rw [hf0] at h1 h2
      linarith
  refine ⟨fun i ↦ w' i / ∑ j, w' j, fun i ↦ div_nonneg (hw' i) hsum.le, ?_, fun z hz ↦ ?_⟩
  · rw [← Finset.sum_div, div_self hsum.ne']
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_le_div_iff_of_pos_right hsum, ← hexp, ← hexp]
    exact hfy.trans (hfE z ⟨z, hz, fun _ ↦ le_rfl⟩)

/-- GAPS 101.39, the compact-group averaging theorem for a finite group with its uniform Haar
measure and a bounded loss. The minimax consequences are not included. -/
theorem exists_equivariant_rule_risk_eq_average {G A : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Θ] [MulAction G A] [MeasurableSpace A]
    (hX : ∀ g : G, Measurable (fun x : X ↦ g • x))
    (hA : ∀ g : G, Measurable (fun a : A ↦ g • a))
    (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (hmodel : ∀ (g : G) θ, (P θ).map (fun x ↦ g • x) = P (g • θ))
    (L : Θ → A → ℝ) (hm : ∀ θ, Measurable (L θ))
    (C : ℝ) (hb : ∀ θ a, |L θ a| ≤ C)
    (hloss : ∀ (g : G) θ a, L (g • θ) (g • a) = L θ a) (delta : RandomizedDecisionRule X A) :
    ∃ bar : RandomizedDecisionRule X A,
      (∀ (g : G) x, bar.val (g • x) = (bar.val x).map (fun a ↦ g • a)) ∧
      ∀ θ, risk P L bar θ = (∑ g : G, risk P L delta (g • θ)) / Fintype.card G := by
  obtain ⟨δ, hδ⟩ := delta
  have hcard : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let c : ℝ≥0∞ := (Fintype.card G : ℝ≥0∞)⁻¹
  let μ : X → Measure A := fun x ↦ c • ∑ g : G, (δ (g⁻¹ • x)).map (fun a ↦ g • a)
  have hμ (x : X) (s : Set A) (hs : MeasurableSet s) :
      μ x s = c * ∑ g : G, δ (g⁻¹ • x) ((fun a ↦ g • a) ⁻¹' s) := by
    simp only [μ, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      Measure.map_apply (hA _) hs]
  have := hδ
  have hμm : Measurable μ := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [hμ _ s hs]
    exact (Finset.measurable_sum _ fun g _ ↦
      (Kernel.measurable_coe δ ((hA g) hs)).comp (hX g⁻¹)).const_mul c
  let K : Kernel X A := ⟨μ, hμm⟩
  have hK : IsMarkovKernel K := ⟨fun x ↦ ⟨by
    change μ x univ = 1
    rw [hμ x univ MeasurableSet.univ]
    simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, c]
    exact ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _)⟩⟩
  refine ⟨⟨K, hK⟩, fun g x ↦ ?_, fun θ ↦ ?_⟩
  · ext s hs
    change μ (g • x) s = (μ x).map (fun a ↦ g • a) s
    rw [Measure.map_apply (hA g) hs, hμ _ _ hs, hμ _ _ ((hA g) hs)]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h ↦ ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_smul]
    congr 1
    ext a
    simp
  · let F : G → X → ℝ := fun g y ↦ ∫ a, L (g⁻¹ • θ) a ∂δ y
    have hFm (g : G) : Measurable (F g) :=
      ((hm _).stronglyMeasurable.integral_kernel (κ := δ)).measurable
    have hFb (g : G) (y : X) : |F g y| ≤ C := by
      have := norm_integral_le_of_norm_le_const (μ := δ y) (C := C)
        (ae_of_all _ fun a ↦ by rw [Real.norm_eq_abs]; exact hb (g⁻¹ • θ) a)
      simpa [Real.norm_eq_abs, F] using this
    have hinner (x : X) : (∫ a, L θ a ∂μ x) = c.toReal * ∑ g : G, F g (g⁻¹ • x) := by
      simp only [μ]
      rw [integral_smul_measure, integral_finsetSum_measure (fun g _ ↦
        integrable_of_measurable_of_abs_le _ (hm θ) (hb θ)), smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [integral_map (hA g).aemeasurable (hm θ).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
      simp only
      rw [← hloss g (g⁻¹ • θ) a, smul_inv_smul]
    have := hP θ
    have hterm (g : G) : (∫ x, F g (g⁻¹ • x) ∂P θ) = risk P L ⟨δ, hδ⟩ (g⁻¹ • θ) := by
      rw [← integral_map (f := F g) (hX g⁻¹).aemeasurable (hFm g).aestronglyMeasurable,
        hmodel]
      rfl
    change (∫ x, ∫ a, L θ a ∂μ x ∂P θ) = _
    simp_rw [hinner]
    rw [integral_const_mul, integral_finsetSum (f := fun g x ↦ F g (g⁻¹ • x)) Finset.univ fun g _ ↦
      integrable_of_measurable_of_abs_le _ ((hFm g).comp (hX g⁻¹)) fun x ↦ hFb g _]
    simp_rw [hterm]
    rw [Fintype.sum_equiv (Equiv.inv G) (fun g ↦ risk P L ⟨δ, hδ⟩ (g⁻¹ • θ))
      (fun g ↦ risk P L ⟨δ, hδ⟩ (g • θ)) (fun g ↦ rfl)]
    simp only [c, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [div_eq_inv_mul]

/-- GAPS 101.42, the mean diffeomorphism in a minimal regular family.
An analytic inverse is stated on the open convex-support interior. -/
theorem exists_analytic_inverse_exponential_family_mean
    {d : ℕ} (nu : Measure (EuclideanSpace ℝ (Fin d))) [SigmaFinite nu]
    (hne : nu ≠ 0)
    (hminimal : ∀ u : EuclideanSpace ℝ (Fin d), u ≠ 0 → ∀ c : ℝ,
      ¬ (∀ᵐ x ∂nu, inner ℝ u x = c)) :
    let N := {eta : EuclideanSpace ℝ (Fin d) |
      Integrable (fun x ↦ Real.exp (inner ℝ eta x)) nu};
    let mean := fun eta : EuclideanSpace ℝ (Fin d) ↦
      (∫ x, Real.exp (inner ℝ eta x) ∂nu)⁻¹ •
        (∫ x, Real.exp (inner ℝ eta x) • x ∂nu);
    let K := interior (convexHull ℝ nu.support);
    IsOpen N → N.Nonempty →
      ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        AnalyticOnNhd ℝ mean N ∧ AnalyticOnNhd ℝ g K ∧
        (∀ eta ∈ N, mean eta ∈ K ∧ g (mean eta) = eta) ∧
        ∀ m ∈ K, g m ∈ N ∧ mean (g m) = m := by
  sorry


end CKSD
