module

public import CKSD.Nonparametric.Basic
public import TauCeti.Probability.McDiarmid
public import TauCeti.MeasureTheory.Function.Lp.Translation
public import TauCeti.Probability.Moments.SampleMean

/-!
# `L¹` consistency of the kernel density estimator

Tools for Devroye's theorem on the universal `L¹` consistency of the kernel density estimator
`f̂_n(t) = (n h)⁻¹ ∑ᵢ K((t - Xᵢ) / h)` on the real line, for a bounded measurable kernel `K`
vanishing outside a compact interval with `∫ K = 1` (not necessarily nonnegative).

The expected error is split as `E ∫ |f̂_n - f| ≤ ∫ |K_h * f - f| + ∫ E |f̂_n - K_h * f|`.
The bias term tends to `0` by the approximate-identity argument, based on the continuity of
translation in `L¹` (TauCeti's `MeasureTheory.MemLp.tendsto_eLpNorm_comp_add_sub`). The
stochastic term is bounded on `[-M, M]` through the variance of a sample mean (TauCeti's
`TauCeti.integral_finiteMean_sub_sq`) and outside `[-M, M]` by the tail mass of the law. The
`L¹` error has bounded differences `2 ∫ |K| / n` in the observations, so McDiarmid's inequality
(TauCeti's `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin`) gives an
exponential concentration bound around the mean.

## Main results

* `CKSD.tendsto_integral_abs_integral_mul_comp_sub_mul_sub`: the approximate identity
  `∫ |∫ K(u) f(t - h u) du - f(t)| dt → 0` as `h → 0` for integrable `f` and bounded
  integrable `K` with `∫ K = 1`.
* `CKSD.tendsto_integral_integral_abs_finiteKernelDensityEstimator_sub`: the expected `L¹`
  error tends to `0` when `h_n → 0` and `n h_n → ∞`.
* `CKSD.measureReal_le_integral_abs_finiteKernelDensityEstimator_sub_le`: the `L¹` error
  exceeds its mean by `ε` with probability at most `exp (-n ε² / (2 (∫ |K|)²))`.

## References

* L. Devroye, *The equivalence of weak, strong and complete convergence in `L₁` for kernel
  density estimates*, Ann. Statist. 11 (1983), 896–904.
* L. Devroye and L. Györfi, *Nonparametric Density Estimation: The `L₁` View*, Wiley (1985).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

/-- Change of variables `∫ F((t - y) / h) dy = h ∫ F` for `h > 0`. -/
private lemma integral_comp_sub_div_eq (F : ℝ → ℝ) (t : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ y, F ((t - y) / h) = h * ∫ u, F u := by
  rw [integral_sub_left_eq_self (fun y ↦ F (y / h)) volume t, Measure.integral_comp_div,
    abs_of_pos hh, smul_eq_mul]

/-- Continuity of translation in `L¹(ℝ)`, in integral form: `∫ |f(t - s) - f(t)| dt → 0` as
`s → 0`. -/
private lemma tendsto_integral_abs_comp_sub_sub {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun s : ℝ ↦ ∫ t, |f (t - s) - f t|) (𝓝 0) (𝓝 0) := by
  have h := (memLp_one_iff_integrable.2 hf).tendsto_eLpNorm_comp_add_sub le_rfl
    ENNReal.one_ne_top
  have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℝ)).tendsto 0
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h.comp hneg)
  rw [ENNReal.toReal_zero] at h'
  refine h'.congr fun s ↦ ?_
  simp only [Function.comp_apply, ← sub_eq_add_neg]
  have hm : AEStronglyMeasurable (fun x ↦ f (x - s) - f x) volume :=
    ((hf.comp_sub_right s).sub hf).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hm]
  simp only [Real.norm_eq_abs]
  exact hm

/-- **Approximate identity in `L¹(ℝ)`.** For a measurable integrable `f` and a bounded
integrable kernel `K` with `∫ K = 1`, the smoothed functions `t ↦ ∫ K(u) f(t - h u) du`
converge to `f` in `L¹` as `h → 0`. The kernel need not be nonnegative. -/
theorem tendsto_integral_abs_integral_mul_comp_sub_mul_sub {f K : ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f) (hKm : Measurable K) (hK : Integrable K) {C : ℝ}
    (hKb : ∀ x, |K x| ≤ C) (hK1 : ∫ x, K x = 1) :
    Tendsto (fun h : ℝ ↦ ∫ t, |(∫ u, K u * f (t - h * u)) - f t|) (𝓝 0) (𝓝 0) := by
  set ω : ℝ → ℝ := fun s ↦ ∫ t, |f (t - s) - f t| with hω
  have hωlim := tendsto_integral_abs_comp_sub_sub hf
  have hωm : Measurable ω := by
    have : StronglyMeasurable (Function.uncurry fun (s t : ℝ) ↦ |f (t - s) - f t|) :=
      (by fun_prop :
        Measurable (Function.uncurry fun (s t : ℝ) ↦ |f (t - s) - f t|)).stronglyMeasurable
    exact (this.integral_prod_right (ν := volume)).measurable
  have hω0 : ∀ s, 0 ≤ ω s := fun s ↦ integral_nonneg fun _ ↦ abs_nonneg _
  have hωle : ∀ s, ω s ≤ 2 * ∫ t, |f t| := fun s ↦ by
    have h1 : ∫ t, |f (t - s)| = ∫ t, |f t| :=
      integral_sub_right_eq_self (fun t ↦ |f t|) s
    calc ω s ≤ ∫ t, (|f (t - s)| + |f t|) :=
          integral_mono ((hf.comp_sub_right s).sub hf).abs
            ((hf.comp_sub_right s).abs.add hf.abs) fun t ↦ abs_sub _ _
      _ = 2 * ∫ t, |f t| := by
          rw [integral_add (hf.comp_sub_right s).abs hf.abs, h1]; ring
  -- the bound by the averaged translation modulus
  have hbound : ∀ h : ℝ, ∫ t, |(∫ u, K u * f (t - h * u)) - f t| ≤ ∫ u, |K u| * ω (h * u) := by
    intro h
    have hFm : Measurable fun p : ℝ × ℝ ↦ |K p.2| * |f (p.1 - h * p.2) - f p.1| := by
      fun_prop
    have hFint : Integrable (fun p : ℝ × ℝ ↦ |K p.2| * |f (p.1 - h * p.2) - f p.1|)
        (volume.prod volume) := by
      refine (integrable_prod_iff' hFm.aestronglyMeasurable).2 ⟨ae_of_all _ fun u ↦ ?_, ?_⟩
      · show Integrable (fun t ↦ |K u| * |f (t - h * u) - f t|) volume
        exact (((hf.comp_sub_right (h * u)).sub hf).abs).const_mul _
      · refine Integrable.mono' (hK.abs.mul_const (2 * ∫ t, |f t|)) ?_ (ae_of_all _ fun u ↦ ?_)
        · exact (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume)).aestronglyMeasurable
        · show ‖∫ t, ‖|K u| * |f (t - h * u) - f t|‖‖ ≤ |K u| * (2 * ∫ t, |f t|)
          simp only [norm_mul, Real.norm_eq_abs, abs_abs]
          rw [integral_const_mul, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hω0 _))]
          exact mul_le_mul_of_nonneg_left (hωle (h * u)) (abs_nonneg _)
    have hinner : ∀ t, (∫ u, K u * f (t - h * u)) - f t =
        ∫ u, K u * (f (t - h * u) - f t) := fun t ↦ by
      have hi : Integrable (fun u ↦ K u * f (t - h * u)) := by
        rcases eq_or_ne h 0 with rfl | h0
        · simpa using hK.mul_const (f t)
        · have : Integrable (fun u ↦ f (t - h * u)) := by
            have := (hf.comp_mul_left' h0).comp_sub_left (t / h)
            refine this.congr (ae_of_all _ fun u ↦ ?_)
            simp only
            congr 1; field_simp
          exact this.bdd_mul hKm.aestronglyMeasurable (ae_of_all _ fun u ↦ by simpa using hKb u)
      simp_rw [mul_sub]
      rw [integral_sub hi (hK.mul_const (f t)), integral_mul_const, hK1, one_mul]
    calc ∫ t, |(∫ u, K u * f (t - h * u)) - f t|
        ≤ ∫ t, ∫ u, |K u| * |f (t - h * u) - f t| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
            hFint.integral_prod_left (ae_of_all _ fun t ↦ ?_)
          dsimp only
          rw [hinner t]
          refine (abs_integral_le_integral_abs).trans_eq ?_
          simp only [abs_mul]
      _ = ∫ u, ∫ t, |K u| * |f (t - h * u) - f t| := integral_integral_swap hFint
      _ = ∫ u, |K u| * ω (h * u) := by
          congr 1; funext u
          rw [integral_const_mul]
  -- dominated convergence for the averaged modulus
  have hlim : Tendsto (fun h : ℝ ↦ ∫ u, |K u| * ω (h * u)) (𝓝 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 (0 : ℝ))
      (F := fun h u ↦ |K u| * ω (h * u)) (f := fun _ ↦ 0)
      (fun u ↦ |K u| * (2 * ∫ t, |f t|))
      (Eventually.of_forall fun h ↦ ((continuous_abs.measurable.comp hKm).mul
        (hωm.comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun h ↦ ae_of_all _ fun u ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hω0 _))]
        exact mul_le_mul_of_nonneg_left (hωle _) (abs_nonneg _))
      (hK.abs.mul_const _)
      (ae_of_all _ fun u ↦ by
        have h1 : Tendsto (fun h : ℝ ↦ h * u) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const u
        simpa using (hωlim.comp h1).const_mul |K u|)
    simpa using this
  exact squeeze_zero (fun h ↦ integral_nonneg fun _ ↦ abs_nonneg _) hbound hlim

/-- Under the product of `n ≥ 1` copies of a probability measure `P`, the coordinates `φ (x i)`
of a bounded measurable `φ` have mean `∫ φ dP`. -/
private lemma integral_comp_eval_pi {n : ℕ} {P : Measure ℝ} [IsProbabilityMeasure P]
    {φ : ℝ → ℝ} (hφ : Measurable φ) (i : Fin n) :
    ∫ x, φ (x i) ∂(Measure.pi fun _ : Fin n ↦ P) = ∫ y, φ y ∂P := by
  have h := (measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_pi_apply i).aemeasurable hφ.aestronglyMeasurable]

/-- Variance of a sample mean on a product space: for `n ≥ 1` and bounded measurable `φ`,
`E (n⁻¹ ∑ φ(xᵢ) - ∫ φ dP)² ≤ n⁻¹ ∫ φ² dP`. -/
private lemma integral_sampleMean_sub_sq_le {n : ℕ} (hn : 0 < n) {P : Measure ℝ}
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) :
    ∫ x, ((n : ℝ)⁻¹ * ∑ i, φ (x i) - ∫ y, φ y ∂P) ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      (n : ℝ)⁻¹ * ∫ y, φ y ^ 2 ∂P := by
  set π := Measure.pi fun _ : Fin n ↦ P
  set c := ∫ y, φ y ∂P
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hZ : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ ↦ φ (x i)) 2 π := fun i ↦
    MemLp.of_bound (hφ.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun x ↦ by simpa using hB (x i))
  have hmean : ∀ i : Fin n, π[fun x : Fin n → ℝ ↦ φ (x i)] = c := fun i ↦
    integral_comp_eval_pi hφ i
  have hind : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) ↦ φ (x i)) π :=
    iIndepFun_pi (X := fun _ ↦ φ) fun _ ↦ hφ.aemeasurable
  have key := TauCeti.integral_finiteMean_sub_sq hZ hmean fun i j hij ↦ hind.indepFun hij
  have hφ2 : Integrable (fun y ↦ φ y ^ 2) P :=
    Integrable.of_bound (hφ.pow_const 2).aestronglyMeasurable (B ^ 2) (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2)
  have hvar : ∀ i : Fin n, ∫ x, (φ (x i) - c) ^ 2 ∂π ≤ ∫ y, φ y ^ 2 ∂P := fun i ↦ by
    have h1 := integral_comp_eval_pi (P := P) ((hφ.sub_const c).pow_const 2) i
    rw [h1]
    have hint : Integrable (fun y ↦ φ y) P :=
      Integrable.of_bound hφ.aestronglyMeasurable B (ae_of_all _ fun y ↦ by simpa using hB y)
    have : ∫ y, (φ y - c) ^ 2 ∂P = ∫ y, φ y ^ 2 ∂P - c ^ 2 := by
      have e : (fun y ↦ (φ y - c) ^ 2) = fun y ↦ φ y ^ 2 - 2 * c * φ y + c ^ 2 := by
        funext y; ring
      have e1 : ∫ y, (φ y ^ 2 - 2 * c * φ y + c ^ 2) ∂P =
          ∫ y, (φ y ^ 2 - 2 * c * φ y) ∂P + ∫ _y, c ^ 2 ∂P :=
        integral_add (hφ2.sub (hint.const_mul _)) (integrable_const _)
      have e2 : ∫ y, (φ y ^ 2 - 2 * c * φ y) ∂P = ∫ y, φ y ^ 2 ∂P - ∫ y, 2 * c * φ y ∂P :=
        integral_sub hφ2 (hint.const_mul _)
      rw [e, e1, e2, integral_const_mul]
      simp [c]; ring
    rw [this]; nlinarith [sq_nonneg c]
  have hfm : ∀ x : Fin n → ℝ, TauCeti.finiteMean ℝ (fun i ↦ φ (x i)) =
      (n : ℝ)⁻¹ * ∑ i, φ (x i) := fun x ↦ by
    rw [TauCeti.finiteMean_eq_inv_smul_sum, Fintype.card_fin, smul_eq_mul]
  simp_rw [hfm] at key
  rw [key, Fintype.card_fin]
  calc ((n : ℝ) ^ 2)⁻¹ * ∑ i : Fin n, ∫ x, (φ (x i) - c) ^ 2 ∂π
      ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ _i : Fin n, ∫ y, φ y ^ 2 ∂P := by
        gcongr with i; exact hvar i
    _ = (n : ℝ)⁻¹ * ∫ y, φ y ^ 2 ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- Mean absolute deviation of a sample mean, crude bound: for `n ≥ 1` and bounded measurable
`φ`, `E |n⁻¹ ∑ φ(xᵢ) - ∫ φ dP| ≤ 2 ∫ |φ| dP`. -/
private lemma integral_abs_sampleMean_sub_le_two_mul {n : ℕ} (hn : 0 < n) {P : Measure ℝ}
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) :
    ∫ x, |(n : ℝ)⁻¹ * ∑ i, φ (x i) - ∫ y, φ y ∂P| ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      2 * ∫ y, |φ y| ∂P := by
  set π := Measure.pi fun _ : Fin n ↦ P
  have hint : Integrable φ P :=
    Integrable.of_bound hφ.aestronglyMeasurable B (ae_of_all _ fun y ↦ by simpa using hB y)
  have hZ : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ ↦ |φ (x i)|) π := fun i ↦
    Integrable.of_bound (continuous_abs.measurable.comp
      (hφ.comp (measurable_pi_apply i))).aestronglyMeasurable B
      (ae_of_all _ fun x ↦ by simpa using hB (x i))
  have hsum : Integrable (fun x : Fin n → ℝ ↦ (n : ℝ)⁻¹ * ∑ i, |φ (x i)| + |∫ y, φ y ∂P|) π :=
    ((integrable_finsetSum _ fun i _ ↦ hZ i).const_mul _).add (integrable_const _)
  calc ∫ x, |(n : ℝ)⁻¹ * ∑ i, φ (x i) - ∫ y, φ y ∂P| ∂π
      ≤ ∫ x, ((n : ℝ)⁻¹ * ∑ i, |φ (x i)| + |∫ y, φ y ∂P|) ∂π := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hsum
          (ae_of_all _ fun x ↦ ?_)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∫ y, |φ y| ∂P + |∫ y, φ y ∂P| := by
        rw [integral_add ((integrable_finsetSum _ fun i _ ↦ hZ i).const_mul _)
          (integrable_const _), integral_const_mul, integral_finsetSum _ fun i _ ↦ hZ i]
        have hi : ∀ i : Fin n, ∫ x, |φ (x i)| ∂π = ∫ y, |φ y| ∂P := fun i ↦
          integral_comp_eval_pi (φ := fun y ↦ |φ y|) (continuous_abs.measurable.comp hφ) i
        simp_rw [hi]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          integral_const, probReal_univ, one_smul]
        field_simp
    _ ≤ 2 * ∫ y, |φ y| ∂P := by
        have := abs_integral_le_integral_abs (f := φ) (μ := P)
        linarith

/-- Mean absolute deviation of a sample mean, variance bound: for `λ > 0`,
`E |n⁻¹ ∑ φ(xᵢ) - ∫ φ dP| ≤ (n⁻¹ ∫ φ² dP) / (2λ) + λ / 2`. -/
private lemma integral_abs_sampleMean_sub_le_div {n : ℕ} (hn : 0 < n) {P : Measure ℝ}
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {lam : ℝ} (hlam : 0 < lam) :
    ∫ x, |(n : ℝ)⁻¹ * ∑ i, φ (x i) - ∫ y, φ y ∂P| ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ((n : ℝ)⁻¹ * ∫ y, φ y ^ 2 ∂P) / (2 * lam) + lam / 2 := by
  set π := Measure.pi fun _ : Fin n ↦ P
  set Z : (Fin n → ℝ) → ℝ := fun x ↦ (n : ℝ)⁻¹ * ∑ i, φ (x i) - ∫ y, φ y ∂P
  have hZm : Measurable Z := by
    simp only [Z]
    exact ((Finset.measurable_sum _ fun i _ ↦ hφ.comp (measurable_pi_apply i)).const_mul _).sub
      measurable_const
  have hZb : ∀ x, |Z x| ≤ 2 * |B| := fun x ↦ by
    have hc : |∫ y, φ y ∂P| ≤ |B| := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ y, |φ y| ∂P ≤ ∫ _y, |B| ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
              (ae_of_all _ fun y ↦ (hB y).trans (le_abs_self B))
        _ = |B| := by simp
    have hm : |(n : ℝ)⁻¹ * ∑ i, φ (x i)| ≤ |B| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc (n : ℝ)⁻¹ * |∑ i, φ (x i)| ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, |B| := by
            gcongr
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ ↦ (hB (x i)).trans (le_abs_self B))
        _ = |B| := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    exact (abs_sub _ _).trans (by linarith)
  have hZ2 : Integrable (fun x ↦ Z x ^ 2) π :=
    Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable ((2 * |B|) ^ 2)
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hZb x) 2)
  have hpt : ∀ x, |Z x| ≤ Z x ^ 2 / (2 * lam) + lam / 2 := fun x ↦ by
    have h1 : 0 ≤ (|Z x| - lam) ^ 2 := sq_nonneg _
    have h2 : |Z x| ^ 2 = Z x ^ 2 := sq_abs _
    have h3 : Z x ^ 2 / (2 * lam) + lam / 2 - |Z x| = (|Z x| - lam) ^ 2 / (2 * lam) := by
      field_simp; rw [← h2]; ring
    have h4 : 0 ≤ (|Z x| - lam) ^ 2 / (2 * lam) := by positivity
    linarith
  have hV : ∫ x, Z x ^ 2 ∂π ≤ (n : ℝ)⁻¹ * ∫ y, φ y ^ 2 ∂P := integral_sampleMean_sub_sq_le hn hφ hB
  have hI : Integrable (fun x ↦ Z x ^ 2 / (2 * lam) + lam / 2) π :=
    (hZ2.div_const _).add (integrable_const _)
  have step1 : ∫ x, |Z x| ∂π ≤ ∫ x, (Z x ^ 2 / (2 * lam) + lam / 2) ∂π :=
    integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hI (ae_of_all _ hpt)
  have step2 : ∫ x, (Z x ^ 2 / (2 * lam) + lam / 2) ∂π =
      (∫ x, Z x ^ 2 ∂π) / (2 * lam) + lam / 2 := by
    rw [integral_add (hZ2.div_const _) (integrable_const _), integral_div, integral_const,
      probReal_univ, one_smul]
  have step3 := div_le_div_of_nonneg_right hV (by positivity : (0 : ℝ) ≤ 2 * lam)
  linarith

/-- A bounded measurable kernel vanishing outside `[-R, R]` is integrable. -/
theorem integrable_of_abs_le_of_eq_zero {K : ℝ → ℝ} (hKm : Measurable K) {C R : ℝ}
    (hKb : ∀ x, |K x| ≤ C) (hKc : ∀ x, R < |x| → K x = 0) : Integrable K := by
  have hsupp : Function.support K ⊆ Icc (-R) R := fun x hx ↦ by
    by_contra h
    refine hx (hKc x (lt_abs.2 ?_))
    simp only [mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · right; linarith
    · left; exact h
  refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
  exact Measure.integrableOn_of_bounded (by simp) hKm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simpa using hKb x)

/-- The rescaled translates `t ↦ K((t - y) / h) / h` of an integrable kernel are integrable. -/
private lemma integrable_comp_sub_div_div {K : ℝ → ℝ} (hK : Integrable K) (y : ℝ) {h : ℝ}
    (hh : 0 < h) : Integrable fun t ↦ K ((t - y) / h) / h :=
  (((hK.comp_div hh.ne').comp_sub_right y)).div_const h

/-- `∫ |K((t - y) / h)| / h dt = ∫ |K|` for `h > 0`. -/
private lemma integral_abs_comp_sub_div_div (K : ℝ → ℝ) (y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ t, |K ((t - y) / h) / h| = ∫ u, |K u| := by
  have : (fun t ↦ |K ((t - y) / h) / h|) = fun t ↦ |K ((t - y) / h)| / h := by
    funext t; rw [abs_div, abs_of_pos hh]
  rw [this, integral_div, integral_sub_right_eq_self (fun t ↦ |K (t / h)|) y,
    Measure.integral_comp_div (fun u ↦ |K u|), abs_of_pos hh, smul_eq_mul]
  field_simp

/-- The kernel density estimator of a sample is the sample mean of the rescaled kernel
translates. -/
private lemma finiteKernelDensityEstimator_eq_mean {n : ℕ} (K : ℝ → ℝ) (h : ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    finiteKernelDensityEstimator K h x t = (n : ℝ)⁻¹ * ∑ i, K ((t - x i) / h) / h := by
  rw [finiteKernelDensityEstimator, ← Finset.sum_div, mul_comm, div_mul_eq_div_div,
    div_div, mul_comm h, ← div_div, div_eq_mul_inv]
  ring

/-- The rescaled kernel `(t, y) ↦ K((t - y) / h) / h` is integrable for Lebesgue measure in
`t` times a probability measure in `y`. -/
private lemma integrable_prod_comp_sub_div_div {K : ℝ → ℝ} (hKm : Measurable K)
    (hK : Integrable K) {h : ℝ} (hh : 0 < h) (P : Measure ℝ) [IsProbabilityMeasure P] :
    Integrable (fun p : ℝ × ℝ ↦ K ((p.1 - p.2) / h) / h) (volume.prod P) := by
  have hm : Measurable fun p : ℝ × ℝ ↦ K ((p.1 - p.2) / h) / h := by fun_prop
  refine (integrable_prod_iff' hm.aestronglyMeasurable).2
    ⟨ae_of_all _ fun y ↦ integrable_comp_sub_div_div hK y hh, ?_⟩
  simp only [Real.norm_eq_abs]
  simp_rw [integral_abs_comp_sub_div_div K _ hh]
  exact integrable_const _

/-- Away from `[-M, M]`, the averaged rescaled kernel has small mass: if `K` vanishes outside
`[-R, R]` and `0 < h ≤ 1`, then
`∫_{|t| > M} ∫ |K((t - y)/h)/h| dP(y) dt ≤ ∫ |K| · P(|y| > M - R)`. -/
private lemma setIntegral_compl_Icc_integral_abs_le {K : ℝ → ℝ} (hKm : Measurable K)
    (hK : Integrable K) {R : ℝ} (hR : 0 < R) (hKc : ∀ x, R < |x| → K x = 0) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (P : Measure ℝ) [IsProbabilityMeasure P] (M : ℝ) :
    ∫ t in (Icc (-M) M)ᶜ, ∫ y, |K ((t - y) / h) / h| ∂P ≤
      (∫ u, |K u|) * P.real {y | M - R < |y|} := by
  have hint := (integrable_prod_comp_sub_div_div hKm hK hh P).norm
  have hint' : Integrable (fun p : ℝ × ℝ ↦ |K ((p.1 - p.2) / h) / h|)
      ((volume.restrict (Icc (-M) M)ᶜ).prod P) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hint.restrict
  rw [integral_integral_swap hint']
  have hpt : ∀ y, ∫ t in (Icc (-M) M)ᶜ, |K ((t - y) / h) / h| ≤
      (∫ u, |K u|) * {y | M - R < |y|}.indicator 1 y := by
    intro y
    by_cases hy : M - R < |y|
    · rw [indicator_of_mem (by exact hy), Pi.one_apply, mul_one,
        ← integral_abs_comp_sub_div_div K y hh]
      exact setIntegral_le_integral (integrable_comp_sub_div_div hK y hh).abs
        (ae_of_all _ fun _ ↦ abs_nonneg _)
    · rw [indicator_of_notMem (by exact hy), mul_zero]
      refine le_of_eq (setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_)
      have ht' : M < |t| := by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
        rcases ht with ht | ht
        · exact lt_abs.2 (Or.inr (by linarith))
        · exact lt_abs.2 (Or.inl ht)
      push Not at hy
      have h1 : R < |(t - y) / h| := by
        rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh]
        have := abs_sub_abs_le_abs_sub t y
        nlinarith
      rw [hKc _ h1, zero_div, abs_zero]
  have hS : MeasurableSet {y : ℝ | M - R < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  refine le_trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
    (((integrable_const (1 : ℝ)).indicator hS).const_mul (∫ u, |K u|)) (ae_of_all _ hpt))
    (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator_const _ hS]
  simp

/-- The kernel density estimator of a sample is integrable in `t`. -/
private lemma integrable_finiteKernelDensityEstimator {K : ℝ → ℝ} (hK : Integrable K) {n : ℕ}
    {h : ℝ} (hh : 0 < h) (x : Fin n → ℝ) :
    Integrable fun t ↦ finiteKernelDensityEstimator K h x t := by
  simp_rw [finiteKernelDensityEstimator_eq_mean]
  exact (integrable_finsetSum _ fun i _ ↦ integrable_comp_sub_div_div hK (x i) hh).const_mul _

/-- The kernel density estimator has `L¹` norm at most `∫ |K|`. -/
private lemma integral_abs_finiteKernelDensityEstimator_le {K : ℝ → ℝ} (hK : Integrable K)
    {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Fin n → ℝ) :
    ∫ t, |finiteKernelDensityEstimator K h x t| ≤ ∫ u, |K u| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [finiteKernelDensityEstimator, integral_nonneg (fun u ↦ abs_nonneg (K u))]
  have hI : ∀ i, Integrable fun t ↦ |K ((t - x i) / h) / h| := fun i ↦
    (integrable_comp_sub_div_div hK (x i) hh).abs
  calc ∫ t, |finiteKernelDensityEstimator K h x t|
      ≤ ∫ t, (n : ℝ)⁻¹ * ∑ i, |K ((t - x i) / h) / h| := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
          ((integrable_finsetSum _ fun i _ ↦ hI i).const_mul _) (ae_of_all _ fun t ↦ ?_)
        dsimp only
        rw [finiteKernelDensityEstimator_eq_mean, abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∫ u, |K u| := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hI i]
        simp_rw [integral_abs_comp_sub_div_div K _ hh]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **Expectation bound for the `L¹` error of the kernel density estimator.** For `n ≥ 1`
observations from `P`, `0 < h ≤ 1`, `λ > 0` and `M ≥ 0`, with `g(t) = ∫ K((t - y)/h)/h dP(y)`,
`E ∫ |f̂_n - f| ≤ ∫ |g - f| + C ∫|K| / (2 λ n h) + λ M + 2 ∫|K| · P(|y| > M - R)`. -/
private lemma integral_integral_abs_finiteKernelDensityEstimator_sub_le {K f : ℝ → ℝ}
    (hKm : Measurable K) {C R : ℝ} (hKb : ∀ x, |K x| ≤ C) (hR : 0 < R)
    (hKc : ∀ x, R < |x| → K x = 0) (hfm : Measurable f) (hf : Integrable f)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (P : Measure ℝ) [IsProbabilityMeasure P] {lam : ℝ} (hlam : 0 < lam) {M : ℝ} (hM : 0 ≤ M) :
    ∫ x, (∫ t, |finiteKernelDensityEstimator K h x t - f t|) ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      (∫ t, |(∫ y, K ((t - y) / h) / h ∂P) - f t|) +
        (C / (n * h) * ∫ u, |K u|) / (2 * lam) + lam * M +
        2 * ((∫ u, |K u|) * P.real {y | M - R < |y|}) := by
  set π := Measure.pi fun _ : Fin n ↦ P
  have hK := integrable_of_abs_le_of_eq_zero hKm hKb hKc
  have hφint := integrable_prod_comp_sub_div_div hKm hK hh P
  set g : ℝ → ℝ := fun t ↦ ∫ y, K ((t - y) / h) / h ∂P with hg
  set a : ℝ → ℝ := fun t ↦ ∫ y, |K ((t - y) / h) / h| ∂P with ha
  have hgint : Integrable g := hφint.integral_prod_left
  have haint : Integrable a := hφint.norm.integral_prod_left
  have ha0 : ∀ t, 0 ≤ a t := fun t ↦ integral_nonneg fun _ ↦ abs_nonneg _
  have hφm : ∀ t, Measurable fun y ↦ K ((t - y) / h) / h := fun t ↦ by fun_prop
  have hφb : ∀ t y, |K ((t - y) / h) / h| ≤ C / h := fun t y ↦ by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (hKb _) hh.le
  have hfk : ∀ x t, finiteKernelDensityEstimator K h x t =
      (n : ℝ)⁻¹ * ∑ i, K ((t - x i) / h) / h := finiteKernelDensityEstimator_eq_mean K h
  -- pointwise bounds on the mean absolute deviation
  have hD1 : ∀ t, ∫ x, |finiteKernelDensityEstimator K h x t - g t| ∂π ≤ 2 * a t := fun t ↦ by
    simp_rw [hfk]
    exact integral_abs_sampleMean_sub_le_two_mul hn (hφm t) (hφb t)
  have hD2 : ∀ t, ∫ x, |finiteKernelDensityEstimator K h x t - g t| ∂π ≤
      (C / (n * h) * a t) / (2 * lam) + lam / 2 := fun t ↦ by
    simp_rw [hfk]
    refine (integral_abs_sampleMean_sub_le_div hn (hφm t) (hφb t) hlam).trans
      (add_le_add_left (div_le_div_of_nonneg_right ?_ (by positivity)) _)
    have hsq : ∫ y, (K ((t - y) / h) / h) ^ 2 ∂P ≤ ∫ y, C / h * |K ((t - y) / h) / h| ∂P := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _)
        ((Integrable.of_bound (continuous_abs.measurable.comp (hφm t)).aestronglyMeasurable (C / h)
          (ae_of_all _ fun y ↦ by simpa using hφb t y)).const_mul _) (ae_of_all _ fun y ↦ ?_)
      dsimp only
      rw [← sq_abs]
      nlinarith [hφb t y, abs_nonneg (K ((t - y) / h) / h)]
    rw [integral_const_mul] at hsq
    calc (n : ℝ)⁻¹ * ∫ y, (K ((t - y) / h) / h) ^ 2 ∂P ≤ (n : ℝ)⁻¹ * (C / h * a t) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = C / (n * h) * a t := by field_simp
  -- Fubini: the averaged kernel has total mass `∫ |K|`
  have hamass : ∫ t, a t = ∫ u, |K u| := by
    have hsw := integral_integral_swap (f := fun t y ↦ |K ((t - y) / h) / h|) (μ := volume)
      (ν := P) hφint.norm
    simp only [ha]
    rw [hsw]
    simp_rw [integral_abs_comp_sub_div_div K _ hh]
    simp
  -- integrability in the sample, for fixed `t`
  have hcoord : ∀ t,
      Integrable (fun x : Fin n → ℝ ↦ |finiteKernelDensityEstimator K h x t - g t|) π :=
    fun t ↦ by
      simp_rw [hfk]
      have hc : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ ↦ K ((t - x i) / h) / h) π :=
        fun i ↦ Integrable.of_bound ((hφm t).comp (measurable_pi_apply i)).aestronglyMeasurable
          (C / h) (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hφb t (x i))
      exact (((integrable_finsetSum _ fun i _ ↦ hc i).const_mul _).sub (integrable_const _)).abs
  -- the pointwise bound
  set U : ℝ → ℝ := fun t ↦ (Icc (-M) M).indicator
    (fun t ↦ (C / (n * h) * a t) / (2 * lam) + lam / 2) t +
      (Icc (-M) M)ᶜ.indicator (fun t ↦ 2 * a t) t with hU
  have hpt : ∀ t, ∫ x, |finiteKernelDensityEstimator K h x t - f t| ∂π ≤ |g t - f t| + U t := by
    intro t
    have h1 : ∫ x, |finiteKernelDensityEstimator K h x t - f t| ∂π ≤
        ∫ x, (|finiteKernelDensityEstimator K h x t - g t| + |g t - f t|) ∂π :=
      integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
        ((hcoord t).add (integrable_const _)) (ae_of_all _ fun x ↦ abs_sub_le _ _ _)
    rw [integral_add (hcoord t) (integrable_const _), integral_const, probReal_univ,
      one_smul] at h1
    have h2 : ∫ x, |finiteKernelDensityEstimator K h x t - g t| ∂π ≤ U t := by
      by_cases ht : t ∈ Icc (-M) M
      · have ht' : t ∉ (Icc (-M) M)ᶜ := fun h' ↦ h' ht
        simp only [hU, indicator_of_mem ht, indicator_of_notMem ht', add_zero]
        exact hD2 t
      · have ht' : t ∈ (Icc (-M) M)ᶜ := ht
        simp only [hU, indicator_of_mem ht', indicator_of_notMem ht, zero_add]
        exact hD1 t
    linarith
  have hUint : Integrable U := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc |>.add
      ((haint.const_mul 2).indicator measurableSet_Icc.compl)
    exact ((haint.const_mul _).div_const _).integrableOn.add (integrableOn_const (by simp))
  have hUle : ∫ t, U t ≤ (C / (n * h) * ∫ u, |K u|) / (2 * lam) + lam * M +
      2 * ((∫ u, |K u|) * P.real {y | M - R < |y|}) := by
    have hI1 : IntegrableOn (fun t ↦ (C / (n * h) * a t) / (2 * lam) + lam / 2) (Icc (-M) M) :=
      ((haint.const_mul _).div_const _).integrableOn.add (integrableOn_const (by simp))
    rw [integral_add (hI1.integrable_indicator measurableSet_Icc)
      ((haint.const_mul 2).indicator measurableSet_Icc.compl),
      integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc.compl,
      integral_add (((haint.const_mul _).div_const _).integrableOn) (integrableOn_const (by simp)),
      setIntegral_const, integral_div, integral_const_mul, integral_const_mul,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    have hIcc : ∫ t in Icc (-M) M, a t ≤ ∫ u, |K u| := by
      rw [← hamass]
      exact setIntegral_le_integral haint (ae_of_all _ ha0)
    have hcompl := setIntegral_compl_Icc_integral_abs_le hKm hK hR hKc hh hh1 P M
    have hc0 : 0 ≤ C / (n * h) := by
      have : 0 ≤ C := (abs_nonneg _).trans (hKb 0)
      positivity
    have e : (M - -M) * (lam / 2) = lam * M := by ring
    rw [e]
    have : C / (n * h) * ∫ t in Icc (-M) M, a t ≤ C / (n * h) * ∫ u, |K u| :=
      mul_le_mul_of_nonneg_left hIcc hc0
    have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * lam)
    linarith
  -- assemble
  have hFint : Integrable (Function.uncurry fun (x : Fin n → ℝ) (t : ℝ) ↦
      |finiteKernelDensityEstimator K h x t - f t|) (π.prod volume) := by
    have hFm : Measurable (Function.uncurry fun (x : Fin n → ℝ) (t : ℝ) ↦
        |finiteKernelDensityEstimator K h x t - f t|) := by
      simp only [Function.uncurry_def]
      simp_rw [hfk]
      fun_prop
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨ae_of_all _ fun x ↦
      ((integrable_finiteKernelDensityEstimator hK hh x).sub hf).abs, ?_⟩
    refine Integrable.of_bound
      (hFm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
      ((∫ u, |K u|) + ∫ t, |f t|) (ae_of_all _ fun x ↦ ?_)
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)]
    calc ∫ t, |finiteKernelDensityEstimator K h x t - f t|
        ≤ ∫ t, (|finiteKernelDensityEstimator K h x t| + |f t|) :=
          integral_mono ((integrable_finiteKernelDensityEstimator hK hh x).sub hf).abs
            ((integrable_finiteKernelDensityEstimator hK hh x).abs.add hf.abs)
            fun t ↦ abs_sub _ _
      _ = (∫ t, |finiteKernelDensityEstimator K h x t|) + ∫ t, |f t| :=
          integral_add (integrable_finiteKernelDensityEstimator hK hh x).abs hf.abs
      _ ≤ (∫ u, |K u|) + ∫ t, |f t| :=
          add_le_add_left (integral_abs_finiteKernelDensityEstimator_le hK hh x) _
  rw [integral_integral_swap hFint]
  have hmain : ∫ t, ∫ x, |finiteKernelDensityEstimator K h x t - f t| ∂π ≤
      ∫ t, (|g t - f t| + U t) :=
    integral_mono_of_nonneg (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
      ((hgint.sub hf).abs.add hUint) (ae_of_all _ hpt)
  have hgf : Integrable (fun t ↦ |g t - f t|) := (hgint.sub hf).abs
  have hsplit : ∫ t, (|g t - f t| + U t) = (∫ t, |g t - f t|) + ∫ t, U t :=
    integral_add hgf hUint
  change _ ≤ (∫ t, |g t - f t|) + _ + _ + _
  linarith

/-- For a law `P` with nonnegative density `f`, the expected rescaled kernel is the smoothed
density: `∫ K((t - y)/h)/h dP(y) = ∫ K(u) f(t - h u) du` for `h > 0`. -/
private lemma integral_comp_sub_div_div_withDensity {K f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ y, K ((t - y) / h) / h ∂(volume.withDensity fun x ↦ ENNReal.ofReal (f x)) =
      ∫ u, K u * f (t - h * u) := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  set G : ℝ → ℝ := fun y ↦ f y * K ((t - y) / h) with hG
  have h1 : ∀ u, K u * f (t - h * u) = (fun v ↦ G (t - v)) (h * u) := fun u ↦ by
    simp only [hG, sub_sub_cancel]
    rw [mul_div_cancel_left₀ _ hh.ne', mul_comm]
  simp_rw [h1]
  rw [Measure.integral_comp_mul_left (fun v ↦ G (t - v)) h, integral_sub_left_eq_self G volume t,
    abs_inv, abs_of_pos hh, smul_eq_mul, ← integral_const_mul]
  congr 1; funext y
  simp only [hG]; field_simp

/-- The tail probabilities `P(|y| > r)` of a probability measure on `ℝ` tend to `0`. -/
private lemma tendsto_measureReal_lt_abs (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun r : ℝ ↦ P.real {y | r < |y|}) atTop (𝓝 0) := by
  have h := tendsto_measure_norm_gt_of_isTightMeasureSet
    (isTightMeasureSet_singleton (μ := P))
  simp only [mem_singleton_iff, iSup_iSup_eq_left, Real.norm_eq_abs] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [measureReal_def, Function.comp_def] using this

/-- **Expected `L¹` consistency of the kernel density estimator.** For a bounded measurable
kernel vanishing outside `[-R, R]` with `∫ K = 1`, a law `P` with density `f ≥ 0`, and
bandwidths `h_n > 0` with `h_n → 0` and `n h_n → ∞`, the expected `L¹` error
`E ∫ |f̂_n - f|` of the kernel density estimator from `n` i.i.d. observations tends to `0`. -/
theorem tendsto_integral_integral_abs_finiteKernelDensityEstimator_sub {K f : ℝ → ℝ}
    (hKm : Measurable K) {C R : ℝ} (hKb : ∀ x, |K x| ≤ C) (hR : 0 < R)
    (hKc : ∀ x, R < |x| → K x = 0) (hK1 : ∫ x, K x = 1)
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P = volume.withDensity fun x ↦ ENNReal.ofReal (f x))
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh0 : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ ↦ (n : ℝ) * h n) atTop atTop) :
    Tendsto (fun n ↦ ∫ x, (∫ t, |finiteKernelDensityEstimator K (h n) x t - f t|)
      ∂(Measure.pi fun _ : Fin n ↦ P)) atTop (𝓝 0) := by
  have hK := integrable_of_abs_le_of_eq_zero hKm hKb hKc
  set κ := ∫ u, |K u| with hκdef
  have hκ : 0 ≤ κ := integral_nonneg fun _ ↦ abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the truncation level `M`
  have htail : Tendsto (fun M : ℝ ↦ 2 * κ * P.real {y | M - R < |y|}) atTop (𝓝 0) := by
    have h1 := (tendsto_measureReal_lt_abs P).comp (tendsto_atTop_add_const_right _ (-R) tendsto_id)
    simpa [Function.comp_def, sub_eq_add_neg] using h1.const_mul (2 * κ)
  obtain ⟨M, hM, hM0⟩ :=
    ((htail.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).and
      (eventually_ge_atTop 0)).exists
  set lam := ε / (4 * (M + 1)) with hlamdef
  have hlam : 0 < lam := by positivity
  have hlamM : lam * M < ε / 4 := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the bias and the stochastic term
  have hbias := (tendsto_integral_abs_integral_mul_comp_sub_mul_sub hfm hf hKm hK hKb hK1).comp
    hh0
  have hvar : Tendsto (fun n : ℕ ↦ (C / (n * h n) * κ) / (2 * lam)) atTop (𝓝 0) := by
    have h1 := (hnh.inv_tendsto_atTop).const_mul (C * κ / (2 * lam))
    rw [mul_zero] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Pi.inv_apply]
    field_simp
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hbias.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).and
      ((hvar.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).and
        ((hh0.eventually (eventually_le_nhds one_pos)).and (eventually_ge_atTop 1))))
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hb, hv, hh1, hn1⟩ := hN n hn
  have hbound := integral_integral_abs_finiteKernelDensityEstimator_sub_le hKm hKb hR hKc hfm hf
    (by omega : 0 < n) (hh n) hh1 P hlam hM0
  have hg : ∀ t, ∫ y, K ((t - y) / h n) / h n ∂P = ∫ u, K u * f (t - h n * u) := fun t ↦ by
    rw [hP]; exact integral_comp_sub_div_div_withDensity hfm hf0 t (hh n)
  simp_rw [hg] at hbound
  have h0 : 0 ≤ ∫ x, (∫ t, |finiteKernelDensityEstimator K (h n) x t - f t|)
      ∂(Measure.pi fun _ : Fin n ↦ P) :=
    integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  simp only [Function.comp_apply] at hb
  linarith

/-- Replacing one observation changes the kernel density estimator by a rescaled difference of
two kernel translates. -/
private lemma finiteKernelDensityEstimator_update_sub {n : ℕ} (K : ℝ → ℝ) (h : ℝ)
    (x : Fin n → ℝ) (i : Fin n) (b t : ℝ) :
    finiteKernelDensityEstimator K h (Function.update x i b) t -
        finiteKernelDensityEstimator K h x t =
      (n : ℝ)⁻¹ * (K ((t - b) / h) / h - K ((t - x i) / h) / h) := by
  simp only [finiteKernelDensityEstimator_eq_mean]
  rw [Fintype.sum_eq_add_sum_compl i,
    Fintype.sum_eq_add_sum_compl i (fun j ↦ K ((t - x j) / h) / h)]
  have : ∑ j ∈ {i}ᶜ, K ((t - Function.update x i b j) / h) / h =
      ∑ j ∈ {i}ᶜ, K ((t - x j) / h) / h :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (by simpa using hj)]
  rw [this, Function.update_self]
  ring

/-- **Bounded differences** for the `L¹` error of the kernel density estimator: replacing one
of `n` observations changes `∫ |f̂_n - f|` by at most `2 ∫ |K| / n`. -/
private lemma abs_integral_abs_finiteKernelDensityEstimator_update_sub_le {K f : ℝ → ℝ}
    (hK : Integrable K) (hf : Integrable f) {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Fin n → ℝ)
    (i : Fin n) (b : ℝ) :
    |(∫ t, |finiteKernelDensityEstimator K h (Function.update x i b) t - f t|) -
        (∫ t, |finiteKernelDensityEstimator K h x t - f t|)| ≤ 2 * (∫ u, |K u|) / n := by
  have hA : Integrable fun t ↦
      |finiteKernelDensityEstimator K h (Function.update x i b) t - f t| :=
    ((integrable_finiteKernelDensityEstimator hK hh (Function.update x i b)).sub hf).abs
  have hB : Integrable fun t ↦ |finiteKernelDensityEstimator K h x t - f t| :=
    ((integrable_finiteKernelDensityEstimator hK hh x).sub hf).abs
  have hb := (integrable_comp_sub_div_div hK b hh).abs
  have hxi := (integrable_comp_sub_div_div hK (x i) hh).abs
  rw [← integral_sub hA hB]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ t, |(|finiteKernelDensityEstimator K h (Function.update x i b) t - f t| -
        |finiteKernelDensityEstimator K h x t - f t|)|
      ≤ ∫ t, (n : ℝ)⁻¹ * (|K ((t - b) / h) / h| + |K ((t - x i) / h) / h|) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _)
          ((hb.add hxi).const_mul _) (ae_of_all _ fun t ↦ ?_)
        refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
        rw [sub_sub_sub_cancel_right, finiteKernelDensityEstimator_update_sub, abs_mul,
          abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ = 2 * (∫ u, |K u|) / n := by
        rw [integral_const_mul, integral_add hb hxi, integral_abs_comp_sub_div_div K b hh,
          integral_abs_comp_sub_div_div K (x i) hh]
        ring

/-- Measurability of the `L¹` error of the kernel density estimator as a function of the
sample. -/
theorem measurable_integral_abs_finiteKernelDensityEstimator_sub {K f : ℝ → ℝ}
    (hKm : Measurable K) (hfm : Measurable f) (n : ℕ) (h : ℝ) :
    Measurable fun x : Fin n → ℝ ↦ ∫ t, |finiteKernelDensityEstimator K h x t - f t| := by
  have hFm : Measurable (Function.uncurry fun (x : Fin n → ℝ) (t : ℝ) ↦
      |finiteKernelDensityEstimator K h x t - f t|) := by
    simp only [Function.uncurry_def]
    simp_rw [finiteKernelDensityEstimator_eq_mean]
    fun_prop
  exact (hFm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

/-- **Concentration of the `L¹` error** (Devroye): by McDiarmid's inequality, for `n ≥ 1`
i.i.d. observations from `P` and `ε ≥ 0`, the `L¹` error of the kernel density estimator
exceeds its mean by `ε` with probability at most `exp (-n ε² / (2 (∫ |K|)²))`. -/
theorem measureReal_le_integral_abs_finiteKernelDensityEstimator_sub_le {K f : ℝ → ℝ}
    (hKm : Measurable K) (hK : Integrable K) (hfm : Measurable f) (hf : Integrable f)
    {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (P : Measure ℝ) [IsProbabilityMeasure P]
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n ↦ P).real {x | ε ≤
      (∫ t, |finiteKernelDensityEstimator K h x t - f t|) -
      ∫ y, (∫ t, |finiteKernelDensityEstimator K h y t - f t|) ∂(Measure.pi fun _ : Fin n ↦ P)} ≤
      Real.exp (-(n * ε ^ 2) / (2 * (∫ u, |K u|) ^ 2)) := by
  have hκ : 0 ≤ ∫ u, |K u| := integral_nonneg fun _ ↦ abs_nonneg _
  have hsub := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin P
    (fun x : Fin n → ℝ ↦ ∫ t, |finiteKernelDensityEstimator K h x t - f t|)
    (measurable_integral_abs_finiteKernelDensityEstimator_sub hKm hfm n h)
    (2 * (∫ u, |K u|) / n)
    (fun x i b ↦ abs_integral_abs_finiteKernelDensityEstimator_update_sub_le hK hf hh x i b)
  refine (hsub.measure_ge_le hε).trans_eq ?_
  congr 1
  have hc : (((n : ℝ≥0) * ((2 * (∫ u, |K u|) / n).toNNReal / 2) ^ 2 : ℝ≥0) : ℝ) =
      (∫ u, |K u|) ^ 2 / n := by
    push_cast [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 2 * (∫ u, |K u|) / n)]
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hc]
  rcases eq_or_lt_of_le hκ with hκ0 | hκ0
  · rw [← hκ0]; simp
  · field_simp

end CKSD
