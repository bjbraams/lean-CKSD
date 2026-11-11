module

public import CKSD.Bayes.MeanFieldCore
public import CKSD.Bayes.MeanFieldWasserstein
public import CKSD.Bayes.MeanFieldCoupling

/-!
# General finite-particle drift and uniqueness

A Wasserstein-Lipschitz mean-field drift induces an ordinary globally Lipschitz vector field on
finite particle configurations. The common empirical coupling gives its Lipschitz bound;
TauCeti's integral Grönwall inequality gives pathwise uniqueness for arbitrary common additive
inputs, without probabilistic assumptions on those inputs.

Source: the finite-particle uniqueness assertion of GAPS 104.51.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace CKSD

/-- A Wasserstein-Lipschitz drift induces a globally Lipschitz finite-particle vector field. -/
theorem IsWassersteinLipschitzDrift.lipschitzWith_particleDrift {d N : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L) (hN : 0 < N) :
    LipschitzWith (2 * Real.toNNReal L) (fun x : Fin N → EuclideanSpace ℝ (Fin d) ↦
      fun i : Fin N ↦ b (x i) (empiricalMeasure N x)) := by
  have hfirst (x : Fin N → EuclideanSpace ℝ (Fin d)) :
      Integrable (fun z ↦ ‖z‖) (empiricalMeasure N x) := by
    dsimp only [empiricalMeasure]
    apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne'))
    apply integrable_finsetSum_measure.mpr
    intro i _
    exact integrable_dirac (by finiteness)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  have hx := isProbabilityMeasure_empiricalMeasure hN x
  have hy := isProbabilityMeasure_empiricalMeasure hN y
  have h := hb (x i) (y i) (empiricalMeasure N x) (empiricalMeasure N y) hx hy (hfirst x) (hfirst y)
  have hw := wassersteinEDist_one_empirical_toReal_le_norm_sub hN x y
  have hl := Real.le_coe_toNNReal L
  have hnon : 0 ≤ ‖x i - y i‖ + (TauCeti.wassersteinEDist 1 (empiricalMeasure N x) (empiricalMeasure N y)).toReal := by positivity
  calc ‖b (x i) (empiricalMeasure N x) - b (y i) (empiricalMeasure N y)‖ ≤
        (Real.toNNReal L : ℝ) * (‖x i - y i‖ + (TauCeti.wassersteinEDist 1 (empiricalMeasure N x) (empiricalMeasure N y)).toReal) :=
          h.trans (mul_le_mul_of_nonneg_right hl hnon)
    _ ≤ (Real.toNNReal L : ℝ) * (‖x - y‖ + ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (norm_le_pi_norm (x - y) i) hw) (Real.toNNReal L).coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat, dist_eq_norm]; ring
/-- Under a Wasserstein-Lipschitz drift, two finite particle systems with the same additive
inputs are indistinguishable on nonnegative time, without assumptions on the input law. -/
theorem IsParticleSystem.ae_eq_of_wassersteinLipschitz {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ}
    (P : Measure Ω)
    (b : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hb : IsWassersteinLipschitzDrift b L)
    (X₀ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (W : ℕ → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (X Y : ℕ → ℝ → Ω → EuclideanSpace ℝ (Fin d))
    (hX : IsParticleSystem b X₀ W N X P) (hY : IsParticleSystem b X₀ W N Y P) :
    ∀ i < N, ∀ᵐ ω ∂P, ∀ t ≥ 0, X i t ω = Y i t ω := by
  intro i hi
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  let F : (Fin N → EuclideanSpace ℝ (Fin d)) → (Fin N → EuclideanSpace ℝ (Fin d)) :=
    fun x j ↦ b (x j) (empiricalMeasure N x)
  have hF : LipschitzWith (2 * Real.toNNReal L) F := hb.lipschitzWith_particleDrift b hN
  have hxall := ae_all_iff.2 (fun j : Fin N ↦ hX.2 j j.isLt)
  have hyall := ae_all_iff.2 (fun j : Fin N ↦ hY.2 j j.isLt)
  filter_upwards [hxall, hyall] with ω hx hy
  let x : ℝ → Fin N → EuclideanSpace ℝ (Fin d) := fun t j ↦ X j t ω
  let y : ℝ → Fin N → EuclideanSpace ℝ (Fin d) := fun t j ↦ Y j t ω
  have hxc : Continuous x := continuous_pi fun j ↦ (hx j).1
  have hyc : Continuous y := continuous_pi fun j ↦ (hy j).1
  have hφ : Continuous (fun t ↦ ‖x t - y t‖) := (hxc.sub hyc).norm
  have heq (t : ℝ) (ht : 0 ≤ t) : x t - y t = ∫ s in (0 : ℝ)..t, F (x s) - F (y s) := by
    have hfi : IntervalIntegrable (fun s ↦ F (x s)) volume 0 t := (hF.continuous.comp hxc).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun s ↦ F (y s)) volume 0 t := (hF.continuous.comp hyc).intervalIntegrable _ _
    funext j
    have hp := (ContinuousLinearMap.proj j : (Fin N → EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d)).intervalIntegral_comp_comm (hfi.sub hgi)
    change (∫ s in (0 : ℝ)..t,
      b (X j s ω) (empiricalMeasure N (fun l : Fin N ↦ X l s ω)) -
        b (Y j s ω) (empiricalMeasure N (fun l : Fin N ↦ Y l s ω))) =
          (∫ s in (0 : ℝ)..t, F (x s) - F (y s)) j at hp
    change X j t ω - Y j t ω = (∫ s in (0 : ℝ)..t, F (x s) - F (y s)) j
    rw [← hp]
    have hxi := (hx j).2 t ht
    have hyi := (hy j).2 t ht
    have hcompX : IntervalIntegrable (fun s ↦ b (X j s ω) (empiricalMeasure N (fun l : Fin N ↦ X l s ω))) volume 0 t :=
      ((continuous_apply j).comp (hF.continuous.comp hxc)).intervalIntegrable _ _
    have hcompY : IntervalIntegrable (fun s ↦ b (Y j s ω) (empiricalMeasure N (fun l : Fin N ↦ Y l s ω))) volume 0 t :=
      ((continuous_apply j).comp (hF.continuous.comp hyc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hcompX hcompY, hxi, hyi]
    abel
  have hineq (t : ℝ) (ht : 0 ≤ t) : ‖x t - y t‖ ≤
      0 + (2 * Real.toNNReal L : ℝ≥0) * ∫ s in (0 : ℝ)..t, ‖x s - y s‖ := by
    rw [heq t ht, zero_add]
    calc _ ≤ ∫ s in (0 : ℝ)..t, ‖F (x s) - F (y s)‖ := intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, (2 * Real.toNNReal L : ℝ≥0) * ‖x s - y s‖ :=
        intervalIntegral.integral_mono ht (((hF.continuous.comp hxc).sub (hF.continuous.comp hyc)).norm.intervalIntegrable _ _)
          ((hφ.const_mul _).intervalIntegrable _ _) (fun s ↦ hF.norm_sub_le _ _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  intro t ht
  have hgr := TauCeti.le_mul_exp_of_le_add_mul_integral hφ.continuousOn
    (2 * Real.toNNReal L).coe_nonneg (fun s (hs : s ∈ Icc (0 : ℝ) t) ↦ hineq s hs.1) t ⟨ht, le_rfl⟩
  have hxy : x t = y t := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hgr) (norm_nonneg _)))
  exact congrFun hxy (⟨i, hi⟩ : Fin N)
end CKSD
