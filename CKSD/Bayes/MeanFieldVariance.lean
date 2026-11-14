module

public import CKSD.Bayes.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import TauCeti.Probability.Moments.SampleMean

/-!
# Mean-square fluctuations of bounded empirical interactions

For independent identically distributed particle locations, the interaction average evaluated
at one of those locations approximates the population interaction with mean-square error of
order `1/N`. The average includes its self-interaction term.

The proof splits the distinguished particle from the complementary tuple, integrates at a
frozen distinguished location, and applies the Hilbert-space Bienaymé identity from pinned
TauCeti (`TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`). The self-interaction is bounded
separately; no continuity or Lipschitz assumption on the measurable interaction is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a frozen location and independent samples, the expected squared centered interaction
sum is at most `4κ²` times the number of samples. -/
theorem integral_norm_sum_centeredInteraction_sq_le
    (μ : Measure E) [IsProbabilityMeasure μ] (K : E → E → E)
    (hKm : Measurable (Function.uncurry K)) (κ : ℝ≥0) (hK : ∀ x y, ‖K x y‖ ≤ κ)
    {ι : Type*} [Fintype ι] (x : E) :
    ∫ z : ι → E, ‖∑ j : ι, (K x (z j) - ∫ y, K x y ∂μ)‖ ^ 2
      ∂Measure.pi (fun _ : ι ↦ μ) ≤ (Fintype.card ι : ℝ) * (4 * (κ : ℝ) ^ 2) := by
  let ν := Measure.pi (fun _ : ι ↦ μ)
  let m := ∫ y, K x y ∂μ
  have hm : Measurable (K x) := hKm.comp (measurable_const.prodMk measurable_id)
  have hKi : Integrable (K x) μ := Integrable.of_bound hm.aestronglyMeasurable κ
    (ae_of_all _ fun y ↦ hK x y)
  have hmb : ‖m‖ ≤ κ := by
    calc ‖m‖ ≤ ∫ y, ‖K x y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : E, (κ : ℝ) ∂μ := integral_mono hKi.norm (integrable_const _) (hK x)
      _ = κ := by simp
  let X : ι → (ι → E) → E := fun j z ↦ K x (z j) - m
  have hXm (j : ι) : Measurable (X j) :=
    (hm.comp (measurable_pi_apply j)).sub measurable_const
  have hXbound (j : ι) (z : ι → E) : ‖X j z‖ ≤ 2 * κ :=
    (norm_sub_le _ _).trans (by linarith [hK x (z j)])
  have hX2 (j : ι) : MemLp (X j) 2 ν := MemLp.of_bound (hXm j).aestronglyMeasurable _
    (ae_of_all _ fun z ↦ hXbound j z)
  have hXmean (j : ι) : (∫ z, X j z ∂ν) = 0 := by
    change (∫ z : ι → E, K x (z j) - m ∂Measure.pi (fun _ : ι ↦ μ)) = 0
    rw [integral_comp_eval (μ := fun _ : ι ↦ μ) (i := j) (f := fun y : E ↦ K x y - m)
      (show Measurable (fun y : E ↦ K x y - m) from hm.sub measurable_const).aestronglyMeasurable]
    rw [integral_sub hKi (integrable_const m), integral_const]
    simp [m]
  have hind : iIndepFun (fun (j : ι) (z : ι → E) ↦ K x (z j) - m) ν :=
    iIndepFun_pi (fun _ ↦ (hm.sub measurable_const).aemeasurable)
  have heq := TauCeti.integral_norm_sum_sq_of_pairwise_indepFun (μ := ν) (X := X)
    (s := Finset.univ) (fun j _ ↦ hX2 j) (fun j _ ↦ hXmean j)
    (fun j _ k _ hjk ↦ hind.indepFun hjk)
  change (∫ z, ‖∑ j, X j z‖ ^ 2 ∂ν) ≤ _
  rw [heq]
  calc ∑ j : ι, ∫ z, ‖X j z‖ ^ 2 ∂ν ≤ ∑ _ : ι, (4 * (κ : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          calc (∫ z, ‖X j z‖ ^ 2 ∂ν) ≤ ∫ _ : ι → E, (4 * (κ : ℝ) ^ 2) ∂ν := by
                  apply integral_mono
                    ((memLp_two_iff_integrable_sq_norm (hX2 j).aestronglyMeasurable).1 (hX2 j))
                    (integrable_const _)
                  intro z
                  nlinarith [hXbound j z, norm_nonneg (X j z), κ.coe_nonneg]
            _ = _ := by simp
    _ = _ := by simp


/-- In an iid sample, the interaction average seen by one sampled particle differs from its
population counterpart in mean square by at most `16κ²/N`, including the self-interaction term. -/
theorem integral_norm_empiricalInteraction_sub_sq_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ] (K : E → E → E)
    (hKm : Measurable (Function.uncurry K)) (κ : ℝ≥0) (hK : ∀ x y, ‖K x y‖ ≤ κ)
    {N : ℕ} (hn : 0 < N) (Y : Fin N → Ω → E) (hYm : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y P) (hlaw : ∀ j, P.map (Y j) = μ) (i : Fin N) :
    ∫ ω, ‖((N : ℝ)⁻¹ • ∑ j, K (Y i ω) (Y j ω)) - ∫ z, K (Y i ω) z ∂μ‖ ^ 2 ∂P ≤
      16 * (κ : ℝ) ^ 2 / (N : ℝ) := by
  classical
  let m : E → E := fun x ↦ ∫ y, K x y ∂μ
  have hmm : Measurable m := hKm.stronglyMeasurable.integral_prod_right.measurable
  have hmb (x : E) : ‖m x‖ ≤ κ := by
    have hki : Integrable (K x) μ := Integrable.of_bound
      (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable κ
      (ae_of_all _ fun y ↦ hK x y)
    calc ‖m x‖ ≤ ∫ y, ‖K x y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : E, (κ : ℝ) ∂μ := integral_mono hki.norm (integrable_const _) (hK x)
      _ = κ := by simp
  let C : E → E → E := fun x y ↦ K x y - m x
  have hCm : Measurable (Function.uncurry C) := hKm.sub (hmm.comp measurable_fst)
  have hCb (x y : E) : ‖C x y‖ ≤ 2 * κ :=
    (norm_sub_le _ _).trans (by linarith [hK x y, hmb x])
  let T : Finset (Fin N) := Finset.univ.erase i
  let ν : Measure (T → E) := Measure.pi (fun _ : T ↦ μ)
  let F : E × (T → E) → E := fun p ↦ C p.1 p.1 + ∑ j : T, C p.1 (p.2 j)
  have hCdiag : Measurable (fun p : E × (T → E) ↦ C p.1 p.1) :=
    hCm.comp (measurable_fst.prodMk measurable_fst)
  have hCcoord (j : T) : Measurable (fun p : E × (T → E) ↦ C p.1 (p.2 j)) :=
    hCm.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hF2 : MemLp F 2 (μ.prod ν) := by
    apply (MemLp.of_bound hCdiag.aestronglyMeasurable (2 * κ)
      (ae_of_all _ fun p ↦ hCb p.1 p.1)).add
    exact memLp_finsetSum _ fun j _ ↦ MemLp.of_bound (hCcoord j).aestronglyMeasurable (2 * κ)
      (ae_of_all _ fun p ↦ hCb p.1 (p.2 j))
  have hFm : Measurable F := hCdiag.add (Finset.univ.measurable_sum fun j _ ↦ hCcoord j)
  have hGint : Integrable (fun p ↦ ‖F p‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).1 hF2
  have hfixed (x : E) : (∫ z : T → E, ‖F (x, z)‖ ^ 2 ∂ν) ≤
      16 * (κ : ℝ) ^ 2 * N := by
    have hS2 : MemLp (fun z : T → E ↦ ∑ j : T, C x (z j)) 2 ν :=
      memLp_finsetSum _ fun j _ ↦ MemLp.of_bound
        (hCm.comp (measurable_const.prodMk (measurable_pi_apply j))).aestronglyMeasurable
        (2 * κ) (ae_of_all _ fun z ↦ hCb x (z j))
    have hFS2 : MemLp (fun z : T → E ↦ F (x, z)) 2 ν := (memLp_const (C x x)).add hS2
    have hintS : Integrable (fun z : T → E ↦ ‖∑ j : T, C x (z j)‖ ^ 2) ν :=
      (memLp_two_iff_integrable_sq_norm hS2.aestronglyMeasurable).1 hS2
    calc (∫ z : T → E, ‖F (x, z)‖ ^ 2 ∂ν) ≤
          ∫ z : T → E, 8 * (κ : ℝ) ^ 2 + 2 * ‖∑ j : T, C x (z j)‖ ^ 2 ∂ν := by
            apply integral_mono
              ((memLp_two_iff_integrable_sq_norm hFS2.aestronglyMeasurable).1 hFS2)
              ((integrable_const _).add (hintS.const_mul 2))
            intro z
            change ‖C x x + ∑ j : T, C x (z j)‖ ^ 2 ≤
              8 * (κ : ℝ) ^ 2 + 2 * ‖∑ j : T, C x (z j)‖ ^ 2
            have htri := norm_add_le (C x x) (∑ j : T, C x (z j))
            have hsquare : ‖C x x + ∑ j : T, C x (z j)‖ ^ 2 ≤
                (‖C x x‖ + ‖∑ j : T, C x (z j)‖) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
            nlinarith [hCb x x, norm_nonneg (C x x),
              sq_nonneg (‖C x x‖ - ‖∑ j : T, C x (z j)‖), κ.coe_nonneg]
      _ = 8 * (κ : ℝ) ^ 2 + 2 * (∫ z : T → E, ‖∑ j : T, C x (z j)‖ ^ 2 ∂ν) := by
        have ha := integral_add (integrable_const (8 * (κ : ℝ) ^ 2)) (hintS.const_mul 2)
        have hconst : (∫ _ : T → E, 8 * (κ : ℝ) ^ 2 ∂ν) = 8 * (κ : ℝ) ^ 2 := by simp
        rw [ha, hconst, integral_const_mul]
      _ ≤ 8 * (κ : ℝ) ^ 2 + 2 * ((Fintype.card T : ℝ) * (4 * (κ : ℝ) ^ 2)) := by
        have hb := integral_norm_sum_centeredInteraction_sq_le μ K hKm κ hK (ι := T) x
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ ≤ 16 * (κ : ℝ) ^ 2 * N := by
        have hcard : Fintype.card T ≤ N := by
          simpa using Fintype.card_le_of_injective (f := (Subtype.val : T → Fin N)) Subtype.val_injective
        have hcard' : (Fintype.card T : ℝ) ≤ N := by exact_mod_cast hcard
        have hn' : (1 : ℝ) ≤ N := by exact_mod_cast hn
        nlinarith [sq_nonneg (κ : ℝ), mul_le_mul_of_nonneg_right hcard' (sq_nonneg (κ : ℝ))]
  have hprod : (∫ p, ‖F p‖ ^ 2 ∂μ.prod ν) ≤ 16 * (κ : ℝ) ^ 2 * N := by
    rw [integral_prod _ hGint]
    calc (∫ x, ∫ z : T → E, ‖F (x, z)‖ ^ 2 ∂ν ∂μ) ≤
          ∫ _ : E, 16 * (κ : ℝ) ^ 2 * N ∂μ :=
            integral_mono hGint.integral_prod_left (integrable_const _) hfixed
      _ = _ := by simp
  let Z : Ω → (T → E) := fun ω j ↦ Y j ω
  have hZm : Measurable Z := measurable_pi_iff.2 fun j ↦ hYm j
  have hZlaw : P.map Z = ν := by
    have hI : iIndepFun (fun j : T ↦ Y j) P :=
      iIndepFun.precomp (g := (Subtype.val : T → Fin N)) Subtype.val_injective hind
    have hh := iIndepFun.map_fun_eq_pi_map (f := fun j : T ↦ Y j)
      (fun j : T ↦ (hYm j).aemeasurable) hI
    simpa only [hlaw] using hh
  have hind' : IndepFun (Y i) Z P := by
    have hh := hind.indepFun_finset {i} T
      (Finset.disjoint_singleton_left.2 (by simp [T])) hYm
    exact hh.comp (φ := fun v : ({i} : Finset (Fin N)) → E ↦
      v ⟨i, Finset.mem_singleton_self i⟩) (ψ := id)
      (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset (Fin N)))) measurable_id
  have hpair : P.map (fun ω ↦ (Y i ω, Z ω)) = μ.prod ν := by
    rw [hind'.map_prod_eq_prod_map_map (hYm i).aemeasurable hZm.aemeasurable, hlaw i, hZlaw]
  have hsplit (ω : Ω) : (∑ j : Fin N, C (Y i ω) (Y j ω)) = F (Y i ω, Z ω) := by
    change (∑ j : Fin N, C (Y i ω) (Y j ω)) =
      C (Y i ω) (Y i ω) + ∑ j : T, C (Y i ω) (Y j ω)
    rw [Finset.sum_coe_sort T (fun j ↦ C (Y i ω) (Y j ω))]
    have hh := Finset.sum_erase_add Finset.univ (fun j ↦ C (Y i ω) (Y j ω)) (Finset.mem_univ i)
    simp [T]
  have hwhole : (∫ ω, ‖∑ j : Fin N, C (Y i ω) (Y j ω)‖ ^ 2 ∂P) ≤
      16 * (κ : ℝ) ^ 2 * N := by
    simp_rw [hsplit]
    rw [← integral_map ((hYm i).prodMk hZm).aemeasurable
      (hFm.norm.pow_const 2).aestronglyMeasurable, hpair]
    exact hprod
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hident (ω : Ω) : ((N : ℝ)⁻¹ • ∑ j, K (Y i ω) (Y j ω)) - m (Y i ω) =
      (N : ℝ)⁻¹ • ∑ j : Fin N, C (Y i ω) (Y j ω) := by
    simp only [C, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  change (∫ ω, ‖((N : ℝ)⁻¹ • ∑ j, K (Y i ω) (Y j ω)) - m (Y i ω)‖ ^ 2 ∂P) ≤ _
  simp_rw [hident, norm_smul,
    Real.norm_of_nonneg (show 0 ≤ (N : ℝ)⁻¹ from inv_nonneg.2 (Nat.cast_nonneg N)), mul_pow]
  rw [integral_const_mul]
  calc _ ≤ ((N : ℝ)⁻¹) ^ 2 * (16 * (κ : ℝ) ^ 2 * N) :=
      mul_le_mul_of_nonneg_left hwhole (sq_nonneg _)
    _ = _ := by field_simp

end CKSD
