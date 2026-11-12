module
public import CKSD.Bayes.ParticleEmpiricalMoments
public import CKSD.Bayes.ParticleTransport
/-!
# Conditional moments of bootstrap sampling errors

A probability-uniform iid empirical `Lᵖ` bound transfers to each generation of the bootstrap
particle system by conditioning on its entire past. Bounded real conditional integration is
obtained from the existing complex integration theorem; taking real powers and integrating
the conditional product-law estimate gives the claimed norm bound.

This is the conditional use of Del Moral, *Feynman–Kac Formulae*, Lemma 7.3.3 in the proof of
Theorem 7.4.4, printed pages 245–246 (PDF pages 258–259 of the local 2004 copy). Mathlib
supplies the real `lpNorm` identities and powers, and the bootstrap conditional law is local.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators Nat
namespace CKSD
/-- Conditional bootstrap integration for bounded real functions of the past and next sample. -/
theorem integral_bootstrap_succ_real
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (N : ℕ) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ) (n : ℕ)
    (H : (Fin (n+1) → Fin N → X) × (Fin N → X) → ℝ) (hH : Measurable H) {C : ℝ}
    (hC : ∀ z, |H z| ≤ C) :
    (∫ ω, H ((fun i : Fin (n+1) ↦ ξ i ω),ξ (n+1) ω) ∂P) =
      ∫ ω, ∫ z, H ((fun i : Fin (n+1) ↦ ξ i ω),z)
        ∂Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω)) ∂P := by
  apply Complex.ofReal_injective
  have h := integral_bootstrap_succ P M N ξ hξ n (fun z ↦ (H z : ℂ))
    (Complex.continuous_ofReal.measurable.comp hH) (C := C)
    (fun z ↦ by simpa only [Complex.norm_real,Real.norm_eq_abs] using hC z)
  simpa only [integral_complex_ofReal] using h

/-- A nonempty finite empirical average preserves an absolute bound. -/
theorem abs_finite_average_le {X : Type*} {N : ℕ} (hN : 0 < N)
    (x : Fin N → X) {f : X → ℝ} {B : ℝ} (hfb : ∀ y, |f y| ≤ B) :
    |(∑ i,f (x i))/(N:ℝ)| ≤ B := by
  have hn : (0:ℝ)<N := Nat.cast_pos.2 hN
  rw [abs_div,abs_of_pos hn,div_le_iff₀ hn]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using
    Finset.sum_le_sum (s := Finset.univ) (f := fun i ↦ |f (x i)|) (g := fun _ ↦ B) (fun i _ ↦ hfb (x i))

/-- A local bootstrap sampling error is a measurable random variable. -/
theorem measurable_particle_sampling_error
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (M : FeynmanKacModel X) {N : ℕ} (ξ : ℕ → Ω → Fin N → X)
    (hξ : ∀ n, Measurable (ξ n)) (n : ℕ) {f : X → ℝ} (hf : Measurable f)
    {B : ℝ} (hfb : ∀ y, |f y| ≤ B) :
    Measurable (fun ω ↦ (∑ i,f (ξ n ω i))/(N:ℝ)-M.pathPredMean (fun q ↦ ξ q ω) n f) := by
  have hpath : Measurable (fun ω (q : ℕ) ↦ ξ q ω) := measurable_pi_iff.2 hξ
  exact ((Finset.measurable_fun_sum _ fun i _ ↦ hf.comp ((measurable_pi_apply i).comp (hξ n))).div_const _).sub
    ((M.measurable_pathPredMean n hf hfb).comp hpath)

/-- Local sampling errors are bounded independently of the particle path. -/
theorem abs_particle_sampling_error_le
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) {N : ℕ} (hN : 0 < N)
    (x : ℕ → Fin N → X) (n : ℕ) {f : X → ℝ} (hf : Measurable f)
    {B : ℝ} (hfb : ∀ y, |f y| ≤ B) :
    |(∑ i,f (x n i))/(N:ℝ)-M.pathPredMean x n f| ≤ 2*B := by
  have := M.isProbabilityMeasure_pathPredictionLaw hN x n
  have hp : |M.pathPredMean x n f| ≤ B := by
    rw [← M.integral_pathPredictionLaw x n f]
    exact abs_integral_le_of_abs_le hf hfb
  exact (abs_sub _ _).trans (by linarith [abs_finite_average_le hN (x n) hfb])

/-- A probability-uniform iid `Lᵖ` bound passes to every conditional bootstrap sampling step. -/
theorem lpNorm_particle_sampling_error_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    {N : ℕ} (hN : 0 < N) (ξ : ℕ → Ω → Fin N → X) (hξ : IsBootstrapParticleSystem P M N ξ)
    {p : ℝ} (hp : 1 ≤ p) {f : X → ℝ} (hf : Measurable f) {B L : ℝ}
    (_hB : 0 ≤ B) (hfb : ∀ y, |f y| ≤ B) (hL : 0 ≤ L)
    (hlocal : ∀ (ν : Measure X), IsProbabilityMeasure ν →
      lpNorm (fun z : Fin N → X ↦ (∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂ν)
        (ENNReal.ofReal p) (Measure.pi (fun _ : Fin N ↦ ν)) ≤ L)
    (n : ℕ) :
    lpNorm (fun ω ↦ (∑ i,f (ξ n ω i))/(N:ℝ)-M.pathPredMean (fun q ↦ ξ q ω) n f)
      (ENNReal.ofReal p) P ≤ L := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow (ν : Measure X) (hν : IsProbabilityMeasure ν) :
      (∫ z : Fin N → X, |(∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂ν|^p
        ∂Measure.pi (fun _ : Fin N ↦ ν)) ≤ L^p := by
    let _ := hν
    have hm : Measurable (fun z : Fin N → X ↦ (∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂ν) :=
      ((Finset.measurable_fun_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)).div_const _).sub measurable_const
    have h := Real.rpow_le_rpow (lpNorm_nonneg (f := fun z : Fin N → X ↦
      (∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂ν) (p := ENNReal.ofReal p) (μ := Measure.pi (fun _ : Fin N ↦ ν)))
      (hlocal ν hν) hp0.le
    rw [lpNorm_ofReal_eq_integral_abs_rpow _ hp0 hm.aestronglyMeasurable,
      ← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
      one_div,inv_mul_cancel₀ hp0.ne',Real.rpow_one] at h
    exact h
  have hmoment : (∫ ω, |(∑ i,f (ξ n ω i))/(N:ℝ)-
      M.pathPredMean (fun q ↦ ξ q ω) n f|^p ∂P) ≤ L^p := by
    cases n with
    | zero =>
      have hm : Measurable (fun z : Fin N → X ↦ |(∑ i,f (z i))/(N:ℝ)-∫ x,f x ∂(M.initial : Measure X)|^p) := by
        fun_prop
      change (∫ ω, |(∑ i,f (ξ 0 ω i))/(N:ℝ)-∫ x,f x ∂(M.initial : Measure X)|^p ∂P) ≤ _
      rw [← integral_map (hξ.1 0).aemeasurable hm.aestronglyMeasurable,hξ.2.1]
      exact hpow M.initial inferInstance
    | succ n =>
      let c : (Fin N → X) → ℝ := fun x ↦ ∫ y,f y ∂M.particlePredictionLaw n x
      have hcm : Measurable c := M.measurable_integral_particlePredictionLaw n hf hfb
      let H : (Fin (n+1) → Fin N → X) × (Fin N → X) → ℝ :=
        fun z ↦ |(∑ i,f (z.2 i))/(N:ℝ)-c (z.1 (Fin.last n))|^p
      have hHm : Measurable H := by
        have hs : Measurable (fun z : (Fin (n+1) → Fin N → X) × (Fin N → X) ↦
            (∑ i,f (z.2 i))/(N:ℝ)) :=
          (Finset.measurable_fun_sum _ fun i _ ↦
            hf.comp ((measurable_pi_apply i).comp measurable_snd)).div_const _
        exact (continuous_abs.measurable.comp
          (hs.sub (hcm.comp ((measurable_pi_apply _).comp measurable_fst)))).pow_const p
      have hHb (z : (Fin (n+1) → Fin N → X) × (Fin N → X)) : |H z| ≤ (2*B)^p := by
        have := M.isProbabilityMeasure_particlePredictionLaw hN n (z.1 (Fin.last n))
        have hcp : |c (z.1 (Fin.last n))| ≤ B := abs_integral_le_of_abs_le hf hfb
        dsimp only [H]
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _)
          ((abs_sub _ _).trans (by linarith [abs_finite_average_le hN z.2 hfb])) hp0.le
      have hInt := integral_bootstrap_succ_real P M N ξ hξ n H hHm hHb
      change (∫ ω, H ((fun i : Fin (n+1) ↦ ξ i ω),ξ (n+1) ω) ∂P) ≤ _
      rw [hInt]
      calc
        (∫ ω, ∫ z, H ((fun i : Fin (n+1) ↦ ξ i ω),z)
          ∂Measure.pi (fun _ : Fin N ↦ M.particlePredictionLaw n (ξ n ω)) ∂P) ≤ (∫ _ : Ω,L^p ∂P) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun ω ↦ integral_nonneg fun z ↦ Real.rpow_nonneg (abs_nonneg _) _)
            (integrable_const _)
          exact ae_of_all _ fun ω ↦ hpow (M.particlePredictionLaw n (ξ n ω))
            (M.isProbabilityMeasure_particlePredictionLaw hN n (ξ n ω))
        _ = L^p := by simp
  rw [lpNorm_ofReal_eq_integral_abs_rpow P hp0
    (measurable_particle_sampling_error M ξ hξ.1 n hf hfb).aestronglyMeasurable]
  have h := Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) hmoment
    (by positivity : 0 ≤ 1/p)
  rw [← Real.rpow_mul hL,one_div,mul_inv_cancel₀ hp0.ne',Real.rpow_one] at h
  simpa only [one_div] using h

end CKSD
