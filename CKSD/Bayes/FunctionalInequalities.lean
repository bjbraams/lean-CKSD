module

public import CKSD.Bayes.LangevinSampling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Resolvent
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Langevin flows, functional inequalities, and the JKO scheme

The law of the overdamped Langevin diffusion `dX = -∇V(X) dt + √2 dW` is represented by a weak
solution of its Fokker–Planck equation (`IsFokkerPlanckSolution` with drift `-∇V` and
infinitesimal covariance `2I`) on every bounded time interval; no stochastic differential equation
is constructed. The Poincaré and logarithmic Sobolev inequalities are TauCeti's. The JKO step is a
point of TauCeti's Moreau–Yosida resolvent on the Wasserstein space `P₂(ℝᵈ)`, for the free energy
built from TauCeti's Boltzmann entropy relative to Lebesgue measure and potential energy.

## Main definitions

* `CKSD.IsLangevinFlow`: a weak solution of the overdamped Langevin Fokker–Planck equation.
* `CKSD.chiSqDiv`: the `χ²` divergence.
* `CKSD.jkoFreeEnergy`: the free energy `∫ ρ log ρ + ∫ V dν` on `P₂(ℝᵈ)`.

## Main results

* `CKSD.poincareInequality_iff_chiSqDiv_langevin_le`,
  `CKSD.logSobolevInequality_iff_klDiv_langevin_le`: the Poincaré and logarithmic Sobolev
  inequalities as exponential decay of `χ²` and relative entropy along the Langevin flow.
* `CKSD.wasserstein_sq_langevin_le_of_logSobolev`: Otto–Villani decay in Wasserstein distance.
* `CKSD.poincareInequality_of_logSobolevInequality`: a logarithmic Sobolev inequality implies the
  Poincaré inequality with the same constant.
* `CKSD.logSobolevInequality_gibbsMeasure_of_bounded_perturbation`,
  `CKSD.poincareInequality_gibbsMeasure_of_bounded_perturbation`: Bakry–Émery and
  Holley–Stroock.
* `CKSD.jko_scheme_tendsto_fokkerPlanck`: the Jordan–Kinderlehrer–Otto theorem.

Sources: GAPS 104.43 and 104.44.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The flow of laws of the overdamped Langevin diffusion: a weak Fokker–Planck solution with
drift `-gradV` and covariance `2I` on `[0, T]` for every `T ≥ 0`. -/
def IsLangevinFlow {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ T ≥ 0, IsFokkerPlanckSolution μ (fun _ x ↦ -gradV x) (fun _ _ ↦ (2 : ℝ) • 1) T

/-- Chi-squared divergence `∫ (dμ/dν - 1)² dν` for `μ ≪ ν`, and `∞` otherwise. -/
def chiSqDiv {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (((μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν else ∞

/-- GAPS 104.44: the Poincaré inequality with constant `C` is equivalent to exponential decay at
rate `2/C` of the chi-squared divergence along every Langevin flow. -/
theorem poincareInequality_iff_chiSqDiv_langevin_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C) :
    (gibbsMeasure V).PoincareInequality C ↔
      ∀ μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)), IsLangevinFlow gradV μ → ∀ t ≥ 0,
        chiSqDiv (μ t) (gibbsMeasure V) ≤
          ENNReal.ofReal (Real.exp (-2 * t / C)) * chiSqDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- GAPS 104.44: the logarithmic Sobolev inequality with constant `C` is equivalent to exponential
decay at rate `2/C` of the relative entropy along every Langevin flow. -/
theorem logSobolevInequality_iff_klDiv_langevin_le {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C) :
    (gibbsMeasure V).LogSobolevInequality C ↔
      ∀ μ : ℝ → Measure (EuclideanSpace ℝ (Fin d)), IsLangevinFlow gradV μ → ∀ t ≥ 0,
        klDiv (μ t) (gibbsMeasure V) ≤
          ENNReal.ofReal (Real.exp (-2 * t / C)) * klDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- GAPS 104.44: under a logarithmic Sobolev inequality, the Otto–Villani inequality gives
`W₂²(μₜ, π) ≤ 2C e^{-2t/C} KL(μ₀‖π)` along every Langevin flow. -/
theorem wasserstein_sq_langevin_le_of_logSobolev {d : ℕ}
    (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hV : IsSamplingPotential V gradV β) (C : ℝ) (hC : 0 < C)
    (hLS : (gibbsMeasure V).LogSobolevInequality C)
    (μ : ℝ → Measure (EuclideanSpace ℝ (Fin d))) (hμ : IsLangevinFlow gradV μ) (t : ℝ)
    (ht : 0 ≤ t) :
    TauCeti.wassersteinEDist 2 (μ t) (gibbsMeasure V) ^ 2 ≤
      ENNReal.ofReal (2 * C * Real.exp (-2 * t / C)) * klDiv (μ 0) (gibbsMeasure V) := by
  sorry

/-- Second-order Taylor bound for `y log y` at `y = 1`:
`|(1+s) log(1+s) - s - s²/2| ≤ 4|s|³` for `|s| ≤ 1/2`. -/
theorem abs_one_add_mul_log_one_add_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(1 + s) * Real.log (1 + s) - s - s ^ 2 / 2| ≤ 4 * |s| ^ 3 := by
  have h1 : |-s| < 1 := by rw [abs_neg]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hlog
  norm_num at hlog
  set r := Real.log (1 + s) - s + s ^ 2 / 2 with hr
  have hr' : |r| ≤ 2 * |s| ^ 3 := by
    have hpos : (0 : ℝ) < 1 - |s| := by linarith
    have : |r| ≤ |s| ^ 3 / (1 - |s|) := by
      convert hlog using 2; rw [hr]; ring
    calc |r| ≤ |s| ^ 3 / (1 - |s|) := this
      _ ≤ |s| ^ 3 / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ = 2 * |s| ^ 3 := by ring
  have heq : (1 + s) * Real.log (1 + s) - s - s ^ 2 / 2 = -s ^ 3 / 2 + (1 + s) * r := by
    rw [hr]; ring
  rw [heq]
  calc |-s ^ 3 / 2 + (1 + s) * r| ≤ |s| ^ 3 / 2 + (3 / 2) * (2 * |s| ^ 3) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_div, abs_neg, abs_pow]; norm_num
        · rw [abs_mul]
          refine mul_le_mul ?_ hr' (abs_nonneg _) (by norm_num)
          calc |1 + s| ≤ |1| + |s| := abs_add_le _ _
            _ ≤ 3 / 2 := by rw [abs_one]; linarith
    _ ≤ 4 * |s| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg s) 3]

/-- A continuous function of a bounded continuous real function is integrable under a finite
measure. -/
theorem integrable_comp_of_abs_le {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] {g : E → ℝ} (hg : Continuous g)
    {G : ℝ} (hG : ∀ x, |g x| ≤ G) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun x ↦ F (g x)) μ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -G) (b := G)).exists_bound_of_continuousOn
    hF.continuousOn
  exact Integrable.of_bound (hF.comp hg).aestronglyMeasurable B
    (ae_of_all _ fun x ↦ hB _ (abs_le.1 (hG x)))

/-- A logarithmic Sobolev inequality with constant `C` gives the Poincaré bound with constant `C`
for bounded smooth test functions: apply it to `1 + εg` and expand the entropy to second order
in `ε`. -/
theorem variance_le_of_logSobolevInequality_of_abs_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {C : ℝ} (h : μ.LogSobolevInequality C) (g : E → ℝ)
    (hg : ContDiff ℝ ∞ g) (G : ℝ) (hG : ∀ x, |g x| ≤ G)
    (hdg : MemLp (fun x ↦ ‖fderiv ℝ g x‖) 2 μ) :
    ProbabilityTheory.variance g μ ≤ C * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂μ := by
  have hgc : Continuous g := hg.continuous
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  set G' := G + 1 with hG'
  have hG'0 : 0 < G' := by linarith
  set V := ProbabilityTheory.variance g μ with hV
  set D := ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂μ with hD
  have hint {F : ℝ → ℝ} (hF : Continuous F) : Integrable (fun x ↦ F (g x)) μ :=
    integrable_comp_of_abs_le μ hgc hG hF
  have key (ε : ℝ) (hε : 0 < ε) (hεG : ε * G' ≤ 1 / 6) :
      2 * ε ^ 2 * V - 220 * ε ^ 3 * G' ^ 3 ≤ 2 * C * (ε ^ 2 * D) := by
    set f : E → ℝ := fun x ↦ 1 + ε * g x with hf
    have hfn (x : E) : ‖fderiv ℝ f x‖ = ε * ‖fderiv ℝ g x‖ := by
      have hd : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
      simp only [hf]
      rw [fderiv_const_add, fderiv_const_mul hd, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hcont2 : Continuous fun y : ℝ ↦ (1 + ε * y) ^ 2 := by fun_prop
    have hLS := h.apply f (contDiff_const.add (contDiff_const.mul hg))
      (by simp_rw [hfn]; exact hdg.const_mul ε) (hint hcont2)
      (hint (Real.continuous_mul_log.comp hcont2))
    simp_rw [hfn, mul_pow] at hLS
    rw [integral_const_mul] at hLS
    refine le_trans ?_ hLS
    -- Second-order expansion of the entropy of `(1 + ε g)²`.
    set t : ℝ → ℝ := fun y ↦ 2 * ε * y + ε ^ 2 * y ^ 2 with ht
    have htc : Continuous t := by fun_prop
    set R : ℝ → ℝ := fun s ↦ (1 + s) * Real.log (1 + s) - s - s ^ 2 / 2 with hR
    have hRc : Continuous R := by
      have : Continuous fun s : ℝ ↦ (1 + s) * Real.log (1 + s) :=
        Real.continuous_mul_log.comp (by fun_prop)
      fun_prop
    set m1 := ∫ x, g x ∂μ with hm1
    set m2 := ∫ x, g x ^ 2 ∂μ with hm2
    set T := ∫ x, t (g x) ∂μ with hT
    have hTeq : T = 2 * ε * m1 + ε ^ 2 * m2 := by
      have i1 : Integrable (fun x ↦ 2 * ε * g x) μ := hint (F := fun y ↦ 2 * ε * y) (by fun_prop)
      have i2 : Integrable (fun x ↦ ε ^ 2 * g x ^ 2) μ :=
        hint (F := fun y ↦ ε ^ 2 * y ^ 2) (by fun_prop)
      simp only [hT, ht]
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    have hm1b : |m1| ≤ G := by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := G)
        (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hG x)
      simpa [Real.norm_eq_abs] using this
    have hy2 (x : E) : g x ^ 2 ≤ G ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hG x) 2
    have hm2b : 0 ≤ m2 ∧ m2 ≤ G ^ 2 := by
      refine ⟨integral_nonneg fun x ↦ sq_nonneg _, ?_⟩
      calc m2 ≤ ∫ _x, G ^ 2 ∂μ := integral_mono (hint (continuous_pow 2))
            (integrable_const _) hy2
        _ = G ^ 2 := by simp
    have htb (x : E) : |t (g x)| ≤ 3 * ε * G' := by
      have hgx := (hG x).trans (by linarith : G ≤ G')
      have h1 : |t (g x)| ≤ 2 * ε * |g x| + ε ^ 2 * |g x| ^ 2 := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        simp only [abs_mul, abs_pow, abs_of_pos hε, abs_two]
      have h3 : ε * |g x| ≤ ε * G' := mul_le_mul_of_nonneg_left hgx hε.le
      have h2 : ε * |g x| ≤ 1 := by linarith
      have h4 : (ε * |g x|) * (ε * |g x|) ≤ ε * |g x| :=
        mul_le_of_le_one_right (by positivity) h2
      calc |t (g x)| ≤ 2 * ε * |g x| + ε ^ 2 * |g x| ^ 2 := h1
        _ = 2 * (ε * |g x|) + (ε * |g x|) * (ε * |g x|) := by ring
        _ ≤ 3 * (ε * G') := by linarith
        _ = 3 * ε * G' := by ring
    have hTb : |T| ≤ 3 * ε * G' := by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x ↦ t (g x))
        (C := 3 * ε * G') (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using htb x)
      simpa [Real.norm_eq_abs] using this
    have hRb {s : ℝ} (hs : |s| ≤ 3 * ε * G') : |R s| ≤ 108 * ε ^ 3 * G' ^ 3 := by
      have := abs_one_add_mul_log_one_add_sub_le (s := s) (by linarith)
      calc |R s| ≤ 4 * |s| ^ 3 := this
        _ ≤ 4 * (3 * ε * G') ^ 3 := by gcongr
        _ = 108 * ε ^ 3 * G' ^ 3 := by ring
    set Q : ℝ → ℝ := fun y ↦ (t y - T) ^ 2 / 2 + R (t y) - R T with hQ
    have hQc : Continuous Q := by fun_prop
    have hpt (x : E) : f x ^ 2 * Real.log (f x ^ 2) - (1 + T) * Real.log (1 + T) =
        (1 + T) * (t (g x) - T) + Q (g x) := by
      have hfx : f x ^ 2 = 1 + t (g x) := by simp only [hf, ht]; ring
      rw [hfx]
      simp only [hQ, hR]
      ring
    have hent : MeasureTheory.Measure.entropy μ (fun x ↦ f x ^ 2) = ∫ x, Q (g x) ∂μ := by
      have hfint : ∫ x, f x ^ 2 ∂μ = 1 + T := by
        have : (fun x ↦ f x ^ 2) = fun x ↦ 1 + t (g x) := by
          funext x; simp only [hf, ht]; ring
        rw [this, integral_add (integrable_const _) (hint htc), integral_const]
        simp [hT]
      rw [MeasureTheory.Measure.entropy_def, hfint]
      have h1 : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ - (1 + T) * Real.log (1 + T) =
          ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - (1 + T) * Real.log (1 + T)) ∂μ := by
        have iL : Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ :=
          hint (F := fun y ↦ (1 + ε * y) ^ 2 * Real.log ((1 + ε * y) ^ 2))
            (Real.continuous_mul_log.comp hcont2)
        rw [integral_sub iL (integrable_const _), integral_const]
        simp
      rw [h1]
      simp_rw [hpt]
      have iA : Integrable (fun x ↦ (1 + T) * (t (g x) - T)) μ :=
        hint (F := fun y ↦ (1 + T) * (t y - T)) (by fun_prop)
      have iT : Integrable (fun x ↦ t (g x)) μ := hint htc
      rw [integral_add iA (hint hQc), integral_const_mul, integral_sub iT (integrable_const T),
        integral_const]
      simp [← hT]
    rw [hent]
    have hlow (x : E) : 2 * ε ^ 2 * (g x - m1) ^ 2 - 220 * ε ^ 3 * G' ^ 3 ≤ Q (g x) := by
      have hdiff : t (g x) - T = 2 * ε * (g x - m1) + ε ^ 2 * (g x ^ 2 - m2) := by
        rw [hTeq]; simp only [ht]; ring
      have ha : |2 * ε * (g x - m1)| ≤ 4 * ε * G' := by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos hε]
        have : |g x - m1| ≤ 2 * G' :=
          (abs_sub _ _).trans (by linarith [hG x, hm1b])
        nlinarith
      have hb : |ε ^ 2 * (g x ^ 2 - m2)| ≤ ε ^ 2 * G' ^ 2 := by
        rw [abs_mul, abs_pow, abs_of_pos hε]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [abs_le]
        constructor <;> nlinarith [hy2 x, hm2b.1, hm2b.2, sq_nonneg (g x)]
      have hR1 := hRb (htb x)
      have hR2 := hRb hTb
      have hsq : (2 * ε * (g x - m1)) ^ 2 / 2 - |2 * ε * (g x - m1)| *
          |ε ^ 2 * (g x ^ 2 - m2)| ≤ (t (g x) - T) ^ 2 / 2 := by
        rw [hdiff]
        set a := 2 * ε * (g x - m1)
        set b := ε ^ 2 * (g x ^ 2 - m2)
        have hab : -(|a| * |b|) ≤ a * b := by rw [← abs_mul]; exact neg_abs_le _
        have hexp : (a + b) ^ 2 / 2 = a ^ 2 / 2 + a * b + b ^ 2 / 2 := by ring
        rw [hexp]
        linarith [sq_nonneg b]
      have hprod : |2 * ε * (g x - m1)| * |ε ^ 2 * (g x ^ 2 - m2)| ≤
          4 * ε * G' * (ε ^ 2 * G' ^ 2) :=
        mul_le_mul ha hb (abs_nonneg _) (by positivity)
      simp only [hQ]
      rw [abs_le] at hR1 hR2
      nlinarith [hR1.1, hR2.2]
    have iV : Integrable (fun x ↦ (g x - m1) ^ 2) μ :=
      hint (F := fun y ↦ (y - m1) ^ 2) (by fun_prop)
    have iW : Integrable (fun x ↦ 2 * ε ^ 2 * (g x - m1) ^ 2 - 220 * ε ^ 3 * G' ^ 3) μ :=
      (iV.const_mul _).sub (integrable_const _)
    have hVeq : V = ∫ x, (g x - m1) ^ 2 ∂μ := by rw [hV, variance_eq_integral hgc.aemeasurable]
    calc 2 * ε ^ 2 * V - 220 * ε ^ 3 * G' ^ 3 =
          ∫ x, (2 * ε ^ 2 * (g x - m1) ^ 2 - 220 * ε ^ 3 * G' ^ 3) ∂μ := by
          rw [integral_sub (iV.const_mul _) (integrable_const _), integral_const_mul,
            integral_const, hVeq]
          simp
      _ ≤ ∫ x, Q (g x) ∂μ := integral_mono iW (hint hQc) hlow
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set ε := min (1 / (6 * G')) (δ / (110 * G' ^ 3)) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεG : ε * G' ≤ 1 / 6 := by
    calc ε * G' ≤ 1 / (6 * G') * G' := mul_le_mul_of_nonneg_right (min_le_left _ _) hG'0.le
      _ = 1 / 6 := by field_simp
  have hεδ : 110 * ε * G' ^ 3 ≤ δ := by
    calc 110 * ε * G' ^ 3 ≤ 110 * (δ / (110 * G' ^ 3)) * G' ^ 3 := by
          gcongr; exact min_le_right _ _
      _ = δ := by field_simp
  have := key ε hε hεG
  have hε2 : 0 < 2 * ε ^ 2 := by positivity
  have : V ≤ C * D + 110 * ε * G' ^ 3 := by
    have h' : 2 * ε ^ 2 * V ≤ 2 * ε ^ 2 * (C * D + 110 * ε * G' ^ 3) := by nlinarith
    exact le_of_mul_le_mul_left h' hε2
  linarith

/-- The truncations `R arctan(s/R)`, `R = n + 1`, converge to `s`. -/
theorem tendsto_mul_arctan_inv_mul (s : ℝ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * Real.arctan (((n : ℝ) + 1)⁻¹ * s)) atTop (𝓝 s) := by
  by_cases hs : s = 0
  · subst hs; simp
  have hslope := Real.hasDerivAt_arctan 0
  rw [hasDerivAt_iff_tendsto_slope] at hslope
  have hu0 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * s) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const s
    simpa [one_div] using this
  have hu : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * s) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hu0, Eventually.of_forall fun n ↦ by
      simp only [mem_compl_iff, mem_singleton_iff, mul_eq_zero, inv_eq_zero, not_or]
      exact ⟨by positivity, hs⟩⟩
  have hlim := (hslope.comp hu).const_mul s
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, div_one,
    mul_one] at hlim
  refine hlim.congr fun n ↦ ?_
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_apply, slope, sub_zero, Real.arctan_zero, smul_eq_mul, vsub_eq_sub]
  field_simp

/-- GAPS 104.44: a logarithmic Sobolev inequality implies the Poincaré inequality with the same
constant, for every probability measure on a real normed space. Unbounded test functions are
reduced to the bounded case `variance_le_of_logSobolevInequality_of_abs_le` through the
truncations `R arctan(f/R)` and dominated convergence. -/
theorem poincareInequality_of_logSobolevInequality {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (C : ℝ) (h : μ.LogSobolevInequality C) :
    μ.PoincareInequality C := by
  rw [MeasureTheory.Measure.PoincareInequality_def]
  intro f hf hfL hdf
  set R : ℕ → ℝ := fun n ↦ (n : ℝ) + 1 with hRdef
  have hR (n : ℕ) : 0 < R n := by simp only [hRdef]; positivity
  set g : ℕ → E → ℝ := fun n x ↦ R n * Real.arctan ((R n)⁻¹ * f x) with hgdef
  set w : ℕ → E → ℝ := fun n x ↦ 1 / (1 + ((R n)⁻¹ * f x) ^ 2) with hwdef
  have hw (n : ℕ) (x : E) : 0 < w n x ∧ w n x ≤ 1 := by
    simp only [hwdef]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg ((R n)⁻¹ * f x)]
  have hgs (n : ℕ) : ContDiff ℝ ∞ (g n) :=
    contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_const.mul hf))
  have hgd (n : ℕ) (x : E) : ‖fderiv ℝ (g n) x‖ = w n x * ‖fderiv ℝ f x‖ := by
    have hfx : HasFDerivAt f (fderiv ℝ f x) x :=
      (hf.differentiable (by simp) x).hasFDerivAt
    have h1 := ((Real.hasDerivAt_arctan ((R n)⁻¹ * f x)).comp_hasFDerivAt x
      (hfx.const_mul (R n)⁻¹)).const_mul (R n)
    rw [show fderiv ℝ (g n) x = _ from h1.fderiv, smul_smul, smul_smul, norm_smul,
      Real.norm_eq_abs]
    congr 1
    have hRn := (hR n).ne'
    rw [show R n * (1 / (1 + ((R n)⁻¹ * f x) ^ 2)) * (R n)⁻¹ = w n x by
      simp only [hwdef]; field_simp]
    exact abs_of_pos (hw n x).1
  have hgb (n : ℕ) (x : E) : |g n x| ≤ R n * (Real.pi / 2) := by
    simp only [hgdef, abs_mul, abs_of_pos (hR n)]
    refine mul_le_mul_of_nonneg_left ?_ (hR n).le
    rw [abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hgf (n : ℕ) (x : E) : |g n x| ≤ |f x| := by
    simp only [hgdef, abs_mul, abs_of_pos (hR n)]
    calc R n * |Real.arctan ((R n)⁻¹ * f x)| ≤ R n * |(R n)⁻¹ * f x| :=
          mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs (hR n).le
      _ = |f x| := by
          rw [abs_mul, abs_inv, abs_of_pos (hR n), ← mul_assoc, mul_inv_cancel₀ (hR n).ne',
            one_mul]
  have hdgL (n : ℕ) : MemLp (fun x ↦ ‖fderiv ℝ (g n) x‖) 2 μ := by
    refine hdf.of_le ((hgs n).continuous_fderiv (by simp)).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp only [norm_norm, hgd]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n x).1.le (norm_nonneg _))]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw n x).2
  have hstep (n : ℕ) := variance_le_of_logSobolevInequality_of_abs_le μ h (g n) (hgs n) _
    (hgb n) (hdgL n)
  -- Pass to the limit on both sides by dominated convergence.
  have hgL (n : ℕ) : MemLp (g n) 2 μ :=
    MemLp.of_bound (hgs n).continuous.aestronglyMeasurable (R n * (Real.pi / 2))
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hgb n x)
  have hgx (x : E) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) :=
    tendsto_mul_arctan_inv_mul (f x)
  have hwx (x : E) : Tendsto (fun n ↦ w n x) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ ↦ (R n)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [one_div] at this
      exact this
    have := ((hinv.mul_const (f x)).pow 2).const_add 1
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at this
    simpa [hwdef] using this.inv₀ one_ne_zero
  have hfint : Integrable f μ := hfL.integrable one_le_two
  have hlim1 : Tendsto (fun n ↦ ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ |f x|)
      (fun n ↦ (hgs n).continuous.aestronglyMeasurable) hfint.abs
      (fun n ↦ ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hgf n x)
      (ae_of_all _ hgx)
  have hlim2 : Tendsto (fun n ↦ ∫ x, g n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ f x ^ 2)
      (fun n ↦ ((hgs n).continuous.pow 2).aestronglyMeasurable) hfL.integrable_sq
      (fun n ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_pow, ← sq_abs (f x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgf n x) 2)
      (ae_of_all _ fun x ↦ (hgx x).pow 2)
  have hlimV : Tendsto (fun n ↦ ProbabilityTheory.variance (g n) μ) atTop
      (𝓝 (ProbabilityTheory.variance f μ)) := by
    simp_rw [variance_eq_sub (hgL _), variance_eq_sub hfL]
    simpa [Pi.pow_apply] using hlim2.sub (hlim1.pow 2)
  have hlimD : Tendsto (fun n ↦ ∫ x, ‖fderiv ℝ (g n) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)) := by
    simp_rw [hgd]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖fderiv ℝ f x‖ ^ 2)
      (fun n ↦ ?_) hdf.integrable_sq (fun n ↦ ae_of_all _ fun x ↦ ?_)
      (ae_of_all _ fun x ↦ ?_)
    · simp_rw [← hgd]
      exact (((hgs n).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos (hw n x).1, abs_norm, mul_pow]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (hw n x).1.le (hw n x).2)
    · simpa using ((hwx x).mul_const ‖fderiv ℝ f x‖).pow 2
  exact le_of_tendsto_of_tendsto' hlimV (hlimD.const_mul C) hstep

/-- Quadratic lower bound from a strongly monotone gradient:
`V x ≥ V 0 + ⟪∇V(0), x⟫ + (α/2) ‖x‖²`. -/
theorem add_inner_add_le_of_isStronglyMonotoneGradient {d : ℕ}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    {gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {α : ℝ}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x) (hα : IsStronglyMonotoneGradient gradV α)
    (x : EuclideanSpace ℝ (Fin d)) :
    V 0 + inner ℝ (gradV 0) x + α / 2 * ‖x‖ ^ 2 ≤ V x := by
  set φ : ℝ → ℝ := fun t ↦
    V (t • x) - V 0 - t * inner ℝ (gradV 0) x - α / 2 * t ^ 2 * ‖x‖ ^ 2 with hφ
  have hd (t : ℝ) : HasDerivAt φ
      (inner ℝ (gradV (t • x)) x - inner ℝ (gradV 0) x - α * t * ‖x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ V (s • x)) (inner ℝ (gradV (t • x)) x) t := by
      have := (hgrad (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
      simp only [id, one_smul, InnerProductSpace.toDual_apply_apply] at this
      exact this
    have h2 := ((h1.sub_const (V 0)).sub ((hasDerivAt_id t).mul_const (inner ℝ (gradV 0) x))).sub
      (((hasDerivAt_pow 2 t).const_mul (α / 2)).mul_const (‖x‖ ^ 2))
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s ↦ rfl)
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, one_mul]
    ring
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    have h := hα (t • x) 0
    simp only [sub_zero] at h
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      mul_pow, inner_sub_left] at h
    have : α * t * ‖x‖ ^ 2 ≤ inner ℝ (gradV (t • x)) x - inner ℝ (gradV 0) x := by
      refine le_of_mul_le_mul_left ?_ ht
      calc t * (α * t * ‖x‖ ^ 2) = α * (t ^ 2 * ‖x‖ ^ 2) := by ring
        _ ≤ _ := h
    linarith
  have h01 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_le_one
  simp only [hφ, zero_smul, zero_mul, one_smul, one_mul, sub_self, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h01
  linarith

/-- For a potential with a strongly monotone gradient (`∇²V ⪰ αI` with `α > 0`), the Gibbs
density `e^{-V}` is integrable, by the quadratic lower bound
`add_inner_add_le_of_isStronglyMonotoneGradient` and Gaussian integrability. -/
theorem integrable_exp_neg_of_isStronglyMonotoneGradient {d : ℕ}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    {gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {α : ℝ}
    (hgrad : ∀ x, HasGradientAt V (gradV x) x) (hα : IsStronglyMonotoneGradient gradV α)
    (hα0 : 0 < α) : Integrable (fun x ↦ Real.exp (-V x)) := by
  have hG := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := ((α / 2 : ℝ) : ℂ)) (by simpa using half_pos hα0)
    (-1) (gradV 0)
  have hG' : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      Real.exp (-(α / 2) * ‖x‖ ^ 2 - inner ℝ (gradV 0) x)) := by
    refine hG.norm.congr (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, Complex.one_re, Complex.one_im, ← Complex.ofReal_pow]
    ring
  have hVc : Continuous V :=
    continuous_iff_continuousAt.2 fun x ↦ (hgrad x).hasFDerivAt.continuousAt
  refine (hG'.const_mul (Real.exp (-V 0))).mono' (hVc.neg.rexp.aestronglyMeasurable)
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := add_inner_add_le_of_isStronglyMonotoneGradient hgrad hα x
  linarith

/-- GAPS 104.44: Bakry–Émery and Holley–Stroock. If `V = V₀ + ψ` with `∇²V₀ ⪰ mI`, `m > 0`, and
`a ≤ ψ ≤ b`, then the Gibbs law satisfies the logarithmic Sobolev inequality with constant
`e^{b-a}/m`. -/
theorem logSobolevInequality_gibbsMeasure_of_bounded_perturbation {d : ℕ}
    (V₀ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m a b : ℝ) (hm : 0 < m)
    (hV₀ : ContDiff ℝ 2 V₀) (hgrad : ∀ x, HasGradientAt V₀ (gradV₀ x) x)
    (hconv : IsStronglyMonotoneGradient gradV₀ m) (hψ : Measurable ψ)
    (hab : ∀ x, ψ x ∈ Icc a b) :
    (gibbsMeasure (V₀ + ψ)).LogSobolevInequality (Real.exp (b - a) / m) := by
  sorry

/-- GAPS 104.44: under the hypotheses of the Bakry–Émery and Holley–Stroock theorem, the Gibbs law
of `V₀ + ψ` satisfies the Poincaré inequality with constant `e^{b-a}/m`. It follows from the
logarithmic Sobolev inequality `logSobolevInequality_gibbsMeasure_of_bounded_perturbation`. -/
theorem poincareInequality_gibbsMeasure_of_bounded_perturbation {d : ℕ}
    (V₀ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (m a b : ℝ) (hm : 0 < m)
    (hV₀ : ContDiff ℝ 2 V₀) (hgrad : ∀ x, HasGradientAt V₀ (gradV₀ x) x)
    (hconv : IsStronglyMonotoneGradient gradV₀ m) (hψ : Measurable ψ)
    (hab : ∀ x, ψ x ∈ Icc a b) :
    (gibbsMeasure (V₀ + ψ)).PoincareInequality (Real.exp (b - a) / m) := by
  have hint : Integrable (fun x ↦ Real.exp (-(V₀ + ψ) x)) := by
    refine ((integrable_exp_neg_of_isStronglyMonotoneGradient hgrad hconv hm).const_mul
      (Real.exp (-a))).mono' ((hV₀.continuous.measurable.add hψ).neg.exp.aestronglyMeasurable)
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Pi.add_apply]
    exact Real.exp_le_exp.2 (by linarith [(hab x).1])
  have := isProbabilityMeasure_gibbsMeasure hint
  exact poincareInequality_of_logSobolevInequality _ _
    (logSobolevInequality_gibbsMeasure_of_bounded_perturbation V₀ ψ gradV₀ m a b hm hV₀ hgrad
      hconv hψ hab)

/-- The underlying measure of a law in the Wasserstein space `P₂(ℝᵈ)`. -/
def wassersteinLaw {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  ((ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)))

/-- Free energy `∫ ρ log ρ + ∫ V dρ` on the Wasserstein space, with the entropy relative to
Lebesgue measure; it is `⊤` for laws without a density. -/
def jkoFreeEnergy {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d))) : EReal :=
  TauCeti.boltzmannEntropy volume (wassersteinLaw ν) + TauCeti.potentialEnergy V (wassersteinLaw ν)

/-- Real Lebesgue density of the absolutely continuous part of a Wasserstein law.
This represents the whole law when that law is absolutely continuous with respect to volume. -/
def wassersteinDensity {d : ℕ} (ν : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((wassersteinLaw ν).rnDeriv volume x).toReal

/-- GAPS 104.43: the Jordan–Kinderlehrer–Otto theorem. Every JKO step for the free energy has a
unique minimizer, and the piecewise-constant interpolations converge, weakly in `L¹` at every time
and strongly in `L¹((0,T) × ℝᵈ)`, to a weak solution of `∂ₜρ = Δρ + ∇·(ρ∇V)` with datum `ρ₀`.
Uniqueness of the limiting weak solution is not part of this statement. -/
theorem jko_scheme_tendsto_fokkerPlanck {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hV : ContDiff ℝ ⊤ V) (hV0 : ∀ x, 0 ≤ V x) (C : ℝ)
    (hgrowth : ∀ x, ‖gradient V x‖ ≤ C * (V x + 1))
    (ρ₀ : TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)))
    (hF : jkoFreeEnergy V ρ₀ ≠ ⊤) :
    (∀ τ : ℝ≥0, 0 < τ → ∀ μ, ∃! ν, ν ∈ TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ μ) ∧
      ∃ ρ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ T ≥ 0, IsFokkerPlanckSolution
          (fun t ↦ volume.withDensity fun x ↦ ENNReal.ofReal (ρ t x))
          (fun _ x ↦ -gradient V x) (fun _ _ ↦ (2 : ℝ) • 1) T) ∧
        (∀ᵐ x, ρ 0 x = wassersteinDensity ρ₀ x) ∧
        ∀ seq : ℝ≥0 → ℕ → TauCeti.WassersteinSpace 2 (EuclideanSpace ℝ (Fin d)),
          (∀ τ, 0 < τ → seq τ 0 = ρ₀ ∧
            ∀ k, seq τ (k + 1) ∈ TauCeti.moreauYosidaResolvent (jkoFreeEnergy V) τ (seq τ k)) →
          (∀ t : ℝ, 0 ≤ t → ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g →
            (∃ M, ∀ x, |g x| ≤ M) →
            Tendsto (fun τ : ℝ≥0 ↦ ∫ x, g x ∂wassersteinLaw (seq τ ⌊t / (τ : ℝ)⌋₊))
              (𝓝[>] 0) (𝓝 (∫ x, g x * ρ t x))) ∧
          ∀ T : ℝ, 0 < T → Tendsto (fun τ : ℝ≥0 ↦ ∫⁻ t in Ioo (0 : ℝ) T, ∫⁻ x,
              ENNReal.ofReal |wassersteinDensity (seq τ ⌊t / (τ : ℝ)⌋₊) x - ρ t x|)
            (𝓝[>] 0) (𝓝 0) := by
  sorry

end CKSD
