module

public import CKSD.Bayes.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import CKSD.Nonparametric.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.BenamouBrenier
public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.PlanInterpolation
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Langevin dynamics: invariance, contraction, entropy decay, and score matching

Deterministic and integral identities underlying Langevin sampling and score-based generative
models.

## Main results

* `CKSD.integral_langevin_generator_eq_zero`: the Gibbs law `e^{-V}/Z` on `ℝ` is invariant for the
  scalar Langevin generator `f'' - V' f'` on compactly supported test functions (GAPS 104.37).
* `CKSD.dist_synchronous_langevin_le_exp`: two solutions of `dX = b(X) dt + dW` driven by the same
  noise contract at rate `m` when `b` is `m`-monotone, `⟪b x - b y, x - y⟫ ≥ m ‖x - y‖²`
  (GAPS 104.38).
* `CKSD.le_exp_neg_mul_of_hasDerivAt_neg_of_two_mul_le`: the Grönwall step behind exponential
  entropy decay: `E' = -I` and `2m E ≤ I` give `E t ≤ e^{-2mt} E 0` (GAPS 104.41).
* `CKSD.integral_sq_sub_score_div_two_eq`: Hyvärinen's score-matching identity (GAPS 104.64).
* `CKSD.wasserstein_le_barycentric_velocity_action`: the barycentric velocity of a straight
  coupling has kinetic action between `W₂²` of the marginals and the transport cost of the
  coupling (SYNOPSIS 104.72).

The barycentric action bound uses TauCeti's displacement interpolation and Benamou–Brenier lower
bound, with Mathlib's conditional-expectation uniqueness and Jensen inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 104.37: invariance of the Gibbs law for the scalar Langevin generator. For a `C¹`
potential `V` and a compactly supported `C²` test function `f`,
`∫ (f'' - V' f') e^{-V} / Z = 0` with `Z = ∫ e^{-V}`. The identity holds for the unnormalized
weight `e^{-V}`, so it needs no integrability of `e^{-V}`. -/
theorem integral_langevin_generator_eq_zero (V f : ℝ → ℝ) (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, (deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x) /
      ∫ y, Real.exp (-V y)) = 0 := by
  let F : ℝ → ℝ := deriv f * (fun x ↦ Real.exp (-V x))
  have hF : ContDiff ℝ 1 F := hf.deriv'.mul hV.neg.exp
  have hFc : HasCompactSupport F := hfc.deriv.mul_right
  have hder (x : ℝ) : HasDerivAt F
      ((deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x)) x := by
    have hd := (hf.differentiable_deriv_two x).hasDerivAt.mul
      ((hV.differentiable (by norm_num) x).hasDerivAt.neg.exp)
    convert hd using 1; simp only [Pi.neg_apply]; ring
  have hiF : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have hidi : Integrable (fun x ↦
      (deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x)) := by
    have hdFi : Integrable (deriv F) :=
      hF.continuous_deriv_one.integrable_of_hasCompactSupport hFc.deriv
    convert hdFi using 1
    funext x
    exact (hder x).deriv.symm
  rw [integral_div, integral_eq_zero_of_hasDerivAt_of_integrable hder hidi hiF, zero_div]

/-- GAPS 104.38: synchronous coupling. If `x` and `y` solve `x t = x 0 - ∫₀ᵗ b(x s) ds + W t`
with the same continuous forcing `W` (so that their difference solves the integral equation below)
and `⟪b x - b y, x - y⟫ ≥ m ‖x - y‖²`, then `‖x t - y t‖ ≤ e^{-mt} ‖x 0 - y 0‖`. The coefficient `m`
may be any real number; `m > 0` gives contraction. -/
theorem dist_synchronous_langevin_le_exp {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hb : Continuous b)
    (m : ℝ)
    (hmono : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (b x - b y) (x - y))
    (x y : ℝ → EuclideanSpace ℝ (Fin d)) (hx : Continuous x) (hy : Continuous y)
    (heq : ∀ t ≥ 0, x t - y t = x 0 - y 0 - ∫ s in (0 : ℝ)..t, b (x s) - b (y s)) :
    ∀ t ≥ 0, ‖x t - y t‖ ≤ Real.exp (-m * t) * ‖x 0 - y 0‖ := by
  set G : ℝ → EuclideanSpace ℝ (Fin d) := fun s ↦ b (x s) - b (y s) with hGdef
  have hG : Continuous G := (hb.comp hx).sub (hb.comp hy)
  have hΔc : Continuous fun t ↦ x t - y t := hx.sub hy
  -- For positive times the difference solves `Δ' = -(b(x) - b(y))`.
  have hΔd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u ↦ x u - y u) (-G t) t := by
    have hI := (hG.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hD : HasDerivAt (fun u ↦ x 0 - y 0 - ∫ s in (0 : ℝ)..u, G s) (-G t) t := by
      simpa using hI.const_sub (x 0 - y 0)
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with u hu
    exact heq u hu.le
  set E : ℝ → ℝ := fun t ↦ ‖x t - y t‖ ^ 2 with hEdef
  set F : ℝ → ℝ := fun t ↦ Real.exp (2 * m * t) * E t with hFdef
  have hFd (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (Real.exp (2 * m * t) * (2 * m) * E t +
        Real.exp (2 * m * t) * (2 * inner ℝ (x t - y t) (-G t))) t := by
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp (2 * m * s))
        (Real.exp (2 * m * t) * (2 * m)) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * m)).exp
    exact he.mul (hΔd t ht).norm_sq
  have hFc : ContinuousOn F (Ici 0) :=
    ((by fun_prop : Continuous fun s : ℝ ↦ Real.exp (2 * m * s)).mul
      (hΔc.norm.pow 2)).continuousOn
  have hanti : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hFc
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact (hFd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      rw [(hFd t ht').deriv]
      have hmono' := hmono (x t) (y t)
      have hin : inner ℝ (x t - y t) (-G t) = -inner ℝ (b (x t) - b (y t)) (x t - y t) := by
        rw [inner_neg_right, real_inner_comm]
      rw [hin]
      have hexp := Real.exp_pos (2 * m * t)
      have : E t = ‖x t - y t‖ ^ 2 := rfl
      nlinarith
  intro t ht
  have hbound : Real.exp (2 * m * t) * ‖x t - y t‖ ^ 2 ≤ ‖x 0 - y 0‖ ^ 2 := by
    simpa [F, E] using hanti (by simp : (0 : ℝ) ∈ Ici 0) ht ht
  have hsq : ‖x t - y t‖ ^ 2 ≤ (Real.exp (-m * t) * ‖x 0 - y 0‖) ^ 2 := by
    have hsplit : Real.exp (2 * m * t) = Real.exp (m * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hinv : Real.exp (-m * t) * Real.exp (m * t) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    rw [hsplit] at hbound
    have h2 : (Real.exp (-m * t) * ‖x 0 - y 0‖) ^ 2 =
        Real.exp (-m * t) ^ 2 * ‖x 0 - y 0‖ ^ 2 := by ring
    rw [h2]
    calc ‖x t - y t‖ ^ 2 = (Real.exp (-m * t) * Real.exp (m * t)) ^ 2 * ‖x t - y t‖ ^ 2 := by
          rw [hinv]; ring
      _ = Real.exp (-m * t) ^ 2 * (Real.exp (m * t) ^ 2 * ‖x t - y t‖ ^ 2) := by ring
      _ ≤ Real.exp (-m * t) ^ 2 * ‖x 0 - y 0‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- GAPS 104.41: the Grönwall step of exponential entropy decay. If `E` is continuous on `[0, ∞)`
with `E' = -I` on `(0, ∞)` (dissipation of relative entropy by Fisher information) and
`2m E ≤ I` (a logarithmic Sobolev inequality), then `E t ≤ e^{-2mt} E 0` for `t ≥ 0`. The
coefficient `m` may be any real number. -/
theorem le_exp_neg_mul_of_hasDerivAt_neg_of_two_mul_le (E I : ℝ → ℝ) (m : ℝ)
    (hE : ContinuousOn E (Ici 0))
    (hder : ∀ t > 0, HasDerivAt E (-I t) t)
    (hlsi : ∀ t > 0, 2 * m * E t ≤ I t) :
    ∀ t ≥ 0, E t ≤ Real.exp (-2 * m * t) * E 0 := by
  let F : ℝ → ℝ := (fun t ↦ Real.exp (2 * m * t)) * E
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt F (Real.exp (2 * m * t) * (2 * m * E t - I t)) t := by
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp (2 * m * s))
        (Real.exp (2 * m * t) * (2 * m)) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * m)).exp
    convert he.mul (hder t ht) using 1; ring
  have hcont : Continuous (fun t : ℝ ↦ Real.exp (2 * m * t)) := by fun_prop
  have hanti : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (f := F) (convex_Ici 0) (hcont.continuousOn.mul hE)
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact (hd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      rw [(hd t ht').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hlsi t ht'])
  intro t ht
  have hbound : Real.exp (2 * m * t) * E t ≤ E 0 := by
    simpa [F, Pi.mul_apply] using hanti (by simp : (0 : ℝ) ∈ Ici 0) ht ht
  have hscaled := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-2 * m * t)).le
  have hcancel : Real.exp (-2 * m * t) * Real.exp (2 * m * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1; ring
  rwa [← mul_assoc, hcancel, one_mul] at hscaled

/-- GAPS 104.64: Hyvärinen's score-matching identity on `ℝ`. For a positive `C¹` density `p` with
square-integrable score `p'/p` and a compactly supported `C¹` candidate score `g`,
`𝔼[(g - p'/p)²/2] = 𝔼[g²/2 + g'] + 𝔼[(p'/p)²/2]`, so the score-matching risk is minimized
without knowledge of `p'/p`. -/
theorem integral_sq_sub_score_div_two_eq (P : Measure ℝ) [IsProbabilityMeasure P] (p g : ℝ → ℝ)
    (hp : HasDensity P volume p) (hpos : ∀ x, 0 < p x)
    (hp1 : ContDiff ℝ 1 p) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hscore : Integrable (fun x ↦ (deriv p x / p x) ^ 2) P) :
    (∫ x, (g x - deriv p x / p x) ^ 2 / 2 ∂P) =
      (∫ x, g x ^ 2 / 2 + deriv g x ∂P) +
        ∫ x, (deriv p x / p x) ^ 2 / 2 ∂P := by
  obtain ⟨hpm, -, hP⟩ := hp
  set s : ℝ → ℝ := fun x ↦ deriv p x / p x with hs
  have hgcont : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hp'c : Continuous (deriv p) := hp1.continuous_deriv le_rfl
  obtain ⟨Cg, hCg⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨Cd, hCd⟩ := hg'c.bounded_above_of_compact_support hgc.deriv
  have hsm : Measurable s := (measurable_deriv p).div hpm
  -- Integrability of the three pieces.
  have hA : Integrable (fun x ↦ g x ^ 2 / 2 + deriv g x) P := by
    refine Integrable.of_bound (((hgcont.pow 2).div_const 2).add hg'c).aestronglyMeasurable
      (Cg ^ 2 / 2 + Cd) (ae_of_all _ fun x ↦ ?_)
    have h1 := hCg x
    have h2 := hCd x
    rw [Real.norm_eq_abs] at h1 h2 ⊢
    have h0 : 0 ≤ Cg := (abs_nonneg _).trans h1
    have hsq : g x ^ 2 ≤ Cg ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc |g x ^ 2 / 2 + deriv g x| ≤ |g x ^ 2 / 2| + |deriv g x| := abs_add_le _ _
      _ ≤ Cg ^ 2 / 2 + Cd := by
        rw [abs_of_nonneg (by positivity)]
        linarith
  have hB : Integrable (fun x ↦ s x ^ 2 / 2) P := hscore.div_const 2
  have hs1 : Integrable s P := by
    refine ((integrable_const (1 : ℝ)).add hscore).div_const 2 |>.mono'
      hsm.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    have : 0 ≤ (|s x| - 1) ^ 2 := sq_nonneg _
    have hsq : |s x| ^ 2 = s x ^ 2 := sq_abs _
    simp only [Pi.add_apply]
    nlinarith
  have hC : Integrable (fun x ↦ g x * s x + deriv g x) P := by
    refine Integrable.add ?_
      (Integrable.of_bound hg'c.aestronglyMeasurable Cd (ae_of_all _ hCd))
    refine (hs1.abs.const_mul Cg).mono' (hgcont.measurable.mul hsm).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCg x) (abs_nonneg _)
  -- The cross term integrates to zero by integration by parts against the density.
  have hcross : ∫ x, (g x * s x + deriv g x) ∂P = 0 := by
    rw [hP, integral_withDensity_eq_integral_toReal_smul hpm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    have hpt (x : ℝ) : (ENNReal.ofReal (p x)).toReal • (g x * s x + deriv g x) =
        (deriv g * p + g * deriv p) x := by
      rw [ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
      simp only [hs, Pi.add_apply, Pi.mul_apply]
      field_simp [(hpos x).ne']
      ring
    simp_rw [hpt]
    have hder (x : ℝ) : HasDerivAt (g * p) ((deriv g * p + g * deriv p) x) x := by
      have := (hg.differentiable one_ne_zero x).hasDerivAt.mul
        (hp1.differentiable one_ne_zero x).hasDerivAt
      simpa [Pi.add_apply, Pi.mul_apply] using this
    refine integral_eq_zero_of_hasDerivAt_of_integrable hder ?_ ?_
    · exact ((hg'c.mul hp1.continuous).add (hgcont.mul hp'c)).integrable_of_hasCompactSupport
        (hgc.deriv.mul_right.add hgc.mul_right)
    · exact (hgcont.mul hp1.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have hpt (x : ℝ) : (g x - deriv p x / p x) ^ 2 / 2 =
      (g x ^ 2 / 2 + deriv g x) + s x ^ 2 / 2 - (g x * s x + deriv g x) := by
    simp only [hs]; ring
  simp_rw [hpt]
  have hsplit := integral_sub (hA.add hB) hC
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add hA hB, hcross, sub_zero]

/-- Slice conditional expectations give the conditional expectation on the product space: if
`v t (X t ·)` is a version of `𝔼[W | X t]` for `ρ`-almost every `t`, then `(t, ω) ↦ v t (X t ω)` is
a version of `𝔼[W | (t, X t)]` under `ρ ⊗ π`. -/
theorem condExp_prod_of_condExp_slices
    {T Ω Y E : Type*} [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ρ : Measure T) [IsFiniteMeasure ρ] (π : Measure Ω) [IsFiniteMeasure π]
    (X : T → Ω → Y) (hX : Measurable (Function.uncurry X))
    (v : T → Y → E) (hv : Measurable (Function.uncurry v))
    (W : Ω → E) (hW : Integrable W π)
    (hc : ∀ᵐ t ∂ρ, (fun ω ↦ v t (X t ω)) =ᵐ[π]
      π[W | MeasurableSpace.comap (X t) inferInstance]) :
    (fun q : T × Ω ↦ v q.1 (X q.1 q.2)) =ᵐ[ρ.prod π]
      (ρ.prod π)[fun q ↦ W q.2 |
        MeasurableSpace.comap (fun q : T × Ω ↦ (q.1, X q.1 q.2)) inferInstance] := by
  let G : T × Ω → T × Y := fun q ↦ (q.1, X q.1 q.2)
  have hG : Measurable G := measurable_fst.prodMk hX
  have hU : Measurable fun q : T × Ω ↦ v q.1 (X q.1 q.2) := hv.comp hG
  have hUint : Integrable (fun q : T × Ω ↦ v q.1 (X q.1 q.2)) (ρ.prod π) := by
    refine (integrable_prod_iff hU.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hc] with t ht
      exact integrable_condExp.congr ht.symm
    · refine (integrable_const (∫ ω, ‖W ω‖ ∂π)).mono'
        hU.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable ?_
      filter_upwards [hc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      calc (∫ ω, ‖v t (X t ω)‖ ∂π) = ∫ ω, ‖π[W | MeasurableSpace.comap (X t) inferInstance] ω‖ ∂π :=
          integral_congr_ae (ht.fun_comp norm)
        _ ≤ ∫ ω, ‖W ω‖ ∂π := integral_norm_condExp_le W
  have hGm : Measurable[MeasurableSpace.comap G inferInstance] G :=
    Measurable.of_comap_le le_rfl
  apply ae_eq_condExp_of_forall_setIntegral_eq hG.comap_le (hW.comp_snd ρ)
    (fun s _ _ ↦ hUint.integrableOn) ?_
    (hv.stronglyMeasurable.comp_measurable hGm).aestronglyMeasurable
  intro s hs _
  obtain ⟨A, hA, rfl⟩ := hs
  rw [← integral_indicator (hG hA), ← integral_indicator (hG hA),
    integral_prod _ (hUint.indicator (hG hA)),
    integral_prod _ ((hW.comp_snd ρ).indicator (hG hA))]
  apply integral_congr_ae
  filter_upwards [hc] with t ht
  have hAt : MeasurableSet[MeasurableSpace.comap (X t) inferInstance]
      {ω | (t, X t ω) ∈ A} := by
    exact ⟨(fun y ↦ (t, y)) ⁻¹' A, measurable_prodMk_left hA, rfl⟩
  have hXt : Measurable (X t) := hX.comp measurable_prodMk_left
  have hAt' := hXt.comap_le _ hAt
  change (∫ ω, ({ω | (t, X t ω) ∈ A}.indicator (fun ω ↦ v t (X t ω))) ω ∂π) =
    ∫ ω, ({ω | (t, X t ω) ∈ A}.indicator W) ω ∂π
  rw [integral_indicator hAt', integral_indicator hAt',
    setIntegral_congr_ae hAt' (ht.mono fun ω hω _ ↦ hω),
    setIntegral_condExp hXt.comap_le hW hAt]

/-- SYNOPSIS 104.72: action bounds for the barycentric velocity of a straight coupling. For a
coupling `π` with finite second moment and `X_t = (1 - t) X₀ + t X₁`, if `v t (X_t)` is a version
of `𝔼[X₁ - X₀ | X_t]` for every `t ∈ [0, 1]`, then
`W₂²(π₀, π₁) ≤ ∫₀¹ 𝔼‖v t (X_t)‖² dt ≤ 𝔼‖X₁ - X₀‖²`. -/
theorem wasserstein_le_barycentric_velocity_action {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure π] (h2 : MemLp id 2 π)
    (v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hv : Measurable (Function.uncurry v)) :
    let Xt := fun t (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      (1 - t) • z.1 + t • z.2;
    ∀ (_hcond : ∀ t ∈ Icc (0 : ℝ) 1,
      (fun z ↦ v t (Xt t z)) =ᵐ[π]
        π[(fun z ↦ z.2 - z.1) | (inferInstance : MeasurableSpace
          (EuclideanSpace ℝ (Fin d))).comap (Xt t)]),
    (TauCeti.wassersteinEDist 2 (π.map Prod.fst) (π.map Prod.snd)).toReal ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π ∧
    (∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) ≤
      ∫ z, ‖z.2 - z.1‖ ^ 2 ∂π := by
  intro Xt hcond
  let ρ := volume.restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
  have hXt : Measurable (Function.uncurry Xt) := by fun_prop
  have hW2 : MemLp (fun z ↦ z.2 - z.1) 2 π := h2.snd.sub h2.fst
  have hW : Integrable (fun z ↦ z.2 - z.1) π := hW2.integrable (by norm_num)
  have hc : ∀ᵐ t ∂ρ, (fun z ↦ v t (Xt t z)) =ᵐ[π]
      π[(fun z ↦ z.2 - z.1) | MeasurableSpace.comap (Xt t) inferInstance] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hcond t ⟨ht.1.le, ht.2.le⟩
  -- Identify the supplied slice-wise conditional velocity with TauCeti's space-time version.
  have hprod := condExp_prod_of_condExp_slices ρ π Xt hXt v hv _ hW hc
  obtain ⟨u, hce, hcu, _⟩ :=
    TauCeti.exists_isContinuityEquation_map_smul_fst_add_smul_snd π
      (by simpa only [← hasFiniteIntegral_iff_enorm] using hW.2)
  have heq : ∀ᵐ q : ℝ × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ∂ρ.prod π,
      u q.1 (Xt q.1 q.2) = v q.1 (Xt q.1 q.2) := by
    change (fun q ↦ u q.1 (Xt q.1 q.2)) =ᵐ[ρ.prod π] _
    exact (Filter.EventuallyEq.of_eq hcu).trans hprod.symm
  have hce' : TauCeti.IsContinuityEquation (fun t ↦ π.map (Xt t)) v 0 1 := by
    apply hce.congr hv
    rw [← ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [Measure.ae_ae_of_ae_prod heq] with t ht
    exact (ae_map_iff (by fun_prop : AEMeasurable (Xt t) π)
      (measurableSet_eq_fun (hce.measurable_velocity.comp measurable_prodMk_left)
        (hv.comp measurable_prodMk_left))).2 ht
  let P : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    ⟨π, inferInstance⟩
  let ν : ℝ → FiniteMeasure (EuclideanSpace ℝ (Fin d)) := fun t ↦
    (P.map (Xt t)).toFiniteMeasure
  have hν (t : ℝ) : (ν t : Measure (EuclideanSpace ℝ (Fin d))) = π.map (Xt t) := by
    rw [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
  -- Narrow continuity, as in TauCeti.isLeast_lintegral_isContinuityEquation.
  have hνc : Continuous ν := ProbabilityMeasure.toFiniteMeasure_continuous.comp
    (P.continuous_map_of_forall_continuous (fun _ ↦ by fun_prop) fun _ ↦ by fun_prop)
  have hceν : TauCeti.IsContinuityEquation (fun t ↦ (ν t : Measure _)) v 0 1 := by
    simpa only [hν] using hce'
  have : IsProbabilityMeasure (ν 0 : Measure (EuclideanSpace ℝ (Fin d))) := by rw [hν]; infer_instance
  have hlow := hceν.wassersteinEDist_rpow_le hνc.continuousOn zero_le_one
    (p := 2) (by norm_num) (by norm_num)
  have hsq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun z ↦ ‖v t (Xt t z)‖ ^ 2) π := by
    have hCE2 : MemLp (π[(fun z ↦ z.2 - z.1) | MeasurableSpace.comap (Xt t) inferInstance]) 2 π :=
      MemLp.condExp (by norm_num) hW2
    exact (hCE2.ae_eq (hcond t ht).symm).integrable_norm_pow (by norm_num)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π ≤ ∫ z, ‖z.2 - z.1‖ ^ 2 ∂π := by
    calc (∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) =
        ∫ z, ‖π[(fun z ↦ z.2 - z.1) | MeasurableSpace.comap (Xt t) inferInstance] z‖ ^ 2 ∂π :=
          integral_congr_ae ((hcond t ht).mono fun z hz ↦ by dsimp only at hz ⊢; rw [hz])
      _ ≤ _ := by
        exact_mod_cast integral_norm_condExp_rpow_le (m := MeasurableSpace.comap (Xt t) inferInstance)
          (p := 2) (by norm_num) (by simpa using hW2.integrable_norm_pow (by norm_num))
  have hAm : Measurable (fun t ↦ ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) :=
    ((hv.comp (measurable_fst.prodMk hXt)).norm.pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have hAint : Integrable (fun t ↦ ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) ρ := by
    refine (integrable_const (∫ z, ‖z.2 - z.1‖ ^ 2 ∂π)).mono' hAm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ by positivity)]
    exact hbound t ⟨ht.1.le, ht.2.le⟩
  have hact : ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ x, ‖v t x‖ₑ ^ (2 : ℝ) ∂π.map (Xt t) =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) := by
    rw [ofReal_integral_eq_lintegral_ofReal hAint
      (ae_of_all _ fun t ↦ integral_nonneg fun _ ↦ by positivity)]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp_rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hsq t ⟨ht.1.le, ht.2.le⟩)
      (ae_of_all _ fun _ ↦ by positivity)).symm
  have hinterval : (∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) =
      ∫ t in Ioo (0 : ℝ) 1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hinterval]
  constructor
  · simp only [hν] at hlow
    simp only [Xt, sub_zero, zero_smul, one_smul, add_zero, sub_self, zero_add] at hlow
    norm_num only [ENNReal.toReal_ofNat, sub_zero, Real.one_rpow, ENNReal.ofReal_one, one_mul] at hlow
    rw [hact, ENNReal.rpow_two] at hlow
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
    have hAnn : 0 ≤ (∫ t in Ioo (0 : ℝ) 1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) :=
      integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hAnn] using this
  · calc
      (∫ t in Ioo (0 : ℝ) 1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) ≤
        (∫ _t in Ioo (0 : ℝ) 1, ∫ z, ‖z.2 - z.1‖ ^ 2 ∂π) := by
        apply integral_mono_ae hAint (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hbound t ⟨ht.1.le, ht.2.le⟩
      _ = _ := by simp


end CKSD
