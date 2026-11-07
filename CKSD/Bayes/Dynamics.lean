module

public import CKSD.Bayes.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import CKSD.Nonparametric.Basic

/-!
# Bayes: Dynamics

Sources: `GAPS.md`, `SYNOPSIS104.md`, and `STRUCTURE104.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 104.37, the scalar Langevin generator has zero Gibbs expectation on smooth tests. -/
theorem integral_langevin_generator_eq_zero (V f : ℝ → ℝ) (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    let Z := ∫ x, Real.exp (-V x);
    ∀ (hZ : 0 < Z),
    ∀ (hi : Integrable (fun x ↦ Real.exp (-V x)) volume),
    (∫ x, (deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x) / Z) = 0 := by
  let F : ℝ → ℝ := deriv f * (fun x ↦ Real.exp (-V x))
  have hF : ContDiff ℝ 1 F := hf.deriv'.mul hV.neg.exp
  have hFc : HasCompactSupport F := hfc.deriv.mul_right
  have hder (x : ℝ) : HasDerivAt F
      ((deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x)) x := by
    have hd := (hf.differentiable_deriv_two x).hasDerivAt.mul
      ((hV.differentiable (by norm_num) x).hasDerivAt.neg.exp)
    convert hd using 1 <;> simp only [Pi.neg_apply] <;> ring
  have hiF : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have hidi : Integrable (fun x ↦
      (deriv (deriv f) x - deriv V x * deriv f x) * Real.exp (-V x)) := by
    have hdFi : Integrable (deriv F) :=
      hF.continuous_deriv_one.integrable_of_hasCompactSupport hFc.deriv
    convert hdFi using 1
    funext x
    exact (hder x).deriv.symm
  dsimp only
  intro hZ hi
  rw [integral_div, integral_eq_zero_of_hasDerivAt_of_integrable hder hidi hiF, zero_div]

/-- GAPS 104.38, pathwise synchronous contraction from a common additive forcing. -/
theorem dist_synchronous_langevin_le_exp {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hb : Continuous b)
    (m : ℝ) (hm : 0 < m)
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

/-- GAPS 104.40, almost-sure Robbins–Monro convergence under bounded conditional noise variance. -/
theorem ae_tendsto_robbins_monro {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (θ M : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (ha : ∀ n, Measurable[F n] (θ n)) (hM : ∀ n, Measurable[F n] (M n))
    (hθ2 : MemLp (θ 0) 2 μ) (hM2 : ∀ n, MemLp (M n) 2 μ)
    (hzero : ∀ n, μ[M (n + 1) | F n] =ᵐ[μ] fun _ ↦ 0)
    (K : ℝ) (hnoise : ∀ n, μ[(fun ω ↦ ‖M (n + 1) ω‖ ^ 2) | F n] ≤ᵐ[μ] fun _ ↦ K)
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ≥0) (hL : LipschitzWith L h) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hz : h θ₀ = 0) (m : ℝ) (hm : 0 < m)
    (hdrift : ∀ x, m * ‖x - θ₀‖ ^ 2 ≤ inner ℝ (x - θ₀) (h x))
    (a : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (ha2 : Summable (fun n ↦ a n ^ 2))
    (haDiverges : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a k) atTop atTop)
    (hrec : ∀ n, ∀ᵐ ω ∂μ, θ (n + 1) ω = θ n ω - a n • (h (θ n ω) + M (n + 1) ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ θ n ω) atTop (𝓝 θ₀) := by
  sorry

/-- GAPS 104.41, the entropy-decay consequence of dissipation and a log-Sobolev bound. -/
theorem entropy_le_exp_of_log_sobolev (E I : ℝ → ℝ) (m : ℝ) (hm : 0 < m)
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
    convert he.mul (hder t ht) using 1 <;> ring
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
    convert Real.exp_zero using 1 <;> ring
  rwa [← mul_assoc, hcancel, one_mul] at hscaled

/-- GAPS 104.64, scalar score-matching identity for compactly supported fitted scores. -/
theorem score_matching_risk_identity (P : Measure ℝ) [IsProbabilityMeasure P] (p g : ℝ → ℝ)
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

/-- SYNOPSIS 104.72: action bounds for the barycentric velocity of an arbitrary straight coupling. -/
theorem wasserstein_le_barycentric_velocity_action {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure π] (h2 : MemLp id 2 π)
    (v : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hv : Measurable (Function.uncurry v)) :
    let Xt := fun t (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ↦
      (1 - t) • z.1 + t • z.2;
    ∀ (hcond : ∀ t ∈ Icc (0 : ℝ) 1,
      (fun z ↦ v t (Xt t z)) =ᵐ[π]
        π[(fun z ↦ z.2 - z.1) | (inferInstance : MeasurableSpace
          (EuclideanSpace ℝ (Fin d))).comap (Xt t)]),
    (TauCeti.wassersteinEDist 2 (π.map Prod.fst) (π.map Prod.snd)).toReal ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π ∧
    (∫ t in (0 : ℝ)..1, ∫ z, ‖v t (Xt t z)‖ ^ 2 ∂π) ≤
      ∫ z, ‖z.2 - z.1‖ ^ 2 ∂π := by
  sorry


end CKSD
