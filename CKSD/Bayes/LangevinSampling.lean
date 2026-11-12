module

public import CKSD.Bayes.GaussianGibbs

public import CKSD.Bayes.MALABasic
public import CKSD.Bayes.MALAGaussianRejection
public import CKSD.Bayes.MALAGaussianLowerBound

public import CKSD.Bayes.Diffusion
public import CKSD.Bayes.HamiltonianSampling
public import CKSD.Bayes.ULAContraction
public import CKSD.Bayes.ULAHamiltonianError
public import CKSD.Bayes.ULATransport
public import CKSD.Bayes.HamiltonianInvariant
import CKSD.Bayes.JKOEnergy
public import CKSD.Nonparametric.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Probability.Concentration.PoincareLogSobolev
public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Unadjusted and Metropolis-adjusted Langevin algorithms

Non-asymptotic guarantees for Langevin Monte Carlo targeting a Gibbs law `π ∝ e^{-V}` on `ℝᵈ`.
The unadjusted Langevin algorithm (ULA) `x ↦ x - h ∇V(x) + √(2h) Z` is iterated on laws through
`langevinStepLaw`. The `1/2`-lazy Metropolis-adjusted algorithm (MALA) is given by a
random-mapping representation: from the current state `x`, a uniform variable compared with `1/2`
decides laziness, a standard Gaussian draw gives the Langevin proposal `y`, and a second uniform
variable accepts `y` with probability `malaAcceptance`.

## Conventions

* The Hessian bounds `αI ⪯ ∇²V ⪯ βI` with `α > 0` for a `C²` potential are expressed by strong
  monotonicity of the gradient (`IsStronglyMonotoneGradient`) and `β`-Lipschitz continuity of
  the gradient (`IsSamplingPotential`), which are equivalent to them. The condition number is
  `κ = β / α`.
* The Wasserstein distance is TauCeti's `wassersteinEDist`, relative entropy is Mathlib's
  `klDiv`, and the logarithmic Sobolev inequality is TauCeti's, whose constant `C` corresponds to
  `KL ≤ (C/2) I`; "LSI with constant `1/α`" in the sense of Vempala–Wibisono is
  `LogSobolevInequality (1 / α)`.
* Uniform random variables have TauCeti's law `uniformMeasure 0 1`.

## Main definitions

* `CKSD.IsSamplingPotential`, `CKSD.IsStronglyMonotoneGradient`: smoothness and strong
  convexity hypotheses on the potential.
* `CKSD.ulaLaw`, `CKSD.malaStepLaw`: the law of the ULA iterates and one MALA step on laws.

## Main results

* `CKSD.exists_ula_iteration_complexity`: ULA iteration complexity in `W₂` and in KL under strong
  convexity (GAPS 104.39).
* `CKSD.exists_klDiv_ula_le_of_logSobolev`: the Vempala–Wibisono KL bound for ULA under a
  logarithmic Sobolev inequality, for step sizes `h ≤ α / (4β²)` (GAPS 104.45).
* `CKSD.exists_wasserstein_ula_le_of_stronglyConvex`: geometric `W₂` convergence of ULA up to a
  bias of order `β √(dh) / α` (GAPS 104.45).
* `CKSD.exists_mala_mixing_time_le`: the warm-start MALA upper bound (GAPS 104.47).
* `CKSD.exists_mala_mixing_time_ge`: a lower bound with the target and curvature scale chosen
  after the step size and accuracy, and `κ` the ratio of permitted curvature bounds.

## References

* S. Vempala and A. Wibisono, *Rapid convergence of the unadjusted Langevin algorithm: isoperimetry
  suffices*, NeurIPS 2019, Theorem 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Standing sampling hypotheses on a potential: twice continuously differentiable, with gradient
`gradV`, the gradient `β`-Lipschitz, and `e^{-V}` integrable. -/
structure IsSamplingPotential {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ)
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (β : ℝ) : Prop where
  /-- The potential is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 V
  /-- `gradV` is the gradient of `V`. -/
  hasGradientAt : ∀ x, HasGradientAt V (gradV x) x
  /-- The gradient is `β`-Lipschitz, that is, `V` is `β`-smooth. -/
  lipschitz : ∀ x y, ‖gradV x - gradV y‖ ≤ β * ‖x - y‖
  /-- The Gibbs density `e^{-V}` is integrable. -/
  integrable : Integrable (fun x ↦ Real.exp (-V x))

/-- Strong monotonicity of the gradient, equivalent to `∇²V ⪰ αI` for a `C²` potential. -/
def IsStronglyMonotoneGradient {d : ℕ}
    (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α : ℝ) : Prop :=
  ∀ x y, α * ‖x - y‖ ^ 2 ≤ inner ℝ (gradV x - gradV y) (x - y)

/-- Law of the unadjusted Langevin algorithm after `n` steps of size `h` from the initial law
`μ₀`. -/
def ulaLaw {d : ℕ} (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (n : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (langevinStepLaw gradV h)^[n] μ₀

/-- GAPS 104.39: iteration complexity of the unadjusted Langevin algorithm under
`αI ⪯ ∇²V ⪯ βI`, both in `W₂` at the last iterate and in relative entropy for the average of the
laws of iterates `N+1, …, 2N`. The initial law has a finite second moment. -/
theorem exists_ula_iteration_complexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ → MemLp id 2 μ₀ →
        ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt d →
          let h := c * ε ^ 2 / (β * d)
          let W₀ := (TauCeti.wassersteinEDist 2 μ₀ (gibbsMeasure V)).toReal
          ∀ N : ℕ, C * (β / α) * d / ε ^ 2 * Real.log (Real.exp 1 + α * W₀ ^ 2 / ε ^ 2) ≤ N →
            TauCeti.wassersteinEDist 2 (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
                ENNReal.ofReal (ε / Real.sqrt α) ∧
              klDiv ((N : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.Ioc N (2 * N), ulaLaw gradV h μ₀ j)
                  (gibbsMeasure V) ≤ ENNReal.ofReal (ε ^ 2) := by
  sorry

/-- GAPS 104.45: Vempala–Wibisono bound for the unadjusted Langevin algorithm. If the Gibbs law
`π` satisfies a logarithmic Sobolev inequality with constant `1/α` and `V` is `β`-smooth (not
necessarily convex), there is a universal `C` such that for `0 < h ≤ α / (4β²)` and all `N`,
`KL(μ_N ‖ π) ≤ e^{-α N h} KL(μ₀ ‖ π) + C β² d h / α`. -/
theorem exists_klDiv_ula_le_of_logSobolev :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → 0 < β → IsSamplingPotential V gradV β →
        (gibbsMeasure V).LogSobolevInequality (1 / α) →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ →
        ∀ h : ℝ, 0 < h → h ≤ α / (4 * β ^ 2) → ∀ N : ℕ,
          klDiv (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
            ENNReal.ofReal (Real.exp (-(α * N * h))) * klDiv μ₀ (gibbsMeasure V) +
              ENNReal.ofReal (C * β ^ 2 * d * h / α) := by
  sorry

/-- GAPS 104.45: geometric `W₂` convergence of the unadjusted Langevin algorithm under
`αI ⪯ ∇²V ⪯ βI`: there are universal `c, C` such that for `0 < h ≤ c / (βκ)` and all `N`,
`W₂(μ_N, π) ≤ e^{-α N h / 2} W₂(μ₀, π) + C β √(d h) / α`. -/
theorem exists_wasserstein_ula_le_of_stronglyConvex :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ →
        ∀ h : ℝ, 0 < h → h ≤ c / (β * (β / α)) → ∀ N : ℕ,
          TauCeti.wassersteinEDist 2 (ulaLaw gradV h μ₀ N) (gibbsMeasure V) ≤
            ENNReal.ofReal (Real.exp (-(α * N * h / 2))) *
                TauCeti.wassersteinEDist 2 μ₀ (gibbsMeasure V) +
              ENNReal.ofReal (C * β * Real.sqrt (d * h) / α) := by
  refine ⟨1/4, 12, by norm_num, by norm_num, ?_⟩
  intro d V G α β hα hV hmono μ hμ h hh hsize N
  have := hμ
  have := isProbabilityMeasure_gibbsMeasure hV.integrable
  have hprob (k : ℕ) : IsProbabilityMeasure (ulaLaw G h μ k) := by
    induction k with
    | zero => simpa [ulaLaw] using hμ
    | succ k ih =>
      change IsProbabilityMeasure ((langevinStepLaw G h)^[k+1] μ)
      rw [Function.iterate_succ_apply']
      have : IsProbabilityMeasure ((langevinStepLaw G h)^[k] μ) := by simpa only [ulaLaw] using ih
      exact isProbabilityMeasure_langevinStepLaw G h _
  by_cases hd : d = 0
  · subst d
    have := hprob N
    rw [wassersteinEDist_eq_zero_of_subsingleton (ulaLaw G h μ N) (gibbsMeasure V)]
    exact zero_le
  have : NeZero d := ⟨hd⟩
  have hab : α ≤ β := monotonicity_le_lipschitz hV.lipschitz hmono
  have hβ : 0 < β := hα.trans_le hab
  have hG : LipschitzWith (Real.toNNReal β) G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, Real.coe_toNNReal _ hβ.le] using hV.lipschitz x y
  have hid : (1/4 : ℝ)/(β*(β/α)) = α/(4*β^2) := by
    field_simp [hα.ne', hβ.ne']
  rw [hid] at hsize
  have hsize' := (le_div_iff₀ (by positivity : 0 < 4*β^2)).1 hsize
  have hstep : h*β^2 ≤ α := by nlinarith
  have hsquare : α^2 ≤ β^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare hh.le
  have hαh : α*h ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hα).1
    nlinarith
  have hInv := measurePreserving_mechanicalFlow_gibbsMeasure V G hV.contDiff hV.hasGradientAt hG
  have hrate := wassersteinEDist_iterate_langevinStepLaw_le (gibbsMeasure V) G hG hInv hα hmono hh.le
    (by simpa only [Real.coe_toNNReal _ hβ.le] using hstep) hαh μ N
  simpa only [ulaLaw, Real.coe_toNNReal _ hβ.le] using hrate


/-- GAPS 104.47: mixing-time upper bound for the `1/2`-lazy Metropolis-adjusted Langevin
algorithm from an `M`-warm start (`μ₀ ≤ Mπ`), with `Λ = log max {κ, d, M/ε, c₂}`. -/
theorem exists_mala_mixing_time_le :
    ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (d : ℕ) (V : EuclideanSpace ℝ (Fin d) → ℝ)
        (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α β : ℝ),
        0 < d → 0 < α → IsSamplingPotential V gradV β → IsStronglyMonotoneGradient gradV α →
        ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ M : ℝ, ∀ μ₀ : Measure (EuclideanSpace ℝ (Fin d)),
          IsProbabilityMeasure μ₀ → μ₀ ≤ ENNReal.ofReal M • gibbsMeasure V →
          let κ := β / α
          let Λ := Real.log (max (max κ d) (max (M / ε) c₂))
          let h := c₀ / (β * Real.sqrt d * Λ ^ 2)
          ∃ n : ℕ, (n : ℝ) ≤ c₁ * κ * Real.sqrt d * Λ ^ 3 ∧
            totalVariationDistance ((malaStepLaw V gradV h)^[n] μ₀) (gibbsMeasure V) ≤ ε := by
  sorry

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive isotropic Gaussian precision gives the sampling hypotheses with every permitted
curvature ratio at least one. The intrinsic Gaussian condition number remains one. -/
theorem isSamplingPotential_and_stronglyMonotone_gaussianPrecision {α κ : ℝ}
    (hα : 0 < α) (hκ : 1 ≤ κ) :
    IsSamplingPotential (d:=d) (gaussianPrecisionPotential α) (gaussianPrecisionGradient α) (κ*α) ∧
      IsStronglyMonotoneGradient (d:=d) (gaussianPrecisionGradient α) α := by
  constructor
  · constructor
    · change ContDiff ℝ 2 (fun x:E ↦ α/2*‖x‖^2)
      exact contDiff_const.mul (contDiff_norm_sq ℝ)
    · exact hasGradientAt_gaussianPrecisionPotential α
    · intro x y
      change ‖α • x-α • y‖≤κ*α*‖x-y‖
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hα]
      have hm := mul_nonneg (sub_nonneg.mpr hκ) (mul_nonneg hα.le (norm_nonneg (x-y)))
      nlinarith
    · change Integrable (fun x:E ↦ Real.exp (-(α/2*‖x‖^2)))
      exact integrable_exp_neg_mul_norm_sq (by positivity)
  · intro x y
    change α*‖x-y‖^2 ≤ inner ℝ (α • x-α • y) (x-y)
    rw [← smul_sub,real_inner_smul_left,real_inner_self_eq_norm_sq]

/-- GAPS 104.47: a scale-adaptive lower bound for lazy MALA. For each step size `h` and
accuracy `ε`, the target, curvature scale `α`, and warm initialization may be chosen afterwards.
Here `κ` is the ratio of permitted upper and lower curvature bounds; the target need not attain
that intrinsic condition number. A sufficiently concentrated isotropic Gaussian supplies the
bound. This quantifier scope does not assert one fixed normalized target is hard for every
step size. -/
theorem exists_mala_mixing_time_ge :
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧ ∀ a b : ℝ, 0 < a → 0 < b → ∃ N₀ : ℕ,
      ∀ d : ℕ, N₀ < d → ∀ κ : ℝ, 3 ≤ κ → κ ≤ a * (d : ℝ) ^ b → ∀ M : ℝ, 12 ≤ M →
      ∀ h : ℝ, 0 < h → ∀ ε ∈ Ioo (0 : ℝ) 1,
        ∃ (V : EuclideanSpace ℝ (Fin d) → ℝ)
          (gradV : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (α : ℝ),
          0 < α ∧ IsSamplingPotential V gradV (κ * α) ∧ IsStronglyMonotoneGradient gradV α ∧
          ∃ μ₀ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ₀ ∧
            μ₀ ≤ ENNReal.ofReal M • gibbsMeasure V ∧
            ∀ n : ℕ, (n : ℝ) < c₃ * κ * Real.sqrt d *
                (max (Real.log κ) (Real.log d)) ^ (-3 : ℤ) * Real.log (c₄ / ε) →
              ε < totalVariationDistance ((malaStepLaw V gradV h)^[n] μ₀) (gibbsMeasure V) := by
  refine ⟨1,1/4,by norm_num,by norm_num,?_⟩
  intro a b _ _
  refine ⟨0,?_⟩
  intro d hd κ hκ _ M hM h hh ε hε
  obtain ⟨q,hq,hqa⟩ := exists_pos_gaussianReal_tail_eq_quarter
  let R : ℝ := κ*Real.sqrt d*(max (Real.log κ) (Real.log d))^(-3:ℤ)*Real.log ((1/4)/ε)
  let N : ℕ := ⌈R⌉₊
  obtain ⟨σ,hσ,μ,hμ,hμwarm,hfar⟩ := exists_scaled_gaussian_mala_far hq hqa hh
    (⟨0,hd⟩ : Fin d) N
  have hα : 0 < (σ⁻¹)^2 := by positivity
  obtain ⟨hV, hG⟩ := isSamplingPotential_and_stronglyMonotone_gaussianPrecision
    (κ := κ) hα (by linarith)
  refine ⟨gaussianPrecisionPotential ((σ⁻¹)^2), gaussianPrecisionGradient ((σ⁻¹)^2),
    (σ⁻¹)^2, hα, hV, hG, μ, hμ, ?_, ?_⟩
  · apply hμwarm.trans
    have h4 : (4:ℝ≥0∞)≤ENNReal.ofReal M := by
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (by linarith : (4:ℝ)≤M)
    intro s
    change (4:ℝ≥0∞)*_≤ENNReal.ofReal M*_
    gcongr
  · intro n hn
    have hnR : (n:ℝ)<R := by simpa only [one_mul] using hn
    have hnN : n≤N := by exact_mod_cast (hnR.le.trans (Nat.le_ceil R))
    have hlog : 0<Real.log ((1/4)/ε) := by
      have hcoef : 0≤κ*Real.sqrt d*(max (Real.log κ) (Real.log d))^(-3:ℤ) := by
        apply mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
        apply zpow_nonneg
        exact le_max_of_le_left (Real.log_nonneg (by linarith))
      by_contra hnot
      have hR : R≤0 := mul_nonpos_of_nonneg_of_nonpos hcoef (le_of_not_gt hnot)
      exact (not_lt_of_ge (Nat.cast_nonneg n)) (hnR.trans_le hR)
    have hεq : ε<1/4 := by
      have hratio : 1<(1/4)/ε := (Real.log_pos_iff (div_pos (by norm_num) hε.1).le).mp hlog
      simpa only [one_mul] using (lt_div_iff₀ hε.1).mp hratio
    exact hεq.trans_le ((by norm_num : (1/4:ℝ)≤3/8).trans (hfar n hnN))

end CKSD
