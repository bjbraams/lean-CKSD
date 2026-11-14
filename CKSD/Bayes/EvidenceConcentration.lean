module

public import CKSD.Bayes.Nonparametric
public import CKSD.Bayes.EvidenceBounds
public import CKSD.Bayes.ExponentialTests
public import Mathlib.Probability.Moments.Variance


/-!
# Quantitative lower bounds for Bayesian evidence

The denominator estimate for posterior contraction on shrinking Kullback–Leibler balls.
If the mean and second moment of the log-likelihood ratio are at most `δ`, independent sampling
and Chebyshev's inequality show that the evidence is at least
`π(B) / 2` times the true likelihood times `exp (-2 n δ)`, outside an event of probability at
most `2 / (n δ)`. Thus the bound holds with probability tending to one for balls with
`n δ → ∞`, even when their prior masses tend to zero.

The iid variance identity and Chebyshev bound come from Mathlib's
`ProbabilityTheory.variance_sum_pi` and `ProbabilityTheory.meas_ge_le_variance_div_sq`.
The integration over parameter balls follows the Tonelli argument of `CKSD.Bayes.EvidenceBounds`.
The second-moment convention is `CKSD.logLikelihoodRatioSecondMoment`.

## Main results

* `CKSD.measure_infinite_pi_evidence_lt_le`: a nonasymptotic evidence lower bound.
* `CKSD.tendsto_infinite_pi_evidence_lt_of_second_moment`: its shrinking-ball consequence.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- Chebyshev bound for the sum of independent copies of a real variable with mean at least
`-δ` and second moment at most `δ`. -/
theorem measure_sum_lt_neg_two_mul_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (g : X → ℝ) (hg : Measurable g)
    (hg2 : MemLp g 2 P) (δ : ℝ) (hδ : 0 < δ)
    (hmean : -δ ≤ ∫ x, g x ∂P) (hsecond : ∫ x, g x ^ 2 ∂P ≤ δ)
    (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ P) {x | (∑ i, g (x i)) < -2 * n * δ} ≤
      ENNReal.ofReal (1 / (n * δ)) := by
  let ν := Measure.pi fun _ : Fin n ↦ P
  let S : (Fin n → X) → ℝ := fun x ↦ ∑ i, g (x i)
  have hcoord (i : Fin n) : MemLp (fun x : Fin n → X ↦ g (x i)) 2 ν :=
    hg2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ P) i)
  have hS : MemLp S 2 ν := memLp_finsetSum _ fun i _ ↦ hcoord i
  have hES : ∫ x, S x ∂ν = n * ∫ x, g x ∂P := by
    rw [show S = fun x ↦ ∑ i, g (x i) from rfl, integral_finsetSum _ fun i _ ↦ (hcoord i).integrable (by norm_num)]
    have hcoordInt (i : Fin n) : ∫ x : Fin n → X, g (x i) ∂ν = ∫ x, g x ∂P := by
      have h := integral_map (measurePreserving_eval (fun _ : Fin n ↦ P) i).aemeasurable
        (f := g) (by
          rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq]
          exact hg.aestronglyMeasurable)
      rw [(measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq] at h
      exact h.symm
    simp_rw [hcoordInt]
    simp
  have hvar : variance S ν ≤ n * δ := by
    have heq := variance_sum_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ g) (fun _ ↦ hg2)
    have hEq : variance S ν = n * variance g P := by
      have hfun : S = ∑ i : Fin n, fun x : Fin n → X ↦ g (x i) := by
        ext x; simp [S, Finset.sum_apply]
      rw [hfun]
      simpa [ν] using heq
    rw [hEq]
    exact mul_le_mul_of_nonneg_left ((variance_le_expectation_sq hg.aestronglyMeasurable).trans hsecond) (Nat.cast_nonneg n)
  have hnd : 0 < (n : ℝ) * δ := mul_pos (by exact_mod_cast hn) hδ
  have hsub : {x | (∑ i, g (x i)) < -2 * n * δ} ⊆
      {x | (n : ℝ) * δ ≤ |S x - ∫ y, S y ∂ν|} := by
    intro x hx
    have hESlow : -(n : ℝ) * δ ≤ ∫ y, S y ∂ν := by
      rw [hES]; nlinarith [mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg n)]
    apply le_trans _ (neg_le_abs (S x - ∫ y, S y ∂ν))
    change ∑ i, g (x i) < -2 * n * δ at hx
    dsimp [S]
    linarith
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hS hnd).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  calc variance S ν / ((n : ℝ) * δ) ^ 2 ≤ (n * δ) / (n * δ) ^ 2 := by gcongr
    _ = 1 / (n * δ) := by field_simp

/-- The log-density ratio has a finite second moment when the likelihood-ratio second moment
used in the posterior contraction hypotheses is finite. -/
theorem mem_lp_log_sub_log_of_second_moment {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q)
    (hKL : klDiv P Q ≠ ∞) (hsecond : logLikelihoodRatioSecondMoment P Q ≠ ∞) :
    MemLp (fun x ↦ Real.log (q x) - Real.log (p x)) 2 P := by
  have hllr : MemLp (llr P Q) 2 P := by
    apply (memLp_two_iff_integrable_sq (measurable_llr P Q).aestronglyMeasurable).2
    exact (lintegral_ofReal_ne_top_iff_integrable
      ((measurable_llr P Q).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x ↦ sq_nonneg _)).1 hsecond
  refine hllr.neg.ae_eq ?_
  have hae := llr_ae_eq_log_sub_log hP hQ (klDiv_ne_top_iff.1 hKL).1
  filter_upwards [hae] with x hx
  simp only [Pi.neg_apply]
  rw [hx]
  ring

/-- The probability that the log likelihood of an alternative in a KL and second-moment ball
falls below `-2 n δ` is at most `1/(n δ)`. -/
theorem measure_sum_log_ratio_lt_le {X : Type*} [MeasurableSpace X]
    {P Q μ : Measure X} [SigmaFinite μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q)
    (δ : ℝ) (hδ : 0 < δ) (hKL : klDiv P Q ≤ ENNReal.ofReal δ)
    (hsecond : logLikelihoodRatioSecondMoment P Q ≤ ENNReal.ofReal δ)
    (n : ℕ) (hn : 0 < n) :
    (Measure.infinitePi fun _ : ℕ ↦ P)
      {ω | (∑ i ∈ Finset.range n, (Real.log (q (ω i)) - Real.log (p (ω i)))) < -2 * n * δ} ≤
        ENNReal.ofReal (1 / (n * δ)) := by
  have hKLfin : klDiv P Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hsecondfin : logLikelihoodRatioSecondMoment P Q ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsecond
  let g : X → ℝ := fun x ↦ Real.log (q x) - Real.log (p x)
  have hg : Measurable g := hQ.1.log.sub hP.1.log
  have hg2 : MemLp g 2 P := mem_lp_log_sub_log_of_second_moment hP hQ hKLfin hsecondfin
  obtain ⟨hint, hmean⟩ := integral_log_sub_log_eq_neg_to_real_kl_div hP hQ hKLfin
  have hlow : -δ ≤ ∫ x, g x ∂P := by
    rw [hmean]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    rw [ENNReal.toReal_ofReal hδ.le] at this
    linarith
  have hvar : ∫ x, g x ^ 2 ∂P ≤ δ := by
    have heq : (∫ x, g x ^ 2 ∂P) = (logLikelihoodRatioSecondMoment P Q).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _) (hg.pow_const 2).aestronglyMeasurable]
      congr 1
      apply lintegral_congr_ae
      have hae := llr_ae_eq_log_sub_log hP hQ (klDiv_ne_top_iff.1 hKLfin).1
      filter_upwards [hae] with x hx
      change ENNReal.ofReal (g x ^ 2) = ENNReal.ofReal (llr P Q x ^ 2)
      rw [hx]
      congr 1
      dsimp [g]
      ring
    rw [heq]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hsecond).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have h := measure_sum_lt_neg_two_mul_le P g hg hg2 δ hδ hlow hvar n hn
  rw [← infinite_pi_map_fin_val P n, Measure.map_apply (by fun_prop)
    (measurableSet_lt (by fun_prop) measurable_const)] at h
  simpa only [Set.preimage_ofPred_eq, Finset.sum_range, g] using h

/-- Quantitative evidence lower bound on a KL and log-likelihood second-moment ball.
For `n > 0`, the evidence is at least half the prior mass of the ball times the true likelihood
and `exp (-2 n δ)`, except on a set of probability at most `2/(n δ)`. -/
theorem measure_infinite_pi_evidence_lt_le {Θ X : Type*} [MeasurableSpace Θ]
    [MeasurableSpace X] (π : Measure Θ) [IsFiniteMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ) {B : Set Θ} (hBm : MeasurableSet B)
    (δ : ℝ) (hδ : 0 < δ)
    (hKL : ∀ θ ∈ B, klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal δ)
    (hsecond : ∀ θ ∈ B, logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal δ)
    (n : ℕ) (hn : 0 < n) :
    (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
        π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-(2 * δ) * n))} ≤
          ENNReal.ofReal (2 / (n * δ)) := by
  let γ := 2 * δ
  set Pinf := Measure.infinitePi (fun _ : ℕ ↦ P θ₀)
  let good : ℕ → Θ → (ℕ → X) → Prop := fun n θ ω ↦
    (∀ i ∈ Finset.range n, 0 < f θ (ω i)) ∧ (∀ i ∈ Finset.range n, 0 < f θ₀ (ω i)) ∧
      -(γ * n) ≤ ∑ i ∈ Finset.range n, (Real.log (f θ (ω i)) - Real.log (f θ₀ (ω i)))
  have hfω : ∀ i, Measurable fun p : Θ × (ℕ → X) ↦ f p.1 (p.2 i) :=
    fun i ↦ hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hfω' : ∀ i, Measurable fun p : Θ × (ℕ → X) ↦ f θ₀ (p.2 i) :=
    fun i ↦ (hdensity θ₀).1.comp ((measurable_pi_apply i).comp measurable_snd)
  have hgood : ∀ n, MeasurableSet {p : Θ × (ℕ → X) | good n p.1 p.2} := by
    intro n
    have : {p : Θ × (ℕ → X) | good n p.1 p.2} =
        (⋂ i ∈ Finset.range n, {p | 0 < f p.1 (p.2 i)}) ∩
          (⋂ i ∈ Finset.range n, {p | 0 < f θ₀ (p.2 i)}) ∩
          {p | -(γ * n) ≤
            ∑ i ∈ Finset.range n, (Real.log (f p.1 (p.2 i)) - Real.log (f θ₀ (p.2 i)))} := by
      ext p; simp [good, and_assoc]
    rw [this]
    refine ((Finset.measurableSet_biInter _ fun i _ ↦
      measurableSet_lt measurable_const (hfω i)).inter
      (Finset.measurableSet_biInter _ fun i _ ↦ measurableSet_lt measurable_const (hfω' i))).inter
      (measurableSet_le measurable_const ?_)
    exact Finset.measurable_sum _ fun i _ ↦ (hfω i).log.sub (hfω' i).log
  have hcoord : ∀ q : X → Prop, (∀ᵐ x ∂(P θ₀), q x) → ∀ᵐ ω ∂Pinf, ∀ i, q (ω i) := by
    intro q hq
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable
      (by rwa [Measure.infinitePi_map_eval])
  have hbad : ∀ θ ∈ B, Pinf {ω | ¬ good n θ ω} ≤ ENNReal.ofReal (1 / (n * δ)) := by
    intro θ hθ
    have hKLfin : klDiv (P θ₀) (P θ) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKL θ hθ)
    have hPQ := (klDiv_ne_top_iff.1 hKLfin).1
    have hsub : {ω | ¬ good n θ ω} ≤ᵐ[Pinf]
        {ω | (∑ i ∈ Finset.range n, (Real.log (f θ (ω i)) - Real.log (f θ₀ (ω i)))) < -2 * n * δ} := by
      filter_upwards [hcoord _ (hPQ.ae_le (hdensity θ).ae_pos),
        hcoord _ (hdensity θ₀).ae_pos] with ω h1 h2
      intro hω
      change ¬ good n θ ω at hω
      by_contra h
      apply hω
      refine ⟨fun i _ ↦ h1 i, fun i _ ↦ h2 i, ?_⟩
      dsimp [γ]
      linarith
    exact (measure_mono_ae hsub).trans
      (measure_sum_log_ratio_lt_le (hdensity θ₀) (hdensity θ) δ hδ (hKL θ hθ)
        (hsecond θ hθ) n hn)
  -- the joint bad set and Tonelli's theorem
  let T : ℕ → Set (Θ × (ℕ → X)) := fun n ↦ {p | p.1 ∈ B ∧ ¬ good n p.1 p.2}
  have hT : ∀ n, MeasurableSet (T n) := fun n ↦
    (measurable_fst hBm).inter (hgood n).compl
  have hTon : ∀ n, ∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf =
      ∫⁻ θ, B.indicator (fun θ ↦ Pinf {ω | ¬ good n θ ω}) θ ∂π := by
    intro n
    rw [← Measure.prod_apply_symm (hT n), Measure.prod_apply (hT n)]
    refine lintegral_congr fun θ ↦ ?_
    by_cases hθ : θ ∈ B
    · simp [T, hθ, Set.indicator]
    · simp [T, hθ]
  have hbound : (∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf) ≤
      ENNReal.ofReal (1 / (n * δ)) * π B := by
    rw [hTon n, lintegral_indicator hBm]
    calc ∫⁻ θ in B, Pinf {ω | ¬ good n θ ω} ∂π ≤
        ∫⁻ _ in B, ENNReal.ofReal (1 / (n * δ)) ∂π :=
          setLIntegral_mono measurable_const fun θ hθ ↦ hbad θ hθ
      _ = _ := by rw [setLIntegral_const]
  by_cases hπB : π B = 0
  · simp [hπB]
  have hπB2 : π B / 2 ≠ 0 := by simp [hπB]
  have hπB2' : π B / 2 ≠ ∞ := ENNReal.div_ne_top (measure_ne_top _ _) (by norm_num)
  have hsub : ∀ n : ℕ, {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
      π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n))} ⊆
      {ω | π B / 2 ≤ π ((fun θ ↦ (θ, ω)) ⁻¹' T n)} := by
    intro n ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    push Not at hlt
    set G := {θ | θ ∈ B ∧ good n θ ω}
    have hGm : MeasurableSet G :=
      ((measurable_fst hBm).inter (hgood n)).preimage measurable_prodMk_right
    have hsplit : π B = π G + π ((fun θ ↦ (θ, ω)) ⁻¹' T n) := by
      rw [← measure_union _ ((hT n).preimage measurable_prodMk_right)]
      · congr 1; ext θ; simp only [G, T, Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage]; tauto
      · rw [Set.disjoint_left]; intro θ h1 h2; exact h2.2 h1.2
    have hG : π B / 2 ≤ π G := by
      by_contra h
      push Not at h
      have := ENNReal.add_lt_add h hlt
      rw [ENNReal.add_halves, ← hsplit] at this
      exact lt_irrefl _ this
    have hF : Measurable fun θ ↦ ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) :=
      ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
        hf.comp (measurable_id.prodMk measurable_const))
    have hle : π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n)) ≤
        ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π := by
      calc π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n))
          ≤ π G * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n)) :=
            mul_le_mul_left hG _
        _ = ∫⁻ _ in G, ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n)) ∂π := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ θ in G, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π := by
            refine setLIntegral_mono hF fun θ hθ ↦ ENNReal.ofReal_le_ofReal ?_
            refine prod_mul_exp_le_prod (fun i ↦ hθ.2.2.1 i (Finset.mem_range.2 i.2))
              (fun i ↦ hθ.2.1 i (Finset.mem_range.2 i.2)) ?_
            have := hθ.2.2.2
            rwa [Finset.sum_range] at this
        _ ≤ ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π := setLIntegral_le_lintegral _ _
    exact absurd hω (not_lt.2 hle)
  have hmarkov : ∀ n, Pinf {ω | π B / 2 ≤ π ((fun θ ↦ (θ, ω)) ⁻¹' T n)} ≤
      (∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf) / (π B / 2) := fun n ↦
    meas_ge_le_lintegral_div (measurable_measure_prodMk_right (hT n)).aemeasurable hπB2 hπB2'
  refine (measure_mono (hsub n)).trans ((hmarkov n).trans ?_)
  calc (∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf) / (π B / 2) ≤
      (ENNReal.ofReal (1 / (n * δ)) * π B) / (π B / 2) := by gcongr
    _ = ENNReal.ofReal (2 / (n * δ)) := by
      rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv,
        ENNReal.div_div_cancel hπB (measure_ne_top _ _)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (n * δ))]
      congr 1
      ring

/-- The evidence lower bound holds with probability tending to one for varying KL and
second-moment balls of radius `δ n`, provided `n δ n → ∞`. The prior mass of each ball may
vanish, and no lower bound on that mass is needed for this relative evidence estimate. -/
theorem tendsto_infinite_pi_evidence_lt_of_second_moment {Θ X : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] (π : Measure Θ) [IsFiniteMeasure π]
    (μ : Measure X) [SigmaFinite μ] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (f : Θ → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hdensity : ∀ θ, HasDensity (P θ) μ (f θ))
    (θ₀ : Θ) (B : ℕ → Set Θ) (hBm : ∀ n, MeasurableSet (B n))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hnδ : Tendsto (fun n : ℕ ↦ (n : ℝ) * δ n) atTop atTop)
    (hKL : ∀ n, ∀ θ ∈ B n, klDiv (P θ₀) (P θ) ≤ ENNReal.ofReal (δ n))
    (hsecond : ∀ n, ∀ θ ∈ B n,
      logLikelihoodRatioSecondMoment (P θ₀) (P θ) ≤ ENNReal.ofReal (δ n)) :
    Tendsto (fun n : ℕ ↦ (Measure.infinitePi fun _ : ℕ ↦ P θ₀)
      {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
        π (B n) / 2 * ENNReal.ofReal
          ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-(2 * δ n) * n))}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 / ((n : ℝ) * δ n))) atTop (𝓝 0) :=
    by simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hnδ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n ↦ zero_le)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact measure_infinite_pi_evidence_lt_le π μ P f hf hdensity θ₀ (hBm n) (δ n) (hδ n)
    (hKL n) (hsecond n) n hn

end CKSD
