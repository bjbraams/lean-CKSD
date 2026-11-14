module

public import CKSD.Inference.Basic
public import TauCeti.Probability.StrongLaw


/-!
# Lower bounds for the evidence of a dominated model

For a dominated model `P θ = f θ · μ` and a true parameter `θ₀`, the evidence (marginal
likelihood) of the first `n` observations is `∫ ∏ᵢ f θ (xᵢ) dπ(θ)`. If the prior gives positive
mass to a set `B` of parameters whose Kullback–Leibler divergence from `θ₀` is below `γ`, then
with probability tending to one under the true law the evidence is at least
`π(B)/2 · ∏ᵢ f θ₀ (xᵢ) · e^{-γ n}`. This is the denominator estimate in Schwartz's posterior
consistency theorem. The proof applies the strong law of large numbers (TauCeti's
`TauCeti.Probability.strong_law_ae_infinitePi`) to the log-likelihood ratio for each parameter in
`B` and integrates over the prior with Tonelli's theorem.

## Main results

* `CKSD.HasDensity.measure_nonpos_eq_zero`: a law has no mass where its density is nonpositive.
* `CKSD.llr_ae_eq_log_sub_log`: the log-likelihood ratio of two dominated laws is the difference
  of the log densities.
* `CKSD.integral_log_sub_log_eq_neg_to_real_kl_div`: the expected log-likelihood ratio is minus the
  Kullback–Leibler divergence.
* `CKSD.tendsto_infinite_pi_evidence_lt`: the evidence lower bound holds with probability tending
  to one.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

variable {X : Type*} [MeasurableSpace X]

/-- A law with real density `p` gives no mass to the set where `p ≤ 0`. -/
theorem HasDensity.measure_nonpos_eq_zero {P μ : Measure X} {p : X → ℝ}
    (hP : HasDensity P μ p) : P {x | p x ≤ 0} = 0 := by
  have hs : MeasurableSet {x | p x ≤ 0} := measurableSet_le hP.1 measurable_const
  rw [hP.2.2, withDensity_apply _ hs]
  refine le_antisymm ?_ zero_le
  calc ∫⁻ x in {x | p x ≤ 0}, ENNReal.ofReal (p x) ∂μ ≤ ∫⁻ _ in {x | p x ≤ 0}, 0 ∂μ :=
        setLIntegral_mono measurable_const fun x hx ↦ by
          simp [ENNReal.ofReal_eq_zero.2 (show p x ≤ 0 from hx)]
    _ = 0 := by simp

/-- Under a law with density `p`, the density is almost surely positive. -/
theorem HasDensity.ae_pos {P μ : Measure X} {p : X → ℝ} (hP : HasDensity P μ p) :
    ∀ᵐ x ∂P, 0 < p x := by
  rw [ae_iff]
  simpa only [not_lt] using hP.measure_nonpos_eq_zero

/-- For laws `P = p · μ` and `Q = q · μ` with `P ≪ Q`, the log-likelihood ratio `log (dP/dQ)` is
`P`-almost surely `log p - log q`. -/
theorem llr_ae_eq_log_sub_log {P Q μ : Measure X} [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] {p q : X → ℝ} (hP : HasDensity P μ p) (hQ : HasDensity Q μ q)
    (hPQ : P ≪ Q) : llr P Q =ᵐ[P] fun x ↦ Real.log (p x) - Real.log (q x) := by
  have hPμ : P ≪ μ := by rw [hP.2.2]; exact withDensity_absolutelyContinuous _ _
  have h1 := Measure.rnDeriv_mul_rnDeriv (κ := μ) hPQ
  have h2 : Q.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (q x) := by
    rw [hQ.2.2]; exact Measure.rnDeriv_withDensity μ hQ.1.ennreal_ofReal
  have h3 : P.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (p x) := by
    rw [hP.2.2]; exact Measure.rnDeriv_withDensity μ hP.1.ennreal_ofReal
  filter_upwards [hPμ.ae_le h1, hPμ.ae_le h2, hPμ.ae_le h3, hP.ae_pos, hPQ.ae_le hQ.ae_pos]
    with x hx1 hx2 hx3 hp hq
  simp only [Pi.mul_apply] at hx1
  rw [hx2, hx3] at hx1
  have hr : (P.rnDeriv Q x).toReal * q x = p x := by
    have := congrArg ENNReal.toReal hx1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hp.le] at this
  rw [llr, ← Real.log_div hp.ne' hq.ne', eq_div_of_mul_eq hq.ne' hr]

/-- For probability laws `P = p · μ`, `Q = q · μ` with finite Kullback–Leibler divergence
`KL(P ‖ Q)`, the function `log q - log p` is `P`-integrable with integral `-KL(P ‖ Q)`. -/
theorem integral_log_sub_log_eq_neg_to_real_kl_div {P Q μ : Measure X} [SigmaFinite μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p q : X → ℝ} (hP : HasDensity P μ p)
    (hQ : HasDensity Q μ q) (hKL : klDiv P Q ≠ ∞) :
    Integrable (fun x ↦ Real.log (q x) - Real.log (p x)) P ∧
      ∫ x, (Real.log (q x) - Real.log (p x)) ∂P = -(klDiv P Q).toReal := by
  obtain ⟨hPQ, hint⟩ := klDiv_ne_top_iff.1 hKL
  have hae := llr_ae_eq_log_sub_log hP hQ hPQ
  have hae' : (fun x ↦ Real.log (q x) - Real.log (p x)) =ᵐ[P] fun x ↦ -llr P Q x := by
    filter_upwards [hae] with x hx
    rw [hx]; ring
  refine ⟨hint.neg.congr hae'.symm, ?_⟩
  rw [integral_congr_ae hae', integral_neg,
    toReal_klDiv_of_measure_eq hPQ (by simp)]

/-- If `a` and `b` are positive and `∑ (log bᵢ - log aᵢ) ≥ -γ n`, then
`(∏ aᵢ) e^{-γ n} ≤ ∏ bᵢ`. -/
theorem prod_mul_exp_le_prod {n : ℕ} {a b : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) {γ : ℝ} (h : -(γ * n) ≤ ∑ i, (Real.log (b i) - Real.log (a i))) :
    (∏ i, a i) * Real.exp (-γ * n) ≤ ∏ i, b i := by
  have hA : ∏ i, a i = Real.exp (∑ i, Real.log (a i)) := by
    rw [Real.exp_sum]; exact Finset.prod_congr rfl fun i _ ↦ (Real.exp_log (ha i)).symm
  have hB : ∏ i, b i = Real.exp (∑ i, Real.log (b i)) := by
    rw [Real.exp_sum]; exact Finset.prod_congr rfl fun i _ ↦ (Real.exp_log (hb i)).symm
  rw [hA, hB, ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- **Evidence lower bound.** Let `P θ = f θ · μ` and let `B` be a measurable set of parameters
with `KL(P θ₀ ‖ P θ) < γ` for `θ ∈ B`. Under the true i.i.d. law `P θ₀^∞`, the probability that the
evidence `∫ ∏_{i<n} f θ (ωᵢ) dπ(θ)` is below `π(B)/2 · ∏_{i<n} f θ₀ (ωᵢ) · e^{-γ n}` tends to
zero. -/
theorem tendsto_infinite_pi_evidence_lt {Θ : Type*} [MeasurableSpace Θ]
    (π : Measure Θ) [IsFiniteMeasure π] (μ : Measure X) [SigmaFinite μ]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (f : Θ → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hdensity : ∀ θ, HasDensity (P θ) μ (f θ)) (θ₀ : Θ) {B : Set Θ} (hBm : MeasurableSet B)
    {γ : ℝ} (hB : ∀ θ ∈ B, klDiv (P θ₀) (P θ) < ENNReal.ofReal γ) :
    Tendsto (fun n : ℕ ↦ Measure.infinitePi (fun _ : ℕ ↦ P θ₀)
      {ω | ∫⁻ θ, ENNReal.ofReal (∏ i : Fin n, f θ (ω i)) ∂π <
        π B / 2 * ENNReal.ofReal ((∏ i : Fin n, f θ₀ (ω i)) * Real.exp (-γ * n))})
      atTop (𝓝 0) := by
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
  -- for each `θ ∈ B`, almost surely all observations are eventually good
  have hcoord : ∀ q : X → Prop, (∀ᵐ x ∂(P θ₀), q x) → ∀ᵐ ω ∂Pinf, ∀ i, q (ω i) := by
    intro q hq
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable
      (by rwa [Measure.infinitePi_map_eval])
  have hev : ∀ θ ∈ B, ∀ᵐ ω ∂Pinf, ∀ᶠ n in atTop, good n θ ω := by
    intro θ hθ
    have hKL : klDiv (P θ₀) (P θ) ≠ ∞ := ne_top_of_lt (hB θ hθ)
    have hPQ := (klDiv_ne_top_iff.1 hKL).1
    obtain ⟨hint, hmean⟩ :=
      integral_log_sub_log_eq_neg_to_real_kl_div (hdensity θ₀) (hdensity θ) hKL
    have hlt : -γ < ∫ x, (Real.log (f θ x) - Real.log (f θ₀ x)) ∂(P θ₀) := by
      rw [hmean]; have := ENNReal.toReal_lt_of_lt_ofReal (hB θ hθ); linarith
    have hslln := TauCeti.Probability.strong_law_ae_infinitePi (P θ₀)
      ((hdensity θ).1.log.sub (hdensity θ₀).1.log) hint
    filter_upwards [hslln, hcoord _ (hPQ.ae_le (hdensity θ).ae_pos),
      hcoord _ (hdensity θ₀).ae_pos] with ω hω h1 h2
    filter_upwards [hω.eventually (lt_mem_nhds hlt), eventually_gt_atTop 0] with n hn hn0
    refine ⟨fun i _ ↦ h1 i, fun i _ ↦ h2 i, ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [smul_eq_mul] at hn
    have hmul := mul_lt_mul_of_pos_left hn hn'
    rw [← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul] at hmul
    simp only [Pi.sub_apply] at hmul
    linarith
  -- for each `θ ∈ B`, the probability of a bad sample tends to zero
  have hbadm : ∀ n θ, MeasurableSet {ω | ¬ good n θ ω} := fun n θ ↦
    ((hgood n).preimage measurable_prodMk_left).compl
  have hbad : ∀ θ ∈ B, Tendsto (fun n ↦ Pinf {ω | ¬ good n θ ω}) atTop (𝓝 0) := by
    intro θ hθ
    have h := tendsto_lintegral_of_dominated_convergence (μ := Pinf) (fun _ ↦ 1)
      (F := fun n ω ↦ {ω | ¬ good n θ ω}.indicator 1 ω) (f := 0)
      (fun n ↦ measurable_one.indicator (hbadm n θ))
      (fun n ↦ ae_of_all _ fun ω ↦ by
        by_cases h : ω ∈ {ω | ¬ good n θ ω} <;> simp [h])
      (by simp)
      (by
        filter_upwards [hev θ hθ] with ω hω
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hω] with n hn
        simp [Set.indicator, hn])
    simpa [lintegral_indicator_one (hbadm _ θ)] using h
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
  have hlim : Tendsto (fun n ↦ ∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf) atTop (𝓝 0) := by
    simp_rw [hTon]
    have h := tendsto_lintegral_of_dominated_convergence (μ := π) (fun _ ↦ 1)
      (F := fun n θ ↦ B.indicator (fun θ ↦ Pinf {ω | ¬ good n θ ω}) θ) (f := 0)
      (fun n ↦ ((measurable_measure_prodMk_left (hgood n).compl).indicator hBm))
      (fun n ↦ ae_of_all _ fun θ ↦ by
        by_cases h : θ ∈ B
        · simp [h, prob_le_one]
        · simp [h])
      (by simp)
      (ae_of_all _ fun θ ↦ by
        by_cases h : θ ∈ B
        · simpa [h] using hbad θ h
        · simp [h])
    simpa using h
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
  have h0 : Tendsto (fun n ↦ (∫⁻ ω, π ((fun θ ↦ (θ, ω)) ⁻¹' T n) ∂Pinf) / (π B / 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hlim (Or.inr hπB2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n ↦ zero_le)
    (fun n ↦ (measure_mono (hsub n)).trans (hmarkov n))

end CKSD
