module

public import CKSD.Bayes.ParticleCentralLimit


/-!
# Fixed-time Feynman–Kac semigroups and particle fluctuations

Central limit theorems for the bootstrap particle filter of a
Feynman–Kac model. The backwards operator over `m` transitions from time `p` includes the
potentials from time `p` through time `p + m - 1`, so that the zero-step operator is the identity,
matching the normalization of the filtering laws of `CKSD.FeynmanKacModel`.

## Main definitions

* `CKSD.FeynmanKacModel.backwardOperator`: the backwards Feynman–Kac operator.
* `CKSD.FeynmanKacModel.particleAverageAsymptoticVariance`,
  `CKSD.FeynmanKacModel.particleLikelihoodAsymptoticVariance`: the asymptotic variances of the
  particle average and of the normalized likelihood estimate.

## Main results

* `CKSD.FeynmanKacModel.integral_backward_operator`: the semigroup identity
  `γₚ(Q_{p,p+m} f) = γ_{p+m}(f)`.
* `CKSD.sqrt_mul_particle_likelihood_mul_average_sub`: the telescoping decomposition of the
  particle error into local errors.
* `CKSD.tendsto_in_distribution_particle_average`,
  `CKSD.tendsto_in_distribution_particle_likelihood`: fixed-time central limit theorems.

The central limit theorems follow from the telescoping decomposition, the central limit theorem
`CKSD.tendsto_in_distribution_sum_local_error` for the summed local errors, and Slutsky's theorem.

Source: GAPS 104.59.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Backwards Feynman–Kac operator over `m` transitions starting at time `p`. -/
def FeynmanKacModel.backwardOperator {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p : ℕ) : ℕ → (X → ℝ) → X → ℝ
  | 0, f => f
  | m + 1, f => fun x ↦ M.potential p x *
      ∫ y, M.backwardOperator (p + 1) m f y ∂M.transition p x

/-- Asymptotic variance of the bootstrap particle average of `f` at time `n`:
`∑_{p ≤ n} 𝛈ₚ((Q_{p,n}(f - 𝛈ₙ f))²) / 𝛈ₚ(Q_{p,n} 1)²`, with `𝛈ₚ` the filtering law and `Q_{p,n}`
the backwards operator over `n - p` transitions from time `p`. -/
def FeynmanKacModel.particleAverageAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) : ℝ :=
  let centered := fun x ↦ f x - ∫ y, f y ∂M.filterLaw n
  ∑ p ∈ Finset.range (n + 1),
    (∫ x, (M.backwardOperator p (n - p) centered x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2

/-- Asymptotic variance of the particle likelihood estimate at time `n`, normalized by the true
likelihood: `∑_{p ≤ n} (𝛈ₚ((Q_{p,n} 1)²) / 𝛈ₚ(Q_{p,n} 1)² - 1)`. -/
def FeynmanKacModel.particleLikelihoodAsymptoticVariance {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1),
    ((∫ x, (M.backwardOperator p (n - p) (fun _ ↦ 1) x) ^ 2 ∂M.filterLaw p) /
      (∫ x, M.backwardOperator p (n - p) (fun _ ↦ 1) x ∂M.filterLaw p) ^ 2 - 1)

/-- With unit potentials, the backwards operator preserves the constant one function. -/
theorem FeynmanKacModel.backward_operator_one_of_potential_eq_one
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    (hpotential : ∀ p x, M.potential p x = 1) (p m : ℕ) :
    M.backwardOperator p m (fun _ ↦ 1) = fun _ ↦ 1 := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    funext x
    have := M.isMarkov_transition p
    simp [FeynmanKacModel.backwardOperator, ih, hpotential]

/-- At time zero the likelihood estimate is deterministic and its asymptotic variance is zero. -/
@[simp] theorem FeynmanKacModel.particle_likelihood_asymptotic_variance_zero
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) :
    M.particleLikelihoodAsymptoticVariance 0 = 0 := by
  simp [FeynmanKacModel.particleLikelihoodAsymptoticVariance, FeynmanKacModel.backwardOperator]

/-- Unit observation potentials give zero likelihood-estimation asymptotic variance. -/
theorem FeynmanKacModel.particle_likelihood_asymptotic_variance_eq_zero_of_potential_eq_one
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X)
    (hpotential : ∀ p x, M.potential p x = 1) (n : ℕ) :
    M.particleLikelihoodAsymptoticVariance n = 0 := by
  simp [FeynmanKacModel.particleLikelihoodAsymptoticVariance,
    M.backward_operator_one_of_potential_eq_one hpotential]

section Telescoping

variable {X : Type*} [MeasurableSpace X]

namespace FeynmanKacModel

/-- The backwards operator maps bounded measurable functions to bounded measurable functions. -/
private theorem measurable_and_bounded_backward_operator (M : FeynmanKacModel X) (p m : ℕ)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Measurable (M.backwardOperator p m f) ∧ ∃ K, ∀ x, |M.backwardOperator p m f x| ≤ K := by
  induction m generalizing p with
  | zero => exact ⟨hf, C, hC⟩
  | succ m ih =>
    obtain ⟨hm, K, hK⟩ := ih (p + 1)
    obtain ⟨a, b, ha, hab⟩ := M.potential_bounds p
    have := M.isMarkov_transition p
    refine ⟨(M.measurable_potential p).mul (M.measurable_integral_transition p hm), b * K,
      fun x ↦ ?_⟩
    change |M.potential p x * ∫ y, M.backwardOperator (p + 1) m f y ∂M.transition p x| ≤ b * K
    rw [abs_mul, abs_of_pos (ha.trans_le (hab x).1)]
    exact mul_le_mul (hab x).2 (abs_integral_le_of_abs_le hm hK) (abs_nonneg _)
      ((ha.trans_le (hab x).1).le.trans (hab x).2)

/-- Semigroup property of the backwards operator: `γₚ(Q_{p,p+m} f) = γ_{p+m}(f)`. -/
theorem integral_backward_operator (M : FeynmanKacModel X) (p m : ℕ) {f : X → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∫ x, M.backwardOperator p m f x ∂M.unnormalizedLaw p = ∫ x, f x ∂M.unnormalizedLaw (p + m) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    obtain ⟨hm, K, hK⟩ := M.measurable_and_bounded_backward_operator (p + 1) m hf hC
    rw [show p + (m + 1) = p + 1 + m by omega, ← ih (p + 1),
      M.integral_unnormalized_law_succ p hm hK]
    rfl

end FeynmanKacModel

/-- Telescoping sums: if `b (p + 1) = a p` for `p < n`, then `∑_{p ≤ n} (a p - b p) = a n - b 0`. -/
private theorem sum_range_sub_eq_of_succ_eq (a b : ℕ → ℝ) (n : ℕ)
    (h : ∀ p < n, b (p + 1) = a p) : ∑ p ∈ Finset.range (n + 1), (a p - b p) = a n - b 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih fun p hp ↦ h p (by omega), h n (by omega)]
    ring

/-- Telescoping decomposition of the particle error along a path: the scaled error
`√N (γᴺₙ(h) - γₙ(h))` of the particle approximation of the unnormalized measure is the sum of the
local errors of the generations `p ≤ n` in the directions `Q_{p,n} h`. -/
theorem sqrt_mul_particle_likelihood_mul_average_sub (M : FeynmanKacModel X) {N : ℕ}
    (x : ℕ → Fin (N + 1) → X) (n : ℕ) {h : X → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) :
    Real.sqrt (N + 1) * (M.particleLikelihood x n * ((∑ i, h (x n i)) / (N + 1)) -
        ∫ y, h y ∂M.unnormalizedLaw n) =
      ∑ p ∈ Finset.range (n + 1),
        M.localError (fun p ↦ M.backwardOperator p (n - p) h) x p := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hs : Real.sqrt (N + 1) ^ 2 = N + 1 := Real.sq_sqrt hN.le
  have hs0 : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.2 hN
  have hloc : ∀ p, M.localError (fun p ↦ M.backwardOperator p (n - p) h) x p =
      Real.sqrt (N + 1) * (M.particleLikelihood x p *
          ((∑ i, M.backwardOperator p (n - p) h (x p i)) / (N + 1)) -
        M.particleLikelihood x p * M.pathPredMean x p (M.backwardOperator p (n - p) h)) := by
    intro p
    simp only [FeynmanKacModel.localError]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    rw [div_eq_iff hs0.ne']
    field_simp
    rw [hs]
    ring
  rw [Finset.sum_congr rfl fun p _ ↦ hloc p, ← Finset.mul_sum, sum_range_sub_eq_of_succ_eq]
  · congr 1
    rw [Nat.sub_self, Nat.sub_zero, FeynmanKacModel.particle_likelihood_zero, one_mul]
    congr 1
    have := M.integral_backward_operator 0 n hh hC
    rw [zero_add] at this
    exact this.symm
  · intro p hp
    have hn : n - p = n - (p + 1) + 1 := by omega
    obtain ⟨hm, K, hK⟩ := M.measurable_and_bounded_backward_operator (p + 1) (n - (p + 1)) hh hC
    have hG : 0 < ∑ i, M.potential p (x p i) :=
      Finset.sum_pos (fun i _ ↦ M.potential_pos p _) Finset.univ_nonempty
    rw [hn, FeynmanKacModel.path_pred_mean_succ, M.integral_particle_prediction_law p (x p) hm hK]
    simp only [FeynmanKacModel.particleLikelihood, Finset.prod_range_succ,
      FeynmanKacModel.backwardOperator]
    push_cast
    field_simp

end Telescoping

section Limits

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The functions `Q_{p,n} h`, `p ∈ ℕ`, are uniformly bounded. -/
private theorem exists_abs_backward_operator_sub_le (M : FeynmanKacModel X) (n : ℕ) {h : X → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ∃ B, ∀ p x, |M.backwardOperator p (n - p) h x| ≤ B := by
  choose _ K hK using fun p ↦ M.measurable_and_bounded_backward_operator p (n - p) hh hC
  refine ⟨|C| + ∑ p ∈ Finset.range n, |K p|, fun p x ↦ ?_⟩
  rcases lt_or_ge p n with hp | hp
  · refine (hK p x).trans ((le_abs_self _).trans ?_)
    have := Finset.single_le_sum (f := fun p ↦ |K p|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_range.2 hp)
    linarith [abs_nonneg C]
  · rw [Nat.sub_eq_zero_of_le hp]
    have : 0 ≤ ∑ p ∈ Finset.range n, |K p| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    exact (hC x).trans (by linarith [le_abs_self C])

/-- The total masses of the unnormalized Feynman–Kac measures are positive. -/
private theorem unnormalized_law_real_univ_pos (M : FeynmanKacModel X) (p : ℕ) :
    0 < (M.unnormalizedLaw p).real univ :=
  ENNReal.toReal_pos (M.unnormalized_law_univ_ne_zero p) (measure_ne_top _ _)

/-- `𝛈ₚ(Q_{p,n} h) = γₙ(h) / γₚ(1)` for `p ≤ n`. -/
private theorem integral_backward_operator_filter_law (M : FeynmanKacModel X) {p n : ℕ}
    (hpn : p ≤ n) {h : X → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ∫ x, M.backwardOperator p (n - p) h x ∂M.filterLaw p =
      ((M.unnormalizedLaw p).real univ)⁻¹ * ∫ x, h x ∂M.unnormalizedLaw n := by
  rw [M.integral_filter_law, M.integral_backward_operator p (n - p) hh hC, Nat.add_sub_cancel' hpn]

/-- Convergence in distribution to the identity under a given law, from convergence in
distribution to a variable with that law. -/
private theorem tendsto_in_distribution_id_of_map_eq {Y Y' : ℕ → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} (h : TendstoInDistribution Y atTop Z (fun _ ↦ P) μ')
    (hY : Y = Y') {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : μ'.map Z = ν) :
    TendstoInDistribution Y' atTop id (fun _ ↦ P) ν := by
  subst hY
  refine ⟨h.forall_aemeasurable, aemeasurable_id, ?_⟩
  have e : (⟨ν.map id, inferInstance⟩ : ProbabilityMeasure ℝ) = ⟨μ'.map Z, inferInstance⟩ :=
    Subtype.ext (by simp [hν])
  rw [e]
  exact h.tendsto

/-- Convergence in probability from mean-absolute convergence. -/
private theorem tendsto_in_measure_of_tendsto_integral_abs_sub {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {c K : ℝ}
    (hm : ∀ N, Measurable (Y N)) (hK : ∀ N ω, |Y N ω| ≤ K)
    (h : Tendsto (fun N ↦ ∫ ω, |Y N ω - c| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ ↦ c) := by
  rw [tendsto_in_measure_iff_measure_real_lt_dist]
  intro ε hε
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun N ↦ ?_) (by simpa using h.div_const ε)
  have hi : Integrable (fun ω ↦ |Y N ω - c|) P :=
    Integrable.of_bound (continuous_abs.measurable.comp
      ((hm N).sub measurable_const)).aestronglyMeasurable (K + |c|) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_abs]; exact (abs_sub _ _).trans (by linarith [hK N ω]))
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ abs_nonneg _) hi ε
  calc P.real {ω | ε < dist (Y N ω) c} ≤ P.real {ω | ε ≤ |Y N ω - c|} :=
        measureReal_mono fun ω hω ↦ by
          simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢; exact hω.le
    _ ≤ (∫ ω, |Y N ω - c| ∂P) / ε := by rw [le_div_iff₀ hε, mul_comm]; exact hM

end Limits

/-- GAPS 104.59: central limit theorem for the bootstrap particle filter at a fixed time `n`.
For a bounded measurable `f`, `√N (N⁻¹ ∑ᵢ f(ξᵢ) - 𝛈ₙ f)` converges in distribution to the centred
normal law with variance `particleAverageAsymptoticVariance n f`. -/
theorem tendsto_in_distribution_particle_average {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (n : ℕ) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ Real.sqrt (N + 1) *
        ((∑ i, f (ξ N n ω i)) / (N + 1) - ∫ x, f x ∂M.filterLaw n)) atTop id (fun _ ↦ P)
      (gaussianReal 0 (Real.toNNReal (M.particleAverageAsymptoticVariance n f))) := by
  obtain ⟨C, hC⟩ := hb
  set c := ∫ x, f x ∂M.filterLaw n with hc
  have hh : Measurable fun x ↦ f x - c := hf.sub measurable_const
  have hhC : ∀ x, |f x - c| ≤ C + |c| := fun x ↦ (abs_sub _ _).trans (by linarith [hC x])
  obtain ⟨B, hB⟩ := exists_abs_backward_operator_sub_le M n hh hhC
  have hφ : ∀ p, Measurable (M.backwardOperator p (n - p) fun x ↦ f x - c) := fun p ↦
    (M.measurable_and_bounded_backward_operator p (n - p) hh hhC).1
  set Γ := (M.unnormalizedLaw n).real univ with hΓ
  have hΓ0 : 0 < Γ := unnormalized_law_real_univ_pos M n
  have hpath : ∀ N, Measurable fun ω (q : ℕ) ↦ ξ N q ω := fun N ↦
    measurable_pi_iff.2 fun q ↦ (hξ N).1 q
  -- a positive lower bound for the likelihood estimates
  choose a b ha hab using M.potential_bounds
  set c0 := min (∏ q ∈ Finset.range n, a q) Γ with hc0
  have hc0 : 0 < c0 := lt_min (Finset.prod_pos fun q _ ↦ ha q) hΓ0
  have hLlow : ∀ N ω, c0 ≤ M.particleLikelihood (fun q ↦ ξ N q ω) n := fun N ω ↦
    (min_le_left _ _).trans (Finset.prod_le_prod₀ (fun q _ ↦ (ha q).le) fun q _ ↦ by
      rw [le_div_iff₀ (by positivity)]
      simpa [mul_comm] using Finset.sum_le_sum
        fun i (_ : i ∈ (Finset.univ : Finset (Fin (N + 1)))) ↦ (hab q (ξ N q ω i)).1)
  obtain ⟨⟨K, hK⟩, hL1⟩ := tendsto_integral_abs_particle_likelihood_sub P M ξ hξ n
  have hY := tendsto_in_measure_of_tendsto_integral_abs_sub
    (fun N ↦ (M.measurable_particle_likelihood n).comp (hpath N)) hK hL1
  have hgc : Continuous fun z : ℝ × ℝ ↦ z.1 / max z.2 c0 :=
    continuous_fst.div (continuous_snd.max continuous_const) fun z ↦
      (lt_max_of_lt_right hc0).ne'
  have hS := (tendsto_in_distribution_sum_local_error P M ξ hξ _ hφ hB
    n).continuous_comp_prodMk_of_tendstoInMeasure_const hgc hY
    fun N ↦ ((M.measurable_particle_likelihood n).comp (hpath N)).aemeasurable
  have hint0 : ∫ x, (f x - c) ∂M.unnormalizedLaw n = 0 := by
    have hfi : Integrable f (M.unnormalizedLaw n) := Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
    rw [integral_sub hfi (integrable_const c), integral_const, smul_eq_mul, ← hΓ, hc,
      M.integral_filter_law, ← hΓ]
    field_simp
    ring
  refine tendsto_in_distribution_id_of_map_eq hS ?_ ?_
  · funext N ω
    have := sqrt_mul_particle_likelihood_mul_average_sub M (fun p ↦ ξ N p ω) n hh hhC
    have hL := hLlow N ω
    rw [hint0] at this
    simp only [← this, Function.comp_apply, max_eq_left hL, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_zero]
    have hL0 : M.particleLikelihood (fun q ↦ ξ N q ω) n ≠ 0 := (hc0.trans_le hL).ne'
    push_cast
    field_simp
  · have hcomp : (fun y : ℝ ↦ (id y, Γ).1 / max (id y, Γ).2 c0) = (· * Γ⁻¹) := funext fun y ↦ by
      simp only [id, div_eq_mul_inv]
      rw [max_eq_left (min_le_right _ _)]
    rw [hcomp, gaussianReal_map_mul_const, mul_zero]
    congr 1
    have hone : ∀ x : X, |(fun _ ↦ (1 : ℝ)) x| ≤ 1 := fun _ ↦ by simp
    have hV0 : 0 ≤ ∑ p ∈ Finset.range (n + 1), M.localVariance
        (fun p ↦ M.backwardOperator p (n - p) fun x ↦ f x - c) p :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    have hvar : (Γ⁻¹) ^ 2 * ∑ p ∈ Finset.range (n + 1), M.localVariance
        (fun p ↦ M.backwardOperator p (n - p) fun x ↦ f x - c) p =
        M.particleAverageAsymptoticVariance n f := by
      rw [Finset.mul_sum, FeynmanKacModel.particleAverageAsymptoticVariance]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      have hΓp := unnormalized_law_real_univ_pos M p
      simp only [FeynmanKacModel.localVariance]
      rw [integral_backward_operator_filter_law M hpn hh hhC, hint0, mul_zero,
        integral_backward_operator_filter_law M hpn measurable_const hone]
      simp only [sub_zero, integral_const, smul_eq_mul, mul_one, ← hΓ, ← hc]
      field_simp
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hV0]
    rw [Real.coe_toNNReal _ (hvar ▸ mul_nonneg (sq_nonneg _) hV0), ← hvar, inv_pow]

/-- GAPS 104.59: central limit theorem for the particle likelihood estimate at a fixed time `n`.
The relative error `√N (Ẑₙ / Zₙ - 1)` converges in distribution to the centred normal law with
variance `particleLikelihoodAsymptoticVariance n`. -/
theorem tendsto_in_distribution_particle_likelihood {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    (ξ : ∀ N : ℕ, ℕ → Ω → Fin (N + 1) → X)
    (hξ : ∀ N, IsBootstrapParticleSystem P M (N + 1) (ξ N)) (n : ℕ) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ Real.sqrt (N + 1) *
        (M.particleLikelihood (fun p ↦ ξ N p ω) n / (M.unnormalizedLaw n).real univ - 1))
      atTop id (fun _ ↦ P)
      (gaussianReal 0 (Real.toNNReal (M.particleLikelihoodAsymptoticVariance n))) := by
  have hone : ∀ x : X, |(fun _ ↦ (1 : ℝ)) x| ≤ 1 := fun _ ↦ by simp
  obtain ⟨B, hB⟩ := exists_abs_backward_operator_sub_le M n measurable_const hone
  have hφ : ∀ p, Measurable (M.backwardOperator p (n - p) fun _ ↦ (1 : ℝ)) := fun p ↦
    (M.measurable_and_bounded_backward_operator p (n - p) measurable_const hone).1
  set Γ := (M.unnormalizedLaw n).real univ with hΓ
  have hΓ0 : 0 < Γ := unnormalized_law_real_univ_pos M n
  have hS := (tendsto_in_distribution_sum_local_error P M ξ hξ _ hφ hB n).continuous_comp
    (g := fun y ↦ Γ⁻¹ * y) (continuous_const.mul continuous_id)
  refine tendsto_in_distribution_id_of_map_eq hS ?_ ?_
  · funext N ω
    have := sqrt_mul_particle_likelihood_mul_average_sub M (fun p ↦ ξ N p ω) n
      measurable_const hone
    simp only [Function.comp_apply, ← this, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, integral_const, smul_eq_mul, ← hΓ]
    push_cast
    field_simp
  · have hcomp : (fun y ↦ Γ⁻¹ * y) ∘ (id : ℝ → ℝ) = (Γ⁻¹ * ·) := rfl
    rw [hcomp, gaussianReal_map_const_mul, mul_zero]
    congr 1
    have hV0 : 0 ≤ ∑ p ∈ Finset.range (n + 1), M.localVariance
        (fun p ↦ M.backwardOperator p (n - p) fun _ ↦ (1 : ℝ)) p :=
      Finset.sum_nonneg fun p _ ↦ mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    have hvar : (Γ⁻¹) ^ 2 * ∑ p ∈ Finset.range (n + 1), M.localVariance
        (fun p ↦ M.backwardOperator p (n - p) fun _ ↦ (1 : ℝ)) p =
        M.particleLikelihoodAsymptoticVariance n := by
      rw [Finset.mul_sum, FeynmanKacModel.particleLikelihoodAsymptoticVariance]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      obtain ⟨hm, K, hK⟩ := M.measurable_and_bounded_backward_operator p (n - p)
        measurable_const hone
      have hΓp := unnormalized_law_real_univ_pos M p
      simp only [FeynmanKacModel.localVariance]
      rw [integral_sub_integral_sq hm hK,
        integral_backward_operator_filter_law M hpn measurable_const hone]
      simp only [integral_const, smul_eq_mul, mul_one, ← hΓ]
      field_simp
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hV0]
    rw [Real.coe_toNNReal _ (hvar ▸ mul_nonneg (sq_nonneg _) hV0), ← hvar, inv_pow]

/-- A zero-step backwards operator is the identity. -/
@[simp] theorem FeynmanKacModel.backward_operator_zero {X : Type*} [MeasurableSpace X]
    (M : FeynmanKacModel X) (p : ℕ) (f : X → ℝ) : M.backwardOperator p 0 f = f := rfl

/-- Each particle-average asymptotic variance is nonnegative. -/
theorem FeynmanKacModel.particle_average_asymptotic_variance_nonneg
    {X : Type*} [MeasurableSpace X] (M : FeynmanKacModel X) (n : ℕ) (f : X → ℝ) :
    0 ≤ M.particleAverageAsymptoticVariance n f := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)) (sq_nonneg _)

end CKSD
