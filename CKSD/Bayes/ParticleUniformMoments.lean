module
public import CKSD.Bayes.ParticleConditionalMoments
public import Mathlib.Algebra.Ring.GeomSum
/-!
# Time-uniform normalized particle moment bounds

Geometric oscillation decay, normalized Feynman–Kac telescoping and conditional iid moment
bounds give an `Lᵖ` error of order inverse square-root particle count, uniformly in time and
terminal tests with oscillation at most one. A finite geometric series bounds the total error.
The constant is allowed to depend on the fixed mixing parameters; no sharp universal value
is asserted.

This follows Del Moral, *Feynman–Kac Formulae*, Theorem 7.4.4 and equations (7.24)–(7.26),
printed pages 244–246 (PDF pages 257–259 of the local 2004 copy). The normalized decomposition
is local; Mathlib supplies real `lpNorm` monotonicity, Minkowski's inequality and geometric
summation. Sampling and mixing ingredients are imported from local proved modules.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD
/-- Positively weighted expectation ratios are controlled by two ordinary expectation errors. -/
theorem abs_integral_div_sub_integral_div_le
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g v : X → ℝ} (hg : Measurable g) {α β D : ℝ} (hα : 0 < α)
    (hgb : ∀ x, g x ∈ Icc α β) (hvb : ∀ x, |v x| ≤ D*g x) :
    |(∫ x,v x ∂μ)/(∫ x,g x ∂μ)-(∫ x,v x ∂ν)/(∫ x,g x ∂ν)| ≤
      (1/α)*(|(∫ x,v x ∂μ)-(∫ x,v x ∂ν)|+D*|(∫ x,g x ∂μ)-(∫ x,g x ∂ν)|) := by
  have hg0 (x : X) : 0 ≤ g x := (hα.trans_le (hgb x).1).le
  have hgi (π : Measure X) [IsProbabilityMeasure π] : Integrable g π :=
    Integrable.of_bound hg.aestronglyMeasurable β (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 x)]
      exact (hgb x).2)
  have hI (π : Measure X) [IsProbabilityMeasure π] : α ≤ ∫ x,g x ∂π := by
    simpa using integral_mono_ae (integrable_const α) (hgi π) (ae_of_all _ fun x ↦ (hgb x).1)
  have hνv : |∫ x,v x ∂ν| ≤ D*(∫ x,g x ∂ν) := by
    rw [← integral_const_mul,← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((hgi ν).const_mul D)
    exact ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hvb x
  have h := abs_div_sub_div_le_of_bound (u := ∫ x,v x ∂μ) hα (hI μ) (hI ν) hνv
  simpa only [div_eq_mul_inv,one_div,mul_comm,one_mul,mul_one] using h

/-- The backwards geometric weights have a bound independent of the time horizon. -/
theorem sum_range_pow_sub_le_geometric {ρ : ℝ} (hρ : ρ ∈ Ico 0 1) (n : ℕ) :
    (∑ q ∈ Finset.range (n+1),ρ^(n-q)) ≤ 1/(1-ρ) := by
  have hrev := Finset.sum_range_reflect (fun q ↦ ρ^q) (n+1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [hrev]
  apply (le_div_iff₀ (sub_pos.2 hρ.2)).2
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hρ.1 (n+1)]
/-- Mixing and conditional iid sampling give an error bound uniform in time and test
functions for the normalized bootstrap approximation. -/
theorem exists_uniform_particle_lpNorm_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : FeynmanKacModel X)
    {εG εM : ℝ} (hG : εG ∈ Ioc 0 1) (hM : εM ∈ Ioc 0 1)
    (hpotential : ∀ n x y, εG*M.potential n y ≤ M.potential n x)
    (htransition : ∀ n x y A, MeasurableSet A →
      ENNReal.ofReal εM*M.transition n y A ≤ M.transition n x A)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C > 0, ∀ (N : ℕ), 0 < N → ∀ (ξ : ℕ → Ω → Fin N → X),
      IsBootstrapParticleSystem P M N ξ → ∀ (n : ℕ) (f : X → ℝ), Measurable f →
      (∀ x y, |f x-f y| ≤ 1) →
      lpNorm (fun ω ↦ (∑ i,f (ξ n ω i))/(N:ℝ)-∫ x,f x ∂M.filterLaw n)
        (ENNReal.ofReal p) P ≤ C/Real.sqrt N := by
  obtain ⟨K,hK,hKbase⟩ := exists_iid_empirical_mean_lpNorm_bound (X := X) p hp
  let α := εM*εG
  let ρ := 1-εM^2
  have hα : 0 < α := mul_pos hM.1 hG.1
  have hε2 : 0 < εM^2 := sq_pos_of_pos hM.1
  have hρ : ρ ∈ Ico 0 1 := by
    dsimp [ρ]
    constructor
    · nlinarith [mul_nonneg hM.1.le (sub_nonneg.2 hM.2)]
    · nlinarith
  have hq : 1 ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  refine ⟨2*K/(α^2*εM^2),div_pos (mul_pos two_pos hK) (mul_pos (sq_pos_of_pos hα) hε2),
    fun N hN ξ hξ n f hf hosc ↦ ?_⟩
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (Nat.cast_pos.2 hN)
  let x₀ := Classical.arbitrary X
  let C₀ := |f x₀|+1
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hfb (x : X) : |f x| ≤ C₀ := by
    have h := abs_add_le (f x-f x₀) (f x₀)
    rw [sub_add_cancel] at h
    dsimp [C₀]
    linarith [hosc x x₀]
  choose a g v hgm hvm hgb hvb hrep using fun q : ℕ ↦
    M.exists_normalizedTransport_test_pair hG hM hpotential htransition q (n-q) hf hC₀ hfb hosc
  let d : ℕ → ℝ := fun q ↦ ρ^(n-q)
  have hd (q : ℕ) : 0 ≤ d q := pow_nonneg hρ.1 _
  have hGabs (q : ℕ) (x : X) : |g q x| ≤ 1/α := by
    rw [abs_of_pos (hα.trans_le (hgb q x).1)]
    exact (hgb q x).2
  have hVabs (q : ℕ) (x : X) : |v q x| ≤ d q/α := by
    calc |v q x| ≤ d q*g q x := hvb q x
      _ ≤ d q*(1/α) := mul_le_mul_of_nonneg_left (hgb q x).2 (hd q)
      _ = d q/α := by ring
  let E : (X → ℝ) → ℕ → Ω → ℝ := fun test q ω ↦
    (∑ i,test (ξ q ω i))/(N:ℝ)-M.pathPredMean (fun r ↦ ξ r ω) q test
  have hEg (q : ℕ) : Measurable (E (g q) q) := measurable_particle_sampling_error M ξ hξ.1 q (hgm q) (hGabs q)
  have hEv (q : ℕ) : Measurable (E (v q) q) := measurable_particle_sampling_error M ξ hξ.1 q (hvm q) (hVabs q)
  have hMg (q : ℕ) : MemLp (E (g q) q) (ENNReal.ofReal p) P :=
    MemLp.of_bound (hEg q).aestronglyMeasurable (2*(1/α)) (ae_of_all _ fun ω ↦ by
      simpa only [Real.norm_eq_abs] using abs_particle_sampling_error_le M hN (fun r ↦ ξ r ω) q (hgm q) (hGabs q))
  have hMv (q : ℕ) : MemLp (E (v q) q) (ENNReal.ofReal p) P :=
    MemLp.of_bound (hEv q).aestronglyMeasurable (2*(d q/α)) (ae_of_all _ fun ω ↦ by
      simpa only [Real.norm_eq_abs] using abs_particle_sampling_error_le M hN (fun r ↦ ξ r ω) q (hvm q) (hVabs q))
  have hMgb (q : ℕ) : MemLp (fun ω ↦ |E (g q) q ω|) (ENNReal.ofReal p) P := by
    simpa only [Real.norm_eq_abs] using (hMg q).norm
  have hMvb (q : ℕ) : MemLp (fun ω ↦ |E (v q) q ω|) (ENNReal.ofReal p) P := by
    simpa only [Real.norm_eq_abs] using (hMv q).norm
  have hEglp (q : ℕ) : lpNorm (E (g q) q) (ENNReal.ofReal p) P ≤ K*(1/α)/Real.sqrt N := by
    exact lpNorm_particle_sampling_error_le P M hN ξ hξ hp (hgm q)
      (by positivity) (hGabs q) (by positivity)
      (fun ν hν ↦ hKbase ν hν hN (hgm q) (by positivity) (hGabs q)) q
  have hEvlp (q : ℕ) : lpNorm (E (v q) q) (ENNReal.ofReal p) P ≤ K*(d q/α)/Real.sqrt N := by
    have hdq := hd q
    exact lpNorm_particle_sampling_error_le P M hN ξ hξ hp (hvm q)
      (by positivity) (hVabs q) (by positivity)
      (fun ν hν ↦ hKbase ν hν hN (hvm q) (by positivity) (hVabs q)) q
  let G : ℕ → Ω → ℝ := fun q ω ↦ (1/α)*(|E (v q) q ω|+d q*|E (g q) q ω|)
  have hMG (q : ℕ) : MemLp (G q) (ENNReal.ofReal p) P := by
    simpa only [G,Pi.add_apply] using ((hMvb q).add ((hMgb q).const_mul (d q))).const_mul (1/α)
  have hScale (c : ℝ) (hc : 0 ≤ c) (u : Ω → ℝ) :
      lpNorm (fun ω ↦ c*u ω) (ENNReal.ofReal p) P = c*lpNorm u (ENNReal.ofReal p) P := by
    have hh := lpNorm_const_smul (𝕜 := ℝ) c u P (p := ENNReal.ofReal p)
    have hfun : c • u = (fun ω ↦ c*u ω) := by funext ω; rfl
    rw [hfun] at hh
    simp only [coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg hc] at hh
    with_reducible_and_instances exact hh
  have hGlp (q : ℕ) : lpNorm (G q) (ENNReal.ofReal p) P ≤ 2*K*d q/(α^2*Real.sqrt N) := by
    have hdq := hd q
    change lpNorm (fun ω ↦ (1/α)*(|E (v q) q ω|+d q*|E (g q) q ω|)) (ENNReal.ofReal p) P ≤ _
    rw [hScale (1/α) (by positivity)]
    calc
      (1/α)*lpNorm (fun ω ↦ |E (v q) q ω|+d q*|E (g q) q ω|) (ENNReal.ofReal p) P ≤
          (1/α)*(lpNorm (fun ω ↦ |E (v q) q ω|) (ENNReal.ofReal p) P+
            lpNorm (fun ω ↦ d q*|E (g q) q ω|) (ENNReal.ofReal p) P) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := lpNorm_add_le (hMvb q) (g := fun ω ↦ d q*|E (g q) q ω|) hq
        have hfun : ((fun ω ↦ |E (v q) q ω|)+(fun ω ↦ d q*|E (g q) q ω|)) =
            (fun ω ↦ |E (v q) q ω|+d q*|E (g q) q ω|) := by funext ω; rfl
        rw [hfun] at hh
        with_reducible_and_instances exact hh
      _ = (1/α)*(lpNorm (E (v q) q) (ENNReal.ofReal p) P+d q*lpNorm (E (g q) q) (ENNReal.ofReal p) P) := by
        rw [hScale (d q) hdq,lpNorm_fun_abs (f := E (v q) q) (hEv q).aestronglyMeasurable,lpNorm_fun_abs (f := E (g q) q) (hEg q).aestronglyMeasurable]
      _ ≤ (1/α)*(K*(d q/α)/Real.sqrt N+d q*(K*(1/α)/Real.sqrt N)) := by
        gcongr
        · exact hEvlp q
        · exact hEglp q
      _ = 2*K*d q/(α^2*Real.sqrt N) := by ring
  have hlocal (q : ℕ) (ω : Ω) :
      |M.normalizedTransport q (n-q) (empiricalMeasure N (ξ q ω)) f-
        M.normalizedTransport q (n-q) (M.pathPredictionLaw (fun r ↦ ξ r ω) q) f| ≤ G q ω := by
    let μ := empiricalMeasure N (ξ q ω)
    let ν := M.pathPredictionLaw (fun r ↦ ξ r ω) q
    let _ : IsProbabilityMeasure μ := isProbabilityMeasure_empiricalMeasure hN _
    let _ : IsProbabilityMeasure ν := M.isProbabilityMeasure_pathPredictionLaw hN _ _
    change |M.normalizedTransport q (n-q) μ f-M.normalizedTransport q (n-q) ν f| ≤ _
    rw [hrep q μ inferInstance,hrep q ν inferInstance]
    simp only [add_sub_add_left_eq_sub]
    have h := abs_integral_div_sub_integral_div_le μ ν (hgm q) hα (hgb q) (hvb q)
    calc
      |(∫ x,v q x ∂μ)/(∫ x,g q x ∂μ)-(∫ x,v q x ∂ν)/(∫ x,g q x ∂ν)| ≤
          (1/α)*(|(∫ x,v q x ∂μ)-(∫ x,v q x ∂ν)|+d q*|(∫ x,g q x ∂μ)-(∫ x,g q x ∂ν)|) := h
      _ = G q ω := by
        simp only [G,E,μ,ν,integral_empiricalMeasure_vector,FeynmanKacModel.integral_pathPredictionLaw,
          smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hsumMem : MemLp (fun ω ↦ ∑ q ∈ Finset.range (n+1),G q ω) (ENNReal.ofReal p) P :=
    memLp_finsetSum _ (fun q _ ↦ hMG q)
  have hbound (ω : Ω) : ‖(∑ i,f (ξ n ω i))/(N:ℝ)-∫ x,f x ∂M.filterLaw n‖ ≤
      ∑ q ∈ Finset.range (n+1),G q ω := by
    rw [Real.norm_eq_abs,M.particle_average_sub_filter_eq_sum_normalizedTransport hN (fun r ↦ ξ r ω) n hf hfb]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ ↦ hlocal q ω))
  have hgeo : (∑ q ∈ Finset.range (n+1),d q) ≤ 1/(1-ρ) := sum_range_pow_sub_le_geometric hρ n
  calc
    lpNorm (fun ω ↦ (∑ i,f (ξ n ω i))/(N:ℝ)-∫ x,f x ∂M.filterLaw n) (ENNReal.ofReal p) P ≤
        lpNorm (fun ω ↦ ∑ q ∈ Finset.range (n+1),G q ω) (ENNReal.ofReal p) P := lpNorm_mono_real hsumMem hbound
    _ ≤ ∑ q ∈ Finset.range (n+1),lpNorm (G q) (ENNReal.ofReal p) P := by
      have hh := lpNorm_sum_le (s := Finset.range (n+1)) (f := G) (fun q _ ↦ hMG q) hq
      have hfun : (∑ q ∈ Finset.range (n+1),G q) = (fun ω ↦ ∑ q ∈ Finset.range (n+1),G q ω) := by
        funext ω
        simp only [Finset.sum_apply]
      rw [hfun] at hh
      with_reducible_and_instances exact hh
    _ ≤ ∑ q ∈ Finset.range (n+1),2*K*d q/(α^2*Real.sqrt N) := Finset.sum_le_sum (fun q _ ↦ hGlp q)
    _ = (2*K/(α^2*Real.sqrt N))*(∑ q ∈ Finset.range (n+1),d q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ (2*K/(α^2*Real.sqrt N))*(1/(1-ρ)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = (2*K/(α^2*εM^2))/Real.sqrt N := by
      dsimp [ρ]
      rw [show 1-(1-εM^2)=εM^2 by ring]
      ring

end CKSD
