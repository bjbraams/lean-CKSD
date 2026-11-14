module

public import CKSD.Bayes.ULAHamiltonianError
public import CKSD.Bayes.ULAContraction
/-!
# Wasserstein bounds from a stationary Hamiltonian coupling

A common phase-space coupling converts the mechanical discretization error into a one-step
ULA bias of at most `3 L h sqrt(d h)`. Synchronous-noise contraction and an affine recurrence
then give `exp(-alpha n h / 2) W₂(mu,pi) + 12 L sqrt(d h) / alpha`. The argument treats
extended Wasserstein distances directly, so no initial second-moment hypothesis is needed.

The stationary comparison is the short mechanical Hamiltonian trajectory. The contraction
and coupling method is the one underlying Chewi, *Log-Concave Sampling*, August 20, 2026,
Theorem 4.1.2. Pinned TauCeti supplies transport costs and Wasserstein triangle inequalities;
Mathlib supplies integration, Gaussian laws and exponential estimates.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Two maps on one probability space give an explicit quadratic transport bound. -/
theorem wasserstein_e_dist_maps_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g) :
    TauCeti.wassersteinEDist 2 (P.map f) (P.map g) ^ 2 ≤
      ∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ 2) ∂P := by
  have hc : TauCeti.IsCoupling (P.map (fun ω ↦ (f ω, g ω))) (P.map f) (P.map g) :=
    ⟨Measure.fst_map_prodMk hf hg, Measure.snd_map_prodMk hf hg⟩
  have hw := TauCeti.wassersteinEDist_rpow_le_lintegral (p := 2) measurable_edist
    (by norm_num) (by norm_num) hc
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hw
  refine hw.trans_eq ?_
  rw [lintegral_map (by fun_prop) (hf.prodMk hg)]
  apply lintegral_congr
  intro ω
  simp only [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The frozen-force quadratic position has Wasserstein error controlled by stationary energy. -/
theorem wasserstein_e_dist_mechanical_position_le
    (π : Measure E) [IsProbabilityMeasure π] (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (hInv : ∀ s : ℝ, MeasurePreserving (mechanicalFlow G hG s)
      (π.prod (stdGaussian E)) (π.prod (stdGaussian E))) {T : ℝ} (hT : 0 ≤ T) :
    TauCeti.wassersteinEDist 2
      ((π.prod (stdGaussian E)).map (fun z ↦ z.1 + T • z.2 - (T^2/2) • G z.1)) π ≤
        ENNReal.ofReal ((L : ℝ) * Real.sqrt (Module.finrank ℝ E) * T^3) := by
  let P := π.prod (stdGaussian E)
  let f : E × E → E := fun z ↦ z.1 + T • z.2 - (T^2/2) • G z.1
  let g : E × E → E := fun z ↦ (mechanicalFlow G hG T z).1
  have hGm := hG.continuous.measurable
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := ((mechanicalFlow G hG).continuous continuous_const continuous_id).fst.measurable
  have hmap : P.map g = π := by
    have h := (measurePreserving_fst (μ := π) (ν := stdGaussian E)).comp (hInv T)
    exact h.map_eq
  change TauCeti.wassersteinEDist 2 (P.map f) π ≤ _
  have hweq := congrArg (fun ν ↦ TauCeti.wassersteinEDist 2 (P.map f) ν) hmap.symm
  rw [hweq]
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).1
  have hw := wasserstein_e_dist_maps_sq_le P f g hf hg
  have he := lintegral_mechanical_position_error_sq_le π G hG hInv hT
  have hbound : (∫⁻ z, ENNReal.ofReal (‖f z - g z‖^2) ∂P) ≤
      ENNReal.ofReal ((L : ℝ)^2*(Module.finrank ℝ E)*T^6) := by
    simpa only [f, g, P, norm_sub_rev] using he
  refine (hw.trans hbound).trans_eq ?_
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (L : ℝ)*Real.sqrt (Module.finrank ℝ E)*T^3)]
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (Module.finrank ℝ E : ℝ))]
  ring
/-- One ULA step from an invariant mechanical position law has order `h^(3/2)` bias. -/
theorem wasserstein_e_dist_langevin_step_law_self_le {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure π]
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L : ℝ≥0} (hG : LipschitzWith L G)
    (hInv : ∀ s : ℝ, MeasurePreserving (mechanicalFlow G hG s)
      (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d))))
      (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))) )
    {h : ℝ} (hh : 0 ≤ h) :
    TauCeti.wassersteinEDist 2 (langevinStepLaw G h π) π ≤
      ENNReal.ofReal (3 * (L : ℝ) * h * Real.sqrt (d*h)) := by
  have hT := Real.sq_sqrt (by positivity : 0 ≤ 2*h)
  have heq : langevinStepLaw G h π =
      (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
        (fun z ↦ z.1 + Real.sqrt (2*h) • z.2 - (Real.sqrt (2*h)^2/2) • G z.1) := by
    unfold langevinStepLaw
    congr 1
    funext z
    rw [hT]
    module
  rw [heq]
  refine (wasserstein_e_dist_mechanical_position_le π G hG hInv (Real.sqrt_nonneg _)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hs : Real.sqrt (2*h) ≤ 3/2 * Real.sqrt h := by
    have h1 := Real.sq_sqrt hh
    have h2 := Real.sqrt_nonneg h
    have h3 := Real.sqrt_nonneg (2*h)
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*h)
  have hid : Real.sqrt (2*h)^3 = 2*h*Real.sqrt (2*h) := by
    calc _ = Real.sqrt (2*h)^2*Real.sqrt (2*h) := by ring
         _ = _ := by rw [hT]
  have hsd : Real.sqrt ((d : ℝ)*h) = Real.sqrt (d : ℝ)*Real.sqrt h :=
    Real.sqrt_mul (by positivity) h
  rw [hid, hsd]
  have := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (L : ℝ)*Real.sqrt (d : ℝ))
  nlinarith
/-- An affine recurrence with a supersolution has a geometric transient bound. -/
theorem ennreal_affine_recurrence_le (u : ℕ → ℝ≥0∞) (r e B : ℝ≥0∞)
    (hu : ∀ n, u (n+1) ≤ r * u n + e) (hB : r*B+e ≤ B) (n : ℕ) :
    u n ≤ r^n*u 0+B := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc u (n+1) ≤ r*u n+e := hu n
      _ ≤ r*(r^n*u 0+B)+e := by gcongr
      _ = r^(n+1)*u 0+(r*B+e) := by ring
      _ ≤ r^(n+1)*u 0+B := by gcongr

/-- A linear deficit bounds the contraction exponential on a unit interval. -/
theorem exp_neg_le_one_sub_half {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1-x/2 := by
  have hn : 0 ≤ 1-x/2 := by linarith
  have hsq : x^2 ≤ x := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp x) hn
  have hp : 1 ≤ (1-x/2)*Real.exp x := by nlinarith
  have he := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-x)).le
  have hid : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  simpa only [one_mul, mul_assoc, hid, mul_one] using he

/-- The order-sqrt-step ULA bias is a supersolution for the local error recurrence. -/
theorem ula_bias_supersolution {α β h D : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hh : 0 ≤ h) (_hD : 0 ≤ D) (hαh : α*h ≤ 1) :
    ENNReal.ofReal (Real.exp (-α*h/2)) * ENNReal.ofReal (12*β*Real.sqrt (D*h)/α) +
      ENNReal.ofReal (3*β*h*Real.sqrt (D*h)) ≤
        ENNReal.ofReal (12*β*Real.sqrt (D*h)/α) := by
  have hr : Real.exp (-α*h/2) ≤ 1-α*h/4 := by
    have he := exp_neg_le_one_sub_half (x := α*h/2) (by positivity) (by linarith)
    convert he using 1 <;> ring_nf
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hb : 0 ≤ 12*β*Real.sqrt (D*h)/α := by positivity
  have hm := mul_le_mul_of_nonneg_right hr hb
  have hid : (1-α*h/4)*(12*β*Real.sqrt (D*h)/α)+3*β*h*Real.sqrt (D*h) =
      12*β*Real.sqrt (D*h)/α := by field_simp [hα.ne']; ring
  linarith
/-- A Langevin step maps probability measures to probability measures. -/
theorem is_probability_measure_langevin_step_law {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (h : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (langevinStepLaw G h μ) := by
  unfold langevinStepLaw
  infer_instance

/-- A mechanically invariant law gives a geometric ULA bound with an order-sqrt-step bias. -/
theorem wasserstein_e_dist_iterate_langevin_step_law_le {d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure π]
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {L : ℝ≥0} (hG : LipschitzWith L G)
    (hInv : ∀ s : ℝ, MeasurePreserving (mechanicalFlow G hG s)
      (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d))))
      (π.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))))
    {α h : ℝ} (hα : 0 < α)
    (hmono : ∀ x y, α * ‖x-y‖^2 ≤ inner ℝ (G x-G y) (x-y))
    (hh : 0 ≤ h) (hstep : h*(L : ℝ)^2 ≤ α) (hαh : α*h ≤ 1)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (n : ℕ) :
    TauCeti.wassersteinEDist 2 ((langevinStepLaw G h)^[n] μ) π ≤
      ENNReal.ofReal (Real.exp (-(α*n*h/2))) * TauCeti.wassersteinEDist 2 μ π +
        ENNReal.ofReal (12*(L : ℝ)*Real.sqrt (d*h)/α) := by
  have hprob (k : ℕ) : IsProbabilityMeasure ((langevinStepLaw G h)^[k] μ) := by
    induction k with
    | zero => simpa using inferInstanceAs (IsProbabilityMeasure μ)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact is_probability_measure_langevin_step_law G h _
  let u : ℕ → ℝ≥0∞ := fun k ↦ TauCeti.wassersteinEDist 2 ((langevinStepLaw G h)^[k] μ) π
  have hu (k : ℕ) : u (k+1) ≤ ENNReal.ofReal (Real.exp (-α*h/2))*u k+
      ENNReal.ofReal (3*(L : ℝ)*h*Real.sqrt (d*h)) := by
    have := hprob k
    have := is_probability_measure_langevin_step_law G h π
    have ht := TauCeti.wassersteinEDist_triangle (p := 2) measurable_edist (by norm_num)
      (langevinStepLaw G h ((langevinStepLaw G h)^[k] μ)) (langevinStepLaw G h π) π
    have hc := wasserstein_e_dist_langevin_step_law_le hG hmono hh hstep
      ((langevinStepLaw G h)^[k] μ) π
    have hb := wasserstein_e_dist_langevin_step_law_self_le π G hG hInv hh
    simpa only [u, Function.iterate_succ_apply'] using ht.trans (add_le_add hc hb)
  have hx := ennreal_affine_recurrence_le u _ _ _ hu
    (ula_bias_supersolution hα L.coe_nonneg hh (by positivity : 0 ≤ (d : ℝ)) hαh) n
  have hp : ENNReal.ofReal (Real.exp (-α*h/2))^n = ENNReal.ofReal (Real.exp (-(α*n*h/2))) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  simpa only [u, Function.iterate_zero_apply, hp] using hx
/-- Every quadratic transport distance vanishes on a subsingleton space. -/
theorem wasserstein_e_dist_eq_zero_of_subsingleton {E : Type*} [PseudoEMetricSpace E]
    [MeasurableSpace E] [Subsingleton E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TauCeti.wassersteinEDist 2 μ ν = 0 := by
  apply le_antisymm _ zero_le
  have hw := TauCeti.wassersteinEDist_le (TauCeti.isCoupling_prod μ ν) 2
  have hf : (fun z : E × E ↦ edist z.1 z.2) = fun _ ↦ (0 : ℝ≥0∞) := by
    funext z
    rw [Subsingleton.elim z.1 z.2, edist_self]
  simpa [hf] using hw
end CKSD
