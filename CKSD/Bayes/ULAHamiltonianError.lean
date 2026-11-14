module
public import CKSD.Bayes.HamiltonianSampling
public import TauCeti.Probability.Distributions.Gaussian.L2
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
/-!
# Averaged mechanical Hamiltonian discretization error

A phase-space flow preserving a Gibbs position law and standard Gaussian momentum law has
stationary momentum energy. Tonelli's theorem and the deterministic mechanical-flow error
then bound the squared one-step position error by `L² dim(E) T⁶`. This coupling estimate uses
only momentum moments and therefore places no additional moment condition on the position law.

The coupling approach follows Chewi, *Log-Concave Sampling*, August 20, 2026, Section 4.1;
the stationary comparison trajectory here is the mechanical Hamiltonian flow. Mathlib supplies
Gaussian moments, Bochner integration and Tonelli; pinned TauCeti supplies scalar Gaussian
second moments and the underlying globally Lipschitz Hamiltonian flow.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The second radial moment of the standard Gaussian is the real dimension. -/
theorem integral_norm_sq_stdGaussian : (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hf : (fun x : E ↦ ‖x‖ ^ 2) = fun x ↦ ∑ i, ⟪b i, x⟫ ^ 2 :=
    funext fun x ↦ (b.sum_sq_inner_right x).symm
  rw [hf, integral_finsetSum]
  · simp_rw [TauCeti.Probability.integral_sq_inner_stdGaussian]
    simp only [b.orthonormal.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · intro i _
    exact (memLp_two_iff_integrable_sq (by fun_prop)).1
      (TauCeti.Probability.memLp_inner_stdGaussian (b i) 2 (by simp))

/-- Extended-nonnegative version of the standard Gaussian second moment. -/
theorem lintegral_norm_sq_stdGaussian :
    (∫⁻ x : E, ENNReal.ofReal (‖x‖ ^ 2) ∂stdGaussian E) = Module.finrank ℝ E := by
  have hi : Integrable (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) :=
    by
      let b := stdOrthonormalBasis ℝ E
      have hf : (fun x : E ↦ ‖x‖ ^ 2) = fun x ↦ ∑ i, ⟪b i, x⟫ ^ 2 :=
        funext fun x ↦ (b.sum_sq_inner_right x).symm
      rw [hf]
      exact integrable_finsetSum _ fun i _ ↦
        (memLp_two_iff_integrable_sq (by fun_prop)).1
          (TauCeti.Probability.memLp_inner_stdGaussian (b i) 2 (by simp))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _), integral_norm_sq_stdGaussian]
  simp

/-- A phase-law preserving mechanical flow has stationary Gaussian momentum second moments. -/
theorem lintegral_momentum_mechanicalFlow_sq
    (π : Measure E) [IsProbabilityMeasure π] (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (hInv : ∀ s : ℝ, MeasurePreserving (mechanicalFlow G hG s)
      (π.prod (stdGaussian E)) (π.prod (stdGaussian E))) (s : ℝ) :
    (∫⁻ z : E × E, ENNReal.ofReal (‖(mechanicalFlow G hG s z).2‖ ^ 2)
      ∂π.prod (stdGaussian E)) = Module.finrank ℝ E := by
  have hm : Measurable (fun z : E × E ↦ ENNReal.ofReal (‖z.2‖ ^ 2)) := by fun_prop
  rw [(hInv s).lintegral_comp hm, lintegral_prod _ hm.aemeasurable]
  simp only [lintegral_norm_sq_stdGaussian, lintegral_const, measure_univ, mul_one]

/-- Averaging the deterministic Hamiltonian position error uses only stationary momentum energy. -/
theorem lintegral_mechanical_position_error_sq_le
    (π : Measure E) [IsProbabilityMeasure π] (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (hInv : ∀ s : ℝ, MeasurePreserving (mechanicalFlow G hG s)
      (π.prod (stdGaussian E)) (π.prod (stdGaussian E))) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ z : E × E, ENNReal.ofReal (‖(mechanicalFlow G hG T z).1 -
      (z.1 + T • z.2 - (T ^ 2 / 2) • G z.1)‖ ^ 2) ∂π.prod (stdGaussian E)) ≤
      ENNReal.ofReal ((L : ℝ) ^ 2 * (Module.finrank ℝ E) * T ^ 6) := by
  let P := π.prod (stdGaussian E)
  let A : ℝ → E × E → ℝ := fun s z ↦ ‖(mechanicalFlow G hG s z).2‖ ^ 2
  have hAc : Continuous (Function.uncurry A) :=
    ((mechanicalFlow G hG).continuous continuous_fst continuous_snd).snd.norm.pow 2
  have hAm : Measurable (fun z : (E × E) × ℝ ↦ ENNReal.ofReal (A z.2 z.1)) := by
    exact (ENNReal.measurable_ofReal.comp hAc.measurable).comp measurable_swap
  have hbound (z : E × E) : ‖(mechanicalFlow G hG T z).1 -
      (z.1 + T • z.2 - (T^2/2) • G z.1)‖^2 ≤ (L : ℝ)^2*T^5*∫ s in (0 : ℝ)..T, A s z := by
    have hc := (mechanicalFlow G hG).continuous continuous_id (continuous_const : Continuous (fun _ : ℝ ↦ z))
    have hh := mechanical_position_error_sq_le G hG
      (fun s ↦ (mechanicalFlow G hG s z).1) (fun s ↦ (mechanicalFlow G hG s z).2)
      hc.fst hc.snd (fun t _ ↦ by simpa only [Flow.map_zero, id_eq] using mechanicalFlow_fst_eq G hG z t)
      (fun t _ ↦ by simpa only [Flow.map_zero, id_eq] using mechanicalFlow_snd_eq G hG z t) hT
    simpa only [Flow.map_zero, id_eq] using hh
  have hint (z : E × E) :
      ENNReal.ofReal (∫ s in (0 : ℝ)..T, A s z) = ∫⁻ s in Ioc (0 : ℝ) T, ENNReal.ofReal (A s z) := by
    rw [intervalIntegral.integral_of_le hT]
    exact ofReal_integral_eq_lintegral_ofReal
      (((hAc.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc))
      (ae_of_all _ fun _ ↦ sq_nonneg _)
  calc _ ≤ ∫⁻ z : E × E, ENNReal.ofReal ((L : ℝ)^2*T^5*∫ s in (0 : ℝ)..T, A s z) ∂P :=
      lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal (hbound z)
    _ = ENNReal.ofReal ((L : ℝ)^2*T^5) *
        ∫⁻ z : E × E, ∫⁻ s in Ioc (0 : ℝ) T, ENNReal.ofReal (A s z) ∂volume ∂P := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ)^2*T^5), hint]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((L : ℝ)^2*T^5) *
        ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ z : E × E, ENNReal.ofReal (A s z) ∂P := by
      rw [lintegral_lintegral_swap hAm.aemeasurable]
    _ = _ := by
      simp_rw [show ∀ s, (∫⁻ z : E × E, ENNReal.ofReal (A s z) ∂P) = Module.finrank ℝ E from
        fun s ↦ lintegral_momentum_mechanicalFlow_sq π G hG hInv s]
      rw [lintegral_const]
      simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Module.finrank ℝ E : ℝ)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ)^2*T^5)]
      congr 1
      ring
end CKSD
