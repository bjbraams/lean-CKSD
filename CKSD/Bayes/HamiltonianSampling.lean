module
public import TauCeti.Geometry.Symplectic.Hamiltonian.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CKSD.Bayes.MeanFieldQuantitative
/-!
# Mechanical Hamiltonian flow and Euler position error

A globally Lipschitz force gives a canonical mechanical flow. For a C2 potential this is the
standard symplectic Hamiltonian flow, so the upstream conservation and symplectic-variation
results apply. The position error against a frozen-force quadratic step is controlled by the
time integral of squared momentum. This supports the stationary Hamiltonian coupling proof
of the ULA Wasserstein estimate (GAPS 104.45).

The Hamiltonian-flow theory is pinned TauCeti; the deterministic integral estimate uses
Mathlib calculus and the local continuous-time Cauchy-Schwarz lemma. The short-Hamiltonian-step
comparison supplies an alternative to the stationary diffusion coupling in Chewi,
Log-Concave Sampling, August 20, 2026, Theorem 4.1.2; ideal HMC invariance is discussed in Section 5.2.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace CKSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Mechanical energy on position-momentum phase space. -/
def mechanicalHamiltonian (V : E → ℝ) (z : E × E) : ℝ := V z.1 + ‖z.2‖ ^ 2 / 2

/-- The position-momentum velocity of Hamilton's equations. -/
def mechanicalVelocity (G : E → E) (z : E × E) : E × E := (z.2, -G z.1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A Lipschitz force gives a globally Lipschitz Hamiltonian velocity. -/
theorem lipschitzWith_mechanicalVelocity {G : E → E} {L : ℝ≥0} (hG : LipschitzWith L G) :
    LipschitzWith (max 1 L) (mechanicalVelocity G) := by
  change LipschitzWith (max 1 L) (fun z : E × E ↦ (z.2, -G z.1))
  simpa only [mul_one, Function.comp_def, Pi.neg_apply] using LipschitzWith.prod_snd.prodMk (hG.comp LipschitzWith.prod_fst).neg

/-- The derivative of mechanical energy consists of the potential gradient and momentum. -/
theorem hasFDerivAt_mechanicalHamiltonian (V : E → ℝ) (G : E → E)
    (hG : ∀ x, HasGradientAt V (G x) x) (z : E × E) :
    HasFDerivAt (mechanicalHamiltonian V)
      ((innerSL ℝ (G z.1)).coprod (innerSL ℝ z.2)) z := by
  have hV := (hG z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hP := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq.const_mul (1 / 2 : ℝ)
  have heq : mechanicalHamiltonian V = fun z : E × E ↦ V z.1 + (1 / 2 : ℝ) * ‖z.2‖ ^ 2 := by
    funext z
    dsimp [mechanicalHamiltonian]
    ring
  rw [heq]
  apply (hV.add hP).congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  simp [ContinuousLinearMap.coprod_apply, innerSL_apply_apply]

/-- Mechanical Hamilton's equations have velocity `(p,-gradV(q))`. -/
theorem hamiltonianVectorField_mechanicalHamiltonian (V : E → ℝ) (G : E → E)
    (hG : ∀ x, HasGradientAt V (G x) x) :
    (TauCeti.stdSymplecticForm (V := E)).hamiltonianVectorField (mechanicalHamiltonian V) =
      mechanicalVelocity G := by
  funext z
  exact TauCeti.stdSymplecticForm_hamiltonianVectorField (hasFDerivAt_mechanicalHamiltonian V G hG z)

omit [FiniteDimensional ℝ E] in
/-- Mechanical energy is twice continuously differentiable for a C2 potential. -/
theorem contDiff_mechanicalHamiltonian (V : E → ℝ) (hV : ContDiff ℝ 2 V) :
    ContDiff ℝ 2 (mechanicalHamiltonian V) :=
  (hV.comp contDiff_fst).add (((contDiff_norm_sq ℝ).comp contDiff_snd).div_const 2)

/-- The canonical mechanical flow of a globally Lipschitz force. -/
def mechanicalFlow (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G) : Flow ℝ (E × E) :=
  TauCeti.flowOfLipschitz (mechanicalVelocity G) (lipschitzWith_mechanicalVelocity hG)

/-- The mechanical flow is the symplectic Hamiltonian flow of its energy. -/
theorem mechanicalFlow_eq_hamiltonianFlow (V : E → ℝ) (G : E → E)
    (hgrad : ∀ x, HasGradientAt V (G x) x) {L : ℝ≥0} (hG : LipschitzWith L G) :
    let hX : LipschitzWith (max 1 L)
      ((TauCeti.stdSymplecticForm (V := E)).hamiltonianVectorField (mechanicalHamiltonian V)) :=
      (hamiltonianVectorField_mechanicalHamiltonian V G hgrad).symm ▸ lipschitzWith_mechanicalVelocity hG;
    mechanicalFlow G hG = (TauCeti.stdSymplecticForm (V := E)).hamiltonianFlow (mechanicalHamiltonian V) hX := by
  dsimp only
  apply Flow.ext
  intro t z
  have hder (s : ℝ) := (TauCeti.stdSymplecticForm (V := E)).hasDerivAt_hamiltonianFlow
    (mechanicalHamiltonian V) ((hamiltonianVectorField_mechanicalHamiltonian V G hgrad).symm ▸
      lipschitzWith_mechanicalVelocity hG) z s
  have hd (s : ℝ) : HasDerivAt
      (fun r ↦ (TauCeti.stdSymplecticForm (V := E)).hamiltonianFlow (mechanicalHamiltonian V)
        ((hamiltonianVectorField_mechanicalHamiltonian V G hgrad).symm ▸ lipschitzWith_mechanicalVelocity hG) r z)
      (mechanicalVelocity G ((TauCeti.stdSymplecticForm (V := E)).hamiltonianFlow (mechanicalHamiltonian V)
        ((hamiltonianVectorField_mechanicalHamiltonian V G hgrad).symm ▸ lipschitzWith_mechanicalVelocity hG) s z)) s :=
    (hder s).congr_deriv (congrFun (hamiltonianVectorField_mechanicalHamiltonian V G hgrad) _)
  have hc := TauCeti.eq_flowOfLipschitz (lipschitzWith_mechanicalVelocity hG) hd t
  simpa only [Flow.map_zero, id_eq, mechanicalFlow] using hc.symm

/-- Mechanical-flow trajectories solve Hamilton's equations. -/
theorem hasDerivAt_mechanicalFlow (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (z : E × E) (t : ℝ) :
    HasDerivAt (fun s ↦ mechanicalFlow G hG s z)
      ((mechanicalFlow G hG t z).2, -G (mechanicalFlow G hG t z).1) t :=
  TauCeti.hasDerivAt_flowOfLipschitz (lipschitzWith_mechanicalVelocity hG) z t

/-- Position along a mechanical orbit is the integral of momentum. -/
theorem mechanicalFlow_fst_eq (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (z : E × E) (t : ℝ) :
    (mechanicalFlow G hG t z).1 = z.1 + ∫ s in (0 : ℝ)..t, (mechanicalFlow G hG s z).2 := by
  have h := congrArg Prod.fst (TauCeti.flowOfLipschitz_eq_add_integral
    (lipschitzWith_mechanicalVelocity hG) z t)
  have hc : Continuous (fun s ↦ mechanicalVelocity G (mechanicalFlow G hG s z)) :=
    (lipschitzWith_mechanicalVelocity hG).continuous.comp
      ((mechanicalFlow G hG).continuous continuous_id continuous_const)
  have hi := (ContinuousLinearMap.fst ℝ E E).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
  change (mechanicalFlow G hG t z).1 = z.1 +
    (ContinuousLinearMap.fst ℝ E E) (∫ s in (0 : ℝ)..t, mechanicalVelocity G (mechanicalFlow G hG s z)) at h
  rw [← hi] at h
  exact h

/-- Momentum along a mechanical orbit is the integral of the force. -/
theorem mechanicalFlow_snd_eq (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (z : E × E) (t : ℝ) :
    (mechanicalFlow G hG t z).2 = z.2 - ∫ s in (0 : ℝ)..t, G (mechanicalFlow G hG s z).1 := by
  have h := congrArg Prod.snd (TauCeti.flowOfLipschitz_eq_add_integral
    (lipschitzWith_mechanicalVelocity hG) z t)
  have hc : Continuous (fun s ↦ mechanicalVelocity G (mechanicalFlow G hG s z)) :=
    (lipschitzWith_mechanicalVelocity hG).continuous.comp
      ((mechanicalFlow G hG).continuous continuous_id continuous_const)
  have hi := (ContinuousLinearMap.snd ℝ E E).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 t)
  change (mechanicalFlow G hG t z).2 = z.2 +
    (ContinuousLinearMap.snd ℝ E E) (∫ s in (0 : ℝ)..t, mechanicalVelocity G (mechanicalFlow G hG s z)) at h
  rw [← hi] at h
  change (mechanicalFlow G hG t z).2 = z.2 + ∫ s in (0 : ℝ)..t, -G (mechanicalFlow G hG s z).1 at h
  simpa only [intervalIntegral.integral_neg, sub_eq_add_neg] using h
omit [FiniteDimensional ℝ E] in
/-- Squared norm of a continuous time integral is bounded by length times its squared energy. -/
theorem norm_intervalIntegral_sq_le (f : ℝ → E) (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ s in (0 : ℝ)..T, f s‖ ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hT
  have hp := sq_intervalIntegral_le_length_mul_integral_sq (fun s ↦ ‖f s‖) hf.norm hT
  have hi := intervalIntegral.integral_nonneg (μ := volume) hT (fun s _ ↦ norm_nonneg (f s))
  nlinarith [norm_nonneg (∫ s in (0 : ℝ)..T, f s)]

/-- The local position error of Hamiltonian flow against its frozen-force quadratic step is
controlled only by the time integral of squared momentum. -/
theorem mechanical_position_error_sq_le (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G)
    (q p : ℝ → E) (hq : Continuous q) (hp : Continuous p)
    (hqp : ∀ t ≥ 0, q t = q 0 + ∫ s in (0 : ℝ)..t, p s)
    (hpq : ∀ t ≥ 0, p t = p 0 - ∫ s in (0 : ℝ)..t, G (q s))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖q T - (q 0 + T • p 0 - (T ^ 2 / 2) • G (q 0))‖ ^ 2 ≤
      (L : ℝ) ^ 2 * T ^ 5 * ∫ s in (0 : ℝ)..T, ‖p s‖ ^ 2 := by
  let A := ∫ s in (0 : ℝ)..T, ‖p s‖ ^ 2
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg (μ := volume) hT (fun s _ ↦ sq_nonneg _)
  let B := Real.sqrt (T * A)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B ^ 2 = T * A := Real.sq_sqrt (mul_nonneg hT hA)
  have hmove (s : ℝ) (hs : s ∈ Icc 0 T) : ‖q s - q 0‖ ≤ B := by
    have hi : (∫ r in (0 : ℝ)..s, ‖p r‖ ^ 2) ≤ A :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (ae_of_all _ fun _ ↦ sq_nonneg _) ((hp.norm.pow 2).intervalIntegrable _ _)
    have hn := norm_intervalIntegral_sq_le p hp hs.1
    rw [hqp s hs.1, add_sub_cancel_left]
    have ht : s * ∫ r in (0 : ℝ)..s, ‖p r‖ ^ 2 ≤ T * A :=
      (mul_le_mul_of_nonneg_left hi hs.1).trans (mul_le_mul_of_nonneg_right hs.2 hA)
    nlinarith [norm_nonneg (∫ r in (0 : ℝ)..s, p r)]
  let r : ℝ → E := fun s ↦ p s - p 0 + s • G (q 0)
  have hrc : Continuous r := by dsimp [r]; fun_prop
  have hr_eq (s : ℝ) (hs : 0 ≤ s) : r s = -∫ u in (0 : ℝ)..s, G (q u) - G (q 0) := by
    have hi : IntervalIntegrable (fun u ↦ G (q u)) volume 0 s := (hG.continuous.comp hq).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    dsimp only [r]
    rw [hpq s hs]
    simp only [sub_zero]
    module
  have hrbound (s : ℝ) (hs : s ∈ Icc 0 T) : ‖r s‖ ≤ s * ((L : ℝ) * B) := by
    rw [hr_eq s hs.1, norm_neg]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
      (C := (L : ℝ) * B) (f := fun u ↦ G (q u) - G (q 0)) (fun u hu ↦ by
        rw [uIoc_of_le hs.1] at hu
        exact (hG.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left
          (hmove u ⟨hu.1.le, hu.2.trans hs.2⟩) L.coe_nonneg))
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1, mul_comm] using hh
  have herr : q T - (q 0 + T • p 0 - (T ^ 2 / 2) • G (q 0)) = ∫ s in (0 : ℝ)..T, r s := by
    change _ = ∫ s in (0 : ℝ)..T, p s - p 0 + s • G (q 0)
    have h1 : IntervalIntegrable (fun s ↦ p s - p 0) volume 0 T := (hp.sub continuous_const).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ ↦ s • G (q 0)) volume 0 T := (continuous_id.smul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_smul_const, _root_.integral_id]
    rw [hqp T hT]
    simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
    module
  have hnorm : ‖∫ s in (0 : ℝ)..T, r s‖ ≤ T ^ 2 / 2 * ((L : ℝ) * B) := by
    calc _ ≤ ∫ s in (0 : ℝ)..T, ‖r s‖ := intervalIntegral.norm_integral_le_integral_norm hT
      _ ≤ ∫ s in (0 : ℝ)..T, s * ((L : ℝ) * B) :=
        intervalIntegral.integral_mono_on hT (hrc.norm.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun s : ℝ ↦ s * ((L : ℝ) * B))).intervalIntegrable 0 T)
          (fun s hs ↦ hrbound s hs)
      _ = _ := by rw [intervalIntegral.integral_mul_const, _root_.integral_id]; simp
  rw [herr]
  have hR : 0 ≤ T ^ 2 / 2 * ((L : ℝ) * B) := by positivity
  have hh : ‖∫ s in (0 : ℝ)..T, r s‖ ^ 2 ≤ (T ^ 2 / 2 * ((L : ℝ) * B)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc _ ≤ (T ^ 2 / 2 * ((L : ℝ) * B)) ^ 2 := hh
    _ = (L : ℝ) ^ 2 * T ^ 5 * A / 4 := by rw [mul_pow, mul_pow, hB2]; ring
    _ ≤ _ := by change _ ≤ (L : ℝ) ^ 2 * T ^ 5 * A; nlinarith [mul_nonneg (sq_nonneg (L : ℝ)) (mul_nonneg (pow_nonneg hT 5) hA)]

end CKSD
