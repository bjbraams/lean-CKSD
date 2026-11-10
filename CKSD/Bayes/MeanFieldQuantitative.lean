module
public import CKSD.Bayes.MeanFieldCoupling
public import Mathlib.Algebra.Order.Chebyshev
/-!
# Quantitative synchronous coupling with residual forcing

The averaged error satisfies an integral Grönwall inequality. Its uniform bound gives a
second Grönwall inequality for each particle. Continuous-time Cauchy–Schwarz and finite-sum
Jensen then bound each squared error by the particle's residual energy and the mean residual
energy, with a constant depending only on time and the two drift Lipschitz constants.

Mathlib supplies interval integration and finite-sum Jensen; TauCeti supplies the integral
Grönwall inequality. No probabilistic assumptions enter these deterministic estimates.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace CKSD

/-- Averaged integral coupling inequalities give a uniform bound for each coordinate. -/
theorem finite_coupling_gronwall {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (R : Fin N → ℝ) (hR : ∀ i, 0 ≤ R i)
    {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (h : ∀ i t, t ∈ Icc (0 : ℝ) T →
      u i t ≤ R i + a * (∫ s in (0 : ℝ)..t, u i s) +
        b * (∫ s in (0 : ℝ)..t, (N : ℝ)⁻¹ * ∑ j, u j s)) :
    ∀ i t, t ∈ Icc (0 : ℝ) T → u i t ≤
      (R i + b * T * ((N : ℝ)⁻¹ * ∑ j, R j) * Real.exp ((a + b) * T)) * Real.exp (a * T) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hni : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hn.le
  let U : ℝ → ℝ := fun s ↦ (N : ℝ)⁻¹ * ∑ j, u j s
  let A : ℝ := (N : ℝ)⁻¹ * ∑ j, R j
  have hA : 0 ≤ A := mul_nonneg hni (Finset.sum_nonneg fun i _ ↦ hR i)
  have hU : Continuous U := (continuous_finsetSum _ fun i _ ↦ hu i).const_mul _
  have hiU (t : ℝ) : (∫ s in (0 : ℝ)..t, U s) = (N : ℝ)⁻¹ * ∑ j, ∫ s in (0 : ℝ)..t, u j s := by
    rw [show U = fun s ↦ (N : ℝ)⁻¹ * ∑ j, u j s from rfl, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ ↦ (hu i).intervalIntegrable _ _]
  have hUineq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      U t ≤ A + (a + b) * ∫ s in (0 : ℝ)..t, U s := by
    calc U t ≤ (N : ℝ)⁻¹ * ∑ i, (R i + a * (∫ s in (0 : ℝ)..t, u i s) +
          b * (∫ s in (0 : ℝ)..t, U s)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ h i t ht) hni
      _ = A + (a + b) * ∫ s in (0 : ℝ)..t, U s := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, hiU, A]
        field_simp
        ring
  have hUb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : U t ≤ A * Real.exp ((a + b) * T) := by
    refine (TauCeti.le_mul_exp_of_le_add_mul_integral hU.continuousOn (add_nonneg ha hb)
      hUineq t ht).trans ?_
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left ht.2 (add_nonneg ha hb))) hA
  have hiUb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ s in (0 : ℝ)..t, U s) ≤ T * A * Real.exp ((a + b) * T) := by
    calc (∫ s in (0 : ℝ)..t, U s) ≤ ∫ s in (0 : ℝ)..t, A * Real.exp ((a + b) * T) :=
        intervalIntegral.integral_mono_on ht.1 (hU.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun s hs ↦ hUb s ⟨hs.1, hs.2.trans ht.2⟩)
      _ = t * A * Real.exp ((a + b) * T) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hA) (Real.exp_pos _).le
  intro i t ht
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : u i s ≤
      (R i + b * T * A * Real.exp ((a + b) * T)) + a * ∫ r in (0 : ℝ)..s, u i r := by
    have h1 := h i s hs
    have h2 := mul_le_mul_of_nonneg_left (hiUb s hs) hb
    nlinarith
  refine (TauCeti.le_mul_exp_of_le_add_mul_integral (hu i).continuousOn ha hi t ht).trans ?_
  rw [sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 ha))
    (add_nonneg (hR i) (by positivity))

/-- Cauchy–Schwarz for a continuous scalar integral on a finite time interval. -/
theorem sq_intervalIntegral_le_length_mul_integral_sq (r : ℝ → ℝ) (hr : Continuous r)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, r s) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, r s ^ 2 := by
  rcases hT.eq_or_lt with rfl | hT
  · simp
  let c := ∫ s in (0 : ℝ)..T, r s
  have hnon := intervalIntegral.integral_nonneg (μ := volume) hT.le
    (fun s _ ↦ sq_nonneg (T * r s - c))
  have heq : (∫ s in (0 : ℝ)..T, (T * r s - c) ^ 2) =
      T ^ 2 * (∫ s in (0 : ℝ)..T, r s ^ 2) - T * c ^ 2 := by
    calc _ = ∫ s in (0 : ℝ)..T, T ^ 2 * r s ^ 2 - (2 * T * c) * r s + c ^ 2 := by
              congr 1
              funext s
              ring
      _ = _ := by
        have h1 : IntervalIntegrable (fun s ↦ T ^ 2 * r s ^ 2) volume 0 T :=
          (show Continuous (fun s ↦ T ^ 2 * r s ^ 2) by fun_prop).intervalIntegrable _ _
        have h2 : IntervalIntegrable (fun s ↦ (2 * T * c) * r s) volume 0 T :=
          (hr.const_mul _).intervalIntegrable _ _
        rw [intervalIntegral.integral_add (h1.sub h2) (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        change T ^ 2 * _ - 2 * T * c * c + T * c ^ 2 = _
        ring
  rw [heq] at hnon
  nlinarith

/-- Squared averaged coupling errors are controlled by individual and averaged residual energy. -/
theorem finite_coupling_gronwall_sq {N : ℕ} (hN : 0 < N) (u r : Fin N → ℝ → ℝ)
    (hu : ∀ i, Continuous (u i)) (hu0 : ∀ i t, 0 ≤ u i t)
    (hr : ∀ i, Continuous (r i)) (hr0 : ∀ i t, 0 ≤ r i t)
    {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (h : ∀ i t, t ∈ Icc (0 : ℝ) T →
      u i t ≤ (∫ s in (0 : ℝ)..T, r i s) + a * (∫ s in (0 : ℝ)..t, u i s) +
        b * (∫ s in (0 : ℝ)..t, (N : ℝ)⁻¹ * ∑ j, u j s)) :
    ∀ i t, t ∈ Icc (0 : ℝ) T → u i t ^ 2 ≤
      (2 * T * Real.exp (a * T) ^ 2 * (1 + (b * T * Real.exp ((a + b) * T)) ^ 2)) *
        ((∫ s in (0 : ℝ)..T, r i s ^ 2) + (N : ℝ)⁻¹ * ∑ j, ∫ s in (0 : ℝ)..T, r j s ^ 2) := by
  let R (i : Fin N) := ∫ s in (0 : ℝ)..T, r i s
  let V (i : Fin N) := ∫ s in (0 : ℝ)..T, r i s ^ 2
  let A := (N : ℝ)⁻¹ * ∑ j, R j
  let B := (N : ℝ)⁻¹ * ∑ j, V j
  let q := b * T * Real.exp ((a + b) * T)
  have hR (i : Fin N) : 0 ≤ R i := intervalIntegral.integral_nonneg hT (fun s _ ↦ hr0 i s)
  have hV (i : Fin N) : 0 ≤ V i := intervalIntegral.integral_nonneg hT (fun s _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ hV i)
  have hsq (i : Fin N) : R i ^ 2 ≤ T * V i := sq_intervalIntegral_le_length_mul_integral_sq _ (hr i) hT
  have hAsq : A ^ 2 ≤ T * B := by
    calc A ^ 2 ≤ (N : ℝ)⁻¹ * ∑ j, R j ^ 2 := by
            simpa only [Finset.card_univ, Fintype.card_fin, div_eq_inv_mul] using
              (sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := R))
      _ ≤ (N : ℝ)⁻¹ * ∑ j, T * V j :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hsq j) (by positivity)
      _ = T * B := by dsimp [B]; rw [← Finset.mul_sum]; ring
  have hbound := finite_coupling_gronwall hN u hu R hR ha hb hT h
  intro i t ht
  have hbnd : u i t ≤ (R i + q * A) * Real.exp (a * T) := by
    convert hbound i t ht using 1
    dsimp [q, A]
    ring
  have hsq1 : u i t ^ 2 ≤ (R i + q * A) ^ 2 * Real.exp (a * T) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hu0 i t) hbnd 2
  have hsq2 : (R i + q * A) ^ 2 ≤ 2 * (R i ^ 2 + q ^ 2 * A ^ 2) := by nlinarith [sq_nonneg (R i - q * A)]
  have hsq3 : R i ^ 2 + q ^ 2 * A ^ 2 ≤ T * (V i + q ^ 2 * B) := by
    have := mul_le_mul_of_nonneg_left hAsq (sq_nonneg q)
    nlinarith [hsq i]
  have hsq4 : V i + q ^ 2 * B ≤ (1 + q ^ 2) * (V i + B) := by nlinarith [mul_nonneg (sq_nonneg q) (hV i)]
  calc u i t ^ 2 ≤ (2 * T * (1 + q ^ 2) * (V i + B)) * Real.exp (a * T) ^ 2 := by
        exact hsq1.trans (mul_le_mul_of_nonneg_right
          (hsq2.trans (by nlinarith [hsq3, mul_le_mul_of_nonneg_left hsq4 hT])) (sq_nonneg _))
    _ = _ := by dsimp [q, V, B]; ring

/-- The empirical interaction difference is bounded by a particle's error plus the mean error. -/
theorem norm_mean_interaction_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (K : E → E → E) {L : ℝ≥0}
    (hK : LipschitzWith L (Function.uncurry K)) (x y : Fin N → E) (i : Fin N) :
    ‖(N : ℝ)⁻¹ • ∑ j, (K (x i) (x j) - K (y i) (y j))‖ ≤
      L * (‖x i - y i‖ + (N : ℝ)⁻¹ * ∑ j, ‖x j - y j‖) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hn.le)]
  calc (N : ℝ)⁻¹ * ‖∑ j, (K (x i) (x j) - K (y i) (y j))‖ ≤
        (N : ℝ)⁻¹ * ∑ j, ‖K (x i) (x j) - K (y i) (y j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hn.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ j, (L : ℝ) * (‖x i - y i‖ + ‖x j - y j‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hn.le)
      apply Finset.sum_le_sum
      intro j _
      refine (hK.norm_sub_le (x i, x j) (y i, y j)).trans ?_
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      change max ‖x i - y i‖ ‖x j - y j‖ ≤ _
      exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Deterministic squared-error estimate for synchronously coupled interacting particles. -/
theorem norm_sub_sq_le_residual_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} (hN : 0 < N) (b₀ : E → E) {L₀ : ℝ≥0}
    (hb₀ : LipschitzWith L₀ b₀) (K : E → E → E) {L_K : ℝ≥0}
    (hK : LipschitzWith L_K (Function.uncurry K))
    (x y r : Fin N → ℝ → E) (hx : ∀ i, Continuous (x i))
    (hy : ∀ i, Continuous (y i)) (hr : ∀ i, Continuous (r i))
    {T : ℝ} (hT : 0 ≤ T)
    (heq : ∀ i t, t ∈ Icc (0 : ℝ) T → x i t - y i t = ∫ s in (0 : ℝ)..t,
      b₀ (x i s) - b₀ (y i s) +
        (N : ℝ)⁻¹ • ∑ j, (K (x i s) (x j s) - K (y i s) (y j s)) + r i s) :
    ∀ i t, t ∈ Icc (0 : ℝ) T → ‖x i t - y i t‖ ^ 2 ≤
      (2 * T * Real.exp (((L₀ : ℝ) + L_K) * T) ^ 2 *
        (1 + ((L_K : ℝ) * T * Real.exp (((L₀ : ℝ) + L_K + L_K) * T)) ^ 2)) *
      ((∫ s in (0 : ℝ)..T, ‖r i s‖ ^ 2) + (N : ℝ)⁻¹ * ∑ j, ∫ s in (0 : ℝ)..T, ‖r j s‖ ^ 2) := by
  let u : Fin N → ℝ → ℝ := fun i s ↦ ‖x i s - y i s‖
  let R : Fin N → ℝ → ℝ := fun i s ↦ ‖r i s‖
  let a := (L₀ : ℝ) + L_K
  let b := (L_K : ℝ)
  have hu (i : Fin N) : Continuous (u i) := ((hx i).sub (hy i)).norm
  have hR (i : Fin N) : Continuous (R i) := (hr i).norm
  apply finite_coupling_gronwall_sq hN u R hu (fun i s ↦ norm_nonneg _) hR
    (fun i s ↦ norm_nonneg _) (add_nonneg L₀.coe_nonneg L_K.coe_nonneg) L_K.coe_nonneg hT
  intro i t ht
  let F : ℝ → E := fun s ↦ b₀ (x i s) - b₀ (y i s) +
    (N : ℝ)⁻¹ • ∑ j, (K (x i s) (x j s) - K (y i s) (y j s)) + r i s
  have hF : Continuous F := by
    dsimp [F]
    exact (((hb₀.continuous.comp (hx i)).sub (hb₀.continuous.comp (hy i))).add
      ((continuous_finsetSum _ fun j _ ↦
        (hK.continuous.comp ((hx i).prodMk (hx j))).sub
          (hK.continuous.comp ((hy i).prodMk (hy j)))).const_smul _)).add (hr i)
  have hbd (s : ℝ) : ‖F s‖ ≤ a * u i s + b * ((N : ℝ)⁻¹ * ∑ j, u j s) + R i s := by
    have hk := norm_mean_interaction_sub_le hN K hK (fun j ↦ x j s) (fun j ↦ y j s) i
    have hb := hb₀.norm_sub_le (x i s) (y i s)
    have ht1 := norm_add_le (b₀ (x i s) - b₀ (y i s))
      ((N : ℝ)⁻¹ • ∑ j, (K (x i s) (x j s) - K (y i s) (y j s)))
    have ht2 := norm_add_le (b₀ (x i s) - b₀ (y i s) +
      (N : ℝ)⁻¹ • ∑ j, (K (x i s) (x j s) - K (y i s) (y j s))) (r i s)
    dsimp only [F, a, b, u, R]
    nlinarith
  calc u i t = ‖∫ s in (0 : ℝ)..t, F s‖ := by dsimp [u]; rw [heq i t ht]
    _ ≤ ∫ s in (0 : ℝ)..t, ‖F s‖ := intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0 : ℝ)..t, a * u i s + b * ((N : ℝ)⁻¹ * ∑ j, u j s) + R i s :=
      intervalIntegral.integral_mono ht.1 (hF.norm.intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop) hbd
    _ = a * (∫ s in (0 : ℝ)..t, u i s) +
        b * (∫ s in (0 : ℝ)..t, (N : ℝ)⁻¹ * ∑ j, u j s) + ∫ s in (0 : ℝ)..t, R i s := by
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        ((hR i).intervalIntegrable _ _),
        intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      have hrem := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ht.1 ht.2
        (μ := volume) (f := R i) (ae_of_all _ fun s ↦ norm_nonneg _) ((hR i).intervalIntegrable _ _)
      linarith

end CKSD
