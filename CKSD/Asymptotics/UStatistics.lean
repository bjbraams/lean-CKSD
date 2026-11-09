module

public import CKSD.Asymptotics.Basic
public import CKSD.Asymptotics.MultivariateCLT
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Covariance

/-!
# U-statistic projections, variance and limit laws

The nondegenerate central limit theorem uses the first Hoeffding projection; order-two
kernels have an exact decomposition and variance, and finite-rank degenerate kernels have
Gaussian-chaos limits. Sources: GAPS 102.8, 102.29 and 102.30, and `SYNOPSIS102.md`.
The normalization is the ordered-injection convention of `CKSD.uStatistic`.
The order-two proof uses Mathlib's finite-product `HasLaw` and integration adapters,
`variance_sum_pi`, and the variance and covariance identities. Distinct degenerate kernel
terms are orthogonal by integrating out a coordinate occurring in only one term.
The finite-rank limit uses the Euclidean CLT from `CKSD.Asymptotics.MultivariateCLT`,
Mathlib's `strong_law_ae`, and `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`
for the sample second moments and deterministic normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 102.8: the central limit theorem for U-statistics. For a symmetric square-integrable
kernel `h` of order `m + 1` with mean `θ` and first projection `g(x) = E h(x, X₂, …) - θ`,
`√n (Uₙ - θ)` converges in law to `N(0, (m + 1)² Var g)`. In the degenerate case `Var g = 0`
the limit is the point mass at `0`. -/
theorem tendstoInDistribution_uStatistic_of_nondegenerate
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (m : ℕ)
    (h : (Fin (m + 1) → E) → ℝ) (hmeas : Measurable h)
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) x, h (x ∘ σ) = h x)
    (h2 : MemLp h 2 (Measure.pi fun _ : Fin (m + 1) ↦ P)) :
    let θ := ∫ x, h x ∂(Measure.pi fun _ : Fin (m + 1) ↦ P);
    let g := fun x ↦ (∫ y, h (Fin.cases x y) ∂(Measure.pi fun _ : Fin m ↦ P)) - θ;
    TendstoInDistribution (fun (n : ℕ) ω ↦ Real.sqrt n *
      (uStatistic (m + 1) n h (fun i ↦ X i.val ω) - θ)) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (Real.toNNReal (((m + 1 : ℕ) : ℝ) ^ 2 * Var[g; P]))) := by
  sorry


/-- The order-two ordered-injection sum is the sum over distinct ordered pairs. -/
theorem uStatistic_two_eq_sum {E : Type*} {n : ℕ} (h : E × E → ℝ) (x : Fin n → E) :
    uStatistic 2 n (fun z ↦ h (z 0, z 1)) x =
      (n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹ * ∑ i, ∑ j, if i = j then 0 else h (x i, x j) := by
  classical
  have hinj (f : Fin 2 → Fin n) : Function.Injective f ↔ f 0 ≠ f 1 := by
    constructor
    · exact fun hf ↦ fun he ↦ by have := hf he; norm_num at this
    · intro hf i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hsum : (∑ f : Fin 2 → Fin n, if Function.Injective f then h (x (f 0), x (f 1)) else 0) =
      ∑ p : Fin n × Fin n, if p.1 = p.2 then 0 else h (x p.1, x p.2) := by
    simpa only [hinj, ite_not] using
      (Fintype.sum_equiv (finTwoArrowEquiv (Fin n))
        (fun f ↦ if f 0 ≠ f 1 then h (x (f 0), x (f 1)) else 0)
        (fun p ↦ if p.1 ≠ p.2 then h (x p.1, x p.2) else 0) (fun f ↦ rfl))
  simp only [uStatistic, Finset.sum_filter, Function.comp_apply]
  rw [hsum, Fintype.sum_prod_type]
  rw [show n.descFactorial 2 = n * (n - 1) by simp [Nat.descFactorial_succ, mul_comm]]
  push_cast
  rw [mul_inv_rev]
  ring

/-- The sum of a one-coordinate term over all distinct ordered pairs. -/
theorem sum_pair_ne_left {n : ℕ} (g : Fin n → ℝ) :
    (∑ i, ∑ j, if i = j then 0 else g i) = (n - 1 : ℕ) * ∑ i, g i := by
  classical
  by_cases hn : n = 0
  · subst n; simp
  have hn' : (n : ℝ) - 1 = (n - 1 : ℕ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; rfl
  calc (∑ i, ∑ j, if i = j then 0 else g i) = ∑ i, ((n : ℝ) - 1) * g i := by
        apply Finset.sum_congr rfl
        intro i _
        have he : ∀ j : Fin n, (if i = j then 0 else g i) = g i - (if i = j then g i else 0) := by
          intro j; split_ifs <;> ring
        simp_rw [he]
        simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, sub_mul]
    _ = _ := by rw [hn', Finset.mul_sum]

/-- The order-two Hoeffding decomposition is a deterministic identity. -/
theorem uStatistic_two_sub_eq {E : Type*} {n : ℕ} (hn : 2 ≤ n)
    (h : E × E → ℝ) (g : E → ℝ) (θ : ℝ) (x : Fin n → E) :
    uStatistic 2 n (fun z ↦ h (z 0, z 1)) x - θ =
      2 / n * ∑ i, g (x i) +
        uStatistic 2 n (fun z ↦ h (z 0, z 1) - θ - g (z 0) - g (z 1)) x := by
  classical
  rw [uStatistic_two_eq_sum]
  have hq := uStatistic_two_eq_sum (fun z : E × E ↦ h z - θ - g z.1 - g z.2) x
  change _ = _ + uStatistic 2 n (fun z ↦ (fun p : E × E ↦ h p - θ - g p.1 - g p.2) (z 0, z 1)) x
  rw [hq]
  have hsplit : (∑ i, ∑ j, if i = j then 0 else h (x i, x j) - θ - g (x i) - g (x j)) =
      (∑ i, ∑ j, if i = j then 0 else h (x i, x j)) -
      (n : ℝ) * (n - 1 : ℕ) * θ - 2 * (n - 1 : ℕ) * ∑ i, g (x i) := by
    have hite : ∀ i j : Fin n, (if i = j then 0 else h (x i, x j) - θ - g (x i) - g (x j)) =
        (if i = j then 0 else h (x i, x j)) - (if i = j then 0 else θ) -
          (if i = j then 0 else g (x i)) - (if i = j then 0 else g (x j)) := by
      intro i j; split_ifs <;> ring
    simp_rw [hite, Finset.sum_sub_distrib]
    rw [sum_pair_ne_left, sum_pair_ne_left]
    have hr : (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else g (x j)) =
        (n - 1 : ℕ) * ∑ i, g (x i) := by
      rw [Finset.sum_comm]
      simpa only [eq_comm] using sum_pair_ne_left (fun i ↦ g (x i))
    rw [hr]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsplit]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  field_simp
  ring


/-- Distinct coordinates under a finite product law have the product of their laws. -/
theorem hasLaw_pi_pair {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HasLaw (fun x : Fin n → E ↦ (x i, x j)) (P.prod P) (Measure.pi fun _ : Fin n ↦ P) := by
  have h := iIndepFun_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ id)
    (fun _ ↦ aemeasurable_id)
  exact (h.indepFun hij).hasLaw_prod
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    ⟨(measurable_pi_apply j).aemeasurable, (measurePreserving_eval _ j).map_eq⟩

/-- The conditional integral of a square-integrable real kernel is square integrable. -/
theorem memLp_integral_kernel {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (h : E × E → ℝ) (hm : Measurable h) (h2 : MemLp h 2 (P.prod P)) :
    MemLp (fun x ↦ ∫ y, h (x,y) ∂P) 2 P := by
  apply (memLp_two_iff_integrable_sq
    hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable).2
  have hb := h2.integrable_sq.integral_prod_left
  apply hb.mono' (hm.stronglyMeasurable.integral_prod_right'.pow 2).aestronglyMeasurable
  filter_upwards [h2.integrable_sq.prod_right_ae] with x hx
  have hx2 : MemLp (fun y ↦ h (x,y)) 2 P :=
    (memLp_two_iff_integrable_sq (hm.comp measurable_prodMk_left).aestronglyMeasurable).2 hx
  have hv := ProbabilityTheory.variance_nonneg (fun y ↦ h (x,y)) P
  rw [ProbabilityTheory.variance_eq_sub hx2] at hv
  simp only [Pi.pow_apply] at hv ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

/-- A centered conditional kernel has zero first-coordinate integral. -/
theorem integral_hoeffding_kernel_eq_zero {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (h : E × E → ℝ) (h2 : MemLp h 2 (P.prod P))
    (hs : ∀ x y, h (x,y) = h (y,x)) :
    let θ := ∫ z, h z ∂P.prod P
    let g := fun x ↦ (∫ y, h (x,y) ∂P) - θ
    let q := fun z : E × E ↦ h z - θ - g z.1 - g z.2
    (∫ x, g x ∂P) = 0 ∧ ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0 := by
  let θ := ∫ z, h z ∂P.prod P
  let g := fun x ↦ (∫ y, h (x,y) ∂P) - θ
  change (∫ x, g x ∂P) = 0 ∧ ∀ᵐ y ∂P, (∫ x, h (x,y) - θ - g x - g y ∂P) = 0
  have hi := h2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgi : Integrable g P := hi.integral_prod_left.sub (integrable_const θ)
  have hg0 : (∫ x, g x ∂P) = 0 := by
    dsimp only [g]
    rw [integral_sub hi.integral_prod_left (integrable_const θ), ← integral_prod _ hi]
    simp [θ]
  refine ⟨hg0, ?_⟩
  filter_upwards [hi.prod_left_ae] with y hy
  calc (∫ x, h (x,y) - θ - g x - g y ∂P) =
        (∫ x, h (x,y) - θ - g x ∂P) - ∫ x, g y ∂P :=
      integral_sub ((hy.sub (integrable_const θ)).sub hgi) (integrable_const (g y))
    _ = ((∫ x, h (x,y) ∂P) - θ) - (∫ x, g x ∂P) - g y := by
      have e1 := integral_sub (hy.sub (integrable_const θ)) hgi
      have e2 := integral_sub hy (integrable_const θ)
      simp only [Pi.sub_apply] at e1 e2
      rw [e1, e2]
      simp
    _ = 0 := by rw [hg0]; simp_rw [hs _ y]; dsimp [g]; ring


/-- A centered pair kernel is orthogonal to any square-integrable function not using its first
coordinate. -/
theorem integral_pair_mul_eq_zero {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] {n : ℕ} (i j : Fin (n+1)) (hij : i ≠ j)
    (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0)
    (F : (Fin (n+1) → E) → ℝ) (hF : MemLp F 2 (Measure.pi fun _ ↦ P))
    (hnot : ∀ (a b : E) (z : Fin n → E), F (i.insertNth a z) = F (i.insertNth b z)) :
    (∫ x, q (x i, x j) * F x ∂(Measure.pi fun _ : Fin (n+1) ↦ P)) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ E) i
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ P) i
  have hei := he.symm e
  have hiq := (hasLaw_pi_pair P i j hij).memLp_fun_comp hq
  have hint := hiq.integrable_mul hF
  have hint' := hei.integrable_comp_of_integrable hint
  have hsymm : (∫ x, q (x i, x j) * F x ∂(Measure.pi fun _ : Fin (n+1) ↦ P)) =
      ∫ z, ∫ t, q ((e.symm (t,z)) i, (e.symm (t,z)) j) * F (e.symm (t,z)) ∂P
        ∂(Measure.pi fun _ : Fin n ↦ P) := by
    rw [← hei.integral_comp' (fun x ↦ q (x i, x j) * F x)]
    exact integral_prod_symm _ hint'
  rw [hsymm]
  obtain ⟨j', hj'⟩ : ∃ j' : Fin n, i.succAbove j' = j := by
    rcases i.eq_self_or_eq_succAbove j with h | ⟨j', hj'⟩
    · exact (hij h.symm).elim
    · exact ⟨j', hj'.symm⟩
  have heval := (measurePreserving_eval (fun _ : Fin n ↦ P) j').quasiMeasurePreserving
  have hae := heval.ae hzero
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with z hz
  have hnE := nonempty_of_isProbabilityMeasure P
  obtain ⟨a⟩ := hnE
  have hFn : ∀ t : E, F (e.symm (t,z)) = F (i.insertNth a z) := fun t ↦ hnot t a z
  change (∫ t, q ((e.symm (t,z)) i, (e.symm (t,z)) j) * F (e.symm (t,z)) ∂P) = 0
  simp_rw [hFn]
  change (∫ t, q ((i.insertNth (α := fun _ ↦ E) t z) i, (i.insertNth (α := fun _ ↦ E) t z) j) * F (i.insertNth a z) ∂P) = 0
  simp only [← hj', Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [integral_mul_const, hz, zero_mul]


/-- Inserting a different value at one coordinate leaves every other coordinate unchanged. -/
theorem insertNth_eq_of_ne {E : Type*} {n : ℕ} (i k : Fin (n+1)) (hik : i ≠ k)
    (a b : E) (z : Fin n → E) :
    (i.insertNth (α := fun _ ↦ E) a z) k = (i.insertNth (α := fun _ ↦ E) b z) k := by
  rcases i.eq_self_or_eq_succAbove k with h | ⟨k', rfl⟩
  · exact (hik h.symm).elim
  · simp

/-- Two centered symmetric pair kernels are orthogonal unless their unordered coordinate pairs
coincide. -/
theorem integral_pair_mul_pair {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] {n : ℕ} (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P)) (hs : ∀ x y, q (x,y) = q (y,x))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0) :
    (∫ x, q (x i, x j) * q (x k, x l) ∂(Measure.pi fun _ : Fin n ↦ P)) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then ∫ z, q z ^ 2 ∂P.prod P else 0 := by
  classical
  by_cases heq : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  · rw [ite_eq_left heq]
    have he : ∀ x : Fin n → E, q (x i, x j) * q (x k, x l) = q (x i, x j) ^ 2 := by
      intro x
      rcases heq with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
      · rw [← hik, ← hjl]; ring
      · rw [← hil, ← hjk, hs (x j) (x i)]; ring
    simp_rw [he]
    simpa only [Function.comp_apply, Pi.pow_apply] using
      (hasLaw_pi_pair P i j hij).integral_comp (hq.aestronglyMeasurable.pow 2)
  rw [ite_eq_right heq]
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have horth (a b : Fin (n+1)) (hab : a ≠ b) (hak : a ≠ k) (hal : a ≠ l) :
        (∫ x, q (x a, x b) * q (x k, x l) ∂(Measure.pi fun _ : Fin (n+1) ↦ P)) = 0 := by
      apply integral_pair_mul_eq_zero P a b hab q hq hzero
        (fun x ↦ q (x k, x l)) ((hasLaw_pi_pair P k l hkl).memLp_fun_comp hq)
      intro t u z
      congr 1
      exact Prod.ext (insertNth_eq_of_ne a k hak t u z) (insertNth_eq_of_ne a l hal t u z)
    by_cases hi : i ≠ k ∧ i ≠ l
    · exact horth i j hij hi.1 hi.2
    have hj : j ≠ k ∧ j ≠ l := by aesop
    convert horth j i hij.symm hj.1 hj.2 using 1
    exact integral_congr_ae (ae_of_all _ fun x ↦ by dsimp only; rw [hs (x i) (x j)])

/-- A centered symmetric pair kernel is orthogonal to each one-coordinate function. -/
theorem integral_pair_mul_single {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] {n : ℕ} (i j k : Fin n) (hij : i ≠ j)
    (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P)) (hs : ∀ x y, q (x,y) = q (y,x))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0) (g : E → ℝ) (hg : MemLp g 2 P) :
    (∫ x, q (x i, x j) * g (x k) ∂(Measure.pi fun _ : Fin n ↦ P)) = 0 := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hgk := hg.comp_measurePreserving (measurePreserving_eval (fun _ : Fin (n+1) ↦ P) k)
    by_cases hik : i ≠ k
    · apply integral_pair_mul_eq_zero P i j hij q hq hzero (fun x ↦ g (x k)) hgk
      intro t u z
      rw [insertNth_eq_of_ne i k hik t u z]
    · have hik' : i = k := not_not.1 hik
      have hjk : j ≠ k := by subst k; exact hij.symm
      have hh := integral_pair_mul_eq_zero P j i hij.symm q hq hzero (fun x ↦ g (x k)) hgk
        (fun t u z ↦ congrArg g (insertNth_eq_of_ne j k hjk t u z))
      calc (∫ x, q (x i, x j) * g (x k) ∂(Measure.pi fun _ : Fin (n+1) ↦ P)) =
          ∫ x, q (x j, x i) * g (x k) ∂(Measure.pi fun _ : Fin (n+1) ↦ P) :=
            integral_congr_ae (ae_of_all _ fun x ↦ by dsimp only; rw [hs (x i) (x j)])
        _ = 0 := hh


/-- The sum of a square-integrable kernel over distinct coordinate pairs is square integrable. -/
theorem memLp_sum_pairs {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P)) (n : ℕ) :
    MemLp (fun x : Fin n → E ↦ ∑ i, ∑ j, if i = j then 0 else q (x i, x j)) 2
      (Measure.pi fun _ : Fin n ↦ P) := by
  classical
  apply memLp_finsetSum _
  intro i _
  apply memLp_finsetSum _
  intro j _
  by_cases hij : i = j
  · simp only [hij, ite_true]; exact memLp_const (0 : ℝ)
  · simp only [hij, ite_false]
    exact (hasLaw_pi_pair P i j hij).memLp_fun_comp hq

/-- Degenerate pair sums have mean zero. -/
theorem integral_sum_pairs_eq_zero {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0) (n : ℕ) :
    (∫ x : Fin n → E, ∑ i, ∑ j, if i = j then 0 else q (x i, x j)
      ∂(Measure.pi fun _ : Fin n ↦ P)) = 0 := by
  classical
  have hz : (∫ z, q z ∂P.prod P) = 0 := by
    rw [integral_prod_symm _ (hq.integrable (by norm_num))]
    exact integral_eq_zero_of_ae hzero
  have hint (i j : Fin n) : Integrable (fun x : Fin n → E ↦ if i = j then 0 else q (x i, x j))
      (Measure.pi fun _ : Fin n ↦ P) := by
    by_cases hij : i = j
    · simp only [hij, ite_true]; exact integrable_const (0 : ℝ)
    · simp only [hij, ite_false]
      exact (hasLaw_pi_pair P i j hij).integrable_fun_comp (hq.integrable (by norm_num))
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ite_false]
    simpa only [Function.comp_apply, hz] using
      (hasLaw_pi_pair P i j hij).integral_comp hq.aestronglyMeasurable

/-- The second moment of a degenerate symmetric ordered-pair sum. -/
theorem integral_sq_sum_pairs {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P))
    (hs : ∀ x y, q (x,y) = q (y,x))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0) (n : ℕ) :
    (∫ x : Fin n → E, (∑ i, ∑ j, if i = j then 0 else q (x i, x j)) ^ 2
      ∂(Measure.pi fun _ : Fin n ↦ P)) =
      2 * n * (n - 1 : ℕ) * ∫ z, q z ^ 2 ∂P.prod P := by
  classical
  let A := fun (i j : Fin n) (x : Fin n → E) ↦ if i = j then 0 else q (x i, x j)
  let V := ∫ z, q z ^ 2 ∂P.prod P
  have hA (i j : Fin n) : MemLp (A i j) 2 (Measure.pi fun _ : Fin n ↦ P) := by
    dsimp only [A]
    by_cases hij : i = j
    · simp only [hij, ite_true]; exact memLp_const (0 : ℝ)
    · simp only [hij, ite_false]; exact (hasLaw_pi_pair P i j hij).memLp_fun_comp hq
  have hterm (i j k l : Fin n) :
      (∫ x, A i j x * A k l x ∂(Measure.pi fun _ : Fin n ↦ P)) =
        if i = j then 0 else if k = i ∧ l = j then V else if k = j ∧ l = i then V else 0 := by
    by_cases hij : i = j
    · simp [A, hij]
    by_cases hkl : k = l
    · simp [A, hkl]; aesop
    dsimp only [A]
    simp only [hij, hkl, ite_false]
    rw [integral_pair_mul_pair P i j k l hij hkl q hq hs hzero]
    split_ifs <;> simp_all only [V] <;> aesop
  have hsum (i j : Fin n) :
      (∑ k, ∑ l, ∫ x, A i j x * A k l x ∂(Measure.pi fun _ : Fin n ↦ P)) =
        if i = j then 0 else 2 * V := by
    simp_rw [hterm]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false]
      have he (k l : Fin n) :
          (if k = i ∧ l = j then V else if k = j ∧ l = i then V else 0) =
          (if k = i then if l = j then V else 0 else 0) +
            (if k = j then if l = i then V else 0 else 0) := by
        split_ifs <;> simp_all
      simp_rw [he, Finset.sum_add_distrib]
      simp [two_mul]
  have hint (i j k l : Fin n) : Integrable (fun x ↦ A i j x * A k l x)
      (Measure.pi fun _ : Fin n ↦ P) := (hA i j).integrable_mul (hA k l)
  have hpoint (x : Fin n → E) : (∑ i, ∑ j, A i j x) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j x * A k l x := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  change (∫ x, (∑ i, ∑ j, A i j x) ^ 2 ∂(Measure.pi fun _ : Fin n ↦ P)) = _
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ (fun k _ ↦ integrable_finsetSum _ (fun l _ ↦
      hint i j k l))))]
  conv_lhs => enter [2,i]; rw [integral_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ (fun k _ ↦ integrable_finsetSum _ (fun l _ ↦
      hint i j k l)))]
  conv_lhs => enter [2,i,2,j]; rw [integral_finsetSum _ (fun k _ ↦
    integrable_finsetSum _ (fun l _ ↦ hint i j k l))]
  conv_lhs => enter [2,i,2,j,2,k]; rw [integral_finsetSum _ (fun l _ ↦
    hint i j k l)]
  simp_rw [hsum]
  rw [sum_pair_ne_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- A degenerate pair sum is orthogonal to the sum of any square-integrable one-coordinate
function. -/
theorem integral_sum_pairs_mul_sum_eq_zero {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (q : E × E → ℝ) (hq : MemLp q 2 (P.prod P))
    (hs : ∀ x y, q (x,y) = q (y,x))
    (hzero : ∀ᵐ y ∂P, (∫ x, q (x,y) ∂P) = 0) (g : E → ℝ) (hg : MemLp g 2 P) (n : ℕ) :
    (∫ x : Fin n → E, (∑ i, ∑ j, if i = j then 0 else q (x i, x j)) * (∑ k, g (x k))
      ∂(Measure.pi fun _ : Fin n ↦ P)) = 0 := by
  classical
  let A := fun (i j : Fin n) (x : Fin n → E) ↦ if i = j then 0 else q (x i, x j)
  have hA (i j : Fin n) : MemLp (A i j) 2 (Measure.pi fun _ : Fin n ↦ P) := by
    dsimp only [A]
    by_cases hij : i = j
    · simp only [hij, ite_true]; exact memLp_const (0 : ℝ)
    · simp only [hij, ite_false]; exact (hasLaw_pi_pair P i j hij).memLp_fun_comp hq
  have hG : MemLp (fun x : Fin n → E ↦ ∑ k, g (x k)) 2 (Measure.pi fun _ : Fin n ↦ P) :=
    memLp_finsetSum _ fun k _ ↦ hg.comp_measurePreserving (measurePreserving_eval _ k)
  have he (i j : Fin n) :
      (∫ x : Fin n → E, A i j x * (∑ k, g (x k)) ∂(Measure.pi fun _ : Fin n ↦ P)) = 0 := by
    by_cases hij : i = j
    · simp [A, hij]
    simp only [A, hij, ite_false]
    simp_rw [Finset.mul_sum]
    have hint (k : Fin n) : Integrable (fun x : Fin n → E ↦ q (x i, x j) * g (x k))
        (Measure.pi fun _ : Fin n ↦ P) :=
      ((hasLaw_pi_pair P i j hij).memLp_fun_comp hq).integrable_mul
        (hg.comp_measurePreserving (measurePreserving_eval _ k))
    rw [integral_finsetSum _ (fun k _ ↦ hint k)]
    simp_rw [integral_pair_mul_single P i j _ hij q hq hs hzero g hg]
    simp
  change (∫ x : Fin n → E, (∑ i, ∑ j, A i j x) * (∑ k, g (x k))
    ∂(Measure.pi fun _ : Fin n ↦ P)) = 0
  simp_rw [Finset.sum_mul]
  have hint (i j : Fin n) : Integrable (fun x : Fin n → E ↦ A i j x * (∑ k, g (x k)))
      (Measure.pi fun _ : Fin n ↦ P) := (hA i j).integrable_mul hG
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
  conv_lhs => enter [2,i]; rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  simp_rw [he]
  simp

/-- GAPS 102.29: order-two Hoeffding decomposition, including the exact variance. -/
theorem uStatistic_hoeffding_decomposition_and_variance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (h : E × E → ℝ)
    (hm : Measurable h) (h2 : MemLp h 2 (P.prod P)) (hs : ∀ x y, h (x,y) = h (y,x))
    (n : ℕ) (hn : 2 ≤ n) :
    let θ := ∫ z, h z ∂P.prod P;
    let g := fun x ↦ (∫ y, h (x,y) ∂P) - θ;
    let q := fun z : E × E ↦ h z - θ - g z.1 - g z.2;
    let U := fun x : Fin n → E ↦ uStatistic 2 n (fun z ↦ h (z 0, z 1)) x;
    (∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P),
      U x - θ = 2 / n * (∑ i, g (x i)) +
        uStatistic 2 n (fun z ↦ q (z 0, z 1)) x) ∧
    Var[U; Measure.pi fun _ : Fin n ↦ P] =
      4 / n * Var[g; P] + 2 / ((n : ℝ) * (n - 1 : ℕ)) * ∫ z, q z ^ 2 ∂P.prod P := by
  classical
  let θ := ∫ z, h z ∂P.prod P
  let g := fun x ↦ (∫ y, h (x,y) ∂P) - θ
  let q := fun z : E × E ↦ h z - θ - g z.1 - g z.2
  let U := fun x : Fin n → E ↦ uStatistic 2 n (fun z ↦ h (z 0, z 1)) x
  change (∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ P), U x - θ = 2 / n * (∑ i, g (x i)) +
      uStatistic 2 n (fun z ↦ q (z 0, z 1)) x) ∧ _
  refine ⟨ae_of_all _ (uStatistic_two_sub_eq hn h g θ), ?_⟩
  let μ := Measure.pi fun _ : Fin n ↦ P
  let G := fun x : Fin n → E ↦ ∑ i, g (x i)
  let S := fun x : Fin n → E ↦ ∑ i, ∑ j, if i = j then 0 else q (x i, x j)
  let c : ℝ := (n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹
  have hg : MemLp g 2 P := (memLp_integral_kernel P h hm h2).sub (memLp_const θ)
  have hq : MemLp q 2 (P.prod P) :=
    ((h2.sub (memLp_const θ)).sub (hg.comp_measurePreserving measurePreserving_fst)).sub
      (hg.comp_measurePreserving measurePreserving_snd)
  have hqs : ∀ x y, q (x,y) = q (y,x) := by
    intro x y
    dsimp only [q]
    rw [hs x y]
    ring
  obtain ⟨-, hq0⟩ := integral_hoeffding_kernel_eq_zero P h h2 hs
  have hS : MemLp S 2 μ := memLp_sum_pairs P q hq n
  have hG : MemLp G 2 μ :=
    memLp_finsetSum _ fun i _ ↦ hg.comp_measurePreserving (measurePreserving_eval _ i)
  have hS0 : (∫ x, S x ∂μ) = 0 := integral_sum_pairs_eq_zero P q hq hq0 n
  have hS2 : (∫ x, S x ^ 2 ∂μ) = 2 * n * (n - 1 : ℕ) * ∫ z, q z ^ 2 ∂P.prod P :=
    integral_sq_sum_pairs P q hq hqs hq0 n
  have hcov : ProbabilityTheory.covariance S G μ = 0 := by
    rw [covariance_eq_sub hS hG]
    change (∫ x, S x * G x ∂μ) - (∫ x, S x ∂μ) * (∫ x, G x ∂μ) = 0
    rw [hS0, zero_mul, sub_zero]
    exact integral_sum_pairs_mul_sum_eq_zero P q hq hqs hq0 g hg n
  have hGvar : ProbabilityTheory.variance G μ = n * Var[g; P] := by
    calc ProbabilityTheory.variance G μ = ∑ i : Fin n, ProbabilityTheory.variance g P := by
          rw [show G = ∑ i : Fin n, (fun x : Fin n → E ↦ g (x i)) by funext x; simp [G]]
          exact ProbabilityTheory.variance_sum_pi (μ := fun _ : Fin n ↦ P) (X := fun _ ↦ g) (fun _ ↦ hg)
      _ = n * Var[g; P] := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hU : U = fun x ↦ ((2 / n) * G x + c * S x) + θ := by
    funext x
    have hd := uStatistic_two_sub_eq hn h g θ x
    have hqsum := uStatistic_two_eq_sum q x
    change U x - θ = 2 / n * G x + uStatistic 2 n (fun z ↦ q (z 0, z 1)) x at hd
    rw [hqsum] at hd
    change U x - θ = 2 / n * G x + c * S x at hd
    linarith
  have hU2 : MemLp U 2 μ := by rw [hU]; exact ((hG.const_mul _).add (hS.const_mul _)).add (memLp_const θ)
  change Var[U; μ] = _
  have hshift := ProbabilityTheory.variance_add_const
    (X := fun x ↦ (2 / n) * G x + c * S x)
    ((hG.const_mul (2 / n)).add (hS.const_mul c)).aestronglyMeasurable θ
  have hadd := ProbabilityTheory.variance_fun_add (hG.const_mul (2 / n)) (hS.const_mul c)
  rw [hU, hshift, hadd,
    ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_const_mul,
    covariance_const_mul_left, covariance_const_mul_right, covariance_comm, hcov,
    hGvar, ProbabilityTheory.variance_of_integral_eq_zero hS.aemeasurable hS0, hS2]
  dsimp only [c]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  field_simp
  ring

/-- The finite-rank quadratic U-statistic is a difference between squared sample sums and
sample sums of squares. The identity includes sample sizes zero and one. -/
theorem uStatistic_two_finite_rank_eq {E : Type*} (r n : ℕ) (a : Fin r → ℝ)
    (e : Fin r → E → ℝ) (x : Fin n → E) :
    (n : ℝ) * uStatistic 2 n (fun z ↦ ∑ j, a j * e j (z 0) * e j (z 1)) x =
      ((n : ℝ) / (n - 1 : ℕ)) *
        ((∑ j, a j * ((Real.sqrt n)⁻¹ * ∑ i, e j (x i)) ^ 2) -
          (n : ℝ)⁻¹ * ∑ i, ∑ j, a j * e j (x i) ^ 2) := by
  classical
  by_cases hn : n = 0
  · subst n; simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsum (j : Fin r) : (∑ i : Fin n, ∑ k : Fin n, if i = k then 0 else e j (x i) * e j (x k)) =
      (∑ i : Fin n, e j (x i)) ^ 2 - ∑ i : Fin n, e j (x i) ^ 2 := by
    have hp (i k : Fin n) : (if i = k then 0 else e j (x i) * e j (x k)) =
        e j (x i) * e j (x k) - (if i = k then e j (x i) ^ 2 else 0) := by
      split_ifs with h
      · subst k; ring
      · ring
    simp_rw [hp, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul_sum]
    ring
  have hswap : (∑ i : Fin n, ∑ k : Fin n, if i = k then 0 else ∑ j, a j * e j (x i) * e j (x k)) =
      ∑ j, a j * ((∑ i, e j (x i)) ^ 2 - ∑ i, e j (x i) ^ 2) := by
    have hp (i k : Fin n) : (if i = k then 0 else ∑ j, a j * e j (x i) * e j (x k)) =
        ∑ j, a j * (if i = k then 0 else e j (x i) * e j (x k)) := by
      split_ifs <;> simp [mul_assoc]
    simp_rw [hp]
    conv_lhs => enter [2,i]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← Finset.mul_sum]
    rw [hsum]
  rw [uStatistic_two_eq_sum (fun z : E × E ↦ ∑ j, a j * e j z.1 * e j z.2)]
  rw [hswap]
  have hsqrt : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp_rw [mul_pow, hsqrt]
  have hA : (∑ j, a j * ((n : ℝ)⁻¹ * (∑ i, e j (x i)) ^ 2)) =
      (n : ℝ)⁻¹ * ∑ j, a j * (∑ i, e j (x i)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hB : (∑ i, ∑ j, a j * e j (x i) ^ 2) = ∑ j, a j * ∑ i, e j (x i) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [hA, hB]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  field_simp


/-- A finite-rank quadratic kernel has the Gaussian-chaos limit whenever its vector of
normalized scores has the standard Gaussian limit. -/
theorem tendstoInDistribution_uStatistic_finite_rank_of_scores
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (r : ℕ) (a : Fin r → ℝ) (e : Fin r → E → ℝ) (he : ∀ j, MemLp (e j) 2 P)
    (hesq : ∀ j, (∫ x, e j x ^ 2 ∂P) = 1)
    (hscore : TendstoInDistribution
      (fun (n : ℕ) ω ↦ WithLp.toLp 2 (fun j ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, e j (X i ω)))
      atTop id (fun _ ↦ μ) (stdGaussian (EuclideanSpace ℝ (Fin r)))) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) * uStatistic 2 n
      (fun z ↦ ∑ j, a j * e j (z 0) * e j (z 1)) (fun i ↦ X i.val ω)) atTop id (fun _ ↦ μ)
      ((Measure.pi fun _ : Fin r ↦ gaussianReal 0 1).map
        (fun z ↦ ∑ j, a j * (z j ^ 2 - 1))) := by
  classical
  let s := fun x : E ↦ ∑ j, a j * e j x ^ 2
  let b := ∑ j, a j
  let R := fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, s (X i ω)
  let c := fun n : ℕ ↦ (n : ℝ) / (n - 1 : ℕ)
  let φ := fun z : EuclideanSpace ℝ (Fin r) ↦ ∑ j, a j * z j ^ 2
  have hs : Integrable s P := integrable_finsetSum _ fun j _ ↦ (he j).integrable_sq.const_mul _
  have hsmean : (∫ x, s x ∂P) = b := by
    rw [integral_finsetSum _ (fun j _ ↦ (he j).integrable_sq.const_mul _)]
    simp only [integral_const_mul, hesq, mul_one, b]
  have hXlaw (i : ℕ) : HasLaw (X i) P μ := ⟨(hiid.1 i).aemeasurable, hiid.2.2 i⟩
  have hS (i : ℕ) : HasLaw (s ∘ X i) (P.map s) μ :=
    (hasLaw_map hs.aemeasurable).comp (hXlaw i)
  have hident : ∀ i, IdentDistrib (s ∘ X i) (s ∘ X 0) μ μ := fun i ↦
    ⟨(hS i).aemeasurable, (hS 0).aemeasurable, (hS i).map_eq.trans (hS 0).map_eq.symm⟩
  have hind : iIndepFun (fun i ↦ s ∘ X i) μ :=
    hiid.2.1.comp₀ (fun _ ↦ s) (fun i ↦ (hiid.1 i).aemeasurable)
      (fun i ↦ by rw [hiid.2.2 i]; exact hs.aemeasurable)
  have hRmeas (n : ℕ) : AEMeasurable (R n) μ :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ (hS i).aemeasurable).const_mul _
  have hmean : μ[s ∘ X 0] = b := by
    rw [← hsmean]
    exact (hXlaw 0).integral_comp hs.aestronglyMeasurable
  have hR : TendstoInMeasure μ R atTop (fun _ ↦ b) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n ↦ (hRmeas n).aestronglyMeasurable)
    have hstrong := strong_law_ae (fun i ↦ s ∘ X i)
      ((hXlaw 0).integrable_comp hs) (fun i j hij ↦ hind.indepFun hij) hident
    rw [hmean] at hstrong
    simpa only [R, smul_eq_mul, Function.comp_apply] using hstrong
  have hc : Tendsto c atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have ht := (tendsto_const_nhds.sub hinv).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    have hce : (fun n : ℕ ↦ (1 - (n : ℝ)⁻¹)⁻¹) =ᶠ[atTop] c := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      dsimp only [c]
      rw [Nat.cast_sub hn, Nat.cast_one]
      by_cases hn1 : (n : ℝ) = 1
      · simp [hn1]
      · field_simp [hn0, sub_ne_zero.mpr hn1]
    simpa only [sub_zero, inv_one] using ht.congr' hce
  have hC : TendstoInMeasure μ (fun n (_ : Ω) ↦ c n) atTop (fun _ ↦ 1) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const) (ae_of_all _ fun _ ↦ hc)
  have hZ := hscore.continuous_comp (g := φ) (by dsimp only [φ]; fun_prop)
  have hZR := hZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 - p.2) (by fun_prop) hR hRmeas
  have hscaled := hZR.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.2 * p.1) (by fun_prop) hC (fun _ ↦ aemeasurable_const)
  let Y := fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) * uStatistic 2 n
    (fun z ↦ ∑ j, a j * e j (z 0) * e j (z 1)) (fun i ↦ X i.val ω)
  have hYe : ∀ n, (fun ω ↦ c n *
      (φ (WithLp.toLp 2 (fun j ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, e j (X i ω))) - R n ω)) = Y n := by
    intro n
    funext ω
    have h := uStatistic_two_finite_rank_eq r n a e (fun i ↦ X i.val ω)
    dsimp only [φ, R, c, Y, s]
    have heq (j : Fin r) : (∑ i : Fin n, e j (X i.val ω)) =
        ∑ i ∈ Finset.range n, e j (X i ω) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ e j (X i ω)) n
    have hes : (∑ i : Fin n, ∑ j, a j * e j (X i.val ω) ^ 2) =
        ∑ i ∈ Finset.range n, ∑ j, a j * e j (X i ω) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j, a j * e j (X i ω) ^ 2) n
    simpa only [heq, hes] using h.symm
  have hlimit : TendstoInDistribution Y atTop
      (fun z : EuclideanSpace ℝ (Fin r) ↦ φ z - b) (fun _ ↦ μ)
      (stdGaussian (EuclideanSpace ℝ (Fin r))) :=
    hscaled.congr (fun n ↦ ae_of_all _ fun ω ↦ congrFun (hYe n) ω)
      (ae_of_all _ fun z ↦ by simp only [Function.comp_apply, id_eq, one_mul])
  refine tendstoInDistribution_of_map_eq hlimit aemeasurable_id ?_
  rw [Measure.map_id, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  dsimp only [φ, b, Function.comp_apply]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]


/-- GAPS 102.30: finite-rank degenerate quadratic kernels have Gaussian-chaos limits. -/
theorem tendstoInDistribution_uStatistic_of_finite_rank_degenerate
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P) (r : ℕ) (a : Fin r → ℝ)
    (e : Fin r → E → ℝ) (he : ∀ j, MemLp (e j) 2 P)
    (he0 : ∀ j, (∫ x, e j x ∂P) = 0)
    (hortho : ∀ i j, (∫ x, e i x * e j x ∂P) = if i = j then 1 else 0) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (n : ℝ) * uStatistic 2 n
      (fun z ↦ ∑ j, a j * e j (z 0) * e j (z 1)) (fun i ↦ X i.val ω)) atTop id (fun _ ↦ μ)
      ((Measure.pi fun _ : Fin r ↦ gaussianReal 0 1).map
        (fun z ↦ ∑ j, a j * (z j ^ 2 - 1))) := by
  classical
  let v := fun x : E ↦ WithLp.toLp 2 (fun j ↦ e j x)
  let V := fun i ω ↦ v (X i ω)
  have hv : MemLp v 2 P := MemLp.of_eval_piLp he
  have hXlaw (i : ℕ) : HasLaw (X i) P μ := ⟨(hiid.1 i).aemeasurable, hiid.2.2 i⟩
  have hVlaw (i : ℕ) : HasLaw (V i) (P.map v) μ :=
    (hasLaw_map hv.aemeasurable).comp (hXlaw i)
  have hV2 : MemLp (V 0) 2 μ := (hXlaw 0).memLp_fun_comp hv
  have hVident : ∀ i, IdentDistrib (V i) (V 0) μ μ := fun i ↦
    ⟨(hVlaw i).aemeasurable, (hVlaw 0).aemeasurable, (hVlaw i).map_eq.trans (hVlaw 0).map_eq.symm⟩
  have hVind : iIndepFun V μ :=
    hiid.2.1.comp₀ (fun _ ↦ v) (fun i ↦ (hiid.1 i).aemeasurable)
      (fun i ↦ by rw [hiid.2.2 i]; exact hv.aemeasurable)
  have hVmean : (∫ ω, V 0 ω ∂μ) = 0 := by
    ext j
    rw [eval_integral_piLp (fun j ↦ ((hXlaw 0).memLp_fun_comp (he j)).integrable (by norm_num))]
    simpa only [V, v, PiLp.zero_apply, he0, Function.comp_apply] using
      (hXlaw 0).integral_comp (he j).aestronglyMeasurable
  have hcov : TauCeti.covMatrix (μ.map (V 0)) = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j
    rw [TauCeti.covMatrix_apply, covariance_map_fun (by fun_prop) (by fun_prop) (hVlaw 0).aemeasurable]
    change ProbabilityTheory.covariance (fun ω ↦ e i (X 0 ω)) (fun ω ↦ e j (X 0 ω)) μ = _
    rw [(hXlaw 0).covariance_fun_comp (he i).aemeasurable (he j).aemeasurable,
      covariance_eq_sub (he i) (he j), he0, he0, zero_mul, sub_zero]
    simpa only [Matrix.one_apply, Pi.mul_apply] using hortho i j
  have hclt := tendstoInDistribution_inv_sqrt_smul_sum_sub_of_iid μ V hV2 hVind hVident
  simp only [hVmean, hcov, multivariateGaussian_zero_one] at hclt
  apply tendstoInDistribution_uStatistic_finite_rank_of_scores μ P X hiid r a e he
    (fun j ↦ by simpa only [← pow_two, ite_true] using hortho j j)
  convert hclt using 1
  funext n ω
  simp only [smul_zero, sub_zero]
  ext j
  simp [V, v, smul_eq_mul]

end CKSD
