module

public import CKSD.Bayes.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Bayes: MonteCarlo

Sources: `GAPS.md`, `SYNOPSIS104.md`, and `STRUCTURE104.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 104.22, finite-state Metropolis–Hastings: stochasticity, balance and invariance. -/
theorem metropolisTransition_stochastic_and_detailed_balance
    {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1) :
    (∀ x y, 0 ≤ metropolisTransition π q x y) ∧
      (∀ x, ∑ y, metropolisTransition π q x y = 1) ∧
      (∀ x y, π x * metropolisTransition π q x y = π y * metropolisTransition π q y x) ∧
      ∀ y, (∑ x, π x * metropolisTransition π q x y) = π y := by
  have hacc (x y : Fin s) : 0 ≤ metropolisAcceptance π q x y ∧
      metropolisAcceptance π q x y ≤ 1 := by
    unfold metropolisAcceptance
    split_ifs with hzero
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_min zero_le_one (div_nonneg
        (mul_nonneg (hπ y).le (hq y x)) (mul_nonneg (hπ x).le (hq x y))),
        min_le_left _ _⟩
  have hrow (x : Fin s) : ∑ y, q x y * metropolisAcceptance π q x y ≤ 1 := by
    calc
      _ ≤ ∑ y, q x y := Finset.sum_le_sum fun y _ ↦ by
        simpa using mul_le_mul_of_nonneg_left (hacc x y).2 (hq x y)
      _ = 1 := hq1 x
  have hflux (x y : Fin s) :
      π x * q x y * metropolisAcceptance π q x y = min (π x * q x y) (π y * q y x) := by
    unfold metropolisAcceptance
    split_ifs with hzero
    · simp [hzero, min_eq_left (mul_nonneg (hπ y).le (hq y x))]
    · rw [mul_min_of_nonneg _ _ (mul_nonneg (hπ x).le (hq x y)), mul_one]
      congr 1
      field_simp [(hπ x).ne', (mul_ne_zero_iff.mp hzero).2]
      <;> ring
  have hstoch (x : Fin s) : ∑ y, metropolisTransition π q x y = 1 := by
    simp [metropolisTransition, Finset.sum_add_distrib]
  have hbalance (x y : Fin s) :
      π x * metropolisTransition π q x y = π y * metropolisTransition π q y x := by
    by_cases hxy : x = y
    · subst y; rfl
    · simp only [metropolisTransition, hxy, Ne.symm hxy, ↓reduceIte, add_zero]
      simpa only [← mul_assoc, hflux, min_comm]
  refine ⟨?_, hstoch, hbalance, ?_⟩
  · intro x y
    apply add_nonneg (mul_nonneg (hq x y) (hacc x y).1)
    split_ifs
    · exact sub_nonneg.mpr (hrow x)
    · exact le_rfl
  · intro y
    simp_rw [hbalance]
    rw [← Finset.mul_sum, hstoch, mul_one]

/-- GAPS 104.24, stationary finite-state Markov chain CLT with a positive transition matrix. -/
theorem tendstoInDistribution_finite_markov_chain_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ}
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n))
    (π : Fin s → ℝ) (K : Matrix (Fin s) (Fin s) ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hK : ∀ x y, 0 < K x y) (hK1 : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, (∑ x, π x * K x y) = π y)
    (hlaw : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n, X i ω = path i} = π (path 0) *
        ∏ i ∈ Finset.range n, K (path i) (path (i + 1)))
    (f : Fin s → ℝ) :
    let m := ∑ x, π x * f x;
    let sigmaSq := variance μ (f ∘ X 0) +
      2 * ∑' k : ℕ, covariance μ (f ∘ X 0) (f ∘ X (k + 1));
    Summable (fun k : ℕ ↦ |covariance μ (f ∘ X 0) (f ∘ X (k + 1))|) ∧
      TendstoInDistribution μ (fun n ω ↦ Real.sqrt n * (sampleAverage (fun i ω ↦ f
        (X i ω)) n ω - m))
        (gaussianReal 0 (Real.toNNReal sigmaSq)) := by
  sorry

/-- Powers of a finite stochastic matrix are nonnegative, stochastic, and keep an invariant law. -/
theorem pow_nonneg_stochastic_stationary {s : ℕ} (π : Fin s → ℝ)
    (K : Matrix (Fin s) (Fin s) ℝ) (hK : ∀ x y, 0 ≤ K x y) (hK1 : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y) (n : ℕ) :
    (∀ x y, 0 ≤ (K ^ n) x y) ∧ (∀ x, ∑ y, (K ^ n) x y = 1) ∧
      ∀ y, ∑ x, π x * (K ^ n) x y = π y := by
  induction n with
  | zero =>
      refine ⟨fun x y ↦ ?_, fun x ↦ ?_, fun y ↦ ?_⟩
      · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
      · simp [Matrix.one_apply]
      · simp [Matrix.one_apply]
  | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨fun x y ↦ ?_, fun x ↦ ?_, fun y ↦ ?_⟩
      · rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (h0 x z) (hK z y)
      · simp_rw [pow_succ, Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hK1, mul_one, h1]
      · simp_rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [← mul_assoc, ← Finset.sum_mul, h2, hstat]

/-- Doeblin's bound: a minorization `K x y ≥ ε π y` by the invariant law gives geometric
convergence of every row of `K ^ n` to `π`, uniformly over events. -/
theorem abs_sum_pow_sub_le_of_minorization {s : ℕ} (π : Fin s → ℝ)
    (K : Matrix (Fin s) (Fin s) ℝ) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hK : ∀ x y, 0 ≤ K x y) (hK1 : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y) (ε : ℝ) (hmin : ∀ x y, ε * π y ≤ K x y)
    (A : Finset (Fin s)) (n : ℕ) (x : Fin s) :
    |∑ y ∈ A, (K ^ n) x y - ∑ y ∈ A, π y| ≤ (1 - ε) ^ n := by
  have hA0 : 0 ≤ ∑ y ∈ A, π y := Finset.sum_nonneg fun y _ ↦ hπ y
  have hA1 : ∑ y ∈ A, π y ≤ 1 := hπ1 ▸ Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ A) fun y _ _ ↦ hπ y
  induction n generalizing x with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, pow_zero]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  | succ n ih =>
      set E : Fin s → ℝ := fun z ↦ ∑ y ∈ A, (K ^ n) z y - ∑ y ∈ A, π y with hE
      have hpow := pow_nonneg_stochastic_stationary π K hK hK1 hstat n
      -- The error propagates through `K`, and also through `K - ε π` since `π E = 0`.
      have hstep : ∑ y ∈ A, (K ^ (n + 1)) x y - ∑ y ∈ A, π y = ∑ z, K x z * E z := by
        simp_rw [pow_succ', Matrix.mul_apply, hE, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hK1, one_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      have hcenter : ∑ z, π z * E z = 0 := by
        simp_rw [hE, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [hpow.2.2, sub_self]
      have hstep' : ∑ y ∈ A, (K ^ (n + 1)) x y - ∑ y ∈ A, π y =
          ∑ z, (K x z - ε * π z) * E z := by
        rw [hstep]
        simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hcenter,
          mul_zero, sub_zero]
      rw [hstep', pow_succ]
      calc
        |∑ z, (K x z - ε * π z) * E z| ≤ ∑ z, (K x z - ε * π z) * |E z| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmin x z))]
        _ ≤ ∑ z, (K x z - ε * π z) * (1 - ε) ^ n :=
          Finset.sum_le_sum fun z _ ↦
            mul_le_mul_of_nonneg_left (ih z) (sub_nonneg.mpr (hmin x z))
        _ = (1 - ε) ^ n * (1 - ε) := by
          rw [← Finset.sum_mul, Finset.sum_sub_distrib, hK1, ← Finset.mul_sum, hπ1]
          ring

/-- GAPS 104.32, uniform convergence rate of a finite independence sampler. -/
theorem independence_sampler_totalVariationDistance_le {s : ℕ} (π g : Fin s → ℝ)
    (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hg : ∀ x, 0 < g x) (hg1 : ∑ x, g x = 1)
    (M : ℝ) (hM : 1 ≤ M) (hdom : ∀ x, π x ≤ M * g x)
    (n : ℕ) (x : Fin s) (A : Finset (Fin s)) :
    |(∑ y ∈ A, (metropolisTransition π (fun _ y ↦ g y) ^ n) x y) - ∑ y ∈ A, π y| ≤
      (1 - 1 / M) ^ n := by
  set q : Matrix (Fin s) (Fin s) ℝ := fun _ y ↦ g y with hq
  obtain ⟨hP0, hP1, -, hPst⟩ := metropolisTransition_stochastic_and_detailed_balance π q
    hπ hπ1 (fun _ y ↦ (hg y).le) (fun _ ↦ hg1)
  have hMpos : 0 < M := by linarith
  have hgy (y : Fin s) : 1 / M * π y ≤ g y := by
    rw [one_div_mul_eq_div, div_le_iff₀ hMpos]
    linarith [hdom y]
  -- The independence sampler is minorized by `π / M` in every row.
  have hmin (x y : Fin s) : 1 / M * π y ≤ metropolisTransition π q x y := by
    have hacc (z : Fin s) : metropolisAcceptance π q x z ≤ 1 := by
      unfold metropolisAcceptance
      split_ifs
      exacts [le_rfl, min_le_left _ _]
    have hrej : 0 ≤ 1 - ∑ z, q x z * metropolisAcceptance π q x z := by
      have : ∑ z, q x z * metropolisAcceptance π q x z ≤ ∑ z, q x z :=
        Finset.sum_le_sum fun z _ ↦ by
          simpa using mul_le_mul_of_nonneg_left (hacc z) (hg z).le
      simp only [hq, hg1] at this ⊢
      linarith
    by_cases hxy : x = y
    · subst hxy
      have h1 : metropolisAcceptance π q x x = 1 := by
        have hne : π x * q x x ≠ 0 := (mul_pos (hπ x) (hg x)).ne'
        simp [metropolisAcceptance, hne]
      simp only [metropolisTransition, ↓reduceIte, h1, mul_one]
      have : q x x = g x := rfl
      linarith [hgy x]
    · simp only [metropolisTransition, hxy, ↓reduceIte, add_zero]
      unfold metropolisAcceptance
      have hne : π x * q x y ≠ 0 := (mul_pos (hπ x) (hg y)).ne'
      simp only [hne, ↓reduceIte]
      rw [mul_min_of_nonneg _ _ (hg y).le, mul_one]
      refine le_min (hgy y) ?_
      have hrw : q x y * (π y * q y x / (π x * q x y)) = π y * (g x / π x) := by
        simp only [hq]
        field_simp [(hπ x).ne', (hg y).ne']
      rw [hrw, mul_comm (1 / M)]
      refine mul_le_mul_of_nonneg_left ?_ (hπ y).le
      rw [div_le_div_iff₀ hMpos (hπ x)]
      linarith [hdom x]
  exact abs_sum_pow_sub_le_of_minorization π _ (fun x ↦ (hπ x).le) hπ1 hP0 hP1 hPst _ hmin
    A n x

/-- GAPS 104.35, reversibility and volume preservation of repeated leapfrog steps. -/
theorem leapfrogStep_iterate_measurePreserving_and_reversible {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (h : ℝ) (L : ℕ) :
    let R := fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦ (z.1, -z.2);
    MeasurePreserving ((leapfrogStep g h)^[L]) volume volume ∧
      ∀ z, (leapfrogStep g h)^[L] (R ((leapfrogStep g h)^[L] z)) = R z := by
  let E := EuclideanSpace ℝ (Fin d)
  let R := fun z : E × E ↦ (z.1, -z.2)
  let K := fun z : E × E ↦ (z.1, z.2 - (h / 2) • g z.1)
  let D := fun z : E × E ↦ (z.1 + h • z.2, z.2)
  -- Each kick is a translation in momentum at a fixed position.
  have hK : MeasurePreserving K volume volume := by
    rw [Measure.volume_eq_prod E E]
    apply (MeasurePreserving.id (volume : Measure E)).skew_product
      (g := fun x p ↦ p - (h / 2) • g x)
    · exact measurable_snd.sub ((hg.comp measurable_fst).const_smul (h / 2))
    · exact ae_of_all _ fun x ↦ by
        simpa only [sub_eq_add_neg, neg_smul] using
          (measurePreserving_add_right (volume : Measure E) (-(h / 2) • g x)).map_eq
  -- Interchanging position and momentum turns the drift into another translation.
  have hDskew : MeasurePreserving (fun z : E × E ↦ (z.1, z.2 + h • z.1))
      volume volume := by
    rw [Measure.volume_eq_prod E E]
    apply (MeasurePreserving.id (volume : Measure E)).skew_product
      (g := fun x p ↦ p + h • x)
    · exact measurable_snd.add (measurable_fst.const_smul h)
    · exact ae_of_all _ fun x ↦
        (measurePreserving_add_right (volume : Measure E) (h • x)).map_eq
  have hswap : MeasurePreserving (Prod.swap : E × E → E × E) volume volume := by
    rw [Measure.volume_eq_prod E E]
    exact Measure.measurePreserving_swap
  have hD : MeasurePreserving D volume volume := hswap.comp (hDskew.comp hswap)
  have hstep : leapfrogStep g h = K ∘ D ∘ K := rfl
  have hmp : MeasurePreserving (leapfrogStep g h) volume volume := by
    rw [hstep]
    exact hK.comp (hD.comp hK)
  have hrev (z : E × E) : leapfrogStep g h (R (leapfrogStep g h z)) = R z := by
    have hp : -(z.2 - (h / 2) • g z.1 -
        (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1))) -
        (h / 2) • g (z.1 + h • (z.2 - (h / 2) • g z.1)) =
        -(z.2 - (h / 2) • g z.1) := by abel
    have hx : z.1 + h • (z.2 - (h / 2) • g z.1) +
        h • (-(z.2 - (h / 2) • g z.1)) = z.1 := by
      simp only [smul_neg]
      abel
    dsimp only [leapfrogStep, R]
    rw [hp, hx]
    congr 1
    abel
  refine ⟨hmp.iterate L, ?_⟩
  change ∀ z, (leapfrogStep g h)^[L] (R ((leapfrogStep g h)^[L] z)) = R z
  induction L with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, hrev]


/-- GAPS 104.31, finite-state form of total-variation convergence of Metropolis–Hastings.
The target is positive; irreducibility is taken in the sufficient form `q x y > 0` for `x ≠ y`,
and aperiodicity in the sufficient form that some proposed move has acceptance below one.
The convergence is uniform over events, which is total-variation convergence. -/
theorem eventually_abs_metropolisTransition_pow_sub_le {s : ℕ} (π : Fin s → ℝ)
    (q : Matrix (Fin s) (Fin s) ℝ) (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1)
    (hirr : ∀ x y, x ≠ y → 0 < q x y)
    (hap : ∃ x y, 0 < q x y ∧ metropolisAcceptance π q x y < 1) (x : Fin s) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ A : Finset (Fin s),
      |∑ y ∈ A, (metropolisTransition π q ^ n) x y - ∑ y ∈ A, π y| ≤ ε := by
  set P := metropolisTransition π q with hPdef
  obtain ⟨hP0, hP1, -, hPst⟩ :=
    metropolisTransition_stochastic_and_detailed_balance π q hπ hπ1 hq hq1
  obtain ⟨x₀, y₀, hqy₀, hacc₀⟩ := hap
  have hacc_le (u z : Fin s) : metropolisAcceptance π q u z ≤ 1 := by
    unfold metropolisAcceptance
    split_ifs
    exacts [le_rfl, min_le_left _ _]
  have hacc_pos (u z : Fin s) : 0 < metropolisAcceptance π q u z := by
    unfold metropolisAcceptance
    split_ifs with h0
    · exact one_pos
    · have hqz : 0 < q u z := lt_of_le_of_ne (hq u z) fun h ↦ h0 (by rw [← h, mul_zero])
      have hzu : 0 < q z u := by
        by_cases hzu : z = u
        · subst hzu; exact hqz
        · exact hirr z u hzu
      exact lt_min one_pos (div_pos (mul_pos (hπ z) hzu) (mul_pos (hπ u) hqz))
  -- Off-diagonal moves are possible, and the state `x₀` rejects with positive probability.
  have hoff (u z : Fin s) (h : u ≠ z) : 0 < P u z := by
    simp only [hPdef, metropolisTransition, h, ↓reduceIte, add_zero]
    exact mul_pos (hirr u z h) (hacc_pos u z)
  have hdiag : 0 < P x₀ x₀ := by
    have hlt : ∑ z, q x₀ z * metropolisAcceptance π q x₀ z < ∑ z, q x₀ z := by
      apply Finset.sum_lt_sum
      · intro z _
        simpa using mul_le_mul_of_nonneg_left (hacc_le x₀ z) (hq x₀ z)
      · exact ⟨y₀, Finset.mem_univ _, by
          simpa using mul_lt_mul_of_pos_left hacc₀ hqy₀⟩
    simp only [hPdef, metropolisTransition, ↓reduceIte]
    rw [hq1] at hlt
    have := mul_nonneg (hq x₀ x₀) (hacc_pos x₀ x₀).le
    linarith
  have hto (u : Fin s) : 0 < P u x₀ := by
    by_cases h : u = x₀
    · subst h; exact hdiag
    · exact hoff u x₀ h
  have hfrom (z : Fin s) : 0 < P x₀ z := by
    by_cases h : x₀ = z
    · subst h; exact hdiag
    · exact hoff x₀ z h
  -- Three steps through `x₀` give a strictly positive matrix.
  set K := P ^ 3 with hKdef
  have hKpos (u z : Fin s) : 0 < K u z := by
    have hK : K u z = ∑ b, (∑ a, P u a * P a b) * P b z := by
      rw [hKdef, pow_succ, pow_two, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    rw [hK]
    have hin (b : Fin s) : 0 ≤ ∑ a, P u a * P a b :=
      Finset.sum_nonneg fun a _ ↦ mul_nonneg (hP0 u a) (hP0 a b)
    calc
      0 < (P u x₀ * P x₀ x₀) * P x₀ z := mul_pos (mul_pos (hto u) hdiag) (hfrom z)
      _ ≤ (∑ a, P u a * P a x₀) * P x₀ z := by
        refine mul_le_mul_of_nonneg_right ?_ (hP0 x₀ z)
        exact Finset.single_le_sum (f := fun a ↦ P u a * P a x₀)
          (fun a _ ↦ mul_nonneg (hP0 u a) (hP0 a x₀)) (Finset.mem_univ x₀)
      _ ≤ ∑ b, (∑ a, P u a * P a b) * P b z :=
        Finset.single_le_sum (f := fun b ↦ (∑ a, P u a * P a b) * P b z)
          (fun b _ ↦ mul_nonneg (hin b) (hP0 b z)) (Finset.mem_univ x₀)
  obtain ⟨hK0, hK1, hKst⟩ := pow_nonneg_stochastic_stationary π P hP0 hP1 hPst 3
  set m := (Finset.univ : Finset (Fin s × Fin s)).inf' ⟨(x, x), Finset.mem_univ _⟩
    (fun z ↦ K z.1 z.2) with hm
  have hm_pos : 0 < m := (Finset.lt_inf'_iff _).2 fun z _ ↦ hKpos z.1 z.2
  have hm_le (u z : Fin s) : m ≤ K u z :=
    Finset.inf'_le (fun z : Fin s × Fin s ↦ K z.1 z.2) (Finset.mem_univ (u, z))
  have hm_one : m ≤ 1 := by
    have := Finset.single_le_sum (f := fun z ↦ K x z) (fun z _ ↦ hK0 x z)
      (Finset.mem_univ x)
    have h1 : ∑ z, K x z = 1 := hK1 x
    linarith [hm_le x x]
  have hπle (y : Fin s) : π y ≤ 1 := hπ1 ▸ Finset.single_le_sum (f := π)
    (fun z _ ↦ (hπ z).le) (Finset.mem_univ y)
  have hmin (u z : Fin s) : m * π z ≤ K u z :=
    (mul_le_of_le_one_right hm_pos.le (hπle z)).trans (hm_le u z)
  have hK3 (k : ℕ) (u : Fin s) (A : Finset (Fin s)) :
      |∑ y ∈ A, (K ^ k) u y - ∑ y ∈ A, π y| ≤ (1 - m) ^ k :=
    abs_sum_pow_sub_le_of_minorization π K (fun z ↦ (hπ z).le) hπ1 hK0 hK1 hKst m hmin A k u
  -- Remaining steps average the errors of `K ^ k` with stochastic weights.
  have hbound (n : ℕ) (A : Finset (Fin s)) :
      |∑ y ∈ A, (P ^ n) x y - ∑ y ∈ A, π y| ≤ (1 - m) ^ (n / 3) := by
    obtain ⟨hR0, hR1, -⟩ := pow_nonneg_stochastic_stationary π P hP0 hP1 hPst (n % 3)
    have hsplit : P ^ n = P ^ (n % 3) * K ^ (n / 3) := by
      rw [hKdef, ← pow_mul, ← pow_add, Nat.mod_add_div]
    have hrw : ∑ y ∈ A, (P ^ n) x y - ∑ y ∈ A, π y =
        ∑ z, (P ^ (n % 3)) x z * (∑ y ∈ A, (K ^ (n / 3)) z y - ∑ y ∈ A, π y) := by
      simp_rw [hsplit, Matrix.mul_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hR1, one_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hrw]
    calc
      _ ≤ ∑ z, (P ^ (n % 3)) x z * |∑ y ∈ A, (K ^ (n / 3)) z y - ∑ y ∈ A, π y| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun z _ ↦ by rw [abs_mul, abs_of_nonneg (hR0 x z)]
      _ ≤ ∑ z, (P ^ (n % 3)) x z * (1 - m) ^ (n / 3) :=
        Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (hK3 _ z A) (hR0 x z)
      _ = (1 - m) ^ (n / 3) := by rw [← Finset.sum_mul, hR1, one_mul]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - m < 1)
  filter_upwards [eventually_ge_atTop (3 * k₀)] with n hn A
  have hk : k₀ ≤ n / 3 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  calc
    _ ≤ (1 - m) ^ (n / 3) := hbound n A
    _ ≤ (1 - m) ^ k₀ := pow_le_pow_of_le_one (by linarith) (by linarith) hk
    _ ≤ ε := hk₀.le

/-- GAPS 104.31, finite-state ergodic theorem for Metropolis–Hastings from a fixed initial state.
The chain is specified by its finite-dimensional path probabilities; irreducibility is taken in the
sufficient form `q x y > 0` for `x ≠ y`. On a finite space every function is `π`-integrable. -/
theorem ae_tendsto_sampleAverage_metropolis {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ} (π : Fin s → ℝ)
    (q : Matrix (Fin s) (Fin s) ℝ) (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hq : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1)
    (hirr : ∀ x y, x ≠ y → 0 < q x y)
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n)) (x₀ : Fin s)
    (hlaw : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n, X i ω = path i} = (if path 0 = x₀ then 1 else 0) *
        ∏ i ∈ Finset.range n, metropolisTransition π q (path i) (path (i + 1)))
    (h : Fin s → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ sampleAverage (fun i ω ↦ h (X i ω)) n ω) atTop
      (𝓝 (∑ x, π x * h x)) := by
  sorry

end CKSD
