module

public import CKSD.Bayes.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Analysis.SpecificLimits.FloorPow
public import Mathlib.Analysis.PSeries

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

/-- GAPS 104.22, finite-state Metropolis–Hastings: stochasticity, balance and invariance
for positive target weights, without a normalization requirement. -/
theorem metropolisTransition_stochastic_and_detailed_balance
    {s : ℕ} (π : Fin s → ℝ) (q : Matrix (Fin s) (Fin s) ℝ)
    (hπ : ∀ x, 0 < π x)
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
    hπ (fun _ y ↦ (hg y).le) (fun _ ↦ hg1)
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
    metropolisTransition_stochastic_and_detailed_balance π q hπ hq hq1
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

/-- The integral of a function of a random variable with finitely many values is the sum of the
values weighted by their probabilities. -/
theorem integral_comp_eq_sum_measureReal {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (Y : Ω → β) (hY : Measurable Y) (F : β → ℝ) :
    ∫ ω, F (Y ω) ∂μ = ∑ b, μ.real (Y ⁻¹' {b}) * F b := by
  rw [← integral_map hY.aemeasurable
    (measurable_of_finite F).aestronglyMeasurable, integral_fintype Integrable.of_finite]
  simp [map_measureReal_apply hY (measurableSet_singleton _)]

/-- A function of a random variable with finitely many values is integrable under a finite
measure. -/
theorem integrable_comp_of_fintype {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (Y : Ω → β) (hY : Measurable Y) (F : β → ℝ) : Integrable (fun ω ↦ F (Y ω)) μ :=
  (Integrable.of_finite (μ := μ.map Y)).comp_measurable hY

/-- The prefix `(X 0, …, X n)` of a measurable finite-state process is measurable. -/
theorem measurable_finChainPrefix {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable fun ω (i : Fin (n + 1)) ↦ X i ω :=
  measurable_pi_iff.2 fun i ↦ hX i

/-- One-step Markov property of a finite-state chain given by its path probabilities: for a
function `F` of the prefix `(X 0, …, X n)`, `𝔼[F · v(X (n+1))] = 𝔼[F · (K v)(X n)]`. -/
theorem integral_mul_comp_succ_eq_mulVec {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ} (K : Matrix (Fin s) (Fin s) ℝ)
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n))
    (hstep : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n + 1, X i ω = path i} =
        μ.real {ω | ∀ i ≤ n, X i ω = path i} * K (path n) (path (n + 1)))
    (n : ℕ) (F : (Fin (n + 1) → Fin s) → ℝ) (v : Fin s → ℝ) :
    ∫ ω, F (fun i : Fin (n + 1) ↦ X i ω) * v (X (n + 1) ω) ∂μ =
      ∫ ω, F (fun i : Fin (n + 1) ↦ X i ω) * (Matrix.mulVec K v) (X n ω) ∂μ := by
  have hpre := measurable_finChainPrefix X hX n
  rw [integral_comp_eq_sum_measureReal μ (fun ω ↦ ((fun i : Fin (n + 1) ↦ X i ω), X (n + 1) ω))
      (hpre.prodMk (hX (n + 1))) (fun z ↦ F z.1 * v z.2)]
  have h2 := integral_comp_eq_sum_measureReal μ (fun ω (i : Fin (n + 1)) ↦ X i ω) hpre
      (fun z ↦ F z * (Matrix.mulVec K v) (z (Fin.last n)))
  simp only [Fin.val_last] at h2
  rw [h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  set path : ℕ → Fin s := fun i ↦ if h : i < n + 1 then z ⟨i, h⟩ else z 0 with hpath
  have hset (y : Fin s) : (fun ω ↦ ((fun i : Fin (n + 1) ↦ X i ω), X (n + 1) ω)) ⁻¹' {(z, y)} =
      {ω | ∀ i ≤ n + 1, X i ω = (Function.update path (n + 1) y) i} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, funext_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · rw [Function.update_of_ne (by omega), hpath]
        simp only [h, ↓reduceDIte]
        exact h1 ⟨i, h⟩
      · obtain rfl : i = n + 1 := by omega
        simpa using h2
    · intro h
      refine ⟨fun i ↦ ?_, by simpa using h (n + 1) le_rfl⟩
      have := h i (by omega)
      rw [Function.update_of_ne (by omega)] at this
      simpa [hpath, Nat.lt_succ_iff.mp i.2] using this
  have hset0 : (fun ω (i : Fin (n + 1)) ↦ X i ω) ⁻¹' {z} =
      {ω | ∀ i ≤ n, X i ω = (Function.update path (n + 1) (z 0)) i} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, funext_iff, mem_ofPred_eq]
    constructor
    · intro h1 i hi
      rw [Function.update_of_ne (by omega)]
      simp only [hpath, show i < n + 1 by omega, ↓reduceDIte]
      exact h1 ⟨i, by omega⟩
    · intro h i
      have := h i (by omega)
      rw [Function.update_of_ne (by omega)] at this
      simpa [hpath, Nat.lt_succ_iff.mp i.2] using this
  have hlast : path n = z (Fin.last n) := by
    simp [hpath, Fin.last]
  simp_rw [hset, hstep]
  have hpre0 (y : Fin s) : {ω | ∀ i ≤ n, X i ω = Function.update path (n + 1) y i} =
      (fun ω (i : Fin (n + 1)) ↦ X i ω) ⁻¹' {z} := by
    rw [hset0]
    ext ω
    simp only [mem_ofPred_eq]
    refine forall₂_congr fun i hi ↦ ?_
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  simp_rw [hpre0, Function.update_self, Function.update_of_ne (by omega : n ≠ n + 1), hlast,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  ring

/-- Second moment of the martingale `∑_{i<n} (u(X (i+1)) - (K u)(X i))` of a finite-state chain:
the increments are orthogonal, so a bound `B` on them gives `𝔼[Mₙ²] ≤ n B²`. -/
theorem integral_sq_sum_markovIncrement_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ} (K : Matrix (Fin s) (Fin s) ℝ)
    (X : ℕ → Ω → Fin s) (hX : ∀ n, Measurable (X n))
    (hstep : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n + 1, X i ω = path i} =
        μ.real {ω | ∀ i ≤ n, X i ω = path i} * K (path n) (path (n + 1)))
    (u : Fin s → ℝ) (B : ℝ) (hB : ∀ x y, |u y - Matrix.mulVec K u x| ≤ B) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, (u (X (i + 1) ω) - Matrix.mulVec K u (X i ω))) ^ 2 ∂μ ≤
      n * B ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpre := measurable_finChainPrefix X hX n
    set F : (Fin (n + 1) → Fin s) → ℝ := fun z ↦
      ∑ i : Fin n, (u (z i.succ) - Matrix.mulVec K u (z i.castSucc)) with hF
    have hM (ω : Ω) : ∑ i ∈ Finset.range n, (u (X (i + 1) ω) - Matrix.mulVec K u (X i ω)) =
        F (fun i : Fin (n + 1) ↦ X i ω) := by
      rw [hF, ← Fin.sum_univ_eq_sum_range]
      rfl
    have hY : Measurable fun ω ↦ ((fun i : Fin (n + 1) ↦ X i ω), X (n + 1) ω) :=
      hpre.prodMk (hX (n + 1))
    have hint (G : (Fin (n + 1) → Fin s) × Fin s → ℝ) :
        Integrable (fun ω ↦ G ((fun i : Fin (n + 1) ↦ X i ω), X (n + 1) ω)) μ :=
      integrable_comp_of_fintype μ _ hY G
    have hexp (ω : Ω) : (∑ i ∈ Finset.range (n + 1),
        (u (X (i + 1) ω) - Matrix.mulVec K u (X i ω))) ^ 2 =
        F (fun i : Fin (n + 1) ↦ X i ω) ^ 2 +
          2 * (F (fun i : Fin (n + 1) ↦ X i ω) * u (X (n + 1) ω) -
            F (fun i : Fin (n + 1) ↦ X i ω) * Matrix.mulVec K u (X n ω)) +
          (u (X (n + 1) ω) - Matrix.mulVec K u (X n ω)) ^ 2 := by
      rw [Finset.sum_range_succ, hM]
      ring
    simp_rw [hexp]
    have hlast (ω : Ω) : X n ω = (fun i : Fin (n + 1) ↦ X i ω) (Fin.last n) := rfl
    have i1 := hint fun z ↦ F z.1 ^ 2
    have i2 := hint fun z ↦ F z.1 * u z.2
    have i3 := hint fun z ↦ F z.1 * Matrix.mulVec K u (z.1 (Fin.last n))
    have i4 := hint fun z ↦ (u z.2 - Matrix.mulVec K u (z.1 (Fin.last n))) ^ 2
    simp only [Fin.val_last] at i1 i2 i3 i4
    have i23 : Integrable (fun ω ↦ 2 * ((F fun i : Fin (n + 1) ↦ X i ω) * u (X (n + 1) ω) -
        (F fun i : Fin (n + 1) ↦ X i ω) * Matrix.mulVec K u (X n ω))) μ :=
      (i2.sub i3).const_mul 2
    have e1 := integral_add (i1.add i23) i4
    have e2 := integral_add i1 i23
    simp only [Pi.add_apply] at e1
    rw [e1, e2, integral_const_mul,
      integral_sub i2 i3, integral_mul_comp_succ_eq_mulVec μ K X hX hstep n F u, sub_self,
      mul_zero, add_zero]
    have hD : ∫ ω, (u (X (n + 1) ω) - Matrix.mulVec K u (X n ω)) ^ 2 ∂μ ≤ B ^ 2 := by
      calc _ ≤ ∫ _ω, B ^ 2 ∂μ := integral_mono i4 (integrable_const _) fun ω ↦ by
              simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB (X n ω) (X (n + 1) ω)) 2
        _ = B ^ 2 := by simp
    have ih' : ∫ ω, F (fun i : Fin (n + 1) ↦ X i ω) ^ 2 ∂μ ≤ n * B ^ 2 := by
      simpa only [hM] using ih
    push_cast
    linarith

/-- Poisson equation for a finite stochastic matrix with positive off-diagonal entries and a
positive invariant law `π`: every `π`-centred `g` is `u - P u` for some `u`. The solution is
`u = ½ ∑ₖ Lᵏ g` for the lazy chain `L = (I + P)/2`, which converges geometrically by Doeblin's
bound. -/
theorem exists_sub_mulVec_eq_of_offDiag_pos {s : ℕ} (π : Fin s → ℝ)
    (P : Matrix (Fin s) (Fin s) ℝ) (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    (hPst : ∀ y, ∑ x, π x * P x y = π y) (hoff : ∀ x y, x ≠ y → 0 < P x y)
    (g : Fin s → ℝ) (hg : ∑ x, π x * g x = 0) :
    ∃ u : Fin s → ℝ, ∀ x, u x - Matrix.mulVec P u x = g x := by
  -- The lazy chain `L = (I + P) / 2` has strictly positive entries.
  set L : Matrix (Fin s) (Fin s) ℝ := (2 : ℝ)⁻¹ • (1 + P) with hL
  have hLe (x y : Fin s) : L x y = ((if x = y then 1 else 0) + P x y) / 2 := by
    simp only [hL, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have hLpos (x y : Fin s) : 0 < L x y := by
    rw [hLe]
    by_cases h : x = y
    · subst h; simp only [↓reduceIte]; linarith [hP0 x x]
    · simp only [h, ↓reduceIte, zero_add]; linarith [hoff x y h]
  have hL1 (x : Fin s) : ∑ y, L x y = 1 := by
    simp only [hLe, ← Finset.sum_div, Finset.sum_add_distrib, hP1, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    norm_num
  have hLst (y : Fin s) : ∑ x, π x * L x y = π y := by
    simp only [hLe, mul_div_assoc', ← Finset.sum_div, mul_add, Finset.sum_add_distrib, hPst,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  by_cases hs : s = 0
  · subst hs; exact ⟨0, fun x ↦ x.elim0⟩
  have x₀ : Fin s := ⟨0, Nat.pos_of_ne_zero hs⟩
  set m := (Finset.univ : Finset (Fin s × Fin s)).inf' ⟨(x₀, x₀), Finset.mem_univ _⟩
    (fun z ↦ L z.1 z.2) with hm
  have hm_pos : 0 < m := (Finset.lt_inf'_iff _).2 fun z _ ↦ hLpos z.1 z.2
  have hm_le (u z : Fin s) : m ≤ L u z :=
    Finset.inf'_le (fun z : Fin s × Fin s ↦ L z.1 z.2) (Finset.mem_univ (u, z))
  have hm_one : m ≤ 1 := by
    have := Finset.single_le_sum (f := fun z ↦ L x₀ z) (fun z _ ↦ (hLpos x₀ z).le)
      (Finset.mem_univ x₀)
    linarith [hm_le x₀ x₀, hL1 x₀]
  have hπle (y : Fin s) : π y ≤ 1 := hπ1 ▸ Finset.single_le_sum (f := π)
    (fun z _ ↦ (hπ z).le) (Finset.mem_univ y)
  have hmin (u z : Fin s) : m * π z ≤ L u z :=
    (mul_le_of_le_one_right hm_pos.le (hπle z)).trans (hm_le u z)
  set G := ∑ y, |g y| with hG
  -- Geometric decay of `Lᵏ g`, since `g` is centred under `π`.
  have hdecay (k : ℕ) (x : Fin s) : |Matrix.mulVec (L ^ k) g x| ≤ G * (1 - m) ^ k := by
    have hrw : Matrix.mulVec (L ^ k) g x = ∑ y, ((L ^ k) x y - π y) * g y := by
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, hg, sub_zero]
    rw [hrw, hG, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
    rw [abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa using abs_sum_pow_sub_le_of_minorization π L (fun z ↦ (hπ z).le) hπ1
      (fun a b ↦ (hLpos a b).le) hL1 hLst m hmin {y} k x
  have hsum (x : Fin s) : Summable fun k ↦ Matrix.mulVec (L ^ k) g x :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := 1 - m) (by linarith) (by linarith)).mul_left G)
      fun k ↦ by simpa [Real.norm_eq_abs] using hdecay k x
  set w : Fin s → ℝ := fun x ↦ ∑' k, Matrix.mulVec (L ^ k) g x with hw
  have hLw (x : Fin s) : Matrix.mulVec L w x = w x - g x := by
    have h1 : Matrix.mulVec L w x = ∑' k, Matrix.mulVec (L ^ (k + 1)) g x := by
      calc Matrix.mulVec L w x = ∑ y, ∑' k, L x y * Matrix.mulVec (L ^ k) g y := by
            simp only [Matrix.mulVec, dotProduct, hw]
            exact Finset.sum_congr rfl fun y _ ↦ ((hsum y).tsum_mul_left (L x y)).symm
        _ = ∑' k, ∑ y, L x y * Matrix.mulVec (L ^ k) g y :=
            (Summable.tsum_finsetSum fun y _ ↦ (hsum y).mul_left (L x y)).symm
        _ = ∑' k, Matrix.mulVec (L ^ (k + 1)) g x := by
            congr 1 with k
            rw [pow_succ', ← Matrix.mulVec_mulVec]
            rfl
    rw [h1]
    simp only [hw]
    rw [(hsum x).tsum_eq_zero_add]
    simp
  refine ⟨fun x ↦ w x / 2, fun x ↦ ?_⟩
  have hLv : Matrix.mulVec L w x = (w x + Matrix.mulVec P w x) / 2 := by
    simp only [hL, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul]
    ring
  have hPw : Matrix.mulVec P w x = 2 * Matrix.mulVec L w x - w x := by
    rw [hLv]; ring
  have hPu : Matrix.mulVec P (fun x ↦ w x / 2) x = Matrix.mulVec P w x / 2 := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc']
  rw [hPu, hPw, hLw]
  ring
/-- For a bounded real sequence, convergence of the centred averages along the squares
`(k+1)²` implies convergence of all averages, by monotonicity of the shifted partial sums. -/
theorem tendsto_avg_of_tendsto_sum_sq_div {a : ℕ → ℝ} {H l : ℝ} (ha : ∀ i, |a i| ≤ H)
    (hsq : Tendsto (fun k : ℕ ↦ (∑ i ∈ Finset.range ((k + 1) ^ 2), (a i - l)) /
      (((k + 1) ^ 2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 l) := by
  set T : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, (a i + H) with hT
  have hmono : Monotone T := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    simp only [hT, Finset.sum_range_succ]
    linarith [(abs_le.1 (ha n)).1]
  have hTsplit (n : ℕ) : T n = ∑ i ∈ Finset.range n, (a i - l) + n * (l + H) := by
    simp only [hT, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  have hTlim : Tendsto (fun n ↦ T n / n) atTop (𝓝 (l + H)) := by
    refine tendsto_div_of_monotone_of_exists_subseq_tendsto_div T (l + H) hmono fun b hb ↦ ?_
    refine ⟨fun k ↦ (k + 1) ^ 2, ?_, ?_, ?_⟩
    · have hlim : Tendsto (fun k : ℕ ↦ (1 + 1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
        ((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).pow 2)
      rw [add_zero, one_pow] at hlim
      filter_upwards [(tendsto_order.1 hlim).2 b hb] with k hk
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have : ((k + 1 + 1 : ℕ) : ℝ) ^ 2 = (1 + 1 / ((k : ℝ) + 1)) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
        field_simp
        push_cast
        ring
      push_cast at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_right hk.le (by positivity)
    · exact tendsto_atTop_mono (fun k ↦ by nlinarith : ∀ k : ℕ, k ≤ (k + 1) ^ 2) tendsto_id
    · have : (fun k : ℕ ↦ T ((k + 1) ^ 2) / (((k + 1) ^ 2 : ℕ) : ℝ)) =
          fun k : ℕ ↦ (∑ i ∈ Finset.range ((k + 1) ^ 2), (a i - l)) /
            (((k + 1) ^ 2 : ℕ) : ℝ) + (l + H) := by
        funext k
        rw [hTsplit, add_div, mul_div_cancel_left₀ _ (by positivity)]
      rw [this]
      simpa using hsq.add_const (l + H)
  have := hTlim.sub_const H
  rw [add_sub_cancel_right] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [hT, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- If `𝔼[Sₙ²] ≤ C n`, then `Sₙ / n → 0` almost surely along the squares `n = (k+1)²`, by
Chebyshev's inequality and the Borel–Cantelli lemma. -/
theorem ae_tendsto_div_sq_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : ℕ → Ω → ℝ)
    (hint : ∀ n, Integrable (fun ω ↦ S n ω ^ 2) μ) (C : ℝ)
    (hC : ∀ n, ∫ ω, S n ω ^ 2 ∂μ ≤ C * n) :
    ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ ↦ S ((k + 1) ^ 2) ω / (((k + 1) ^ 2 : ℕ) : ℝ)) atTop
      (𝓝 0) := by
  have hC0 : 0 ≤ C := by
    have := hC 1
    have h0 : 0 ≤ ∫ ω, S 1 ω ^ 2 ∂μ := integral_nonneg fun ω ↦ sq_nonneg _
    simp only [Nat.cast_one, mul_one] at this
    linarith
  have key (j : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
      |S ((k + 1) ^ 2) ω / (((k + 1) ^ 2 : ℕ) : ℝ)| < 1 / ((j : ℝ) + 1) := by
    set δ : ℝ := 1 / ((j : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set N : ℕ → ℝ := fun k ↦ (((k + 1) ^ 2 : ℕ) : ℝ) with hN
    have hN0 (k : ℕ) : 0 < N k := by simp only [hN]; positivity
    set A : ℕ → Set Ω := fun k ↦ {ω | δ ^ 2 * N k ^ 2 ≤ S ((k + 1) ^ 2) ω ^ 2} with hA
    set b : ℕ → ℝ := fun k ↦ C / δ ^ 2 * (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) with hb
    have hbsum : Summable b := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
      exact this.mul_left _
    have hb0 (k : ℕ) : 0 ≤ b k := by simp only [hb]; positivity
    have hAb (k : ℕ) : μ (A k) ≤ ENNReal.ofReal (b k) := by
      rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ?_
      have hε : 0 < δ ^ 2 * N k ^ 2 := by have := hN0 k; positivity
      have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _)
        (hint ((k + 1) ^ 2)) (δ ^ 2 * N k ^ 2)
      have hCk := hC ((k + 1) ^ 2)
      have : μ.real (A k) ≤ C * N k / (δ ^ 2 * N k ^ 2) := by
        rw [le_div_iff₀ hε, mul_comm]
        exact hm.trans hCk
      refine this.trans (le_of_eq ?_)
      simp only [hb, hN]
      push_cast
      field_simp
    have htsum : ∑' k, μ (A k) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_
        (CompleteLattice.summable.tsum_le_tsum hAb CompleteLattice.summable)
      rw [← ENNReal.ofReal_tsum_of_nonneg hb0 hbsum]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem htsum] with ω hω
    filter_upwards [hω] with k hk
    simp only [hA, mem_ofPred_eq, not_le] at hk
    have hNk := hN0 k
    rw [abs_div, abs_of_pos hNk, div_lt_iff₀ hNk]
    have : |S ((k + 1) ^ 2) ω| ^ 2 < (δ * N k) ^ 2 := by rw [sq_abs, mul_pow]; exact hk
    exact (pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).1 this
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := (hω j).exists_forall_of_atTop
  exact ⟨K, fun k hk ↦ by rw [Real.dist_eq, sub_zero]; exact (hK k hk).trans hj⟩

/-- Off-diagonal entries of the Metropolis transition are positive when the target is positive
and the proposal is positive off the diagonal. -/
theorem metropolisTransition_pos_of_ne {s : ℕ} (π : Fin s → ℝ)
    (q : Matrix (Fin s) (Fin s) ℝ) (hπ : ∀ x, 0 < π x)
    (hirr : ∀ x y, x ≠ y → 0 < q x y) (x y : Fin s) (hxy : x ≠ y) :
    0 < metropolisTransition π q x y := by
  have hacc : 0 < metropolisAcceptance π q x y := by
    unfold metropolisAcceptance
    split_ifs with h0
    · exact one_pos
    · exact lt_min one_pos (div_pos (mul_pos (hπ y) (hirr y x (Ne.symm hxy)))
        (mul_pos (hπ x) (hirr x y hxy)))
  simp only [metropolisTransition, hxy, ↓reduceIte, add_zero]
  exact mul_pos (hirr x y hxy) hacc

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
  set P := metropolisTransition π q with hPdef
  obtain ⟨hP0, hP1, -, hPst⟩ :=
    metropolisTransition_stochastic_and_detailed_balance π q hπ hq hq1
  have hoff : ∀ x y, x ≠ y → 0 < P x y := metropolisTransition_pos_of_ne π q hπ hirr
  have hstep : ∀ n : ℕ, ∀ path : ℕ → Fin s,
      μ.real {ω | ∀ i ≤ n + 1, X i ω = path i} =
        μ.real {ω | ∀ i ≤ n, X i ω = path i} * P (path n) (path (n + 1)) := by
    intro n path
    rw [hlaw, hlaw, Finset.prod_range_succ, mul_assoc]
  set m := ∑ x, π x * h x with hm
  set g : Fin s → ℝ := fun x ↦ h x - m with hg
  have hgc : ∑ x, π x * g x = 0 := by
    simp only [hg, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ1, one_mul, hm,
      sub_self]
  obtain ⟨u, hu⟩ := exists_sub_mulVec_eq_of_offDiag_pos π P hπ hπ1 hP0 hP1 hPst hoff g hgc
  set U := ∑ y, |u y| with hU
  have hu_le (y : Fin s) : |u y| ≤ U :=
    Finset.single_le_sum (f := fun y ↦ |u y|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ y)
  have hPu_le (x : Fin s) : |Matrix.mulVec P u x| ≤ U := by
    calc |Matrix.mulVec P u x| = |∑ y, P x y * u y| := rfl
      _ ≤ ∑ y, P x y * U := (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun y _ ↦ by
            rw [abs_mul, abs_of_nonneg (hP0 x y)]
            exact mul_le_mul_of_nonneg_left (hu_le y) (hP0 x y))
      _ = U := by rw [← Finset.sum_mul, hP1, one_mul]
  have hB (x y : Fin s) : |u y - Matrix.mulVec P u x| ≤ 2 * U :=
    (abs_sub _ _).trans (by linarith [hu_le y, hPu_le x])
  set M : ℕ → Ω → ℝ := fun n ω ↦
    ∑ i ∈ Finset.range n, (u (X (i + 1) ω) - Matrix.mulVec P u (X i ω)) with hMdef
  set S : ℕ → Ω → ℝ := fun n ω ↦ ∑ i ∈ Finset.range n, (h (X i ω) - m) with hSdef
  have hSM (n : ℕ) (ω : Ω) : S n ω = M n ω + (u (X 0 ω) - u (X n ω)) := by
    have hi (i : ℕ) : h (X i ω) - m = (u (X i ω) - u (X (i + 1) ω)) +
        (u (X (i + 1) ω) - Matrix.mulVec P u (X i ω)) := by
      have := hu (X i ω)
      simp only [hg] at this
      linarith
    simp only [hSdef, hMdef]
    simp_rw [hi, Finset.sum_add_distrib, Finset.sum_range_sub']
    ring
  have hmeasM (n : ℕ) : Measurable (M n) :=
    Finset.measurable_sum _ fun i _ ↦
      ((measurable_of_finite u).comp (hX _)).sub
        ((measurable_of_finite (Matrix.mulVec P u)).comp (hX _))
  have hMb (n : ℕ) (ω : Ω) : |M n ω| ≤ n * (2 * U) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) ↦ hB (X i ω) (X (i + 1) ω)
  have hc (n : ℕ) (ω : Ω) : |u (X 0 ω) - u (X n ω)| ≤ 2 * U :=
    (abs_sub _ _).trans (by linarith [hu_le (X 0 ω), hu_le (X n ω)])
  have hintM2 (n : ℕ) : Integrable (fun ω ↦ M n ω ^ 2) μ :=
    Integrable.of_bound ((hmeasM n).pow_const 2).aestronglyMeasurable ((n * (2 * U)) ^ 2)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hMb n ω) 2)
  have hintS2 (n : ℕ) : Integrable (fun ω ↦ S n ω ^ 2) μ := by
    have hmeas : Measurable (S n) :=
      Finset.measurable_sum _ fun i _ ↦ ((measurable_of_finite h).comp (hX _)).sub_const m
    refine Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable
      ((n * (2 * U) + 2 * U) ^ 2) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow, hSM]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans
      (add_le_add (hMb n ω) (hc n ω))) 2
  have hC (n : ℕ) : ∫ ω, S n ω ^ 2 ∂μ ≤ (4 * (2 * U) ^ 2) * n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hSdef]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc ∫ ω, S n ω ^ 2 ∂μ ≤ ∫ ω, (2 * M n ω ^ 2 + 2 * (2 * U) ^ 2) ∂μ := by
          refine integral_mono (hintS2 n) (((hintM2 n).const_mul 2).add (integrable_const _))
            fun ω ↦ ?_
          have hcω := hc n ω
          have hc2 : (u (X 0 ω) - u (X n ω)) ^ 2 ≤ (2 * U) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcω 2
          simp only
          rw [hSM]
          nlinarith [sq_nonneg (M n ω - (u (X 0 ω) - u (X n ω)))]
      _ = 2 * ∫ ω, M n ω ^ 2 ∂μ + 2 * (2 * U) ^ 2 := by
          rw [integral_add ((hintM2 n).const_mul 2) (integrable_const _), integral_const_mul]
          simp
      _ ≤ 2 * (n * (2 * U) ^ 2) + 2 * (2 * U) ^ 2 := by
          have := integral_sq_sum_markovIncrement_le μ P X hX hstep u (2 * U) hB n
          linarith
      _ ≤ (4 * (2 * U) ^ 2) * n := by nlinarith [sq_nonneg (2 * U)]
  have hae := ae_tendsto_div_sq_of_integral_sq_le μ S hintS2 _ hC
  filter_upwards [hae] with ω hω
  have hH (i : ℕ) : |h (X i ω)| ≤ ∑ x, |h x| :=
    Finset.single_le_sum (f := fun x ↦ |h x|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)
  have := tendsto_avg_of_tendsto_sum_sq_div (a := fun i ↦ h (X i ω)) (l := m) hH hω
  simpa [sampleAverage, smul_eq_mul] using this

end CKSD
