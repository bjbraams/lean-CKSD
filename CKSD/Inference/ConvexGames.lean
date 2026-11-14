module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Field


/-!
# Saddle points for compact convex finite games

Minimizing the largest coordinate of a compact convex set of risk vectors and separating the
strict lower orthant gives a probability vector that supports the risk set at a minimax point.
The supporting vector is a least-favourable prior for the corresponding statistical game.

The proof uses Mathlib's compact extreme-value theorem and
`geometric_hahn_banach_open` for real finite-dimensional separation.
-/

@[expose] public section

noncomputable section
open Set
open scoped BigOperators
namespace CKSD

/-- A compact convex family of finite risk vectors has a least-favourable probability vector
and a risk vector forming a saddle point for weighted risk. -/
theorem exists_compact_convex_game_saddle_point {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    {C : Set (Θ → ℝ)} (hC : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) :
    ∃ y ∈ C, ∃ w : Θ → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ z ∈ C, (∑ i, w i * y i) ≤ ∑ i, w i * z i) ∧
      (∀ i, y i ≤ ∑ j, w j * y j) := by
  classical
  let M : (Θ → ℝ) → ℝ := fun z ↦ Finset.univ.sup' Finset.univ_nonempty z
  have hM : Continuous M := Continuous.finset_sup'_apply _ (fun i _ ↦ continuous_apply i)
  obtain ⟨y, hy, hmin⟩ := hC.exists_isMinOn hne hM.continuousOn
  let t := M y
  let S : Set (Θ → ℝ) := Set.pi Set.univ (fun _ ↦ Iio t)
  have hSconv : Convex ℝ S := convex_pi (fun _ _ ↦ convex_Iio t)
  have hSopen : IsOpen S := isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Iio)
  have hdisj : Disjoint S C := by
    refine Set.disjoint_left.2 fun z hz hzC ↦ ?_
    have hlt : M z < t := (Finset.sup'_lt_iff _).2 (fun i _ ↦ hz i (mem_univ _))
    exact hlt.not_ge (hmin hzC)
  obtain ⟨f, u, hfS, hfC⟩ := geometric_hahn_banach_open hSconv hSopen hconv hdisj
  let a : Θ → ℝ := fun i ↦ f (Pi.single i 1)
  have hf_apply (z : Θ → ℝ) : f z = ∑ i, a i * z i := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : Pi.single i (z i) = (z i) • (Pi.single i (1 : ℝ)) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [heq, map_smul]
    change z i * a i = a i * z i
    ring
  have hconst (r : ℝ) : f (fun _ ↦ r) = r * ∑ i, a i := by
    rw [hf_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let q : Θ → ℝ := fun _ ↦ t - 1
  have hq : q ∈ S := fun i _ ↦ by change t - 1 < t; linarith
  have haq : f q < u := hfS q hq
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hneg
    have hai : a i < 0 := lt_of_not_ge hneg
    let c := (u - f q + 1) / a i
    have hc : c ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hai.le
    have hzS : q + c • Pi.single i 1 ∈ S := by
      intro j _
      change q j + c * (Pi.single i (1 : ℝ) : Θ → ℝ) j < t
      by_cases hj : j = i
      · subst j; simp only [Pi.single_eq_same]; dsimp [q]; linarith
      · simp only [Pi.single_eq_of_ne hj, mul_zero, add_zero]
        exact hq j (mem_univ _)
    have hbad := hfS _ hzS
    rw [map_add, map_smul] at hbad
    change f q + c * a i < u at hbad
    dsimp [c] at hbad
    rw [div_mul_cancel₀ _ hai.ne] at hbad
    linarith
  let A := ∑ i, a i
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ ha i
  have hA : 0 < A := by
    by_contra hn
    have hAz : A = 0 := le_antisymm (le_of_not_gt hn) hA0
    have haz : ∀ i, a i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ ha i).1 hAz
      exact fun i ↦ this i (Finset.mem_univ i)
    have hf0 (z : Θ → ℝ) : f z = 0 := by rw [hf_apply]; simp [haz]
    have hcy := hfC y hy
    rw [hf0 q] at haq
    rw [hf0 y] at hcy
    linarith
  have htu : t * A ≤ u := by
    by_contra hnot
    have hlt : u < t * A := lt_of_not_ge hnot
    let r := (u / A + t) / 2
    have hdiv : u / A < t := (div_lt_iff₀ hA).2 hlt
    have hr : r < t := by dsimp [r]; linarith
    have hrS : (fun _ : Θ ↦ r) ∈ S := fun _ _ ↦ hr
    have hbad := hfS _ hrS
    rw [hconst] at hbad
    have hcross : (u / A) * A = u := div_mul_cancel₀ _ hA.ne'
    dsimp [r] at hbad
    nlinarith
  have hybound (i : Θ) : y i ≤ t := Finset.le_sup' _ (Finset.mem_univ i)
  have hfyt : f y = t * A := by
    apply le_antisymm
    · rw [hf_apply]
      calc ∑ i, a i * y i ≤ ∑ i, a i * t :=
            Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hybound i) (ha i)
        _ = t * A := by rw [← Finset.sum_mul]; ring
    · exact htu.trans (hfC y hy)
  refine ⟨y, hy, (fun i ↦ a i / A), (fun i ↦ div_nonneg (ha i) hA.le), ?_, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hA.ne'
  · intro z hz
    have hfyfz : f y ≤ f z := hfyt.le.trans (htu.trans (hfC z hz))
    have hrep (v : Θ → ℝ) : (∑ i, a i / A * v i) = f v / A := by
      rw [hf_apply, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hrep, hrep]
    exact div_le_div_of_nonneg_right hfyfz hA.le
  · intro i
    have heq : (∑ j, a j / A * y j) = t := by
      calc _ = (∑ j, a j * y j) / A := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = f y / A := by rw [hf_apply]
        _ = t := by rw [hfyt, mul_div_cancel_right₀ _ hA.ne']
    rw [heq]
    exact hybound i

end CKSD
