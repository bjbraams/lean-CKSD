module

public import CKSD.Geometry.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Semidiscrete optimal transport

For a law `P` on `ℝ^d` and a discrete target with masses `b_j` at sites `y_j`, the semidiscrete
dual functional is `E(g) = ∫ φ_g dP + ∑ b_j g_j` with the potential
`φ_g(x) = min_j (‖x - y_j‖² - g_j)` (`CKSD.semidiscreteTransportDual`). This file develops its
first-order theory: `φ_g(x)` is `1`-Lipschitz in `g` for the sup norm, the ties between two sites
lie on affine hyperplanes and so are null for an absolutely continuous `P`, and off the ties
`g ↦ φ_g(x)` is locally affine. Dominated differentiation then gives the gradient
`b_j - P(L_j(g))` in terms of the Laguerre cells `L_j(g)` (`CKSD.laguerreCell`), and dominated
convergence its continuity. The functional is concave, invariant under adding a constant to `g`,
and tends to `-∞` on the normalized slice `g_0 = 0`, so it attains its maximum; the maximizers
are the weights whose cells have masses `b_j`. At a maximizer the cell map `x ↦ y_j` on `L_j(g)`
is a transport map of cost `E(g)`, and integrating `‖x - y‖² ≥ φ_g(x) + g(y)` against any
coupling shows that this cost is the squared Wasserstein distance.

## Main definitions

* `CKSD.semidiscretePotential`: the potential `φ_g`.
* `CKSD.semidiscreteTransportMap`: the map sending each Laguerre cell `L_j(g)` to `y_j`.

## Main results

* `CKSD.hasFDerivAt_semidiscreteTransportDual`: the gradient formula.
* `CKSD.contDiff_semidiscreteTransportDual`: the dual functional is `C¹`.
* `CKSD.concaveOn_semidiscreteTransportDual`: concavity.
* `CKSD.semidiscreteTransportDual_isMax_iff`: maximizers are the weights with cell masses `b_j`.
* `CKSD.exists_isMax_semidiscreteTransportDual`: a maximizer exists.
* `CKSD.map_semidiscreteTransportMap`: at a maximizer the cell map transports `P` to the target.
* `CKSD.semidiscreteTransportDual_eq_wassersteinEDist_sq`: the maximal value is `W₂²`.

## References

* F. Aurenhammer, F. Hoffmann and B. Aronov, *Minkowski-type theorems and least-squares
  clustering*, Algorithmica 20 (1998).
* Q. Mérigot and B. Thibert, *Optimal transport: discretization and algorithms*, Handbook of
  Numerical Analysis 22 (2021), §4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

attribute [local instance] Classical.propDecidable

variable {d k : ℕ}

/-- The semidiscrete potential `φ_g(x) = min_j (‖x - y_j‖² - g_j)`, the integrand of
`CKSD.semidiscreteTransportDual`. -/
def semidiscretePotential (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf (range fun j ↦ ‖x - y j‖ ^ 2 - g j)

/-- The dual functional is the integral of the potential plus the linear term. -/
theorem semidiscreteTransportDual_eq (P : Measure (EuclideanSpace ℝ (Fin d)))
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (b g : Fin k → ℝ) :
    semidiscreteTransportDual P y b g =
      (∫ x, semidiscretePotential y g x ∂P) + ∑ j, b j * g j := rfl

/-- The potential is at most each of the shifted costs. -/
theorem semidiscretePotential_le (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin k) :
    semidiscretePotential y g x ≤ ‖x - y j‖ ^ 2 - g j :=
  csInf_le (Set.finite_range _).bddBelow (mem_range_self j)

/-- For at least one site the potential is attained. -/
theorem exists_semidiscretePotential_eq (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ j, semidiscretePotential y g x = ‖x - y j‖ ^ 2 - g j := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨j, hj⟩ := (Set.range_nonempty _).csInf_mem (Set.finite_range
    fun j ↦ ‖x - y j‖ ^ 2 - g j)
  exact ⟨j, hj.symm⟩

/-- A point lies in the Laguerre cell of `y_j` exactly when the potential is attained at `j`. -/
theorem mem_laguerreCell_iff (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin k) :
    x ∈ laguerreCell y g j ↔ semidiscretePotential y g x = ‖x - y j‖ ^ 2 - g j := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  constructor
  · intro hx
    refine le_antisymm (semidiscretePotential_le y g x j) (le_csInf (range_nonempty _) ?_)
    rintro _ ⟨i, rfl⟩
    exact hx i
  · intro hx i
    rw [← hx]
    exact semidiscretePotential_le y g x i

/-- Every point lies in some Laguerre cell. -/
theorem exists_mem_laguerreCell (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ∃ j, x ∈ laguerreCell y g j := by
  obtain ⟨j, hj⟩ := exists_semidiscretePotential_eq hk y g x
  exact ⟨j, (mem_laguerreCell_iff hk y g x j).mpr hj⟩

/-- The potential is `1`-Lipschitz in the weights for the sup norm. -/
theorem abs_semidiscretePotential_sub_le (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g h : Fin k → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    |semidiscretePotential y g x - semidiscretePotential y h x| ≤ ‖g - h‖ := by
  have key : ∀ g h : Fin k → ℝ,
      semidiscretePotential y g x ≤ semidiscretePotential y h x + ‖g - h‖ := by
    intro g h
    obtain ⟨j, hj⟩ := exists_semidiscretePotential_eq hk y h x
    have h1 := semidiscretePotential_le y g x j
    have h2 : |g j - h j| ≤ ‖g - h‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (g - h) j
    rw [hj]
    linarith [le_abs_self (h j - g j), abs_sub_comm (g j) (h j)]
  rw [abs_le]
  constructor
  · have := key h g
    rw [norm_sub_rev] at this
    linarith
  · linarith [key g h]

/-- The potential is measurable in the point. -/
theorem measurable_semidiscretePotential (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) : Measurable (semidiscretePotential y g) :=
  Measurable.iInf fun j ↦ by fun_prop

/-- The potential is bounded below by `-‖g‖`. -/
theorem neg_norm_le_semidiscretePotential (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (x : EuclideanSpace ℝ (Fin d)) : -‖g‖ ≤ semidiscretePotential y g x := by
  obtain ⟨j, hj⟩ := exists_semidiscretePotential_eq hk y g x
  rw [hj]
  have h1 : g j ≤ ‖g‖ := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j)
  have h2 := sq_nonneg ‖x - y j‖
  linarith

/-- For a law with finite second moment, the squared distance to a site is integrable. -/
theorem integrable_norm_sub_sq {P : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure P]
    (h2 : MemLp id 2 P) (z : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x ↦ ‖x - z‖ ^ 2) P := by
  have : MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x - z) 2 P := h2.sub (memLp_const z)
  exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp this

/-- For a law with finite second moment, the potential is integrable. -/
theorem integrable_semidiscretePotential (hk : 0 < k) {P : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure P] (h2 : MemLp id 2 P) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) : Integrable (semidiscretePotential y g) P := by
  set j₀ : Fin k := ⟨0, hk⟩
  refine ((integrable_norm_sub_sq h2 (y j₀)).add (integrable_const (2 * ‖g‖))).mono'
    (measurable_semidiscretePotential y g).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have h1 := semidiscretePotential_le y g x j₀
  have h3 := neg_norm_le_semidiscretePotential hk y g x
  have h4 : -g j₀ ≤ ‖g‖ := (neg_le_abs _).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j₀)
  rw [Real.norm_eq_abs, abs_le, Pi.add_apply]
  constructor <;> nlinarith [norm_nonneg g, sq_nonneg ‖x - y j₀‖]

/-- The cost difference of two sites is affine:
`‖x - a‖² - ‖x - c‖² = 2 ⟨x, c - a⟩ + ‖a‖² - ‖c‖²`. -/
theorem norm_sub_sq_sub_norm_sub_sq (x a c : EuclideanSpace ℝ (Fin d)) :
    ‖x - a‖ ^ 2 - ‖x - c‖ ^ 2 = 2 * inner ℝ x (c - a) + ‖a‖ ^ 2 - ‖c‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
  ring

/-- Two distinct sites tie on an affine hyperplane, which is Lebesgue-null. -/
private theorem volume_tie_eq_zero (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    {i j : Fin k} (hij : y i ≠ y j) :
    volume {x : EuclideanSpace ℝ (Fin d) | ‖x - y i‖ ^ 2 - g i = ‖x - y j‖ ^ 2 - g j} = 0 := by
  set w := y j - y i with hwdef
  have hw : w ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  set S := {x : EuclideanSpace ℝ (Fin d) | ‖x - y i‖ ^ 2 - g i = ‖x - y j‖ ^ 2 - g j}
  rcases S.eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · rw [h, measure_empty]
  let A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) :=
    AffineSubspace.mk' x0 (LinearMap.ker (innerₛₗ ℝ w))
  have hlin : ∀ x ∈ S, 2 * inner ℝ x w = ‖y j‖ ^ 2 - ‖y i‖ ^ 2 + g i - g j := by
    intro x hx
    have h1 := norm_sub_sq_sub_norm_sub_sq x (y i) (y j)
    simp only [S, mem_ofPred_eq] at hx
    linarith
  have hsub : S ⊆ A := by
    intro x hx
    change x ∈ AffineSubspace.mk' x0 (LinearMap.ker (innerₛₗ ℝ w))
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, innerₛₗ_apply_apply, vsub_eq_sub,
      real_inner_comm, inner_sub_left]
    linarith [hlin x hx, hlin x0 hx0]
  have hA : A ≠ ⊤ := by
    intro h
    have hmem : w ∈ A.direction := by rw [h, AffineSubspace.direction_top]; trivial
    rw [AffineSubspace.direction_mk', LinearMap.mem_ker, innerₛₗ_apply_apply,
      real_inner_self_eq_norm_sq] at hmem
    exact hw (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hmem))
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume A hA)

/-- For an absolutely continuous law and distinct sites, almost every point has no ties. -/
theorem ae_forall_ne_of_absolutelyContinuous {P : Measure (EuclideanSpace ℝ (Fin d))}
    (hP : P ≪ volume) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (g : Fin k → ℝ) :
    ∀ᵐ x ∂P, ∀ i j, i ≠ j → ‖x - y i‖ ^ 2 - g i ≠ ‖x - y j‖ ^ 2 - g j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact ae_of_all _ fun x h ↦ absurd hij h
  · refine measure_mono_null (fun x hx ↦ ?_) (hP (volume_tie_eq_zero y g (hy.ne hij)))
    by_contra hne
    exact hx fun _ ↦ hne

/-- Laguerre cells are closed. -/
theorem isClosed_laguerreCell (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    (j : Fin k) : IsClosed (laguerreCell y g j) := by
  have : laguerreCell y g j = ⋂ i, {x | ‖x - y j‖ ^ 2 - g j ≤ ‖x - y i‖ ^ 2 - g i} := by
    ext x; simp [laguerreCell]
  rw [this]
  exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) (by fun_prop)

/-- Laguerre cells are measurable. -/
theorem measurableSet_laguerreCell (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    (j : Fin k) : MeasurableSet (laguerreCell y g j) :=
  (isClosed_laguerreCell y g j).measurableSet

/-- A point of a Laguerre cell with no ties stays in the cell for all nearby weights. -/
theorem eventually_mem_laguerreCell {y : Fin k → EuclideanSpace ℝ (Fin d)} {g₀ : Fin k → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} {j : Fin k} (hj : x ∈ laguerreCell y g₀ j)
    (huniq : ∀ i, i ≠ j → ‖x - y i‖ ^ 2 - g₀ i ≠ ‖x - y j‖ ^ 2 - g₀ j) :
    ∀ᶠ g in 𝓝 g₀, x ∈ laguerreCell y g j := by
  have h : ∀ i, ∀ᶠ g in 𝓝 g₀, ‖x - y j‖ ^ 2 - g j ≤ ‖x - y i‖ ^ 2 - g i := by
    intro i
    by_cases hij : i = j
    · subst hij; exact Eventually.of_forall fun _ ↦ le_rfl
    · have hlt : ‖x - y j‖ ^ 2 - g₀ j < ‖x - y i‖ ^ 2 - g₀ i :=
        lt_of_le_of_ne (hj i) (huniq i hij).symm
      have hc : ∀ l : Fin k, Continuous fun g : Fin k → ℝ ↦ ‖x - y l‖ ^ 2 - g l := fun l ↦
        continuous_const.sub (continuous_apply l)
      exact ((hc j).continuousAt.eventually_lt (hc i).continuousAt hlt).mono fun _ h ↦ h.le
  exact (eventually_all.mpr h).mono fun g hg ↦ hg

/-- A point outside a Laguerre cell stays outside for all nearby weights. -/
theorem eventually_notMem_laguerreCell {y : Fin k → EuclideanSpace ℝ (Fin d)} {g₀ : Fin k → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} {j : Fin k} (hj : x ∉ laguerreCell y g₀ j) :
    ∀ᶠ g in 𝓝 g₀, x ∉ laguerreCell y g j := by
  simp only [laguerreCell, mem_ofPred_eq, not_forall, not_le] at hj
  obtain ⟨i, hi⟩ := hj
  have hc : ∀ l : Fin k, Continuous fun g : Fin k → ℝ ↦ ‖x - y l‖ ^ 2 - g l := fun l ↦
    continuous_const.sub (continuous_apply l)
  filter_upwards [(hc i).continuousAt.eventually_lt (hc j).continuousAt hi] with g hg hmem
  exact absurd (hmem i) (not_le.mpr hg)

/-- Off the ties, the potential is differentiable in the weights, with derivative `-e_j` on the
cell of `y_j`. -/
theorem hasFDerivAt_semidiscretePotential (hk : 0 < k) {y : Fin k → EuclideanSpace ℝ (Fin d)}
    {g₀ : Fin k → ℝ} {x : EuclideanSpace ℝ (Fin d)} {j : Fin k} (hj : x ∈ laguerreCell y g₀ j)
    (huniq : ∀ i, i ≠ j → ‖x - y i‖ ^ 2 - g₀ i ≠ ‖x - y j‖ ^ 2 - g₀ j) :
    HasFDerivAt (fun g ↦ semidiscretePotential y g x)
      (-(ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) g₀ := by
  have h : HasFDerivAt (fun g : Fin k → ℝ ↦ ‖x - y j‖ ^ 2 - g j)
      (-(ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) g₀ := by
    have h0 := (hasFDerivAt_const (‖x - y j‖ ^ 2) g₀).sub
      (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ).hasFDerivAt
    rw [zero_sub] at h0
    exact h0
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_mem_laguerreCell hj huniq] with g hg
  exact (mem_laguerreCell_iff hk y g x j).mp hg

/-- At a point without ties, the indicator of the Laguerre cell of `y_j` is the Kronecker delta of
the unique minimizing site. -/
theorem indicator_laguerreCell_eq {y : Fin k → EuclideanSpace ℝ (Fin d)} {g : Fin k → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} {j : Fin k} (hj : x ∈ laguerreCell y g j)
    (huniq : ∀ i l, i ≠ l → ‖x - y i‖ ^ 2 - g i ≠ ‖x - y l‖ ^ 2 - g l) (i : Fin k) :
    (laguerreCell y g i).indicator (fun _ ↦ (1 : ℝ)) x = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij; simp [hj]
  · have : x ∉ laguerreCell y g i := fun hi ↦
      huniq i j hij (le_antisymm (hi j) (hj i))
    simp [this, hij]

/-- GAPS 108.56, differentiation under the integral: for an absolutely continuous law with finite
second moment and distinct sites, `g ↦ ∫ φ_g dP` has derivative `-∑ P(L_j(g)) e_j`. -/
theorem hasFDerivAt_integral_semidiscretePotential (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (g₀ : Fin k → ℝ) :
    HasFDerivAt (fun g ↦ ∫ x, semidiscretePotential y g x ∂P)
      (-∑ j, P.real (laguerreCell y g₀ j) •
        (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) g₀ := by
  set F' : EuclideanSpace ℝ (Fin d) → (Fin k → ℝ) →L[ℝ] ℝ := fun x ↦
    -∑ j, (laguerreCell y g₀ j).indicator (fun _ ↦ (1 : ℝ)) x •
      (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ) with hF'
  have hind : ∀ j, Integrable ((laguerreCell y g₀ j).indicator fun _ ↦ (1 : ℝ)) P := fun j ↦
    (integrable_const (1 : ℝ)).indicator (measurableSet_laguerreCell y g₀ j)
  have hF'int : ∫ x, F' x ∂P = -∑ j, P.real (laguerreCell y g₀ j) •
      (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ) := by
    rw [hF', integral_neg, integral_finsetSum _ fun j _ ↦ (hind j).smul_const _]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul_const, integral_indicator_const _ (measurableSet_laguerreCell y g₀ j),
      smul_eq_mul, mul_one]
  have hF'meas : AEStronglyMeasurable F' P := by
    refine (Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦ ?_).neg
    exact ((hind j).aestronglyMeasurable).smul_const _
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := P)
    (F := fun g x ↦ semidiscretePotential y g x) (F' := F') (x₀ := g₀)
    (bound := fun _ ↦ (1 : ℝ)) univ_mem
    (fun g _ ↦ (measurable_semidiscretePotential y g).aestronglyMeasurable)
    (integrable_semidiscretePotential hk h2 y g₀) hF'meas
    (ae_of_all _ fun x g _ ↦ by
      rw [one_mul, Real.norm_eq_abs]; exact abs_semidiscretePotential_sub_le hk y g g₀ x)
    (integrable_const _) ?_
  · rw [← hF'int]; exact key.2
  filter_upwards [ae_forall_ne_of_absolutelyContinuous hP hy g₀] with x hx
  obtain ⟨j, hj⟩ := exists_mem_laguerreCell hk y g₀ x
  have hF'x : F' x = -(ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ) := by
    simp only [hF', indicator_laguerreCell_eq hj hx, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hF'x]
  exact hasFDerivAt_semidiscretePotential hk hj fun i hi ↦ hx i j hi

/-- The mass of a Laguerre cell depends continuously on the weights, for an absolutely continuous
law and distinct sites. -/
theorem continuous_measureReal_laguerreCell {P : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure P] (hP : P ≪ volume) {y : Fin k → EuclideanSpace ℝ (Fin d)}
    (hy : Function.Injective y) (j : Fin k) :
    Continuous fun g ↦ P.real (laguerreCell y g j) := by
  have heq : (fun g ↦ P.real (laguerreCell y g j)) =
      fun g ↦ ∫ x, (laguerreCell y g j).indicator (fun _ ↦ (1 : ℝ)) x ∂P := by
    funext g
    rw [integral_indicator_const _ (measurableSet_laguerreCell y g j), smul_eq_mul, mul_one]
  rw [heq, continuous_iff_continuousAt]
  intro g₀
  refine continuousAt_of_dominated (bound := fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun g ↦ ((integrable_const (1 : ℝ)).indicator
      (measurableSet_laguerreCell y g j)).aestronglyMeasurable)
    (Eventually.of_forall fun g ↦ ae_of_all _ fun x ↦ ?_) (integrable_const _) ?_
  · rw [Real.norm_eq_abs]
    by_cases hx : x ∈ laguerreCell y g j <;> simp [hx]
  filter_upwards [ae_forall_ne_of_absolutelyContinuous hP hy g₀] with x hx
  by_cases hxj : x ∈ laguerreCell y g₀ j
  · refine (continuousAt_const (y := (1 : ℝ))).congr ?_
    filter_upwards [eventually_mem_laguerreCell hxj fun i hi ↦ hx i j hi] with g hg
    simp [hg]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [eventually_notMem_laguerreCell hxj] with g hg
    simp [hg]

/-- GAPS 108.56, the gradient formula: the dual functional has derivative
`∑ (b_j - P(L_j(g))) e_j`. -/
theorem hasFDerivAt_semidiscreteTransportDual (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (b g : Fin k → ℝ) :
    HasFDerivAt (semidiscreteTransportDual P y b)
      (∑ j, (b j - P.real (laguerreCell y g j)) •
        (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)) g := by
  set L : (Fin k → ℝ) →L[ℝ] ℝ :=
    ∑ j, b j • (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)
  have hL : ∀ h, L h = ∑ j, b j * h j := fun h ↦ by simp [L]
  have h := (hasFDerivAt_integral_semidiscretePotential hk hP h2 hy g).add L.hasFDerivAt
  have hfun : ((fun g ↦ ∫ x, semidiscretePotential y g x ∂P) + ⇑L) =
      semidiscreteTransportDual P y b := by
    funext g; rw [Pi.add_apply, hL]; rfl
  rw [hfun] at h
  have e : ∑ j, (b j - P.real (laguerreCell y g j)) •
      (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ) =
      -∑ j, P.real (laguerreCell y g j) • (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ)
        + L := by
    ext v
    simp only [L, add_apply, neg_apply,
      FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [e]
  exact h

/-- GAPS 108.56: the dual functional is continuously differentiable. -/
theorem contDiff_semidiscreteTransportDual (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (b : Fin k → ℝ) : ContDiff ℝ 1 (semidiscreteTransportDual P y b) := by
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨_, ?_,
    hasFDerivAt_semidiscreteTransportDual hk hP h2 hy b⟩
  refine continuous_finsetSum _ fun j _ ↦ ?_
  exact (continuous_const.sub (continuous_measureReal_laguerreCell hP hy j)).smul
    continuous_const

/-- GAPS 108.56: the dual functional is concave. -/
theorem concaveOn_semidiscreteTransportDual (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (h2 : MemLp id 2 P)
    (y : Fin k → EuclideanSpace ℝ (Fin d)) (b : Fin k → ℝ) :
    ConcaveOn ℝ univ (semidiscreteTransportDual P y b) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine ⟨convex_univ, fun g _ h _ a c ha hc hac ↦ ?_⟩
  have hpt : ∀ x, a * semidiscretePotential y g x + c * semidiscretePotential y h x ≤
      semidiscretePotential y (a • g + c • h) x := fun x ↦ by
    refine le_csInf (range_nonempty _) ?_
    rintro _ ⟨j, rfl⟩
    have h1 := semidiscretePotential_le y g x j
    have h2 := semidiscretePotential_le y h x j
    have e : ‖x - y j‖ ^ 2 - (a • g + c • h) j =
        a * (‖x - y j‖ ^ 2 - g j) + c * (‖x - y j‖ ^ 2 - h j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(‖x - y j‖ ^ 2)) * hac
    show _ ≤ ‖x - y j‖ ^ 2 - (a • g + c • h) j
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hc)
  have hint := fun g ↦ integrable_semidiscretePotential hk h2 y g
  simp only [semidiscreteTransportDual_eq, smul_eq_mul]
  have hI : a * (∫ x, semidiscretePotential y g x ∂P) + c * ∫ x, semidiscretePotential y h x ∂P
      ≤ ∫ x, semidiscretePotential y (a • g + c • h) x ∂P := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hint g).const_mul a)
      ((hint h).const_mul c)]
    exact integral_mono (((hint g).const_mul a).add ((hint h).const_mul c)) (hint _) hpt
  have hlin : ∑ j, b j * (a • g + c • h) j = a * ∑ j, b j * g j + c * ∑ j, b j * h j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlin]
  linarith

/-- A concave function with vanishing derivative at `g` attains its global maximum at `g`. -/
private theorem ConcaveOn.le_of_hasFDerivAt_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : F → ℝ} (hf : ConcaveOn ℝ univ f) {g : F}
    (hg : HasFDerivAt f (0 : F →L[ℝ] ℝ) g) (h : F) : f h ≤ f g := by
  set ℓ : ℝ → ℝ := fun t ↦ f (g + t • (h - g))
  have hℓ : HasDerivAt ℓ 0 0 := by
    have hin : HasDerivAt (fun t : ℝ ↦ g + t • (h - g)) (h - g) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (h - g)).const_add g
    have hg' : HasFDerivAt f (0 : F →L[ℝ] ℝ) (g + (0 : ℝ) • (h - g)) := by simpa using hg
    have := hg'.comp_hasDerivAt (0 : ℝ) hin
    rw [zero_apply] at this
    exact this
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hℓ).mono_left
    (nhdsWithin_mono _ fun t (ht : t ∈ Ioi (0 : ℝ)) ↦
      Set.mem_compl_singleton_iff.mpr (ne_of_gt ht))
  refine sub_nonpos.mp (ge_of_tendsto hslope ?_)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hconc := hf.2 (mem_univ g) (mem_univ h) (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)
    ht.1.le (by ring)
  have e : (1 - t) • g + t • h = g + t • (h - g) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [e, smul_eq_mul, smul_eq_mul] at hconc
  rw [slope_def_field, sub_zero]
  simp only [ℓ, zero_smul, add_zero]
  rw [le_div_iff₀ ht.1]
  linarith

/-- Adding a constant to all weights lowers the potential by that constant. -/
theorem semidiscretePotential_add_const (hk : 0 < k) (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    semidiscretePotential y (fun j ↦ g j + c) x = semidiscretePotential y g x - c := by
  obtain ⟨j, hj⟩ := exists_semidiscretePotential_eq hk y g x
  obtain ⟨i, hi⟩ := exists_semidiscretePotential_eq hk y (fun j ↦ g j + c) x
  refine le_antisymm ?_ ?_
  · have := semidiscretePotential_le y (fun j ↦ g j + c) x j
    rw [hj]; linarith
  · have := semidiscretePotential_le y g x i
    rw [hi]; linarith

/-- For target masses summing to one, the dual functional is invariant under adding a constant to
the weights. -/
theorem semidiscreteTransportDual_add_const (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (h2 : MemLp id 2 P)
    (y : Fin k → EuclideanSpace ℝ (Fin d)) {b : Fin k → ℝ} (hb1 : ∑ j, b j = 1)
    (g : Fin k → ℝ) (c : ℝ) :
    semidiscreteTransportDual P y b (fun j ↦ g j + c) = semidiscreteTransportDual P y b g := by
  simp only [semidiscreteTransportDual_eq, semidiscretePotential_add_const hk]
  rw [integral_sub (integrable_semidiscretePotential hk h2 y g) (integrable_const c),
    integral_const, probReal_univ, one_smul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hb1, one_mul]
  ring

/-- An upper bound for the dual functional: with `C = ∑ⱼ ∫ ‖x - y_j‖² dP`,
`E(g) ≤ C - b_i (max g - g_i)` for every site `i`. -/
theorem semidiscreteTransportDual_le (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (h2 : MemLp id 2 P)
    (y : Fin k → EuclideanSpace ℝ (Fin d)) {b : Fin k → ℝ} (hb : ∀ j, 0 < b j)
    (hb1 : ∑ j, b j = 1) (g : Fin k → ℝ) (i j : Fin k) (hmax : ∀ l, g l ≤ g j) :
    semidiscreteTransportDual P y b g ≤
      (∑ l, ∫ x, ‖x - y l‖ ^ 2 ∂P) - b i * (g j - g i) := by
  have hint := integrable_semidiscretePotential hk h2 y g
  have h1 : ∫ x, semidiscretePotential y g x ∂P ≤ (∫ x, ‖x - y j‖ ^ 2 ∂P) - g j := by
    have hI : Integrable (fun x ↦ ‖x - y j‖ ^ 2 - g j) P :=
      (integrable_norm_sub_sq h2 (y j)).sub (integrable_const (g j))
    have := integral_mono hint hI (fun x ↦ semidiscretePotential_le y g x j)
    rwa [integral_sub (integrable_norm_sub_sq h2 (y j)) (integrable_const _), integral_const,
      probReal_univ, one_smul] at this
  have h3 : ∑ l, b l * g l - g j = ∑ l, b l * (g l - g j) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hb1, one_mul]
  have h4 : ∑ l, b l * (g l - g j) ≤ b i * (g i - g j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ l ∈ Finset.univ.erase i, b l * (g l - g j) ≤ 0 :=
      Finset.sum_nonpos fun l _ ↦ mul_nonpos_of_nonneg_of_nonpos (hb l).le
        (sub_nonpos.mpr (hmax l))
    linarith
  have h5 : ∫ x, ‖x - y j‖ ^ 2 ∂P ≤ ∑ l, ∫ x, ‖x - y l‖ ^ 2 ∂P :=
    Finset.single_le_sum (f := fun l ↦ ∫ x, ‖x - y l‖ ^ 2 ∂P)
      (fun l _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) (Finset.mem_univ j)
  rw [semidiscreteTransportDual_eq]
  linarith

/-- GAPS 108.56: the maximizers of the dual functional are exactly the weights whose Laguerre cells
have the target masses. -/
theorem semidiscreteTransportDual_isMax_iff (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (b g : Fin k → ℝ) :
    (∀ h, semidiscreteTransportDual P y b h ≤ semidiscreteTransportDual P y b g) ↔
      ∀ j, P.real (laguerreCell y g j) = b j := by
  have hD := hasFDerivAt_semidiscreteTransportDual hk hP h2 hy b g
  constructor
  · intro hmax j
    have hloc : IsLocalMax (semidiscreteTransportDual P y b) g :=
      Eventually.of_forall fun h ↦ hmax h
    have h0 := hloc.hasFDerivAt_eq_zero hD
    have := congrArg (fun L : (Fin k → ℝ) →L[ℝ] ℝ ↦ L (Pi.single j 1)) h0
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, zero_apply] at this
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by simp [hij]) (by simp)] at this
    simp only [Pi.single_eq_same, mul_one] at this
    linarith
  · intro hmass h
    have h0 : ∑ j, (b j - P.real (laguerreCell y g j)) •
        (ContinuousLinearMap.proj j : (Fin k → ℝ) →L[ℝ] ℝ) = 0 := by
      simp [hmass]
    rw [h0] at hD
    exact ConcaveOn.le_of_hasFDerivAt_eq_zero (concaveOn_semidiscreteTransportDual hk h2 y b) hD h

/-- GAPS 108.56: the dual functional attains its maximum. -/
theorem exists_isMax_semidiscreteTransportDual (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    {b : Fin k → ℝ} (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1) :
    ∃ g, ∀ h, semidiscreteTransportDual P y b h ≤ semidiscreteTransportDual P y b g := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  set E := semidiscreteTransportDual P y b
  set j₀ : Fin k := ⟨0, hk⟩
  set β := Finset.univ.inf' Finset.univ_nonempty b
  have hβ : 0 < β := (Finset.lt_inf'_iff _).mpr fun j _ ↦ hb j
  have hβle : ∀ j, β ≤ b j := fun j ↦ Finset.inf'_le _ (Finset.mem_univ j)
  set C := ∑ l, ∫ x, ‖x - y l‖ ^ 2 ∂P
  have hC : 0 ≤ C := Finset.sum_nonneg fun l _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  set R := C / β
  have hE0 : 0 ≤ E 0 := by
    simp only [E, semidiscreteTransportDual_eq, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero]
    refine integral_nonneg fun x ↦ ?_
    have := neg_norm_le_semidiscretePotential hk y 0 x
    simpa using this
  set K := {g : Fin k → ℝ | g j₀ = 0} ∩ Metric.closedBall 0 R
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_left (isClosed_eq (continuous_apply j₀) continuous_const)
  have h0K : (0 : Fin k → ℝ) ∈ K :=
    ⟨rfl, Metric.mem_closedBall_self (div_nonneg hC hβ.le)⟩
  have hEc : Continuous E := (contDiff_semidiscreteTransportDual hk hP h2 hy b).continuous
  obtain ⟨g, hgK, hgmax⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ hEc.continuousOn
  refine ⟨g, fun h ↦ ?_⟩
  set h' : Fin k → ℝ := fun j ↦ h j + -h j₀
  have hEh : E h = E h' := (semidiscreteTransportDual_add_const hk h2 y hb1 h _).symm
  rw [hEh]
  by_cases hR : ‖h'‖ ≤ R
  · exact hgmax ⟨by simp [h'], by simpa using hR⟩
  · push Not at hR
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ h' Finset.univ_nonempty
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ h' Finset.univ_nonempty
    have hup := semidiscreteTransportDual_le hk h2 y hb hb1 h' i j fun l ↦ hj l (Finset.mem_univ l)
    have hspread : ‖h'‖ ≤ h' j - h' i := by
      have h0 : h' j₀ = 0 := by simp [h']
      refine (pi_norm_le_iff_of_nonneg (by
        linarith [hj j₀ (Finset.mem_univ _), hi j₀ (Finset.mem_univ _)])).mpr fun l ↦ ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hj l (Finset.mem_univ _), hi l (Finset.mem_univ _),
        hj j₀ (Finset.mem_univ _), hi j₀ (Finset.mem_univ _)]
    have hRβ : β * R = C := by simp only [R]; field_simp
    have hlt : E h' < 0 := by
      have h3 : β * R < b i * (h' j - h' i) :=
        calc β * R < β * ‖h'‖ := mul_lt_mul_of_pos_left hR hβ
          _ ≤ β * (h' j - h' i) := mul_le_mul_of_nonneg_left hspread hβ.le
          _ ≤ b i * (h' j - h' i) := mul_le_mul_of_nonneg_right (hβle i)
              ((norm_nonneg _).trans hspread)
      linarith
    exact hlt.le.trans (hE0.trans (hgmax h0K))

/-- At a point without ties lying in the Laguerre cell of `y_j`, a sum of indicators of the cells
picks out the `j`-th value. -/
theorem sum_indicator_laguerreCell_eq {M : Type*} [AddCommMonoid M]
    {y : Fin k → EuclideanSpace ℝ (Fin d)} {g : Fin k → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    {j : Fin k} (hj : x ∈ laguerreCell y g j)
    (huniq : ∀ i l, i ≠ l → ‖x - y i‖ ^ 2 - g i ≠ ‖x - y l‖ ^ 2 - g l) (F : Fin k → M) :
    ∑ i, (laguerreCell y g i).indicator (fun _ ↦ F i) x = F j := by
  rw [Finset.sum_eq_single j (fun i _ hij ↦ ?_) (fun h ↦ absurd (Finset.mem_univ j) h)]
  · exact Set.indicator_of_mem hj _
  · have : x ∉ laguerreCell y g i := fun hi ↦ huniq i j hij (le_antisymm (hi j) (hj i))
    exact Set.indicator_of_notMem this _

/-- The value of a discrete measure `∑ b_j δ_{y_j}` on a set. -/
private theorem sum_smul_dirac_apply (y : Fin k → EuclideanSpace ℝ (Fin d)) (b : Fin k → ℝ)
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)) s =
      ∑ j, ENNReal.ofReal (b j) * s.indicator 1 (y j) := by
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply,
    Measure.dirac_apply, smul_eq_mul]

/-- A discrete measure `∑ b_j δ_{y_j}` with distinct sites gives the site `y_j` the mass `b_j`. -/
theorem sum_smul_dirac_singleton {y : Fin k → EuclideanSpace ℝ (Fin d)}
    (hy : Function.Injective y) (b : Fin k → ℝ) (j : Fin k) :
    (∑ i, ENNReal.ofReal (b i) • Measure.dirac (y i)) {y j} = ENNReal.ofReal (b j) := by
  rw [sum_smul_dirac_apply, Finset.sum_eq_single j (fun i _ hij ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ j) h)]
  · simp
  · have : y i ∉ ({y j} : Set _) := fun h ↦ hij (hy h)
    simp [this]

/-- A discrete measure `∑ b_j δ_{y_j}` is carried by the sites. -/
theorem sum_smul_dirac_compl_range (y : Fin k → EuclideanSpace ℝ (Fin d)) (b : Fin k → ℝ) :
    (∑ i, ENNReal.ofReal (b i) • Measure.dirac (y i)) (range y)ᶜ = 0 := by
  rw [sum_smul_dirac_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have : y j ∉ (range y)ᶜ := fun h ↦ h (mem_range_self j)
  simp [this]

/-- The semidiscrete transport map sends each Laguerre cell `L_j(g)` to its site `y_j` (on the
null set of ties the value is a sum of sites). -/
def semidiscreteTransportMap (y : Fin k → EuclideanSpace ℝ (Fin d)) (g : Fin k → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ j, (laguerreCell y g j).indicator (fun _ ↦ y j) x

/-- The semidiscrete transport map is measurable. -/
theorem measurable_semidiscreteTransportMap (y : Fin k → EuclideanSpace ℝ (Fin d))
    (g : Fin k → ℝ) : Measurable (semidiscreteTransportMap y g) := by
  unfold semidiscreteTransportMap
  exact Finset.measurable_sum _ fun j _ ↦
    measurable_const.indicator (measurableSet_laguerreCell y g j)

/-- For an absolutely continuous law and distinct sites, almost every point lies in a Laguerre
cell and has no ties. -/
theorem ae_exists_mem_laguerreCell (hk : 0 < k) {P : Measure (EuclideanSpace ℝ (Fin d))}
    (hP : P ≪ volume) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    (g : Fin k → ℝ) :
    ∀ᵐ x ∂P, ∃ j, x ∈ laguerreCell y g j ∧
      ∀ i l, i ≠ l → ‖x - y i‖ ^ 2 - g i ≠ ‖x - y l‖ ^ 2 - g l := by
  filter_upwards [ae_forall_ne_of_absolutelyContinuous hP hy g] with x hx
  obtain ⟨j, hj⟩ := exists_mem_laguerreCell hk y g x
  exact ⟨j, hj, hx⟩

/-- GAPS 108.56: when the Laguerre cells have the masses `b_j`, the semidiscrete transport map
pushes `P` forward to the discrete law `∑ b_j δ_{y_j}`. -/
theorem map_semidiscreteTransportMap (hk : 0 < k) {P : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure P] (hP : P ≪ volume) {y : Fin k → EuclideanSpace ℝ (Fin d)}
    (hy : Function.Injective y) {b g : Fin k → ℝ}
    (hmass : ∀ j, P.real (laguerreCell y g j) = b j) :
    P.map (semidiscreteTransportMap y g) = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j) := by
  have hT := measurable_semidiscreteTransportMap y g
  ext s hs
  rw [Measure.map_apply hT hs, sum_smul_dirac_apply, ← lintegral_indicator_one (hT hs)]
  have hae : (fun x ↦ (semidiscreteTransportMap y g ⁻¹' s).indicator 1 x) =ᵐ[P]
      fun x ↦ ∑ j, (laguerreCell y g j).indicator
        (fun _ ↦ s.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (y j)) x := by
    filter_upwards [ae_exists_mem_laguerreCell hk hP hy g] with x ⟨j, hj, huniq⟩
    rw [sum_indicator_laguerreCell_eq hj huniq]
    have hTx : semidiscreteTransportMap y g x = y j := sum_indicator_laguerreCell_eq hj huniq y
    by_cases h : y j ∈ s
    · rw [Set.indicator_of_mem (show x ∈ semidiscreteTransportMap y g ⁻¹' s by
        rw [mem_preimage, hTx]; exact h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ semidiscreteTransportMap y g ⁻¹' s by
        rw [mem_preimage, hTx]; exact h), Set.indicator_of_notMem h]
  rw [lintegral_congr_ae hae, lintegral_finsetSum _ fun j _ ↦
    measurable_const.indicator (measurableSet_laguerreCell y g j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [lintegral_indicator_const (measurableSet_laguerreCell y g j), ← hmass j,
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]

/-- GAPS 108.56: when the Laguerre cells have the masses `b_j`, the quadratic cost of the
semidiscrete transport map is the value of the dual functional. -/
theorem integral_norm_sub_semidiscreteTransportMap_sq (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    {b g : Fin k → ℝ} (hmass : ∀ j, P.real (laguerreCell y g j) = b j) :
    Integrable (fun x ↦ ‖x - semidiscreteTransportMap y g x‖ ^ 2) P ∧
      ∫ x, ‖x - semidiscreteTransportMap y g x‖ ^ 2 ∂P = semidiscreteTransportDual P y b g := by
  have hae : (fun x ↦ ‖x - semidiscreteTransportMap y g x‖ ^ 2) =ᵐ[P]
      fun x ↦ semidiscretePotential y g x +
        ∑ j, (laguerreCell y g j).indicator (fun _ ↦ g j) x := by
    filter_upwards [ae_exists_mem_laguerreCell hk hP hy g] with x ⟨j, hj, huniq⟩
    rw [sum_indicator_laguerreCell_eq hj huniq, (mem_laguerreCell_iff hk y g x j).mp hj,
      show semidiscreteTransportMap y g x = y j from sum_indicator_laguerreCell_eq hj huniq y]
    ring
  have hI : ∀ j, Integrable ((laguerreCell y g j).indicator fun _ ↦ g j) P := fun j ↦
    (integrable_const (g j)).indicator (measurableSet_laguerreCell y g j)
  have hInt : Integrable (fun x ↦ semidiscretePotential y g x +
      ∑ j, (laguerreCell y g j).indicator (fun _ ↦ g j) x) P :=
    (integrable_semidiscretePotential hk h2 y g).add (integrable_finsetSum _ fun j _ ↦ hI j)
  refine ⟨hInt.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (integrable_semidiscretePotential hk h2 y g)
    (integrable_finsetSum _ fun j _ ↦ hI j), integral_finsetSum _ fun j _ ↦ hI j,
    semidiscreteTransportDual_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_indicator_const _ (measurableSet_laguerreCell y g j), hmass j, smul_eq_mul]

/-- GAPS 108.56, weak duality: for every coupling `π` of `P` and `∑ b_j δ_{y_j}` with distinct
sites, the dual functional is at most the quadratic cost of `π`. -/
theorem ofReal_semidiscreteTransportDual_le_lintegral (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (h2 : MemLp id 2 P)
    {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y) {b : Fin k → ℝ}
    (hb : ∀ j, 0 ≤ b j) (g : Fin k → ℝ)
    {π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    (hπ : TauCeti.IsCoupling π P (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))) :
    ENNReal.ofReal (semidiscreteTransportDual P y b g) ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
  set ν := ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)
  have hfst : π.map Prod.fst = P := hπ.fst_eq
  have hsnd : π.map Prod.snd = ν := hπ.snd_eq
  have hπ1 : IsProbabilityMeasure π := by
    have := congrArg (fun m : Measure _ ↦ m univ) hfst
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      measure_univ] at this
    exact ⟨this⟩
  have hran : ∀ᵐ z ∂π, z.2 ∈ range y := by
    have : ∀ᵐ w ∂ν, w ∈ range y := ae_iff.mpr (sum_smul_dirac_compl_range y b)
    rw [← hsnd] at this
    exact ae_of_ae_map measurable_snd.aemeasurable this
  have hφ : Integrable (fun z : _ × _ ↦ semidiscretePotential y g z.1) π := by
    have := integrable_semidiscretePotential hk h2 y g
    rw [← hfst] at this
    exact this.comp_measurable measurable_fst
  have hG : Integrable (fun z : _ × _ ↦ ∑ j, ‖z.1 - y j‖ ^ 2) π := by
    refine integrable_finsetSum _ fun j _ ↦ ?_
    have := integrable_norm_sub_sq h2 (y j)
    rw [← hfst] at this
    exact this.comp_measurable measurable_fst
  have hh : Integrable (fun z : _ × _ ↦ ‖z.1 - z.2‖ ^ 2) π := by
    refine hG.mono' (by fun_prop) ?_
    filter_upwards [hran] with z ⟨j, hj⟩
    rw [← hj, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j ↦ ‖z.1 - y j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ j)
  have hs : ∀ j, MeasurableSet (Prod.snd ⁻¹' {y j} :
      Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) := fun j ↦
    measurable_snd (measurableSet_singleton _)
  have hI : ∀ j, Integrable ((Prod.snd ⁻¹' {y j}).indicator fun _ ↦ g j) π := fun j ↦
    (integrable_const (g j)).indicator (hs j)
  have hle : (fun z : _ × _ ↦ semidiscretePotential y g z.1 +
      ∑ j, (Prod.snd ⁻¹' {y j}).indicator (fun _ ↦ g j) z) ≤ᵐ[π]
      fun z ↦ ‖z.1 - z.2‖ ^ 2 := by
    filter_upwards [hran] with z ⟨j, hj⟩
    have hsum : ∑ i, (Prod.snd ⁻¹' {y i}).indicator (fun _ ↦ g i) z = g j := by
      rw [Finset.sum_eq_single j (fun i _ hij ↦ ?_) (fun h ↦ absurd (Finset.mem_univ j) h)]
      · exact Set.indicator_of_mem (show z ∈ Prod.snd ⁻¹' ({y j} : Set _) from hj.symm) _
      · exact Set.indicator_of_notMem (show z ∉ Prod.snd ⁻¹' ({y i} : Set _) from
          fun h ↦ hij (hy ((show z.2 = y i from h).symm.trans hj.symm))) _
    rw [hsum, ← hj]
    linarith [semidiscretePotential_le y g z.1 j]
  have hval : ∫ z, (semidiscretePotential y g z.1 +
      ∑ j, (Prod.snd ⁻¹' {y j}).indicator (fun _ ↦ g j) z) ∂π =
      semidiscreteTransportDual P y b g := by
    rw [integral_add hφ (integrable_finsetSum _ fun j _ ↦ hI j),
      integral_finsetSum _ fun j _ ↦ hI j, semidiscreteTransportDual_eq]
    congr 1
    · rw [← hfst, integral_map measurable_fst.aemeasurable
        (measurable_semidiscretePotential y g).aestronglyMeasurable]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_indicator_const _ (hs j), smul_eq_mul, Measure.real,
        ← Measure.map_apply measurable_snd (measurableSet_singleton _), hsnd,
        sum_smul_dirac_singleton hy b j, ENNReal.toReal_ofReal (hb j)]
  rw [TauCeti.lintegral_edist_sq_eq_ofReal_integral hh, ← hval]
  exact ENNReal.ofReal_le_ofReal (integral_mono_ae (hφ.add
    (integrable_finsetSum _ fun j _ ↦ hI j)) hh hle)

/-- GAPS 108.56, the value: when the Laguerre cells have the masses `b_j` (equivalently, at a
maximizer), the dual functional equals the squared Wasserstein distance `W₂(P, ∑ b_j δ_{y_j})²`. -/
theorem semidiscreteTransportDual_eq_wassersteinEDist_sq (hk : 0 < k)
    {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P] (hP : P ≪ volume)
    (h2 : MemLp id 2 P) {y : Fin k → EuclideanSpace ℝ (Fin d)} (hy : Function.Injective y)
    {b g : Fin k → ℝ} (hmass : ∀ j, P.real (laguerreCell y g j) = b j) :
    semidiscreteTransportDual P y b g =
      (TauCeti.wassersteinEDist 2 P
        (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))).toReal ^ 2 := by
  have hb : ∀ j, 0 ≤ b j := fun j ↦ hmass j ▸ measureReal_nonneg
  obtain ⟨hInt, hval⟩ := integral_norm_sub_semidiscreteTransportMap_sq hk hP h2 hy hmass
  have hE : 0 ≤ semidiscreteTransportDual P y b g :=
    hval ▸ integral_nonneg fun _ ↦ sq_nonneg _
  have hlaw : ProbabilityTheory.HasLaw (semidiscreteTransportMap y g)
      (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)) P :=
    ⟨(measurable_semidiscreteTransportMap y g).aemeasurable,
      map_semidiscreteTransportMap hk hP hy hmass⟩
  have key : TauCeti.wassersteinEDist 2 P (∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j)) ^
      (2 : ℝ) = ENNReal.ofReal (semidiscreteTransportDual P y b g) := by
    have h2r : (2 : ℝ) = (2 : ℝ≥0∞).toReal := by simp
    rw [h2r, TauCeti.wassersteinEDist_rpow_eq_transportCost measurable_edist two_ne_zero
      ENNReal.ofNat_ne_top, ← h2r]
    simp only [ENNReal.rpow_two]
    refine le_antisymm ((TauCeti.transportCost_le_lintegral_of_hasLaw hlaw _).trans_eq ?_)
      (TauCeti.le_transportCost fun π hπ ↦
        ofReal_semidiscreteTransportDual_le_lintegral hk h2 hy hb g hπ)
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun _ ↦ sq_nonneg _)]
    refine lintegral_congr fun x ↦ ?_
    rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← Real.rpow_two, ENNReal.toReal_rpow, key, ENNReal.toReal_ofReal hE]

end CKSD
