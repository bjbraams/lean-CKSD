module

public import CKSD.Asymptotics.LikelihoodSupport
public import TauCeti.Probability.Moments.Bernstein
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Maximal inequalities for Lipschitz parameter families

For an iid sample and a family of functions `θ ↦ f θ` on a cube of `ℝᵈ` that is Lipschitz in the
parameter with a square-integrable envelope `L`, this file bounds the oscillation of the
normalised empirical process `Gₙ f = n^{-1/2} (∑ f(Xᵢ) - n P f)` over the cube. The envelope is
truncated at `ε √n`; the truncated increments satisfy Bernstein's inequality and are chained over
dyadic grids, and the untruncated part is controlled by an empirical envelope whose expectation
tends to zero. The consequence used for M-estimators, the uniform local expansion
`√n (Gₙ f(θ₀ + h/√n) - Gₙ f θ₀) = ⟪h, n^{-1/2} ∑ s(Xᵢ)⟫ + o_P(1)` over bounded sets of `h`, is
in `CKSD.Asymptotics.LipschitzExpansion`.

## Main definitions

* `CKSD.empiricalProcess`: the normalised centred empirical process.
* `CKSD.halfOpenCube`, `CKSD.cubeGridPoint`, `CKSD.cubeIndex`, `CKSD.centredCube`: dyadic grids.
* `CKSD.lipschitzChainRemainder`: the random remainder of the chaining bound.

## Main results

* `CKSD.measureReal_le_abs_empiricalProcess_le`: Bernstein's inequality for `Gₙ g`.
* `CKSD.measureReal_exists_cube_chain_le`: dyadic chaining on a cube.
* `CKSD.measureReal_exists_abs_empiricalProcess_sub_gt_le`: the maximal inequality.
* `CKSD.tendstoInMeasure_lipschitzChainRemainder`: the remainder tends to zero in probability.

## References

The argument follows the bracketing and chaining proofs in van der Vaart, *Asymptotic
Statistics*, Lemma 19.34 and Lemma 19.31, specialised to Lipschitz parametric classes. Bernstein's
inequality is TauCeti's `ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_of_abs_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- The normalised centred empirical process `n^{-1/2} (∑_{i<n} f(Xᵢ) - n ∫ f dP)`. -/
def empiricalProcess {Ω X : Type*} [MeasurableSpace X] (P : Measure X) (Xn : ℕ → Ω → X)
    (n : ℕ) (f : X → ℝ) (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, f (Xn i ω) - n * ∫ x, f x ∂P)

/-- The empirical process is additive on integrable functions: `Gₙ (f - g) = Gₙ f - Gₙ g`. -/
theorem empiricalProcess_sub {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) {f g : X → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (ω : Ω) :
    empiricalProcess P Xn n (fun x ↦ f x - g x) ω =
      empiricalProcess P Xn n f ω - empiricalProcess P Xn n g ω := by
  simp only [empiricalProcess, integral_sub hf hg, Finset.sum_sub_distrib]
  ring

/-- The empirical process is additive on integrable functions: `Gₙ (f + g) = Gₙ f + Gₙ g`. -/
theorem empiricalProcess_add {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) {f g : X → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (ω : Ω) :
    empiricalProcess P Xn n (fun x ↦ f x + g x) ω =
      empiricalProcess P Xn n f ω + empiricalProcess P Xn n g ω := by
  simp only [empiricalProcess, integral_add hf hg, Finset.sum_add_distrib]
  ring

/-- Deterministic bound: `|Gₙ f| ≤ n^{-1/2} (∑ |f|(Xᵢ) + n ∫ |f|)`. -/
theorem abs_empiricalProcess_le {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) (f F : X → ℝ) (hF : Integrable F P) (hfF : ∀ x, |f x| ≤ F x)
    (ω : Ω) :
    |empiricalProcess P Xn n f ω| ≤
      (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, F (Xn i ω) + n * ∫ x, F x ∂P) := by
  unfold empiricalProcess
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  gcongr
  have h1 : |∑ i ∈ Finset.range n, f (Xn i ω)| ≤ ∑ i ∈ Finset.range n, F (Xn i ω) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hfF _)
  have h2 : |∫ x, f x ∂P| ≤ ∫ x, F x ∂P := by
    by_cases hfi : Integrable f P
    · exact (abs_integral_le_integral_abs).trans (integral_mono hfi.abs hF hfF)
    · rw [integral_undef hfi, abs_zero]
      exact integral_nonneg fun x ↦ (abs_nonneg _).trans (hfF x)
  have h3 : |(n : ℝ) * ∫ x, f x ∂P| ≤ n * ∫ x, F x ∂P := by
    rw [abs_mul, Nat.abs_cast]; gcongr
  calc _ ≤ |∑ i ∈ Finset.range n, f (Xn i ω)| + |(n : ℝ) * ∫ x, f x ∂P| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h3

/-- Bernstein's inequality for the empirical process of a bounded function: if `|g| ≤ b` and
`∫ g² dP ≤ v` with `v > 0`, then `P(t ≤ |Gₙ g|) ≤ 2 exp(-t² / (2 (v + 2 b t / (3 √n))))`. -/
theorem measureReal_le_abs_empiricalProcess_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (g : X → ℝ) (hg : Measurable g) {b v : ℝ} (hgb : ∀ x, |g x| ≤ b)
    (hv : ∫ x, g x ^ 2 ∂P ≤ v) (hv0 : 0 < v) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |empiricalProcess P Xn n g ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (v + 2 * b * t / (3 * Real.sqrt n)))) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hne : Nonempty X := nonempty_of_isProbabilityMeasure P
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hgb (Classical.arbitrary _))
  have hgi : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable b
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hgb x)
  set c : ℝ := ∫ x, g x ∂P with hc
  have hcb : |c| ≤ b := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |g x| ∂P ≤ ∫ _x, b ∂P := integral_mono hgi.abs (integrable_const b) hgb
      _ = b := by simp
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  rcases ht.eq_or_lt with rfl | ht'
  · refine (measureReal_le_one).trans ?_
    simp
  rcases hb0.eq_or_lt with hb | hb
  · have hg0 : ∀ x, g x = 0 := fun x ↦ abs_nonpos_iff.1 (hb ▸ hgb x)
    have : {ω | t ≤ |empiricalProcess P Xn n g ω|} = ∅ := by
      ext ω
      simp only [empiricalProcess, hg0, Finset.sum_const_zero, integral_zero, mul_zero,
        sub_zero, abs_zero, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact ht'
    rw [this, measureReal_empty]
    positivity
  set Y : ℕ → Ω → ℝ := fun i ω ↦ g (Xn i ω) - c with hY
  have hYind : iIndepFun Y μ :=
    hind.comp (fun _ x ↦ g x - c) fun _ ↦ hg.sub measurable_const
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ (hg.comp (hXm i)).sub measurable_const
  have hint : ∀ i (φ : ℝ → ℝ), Measurable φ →
      ∫ ω, φ (g (Xn i ω)) ∂μ = ∫ x, φ (g x) ∂P := fun i φ hφ ↦ by
    rw [← hlaw i]
    exact (integral_map (hXm i).aemeasurable (hφ.comp hg).aestronglyMeasurable).symm
  have hmean : ∀ i ∈ Finset.range n, μ[Y i] = 0 := fun i _ ↦ by
    have := hint i (fun y ↦ y - c) (measurable_id.sub measurable_const)
    simp only [hY]
    rw [this, integral_sub hgi (integrable_const c)]
    simp [hc]
  have hYb : ∀ i ∈ Finset.range n, ∀ᵐ ω ∂μ, |Y i ω| ≤ 2 * b := fun i _ ↦
    ae_of_all _ fun ω ↦ by
      simp only [hY]
      have := hgb (Xn i ω)
      calc |g (Xn i ω) - c| ≤ |g (Xn i ω)| + |c| := abs_sub _ _
        _ ≤ 2 * b := by linarith
  have hYv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v := fun i ↦ by
    have := hint i (fun y ↦ (y - c) ^ 2) ((measurable_id.sub measurable_const).pow_const 2)
    simp only [hY]
    rw [this, ← variance_eq_integral hg.aemeasurable]
    exact (variance_le_expectation_sq hg.aestronglyMeasurable).trans hv
  have hbern := hYind.measureReal_abs_sum_ge_le_of_abs_le (s := Finset.range n) (b := 2 * b)
    (ε := Real.sqrt n * t) (fun i _ ↦ (hYm i).aemeasurable) hmean hYb (by positivity)
  set D' : ℝ := ∑ i ∈ Finset.range n, ∫ ω, Y i ω ^ 2 ∂μ with hD'
  have hD'le : D' ≤ n * v := by
    calc D' ≤ ∑ _i ∈ Finset.range n, v := Finset.sum_le_sum fun i _ ↦ hYv i
      _ = n * v := by simp
  have hD'0 : 0 ≤ D' := Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hset : {ω | t ≤ |empiricalProcess P Xn n g ω|} =
      {ω | Real.sqrt n * t ≤ |∑ i ∈ Finset.range n, Y i ω|} := by
    ext ω
    have hsum : ∑ i ∈ Finset.range n, Y i ω = ∑ i ∈ Finset.range n, g (Xn i ω) - n * c := by
      simp [hY, Finset.sum_sub_distrib]
    simp only [mem_ofPred_eq, empiricalProcess, hsum, ← hc, abs_mul,
      abs_of_pos (inv_pos.2 hsn)]
    rw [inv_mul_eq_div, le_div_iff₀ hsn, mul_comm]
  rw [hset]
  refine hbern.trans ?_
  gcongr 2 * Real.exp ?_
  have hpos1 : 0 < D' + 2 * b * (Real.sqrt n * t) / 3 := by positivity
  have hpos2 : 0 < v + 2 * b * t / (3 * Real.sqrt n) := by positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  calc t ^ 2 / (2 * (v + 2 * b * t / (3 * Real.sqrt n)))
      = (Real.sqrt n * t) ^ 2 / (2 * (n * v + 2 * b * (Real.sqrt n * t) / 3)) := by
        field_simp
        linear_combination (-3 * v) * hsq
    _ ≤ (Real.sqrt n * t) ^ 2 / (2 * (D' + 2 * b * (Real.sqrt n * t) / 3)) := by
        gcongr

/-! ### Dyadic grids on a half-open cube -/

/-- The half-open cube `∏ᵢ [aᵢ, aᵢ + w)` in Euclidean space. -/
def halfOpenCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (w : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {θ | ∀ i, a i ≤ θ i ∧ θ i < a i + w}

/-- The point `a + (w / 2ᵏ) z` of the dyadic grid of level `k` in the cube anchored at `a`. -/
def cubeGridPoint {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (w : ℝ) (k : ℕ) (z : Fin d → ℤ) :
    EuclideanSpace ℝ (Fin d) :=
  a + WithLp.toLp 2 (fun i ↦ (z i : ℝ) * (w / 2 ^ k))

/-- The index of the dyadic cell of level `k` containing `θ`. -/
def cubeIndex {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (w : ℝ) (k : ℕ)
    (θ : EuclideanSpace ℝ (Fin d)) : Fin d → ℤ :=
  fun i ↦ ⌊(θ i - a i) * 2 ^ k / w⌋

/-- Coordinates of a grid point: `(a + (w / 2ᵏ) z)ᵢ = aᵢ + zᵢ w / 2ᵏ`. -/
@[simp] theorem cubeGridPoint_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (w : ℝ) (k : ℕ)
    (z : Fin d → ℤ) (i : Fin d) : cubeGridPoint a w k z i = a i + z i * (w / 2 ^ k) := by
  simp [cubeGridPoint]

/-- A vector whose coordinates are bounded by `c` has Euclidean norm at most `√d c`. -/
theorem norm_le_sqrt_card_mul_of_abs_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) {c : ℝ}
    (h : ∀ i, |v i| ≤ c) : ‖v‖ ≤ Real.sqrt d * c := by
  have hne : ∀ i, 0 ≤ c := fun i ↦ (abs_nonneg _).trans (h i)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [EuclideanSpace.norm_eq]
  have hc : 0 ≤ c := hne ⟨0, hd⟩
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hc, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * c ^ 2 := by simp

/-- The cell indices of a point of the cube lie in `[0, 2ᵏ)`. -/
theorem cubeIndex_mem {d : ℕ} {a θ : EuclideanSpace ℝ (Fin d)} {w : ℝ} (hw : 0 < w)
    (hθ : θ ∈ halfOpenCube a w) (k : ℕ) :
    cubeIndex a w k θ ∈ Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (2 ^ k) := by
  rw [Fintype.mem_piFinset]
  intro i
  obtain ⟨h1, h2⟩ := hθ i
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [Finset.mem_Ico, cubeIndex, Int.le_floor, Int.floor_lt]
  push_cast
  constructor
  · exact div_nonneg (mul_nonneg (by linarith) hp.le) hw.le
  · rw [div_lt_iff₀ hw]; nlinarith

/-- Grid points with indices in `[0, 2ᵏ)` lie in the cube. -/
theorem cubeGridPoint_mem {d : ℕ} {a : EuclideanSpace ℝ (Fin d)} {w : ℝ} (hw : 0 < w) {k : ℕ}
    {z : Fin d → ℤ} (hz : z ∈ Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (2 ^ k)) :
    cubeGridPoint a w k z ∈ halfOpenCube a w := by
  rw [Fintype.mem_piFinset] at hz
  intro i
  have h := Finset.mem_Ico.1 (hz i)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : (0 : ℝ) ≤ z i := by exact_mod_cast h.1
  have h2 : (z i : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Int.add_one_le_iff.2 h.2
  have e : (2 : ℝ) ^ k * (w / 2 ^ k) = w := by field_simp
  rw [cubeGridPoint_apply]
  constructor
  · have : 0 ≤ (z i : ℝ) * (w / 2 ^ k) := mul_nonneg h1 (by positivity)
    linarith
  · have : ((z i : ℝ) + 1) * (w / 2 ^ k) ≤ 2 ^ k * (w / 2 ^ k) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith

/-- A point exceeds its grid point of level `k` coordinatewise by less than `w / 2ᵏ`. -/
theorem sub_cubeGridPoint_cubeIndex_mem {d : ℕ} (a θ : EuclideanSpace ℝ (Fin d)) {w : ℝ}
    (hw : 0 < w) (k : ℕ) (i : Fin d) :
    0 ≤ θ i - cubeGridPoint a w k (cubeIndex a w k θ) i ∧
      θ i - cubeGridPoint a w k (cubeIndex a w k θ) i < w / 2 ^ k := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  set x := (θ i - a i) * 2 ^ k / w with hx
  have hx' : θ i - a i = x * (w / 2 ^ k) := by rw [hx]; field_simp
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hh : 0 < w / 2 ^ k := by positivity
  rw [cubeGridPoint_apply, cubeIndex]
  rw [← hx]
  constructor <;> nlinarith

/-- A point of the cube is within `√d w / 2ᵏ` of its grid point of level `k`. -/
theorem norm_sub_cubeGridPoint_cubeIndex_le {d : ℕ} (a θ : EuclideanSpace ℝ (Fin d)) {w : ℝ}
    (hw : 0 < w) (k : ℕ) :
    ‖θ - cubeGridPoint a w k (cubeIndex a w k θ)‖ ≤ Real.sqrt d * (w / 2 ^ k) := by
  refine norm_le_sqrt_card_mul_of_abs_le _ fun i ↦ ?_
  obtain ⟨h1, h2⟩ := sub_cubeGridPoint_cubeIndex_mem a θ hw k i
  rw [PiLp.sub_apply, abs_of_nonneg h1]
  exact h2.le

/-- The cell index of level `k` is the halved cell index of level `k + 1`. -/
theorem cubeIndex_eq_div_two {d : ℕ} (a θ : EuclideanSpace ℝ (Fin d)) (w : ℝ) (k : ℕ) :
    cubeIndex a w k θ = fun i ↦ cubeIndex a w (k + 1) θ i / 2 := by
  funext i
  set x := (θ i - a i) * 2 ^ k / w with hx
  have hx2 : (θ i - a i) * 2 ^ (k + 1) / w = 2 * x := by rw [hx, pow_succ]; ring
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hk1 : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hk2 : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by rw [Int.floor_lt]; push_cast; linarith
  simp only [cubeIndex]
  rw [hx2, ← hx]
  omega

/-- Consecutive grid points of a chain are within `√d w / 2ᵏ⁺¹` of each other. -/
theorem norm_cubeGridPoint_succ_sub_le {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) {w : ℝ}
    (hw : 0 < w) (k : ℕ) (z : Fin d → ℤ) :
    ‖cubeGridPoint a w (k + 1) z - cubeGridPoint a w k (fun i ↦ z i / 2)‖ ≤
      Real.sqrt d * (w / 2 ^ (k + 1)) := by
  refine norm_le_sqrt_card_mul_of_abs_le _ fun i ↦ ?_
  have hdm : 2 * (z i / 2) + z i % 2 = z i := by omega
  have hm0 := Int.emod_nonneg (z i) (by norm_num : (2 : ℤ) ≠ 0)
  have hm1 := Int.emod_lt_of_pos (z i) (by norm_num : (0 : ℤ) < 2)
  have e : (z i : ℝ) = 2 * ((z i / 2 : ℤ) : ℝ) + ((z i % 2 : ℤ) : ℝ) := by
    exact_mod_cast hdm.symm
  have r0 : (0 : ℝ) ≤ ((z i % 2 : ℤ) : ℝ) := by exact_mod_cast hm0
  have r1 : ((z i % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : z i % 2 ≤ 1)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hval : cubeGridPoint a w (k + 1) z i - cubeGridPoint a w k (fun i ↦ z i / 2) i =
      ((z i % 2 : ℤ) : ℝ) * (w / 2 ^ (k + 1)) := by
    rw [cubeGridPoint_apply, cubeGridPoint_apply, e, pow_succ]
    field_simp
    ring
  rw [PiLp.sub_apply, hval, abs_mul, abs_of_nonneg r0, abs_of_pos (by positivity)]
  nlinarith [show (0 : ℝ) < w / 2 ^ (k + 1) by positivity]

/-- The level-zero grid point of a point of the cube is the anchor. -/
theorem cubeGridPoint_zero_cubeIndex {d : ℕ} {a θ : EuclideanSpace ℝ (Fin d)} {w : ℝ}
    (hw : 0 < w) (hθ : θ ∈ halfOpenCube a w) :
    cubeGridPoint a w 0 (cubeIndex a w 0 θ) = a := by
  have h := cubeIndex_mem hw hθ 0
  rw [Fintype.mem_piFinset] at h
  have h0 : cubeIndex a w 0 θ = 0 := by
    funext i
    have := Finset.mem_Ico.1 (h i)
    simp only [pow_zero] at this
    simp only [Pi.zero_apply]
    omega
  rw [h0]
  ext i
  simp

/-- `∑_{k<K} (k + 1) / 2ᵏ⁺¹ = 2 - (K + 2) / 2ᴷ`. -/
private theorem sum_range_succ_div_two_pow (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ (k + 1) = 2 - (K + 2) / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- `∑_{k<K} 1 / 2ᵏ⁺¹ = 1 - 1 / 2ᴷ`. -/
private theorem sum_range_one_div_two_pow (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 : ℝ) / 2 ^ (k + 1) = 1 - 1 / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring

/-- Dyadic chaining on a half-open cube. If every increment of a process `S` over the cube
exceeds `‖u - v‖ ((j + 1) A + W)` with probability at most `2 pʲ⁺¹`, then the increment between
the anchor and the grid point of level `K` of any point of the cube exceeds `√d w (2 A + W)` with
probability at most `2 ∑_{k<K} (2ᵈ p)ᵏ⁺¹`. -/
theorem measureReal_exists_cube_chain_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {d : ℕ} (S : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (a : EuclideanSpace ℝ (Fin d)) {w : ℝ} (hw : 0 < w) (W : Ω → ℝ) (hW : ∀ ω, 0 ≤ W ω)
    {A p : ℝ} (hA : 0 ≤ A)
    (hS : ∀ u ∈ halfOpenCube a w, ∀ v ∈ halfOpenCube a w, ∀ j : ℕ,
      μ.real {ω | ‖u - v‖ * ((j + 1) * A + W ω) < |S u ω - S v ω|} ≤ 2 * p ^ (j + 1))
    (K : ℕ) :
    μ.real {ω | ∃ θ ∈ halfOpenCube a w, Real.sqrt d * w * (2 * A + W ω) <
      |S (cubeGridPoint a w K (cubeIndex a w K θ)) ω - S a ω|} ≤
      2 * ∑ k ∈ Finset.range K, (2 ^ d * p) ^ (k + 1) := by
  set I : ℕ → Finset (Fin d → ℤ) := fun k ↦
    Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (2 ^ (k + 1)) with hI
  set g : ℕ → (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := cubeGridPoint a w with hg
  set B : ℕ → (Fin d → ℤ) → Set Ω := fun k z ↦ {ω | ‖g (k + 1) z - g k (fun i ↦ z i / 2)‖ *
    ((k + 1) * A + W ω) < |S (g (k + 1) z) ω - S (g k (fun i ↦ z i / 2)) ω|} with hB
  have hsub : {ω | ∃ θ ∈ halfOpenCube a w, Real.sqrt d * w * (2 * A + W ω) <
      |S (cubeGridPoint a w K (cubeIndex a w K θ)) ω - S a ω|} ⊆
      ⋃ k ∈ Finset.range K, ⋃ z ∈ I k, B k z := by
    rintro ω ⟨θ, hθ, hlt⟩
    by_contra hn
    simp only [mem_iUnion, not_exists, hB, mem_ofPred_eq, not_lt, Finset.mem_range] at hn
    set π : ℕ → EuclideanSpace ℝ (Fin d) := fun j ↦ g j (cubeIndex a w j θ) with hπ
    have hstep : ∀ k < K, |S (π (k + 1)) ω - S (π k) ω| ≤
        Real.sqrt d * (w / 2 ^ (k + 1)) * ((k + 1) * A + W ω) := by
      intro k hk
      have hz := cubeIndex_mem hw hθ (k + 1)
      have hπk : π k = g k (fun i ↦ cubeIndex a w (k + 1) θ i / 2) := by
        simp only [hπ]; rw [cubeIndex_eq_div_two a θ w k]
      rw [hπk]
      refine (hn k hk _ hz).trans ?_
      gcongr
      · have := hW ω; positivity
      · exact norm_cubeGridPoint_succ_sub_le a hw k _
    have htel : S (π K) ω - S (π 0) ω =
        ∑ k ∈ Finset.range K, (S (π (k + 1)) ω - S (π k) ω) :=
      (Finset.sum_range_sub (fun j ↦ S (π j) ω) K).symm
    have h0 : π 0 = a := cubeGridPoint_zero_cubeIndex hw hθ
    have hsum : |∑ k ∈ Finset.range K, (S (π (k + 1)) ω - S (π k) ω)| ≤
        Real.sqrt d * w * (2 * A + W ω) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun k hk ↦ hstep k (Finset.mem_range.1 hk)).trans ?_
      have e : ∑ k ∈ Finset.range K,
          Real.sqrt d * (w / 2 ^ (k + 1)) * ((k + 1) * A + W ω) =
          Real.sqrt d * w * (A * ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ (k + 1) +
            W ω * ∑ k ∈ Finset.range K, (1 : ℝ) / 2 ^ (k + 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        field_simp
      rw [e, sum_range_succ_div_two_pow, sum_range_one_div_two_pow]
      have hK1 : 0 ≤ ((K : ℝ) + 2) / 2 ^ K := by positivity
      have hK2 : 0 ≤ (1 : ℝ) / 2 ^ K := by positivity
      have hWω := hW ω
      have : A * (2 - (K + 2) / 2 ^ K) + W ω * (1 - 1 / 2 ^ K) ≤ 2 * A + W ω := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hlt' : Real.sqrt d * w * (2 * A + W ω) < |S (π K) ω - S (π 0) ω| := by
      rw [h0]; exact hlt
    rw [htel] at hlt'
    linarith
  have hcard : ∀ k, ((I k).card : ℝ) = (2 ^ d) ^ (k + 1) := fun k ↦ by
    simp only [hI, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Ico, sub_zero]
    have : ((2 : ℤ) ^ (k + 1)).toNat = 2 ^ (k + 1) := by
      rw [show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
    rw [this]
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm]
  calc _ ≤ μ.real (⋃ k ∈ Finset.range K, ⋃ z ∈ I k, B k z) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range K, ∑ z ∈ I k, μ.real (B k z) :=
        (measureReal_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun k _ ↦ measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ k ∈ Finset.range K, ∑ _z ∈ I k, 2 * p ^ (k + 1) := by
        refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun z hz ↦ ?_
        have hz1 : z ∈ Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (2 ^ (k + 1)) := hz
        have hz2 : (fun i ↦ z i / 2) ∈ Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (2 ^ k) := by
          rw [Fintype.mem_piFinset] at hz1 ⊢
          intro i
          have := Finset.mem_Ico.1 (hz1 i)
          rw [pow_succ] at this
          rw [Finset.mem_Ico]
          omega
        simp only [hB]
        exact hS _ (cubeGridPoint_mem hw hz1) _ (cubeGridPoint_mem hw hz2) k
    _ = 2 * ∑ k ∈ Finset.range K, (2 ^ d * p) ^ (k + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_pow]
        ring

/-! ### Maximal inequality for Lipschitz parameter families -/

/-- The envelope `n^{-1/2} (∑_{i<n} F(Xᵢ) + n ∫ F dP)` bounding `|Gₙ f|` when `|f| ≤ F`. -/
def empiricalEnvelope {Ω X : Type*} [MeasurableSpace X] (P : Measure X) (Xn : ℕ → Ω → X)
    (n : ℕ) (F : X → ℝ) (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * (∑ i ∈ Finset.range n, F (Xn i ω) + n * ∫ x, F x ∂P)

/-- The random remainder in the chaining bound for a Lipschitz family with envelope `L`:
the envelope of the part of `L` above the truncation level `ε √n`, plus `2⁻ⁿ` times the envelope
of `L`. -/
def lipschitzChainRemainder {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (L : X → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  empiricalEnvelope P Xn n ({x | ε * Real.sqrt n < L x}.indicator L) ω +
    (2 ^ n)⁻¹ * empiricalEnvelope P Xn n L ω

/-- The Bernstein exponent `t² / (2 (β + γ t))`. -/
def bernsteinExponent (β γ t : ℝ) : ℝ := t ^ 2 / (2 * (β + γ * t))

/-- The Bernstein exponent grows at least linearly under dilation by `c ≥ 1`. -/
theorem mul_bernsteinExponent_le {β γ t c : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hc : 1 ≤ c) : c * bernsteinExponent β γ t ≤ bernsteinExponent β γ (c * t) := by
  unfold bernsteinExponent
  have h1 : 0 < β + γ * t := by positivity
  have h2 : 0 < β + γ * (c * t) := by have : 0 ≤ c := by linarith
                                      positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have : β + γ * (c * t) ≤ c * (β + γ * t) := by nlinarith
  have hct : 0 ≤ 2 * c * t ^ 2 := by positivity
  have key := mul_le_mul_of_nonneg_left this hct
  calc c * t ^ 2 * (2 * (β + γ * (c * t))) = 2 * c * t ^ 2 * (β + γ * (c * t)) := by ring
    _ ≤ 2 * c * t ^ 2 * (c * (β + γ * t)) := key
    _ = (c * t) ^ 2 * (2 * (β + γ * t)) := by ring

/-- The empirical envelope of a nonnegative function is nonnegative. -/
theorem empiricalEnvelope_nonneg {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) {F : X → ℝ} (hF : ∀ x, 0 ≤ F x) (ω : Ω) :
    0 ≤ empiricalEnvelope P Xn n F ω :=
  mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
    (add_nonneg (Finset.sum_nonneg fun _ _ ↦ hF _)
      (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg hF)))

/-- The empirical envelope is homogeneous: `envₙ (c F) = c envₙ F`. -/
theorem empiricalEnvelope_const_mul {Ω X : Type*} [MeasurableSpace X] (P : Measure X)
    (Xn : ℕ → Ω → X) (n : ℕ) (c : ℝ) (F : X → ℝ) (ω : Ω) :
    empiricalEnvelope P Xn n (fun x ↦ c * F x) ω = c * empiricalEnvelope P Xn n F ω := by
  simp only [empiricalEnvelope, integral_const_mul, ← Finset.mul_sum]
  ring

/-- **Maximal inequality for Lipschitz families.** Let `θ ↦ f θ` be a family of integrable
functions on a half-open cube of width `w` anchored at `a`, Lipschitz in `θ` with a nonnegative
square-integrable envelope `L`. For `n ≥ 1`, a truncation level `ε > 0` and `A ≥ 0`, the event
that `|Gₙ f θ - Gₙ f a| > √d w (2A + Rₙ)` for some `θ` of the cube, where `Rₙ` is
`lipschitzChainRemainder`, has probability at most `2 ∑_{k<n} (2ᵈ e^{-φ(A)})ᵏ⁺¹`, with `φ` the
Bernstein exponent with `β = ∫ L² + 1` and `γ = 2ε/3`. The proof truncates the envelope at
`ε √n`, applies Bernstein's inequality to the truncated increments, and chains over dyadic grids
of levels `< n`. -/
theorem measureReal_exists_abs_empiricalProcess_sub_gt_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → X → ℝ) (a : EuclideanSpace ℝ (Fin d)) {w : ℝ}
    (hw : 0 < w) (hfm : ∀ θ ∈ halfOpenCube a w, Measurable (f θ))
    (hfi : ∀ θ ∈ halfOpenCube a w, Integrable (f θ) P)
    (L : X → ℝ) (hLm : Measurable L) (hL0 : ∀ x, 0 ≤ L x) (hL2 : MemLp L 2 P)
    (hlip : ∀ u ∈ halfOpenCube a w, ∀ v ∈ halfOpenCube a w, ∀ x,
      |f u x - f v x| ≤ L x * ‖u - v‖)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 ≤ A) :
    μ.real {ω | ∃ θ ∈ halfOpenCube a w,
      Real.sqrt d * w * (2 * A + lipschitzChainRemainder P Xn L ε n ω) <
        |empiricalProcess P Xn n (f θ) ω - empiricalProcess P Xn n (f a) ω|} ≤
      2 * ∑ k ∈ Finset.range n,
        (2 ^ d * Real.exp (-bernsteinExponent (∫ x, L x ^ 2 ∂P + 1) (2 * ε / 3) A)) ^ (k + 1) := by
  set β : ℝ := ∫ x, L x ^ 2 ∂P + 1 with hβ
  have hβ0 : 0 < β := by
    have : 0 ≤ ∫ x, L x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    linarith
  set κ : ℝ := ε * Real.sqrt n with hκ
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set Lt : X → ℝ := {x | κ < L x}.indicator L with hLt
  have hLtm : Measurable Lt := hLm.indicator (measurableSet_lt measurable_const hLm)
  have hLt0 : ∀ x, 0 ≤ Lt x := fun x ↦ Set.indicator_nonneg (fun x _ ↦ hL0 x) x
  have hLi : Integrable L P := hL2.integrable one_le_two
  have hLti : Integrable Lt P := hLi.indicator (measurableSet_lt measurable_const hLm)
  set W : Ω → ℝ := empiricalEnvelope P Xn n Lt with hW
  have hW0 : ∀ ω, 0 ≤ W ω := empiricalEnvelope_nonneg P Xn n hLt0
  set S : EuclideanSpace ℝ (Fin d) → Ω → ℝ := fun θ ω ↦ empiricalProcess P Xn n (f θ) ω
    with hS
  set p : ℝ := Real.exp (-bernsteinExponent β (2 * ε / 3) A) with hp
  have hp0 : 0 ≤ p := (Real.exp_pos _).le
  -- The increment bound required by the chaining lemma.
  have hinc : ∀ u ∈ halfOpenCube a w, ∀ v ∈ halfOpenCube a w, ∀ j : ℕ,
      μ.real {ω | ‖u - v‖ * ((j + 1) * A + W ω) < |S u ω - S v ω|} ≤ 2 * p ^ (j + 1) := by
    intro u hu v hv j
    set t : ℝ := (j + 1) * A with ht
    have ht0 : 0 ≤ t := by positivity
    rcases eq_or_ne u v with rfl | huv
    · have : {ω | ‖u - u‖ * (t + W ω) < |S u ω - S u ω|} = ∅ := by
        ext ω; simp
      rw [this, measureReal_empty]; positivity
    set σ : ℝ := ‖u - v‖ with hσ
    have hσ0 : 0 < σ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    set D : X → ℝ := fun x ↦ f u x - f v x with hD
    have hDm : Measurable D := (hfm u hu).sub (hfm v hv)
    have hDb : ∀ x, |D x| ≤ σ * L x := fun x ↦ by
      rw [mul_comm]; exact hlip u hu v hv x
    set g : X → ℝ := {x | κ < L x}ᶜ.indicator D with hg
    set h : X → ℝ := {x | κ < L x}.indicator D with hh
    have hmeasL : MeasurableSet {x | κ < L x} := measurableSet_lt measurable_const hLm
    have hgm : Measurable g := hDm.indicator hmeasL.compl
    have hgh : ∀ x, D x = g x + h x := fun x ↦ by
      simp only [hg, hh]
      by_cases hx : κ < L x
      · simp [Set.indicator_of_mem, hx]
      · simp [Set.indicator_of_notMem, hx]
    have hgb : ∀ x, |g x| ≤ σ * κ := fun x ↦ by
      simp only [hg]
      by_cases hx : κ < L x
      · simp [hx]; positivity
      · simp only [Set.indicator_of_mem (show x ∈ {x | κ < L x}ᶜ from hx)]
        refine (hDb x).trans ?_
        exact mul_le_mul_of_nonneg_left (not_lt.1 hx) hσ0.le
    have hhb : ∀ x, |h x| ≤ σ * Lt x := fun x ↦ by
      simp only [hh, hLt]
      by_cases hx : κ < L x
      · simp only [Set.indicator_of_mem (show x ∈ {x | κ < L x} from hx)]; exact hDb x
      · simp [Set.indicator_of_notMem, hx]
    have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable (σ * κ)
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hgb x)
    have hhi : Integrable h P := (hLti.const_mul σ).mono'
      (hDm.indicator hmeasL).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hhb x)
    have hg2 : ∫ x, g x ^ 2 ∂P ≤ σ ^ 2 * β := by
      have hle : ∀ x, g x ^ 2 ≤ σ ^ 2 * L x ^ 2 := fun x ↦ by
        have : |g x| ≤ σ * L x := by
          simp only [hg]
          by_cases hx : κ < L x
          · simp [hx]; exact mul_nonneg hσ0.le (hL0 x)
          · simp only [Set.indicator_of_mem (show x ∈ {x | κ < L x}ᶜ from hx)]; exact hDb x
        rw [← sq_abs, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      calc ∫ x, g x ^ 2 ∂P ≤ ∫ x, σ ^ 2 * L x ^ 2 ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _)
              (hL2.integrable_sq.const_mul _) (ae_of_all _ hle)
        _ = σ ^ 2 * ∫ x, L x ^ 2 ∂P := integral_const_mul _ _
        _ ≤ σ ^ 2 * β := by gcongr; linarith
    have hsplit : ∀ ω, S u ω - S v ω =
        empiricalProcess P Xn n g ω + empiricalProcess P Xn n h ω := fun ω ↦ by
      simp only [hS]
      rw [← empiricalProcess_sub P Xn n (hfi u hu) (hfi v hv), ← empiricalProcess_add P Xn n
        hgi hhi]
      simp only [← hgh]
      rfl
    have hhW : ∀ ω, |empiricalProcess P Xn n h ω| ≤ σ * W ω := fun ω ↦ by
      have := abs_empiricalProcess_le P Xn n h (fun x ↦ σ * Lt x) (hLti.const_mul σ) hhb ω
      rw [hW, ← empiricalEnvelope_const_mul]
      exact this
    have hsub : {ω | σ * (t + W ω) < |S u ω - S v ω|} ⊆
        {ω | σ * t ≤ |empiricalProcess P Xn n g ω|} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [hsplit] at hω
      have := abs_add_le (empiricalProcess P Xn n g ω) (empiricalProcess P Xn n h ω)
      have := hhW ω
      nlinarith
    have hbern := measureReal_le_abs_empiricalProcess_le μ P Xn hiid g hgm hgb hg2
      (by positivity) hn (t := σ * t) (by positivity)
    refine (measureReal_mono hsub).trans (hbern.trans ?_)
    have hexp : Real.exp (-bernsteinExponent β (2 * ε / 3) A) ^ (j + 1) =
        Real.exp (-((j + 1 : ℝ) * bernsteinExponent β (2 * ε / 3) A)) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [hp, hexp]
    gcongr 2 * Real.exp ?_
    rw [neg_div, neg_le_neg_iff]
    have hmono := mul_bernsteinExponent_le (β := β) (γ := 2 * ε / 3) (t := A)
      (c := (j + 1 : ℝ)) hβ0 (by positivity) hA (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    refine hmono.trans (le_of_eq ?_)
    simp only [bernsteinExponent, ht]
    have hκ' : σ * κ * (σ * ((j + 1) * A)) / (3 * Real.sqrt n) =
        σ ^ 2 * (ε * ((j + 1) * A) / 3) := by
      simp only [hκ]; field_simp
    rw [show 2 * (σ * κ) * (σ * ((↑j + 1) * A)) / (3 * Real.sqrt ↑n) =
      2 * (σ * κ * (σ * ((j + 1) * A)) / (3 * Real.sqrt n)) by ring, hκ']
    field_simp
  have hchain := measureReal_exists_cube_chain_le μ S a hw W hW0 hA hinc n
  refine (measureReal_mono ?_).trans hchain
  rintro ω ⟨θ, hθ, hlt⟩
  refine ⟨θ, hθ, ?_⟩
  set πθ := cubeGridPoint a w n (cubeIndex a w n θ)
  have hπ : πθ ∈ halfOpenCube a w := cubeGridPoint_mem hw (cubeIndex_mem hw hθ n)
  have hres : |S θ ω - S πθ ω| ≤ Real.sqrt d * w * ((2 ^ n)⁻¹ * empiricalEnvelope P Xn n L ω) := by
    simp only [hS]
    rw [← empiricalProcess_sub P Xn n (hfi θ hθ) (hfi πθ hπ)]
    have hb : ∀ x, |f θ x - f πθ x| ≤ ‖θ - πθ‖ * L x := fun x ↦ by
      rw [mul_comm]; exact hlip θ hθ πθ hπ x
    refine (abs_empiricalProcess_le P Xn n _ _ (hLi.const_mul _) hb ω).trans ?_
    change empiricalEnvelope P Xn n (fun x ↦ ‖θ - πθ‖ * L x) ω ≤ _
    rw [empiricalEnvelope_const_mul]
    have h1 := norm_sub_cubeGridPoint_cubeIndex_le a θ hw n
    have h2 := empiricalEnvelope_nonneg P Xn n hL0 ω
    calc ‖θ - πθ‖ * empiricalEnvelope P Xn n L ω
        ≤ Real.sqrt d * (w / 2 ^ n) * empiricalEnvelope P Xn n L ω := by gcongr
      _ = _ := by ring
  have htri := abs_sub_le (S θ ω) (S πθ ω) (S a ω)
  simp only [lipschitzChainRemainder] at hlt
  show Real.sqrt d * w * (2 * A + W ω) < |S πθ ω - S a ω|
  have e : Real.sqrt d * w * (2 * A + (W ω + (2 ^ n)⁻¹ * empiricalEnvelope P Xn n L ω)) =
      Real.sqrt d * w * (2 * A + W ω) +
        Real.sqrt d * w * ((2 ^ n)⁻¹ * empiricalEnvelope P Xn n L ω) := by ring
  rw [e] at hlt
  simp only [hS] at htri hres ⊢
  linarith

/-- The expectation of the empirical envelope of an integrable function is `2 √n ∫ F dP`. -/
theorem integral_empiricalEnvelope {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X) (Xn : ℕ → Ω → X)
    (hiid : IsIndependentIdenticallyDistributed μ Xn P) (n : ℕ) {F : X → ℝ} (hFm : Measurable F)
    (hF : Integrable F P) :
    Integrable (empiricalEnvelope P Xn n F) μ ∧
      ∫ ω, empiricalEnvelope P Xn n F ω ∂μ = 2 * Real.sqrt n * ∫ x, F x ∂P := by
  obtain ⟨hXm, -, hlaw⟩ := hiid
  have hi : ∀ i, Integrable (fun ω ↦ F (Xn i ω)) μ := fun i ↦ by
    have : Integrable F (μ.map (Xn i)) := by rw [hlaw i]; exact hF
    exact this.comp_measurable (hXm i)
  have he : ∀ i, ∫ ω, F (Xn i ω) ∂μ = ∫ x, F x ∂P := fun i ↦ by
    rw [← hlaw i]; exact (integral_map (hXm i).aemeasurable hFm.aestronglyMeasurable).symm
  have hint : Integrable (fun ω ↦ ∑ i ∈ Finset.range n, F (Xn i ω) + n * ∫ x, F x ∂P) μ :=
    (integrable_finsetSum _ fun i _ ↦ hi i).add (integrable_const _)
  refine ⟨hint.const_mul _, ?_⟩
  simp only [empiricalEnvelope]
  rw [integral_const_mul, integral_add (integrable_finsetSum _ fun i _ ↦ hi i)
    (integrable_const _), integral_finsetSum _ fun i _ ↦ hi i]
  simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  field_simp
  linear_combination (-2 * ∫ x, F x ∂P) * hsq

/-- The chaining remainder `lipschitzChainRemainder` of a square-integrable envelope tends to
zero in probability: its expectation is at most `(2/ε) ∫_{L > ε√n} L² + 2⁻ⁿ⁺¹ √n ∫ L`. -/
theorem tendstoInMeasure_lipschitzChainRemainder {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure X)
    [IsProbabilityMeasure P] (Xn : ℕ → Ω → X) (hiid : IsIndependentIdenticallyDistributed μ Xn P)
    (L : X → ℝ) (hLm : Measurable L) (hL0 : ∀ x, 0 ≤ L x) (hL2 : MemLp L 2 P)
    {ε : ℝ} (hε : 0 < ε) :
    TendstoInMeasure μ (fun n ω ↦ lipschitzChainRemainder P Xn L ε n ω) atTop
      (fun _ ↦ 0) := by
  have hLi : Integrable L P := hL2.integrable one_le_two
  set Lt : ℕ → X → ℝ := fun n ↦ {x | ε * Real.sqrt n < L x}.indicator L with hLt
  have hmeas : ∀ n, MeasurableSet {x | ε * Real.sqrt n < L x} := fun n ↦
    measurableSet_lt measurable_const hLm
  have hLtm : ∀ n, Measurable (Lt n) := fun n ↦ hLm.indicator (hmeas n)
  have hLti : ∀ n, Integrable (Lt n) P := fun n ↦ hLi.indicator (hmeas n)
  have hLt0 : ∀ n x, 0 ≤ Lt n x := fun n x ↦ Set.indicator_nonneg (fun x _ ↦ hL0 x) x
  have hE := fun n ↦ integral_empiricalEnvelope μ P Xn hiid n (hLtm n) (hLti n)
  have hE' := fun n ↦ integral_empiricalEnvelope μ P Xn hiid n hLm hLi
  set e : ℕ → ℝ := fun n ↦ ∫ ω, lipschitzChainRemainder P Xn L ε n ω ∂μ with he
  have heq : ∀ n, e n = 2 * (Real.sqrt n * ∫ x, Lt n x ∂P) +
      2 * ((2 ^ n)⁻¹ * Real.sqrt n) * ∫ x, L x ∂P := fun n ↦ by
    simp only [he, lipschitzChainRemainder]
    rw [integral_add (hE n).1 ((hE' n).1.const_mul _), integral_const_mul, (hE n).2, (hE' n).2]
    ring
  -- The truncated part: `√n ∫ L 1{L > ε√n} ≤ ε⁻¹ ∫ L² 1{L > ε√n} → 0`.
  have hbound : ∀ n : ℕ, Real.sqrt n * ∫ x, Lt n x ∂P ≤
      ε⁻¹ * ∫ x, {x | ε * Real.sqrt n < L x}.indicator (fun x ↦ L x ^ 2) x ∂P := fun n ↦ by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_mono ((hLti n).const_mul _)
      ((hL2.integrable_sq.indicator (hmeas n)).const_mul _) fun x ↦ ?_
    simp only [hLt]
    by_cases hx : ε * Real.sqrt n < L x
    · simp only [Set.indicator_of_mem (show x ∈ {x | ε * Real.sqrt n < L x} from hx)]
      rw [inv_mul_eq_div, le_div_iff₀ hε]
      nlinarith [hL0 x, Real.sqrt_nonneg (n : ℝ)]
    · simp [Set.indicator_of_notMem, hx]
  have hdct : Tendsto (fun n : ℕ ↦
      ∫ x, {x | ε * Real.sqrt n < L x}.indicator (fun x ↦ L x ^ 2) x ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun x ↦ L x ^ 2)
      (F := fun (n : ℕ) x ↦ {x | ε * Real.sqrt n < L x}.indicator (fun x ↦ L x ^ 2) x)
      (f := fun _ ↦ (0 : ℝ))
      (fun n ↦ ((hLm.pow_const 2).indicator (hmeas n)).aestronglyMeasurable)
      hL2.integrable_sq
      (fun n ↦ ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun x _ ↦ sq_nonneg _) x)]
        exact Set.indicator_le_self' (fun x _ ↦ sq_nonneg (L x)) x)
      (ae_of_all _ fun x ↦ by
        have hs : Tendsto (fun n : ℕ ↦ ε * Real.sqrt n) atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hs.eventually_ge_atTop (L x)] with n hn
        simp [Set.indicator_of_notMem, not_lt.2 hn])
    simpa using this
  have hgeo : Tendsto (fun n : ℕ ↦ (2 ^ n : ℝ)⁻¹ * Real.sqrt n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    rw [pow_one, inv_mul_eq_div]
    gcongr
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_one] at this
      nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ ↦ 2 * (ε⁻¹ *
        ∫ x, {x | ε * Real.sqrt n < L x}.indicator (fun x ↦ L x ^ 2) x ∂P) +
        2 * ((2 ^ n)⁻¹ * Real.sqrt n) * ∫ x, L x ∂P) atTop (𝓝 0) := by
      have := ((hdct.const_mul ε⁻¹).const_mul 2).add ((hgeo.const_mul 2).mul_const (∫ x, L x ∂P))
      simpa using this
    refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hup
    · exact integral_nonneg fun ω ↦ add_nonneg (empiricalEnvelope_nonneg P Xn n (hLt0 n) ω)
        (mul_nonneg (by positivity) (empiricalEnvelope_nonneg P Xn n hL0 ω))
    · rw [heq]
      have := hbound n
      linarith
  rw [tendstoInMeasure_iff_measureReal_lt_dist]
  intro c hc
  have hR0 : ∀ n ω, 0 ≤ lipschitzChainRemainder P Xn L ε n ω := fun n ω ↦
    add_nonneg (empiricalEnvelope_nonneg P Xn n (hLt0 n) ω)
      (mul_nonneg (by positivity) (empiricalEnvelope_nonneg P Xn n hL0 ω))
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (he0.div_const c |>.trans
    (by rw [zero_div]))
  have hint : Integrable (lipschitzChainRemainder P Xn L ε n) μ :=
    (hE n).1.add ((hE' n).1.const_mul _)
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hR0 n)) hint c
  have hsub : {ω | c < dist (lipschitzChainRemainder P Xn L ε n ω) 0} ⊆
      {ω | c ≤ lipschitzChainRemainder P Xn L ε n ω} := fun ω hω ↦ by
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (hR0 n ω)] at hω ⊢
    exact hω.le
  rw [le_div_iff₀ hc, mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _)) hc.le).trans hm

/-! ### Centred cubes and dyadic counting -/

/-- The number of grid indices of level `k` is `(2ᵏ)ᵈ`. -/
theorem card_piFinset_Ico_two_pow (d k : ℕ) :
    ((Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) (2 ^ k)).card : ℝ) = (2 ^ k) ^ d := by
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Ico, sub_zero]
  have : ((2 : ℤ) ^ k).toNat = 2 ^ k := by
    rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  rw [this]
  push_cast
  ring

/-- `2 ∑_{j<n} qʲ⁺¹ ≤ 4 q` for `0 ≤ q ≤ 1/2`. -/
theorem two_mul_sum_range_pow_succ_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (n : ℕ) :
    2 * ∑ j ∈ Finset.range n, q ^ (j + 1) ≤ 4 * q := by
  have h : ∑ j ∈ Finset.range n, q ^ (j + 1) = q * ∑ j ∈ Finset.range n, q ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hq1 : q < 1 := by linarith
  have hg : ∑ j ∈ Finset.range n, q ^ j ≤ 2 := by
    rw [geom_sum_eq hq1.ne, div_le_iff_of_neg (by linarith)]
    have := pow_nonneg hq0 n
    nlinarith
  rw [h]
  nlinarith

/-- Scaling a half-open cube: if `h ∈ ∏ [uᵢ, uᵢ + w)` and `c > 0`, then
`θ₀ + c h ∈ ∏ [θ₀ᵢ + c uᵢ, θ₀ᵢ + c uᵢ + c w)`. -/
theorem add_smul_mem_halfOpenCube {d : ℕ} {u h : EuclideanSpace ℝ (Fin d)} {w : ℝ}
    (hh : h ∈ halfOpenCube u w) (θ₀ : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 < c) :
    θ₀ + c • h ∈ halfOpenCube (θ₀ + c • u) (c * w) := by
  intro i
  obtain ⟨h1, h2⟩ := hh i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> nlinarith

/-- The half-open cube `∏ᵢ [θ₀ᵢ - ρ, θ₀ᵢ + ρ)` centred at `θ₀`. -/
def centredCube {d : ℕ} (θ₀ : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  halfOpenCube (θ₀ - WithLp.toLp 2 fun _ ↦ ρ) (2 * ρ)

/-- Points within `ρ` of `θ₀` lie in the centred cube of half-width `ρ`. -/
theorem mem_centredCube_of_norm_sub_lt {d : ℕ} {θ₀ θ : EuclideanSpace ℝ (Fin d)} {ρ : ℝ}
    (h : ‖θ - θ₀‖ < ρ) : θ ∈ centredCube θ₀ ρ := by
  intro i
  have := (PiLp.norm_apply_le (θ - θ₀) i).trans_lt h
  rw [PiLp.sub_apply, Real.norm_eq_abs, abs_lt] at this
  constructor <;> simp only [PiLp.sub_apply] <;> linarith

/-- Points of the centred cube of half-width `ρ` lie within `√d ρ` of the centre. -/
theorem norm_sub_le_of_mem_centredCube {d : ℕ} {θ₀ θ : EuclideanSpace ℝ (Fin d)} {ρ : ℝ}
    (h : θ ∈ centredCube θ₀ ρ) : ‖θ - θ₀‖ ≤ Real.sqrt d * ρ := by
  refine norm_le_sqrt_card_mul_of_abs_le _ fun i ↦ ?_
  obtain ⟨h1, h2⟩ := h i
  simp only [PiLp.sub_apply] at h1 h2 ⊢
  rw [abs_le]; constructor <;> linarith

/-- `xᵈ e^{-a x}` along `x = 2ᵏ` tends to zero for `a > 0`. -/
theorem tendsto_two_pow_pow_mul_exp_neg {a : ℝ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun k : ℕ ↦ ((2 : ℝ) ^ k) ^ d * Real.exp (-(a * 2 ^ k))) atTop (𝓝 0) := by
  have h2 : Tendsto (fun k : ℕ ↦ a * (2 : ℝ) ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop ha
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp h2).const_mul (a⁻¹ ^ d)
  rw [mul_zero] at h
  refine h.congr fun k ↦ ?_
  simp only [Function.comp, mul_pow, ← mul_assoc]
  rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_mul]

end CKSD
