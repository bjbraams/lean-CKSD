module

public import CKSD.Asymptotics.LikelihoodSupport


/-!
# Lipschitz empirical processes and Z-estimator normality

An elementary dyadic chaining estimate controls the centered empirical process of a scalar
Lipschitz parameter family. It yields stochastic equicontinuity and the asymptotically linear
expansion and normal limit of a consistent approximate estimating-equation root.
Sources: GAPS 102.4 and van der Vaart, *Asymptotic Statistics*, Theorem 5.21. The argument uses
Chebyshev's inequality and the convergence adapters in `CKSD.Asymptotics.Basic`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Square integrability of a parameter family with a square-integrable Lipschitz envelope, at
parameters within the Lipschitz radius. -/
theorem mem_lp_two_of_lipschitz_envelope {E : Type*} [MeasurableSpace E] (P : Measure E)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) :
    MemLp (fun x ↦ psi a x - psi b x) 2 P ∧ MemLp (psi a) 2 P ∧
      ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ (∫ x, M x ^ 2 ∂P) * (a - b) ^ 2 := by
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  have h0 : |theta₀ - theta₀| < r := by simpa using hr
  have hd : ∀ a b, |a - theta₀| < r → |b - theta₀| < r →
      MemLp (fun x ↦ psi a x - psi b x) 2 P := fun a b ha hb ↦ by
    refine (hM.const_mul |a - b|).of_le ((hmeas a).sub (hmeas b)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    have := hlip x a b ha hb
    have := le_abs_self (M x)
    nlinarith [abs_nonneg (a - b)]
  refine ⟨hd a b ha hb, ?_, ?_⟩
  · have := (hd a theta₀ ha h0).add hpsi
    convert this using 1
    ext x; simp
  · have hab := hd a b ha hb
    calc ∫ x, (psi a x - psi b x) ^ 2 ∂P ≤ ∫ x, M x ^ 2 * (a - b) ^ 2 ∂P := by
          refine integral_mono hab.integrable_sq (hM.integrable_sq.mul_const _) fun x ↦ ?_
          have h1 := hlip x a b ha hb
          have h2 : 0 ≤ |psi a x - psi b x| := abs_nonneg _
          have : (psi a x - psi b x) ^ 2 ≤ (M x * |a - b|) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ h2 h1 2
          simpa [mul_pow, sq_abs] using this
      _ = _ := integral_mul_const _ _

/-- Chebyshev's inequality for the increments of the centred partial-sum process of a parameter
family with a square-integrable Lipschitz envelope. -/
theorem measure_real_le_abs_centred_sum_sub_le {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (n : ℕ) (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |(∑ i ∈ Finset.range n, psi a (X i ω) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (X i ω) - n * ∫ x, psi b x ∂P)|} ≤
      n * (∫ x, M x ^ 2 ∂P) * (a - b) ^ 2 / c ^ 2 := by
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hd, ha2, hK⟩ := mem_lp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    a b ha hb
  have hb2 := (mem_lp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    b a hb ha).2.1
  have hcheb := measure_real_le_abs_sum_sub_le_of_iid μ P X hiid _ ((hmeas a).sub (hmeas b))
    hd n hc
  have hint : ∫ x, (psi a x - psi b x) ∂P = ∫ x, psi a x ∂P - ∫ x, psi b x ∂P :=
    integral_sub (ha2.integrable one_le_two) (hb2.integrable one_le_two)
  have hset : {ω | c ≤ |(∑ i ∈ Finset.range n, psi a (X i ω) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (X i ω) - n * ∫ x, psi b x ∂P)|} =
      {ω | c ≤ |∑ i ∈ Finset.range n, (psi a (X i ω) - psi b (X i ω)) -
        n * ∫ x, (psi a x - psi b x) ∂P|} := by
    ext ω
    simp only [mem_ofPred_eq, hint, Finset.sum_sub_distrib]
    ring_nf
  rw [hset]
  refine hcheb.trans ?_
  simp only [Pi.sub_apply]
  rw [mul_assoc]
  gcongr

/-- Deterministic Lipschitz bound for the increments of the centred partial-sum process. -/
theorem abs_centred_sum_sub_le {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P]
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (n : ℕ) (y : ℕ → E) (a b : ℝ) (ha : |a - theta₀| < r) (hb : |b - theta₀| < r) :
    |(∑ i ∈ Finset.range n, psi a (y i) - n * ∫ x, psi a x ∂P) -
      (∑ i ∈ Finset.range n, psi b (y i) - n * ∫ x, psi b x ∂P)| ≤
      |a - b| * (∑ i ∈ Finset.range n, M (y i) + n * ∫ x, M x ∂P) := by
  have ha2 := (mem_lp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    a b ha hb).2.1
  have hb2 := (mem_lp_two_of_lipschitz_envelope P psi hm theta₀ r hr M hM hpsi hlip
    b a hb ha).2.1
  have hMi : Integrable M P := hM.integrable one_le_two
  have hI : |∫ x, psi a x ∂P - ∫ x, psi b x ∂P| ≤ |a - b| * ∫ x, M x ∂P := by
    rw [← integral_sub (ha2.integrable one_le_two) (hb2.integrable one_le_two),
      ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      ((ha2.integrable one_le_two).sub (hb2.integrable one_le_two)).abs
      (hMi.const_mul _) fun x ↦ ?_)
    have := hlip x a b ha hb
    simp only
    linarith [mul_comm (M x) |a - b|]
  have hS : |∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)| ≤
      |a - b| * ∑ i ∈ Finset.range n, M (y i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    linarith [hlip (y i) a b ha hb, mul_comm (M (y i)) |a - b|]
  calc _ = |(∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)) -
        n * (∫ x, psi a x ∂P - ∫ x, psi b x ∂P)| := by ring_nf
    _ ≤ |∑ i ∈ Finset.range n, psi a (y i) - ∑ i ∈ Finset.range n, psi b (y i)| +
        |(n : ℝ) * (∫ x, psi a x ∂P - ∫ x, psi b x ∂P)| := abs_sub _ _
    _ ≤ |a - b| * ∑ i ∈ Finset.range n, M (y i) + n * (|a - b| * ∫ x, M x ∂P) := by
        rw [abs_mul, Nat.abs_cast]
        gcongr
    _ = _ := by ring

/-- The left endpoint of the dyadic cell of level `j`, of width `δ / 2 ^ j`, containing `t` in the
grid anchored at `θ₀`. -/
def dyadicGridPoint (θ₀ δ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  θ₀ + ⌊(t - θ₀) * 2 ^ j / δ⌋ * (δ / 2 ^ j)

/-- The dyadic cell index of a point within `δ` of the anchor lies in `[-2 ^ j, 2 ^ j)`. -/
theorem dyadic_grid_point_index_mem {θ₀ δ t : ℝ} (hδ : 0 < δ) (ht : |t - θ₀| < δ) (j : ℕ) :
    ⌊(t - θ₀) * 2 ^ j / δ⌋ ∈ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j) := by
  rw [abs_lt] at ht
  have h1 : -1 < (t - θ₀) / δ := by rw [lt_div_iff₀ hδ]; linarith
  have h2 : (t - θ₀) / δ < 1 := by rw [div_lt_one hδ]; linarith
  have hx : (t - θ₀) * 2 ^ j / δ = (t - θ₀) / δ * 2 ^ j := by ring
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  rw [Finset.mem_Ico, Int.le_floor, Int.floor_lt, hx]
  push_cast
  constructor <;> nlinarith

/-- A dyadic grid point lies within `δ` of the anchor, as does the midpoint of its cell. -/
theorem abs_dyadic_sub_le {θ₀ δ : ℝ} (hδ : 0 < δ) {j : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j)) :
    |θ₀ + k * (δ / 2 ^ j) - θ₀| ≤ δ ∧ |θ₀ + k * (δ / 2 ^ j) + δ / 2 ^ j / 2 - θ₀| ≤ δ := by
  rw [Finset.mem_Ico] at hk
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : -(2 : ℝ) ^ j ≤ k := by exact_mod_cast hk.1
  have h2 : (k : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast (Int.add_one_le_iff.2 hk.2)
  have hh : 0 < δ / 2 ^ j := div_pos hδ hp
  have e : (2 : ℝ) ^ j * (δ / 2 ^ j) = δ := by field_simp
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

/-- A point is within one cell width of its dyadic grid point. -/
theorem abs_sub_dyadic_grid_point_le {θ₀ δ : ℝ} (hδ : 0 < δ) (j : ℕ) (t : ℝ) :
    |t - dyadicGridPoint θ₀ δ j t| ≤ δ / 2 ^ j := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hh : 0 < δ / 2 ^ j := div_pos hδ hp
  set x := (t - θ₀) * 2 ^ j / δ
  have hx : t - θ₀ = x * (δ / 2 ^ j) := by simp only [x]; field_simp
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold dyadicGridPoint
  rw [abs_le]
  constructor <;> nlinarith

/-- Consecutive dyadic levels: the finer grid point is the coarser one or the midpoint of its
cell. -/
theorem dyadic_grid_point_succ (θ₀ δ : ℝ) (j : ℕ) (t : ℝ) :
    dyadicGridPoint θ₀ δ (j + 1) t = dyadicGridPoint θ₀ δ j t ∨
      dyadicGridPoint θ₀ δ (j + 1) t = dyadicGridPoint θ₀ δ j t + δ / 2 ^ j / 2 := by
  set x := (t - θ₀) * 2 ^ j / δ with hxdef
  have hx2 : (t - θ₀) * 2 ^ (j + 1) / δ = 2 * x := by rw [hxdef, pow_succ]; ring
  have hw : δ / 2 ^ (j + 1) = δ / 2 ^ j / 2 := by rw [pow_succ, div_div]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hk1 : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hk2 : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by rw [Int.floor_lt]; push_cast; linarith
  unfold dyadicGridPoint
  rw [hx2, hw, ← hxdef]
  rcases (by omega : ⌊2 * x⌋ = 2 * ⌊x⌋ ∨ ⌊2 * x⌋ = 2 * ⌊x⌋ + 1) with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring

/-- The level-zero dyadic grid point of a point within `δ` of the anchor is `θ₀ - δ` or `θ₀`. -/
theorem dyadic_grid_point_zero {θ₀ δ t : ℝ} (hδ : 0 < δ) (ht : |t - θ₀| < δ) :
    dyadicGridPoint θ₀ δ 0 t = θ₀ - δ ∨ dyadicGridPoint θ₀ δ 0 t = θ₀ := by
  have hk := dyadic_grid_point_index_mem hδ ht 0
  simp only [pow_zero, mul_one, Finset.mem_Ico] at hk
  unfold dyadicGridPoint
  simp only [pow_zero, mul_one, div_one]
  rcases (by omega : ⌊(t - θ₀) / δ⌋ = -1 ∨ ⌊(t - θ₀) / δ⌋ = 0) with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; simp

/-- Dyadic chaining bound: if the increments of a real process indexed by `[θ₀ - δ, θ₀ + δ]`
satisfy the Chebyshev bound `P(c ≤ |S a - S b|) ≤ L (a - b)² / c²`, then for any random
parameter `t` the process at the dyadic grid point of `t` of any level stays within `c` of its value
at `θ₀`, except on an event of probability at most `300 L δ² / c²` or where `|t - θ₀| ≥ δ`. -/
theorem measure_real_dyadic_chain_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : ℝ → Ω → ℝ) (θ₀ δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hS : ∀ a b, |a - θ₀| ≤ δ → |b - θ₀| ≤ δ → ∀ c, 0 < c →
      μ.real {ω | c ≤ |S a ω - S b ω|} ≤ L * (a - b) ^ 2 / c ^ 2)
    (t : Ω → ℝ) (J : ℕ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | |t ω - θ₀| < δ ∧ c ≤ |S (dyadicGridPoint θ₀ δ J (t ω)) ω - S θ₀ ω|} ≤
      300 * L * δ ^ 2 / c ^ 2 := by
  set thr : ℕ → ℝ := fun j ↦ c * (3 / 4) ^ j / 8 with hthr
  have hthr0 : ∀ j, 0 < thr j := fun j ↦ by simp only [hthr]; positivity
  set I : ℕ → Finset ℤ := fun j ↦ Finset.Ico (-(2 : ℤ) ^ j) (2 ^ j) with hI
  set B : ℕ → ℤ → Set Ω := fun j k ↦ {ω | thr j ≤
    |S (θ₀ + k * (δ / 2 ^ j) + δ / 2 ^ j / 2) ω - S (θ₀ + k * (δ / 2 ^ j)) ω|} with hB
  set A0 : Set Ω := {ω | c / 2 ≤ |S (θ₀ - δ) ω - S θ₀ ω|} with hA0
  have hgeo1 : ∑ j ∈ Finset.range J, thr j ≤ c / 2 := by
    have hg := geom_sum_eq (x := (3 / 4 : ℝ)) (by norm_num) J
    have hp : 0 ≤ (3 / 4 : ℝ) ^ J := by positivity
    have : ∑ j ∈ Finset.range J, thr j = c / 8 * ∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_; simp only [hthr]; ring
    rw [this, hg]
    have : ((3 / 4 : ℝ) ^ J - 1) / (3 / 4 - 1) ≤ 4 := by
      rw [div_le_iff_of_neg (by norm_num)]; linarith
    nlinarith
  have hsub : {ω | |t ω - θ₀| < δ ∧ c ≤ |S (dyadicGridPoint θ₀ δ J (t ω)) ω - S θ₀ ω|} ⊆
      A0 ∪ ⋃ j ∈ Finset.range J, ⋃ k ∈ I j, B j k := by
    rintro ω ⟨h1, h2⟩
    by_contra hn
    simp only [mem_union, mem_iUnion, not_or, not_exists, hA0, hB, mem_ofPred_eq, not_le,
      Finset.mem_range] at hn
    obtain ⟨hA, hBn⟩ := hn
    set π : ℕ → ℝ := fun j ↦ dyadicGridPoint θ₀ δ j (t ω) with hπ
    have h0 : |S (π 0) ω - S θ₀ ω| < c / 2 := by
      rcases dyadic_grid_point_zero hδ h1 with h | h
      · simpa [hπ, h] using hA
      · simp only [hπ, h, sub_self, abs_zero]; positivity
    have hstep : ∀ j < J, |S (π (j + 1)) ω - S (π j) ω| < thr j := fun j hj ↦ by
      rcases dyadic_grid_point_succ θ₀ δ j (t ω) with h | h
      · simp only [hπ, h, sub_self, abs_zero]; exact hthr0 j
      · have := hBn j hj _ (dyadic_grid_point_index_mem hδ h1 j)
        simp only [hπ, h]
        exact this
    have htel : S (π J) ω - S θ₀ ω = (S (π 0) ω - S θ₀ ω) +
        ∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω) := by
      rw [Finset.sum_range_sub (fun j ↦ S (π j) ω)]; ring
    have hsum : |∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω)| ≤
        ∑ j ∈ Finset.range J, thr j :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj ↦
        (hstep j (Finset.mem_range.1 hj)).le)
    have := abs_add_le (S (π 0) ω - S θ₀ ω)
      (∑ j ∈ Finset.range J, (S (π (j + 1)) ω - S (π j) ω))
    rw [← htel] at this
    simp only [hπ] at this h2 h0
    linarith
  have hcardI : ∀ j, ((I j).card : ℝ) = 2 * 2 ^ j := fun j ↦ by
    simp only [hI, Int.card_Ico]
    have : ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) := by push_cast; ring
    rw [this, show ((2 ^ j : ℕ) : ℤ) - -((2 ^ j : ℕ) : ℤ) = ((2 * 2 ^ j : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  have hBj : ∀ j, ∑ k ∈ I j, μ.real (B j k) ≤ 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
    intro j
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hw : (0 : ℝ) < (3 / 4) ^ j := by positivity
    have hrel : (8 / 9 : ℝ) ^ j = (2 ^ j * ((3 / 4) ^ j) ^ 2)⁻¹ := by
      rw [← pow_mul, show j * 2 = 2 * j by ring, pow_mul, ← mul_pow, ← inv_pow]
      norm_num
    calc ∑ k ∈ I j, μ.real (B j k)
        ≤ ∑ _k ∈ I j, L * (δ / 2 ^ j / 2) ^ 2 / thr j ^ 2 := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          obtain ⟨ha, hb⟩ := abs_dyadic_sub_le (θ₀ := θ₀) hδ hk
          have := hS _ _ hb ha (thr j) (hthr0 j)
          simp only [hB]
          refine this.trans (le_of_eq ?_)
          ring
      _ = 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardI, hrel]
          simp only [hthr]
          field_simp
          ring
  have hgeo2 : ∑ j ∈ Finset.range J, (8 / 9 : ℝ) ^ j ≤ 9 := by
    rw [geom_sum_eq (by norm_num)]
    have hp : 0 ≤ (8 / 9 : ℝ) ^ J := by positivity
    rw [div_le_iff_of_neg (by norm_num)]; linarith
  have hK : 0 ≤ 32 * L * δ ^ 2 / c ^ 2 := by positivity
  calc _ ≤ μ.real (A0 ∪ ⋃ j ∈ Finset.range J, ⋃ k ∈ I j, B j k) := measureReal_mono hsub
    _ ≤ μ.real A0 + ∑ j ∈ Finset.range J, ∑ k ∈ I j, μ.real (B j k) := by
        refine (measureReal_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        exact measureReal_biUnion_finset_le _ _
    _ ≤ L * (θ₀ - δ - θ₀) ^ 2 / (c / 2) ^ 2 +
        ∑ j ∈ Finset.range J, 32 * L * δ ^ 2 / c ^ 2 * (8 / 9) ^ j := by
        gcongr with j
        · exact hS _ _ (by simp [abs_of_pos hδ]) (by simp [hδ.le]) _ (half_pos hc)
        · exact hBj j
    _ ≤ 4 * L * δ ^ 2 / c ^ 2 + 32 * L * δ ^ 2 / c ^ 2 * 9 := by
        have e : L * (θ₀ - δ - θ₀) ^ 2 / (c / 2) ^ 2 = 4 * L * δ ^ 2 / c ^ 2 := by
          field_simp; ring
        rw [e, ← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeo2 hK)
    _ ≤ 300 * L * δ ^ 2 / c ^ 2 := by
        have : 0 ≤ L * δ ^ 2 / c ^ 2 := by positivity
        have e1 : 4 * L * δ ^ 2 / c ^ 2 = 4 * (L * δ ^ 2 / c ^ 2) := by ring
        have e2 : 32 * L * δ ^ 2 / c ^ 2 * 9 = 288 * (L * δ ^ 2 / c ^ 2) := by ring
        have e3 : 300 * L * δ ^ 2 / c ^ 2 = 300 * (L * δ ^ 2 / c ^ 2) := by ring
        rw [e1, e2, e3]; linarith

/-- Stochastic equicontinuity of the empirical process of a scalar parameter family with a
square-integrable Lipschitz envelope: evaluated at a consistent random parameter `Tₙ`, the
normalised centred partial-sum increment `n^{-1/2} ∑ᵢ (ψ_{Tₙ} - ψ_{θ₀})(Xᵢ) - √n (P ψ_{Tₙ} - P ψ_{θ₀})`
tends to `0` in probability. The proof is a dyadic chaining argument with Chebyshev's inequality
at each level. -/
theorem tendsto_in_measure_centred_sum_sub_of_lipschitz {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure E)
    [IsProbabilityMeasure P] (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed μ X P)
    (psi : ℝ → E → ℝ) (hm : Measurable (Function.uncurry psi)) (theta₀ r : ℝ) (hr : 0 < r)
    (M : E → ℝ) (hM : MemLp M 2 P) (hpsi : MemLp (psi theta₀) 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hcons : TendstoInMeasure μ T atTop (fun _ ↦ theta₀)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P)))
            atTop (fun _ ↦ 0) := by
  obtain ⟨hXm, hind, hlaw⟩ := hiid
  have hiid : IsIndependentIdenticallyDistributed μ X P := ⟨hXm, hind, hlaw⟩
  set S : ℕ → ℝ → Ω → ℝ := fun n θ ω ↦
    ∑ i ∈ Finset.range n, psi θ (X i ω) - n * ∫ x, psi θ x ∂P with hSdef
  set K : ℝ := ∫ x, M x ^ 2 ∂P with hK
  have hK0 : 0 ≤ K := integral_nonneg fun x ↦ sq_nonneg _
  have hMnn : ∀ x, 0 ≤ M x := fun x ↦ by
    have h := hlip x theta₀ (theta₀ + r / 2) (by simpa using hr)
      (by rw [add_sub_cancel_left, abs_of_pos (half_pos hr)]; linarith)
    have hp : 0 < |theta₀ - (theta₀ + r / 2)| := by
      rw [abs_pos]; linarith
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hp
    linarith [abs_nonneg (psi theta₀ x - psi (theta₀ + r / 2) x)]
  set M' : E → ℝ := hM.aestronglyMeasurable.mk M with hM'def
  have hM'm : Measurable M' := hM.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMM' : M =ᵐ[P] M' := hM.aestronglyMeasurable.ae_eq_mk
  have hMi : Integrable M P := hM.integrable one_le_two
  have hM'i : Integrable M' P := hMi.congr hMM'
  have hMae : ∀ᵐ w ∂μ, ∀ i, M (X i w) = M' (X i w) := by
    rw [ae_all_iff]
    intro i
    have : ∀ᵐ x ∂(μ.map (X i)), M x = M' x := by rw [hlaw i]; exact hMM'
    exact ae_of_ae_map (hXm i).aemeasurable this
  set G : Set Ω := {w | ∀ i, M (X i w) = M' (X i w)} with hG
  have hGc : μ.real Gᶜ = 0 := by
    rw [measureReal_def, hG, compl_ofPred, ae_iff.mp hMae, ENNReal.toReal_zero]
  set s : E → ℝ := fun x ↦ M' x + ∫ y, M y ∂P with hs
  have hsm : Measurable s := hM'm.add measurable_const
  set V : ℕ → Ω → ℝ := fun n w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, s (X i w) with hV
  have hVb : IsBoundedInProbability μ V :=
    is_bounded_in_probability_of_tendsto_in_measure μ V _
      (tendsto_in_measure_sample_mean_of_iid μ P X hiid s hsm
        (hM'i.add (integrable_const _)))
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at hcons ⊢
  intro ε hε
  refine tendsto_zero_of_forall_eventually_le (fun n ↦ measureReal_nonneg) fun η hη ↦ ?_
  have htδ : Tendsto (fun δ : ℝ ↦ 1200 * K * δ ^ 2 / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun δ : ℝ ↦ 1200 * K * δ ^ 2 / ε ^ 2) := by fun_prop
    have h := this.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hδη, hδ0, hδr⟩ :=
    ((htδ.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3))).and
      (Ioo_mem_nhdsGT hr)).exists
  set u : ℕ → ℝ := fun n ↦ δ * Real.sqrt n / 2 ^ n with hu
  have hulim : Tendsto u atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)).const_mul δ
    rw [mul_zero] at h1
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) h1
    simp only [hu, pow_one]
    rw [mul_div_assoc]
    gcongr
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_one] at this
      nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)]
  have hR := tendsto_in_measure_mul_zero_of_is_bounded_in_probability μ V (fun n _ ↦ u n) hVb
    (tendsto_in_measure_const_of_tendsto μ u hulim)
  rw [tendsto_in_measure_iff_measure_real_lt_dist] at hR
  filter_upwards [eventually_ge_atTop 1,
    (hcons (δ / 2) (half_pos hδ0)).eventually (eventually_le_nhds (by positivity : 0 < η / 3)),
    (hR (ε / 4) (by positivity)).eventually (eventually_le_nhds (by positivity : 0 < η / 3))]
    with n hn1 hn2 hn3
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc : 0 < ε * Real.sqrt n / 2 := by positivity
  have hchain := measure_real_dyadic_chain_le μ (S n) theta₀ δ (n * K) hδ0 (by positivity)
    (fun a b ha hb c hc ↦ measure_real_le_abs_centred_sum_sub_le μ P X hiid psi hm theta₀ r hr M hM
      hpsi hlip n a b (by linarith) (by linarith) hc) (T n) n hc
  have hcb : 300 * (n * K) * δ ^ 2 / (ε * Real.sqrt n / 2) ^ 2 = 1200 * K * δ ^ 2 / ε ^ 2 := by
    rw [div_pow, mul_pow, hsq]
    field_simp
    ring
  rw [hcb] at hchain
  have hsub : {ω | ε < dist ((Real.sqrt n)⁻¹ *
      ((∑ i ∈ Finset.range n, psi (T n ω) (X i ω) - n * ∫ x, psi (T n ω) x ∂P) -
        (∑ i ∈ Finset.range n, psi theta₀ (X i ω) - n * ∫ x, psi theta₀ x ∂P))) 0} ⊆
      (({ω | δ / 2 < dist (T n ω) theta₀} ∪
        {ω | |T n ω - theta₀| < δ ∧
          ε * Real.sqrt n / 2 ≤ |S n (dyadicGridPoint theta₀ δ n (T n ω)) ω - S n theta₀ ω|}) ∪
        {ω | ε / 4 < dist (V n ω * u n) 0}) ∪ Gᶜ := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, not_or, not_lt, not_and, not_le,
      not_not] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    rw [Real.dist_eq] at h1
    have hT : |T n ω - theta₀| < δ := by linarith
    have h2 := h2 hT
    simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul, abs_inv,
      abs_of_pos hsqn] at hω
    rw [Real.dist_eq, sub_zero] at h3
    set πT := dyadicGridPoint theta₀ δ n (T n ω)
    have hπ : |πT - theta₀| ≤ δ :=
      (abs_dyadic_sub_le (θ₀ := theta₀) hδ0 (dyadic_grid_point_index_mem hδ0 hT n)).1
    have hres := abs_centred_sum_sub_le P psi hm theta₀ r hr M hM hpsi hlip n (fun i ↦ X i ω)
      (T n ω) πT (by linarith) (by linarith)
    have hQ : 0 ≤ ∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P :=
      add_nonneg (Finset.sum_nonneg fun i _ ↦ hMnn _)
        (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg hMnn))
    have hd := abs_sub_dyadic_grid_point_le (θ₀ := theta₀) hδ0 n (T n ω)
    have hVu : δ / 2 ^ n * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P) =
        Real.sqrt n * (V n ω * u n) := by
      have h4' : ∀ i, M (X i ω) = M' (X i ω) := h4
      rw [Finset.sum_congr rfl fun i _ ↦ h4' i]
      simp only [hV, hu, hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      rw [hsq]; ring
    have hres' : |S n (T n ω) ω - S n πT ω| ≤ Real.sqrt n * (ε / 4) := by
      refine hres.trans ?_
      calc |T n ω - πT| * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P)
          ≤ δ / 2 ^ n * (∑ i ∈ Finset.range n, M (X i ω) + n * ∫ x, M x ∂P) := by gcongr
        _ = Real.sqrt n * (V n ω * u n) := hVu
        _ ≤ Real.sqrt n * |V n ω * u n| := by gcongr; exact le_abs_self _
        _ ≤ Real.sqrt n * (ε / 4) := by gcongr
    have htri := abs_sub_le (S n (T n ω) ω) (S n πT ω) (S n theta₀ ω)
    have hω' : ε * Real.sqrt n < |S n (T n ω) ω - S n theta₀ ω| := by
      rw [inv_mul_eq_div, lt_div_iff₀ hsqn] at hω
      exact hω
    nlinarith
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ η / 3 + 1200 * K * δ ^ 2 / ε ^ 2 + η / 3 + μ.real Gᶜ := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ hn3)
        exact (measureReal_union_le _ _).trans (add_le_add hn2 hchain)
    _ ≤ η := by rw [hGc]; linarith

/-- GAPS 102.4, the scalar Z-estimator theorem under a square-integrable Lipschitz envelope. -/
theorem z_estimator_asymptotic_linearization_and_normality
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (P : Measure E) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (hiid : IsIndependentIdenticallyDistributed mu X P) (psi : ℝ → E → ℝ)
    (hm : Measurable (Function.uncurry psi)) (theta₀ D : ℝ) (hD : D ≠ 0)
    (hpsi : MemLp (psi theta₀) 2 P) (h0 : (∫ x, psi theta₀ x ∂P) = 0)
    (hd : HasDerivAt (fun theta ↦ ∫ x, psi theta x ∂P) D theta₀)
    (r : ℝ) (hr : 0 < r) (M : E → ℝ) (hM : MemLp M 2 P)
    (hlip : ∀ x a b, |a - theta₀| < r → |b - theta₀| < r →
      |psi a x - psi b x| ≤ M x * |a - b|)
    (T : ℕ → Ω → ℝ) (hT : ∀ n, Measurable (T n))
    (hcons : TendstoInMeasure mu T atTop (fun _ ↦ theta₀))
    (hroot : TendstoInMeasure mu (fun (n : ℕ) w ↦ (Real.sqrt n)⁻¹ *
      ∑ i ∈ Finset.range n, psi (T n w) (X i w)) atTop (fun _ ↦ 0)) :
    TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) atTop (fun _ ↦ 0) ∧
      TendstoInDistribution (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀)) atTop id (fun _ ↦ mu)
        (gaussianReal 0 (Real.toNNReal (Var[psi theta₀; P] / D ^ 2))) := by
  have hXm := hiid.1
  have hmeas : ∀ t, Measurable (psi t) := fun t ↦
    hm.comp (measurable_const.prodMk measurable_id)
  set F : ℝ → ℝ := fun θ ↦ ∫ x, psi θ x ∂P with hF
  set Z : ℕ → Ω → ℝ := fun n w ↦ (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)
    with hZ
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    (Finset.measurable_fun_sum _ fun i _ ↦ (hmeas theta₀).comp (hXm i)).const_mul _
  have hZlim : TendstoInDistribution Z atTop id (fun _ ↦ mu)
      (gaussianReal 0 (Real.toNNReal (∫ x, psi theta₀ x ^ 2 ∂P))) :=
    tendsto_in_distribution_inv_sqrt_mul_sum_of_iid mu P X hiid _ (hmeas theta₀) hpsi h0
  have hZb : IsBoundedInProbability mu Z :=
    is_bounded_in_probability_of_tendsto_in_distribution mu Z hZlim
  have hsn : ∀ n : ℕ, (Real.sqrt n)⁻¹ * n = Real.sqrt n := fun n ↦ by
    rw [inv_mul_eq_div, Real.div_sqrt]
  have hSE := tendsto_in_measure_centred_sum_sub_of_lipschitz mu P X hiid psi hm theta₀ r hr
    M hM hpsi hlip T hcons
  -- `√n F(Tₙ) + Zₙ → 0`
  have hE1 : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * F (T n w) + Z n w)
      atTop (fun _ ↦ 0) := by
    have := tendsto_in_measure_add_zero mu _ _ hroot
      (tendsto_in_measure_const_mul_zero mu _ (-1) hSE)
    convert this using 3 with n w
    simp only [hZ, hF]
    rw [h0]
    first
      | linear_combination (∫ x, psi (T n w) x ∂P) * hsn n
      | linear_combination (-(∫ x, psi (T n w) x ∂P)) * hsn n
  set ρ : ℝ → ℝ := Function.update (fun t ↦ slope F theta₀ t - D) theta₀ 0 with hρ
  have hρc : ContinuousAt ρ theta₀ := by
    rw [hρ, continuousAt_update_same]
    have := (hasDerivAt_iff_tendsto_slope.1 hd).sub_const D
    simpa using this
  have hρ0 : ρ theta₀ = 0 := by simp [hρ]
  have hρT : TendstoInMeasure mu (fun (n : ℕ) w ↦ ρ (T n w)) atTop (fun _ ↦ 0) := by
    have := tendsto_in_measure_comp_of_continuous_at mu T theta₀ ρ hρc hcons
    rwa [hρ0] at this
  set W : ℕ → Ω → ℝ := fun n w ↦ Real.sqrt n * (T n w - theta₀) with hW
  have hF0 : F theta₀ = 0 := h0
  have hid : ∀ (n : ℕ) (w : Ω), Real.sqrt n * F (T n w) = D * W n w + W n w * ρ (T n w) := fun n w ↦ by
    by_cases h : T n w = theta₀
    · simp [hW, h, hF0]
    · have : ρ (T n w) = (T n w - theta₀)⁻¹ * (F (T n w) - F theta₀) - D := by
        rw [hρ, Function.update_of_ne h]
        simp [slope_def_field, div_eq_inv_mul]
      rw [this, hF0, sub_zero]
      have hne : T n w - theta₀ ≠ 0 := sub_ne_zero.2 h
      simp only [hW]
      field_simp
      ring
  set Ev : ℕ → Ω → ℝ := fun n w ↦ D * W n w + W n w * ρ (T n w) + Z n w with hEv
  have hE : TendstoInMeasure mu Ev atTop (fun _ ↦ 0) := by
    convert hE1 using 3 with n w
    simp only [hEv]
    rw [hid]
  have hWb : IsBoundedInProbability mu W := by
    rw [tendsto_in_measure_iff_measure_real_lt_dist] at hE hρT
    intro ε hε
    obtain ⟨C₁, hC₁, hZev⟩ := hZb (ε / 3) (by positivity)
    have hDp : 0 < |D| := abs_pos.2 hD
    refine ⟨2 * (1 + C₁) / |D|, by positivity, ?_⟩
    filter_upwards [hZev, (hE 1 one_pos).eventually (eventually_le_nhds (by positivity :
      0 < ε / 3)), (hρT (|D| / 4) (by positivity)).eventually (eventually_le_nhds (by positivity :
      0 < ε / 3))] with n h1 h2 h3
    have hsub : {w | 2 * (1 + C₁) / |D| < |W n w|} ⊆
        ({w | C₁ < |Z n w|} ∪ {w | 1 < dist (Ev n w) 0}) ∪
          {w | |D| / 4 < dist (ρ (T n w)) 0} := by
      intro w hw
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt, Real.dist_eq, sub_zero] at hcon hw
      obtain ⟨⟨c1, c2⟩, c3⟩ := hcon
      have hfac : W n w * (D + ρ (T n w)) = Ev n w - Z n w := by simp only [hEv]; ring
      have hlow : 3 * |D| / 4 ≤ |D + ρ (T n w)| := by
        have := abs_sub_abs_le_abs_sub D (-ρ (T n w))
        rw [sub_neg_eq_add, abs_neg] at this
        linarith
      have hup : |W n w| * |D + ρ (T n w)| ≤ 1 + C₁ := by
        rw [← abs_mul, hfac]
        exact (abs_sub _ _).trans (by linarith)
      have hW0 := abs_nonneg (W n w)
      rw [div_lt_iff₀ hDp] at hw
      nlinarith
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ h3)
        exact (measureReal_union_le _ _).trans (add_le_add h1 h2)
      _ = ε := by ring
  have hWρ := tendsto_in_measure_mul_zero_of_is_bounded_in_probability mu W _ hWb hρT
  have hDWZ : TendstoInMeasure mu (fun (n : ℕ) w ↦ D * W n w + Z n w) atTop (fun _ ↦ 0) := by
    have := tendsto_in_measure_add_zero mu _ _ hE
      (tendsto_in_measure_const_mul_zero mu _ (-1) hWρ)
    convert this using 3 with n w
    simp only [hEv]; ring
  have hrem : TendstoInMeasure mu (fun (n : ℕ) w ↦ Real.sqrt n * (T n w - theta₀) +
      (D * Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, psi theta₀ (X i w)) atTop (fun _ ↦ 0) := by
    have := tendsto_in_measure_const_mul_zero mu _ D⁻¹ hDWZ
    convert this using 3 with n w
    simp only [hW, hZ]
    rw [mul_inv]
    field_simp
  refine ⟨hrem, ?_⟩
  have hvar : Var[psi theta₀; P] = ∫ x, psi theta₀ x ^ 2 ∂P := by
    rw [variance_eq_integral (hmeas theta₀).aemeasurable]
    simp only [h0, sub_zero]
  have hX' : TendstoInDistribution (fun (n : ℕ) w ↦ -D⁻¹ * Z n w) atTop id (fun _ ↦ mu)
      (gaussianReal 0 (Real.toNNReal (Var[psi theta₀; P] / D ^ 2))) := by
    refine tendsto_in_distribution_of_map_eq (hZlim.continuous_comp (g := fun x ↦ -D⁻¹ * x)
      (continuous_const.mul continuous_id)) aemeasurable_id ?_
    rw [Measure.map_id, Function.comp_id, gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    have hI0 : 0 ≤ ∫ x, psi theta₀ x ^ 2 ∂P := integral_nonneg fun x ↦ sq_nonneg _
    simp only [NNReal.coe_mul, NNReal.coe_mk, hvar, Real.coe_toNNReal _ hI0,
      Real.coe_toNNReal _ (div_nonneg hI0 (sq_nonneg D))]
    field_simp
  refine tendsto_in_distribution_of_tendsto_in_measure_sub_of_measurable mu _ _
    (fun n ↦ (hZm n).const_mul _) (fun n ↦ ((hT n).sub_const _).const_mul _) hX' ?_
  convert hrem using 3 with n w
  simp only [hZ]
  rw [mul_inv]
  ring

end CKSD
