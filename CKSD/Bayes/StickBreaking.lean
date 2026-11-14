module

public import CKSD.Bayes.Nonparametric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.ProductMeasure
public import TauCeti.Probability.Distributions.Dirichlet.Aggregation
public import TauCeti.Probability.Distributions.Dirichlet.Density
public import TauCeti.Probability.Distributions.Dirichlet.Moments
public import TauCeti.Probability.Distributions.Dirichlet.StickBreaking


/-!
# Stick breaking and the Dirichlet law

The partition masses of Sethuraman's stick-breaking measure `∑ πₖ δ_{θₖ}`, with independent
`Beta(1, |α|)` fractions and independent atoms of law `α / |α|`, have the finite-dimensional
Dirichlet laws of a Dirichlet process with base `α`.

The proof follows Sethuraman (1994). Breaking off the first stick, the vector `p` of cell masses
satisfies the distributional equation `p =ᵈ V e(θ) + (1 - V) p'`, where `e(θ)` is the indicator
vector of the cell of `θ` and `(V, θ)` is independent of `p' =ᵈ p`. The Dirichlet law solves the
same equation: given the cell `j` of `θ`, TauCeti's stick insertion and aggregation laws turn
`V eⱼ + (1 - V) Y` into `Dir(a + eⱼ)`, and the mixture of these tilted laws with weights
`aⱼ / ∑ aᵢ` is `Dir(a)`. The equation has at most one solution with bounded support, because the
map it defines contracts Lipschitz means by the factor `E(1 - V) = |α| / (1 + |α|) < 1`.

## Main results

* `CKSD.eq_of_affine_fixed_point`: uniqueness of bounded solutions of `Y =ᵈ b(S) + c(S) Y` with
  `c ≥ 0` and `E c(S) < 1`.
* `CKSD.integral_dirichlet_measure_add_single`: the tilting `Dir(a + eⱼ) = (∑ aᵢ / aⱼ) yⱼ Dir(a)`.
* `CKSD.map_prod_beta_measure_dirichlet_measure_eq_add_single`: `x eⱼ + (1 - x) y ~ Dir(a + eⱼ)`
  for `x ~ Beta(1, ∑ aᵢ)` and `y ~ Dir(a)` independent.
* `CKSD.sum_integral_stick_insert_dirichlet_measure`: the Dirichlet law solves the stick-breaking
  equation.
* `CKSD.map_head_tail_infinite_pi`: the head and the tail of an i.i.d. sequence are independent.
* `CKSD.stick_breaking_measure_eq_add`: the stick-breaking recursion.
* `CKSD.map_stick_breaking_measure_cells_eq_dirichlet_measure`: Sethuraman's theorem on the
  canonical product space.

The Dirichlet laws, their chart densities, stick insertion and aggregation are those of TauCeti
(`TauCeti.Probability.dirichletMeasure`); the identification of laws from bounded Lipschitz test
functions is Mathlib's `MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`.

## References

* J. Sethuraman, *A constructive definition of Dirichlet priors*, Statist. Sinica 4 (1994),
  639–650.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

section AffineFixedPoint

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
/-- A bounded Lipschitz function is integrable against a finite measure. -/
private theorem integrable_of_bounded_lipschitz {L : Measure E} [IsFiniteMeasure L] {f : E → ℝ}
    {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {K : ℝ≥0} (hK : LipschitzWith K f) :
    Integrable f L := by
  refine Integrable.of_bound hK.continuous.aestronglyMeasurable (‖f 0‖ + C)
    (ae_of_all _ fun x ↦ ?_)
  have h := hC x 0
  rw [dist_eq_norm] at h
  linarith [norm_le_norm_add_norm_sub' (f x) (f 0)]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
/-- Under a probability law concentrated on the ball of radius `R`, a `K`-Lipschitz function has
mean within `K R` of its value at the origin. -/
private theorem abs_integral_sub_apply_zero_le {L : Measure E} [IsProbabilityMeasure L] {R : ℝ}
    (hL : ∀ᵐ y ∂L, ‖y‖ ≤ R) {f : E → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {K : ℝ≥0}
    (hK : LipschitzWith K f) :
    |∫ y, f y ∂L - f 0| ≤ K * R := by
  have hint := integrable_of_bounded_lipschitz (L := L) hC hK
  have h : ∫ y, (f y - f 0) ∂L = ∫ y, f y ∂L - f 0 := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [← h, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := L) (f := fun y ↦ f y - f 0) (C := K * R)
    (by
      filter_upwards [hL] with y hy
      have := hK.dist_le_mul y 0
      rw [dist_eq_norm, dist_zero_right] at this
      exact this.trans (mul_le_mul_of_nonneg_left hy K.2))
  simpa using hb

/-- The contraction estimate behind uniqueness for the affine fixed-point equation
`Y =ᵈ b(S) + c(S) Y`: two solutions concentrated on the ball of radius `R` have `K`-Lipschitz
means within `2 K R q^m` for every `m`, where `q = E c(S)`. -/
private theorem abs_integral_sub_le_of_affine_fixed_point (ρ : Measure S) [IsProbabilityMeasure ρ]
    {b : S → E} {c : S → ℝ} (hb : Measurable b) (hc : Measurable c) (hc0 : ∀ᵐ s ∂ρ, 0 ≤ c s)
    (hci : Integrable c ρ) {L₁ L₂ : Measure E} [IsProbabilityMeasure L₁] [IsProbabilityMeasure L₂]
    {R : ℝ} (h₁ : ∀ᵐ y ∂L₁, ‖y‖ ≤ R) (h₂ : ∀ᵐ y ∂L₂, ‖y‖ ≤ R)
    (hL₁ : ∀ f : E → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∫ y, f y ∂L₁ = ∫ s, ∫ y, f (b s + c s • y) ∂L₁ ∂ρ)
    (hL₂ : ∀ f : E → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∫ y, f y ∂L₂ = ∫ s, ∫ y, f (b s + c s • y) ∂L₂ ∂ρ) (m : ℕ) :
    ∀ (K : ℝ≥0) (f : E → ℝ) (C : ℝ), (∀ x y, dist (f x) (f y) ≤ C) → LipschitzWith K f →
      |∫ y, f y ∂L₁ - ∫ y, f y ∂L₂| ≤ 2 * K * R * (∫ s, c s ∂ρ) ^ m := by
  induction m with
  | zero =>
    intro K f C hC hK
    have e₁ := abs_integral_sub_apply_zero_le h₁ hC hK
    have e₂ := abs_integral_sub_apply_zero_le h₂ hC hK
    rw [pow_zero, mul_one]
    calc |∫ y, f y ∂L₁ - ∫ y, f y ∂L₂|
        = |(∫ y, f y ∂L₁ - f 0) - (∫ y, f y ∂L₂ - f 0)| := by ring_nf
      _ ≤ |∫ y, f y ∂L₁ - f 0| + |∫ y, f y ∂L₂ - f 0| := abs_sub _ _
      _ ≤ 2 * K * R := by linarith
  | succ m ih =>
    intro K f C hC hK
    set q := ∫ s, c s ∂ρ
    have hgm : Measurable fun z : S × E ↦ f (b z.1 + c z.1 • z.2) :=
      hK.continuous.measurable.comp
        ((hb.comp measurable_fst).add ((hc.comp measurable_fst).smul measurable_snd))
    have hI : ∀ (L : Measure E) [IsProbabilityMeasure L],
        Integrable (fun s ↦ ∫ y, f (b s + c s • y) ∂L) ρ := by
      intro L _
      refine Integrable.of_bound
        (hgm.stronglyMeasurable.integral_prod_right' (ν := L)).aestronglyMeasurable
        (‖f 0‖ + C) (ae_of_all _ fun s ↦ ?_)
      have hb' := norm_integral_le_of_norm_le_const (μ := L)
        (f := fun y ↦ f (b s + c s • y)) (C := ‖f 0‖ + C) (ae_of_all _ fun y ↦ by
          have h := hC (b s + c s • y) 0
          rw [dist_eq_norm] at h
          linarith [norm_le_norm_add_norm_sub' (f (b s + c s • y)) (f 0)])
      simpa using hb'
    rw [hL₁ f ⟨C, hC⟩ ⟨K, hK⟩, hL₂ f ⟨C, hC⟩ ⟨K, hK⟩, ← integral_sub (hI L₁) (hI L₂)]
    have hpt : ∀ᵐ s ∂ρ, |∫ y, f (b s + c s • y) ∂L₁ - ∫ y, f (b s + c s • y) ∂L₂| ≤
        c s * (2 * K * R * q ^ m) := by
      filter_upwards [hc0] with s hs
      have hlin : LipschitzWith ⟨c s, hs⟩ fun y : E ↦ b s + c s • y :=
        LipschitzWith.of_dist_le_mul fun x y ↦ by
          rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg hs]
          rfl
      have := ih (K * ⟨c s, hs⟩) (fun y ↦ f (b s + c s • y)) C (fun x y ↦ hC _ _)
        (hK.comp hlin)
      have e : ((K * ⟨c s, hs⟩ : ℝ≥0) : ℝ) = K * c s := rfl
      rw [e] at this
      linarith
    calc |∫ s, (∫ y, f (b s + c s • y) ∂L₁ - ∫ y, f (b s + c s • y) ∂L₂) ∂ρ|
        ≤ ∫ s, |∫ y, f (b s + c s • y) ∂L₁ - ∫ y, f (b s + c s • y) ∂L₂| ∂ρ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s, c s * (2 * K * R * q ^ m) ∂ρ :=
          integral_mono_ae ((hI L₁).sub (hI L₂)).abs (hci.mul_const _) hpt
      _ = 2 * K * R * q ^ (m + 1) := by rw [integral_mul_const]; ring

/-- **Uniqueness for the affine distributional fixed-point equation** `Y =ᵈ b(S) + c(S) Y`, with
`S ~ ρ` independent of `Y`, in integrated form on bounded Lipschitz test functions. If
`c(S) ≥ 0` and `E c(S) < 1`, then the equation has at most one solution among probability laws
concentrated on a bounded set. The proof iterates the contraction of Lipschitz means by the
factor `E c(S)` and identifies the laws by the bounded Lipschitz criterion
`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`. -/
theorem eq_of_affine_fixed_point (ρ : Measure S) [IsProbabilityMeasure ρ]
    {b : S → E} {c : S → ℝ} (hb : Measurable b) (hc : Measurable c) (hc0 : ∀ᵐ s ∂ρ, 0 ≤ c s)
    (hci : Integrable c ρ) (hq : ∫ s, c s ∂ρ < 1)
    {L₁ L₂ : Measure E} [IsProbabilityMeasure L₁] [IsProbabilityMeasure L₂]
    {R : ℝ} (h₁ : ∀ᵐ y ∂L₁, ‖y‖ ≤ R) (h₂ : ∀ᵐ y ∂L₂, ‖y‖ ≤ R)
    (hL₁ : ∀ f : E → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∫ y, f y ∂L₁ = ∫ s, ∫ y, f (b s + c s • y) ∂L₁ ∂ρ)
    (hL₂ : ∀ f : E → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∫ y, f y ∂L₂ = ∫ s, ∫ y, f (b s + c s • y) ∂L₂ ∂ρ) :
    L₁ = L₂ := by
  have hq0 : 0 ≤ ∫ s, c s ∂ρ := integral_nonneg_of_ae hc0
  have hint : ∀ f : E → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) → (∃ K, LipschitzWith K f) →
      ∫ y, f y ∂L₁ = ∫ y, f y ∂L₂ := by
    rintro f ⟨C, hC⟩ ⟨K, hK⟩
    have ht : Tendsto (fun m : ℕ ↦ 2 * K * R * (∫ s, c s ∂ρ) ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (2 * K * R)
    have h0 : |∫ y, f y ∂L₁ - ∫ y, f y ∂L₂| ≤ 0 := ge_of_tendsto' ht fun m ↦
      abs_integral_sub_le_of_affine_fixed_point ρ hb hc hc0 hci h₁ h₂ hL₁ hL₂ m K f C hC hK
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  let P₁ : ProbabilityMeasure E := ⟨L₁, inferInstance⟩
  let P₂ : ProbabilityMeasure E := ⟨L₂, inferInstance⟩
  have ht := (tendsto_iff_forall_lipschitz_integral_tendsto (μs := fun _ : ℕ ↦ P₁) (μ := P₂)
    (F := atTop)).mpr fun f hf hl ↦ by
      simp only [P₁, P₂, ProbabilityMeasure.coe_mk, hint f hf hl]
      exact tendsto_const_nhds
  have e : P₁ = P₂ := tendsto_nhds_unique tendsto_const_nhds ht
  exact congrArg (fun P : ProbabilityMeasure E ↦ (P : Measure E)) e

end AffineFixedPoint

section DirichletTilting

open TauCeti TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Dirichlet chart density at `a + eⱼ`, in the chart that drops the coordinate `j`, is the
density at `a` multiplied by `(∑ aᵢ / aⱼ) yⱼ`, where `yⱼ = 1 - ∑ xₗ` is the dropped coordinate. -/
private theorem dirichlet_chart_pdf_real_add_single {a : ι → ℝ} (ha : ∀ i, 0 < a i) (j : ι)
    (x : {i // i ≠ j} → ℝ) :
    dirichletChartPDFReal (a + Pi.single j 1 : ι → ℝ) j x =
      (∑ i, a i) / a j * (dirichletChart j x j * dirichletChartPDFReal a j x) := by
  by_cases hx : x ∈ dirichletChartRegion j
  · rw [dirichletChartPDFReal_of_mem _ hx, dirichletChartPDFReal_of_mem _ hx,
      dirichletChart_apply_self]
    have hs : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) ⟨j, Finset.mem_univ j⟩
    have hne : ∀ l : {i // i ≠ j}, (a + Pi.single j 1 : ι → ℝ) l = a l := fun l ↦ by
      simp [Pi.single_eq_of_ne l.2]
    have hsum : ∑ i, (a + Pi.single j 1 : ι → ℝ) i = ∑ i, a i + 1 := by
      simp [Finset.sum_add_distrib]
    have hprod : ∏ i, Real.Gamma ((a + Pi.single j 1 : ι → ℝ) i) = a j * ∏ i, Real.Gamma (a i) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ j,
        Fintype.prod_eq_mul_prod_subtype_ne (fun i ↦ Real.Gamma (a i)) j]
      simp only [Pi.add_apply, Pi.single_eq_same, hne]
      rw [Real.Gamma_add_one (ha j).ne']
      ring
    have hpos : 0 < 1 - ∑ l, x l := sub_pos.mpr (mem_dirichletChartRegion_iff.mp hx).2
    have hlast : (1 - ∑ l, x l) ^ ((a + Pi.single j 1 : ι → ℝ) j - 1) =
        (1 - ∑ l, x l) * (1 - ∑ l, x l) ^ (a j - 1) := by
      simp only [Pi.add_apply, Pi.single_eq_same, add_sub_cancel_right]
      rw [Real.rpow_sub_one hpos.ne']
      field_simp
    rw [hsum, hprod, Real.Gamma_add_one hs.ne', hlast]
    simp only [hne]
    have := Real.Gamma_pos_of_pos hs
    have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) ↦ Real.Gamma_pos_of_pos (ha i)
    have := ha j
    field_simp
  · simp [hx]

/-- **Tilting of the Dirichlet law.** Raising the `j`-th concentration parameter by one tilts the
Dirichlet law by its `j`-th coordinate: `Dir(a + eⱼ) = (∑ aᵢ / aⱼ) yⱼ · Dir(a)`. -/
theorem integral_dirichlet_measure_add_single {a : ι → ℝ} (ha : ∀ i, 0 < a i) (j : ι)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f) :
    ∫ y, f y ∂dirichletMeasure (a + Pi.single j 1 : ι → ℝ) =
      (∑ i, a i) / a j * ∫ y, y j * f y ∂dirichletMeasure a := by
  have ha' : ∀ i, 0 < (a + Pi.single j 1 : ι → ℝ) i := fun i ↦ by
    by_cases h : i = j
    · subst h; simp; linarith [ha i]
    · simp [Pi.single_eq_of_ne h, ha i]
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha' j,
    dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha j,
    integral_map measurable_dirichletChart.aemeasurable hf.aestronglyMeasurable,
    integral_map (f := fun y : EuclideanSpace ℝ ι ↦ y j * f y)
      measurable_dirichletChart.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop)),
    integral_withDensity_eq_integral_toReal_smul (measurable_dirichletChartPDF _ _)
      (ae_of_all _ fun _ ↦ by rw [dirichletChartPDF_eq_ofReal]; exact ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (measurable_dirichletChartPDF _ _)
      (ae_of_all _ fun _ ↦ by rw [dirichletChartPDF_eq_ofReal]; exact ENNReal.ofReal_lt_top),
      ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [dirichletChartPDF_eq_ofReal,
    ENNReal.toReal_ofReal (dirichletChartPDFReal_nonneg ha' j x),
    ENNReal.toReal_ofReal (dirichletChartPDFReal_nonneg ha j x), smul_eq_mul]
  rw [dirichlet_chart_pdf_real_add_single ha j x]
  ring

/-- **Stick insertion into a fixed cell.** If `x ~ Beta(1, ∑ aᵢ)` and `y ~ Dir(a)` are
independent, then `x eⱼ + (1 - x) y ~ Dir(a + eⱼ)`. This combines TauCeti's stick insertion
`map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure` with the aggregation law
`map_euclideanFiberSum_dirichletMeasure`. -/
theorem map_prod_beta_measure_dirichlet_measure_eq_add_single [Nonempty ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (j : ι) :
    ((betaMeasure 1 (∑ i, a i)).prod (dirichletMeasure a)).map
        (fun z ↦ z.1 • EuclideanSpace.single j 1 + (1 - z.1) • z.2) =
      dirichletMeasure (a + Pi.single j 1 : ι → ℝ) := by
  have ha' : ∀ o : Option ι, 0 < o.elim 1 a := by rintro (_ | i) <;> simp [ha]
  have hg : Surjective fun o : Option ι ↦ o.elim j id := fun i ↦ ⟨some i, rfl⟩
  have h1 := map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure
    (a := fun o : Option ι ↦ o.elim 1 a) ha'
  simp only [Option.elim_none, Option.elim_some] at h1
  have h2 := map_euclideanFiberSum_dirichletMeasure hg ha'
  have hcomp : euclideanFiberSum (fun o : Option ι ↦ o.elim j id) ∘ dirichletStickInsert =
      fun z : ℝ × EuclideanSpace ℝ ι ↦ z.1 • EuclideanSpace.single j 1 + (1 - z.1) • z.2 := by
    funext z
    ext i
    simp [euclideanFiberSum_apply, Finset.sum_filter, Fintype.sum_option, eq_comm]
  have hparam : (fun i ↦ ∑ o with (fun o : Option ι ↦ o.elim j id) o = i, o.elim 1 a) =
      (a + Pi.single j 1 : ι → ℝ) := by
    funext i
    rw [Finset.sum_filter, Fintype.sum_option]
    show (if j = i then (1 : ℝ) else 0) + ∑ l, (if l = i then a l else 0) =
      a i + Pi.single (M := fun _ ↦ ℝ) j 1 i
    rw [Finset.sum_ite_eq' Finset.univ i a]
    simp only [Finset.mem_univ, ite_true, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp [add_comm]
    · simp [h, Ne.symm h]
  rw [← hcomp, ← Measure.map_map (measurable_euclideanFiberSum _)
    measurable_dirichletStickInsert, h1, h2, hparam]

/-- **The Dirichlet law solves the stick-breaking equation.** If `J` has law
`(aⱼ / ∑ aᵢ)ⱼ`, `x ~ Beta(1, ∑ aᵢ)` and `y ~ Dir(a)` are independent, then
`x e_J + (1 - x) y ~ Dir(a)`; this is stated in integrated form for bounded measurable test
functions. Each cell contributes the tilted law `Dir(a + eⱼ)`, and the tilts sum to one on the
simplex. -/
theorem sum_integral_stick_insert_dirichlet_measure [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∑ j, a j / (∑ i, a i) * ∫ x, ∫ y, f (x • EuclideanSpace.single j 1 + (1 - x) • y)
        ∂dirichletMeasure a ∂betaMeasure 1 (∑ i, a i) = ∫ y, f y ∂dirichletMeasure a := by
  have hs : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have := isProbabilityMeasureBeta one_pos hs
  have := isProbabilityMeasure_dirichletMeasure ha
  have hj : ∀ j, ∫ x, ∫ y, f (x • EuclideanSpace.single j 1 + (1 - x) • y)
      ∂dirichletMeasure a ∂betaMeasure 1 (∑ i, a i) =
        (∑ i, a i) / a j * ∫ y, y j * f y ∂dirichletMeasure a := by
    intro j
    have hm : Measurable fun z : ℝ × EuclideanSpace ℝ ι ↦
        z.1 • EuclideanSpace.single j 1 + (1 - z.1) • z.2 := by fun_prop
    rw [← integral_prod (f := fun z : ℝ × EuclideanSpace ℝ ι ↦
        f (z.1 • EuclideanSpace.single j 1 + (1 - z.1) • z.2))
        (Integrable.of_bound (hf.comp hm).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC _)),
      ← integral_map hm.aemeasurable hf.aestronglyMeasurable,
      map_prod_beta_measure_dirichlet_measure_eq_add_single ha j,
      integral_dirichlet_measure_add_single ha j hf]
  have hcancel : ∀ j, a j / (∑ i, a i) * ((∑ i, a i) / a j * ∫ y, y j * f y ∂dirichletMeasure a) =
      ∫ y, y j * f y ∂dirichletMeasure a := fun j ↦ by
    have := ha j
    field_simp
  simp_rw [hj, hcancel]
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards [ae_sum_eq_one_dirichletMeasure ha] with y hy
    rw [← Finset.sum_mul, hy, one_mul]
  · intro j _
    exact (((memLp_eval_dirichletMeasure j 1).integrable le_rfl).bdd_mul
      hf.aestronglyMeasurable (ae_of_all _ hC)).congr (ae_of_all _ fun y ↦ mul_comm _ _)

end DirichletTilting

section Sequences

variable {α : Type*} [MeasurableSpace α]

/-- Prepend a point to a sequence. -/
private def seqCons (p : α × (ℕ → α)) : ℕ → α
  | 0 => p.1
  | k + 1 => p.2 k

/-- Prepending a point to a sequence is measurable. -/
private theorem measurable_seq_cons : Measurable (seqCons (α := α)) := by
  refine measurable_pi_iff.mpr fun k ↦ ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

/-- A finite product over `s ⊆ ℕ` splits into the factor at `0` and the shifted factors. -/
private theorem prod_eq_ite_mul_prod_preimage_succ {M : Type*} [CommMonoid M] (s : Finset ℕ)
    (g : ℕ → M) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ k ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (k + 1) := by
  classical
  rw [Finset.prod_preimage' Nat.succ s _ g,
    ← Finset.prod_filter_not_mul_prod_filter s (fun x ↦ x ∈ Set.range Nat.succ)]
  congr 1
  have : s.filter (fun x ↦ x ∉ Set.range Nat.succ) = s.filter (fun x ↦ x = 0) := by
    ext x
    simp only [Finset.mem_filter, Set.mem_range, not_exists]
    refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h y hy ↦ by omega⟩
    cases x with
    | zero => rfl
    | succ x => exact absurd rfl (h x)
  rw [this, Finset.filter_eq']
  split_ifs <;> simp

/-- Prepending an independent point to an i.i.d. sequence gives an i.i.d. sequence. -/
private theorem map_seq_cons_prod_infinite_pi (ν : Measure α) [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi fun _ : ℕ ↦ ν)).map seqCons =
      Measure.infinitePi fun _ : ℕ ↦ ν := by
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  have hpre : seqCons ⁻¹' Set.pi ↑s t = (if 0 ∈ s then t 0 else univ) ×ˢ
      Set.pi ↑(s.preimage Nat.succ Nat.succ_injective.injOn) (fun k ↦ t (k + 1)) := by
    ext ⟨x, y⟩
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun k hk ↦ h (k + 1) hk⟩
      split_ifs with h0
      exacts [h 0 h0, trivial]
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero =>
        simp only [hi, ite_true] at h0
        exact h0
      | succ k => exact h1 k hi
  rw [Measure.map_apply measurable_seq_cons (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i),
    hpre, Measure.prod_prod, Measure.infinitePi_pi (μ := fun _ : ℕ ↦ ν)
      (s := s.preimage Nat.succ Nat.succ_injective.injOn) (t := fun k ↦ t (k + 1))
      (fun i _ ↦ ht _),
    prod_eq_ite_mul_prod_preimage_succ s]
  split_ifs <;> simp

/-- **Head and tail of an i.i.d. sequence.** Under the infinite product of a probability measure
`ν`, the first coordinate and the shifted sequence are independent, with laws `ν` and the
infinite product itself. -/
theorem map_head_tail_infinite_pi (ν : Measure α) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ ↦ ν).map (fun x ↦ (x 0, fun k ↦ x (k + 1))) =
      ν.prod (Measure.infinitePi fun _ : ℕ ↦ ν) := by
  conv_lhs => rw [← map_seq_cons_prod_infinite_pi ν]
  rw [Measure.map_map (by fun_prop) measurable_seq_cons]
  have : (fun x : ℕ → α ↦ (x 0, fun k ↦ x (k + 1))) ∘ seqCons = id := by
    funext p
    rfl
  rw [this, Measure.map_id]

end Sequences

section Rearrangement

variable {α₁ α₂ α₃ α₄ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace α₃]
  [MeasurableSpace α₄]

/-- Rectangles cover a product of finite measures by a constant spanning sequence. -/
private def finiteSpanningSetsIn_rectangles {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (β × γ)) [IsFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn
      (image2 (· ×ˢ ·) {s : Set β | MeasurableSet s} {t : Set γ | MeasurableSet t}) where
  set _ := univ
  set_mem _ := ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩
  finite _ := measure_lt_top _ _
  spanning := iUnion_const _

/-- Exchanging the middle factors of a fourfold product of finite measures. -/
theorem map_prod_prod_prod_comm_prod (μ₁ : Measure α₁) (μ₂ : Measure α₂) (μ₃ : Measure α₃)
    (μ₄ : Measure α₄) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    [IsFiniteMeasure μ₄] :
    ((μ₁.prod μ₂).prod (μ₃.prod μ₄)).map (fun z ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2))) =
      (μ₁.prod μ₃).prod (μ₂.prod μ₄) := by
  have hF : Measurable fun z : (α₁ × α₂) × (α₃ × α₄) ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2)) := by
    fun_prop
  refine (Measure.prod_eq_generateFrom generateFrom_prod generateFrom_prod isPiSystem_prod
    isPiSystem_prod (finiteSpanningSetsIn_rectangles _) (finiteSpanningSetsIn_rectangles _)
    ?_).symm
  rintro _ ⟨A, hA, C, hC, rfl⟩ _ ⟨B, hB, D, hD, rfl⟩
  have hpre : (fun z : (α₁ × α₂) × (α₃ × α₄) ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2))) ⁻¹'
      ((A ×ˢ C) ×ˢ (B ×ˢ D)) = (A ×ˢ B) ×ˢ (C ×ˢ D) := by
    ext z
    simp only [mem_preimage, mem_prod]
    tauto
  rw [Measure.map_apply hF (((measurableSet_prod.mpr (Or.inl ⟨hA, hC⟩))).prod
      (measurableSet_prod.mpr (Or.inl ⟨hB, hD⟩))), hpre]
  simp only [Measure.prod_prod]
  ring

end Rearrangement

section StickBreakingAlgebra

variable {X : Type*} [MeasurableSpace X]

/-- Removing the first stick: the `(k + 1)`-st weight is `1 - V₀` times the `k`-th weight of the
shifted fractions. -/
theorem stick_breaking_weight_succ (V : ℕ → ℝ) (k : ℕ) :
    stickBreakingWeight V (k + 1) = (1 - V 0) * stickBreakingWeight (fun j ↦ V (j + 1)) k := by
  simp only [stickBreakingWeight, Finset.prod_range_succ']
  ring

/-- The first `n` stick-breaking weights total `1 - ∏_{j < n} (1 - Vⱼ)`. -/
theorem sum_range_stick_breaking_weight (V : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, stickBreakingWeight V k = 1 - ∏ j ∈ Finset.range n, (1 - V j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ, stickBreakingWeight]
    ring

/-- Stick-breaking weights are nonnegative when the fractions lie in `[0, 1]`. -/
theorem stick_breaking_weight_nonneg {V : ℕ → ℝ} (hV : ∀ k, V k ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ stickBreakingWeight V k :=
  mul_nonneg (hV k).1 (Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (hV j).2)

/-- With fractions in `[0, 1]` the stick-breaking measure has total mass at most one. -/
theorem stick_breaking_measure_univ_le_one {V : ℕ → ℝ} (hV : ∀ k, V k ∈ Icc (0 : ℝ) 1)
    (θ : ℕ → X) : stickBreakingMeasure V θ univ ≤ 1 := by
  rw [stickBreakingMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ stick_breaking_weight_nonneg hV k,
    sum_range_stick_breaking_weight]
  exact ENNReal.ofReal_le_one.mpr
    (sub_le_self _ (Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (hV j).2))

/-- With fractions in `[0, 1]` the stick-breaking measure is finite. -/
theorem is_finite_measure_stick_breaking_measure {V : ℕ → ℝ} (hV : ∀ k, V k ∈ Icc (0 : ℝ) 1)
    (θ : ℕ → X) : IsFiniteMeasure (stickBreakingMeasure V θ) :=
  ⟨(stick_breaking_measure_univ_le_one hV θ).trans_lt ENNReal.one_lt_top⟩

/-- **The stick-breaking recursion.** Breaking off the first stick, the stick-breaking measure is
`V₀ δ_{θ₀} + (1 - V₀) P'`, where `P'` is the stick-breaking measure of the shifted sequences. -/
theorem stick_breaking_measure_eq_add {V : ℕ → ℝ} (hV0 : V 0 ≤ 1) (θ : ℕ → X) :
    stickBreakingMeasure V θ = ENNReal.ofReal (V 0) • Measure.dirac (θ 0) +
      ENNReal.ofReal (1 - V 0) •
        stickBreakingMeasure (fun k ↦ V (k + 1)) (fun k ↦ θ (k + 1)) := by
  ext s hs
  simp only [stickBreakingMeasure, add_apply, smul_apply,
    Measure.sum_apply _ hs, smul_eq_mul]
  rw [tsum_eq_zero_add' CompleteLattice.summable, ← ENNReal.tsum_mul_left, stick_breaking_weight_zero]
  congr 1
  refine tsum_congr fun k ↦ ?_
  rw [stick_breaking_weight_succ, ENNReal.ofReal_mul (sub_nonneg.mpr hV0), mul_assoc]

end StickBreakingAlgebra

section TotalMass

/-- The remaining stick after `n` breaks, `∏_{j < n} (1 - Vⱼ)`, has mean `qⁿ` under an i.i.d.
law of the fractions, where `q = E(1 - V)`. -/
private theorem integral_prod_one_sub_infinite_pi (β : Measure ℝ) [IsProbabilityMeasure β]
    (n : ℕ) :
    ∫ v, ∏ j ∈ Finset.range n, (1 - v j) ∂Measure.infinitePi (fun _ : ℕ ↦ β) =
      (∫ x, (1 - x) ∂β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : Measurable fun v : ℕ → ℝ ↦ (v 0, fun k ↦ v (k + 1)) := by fun_prop
    have h : ∫ v, ∏ j ∈ Finset.range (n + 1), (1 - v j) ∂Measure.infinitePi (fun _ : ℕ ↦ β) =
        ∫ v, (fun z : ℝ × (ℕ → ℝ) ↦ (1 - z.1) * ∏ j ∈ Finset.range n, (1 - z.2 j))
          (v 0, fun k ↦ v (k + 1)) ∂Measure.infinitePi (fun _ : ℕ ↦ β) := by
      congr 1
      funext v
      simp only [Finset.prod_range_succ']
      ring
    rw [h, ← integral_map (f := fun z : ℝ × (ℕ → ℝ) ↦
        (1 - z.1) * ∏ j ∈ Finset.range n, (1 - z.2 j)) hm.aemeasurable
        (Measurable.aestronglyMeasurable (by fun_prop)),
      map_head_tail_infinite_pi, integral_prod_mul (fun x : ℝ ↦ 1 - x)
        (fun v : ℕ → ℝ ↦ ∏ j ∈ Finset.range n, (1 - v j)), ih, pow_succ, mul_comm]

/-- **The sticks exhaust the unit mass.** For i.i.d. fractions in `[0, 1]` with `E(1 - V) < 1`,
the stick-breaking weights sum to one almost surely. -/
theorem ae_tsum_stick_breaking_weight_eq_one (β : Measure ℝ) [IsProbabilityMeasure β]
    (hβ : ∀ᵐ x ∂β, x ∈ Icc (0 : ℝ) 1) (hq : ∫ x, (1 - x) ∂β < 1) :
    ∀ᵐ v ∂Measure.infinitePi (fun _ : ℕ ↦ β),
      ∑' k, ENNReal.ofReal (stickBreakingWeight v k) = 1 := by
  set π := Measure.infinitePi (fun _ : ℕ ↦ β)
  set R : ℕ → (ℕ → ℝ) → ℝ := fun n v ↦ ∏ j ∈ Finset.range n, (1 - v j)
  have hgood : ∀ᵐ v ∂π, ∀ n, v n ∈ Icc (0 : ℝ) 1 := ae_all_iff.mpr fun n ↦
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ β) n).quasiMeasurePreserving.ae hβ
  have hR0 : ∀ v, (∀ n, v n ∈ Icc (0 : ℝ) 1) → ∀ n, 0 ≤ R n v := fun v hv n ↦
    Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (hv j).2
  have hRanti : ∀ v, (∀ n, v n ∈ Icc (0 : ℝ) 1) → Antitone fun n ↦ R n v := by
    intro v hv
    refine antitone_nat_of_succ_le fun n ↦ ?_
    simp only [R, Finset.prod_range_succ]
    exact mul_le_of_le_one_right (hR0 v hv n) (sub_le_self _ (hv n).1)
  have hRm : ∀ n, Measurable (R n) := fun n ↦
    Finset.measurable_prod _ fun j _ ↦ measurable_const.sub (measurable_pi_apply j)
  set L : (ℕ → ℝ) → ℝ := fun v ↦ ⨅ n, R n v
  have hLm : Measurable L := Measurable.iInf hRm
  have hL0 : ∀ᵐ v ∂π, 0 ≤ L v := hgood.mono fun v hv ↦ le_ciInf (hR0 v hv)
  have hLle : ∀ n, ∀ᵐ v ∂π, L v ≤ R n v := fun n ↦ hgood.mono fun v hv ↦
    ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact hR0 v hv m⟩ n
  have hLint : Integrable L π := Integrable.of_bound hLm.aestronglyMeasurable 1 (by
    filter_upwards [hL0, hLle 0] with v h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simpa [R] using h1)
  have hq0 : 0 ≤ ∫ x, (1 - x) ∂β :=
    integral_nonneg_of_ae (hβ.mono fun x hx ↦ sub_nonneg.mpr hx.2)
  have hLint0 : ∫ v, L v ∂π ≤ 0 := by
    refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq) fun n ↦ ?_
    rw [← integral_prod_one_sub_infinite_pi β n]
    refine integral_mono_ae hLint (Integrable.of_bound (hRm n).aestronglyMeasurable 1 ?_) (hLle n)
    filter_upwards [hgood] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 v hv n)]
    exact (hRanti v hv (Nat.zero_le n)).trans_eq (by simp [R])
  have hLae : L =ᵐ[π] 0 := (integral_eq_zero_iff_of_nonneg_ae hL0 hLint).mp
    (le_antisymm hLint0 (integral_nonneg_of_ae hL0))
  filter_upwards [hgood, hLae] with v hv hLv
  have hlim : Tendsto (fun n ↦ R n v) atTop (𝓝 0) := by
    have := tendsto_atTop_ciInf (hRanti v hv) ⟨0, by rintro _ ⟨m, rfl⟩; exact hR0 v hv m⟩
    simpa [L, hLv] using this
  have hpartial : ∀ n, ∑ k ∈ Finset.range n, ENNReal.ofReal (stickBreakingWeight v k) =
      ENNReal.ofReal (1 - R n v) := fun n ↦ by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ stick_breaking_weight_nonneg hv k,
      sum_range_stick_breaking_weight]
  have h1 : Tendsto (fun n ↦ ENNReal.ofReal (1 - R n v)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim)
  refine tendsto_nhds_unique (ENNReal.tendsto_nat_tsum _) ?_
  simpa only [hpartial] using h1

end TotalMass

section CellMasses

open TauCeti.Probability

variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- The vector of masses of a measure on finitely many cells. -/
private def cellMasses (A : Fin k → Set X) (ν : Measure X) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i ↦ ν.real (A i)

/-- Coordinates of the cell-mass vector. -/
private theorem cell_masses_apply (A : Fin k → Set X) (ν : Measure X) (i : Fin k) :
    cellMasses A ν i = ν.real (A i) := rfl

/-- The cell masses of a Dirac measure are the cell indicators. -/
private theorem cell_masses_dirac {A : Fin k → Set X} (hA : ∀ i, MeasurableSet (A i)) (t : X)
    (i : Fin k) : cellMasses A (Measure.dirac t) i = (A i).indicator 1 t := by
  rw [cell_masses_apply, measureReal_def, Measure.dirac_apply' t (hA i)]
  by_cases h : t ∈ A i <;> simp [h]

/-- On a cell of a disjoint family, the cell masses of a Dirac measure form a unit vector. -/
private theorem cell_masses_dirac_of_mem {A : Fin k → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) {t : X} {j : Fin k} (ht : t ∈ A j) :
    cellMasses A (Measure.dirac t) = EuclideanSpace.single j 1 := by
  ext i
  rw [cell_masses_dirac hA, PiLp.single_apply]
  by_cases h : i = j
  · subst h
    simp [ht]
  · have : t ∉ A i := fun hi ↦ (hd h).le_bot ⟨hi, ht⟩
    simp [h, this]

/-- The cell masses of a Dirac measure depend measurably on the atom. -/
private theorem measurable_cell_masses_dirac {A : Fin k → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable fun t : X ↦ cellMasses A (Measure.dirac t) := by
  have : (fun t : X ↦ cellMasses A (Measure.dirac t)) =
      fun t ↦ WithLp.toLp 2 fun i ↦ (A i).indicator (1 : X → ℝ) t := by
    funext t
    ext i
    exact cell_masses_dirac hA t i
  rw [this]
  exact (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun i ↦ measurable_one.indicator (hA i))

/-- The cell masses of `x δ + y ν` for finite measures and nonnegative weights. -/
private theorem cell_masses_add_smul (A : Fin k → Set X) (δ ν : Measure X) [IsFiniteMeasure δ]
    [IsFiniteMeasure ν] {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cellMasses A (ENNReal.ofReal x • δ + ENNReal.ofReal y • ν) =
      x • cellMasses A δ + y • cellMasses A ν := by
  ext i
  simp only [cell_masses_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, measureReal_def,
    add_apply, smul_apply]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy]

/-- The cell masses of the stick-breaking measure of a pair of sequences. -/
private def sbCells (A : Fin k → Set X) (w : (ℕ → ℝ) × (ℕ → X)) : EuclideanSpace ℝ (Fin k) :=
  cellMasses A (stickBreakingMeasure w.1 w.2)

/-- The shift of a pair of sequences. -/
private def pairTail (w : (ℕ → ℝ) × (ℕ → X)) : (ℕ → ℝ) × (ℕ → X) :=
  (fun n ↦ w.1 (n + 1), fun n ↦ w.2 (n + 1))

/-- The stick-breaking recursion for the cell masses. -/
private theorem sb_cells_eq (A : Fin k → Set X) {w : (ℕ → ℝ) × (ℕ → X)}
    (hw : ∀ n, w.1 n ∈ Icc (0 : ℝ) 1) :
    sbCells A w = w.1 0 • cellMasses A (Measure.dirac (w.2 0)) +
      (1 - w.1 0) • sbCells A (pairTail w) := by
  have := is_finite_measure_stick_breaking_measure (V := fun n ↦ w.1 (n + 1)) (fun n ↦ hw (n + 1))
    (fun n ↦ w.2 (n + 1))
  rw [sbCells, stick_breaking_measure_eq_add (hw 0).2,
    cell_masses_add_smul _ _ _ (hw 0).1 (sub_nonneg.mpr (hw 0).2)]
  rfl

/-- The mass that the stick-breaking measure gives to a measurable set depends measurably on the
fractions and the atoms. -/
theorem measurable_stick_breaking_measure_apply {B : Set X} (hB : MeasurableSet B) :
    Measurable fun w : (ℕ → ℝ) × (ℕ → X) ↦ stickBreakingMeasure w.1 w.2 B := by
  have : (fun w : (ℕ → ℝ) × (ℕ → X) ↦ stickBreakingMeasure w.1 w.2 B) =
      fun w ↦ ∑' n, ENNReal.ofReal (stickBreakingWeight w.1 n) * B.indicator 1 (w.2 n) := by
    funext w
    simp only [stickBreakingMeasure, Measure.sum_apply _ hB, smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hB]
  rw [this]
  simp_rw [tsum_eq_iSup_sum]
  refine Measurable.iSup fun s ↦ Finset.measurable_sum s fun n _ ↦ ?_
  refine Measurable.mul (ENNReal.measurable_ofReal.comp ?_)
    ((measurable_one.indicator hB).comp ((measurable_pi_apply n).comp measurable_snd))
  simp only [stickBreakingWeight]
  exact ((measurable_pi_apply n).comp measurable_fst).mul (Finset.measurable_prod _
    fun j _ ↦ measurable_const.sub ((measurable_pi_apply j).comp measurable_fst))

/-- The stick-breaking cell masses depend measurably on the sequences. -/
private theorem measurable_sb_cells {A : Fin k → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (sbCells A) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i ↦
    (measurable_stick_breaking_measure_apply (hA i)).ennreal_toReal)

/-- With fractions in `[0, 1]` the stick-breaking cell masses lie in the ball of radius `√k`. -/
private theorem norm_sb_cells_le (A : Fin k → Set X) {w : (ℕ → ℝ) × (ℕ → X)}
    (hw : ∀ n, w.1 n ∈ Icc (0 : ℝ) 1) : ‖sbCells A w‖ ≤ Real.sqrt k := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖sbCells A w i‖ ^ 2 ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ ?_
    _ = k := by simp
  have h0 : 0 ≤ (stickBreakingMeasure w.1 w.2).real (A i) := measureReal_nonneg
  have h1 : (stickBreakingMeasure w.1 w.2).real (A i) ≤ 1 := by
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact (measure_mono (subset_univ _)).trans (stick_breaking_measure_univ_le_one hw _)
  change ‖(stickBreakingMeasure w.1 w.2).real (A i)‖ ^ 2 ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith

end CellMasses

section Sethuraman

open TauCeti TauCeti.Probability

variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- A function with oscillation at most `C` is bounded by `‖f 0‖ + C`. -/
private theorem norm_le_of_dist_le {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {C : ℝ}
    (hC : ∀ x y, dist (f x) (f y) ≤ C) (y : E) : ‖f y‖ ≤ ‖f 0‖ + C := by
  have h := hC y 0
  rw [dist_eq_norm] at h
  linarith [norm_le_norm_add_norm_sub' (f y) (f 0)]

/-- The cells of a partition of a set of full base mass carry the whole base mass. -/
private theorem sum_measure_real_cells (α : Measure X) [IsFiniteMeasure α] {A : Fin k → Set X}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAc : α (⋃ i, A i)ᶜ = 0) : ∑ i, α.real (A i) = α.real univ := by
  rw [← measureReal_iUnion_fintype hAd hAm, ← measureReal_add_measureReal_compl
    (MeasurableSet.iUnion hAm), measureReal_def (s := (⋃ i, A i)ᶜ), hAc, ENNReal.toReal_zero,
    add_zero]

/-- **The Dirichlet law solves the stick-breaking equation for a partition.** With
`(V, θ) ~ Beta(1, |α|) ⊗ α/|α|` independent of `Y ~ Dir(α(A₁), …, α(A_k))`, the vector
`V e(θ) + (1 - V) Y`, where `e(θ)` is the indicator vector of the cell of `θ`, is again
`Dir(α(A₁), …, α(A_k))`; stated in integrated form. -/
private theorem integral_dirichlet_measure_eq_stick (α : Measure X) [IsFiniteMeasure α]
    (hα : α ≠ 0) (hk : 0 < k) {A : Fin k → Set X} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (hAc : α (⋃ i, A i)ᶜ = 0) (hApos : ∀ i, 0 < α (A i))
    {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂dirichletMeasure (fun i ↦ α.real (A i)) =
      ∫ s, ∫ y, f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • y)
        ∂dirichletMeasure (fun i ↦ α.real (A i))
        ∂(betaMeasure 1 (α.real univ)).prod ((α univ)⁻¹ • α) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : NeZero α := ⟨hα⟩
  have ha : ∀ i, 0 < α.real (A i) := fun i ↦
    ENNReal.toReal_pos (hApos i).ne' (measure_ne_top _ _)
  have hsum := sum_measure_real_cells α hAm hAd hAc
  have hs : 0 < α.real univ := hsum ▸ Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have := isProbabilityMeasureBeta one_pos hs
  have := isProbabilityMeasure_dirichletMeasure ha
  have hm : Measurable fun z : (ℝ × X) × EuclideanSpace ℝ (Fin k) ↦
      f (z.1.1 • cellMasses A (Measure.dirac z.1.2) + (1 - z.1.1) • z.2) :=
    hf.comp ((measurable_fst.comp measurable_fst).smul
      ((measurable_cell_masses_dirac hAm).comp (measurable_snd.comp measurable_fst)) |>.add
      ((measurable_const.sub (measurable_fst.comp measurable_fst)).smul measurable_snd))
  have hhint : Integrable (fun s : ℝ × X ↦ ∫ y, f (s.1 • cellMasses A (Measure.dirac s.2) +
      (1 - s.1) • y) ∂dirichletMeasure (fun i ↦ α.real (A i)))
      ((betaMeasure 1 (α.real univ)).prod ((α univ)⁻¹ • α)) := by
    refine Integrable.of_bound (hm.stronglyMeasurable.integral_prod_right'
      (ν := dirichletMeasure (fun i ↦ α.real (A i)))).aestronglyMeasurable C
      (ae_of_all _ fun s ↦ ?_)
    have := norm_integral_le_of_norm_le_const (μ := dirichletMeasure (fun i ↦ α.real (A i)))
      (f := fun y ↦ f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • y))
      (ae_of_all _ fun y ↦ hC _)
    simpa using this
  rw [integral_prod_symm _ hhint]
  have hae : ∀ᵐ t ∂(α univ)⁻¹ • α, ∫ x, ∫ y, f (x • cellMasses A (Measure.dirac t) +
      (1 - x) • y) ∂dirichletMeasure (fun i ↦ α.real (A i)) ∂betaMeasure 1 (α.real univ) =
      ∑ j, (A j).indicator (fun _ ↦ ∫ x, ∫ y, f (x • EuclideanSpace.single j 1 + (1 - x) • y)
        ∂dirichletMeasure (fun i ↦ α.real (A i)) ∂betaMeasure 1 (α.real univ)) t := by
    have hG : ((α univ)⁻¹ • α) (⋃ i, A i)ᶜ = 0 := by
      simp only [smul_apply, hAc, smul_eq_mul, mul_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hG] with t ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp ht)
    rw [Finset.sum_eq_single j (fun i _ hij ↦ indicator_of_notMem
      (fun hi ↦ (hAd hij).le_bot ⟨hi, hj⟩) _) (by simp), indicator_of_mem hj,
      cell_masses_dirac_of_mem hAm hAd hj]
  rw [integral_congr_ae hae, integral_finsetSum _ fun j _ ↦ (integrable_const _).indicator (hAm j)]
  simp_rw [integral_indicator_const _ (hAm _)]
  conv_lhs => rw [← sum_integral_stick_insert_dirichlet_measure ha hf hC, hsum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul]
  congr 1
  simp [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]

/-- Head and tail of a pair of independent i.i.d. sequences. -/
private theorem map_head_pair_tail (β : Measure ℝ) (G : Measure X) [IsProbabilityMeasure β]
    [IsProbabilityMeasure G] :
    ((Measure.infinitePi fun _ : ℕ ↦ β).prod (Measure.infinitePi fun _ : ℕ ↦ G)).map
        (fun w ↦ ((w.1 0, w.2 0), pairTail w)) =
      (β.prod G).prod
        ((Measure.infinitePi fun _ : ℕ ↦ β).prod (Measure.infinitePi fun _ : ℕ ↦ G)) := by
  rw [← map_prod_prod_prod_comm_prod, ← map_head_tail_infinite_pi β, ← map_head_tail_infinite_pi G,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The stick-breaking cell masses solve the stick-breaking equation.** Breaking off the first
stick, `p = V₀ e(θ₀) + (1 - V₀) p'`, where `p'` is built from the shifted sequences, has the law
of `p` and is independent of `(V₀, θ₀)`; stated in integrated form. -/
private theorem integral_map_sb_cells_eq_stick (β : Measure ℝ) (G : Measure X)
    [IsProbabilityMeasure β] [IsProbabilityMeasure G] (hβ : ∀ᵐ x ∂β, x ∈ Icc (0 : ℝ) 1)
    {A : Fin k → Set X} (hAm : ∀ i, MeasurableSet (A i)) {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂((Measure.infinitePi fun _ : ℕ ↦ β).prod
        (Measure.infinitePi fun _ : ℕ ↦ G)).map (sbCells A) =
      ∫ s, ∫ y, f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • y)
        ∂((Measure.infinitePi fun _ : ℕ ↦ β).prod
          (Measure.infinitePi fun _ : ℕ ↦ G)).map (sbCells A) ∂β.prod G := by
  set M := (Measure.infinitePi fun _ : ℕ ↦ β).prod (Measure.infinitePi fun _ : ℕ ↦ G)
  have hΦ := measurable_sb_cells hAm
  have hgood : ∀ᵐ w ∂M, ∀ n, w.1 n ∈ Icc (0 : ℝ) 1 := by
    refine ae_all_iff.mpr fun n ↦ ?_
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ β) n).quasiMeasurePreserving.ae hβ
    exact Measure.quasiMeasurePreserving_fst.ae h
  have hb : Measurable fun s : ℝ × X ↦ s.1 • cellMasses A (Measure.dirac s.2) :=
    measurable_fst.smul ((measurable_cell_masses_dirac hAm).comp measurable_snd)
  have hgm : Measurable fun z : (ℝ × X) × ((ℕ → ℝ) × (ℕ → X)) ↦
      f (z.1.1 • cellMasses A (Measure.dirac z.1.2) + (1 - z.1.1) • sbCells A z.2) :=
    hf.comp ((hb.comp measurable_fst).add
      ((measurable_const.sub (measurable_fst.comp measurable_fst)).smul (hΦ.comp measurable_snd)))
  have inner : ∀ s : ℝ × X, ∫ y, f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • y)
      ∂M.map (sbCells A) =
        ∫ w, f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • sbCells A w) ∂M :=
    fun s ↦ integral_map hΦ.aemeasurable (Measurable.aestronglyMeasurable
      (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) ↦
        f (s.1 • cellMasses A (Measure.dirac s.2) + (1 - s.1) • y)))
  simp_rw [inner]
  rw [integral_map hΦ.aemeasurable hf.aestronglyMeasurable,
    ← integral_prod _ (Integrable.of_bound hgm.aestronglyMeasurable C (ae_of_all _ fun z ↦ hC _)),
    ← map_head_pair_tail, integral_map (by unfold pairTail; fun_prop) hgm.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hgood] with w hw
  rw [sb_cells_eq A hw]

/-- **Sethuraman's theorem on the canonical space.** Let `V` and `θ` be independent i.i.d.
sequences with laws `Beta(1, |α|)` and `α / |α|`, realized as coordinates on the product space.
For a measurable partition `A₁, …, A_k` of a set of full `α`-mass into cells of positive mass,
the masses of the stick-breaking measure `∑ πₖ δ_{θₖ}` on the cells have the Dirichlet law
`Dir(α(A₁), …, α(A_k))`.

Both laws solve the distributional equation `p = V e(θ) + (1 - V) p'` with `(V, θ)` independent
of `p'`, and that equation has a unique bounded solution (`eq_of_affine_fixed_point`). -/
theorem map_stick_breaking_measure_cells_eq_dirichlet_measure (α : Measure X) [IsFiniteMeasure α]
    (hα : α ≠ 0) (hk : 0 < k) {A : Fin k → Set X} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (hAc : α (⋃ i, A i)ᶜ = 0) (hApos : ∀ i, 0 < α (A i)) :
    ((Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 (α.real univ)).prod
        (Measure.infinitePi fun _ : ℕ ↦ (α univ)⁻¹ • α)).map
      (fun w ↦ WithLp.toLp 2 fun i ↦ (stickBreakingMeasure w.1 w.2).real (A i)) =
    dirichletMeasure fun i ↦ α.real (A i) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : NeZero α := ⟨hα⟩
  have ha : ∀ i, 0 < α.real (A i) := fun i ↦
    ENNReal.toReal_pos (hApos i).ne' (measure_ne_top _ _)
  have hsum := sum_measure_real_cells α hAm hAd hAc
  have hs : 0 < α.real univ := hsum ▸ Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  have := isProbabilityMeasureBeta one_pos hs
  have := isProbabilityMeasure_dirichletMeasure ha
  set β := betaMeasure 1 (α.real univ) with hβdef
  set G : Measure X := (α univ)⁻¹ • α
  set M := (Measure.infinitePi fun _ : ℕ ↦ β).prod (Measure.infinitePi fun _ : ℕ ↦ G)
  have hΦ := measurable_sb_cells hAm
  have := (Measure.isProbabilityMeasure_map_iff (μ := M) hΦ.aemeasurable).mpr inferInstance
  change M.map (sbCells A) = _
  have hβ : ∀ᵐ x ∂β, x ∈ Icc (0 : ℝ) 1 := ae_mem_Icc_betaMeasure 1 (α.real univ)
  have hρ : ∀ᵐ s ∂β.prod G, s.1 ∈ Icc (0 : ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae hβ
  have hb : Measurable fun s : ℝ × X ↦ s.1 • cellMasses A (Measure.dirac s.2) :=
    measurable_fst.smul ((measurable_cell_masses_dirac hAm).comp measurable_snd)
  have hc : Measurable fun s : ℝ × X ↦ 1 - s.1 := by fun_prop
  have hci : Integrable (fun s : ℝ × X ↦ 1 - s.1) (β.prod G) :=
    Integrable.of_bound hc.aestronglyMeasurable 1 (hρ.mono fun s hs ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2])
  have hxint : Integrable (fun x : ℝ ↦ x) β :=
    Integrable.of_bound aestronglyMeasurable_id 1 (hβ.mono fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2])
  have hq : ∫ s, (1 - s.1) ∂β.prod G < 1 := by
    have h := integral_fun_fst (μ := β) (ν := G) (fun x : ℝ ↦ 1 - x)
    rw [h, probReal_univ, one_smul, integral_sub (integrable_const 1) hxint, integral_const,
      probReal_univ, one_smul, hβdef, integral_id_betaMeasure one_pos hs]
    have : 0 < 1 / (1 + α.real univ) := by positivity
    linarith
  have h₁ : ∀ᵐ y ∂M.map (sbCells A), ‖y‖ ≤ Real.sqrt k :=
    (ae_map_iff hΦ.aemeasurable (measurableSet_le measurable_norm measurable_const)).mpr
      (by
        filter_upwards [show ∀ᵐ w ∂M, ∀ n, w.1 n ∈ Icc (0 : ℝ) 1 from ae_all_iff.mpr fun n ↦
          Measure.quasiMeasurePreserving_fst.ae
            ((measurePreserving_eval_infinitePi (fun _ : ℕ ↦ β) n).quasiMeasurePreserving.ae hβ)]
          with w hw
        exact norm_sb_cells_le A hw)
  have h₂ : ∀ᵐ y ∂dirichletMeasure (fun i ↦ α.real (A i)), ‖y‖ ≤ Real.sqrt k :=
    ae_norm_le_one_dirichletMeasure.mono fun y hy ↦
      hy.trans (Real.one_le_sqrt.mpr (by exact_mod_cast hk))
  refine eq_of_affine_fixed_point (β.prod G) hb hc (hρ.mono fun s hs ↦ sub_nonneg.mpr hs.2) hci hq
    h₁ h₂ ?_ ?_
  · rintro f ⟨C, hC⟩ ⟨K, hK⟩
    exact integral_map_sb_cells_eq_stick β G hβ hAm hK.continuous.measurable
      (norm_le_of_dist_le hC)
  · rintro f ⟨C, hC⟩ ⟨K, hK⟩
    exact integral_dirichlet_measure_eq_stick α hα hk hAm hAd hAc hApos hK.continuous.measurable
      (norm_le_of_dist_le hC)

end Sethuraman

end CKSD
