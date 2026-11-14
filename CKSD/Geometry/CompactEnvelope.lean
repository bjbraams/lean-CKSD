module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Differentiating compact quadratic envelopes

A compact minimization problem has the expected directional derivative when all minimizers of
the unperturbed energy have the same linear coefficient. Lower semicontinuity of `A` and `A ± B`
suffices; the coefficient itself need not be continuous. This form is suitable for transport plans
with a measurable square-integrable displacement field.

The proof uses compactness to identify the linear coefficient of every sequence of perturbed
minimizers. The quadratic remainder then vanishes in the difference quotient.

## Main results

* `CKSD.tendsto_coefficient_of_compact_minimization`: convergence of minimizing coefficients.
* `CKSD.hasDerivAt_compact_quadratic_minimum`: differentiation of the quadratic envelope.
-/

public section
noncomputable section
open Filter Set Topology
namespace CKSD

/-- A lower semicontinuous function is bounded above at a sequential limit by the limit of its
  values. -/
lemma lowerSemicontinuousOn_le_of_tendsto {X : Type*} [TopologicalSpace X]
    {S : Set X} {f : X → ℝ} (hf : LowerSemicontinuousOn f S)
    {q : ℕ → X} {x : X} {b : ℝ} (hx : x ∈ S) (hq : ∀ n, q n ∈ S)
    (hqx : Tendsto q atTop (𝓝 x)) (hb : Tendsto (fun n ↦ f (q n)) atTop (𝓝 b)) :
    f x ≤ b := by
  by_contra h
  obtain ⟨c, hbc, hcf⟩ := exists_between (lt_of_not_ge h)
  have hqs : Tendsto q atTop (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqx, Eventually.of_forall hq⟩
  have hgt := hqs.eventually ((hf x hx) c hcf)
  have hlt := hb.eventually (gt_mem_nhds hbc)
  obtain ⟨n, hn₁, hn₂⟩ := (hgt.and hlt).exists
  exact (lt_asymm hn₁ hn₂)

/-- In a compact minimization problem, nearly minimizing affine perturbations have the unique
coefficient attained by minimizers of the unperturbed energy. Only lower semicontinuity of the
three energies `A`, `A+B`, and `A-B` is required. -/
theorem tendsto_coefficient_of_compact_minimization {X I : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {l : Filter I} [l.IsCountablyGenerated]
    {S : Set X} (hS : IsCompact S) (A B : X → ℝ)
    (hA : LowerSemicontinuousOn A S)
    (hAp : LowerSemicontinuousOn (fun x ↦ A x + B x) S)
    (hAm : LowerSemicontinuousOn (fun x ↦ A x - B x) S)
    (a D M : ℝ) (ha : ∀ x ∈ S, a ≤ A x)
    (hD : ∀ x ∈ S, A x = a → B x = D) (hB : ∀ x ∈ S, |B x| ≤ M)
    (q : I → X) (hq : ∀ i, q i ∈ S) (t : I → ℝ) (ht : Tendsto t l (𝓝 0))
    (hmin : ∀ i, A (q i) + t i * B (q i) ≤ a + t i * D) :
    Tendsto (fun i ↦ B (q i)) l (𝓝 D) := by
  have hAlim : Tendsto (fun i ↦ A (q i)) l (𝓝 a) := by
    have herror : Tendsto (fun i ↦ |t i| * (M + |D|)) l (𝓝 0) := by
      simpa using ht.abs.mul_const (M + |D|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add herror) (fun i ↦ ha _ (hq i)) ?_
    intro i
    have hi := hmin i
    have hb := hB _ (hq i)
    have hprod := le_abs_self (t i * (D - B (q i)))
    have hdiff : |D - B (q i)| ≤ |D| + M :=
      (abs_sub _ _).trans (by linarith)
    have hbd := mul_le_mul_of_nonneg_left hdiff (abs_nonneg (t i))
    rw [abs_mul] at hprod
    nlinarith
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hmem : ∀ n, (q (ns n), B (q (ns n))) ∈ S ×ˢ Icc (-M) M := by
    intro n
    exact ⟨hq _, abs_le.mp (hB _ (hq _))⟩
  obtain ⟨⟨x, b⟩, hxb, ms, hms, hlim⟩ :=
    (hS.prod isCompact_Icc).isSeqCompact.subseq_of_frequently_in
      (Frequently.of_forall hmem)
  have hxlim : Tendsto (fun n ↦ q (ns (ms n))) atTop (𝓝 x) :=
    (continuous_fst.tendsto (x, b)).comp hlim
  have hblim : Tendsto (fun n ↦ B (q (ns (ms n)))) atTop (𝓝 b) :=
    (continuous_snd.tendsto (x, b)).comp hlim
  have halim : Tendsto (fun n ↦ A (q (ns (ms n)))) atTop (𝓝 a) :=
    hAlim.comp (hns.comp hms.tendsto_atTop)
  have hqmem : ∀ n, q (ns (ms n)) ∈ S := fun n ↦ hq _
  have hax : A x = a := le_antisymm
    (lowerSemicontinuousOn_le_of_tendsto hA hxb.1 hqmem hxlim halim) (ha x hxb.1)
  have hp := lowerSemicontinuousOn_le_of_tendsto hAp hxb.1 hqmem hxlim
    (halim.add hblim)
  have hm := lowerSemicontinuousOn_le_of_tendsto hAm hxb.1 hqmem hxlim
    (halim.sub hblim)
  have hbx : B x = b := by linarith
  have hbD : b = D := hbx.symm.trans (hD x hxb.1 hax)
  exact ⟨ms, hbD ▸ hblim⟩

/-- A compact quadratic-envelope differentiation rule. The first-order coefficient need only
be uniquely determined among minimizers; the minimizing point itself may not be unique. -/
theorem hasDerivAt_compact_quadratic_minimum {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {S : Set X} (hS : IsCompact S) (A B : X → ℝ)
    (hA : LowerSemicontinuousOn A S)
    (hAp : LowerSemicontinuousOn (fun x ↦ A x + B x) S)
    (hAm : LowerSemicontinuousOn (fun x ↦ A x - B x) S)
    (a D M C : ℝ) (ha : ∀ x ∈ S, a ≤ A x)
    (hD : ∀ x ∈ S, A x = a → B x = D) (hB : ∀ x ∈ S, |B x| ≤ M)
    (q : ℝ → X) (hq : ∀ t, q t ∈ S)
    (hmin : ∀ t, A (q t) + t * B (q t) ≤ a + t * D) :
    HasDerivAt (fun t ↦ A (q t) + t * B (q t) + t ^ 2 * C) D 0 := by
  let f : ℝ → ℝ := fun t ↦ A (q t) + t * B (q t) + t ^ 2 * C
  have hbase : f 0 = a := by
    have h₁ := ha _ (hq 0)
    have h₂ := hmin 0
    dsimp [f]
    simp only [zero_mul, zero_pow two_ne_zero, add_zero] at h₂ ⊢
    exact le_antisymm h₂ h₁
  have hcoef : Tendsto (fun t ↦ B (q t)) (𝓝[≠] 0) (𝓝 D) :=
    tendsto_coefficient_of_compact_minimization hS A B hA hAp hAm a D M ha hD hB q hq
      id (tendsto_id.mono_left nhdsWithin_le_nhds) hmin
  have hbound : ∀ t ≠ 0,
      |t⁻¹ * (f t - a) - D| ≤ |B (q t) - D| + |t| * |C| := by
    intro t ht
    have h₁ := ha _ (hq t)
    have h₂ := hmin t
    set r := f t - a - t * D - t ^ 2 * C with hr
    have hr₀ : r ≤ 0 := by dsimp [r, f]; linarith
    have hr₁ : -r ≤ |t| * |B (q t) - D| := by
      have hprod := neg_le_abs (t * (B (q t) - D))
      rw [abs_mul] at hprod
      dsimp [r, f]
      nlinarith
    have hrabs : |r| ≤ |t| * |B (q t) - D| := by
      rwa [abs_of_nonpos hr₀]
    have heq : t⁻¹ * (f t - a) - D = r / t + t * C := by
      dsimp [r]
      field_simp; ring
    rw [heq]
    calc |r / t + t * C| ≤ |r / t| + |t * C| := abs_add_le _ _
      _ = |r| / |t| + |t| * |C| := by rw [abs_div, abs_mul]
      _ ≤ |B (q t) - D| + |t| * |C| := by
        gcongr
        exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by simpa [mul_comm] using hrabs)
  have herror : Tendsto (fun t : ℝ ↦ |B (q t) - D| + |t| * |C|)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hcoef.sub (tendsto_const_nhds (x := D))).abs.add
      (((tendsto_id.mono_left nhdsWithin_le_nhds).abs).mul_const |C|)
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hslope : Tendsto (fun t : ℝ ↦ |t⁻¹ * (f t - a) - D|) (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _)
      (hne.mono fun t ht ↦ hbound t ht)
      herror
  -- Name the quadratic envelope before applying the difference-quotient criterion.
  change HasDerivAt f D 0
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hs : Tendsto (fun t : ℝ ↦ t⁻¹ * (f t - a)) (𝓝[≠] 0) (𝓝 D) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hslope)
  simpa only [zero_add, smul_eq_mul, hbase] using hs

end CKSD
