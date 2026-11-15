module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import CKSD.Inference.Basic

/-!
# Hadamard differentiability and the functional delta method

## Main definitions

* `CKSD.HasHadamardFDerivAt`: sequential Hadamard differentiability tangentially to a subspace.

## Main results

* `CKSD.tendstoInDistribution_of_hasHadamardFDerivAt`: the functional delta method
  (GAPS 102.28).

## References

van der Vaart, *Asymptotic Statistics*, Chapter 20. The proof uses Mathlib's closed-set
portmanteau theorem (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`,
`tendsto_of_forall_isClosed_limsup_le'`).
-/
public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CKSD

/-- Sequential tangential Hadamard differentiability, with a continuous linear extension. -/
def HasHadamardFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (domain : Set E)
    (D₀ : Submodule ℝ E) (D : E →L[ℝ] F) (θ : E) : Prop :=
  θ ∈ domain ∧ ∀ (t : ℕ → ℝ) (h : ℕ → E) (v : E),
    (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) → Tendsto h atTop (𝓝 v) → v ∈ D₀ →
    (∀ n, θ + t n • h n ∈ domain) →
    Tendsto (fun n ↦ (t n)⁻¹ • (g (θ + t n • h n) - g θ)) atTop (𝓝 (D v))

/-- GAPS 102.28: functional delta method for measurable maps and a closed tangent space.
The outer version for nonmeasurable empirical processes uses `TendstoInOuterDistribution`. -/
theorem tendstoInDistribution_of_hasHadamardFDerivAt
    {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → E) (hT : ∀ n, Measurable (T n))
    (θ : E) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop atTop)
    (G : Measure E) [IsProbabilityMeasure G] (D₀ : Submodule ℝ E) (hclosed : IsClosed (D₀ : Set E))
    (hsupp : G D₀ = 1) (g : E → F) (hg : Measurable g) (domain : Set E)
    (hdomain : ∀ n ω, T n ω ∈ domain) (D : E →L[ℝ] F)
    (hd : HasHadamardFDerivAt g domain D₀ D θ)
    (hlim : TendstoInDistribution (fun (n : ℕ) ω ↦ r n • (T n ω - θ)) atTop id (fun _ ↦ μ) G) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ r n • (g (T n ω) - g θ)) atTop id (fun _ ↦ μ)
      (G.map D) := by
  set Z : ℕ → Ω → E := fun n ω ↦ r n • (T n ω - θ) with hZ
  set Y : ℕ → Ω → F := fun n ω ↦ r n • (g (T n ω) - g θ) with hY
  have hZm : ∀ n, Measurable (Z n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hT n)
  have hYm : ∀ n, Measurable (Y n) := fun n ↦
    ((continuous_id.sub continuous_const).const_smul _).measurable.comp (hg.comp (hT n))
  -- Probability-measure versions of the laws.
  let PZ : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μ.map (Z n), inferInstance⟩
  let PY : ℕ → ProbabilityMeasure F := fun n ↦ ⟨μ.map (Y n), inferInstance⟩
  let PG : ProbabilityMeasure E := ⟨G, inferInstance⟩
  let PGD : ProbabilityMeasure F := ⟨G.map D, inferInstance⟩
  have hZlim : Tendsto PZ atTop (𝓝 PG) := (tendstoInDistribution_id_iff.1 hlim).2
  suffices hYlim : Tendsto PY atTop (𝓝 PGD) from
    tendstoInDistribution_id_iff.2 ⟨fun n ↦ (hYm n).aemeasurable, hYlim⟩
  refine tendsto_of_forall_isClosed_limsup_le' fun Fc hFc ↦ ?_
  -- The sets of local increments mapped into `Fc` at stage `m`.
  let A : ℕ → Set E := fun m ↦
    {h | θ + (r m)⁻¹ • h ∈ domain ∧ r m • (g (θ + (r m)⁻¹ • h) - g θ) ∈ Fc}
  let C : ℕ → Set E := fun k ↦ closure (⋃ m ≥ k, A m)
  have hCc : ∀ k, IsClosed (C k) := fun k ↦ isClosed_closure
  have hCanti : Antitone C := fun k l hkl ↦
    closure_mono (iUnion₂_subset fun m hm ↦ subset_iUnion₂_of_subset m (hkl.trans hm) le_rfl)
  have hTZ : ∀ n ω, θ + (r n)⁻¹ • Z n ω = T n ω := fun n ω ↦ by
    simp only [hZ, smul_smul, inv_mul_cancel₀ (hr n).ne', one_smul, add_sub_cancel]
  -- Step 1: bound the laws of `Yₙ` on `Fc` by those of `Zₙ` on `C k`.
  have hstep : ∀ k, limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (C k) := by
    intro k
    have hle : ∀ n ≥ k, (PY n : Measure F) Fc ≤ (PZ n : Measure E) (C k) := by
      intro n hn
      simp only [PY, PZ, ProbabilityMeasure.coe_mk]
      rw [Measure.map_apply (hYm n) hFc.measurableSet,
        Measure.map_apply (hZm n) (hCc k).measurableSet]
      refine measure_mono fun ω hω ↦ subset_closure ?_
      refine mem_iUnion₂.2 ⟨n, hn, ?_⟩
      simp only [A, mem_ofPred_eq, hTZ]
      exact ⟨hdomain n ω, hω⟩
    calc limsup (fun n ↦ (PY n : Measure F) Fc) atTop
        ≤ limsup (fun n ↦ (PZ n : Measure E) (C k)) atTop :=
          limsup_le_limsup (eventually_atTop.2 ⟨k, hle⟩)
      _ ≤ G (C k) := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hZlim (hCc k)
  -- Step 2: pass to the intersection.
  have hInter : Tendsto (fun k ↦ G (C k)) atTop (𝓝 (G (⋂ k, C k))) :=
    tendsto_measure_iInter_atTop (fun k ↦ (hCc k).measurableSet.nullMeasurableSet) hCanti
      ⟨0, measure_ne_top _ _⟩
  have hlimsup : limsup (fun n ↦ (PY n : Measure F) Fc) atTop ≤ G (⋂ k, C k) :=
    ge_of_tendsto hInter (Eventually.of_forall hstep)
  -- Step 3: on `D₀`, the intersection maps into `Fc`.
  have hsub : (⋂ k, C k) ∩ D₀ ⊆ D ⁻¹' Fc := by
    rintro v ⟨hv, hvD⟩
    have hvk : ∀ k : ℕ, ∃ m, k ≤ m ∧ ∃ h ∈ A m, dist h v < 1 / ((k : ℝ) + 1) := by
      intro k
      have hk := mem_iInter.1 hv k
      obtain ⟨h, hh, hdist⟩ := Metric.mem_closure_iff.1 hk _ Nat.one_div_pos_of_nat
      obtain ⟨m, hm, hhm⟩ := mem_iUnion₂.1 hh
      exact ⟨m, hm, h, hhm, by rwa [dist_comm]⟩
    choose m hm h hhA hhd using hvk
    have hmlim : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
    have ht : Tendsto (fun k ↦ (r (m k))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hrlim.comp hmlim)
    have hh : Tendsto h atTop (𝓝 v) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hhd k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := hd.2 (fun k ↦ (r (m k))⁻¹) h v (fun k ↦ inv_pos.2 (hr _)) ht hh hvD
      (fun k ↦ (hhA k).1)
    simp only [inv_inv] at hconv
    exact hFc.mem_of_tendsto hconv (Eventually.of_forall fun k ↦ (hhA k).2)
  -- Step 4: conclude.
  have hD0c : G (D₀ : Set E)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hclosed.measurableSet, hsupp, tsub_self]
  refine hlimsup.trans ?_
  simp only [PGD, ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply D.continuous.measurable hFc.measurableSet]
  calc G (⋂ k, C k) ≤ G (((⋂ k, C k) ∩ D₀) ∪ (D₀ : Set E)ᶜ) := by
        refine measure_mono fun v hv ↦ ?_
        by_cases hvD : v ∈ (D₀ : Set E)
        · exact Or.inl ⟨hv, hvD⟩
        · exact Or.inr hvD
    _ ≤ G ((⋂ k, C k) ∩ D₀) + G (D₀ : Set E)ᶜ := measure_union_le _ _
    _ ≤ G (D ⁻¹' Fc) := by rw [hD0c, add_zero]; exact measure_mono hsub

end CKSD
