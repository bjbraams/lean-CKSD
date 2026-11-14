module

public import CKSD.Inference.Model
import CKSD.Inference.BlackwellApproximation
import CKSD.Inference.BlackwellCoupling

/-!
# Joint limits realizing finite randomizations

Exact randomizations to finite quantizations yield finite joint measures on a
compact likelihood cube. One weakly convergent subsequence preserves the first
marginal and every bounded continuous coordinate tilt. Disintegration then
provides a common randomization kernel. This is the compactness extension of
finite-action Blackwell comparison to general dominated observations.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace CKSD

/-- Exact finite randomizations produce a joint likelihood-vector law with every required
coordinate-weighted marginal. Compactness chooses one joint subsequence for all parameters. -/
theorem exists_joint_of_finite_randomizations
    {Θ X Y C : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MetricSpace C] [MeasurableSpace C] [BorelSpace C]
    [SecondCountableTopology C] [CompactSpace C] [Nonempty C]
    (μ : Measure X) [IsFiniteMeasure μ]
    (P : Θ → Measure X) (Q : Θ → Measure Y) [∀ θ, IsFiniteMeasure (Q θ)]
    (u : X → C) (hu : Measurable u) (v : Y → C) (hv : Measurable v)
    (w : Θ → BoundedContinuousFunction C ℝ) (hw : ∀ θ x, 0 ≤ w θ x)
    (hP : ∀ θ, P θ = μ.withDensity (fun x ↦ ENNReal.ofReal (w θ (u x))))
    (hfinite : ∀ n : ℕ, 0 < n → ∀ q : Y → Fin n, Measurable q →
      ∃ δ : RandomizedDecisionRule X (Fin n), ∀ θ, δ.val ∘ₘ P θ = (Q θ).map q) :
    ∃ ρ : FiniteMeasure (C × C), (ρ : Measure (C × C)).fst = μ.map u ∧
      ∀ θ, ((ρ : Measure (C × C)).withDensity
        (fun p ↦ ENNReal.ofReal (w θ p.1))).snd = (Q θ).map v := by
  obtain ⟨q, hq, r, hr⟩ := exists_measurable_finite_quantizations C
  choose δ hδ using fun n ↦ hfinite (n + 1) (Nat.succ_pos n) (q n ∘ v) ((hq n).comp hv)
  have hδm : ∀ n, IsMarkovKernel (δ n).val := fun n ↦ (δ n).property
  let := hδm
  have hrm (n : ℕ) : Measurable (r n) := measurable_of_countable _
  let R : ℕ → FiniteMeasure (C × C) := fun n ↦
    ⟨(μ ⊗ₘ (δ n).val).map (fun p : X × Fin (n + 1) ↦ (u p.1, r n p.2)), inferInstance⟩
  have hfst (n : ℕ) : (R n : Measure (C × C)).fst = μ.map u :=
    fst_map_comp_prod μ (δ n).val u hu (r n) (hrm n)
  let μu : FiniteMeasure C := ⟨μ.map u, inferInstance⟩
  have hmass (n : ℕ) : (R n).mass = μu.mass := by
    -- Express finite-measure coercions as their underlying mapped measures.
    change ((R n : Measure (C × C)) univ).toNNReal = ((μ.map u) univ).toNNReal
    apply congrArg ENNReal.toNNReal
    simpa only [Measure.fst_apply MeasurableSet.univ, Set.preimage_univ] using
      congrArg (fun η : Measure C ↦ η univ) (hfst n)
  obtain ⟨φ, hφ, ρ, hρ⟩ := exists_finite_measure_subsequence_limit_of_mass_eq R μu.mass hmass
  have hmap : Tendsto (fun n ↦ (R (φ n)).map Prod.fst) atTop (𝓝 (ρ.map Prod.fst)) :=
    FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hρ continuous_fst
  have hmaps (n : ℕ) : (R (φ n)).map Prod.fst = μu := by
    apply Subtype.ext
    exact hfst (φ n)
  simp only [hmaps] at hmap
  have hρfst : (ρ : Measure (C × C)).fst = μ.map u := by
    have he := tendsto_nhds_unique hmap tendsto_const_nhds
    exact congrArg FiniteMeasure.toMeasure he
  refine ⟨ρ, hρfst, fun θ ↦ ?_⟩
  let ν : FiniteMeasure C := ⟨(Q θ).map v, inferInstance⟩
  let νs : ℕ → FiniteMeasure C := fun n ↦ ν.map (r n ∘ q n)
  have hν : Tendsto νs atTop (𝓝 ν) := by
    have hh := finite_measure_tendsto_map_of_pointwise ν (fun n ↦ r n ∘ q n)
      (fun n ↦ (hrm n).comp (hq n)) id measurable_id hr
    have hid : ν.map id = ν := by
      apply Subtype.ext
      exact Measure.map_id
    simpa only [hid] using hh
  have hweighted (n : ℕ) : ((R n : Measure (C × C)).withDensity
      (fun p ↦ ENNReal.ofReal (w θ p.1))).snd = (νs n : Measure C) := by
    -- Express finite-measure coercions as their underlying mapped measures.
    change (((μ ⊗ₘ (δ n).val).map (fun p : X × Fin (n + 1) ↦ (u p.1, r n p.2))).withDensity
      (fun p ↦ ENNReal.ofReal (w θ p.1))).snd = _
    rw [snd_with_density_map_comp_prod μ (δ n).val u hu (r n) (hrm n)
      (fun c ↦ ENNReal.ofReal (w θ c)) (by fun_prop)]
    have hd : μ.withDensity ((fun c ↦ ENNReal.ofReal (w θ c)) ∘ u) = P θ := (hP θ).symm
    rw [hd, hδ n θ, Measure.map_map (hrm n) ((hq n).comp hv)]
    -- Express finite-measure coercions as their underlying mapped measures.
    change (Q θ).map (r n ∘ (q n ∘ v)) = ((Q θ).map v).map (r n ∘ q n)
    rw [Measure.map_map ((hrm n).comp (hq n)) hv]
    rfl
  exact snd_with_density_eq_of_finite_measure_tendsto (fun n ↦ R (φ n)) ρ hρ
    (fun n ↦ νs (φ n)) ν (hν.comp hφ.tendsto_atTop) (w θ) (hw θ)
    (fun n ↦ hweighted (φ n))

end CKSD
