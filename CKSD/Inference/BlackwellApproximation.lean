module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
/-!
# Finite quantizations and compact limits for Blackwell comparison

Mathlib's nearest points in a countable dense sequence give measurable finite
quantizations converging pointwise to the identity. On compact metric spaces,
normalization reduces subsequence compactness of finite measures of fixed mass
to compactness and metrizability of probability measures. These approximation
steps extend finite-action randomizations to compact likelihood-vector laws.
-/
public section
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal
namespace CKSD

/-- Every nonempty separable metric space has measurable finite quantizations converging
pointwise to the identity. The action set at stage `n` has `n + 1` elements. -/
theorem exists_measurable_finite_quantizations
    (C : Type*) [MetricSpace C] [MeasurableSpace C] [BorelSpace C]
    [SeparableSpace C] [Nonempty C] :
    ∃ q : ∀ n, C → Fin (n + 1), (∀ n, Measurable (q n)) ∧
      ∃ v : ∀ n, Fin (n + 1) → C,
        ∀ x, Tendsto (fun n ↦ v n (q n x)) atTop (𝓝 x) := by
  let e : ℕ → C := denseSeq C
  let q : ∀ n, C → Fin (n + 1) := fun n x ↦ Fin.ofNat (n + 1) (SimpleFunc.nearestPtInd e n x)
  refine ⟨q, fun n ↦ ?_, fun n i ↦ e i.val, fun x ↦ ?_⟩
  · exact (measurable_of_countable (fun k : ℕ ↦ Fin.ofNat (n + 1) k)).comp
      (SimpleFunc.nearestPtInd e n).measurable
  · have he (n : ℕ) : e (q n x).val = SimpleFunc.nearestPt e n x := by
      dsimp only [q]
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le (SimpleFunc.nearestPtInd_le e n x))]
      rfl
    have hx : x ∈ closure (range e) := (denseRange_denseSeq C) x
    simpa only [he] using SimpleFunc.tendsto_nearestPt (e := e) hx

/-- Finite measures of fixed mass on a compact metric space admit a weakly convergent
subsequence. Normalization reduces this to compactness of probability measures. -/
theorem exists_finiteMeasure_subsequence_limit_of_mass_eq
    {C : Type*} [MetricSpace C] [MeasurableSpace C] [BorelSpace C]
    [CompactSpace C] [SeparableSpace C] [Nonempty C]
    (μ : ℕ → FiniteMeasure C) (M : ℝ≥0) (hM : ∀ n, (μ n).mass = M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : FiniteMeasure C,
      Tendsto (fun n ↦ μ (φ n)) atTop (𝓝 ν) := by
  obtain ⟨ρ, -, φ, hφ, hlim⟩ := isCompact_univ.isSeqCompact
    (fun n ↦ (mem_univ ((μ n).normalize)))
  have hf : Tendsto (fun n ↦ (μ (φ n)).normalize.toFiniteMeasure) atTop (𝓝 ρ.toFiniteMeasure) := by
    have hh := (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).1 hlim
    convert hh using 1; rfl
  refine ⟨φ, hφ, M • ρ.toFiniteMeasure, ?_⟩
  have hs := (tendsto_const_nhds (x := M)).smul hf
  convert hs using 1
  funext n
  rw [← hM (φ n), ← FiniteMeasure.self_eq_mass_smul_normalize]

end CKSD
