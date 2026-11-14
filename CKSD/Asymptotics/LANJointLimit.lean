module

public import CKSD.Asymptotics.Basic
public import TauCeti.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
/-!
# Joint subsequence limits

Polish marginal weak limits imply joint tightness and hence one joint subsequence
limit. The proof uses Mathlib product tightness and Prokhorov compactness, with
pinned TauCeti supplying tightness of a weakly convergent sequence. This is the
compactness step in van der Vaart, *Asymptotic Statistics*, Theorem 7.10, p. 99.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace CKSD
/-- Convergent Polish marginals admit one joint weakly convergent subsequence. -/
theorem exists_joint_subsequence_limit_of_marginal_limits
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {A B : Type*} [MeasurableSpace A] [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
    [MeasurableSpace B] [TopologicalSpace B] [PolishSpace B] [BorelSpace B]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → A) (Y : ∀ n, Ω n → B)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (hμ : TendstoInDistribution X atTop id P μ) (hν : TendstoInDistribution Y atTop id P ν) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ρ : ProbabilityMeasure (A × B),
      TendstoInDistribution (fun k ω ↦ (X (φ k) ω,Y (φ k) ω)) atTop id (fun k ↦ P (φ k)) (ρ : Measure (A × B)) ∧
      (ρ : Measure (A × B)).fst=μ ∧ (ρ : Measure (A × B)).snd=ν := by
  let : MetricSpace A := TopologicalSpace.completelyMetrizableMetric A
  let : MetricSpace B := TopologicalSpace.completelyMetrizableMetric B
  let PX : ℕ → ProbabilityMeasure A := fun n ↦ ⟨(P n).map (X n),inferInstance⟩
  let PY : ℕ → ProbabilityMeasure B := fun n ↦ ⟨(P n).map (Y n),inferInstance⟩
  let J : ℕ → ProbabilityMeasure (A × B) := fun n ↦
    ⟨(P n).map (fun ω ↦ (X n ω,Y n ω)),inferInstance⟩
  have hPX : Tendsto PX atTop (𝓝 ⟨μ,inferInstance⟩) := by
    simpa only [PX,Measure.map_id] using hμ.tendsto
  have hPY : Tendsto PY atTop (𝓝 ⟨ν,inferInstance⟩) := by
    simpa only [PY,Measure.map_id] using hν.tendsto
  have hfst (n : ℕ) : ((J n : Measure (A × B))).fst=(PX n : Measure A) := by
    change ((P n).map (fun ω ↦ (X n ω,Y n ω))).map Prod.fst=(P n).map (X n)
    rw [Measure.map_map measurable_fst ((hX n).prodMk (hY n))]
    rfl
  have hsnd (n : ℕ) : ((J n : Measure (A × B))).snd=(PY n : Measure B) := by
    change ((P n).map (fun ω ↦ (X n ω,Y n ω))).map Prod.snd=(P n).map (Y n)
    rw [Measure.map_map measurable_snd ((hX n).prodMk (hY n))]
    rfl
  have hT : IsTightMeasureSet (range fun n ↦ (J n : Measure (A × B))) := by
    apply IsTightMeasureSet.prodMk
    · apply (TauCeti.isTightMeasureSet_range_of_tendsto hPX).subset
      rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
      exact ⟨n,(hfst n).symm⟩
    · apply (TauCeti.isTightMeasureSet_range_of_tendsto hPY).subset
      rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
      exact ⟨n,(hsnd n).symm⟩
  have hC : IsCompact (closure (range J)) := isCompact_closure_of_isTightMeasureSet
    (hT.subset (by rintro _ ⟨_,⟨n,rfl⟩,rfl⟩; exact ⟨n,rfl⟩))
  obtain ⟨ρ,-,φ,hφ,hφlim⟩ := hC.isSeqCompact (fun n ↦ subset_closure (mem_range_self n))
  have hjoint : TendstoInDistribution (fun k ω ↦ (X (φ k) ω,Y (φ k) ω)) atTop id
      (fun k ↦ P (φ k)) (ρ : Measure (A × B)) := by
    refine ⟨fun k ↦ ((hX _).prodMk (hY _)).aemeasurable,measurable_id.aemeasurable,?_⟩
    have heta : (⟨(ρ : Measure (A × B)),inferInstance⟩ : ProbabilityMeasure (A × B)) = ρ := by
      exact Subtype.eta _ _
    simp only [Measure.map_id,heta]
    convert hφlim using 1; rfl
  have hμsub : TendstoInDistribution (fun k ↦ X (φ k)) atTop id (fun k ↦ P (φ k)) μ :=
    ⟨fun k ↦ (hX _).aemeasurable,measurable_id.aemeasurable,hμ.tendsto.comp hφ.tendsto_atTop⟩
  have hνsub : TendstoInDistribution (fun k ↦ Y (φ k)) atTop id (fun k ↦ P (φ k)) ν :=
    ⟨fun k ↦ (hY _).aemeasurable,measurable_id.aemeasurable,hν.tendsto.comp hφ.tendsto_atTop⟩
  refine ⟨φ,hφ,ρ,hjoint,?_,?_⟩
  · have h := tendstoInDistribution_unique (fun k ↦ X (φ k))
      (hjoint.continuous_comp continuous_fst) hμsub
    simpa only [Function.comp_def,Measure.map_id,Measure.fst,id_eq] using h
  · have h := tendstoInDistribution_unique (fun k ↦ Y (φ k))
      (hjoint.continuous_comp continuous_snd) hνsub
    simpa only [Function.comp_def,Measure.map_id,Measure.snd,id_eq] using h
end CKSD
