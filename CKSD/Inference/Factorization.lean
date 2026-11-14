module

public import CKSD.Inference.Basic
public import CKSD.Inference.Density
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.CondDistrib


/-!
# Inference: the factorization theorem

Tools for GAPS 101.1 and 101.2 for a family of laws with densities `f θ` with respect to a
σ-finite measure `μ`.

* `exists_absolutely_continuous_countable_mixture`: the Halmos–Savage lemma in density form; the
  family is dominated by a countable mixture `∑ 2^{-(n+1)} P (θs n)` of its members.
* `exists_factorization_of_is_sufficient_statistic`: a statistic with a common disintegrating
  kernel gives a factorization `f θ = g θ ∘ T * h` almost everywhere.
* `is_sufficient_statistic_of_factorization`: conversely, a factorization gives a common kernel,
  namely the conditional distribution of the sample given `T` under the dominating mixture
  (the sample space is standard Borel).

Sources: `GAPS.md` and `SYNOPSIS101.md`. The proofs use Mathlib's Radon–Nikodym derivatives,
`Measure.toFinite`, `Measure.withDensity_compProd`, and `ProbabilityTheory.condDistrib`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace CKSD

variable {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]

/-- The weights `2^{-(n+1)}` used for countable mixtures. -/
def mixtureWeight (n : ℕ) : ℝ≥0∞ := (2 ^ (n + 1))⁻¹

/-- The mixture weights are nonzero. -/
theorem mixture_weight_ne_zero (n : ℕ) : mixtureWeight n ≠ 0 := by
  simp [mixtureWeight]

/-- The mixture weights sum to one. -/
theorem tsum_mixture_weight : ∑' n, mixtureWeight n = 1 := by
  unfold mixtureWeight
  have h : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 2⁻¹ ^ n * 2⁻¹ := fun n ↦ by
    rw [ENNReal.inv_pow, pow_succ]
  simp_rw [h]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The countable mixture `∑ 2^{-(n+1)} P (θs n)`. -/
def countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) : Measure X :=
  Measure.sum fun n ↦ mixtureWeight n • P (θs n)

/-- A countable mixture of probability measures has total mass one. -/
theorem countable_mixture_univ (P : Θ → Measure X) (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (θs : ℕ → Θ) : countableMixture P θs univ = 1 := by
  simp [countableMixture, Measure.sum_apply _ MeasurableSet.univ, tsum_mixture_weight]

/-- A countable mixture of probability measures is a probability measure. -/
instance (P : Θ → Measure X) [hP : ∀ θ, IsProbabilityMeasure (P θ)] (θs : ℕ → Θ) :
    IsProbabilityMeasure (countableMixture P θs) :=
  ⟨countable_mixture_univ P hP θs⟩

/-- A measurable set is null for a countable mixture iff it is null for every component. -/
theorem countable_mixture_apply_eq_zero (P : Θ → Measure X) (θs : ℕ → Θ) {A : Set X}
    (hA : MeasurableSet A) :
    countableMixture P θs A = 0 ↔ ∀ n, P (θs n) A = 0 := by
  simp [countableMixture, Measure.sum_apply _ hA, mixture_weight_ne_zero]

/-- Each component of a countable mixture is absolutely continuous with respect to it. -/
theorem absolutely_continuous_countable_mixture (P : Θ → Measure X) (θs : ℕ → Θ) (n : ℕ) :
    P (θs n) ≪ countableMixture P θs := by
  refine Measure.AbsolutelyContinuous.mk fun A hA h ↦ ?_
  exact (countable_mixture_apply_eq_zero P θs hA).1 h n

/-- Halmos–Savage lemma, density form: a family of laws with densities with respect to a
σ-finite measure is dominated by one of its countable mixtures. -/
theorem exists_absolutely_continuous_countable_mixture [Nonempty Θ] (P : Θ → Measure X)
    (μ : Measure X) [SigmaFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs := by
  classical
  set ν := μ.toFinite
  let C : Θ → Set X := fun θ ↦ {x | ENNReal.ofReal (f θ x) ≠ 0}
  have hCm : ∀ θ, MeasurableSet (C θ) := fun θ ↦
    (ENNReal.measurable_ofReal.comp (hf θ).1) (measurableSet_singleton 0).compl
  let U : (ℕ → Θ) → Set X := fun θs ↦ ⋃ n, C (θs n)
  let A : Set ℝ := range fun θs ↦ ν.real (U θs)
  have hAne : A.Nonempty := ⟨_, ⟨fun _ ↦ Classical.arbitrary Θ, rfl⟩⟩
  have hAbdd : BddAbove A := ⟨ν.real univ, by
    rintro _ ⟨θs, rfl⟩; exact measureReal_mono (subset_univ _)⟩
  obtain ⟨u, -, hu, huA⟩ := exists_seq_tendsto_sSup hAne hAbdd
  choose θss hθss using huA
  let θstar : ℕ → Θ := fun m ↦ θss (Nat.unpair m).1 (Nat.unpair m).2
  have hUstar : ∀ k, U (θss k) ⊆ U θstar := by
    intro k x hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨Nat.pair k n, by simpa [θstar, Nat.unpair_pair] using hn⟩
  have hstar : ν.real (U θstar) = sSup A := by
    refine le_antisymm (le_csSup hAbdd ⟨θstar, rfl⟩) (le_of_tendsto' hu fun k ↦ ?_)
    rw [← hθss k]
    exact measureReal_mono (hUstar k)
  have hnull : ∀ θ, μ (C θ \ U θstar) = 0 := by
    intro θ
    let θ' : ℕ → Θ := fun n ↦ Nat.casesOn n θ fun m ↦ θstar m
    have hU' : U θ' = C θ ∪ U θstar := by
      ext x
      simp only [U, mem_iUnion, mem_union]
      constructor
      · rintro ⟨n, hn⟩
        cases n with
        | zero => exact Or.inl hn
        | succ m => exact Or.inr ⟨m, hn⟩
      · rintro (h | ⟨m, hm⟩)
        · exact ⟨0, h⟩
        · exact ⟨m + 1, hm⟩
    have hle : ν.real (U θ') ≤ ν.real (U θstar) := hstar ▸ le_csSup hAbdd ⟨θ', rfl⟩
    have hUm : MeasurableSet (U θstar) := MeasurableSet.iUnion fun n ↦ hCm _
    rw [hU', union_comm, ← union_sdiff_self, measureReal_union disjoint_sdiff_right
      ((hCm θ).diff hUm)] at hle
    have h0 : ν.real (C θ \ U θstar) = 0 :=
      le_antisymm (by linarith) measureReal_nonneg
    rw [measureReal_eq_zero_iff] at h0
    exact toFinite_apply_eq_zero_iff.1 h0
  refine ⟨θstar, fun θ ↦ Measure.AbsolutelyContinuous.mk fun B hB hB0 ↦ ?_⟩
  have hall := (countable_mixture_apply_eq_zero P θstar hB).1 hB0
  have hn : ∀ n, μ (C (θstar n) ∩ B) = 0 := fun n ↦ by
    have := hall n
    rwa [(hf (θstar n)).2.2, withDensity_apply_eq_zero
      (hf (θstar n)).1.ennreal_ofReal] at this
  rw [(hf θ).2.2, withDensity_apply_eq_zero (hf θ).1.ennreal_ofReal]
  have hUB : μ (U θstar ∩ B) = 0 := by
    rw [iUnion_inter]
    exact measure_iUnion_null hn
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hUB (hnull θ))
  by_cases hxU : x ∈ U θstar
  · exact Or.inl ⟨hxU, hx.2⟩
  · exact Or.inr ⟨hx.1, hxU⟩

/-- A countable mixture of laws sharing a disintegrating kernel is disintegrated by that kernel. -/
theorem countable_mixture_map_prod_mk_eq_comp_prod (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (θs : ℕ → Θ) {T : X → S} (hT : Measurable T)
    (K : Kernel S X) [IsMarkovKernel K]
    (hK : ∀ n, (P (θs n)).map (fun x ↦ (T x, x)) = (P (θs n)).map T ⊗ₘ K) :
    (countableMixture P θs).map (fun x ↦ (T x, x)) =
      (countableMixture P θs).map T ⊗ₘ K := by
  have hTX : Measurable (fun x ↦ (T x, x)) := hT.prodMk measurable_id
  simp only [countableMixture]
  rw [Measure.map_sum hTX.aemeasurable, Measure.map_sum hT.aemeasurable,
    Measure.compProd_sum_left]
  congr 1
  funext n
  rw [Measure.map_smul, Measure.map_smul, Measure.compProd_smul_left, hK n]
  all_goals first | exact hTX.aemeasurable | exact hT.aemeasurable

/-- The density of a countable mixture with respect to a dominating measure. -/
theorem countable_mixture_eq_with_density (P : Θ → Measure X) (μ : Measure X)
    (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (θs : ℕ → Θ) :
    countableMixture P θs =
      μ.withDensity (fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)) := by
  have hm : ∀ n, Measurable fun x ↦ mixtureWeight n * ENNReal.ofReal (f (θs n) x) :=
    fun n ↦ (hf (θs n)).1.ennreal_ofReal.const_mul _
  rw [show (fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)) =
    ∑' n, fun x ↦ mixtureWeight n * ENNReal.ofReal (f (θs n) x) by
      funext x; rw [ENNReal.tsum_apply], withDensity_tsum hm, countableMixture]
  congr 1
  funext n
  rw [(hf (θs n)).2.2, ← withDensity_smul _ (hf (θs n)).1.ennreal_ofReal]
  rfl

/-- If `P = L.withDensity (r ∘ T)` and the joint law of `(T, X)` under `L` is disintegrated by
`K`, then the joint law under `P` is also disintegrated by `K`. -/
theorem map_prod_mk_eq_comp_prod_of_with_density_comp (L : Measure X) [IsFiniteMeasure L]
    {T : X → S} (hT : Measurable T) (K : Kernel S X) [IsMarkovKernel K]
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) {r : S → ℝ≥0∞} (hr : Measurable r) :
    (L.withDensity (r ∘ T)).map (fun x ↦ (T x, x)) = (L.withDensity (r ∘ T)).map T ⊗ₘ K := by
  have hTX : Measurable (fun x ↦ (T x, x)) := hT.prodMk measurable_id
  rw [show r ∘ T = (fun p : S × X ↦ r p.1) ∘ (fun x ↦ (T x, x)) from rfl,
    map_with_density_comp (k := fun p : S × X ↦ r p.1) L hTX (hr.comp measurable_fst), hL,
    ← Measure.withDensity_compProd hr]
  congr 1
  exact (map_with_density_comp L hT hr).symm

/-- If two finite laws `P ≪ L` have joint laws of `(T, X)` disintegrated by the same kernel, then
`P` has a density with respect to `L` that is a function of `T`. -/
theorem eq_with_density_rn_deriv_comp_of_comp_prod (P L : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure L] (hPL : P ≪ L) {T : X → S} (hT : Measurable T)
    (K : Kernel S X) [IsMarkovKernel K]
    (hP : P.map (fun x ↦ (T x, x)) = P.map T ⊗ₘ K)
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) :
    P = L.withDensity (((P.map T).rnDeriv (L.map T)) ∘ T) := by
  have hTX : Measurable (fun x ↦ (T x, x)) := hT.prodMk measurable_id
  have hsnd : ∀ ν : Measure X, (ν.map (fun x ↦ (T x, x))).map Prod.snd = ν := fun ν ↦ by
    rw [Measure.map_map measurable_snd hTX]; exact Measure.map_id
  have hr := Measure.measurable_rnDeriv (P.map T) (L.map T)
  have hac : P.map T ≪ L.map T := hPL.map hT
  conv_lhs => rw [← hsnd P, hP, ← Measure.withDensity_rnDeriv_eq _ _ hac]
  rw [← hsnd (L.withDensity _), map_prod_mk_eq_comp_prod_of_with_density_comp L hT K hL hr,
    map_with_density_comp L hT hr]

/-- Sufficiency implies a factorization of the densities (necessity half of GAPS 101.1). -/
theorem exists_factorization_of_is_sufficient_statistic [Nonempty Θ] (P : Θ → Measure X)
    (μ : Measure X) [SigmaFinite μ] (hP : ∀ θ, IsProbabilityMeasure (P θ)) (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S) (hsuff : IsSufficientStatistic P T) :
    ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  obtain ⟨hT, K, hKm, hK⟩ := hsuff
  obtain ⟨θs, hac⟩ := exists_absolutely_continuous_countable_mixture P μ f hf
  have := hP
  set L := countableMixture P θs
  have hL := countable_mixture_map_prod_mk_eq_comp_prod P θs hT K fun n ↦ hK (θs n)
  set ρ : X → ℝ≥0∞ := fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)
  have hρm : Measurable ρ := Measurable.tsum fun n ↦
    (hf (θs n)).1.ennreal_ofReal.const_mul _
  have hLρ : L = μ.withDensity ρ := countable_mixture_eq_with_density P μ f hf θs
  let r : Θ → S → ℝ≥0∞ := fun θ ↦ ((P θ).map T).rnDeriv (L.map T)
  refine ⟨fun θ s ↦ (r θ s).toReal, fun x ↦ (ρ x).toReal,
    fun θ ↦ ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg⟩,
    hρm.ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg, fun θ ↦ ?_⟩
  have hPθ' : P θ = L.withDensity (r θ ∘ T) :=
    eq_with_density_rn_deriv_comp_of_comp_prod (P θ) L (hac θ) hT K (hK θ) hL
  have hrm : Measurable (r θ ∘ T) := (Measure.measurable_rnDeriv _ _).comp hT
  have hPθ : μ.withDensity (fun x ↦ ENNReal.ofReal (f θ x)) = μ.withDensity (ρ * (r θ ∘ T)) := by
    rw [withDensity_mul μ hρm hrm, ← hLρ, ← hPθ', ← (hf θ).2.2]
  have hae := (withDensity_eq_iff_of_sigmaFinite (hf θ).1.ennreal_ofReal.aemeasurable
    (hρm.mul hrm).aemeasurable).1 hPθ
  filter_upwards [hae, (hf θ).2.1] with x hx hx0
  have := congrArg ENNReal.toReal hx
  simp only [Pi.mul_apply, Function.comp_apply, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hx0] at this
  rw [this, mul_comm]

/-- A factorization of the densities implies sufficiency (sufficiency half of GAPS 101.1). The
common kernel is the conditional distribution of the sample given `T` under a dominating countable
mixture of the family. -/
theorem is_sufficient_statistic_of_factorization [StandardBorelSpace X] [Nonempty X] [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SigmaFinite μ] (hP : ∀ θ, IsProbabilityMeasure (P θ))
    (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) {T : X → S} (hT : Measurable T)
    (g : Θ → S → ℝ) (h : X → ℝ) (hg : ∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s)
    (hfac : ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x) :
    IsSufficientStatistic P T := by
  obtain ⟨θs, hac⟩ := exists_absolutely_continuous_countable_mixture P μ f hf
  have := hP
  set L := countableMixture P θs
  set ρ : X → ℝ≥0∞ := fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)
  have hρm : Measurable ρ := Measurable.tsum fun n ↦
    (hf (θs n)).1.ennreal_ofReal.const_mul _
  have hLρ : L = μ.withDensity ρ := countable_mixture_eq_with_density P μ f hf θs
  let K : Kernel S X := condDistrib (fun x ↦ x) T L
  have hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
    (compProd_map_condDistrib hT.aemeasurable aemeasurable_id).symm
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let G : S → ℝ≥0∞ := fun s ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (g (θs n) s)
  let r : S → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (g θ s) / G s
  have hGm : Measurable G := Measurable.tsum fun n ↦ (hg _).1.ennreal_ofReal.const_mul _
  have hrm : Measurable r := (hg θ).1.ennreal_ofReal.div hGm
  suffices hPθ : P θ = L.withDensity (r ∘ T) by
    rw [hPθ]
    exact map_prod_mk_eq_comp_prod_of_with_density_comp L hT K hL hrm
  rw [hLρ, ← withDensity_mul μ hρm (hrm.comp hT), (hf θ).2.2]
  refine withDensity_congr_ae ?_
  have hint : ∫⁻ x, ρ x ∂μ = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hLρ, measure_univ]
  have hfin : ∀ᵐ x ∂μ, ρ x < ∞ := ae_lt_top hρm (by rw [hint]; exact ENNReal.one_ne_top)
  have hzero : ∀ᵐ x ∂μ, ρ x = 0 → ENNReal.ofReal (f θ x) = 0 := by
    have h1 : L {x | ρ x = 0} = 0 := by
      rw [hLρ, withDensity_apply_eq_zero hρm]
      convert measure_empty (μ := μ)
      ext x
      simp
    have h2 : P θ {x | ρ x = 0} = 0 := hac θ h1
    rw [(hf θ).2.2, withDensity_apply_eq_zero (hf θ).1.ennreal_ofReal] at h2
    rw [ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) h2
    simp only [not_imp, mem_ofPred_eq] at hx
    exact ⟨hx.2, hx.1⟩
  filter_upwards [hfin, hzero, hfac θ, ae_all_iff.2 fun n ↦ hfac (θs n)] with x hxfin hx0 hxθ hxn
  have hρx : ρ x = G (T x) * ENNReal.ofReal (h x) := by
    simp only [ρ, G, hxn, ENNReal.ofReal_mul ((hg _).2 _), ← mul_assoc, ENNReal.tsum_mul_right]
  change ENNReal.ofReal (f θ x) = ρ x * r (T x)
  by_cases hρ0 : ρ x = 0
  · rw [hx0 hρ0, hρ0, zero_mul]
  · rw [hρx] at hρ0 hxfin ⊢
    have hG0 : G (T x) ≠ 0 := left_ne_zero_of_mul hρ0
    have hh0' : ENNReal.ofReal (h x) ≠ 0 := right_ne_zero_of_mul hρ0
    have hGtop : G (T x) ≠ ∞ := fun hG ↦ by
      rw [hG, ENNReal.top_mul hh0'] at hxfin
      exact lt_irrefl _ hxfin
    rw [mul_comm (G _), mul_assoc, ENNReal.mul_div_cancel hG0 hGtop, hxθ,
      ENNReal.ofReal_mul ((hg θ).2 _), mul_comm]

end CKSD
