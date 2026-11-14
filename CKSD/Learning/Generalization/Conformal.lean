module

public import CKSD.Learning.Generalization.Concentration

/-!
# Conformal coverage from exchangeable ranks

Strict ranks with arbitrary ties yield finite-sample prediction coverage under exchangeability.

## Main definitions

* `CKSD.conformalRank`: the strict rank of a coordinate of a real vector.
* `CKSD.conformalEvent`: the event that the last of `n + 1` scores has fewer than `k` strictly
  smaller scores among the others.

## Main results

* `CKSD.div_le_measureReal_conformalEvent`: coverage at least `k / (n + 1)`, ties allowed
  (GAPS 107.6).
* `CKSD.measureReal_conformalEvent_eq_div`: exact coverage `k / (n + 1)` for almost surely
  distinct scores (GAPS 107.6).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- Strict rank of a coordinate: the number of coordinates with a strictly smaller value. -/
def conformalRank {m : ℕ} (v : Fin m → ℝ) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun j ↦ v j < v i).card

/-- At least `k` coordinates have strict rank below `k`, whatever the ties. -/
theorem le_card_conformalRank_lt {m : ℕ} (v : Fin m → ℝ) (k : ℕ) (hk : k ≤ m) :
    k ≤ (Finset.univ.filter fun i ↦ conformalRank v i < k).card := by
  set T := Finset.univ.filter fun i ↦ conformalRank v i < k
  by_contra hlt
  push Not at hlt
  have hne : (Finset.univ \ T).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ_sdiff, Fintype.card_fin]; omega
  obtain ⟨a, ha, hamin⟩ := (Finset.univ \ T).exists_min_image v hne
  have haT : ¬ conformalRank v a < k := by
    simpa [T] using (Finset.mem_sdiff.mp ha).2
  have hsub : (Finset.univ.filter fun j ↦ v j < v a) ⊆ T := by
    intro j hj
    by_contra hjT
    have := hamin j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjT⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    linarith
  have := Finset.card_le_card hsub
  unfold conformalRank at haT
  omega

/-- For distinct values exactly `k` coordinates have strict rank below `k`. -/
theorem card_conformalRank_lt_of_injective {m : ℕ} (v : Fin m → ℝ) (hv : Function.Injective v)
    (k : ℕ) (hk : k ≤ m) :
    (Finset.univ.filter fun i ↦ conformalRank v i < k).card = k := by
  have hmono : ∀ i i', v i < v i' → conformalRank v i < conformalRank v i' := by
    intro i i' h
    apply Finset.card_lt_card
    refine ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; linarith
    · have := hsub (show i ∈ Finset.univ.filter fun j ↦ v j < v i' by simpa using h)
      simp at this
  have hinj : Function.Injective (conformalRank v) := by
    intro i i' h
    by_contra hne
    rcases lt_or_gt_of_ne (hv.ne hne) with hl | hl
    · exact absurd h (hmono _ _ hl).ne
    · exact absurd h (hmono _ _ hl).ne'
  have hlt : ∀ i, conformalRank v i < m := fun i ↦ by
    unfold conformalRank
    calc _ < (Finset.univ : Finset (Fin m)).card := Finset.card_lt_card
          ⟨Finset.subset_univ _, fun h ↦ by simpa using h (Finset.mem_univ i)⟩
      _ = m := by simp
  -- conformalRank is a bijection onto range m
  let f : Fin m → Fin m := fun i ↦ ⟨conformalRank v i, hlt i⟩
  have hf : Function.Bijective f := (Finite.injective_iff_bijective).mp fun i i' h ↦
    hinj (congrArg Fin.val h)
  have : (Finset.univ.filter fun i ↦ conformalRank v i < k) =
      (Finset.univ.filter fun r : Fin m ↦ r.val < k).map
        (Equiv.ofBijective f hf).symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_symm, Equiv.ofBijective_apply, f]
  rw [this, Finset.card_map]
  have hmap : (Finset.univ.filter fun r : Fin m ↦ r.val < k).map Fin.valEmbedding =
      Finset.range k := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]

/-- Swapping two coordinates transports the strict rank. -/
theorem conformalRank_comp_swap {m : ℕ} (v : Fin m → ℝ) (i l : Fin m) :
    conformalRank (fun j ↦ v (Equiv.swap i l j)) l = conformalRank v i := by
  unfold conformalRank
  simp only [Equiv.swap_apply_right]
  exact Finset.card_bij (fun j _ ↦ Equiv.swap i l j) (by simp)
    (fun a _ b _ h ↦ (Equiv.swap i l).injective h)
    (fun b hb ↦ ⟨Equiv.swap i l b, by simpa using hb, by simp⟩)

/-- The strict rank is a measurable function of the vector. -/
theorem measurable_conformalRank_cast {m : ℕ} (i : Fin m) :
    Measurable fun v : Fin m → ℝ ↦ (conformalRank v i : ℝ) := by
  have : (fun v : Fin m → ℝ ↦ (conformalRank v i : ℝ)) =
      fun v ↦ ∑ j, if v j < v i then (1 : ℝ) else 0 := by
    funext v; unfold conformalRank; rw [Finset.natCast_card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ ↦ Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

/-- The number of coordinates of strict rank below `k` is a measurable function of the
vector. -/
theorem measurable_card_conformalRank_lt {m : ℕ} (k : ℕ) :
    Measurable fun v : Fin m → ℝ ↦
      ((Finset.univ.filter fun i ↦ conformalRank v i < k).card : ℝ) := by
  simp_rw [Finset.natCast_card_filter]
  refine Finset.measurable_sum _ fun i _ ↦ Measurable.ite ?_ measurable_const measurable_const
  have := (measurable_conformalRank_cast i) (measurableSet_Iio : MeasurableSet (Iio (k : ℝ)))
  convert this using 1
  ext v
  simp

/-- The conformal event `{ω | #{i < n : Sᵢ(ω) < Sₙ(ω)} < k}` for the last of `n + 1` scores
`S₀, …, Sₙ`. -/
def conformalEvent {Ω : Type*} {n : ℕ} (S : Fin (n + 1) → Ω → ℝ) (k : ℕ) : Set Ω :=
  {ω | ((Finset.univ : Finset (Fin n)).filter
    (fun i ↦ S i.castSucc ω < S (Fin.last n) ω)).card < k}

/-- Under exchangeability of the scores, `(n + 1)` times the probability of the conformal event
is the expected number of coordinates of strict rank below `k`. -/
theorem natCast_add_one_mul_measureReal_conformalEvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (S : Fin (n + 1) → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      P.map (fun ω i ↦ S (σ i) ω) = P.map (fun ω i ↦ S i ω)) (k : ℕ) :
    (n + 1) * P.real (conformalEvent S k) = ∫ ω,
      ((Finset.univ.filter fun i ↦ conformalRank (fun j ↦ S j ω) i < k).card : ℝ) ∂P := by
  set C := conformalEvent S k
  set V : Ω → Fin (n + 1) → ℝ := fun ω i ↦ S i ω
  have hV : Measurable V := measurable_pi_iff.mpr hS
  set A : Fin (n + 1) → Set Ω := fun i ↦ {ω | conformalRank (V ω) i < k}
  have hAm : ∀ i, MeasurableSet (A i) := fun i ↦ by
    have := ((measurable_conformalRank_cast i).comp hV)
      (measurableSet_Iio : MeasurableSet (Iio (k : ℝ)))
    convert this using 1
    ext ω; simp [A]
  have hCA : C = A (Fin.last n) := by
    ext ω
    simp only [C, conformalEvent, A, mem_ofPred_eq]
    unfold conformalRank
    have : (Finset.univ.filter fun j : Fin (n + 1) ↦ V ω j < V ω (Fin.last n)) =
        (Finset.univ.filter fun i : Fin n ↦ S i.castSucc ω < S (Fin.last n) ω).map
          Fin.castSuccEmb := by
      ext j
      cases j using Fin.lastCases with
      | last => simp [V]
      | cast i => simp [V]
    rw [this, Finset.card_map]
  have hAeq : ∀ i, P.real (A i) = P.real C := by
    intro i
    set σ := Equiv.swap i (Fin.last n)
    have hW : Measurable fun ω (j : Fin (n + 1)) ↦ S (σ j) ω :=
      measurable_pi_iff.mpr fun j ↦ hS (σ j)
    have hE : MeasurableSet {v : Fin (n + 1) → ℝ | conformalRank v (Fin.last n) < k} := by
      have := (measurable_conformalRank_cast (Fin.last n))
        (measurableSet_Iio : MeasurableSet (Iio (k : ℝ)))
      convert this using 1
      ext v; simp
    have hmap := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦
      μ.real {v | conformalRank v (Fin.last n) < k}) (hex σ)
    rw [map_measureReal_apply hW hE, map_measureReal_apply hV hE] at hmap
    rw [hCA]
    convert hmap using 2
    ext ω
    simp only [A, mem_ofPred_eq, mem_preimage]
    rw [show (fun j ↦ S (σ j) ω) = fun j ↦ V ω (σ j) from rfl, conformalRank_comp_swap]
    rfl
  have hint : ∀ i, Integrable ((A i).indicator (1 : Ω → ℝ)) P := fun i ↦
    (integrable_const (1 : ℝ)).indicator (hAm i)
  have hsum : ∑ i, P.real (A i) = ∫ ω, ∑ i, (A i).indicator (1 : Ω → ℝ) ω ∂P := by
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_indicator_one (hAm i)]
  have hcount : ∀ ω, ∑ i, (A i).indicator (1 : Ω → ℝ) ω =
      (Finset.univ.filter fun i ↦ conformalRank (V ω) i < k).card := by
    intro ω
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [indicator, A, mem_ofPred_eq, Pi.one_apply]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hsumC : ∑ i, P.real (A i) = (n + 1) * P.real C := by
    simp only [hAeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [← hsumC, hsum]
  exact integral_congr_ae (ae_of_all _ hcount)

/-- GAPS 107.6, the exchangeable-rank coverage assertion, with ties allowed: for exchangeable
scores `S₀, …, Sₙ` and `k ≤ n + 1`, the last score has fewer than `k` strictly smaller scores
among the others with probability at least `k / (n + 1)`. -/
theorem div_le_measureReal_conformalEvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin (n + 1) → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      P.map (fun ω i ↦ S (σ i) ω) = P.map (fun ω i ↦ S i ω))
    {k : ℕ} (hkn : k ≤ n + 1) :
    (k : ℝ) / (n + 1) ≤ P.real (conformalEvent S k) := by
  rw [div_le_iff₀' (by positivity), natCast_add_one_mul_measureReal_conformalEvent P S hS hex k]
  have hm : Measurable fun ω ↦
      ((Finset.univ.filter fun i ↦ conformalRank (fun j ↦ S j ω) i < k).card : ℝ) :=
    (measurable_card_conformalRank_lt k).comp (measurable_pi_iff.mpr hS)
  have hb : ∀ ω, ((Finset.univ.filter fun i ↦ conformalRank (fun j ↦ S j ω) i < k).card : ℝ) ∈
      Icc 0 ((n : ℝ) + 1) := fun ω ↦
    ⟨Nat.cast_nonneg _, by exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)⟩
  calc (k : ℝ) = ∫ _ω, (k : ℝ) ∂P := by simp
    _ ≤ _ := integral_mono (integrable_const _)
        (Integrable.of_mem_Icc 0 ((n : ℝ) + 1) hm.aemeasurable (ae_of_all _ hb))
        fun ω ↦ by exact_mod_cast le_card_conformalRank_lt _ k hkn

/-- GAPS 107.6, the exchangeable-rank coverage assertion, without ties: if the scores are almost
surely distinct, the coverage probability is exactly `k / (n + 1)`. -/
theorem measureReal_conformalEvent_eq_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin (n + 1) → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      P.map (fun ω i ↦ S (σ i) ω) = P.map (fun ω i ↦ S i ω))
    {k : ℕ} (hkn : k ≤ n + 1) (hinj : ∀ᵐ ω ∂P, Function.Injective (fun i ↦ S i ω)) :
    P.real (conformalEvent S k) = (k : ℝ) / (n + 1) := by
  rw [eq_div_iff (by positivity), mul_comm,
    natCast_add_one_mul_measureReal_conformalEvent P S hS hex k]
  calc _ = ∫ _ω, (k : ℝ) ∂P := integral_congr_ae (hinj.mono fun ω hω ↦ by
          dsimp only
          exact_mod_cast card_conformalRank_lt_of_injective _ hω k hkn)
    _ = k := by simp

end CKSD
