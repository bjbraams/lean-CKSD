module

public import CKSD.Learning.Basic
public import CKSD.Asymptotics.Basic
public import CKSD.Nonparametric.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Learning: Generalization

Sources: `GAPS.md`, `SYNOPSIS107.md`, and `STRUCTURE107.md`.
Declarations adapted from this project's section drafts.
The docstrings specify the scope of each result; `sorry` marks unfinished proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- GAPS 107.1, finite-class uniform risk concentration (a scoped PAC upper bound). -/
theorem measure_uniform_empirical_risk_deviation_le
    {H X : Type*} [Fintype H] [Nonempty H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (epsilon : ℝ) (he : 0 < epsilon) :
    (Measure.pi fun _ : Fin n ↦ P).real {x | ∃ h,
      |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} ≤
      2 * Fintype.card H * Real.exp (-2 * n * epsilon ^ 2) := by
  let Q : Measure (Fin n → X) := Measure.pi (fun _ ↦ P)
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have htail (h : H) :
      Q.real {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} ≤
        2 * Real.exp (-2 * n * epsilon ^ 2) := by
    let m := ∫ z, f h z ∂P
    let Z : Fin n → (Fin n → X) → ℝ := fun i x ↦ f h (x i) - m
    have hbase : HasSubgaussianMGF (fun z ↦ f h z - m) (1 / 4) P := by
      have hs := hasSubgaussianMGF_of_mem_Icc (μ := P) (hm h).aemeasurable
        (Filter.Eventually.of_forall (hb h))
      norm_num at hs
      exact hs
    have hZ : ∀ i, HasSubgaussianMGF (Z i) (1 / 4) Q := by
      intro i
      have hp := measurePreserving_eval (fun _ : Fin n ↦ P) i
      exact HasSubgaussianMGF.of_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hbase)
    have hindep : iIndepFun Z Q :=
      iIndepFun_pi (fun _ : Fin n ↦ ((hm h).sub_const m).aemeasurable)
    have hsum : HasSubgaussianMGF (fun x ↦ ∑ i, Z i x)
        (∑ _ : Fin n, (1 / 4 : ℝ≥0)) Q :=
      HasSubgaussianMGF.sum_of_iIndepFun hindep (fun i _ ↦ hZ i)
    have hden : (↑(∑ _ : Fin n, (1 / 4 : ℝ≥0)) : ℝ) = (n : ℝ) / 4 := by
      norm_num [Finset.sum_const, nsmul_eq_mul]
      <;> ring
    have hexp : -((n : ℝ) * epsilon) ^ 2 / (2 * ((n : ℝ) / 4)) =
        -2 * n * epsilon ^ 2 := by
      field_simp [ne_of_gt hnreal]
      <;> ring
    have hup := hsum.measure_ge_le (mul_nonneg hnreal.le he.le)
    have hlow := hsum.neg.measure_ge_le (mul_nonneg hnreal.le he.le)
    rw [hden, hexp] at hup hlow
    simp only [Pi.neg_apply] at hlow
    have hsum_eq (x : Fin n → X) :
        (∑ i, Z i x) = (∑ i, f h (x i)) - (n : ℝ) * m := by
      simp only [Z, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsub : {x | epsilon < |(∑ i, f h (x i)) / n - m|} ⊆
        {x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} ∪
          {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)} := by
      intro x hx
      change epsilon < |(∑ i, f h (x i)) / n - m| at hx
      change (n : ℝ) * epsilon ≤ ∑ i, Z i x ∨ (n : ℝ) * epsilon ≤ -(∑ i, Z i x)
      have hid : (∑ i, f h (x i)) / n - m = (∑ i, Z i x) / n := by
        rw [hsum_eq]
        field_simp [ne_of_gt hnreal]
        <;> ring
      rw [hid, abs_div, abs_of_pos hnreal] at hx
      have ha : (n : ℝ) * epsilon < |∑ i, Z i x| := by
        nlinarith [(lt_div_iff₀ hnreal).mp hx]
      by_cases hz : 0 ≤ ∑ i, Z i x
      · left
        rw [abs_of_nonneg hz] at ha
        exact ha.le
      · right
        rw [abs_of_neg (lt_of_not_ge hz)] at ha
        exact ha.le
    calc
      _ ≤ Q.real ({x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} ∪
          {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)}) := measureReal_mono hsub
      _ ≤ Q.real {x | (n : ℝ) * epsilon ≤ ∑ i, Z i x} +
          Q.real {x | (n : ℝ) * epsilon ≤ -(∑ i, Z i x)} := measureReal_union_le _ _
      _ ≤ _ := by linarith
  change Q.real _ ≤ _
  rw [show {x : Fin n → X | ∃ h, |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} =
    ⋃ h, {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} by ext x; simp]
  calc
    _ ≤ ∑ h, Q.real {x | |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P| > epsilon} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : H, 2 * Real.exp (-2 * n * epsilon ^ 2) :=
      Finset.sum_le_sum (fun h _ ↦ htail h)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- GAPS 107.2, symmetrization and the expected-complexity bound for a finite class. -/
theorem rademacher_symmetrization_and_risk_bound
    {H X : Type*} [Fintype H] [Nonempty H] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H → X → ℝ)
    (hm : ∀ h, Measurable (f h)) (hb : ∀ h x, f h x ∈ Icc 0 1)
    (n : ℕ) (hn : 0 < n) (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    let Pn := Measure.pi fun _ : Fin n ↦ P;
    let R := ∫ x, empiricalRademacherComplexity n f x ∂Pn;
    (∫ x, sSup (range fun h ↦ (∑ i, f h (x i)) / n - ∫ z, f h z ∂P) ∂Pn) ≤ 2 * R ∧
      Pn.real {x | 2 * R + Real.sqrt (Real.log (2 / delta) / (2 * n)) <
        sSup (range fun h ↦ |(∑ i, f h (x i)) / n - ∫ z, f h z ∂P|)} ≤ delta := by
  sorry

/-- Integrals against a finite weighted sum of Dirac masses on `Fin K`. -/
theorem integral_finiteDiracSum {K : ℕ} (p : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (g : Fin K → ℝ) :
    ∫ x, g x ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac j) = ∑ j, p j * g j := by
  rw [integral_finsetSum_measure (fun j _ ↦
    (Integrable.of_finite (μ := Measure.dirac j)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp j), smul_eq_mul]

/-- Hoeffding's lemma for a finite probability vector and values in `[0,1]`, from Mathlib's
`hasSubgaussianMGF_of_mem_Icc`. -/
theorem sum_mul_exp_le {K : ℕ} (p ℓ : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hℓ : ∀ j, ℓ j ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    ∑ j, p j * Real.exp (t * ℓ j) ≤ Real.exp (t * ∑ j, p j * ℓ j + t ^ 2 / 8) := by
  set μ : Measure (Fin K) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac j
  have hμ1 : μ Set.univ = 1 := by
    simp only [μ, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hp j, hp1, ENNReal.ofReal_one]
  have : IsProbabilityMeasure μ := ⟨hμ1⟩
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := 0) (b := 1)
    (measurable_of_finite ℓ).aemeasurable (ae_of_all _ hℓ)
  have hm := hs.mgf_le t
  have hmean : μ[ℓ] = ∑ j, p j * ℓ j := integral_finiteDiracSum p hp ℓ
  rw [mgf, integral_finiteDiracSum p hp, hmean] at hm
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 / 4 : ℝ≥0) := by
    norm_num
  rw [hc] at hm
  have hpt : ∀ j, Real.exp (t * ℓ j) =
      Real.exp (t * (ℓ j - ∑ i, p i * ℓ i)) * Real.exp (t * ∑ i, p i * ℓ i) := by
    intro j; rw [← Real.exp_add]; ring_nf
  calc ∑ j, p j * Real.exp (t * ℓ j)
      = (∑ j, p j * Real.exp (t * (ℓ j - ∑ i, p i * ℓ i))) * Real.exp (t * ∑ i, p i * ℓ i) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [hpt]; ring
    _ ≤ Real.exp ((1 / 4 : ℝ≥0) * t ^ 2 / 2) * Real.exp (t * ∑ i, p i * ℓ i) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- GAPS 107.5: the exponential-weights regret bound, for any positive learning rate. -/
theorem hedge_regret_le {K : ℕ} (hK : 0 < K) (loss : ℕ → Fin K → ℝ)
    (hloss : ∀ t i, loss t i ∈ Icc 0 1) (eta : ℝ) (he : 0 < eta)
    (T : ℕ) (i : Fin K) :
    (∑ t ∈ Finset.range T, ∑ j, hedgeWeight loss eta t j * loss t j) -
      (∑ t ∈ Finset.range T, loss t i) ≤ Real.log K / eta + eta * T / 8 := by
  set L : ℕ → Fin K → ℝ := fun t j ↦ ∑ s ∈ Finset.range t, loss s j
  set W : ℕ → ℝ := fun t ↦ ∑ j, Real.exp (-eta * L t j)
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hW : ∀ t, 0 < W t := fun t ↦ Finset.sum_pos (fun j _ ↦ Real.exp_pos _) hne
  have hp : ∀ t j, hedgeWeight loss eta t j = Real.exp (-eta * L t j) / W t := fun _ _ ↦ rfl
  have hp0 : ∀ t j, 0 ≤ hedgeWeight loss eta t j := fun t j ↦ by
    rw [hp]; exact div_nonneg (Real.exp_pos _).le (hW t).le
  have hp1 : ∀ t, ∑ j, hedgeWeight loss eta t j = 1 := fun t ↦ by
    simp_rw [hp]; rw [← Finset.sum_div, div_self (hW t).ne']
  have hstep : ∀ t, Real.log (W (t + 1)) ≤ Real.log (W t) -
      eta * (∑ j, hedgeWeight loss eta t j * loss t j) + eta ^ 2 / 8 := by
    intro t
    have hWt : W (t + 1) = W t * ∑ j, hedgeWeight loss eta t j * Real.exp (-eta * loss t j) := by
      have hWt0 := (hW t).ne'
      conv_lhs => simp only [W]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hp]
      have hL : L (t + 1) j = L t j + loss t j := Finset.sum_range_succ _ _
      rw [hL, mul_add, Real.exp_add]
      field_simp
    have hb := sum_mul_exp_le (fun j ↦ hedgeWeight loss eta t j) (loss t) (hp0 t) (hp1 t)
      (hloss t) (-eta)
    have hpos : 0 < ∑ j, hedgeWeight loss eta t j * Real.exp (-eta * loss t j) := by
      have := hW (t + 1); rw [hWt] at this; exact pos_of_mul_pos_right this (hW t).le
    rw [hWt, Real.log_mul (hW t).ne' hpos.ne']
    have := Real.log_le_log hpos hb
    rw [Real.log_exp] at this
    nlinarith
  have hind : ∀ n, Real.log (W n) ≤ Real.log K -
      eta * (∑ t ∈ Finset.range n, ∑ j, hedgeWeight loss eta t j * loss t j) + n * eta ^ 2 / 8 := by
    intro n
    induction n with
    | zero => simp [W, L]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      push_cast
      nlinarith
  have hlow : -eta * L T i ≤ Real.log (W T) := by
    rw [← Real.log_exp (-eta * L T i)]
    exact Real.log_le_log (Real.exp_pos _)
      (Finset.single_le_sum (f := fun j ↦ Real.exp (-eta * L T j))
        (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i))
  have h := (hlow.trans (hind T))
  have hfinal : eta * ((∑ t ∈ Finset.range T, ∑ j, hedgeWeight loss eta t j * loss t j) -
      (∑ t ∈ Finset.range T, loss t i)) ≤ eta * (Real.log K / eta + eta * T / 8) := by
    rw [mul_add, mul_div_cancel₀ _ he.ne']
    simp only [L] at h
    nlinarith
  exact le_of_mul_le_mul_left hfinal he

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

/-- GAPS 107.6: the exchangeable-rank coverage assertion, with ties allowed. -/
theorem conformal_coverage_ge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Fin (n + 1) → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hex : ∀ σ : Equiv.Perm (Fin (n + 1)),
      P.map (fun ω i ↦ S (σ i) ω) = P.map (fun ω i ↦ S i ω))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let C := {ω | ((Finset.univ : Finset (Fin n)).filter
      (fun i ↦ S i.castSucc ω < S (Fin.last n) ω)).card < k};
    (k : ℝ) / (n + 1) ≤ P.real C ∧
      ((∀ᵐ ω ∂P, Function.Injective (fun i ↦ S i ω)) → P.real C = (k : ℝ) / (n + 1)) := by
  intro C
  set V : Ω → Fin (n + 1) → ℝ := fun ω i ↦ S i ω
  have hV : Measurable V := measurable_pi_iff.mpr hS
  set A : Fin (n + 1) → Set Ω := fun i ↦ {ω | conformalRank (V ω) i < k}
  have hAm : ∀ i, MeasurableSet (A i) := fun i ↦ by
    have := ((measurable_conformalRank_cast i).comp hV) (measurableSet_Iio : MeasurableSet (Iio (k : ℝ)))
    convert this using 1
    ext ω; simp [A]
  have hCA : C = A (Fin.last n) := by
    ext ω
    simp only [C, A, mem_ofPred_eq]
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
  constructor
  · rw [div_le_iff₀' hn1, ← hsumC, hsum]
    calc (k : ℝ) = ∫ _ω, (k : ℝ) ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const _)
          (integrable_finsetSum _ fun i _ ↦ hint i)
          fun ω ↦ by rw [hcount]; exact_mod_cast le_card_conformalRank_lt (V ω) k hkn
  · intro hinj
    rw [eq_div_iff hn1.ne', mul_comm, ← hsumC, hsum]
    calc ∫ ω, ∑ i, (A i).indicator (1 : Ω → ℝ) ω ∂P = ∫ _ω, (k : ℝ) ∂P := by
          refine integral_congr_ae (hinj.mono fun ω hω ↦ ?_)
          dsimp only
          rw [hcount]
          exact_mod_cast card_conformalRank_lt_of_injective (V ω) hω k hkn
      _ = k := by simp

/-- Flipping one label is an involution, so a label-blind guess at that coordinate is wrong for
exactly half of all labellings. -/
theorem sum_flip_ne {m : ℕ} (j : Fin m) (g : (Fin m → Bool) → Bool)
    (hg : ∀ lab, g (Function.update lab j (!lab j)) = g lab) :
    ∑ lab : Fin m → Bool, (if g lab ≠ lab j then (1 : ℝ) else 0) = 2 ^ m / 2 := by
  have hinv : Function.Involutive fun lab : Fin m → Bool ↦ Function.update lab j (!lab j) := by
    intro lab; ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  set e := hinv.toPerm
  have hcomp := Equiv.sum_comp e (fun lab ↦ if g lab ≠ lab j then (1 : ℝ) else 0)
  have hpt : ∀ lab : Fin m → Bool, (if g (e lab) ≠ (e lab) j then (1 : ℝ) else 0) =
      1 - if g lab ≠ lab j then 1 else 0 := by
    intro lab
    simp only [e, Function.Involutive.coe_toPerm, hg, Function.update_self]
    cases g lab <;> cases lab j <;> simp
  simp_rw [hpt] at hcomp
  rw [Finset.sum_sub_distrib] at hcomp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcomp
  push_cast at hcomp
  linarith

/-- GAPS 107.7, finite-support no-free-lunch bound; taking arbitrarily large `m`
gives the infinite-feature-space assertion. -/
theorem no_free_lunch_lower_bound (n m : ℕ) (hm : 0 < m)
    (learn : (Fin n → Fin m × Bool) → Fin m → Bool) :
    ∃ label : Fin m → Bool,
      (1 - (n : ℝ) / m) / 2 ≤
        (∑ x : Fin n → Fin m,
          ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label
            (x i))) j ≠ label j).card : ℝ) / m) /
          (m : ℝ) ^ n := by
  set F : (Fin m → Bool) → ℝ := fun label ↦ (∑ x : Fin n → Fin m,
      ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) /
        m) / (m : ℝ) ^ n
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- per sample: the label sum over unseen points
  have hx : ∀ x : Fin n → Fin m, (2 : ℝ) ^ m / 2 * (m - n) ≤
      ∑ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) := by
    intro x
    have hcard : ∀ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card : ℝ) =
          ∑ j, if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 := by
      intro label; rw [Finset.natCast_card_filter]
    simp_rw [hcard]
    rw [Finset.sum_comm]
    set U := Finset.univ \ Finset.univ.image x
    have hU : (m : ℝ) - n ≤ U.card := by
      have h1 : U.card = m - (Finset.univ.image x).card := by
        rw [Finset.card_univ_sdiff, Fintype.card_fin]
      have h2 : (Finset.univ.image x).card ≤ n := by
        simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := x)
      have h3 : (Finset.univ.image x).card ≤ m := by
        simpa using Finset.card_le_univ (Finset.univ.image x)
      rw [h1, Nat.cast_sub h3]
      have h2' : ((Finset.univ.image x).card : ℝ) ≤ n := by exact_mod_cast h2
      linarith
    calc (2 : ℝ) ^ m / 2 * (m - n) ≤ (2 : ℝ) ^ m / 2 * U.card :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ = ∑ j ∈ U, ∑ label : Fin m → Bool,
            if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 := by
          rw [Finset.sum_congr rfl fun j hj ↦ sum_flip_ne j
            (fun label ↦ learn (fun i ↦ (x i, label (x i))) j) fun lab ↦ ?_]
          · simp [mul_comm]
          · have hj' : ∀ i, x i ≠ j := fun i hi ↦ by
              simp only [U, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and,
                not_exists] at hj
              exact hj i hi
            simp only [Function.update_of_ne (hj' _)]
      _ ≤ ∑ j, ∑ label : Fin m → Bool,
            if learn (fun i ↦ (x i, label (x i))) j ≠ label j then (1 : ℝ) else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦
            Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
  have hsum : (2 : ℝ) ^ m * ((1 - (n : ℝ) / m) / 2) ≤ ∑ label, F label := by
    have hF : ∑ label, F label = (∑ x : Fin n → Fin m, ∑ label : Fin m → Bool,
        ((Finset.univ.filter fun j ↦ learn (fun i ↦ (x i, label (x i))) j ≠ label j).card :
          ℝ)) / (m ^ n * m) := by
      simp only [F, div_div, ← Finset.sum_div]
      rw [Finset.sum_comm, mul_comm]
    rw [hF, le_div_iff₀ (by positivity)]
    calc (2 : ℝ) ^ m * ((1 - (n : ℝ) / m) / 2) * ((m : ℝ) ^ n * m)
        = ∑ _x : Fin n → Fin m, (2 : ℝ) ^ m / 2 * (m - n) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ hx x
  by_contra hcon
  push Not at hcon
  have : ∑ label, F label < ∑ _label : Fin m → Bool, (1 - (n : ℝ) / m) / 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun label _ ↦ hcon label
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  linarith

/-- Binary conditional classification loss is integrable under a probability law. -/
theorem integrable_classificationLoss {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η : X → ℝ) (hη : Measurable η)
    (hrange : ∀ x, η x ∈ Icc 0 1) (g : X → Bool) (hg : Measurable g) :
    Integrable (fun x ↦ if g x then 1 - η x else η x) P := by
  have hs : MeasurableSet {x | g x = true} := hg (measurableSet_singleton true)
  apply Integrable.of_bound
    (Measurable.ite hs (measurable_const.sub hη) hη).aestronglyMeasurable 1
  filter_upwards with x
  simp only [Pi.sub_apply]
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  split_ifs <;> constructor <;> linarith [(hrange x).1, (hrange x).2]

/-- GAPS 107.8: the exact excess Bayes classification risk identity. -/
theorem classificationRisk_sub_bayes_risk_eq {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η : X → ℝ) (hη : Measurable η)
    (hrange : ∀ x, η x ∈ Icc 0 1) (g : X → Bool) (hg : Measurable g) :
    let star := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x);
    classificationRisk P η g - classificationRisk P η star =
      ∫ x, if g x ≠ star x then |2 * η x - 1| else 0 ∂P := by
  dsimp only
  let star : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)
  have hstar : Measurable star := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ η x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const hη)
  change (∫ x, (if g x then 1 - η x else η x) ∂P) -
      (∫ x, (if star x then 1 - η x else η x) ∂P) =
    ∫ x, if g x ≠ star x then |2 * η x - 1| else 0 ∂P
  rw [← integral_sub (integrable_classificationLoss P η hη hrange g hg)
    (integrable_classificationLoss P η hη hrange star hstar)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : (1 / 2 : ℝ) ≤ η x
  · cases hx : g x <;>
      simp [star, abs_of_nonneg (by linarith : 0 ≤ 2 * η x - 1)] <;>
        split_ifs <;> linarith
  · cases hx : g x <;>
      simp [star, abs_of_nonpos (by linarith : 2 * η x - 1 ≤ 0)] <;>
        split_ifs <;> linarith

/-- GAPS 107.8: the plugin classification risk bound. -/
theorem classificationRisk_plugin_sub_bayes_risk_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (η a : X → ℝ)
    (hη : Measurable η) (ha : Measurable a) (hi : Integrable a P)
    (hrange : ∀ x, η x ∈ Icc 0 1) :
    classificationRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ a x)) -
      classificationRisk P η (fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)) ≤
        2 * ∫ x, |a x - η x| ∂P := by
  let ga : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ a x)
  let star : X → Bool := fun x ↦ decide ((1 / 2 : ℝ) ≤ η x)
  have hga : Measurable ga := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ a x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const ha)
  have hstar : Measurable star := by
    apply measurable_to_bool
    change MeasurableSet {x | decide ((1 / 2 : ℝ) ≤ η x) = true}
    simpa only [decide_eq_true_eq] using (measurableSet_le measurable_const hη)
  have hiη : Integrable η P := by
    simpa only [Bool.false_eq_true, ite_false] using
      integrable_classificationLoss P η hη hrange (fun _ ↦ false) measurable_const
  change (∫ x, (if ga x then 1 - η x else η x) ∂P) -
      (∫ x, (if star x then 1 - η x else η x) ∂P) ≤ _
  rw [← integral_sub (integrable_classificationLoss P η hη hrange ga hga)
    (integrable_classificationLoss P η hη hrange star hstar), ← integral_const_mul]
  apply integral_mono
    ((integrable_classificationLoss P η hη hrange ga hga).sub
      (integrable_classificationLoss P η hη hrange star hstar))
    ((hi.sub hiη).abs.const_mul 2)
  intro x
  dsimp only [ga, star]
  simp only [decide_eq_true_eq, Pi.sub_apply]
  have hlo := neg_abs_le (a x - η x)
  have hhi := le_abs_self (a x - η x)
  split_ifs <;> linarith [abs_nonneg (a x - η x)]

/-- GAPS 107.11, pointwise classification calibration of a convex surrogate. -/
theorem surrogate_minimizer_sign_of_convex (phi : ℝ → ℝ) (hc : ConvexOn ℝ univ phi)
    (hmono : Monotone phi) (d : ℝ) (hd : HasDerivAt phi d 0) (hdpos : 0 < d)
    (eta : ℝ) (he : eta ∈ Ioo 0 1) (hne : eta ≠ 1 / 2)
    (u : ℝ) (hmin : ∀ v, eta * phi (-u) + (1 - eta) * phi u ≤
      eta * phi (-v) + (1 - eta) * phi v) : 0 < (eta - 1 / 2) * u := by
  let C : ℝ → ℝ := fun v ↦ eta * phi (-v) + (1 - eta) * phi v
  change ∀ v, C u ≤ C v at hmin
  have hcneg : ConvexOn ℝ univ (fun v ↦ phi (-v)) := by
    simpa only [preimage_univ, Function.comp_def, LinearMap.neg_apply, LinearMap.id_apply] using
      hc.comp_linearMap (-(LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have hC : ConvexOn ℝ univ C := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hneg := hcneg.2 (mem_univ x) (mem_univ y) ha hb hab
    have hpos := hc.2 (mem_univ x) (mem_univ y) ha hb hab
    dsimp only [C]
    simp only [smul_eq_mul] at hneg hpos ⊢
    calc
      _ ≤ eta * (a * phi (-x) + b * phi (-y)) +
          (1 - eta) * (a * phi x + b * phi y) :=
        add_le_add (mul_le_mul_of_nonneg_left hneg he.1.le)
          (mul_le_mul_of_nonneg_left hpos (sub_nonneg.mpr he.2.le))
      _ = _ := by ring
  have hdneg : HasDerivAt (fun v ↦ phi (-v)) (-d) 0 := by
    have hd' : HasDerivAt phi d (-(0 : ℝ)) := by simpa only [neg_zero] using hd
    have h := hd'.comp (0 : ℝ) (hasDerivAt_neg 0)
    simpa only [Function.comp_def, neg_zero, mul_neg_one] using h
  have hD : HasDerivAt C (eta * (-d) + (1 - eta) * d) 0 :=
    (hdneg.const_mul eta).add (hd.const_mul (1 - eta))
  by_cases hu : u = 0
  · subst u
    have hlocal : IsLocalMin C 0 := Filter.Eventually.of_forall hmin
    have hz := hlocal.hasDerivAt_eq_zero hD
    exfalso
    apply hne
    have hmul : (1 - 2 * eta) * d = 0 := by nlinarith
    have hzeta := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hdpos)
    linarith
  · rcases lt_or_gt_of_ne hu with hneg | hpos
    · have hs := hC.slope_le_of_hasDerivAt (mem_univ u) (mem_univ 0) hneg hD
      have hsl : 0 ≤ slope C u 0 := by
        rw [slope_def_field]
        exact div_nonneg (sub_nonneg.mpr (hmin 0)) (by linarith)
      have hmul : 0 ≤ (1 - 2 * eta) * d := by nlinarith
      have hηle : eta ≤ 1 / 2 := by
        have := (mul_nonneg_iff_of_pos_right hdpos).mp hmul
        linarith
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (lt_of_le_of_ne hηle hne)) hneg
    · have hs := hC.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ u) hpos hD
      have hsl : slope C 0 u ≤ 0 := by
        rw [slope_def_field]
        exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmin 0)) (by linarith)
      have hmul : (1 - 2 * eta) * d ≤ 0 := by nlinarith
      have hηge : 1 / 2 ≤ eta := by
        have hh : 0 ≤ (2 * eta - 1) * d := by nlinarith
        have := (mul_nonneg_iff_of_pos_right hdpos).mp hh
        linarith
      exact mul_pos (sub_pos.mpr (lt_of_le_of_ne hηge hne.symm)) hpos

/-- GAPS 107.12: generalization of a measurable uniformly stable algorithm. -/
theorem generalization_bound_of_uniform_stability {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (loss : (Fin n → X) → X → ℝ) (hm : Measurable (Function.uncurry loss))
    (beta M : ℝ) (hb : 0 ≤ beta) (hM : 0 ≤ M) (hl : ∀ x z, loss x z ∈ Icc 0 M)
    (hstable : ∀ x y, (∃ i : Fin n, ∀ j, j ≠ i → x j = y j) →
      ∀ z, |loss x z - loss y z| ≤ beta)
    (delta : ℝ) (hd : delta ∈ Ioo 0 1) :
    (Measure.pi fun _ : Fin n ↦ P).real {x |
      (∑ i, loss x (x i)) / n + beta + (2 * n * beta + M) *
        Real.sqrt (Real.log (1 / delta) / (2 * n)) < ∫ z, loss x z ∂P} ≤ delta := by
  sorry


end CKSD
