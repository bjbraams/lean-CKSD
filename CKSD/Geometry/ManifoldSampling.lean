module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Exp


/-!
# Sampling nets and small balls on immersed manifolds

Two ingredients of Hausdorff sampling bounds for supports of probability measures.

A packing argument turns a uniform lower bound on the mass of small balls into a finite net of
controlled cardinality, and a union bound over that net shows that an independent sample covers
the support at a given scale with high probability.

On a compact smooth `d`-manifold immersed in `ℝ^D`, small balls centered on the image have
`d`-dimensional Hausdorff measure at least a constant times `r^d`. In the local normal form of an
immersion, the parametrization `j ∘ φ⁻¹` is Lipschitz and has a Lipschitz left inverse, so the
Hausdorff measure of a small image ball is comparable with the Lebesgue measure of a ball in
`ℝ^d`; compactness makes the constants uniform.

## Main results

* `CKSD.exists_finset_net_of_le_measure_ball`: a packing bound for nets.
* `CKSD.one_sub_le_measure_real_pi_hausdorff_dist_le`: the probability that an i.i.d. sample is
  `ε`-close to the support in Hausdorff distance, under a small-ball lower bound.
* `CKSD.exists_hausdorff_measure_ball_inter_range_ge_of_is_immersion`: the uniform lower bound
  `μH[d] (B(j x, r) ∩ j(N)) ≥ a r^d` on a compact immersed manifold.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology Manifold ContDiff

namespace CKSD

/-- A packing bound for nets: if every open ball of radius `s > 0` centered in `K` has
`P`-mass at least `a > 0` under a probability measure `P`, then a finite subset `F ⊆ K` with
`|F| a ≤ 1` is a `2s`-net of `K`. -/
theorem exists_finset_net_of_le_measure_ball {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (K : Set X) {s a : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hball : ∀ x ∈ K, ENNReal.ofReal a ≤ P (Metric.ball x s)) :
    ∃ F : Finset X, (F : Set X) ⊆ K ∧ (F.card : ℝ) * a ≤ 1 ∧
      ∀ y ∈ K, ∃ z ∈ F, dist y z < 2 * s := by
  classical
  have hsmall : ∀ F : Finset X, (F : Set X) ⊆ K →
      (F : Set X).Pairwise (fun x y ↦ 2 * s ≤ dist x y) → (F.card : ℝ) * a ≤ 1 := by
    intro F hFK hsep
    have hdisj : (F : Set X).PairwiseDisjoint (fun x ↦ Metric.ball x s) := by
      intro x hx y hy hxy
      rw [Function.onFun, Set.disjoint_left]
      intro z hzx hzy
      have h1 := hsep hx hy hxy
      rw [Metric.mem_ball] at hzx hzy
      have h2 := dist_triangle_left x y z
      linarith
    have hU := measure_biUnion_finset (μ := P) hdisj (fun x _ ↦ measurableSet_ball)
    have hle : ∑ x ∈ F, P (Metric.ball x s) ≤ 1 := hU ▸ prob_le_one
    have h : ∑ _x ∈ F, ENNReal.ofReal a ≤ 1 :=
      (Finset.sum_le_sum fun x hx ↦ hball x (hFK hx)).trans hle
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)] at h
    exact ENNReal.ofReal_le_one.mp h
  by_contra hno
  push Not at hno
  have hbuild : ∀ k : ℕ, ∃ F : Finset X, (F : Set X) ⊆ K ∧
      (F : Set X).Pairwise (fun x y ↦ 2 * s ≤ dist x y) ∧ F.card = k := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp, rfl⟩
    | succ k ih =>
      obtain ⟨F, hFK, hsep, hcard⟩ := ih
      obtain ⟨y, hyK, hy⟩ := hno F hFK (hsmall F hFK hsep)
      have hyF : y ∉ F := fun h ↦ by
        have := hy y h
        rw [dist_self] at this
        linarith
      refine ⟨insert y F, ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]; exact insert_subset hyK hFK
      · rw [Finset.coe_insert]
        refine Set.pairwise_insert.2 ⟨hsep, fun b hb _ ↦ ⟨hy b hb, ?_⟩⟩
        rw [dist_comm]; exact hy b hb
      · rw [Finset.card_insert_of_notMem hyF, hcard]
  obtain ⟨F, hFK, hsep, hcard⟩ := hbuild (⌈1 / a⌉₊ + 1)
  have h := hsmall F hFK hsep
  rw [hcard] at h
  have h1 : 1 / a < ((⌈1 / a⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  rw [div_lt_iff₀ ha] at h1
  linarith

/-- Hausdorff sampling bound from a small-ball lower bound: let `μ` be a probability measure
carried by a measurable set `K` such that every ball `B(x, s)` with `x ∈ K` and `0 < s ≤ ε/2`
has mass at least `β s^d`. Then an independent sample of size `n` from `μ` is `ε`-close to `K`
in Hausdorff distance with probability at least `1 - (β (ε/4)^d)⁻¹ exp(-β (ε/2)^d n)`. The proof
is a union bound over the balls of radius `ε/2` around a maximal `ε/2`-packing of `K`. -/
theorem one_sub_le_measure_real_pi_hausdorff_dist_le {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {K : Set X} (hK : MeasurableSet K) (hμK : μ Kᶜ = 0) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β)
    (d n : ℕ)
    (hball : ∀ x ∈ K, ∀ s ∈ Ioc 0 (ε / 2), ENNReal.ofReal (β * s ^ d) ≤ μ (ball x s)) :
    1 - (β * (ε / 4) ^ d)⁻¹ * Real.exp (-(β * (ε / 2) ^ d * n)) ≤
      (Measure.pi fun _ : Fin n ↦ μ).real {x | hausdorffDist (range x) K ≤ ε} := by
  set P := Measure.pi fun _ : Fin n ↦ μ
  obtain ⟨F, hFK, hFcard, hFnet⟩ := exists_finset_net_of_le_measure_ball μ K (s := ε / 4)
    (by positivity) (a := β * (ε / 4) ^ d) (by positivity)
    (fun x hx ↦ hball x hx _ ⟨by positivity, by linarith⟩)
  set p := β * (ε / 2) ^ d
  -- the bad event
  set A := ⋃ i : Fin n, (fun x : Fin n → X ↦ x i) ⁻¹' Kᶜ
  set B := ⋃ z ∈ F, univ.pi fun _ : Fin n ↦ (ball z (ε / 2))ᶜ
  have hsub : (A ∪ B)ᶜ ⊆ {x | hausdorffDist (range x) K ≤ ε} := by
    intro x hx
    simp only [A, B, compl_union, mem_inter_iff, mem_compl_iff, mem_iUnion, mem_preimage,
      not_exists, not_not, mem_univ_pi, not_forall] at hx
    obtain ⟨hK', hB'⟩ := hx
    refine Metric.hausdorffDist_le_of_mem_dist hε.le ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, hK' i, by rw [dist_self]; exact hε.le⟩
    · intro y hy
      obtain ⟨z, hzF, hyz⟩ := hFnet y hy
      obtain ⟨i, hiz⟩ := hB' z hzF
      refine ⟨_, ⟨i, rfl⟩, ?_⟩
      rw [mem_ball] at hiz
      linarith [dist_triangle y z (x i), dist_comm z (x i)]
  have hAm : MeasurableSet A := MeasurableSet.iUnion fun i ↦ measurable_pi_apply i hK.compl
  have hBm : MeasurableSet B := Finset.measurableSet_biUnion _ fun z _ ↦
    MeasurableSet.univ_pi fun _ ↦ measurableSet_ball.compl
  have hA : P.real A = 0 := by
    refine le_antisymm ((measureReal_iUnion_fintype_le _).trans ?_) measureReal_nonneg
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).le
    rw [measureReal_def, Measure.pi_eval_preimage_null _ hμK, ENNReal.toReal_zero]
  have hB : P.real B ≤ F.card * Real.exp (-(p * n)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun z hz ↦ ?_
    rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← measureReal_def, probReal_compl_eq_one_sub measurableSet_ball]
    set q := μ.real (ball z (ε / 2))
    have hq1 : q ≤ 1 := measureReal_le_one
    have hpq : p ≤ q := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1
      (hball z (hFK hz) _ ⟨by positivity, le_rfl⟩)
    calc (1 - q) ^ n ≤ Real.exp (-q) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) n
      _ = Real.exp (-(q * n)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(p * n)) := Real.exp_le_exp.mpr (by nlinarith)
  have hFb : (F.card : ℝ) ≤ (β * (ε / 4) ^ d)⁻¹ := by
    rw [← one_div]; exact (le_div_iff₀ (by positivity)).2 hFcard
  calc 1 - (β * (ε / 4) ^ d)⁻¹ * Real.exp (-(p * n))
      ≤ 1 - P.real (A ∪ B) := by
        have := measureReal_union_le (μ := P) A B
        have : (F.card : ℝ) * Real.exp (-(p * n)) ≤ (β * (ε / 4) ^ d)⁻¹ * Real.exp (-(p * n)) :=
          mul_le_mul_of_nonneg_right hFb (Real.exp_pos _).le
        linarith
    _ = P.real (A ∪ B)ᶜ := (probReal_compl_eq_one_sub (hAm.union hBm)).symm
    _ ≤ P.real {x | hausdorffDist (range x) K ≤ ε} := measureReal_mono hsub

/-- Small balls in the image of a bi-Lipschitz local parametrization: let `g : ℝ^d → X` be
Lipschitz near `u₀` and have a left inverse `h` on a neighbourhood `T` of `u₀` that is Lipschitz
near `g u₀`. Then there are `ρ, a, r₀ > 0` such that `μH[d] (B(g u, r) ∩ g(T)) ≥ a r^d` for all
`u` with `|u - u₀| < ρ` and all `r ∈ (0, r₀)`. -/
private theorem exists_hausdorff_measure_ball_inter_image_ge
    {d : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {g : EuclideanSpace ℝ (Fin d) → X} {h : X → EuclideanSpace ℝ (Fin d)}
    {T U : Set (EuclideanSpace ℝ (Fin d))} {W : Set X} {u₀ : EuclideanSpace ℝ (Fin d)}
    {K₁ K₂ : ℝ≥0} (hT : T ∈ 𝓝 u₀) (hU : U ∈ 𝓝 u₀) (hW : W ∈ 𝓝 (g u₀))
    (hg : LipschitzOnWith K₁ g U) (hh : LipschitzOnWith K₂ h W) (hhg : ∀ u ∈ T, h (g u) = u) :
    ∃ ρ > 0, ∃ a > 0, ∃ r₀ > 0, ∀ u ∈ ball u₀ ρ, ∀ r ∈ Ioo 0 r₀,
      ENNReal.ofReal (a * r ^ d) ≤ μH[d] (ball (g u) r ∩ g '' T) := by
  have hgc : ContinuousAt g u₀ := hg.continuousOn.continuousAt hU
  have hS : T ∩ U ∩ g ⁻¹' W ∈ 𝓝 u₀ := inter_mem (inter_mem hT hU) (hgc.preimage_mem_nhds hW)
  obtain ⟨ρ', hρ', hball⟩ := Metric.mem_nhds_iff.1 hS
  set L₁ : ℝ≥0 := K₁ + 1
  set L₂ : ℝ≥0 := K₂ + 1
  have hL₁ : (0 : ℝ) < L₁ := by positivity
  have hL₂ : (0 : ℝ) < L₂ := by positivity
  set B : ℝ≥0∞ := μH[d] (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hB0 : B ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hBtop : B ≠ ⊤ := measure_ball_lt_top.ne
  set a : ℝ := B.toReal / ((L₁ : ℝ) ^ d * (L₂ : ℝ) ^ d)
  have ha : 0 < a := div_pos (ENNReal.toReal_pos hB0 hBtop) (by positivity)
  refine ⟨ρ' / 2, by positivity, a, ha, L₁ * (ρ' / 2), by positivity, ?_⟩
  rintro u hu r ⟨hr0, hr⟩
  set A := ball u (r / L₁)
  have hrL : r / L₁ < ρ' / 2 := by rw [div_lt_iff₀ hL₁]; linarith
  have hA : A ⊆ T ∩ U ∩ g ⁻¹' W := by
    refine Subset.trans (fun v hv ↦ ?_) hball
    rw [mem_ball] at hv hu ⊢
    linarith [dist_triangle v u u₀]
  have hgA : g '' A ⊆ ball (g u) r ∩ g '' T := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, mem_image_of_mem g (hA hv).1.1⟩
    have hu' : u ∈ A := mem_ball_self (by positivity)
    have h1 := (hg.weaken (show K₁ ≤ L₁ from le_add_of_nonneg_right zero_le_one)).dist_le_mul v
      (hA hv).1.2 u (hA hu').1.2
    rw [mem_ball] at hv ⊢
    calc dist (g v) (g u) ≤ L₁ * dist v u := h1
      _ < L₁ * (r / L₁) := by gcongr
      _ = r := by field_simp
  have hhgA : h '' (g '' A) = A := by
    rw [image_image]
    exact (image_congr fun v hv ↦ hhg v (hA hv).1.1).trans (image_id' A)
  have hle : μH[d] A ≤ (L₂ : ℝ≥0∞) ^ (d : ℝ) * μH[d] (g '' A) := by
    have := ((hh.weaken (show K₂ ≤ L₂ from le_add_of_nonneg_right zero_le_one)).mono
      (show g '' A ⊆ W by rintro _ ⟨v, hv, rfl⟩; exact (hA hv).2)).hausdorffMeasure_image_le
      (d := d) (Nat.cast_nonneg d)
    rwa [hhgA] at this
  have hAeq : μH[d] A = ENNReal.ofReal ((r / L₁) ^ d) * B := by
    rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace_fin]
  have hkey : ENNReal.ofReal (a * r ^ d) * (L₂ : ℝ≥0∞) ^ (d : ℝ) = μH[d] A := by
    rw [hAeq, ENNReal.rpow_natCast, ← ENNReal.ofReal_toReal hBtop, ← ENNReal.ofReal_mul
      (by positivity), ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [a]
    rw [div_pow]
    field_simp
  refine le_trans ?_ (measure_mono hgA)
  have hL₂0 : (L₂ : ℝ≥0∞) ^ (d : ℝ) ≠ 0 := by positivity
  have hL₂t : (L₂ : ℝ≥0∞) ^ (d : ℝ) ≠ ⊤ := by simp
  rw [← ENNReal.mul_le_mul_iff_left hL₂0 hL₂t, hkey, mul_comm]
  exact hle


/-- Local small-ball bound on an immersed manifold: if `j : N → ℝ^D` is a smooth immersion of a
manifold modeled on `ℝ^d`, every point of `N` has an open neighbourhood `V` and constants
`a, r₀ > 0` with `μH[d] (B(j x', r) ∩ j(N)) ≥ a r^d` for `x' ∈ V` and `r ∈ (0, r₀)`. -/
private theorem exists_is_open_hausdorff_measure_ball_inter_range_ge {d D : ℕ} {N : Type*}
    [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    [IsManifold (𝓡 d) ∞ N] {j : N → EuclideanSpace ℝ (Fin D)}
    (hj : Manifold.IsImmersion (𝓡 d) 𝓘(ℝ, EuclideanSpace ℝ (Fin D)) ∞ j) (x : N) :
    ∃ V : Set N, IsOpen V ∧ x ∈ V ∧ ∃ a > 0, ∃ r₀ > 0, ∀ x' ∈ V, ∀ r ∈ Ioo 0 r₀,
      ENNReal.ofReal (a * r ^ d) ≤ μH[d] (ball (j x') r ∩ range j) := by
  have hx := hj.isImmersionAt x
  set φ := hx.domChart
  set ψ := hx.codChart
  set L := hx.equiv
  have hψ := hx.codChart_mem_maximalAtlas
  have hψs : φ.source ⊆ j ⁻¹' ψ.source := hx.source_subset_preimage_source
  have hxφ : x ∈ φ.source := hx.mem_domChart_source
  have hTsimp : (φ.extend (𝓡 d)).target = φ.target := by simp
  have hw : EqOn (ψ ∘ j ∘ φ.symm) (L ∘ (·, 0)) φ.target := by
    have h := hx.writtenInCharts
    rw [hTsimp] at h
    simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id] using h
  -- `g = j ∘ φ⁻¹` agrees with `ψ⁻¹ ∘ L ∘ (·, 0)` on the chart target
  have hgT : ∀ u ∈ φ.target, j (φ.symm u) = ψ.symm (L (u, 0)) := by
    intro u hu
    have h1 : j (φ.symm u) ∈ ψ.source := hψs (φ.map_target hu)
    rw [← ψ.left_inv h1]
    exact congrArg ψ.symm (hw hu)
  have hxT : φ x ∈ φ.target := φ.map_source hxφ
  have hjx : ψ (j x) = L (φ x, 0) := by
    have := hw hxT
    simp only [Function.comp_apply, φ.left_inv hxφ] at this
    exact this
  have hjxs : j x ∈ ψ.source := hψs hxφ
  -- smoothness of `ψ` and `ψ⁻¹`
  have hψd : ContDiffOn ℝ ∞ ψ ψ.source :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_of_mem_maximalAtlas hψ)
  have hψd' : ContDiffOn ℝ ∞ ψ.symm ψ.target :=
    contMDiffOn_iff_contDiffOn.1 (contMDiffOn_symm_of_mem_maximalAtlas hψ)
  set ι : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin D) :=
    L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)
  have hι : ∀ u, ι u = L (u, 0) := fun u ↦ rfl
  have hg1 : ContDiffAt ℝ 1 (fun u ↦ ψ.symm (ι u)) (φ x) := by
    have hmem : ι (φ x) ∈ ψ.target := by rw [hι, ← hjx]; exact ψ.map_source hjxs
    have : ContDiffAt ℝ 1 ψ.symm (ι (φ x)) :=
      (hψd'.contDiffAt (ψ.open_target.mem_nhds hmem)).of_le (by simp)
    exact this.comp (φ x) ι.contDiff.contDiffAt
  set π : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.fst ℝ _ _).comp L.symm.toContinuousLinearMap
  have hh1 : ContDiffAt ℝ 1 (fun y ↦ π (ψ y)) (j x) := by
    have : ContDiffAt ℝ 1 ψ (j x) :=
      (hψd.contDiffAt (ψ.open_source.mem_nhds hjxs)).of_le (by simp)
    exact π.contDiff.contDiffAt.comp (j x) this
  obtain ⟨K₁, U, hU, hgU⟩ := hg1.exists_lipschitzOnWith
  obtain ⟨K₂, W, hW, hhW⟩ := hh1.exists_lipschitzOnWith
  have hgL : LipschitzOnWith K₁ (j ∘ φ.symm) (U ∩ φ.target) := by
    intro u hu v hv
    simp only [Function.comp_apply, hgT u hu.2, hgT v hv.2]
    exact hgU hu.1 hv.1
  have hhg : ∀ u ∈ φ.target, π (ψ ((j ∘ φ.symm) u)) = u := by
    intro u hu
    have h := hw hu
    simp only [Function.comp_apply] at h
    simp [π, h]
  have hgx : (j ∘ φ.symm) (φ x) = j x := by simp [φ.left_inv hxφ]
  obtain ⟨ρ, hρ, a, ha, r₀, hr₀, hmain⟩ := exists_hausdorff_measure_ball_inter_image_ge
    (φ.open_target.mem_nhds hxT) (inter_mem hU (φ.open_target.mem_nhds hxT))
    (by rw [hgx]; exact hW) hgL hhW hhg
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ x) ρ, φ.continuousOn.isOpen_inter_preimage φ.open_source
    isOpen_ball, ⟨hxφ, mem_preimage.2 (mem_ball_self hρ)⟩, a, ha, r₀, hr₀, ?_⟩
  rintro x' ⟨hx's, hx'b⟩ r hr
  have h := hmain (φ x') hx'b r hr
  have hgx' : (j ∘ φ.symm) (φ x') = j x' := by simp [φ.left_inv hx's]
  rw [hgx'] at h
  refine h.trans (measure_mono (inter_subset_inter_right _ ?_))
  rintro _ ⟨u, -, rfl⟩
  exact mem_range_self _

/-- Uniform small-ball bound on a compact immersed manifold: if `N` is a compact smooth manifold
modeled on `ℝ^d` and `j : N → ℝ^D` a smooth immersion, there are `a, r₀ > 0` such that
`μH[d] (B(j x, r) ∩ j(N)) ≥ a r^d` for every `x ∈ N` and every `r ∈ (0, r₀)`. -/
theorem exists_hausdorff_measure_ball_inter_range_ge_of_is_immersion {d D : ℕ} {N : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin d)) N] [IsManifold (𝓡 d) ∞ N]
    [CompactSpace N] {j : N → EuclideanSpace ℝ (Fin D)}
    (hj : Manifold.IsImmersion (𝓡 d) 𝓘(ℝ, EuclideanSpace ℝ (Fin D)) ∞ j) :
    ∃ a > 0, ∃ r₀ > 0, ∀ x : N, ∀ r ∈ Ioo 0 r₀,
      ENNReal.ofReal (a * r ^ d) ≤ μH[d] (ball (j x) r ∩ range j) := by
  rcases isEmpty_or_nonempty N with hN | hN
  · exact ⟨1, one_pos, 1, one_pos, fun x ↦ isEmptyElim x⟩
  choose V hVo hxV a ha r₀ hr₀ hV using exists_is_open_hausdorff_measure_ball_inter_range_ge hj
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover V fun x ↦ (hVo x).mem_nhds (hxV x)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := hN
    have hx : x ∈ ⋃ y ∈ t, V y := ht ▸ mem_univ x
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 hx
    exact ⟨y, hy⟩
  refine ⟨t.inf' htne a, (Finset.lt_inf'_iff htne).2 fun y _ ↦ ha y, t.inf' htne r₀,
    (Finset.lt_inf'_iff htne).2 fun y _ ↦ hr₀ y, ?_⟩
  intro x r ⟨hr0, hr⟩
  have hx : x ∈ ⋃ y ∈ t, V y := ht ▸ mem_univ x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hV y x hxy r ⟨hr0, hr.trans_le
    (Finset.inf'_le _ hy)⟩)
  exact mul_le_mul_of_nonneg_right (Finset.inf'_le _ hy) (by positivity)

end CKSD
