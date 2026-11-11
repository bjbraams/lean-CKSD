module

public import CKSD.Bayes.StochasticApproximationPath
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.OmegaLimit

/-!
# Limit sets of stochastic approximation and asymptotic pseudotrajectories

A bounded affine stochastic approximation with vanishing steps and convergent accumulated noise
has a compact connected internally chain transitive limit set. The argument passes to its
continuous interpolation, applies the deterministic ODE method, and identifies its cluster set
with the discrete limit set.

Mathlib supplies Grönwall bounds for ODE trajectories and attraction to compactly absorbed
omega-limit sets. Pinned TauCeti supplies preconnectedness of the cluster set of a continuous
curve (`TauCeti.isPreconnected_setOf_mapClusterPt_atTop`). Flow invariance follows by extending
asymptotic tracking to negative times. For internal chain transitivity, a late segment joining
neighborhoods of two cluster points is partitioned into flight times between `T` and `2T`, and
the partition points are approximated by points of the cluster set.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two global trajectories of a Lipschitz autonomous field differ by at most the usual
exponential factor in either time direction. -/
theorem dist_le_exp_of_global_trajectories {F : E → E} {L : ℝ≥0}
    (hL : LipschitzWith L F) {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (F (f t)) t) (hg : ∀ t, HasDerivAt g (F (g t)) t) (t : ℝ) :
    dist (f t) (g t) ≤ dist (f 0) (g 0) * Real.exp ((L : ℝ) * |t|) := by
  have hpos {v : E → E} (hv : LipschitzWith L v) {p q : ℝ → E}
      (hp : ∀ s, HasDerivAt p (v (p s)) s) (hq : ∀ s, HasDerivAt q (v (q s)) s)
      (r : ℝ) (hr : 0 ≤ r) : dist (p r) (q r) ≤ dist (p 0) (q 0) * Real.exp ((L : ℝ) * r) := by
    have hpcont : Continuous p := continuous_iff_continuousAt.2 fun s ↦ (hp s).continuousAt
    have hqcont : Continuous q := continuous_iff_continuousAt.2 fun s ↦ (hq s).continuousAt
    have hb := dist_le_of_trajectories_ODE (v := fun _ x ↦ v x) (K := L)
      (fun _ ↦ hv) hpcont.continuousOn (fun s _ ↦ (hp s).hasDerivWithinAt)
      hqcont.continuousOn (fun s _ ↦ (hq s).hasDerivWithinAt) (le_refl (dist (p 0) (q 0))) r ⟨hr, le_rfl⟩
    simpa only [sub_zero] using hb
  rcases le_total 0 t with ht | ht
  · simpa only [abs_of_nonneg ht] using hpos hL hf hg t ht
  · have hfr (r : ℝ) : HasDerivAt (fun s ↦ f (-s)) (-F (f (-r))) r := by
      have hh := (hf (-r)).scomp r (hasDerivAt_neg r)
      simpa only [Function.comp_def, neg_one_smul] using hh
    have hgr (r : ℝ) : HasDerivAt (fun s ↦ g (-s)) (-F (g (-r))) r := by
      have hh := (hg (-r)).scomp r (hasDerivAt_neg r)
      simpa only [Function.comp_def, neg_one_smul] using hh
    simpa only [neg_neg, neg_zero, abs_of_nonpos ht] using
      hpos hL.neg hfr hgr (-t) (neg_nonneg.2 ht)

/-- A globally defined solution family of a Lipschitz autonomous ODE satisfies the flow law. -/
theorem IsFlowOf.map_add {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h)
    {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ) (t s : ℝ) (x : E) :
    Φ t (Φ s x) = Φ (t + s) x := by
  have hd (r : ℝ) : HasDerivAt (fun u ↦ Φ (u + s) x) (-h (Φ (r + s) x)) r := by
    have hh := ((hΦ x).2 (r + s)).scomp r ((hasDerivAt_id r).add_const s)
    simpa only [Function.comp_def, id_eq, one_smul] using hh
  have hh := dist_le_exp_of_global_trajectories hL.neg ((hΦ (Φ s x)).2) hd t
  have hz : dist (Φ 0 (Φ s x)) (Φ (0 + s) x) = 0 := by rw [(hΦ _).1, zero_add, dist_self]
  rw [hz, zero_mul] at hh
  exact dist_le_zero.1 hh

/-- A Lipschitz autonomous flow has an exponential bound on dependence on its initial point. -/
theorem IsFlowOf.norm_sub_le_exp {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h)
    {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ) (t : ℝ) (x y : E) :
    ‖Φ t x - Φ t y‖ ≤ Real.exp ((L : ℝ) * |t|) * ‖x - y‖ := by
  have hh := dist_le_exp_of_global_trajectories hL.neg ((hΦ x).2) ((hΦ y).2) t
  simpa only [(hΦ x).1, (hΦ y).1, dist_eq_norm, mul_comm] using hh

/-- At every fixed time, a Lipschitz autonomous flow is continuous in its initial point. -/
theorem IsFlowOf.continuous_apply {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h)
    {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ) (t : ℝ) : Continuous (Φ t) := by
  apply continuous_iff_continuousAt.2
  intro x
  apply Metric.continuousAt_iff.2
  intro ε hε
  refine ⟨ε / Real.exp ((L : ℝ) * |t|), div_pos hε (Real.exp_pos _), ?_⟩
  intro y hy
  rw [dist_eq_norm] at hy ⊢
  calc ‖Φ t y - Φ t x‖ ≤ Real.exp ((L : ℝ) * |t|) * ‖y - x‖ := hΦ.norm_sub_le_exp hL t y x
    _ < Real.exp ((L : ℝ) * |t|) * (ε / Real.exp ((L : ℝ) * |t|)) :=
      mul_lt_mul_of_pos_left hy (Real.exp_pos _)
    _ = ε := by field_simp

omit [NormedSpace ℝ E] in
/-- Functions whose difference tends to zero have the same cluster points along a countably
generated filter. -/
theorem mapClusterPt_of_tendsto_sub {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {u v : α → E} {x : E} (hu : MapClusterPt x l u)
    (huv : Tendsto (fun a ↦ u a - v a) l (𝓝 0)) : MapClusterPt x l v := by
  obtain ⟨ψ, hψu, hψ⟩ := hu.exists_seq_tendsto
  have hh := hψu.sub (huv.comp hψ)
  have hv : Tendsto (v ∘ ψ) atTop (𝓝 x) := by
    convert hh using 1
    · funext n
      simp only [Function.comp_apply]
      abel
    · simp
  exact hv.mapClusterPt.of_comp hψ

/-- Forward asymptotic tracking of a globally defined Lipschitz flow also gives tracking at
each fixed negative time. -/
theorem tendsto_shift_sub_flow_of_apt {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h)
    {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ) (u : ℝ → E)
    (hapt : ∀ T > 0, ∀ ε > 0, ∀ᶠ s in atTop, ∀ r ∈ Icc 0 T, ‖u (s + r) - Φ r (u s)‖ ≤ ε)
    (t : ℝ) : Tendsto (fun s ↦ u (s + t) - Φ t (u s)) atTop (𝓝 0) := by
  have hpos (r : ℝ) (hr : 0 ≤ r) :
      Tendsto (fun s ↦ u (s + r) - Φ r (u s)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hapt (r + 1) (by linarith) (ε / 2) (half_pos hε)] with s hs
    have hh := hs r ⟨hr, by linarith⟩
    simpa only [dist_eq_norm, sub_zero] using hh.trans_lt (half_lt_self hε)
  rcases le_total 0 t with ht | ht
  · exact hpos t ht
  · have hshift : Tendsto (fun s : ℝ ↦ s + t) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have he := (hpos (-t) (neg_nonneg.2 ht)).comp hshift
    apply squeeze_zero_norm (fun s ↦ ?_)
      (by simpa using he.norm.const_mul (Real.exp ((L : ℝ) * |t|)))
    have hh := hΦ.norm_sub_le_exp hL t (Φ (-t) (u (s + t))) (u s)
    rw [hΦ.map_add hL, add_neg_cancel, (hΦ _).1] at hh
    exact hh.trans_eq (congrArg (fun z : ℝ ↦ Real.exp ((L : ℝ) * |t|) * z) (norm_sub_rev _ _))

/-- The cluster set at infinity of an asymptotic pseudotrajectory is invariant under the flow
for every real time. -/
theorem isInvariantSet_clusterSet_of_apt {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h)
    {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ) (u : ℝ → E)
    (hapt : ∀ T > 0, ∀ ε > 0, ∀ᶠ s in atTop, ∀ r ∈ Icc 0 T, ‖u (s + r) - Φ r (u s)‖ ≤ ε) :
    IsInvariantSet Φ {x | MapClusterPt x atTop u} := by
  have hmaps (t : ℝ) {x : E} (hx : MapClusterPt x atTop u) : MapClusterPt (Φ t x) atTop u := by
    have hc := hx.continuousAt_comp (hΦ.continuous_apply hL t).continuousAt
    have he := tendsto_shift_sub_flow_of_apt hL hΦ u hapt t
    have he' : Tendsto (fun s ↦ (Φ t ∘ u) s - u (s + t)) atTop (𝓝 0) := by
      convert he.neg using 1
      · funext s
        simp only [Function.comp_apply]
        abel
      · simp
    have hc' : MapClusterPt (Φ t x) atTop (fun s ↦ u (s + t)) :=
      mapClusterPt_of_tendsto_sub hc he'
    exact hc'.of_comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  intro t
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hmaps t hx
  · intro x hx
    refine ⟨Φ (-t) x, hmaps (-t) hx, ?_⟩
    rw [hΦ.map_add hL, add_neg_cancel, (hΦ x).1]


omit [NormedSpace ℝ E] in
/-- A continuous curve confined to a compact set has a compact connected cluster set at infinity. -/
theorem isCompact_isConnected_clusterSet_of_mapsTo {u : ℝ → E} {K : Set E}
    (hK : IsCompact K) (hu : ContinuousOn u (Ici 0)) (hum : MapsTo u (Ici 0) K) :
    IsCompact {x | MapClusterPt x atTop u} ∧ IsConnected {x | MapClusterPt x atTop u} := by
  have hev : ∀ᶠ s in atTop, u s ∈ K := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs using hum hs
  have hclosed : IsClosed {x | MapClusterPt x atTop u} := by
    rw [TauCeti.setOf_mapClusterPt_atTop_eq_iInter u 0]
    exact isClosed_iInter fun _ ↦ isClosed_closure
  have hsub : {x | MapClusterPt x atTop u} ⊆ K := fun x hx ↦
    hK.isClosed.mem_of_mapClusterPt hx hev
  have hcompact := hK.of_isClosed_subset hclosed hsub
  have hne : ({x | MapClusterPt x atTop u} : Set E).Nonempty := by
    obtain ⟨x, _, hx⟩ := hK.exists_mapClusterPt (tendsto_principal.2 hev)
    exact ⟨x, hx⟩
  exact ⟨hcompact, hne, TauCeti.isPreconnected_setOf_mapClusterPt_atTop hK hu hum⟩

omit [NormedSpace ℝ E] in
/-- A curve confined eventually to a compact set approaches its cluster set at infinity. -/
theorem eventually_exists_clusterPoint_near {u : ℝ → E} {K : Set E}
    (hK : IsCompact K) (hum : MapsTo u (Ici 0) K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ s in atTop, ∃ z, MapClusterPt z atTop u ∧ ‖u s - z‖ < δ := by
  let A : Set E := {x | MapClusterPt x atTop u}
  have heq : omegaLimit atTop (fun t (_ : Unit) ↦ u t) {()} = A := by
    ext x
    exact mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := fun t (_ : Unit) ↦ u t) () x
  have hev : ∀ᶠ t in atTop, MapsTo (fun _ : Unit ↦ u t) {()} K := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact fun _ _ ↦ hum ht
  have hsub : omegaLimit atTop (fun t (_ : Unit) ↦ u t) {()} ⊆ Metric.thickening δ A := by
    rw [heq]
    exact Metric.self_subset_thickening hδ A
  have hh := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
    atTop (fun t (_ : Unit) ↦ u t) {()} hK hev Metric.isOpen_thickening hsub
  filter_upwards [hh] with s hs
  obtain ⟨z, hz, hsz⟩ := Metric.mem_thickening_iff.1 (hs (show () ∈ ({()} : Set Unit) by simp))
  exact ⟨z, hz, by simpa only [dist_eq_norm] using hsz⟩


/-- The cluster set at infinity of a confined asymptotic pseudotrajectory is internally chain
transitive. Long late curve segments give chains with flight times between `T` and `2T`. -/
theorem isInternallyChainTransitive_clusterSet_of_apt {h : E → E} {L : ℝ≥0}
    (hL : LipschitzWith L h) {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ)
    (u : ℝ → E) {K : Set E} (hK : IsCompact K) (hum : MapsTo u (Ici 0) K)
    (hapt : ∀ T > 0, ∀ ε > 0, ∀ᶠ s in atTop, ∀ r ∈ Icc 0 T, ‖u (s + r) - Φ r (u s)‖ ≤ ε) :
    IsInternallyChainTransitive Φ {x | MapClusterPt x atTop u} := by
  classical
  refine ⟨isInvariantSet_clusterSet_of_apt hL hΦ u hapt, ?_⟩
  intro x hx y hy ε hε T hT
  let C := Real.exp ((L : ℝ) * (2 * T))
  have hC : 0 < C := Real.exp_pos _
  let δ := ε / (C + 2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : C * δ + δ + δ = ε := by dsimp [δ]; field_simp; ring
  obtain ⟨S, hS⟩ := eventually_atTop.1
    ((hapt (2 * T) (by positivity) δ hδ).and (eventually_exists_clusterPoint_near hK hum hδ))
  obtain ⟨a, hax, haS⟩ := ((hx.frequently (Metric.ball_mem_nhds x hδ)).and_eventually
    (eventually_ge_atTop S)).exists
  have hax' : ‖u a - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hax
  obtain ⟨b, hby, hba⟩ := ((hy.frequently (Metric.ball_mem_nhds y hδ)).and_eventually
    (eventually_ge_atTop (a + T))).exists
  have hby' : ‖u b - y‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hby
  let D := b - a
  have hD : T ≤ D := by dsimp [D]; linarith
  have hratio : 1 ≤ D / T := (le_div_iff₀ hT).2 (by linarith)
  let n := ⌊D / T⌋₊
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hratio)
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnle : (n : ℝ) ≤ D / T := Nat.floor_le (by positivity)
  have hlt : D / T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  let q := D / n
  have hqT : T ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hnR]
    simpa only [mul_comm] using (le_div_iff₀ hT).1 hnle
  have hq0 : 0 < q := hT.trans_le hqT
  have hq2 : q ≤ 2 * T := by
    dsimp [q]
    rw [div_le_iff₀ hnR]
    have hdlt : D < ((n : ℝ) + 1) * T := (div_lt_iff₀ hT).1 hlt
    nlinarith
  let τ : ℕ → ℝ := fun j ↦ a + (j : ℝ) * q
  have hτge (j : ℕ) : S ≤ τ j := by
    dsimp [τ]
    exact haS.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hq0.le))
  have hτ0 : τ 0 = a := by simp [τ]
  have hτn : τ n = b := by
    dsimp [τ, q, D]
    field_simp
    ring
  have hτsucc (j : ℕ) : τ (j + 1) = τ j + q := by simp [τ, Nat.cast_add]; ring
  have hnear (j : ℕ) : ∃ z, MapClusterPt z atTop u ∧ ‖u (τ j) - z‖ < δ := (hS _ (hτge j)).2
  choose w hwA hwnear using hnear
  let z : ℕ → E := fun j ↦ if j = 0 then x else if j = n then y else w j
  have hzA (j : ℕ) : MapClusterPt (z j) atTop u := by
    dsimp [z]
    split_ifs
    · exact hx
    · exact hy
    · exact hwA j
  have hz0 : z 0 = x := by simp [z]
  have hzn : z n = y := by simp [z, hn.ne']
  have hznear (j : ℕ) (hj : j ≤ n) : ‖z j - u (τ j)‖ < δ := by
    by_cases hj0 : j = 0
    · subst j
      simpa only [hz0, hτ0, norm_sub_rev] using hax'
    · by_cases hjn : j = n
      · subst j
        simpa only [hzn, hτn, norm_sub_rev] using hby'
      · simpa only [z, ite_eq_right hj0, ite_eq_right hjn, norm_sub_rev] using hwnear j
  refine ⟨n, hn, z, fun j _ ↦ hzA j, ?_, hzn, ?_⟩
  · rw [hz0, sub_self, norm_zero]
    exact hε
  · intro j hj
    refine ⟨q, hqT, ?_⟩
    have hnode := hznear j hj.le
    have hnext := hznear (j + 1) (Nat.succ_le_iff.2 hj)
    have hflow : ‖Φ q (z j) - Φ q (u (τ j))‖ < C * δ := by
      have hlip := hΦ.norm_sub_le_exp hL q (z j) (u (τ j))
      have hExp : Real.exp ((L : ℝ) * |q|) ≤ C := by
        rw [abs_of_pos hq0]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hq2 L.coe_nonneg)
      calc _ ≤ C * ‖z j - u (τ j)‖ :=
            hlip.trans (mul_le_mul_of_nonneg_right hExp (norm_nonneg _))
        _ < C * δ := mul_lt_mul_of_pos_left hnode hC
    have htrack : ‖Φ q (u (τ j)) - u (τ (j + 1))‖ ≤ δ := by
      rw [hτsucc, norm_sub_rev]
      exact (hS _ (hτge j)).1 q ⟨hq0.le, hq2⟩
    calc ‖Φ q (z j) - z (j + 1)‖ ≤
          ‖Φ q (z j) - Φ q (u (τ j))‖ + ‖Φ q (u (τ j)) - z (j + 1)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖Φ q (z j) - Φ q (u (τ j))‖ +
          (‖Φ q (u (τ j)) - u (τ (j + 1))‖ + ‖u (τ (j + 1)) - z (j + 1)‖) := by
            exact add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ < C * δ + (δ + δ) := by
        rw [norm_sub_rev (u (τ (j + 1))) (z (j + 1))]
        exact add_lt_add hflow (add_lt_add_of_le_of_lt htrack hnext)
      _ = ε := by linarith


/-- The affine stochastic-approximation interpolation recovers the sequence at each grid time. -/
theorem stochasticApproxInterp_time {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) (n : ℕ) :
    stochasticApproxInterp a x (stochasticApproxTime a n) = x n := by
  rw [stochasticApproxInterp_eq_of_mem_Icc ha ht x
    ⟨le_rfl, (strictMono_stochasticApproxTime ha).monotone (Nat.le_succ n)⟩,
    sub_self, zero_div, zero_smul, add_zero]

/-- For vanishing increments, the discrete limit set equals the interpolation cluster set. -/
theorem limitSet_eq_clusterSet_stochasticApproxInterp {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E)
    (hinc : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0)) :
    limitSet x = {y | MapClusterPt y atTop (stochasticApproxInterp a x)} := by
  ext y
  simp only [limitSet, mem_iInter, mem_ofPred_eq]
  rw [← mapClusterPt_atTop_iff_forall_mem_closure]
  constructor
  · intro hy
    have hh : MapClusterPt y atTop ((stochasticApproxInterp a x) ∘ stochasticApproxTime a) := by
      simpa only [Function.comp_def, stochasticApproxInterp_time ha ht] using hy
    exact hh.of_comp ht
  · intro hy
    have hh := mapClusterPt_of_tendsto_sub hy
      (tendsto_stochasticApproxInterp_sub_node ha ht x hinc)
    exact hh.of_comp (tendsto_stochasticApproxIndex ha ht)

/-- A bounded sequence gives a bounded affine interpolation on nonnegative times. -/
theorem norm_stochasticApproxInterp_le {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E) {R : ℝ}
    (hR : ∀ n, ‖x n‖ ≤ R) {s : ℝ} (hs : 0 ≤ s) : ‖stochasticApproxInterp a x s‖ ≤ 3 * R := by
  let n := stochasticApproxIndex a s
  have hh := norm_stochasticApproxInterp_sub_node_le ha ht x hs
  have hnext : ‖x (n + 1) - x n‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith [hR (n + 1), hR n])
  have htri := norm_le_norm_sub_add (stochasticApproxInterp a x s) (x n)
  linarith [hR n]

/-- A bounded affine interpolation that is an asymptotic pseudotrajectory has a compact
connected internally chain transitive discrete limit set when its increments vanish. -/
theorem limitSet_properties_of_stochasticApproxInterp [ProperSpace E]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (ht : Tendsto (stochasticApproxTime a) atTop atTop) (x : ℕ → E)
    (hinc : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0))
    (hbdd : BddAbove (range fun n ↦ ‖x n‖))
    {h : E → E} {L : ℝ≥0} (hL : LipschitzWith L h) {Φ : ℝ → E → E} (hΦ : IsFlowOf h Φ)
    (hapt : ∀ T > 0, ∀ ε > 0, ∀ᶠ s in atTop, ∀ r ∈ Icc 0 T,
      ‖stochasticApproxInterp a x (s + r) - Φ r (stochasticApproxInterp a x s)‖ ≤ ε) :
    IsCompact (limitSet x) ∧ IsConnected (limitSet x) ∧ IsInternallyChainTransitive Φ (limitSet x) := by
  obtain ⟨R, hR⟩ := hbdd
  have hmap : MapsTo (stochasticApproxInterp a x) (Ici 0) (Metric.closedBall 0 (3 * R)) := by
    intro s hs
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_stochasticApproxInterp_le ha ht x (fun n ↦ hR (mem_range_self n)) hs
  rw [limitSet_eq_clusterSet_stochasticApproxInterp ha ht x hinc]
  have hh := isCompact_isConnected_clusterSet_of_mapsTo (isCompact_closedBall (0 : E) (3 * R))
    (continuousOn_stochasticApproxInterp ha ht x) hmap
  exact ⟨hh.1, hh.2, isInternallyChainTransitive_clusterSet_of_apt hL hΦ
    (stochasticApproxInterp a x) (isCompact_closedBall (0 : E) (3 * R)) hmap hapt⟩

/-- Bounded stochastic-approximation iterates with vanishing steps and convergent cumulative
noise have a compact connected internally chain transitive limit set. -/
theorem limitSet_properties_of_stochasticApproximation [ProperSpace E]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (ht : Tendsto (stochasticApproxTime a) atTop atTop)
    (h : E → E) (L : ℝ≥0) (hL : LipschitzWith L h) (Φ : ℝ → E → E) (hΦ : IsFlowOf h Φ)
    (x S : ℕ → E) {c : E} (hS : Tendsto S atTop (𝓝 c))
    (hbdd : BddAbove (range fun n ↦ ‖x n‖))
    (hrec : ∀ n, x (n + 1) = x n - a n • h (x n) - (S (n + 1) - S n)) :
    IsCompact (limitSet x) ∧ IsConnected (limitSet x) ∧ IsInternallyChainTransitive Φ (limitSet x) := by
  obtain ⟨R, hR⟩ := hbdd
  let B := ‖h 0‖ + (L : ℝ) * max R 0
  have hB (n : ℕ) : ‖h (x n)‖ ≤ B := by
    calc ‖h (x n)‖ ≤ ‖h (x n) - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖x n‖ + ‖h 0‖ := by
        gcongr
        simpa using hL.norm_sub_le (x n) 0
      _ ≤ B := by
        dsimp [B]
        have hxR : ‖x n‖ ≤ max R 0 := (hR (mem_range_self n)).trans (le_max_left _ _)
        nlinarith [L.coe_nonneg, mul_le_mul_of_nonneg_left hxR L.coe_nonneg]
  have hadrift : Tendsto (fun n ↦ a n • h (x n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n ↦ by simpa only [norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (hB n) (abs_nonneg (a n)))
    simpa using ha0.abs.mul_const B
  have hSinc : Tendsto (fun n ↦ S (n + 1) - S n) atTop (𝓝 0) := by
    simpa using (hS.comp (tendsto_add_atTop_nat 1)).sub hS
  have hxinc : Tendsto (fun n ↦ x (n + 1) - x n) atTop (𝓝 0) := by
    convert hadrift.neg.sub hSinc using 1
    · funext n
      rw [hrec]
      abel
    · simp
  apply limitSet_properties_of_stochasticApproxInterp ha ht x hxinc ⟨R, hR⟩ hL hΦ
  exact fun T hT ↦ asymptotic_pseudotrajectory_stochasticApproxInterp ha ha0 ht
    h L hL Φ hΦ x S hS ⟨R, hR⟩ hrec T hT

end CKSD
