module

public import CKSD.LinearModels.DirectedGraphical.Basic.CausalGraph

/-!
# Identifiability of restricted structural equation models

A structural equation model along a directed acyclic graph `G` on a finite vertex set `V` is
described at the level of laws on `V → ℝ`: the noise vector has the product law of its
coordinate laws, and the observed vector is the image of the noise under the solution map of
the structural equations. In the linear case `X = B X + N`, with `B j k ≠ 0` exactly on the
edges `k → j`, the solution map is `N ↦ (1 - B)⁻¹ N`.

Conditional independence for laws on `V → ℝ` is Mathlib's `CondIndepFun` of coordinate
projections. Source: GAPS 105.71.

## Main results

* `CKSD.CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance`: linear Gaussian models with
  equal noise variances identify the graph.
* `CKSD.CausalGraph.IsLinearSEMMatrix.det_one_sub_ne_zero`: `1 - B` is nonsingular along a
  directed acyclic graph.
* `CKSD.variance_linearSEMLaw_gaussianReal`: the variance of a linear functional of a linear
  Gaussian model with common noise variance.

The equal-variance case compares precision matrices: equal laws give
`σ'² (1 - B)ᵀ(1 - B) = σ² (1 - B')ᵀ(1 - B')`. At a vertex without children the diagonal of
`(1 - B)ᵀ(1 - B)` equals one, and every diagonal entry is at least one, which forces `σ = σ'`.
Removing such vertices one at a time then recovers the rows of `1 - B` from the Gram matrix.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace CKSD

variable {V : Type*}

/-- A coefficient matrix of a linear structural equation model along `G`: the coefficient of
`X_k` in the equation of `X_j` is nonzero exactly when `k → j` is an edge. -/
def CausalGraph.IsLinearSEMMatrix (G : CausalGraph V) (B : Matrix V V ℝ) : Prop :=
  ∀ j k, B j k ≠ 0 ↔ G.edge k j

/-- The law of the solution `X = (1 - B)⁻¹ N` of a linear structural equation model with
independent noises of laws `ν j`. -/
def linearSEMLaw [Fintype V] [DecidableEq V] (B : Matrix V V ℝ) (ν : V → Measure ℝ) :
    Measure (V → ℝ) :=
  (Measure.pi ν).map fun n ↦ ((1 - B)⁻¹).mulVec n

/-- The law of a linear structural equation model with noise laws that are probability measures
is a probability measure. -/
instance isProbabilityMeasure_linearSEMLaw [Fintype V] [DecidableEq V] (B : Matrix V V ℝ)
    (ν : V → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] :
    IsProbabilityMeasure (linearSEMLaw B ν) := by
  unfold linearSEMLaw
  infer_instance

/-- A real law is non-Gaussian with a strictly positive density. -/
def IsNonGaussianPositiveDensityLaw (ν : Measure ℝ) : Prop :=
  (∃ f : ℝ → ℝ, HasDensity ν volume f ∧ ∀ t, 0 < f t) ∧
    ∀ (m : ℝ) (v : ℝ≥0), ν ≠ gaussianReal m v

/-- Restriction of a vector to the coordinates in `B`. -/
def coordinateRestriction (B : Finset V) (x : V → ℝ) : B → ℝ := fun b ↦ x b

/-- Coordinate restrictions are measurable. -/
@[fun_prop] theorem measurable_coordinateRestriction (B : Finset V) :
    Measurable (coordinateRestriction B : (V → ℝ) → B → ℝ) := by
  unfold coordinateRestriction
  fun_prop

/-- A law on `V → ℝ` is faithful to `G` when, for disjoint `A`, `B`, `C`, the coordinates in
`A` and `B` are conditionally independent given those in `C` exactly when `A` and `B` are
d-separated by `C`. -/
def CausalGraph.IsFaithfulLaw [Fintype V] (G : CausalGraph V) (μ : Measure (V → ℝ))
    [IsFiniteMeasure μ] : Prop :=
  ∀ A B C : Finset V, Disjoint A B → Disjoint A C → Disjoint B C →
    (G.DSeparated A B C ↔
      CondIndepFun ((inferInstance : MeasurableSpace (C → ℝ)).comap (coordinateRestriction C))
        (measurable_coordinateRestriction C).comap_le (coordinateRestriction A)
        (coordinateRestriction B) μ)

/-- The structural functions of an additive-noise model respect the parents of `G`. -/
def CausalGraph.RespectsParentsReal (G : CausalGraph V) (f : V → (V → ℝ) → ℝ) : Prop :=
  ∀ j x y, (∀ k, G.edge k j → x k = y k) → f j x = f j y

/-- The law of an additive-noise model `X_j = f_j(X_{pa(j)}) + N_j` with independent noises
of laws `ν j`: the image of the noise law under a measurable solution map of the equations. -/
def IsAdditiveNoiseLaw [Fintype V] (f : V → (V → ℝ) → ℝ) (ν : V → Measure ℝ)
    (μ : Measure (V → ℝ)) : Prop :=
  ∃ Φ : (V → ℝ) → V → ℝ, Measurable Φ ∧ (∀ n j, Φ n j = f j (Φ n) + n j) ∧
    μ = (Measure.pi ν).map Φ

/-- Each structural function is nonlinear in each of its parent arguments: along every line in
the direction of a parent coordinate it is not affine. -/
def CausalGraph.IsNonlinearInParents [DecidableEq V] (G : CausalGraph V)
    (f : V → (V → ℝ) → ℝ) : Prop :=
  ∀ j k, G.edge k j → ∀ x : V → ℝ, ¬ ∃ c d : ℝ, ∀ t, f j (Function.update x k t) = c * t + d

/-- GAPS 105.71, linear non-Gaussian models: if two linear structural equation models along
`G` and `H`, with nonzero coefficients on the edges and independent non-Gaussian noises with
strictly positive densities, have the same law, then `G = H`. -/
theorem CausalGraph.edge_eq_of_linearSEMLaw_eq_of_nonGaussian [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B B' : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B)
    (hB' : H.IsLinearSEMMatrix B') (ν ν' : V → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, IsProbabilityMeasure (ν' j)]
    (hν : ∀ j, IsNonGaussianPositiveDensityLaw (ν j))
    (hν' : ∀ j, IsNonGaussianPositiveDensityLaw (ν' j))
    (hlaw : linearSEMLaw B ν = linearSEMLaw B' ν') :
    G.edge = H.edge := by
  sorry

/-- In a causal graph there are no self-loops. -/
private theorem CausalGraph.not_edge_self' (G : CausalGraph V) (v : V) : ¬ G.edge v v :=
  fun h ↦ G.acyclic v (Relation.TransGen.single h)

/-- Every nonempty finite set of vertices contains a vertex with no child in the set. -/
private theorem CausalGraph.exists_sink_mem [Finite V] (G : CausalGraph V) {W : Finset V}
    (hW : W.Nonempty) : ∃ j ∈ W, ∀ k ∈ W, ¬ G.edge j k := by
  have : IsTrans V (flip (Relation.TransGen G.edge)) :=
    ⟨fun a b c hab hbc ↦ Relation.TransGen.trans hbc hab⟩
  have : Std.Irrefl (flip (Relation.TransGen G.edge)) := ⟨fun a ↦ G.acyclic a⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (flip (Relation.TransGen G.edge))
  obtain ⟨j, hj, hmin⟩ := wf.has_min (W : Set V) hW
  exact ⟨j, hj, fun k hk he ↦ hmin k hk (Relation.TransGen.single he)⟩

/-- The partial Gram matrix `∑_{r ∈ W} A_r A_rᵀ` of the rows of `A` indexed by `W`. -/
private def rowGram [Fintype V] (W : Finset V) (A : Matrix V V ℝ) : Matrix V V ℝ :=
  fun a b ↦ ∑ r ∈ W, A r a * A r b

/-- The diagonal of a linear SEM matrix vanishes. -/
theorem CausalGraph.IsLinearSEMMatrix.apply_self {G : CausalGraph V} {B : Matrix V V ℝ}
    (hB : G.IsLinearSEMMatrix B) (j : V) : B j j = 0 :=
  not_not.1 fun h ↦ G.not_edge_self' j ((hB j j).1 h)

/-- For a sink `j` of `G` within `W`, the `j`-th column of `1 - B` vanishes on `W` off `j`. -/
private theorem one_sub_apply_sink [DecidableEq V] {G : CausalGraph V} {B : Matrix V V ℝ}
    (hB : G.IsLinearSEMMatrix B) {W : Finset V} {j : V} (hj : ∀ k ∈ W, ¬ G.edge j k)
    {r : V} (hr : r ∈ W) : (1 - B) r j = if r = j then 1 else 0 := by
  have hB0 : B r j = 0 := by
    by_contra h
    exact hj r hr ((hB r j).1 h)
  by_cases h : r = j
  · subst h; simp [hB0]
  · simp [h, hB0, Matrix.one_apply_ne h]

/-- Peeling sinks: for linear SEM matrices `B`, `B'` along causal graphs `G`, `H`, equality of
the partial Gram matrices of `1 - B` and `1 - B'` over `W` forces equal rows over `W`. -/
private theorem rows_eq_of_rowGram_eq [Fintype V] [DecidableEq V] {G H : CausalGraph V}
    {B B' : Matrix V V ℝ} (hB : G.IsLinearSEMMatrix B) (hB' : H.IsLinearSEMMatrix B')
    (W : Finset V) (hW : rowGram W (1 - B) = rowGram W (1 - B')) :
    ∀ r ∈ W, (1 - B) r = (1 - B') r := by
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨j, hjW, hj⟩ := G.exists_sink_mem hne
  have hA := fun r (hr : r ∈ W) ↦ one_sub_apply_sink hB hj hr
  have hjj' : (1 - B') j j = 1 := by simp [Matrix.sub_apply, hB'.apply_self j]
  -- the `j`-th column of `A'` vanishes on `W` off `j`
  have hcol : ∀ r ∈ W, r ≠ j → (1 - B') r j = 0 := by
    have h1 : rowGram W (1 - B) j j = 1 := by
      simp only [rowGram]
      rw [Finset.sum_eq_single_of_mem j hjW fun r hr hrj ↦ by simp [hA r hr, hrj]]
      simp [hA j hjW]
    rw [hW] at h1
    simp only [rowGram] at h1
    rw [← Finset.add_sum_erase _ _ hjW, hjj', one_mul, add_eq_left] at h1
    intro r hr hrj
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_self_nonneg ((1 - B') i j)).1 h1 r
      (Finset.mem_erase.2 ⟨hrj, hr⟩)
    exact mul_self_eq_zero.1 this
  -- the `j`-th rows agree
  have hrow : (1 - B) j = (1 - B') j := by
    funext b
    have h := congrFun (congrFun hW j) b
    simp only [rowGram] at h
    rw [Finset.sum_eq_single_of_mem j hjW fun r hr hrj ↦ by simp [hA r hr, hrj],
      Finset.sum_eq_single_of_mem j hjW fun r hr hrj ↦ by simp [hcol r hr hrj], hjj',
      hA j hjW] at h
    simpa using h
  have hW' : rowGram (W.erase j) (1 - B) = rowGram (W.erase j) (1 - B') := by
    funext a b
    have h := congrFun (congrFun hW a) b
    simp only [rowGram] at h ⊢
    rw [← Finset.add_sum_erase _ _ hjW, ← Finset.add_sum_erase _ _ hjW, hrow] at h
    exact add_left_cancel h
  intro r hr
  by_cases hrj : r = j
  · rw [hrj]; exact hrow
  · exact ih _ (Finset.erase_ssubset hjW) hW' r (Finset.mem_erase.2 ⟨hrj, hr⟩)

/-- For a linear SEM matrix `B` along a causal graph, `1 - B` is nonsingular. -/
theorem CausalGraph.IsLinearSEMMatrix.det_one_sub_ne_zero [Fintype V] [DecidableEq V]
    {G : CausalGraph V} {B : Matrix V V ℝ} (hB : G.IsLinearSEMMatrix B) : (1 - B).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have : IsTrans V (Relation.TransGen G.edge) := ⟨fun _ _ _ ↦ Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen G.edge) := ⟨fun a ↦ G.acyclic a⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen G.edge)
  refine hx0 (funext fun j ↦ wf.induction (C := fun j ↦ x j = 0) j fun j ih ↦ ?_)
  have hj := congrFun hx j
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hj
  rw [hj, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : B j k = 0
  · simp [hk]
  · simp [ih k (Relation.TransGen.single ((hB j k).1 hk))]

/-- Variance of a linear functional of a linear Gaussian SEM with common noise variance:
`Var(∑ₐ cₐ Xₐ) = σ² ∑ₖ (∑ₐ cₐ Mₐₖ)²` for `X = M N`. -/
theorem variance_linearSEMLaw_gaussianReal [Fintype V] [DecidableEq V] (B : Matrix V V ℝ)
    (m : V → ℝ) (σ2 : ℝ≥0) (c : V → ℝ) :
    Var[fun x ↦ ∑ a, c a * x a; linearSEMLaw B fun j ↦ gaussianReal (m j) σ2] =
      σ2 * ∑ k, (∑ a, c a * (1 - B)⁻¹ a k) ^ 2 := by
  have hc : Measurable fun x : V → ℝ ↦ ∑ a, c a * x a :=
    Finset.measurable_sum _ fun a _ ↦ measurable_const.mul (measurable_pi_apply a)
  have hM : Measurable fun n : V → ℝ ↦ ((1 - B)⁻¹).mulVec n := by fun_prop
  unfold linearSEMLaw
  rw [variance_map hc.aemeasurable hM.aemeasurable]
  let w : V → ℝ := fun k ↦ ∑ a, c a * (1 - B)⁻¹ a k
  have hfun : (fun x : V → ℝ ↦ ∑ a, c a * x a) ∘ (fun n ↦ ((1 - B)⁻¹).mulVec n) =
      ∑ k, fun n : V → ℝ ↦ (fun t : ℝ ↦ w k * t) (n k) := by
    funext n
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum,
      Finset.sum_mul, w]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
  rw [hfun, variance_sum_pi (X := fun k t ↦ w k * t)
    fun k ↦ (memLp_id_gaussianReal 2).const_mul (w k)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [show (fun t : ℝ ↦ w k * t) = fun t ↦ w k * id t from rfl,
    variance_const_mul, variance_id_gaussianReal]
  ring

/-- Polarization for the quadratic form `c ↦ ∑ₖ (∑ₐ cₐ Mₐₖ)²` of `M Mᵀ`. -/
private theorem polarization_mul_transpose [Fintype V] [DecidableEq V] (M : Matrix V V ℝ)
    (a b : V) :
    (∑ k, (∑ x, (Pi.single a 1 + Pi.single b 1 : V → ℝ) x * M x k) ^ 2) -
      (∑ k, (∑ x, (Pi.single a 1 : V → ℝ) x * M x k) ^ 2) -
      (∑ k, (∑ x, (Pi.single b 1 : V → ℝ) x * M x k) ^ 2) = 2 * (M * Mᵀ) a b := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The diagonal of the Gram matrix of `1 - B` over all rows is at least one. -/
private theorem one_le_rowGram_univ [Fintype V] [DecidableEq V] {G : CausalGraph V}
    {B : Matrix V V ℝ} (hB : G.IsLinearSEMMatrix B) (j : V) :
    1 ≤ rowGram Finset.univ (1 - B) j j := by
  simp only [rowGram]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have : (1 - B) j j = 1 := by simp [Matrix.sub_apply, hB.apply_self j]
  rw [this, one_mul]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)

/-- At a sink of `G`, the diagonal of the Gram matrix of `1 - B` equals one. -/
private theorem rowGram_univ_sink [Fintype V] [DecidableEq V] {G : CausalGraph V}
    {B : Matrix V V ℝ} (hB : G.IsLinearSEMMatrix B) {j : V} (hj : ∀ k ∈ Finset.univ, ¬ G.edge j k) :
    rowGram Finset.univ (1 - B) j j = 1 := by
  simp only [rowGram]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun r hr hrj ↦ by
    simp [one_sub_apply_sink hB hj hr, hrj]]
  simp [one_sub_apply_sink hB hj (Finset.mem_univ j)]

/-- From equal covariances `σ² M Mᵀ = σ'² M' M'ᵀ` with `M = A⁻¹`, `M' = A'⁻¹`, the precisions
satisfy `σ'² AᵀA = σ² A'ᵀA'`. -/
private theorem smul_transpose_mul_eq [Fintype V] [DecidableEq V] {A A' : Matrix V V ℝ}
    (hA : A.det ≠ 0) (hA' : A'.det ≠ 0) {s s' : ℝ}
    (h : s • (A⁻¹ * A⁻¹ᵀ) = s' • (A'⁻¹ * A'⁻¹ᵀ)) : s' • (Aᵀ * A) = s • (A'ᵀ * A') := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hu' : IsUnit A'.det := isUnit_iff_ne_zero.2 hA'
  have h1 : Aᵀ * A * (A⁻¹ * A⁻¹ᵀ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
      ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one]
  have h2 : A'⁻¹ * A'⁻¹ᵀ * (A'ᵀ * A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A'⁻¹ᵀ, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ hu', Matrix.transpose_one, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hu']
  calc s' • (Aᵀ * A) = Aᵀ * A * (s' • (A'⁻¹ * A'⁻¹ᵀ)) * (A'ᵀ * A') := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = Aᵀ * A * (s • (A⁻¹ * A⁻¹ᵀ)) * (A'ᵀ * A') := by rw [h]
    _ = s • (A'ᵀ * A') := by
        rw [Matrix.mul_smul, h1, Matrix.smul_mul, Matrix.one_mul]

/-- GAPS 105.71, linear Gaussian models with equal noise variances: if two linear structural
equation models along `G` and `H`, with nonzero coefficients on the edges and independent
Gaussian noises of one common positive variance within each model, have the same law, then
`G = H`. The noise means are arbitrary. -/
theorem CausalGraph.edge_eq_of_linearSEMLaw_eq_of_equalVariance [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B B' : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B)
    (hB' : H.IsLinearSEMMatrix B') (m m' : V → ℝ) (σ2 σ2' : ℝ≥0) (hσ : 0 < σ2) (hσ' : 0 < σ2')
    (hlaw : linearSEMLaw B (fun j ↦ gaussianReal (m j) σ2) =
      linearSEMLaw B' (fun j ↦ gaussianReal (m' j) σ2')) :
    G.edge = H.edge := by
  have hvar : ∀ c : V → ℝ, (σ2 : ℝ) * ∑ k, (∑ a, c a * (1 - B)⁻¹ a k) ^ 2 =
      σ2' * ∑ k, (∑ a, c a * (1 - B')⁻¹ a k) ^ 2 := fun c ↦ by
    rw [← variance_linearSEMLaw_gaussianReal, ← variance_linearSEMLaw_gaussianReal, hlaw]
  have hcov : (σ2 : ℝ) • ((1 - B)⁻¹ * (1 - B)⁻¹ᵀ) = (σ2' : ℝ) • ((1 - B')⁻¹ * (1 - B')⁻¹ᵀ) := by
    funext a b
    have h := polarization_mul_transpose (1 - B)⁻¹ a b
    have h' := polarization_mul_transpose (1 - B')⁻¹ a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e1 := hvar (Pi.single a 1 + Pi.single b 1)
    have e2 := hvar (Pi.single a 1)
    have e3 := hvar (Pi.single b 1)
    nlinarith
  have hprec := smul_transpose_mul_eq hB.det_one_sub_ne_zero hB'.det_one_sub_ne_zero hcov
  have hgram : ∀ C : Matrix V V ℝ, rowGram Finset.univ C = Cᵀ * C := fun C ↦ by
    funext a b
    simp [rowGram, Matrix.mul_apply]
  rw [← hgram, ← hgram] at hprec
  -- the two variances agree
  have hentry : ∀ j, (σ2' : ℝ) * rowGram Finset.univ (1 - B) j j =
      σ2 * rowGram Finset.univ (1 - B') j j := fun j ↦ by
    simpa using congrFun (congrFun hprec j) j
  rcases isEmpty_or_nonempty V with hV | hV
  · funext k
    exact isEmptyElim k
  obtain ⟨j, -, hj⟩ := G.exists_sink_mem (Finset.univ_nonempty (α := V))
  obtain ⟨j', -, hj'⟩ := H.exists_sink_mem (Finset.univ_nonempty (α := V))
  have e1 := hentry j
  have e2 := hentry j'
  rw [rowGram_univ_sink hB hj] at e1
  rw [rowGram_univ_sink hB' hj'] at e2
  have g1 := one_le_rowGram_univ hB' j
  have g2 := one_le_rowGram_univ hB j'
  have hσ0 : (0 : ℝ) < σ2 := hσ
  have hσ0' : (0 : ℝ) < σ2' := hσ'
  have hs : (σ2' : ℝ) = σ2 := by nlinarith
  rw [hs] at hprec
  have hG := smul_right_injective (Matrix V V ℝ) hσ0.ne' hprec
  have hrows := rows_eq_of_rowGram_eq hB hB' Finset.univ hG
  have hBB : B = B' := sub_right_injective (funext fun r ↦ hrows r (Finset.mem_univ r))
  subst hBB
  funext k j
  exact propext ((hB j k).symm.trans (hB' j k))

/-- GAPS 105.71, nonlinear additive Gaussian-noise models: if two additive-noise models along
`G` and `H`, with three times continuously differentiable structural functions that respect
the parents and are nonlinear in each parent argument, and independent Gaussian noises of
positive variances, have the same law, then `G = H`. -/
theorem CausalGraph.edge_eq_of_additiveNoiseLaw_eq [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (f g : V → (V → ℝ) → ℝ)
    (hfG : G.RespectsParentsReal f) (hgH : H.RespectsParentsReal g)
    (hf : ∀ j, ContDiff ℝ 3 (f j)) (hg : ∀ j, ContDiff ℝ 3 (g j))
    (hfn : G.IsNonlinearInParents f) (hgn : H.IsNonlinearInParents g)
    (m m' : V → ℝ) (σ2 σ2' : V → ℝ≥0) (hσ : ∀ j, 0 < σ2 j) (hσ' : ∀ j, 0 < σ2' j)
    (μ : Measure (V → ℝ))
    (hμ : IsAdditiveNoiseLaw f (fun j ↦ gaussianReal (m j) (σ2 j)) μ)
    (hμ' : IsAdditiveNoiseLaw g (fun j ↦ gaussianReal (m' j) (σ2' j)) μ) :
    G.edge = H.edge := by
  sorry

/-- GAPS 105.71, linear Gaussian models with unrestricted variances identify only the Markov
equivalence class: for a linear Gaussian model along `G` whose law is faithful to `G`, a
directed acyclic graph `H` carries a linear Gaussian model (nonzero edge coefficients,
positive noise variances) with the same law faithful to `H` exactly when `H` is Markov
equivalent to `G`. Faithfulness to both graphs makes the equivalence class the precise answer. -/
theorem CausalGraph.exists_linearGaussianSEM_iff_markovEquivalent [Fintype V] [DecidableEq V]
    (G H : CausalGraph V) (B : Matrix V V ℝ) (hB : G.IsLinearSEMMatrix B) (m : V → ℝ)
    (σ2 : V → ℝ≥0) (hσ : ∀ j, 0 < σ2 j)
    (hfaith : G.IsFaithfulLaw (linearSEMLaw B fun j ↦ gaussianReal (m j) (σ2 j))) :
    (∃ (B' : Matrix V V ℝ) (m' : V → ℝ) (σ2' : V → ℝ≥0), H.IsLinearSEMMatrix B' ∧
        (∀ j, 0 < σ2' j) ∧
        H.IsFaithfulLaw (linearSEMLaw B' fun j ↦ gaussianReal (m' j) (σ2' j)) ∧
        linearSEMLaw B' (fun j ↦ gaussianReal (m' j) (σ2' j)) =
          linearSEMLaw B fun j ↦ gaussianReal (m j) (σ2 j)) ↔
      H.MarkovEquivalent G := by
  sorry

end CKSD
