module

public import CKSD.LinearModels.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.CompProdEqIff
import TauCeti.Probability.Distributions.Gaussian.Independence


/-!
# Gaussian graphical concentration models

For an undirected graph `G` on a finite index type `ι` (Mathlib's `SimpleGraph`), the Gaussian
concentration model consists of the nondegenerate Gaussian laws whose concentration (precision)
matrix `Σ⁻¹` vanishes off the edges of `G`.

## Main definitions

* `CKSD.concentrationModel`: the positive definite matrices with zero entries off the edges.
* `CKSD.HasGaussianPairwiseMarkovProperty`: nonadjacent coordinates of `N(m, Σ)` are
  conditionally independent given all the other coordinates.
* `CKSD.gaussianConcentrationLogLikelihood`: the Gaussian log likelihood of a concentration
  matrix, up to an additive constant and a positive factor.
* `CKSD.IsConcentrationMLE`: a concentration matrix of the model that is the unique maximizer of
  the likelihood over the model.

## Main results

* `CKSD.cond_indep_fun_multivariate_gaussian_iff_inv_apply_eq_zero`: for positive definite `Σ`,
  coordinates `i ≠ j` of `N(m, Σ)` are conditionally independent given the other coordinates
  exactly when `(Σ⁻¹)ᵢⱼ = 0`.
* `CKSD.has_gaussian_pairwise_markov_property_iff_inv_mem_concentration_model`: the pairwise Markov
  property relative to `G` holds exactly when `Σ⁻¹` lies in the concentration model of `G`.
* `CKSD.cond_indep_fun_iff_indep_fun_of_eq_add`: conditional independence given `Y` of two variables
  that differ from functions of `Y` by a residual pair independent of `Y` is independence of the
  residuals.

The Gaussian result regresses `(xᵢ, xⱼ)` on the other coordinates with the precision-matrix
residual `K_{AA}⁻¹ K_{A·} x`, `A = {i, j}`, which is independent of the other coordinates and has
covariance `K_{AA}⁻¹`. The independence criterion for linear images of a Gaussian vector is
`TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff`.

The Hammersley–Clifford theorem and the intersection property for general positive densities
are not stated. Source: GAPS 105.26, Gaussian precision-matrix part.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Matrix
open scoped NNReal ENNReal Topology

namespace CKSD

/-- Conditional independence through a conditional law: if the conditional distribution of
`(f, g)` given `k` is a.e. the Markov kernel `κ`, then `f` and `g` are conditionally independent
given `k` exactly when `κ` is a.e. the product of its two marginal kernels. -/
theorem cond_indep_fun_iff_ae_eq_prod_of_cond_distrib_ae_eq
    {Ω γ β β' : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {mγ : MeasurableSpace γ} {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace β'] [Nonempty β']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → β} {g : Ω → β'} {k : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k)
    (κ : Kernel γ (β × β')) [IsMarkovKernel κ]
    (hκ : condDistrib (fun ω ↦ (f ω, g ω)) k μ =ᵐ[μ.map k] κ) :
    f ⟂ᵢ[k, hk; μ] g ↔ κ =ᵐ[μ.map k] (κ.map Prod.fst ×ₖ κ.map Prod.snd) := by
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hf hg hk]
  have hL : μ.map (fun ω ↦ (k ω, f ω, g ω)) = μ.map k ⊗ₘ κ := by
    rw [← Measure.compProd_congr hκ, compProd_map_condDistrib hk.aemeasurable (by fun_prop)]
  have hf' : condDistrib f k μ =ᵐ[μ.map k] κ.map Prod.fst := by
    have h1 := condDistrib_comp (μ := μ) hk.aemeasurable (hf.prodMk hg).aemeasurable
      measurable_fst
    filter_upwards [h1, hκ] with y h1 h2
    rw [Kernel.map_apply _ measurable_fst, ← h2, ← Kernel.map_apply _ measurable_fst, ← h1]
    rfl
  have hg' : condDistrib g k μ =ᵐ[μ.map k] κ.map Prod.snd := by
    have h1 := condDistrib_comp (μ := μ) hk.aemeasurable (hf.prodMk hg).aemeasurable
      measurable_snd
    filter_upwards [h1, hκ] with y h1 h2
    rw [Kernel.map_apply _ measurable_snd, ← h2, ← Kernel.map_apply _ measurable_snd, ← h1]
    rfl
  have hR : (Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k =
      μ.map k ⊗ₘ (κ.map Prod.fst ×ₖ κ.map Prod.snd) := by
    rw [← Measure.compProd_eq_comp_prod]
    apply Measure.compProd_congr
    filter_upwards [hf', hg'] with y h1 h2
    rw [Kernel.prod_apply, Kernel.prod_apply, h1, h2]
  rw [hL, hR, Kernel.compProd_eq_iff]

/-- Conditional independence given `Y` of `f = R₁ + a₁ ∘ Y` and `g = R₂ + a₂ ∘ Y`, where the
residual pair `(R₁, R₂)` is independent of `Y`, is equivalent to independence of `R₁` and `R₂`. -/
theorem cond_indep_fun_iff_indep_fun_of_eq_add
    {Ω γ : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {mγ : MeasurableSpace γ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → γ} {f g R₁ R₂ : Ω → ℝ}
    {a₁ a₂ : γ → ℝ} (hY : Measurable Y) (hR₁ : Measurable R₁) (hR₂ : Measurable R₂)
    (ha₁ : Measurable a₁) (ha₂ : Measurable a₂)
    (hf : ∀ ω, f ω = R₁ ω + a₁ (Y ω)) (hg : ∀ ω, g ω = R₂ ω + a₂ (Y ω))
    (hind : IndepFun Y (fun ω ↦ (R₁ ω, R₂ ω)) μ) :
    f ⟂ᵢ[Y, hY; μ] g ↔ IndepFun R₁ R₂ μ := by
  have hf' : f = fun ω ↦ R₁ ω + a₁ (Y ω) := funext hf
  have hg' : g = fun ω ↦ R₂ ω + a₂ (Y ω) := funext hg
  subst hf' hg'
  set ν : Measure (ℝ × ℝ) := μ.map (fun ω ↦ (R₁ ω, R₂ ω)) with hν
  have hR : Measurable fun ω ↦ (R₁ ω, R₂ ω) := hR₁.prodMk hR₂
  let T : γ × (ℝ × ℝ) → ℝ × ℝ := fun p ↦ (p.2.1 + a₁ p.1, p.2.2 + a₂ p.1)
  have hT : Measurable T := by fun_prop
  let κ : Kernel γ (ℝ × ℝ) := (Kernel.id ×ₖ Kernel.const γ ν).map T
  have hκ_apply (y : γ) : κ y = ν.map (fun r ↦ (r.1 + a₁ y, r.2 + a₂ y)) := by
    simp only [κ, Kernel.map_apply _ hT, Kernel.prod_apply, Kernel.id_apply,
      Kernel.const_apply, Measure.dirac_prod]
    rw [Measure.map_map hT measurable_prodMk_left]
    rfl
  have hcond : condDistrib (fun ω ↦ (R₁ ω + a₁ (Y ω), R₂ ω + a₂ (Y ω))) Y μ =ᵐ[μ.map Y] κ := by
    refine condDistrib_ae_eq_of_measure_eq_compProd hY.aemeasurable (by fun_prop) ?_
    ext s hs
    rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs]
    have hprod : μ.map (fun ω ↦ (Y ω, R₁ ω, R₂ ω)) = (μ.map Y).prod ν :=
      (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable).1 hind
    have hS : MeasurableSet ((fun p : γ × (ℝ × ℝ) ↦ (p.1, T p)) ⁻¹' s) :=
      (measurable_fst.prodMk hT) hs
    have h1 : μ ((fun ω ↦ (Y ω, R₁ ω + a₁ (Y ω), R₂ ω + a₂ (Y ω))) ⁻¹' s) =
        (μ.map (fun ω ↦ (Y ω, R₁ ω, R₂ ω))) ((fun p : γ × (ℝ × ℝ) ↦ (p.1, T p)) ⁻¹' s) := by
      rw [Measure.map_apply (by fun_prop) hS]
      rfl
    rw [h1, hprod, Measure.prod_apply hS]
    refine lintegral_congr fun y ↦ ?_
    rw [hκ_apply, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
    rfl
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  have : IsMarkovKernel κ := Kernel.IsMarkovKernel.map _ hT
  rw [cond_indep_fun_iff_ae_eq_prod_of_cond_distrib_ae_eq (by fun_prop) (by fun_prop) hY κ hcond]
  have hind' : IndepFun R₁ R₂ μ ↔ ν = (ν.map Prod.fst).prod (ν.map Prod.snd) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hR₁.aemeasurable hR₂.aemeasurable, hν,
      Measure.map_map measurable_fst hR, Measure.map_map measurable_snd hR]
    rfl
  clear_value ν
  have hpt (y : γ) : (κ.map Prod.fst ×ₖ κ.map Prod.snd) y =
      ((ν.map Prod.fst).prod (ν.map Prod.snd)).map (Prod.map (· + a₁ y) (· + a₂ y)) := by
    rw [Kernel.prod_apply, Kernel.map_apply _ measurable_fst, Kernel.map_apply _ measurable_snd,
      hκ_apply, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    congr 1 <;> rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] <;> rfl
  have heq (y : γ) : κ y = (κ.map Prod.fst ×ₖ κ.map Prod.snd) y ↔
      ν = (ν.map Prod.fst).prod (ν.map Prod.snd) := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      (MeasurableEquiv.addRight (a₁ y)).prodCongr (MeasurableEquiv.addRight (a₂ y))
    rw [hpt, hκ_apply]
    exact e.map_measurableEquiv_injective.eq_iff
  rw [hind', Filter.EventuallyEq]
  simp_rw [heq]
  exact Filter.eventually_const

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinates of `x` other than the `i`-th and the `j`-th. -/
def otherCoordinates (i j : ι) (x : EuclideanSpace ℝ ι) :
    {k : ι // k ≠ i ∧ k ≠ j} → ℝ := fun k ↦ x k.val

omit [Fintype ι] [DecidableEq ι] in
/-- The map to the coordinates other than `i` and `j` is measurable. -/
@[fun_prop] theorem measurable_other_coordinates (i j : ι) :
    Measurable (otherCoordinates i j) := by
  unfold otherCoordinates
  fun_prop

/-- The concentration matrices of the Gaussian graphical model of `G`: positive definite
matrices with zero entries off the edges of `G`. -/
def concentrationModel (G : SimpleGraph ι) : Set (Matrix ι ι ℝ) :=
  {K | K.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → K i j = 0}

/-- The Gaussian pairwise Markov property of `N(m, Σ)` relative to an undirected graph: for
nonadjacent `i ≠ j`, the coordinates `xᵢ` and `xⱼ` are conditionally independent given the
remaining coordinates. -/
def HasGaussianPairwiseMarkovProperty (G : SimpleGraph ι) (m : EuclideanSpace ℝ ι)
    (Sigma : Matrix ι ι ℝ) : Prop :=
  ∀ i j, i ≠ j → ¬ G.Adj i j →
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : ι // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_other_coordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma)

/-- Splitting a sum over `ι` into the terms at `i`, at `j`, and at the remaining indices. -/
private theorem sum_eq_add_add_sum_other_coords {i j : ι} (hij : i ≠ j) (h : ι → ℝ) :
    ∑ k, h k = h i + h j + ∑ b : {k : ι // k ≠ i ∧ k ≠ j}, h b := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]
  congr 2
  exact Finset.sum_subtype _ (fun k ↦ by simp [and_comm]) h

/-- For a positive definite `2 × 2` matrix `M`, the off-diagonal entry of `M⁻¹` vanishes exactly
when that of `M` does. -/
private theorem inv_apply_one_zero_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.PosDef) :
    M⁻¹ 1 0 = 0 ↔ M 1 0 = 0 := by
  have hu : IsUnit M.det := hM.det_pos.ne'.isUnit
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) 1) 0
  have h2 := congrFun (congrFun (Matrix.nonsing_inv_mul M hu) 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    at h1 h2
  have p1 : 0 < M⁻¹ 0 0 := hM.inv.diag_pos
  have p2 : 0 < M 0 0 := hM.diag_pos
  constructor
  · intro h
    rw [h, mul_zero, add_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right p1.ne'
  · intro h
    rw [h, mul_zero, add_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right p2.ne'

/-- Two linear functionals `x ↦ (W x)_r` and `x ↦ (W x)_s` of a Gaussian vector `N(m, Σ)` are
independent exactly when their covariance `(W Σ Wᵀ)_{rs}` vanishes. -/
private theorem indep_fun_mul_vec_apply_multivariate_gaussian_iff {κ : Type*} [Fintype κ]
    (m : EuclideanSpace ℝ ι) {Sigma : Matrix ι ι ℝ} (hS : Sigma.PosSemidef) (W : Matrix κ ι ℝ)
    (r s : κ) :
    IndepFun (fun x : EuclideanSpace ℝ ι ↦ (W *ᵥ WithLp.ofLp x) r)
        (fun x ↦ (W *ᵥ WithLp.ofLp x) s) (multivariateGaussian m Sigma) ↔
      (W * Sigma * Wᵀ) r s = 0 := by
  let A₀ : Matrix Unit ι ℝ := W.submatrix (fun _ ↦ r) id
  let A₁ : Matrix Unit ι ℝ := W.submatrix (fun _ ↦ s) id
  have hA : A₀ * Sigma * A₁ᵀ = 0 ↔ (W * Sigma * Wᵀ) r s = 0 := by
    have : A₀ * Sigma * A₁ᵀ = Matrix.of fun _ _ ↦ (W * Sigma * Wᵀ) r s := by
      ext u v
      simp [A₀, A₁, Matrix.mul_apply]
    rw [this]
    constructor
    · intro h
      simpa using congrFun (congrFun h ()) ()
    · intro h
      ext u v
      simp [h]
  rw [← hA, ← TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff m hS A₀ A₁]
  constructor
  · intro h
    have h' := h.comp (φ := fun t : ℝ ↦ (WithLp.toLp 2 fun _ : Unit ↦ t))
      (ψ := fun t : ℝ ↦ (WithLp.toLp 2 fun _ : Unit ↦ t)) (by fun_prop) (by fun_prop)
    convert h' using 1 <;>
    · funext x
      ext u
      simp [A₀, A₁, mulVec, dotProduct]
  · intro h
    have h' := h.comp (φ := fun z : EuclideanSpace ℝ Unit ↦ z ())
      (ψ := fun z : EuclideanSpace ℝ Unit ↦ z ()) (by fun_prop) (by fun_prop)
    convert h' using 1 <;>
    · funext x
      simp [A₀, A₁, mulVec, dotProduct]

/-- GAPS 105.26: for a positive definite covariance `Σ` and `i ≠ j`, the coordinates `xᵢ` and
`xⱼ` of `N(m, Σ)` are conditionally independent given the remaining coordinates exactly when the
`(i, j)` entry of the concentration matrix `Σ⁻¹` vanishes. -/
theorem cond_indep_fun_multivariate_gaussian_iff_inv_apply_eq_zero
    (m : EuclideanSpace ℝ ι) (Sigma : Matrix ι ι ℝ)
    (hSigma : Sigma.PosDef) (i j : ι) (hij : i ≠ j) :
    CondIndepFun ((inferInstance : MeasurableSpace
      ({k : ι // k ≠ i ∧ k ≠ j} → ℝ)).comap (otherCoordinates i j))
      (measurable_other_coordinates i j).comap_le (fun x ↦ x i) (fun x ↦ x j)
        (multivariateGaussian m Sigma) ↔ Sigma⁻¹ i j = 0 := by
  set K := Sigma⁻¹ with hK
  have hKpd : K.PosDef := hSigma.inv
  have hKS : K * Sigma = 1 := Matrix.nonsing_inv_mul _ hSigma.det_pos.ne'.isUnit
  let idx : Fin 2 → ι := ![i, j]
  let K₂ : Matrix (Fin 2) (Fin 2) ℝ := K.submatrix idx idx
  have hidx : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [idx, eq_comm]
  have hK₂ : K₂.PosDef := hKpd.submatrix hidx
  let W : Matrix (Fin 2) ι ℝ := K₂⁻¹ * K.submatrix idx id
  let KAB : Matrix (Fin 2) {k : ι // k ≠ i ∧ k ≠ j} ℝ := K.submatrix idx Subtype.val
  let a : ({k : ι // k ≠ i ∧ k ≠ j} → ℝ) → Fin 2 → ℝ := fun y ↦ -(K₂⁻¹ *ᵥ (KAB *ᵥ y))
  let R : EuclideanSpace ℝ ι → Fin 2 → ℝ := fun x ↦ W *ᵥ WithLp.ofLp x
  have hu₂ : IsUnit K₂.det := hK₂.det_pos.ne'.isUnit
  have hsplit (x : ι → ℝ) : K.submatrix idx id *ᵥ x =
      K₂ *ᵥ (fun r ↦ x (idx r)) + KAB *ᵥ (fun b ↦ x b) := by
    ext r
    simp only [mulVec, dotProduct, Pi.add_apply, submatrix_apply, id]
    rw [sum_eq_add_add_sum_other_coords hij, Fin.sum_univ_two]
    fin_cases r <;> simp [idx, KAB, K₂]
  have hR (x : EuclideanSpace ℝ ι) :
      R x = (fun r ↦ x (idx r)) + K₂⁻¹ *ᵥ (KAB *ᵥ otherCoordinates i j x) := by
    simp only [R, W, ← mulVec_mulVec, hsplit, mulVec_add]
    rw [mulVec_mulVec, nonsing_inv_mul _ hu₂, one_mulVec]
    rfl
  have hdecomp (x : EuclideanSpace ℝ ι) (r : Fin 2) :
      x (idx r) = R x r + a (otherCoordinates i j x) r := by
    rw [hR]
    simp [a]
  have hS : Sigma.PosSemidef := hSigma.posSemidef
  have hKt : Kᵀ = K := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hKpd.isHermitian.eq
  have hKsymm (a b : ι) : K a b = K b a := by
    rw [← transpose_apply K a b, hKt]
  have hSKt : Sigma * Kᵀ = 1 := by
    rw [hKt]
    exact mul_nonsing_inv _ hSigma.det_pos.ne'.isUnit
  have hSW : Sigma * (K.submatrix idx id)ᵀ = (1 : Matrix ι ι ℝ).submatrix id idx := by
    ext k r
    have := congrFun (congrFun hSKt k) (idx r)
    simp only [Matrix.mul_apply, transpose_apply, submatrix_apply, id] at this ⊢
    exact this
  let P : Matrix {k : ι // k ≠ i ∧ k ≠ j} ι ℝ := (1 : Matrix ι ι ℝ).submatrix Subtype.val id
  have hcross : P * Sigma * Wᵀ = 0 := by
    have h0 : P * (1 : Matrix ι ι ℝ).submatrix id idx = 0 := by
      ext b r
      have hb : b.val ≠ idx r := by
        fin_cases r
        · exact b.2.1
        · exact b.2.2
      simp only [P, Matrix.mul_apply, submatrix_apply, id, Matrix.one_apply]
      simp [hb]
    simp only [W, transpose_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc P, hSW, h0, Matrix.zero_mul]
  have hind : IndepFun (otherCoordinates i j) (fun x ↦ (R x 0, R x 1))
      (multivariateGaussian m Sigma) := by
    have h := (TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff m hS P W).2 hcross
    have h' := h.comp (φ := fun z : EuclideanSpace ℝ {k : ι // k ≠ i ∧ k ≠ j} ↦ fun b ↦ z b)
      (ψ := fun z : EuclideanSpace ℝ (Fin 2) ↦ (z 0, z 1)) (by fun_prop) (by fun_prop)
    convert h' using 1
    · funext x
      ext b
      simp [P, otherCoordinates, mulVec, dotProduct, Matrix.one_apply, id]
    · funext x
      simp [R]
  have hWSW : W * Sigma * Wᵀ = (K₂⁻¹)ᵀ := by
    have h1 : K.submatrix idx id * (1 : Matrix ι ι ℝ).submatrix id idx = K₂ := by
      ext r s
      simp [K₂, Matrix.mul_apply, Matrix.one_apply]
    simp only [W, transpose_mul]
    rw [show K₂⁻¹ * K.submatrix idx id * Sigma * ((K.submatrix idx id)ᵀ * K₂⁻¹ᵀ) =
      K₂⁻¹ * (K.submatrix idx id * (Sigma * (K.submatrix idx id)ᵀ)) * K₂⁻¹ᵀ by
        simp only [Matrix.mul_assoc]]
    rw [hSW, h1, nonsing_inv_mul _ hu₂, Matrix.one_mul]
  have hpair : IndepFun (fun x ↦ R x 0) (fun x ↦ R x 1) (multivariateGaussian m Sigma) ↔
      (W * Sigma * Wᵀ) 0 1 = 0 :=
    indep_fun_mul_vec_apply_multivariate_gaussian_iff m hS W 0 1
  rw [cond_indep_fun_iff_indep_fun_of_eq_add (f := fun x ↦ x i) (g := fun x ↦ x j)
    (R₁ := fun x ↦ R x 0) (R₂ := fun x ↦ R x 1)
    (a₁ := fun y ↦ a y 0) (a₂ := fun y ↦ a y 1) (measurable_other_coordinates i j)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (fun x ↦ hdecomp x 0)
    (fun x ↦ hdecomp x 1) hind, hpair, hWSW, transpose_apply,
    inv_apply_one_zero_eq_zero_iff hK₂]
  simp [K₂, idx, hKsymm j i]

/-- GAPS 105.26: for a positive definite covariance `Σ`, the law `N(m, Σ)` has the pairwise
Markov property relative to `G` exactly when its concentration matrix `Σ⁻¹` lies in the
concentration model of `G`. -/
theorem has_gaussian_pairwise_markov_property_iff_inv_mem_concentration_model (G : SimpleGraph ι)
    (m : EuclideanSpace ℝ ι) {Sigma : Matrix ι ι ℝ} (hSigma : Sigma.PosDef) :
    HasGaussianPairwiseMarkovProperty G m Sigma ↔ Sigma⁻¹ ∈ concentrationModel G :=
  ⟨fun h ↦ ⟨hSigma.inv, fun i j hij hG ↦
      (cond_indep_fun_multivariate_gaussian_iff_inv_apply_eq_zero m Sigma hSigma i j hij).1
        (h i j hij hG)⟩,
    fun h i j hij hG ↦
      (cond_indep_fun_multivariate_gaussian_iff_inv_apply_eq_zero m Sigma hSigma i j hij).2
        (h.2 i j hij hG)⟩

/-- The Gaussian log likelihood of a concentration matrix `K` for `n` observations with centred
sum-of-squares matrix `ssd`, up to an additive constant and the factor `n / 2`:
`log det K - tr(K ssd) / n`. -/
def gaussianConcentrationLogLikelihood (n : ℕ) (ssd K : Matrix ι ι ℝ) : ℝ :=
  Real.log K.det - Matrix.trace (K * ssd) / n

/-- `K` is the maximum likelihood estimate of the concentration matrix in the Gaussian graphical
model of `G`: it lies in the concentration model and has strictly larger likelihood than every
other concentration matrix of the model. -/
def IsConcentrationMLE (G : SimpleGraph ι) (n : ℕ) (ssd K : Matrix ι ι ℝ) : Prop :=
  K ∈ concentrationModel G ∧ ∀ K' ∈ concentrationModel G, K' ≠ K →
    gaussianConcentrationLogLikelihood n ssd K' < gaussianConcentrationLogLikelihood n ssd K

end CKSD
