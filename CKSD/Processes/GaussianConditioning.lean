module

public import CKSD.Processes.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Gaussian.Sum
public import TauCeti.Probability.Distributions.Gaussian.Independence
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Gaussian independence and conditional laws

Independence bookkeeping for finite prefixes, linear Gaussian image laws, Gaussian shift
kernels and conditional distributions, and density transport under measurable equivalences.
Gaussian laws, densities, affine maps and independence criteria are reused from pinned TauCeti.
These probability tools support the Kalman filter but do not depend on its model.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace CKSD

section Generic

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {P : Measure Ω}

/-- If `X` is independent of `Y` and the pair `(X, Y)` is independent of `Z`, then `X` is
independent of the pair `(Y, Z)`. -/
theorem indepFun_prodMk_of_indepFun_of_indepFun_prodMk [IsProbabilityMeasure P]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hZ : AEMeasurable Z P) (hXY : IndepFun X Y P)
    (hXYZ : IndepFun (fun ω ↦ (X ω, Y ω)) Z P) :
    IndepFun X (fun ω ↦ (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P :=
    hXYZ.comp (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
  rw [indepFun_iff_map_prod_eq_prod_map_map hX (hY.prodMk hZ)]
  rw [indepFun_iff_map_prod_eq_prod_map_map hY hZ] at hYZ
  rw [indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY) hZ] at hXYZ
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY] at hXY
  rw [hYZ]
  have hcomp : (fun ω ↦ (X ω, (Y ω, Z ω))) =
      MeasurableEquiv.prodAssoc ∘ (fun ω ↦ ((X ω, Y ω), Z ω)) := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    MeasurableEquiv.prodAssoc.measurable.aemeasurable ((hX.prodMk hY).prodMk hZ), hXYZ, hXY]
  exact (measurePreserving_prodAssoc _ _ _).map_eq

/-- A sequence of random variables is mutually independent when each term is independent of
the vector of its predecessors. -/
theorem iIndepFun_of_indepFun_finPrefix [IsProbabilityMeasure P] {e : ℕ → Ω → β}
    (h : ∀ n, IndepFun (fun ω (i : Fin n) ↦ e i ω) (e n) P) : iIndepFun e P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  suffices H : ∀ N, ∀ S : Finset ℕ, (∀ i ∈ S, i < N) → (∀ i ∈ S, MeasurableSet (sets i)) →
      P (⋂ i ∈ S, e i ⁻¹' sets i) = ∏ i ∈ S, P (e i ⁻¹' sets i) by
    obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ S, i < N :=
      ⟨S.sup id + 1, fun i hi ↦ Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
    exact H N S hN hsets
  intro N
  induction N with
  | zero =>
    intro S hS _
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun i hi ↦ Nat.not_lt_zero _ (hS i hi)
    subst this
    simp
  | succ N ih =>
    intro S hS hmeas
    by_cases hN : N ∈ S
    · set S' := S.erase N with hS'
      have hS'lt : ∀ i ∈ S', i < N := fun i hi ↦ by
        have := hS i (Finset.mem_of_mem_erase hi)
        have := Finset.ne_of_mem_erase hi
        omega
      have hinsert : S = insert N S' := (Finset.insert_erase hN).symm
      let B : Set (Fin N → β) := ⋂ (i : Fin N) (_ : (i : ℕ) ∈ S'), (fun f ↦ f i) ⁻¹' sets i
      have hB : MeasurableSet B := by
        refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun hi ↦ ?_
        exact measurable_pi_apply i (hmeas i (Finset.mem_of_mem_erase hi))
      have hpre : (fun ω (i : Fin N) ↦ e i ω) ⁻¹' B = ⋂ i ∈ S', e i ⁻¹' sets i := by
        ext ω
        simp only [B, Set.mem_preimage, Set.mem_iInter]
        constructor
        · intro hω i hi
          exact hω ⟨i, hS'lt i hi⟩ hi
        · intro hω i hi
          exact hω i hi
      rw [hinsert, Finset.set_biInter_insert, Finset.prod_insert (Finset.notMem_erase N S),
        ← hpre, Set.inter_comm,
        (h N).measure_inter_preimage_eq_mul _ _ hB (hmeas N hN), hpre,
        ih S' hS'lt fun i hi ↦ hmeas i (Finset.mem_of_mem_erase hi), mul_comm]
    · exact ih S (fun i hi ↦ by
        have := hS i hi
        have : i ≠ N := fun h ↦ hN (h ▸ hi)
        omega) hmeas

/-- If `A` is independent of the pair `(B, C)` and `B` is independent of `C`, then the pair
`(A, B)` is independent of `C`. -/
theorem indepFun_prodMk_left_of_indepFun_prodMk [IsProbabilityMeasure P]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hZ : AEMeasurable Z P) (hXYZ : IndepFun X (fun ω ↦ (Y ω, Z ω)) P)
    (hYZ : IndepFun Y Z P) :
    IndepFun (fun ω ↦ (X ω, Y ω)) Z P := by
  have h₁ : IndepFun (fun ω ↦ (Z ω, Y ω)) X P :=
    (hXYZ.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm
  have h₂ := indepFun_prodMk_of_indepFun_of_indepFun_prodMk hZ hY hX hYZ.symm h₁
  exact (h₂.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm

/-- In a family consisting of an initial value `x₀`, a sequence `w`, and a mutually independent
sequence `v`, with `x₀` independent of `(w, v)` and `w` independent of `v`, the term `v t` is
independent of `x₀`, the whole sequence `w`, and the terms `v i` with `i < t`. -/
theorem indepFun_apply_prefix_of_indepFun {δ : Type*} [MeasurableSpace δ] [IsProbabilityMeasure P]
    {x₀ : Ω → α} {w : ℕ → Ω → β} {v : ℕ → Ω → δ} (hx₀ : AEMeasurable x₀ P)
    (hw : ∀ t, AEMeasurable (w t) P) (hv : ∀ t, AEMeasurable (v t) P)
    (hvind : iIndepFun v P) (hwv : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P)
    (hx₀wv : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P) (t : ℕ) :
    IndepFun (v t) (fun ω ↦ (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω)) P := by
  have hW : AEMeasurable (fun ω i ↦ w i ω) P := AEMeasurable.of_eval hw
  have hV : AEMeasurable (fun ω i ↦ v i ω) P := AEMeasurable.of_eval hv
  have h₁ : IndepFun x₀ (fun ω ↦ ((fun i ↦ w i ω), fun i ↦ v i ω)) P :=
    hx₀wv.comp (φ := id) (ψ := fun f : ℕ → β × δ ↦ ((fun i ↦ (f i).1), fun i ↦ (f i).2))
      measurable_id (by fun_prop)
  have h₂ := indepFun_prodMk_left_of_indepFun_prodMk hx₀ hW hV h₁ hwv
  have h₃ : IndepFun (v t) (fun ω (i : Fin t) ↦ v i ω) P := by
    have h := hvind.indepFun_finset₀ {t} (Finset.range t) (by simp) hv
    exact h.comp (φ := fun g : ((({t} : Finset ℕ) : Set ℕ) → δ) ↦
        g ⟨t, Finset.mem_singleton_self t⟩)
      (ψ := fun (g : ((Finset.range t : Finset ℕ) : Set ℕ) → δ) (i : Fin t) ↦
        g ⟨i, Finset.mem_range.2 i.2⟩)
      (measurable_pi_apply _) (measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _)
  have h₄ : IndepFun (fun ω ↦ (v t ω, fun i : Fin t ↦ v i ω))
      (fun ω ↦ (x₀ ω, fun i ↦ w i ω)) P :=
    h₂.symm.comp (φ := fun g : ℕ → δ ↦ (g t, fun i : Fin t ↦ g i)) (ψ := id)
      (by fun_prop) measurable_id
  have h₅ := indepFun_prodMk_of_indepFun_of_indepFun_prodMk (hv t)
    (AEMeasurable.of_eval fun i : Fin t ↦ hv i) (hx₀.prodMk hW) h₃ h₄
  exact h₅.comp (φ := id) (ψ := fun q ↦ (q.2.1, q.2.2, q.1)) measurable_id (by fun_prop)

/-- In the setting of `indepFun_apply_prefix_of_indepFun`, with `w` mutually independent, the
term `w t` is independent of `x₀`, the terms `w i` with `i < t`, and the whole sequence `v`. -/
theorem indepFun_apply_prefix_of_indepFun' {δ : Type*} [MeasurableSpace δ]
    [IsProbabilityMeasure P]
    {x₀ : Ω → α} {w : ℕ → Ω → β} {v : ℕ → Ω → δ} (hx₀ : AEMeasurable x₀ P)
    (hw : ∀ t, AEMeasurable (w t) P) (hv : ∀ t, AEMeasurable (v t) P)
    (hwind : iIndepFun w P) (hwv : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P)
    (hx₀wv : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P) (t : ℕ) :
    IndepFun (w t) (fun ω ↦ (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω)) P := by
  have hx₀vw : IndepFun x₀ (fun ω t ↦ (v t ω, w t ω)) P :=
    hx₀wv.comp (φ := id) (ψ := fun f : ℕ → β × δ ↦ fun i ↦ (f i).swap) measurable_id
      (by fun_prop)
  have h := indepFun_apply_prefix_of_indepFun hx₀ hv hw hwind hwv.symm hx₀vw t
  exact h.comp (φ := id) (ψ := fun q ↦ (q.1, q.2.2, q.2.1)) measurable_id (by fun_prop)

end Generic

section GaussianPair

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ι κ τ σ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype σ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ]

/-- A matrix image of a centered multivariate Gaussian vector is centered Gaussian with the
congruent covariance. -/
theorem hasLaw_toEuclideanLin_multivariateGaussian_zero {X : Ω → EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateGaussian 0 S) P) (A : Matrix τ ι ℝ) :
    HasLaw (fun ω ↦ A.toEuclideanLin (X ω))
      (multivariateGaussian 0 (A * S * A.transpose)) P := by
  have h := TauCeti.Probability.map_affine_multivariateGaussian 0 hS A 0
  simp only [map_zero, add_zero] at h
  exact HasLaw.comp (Y := fun x ↦ A.toEuclideanLin x) ⟨by fun_prop, h⟩ hX

/-- For independent centered Gaussian vectors `ε` and `v`, the combination `A₁ ε + A₂ v` is
centered Gaussian with covariance `A₁ S₁ A₁ᵀ + A₂ S₂ A₂ᵀ`. -/
theorem hasLaw_toEuclideanLin_add_of_indepFun {ε : Ω → EuclideanSpace ℝ ι}
    {v : Ω → EuclideanSpace ℝ κ} {S₁ : Matrix ι ι ℝ} {S₂ : Matrix κ κ ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hε : HasLaw ε (multivariateGaussian 0 S₁) P) (hv : HasLaw v (multivariateGaussian 0 S₂) P)
    (hεv : IndepFun ε v P) (A₁ : Matrix τ ι ℝ) (A₂ : Matrix τ κ ℝ) :
    HasLaw (fun ω ↦ A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω))
      (multivariateGaussian 0 (A₁ * S₁ * A₁.transpose + A₂ * S₂ * A₂.transpose)) P := by
  have h₁ := hasLaw_toEuclideanLin_multivariateGaussian_zero hS₁ hε A₁
  have h₂ := hasLaw_toEuclideanLin_multivariateGaussian_zero hS₂ hv A₂
  have hind : IndepFun (fun ω ↦ A₁.toEuclideanLin (ε ω)) (fun ω ↦ A₂.toEuclideanLin (v ω)) P :=
    hεv.comp (φ := fun x ↦ A₁.toEuclideanLin x) (ψ := fun x ↦ A₂.toEuclideanLin x)
      (by fun_prop) (by fun_prop)
  have h := hind.hasLaw_fun_add h₁ h₂
  have hP₁ : (A₁ * S₁ * A₁.transpose).PosSemidef := by
    simpa using hS₁.mul_mul_conjTranspose_same A₁
  have hP₂ : (A₂ * S₂ * A₂.transpose).PosSemidef := by
    simpa using hS₂.mul_mul_conjTranspose_same A₂
  rw [TauCeti.Probability.multivariateGaussian_conv_multivariateGaussian _ _ hP₁ hP₂,
    add_zero] at h
  exact h

omit [DecidableEq τ] [DecidableEq σ] in
/-- Two linear combinations `A₁ ε + A₂ v` and `B₁ ε + B₂ v` of independent centered Gaussian
vectors are independent when their cross-covariance `A₁ S₁ B₁ᵀ + A₂ S₂ B₂ᵀ` vanishes. -/
theorem indepFun_toEuclideanLin_add_of_indepFun {ε : Ω → EuclideanSpace ℝ ι}
    {v : Ω → EuclideanSpace ℝ κ} {S₁ : Matrix ι ι ℝ} {S₂ : Matrix κ κ ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hε : HasLaw ε (multivariateGaussian 0 S₁) P) (hv : HasLaw v (multivariateGaussian 0 S₂) P)
    (hεv : IndepFun ε v P) (A₁ : Matrix τ ι ℝ) (A₂ : Matrix τ κ ℝ) (B₁ : Matrix σ ι ℝ)
    (B₂ : Matrix σ κ ℝ)
    (hcov : A₁ * S₁ * B₁.transpose + A₂ * S₂ * B₂.transpose = 0) :
    IndepFun (fun ω ↦ A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω))
      (fun ω ↦ B₁.toEuclideanLin (ε ω) + B₂.toEuclideanLin (v ω)) P := by
  let J₁ : Matrix (ι ⊕ κ) ι ℝ := Matrix.fromRows 1 0
  let J₂ : Matrix (ι ⊕ κ) κ ℝ := Matrix.fromRows 0 1
  have hU := hasLaw_toEuclideanLin_add_of_indepFun hS₁ hS₂ hε hv hεv J₁ J₂
  have hS : (J₁ * S₁ * J₁.transpose + J₂ * S₂ * J₂.transpose).PosSemidef := by
    have h₁ : (J₁ * S₁ * J₁.transpose).PosSemidef := by
      simpa using hS₁.mul_mul_conjTranspose_same J₁
    have h₂ : (J₂ * S₂ * J₂.transpose).PosSemidef := by
      simpa using hS₂.mul_mul_conjTranspose_same J₂
    exact h₁.add h₂
  have key := (TauCeti.Probability.indepFun_matrix_of_hasLaw_multivariateGaussian_iff hS hU
    (Matrix.fromCols A₁ A₂) (Matrix.fromCols B₁ B₂)).2 (by
      calc Matrix.fromCols A₁ A₂ * (J₁ * S₁ * J₁.transpose + J₂ * S₂ * J₂.transpose) *
            (Matrix.fromCols B₁ B₂).transpose
          = (Matrix.fromCols A₁ A₂ * J₁) * S₁ * (Matrix.fromCols B₁ B₂ * J₁).transpose +
            (Matrix.fromCols A₁ A₂ * J₂) * S₂ * (Matrix.fromCols B₁ B₂ * J₂).transpose := by
            simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by simpa [J₁, J₂, Matrix.fromCols_mul_fromRows] using hcov)
  have hA : ∀ ω, (Matrix.fromCols A₁ A₂).toEuclideanLin
      (J₁.toEuclideanLin (ε ω) + J₂.toEuclideanLin (v ω)) =
        A₁.toEuclideanLin (ε ω) + A₂.toEuclideanLin (v ω) := by
    intro ω
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    simp [J₁, J₂, Matrix.fromCols_mul_fromRows]
  have hB : ∀ ω, (Matrix.fromCols B₁ B₂).toEuclideanLin
      (J₁.toEuclideanLin (ε ω) + J₂.toEuclideanLin (v ω)) =
        B₁.toEuclideanLin (ε ω) + B₂.toEuclideanLin (v ω) := by
    intro ω
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    simp [J₁, J₂, Matrix.fromCols_mul_fromRows]
  simpa only [hA, hB] using key

/-- The Gaussian location kernel `m ↦ N(m, S)`. -/
def gaussianShiftKernel (S : Matrix ι ι ℝ) :
    ProbabilityTheory.Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) where
  toFun m := multivariateGaussian m S
  measurable' := by
    change Measurable (Function.uncurry multivariateGaussian ∘ fun m ↦ (m, S))
    exact measurable_multivariateGaussian.comp (measurable_id.prodMk measurable_const)

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- The Gaussian shift kernel at `m` is the Gaussian law with mean `m` and covariance `S`. -/
@[simp]
theorem gaussianShiftKernel_apply (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) :
    gaussianShiftKernel S m = multivariateGaussian m S := rfl

instance (S : Matrix ι ι ℝ) : IsMarkovKernel (gaussianShiftKernel S) where
  isProbabilityMeasure m := by rw [gaussianShiftKernel_apply]; infer_instance

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- The multivariate Gaussian density is jointly measurable in the mean and the point. -/
theorem measurable_multivariateGaussianPDF_uncurry (S : Matrix ι ι ℝ) :
    Measurable fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      TauCeti.Probability.multivariateGaussianPDF q.1 S q.2 := by
  simp only [TauCeti.Probability.multivariateGaussianPDF_def,
    TauCeti.Probability.multivariateGaussianPDFReal_def]
  fun_prop

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- If `Z` has law `N(0, S)` and is independent of `Y`, then the joint law of `Y` and
`g(Y) + Z` is the composition of the law of `Y` with the Gaussian kernel `y ↦ N(g y, S)`. -/
theorem map_prodMk_add_eq_compProd {β : Type*} [MeasurableSpace β] [IsProbabilityMeasure P]
    {Y : Ω → β} {Z : Ω → EuclideanSpace ℝ ι} {g : β → EuclideanSpace ℝ ι} (hg : Measurable g)
    (hY : AEMeasurable Y P) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hZ : HasLaw Z (multivariateGaussian 0 S) P) (hYZ : IndepFun Y Z P) :
    P.map (fun ω ↦ (Y ω, g (Y ω) + Z ω)) =
      P.map Y ⊗ₘ (gaussianShiftKernel S).comap g hg := by
  have hpair : P.map (fun ω ↦ (Y ω, Z ω)) = (P.map Y).prod (multivariateGaussian 0 S) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hY hZ.aemeasurable] at hYZ
    rw [hYZ, hZ.map_eq]
  have hF : Measurable fun q : β × EuclideanSpace ℝ ι ↦ (q.1, g q.1 + q.2) :=
    measurable_fst.prodMk ((hg.comp measurable_fst).add measurable_snd)
  have hcomp : (fun ω ↦ (Y ω, g (Y ω) + Z ω)) =
      (fun q : β × EuclideanSpace ℝ ι ↦ (q.1, g q.1 + q.2)) ∘ fun ω ↦ (Y ω, Z ω) := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
    (hY.prodMk hZ.aemeasurable), hpair]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.compProd_apply hs]
  refine lintegral_congr fun b ↦ ?_
  rw [Kernel.comap_apply, gaussianShiftKernel_apply]
  have hshift : multivariateGaussian (g b) S =
      (multivariateGaussian 0 S).map fun z ↦ g b + z := by
    have h := TauCeti.Probability.map_affine_multivariateGaussian 0 hS
      (1 : Matrix ι ι ℝ) (g b)
    simp only [Matrix.toLpLin_one, LinearMap.id_apply, map_zero, zero_add, Matrix.one_mul,
      Matrix.transpose_one, Matrix.mul_one] at h
    rw [← h]
    congr 1
    funext z
    exact add_comm _ _
  rw [hshift, Measure.map_apply (measurable_const_add _) (measurable_prodMk_left hs)]
  rfl

omit [Fintype κ] [Fintype τ] [Fintype σ] [DecidableEq κ] [DecidableEq τ] [DecidableEq σ] in
/-- If `Z` has law `N(0, S)` and is independent of `Y`, then the conditional law of
`g(Y) + Z` given `Y = y` is `N(g y, S)` for almost every `y`. -/
theorem condDistrib_add_eq_multivariateGaussian {β : Type*} [MeasurableSpace β]
    [IsProbabilityMeasure P] {Y : Ω → β} {Z : Ω → EuclideanSpace ℝ ι}
    {g : β → EuclideanSpace ℝ ι} (hg : Measurable g) (hY : AEMeasurable Y P)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hZ : HasLaw Z (multivariateGaussian 0 S) P)
    (hYZ : IndepFun Y Z P) :
    ∀ᵐ b ∂(P.map Y), condDistrib (fun ω ↦ g (Y ω) + Z ω) Y P b =
      multivariateGaussian (g b) S := by
  have h := condDistrib_ae_eq_of_measure_eq_compProd hY
    (show AEMeasurable (fun ω ↦ g (Y ω) + Z ω) P from
      (hg.comp_aemeasurable hY).add hZ.aemeasurable)
    (map_prodMk_add_eq_compProd hg hY hS hZ hYZ)
  filter_upwards [h] with b hb
  rw [hb, Kernel.comap_apply, gaussianShiftKernel_apply]

end GaussianPair

section Density

/-- Transport of a measure with density along a measurable equivalence. -/
theorem map_withDensity_comp_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (e : α ≃ᵐ β) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ e)).map e = (μ.map e).withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs hf e.measurable]
  rfl

end Density


end CKSD
