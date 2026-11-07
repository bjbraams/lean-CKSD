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
# The Kalman filter

A time-varying linear Gaussian state-space model `x_{t+1} = F_t x_t + w_t`,
`y_t = H_t x_t + v_t` in finite dimensions, with time indexed from `0`: the initial state is
`x_0`, so `x_{0|-1}` and `P_{0|-1}` are its mean and covariance. The covariance recursion does
not depend on the data; the mean recursion is a function of the observation sequence, of which
only the first `t + 1` terms enter the filtered mean at time `t`.

Gaussian densities are TauCeti's `multivariateGaussianPDF`.

## Proof outline

The proof follows the innovations argument and works with the prediction errors
`ε_t = x_t - x_{t|t-1}`, the filtering errors `φ_t = x_t - x_{t|t}`, and the innovations
`e_t = y_t - H_t x_{t|t-1}` (`KalmanModel.predErr`, `KalmanModel.filtErr`,
`KalmanModel.innovation`). By induction on `t`, `ε_t` has law `N(0, P_{t|t-1})` and is
independent of `(y_0, …, y_{t-1})` (`KalmanModel.GaussianInputs.predErr_hasLaw_indepFun`).

* Measurement update (`KalmanModel.GaussianInputs.measurement_update`): `e_t = H_t ε_t + v_t`
  and `φ_t = (I - K_t H_t) ε_t - K_t v_t` are linear combinations of the independent centered
  Gaussian vectors `ε_t` and `v_t`; they are independent because their cross-covariance
  vanishes, and the Joseph form gives the covariance `P_{t|t}` of `φ_t`.
* Time update (`KalmanModel.GaussianInputs.time_update`): `ε_{t+1} = F_t φ_t + w_t`.
* Independence bookkeeping uses that `v_t` and `w_t` are independent of the inputs that
  determine the earlier errors and observations (`indepFun_apply_prefix_of_indepFun`).

The conditional laws then follow from `x_t = x_{t|t}(y_0, …, y_t) + φ_t` with `φ_t`
independent of the record (`condDistrib_add_eq_multivariateGaussian`); the innovations are
mutually independent because each is independent of the earlier record
(`iIndepFun_of_indepFun_finPrefix`); and the density factorization follows by appending one
observation at a time (`KalmanModel.GaussianInputs.map_obsPrefix_eq_withDensity`).

Reused results: from TauCeti, the affine images, convolutions, independence criterion, and
densities of multivariate Gaussian laws (`TauCeti.Probability.map_affine_multivariateGaussian`,
`TauCeti.Probability.multivariateGaussian_conv_multivariateGaussian`,
`TauCeti.Probability.indepFun_matrix_of_hasLaw_multivariateGaussian_iff`,
`TauCeti.Probability.multivariateGaussian_eq_withDensity`); from Mathlib, the
conditional-distribution characterization `condDistrib_ae_eq_of_measure_eq_compProd`,
`Measure.withDensity_compProd_withDensity`, and `measurePreserving_piFinSuccAbove`.

Source: GAPS 106.7.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

/-- Coefficients of a time-varying linear Gaussian state-space model with state dimension `d`
and observation dimension `p`. -/
structure KalmanModel (d p : ℕ) where
  /-- State transition matrices `F_t`. -/
  transition : ℕ → Matrix (Fin d) (Fin d) ℝ
  /-- Observation matrices `H_t`. -/
  observation : ℕ → Matrix (Fin p) (Fin d) ℝ
  /-- State-noise covariances `Q_t`. -/
  stateCov : ℕ → Matrix (Fin d) (Fin d) ℝ
  /-- Observation-noise covariances `R_t`. -/
  obsCov : ℕ → Matrix (Fin p) (Fin p) ℝ
  /-- Mean of the initial state. -/
  initMean : EuclideanSpace ℝ (Fin d)
  /-- Covariance of the initial state. -/
  initCov : Matrix (Fin d) (Fin d) ℝ

namespace KalmanModel

variable {d p : ℕ} (M : KalmanModel d p)

/-- Innovation covariance `H_t C H_tᵀ + R_t` for a predicted covariance `C`. -/
def innovCovOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  M.observation t * C * (M.observation t).transpose + M.obsCov t

/-- Kalman gain `C H_tᵀ (H_t C H_tᵀ + R_t)⁻¹` for a predicted covariance `C`. -/
def gainOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin p) ℝ :=
  C * (M.observation t).transpose * (M.innovCovOf t C)⁻¹

/-- Filtered covariance `C - K_t H_t C` for a predicted covariance `C`. -/
def filtCovOf (t : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  C - M.gainOf t C * M.observation t * C

/-- Predicted covariances `P_{t|t-1}`, with `P_{0|-1}` the initial covariance. -/
def predCov : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => M.initCov
  | t + 1 => M.transition t * M.filtCovOf t (predCov t) * (M.transition t).transpose +
      M.stateCov t

/-- Innovation covariances `Σ_t = H_t P_{t|t-1} H_tᵀ + R_t`. -/
def innovCov (t : ℕ) : Matrix (Fin p) (Fin p) ℝ := M.innovCovOf t (M.predCov t)

/-- Kalman gains `K_t = P_{t|t-1} H_tᵀ Σ_t⁻¹`. -/
def gain (t : ℕ) : Matrix (Fin d) (Fin p) ℝ := M.gainOf t (M.predCov t)

/-- Filtered covariances `P_{t|t} = P_{t|t-1} - K_t H_t P_{t|t-1}`. -/
def filtCov (t : ℕ) : Matrix (Fin d) (Fin d) ℝ := M.filtCovOf t (M.predCov t)

/-- Predicted means `x_{t|t-1}` as functions of the observations, with `x_{0|-1}` the initial
mean and `x_{t+1|t} = F_t x_{t|t}`. -/
def predMean (y : ℕ → EuclideanSpace ℝ (Fin p)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => M.initMean
  | t + 1 => Matrix.toEuclideanLin (M.transition t)
      (predMean y t + Matrix.toEuclideanLin (M.gain t)
        (y t - Matrix.toEuclideanLin (M.observation t) (predMean y t)))

/-- Filtered means `x_{t|t} = x_{t|t-1} + K_t (y_t - H_t x_{t|t-1})`. -/
def filtMean (y : ℕ → EuclideanSpace ℝ (Fin p)) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  M.predMean y t + Matrix.toEuclideanLin (M.gain t)
    (y t - Matrix.toEuclideanLin (M.observation t) (M.predMean y t))

/-- The state process `x_0 = x₀`, `x_{t+1} = F_t x_t + w_t`. -/
def state {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0 => x₀
  | t + 1 => fun ω ↦ Matrix.toEuclideanLin (M.transition t) (state x₀ w t ω) + w t ω

/-- The observation process `y_t = H_t x_t + v_t`. -/
def observationProcess {Ω : Type*} (x : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  Matrix.toEuclideanLin (M.observation t) (x t ω) + v t ω

end KalmanModel

/-- Extension of a finite observation record `y_0, …, y_{n-1}` by zeros. -/
def extendObservations {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) (i : ℕ) : E :=
  if h : i < n then ys ⟨i, h⟩ else 0

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


section Deterministic

/-- A zero-extended observation record is measurable in each coordinate. -/
theorem measurable_extendObservations_apply {E : Type*} [Zero E] [MeasurableSpace E] {n : ℕ}
    (i : ℕ) : Measurable fun ys : Fin n → E ↦ extendObservations ys i := by
  unfold extendObservations
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The zero extension of a finite record returns the recorded values. -/
@[simp]
theorem extendObservations_of_lt {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) {i : ℕ}
    (h : i < n) : extendObservations ys i = ys ⟨i, h⟩ := by
  simp [extendObservations, h]


namespace KalmanModel

variable {d p : ℕ} (M : KalmanModel d p)

/-- The predicted mean at time `t` depends only on the observations before time `t`. -/
theorem predMean_congr {y y' : ℕ → EuclideanSpace ℝ (Fin p)} {t : ℕ}
    (h : ∀ i < t, y i = y' i) : M.predMean y t = M.predMean y' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)
    simp only [predMean, ih', h t (Nat.lt_succ_self t)]

/-- The filtered mean at time `t` depends only on the observations up to time `t`. -/
theorem filtMean_congr {y y' : ℕ → EuclideanSpace ℝ (Fin p)} {t : ℕ}
    (h : ∀ i ≤ t, y i = y' i) : M.filtMean y t = M.filtMean y' t := by
  have hp := M.predMean_congr (t := t) fun i hi ↦ h i hi.le
  simp only [filtMean, hp, h t le_rfl]

/-- The time update of the mean: `x_{t+1|t} = F_t x_{t|t}`. -/
theorem predMean_succ (y : ℕ → EuclideanSpace ℝ (Fin p)) (t : ℕ) :
    M.predMean y (t + 1) = Matrix.toEuclideanLin (M.transition t) (M.filtMean y t) := rfl

/-- The predicted mean is a measurable function of a measurably parametrized observation
sequence. -/
theorem measurable_predMean {β : Type*} [MeasurableSpace β]
    {y : ℕ → β → EuclideanSpace ℝ (Fin p)} (hy : ∀ i, Measurable (y i)) (t : ℕ) :
    Measurable fun b ↦ M.predMean (fun i ↦ y i b) t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [predMean]
    have h1 : Measurable fun b ↦ Matrix.toEuclideanLin (M.observation t)
        (M.predMean (fun i ↦ y i b) t) := by fun_prop
    have h2 : Measurable fun b ↦ Matrix.toEuclideanLin (M.gain t)
        (y t b - Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ y i b) t)) :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) ↦
        Matrix.toEuclideanLin (M.gain t) z).comp ((hy t).sub h1)
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
      Matrix.toEuclideanLin (M.transition t) z).comp (ih.add h2)

/-- The filtered mean is a measurable function of a measurably parametrized observation
sequence. -/
theorem measurable_filtMean {β : Type*} [MeasurableSpace β]
    {y : ℕ → β → EuclideanSpace ℝ (Fin p)} (hy : ∀ i, Measurable (y i)) (t : ℕ) :
    Measurable fun b ↦ M.filtMean (fun i ↦ y i b) t := by
  have hF : Measurable fun b ↦ M.filtMean (fun i ↦ y i b) t := by
    unfold filtMean
    have h1 := M.measurable_predMean hy t
    have h2 : Measurable fun b ↦ Matrix.toEuclideanLin (M.observation t)
        (M.predMean (fun i ↦ y i b) t) :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
        Matrix.toEuclideanLin (M.observation t) z).comp h1
    exact h1.add ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin p) ↦
        Matrix.toEuclideanLin (M.gain t) z).comp ((hy t).sub h2))
  exact hF

/-- The state at time `s` is unchanged by a change of sample space that preserves the initial
state and the state noises before time `s`. -/
theorem state_congr {Ω Ω' : Type*} (f : Ω' → Ω) {x₀ : Ω → EuclideanSpace ℝ (Fin d)}
    {w : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {x₀' : Ω' → EuclideanSpace ℝ (Fin d)}
    {w' : ℕ → Ω' → EuclideanSpace ℝ (Fin d)} (h₀ : ∀ ω, x₀' ω = x₀ (f ω)) {s : ℕ}
    (hw : ∀ i < s, ∀ ω, w' i ω = w i (f ω)) (ω : Ω') :
    M.state x₀' w' s ω = M.state x₀ w s (f ω) := by
  induction s with
  | zero => exact h₀ ω
  | succ s ih =>
    simp only [state, ih fun i hi ↦ hw i (Nat.lt_succ_of_lt hi), hw s (Nat.lt_succ_self s)]

/-- The state process is measurable when the initial state and the noises are. -/
theorem measurable_state {Ω : Type*} [MeasurableSpace Ω] {x₀ : Ω → EuclideanSpace ℝ (Fin d)}
    {w : ℕ → Ω → EuclideanSpace ℝ (Fin d)} (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (s : ℕ) : Measurable (M.state x₀ w s) := by
  induction s with
  | zero => exact h₀
  | succ s ih =>
    exact ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
      Matrix.toEuclideanLin (M.transition s) z).comp ih).add (hw s)

/-- The observation process is measurable when the state and the observation noise are. -/
theorem measurable_observationProcess {Ω : Type*} [MeasurableSpace Ω]
    {x : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {v : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (hx : ∀ i, Measurable (x i)) (hv : ∀ i, Measurable (v i)) (s : ℕ) :
    Measurable (M.observationProcess x v s) :=
  ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
    Matrix.toEuclideanLin (M.observation s) z).comp (hx s)).add (hv s)

end KalmanModel

/-- Appending a value to a finite record does not change its zero extension below the old
length. -/
theorem extendObservations_snoc {E : Type*} [Zero E] {n : ℕ} (ys : Fin n → E) (y : E) {j : ℕ}
    (hj : j < n) :
    extendObservations (Fin.snoc ys y : Fin (n + 1) → E) j = extendObservations ys j := by
  rw [extendObservations_of_lt _ (Nat.lt_succ_of_lt hj), extendObservations_of_lt _ hj]
  exact Fin.snoc_castSucc (α := fun _ ↦ E) (p := ys) (x := y) ⟨j, hj⟩

namespace KalmanModel

variable {d p : ℕ} (M : KalmanModel d p)

/-- The product of the one-step predictive densities `∏_{i<n} φ(y_i; H_i x_{i|i-1}, Σ_i)` of an
observation record `(y_0, …, y_{n-1})`. -/
def innovDensity (n : ℕ) (ys : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ≥0∞ :=
  ∏ i : Fin n, TauCeti.Probability.multivariateGaussianPDF
    (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
    (M.innovCov i) (ys i)

/-- The predicted mean computed from a zero-extended record is measurable in the record. -/
theorem measurable_predMean_extendObservations (n t : ℕ) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ (Fin p) ↦
      M.predMean (extendObservations ys) t :=
  M.measurable_predMean (y := fun i ys ↦ extendObservations ys i)
    (fun i ↦ measurable_extendObservations_apply i) t

/-- The filtered mean computed from a zero-extended record is measurable in the record. -/
theorem measurable_filtMean_extendObservations (n t : ℕ) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ (Fin p) ↦
      M.filtMean (extendObservations ys) t :=
  M.measurable_filtMean (y := fun i ys ↦ extendObservations ys i)
    (fun i ↦ measurable_extendObservations_apply i) t

/-- Each one-step predictive density factor is measurable in the record. -/
theorem measurable_innovDensity_factor (n : ℕ) (i : Fin n) :
    Measurable fun ys : Fin n → EuclideanSpace ℝ (Fin p) ↦
      TauCeti.Probability.multivariateGaussianPDF
        (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
        (M.innovCov i) (ys i) := by
  have h₁ := M.measurable_predMean_extendObservations n i
  have h₂ : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
      Matrix.toEuclideanLin (M.observation i) z := by fun_prop
  have hq : Measurable fun ys : Fin n → EuclideanSpace ℝ (Fin p) ↦
      (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i), ys i) :=
    (h₂.comp h₁).prodMk (measurable_pi_apply i)
  have := (measurable_multivariateGaussianPDF_uncurry (M.innovCov i)).comp hq
  exact this

/-- The product of predictive densities is measurable. -/
theorem measurable_innovDensity (n : ℕ) : Measurable (M.innovDensity n) := by
  unfold innovDensity
  exact Finset.measurable_prod _ fun i _ ↦ M.measurable_innovDensity_factor n i

/-- The product of predictive densities factors over the last observation. -/
theorem innovDensity_snoc (n : ℕ) (ys : Fin n → EuclideanSpace ℝ (Fin p))
    (y : EuclideanSpace ℝ (Fin p)) :
    M.innovDensity (n + 1) (Fin.snoc ys y) = M.innovDensity n ys *
      TauCeti.Probability.multivariateGaussianPDF
        (Matrix.toEuclideanLin (M.observation n) (M.predMean (extendObservations ys) n))
        (M.innovCov n) y := by
  unfold innovDensity
  rw [Fin.prod_univ_castSucc]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Fin.snoc_castSucc, Fin.val_castSucc, M.predMean_congr fun j hj ↦
      extendObservations_snoc ys y (hj.trans i.2)]
  · rw [Fin.snoc_last, Fin.val_last, M.predMean_congr fun j hj ↦ extendObservations_snoc ys y hj]

end KalmanModel


end Deterministic


namespace KalmanModel

variable {d p : ℕ} (M : KalmanModel d p)

section Covariance

/-- A real congruence `A S Aᵀ` of a positive-semidefinite matrix is positive semidefinite. -/
theorem posSemidef_mul_mul_transpose {m n : Type*} [Fintype m] [Fintype n]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (A : Matrix m n ℝ) :
    (A * S * A.transpose).PosSemidef := by
  simpa using hS.mul_mul_conjTranspose_same A

/-- With a nonsingular innovation covariance, `K_t Σ_t = P_{t|t-1} H_tᵀ`. -/
theorem gain_mul_innovCov {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    M.gain t * M.innovCov t = M.predCov t * (M.observation t).transpose := by
  simp only [gain, gainOf]
  rw [Matrix.mul_assoc, ← innovCov, Matrix.nonsing_inv_mul _ hdet.isUnit, Matrix.mul_one]

/-- The cross-covariance of the filtered error and the innovation vanishes:
`(I - K_t H_t) P_{t|t-1} H_tᵀ - K_t R_t = 0`. -/
theorem filtErr_innovation_cross {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    (1 - M.gain t * M.observation t) * M.predCov t * (M.observation t).transpose +
      (-M.gain t) * M.obsCov t * (1 : Matrix (Fin p) (Fin p) ℝ).transpose = 0 := by
  have h := M.gain_mul_innovCov hdet
  simp only [innovCov, innovCovOf] at h
  calc _ = M.predCov t * (M.observation t).transpose - M.gain t *
        (M.observation t * M.predCov t * (M.observation t).transpose + M.obsCov t) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.transpose_one,
          Matrix.mul_one, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = 0 := by rw [h, sub_self]

/-- Joseph form of the filtered covariance: with a nonsingular innovation covariance,
`(I - K_t H_t) P (I - K_t H_t)ᵀ + K_t R_t K_tᵀ = P - K_t H_t P`. -/
theorem filtCov_eq_joseph {t : ℕ} (hdet : (M.innovCov t).det ≠ 0) :
    (1 - M.gain t * M.observation t) * M.predCov t *
        (1 - M.gain t * M.observation t).transpose +
      (-M.gain t) * M.obsCov t * (-M.gain t).transpose = M.filtCov t := by
  have h := M.gain_mul_innovCov hdet
  simp only [innovCov, innovCovOf] at h
  set K := M.gain t
  set H := M.observation t
  set C := M.predCov t
  calc _ = C - K * H * C - C * H.transpose * K.transpose +
        K * (H * C * H.transpose + M.obsCov t) * K.transpose := by
        simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          Matrix.transpose_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]
        abel
    _ = C - K * H * C := by rw [h]; abel
    _ = M.filtCov t := by simp only [filtCov, filtCovOf, K, H, C, gain]

/-- Under positive-semidefinite noise and initial covariances and nonsingular innovation
covariances, every predicted covariance is positive semidefinite. -/
theorem predCov_posSemidef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.predCov t).PosSemidef := by
  induction t with
  | zero => exact hP₀
  | succ t ih =>
    have hf : (M.filtCov t).PosSemidef := by
      rw [← M.filtCov_eq_joseph (hinnov t)]
      exact (posSemidef_mul_mul_transpose ih _).add (posSemidef_mul_mul_transpose (hR t) _)
    exact (posSemidef_mul_mul_transpose hf (M.transition t)).add (hQ t)

/-- Under the hypotheses of `predCov_posSemidef`, every filtered covariance is positive
semidefinite. -/
theorem filtCov_posSemidef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.filtCov t).PosSemidef := by
  rw [← M.filtCov_eq_joseph (hinnov t)]
  exact (posSemidef_mul_mul_transpose (M.predCov_posSemidef hQ hR hP₀ hinnov t) _).add
    (posSemidef_mul_mul_transpose (hR t) _)

/-- Under the hypotheses of `predCov_posSemidef`, every innovation covariance is positive
definite. -/
theorem innovCov_posDef (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) (t : ℕ) : (M.innovCov t).PosDef := by
  have h : (M.innovCov t).PosSemidef :=
    (posSemidef_mul_mul_transpose (M.predCov_posSemidef hQ hR hP₀ hinnov t) _).add (hR t)
  exact h.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (hinnov t).isUnit)

end Covariance

section Errors

variable {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ (Fin d)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin d))
  (v : ℕ → Ω → EuclideanSpace ℝ (Fin p))

/-- The observation process `y_t = H_t x_t + v_t` driven by `x₀`, `w`, and `v`. -/
def obsProc : ℕ → Ω → EuclideanSpace ℝ (Fin p) := M.observationProcess (M.state x₀ w) v

/-- The observation record `(y_0, …, y_{n-1})`. -/
def obsPrefix (n : ℕ) (ω : Ω) : Fin n → EuclideanSpace ℝ (Fin p) :=
  fun i ↦ M.obsProc x₀ w v i ω

/-- The prediction error `x_t - x_{t|t-1}`. -/
def predErr (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  M.state x₀ w t ω - M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t

/-- The filtering error `x_t - x_{t|t}`. -/
def filtErr (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  M.state x₀ w t ω - M.filtMean (fun i ↦ M.obsProc x₀ w v i ω) t

/-- The innovation `y_t - H_t x_{t|t-1}`. -/
def innovation (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  M.obsProc x₀ w v t ω -
    Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t)

/-- The innovation is `H_t (x_t - x_{t|t-1}) + v_t`. -/
theorem innovation_eq (t : ℕ) (ω : Ω) :
    M.innovation x₀ w v t ω =
      Matrix.toEuclideanLin (M.observation t) (M.predErr x₀ w v t ω) + v t ω := by
  simp only [innovation, predErr, obsProc, observationProcess, map_sub]
  abel

/-- The filtering error is `(I - K_t H_t)(x_t - x_{t|t-1}) - K_t v_t`. -/
theorem filtErr_eq (t : ℕ) (ω : Ω) :
    M.filtErr x₀ w v t ω =
      Matrix.toEuclideanLin (1 - M.gain t * M.observation t) (M.predErr x₀ w v t ω) +
        Matrix.toEuclideanLin (-M.gain t) (v t ω) := by
  have h : M.filtErr x₀ w v t ω = M.predErr x₀ w v t ω -
      Matrix.toEuclideanLin (M.gain t) (M.innovation x₀ w v t ω) := by
    simp only [filtErr, filtMean, predErr, innovation]
    abel
  rw [h, innovation_eq]
  simp only [map_sub, map_add, map_neg, LinearMap.sub_apply, LinearMap.neg_apply,
    Matrix.toLpLin_one, Matrix.toLpLin_mul_same, LinearMap.id_apply, LinearMap.comp_apply]
  abel

/-- The prediction error at time `t + 1` is `F_t (x_t - x_{t|t}) + w_t`. -/
theorem predErr_succ (t : ℕ) (ω : Ω) :
    M.predErr x₀ w v (t + 1) ω =
      Matrix.toEuclideanLin (M.transition t) (M.filtErr x₀ w v t ω) + w t ω := by
  simp only [predErr, filtErr, state, predMean_succ, map_sub]
  abel

/-- The observation record up to time `t` is obtained from the record before time `t` and the
innovation at time `t` by appending `e_t + H_t x_{t|t-1}`. -/
theorem obsPrefix_succ_eq (t : ℕ) (ω : Ω) :
    M.obsPrefix x₀ w v (t + 1) ω =
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p)) (Fin.last t)).symm
        (M.innovation x₀ w v t ω + Matrix.toEuclideanLin (M.observation t)
          (M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t),
          M.obsPrefix x₀ w v t ω) := by
  have hpm : M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t =
      M.predMean (fun i ↦ M.obsProc x₀ w v i ω) t :=
    M.predMean_congr fun i hi ↦ by simp [extendObservations_of_lt _ hi, obsPrefix]
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, Fin.insertNth_last',
    hpm]
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [innovation, obsPrefix]
  · simp [obsPrefix]

end Errors


section Congr

variable {Ω Ω' : Type*} (f : Ω → Ω') {x₀ : Ω → EuclideanSpace ℝ (Fin d)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {v : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
  {x₀' : Ω' → EuclideanSpace ℝ (Fin d)} {w' : ℕ → Ω' → EuclideanSpace ℝ (Fin d)}
  {v' : ℕ → Ω' → EuclideanSpace ℝ (Fin p)}

/-- Observations up to time `s` are unchanged by a change of sample space that preserves the
initial state, the state noises before time `s`, and the observation noise at time `s`. -/
theorem obsProc_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {s : ℕ}
    (hw : ∀ i < s, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ ω, v s ω = v' s (f ω)) (ω : Ω) :
    M.obsProc x₀ w v s ω = M.obsProc x₀' w' v' s (f ω) := by
  simp only [obsProc, observationProcess, M.state_congr f h₀ hw, hv]

/-- The prediction error and the observation record at time `t` are unchanged by a change of
sample space that preserves the initial state and the noises before time `t`. -/
theorem predErr_obsPrefix_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {t : ℕ}
    (hw : ∀ i < t, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ i < t, ∀ ω, v i ω = v' i (f ω)) (ω : Ω) :
    M.predErr x₀ w v t ω = M.predErr x₀' w' v' t (f ω) ∧
      M.obsPrefix x₀ w v t ω = M.obsPrefix x₀' w' v' t (f ω) := by
  have hy : ∀ i < t, M.obsProc x₀ w v i ω = M.obsProc x₀' w' v' i (f ω) := fun i hi ↦
    M.obsProc_congr f h₀ (fun j hj ↦ hw j (hj.trans hi)) (hv i hi) ω
  refine ⟨?_, funext fun i ↦ hy i i.2⟩
  simp only [predErr, M.state_congr f h₀ hw, M.predMean_congr hy]

/-- The filtering error at time `t` and the observation record up to time `t` are unchanged
by a change of sample space that preserves the initial state, the state noises before time `t`,
and the observation noises up to time `t`. -/
theorem filtErr_obsPrefix_congr (h₀ : ∀ ω, x₀ ω = x₀' (f ω)) {t : ℕ}
    (hw : ∀ i < t, ∀ ω, w i ω = w' i (f ω)) (hv : ∀ i ≤ t, ∀ ω, v i ω = v' i (f ω)) (ω : Ω) :
    M.filtErr x₀ w v t ω = M.filtErr x₀' w' v' t (f ω) ∧
      M.obsPrefix x₀ w v (t + 1) ω = M.obsPrefix x₀' w' v' (t + 1) (f ω) := by
  have hy : ∀ i ≤ t, M.obsProc x₀ w v i ω = M.obsProc x₀' w' v' i (f ω) := fun i hi ↦
    M.obsProc_congr f h₀ (fun j hj ↦ hw j (lt_of_lt_of_le hj hi)) (hv i hi) ω
  refine ⟨?_, funext fun i ↦ hy i (Nat.lt_succ_iff.mp i.2)⟩
  simp only [filtErr, M.state_congr f h₀ hw, M.filtMean_congr hy]

end Congr

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {x₀ : Ω → EuclideanSpace ℝ (Fin d)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {v : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

/-- The observation process is measurable for measurable inputs. -/
theorem measurable_obsProc (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (s : ℕ) : Measurable (M.obsProc x₀ w v s) :=
  M.measurable_observationProcess (M.measurable_state h₀ hw) hv s

/-- The observation record is measurable for measurable inputs. -/
theorem measurable_obsPrefix (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (n : ℕ) : Measurable (M.obsPrefix x₀ w v n) :=
  measurable_pi_iff.mpr fun i ↦ M.measurable_obsProc h₀ hw hv i

/-- The prediction error is measurable for measurable inputs. -/
theorem measurable_predErr (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (t : ℕ) : Measurable (M.predErr x₀ w v t) :=
  (M.measurable_state h₀ hw t).sub
    (M.measurable_predMean (M.measurable_obsProc h₀ hw hv) t)

/-- The filtering error is measurable for measurable inputs. -/
theorem measurable_filtErr (h₀ : Measurable x₀) (hw : ∀ i, Measurable (w i))
    (hv : ∀ i, Measurable (v i)) (t : ℕ) : Measurable (M.filtErr x₀ w v t) :=
  (M.measurable_state h₀ hw t).sub
    (M.measurable_filtMean (M.measurable_obsProc h₀ hw hv) t)

end Measurability

/-- The prediction error and the observation record at time `t` are a measurable function of
the initial state, the state noises, and the observation noises before time `t`. -/
theorem exists_predErr_obsPrefix_eq_comp {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (v : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (t : ℕ) :
    ∃ G : EuclideanSpace ℝ (Fin d) × (ℕ → EuclideanSpace ℝ (Fin d)) ×
        (Fin t → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) ×
          (Fin t → EuclideanSpace ℝ (Fin p)),
      Measurable G ∧ ∀ ω, (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω) =
        G (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω) := by
  let x₀' : EuclideanSpace ℝ (Fin d) × (ℕ → EuclideanSpace ℝ (Fin d)) ×
      (Fin t → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) := fun b ↦ b.1
  let w' : ℕ → EuclideanSpace ℝ (Fin d) × (ℕ → EuclideanSpace ℝ (Fin d)) ×
      (Fin t → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) := fun i b ↦ b.2.1 i
  let v' : ℕ → EuclideanSpace ℝ (Fin d) × (ℕ → EuclideanSpace ℝ (Fin d)) ×
      (Fin t → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p) :=
    fun i b ↦ extendObservations b.2.2 i
  have h₀ : Measurable x₀' := measurable_fst
  have hw : ∀ i, Measurable (w' i) := fun i ↦
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hv : ∀ i, Measurable (v' i) := fun i ↦
    (measurable_extendObservations_apply i).comp (measurable_snd.comp measurable_snd)
  refine ⟨fun b ↦ (M.predErr x₀' w' v' t b, M.obsPrefix x₀' w' v' t b),
    (M.measurable_predErr h₀ hw hv t).prodMk (M.measurable_obsPrefix h₀ hw hv t),
    fun ω ↦ ?_⟩
  obtain ⟨h1, h2⟩ := M.predErr_obsPrefix_congr
    (fun ω ↦ (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω)) (x₀ := x₀) (w := w) (v := v) (t := t) (x₀' := x₀') (w' := w') (v' := v')
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun i hi ω ↦ by simp [v', extendObservations_of_lt _ hi]) ω
  rw [h1, h2]

/-- The filtering error at time `t` and the observation record up to time `t` are a measurable
function of the initial state, the state noises before time `t`, and the observation noises. -/
theorem exists_filtErr_obsPrefix_eq_comp {Ω : Type*} (x₀ : Ω → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (v : ℕ → Ω → EuclideanSpace ℝ (Fin p)) (t : ℕ) :
    ∃ G : EuclideanSpace ℝ (Fin d) × (Fin t → EuclideanSpace ℝ (Fin d)) ×
        (ℕ → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) ×
          (Fin (t + 1) → EuclideanSpace ℝ (Fin p)),
      Measurable G ∧ ∀ ω, (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω) =
        G (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω) := by
  let x₀' : EuclideanSpace ℝ (Fin d) × (Fin t → EuclideanSpace ℝ (Fin d)) ×
      (ℕ → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) := fun b ↦ b.1
  let w' : ℕ → EuclideanSpace ℝ (Fin d) × (Fin t → EuclideanSpace ℝ (Fin d)) ×
      (ℕ → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin d) :=
    fun i b ↦ extendObservations b.2.1 i
  let v' : ℕ → EuclideanSpace ℝ (Fin d) × (Fin t → EuclideanSpace ℝ (Fin d)) ×
      (ℕ → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p) := fun i b ↦ b.2.2 i
  have h₀ : Measurable x₀' := measurable_fst
  have hw : ∀ i, Measurable (w' i) := fun i ↦
    (measurable_extendObservations_apply i).comp (measurable_fst.comp measurable_snd)
  have hv : ∀ i, Measurable (v' i) := fun i ↦
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  refine ⟨fun b ↦ (M.filtErr x₀' w' v' t b, M.obsPrefix x₀' w' v' (t + 1) b),
    (M.measurable_filtErr h₀ hw hv t).prodMk (M.measurable_obsPrefix h₀ hw hv (t + 1)),
    fun ω ↦ ?_⟩
  obtain ⟨h1, h2⟩ := M.filtErr_obsPrefix_congr
    (fun ω ↦ (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω)) (x₀ := x₀) (w := w) (v := v) (t := t) (x₀' := x₀') (w' := w') (v' := v')
    (fun _ ↦ rfl) (fun i hi ω ↦ by simp [w', extendObservations_of_lt _ hi])
    (fun _ _ _ ↦ rfl) ω
  rw [h1, h2]


section Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of the Kalman filter theorem: positive-semidefinite noise and initial
covariances, a Gaussian initial state, independent Gaussian white noises independent of the
initial state, and nonsingular innovation covariances. -/
structure GaussianInputs (P : Measure Ω) (x₀ : Ω → EuclideanSpace ℝ (Fin d))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (v : ℕ → Ω → EuclideanSpace ℝ (Fin p)) : Prop where
  stateCov_posSemidef : ∀ t, (M.stateCov t).PosSemidef
  obsCov_posSemidef : ∀ t, (M.obsCov t).PosSemidef
  initCov_posSemidef : M.initCov.PosSemidef
  hasLaw_init : HasLaw x₀ (multivariateGaussian M.initMean M.initCov) P
  hasLaw_stateNoise : ∀ t, HasLaw (w t) (multivariateGaussian 0 (M.stateCov t)) P
  hasLaw_obsNoise : ∀ t, HasLaw (v t) (multivariateGaussian 0 (M.obsCov t)) P
  iIndepFun_stateNoise : iIndepFun w P
  iIndepFun_obsNoise : iIndepFun v P
  indepFun_noise : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P
  indepFun_init_noise : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P
  innovCov_det_ne_zero : ∀ t, (M.innovCov t).det ≠ 0

variable {M} {P : Measure Ω} [IsProbabilityMeasure P] {x₀ : Ω → EuclideanSpace ℝ (Fin d)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {v : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

namespace GaussianInputs

variable (h : M.GaussianInputs P x₀ w v)
include h

omit [IsProbabilityMeasure P] in
/-- Every predicted covariance is positive semidefinite. -/
theorem predCov_posSemidef' (t : ℕ) : (M.predCov t).PosSemidef :=
  M.predCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef h.initCov_posSemidef
    h.innovCov_det_ne_zero t

/-- The prediction error and the observation record at time `t` are jointly almost everywhere
measurable, and the observation noise at time `t` is independent of them. -/
theorem aemeasurable_indepFun_predErr (t : ℕ) :
    AEMeasurable (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P ∧
      IndepFun (v t) (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P := by
  obtain ⟨G, hG, hGeq⟩ := M.exists_predErr_obsPrefix_eq_comp x₀ w v t
  have hpair : (fun ω ↦ (M.predErr x₀ w v t ω, M.obsPrefix x₀ w v t ω)) =
      G ∘ fun ω ↦ (x₀ ω, (fun i ↦ w i ω), fun i : Fin t ↦ v i ω) := funext hGeq
  have hx₀ := h.hasLaw_init.aemeasurable
  have hw := fun t ↦ (h.hasLaw_stateNoise t).aemeasurable
  have hv := fun t ↦ (h.hasLaw_obsNoise t).aemeasurable
  rw [hpair]
  refine ⟨hG.comp_aemeasurable (hx₀.prodMk ((AEMeasurable.of_eval hw).prodMk
    (AEMeasurable.of_eval fun i : Fin t ↦ hv i))), ?_⟩
  exact (indepFun_apply_prefix_of_indepFun hx₀ hw hv h.iIndepFun_obsNoise h.indepFun_noise
    h.indepFun_init_noise t).comp measurable_id hG

/-- The filtering error at time `t` and the observation record up to time `t` are jointly
almost everywhere measurable, and the state noise at time `t` is independent of them. -/
theorem aemeasurable_indepFun_filtErr (t : ℕ) :
    AEMeasurable (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) P ∧
      IndepFun (w t) (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) P := by
  obtain ⟨G, hG, hGeq⟩ := M.exists_filtErr_obsPrefix_eq_comp x₀ w v t
  have hpair : (fun ω ↦ (M.filtErr x₀ w v t ω, M.obsPrefix x₀ w v (t + 1) ω)) =
      G ∘ fun ω ↦ (x₀ ω, (fun i : Fin t ↦ w i ω), fun i ↦ v i ω) := funext hGeq
  have hx₀ := h.hasLaw_init.aemeasurable
  have hw := fun t ↦ (h.hasLaw_stateNoise t).aemeasurable
  have hv := fun t ↦ (h.hasLaw_obsNoise t).aemeasurable
  rw [hpair]
  refine ⟨hG.comp_aemeasurable (hx₀.prodMk ((AEMeasurable.of_eval fun i : Fin t ↦ hw i).prodMk
    (AEMeasurable.of_eval hv))), ?_⟩
  exact (indepFun_apply_prefix_of_indepFun' hx₀ hw hv h.iIndepFun_stateNoise h.indepFun_noise
    h.indepFun_init_noise t).comp measurable_id hG

/-- Measurement update. If the prediction error at time `t` has law `N(0, P_{t|t-1})` and is
independent of `y_0, …, y_{t-1}`, then the innovation has law `N(0, Σ_t)`, the filtering error
has law `N(0, P_{t|t})` and is independent of `y_0, …, y_t`, and the innovation is independent
of `y_0, …, y_{t-1}`. -/
theorem measurement_update (t : ℕ)
    (hlaw : HasLaw (M.predErr x₀ w v t) (multivariateGaussian 0 (M.predCov t)) P)
    (hind : IndepFun (M.predErr x₀ w v t) (M.obsPrefix x₀ w v t) P) :
    HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P ∧
      HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P ∧
      IndepFun (M.filtErr x₀ w v t) (M.obsPrefix x₀ w v (t + 1)) P ∧
      IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P := by
  obtain ⟨hm, hF⟩ := h.aemeasurable_indepFun_predErr t
  have hPt := h.predCov_posSemidef' t
  have hRt := h.obsCov_posSemidef t
  have hvt := h.hasLaw_obsNoise t
  have hεv : IndepFun (M.predErr x₀ w v t) (v t) P :=
    (hF.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst).symm
  set H := M.observation t
  set K := M.gain t
  have hinnov : M.innovation x₀ w v t = fun ω ↦ Matrix.toEuclideanLin H (M.predErr x₀ w v t ω) +
      Matrix.toEuclideanLin (1 : Matrix (Fin p) (Fin p) ℝ) (v t ω) := by
    funext ω
    simp [innovation_eq, H]
  have hfilt : M.filtErr x₀ w v t = fun ω ↦
      Matrix.toEuclideanLin (1 - K * H) (M.predErr x₀ w v t ω) +
        Matrix.toEuclideanLin (-K) (v t ω) := by
    funext ω
    exact M.filtErr_eq x₀ w v t ω
  have hlawe : HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P := by
    have := hasLaw_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv H 1
    rw [hinnov]
    convert this using 2
    simp [innovCov, innovCovOf, H]
  have hlawf : HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P := by
    have := hasLaw_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv (1 - K * H) (-K)
    rw [M.filtCov_eq_joseph (h.innovCov_det_ne_zero t)] at this
    rw [hfilt]
    exact this
  have hfe : IndepFun (M.filtErr x₀ w v t) (M.innovation x₀ w v t) P := by
    rw [hfilt, hinnov]
    exact indepFun_toEuclideanLin_add_of_indepFun hPt hRt hlaw hvt hεv (1 - K * H) (-K) H 1
      (M.filtErr_innovation_cross (h.innovCov_det_ne_zero t))
  -- The record before time `t` is independent of the pair (prediction error, noise).
  have hYεv : IndepFun (M.obsPrefix x₀ w v t) (fun ω ↦ (M.predErr x₀ w v t ω, v t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hm.snd hm.fst hvt.aemeasurable hind.symm
      (hF.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm
  have hYfe : IndepFun (M.obsPrefix x₀ w v t)
      (fun ω ↦ (M.filtErr x₀ w v t ω, M.innovation x₀ w v t ω)) P := by
    have := hYεv.comp (φ := id) (ψ := fun q ↦
      (Matrix.toEuclideanLin (1 - K * H) q.1 + Matrix.toEuclideanLin (-K) q.2,
        Matrix.toEuclideanLin H q.1 + Matrix.toEuclideanLin (1 : Matrix (Fin p) (Fin p) ℝ) q.2))
      measurable_id (by fun_prop)
    rw [hfilt, hinnov]
    simpa only [Function.comp_def, id] using this
  have hfm : AEMeasurable (M.filtErr x₀ w v t) P := hlawf.aemeasurable
  have hem : AEMeasurable (M.innovation x₀ w v t) P := hlawe.aemeasurable
  have hf_eY : IndepFun (M.filtErr x₀ w v t)
      (fun ω ↦ (M.innovation x₀ w v t ω, M.obsPrefix x₀ w v t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hfm hem hm.snd hfe hYfe.symm
  have heY : IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P := by
    have hc := hYfe.comp (φ := id) (ψ := Prod.snd) measurable_id measurable_snd
    simpa only [Function.comp_def, id] using hc.symm
  refine ⟨hlawe, hlawf, ?_, heY⟩
  have hY : M.obsPrefix x₀ w v (t + 1) = fun ω ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p)) (Fin.last t)).symm
        (M.innovation x₀ w v t ω + Matrix.toEuclideanLin (M.observation t)
          (M.predMean (extendObservations (M.obsPrefix x₀ w v t ω)) t),
          M.obsPrefix x₀ w v t ω) := funext (M.obsPrefix_succ_eq x₀ w v t)
  have hmeas : Measurable fun q : EuclideanSpace ℝ (Fin p) ×
      (Fin t → EuclideanSpace ℝ (Fin p)) ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p)) (Fin.last t)).symm
        (q.1 + Matrix.toEuclideanLin (M.observation t) (M.predMean (extendObservations q.2) t),
          q.2) := by
    refine (MeasurableEquiv.measurable _).comp (Measurable.prodMk ?_ measurable_snd)
    refine measurable_fst.add ?_
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
      Matrix.toEuclideanLin (M.observation t) z).comp
      ((M.measurable_predMean (y := fun i (q : EuclideanSpace ℝ (Fin p) ×
        (Fin t → EuclideanSpace ℝ (Fin p))) ↦ extendObservations q.2 i)
        (fun i ↦ (measurable_extendObservations_apply i).comp measurable_snd) t))
  have hc := hf_eY.comp (φ := id) measurable_id hmeas
  rw [hY]
  simpa only [Function.comp_def, id] using hc

/-- Time update. If the filtering error at time `t` has law `N(0, P_{t|t})` and is independent
of `y_0, …, y_t`, then the prediction error at time `t + 1` has law `N(0, P_{t+1|t})` and is
independent of `y_0, …, y_t`. -/
theorem time_update (t : ℕ)
    (hlaw : HasLaw (M.filtErr x₀ w v t) (multivariateGaussian 0 (M.filtCov t)) P)
    (hind : IndepFun (M.filtErr x₀ w v t) (M.obsPrefix x₀ w v (t + 1)) P) :
    HasLaw (M.predErr x₀ w v (t + 1)) (multivariateGaussian 0 (M.predCov (t + 1))) P ∧
      IndepFun (M.predErr x₀ w v (t + 1)) (M.obsPrefix x₀ w v (t + 1)) P := by
  obtain ⟨hm, hF⟩ := h.aemeasurable_indepFun_filtErr t
  have hPf := M.filtCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef
    h.initCov_posSemidef h.innovCov_det_ne_zero t
  have hwt := h.hasLaw_stateNoise t
  have hφw : IndepFun (M.filtErr x₀ w v t) (w t) P :=
    (hF.comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst).symm
  set F := M.transition t
  have hpred : M.predErr x₀ w v (t + 1) = fun ω ↦
      Matrix.toEuclideanLin F (M.filtErr x₀ w v t ω) +
        Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) (w t ω) := by
    funext ω
    simp [predErr_succ, F]
  have hYφw : IndepFun (M.obsPrefix x₀ w v (t + 1))
      (fun ω ↦ (M.filtErr x₀ w v t ω, w t ω)) P :=
    indepFun_prodMk_of_indepFun_of_indepFun_prodMk hm.snd hm.fst hwt.aemeasurable hind.symm
      (hF.comp (φ := id) (ψ := Prod.swap) measurable_id measurable_swap).symm
  have hc := hYφw.comp (φ := id) (ψ := fun q ↦ Matrix.toEuclideanLin F q.1 +
    Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) q.2) measurable_id (by fun_prop)
  rw [hpred]
  refine ⟨?_, ?_⟩
  swap
  · simpa only [Function.comp_def, id] using hc.symm
  have := hasLaw_toEuclideanLin_add_of_indepFun hPf (h.stateCov_posSemidef t) hlaw hwt hφw F 1
  convert this using 2
  simp [predCov, filtCov, F]

/-- The prediction errors: at every time `t`, `x_t - x_{t|t-1}` has law `N(0, P_{t|t-1})` and
is independent of `y_0, …, y_{t-1}`. -/
theorem predErr_hasLaw_indepFun (t : ℕ) :
    HasLaw (M.predErr x₀ w v t) (multivariateGaussian 0 (M.predCov t)) P ∧
      IndepFun (M.predErr x₀ w v t) (M.obsPrefix x₀ w v t) P := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · have hmap := TauCeti.Probability.map_affine_multivariateGaussian M.initMean
        h.initCov_posSemidef (1 : Matrix (Fin d) (Fin d) ℝ) (-M.initMean)
      simp only [Matrix.toLpLin_one, LinearMap.id_apply, add_neg_cancel, Matrix.one_mul,
        Matrix.transpose_one, Matrix.mul_one] at hmap
      have hc := HasLaw.comp (Y := fun x ↦ x + -M.initMean) ⟨by fun_prop, hmap⟩ h.hasLaw_init
      rw [show M.predCov 0 = M.initCov from rfl]
      convert hc using 1
      funext ω
      simp [predErr, state, predMean, sub_eq_add_neg]
    · have hc : M.obsPrefix x₀ w v 0 = fun _ ↦ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ (Fin p)) :=
        funext fun _ ↦ Subsingleton.elim _ _
      rw [hc]
      exact indepFun_const_right _ _
  | succ t ih =>
    obtain ⟨-, hlawf, hindf, -⟩ := h.measurement_update t ih.1 ih.2
    exact h.time_update t hlawf hindf

/-- Conditionally on `y_0, …, y_t`, the state `x_t` is Gaussian with the filtered mean and
covariance. -/
theorem condDistrib_state (t : ℕ) :
    ∀ᵐ ys ∂(P.map (M.obsPrefix x₀ w v (t + 1))),
      condDistrib (M.state x₀ w t) (M.obsPrefix x₀ w v (t + 1)) P ys =
        multivariateGaussian (M.filtMean (extendObservations ys) t) (M.filtCov t) := by
  obtain ⟨hlaw, hind⟩ := h.predErr_hasLaw_indepFun t
  obtain ⟨-, hlawf, hindf, -⟩ := h.measurement_update t hlaw hind
  have hx : M.state x₀ w t = fun ω ↦
      M.filtMean (extendObservations (M.obsPrefix x₀ w v (t + 1) ω)) t +
        M.filtErr x₀ w v t ω := by
    funext ω
    rw [M.filtMean_congr (y' := fun i ↦ M.obsProc x₀ w v i ω) fun i hi ↦ by
      simp [extendObservations_of_lt _ (Nat.lt_succ_of_le hi), obsPrefix]]
    simp [filtErr]
  rw [hx]
  exact condDistrib_add_eq_multivariateGaussian
    (M.measurable_filtMean_extendObservations (t + 1) t)
    (h.aemeasurable_indepFun_filtErr t).1.snd
    (M.filtCov_posSemidef h.stateCov_posSemidef h.obsCov_posSemidef h.initCov_posSemidef
      h.innovCov_det_ne_zero t) hlawf hindf.symm

/-- Conditionally on `y_0, …, y_t`, the state `x_{t+1}` is Gaussian with the predicted mean and
covariance. -/
theorem condDistrib_state_succ (t : ℕ) :
    ∀ᵐ ys ∂(P.map (M.obsPrefix x₀ w v (t + 1))),
      condDistrib (M.state x₀ w (t + 1)) (M.obsPrefix x₀ w v (t + 1)) P ys =
        multivariateGaussian (M.predMean (extendObservations ys) (t + 1))
          (M.predCov (t + 1)) := by
  obtain ⟨hlaw, hind⟩ := h.predErr_hasLaw_indepFun (t + 1)
  have hx : M.state x₀ w (t + 1) = fun ω ↦
      M.predMean (extendObservations (M.obsPrefix x₀ w v (t + 1) ω)) (t + 1) +
        M.predErr x₀ w v (t + 1) ω := by
    funext ω
    rw [M.predMean_congr (y' := fun i ↦ M.obsProc x₀ w v i ω) fun i hi ↦ by
      simp [extendObservations_of_lt _ hi, obsPrefix]]
    simp [predErr]
  rw [hx]
  exact condDistrib_add_eq_multivariateGaussian
    (M.measurable_predMean_extendObservations (t + 1) (t + 1))
    (h.aemeasurable_indepFun_predErr (t + 1)).1.snd (h.predCov_posSemidef' (t + 1)) hlaw
    hind.symm

/-- The innovation at time `t` has law `N(0, Σ_t)`. -/
theorem hasLaw_innovation (t : ℕ) :
    HasLaw (M.innovation x₀ w v t) (multivariateGaussian 0 (M.innovCov t)) P :=
  (h.measurement_update t (h.predErr_hasLaw_indepFun t).1 (h.predErr_hasLaw_indepFun t).2).1

/-- The innovation at time `t` is independent of `y_0, …, y_{t-1}`. -/
theorem indepFun_innovation_obsPrefix (t : ℕ) :
    IndepFun (M.innovation x₀ w v t) (M.obsPrefix x₀ w v t) P :=
  (h.measurement_update t (h.predErr_hasLaw_indepFun t).1
    (h.predErr_hasLaw_indepFun t).2).2.2.2

/-- The innovations are mutually independent. -/
theorem iIndepFun_innovation : iIndepFun (M.innovation x₀ w v) P := by
  refine iIndepFun_of_indepFun_finPrefix fun n ↦ ?_
  let Ψ : (Fin n → EuclideanSpace ℝ (Fin p)) → Fin n → EuclideanSpace ℝ (Fin p) :=
    fun ys i ↦ ys i - Matrix.toEuclideanLin (M.observation i)
      (M.predMean (extendObservations ys) i)
  have hΨ : Measurable Ψ := by
    refine measurable_pi_iff.mpr fun i ↦ (measurable_pi_apply i).sub ?_
    exact (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
      Matrix.toEuclideanLin (M.observation i) z).comp
      (M.measurable_predMean_extendObservations n i)
  have hpre : (fun ω (i : Fin n) ↦ M.innovation x₀ w v i ω) =
      Ψ ∘ M.obsPrefix x₀ w v n := by
    funext ω i
    have hpm : M.predMean (extendObservations (M.obsPrefix x₀ w v n ω)) i =
        M.predMean (fun j ↦ M.obsProc x₀ w v j ω) i :=
      M.predMean_congr fun j hj ↦ by simp [extendObservations_of_lt _ (hj.trans i.2), obsPrefix]
    simp only [Function.comp_apply, Ψ, innovation, hpm]
    rfl
  rw [hpre]
  exact (h.indepFun_innovation_obsPrefix n).symm.comp hΨ measurable_id

/-- The law of `(y_0, …, y_{n-1})` has density the product of the one-step predictive
densities. -/
theorem map_obsPrefix_eq_withDensity (n : ℕ) :
    P.map (M.obsPrefix x₀ w v n) = volume.withDensity (M.innovDensity n) := by
  induction n with
  | zero =>
    have hc : M.obsPrefix x₀ w v 0 = fun _ ↦ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ (Fin p)) :=
      funext fun _ ↦ Subsingleton.elim _ _
    have hd : M.innovDensity 0 = 1 := by
      funext ys
      simp [innovDensity]
    rw [hc, Measure.map_const, measure_univ, one_smul, hd, withDensity_one, volume_pi,
      Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    let g : (Fin n → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p) :=
      fun ys ↦ Matrix.toEuclideanLin (M.observation n) (M.predMean (extendObservations ys) n)
    have hg : Measurable g :=
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin d) ↦
        Matrix.toEuclideanLin (M.observation n) z).comp
        (M.measurable_predMean_extendObservations n n)
    have hPD := M.innovCov_posDef h.stateCov_posSemidef h.obsCov_posSemidef
      h.initCov_posSemidef h.innovCov_det_ne_zero n
    have hm : AEMeasurable (M.obsPrefix x₀ w v n) P := (h.aemeasurable_indepFun_predErr n).1.snd
    have hjoint := map_prodMk_add_eq_compProd hg hm hPD.posSemidef (h.hasLaw_innovation n)
      (h.indepFun_innovation_obsPrefix n).symm
    let f : (Fin n → EuclideanSpace ℝ (Fin p)) → EuclideanSpace ℝ (Fin p) → ℝ≥0∞ :=
      fun ys y ↦ TauCeti.Probability.multivariateGaussianPDF (g ys) (M.innovCov n) y
    have hq : Measurable fun q : (Fin n → EuclideanSpace ℝ (Fin p)) ×
        EuclideanSpace ℝ (Fin p) ↦ (g q.1, q.2) :=
      (hg.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (Function.uncurry f) := by
      have := (measurable_multivariateGaussianPDF_uncurry (M.innovCov n)).comp hq
      exact this
    have : IsSFiniteKernel ((Kernel.const (Fin n → EuclideanSpace ℝ (Fin p))
        (volume : Measure (EuclideanSpace ℝ (Fin p)))).withDensity f) :=
      Kernel.IsSFiniteKernel.withDensity _ fun _ _ ↦
        TauCeti.Probability.multivariateGaussianPDF_ne_top _ _ _
    have hκ : (gaussianShiftKernel (M.innovCov n)).comap g hg =
        (Kernel.const (Fin n → EuclideanSpace ℝ (Fin p))
          (volume : Measure (EuclideanSpace ℝ (Fin p)))).withDensity f := by
      ext1 ys
      rw [Kernel.comap_apply, gaussianShiftKernel_apply, Kernel.withDensity_apply _ hf,
        Kernel.const_apply, TauCeti.Probability.multivariateGaussian_eq_withDensity hPD]
    rw [hκ, ih, Measure.withDensity_compProd_withDensity (M.measurable_innovDensity n) hf,
      Measure.compProd_const] at hjoint
    let e : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) ≃ᵐ
        (Fin (n + 1) → EuclideanSpace ℝ (Fin p)) :=
      MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p)) (Fin.last n)).symm
    have he : ∀ q, e q = Fin.snoc q.1 q.2 := by
      intro q
      change (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p))
        (Fin.last n)).symm (q.2, q.1) = _
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
        Fin.insertNth_last']
    have hY : M.obsPrefix x₀ w v (n + 1) =
        e ∘ fun ω ↦ (M.obsPrefix x₀ w v n ω, g (M.obsPrefix x₀ w v n ω) +
          M.innovation x₀ w v n ω) := by
      funext ω
      rw [M.obsPrefix_succ_eq x₀ w v n ω, Function.comp_apply]
      change _ = (MeasurableEquiv.piFinSuccAbove (fun _ ↦ EuclideanSpace ℝ (Fin p))
        (Fin.last n)).symm (g (M.obsPrefix x₀ w v n ω) + M.innovation x₀ w v n ω,
          M.obsPrefix x₀ w v n ω)
      rw [add_comm (M.innovation x₀ w v n ω)]
    have hvol : (volume.prod volume : Measure ((Fin n → EuclideanSpace ℝ (Fin p)) ×
        EuclideanSpace ℝ (Fin p))).map e = volume := by
      have h₁ := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ (volume : Measure (EuclideanSpace ℝ (Fin p)))) (Fin.last n)).symm
      have h₂ := Measure.measurePreserving_swap (μ := (volume : Measure
        (Fin n → EuclideanSpace ℝ (Fin p)))) (ν := (volume : Measure (EuclideanSpace ℝ (Fin p))))
      exact (h₁.comp h₂).map_eq
    have hD : (fun q : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) ↦
        M.innovDensity n q.1 * f q.1 q.2) = M.innovDensity (n + 1) ∘ e := by
      funext q
      rw [Function.comp_apply, he, M.innovDensity_snoc]
    have hpm : AEMeasurable (fun ω ↦ (M.obsPrefix x₀ w v n ω, g (M.obsPrefix x₀ w v n ω) +
        M.innovation x₀ w v n ω)) P :=
      hm.prodMk ((hg.comp_aemeasurable hm).add (h.hasLaw_innovation n).aemeasurable)
    rw [hY, ← AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hpm,
      hjoint, hD, map_withDensity_comp_measurableEquiv _ e (M.measurable_innovDensity (n + 1)),
      hvol]

end GaussianInputs

end Filter

end KalmanModel

/-- GAPS 106.7: the Kalman filter for a finite-dimensional time-varying linear Gaussian
state-space model with positive-semidefinite noise and initial covariances, independent
Gaussian white noises independent of the Gaussian initial state, and nonsingular innovation
covariances. Conditionally on `y_0, …, y_t`, the state `x_t` is Gaussian with the filtered
mean and covariance and `x_{t+1}` with the predicted ones; the innovations
`y_t - H_t x_{t|t-1}` are independent with laws `N(0, Σ_t)`; and the density of
`(y_0, …, y_{n-1})` is the product of the one-step predictive densities. -/
theorem kalmanFilter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d p : ℕ} (M : KalmanModel d p) (hQ : ∀ t, (M.stateCov t).PosSemidef)
    (hR : ∀ t, (M.obsCov t).PosSemidef) (hP₀ : M.initCov.PosSemidef)
    (x₀ : Ω → EuclideanSpace ℝ (Fin d)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (v : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hx₀ : HasLaw x₀ (multivariateGaussian M.initMean M.initCov) P)
    (hw : ∀ t, HasLaw (w t) (multivariateGaussian 0 (M.stateCov t)) P)
    (hv : ∀ t, HasLaw (v t) (multivariateGaussian 0 (M.obsCov t)) P)
    (hwind : iIndepFun w P) (hvind : iIndepFun v P)
    (hwv : IndepFun (fun ω t ↦ w t ω) (fun ω t ↦ v t ω) P)
    (hx₀wv : IndepFun x₀ (fun ω t ↦ (w t ω, v t ω)) P)
    (hinnov : ∀ t, (M.innovCov t).det ≠ 0) :
    let x := M.state x₀ w
    let y := M.observationProcess x v
    let obs : (t : ℕ) → Ω → Fin (t + 1) → EuclideanSpace ℝ (Fin p) := fun t ω i ↦ y i ω
    let e : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun t ω ↦
      y t ω - Matrix.toEuclideanLin (M.observation t) (M.predMean (fun i ↦ y i ω) t)
    (∀ t, ∀ᵐ ys ∂(P.map (obs t)), condDistrib (x t) (obs t) P ys =
      multivariateGaussian (M.filtMean (extendObservations ys) t) (M.filtCov t)) ∧
    (∀ t, ∀ᵐ ys ∂(P.map (obs t)), condDistrib (x (t + 1)) (obs t) P ys =
      multivariateGaussian (M.predMean (extendObservations ys) (t + 1)) (M.predCov (t + 1))) ∧
    iIndepFun e P ∧
    (∀ t, HasLaw (e t) (multivariateGaussian 0 (M.innovCov t)) P) ∧
    ∀ n : ℕ, P.map (fun ω (i : Fin n) ↦ y i ω) =
      volume.withDensity fun ys : Fin n → EuclideanSpace ℝ (Fin p) ↦
        ∏ i : Fin n, TauCeti.Probability.multivariateGaussianPDF
          (Matrix.toEuclideanLin (M.observation i) (M.predMean (extendObservations ys) i))
          (M.innovCov i) (ys i) := by
  intro x y obs e
  have hG : M.GaussianInputs P x₀ w v :=
    ⟨hQ, hR, hP₀, hx₀, hw, hv, hwind, hvind, hwv, hx₀wv, hinnov⟩
  exact ⟨hG.condDistrib_state, hG.condDistrib_state_succ, hG.iIndepFun_innovation,
    hG.hasLaw_innovation, hG.map_obsPrefix_eq_withDensity⟩

end CKSD
