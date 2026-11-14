module

public import CKSD.LinearModels.Basic
public import CKSD.LinearModels.Regression
public import CKSD.Inference.Basic
public import TauCeti.Probability.Distributions.NoncentralF.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Convolution
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic

/-!
# The F test for nested Gaussian linear models

The nested Gaussian linear model: `Y ∼ N_n(μ, σ² I_n)` with `μ` in the range of a star
projection (orthogonal projection) `P₁`, and the smaller model `P₀ μ = μ` for a star projection
`P₀` with `P₁ P₀ = P₀`. Write `r₀ < r₁ < n` for the ranks.

## Main definitions

* `CKSD.nestedFStatistic`: `F = (‖P₁ Y - P₀ Y‖² / (r₁ - r₀)) / (‖Y - P₁ Y‖² / (n - r₁))`.
* `CKSD.IsNestedModelInvariantTest`: invariance under positive rescaling, translation within
  the range of `P₀`, and orthogonal maps commuting with `P₀` and `P₁`.

## Main results

* `CKSD.map_nestedFStatistic_eq_noncentralF`: under the larger model `F` has the noncentral F
  law with noncentrality `‖(P₁ - P₀) μ‖² / σ²` (TauCeti's `noncentralFMeasure`).
* `CKSD.map_nestedFStatistic_eq_fisherSnedecor`: under the smaller model `F` has Fisher's F law
  with `r₁ - r₀` and `n - r₁` degrees of freedom.
* `CKSD.strictMono_noncentralF_upper_tail`: the power `P(F > c)` is strictly increasing in the
  noncentrality.
* `CKSD.fTest_isUniformlyMostPowerful_invariant`: the F test is uniformly most powerful among
  invariant level-`α` tests.

The noncentral law uses TauCeti's shifted Gaussian squared-norm theorem together with the
residual law and the projection independence of `CKSD.LinearModels.Regression`. Strict power
monotonicity uses TauCeti's convolution and support theorems for noncentral chi-squared laws
and its independent-ratio characterization of the noncentral F law.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005,
  §7.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CKSD

/-- The squared length of a shifted finite-dimensional standard Gaussian has noncentral
chi-squared law. -/
theorem hasLaw_norm_sq_add_stdGaussian
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : Ω → E} (hX : HasLaw X (stdGaussian E) P) (m : E) :
    HasLaw (fun ω ↦ ‖m + X ω‖ ^ 2)
      (TauCeti.Probability.noncentralChiSquaredMeasure (Module.finrank ℝ E) (‖m‖₊ ^ 2)) P := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have he : HasLaw (fun ω ↦ e (X ω))
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) P :=
    (HasLaw.mk (by fun_prop) (stdGaussian_map e)).fun_comp hX
  have ha : HasLaw (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ↦ e m + z)
      (multivariateGaussian (e m) 1) (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    refine ⟨by fun_prop, ?_⟩
    have h := TauCeti.Probability.map_add_smul_multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (Matrix.PosSemidef.one) (e m) 1
    simpa only [multivariateGaussian_zero_one, one_smul, smul_zero, add_zero, one_pow] using h
  have h := (ha.fun_comp he).norm_sq_multivariateGaussian
  simpa only [← map_add, e.norm_map, e.nnnorm_map, Fintype.card_fin] using h

variable {n : ℕ}

/-- The F statistic of the nested projection models `P₀ ≤ P₁`. -/
def nestedFStatistic (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let r₀ := Module.finrank ℝ (LinearMap.range P₀.toLinearMap)
  let r₁ := Module.finrank ℝ (LinearMap.range P₁.toLinearMap)
  (‖P₁ x - P₀ x‖ ^ 2 / (r₁ - r₀ : ℕ)) / (‖x - P₁ x‖ ^ 2 / (n - r₁ : ℕ))

/-- A test is invariant under rescaling, translation within the smaller model space, and the
orthogonal maps that commute with both projections. -/
def IsNestedModelInvariantTest (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ (c : ℝ) x, 0 < c → φ (c • x) = φ x) ∧ (∀ x v, P₀ v = v → φ (x + v) = φ x) ∧
    ∀ O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, O (P₀ x) = P₀ (O x)) → (∀ x, O (P₁ x) = P₁ (O x)) → ∀ x, φ (O x) = φ x

/-- GAPS 105.16: under the larger model the F statistic has the noncentral F law with
`r₁ - r₀` and `n - r₁` degrees of freedom and noncentrality
`δ² = ‖(P₁ - P₀) μ‖² / σ²`; hence the power of any test based on it depends on `(μ, σ²)` only
through `δ²`. -/
theorem map_nestedFStatistic_eq_noncentralF
    (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP₀ : IsStarProjection P₀) (hP₁ : IsStarProjection P₁)
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x) (hm : P₁ m = m)
    (hr : Module.finrank ℝ (LinearMap.range P₀.toLinearMap) <
      Module.finrank ℝ (LinearMap.range P₁.toLinearMap))
    (hrn : Module.finrank ℝ (LinearMap.range P₁.toLinearMap) < n) :
    (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))).map
        (nestedFStatistic P₀ P₁) =
      TauCeti.Probability.noncentralFMeasure
        (Module.finrank ℝ (LinearMap.range P₁.toLinearMap) -
          Module.finrank ℝ (LinearMap.range P₀.toLinearMap) : ℕ)
        (n - Module.finrank ℝ (LinearMap.range P₁.toLinearMap) : ℕ)
        (Real.toNNReal (‖P₁ m - P₀ m‖ ^ 2 / v)) := by
  let r₀ := Module.finrank ℝ (LinearMap.range P₀.toLinearMap)
  let r₁ := Module.finrank ℝ (LinearMap.range P₁.toLinearMap)
  let G := multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hid : ∀ x, P₀ (P₀ x) = P₀ x ∧ P₁ (P₁ x) = P₁ x := fun x ↦
    ⟨IsStarProjection.apply_apply hP₀ x, IsStarProjection.apply_apply hP₁ x⟩
  have hsym : ∀ x y, inner ℝ (P₀ x) y = inner ℝ x (P₀ y) ∧
      inner ℝ (P₁ x) y = inner ℝ x (P₁ y) := fun x y ↦
    ⟨IsStarProjection.inner_map_left hP₀ x y, IsStarProjection.inner_map_left hP₁ x y⟩
  have hcomm : ∀ x, P₀ (P₁ x) = P₀ x := by
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [(hsym (P₁ x) y).1, (hsym x (P₀ y)).2, hnest, ← (hsym x y).1]
  let K₀ := LinearMap.range P₀.toLinearMap
  let K₁ := LinearMap.range P₁.toLinearMap
  let S := K₀ᗮ ⊓ K₁
  have hle : K₀ ≤ K₁ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨P₀ x, hnest x⟩
  have hSdim : Module.finrank ℝ S = r₁ - r₀ := by
    have h := Submodule.finrank_add_inf_finrank_orthogonal hle
    change r₀ + Module.finrank ℝ S = r₁ at h
    omega
  have hP₁' : ∀ x, K₁.starProjection x = P₁ x := IsStarProjection.starProjection_range_apply hP₁
  have hS : ∀ x, S.starProjection x = P₁ x - P₀ x := by
    intro x
    refine S.eq_starProjection_of_mem_of_inner_eq_zero ⟨?_, ?_⟩ ?_
    · refine (Submodule.mem_orthogonal' K₀ _).mpr ?_
      rintro _ ⟨y, rfl⟩
      change inner ℝ (P₁ x - P₀ x) (P₀ y) = 0
      rw [inner_sub_left, ← (hsym (P₁ x) y).1, ← (hsym (P₀ x) y).1, hcomm, (hid x).1, sub_self]
    · refine ⟨x - P₀ x, ?_⟩
      change P₁ (x - P₀ x) = P₁ x - P₀ x
      rw [map_sub, hnest]
    · intro y hy
      have hy₀ := (Submodule.mem_orthogonal' K₀ y).mp hy.1 (P₀ x) ⟨x, rfl⟩
      have hy₁ := K₁.starProjection_inner_eq_zero x y hy.2
      rw [hP₁'] at hy₁
      rw [inner_sub_left, inner_sub_left]
      have hy₀' : inner ℝ (P₀ x) y = 0 := by
        rw [real_inner_comm]
        exact hy₀
      rw [hy₀']
      simpa only [inner_sub_left, sub_zero] using hy₁
  set t := Real.sqrt (v : ℝ)
  have ht2 : t ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  let Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x ↦ t⁻¹ • (x - m)
  have hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))) G :=
    hasLaw_smul_sub_multivariateGaussian m v hv
  let a : S := S.orthogonalProjectionOnto (t⁻¹ • m)
  have hvec : ∀ x, ((a + S.orthogonalProjectionOnto (Z x) : S) : EuclideanSpace ℝ (Fin n)) =
      t⁻¹ • (P₁ x - P₀ x) := by
    intro x
    change S.starProjection (t⁻¹ • m) + S.starProjection (Z x) = _
    rw [← map_add]
    have hz : t⁻¹ • m + Z x = t⁻¹ • x := by dsimp [Z]; module
    rw [hz, map_smul, hS]
  have hNS : ∀ x, ‖a + S.orthogonalProjectionOnto (Z x)‖ ^ 2 = ‖P₁ x - P₀ x‖ ^ 2 / v := by
    intro x
    change ‖((a + S.orthogonalProjectionOnto (Z x) : S) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = _
    rw [hvec, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, ht2, div_eq_inv_mul]
  have hnc : ‖a‖₊ ^ 2 = Real.toNNReal (‖P₁ m - P₀ m‖ ^ 2 / v) := by
    apply NNReal.eq
    rw [NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    simpa [Z] using hNS m
  have hnum := hasLaw_norm_sq_add_stdGaussian (hZ.orthogonalProjectionOnto_stdGaussian S) a
  simp only [hNS, hSdim, hnc] at hnum
  have hden : HasLaw (fun x ↦ ‖x - P₁ x‖ ^ 2 / v)
      (TauCeti.Probability.chiSquaredMeasure (n - r₁ : ℕ)) G :=
    ⟨by fun_prop, map_norm_sq_sub_div_eq_chiSquared m v hv P₁ hP₁ hm⟩
  have hi := (indepFun_map_norm_sq_sub m v hv P₁ hP₁).comp (φ := fun z ↦ ‖z - P₀ z‖ ^ 2 / v)
    (ψ := fun z : ℝ ↦ z / v) (by fun_prop) (by fun_prop)
  change IndepFun (fun x ↦ ‖P₁ x - P₀ (P₁ x)‖ ^ 2 / v)
    (fun x ↦ ‖x - P₁ x‖ ^ 2 / v) G at hi
  simp only [hcomm] at hi
  have h := TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared
    (by exact_mod_cast Nat.sub_pos_of_lt hr) (by exact_mod_cast Nat.sub_pos_of_lt hrn)
    hi hnum hden
  have hpt : (fun x ↦ (‖P₁ x - P₀ x‖ ^ 2 / v) / (r₁ - r₀ : ℕ) /
      ((‖x - P₁ x‖ ^ 2 / v) / (n - r₁ : ℕ))) = nestedFStatistic P₀ P₁ := by
    funext x
    dsimp [nestedFStatistic]
    rw [div_right_comm (‖P₁ x - P₀ x‖ ^ 2) (v : ℝ) (r₁ - r₀ : ℕ),
      div_right_comm (‖x - P₁ x‖ ^ 2) (v : ℝ) (n - r₁ : ℕ), div_div_div_cancel_right₀ hv']
  rw [hpt] at h
  exact h.map_eq

/-- GAPS 105.10, exact null F law for nested Gaussian projection models: for
`Y ∼ N(m, v I_n)` with `v > 0` and `m` in the range of the smaller star projection `P₀`, where
`P₁ P₀ = P₀` and `rank P₀ < rank P₁ < n`, the F statistic
`(‖P₁ Y - P₀ Y‖² / (r₁ - r₀)) / (‖Y - P₁ Y‖² / (n - r₁))` has Fisher's F law with
`r₁ - r₀` and `n - r₁` degrees of freedom. This is the case of zero noncentrality of
`map_nestedFStatistic_eq_noncentralF`. -/
theorem map_nestedFStatistic_eq_fisherSnedecor
    (m : EuclideanSpace ℝ (Fin n)) (v : ℝ≥0) (hv : 0 < v)
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP₀ : IsStarProjection P₀) (hP₁ : IsStarProjection P₁)
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x) (hm : P₀ m = m)
    (hr : Module.finrank ℝ (LinearMap.range P₀.toLinearMap) <
      Module.finrank ℝ (LinearMap.range P₁.toLinearMap))
    (hrn : Module.finrank ℝ (LinearMap.range P₁.toLinearMap) < n) :
    (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))).map
        (nestedFStatistic P₀ P₁) =
      TauCeti.Probability.fisherSnedecorMeasure
        (Module.finrank ℝ (LinearMap.range P₁.toLinearMap) -
          Module.finrank ℝ (LinearMap.range P₀.toLinearMap) : ℕ)
        (n - Module.finrank ℝ (LinearMap.range P₁.toLinearMap) : ℕ) := by
  have hm₁ : P₁ m = m := by
    calc P₁ m = P₁ (P₀ m) := by rw [hm]
      _ = m := by rw [hnest, hm]
  rw [map_nestedFStatistic_eq_noncentralF m v hv P₀ P₁ hP₀ hP₁ hnest hm₁ hr hrn, hm₁, hm,
    sub_self, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Real.toNNReal_zero]
  exact TauCeti.Probability.noncentralFMeasure_zero_noncentrality _ _

/-- GAPS 105.16: the power `P(F > c)` of the F test with critical value `c > 0` is strictly
increasing in the noncentrality `δ²`. -/
theorem strictMono_noncentralF_upper_tail (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (c : ℝ)
    (hc : 0 < c) :
    StrictMono fun l : ℝ≥0 ↦ (TauCeti.Probability.noncentralFMeasure d₁ d₂ l).real (Ioi c) := by
  intro a b hab
  let μ := TauCeti.Probability.noncentralChiSquaredMeasure d₁ a
  let ν := TauCeti.Probability.noncentralChiSquaredMeasure 0 (b - a)
  let D := TauCeti.Probability.chiSquaredMeasure d₂
  let R := (μ.prod ν).prod D
  let _ := TauCeti.Probability.isProbabilityMeasure_noncentralChiSquaredMeasure hd₁.le a
  let _ := TauCeti.Probability.isProbabilityMeasure_noncentralChiSquaredMeasure (k := 0) (by norm_num) (b - a)
  let _ := TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure hd₂.le
  let U : (ℝ × ℝ) × ℝ → ℝ := fun z ↦ z.1.1
  let V : (ℝ × ℝ) × ℝ → ℝ := fun z ↦ z.1.1 + z.1.2
  let W : (ℝ × ℝ) × ℝ → ℝ := Prod.snd
  have hU : HasLaw U μ R :=
    measurePreserving_fst.hasLaw.fun_comp measurePreserving_fst.hasLaw
  have hW : HasLaw W D R := measurePreserving_snd.hasLaw
  -- TauCeti's convolution theorem supplies the coupled larger numerator.
  have hsum : HasLaw (fun z : ℝ × ℝ ↦ z.1 + z.2)
      (TauCeti.Probability.noncentralChiSquaredMeasure d₁ b) (μ.prod ν) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.conv, TauCeti.Probability.noncentralChiSquaredMeasure_conv_noncentralChiSquaredMeasure
      hd₁.le (by norm_num), add_zero, add_tsub_cancel_of_le hab.le]
  have hV : HasLaw V (TauCeti.Probability.noncentralChiSquaredMeasure d₁ b) R :=
    hsum.fun_comp measurePreserving_fst.hasLaw
  have hUW : IndepFun U W R := indepFun_prod measurable_fst measurable_id
  have hVW : IndepFun V W R := indepFun_prod (X := fun z : ℝ × ℝ ↦ z.1 + z.2) (by fun_prop) measurable_id
  have hA := TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared hd₁ hd₂ hUW hU hW
  have hB := TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared hd₁ hd₂ hVW hV hW
  let A : Set ((ℝ × ℝ) × ℝ) := {z | c < U z / d₁ / (W z / d₂)}
  let B : Set ((ℝ × ℝ) × ℝ) := {z | c < V z / d₁ / (W z / d₂)}
  have hAB : A ≤ᵐ[R] B := by
    have hν : ∀ᵐ z ∂R, 0 ≤ z.1.2 :=
      measurePreserving_snd.quasiMeasurePreserving.ae
        (TauCeti.Probability.ae_nonneg_noncentralChiSquaredMeasure 0 (b - a)) |>
        measurePreserving_fst.quasiMeasurePreserving.ae
    have hD : ∀ᵐ z ∂R, 0 < z.2 :=
      measurePreserving_snd.quasiMeasurePreserving.ae
        (TauCeti.Probability.ae_pos_chiSquaredMeasure hd₂)
    filter_upwards [hν, hD] with z hzν hzD
    intro hz
    exact hz.trans_le (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hzν) hd₁.le)
      (div_nonneg hzD.le hd₂.le))
  -- A positive product box crosses the cutoff strictly when the increment is added.
  let E : Set ((ℝ × ℝ) × ℝ) :=
    (Ioo 0 (d₁ * c / 2) ×ˢ Ioo (2 * d₁ * c) (3 * d₁ * c)) ×ˢ Ioo d₂ (2 * d₂)
  have hE : MeasurableSet E := (measurableSet_Ioo.prod measurableSet_Ioo).prod measurableSet_Ioo
  have hμpos : 0 < μ (Ioo 0 (d₁ * c / 2)) := by
    apply (Measure.mem_support_iff_forall (d₁ * c / 4)).1 ?_ _
      (Ioo_mem_nhds (by positivity) (by nlinarith [mul_pos hd₁ hc]))
    simp [μ, TauCeti.Probability.support_noncentralChiSquaredMeasure, hd₁.ne', not_lt.mpr hd₁.le]
    positivity
  have hνpos : 0 < ν (Ioo (2 * d₁ * c) (3 * d₁ * c)) := by
    apply (Measure.mem_support_iff_forall (5 * d₁ * c / 2)).1 ?_ _
      (Ioo_mem_nhds (by nlinarith [mul_pos hd₁ hc]) (by nlinarith [mul_pos hd₁ hc]))
    simp [ν, TauCeti.Probability.support_noncentralChiSquaredMeasure, tsub_pos_iff_lt.mpr hab |>.ne']
    positivity
  have hDpos : 0 < D (Ioo d₂ (2 * d₂)) := by
    apply (Measure.mem_support_iff_forall (3 * d₂ / 2)).1 ?_ _
      (Ioo_mem_nhds (by linarith) (by linarith))
    simp [D, TauCeti.Probability.support_chiSquaredMeasure, hd₂, hd₂.ne']
    positivity
  have hEpos : 0 < R.real E := by
    apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
    change 0 < ((μ.prod ν).prod D) _
    rw [Measure.prod_prod, Measure.prod_prod]
    exact ENNReal.mul_pos (ENNReal.mul_pos hμpos.ne' hνpos.ne').ne' hDpos.ne'
  have hEA : Disjoint A E := by
    rw [Set.disjoint_left]
    intro z hz hzE
    change c < z.1.1 / d₁ / (z.2 / d₂) at hz
    rcases hzE with ⟨⟨⟨hu0, hu⟩, hv⟩, hz2⟩
    have hden : 0 < z.2 / d₂ := div_pos (hd₂.trans hz2.1) hd₂
    rw [lt_div_iff₀ hden, lt_div_iff₀ hd₁] at hz
    have hratio : 1 < z.2 / d₂ := (lt_div_iff₀ hd₂).2 (by simpa using hz2.1)
    nlinarith [mul_pos hd₁ hc, mul_pos (mul_pos hd₁ hc) (sub_pos.mpr hratio)]
  have hEB : E ⊆ B := by
    intro z hz
    change c < (z.1.1 + z.1.2) / d₁ / (z.2 / d₂)
    have hden : 0 < z.2 / d₂ := div_pos (hd₂.trans hz.2.1) hd₂
    rw [lt_div_iff₀ hden, lt_div_iff₀ hd₁]
    have hratio : z.2 / d₂ < 2 := (div_lt_iff₀ hd₂).2 (by simpa using hz.2.2)
    rcases hz with ⟨⟨⟨hu0, hu⟩, ⟨hv0, hv⟩⟩, hd⟩
    nlinarith [mul_pos hd₁ hc, mul_pos (mul_pos hd₁ hc) (sub_pos.mpr hratio)]
  have hle : R.real (A ∪ E) ≤ R.real B := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hAB] with z hz
    exact fun hz' ↦ hz'.elim hz (hEB ·)
  rw [measureReal_union hEA hE] at hle
  have hAr : R.real A = (TauCeti.Probability.noncentralFMeasure d₁ d₂ a).real (Ioi c) :=
    hA.measureReal_eq measurableSet_Ioi
  have hBr : R.real B = (TauCeti.Probability.noncentralFMeasure d₁ d₂ b).real (Ioi c) :=
    hB.measureReal_eq measurableSet_Ioi
  rw [hAr, hBr] at hle
  linarith

/-- GAPS 105.16: among level-`α` tests invariant under rescaling, translation within the
smaller model space, and orthogonal maps of the hypothesis and residual spaces, the F test
with critical value `c` (the upper `α` point of the central F law) is uniformly most powerful.
The parameter is `(μ, σ²)` with `P₁ μ = μ` and `σ² > 0`; the null hypothesis is `P₀ μ = μ`.
The level `α` is defined by the critical value `c`; for `c ≤ 0` it equals `1` and the
statement is trivial, so no restriction `0 < α < 1` is imposed. The average-power optimality
among similar tests is not stated. -/
theorem fTest_isUniformlyMostPowerful_invariant
    (P₀ P₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP₀ : IsStarProjection P₀) (hP₁ : IsStarProjection P₁)
    (hnest : ∀ x, P₁ (P₀ x) = P₀ x)
    (hr : Module.finrank ℝ (LinearMap.range P₀.toLinearMap) <
      Module.finrank ℝ (LinearMap.range P₁.toLinearMap))
    (hrn : Module.finrank ℝ (LinearMap.range P₁.toLinearMap) < n) (α c : ℝ)
    (hc : (TauCeti.Probability.fisherSnedecorMeasure
        (Module.finrank ℝ (LinearMap.range P₁.toLinearMap) -
          Module.finrank ℝ (LinearMap.range P₀.toLinearMap) : ℕ)
        (n - Module.finrank ℝ (LinearMap.range P₁.toLinearMap) : ℕ)).real (Ioi c) = α) :
    let law := fun θ : EuclideanSpace ℝ (Fin n) × ℝ≥0 ↦
      multivariateGaussian θ.1 ((θ.2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
    let H₀ := {θ : EuclideanSpace ℝ (Fin n) × ℝ≥0 | P₁ θ.1 = θ.1 ∧ P₀ θ.1 = θ.1 ∧ 0 < θ.2}
    let H₁ := {θ : EuclideanSpace ℝ (Fin n) × ℝ≥0 | P₁ θ.1 = θ.1 ∧ P₀ θ.1 ≠ θ.1 ∧ 0 < θ.2}
    let φ := fun x ↦ if c < nestedFStatistic P₀ P₁ x then (1 : ℝ) else 0
    IsStatisticalTest φ ∧ IsNestedModelInvariantTest P₀ P₁ φ ∧
      (∀ θ ∈ H₀, (∫ x, φ x ∂law θ) = α) ∧
      ∀ ψ, IsStatisticalTest ψ → IsNestedModelInvariantTest P₀ P₁ ψ →
        (∀ θ ∈ H₀, (∫ x, ψ x ∂law θ) ≤ α) →
        ∀ θ ∈ H₁, (∫ x, ψ x ∂law θ) ≤ ∫ x, φ x ∂law θ := by
  sorry

end CKSD
