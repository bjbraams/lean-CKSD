module

public import CKSD.Learning.PrivateEstimation.CentralLowerBounds

/-!
# Local private mean estimation

Noninteractive local privacy contracts Bernoulli alternatives. A clipped Laplace release
achieves a matching upper bound for the mean risk. Source: GAPS 107.66.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

/-! ### Two-point lower bounds for the local mean risk -/

/-- The total variation distance between `Ber(1, 0, a)` and `Ber(1, 0, b)` is at most
`|a - b|`. -/
theorem totalVariationDistance_bernoulliMeasure_le (a b : unitInterval) :
    totalVariationDistance (Ber((1 : ℝ), 0, a)) (Ber((1 : ℝ), 0, b)) ≤ |(a : ℝ) - b| := by
  unfold totalVariationDistance
  refine csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  rw [bernoulliMeasure_real_apply a hA, bernoulliMeasure_real_apply b hA]
  split_ifs
  · simp
  · simp
  · simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    rw [abs_sub_comm]
    ring_nf
    exact le_refl _
  · simp

/-- A lower bound for the local mean risk on a set of estimates far from the mean. -/
theorem ofReal_mul_map_le_localMeanRisk {n : ℕ} (Q : Fin n → Kernel ℝ ℝ)
    {est : (Fin n → ℝ) → ℝ} (hest : Measurable est) (P : Measure ℝ) {B : Set ℝ}
    (hB : MeasurableSet B) {r : ℝ} (hr : ∀ y ∈ B, r ≤ (y - ∫ x, x ∂P) ^ 2) :
    ENNReal.ofReal r * ((Measure.pi fun i ↦ Q i ∘ₘ P).map est) B ≤ localMeanRisk Q est P := by
  rw [Measure.map_apply hest hB, ← lintegral_indicator_const (hest hB)]
  unfold localMeanRisk
  refine lintegral_mono fun z ↦ ?_
  by_cases hz : z ∈ est ⁻¹' B
  · rw [indicator_of_mem hz]
    exact ENNReal.ofReal_le_ofReal (hr _ hz)
  · rw [indicator_of_notMem hz]
    exact zero_le

/-- The lower half of the local minimax rate: for `ε`-locally private release kernels and a
measurable estimator, some Bernoulli law `Ber(1, 0, p)` has mean squared error at least
`min(1, 1/(nε²)) / 768`. The two laws are `Ber(1/2)` and `Ber(1/2 + δ)` with
`δ = min(1/2, 1/(4ε√n))`; the release laws of one individual are at Kullback–Leibler
divergence at most `16 ε² δ²` by the contraction under local privacy (GAPS 107.75,
`klDiv_comp_le_of_local_differential_privacy`), and Le Cam's method concludes as in the
central case. -/
theorem exists_bernoulli_localMeanRisk_ge {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (Q : Fin n → Kernel ℝ ℝ) (hQ : ∀ i, IsMarkovKernel (Q i))
    (hpriv : ∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i))
    (est : (Fin n → ℝ) → ℝ) (hest : Measurable est) :
    ∃ p : unitInterval, ENNReal.ofReal (min 1 (1 / (n * ε ^ 2)) / 768) ≤
      localMeanRisk Q est (Ber((1 : ℝ), 0, p)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hε0 := hε.1
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnr
  set δ : ℝ := min (1 / 2) (1 / (4 * ε * Real.sqrt n)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : 16 * n * ε ^ 2 * δ ^ 2 ≤ 1 := by
    have h1 : δ ≤ 1 / (4 * ε * Real.sqrt n) := min_le_right _ _
    have h2 : δ ^ 2 ≤ (1 / (4 * ε * Real.sqrt n)) ^ 2 := pow_le_pow_left₀ hδ0.le h1 2
    have h3 : (1 / (4 * ε * Real.sqrt n)) ^ 2 = 1 / (16 * n * ε ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le]; ring
    rw [h3] at h2
    calc 16 * n * ε ^ 2 * δ ^ 2 ≤ 16 * n * ε ^ 2 * (1 / (16 * n * ε ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by field_simp
  have hδm : min 1 (1 / (n * ε ^ 2)) / 16 ≤ δ ^ 2 := by
    rcases min_choice (1 / 2 : ℝ) (1 / (4 * ε * Real.sqrt n)) with h | h
    · rw [← hδ_def] at h; rw [h]
      have := min_le_left (1 : ℝ) (1 / (n * ε ^ 2)); linarith
    · rw [← hδ_def] at h; rw [h, div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le]
      have := min_le_right (1 : ℝ) (1 / (n * ε ^ 2))
      calc min 1 (1 / (n * ε ^ 2)) / 16 ≤ 1 / (n * ε ^ 2) / 16 := by linarith
        _ = 1 ^ 2 / (4 ^ 2 * ε ^ 2 * n) := by field_simp; ring
  set a : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  set b : unitInterval := ⟨1 / 2 + δ, by positivity, by linarith⟩
  have ha : (a : ℝ) = 1 / 2 := rfl
  have hb : (b : ℝ) = 1 / 2 + δ := rfl
  have hab : (a : ℝ) < b := by rw [ha, hb]; linarith
  have : ∀ i, IsMarkovKernel (Q i) := hQ
  set μa := Measure.pi fun i ↦ Q i ∘ₘ Ber((1 : ℝ), 0, a)
  set μb := Measure.pi fun i ↦ Q i ∘ₘ Ber((1 : ℝ), 0, b)
  set A : Set ℝ := {y | ((a + b : ℝ)) / 2 ≤ y}
  have hA : MeasurableSet A := measurableSet_Ici
  -- divergence of one release
  have hKLi : ∀ i, InformationTheory.klDiv (Q i ∘ₘ Ber((1 : ℝ), 0, b))
      (Q i ∘ₘ Ber((1 : ℝ), 0, a)) ≤ ENNReal.ofReal (16 * ε ^ 2 * δ ^ 2) := by
    intro i
    have h := klDiv_comp_le_of_local_differential_privacy (Q i) ε (hpriv i)
      (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a))
    refine le_trans le_self_add (h.trans (ENNReal.ofReal_le_ofReal ?_))
    have hTV := totalVariationDistance_bernoulliMeasure_le b a
    have hTV0 : 0 ≤ totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) :=
      Real.sSup_nonneg (by rintro _ ⟨A, -, rfl⟩; exact abs_nonneg _)
    rw [hb, ha, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring, abs_of_pos hδ0] at hTV
    have he : Real.exp ε - 1 ≤ 2 * ε := by
      have := Real.abs_exp_sub_one_le (x := ε) (by rw [abs_of_pos hε0]; exact hε.2)
      rw [abs_of_pos hε0] at this
      exact (le_abs_self _).trans this
    have he0 : 0 ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
    have h1 : (Real.exp ε - 1) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ he0 he 2
    have h2 : totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) ^ 2 ≤ δ ^ 2 :=
      pow_le_pow_left₀ hTV0 hTV 2
    calc 4 * (Real.exp ε - 1) ^ 2 *
          totalVariationDistance (Ber((1 : ℝ), 0, b)) (Ber((1 : ℝ), 0, a)) ^ 2
        ≤ 4 * (2 * ε) ^ 2 * δ ^ 2 := by gcongr
      _ = 16 * ε ^ 2 * δ ^ 2 := by ring
  have hKL : InformationTheory.klDiv μb μa ≤ ENNReal.ofReal 1 := by
    rw [klDiv_pi]
    calc ∑ i, InformationTheory.klDiv (Q i ∘ₘ Ber((1 : ℝ), 0, b)) (Q i ∘ₘ Ber((1 : ℝ), 0, a))
        ≤ ∑ _i : Fin n, ENNReal.ofReal (16 * ε ^ 2 * δ ^ 2) := Finset.sum_le_sum fun i _ ↦ hKLi i
      _ = ENNReal.ofReal (n * (16 * ε ^ 2 * δ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by nlinarith)
  have hKLne : InformationTheory.klDiv μb μa ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hKLr : (InformationTheory.klDiv μb μa).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    rwa [ENNReal.toReal_ofReal zero_le_one] at this
  have hBH := exp_neg_klDiv_le_two_sub_tvDist μb μa hKLne
  have hexp : Real.exp (-1) ≤ Real.exp (-(InformationTheory.klDiv μb μa).toReal) :=
    Real.exp_le_exp.mpr (by linarith)
  have hTV := tvDist_map_le μb μa hest
  have htest : 1 / 6 ≤ (μa.map est).real A + (μb.map est).real Aᶜ :=
    one_div_six_le_measureReal_add_measureReal_compl (by linarith) hA
  have hLa := ofReal_mul_map_le_localMeanRisk Q hest (Ber((1 : ℝ), 0, a)) hA
    (r := ((b - a : ℝ) / 2) ^ 2) fun y hy ↦ by
      rw [integral_id_bernoulliMeasure_one_zero]
      simp only [A, Set.mem_ofPred_eq] at hy
      nlinarith
  have hLb := ofReal_mul_map_le_localMeanRisk Q hest (Ber((1 : ℝ), 0, b)) hA.compl
    (r := ((b - a : ℝ) / 2) ^ 2) fun y hy ↦ by
      rw [integral_id_bernoulliMeasure_one_zero]
      simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
      nlinarith
  have hsum : ENNReal.ofReal (δ ^ 2 / 24) ≤
      localMeanRisk Q est (Ber((1 : ℝ), 0, a)) + localMeanRisk Q est (Ber((1 : ℝ), 0, b)) := by
    refine le_trans ?_ (add_le_add hLa hLb)
    rw [← mul_add, ← ofReal_measureReal (measure_ne_top (μa.map est) A),
      ← ofReal_measureReal (measure_ne_top (μb.map est) Aᶜ),
      ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [ha, hb, show (1 / 2 + δ - 1 / 2 : ℝ) = δ by ring]
    calc δ ^ 2 / 24 = (δ / 2) ^ 2 * (1 / 6) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (by positivity)
  have hfin : ∀ x : ℝ≥0∞, ENNReal.ofReal (δ ^ 2 / 24 / 2) ≤ x →
      ENNReal.ofReal (min 1 (1 / (n * ε ^ 2)) / 768) ≤ x := fun x hx ↦
    le_trans (ENNReal.ofReal_le_ofReal (by nlinarith)) hx
  rcases ofReal_half_le_or_of_ofReal_le_add hsum with h | h
  · exact ⟨a, hfin _ h⟩
  · exact ⟨b, hfin _ h⟩

/-- The local Laplace release kernel: clip to `[-1,1]` and add Laplace noise of scale `2/ε`. -/
def localLaplaceKernel (ε : ℝ) : Kernel ℝ ℝ where
  toFun x := TauCeti.Probability.laplaceMeasure (clipUnit x) (2 / ε : ℝ)
  measurable' := by
    exact TauCeti.Probability.measurable_laplaceMeasure.comp
      (f := fun x : ℝ ↦ (clipUnit x, (2 / ε : ℝ))) (measurable_clipUnit.prodMk measurable_const)

/-- The local Laplace release kernel is a Markov kernel for positive `ε`. -/
theorem isMarkovKernel_localLaplaceKernel {ε : ℝ} (hε : 0 < ε) :
    IsMarkovKernel (localLaplaceKernel ε) :=
  ⟨fun _ ↦ TauCeti.Probability.isProbabilityMeasure_laplaceMeasure (by positivity) _⟩

/-- GAPS 107.66: the local Laplace release kernel is `ε`-locally differentially private. -/
theorem isDifferentiallyPrivate_localLaplaceKernel {ε : ℝ} (hε : 0 < ε) :
    IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (localLaplaceKernel ε) := by
  refine isDifferentiallyPrivate_of_eq_laplaceMeasure _ _ clipUnit (by positivity)
    (fun _ ↦ rfl) fun x x' _ ↦ ?_
  have h1 := clipUnit_mem_Icc x
  have h2 := clipUnit_mem_Icc x'
  calc |clipUnit x - clipUnit x'| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    _ = ε * (2 / ε) := by field_simp

/-- Under a law supported by `[-1,1]`, the squared deviation of a local Laplace release from
the mean has lower integral at most `4 + 8/ε²`. -/
theorem lintegral_sq_sub_localLaplace_le {ε : ℝ} (hε : 0 < ε) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    ∫⁻ y, ENNReal.ofReal ((y - ∫ x, x ∂P) ^ 2) ∂(localLaplaceKernel ε ∘ₘ P) ≤
      ENNReal.ofReal (4 + 8 / ε ^ 2) := by
  set θ := ∫ x, x ∂P
  set b : ℝ := 2 / ε with hb_def
  have hb : 0 < b := by positivity
  have hθ := abs_integral_le_one_of_support P hP
  rw [abs_le] at hθ
  have hclip := clipUnit_mem_Icc
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) (by fun_prop)]
  have hinner : ∀ x, ∫⁻ y, ENNReal.ofReal ((y - θ) ^ 2) ∂localLaplaceKernel ε x =
      ENNReal.ofReal ((clipUnit x - θ) ^ 2 + 2 * b ^ 2) := fun x ↦ by
    have hI : Integrable (fun y ↦ (y - θ) ^ 2) (localLaplaceKernel ε x) :=
      integrable_sq_sub_laplaceMeasure hb _ _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact congrArg _ (integral_sq_sub_laplaceMeasure hb _ _)
  simp_rw [hinner]
  calc ∫⁻ x, ENNReal.ofReal ((clipUnit x - θ) ^ 2 + 2 * b ^ 2) ∂P
      ≤ ∫⁻ _x, ENNReal.ofReal (4 + 8 / ε ^ 2) ∂P := by
        refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
        have h := hclip x
        have h2 : 2 * b ^ 2 = 8 / ε ^ 2 := by rw [hb_def]; field_simp; ring
        nlinarith [h.1, h.2]
    _ = ENNReal.ofReal (4 + 8 / ε ^ 2) := by simp

/-- Under a law supported by `[-1,1]`, a local Laplace release has mean equal to the mean of
the law. -/
theorem integral_id_localLaplace {ε : ℝ} (hε : 0 < ε) (P : Measure ℝ)
    (hP : P (Icc (-1) 1)ᶜ = 0)
    (hint : Integrable (fun y : ℝ ↦ y) (localLaplaceKernel ε ∘ₘ P)) :
    ∫ y, y ∂(localLaplaceKernel ε ∘ₘ P) = ∫ x, x ∂P := by
  have hb : 0 < 2 / ε := by positivity
  have hae : ∀ᵐ x ∂P, clipUnit x = x := by
    have hmem : ∀ᵐ x ∂P, x ∈ Icc (-1 : ℝ) 1 := measure_eq_zero_iff_ae_notMem.mp hP |>.mono
      fun x hx ↦ by simpa using hx
    filter_upwards [hmem] with x hx
    exact clipUnit_of_mem hx
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint]
  simp only [Kernel.const_apply]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  change ∫ y, y ∂TauCeti.Probability.laplaceMeasure (clipUnit x) (2 / ε) = x
  rw [TauCeti.Probability.integral_id_laplaceMeasure, hx]
  exact hb

/-- GAPS 107.66: on laws supported by `[-1,1]`, the sample mean of local Laplace releases has
mean squared error at most `(4 + 8/ε²)/n`. -/
theorem localMeanRisk_localLaplace_mean_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P (Icc (-1) 1)ᶜ = 0) :
    localMeanRisk (fun _ : Fin n ↦ localLaplaceKernel ε) (fun z ↦ (∑ i, z i) / n) P ≤
      ENNReal.ofReal ((4 + 8 / ε ^ 2) / n) := by
  have := isMarkovKernel_localLaplaceKernel hε
  set L : Measure ℝ := localLaplaceKernel ε ∘ₘ P with hL
  set θ := ∫ x, x ∂P
  set π : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ L
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlin := lintegral_sq_sub_localLaplace_le hε P hP
  have hsqI : Integrable (fun y : ℝ ↦ (y - θ) ^ 2) L := by
    refine ⟨(by fun_prop : Measurable fun y : ℝ ↦ (y - θ) ^ 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hL2 : MemLp (fun y : ℝ ↦ y - θ) 2 L :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hsqI
  have hid2 : MemLp (fun y : ℝ ↦ y) 2 L := by
    convert hL2.add (memLp_const θ) using 1
    funext y; simp
  have hmeanL : ∫ y, y ∂L = θ := integral_id_localLaplace hε P hP (hid2.integrable one_le_two)
  have hsqle : ∫ y, (y - θ) ^ 2 ∂L ≤ 4 + 8 / ε ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _) (by fun_prop)]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have hvarL : Var[fun y : ℝ ↦ y; L] ≤ 4 + 8 / ε ^ 2 := by
    rw [variance_eq_integral (by fun_prop), hmeanL]; exact hsqle
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i z ↦ z i
  have hYm : ∀ i, Measurable (Y i) := fun i ↦ measurable_pi_apply i
  have hmap : ∀ i, π.map (Y i) = L := fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ L) i).map_eq
  have hYL : ∀ i, MemLp (Y i) 2 π := fun i ↦ by
    exact hid2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n ↦ L) i)
  have hYint : ∀ i, ∫ z, Y i z ∂π = θ := by
    intro i
    rw [← hmeanL, ← hmap i, integral_map (hYm i).aemeasurable (by fun_prop)]
  have hvY : ∀ i, Var[Y i; π] ≤ 4 + 8 / ε ^ 2 := by
    intro i
    have h := variance_map (μ := π) (X := fun y : ℝ ↦ y) (Y := Y i)
      (by rw [hmap i]; fun_prop) (hYm i).aemeasurable
    rw [hmap i] at h
    rw [show Y i = (fun y : ℝ ↦ y) ∘ Y i from rfl, ← h]; exact hvarL
  have hmean_eq : (fun z : Fin n → ℝ ↦ (∑ i, z i) / n) = fun z ↦ (n : ℝ)⁻¹ * (∑ i, Y i) z := by
    funext z
    simp only [Finset.sum_apply, Y]
    rw [div_eq_inv_mul]
  have hsumL : MemLp (∑ i, Y i) 2 π := memLp_finsetSum' _ fun i _ ↦ hYL i
  have hmL : MemLp (fun z : Fin n → ℝ ↦ (∑ i, z i) / n) 2 π := by
    rw [hmean_eq]; exact hsumL.const_mul _
  have hEmean : ∫ z, (∑ i, z i) / n ∂π = θ := by
    rw [hmean_eq, integral_const_mul]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hYL i).integrable one_le_two]
    simp only [hYint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin n))) fun i j ↦ Y i ⟂ᵢ[π] Y j := by
    intro i _ j _ hij
    exact (iIndepFun_pi (X := fun _ : Fin n ↦ fun y : ℝ ↦ y)
      (fun _ ↦ aemeasurable_id)).indepFun hij
  have hvsum : Var[∑ i, Y i; π] = ∑ i, Var[Y i; π] :=
    IndepFun.variance_sum (fun i _ ↦ hYL i) hindep
  have hsqint : Integrable (fun z : Fin n → ℝ ↦ ((∑ i, z i) / n - θ) ^ 2) π :=
    (hmL.sub (memLp_const θ)).integrable_sq
  unfold localMeanRisk
  rw [← ofReal_integral_eq_lintegral_ofReal hsqint (ae_of_all _ fun _ ↦ sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hvar_eq : ∫ z, ((∑ i, z i) / n - θ) ^ 2 ∂π =
      Var[fun z : Fin n → ℝ ↦ (∑ i, z i) / n; π] := by
    rw [variance_eq_integral hmL.aemeasurable, hEmean]
  rw [hvar_eq, hmean_eq, variance_const_mul, hvsum]
  calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[Y i; π] ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, (4 + 8 / ε ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvY i) (by positivity)
    _ = (4 + 8 / ε ^ 2) / n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- GAPS 107.66, local minimax rate: there are absolute `c, C > 0` such that for `0 < ε ≤ 1`
every noninteractive protocol with `ε`-locally private release kernels and every measurable
estimator has mean squared error at least `c min(1, 1/(nε²))` for some law on `[-1,1]`, and some
such protocol has error at most `C min(1, 1/(nε²))` for every law on `[-1,1]`. -/
theorem localMeanRisk_minimax_order :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → ∀ ε ∈ Ioc (0 : ℝ) 1,
      (∀ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) →
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) →
        ∀ est : (Fin n → ℝ) → ℝ, Measurable est →
        ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ P (Icc (-1) 1)ᶜ = 0 ∧
          ENNReal.ofReal (c * min 1 (1 / (n * ε ^ 2))) ≤ localMeanRisk Q est P) ∧
      ∃ Q : Fin n → Kernel ℝ ℝ, (∀ i, IsMarkovKernel (Q i)) ∧
        (∀ i, IsDifferentiallyPrivate (fun _ _ : ℝ ↦ True) ε 0 (Q i)) ∧
        ∃ est : (Fin n → ℝ) → ℝ, Measurable est ∧
          ∀ P : Measure ℝ, IsProbabilityMeasure P → P (Icc (-1) 1)ᶜ = 0 →
            localMeanRisk Q est P ≤ ENNReal.ofReal (C * min 1 (1 / (n * ε ^ 2))) := by
  refine ⟨1 / 768, by norm_num, 12, by norm_num, fun n hn ε hε ↦ ⟨?_, ?_⟩⟩
  · intro Q hQ hpriv est hest
    obtain ⟨p, hp⟩ := exists_bernoulli_localMeanRisk_ge hn hε Q hQ hpriv est hest
    refine ⟨Ber((1 : ℝ), 0, p), inferInstance, bernoulliMeasure_one_zero_compl_Icc p, ?_⟩
    rw [one_div_mul_eq_div]; exact hp
  have hε0 := hε.1
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have := isMarkovKernel_localLaplaceKernel hε0
  refine ⟨fun _ ↦ localLaplaceKernel ε, fun _ ↦ this,
    fun _ ↦ isDifferentiallyPrivate_localLaplaceKernel hε0,
    fun z ↦ if (n : ℝ) * ε ^ 2 < 1 then 0 else (∑ i, z i) / n, ?_, ?_⟩
  · split_ifs <;> fun_prop
  intro P hP hsupp
  by_cases hsmall : (n : ℝ) * ε ^ 2 < 1
  · simp only [hsmall, ↓reduceIte]
    have hθ := abs_integral_le_one_of_support P hsupp
    have hmin : min 1 (1 / (n * ε ^ 2)) = 1 :=
      min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith)
    unfold localMeanRisk
    rw [lintegral_const, measure_univ, mul_one, hmin]
    apply ENNReal.ofReal_le_ofReal
    have : (0 - ∫ x, x ∂P) ^ 2 ≤ 1 := by
      rw [zero_sub, neg_sq, ← sq_abs]; nlinarith [abs_nonneg (∫ x, x ∂P)]
    linarith
  · simp only [hsmall, ↓reduceIte]
    push Not at hsmall
    have hmin : min 1 (1 / (n * ε ^ 2)) = 1 / (n * ε ^ 2) :=
      min_eq_right (by rw [div_le_iff₀ (by positivity)]; linarith)
    refine (localMeanRisk_localLaplace_mean_le hn hε0 P hsupp).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hmin]
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith [hε.2]
    have h4 : 4 ≤ 4 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    calc (4 + 8 / ε ^ 2) / n ≤ (4 / ε ^ 2 + 8 / ε ^ 2) / n := by gcongr
      _ = 12 * (1 / (n * ε ^ 2)) := by field_simp; ring

end CKSD
