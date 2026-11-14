module
public import CKSD.Asymptotics.GaussianShiftTilt
public import CKSD.Inference.ExponentialFamily
/-!
# Completeness of nondegenerate Gaussian location families

A measurable integrable function whose expectation vanishes under every location of a fixed
nondegenerate Gaussian law vanishes Lebesgue-almost everywhere. In particular, the Gaussian
location experiment is boundedly complete. The zero-dimensional case is included.

The proof reuses completeness of natural exponential families from
`CKSD.Inference.ExponentialFamily`, which is based on multivariate Laplace determinacy.
Pinned TauCeti provides Gaussian exponential integrability and moment-generating functions;
`CKSD.Asymptotics.GaussianShiftTilt` identifies the exponential tilts with the location family.
Positive Gaussian densities transfer the almost-everywhere conclusion to Lebesgue measure
and to every member of the family. This is the completeness bridge used in the Gaussian
shift convolution argument for GAPS 102.16.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace CKSD
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- The Gaussian location family is complete among integrable measurable functions. -/
theorem ae_eq_zero_of_integral_multivariateGaussian_eq_zero
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (f : E → ℝ) (hf : Measurable f)
    (hfi : ∀ h, Integrable f (multivariateGaussian h S))
    (hzero : ∀ h, ∫ x, f x ∂multivariateGaussian h S = 0) :
    ∀ᵐ x ∂volume, f x = 0 := by
  let P := multivariateGaussian (0 : E) S
  let Z : E → ℝ := fun η ↦ Real.exp (inner ℝ η (S.toEuclideanLin η) / 2)
  have hZ (η : E) (_hη : η ∈ (univ : Set E)) :
      Integrable (fun x : E ↦ Real.exp (inner ℝ η (id x))) P ∧
      Z η = ∫ x, Real.exp (inner ℝ η (id x)) ∂P ∧ 0 < Z η := by
    have hi : (1 : ℝ) ∈ integrableExpSet (fun x : E ↦ inner ℝ η x) P := by
      rw [TauCeti.Probability.integrableExpSet_inner_multivariateGaussian 0 η S]
      exact mem_univ _
    have hmgf := TauCeti.Probability.mgf_inner_multivariateGaussian (0 : E) η hS.posSemidef 1
    simp only [mgf,one_mul,inner_zero_right,one_pow,mul_zero,zero_add] at hmgf
    refine ⟨?_,?_,Real.exp_pos _⟩
    · simpa only [integrableExpSet,mem_ofPred_eq,one_mul,id_eq] using hi
    · simpa only [Z,P,id_eq,div_eq_mul_inv,mul_comm,one_mul] using hmgf.symm
  have hc := isCompleteStatistic_withDensity_exp_inner P id measurable_id univ isOpen_univ
    Set.univ_nonempty Z hZ
  have htilt (η : E) : P.withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (inner ℝ η (id x)) / Z η)) =
      multivariateGaussian (S.toEuclideanLin η) S := by
    convert multivariateGaussian_withDensity_exp_inner hS η using 1
    congr 1
    funext x
    rw [Real.exp_sub]
    rfl
  have hz := hc f hf (fun η ↦ by
    dsimp only
    rw [htilt η]
    exact ⟨by simpa only [Function.comp_id] using hfi (S.toEuclideanLin η),
      hzero (S.toEuclideanLin η)⟩) ⟨0,mem_univ _⟩
  dsimp only at hz
  rw [htilt 0] at hz
  simp only [map_zero] at hz
  rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS] at hz
  have he := (ae_withDensity_iff (TauCeti.Probability.measurable_multivariateGaussianPDF 0 S)).1 hz
  filter_upwards [he] with x hx
  exact hx (ne_of_gt (TauCeti.Probability.multivariateGaussianPDF_pos hS.det_pos 0 x))
/-- The identity statistic of a nondegenerate Gaussian location family is complete. -/
theorem isCompleteStatistic_multivariateGaussian_location
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsCompleteStatistic (fun h : E ↦ multivariateGaussian h S) id := by
  intro f hf hzero h
  have hvol := ae_eq_zero_of_integral_multivariateGaussian_eq_zero hS f hf
    (fun k ↦ by simpa only [Function.comp_id] using (hzero k).1) (fun k ↦ (hzero k).2)
  change ∀ᵐ x ∂multivariateGaussian h S, f x = 0
  rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS]
  exact (withDensity_absolutelyContinuous _ _).ae_le hvol

/-- A bounded measurable function whose mean is zero under every Gaussian location vanishes
Lebesgue-almost everywhere. -/
theorem ae_eq_zero_of_bounded_integral_multivariateGaussian_eq_zero
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (hzero : ∀ h, ∫ x, f x ∂multivariateGaussian h S = 0) :
    ∀ᵐ x ∂volume, f x = 0 := by
  apply ae_eq_zero_of_integral_multivariateGaussian_eq_zero hS f hf _ hzero
  intro h
  exact Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun x ↦ by
    simpa only [Real.norm_eq_abs] using hM x)

/-- Gaussian location completeness also gives equality almost everywhere under any member of
the same nondegenerate Gaussian family. -/
theorem ae_gaussian_eq_zero_of_bounded_integral_multivariateGaussian_eq_zero
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (hzero : ∀ h, ∫ x, f x ∂multivariateGaussian h S = 0) (k : E) :
    ∀ᵐ x ∂multivariateGaussian k S, f x = 0 := by
  have hv := ae_eq_zero_of_bounded_integral_multivariateGaussian_eq_zero hS f hf M hM hzero
  rw [TauCeti.Probability.multivariateGaussian_eq_withDensity hS]
  exact (withDensity_absolutelyContinuous _ _).ae_le hv
/-- The identity statistic of a nondegenerate Gaussian location family is boundedly complete. -/
theorem isBoundedlyCompleteStatistic_multivariateGaussian_location
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsBoundedlyCompleteStatistic (fun h : E ↦ multivariateGaussian h S) id := by
  intro f hf hbound hzero k
  obtain ⟨M,hM⟩ := hbound
  exact ae_gaussian_eq_zero_of_bounded_integral_multivariateGaussian_eq_zero hS f hf M hM hzero k
end CKSD
