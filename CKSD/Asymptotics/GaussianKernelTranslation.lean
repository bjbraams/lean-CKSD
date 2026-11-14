module
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Translation of Gaussian observation kernels

Input pullback and output pushforward commute with integrating a kernel against
a law. For Gaussian laws, translating the observation changes only its mean.
Combining these facts identifies the averaged translated decision kernel.

Mathlib supplies kernel composition and measurable-map identities. Pinned
TauCeti supplies the affine Gaussian image formula. This is the translation step
in the equivariant Gaussian convolution argument of van der Vaart (1998),
Proposition 8.4 and Theorem 8.8, printed pp. 113–115, PDF pp. 129–131.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CKSD
/-- Mapping a kernel's output and pulling back its input commute with integrating against a law. -/
theorem comp_map_comap_eq_map_comp_map
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (K : Kernel B C) [IsSFiniteKernel K]
    (f : A → B) (hf : Measurable f) (g : C → D) (hg : Measurable g) :
    ((K.comap f hf).map g) ∘ₘ μ = (K ∘ₘ μ.map f).map g := by
  rw [← Measure.map_comp μ (K.comap f hf) hg,
    ← Kernel.comp_deterministic_eq_comap,← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hf]
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
/-- Translating a Gaussian observation translates its mean without changing covariance. -/
theorem map_add_multivariateGaussian (a h : E) {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) :
    (multivariateGaussian h S).map (fun x ↦ a+x) = multivariateGaussian (a+h) S := by
  have he := TauCeti.Probability.map_affine_multivariateGaussian h hS
    (1 : Matrix (Fin d) (Fin d) ℝ) a
  simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_one,LinearMap.id_apply,
    Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one,add_comm] using he
/-- Translating the input and output of a Gaussian decision kernel preserves its averaged law
up to the same shift of the Gaussian mean and output. -/
theorem translatedKernel_comp_multivariateGaussian
    (K : Kernel E E) [IsMarkovKernel K] (a h : E)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) :
    ((K.comap (fun x : E ↦ a+x) (measurable_const_add a)).map (fun y : E ↦ y-a)) ∘ₘ multivariateGaussian h S =
      (K ∘ₘ multivariateGaussian (a+h) S).map (fun y : E ↦ y-a) := by
  rw [comp_map_comap_eq_map_comp_map (multivariateGaussian h S) K
      (fun x : E ↦ a+x) (by fun_prop) (fun y : E ↦ y-a) (by fun_prop),
    map_add_multivariateGaussian a h hS]
end CKSD
