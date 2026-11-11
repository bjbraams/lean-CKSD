module
public import CKSD.LinearModels.BlockIndependenceBasic
public import CKSD.LinearModels.SphericityLimit
/-!
# The chi-squared limit from a block-independence Beta-product law

A block determinant ratio with `p` Beta factors of shapes `(n-q-1-i)/2` and `q/2` has
likelihood-ratio limit chi-squared with `p*q` degrees of freedom. The input law is the two-block
case of Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 11.2.4, printed pages 533–534
(PDF pages 559–560 of the local 2005 copy), and Anderson, *An Introduction to Multivariate
Statistical Analysis*, Theorem 9.3.3, printed page 388 (PDF page 406 of the local third edition).

The local finite Beta-product limit supplies convergence; Mathlib supplies measurable samples
and pinned TauCeti identifies the resulting Gamma distribution with its chi-squared law.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators MatrixOrder
namespace CKSD
/-- A block determinant-ratio Beta law gives its chi-squared likelihood-ratio limit. -/
theorem tendstoInDistribution_block_independence_of_beta_product_laws
    {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin (p+q)))
    (hXm : ∀ i, Measurable (X i))
    (hexact : ∀ n : ℕ, p+q+1 ≤ n → P.map (fun ω ↦
      blockIndependenceRatio (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω))) =
      (Measure.pi (fun i : Fin p ↦ betaMeasure
        ((((n-1:ℕ):ℝ)-(q:ℝ)-i.val)/2) ((q:ℝ)/2))).map (fun x ↦ ∏ i, x i)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ -(n:ℝ) * Real.log
      (blockIndependenceRatio (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω)))) atTop id (fun _ ↦ P)
      (TauCeti.Probability.chiSquaredMeasure (p*q:ℕ)) := by
  let : Nonempty (Fin p) := Fin.pos_iff_nonempty.1 hp
  let c : Fin p → ℝ := fun i ↦ (q:ℝ)+1+i.val
  let b : Fin p → ℝ := fun _ ↦ (q:ℝ)/2
  let Z : ℕ → Ω → ℝ := fun n ω ↦ blockIndependenceRatio
    (sampleCovarianceMatrix (fun i : Fin n ↦ X i.val ω))
  have hb (i : Fin p) : 0 < b i := by dsimp [b]; exact div_pos (Nat.cast_pos.2 hq) two_pos
  have hbr := measurable_blockIndependenceRatio p q
  have hZm (n : ℕ) : Measurable (Z n) :=
    hbr.comp ((measurable_sampleCovarianceMatrix (n := n) (p := p+q)).comp
      (Measurable.of_eval fun i ↦ hXm i.val))
  have hmap : ∀ᶠ n in atTop, P.map (Z n) =
      (Measure.pi fun i : Fin p ↦ betaMeasure (max 1 (((n:ℝ)-c i)/2)) (b i)).map
        (fun x : Fin p → ℝ ↦ ∏ i, x i) := by
    filter_upwards [eventually_ge_atTop (p+q+3)] with n hn
    rw [show P.map (Z n) = _ from hexact n (by omega)]
    apply congrArg (fun f : Fin p → Measure ℝ ↦ (Measure.pi f).map (fun x : Fin p → ℝ ↦ ∏ i, x i))
    funext i
    dsimp only [c,b]
    have hiR : (q:ℝ)+1+i.val+2 ≤ n := by exact_mod_cast (by omega : q+1+i.val+2 ≤ n)
    rw [max_eq_right (by linarith : (1:ℝ) ≤ ((n:ℝ)-((q:ℝ)+1+i.val))/2),
      Nat.cast_sub (by omega : 1≤n), Nat.cast_one]
    congr 2
    ring
  let : IsProbabilityMeasure (gammaMeasure (∑ i,b i) (1/2)) :=
    isProbabilityMeasure_gammaMeasure (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty) (by norm_num)
  have hlim := tendstoInDistribution_neg_natCast_mul_log_of_beta_product_law P c b hb Z hZm hmap
  have hGamma : gammaMeasure (∑ i,b i) (1/2) = TauCeti.Probability.chiSquaredMeasure (p*q:ℕ) := by
    rw [TauCeti.Probability.chiSquaredMeasure_eq_gammaMeasure (by exact_mod_cast Nat.mul_pos hp hq)]
    congr 1
    simp only [b,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
    ring
  refine ⟨hlim.forall_aemeasurable,measurable_id.aemeasurable,?_⟩
  have hlimitP : (⟨(gammaMeasure (∑ i,b i) (1/2)).map id,inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨(TauCeti.Probability.chiSquaredMeasure (p*q:ℕ)).map id,inferInstance⟩ :=
    Subtype.ext (congrArg (Measure.map id) hGamma)
  have ht := hlim.tendsto
  rw [hlimitP] at ht
  exact ht
end CKSD
