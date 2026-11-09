module

public import CKSD.LinearModels.DirectedGraphical
public import CKSD.LinearModels.GaussianGraphical
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CKSD.LinearModels.Multivariate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
public import CKSD.LinearModels.Decomposable

/-!
# Gaussian decomposable graphical models

The Gaussian maximum likelihood estimate of the concentration matrix in the graphical model of
an undirected graph, for a general graph and, explicitly, for a graph with a perfect sequence of
cliques (`CKSD.IsPerfectCliqueSequence`).

## Main definitions

* `CKSD.principalBlock`, `CKSD.padBlock`: principal blocks and their padding by zeros.
* `CKSD.decomposableConcentrationMLE`: the explicit Gaussian concentration estimate
  `n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`.

## Main results

* `CKSD.isConcentrationMLE_decomposableConcentrationMLE` and
  `CKSD.existsUnique_isConcentrationMLE_inv`: the Gaussian maximum likelihood estimate of the
  concentration matrix for a decomposable and for a general graph.
* `CKSD.isConcentrationMLE_inv_of_apply_eq`: a positive definite `Σ` that agrees with `ssd / n`
  on the diagonal and the edges and whose inverse vanishes off the edges gives the estimate.

The general-graph estimate is obtained by maximizing `det Σ` over the compact convex set of
positive semidefinite completions of the observed entries of `ssd / n`; the first-order condition
along the non-edge directions shows that the maximizer has inverse in the concentration model,
and the strict inequality `log det S + dim < log det C + tr(S C⁻¹)` for `C ≠ S` gives strict
optimality of the likelihood.

The decomposable estimate is obtained by induction over the perfect sequence. At each step the
inverse of the block on `C₀ ∪ ⋯ ∪ C_{j-1}` and the inverse of `ssd_{C_j}` are glued along the
separator `S_j`. Positive definiteness of the glued matrix and the agreement of its inverse with
the two pieces follow from the marginal-precision inequality
`x_D ⬝ (M_D)⁻¹ x_D ≤ x_U ⬝ (M_U)⁻¹ x_U` for `D ⊆ U`, with equality attained by changing `x` off
`D`.

## References

* S. L. Lauritzen, *Graphical Models*, Oxford University Press, 1996, Ch. 5.3.

Source: GAPS 105.36.
-/

@[expose] public section

noncomputable section

open Set Matrix
open scoped BigOperators

namespace CKSD

attribute [local instance] Classical.propDecidable

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block `B_{CC}` of a square matrix indexed by a finite set `C` of coordinates. -/
def principalBlock (B : Matrix ι ι ℝ) (C : Finset ι) : Matrix C C ℝ :=
  B.submatrix Subtype.val Subtype.val

/-- `[B]^V`: a matrix indexed by `C`, padded with zeros to a square matrix indexed by `ι`. -/
def padBlock (C : Finset ι) (B : Matrix C C ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if h : i ∈ C ∧ j ∈ C then B ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The explicit maximum likelihood estimate of the concentration matrix in a decomposable
Gaussian graphical model with perfect sequence of cliques `C`:
`n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`, the separators being counted with
multiplicity. -/
def decomposableConcentrationMLE {k : ℕ} (C : Fin k → Finset ι) (n : ℕ)
    (ssd : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (n : ℝ) • (∑ j, padBlock (C j) (principalBlock ssd (C j))⁻¹ -
    ∑ j : Fin k, if (j : ℕ) = 0 then 0 else
      padBlock (cliqueSeparator C j) (principalBlock ssd (cliqueSeparator C j))⁻¹)

/-- Strict form of the Gaussian covariance criterion on a general finite index type: for positive
definite `S ≠ C`, `log det S + dim < log det C + tr(S C⁻¹)`. -/
theorem log_det_add_card_lt_log_det_add_trace_mul_inv {S C : Matrix ι ι ℝ} (hS : S.PosDef)
    (hC : C.PosDef) (hne : C ≠ S) :
    Real.log S.det + Fintype.card ι < Real.log C.det + (S * C⁻¹).trace := by
  let e := Fintype.equivFin ι
  have hS' : (reindex e e S).PosDef := hS.submatrix e.symm.injective
  have hC' : (reindex e e C).PosDef := hC.submatrix e.symm.injective
  have hle := log_det_add_card_le_log_det_add_trace_mul_inv _ _ hS' hC'
  have hiff := log_det_add_card_eq_log_det_add_trace_mul_inv_iff _ _ hS' hC'
  have htr : (reindex e e S * (reindex e e C)⁻¹).trace = (S * C⁻¹).trace := by
    rw [inv_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv]
    simp only [trace]
    exact Equiv.sum_comp e.symm (fun i ↦ (S * C⁻¹) i i)
  rw [det_reindex_self, det_reindex_self, htr] at hle hiff
  have hne' : reindex e e C ≠ reindex e e S := fun h ↦ hne ((reindex e e).injective h)
  exact lt_of_le_of_ne hle fun h ↦ hne' (hiff.1 h)

/-- Sufficiency of the likelihood equations: if `Σ` is positive definite, agrees with `ssd / n` on
the diagonal and on the edges of `G`, and `Σ⁻¹` vanishes off the edges, then `Σ⁻¹` is the
maximum likelihood estimate of the concentration matrix. -/
theorem isConcentrationMLE_inv_of_apply_eq (G : SimpleGraph ι) {n : ℕ}
    (ssd Sig : Matrix ι ι ℝ) (hSig : Sig.PosDef)
    (hmatch : ∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n)
    (hzero : ∀ i j, i ≠ j → ¬ G.Adj i j → Sig⁻¹ i j = 0) :
    IsConcentrationMLE G n ssd Sig⁻¹ := by
  have hmem : Sig⁻¹ ∈ concentrationModel G := ⟨hSig.inv, hzero⟩
  have htr : ∀ K ∈ concentrationModel G, trace (K * ssd) / n = trace (K * Sig) := by
    intro K hK
    simp only [trace, diag_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases h : i = j ∨ G.Adj i j
    · rw [hmatch j i (h.imp Eq.symm fun hij ↦ hij.symm)]
      ring
    · push Not at h
      rw [hK.2 i j h.1 h.2]
      simp
  refine ⟨hmem, fun K' hK' hne ↦ ?_⟩
  have hdet (A : Matrix ι ι ℝ) (hA : A.PosDef) : Real.log A⁻¹.det = - Real.log A.det := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
  have hne' : K'⁻¹ ≠ Sig := fun h ↦
    hne (by rw [← h, nonsing_inv_nonsing_inv _ hK'.1.det_pos.ne'.isUnit])
  have key := log_det_add_card_lt_log_det_add_trace_mul_inv hSig hK'.1.inv hne'
  rw [nonsing_inv_nonsing_inv _ hK'.1.det_pos.ne'.isUnit, hdet K' hK'.1, trace_mul_comm] at key
  unfold gaussianConcentrationLogLikelihood
  rw [htr K' hK', htr _ hmem, nonsing_inv_mul _ hSig.det_pos.ne'.isUnit, trace_one,
    hdet Sig hSig]
  linarith

open scoped MatrixOrder in
/-- A positive definite matrix dominates a positive multiple of the identity. -/
theorem exists_pos_posSemidef_sub_smul_one {Sig : Matrix ι ι ℝ} [Nonempty ι] (hSig : Sig.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (Sig - c • (1 : Matrix ι ι ℝ)).PosSemidef := by
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff Sig hSig.isHermitian.isSelfAdjoint).2
    fun x hx ↦ hSig.isStrictlyPositive.spectrum_pos hx
  refine ⟨r, hr, ?_⟩
  rw [← Matrix.le_iff]
  simpa [Algebra.algebraMap_eq_smul_one] using hle

/-- The symmetric matrix with ones at `(i, j)` and `(j, i)`. -/
private def symmSingle (i j : ι) : Matrix ι ι ℝ := single i j 1 + single j i 1

/-- `(E_{ij} + E_{ji}) x = x_j eᵢ + x_i eⱼ`. -/
private theorem symmSingle_mulVec (i j : ι) (x : ι → ℝ) :
    symmSingle i j *ᵥ x = Pi.single i (x j) + Pi.single j (x i) := by
  simp [symmSingle, add_mulVec, single_mulVec]
  rfl

/-- A small symmetric perturbation at `(i, j)` and `(j, i)` keeps a positive definite matrix
positive semidefinite. -/
private theorem posSemidef_add_smul_symmSingle {Sig : Matrix ι ι ℝ} (hSig : Sig.PosDef) {i j : ι}
    (hij : i ≠ j) : ∃ δ > 0, ∀ t : ℝ, |t| ≤ δ → (Sig + t • symmSingle i j).PosSemidef := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨c, hc, hpsd⟩ := exists_pos_posSemidef_sub_smul_one hSig
  refine ⟨c, hc, fun t ht ↦ ?_⟩
  have hE : (symmSingle i j).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, symmSingle, transpose_add,
      transpose_single, transpose_single, add_comm]
  have h2 : (c • (1 : Matrix ι ι ℝ) + t • symmSingle i j).PosSemidef := by
    have hH : (c • (1 : Matrix ι ι ℝ) + t • symmSingle i j).IsHermitian := by
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
        conjTranspose_one, hE.eq]
      simp
    refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x ↦ ?_
    have hsq : x i * x i + x j * x j ≤ x ⬝ᵥ x := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k ↦ x k * x k)
        (Finset.subset_univ {i, j}) fun k _ _ ↦ mul_self_nonneg (x k)
      simpa [dotProduct, Finset.sum_pair hij] using this
    simp only [star_trivial, add_mulVec, smul_mulVec, one_mulVec, symmSingle_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul]
    have h1 : -(c * (x i * x i + x j * x j)) ≤ t * (x i * x j + x j * x i) := by
      have habs : |t * (x i * x j + x j * x i)| ≤ c * (x i * x i + x j * x j) := by
        rw [abs_mul]
        have : |x i * x j + x j * x i| ≤ x i * x i + x j * x j := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
        calc |t| * |x i * x j + x j * x i| ≤ c * |x i * x j + x j * x i| :=
              mul_le_mul_of_nonneg_right ht (abs_nonneg _)
          _ ≤ c * (x i * x i + x j * x j) := mul_le_mul_of_nonneg_left this hc.le
      exact (abs_le.1 habs).1
    nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
  have := hpsd.add h2
  rwa [show Sig - c • 1 + (c • 1 + t • symmSingle i j) = Sig + t • symmSingle i j by abel]
    at this

/-- The determinant along the line `Σ + t (E_{ij} + E_{ji})`, by the matrix determinant lemma:
`det Σ · ((1 + t K_{ji})(1 + t K_{ij}) - t² K_{jj} K_{ii})` with `K = Σ⁻¹`. -/
private theorem det_add_smul_symmSingle {Sig : Matrix ι ι ℝ} (hSig : Sig.PosDef) {i j : ι}
    (hij : i ≠ j) (t : ℝ) : (Sig + t • symmSingle i j).det = Sig.det *
      ((1 + t * Sig⁻¹ j i) * (1 + t * Sig⁻¹ i j) - t * Sig⁻¹ j j * (t * Sig⁻¹ i i)) := by
  let U : Matrix ι (Fin 2) ℝ := t • (1 : Matrix ι ι ℝ).submatrix id ![i, j]
  let V : Matrix (Fin 2) ι ℝ := (1 : Matrix ι ι ℝ).submatrix ![j, i] id
  have hUV : U * V = t • symmSingle i j := by
    simp only [U, V, Matrix.smul_mul]
    congr 1
    ext k l
    simp only [Matrix.mul_apply, Fin.sum_univ_two, submatrix_apply, id, symmSingle,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h1 : k = i <;> by_cases h2 : k = j <;> by_cases h3 : l = i <;>
      by_cases h4 : l = j <;> simp_all [Ne.symm hij, eq_comm]
  have hVKU : V * Sig⁻¹ * U = t • Sig⁻¹.submatrix ![j, i] ![i, j] := by
    simp only [U, V, Matrix.mul_smul]
    congr 1
    have hV : (1 : Matrix ι ι ℝ).submatrix ![j, i] id * Sig⁻¹ = Sig⁻¹.submatrix ![j, i] id :=
      one_submatrix_mul ![j, i] (Equiv.refl ι) Sig⁻¹
    rw [hV]
    exact mul_submatrix_one (Equiv.refl ι) ![i, j] _
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) + V * Sig⁻¹ * U =
      !![1 + t * Sig⁻¹ j i, t * Sig⁻¹ j j; t * Sig⁻¹ i i, 1 + t * Sig⁻¹ i j] := by
    rw [hVKU]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
    fin_cases a <;> fin_cases b <;> simp
  rw [← hUV, det_add_mul U V hSig.det_pos.ne'.isUnit, h2, det_fin_two_of]

/-- An entry of a positive semidefinite matrix is bounded by the mean of the two diagonal
entries. -/
private theorem abs_apply_le_of_posSemidef {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    |S i j| ≤ (S i i + S j j) / 2 := by
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonneg (hS.diag_nonneg)]
    linarith
  have hsymm : S j i = S i j := by
    simpa using (hS.isHermitian.apply j i).symm
  have h1 := hS.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hS.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    mulVec_single, single_dotProduct, hsymm] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Existence of the solution of the likelihood equations: maximizing `det Σ` over the compact
set of positive semidefinite `Σ` that agree with `ssd / n` on the diagonal and on the edges gives
a positive definite `Σ` whose inverse vanishes off the edges, by the first-order condition along
each direction `E_{ij} + E_{ji}` for a non-edge `{i, j}`. -/
private theorem exists_posDef_apply_eq_of_inv_apply_eq_zero (G : SimpleGraph ι) {n : ℕ}
    (hn : 0 < n) (ssd : Matrix ι ι ℝ) (hssd : ssd.PosDef) :
    ∃ Sig : Matrix ι ι ℝ, Sig.PosDef ∧
      (∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n) ∧
      ∀ i j, i ≠ j → ¬ G.Adj i j → Sig⁻¹ i j = 0 := by
  let F : Set (Matrix ι ι ℝ) :=
    {S | S.PosSemidef ∧ ∀ i j, (i = j ∨ G.Adj i j) → S i j = ssd i j / n}
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  let T : Matrix ι ι ℝ := (n : ℝ)⁻¹ • ssd
  have hT : T.PosDef := hssd.smul (inv_pos.2 hn')
  have hTF : T ∈ F := ⟨hT.posSemidef, fun i j _ ↦ by simp [T, div_eq_inv_mul]⟩
  have hclosed : IsClosed F := by
    have hF : F = {S : Matrix ι ι ℝ | S.PosSemidef} ∩
        ⋂ i, ⋂ j, {S : Matrix ι ι ℝ | (i = j ∨ G.Adj i j) → S i j = ssd i j / n} := by
      ext S
      simp [F]
    rw [hF]
    refine isClosed_setOfPred_posSemidef.inter
      (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_)
    by_cases h : i = j ∨ G.Adj i j
    · simp only [h, true_implies]
      exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
    · simp [h]
  let R : ℝ := ∑ k, |ssd k k / n|
  have hR (k : ι) : |ssd k k / n| ≤ R :=
    Finset.single_le_sum (f := fun k ↦ |ssd k k / n|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ k)
  have hsub : F ⊆ Set.pi univ fun _ : ι ↦ Set.pi univ fun _ : ι ↦ Icc (-R) R := by
    intro S hS i _ j _
    have h := abs_apply_le_of_posSemidef hS.1 i j
    rw [hS.2 i i (Or.inl rfl), hS.2 j j (Or.inl rfl)] at h
    have := (le_abs_self (ssd i i / n)).trans (hR i)
    have := (le_abs_self (ssd j j / n)).trans (hR j)
    exact abs_le.1 (h.trans (by linarith))
  have hcompact : IsCompact F :=
    (isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset
      hclosed hsub
  obtain ⟨S, hSF, hmax⟩ := hcompact.exists_isMaxOn ⟨T, hTF⟩
    (continuous_id.matrix_det).continuousOn
  have hdetS : 0 < S.det := hT.det_pos.trans_le (hmax hTF)
  have hS : S.PosDef := hSF.1.posDef_iff_isUnit.2
    ((isUnit_iff_isUnit_det S).2 hdetS.ne'.isUnit)
  refine ⟨S, hS, hSF.2, fun i j hij hadj ↦ ?_⟩
  by_contra hq
  obtain ⟨δ, hδ, hpsd⟩ := posSemidef_add_smul_symmSingle hS hij
  set q := S⁻¹ i j with hqdef
  have hqji : S⁻¹ j i = q := by
    simpa using (hS.inv.isHermitian.apply i j)
  set D := q ^ 2 - S⁻¹ i i * S⁻¹ j j with hD
  have hq' : 0 < |q| := abs_pos.2 hq
  set s := min (δ / |q|) (1 / (|D| + 1)) with hsdef
  have hs : 0 < s := lt_min (div_pos hδ hq') (div_pos one_pos (by positivity))
  have hs1 : s ≤ δ / |q| := min_le_left _ _
  have hs2 : s ≤ 1 / (|D| + 1) := min_le_right _ _
  have ht : |s * q| ≤ δ := by
    rw [abs_mul, abs_of_pos hs]
    calc s * |q| ≤ δ / |q| * |q| := mul_le_mul_of_nonneg_right hs1 hq'.le
      _ = δ := div_mul_cancel₀ δ hq'.ne'
  have hmem : S + (s * q) • symmSingle i j ∈ F := by
    refine ⟨hpsd _ ht, fun a b hab ↦ ?_⟩
    have hE : symmSingle i j a b = 0 := by
      simp only [symmSingle, Matrix.add_apply, single_apply]
      have h1 : ¬ (i = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        rcases hab with h | h
        · exact hij h
        · exact hadj h
      have h2 : ¬ (j = a ∧ i = b) := by
        rintro ⟨rfl, rfl⟩
        rcases hab with h | h
        · exact hij h.symm
        · exact hadj h.symm
      simp [h1, h2]
    simp [Matrix.add_apply, Matrix.smul_apply, hE, hSF.2 a b hab]
  have hle : (S + (s * q) • symmSingle i j).det ≤ S.det := hmax hmem
  rw [det_add_smul_symmSingle hS hij, hqji, ← hqdef] at hle
  have hsD : -1 < s * D := by
    have h1 : s * |D| < 1 := by
      calc s * |D| ≤ 1 / (|D| + 1) * |D| := mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
        _ < 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
          linarith
    have := neg_abs_le D
    nlinarith
  have hf : 1 < (1 + s * q * q) * (1 + s * q * q) - s * q * S⁻¹ j j * (s * q * S⁻¹ i i) := by
    have : (1 + s * q * q) * (1 + s * q * q) - s * q * S⁻¹ j j * (s * q * S⁻¹ i i) =
        1 + s * q ^ 2 * (2 + s * D) := by
      rw [hD]
      ring
    rw [this]
    have : 0 < s * q ^ 2 * (2 + s * D) := by
      have : 0 < q ^ 2 := by positivity
      exact mul_pos (mul_pos hs this) (by linarith)
    linarith
  nlinarith

/-- GAPS 105.36, general graph: if `ssd` is positive definite and `n > 0`, there is a unique
positive definite `Σ̂` that agrees with `ssd / n` on the diagonal and on the edges and whose
inverse is the maximum likelihood estimate of the concentration matrix (in particular `Σ̂⁻¹`
vanishes off the edges). Convergence of iterative proportional scaling is not stated. -/
theorem existsUnique_isConcentrationMLE_inv (G : SimpleGraph ι) (n : ℕ) (hn : 0 < n)
    (ssd : Matrix ι ι ℝ) (hssd : ssd.PosDef) :
    ∃! Sig : Matrix ι ι ℝ, Sig.PosDef ∧
      (∀ i j, (i = j ∨ G.Adj i j) → Sig i j = ssd i j / n) ∧
      IsConcentrationMLE G n ssd Sig⁻¹ := by
  obtain ⟨Sig, hpd, hmatch, hzero⟩ := exists_posDef_apply_eq_of_inv_apply_eq_zero G hn ssd hssd
  have hMLE := isConcentrationMLE_inv_of_apply_eq G ssd Sig hpd hmatch hzero
  refine ⟨Sig, ⟨hpd, hmatch, hMLE⟩, ?_⟩
  rintro Sig' ⟨hpd', -, hMLE'⟩
  by_contra hne
  have hne' : Sig'⁻¹ ≠ Sig⁻¹ := fun h ↦ hne (by
    rw [← nonsing_inv_nonsing_inv Sig' hpd'.det_pos.ne'.isUnit, h,
      nonsing_inv_nonsing_inv Sig hpd.det_pos.ne'.isUnit])
  have h1 := hMLE.2 _ hMLE'.1 hne'
  have h2 := hMLE'.2 _ hMLE.1 hne'.symm
  linarith

/-- The restriction `x_D` of a vector `x : ι → ℝ` to a finite set `D` of coordinates. -/
private def res (D : Finset ι) (x : ι → ℝ) : D → ℝ := fun i ↦ x i

omit [DecidableEq ι] in
/-- A sum over `ι` of a function vanishing off `D` is the sum over `D`. -/
private theorem sum_subtype_eq {D : Finset ι} (f : ι → ℝ) (hf : ∀ i ∉ D, f i = 0) :
    ∑ i : D, f i = ∑ i, f i := by
  rw [Finset.sum_coe_sort D f]
  exact Finset.sum_subset (Finset.subset_univ D) fun i _ hi ↦ hf i hi

omit [DecidableEq ι] in
/-- `x_U ⬝ y_U = x ⬝ y` when `x` vanishes off `U`. -/
private theorem dotProduct_res {U : Finset ι} (a b : ι → ℝ) (ha : ∀ i ∉ U, a i = 0) :
    res U a ⬝ᵥ res U b = a ⬝ᵥ b := by
  simp only [dotProduct, res]
  exact sum_subtype_eq (fun i ↦ a i * b i) fun i hi ↦ by simp [ha i hi]

omit [DecidableEq ι] in
/-- `M_U y_U = (M y)_U` when `y` vanishes off `U`. -/
private theorem mulVec_res (M : Matrix ι ι ℝ) {U : Finset ι} (b : ι → ℝ)
    (hb : ∀ i ∉ U, b i = 0) : principalBlock M U *ᵥ res U b = res U (M *ᵥ b) := by
  ext u
  simp only [mulVec, dotProduct, res, principalBlock, submatrix_apply]
  exact sum_subtype_eq (fun v ↦ M u v * b v) fun i hi ↦ by simp [hb i hi]

/-- The quadratic form of `[B]^V` at `x` is the quadratic form of `B` at `x_D`. -/
private theorem dotProduct_mulVec_padBlock (D : Finset ι) (B : Matrix D D ℝ) (x : ι → ℝ) :
    x ⬝ᵥ padBlock D B *ᵥ x = res D x ⬝ᵥ B *ᵥ res D x := by
  simp only [dotProduct, mulVec, res]
  rw [← sum_subtype_eq (D := D)]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [← sum_subtype_eq (D := D)]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [padBlock, i.2, j.2]
    · intro j hj
      simp [padBlock, hj]
  · intro i hi
    simp [padBlock, hi]

/-- Variational form of the inverse: for positive definite `B`,
`2 z ⬝ w - z ⬝ B z ≤ w ⬝ B⁻¹ w`, with equality at `z = B⁻¹ w`. -/
private theorem two_dotProduct_sub_le {T : Type*} [Fintype T] [DecidableEq T] {B : Matrix T T ℝ}
    (hB : B.PosDef) (w z : T → ℝ) :
    2 * (z ⬝ᵥ w) - z ⬝ᵥ B *ᵥ z ≤ w ⬝ᵥ B⁻¹ *ᵥ w := by
  have hBt : Bᵀ = B := by simpa using hB.isHermitian.eq
  have hu : IsUnit B.det := hB.det_pos.ne'.isUnit
  have h := hB.posSemidef.dotProduct_mulVec_nonneg (z - B⁻¹ *ᵥ w)
  simp only [star_trivial] at h
  have e1 : B *ᵥ (B⁻¹ *ᵥ w) = w := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e2 : (B⁻¹ *ᵥ w) ⬝ᵥ B *ᵥ z = z ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hBt, dotProduct_comm, e1]
  rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e1, e2,
    dotProduct_comm (B⁻¹ *ᵥ w) w] at h
  linarith


/-- The quadratic form `x_D ⬝ (M_D)⁻¹ x_D` of the inverse of the block `M_D`. -/
private noncomputable def qf (D : Finset ι) (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  res D x ⬝ᵥ (principalBlock M D)⁻¹ *ᵥ res D x

omit [Fintype ι] [DecidableEq ι] in
/-- A principal block of a positive definite principal block is positive definite. -/
private theorem posDef_principalBlock_of_subset {M : Matrix ι ι ℝ} {D U : Finset ι}
    (hM : (principalBlock M U).PosDef) (hDU : D ⊆ U) : (principalBlock M D).PosDef := by
  exact hM.submatrix (e := fun i : D ↦ (⟨i.1, hDU i.2⟩ : U)) fun a b h ↦
    Subtype.ext (congrArg (fun u : U ↦ u.1) h)

/-- The extension by zero of a vector on `D`. -/
private def ext0 (D : Finset ι) (z : D → ℝ) : ι → ℝ := fun i ↦ if h : i ∈ D then z ⟨i, h⟩ else 0

omit [Fintype ι] in
/-- Restricting the extension by zero recovers the vector. -/
private theorem res_ext0 (D : Finset ι) (z : D → ℝ) : res D (ext0 D z) = z := by
  ext i; simp [res, ext0, i.2]

omit [Fintype ι] in
/-- The extension by zero from `D ⊆ U` vanishes off `U`. -/
private theorem ext0_eq_zero {D U : Finset ι} (hDU : D ⊆ U) (z : D → ℝ) :
    ∀ i ∉ U, ext0 D z i = 0 := fun i hi ↦ by
  simp only [ext0, dite_eq_right_iff.2 fun h ↦ absurd (hDU h) hi]

/-- Marginal precision inequality: `x_D ⬝ (M_D)⁻¹ x_D ≤ x_U ⬝ (M_U)⁻¹ x_U` for `D ⊆ U`, with
equality for a suitable change of `x` off `D`. -/
private theorem qf_le_qf {M : Matrix ι ι ℝ} {D U : Finset ι} (hM : (principalBlock M U).PosDef)
    (hDU : D ⊆ U) (x : ι → ℝ) :
    qf D M x ≤ qf U M x ∧ ∃ y : ι → ℝ, (∀ i ∈ D, y i = x i) ∧ qf U M y = qf D M x := by
  have hMD := posDef_principalBlock_of_subset hM hDU
  have huD : IsUnit (principalBlock M D).det := hMD.det_pos.ne'.isUnit
  have huU : IsUnit (principalBlock M U).det := hM.det_pos.ne'.isUnit
  set B := principalBlock M D
  set z₀ := B⁻¹ *ᵥ res D x
  set z := ext0 D z₀
  have hz0 : ∀ i ∉ D, z i = 0 := ext0_eq_zero subset_rfl z₀
  have hzU : ∀ i ∉ U, z i = 0 := ext0_eq_zero hDU z₀
  have hBz : B *ᵥ z₀ = res D x := by
    simp only [z₀, mulVec_mulVec, mul_nonsing_inv _ huD, one_mulVec]
  -- the value `qf D M x = z₀ ⬝ B z₀ = z ⬝ M z`
  have hval : qf D M x = z ⬝ᵥ M *ᵥ z := by
    have h1 : z ⬝ᵥ M *ᵥ z = z₀ ⬝ᵥ B *ᵥ z₀ := by
      rw [← dotProduct_res (U := D) _ _ hz0, ← mulVec_res M _ hz0, res_ext0]
    rw [h1, hBz, qf]
    exact dotProduct_comm _ _
  have hxz : z ⬝ᵥ x = qf D M x := by
    rw [← dotProduct_res (U := D) _ _ hz0, res_ext0, qf, dotProduct_comm]
  have hzMz : res U z ⬝ᵥ principalBlock M U *ᵥ res U z = z ⬝ᵥ M *ᵥ z := by
    rw [mulVec_res M _ hzU, dotProduct_res _ _ hzU]
  constructor
  · have := two_dotProduct_sub_le hM (res U x) (res U z)
    rw [dotProduct_res _ _ hzU, hzMz, hxz, ← hval] at this
    unfold qf at this ⊢
    linarith
  · refine ⟨M *ᵥ z, fun i hi ↦ ?_, ?_⟩
    · have := congrFun hBz ⟨i, hi⟩
      rw [← res_ext0 D z₀, mulVec_res M _ hz0] at this
      exact this
    · rw [qf, ← mulVec_res M _ hzU, mulVec_mulVec, nonsing_inv_mul _ huU, one_mulVec,
        dotProduct_comm, hzMz, hval]


omit [Fintype ι] in
/-- `qf D X x` depends only on `x_D`. -/
private theorem qf_congr (D : Finset ι) (X : Matrix ι ι ℝ) {x y : ι → ℝ}
    (h : ∀ i ∈ D, x i = y i) : qf D X x = qf D X y := by
  have : res D x = res D y := funext fun i ↦ h i i.2
  simp only [qf, this]

omit [Fintype ι] in
/-- For positive definite `X_D`, `qf D X x = 0` forces `x_D = 0`. -/
private theorem res_eq_zero_of_qf_eq_zero {D : Finset ι} {X : Matrix ι ι ℝ}
    (hX : (principalBlock X D).PosDef) {x : ι → ℝ} (h : qf D X x = 0) : res D x = 0 := by
  by_contra hne
  have := hX.inv.dotProduct_mulVec_pos hne
  simp only [star_trivial] at this
  exact this.ne' h

omit [Fintype ι] in
/-- The `D`-block of `[B]^V` is `B`. -/
private theorem principalBlock_padBlock (D : Finset ι) (B : Matrix D D ℝ) :
    principalBlock (padBlock D B) D = B := by
  ext i j
  simp [principalBlock, padBlock, i.2, j.2]

omit [Fintype ι] in
/-- If `X_D` and `Y_D` are positive definite and `(X_D)⁻¹`, `(Y_D)⁻¹` have the same quadratic
form, then `X_D = Y_D`. -/
private theorem principalBlock_eq_of_qf_eq {D : Finset ι} {X Y : Matrix ι ι ℝ}
    (hX : (principalBlock X D).PosDef) (hY : (principalBlock Y D).PosDef)
    (h : ∀ x, qf D X x = qf D Y x) : principalBlock X D = principalBlock Y D := by
  set A := (principalBlock X D)⁻¹ - (principalBlock Y D)⁻¹
  have hA : A.IsHermitian := hX.inv.isHermitian.sub hY.inv.isHermitian
  have hq : ∀ v, star v ⬝ᵥ A *ᵥ v = 0 := fun v ↦ by
    have := h (ext0 D v)
    simp only [qf, res_ext0] at this
    simp [A, sub_mulVec, dotProduct_sub, this]
  have hpsd : A.PosSemidef :=
    PosSemidef.of_dotProduct_mulVec_nonneg hA fun v ↦ (hq v).ge
  have hA0 : A = 0 := by
    ext i j
    have := (hpsd.dotProduct_mulVec_zero_iff (x := Pi.single j 1)).1 (hq _)
    simpa [mulVec_single] using congrFun this i
  have hinv : (principalBlock X D)⁻¹ = (principalBlock Y D)⁻¹ := sub_eq_zero.1 hA0
  exact inv_inj hinv hX.det_pos.ne'.isUnit


/-- Identification of a block of `Σ` by marginal precisions: if `Σ_W` is positive definite,
`D ⊆ W`, and `qf W Σ = qf D X + R` with `R ≥ 0` vanishing for a suitable change of any vector
off `D`, then `Σ_D = X_D`. -/
private theorem principalBlock_eq_of_qf_eq_add {Sig X : Matrix ι ι ℝ} {D W : Finset ι}
    (hSig : (principalBlock Sig W).PosDef) (hDW : D ⊆ W) (hX : (principalBlock X D).PosDef)
    (R : (ι → ℝ) → ℝ) (hE : ∀ y, qf W Sig y = qf D X y + R y) (hR : ∀ y, 0 ≤ R y)
    (hR0 : ∀ x : ι → ℝ, ∃ y : ι → ℝ, (∀ i ∈ D, y i = x i) ∧ R y = 0) :
    principalBlock Sig D = principalBlock X D := by
  refine principalBlock_eq_of_qf_eq (posDef_principalBlock_of_subset hSig hDW) hX fun x ↦ ?_
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, hRy⟩ := hR0 x
    have h1 := (qf_le_qf hSig hDW y).1
    rw [hE, hRy, add_zero, qf_congr D X hy] at h1
    rwa [qf_congr D Sig hy] at h1
  · obtain ⟨y, hy, heq⟩ := (qf_le_qf hSig hDW x).2
    rw [← heq, hE, qf_congr D X hy]
    linarith [hR y]

/-- If `S ⊆ U`, `S ⊆ D` and `U ∩ D ⊆ S`, any vector can be changed off `D` so that its
quadratic forms `qf U X` and `qf S X` agree. -/
private theorem exists_qf_eq_of_subset {X : Matrix ι ι ℝ} {U D S : Finset ι}
    (hX : (principalBlock X U).PosDef) (hSU : S ⊆ U) (hSD : S ⊆ D)
    (hUD : ∀ i ∈ U, i ∈ D → i ∈ S) (x : ι → ℝ) :
    ∃ y : ι → ℝ, (∀ i ∈ D, y i = x i) ∧ qf U X y = qf S X y := by
  obtain ⟨y₀, hy₀, heq⟩ := (qf_le_qf hX hSU x).2
  refine ⟨fun i ↦ if i ∈ D then x i else y₀ i, fun i hi ↦ by simp [hi], ?_⟩
  rw [qf_congr S X (y := x) fun i hi ↦ by simp [hSD hi], ← heq]
  refine qf_congr U X fun i hi ↦ ?_
  by_cases hiD : i ∈ D
  · simp [hiD, hy₀ i (hUD i hi hiD)]
  · simp [hiD]

/-- `[(X_D)⁻¹]^V`: the inverse of the block `X_D`, padded with zeros. -/
private noncomputable def padInv (D : Finset ι) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  padBlock D (principalBlock X D)⁻¹

/-- The quadratic form of `[(X_D)⁻¹]^V` is `qf D X`. -/
private theorem dotProduct_mulVec_padInv (D : Finset ι) (X : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ padInv D X *ᵥ x = qf D X x :=
  dotProduct_mulVec_padBlock D _ x

omit [Fintype ι] in
/-- `[(X_D)⁻¹]^V` is symmetric when `X_D` is positive definite. -/
private theorem transpose_padInv {D : Finset ι} {X : Matrix ι ι ℝ}
    (hX : (principalBlock X D).PosDef) : (padInv D X)ᵀ = padInv D X := by
  have ht : ((principalBlock X D)⁻¹)ᵀ = (principalBlock X D)⁻¹ := by
    simpa using hX.inv.isHermitian.eq
  ext i j
  simp only [padInv, padBlock, transpose_apply]
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D
  · simp only [hi, hj, and_self, dite_true]
    exact congrFun (congrFun ht ⟨i, hi⟩) ⟨j, hj⟩
  all_goals simp [hi, hj]

/-- Gluing step of the decomposable estimate: if `P_H` and `Q_C` are positive definite and `P`
and `Q` agree on `S = C ∩ H`, then `N = [(P_H)⁻¹]^V + [(Q_C)⁻¹]^V - [(Q_S)⁻¹]^V` has positive
definite block on `H ∪ C`, and the inverse of that block agrees with `P` on `H` and with `Q` on
`C`. -/
private theorem glue {P Q N : Matrix ι ι ℝ} {H C : Finset ι} (hP : (principalBlock P H).PosDef)
    (hQ : (principalBlock Q C).PosDef) (hPQ : ∀ a ∈ C ∩ H, ∀ b ∈ C ∩ H, P a b = Q a b)
    (hN : N = padInv H P + padInv C Q - padInv (C ∩ H) Q) :
    (principalBlock N (H ∪ C)).PosDef ∧
      principalBlock (padBlock (H ∪ C) (principalBlock N (H ∪ C))⁻¹) H = principalBlock P H ∧
      principalBlock (padBlock (H ∪ C) (principalBlock N (H ∪ C))⁻¹) C = principalBlock Q C := by
  set S := C ∩ H
  set W := H ∪ C
  have hSC : S ⊆ C := Finset.inter_subset_left
  have hSH : S ⊆ H := Finset.inter_subset_right
  have hHW : H ⊆ W := Finset.subset_union_left
  have hCW : C ⊆ W := Finset.subset_union_right
  have hQS : (principalBlock Q S).PosDef := posDef_principalBlock_of_subset hQ hSC
  have hPS : (principalBlock P S).PosDef := posDef_principalBlock_of_subset hP hSH
  have hPQS : principalBlock P S = principalBlock Q S := by
    ext a b
    exact hPQ a a.2 b b.2
  have hqfS : ∀ x, qf S P x = qf S Q x := fun x ↦ by simp only [qf, hPQS]
  have hform : ∀ x, x ⬝ᵥ N *ᵥ x = qf H P x + qf C Q x - qf S Q x := fun x ↦ by
    simp only [hN, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub,
      dotProduct_mulVec_padInv]
  have hCS : ∀ x, qf S Q x ≤ qf C Q x := fun x ↦ (qf_le_qf hQ hSC x).1
  have hHS : ∀ x, qf S Q x ≤ qf H P x := fun x ↦ hqfS x ▸ (qf_le_qf hP hSH x).1
  have hNt : Nᵀ = N := by
    rw [hN, transpose_sub, transpose_add, transpose_padInv hP, transpose_padInv hQ,
      transpose_padInv hQS]
  -- the form of `N` on `W`
  have hformW : ∀ y, res W y ⬝ᵥ principalBlock N W *ᵥ res W y =
      qf H P y + qf C Q y - qf S Q y := fun y ↦ by
    have hz := ext0_eq_zero (subset_refl W) (res W y)
    rw [← res_ext0 W (res W y), mulVec_res N _ hz, dotProduct_res _ _ hz, hform]
    have hag : ∀ i ∈ W, ext0 W (res W y) i = y i := fun i hi ↦ by simp [ext0, res, hi]
    rw [qf_congr H P fun i hi ↦ hag i (hHW hi), qf_congr C Q fun i hi ↦ hag i (hCW hi),
      qf_congr S Q fun i hi ↦ hag i (hCW (hSC hi))]
  have hNW : (principalBlock N W).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv ↦ ?_
    · have : (principalBlock N W)ᵀ = principalBlock N W := by
        ext i j
        exact congrFun (congrFun hNt i.1) j.1
      simpa [IsHermitian] using this
    · simp only [star_trivial]
      by_contra hle
      push Not at hle
      set x := ext0 W v
      have hxv : res W x = v := res_ext0 W v
      rw [← hxv, hformW] at hle
      have hPx : qf H P x = 0 := le_antisymm (by linarith [hCS x])
        (by have := (hP.inv.posSemidef.dotProduct_mulVec_nonneg (res H x)); simpa [qf] using this)
      have hxH := res_eq_zero_of_qf_eq_zero hP hPx
      have hSx : qf S Q x = 0 := by
        have : res S x = 0 := funext fun i ↦ congrFun hxH ⟨i.1, hSH i.2⟩
        simp [qf, this]
      have hCx : qf C Q x = 0 := le_antisymm (by linarith) (by linarith [hCS x])
      have hxC := res_eq_zero_of_qf_eq_zero hQ hCx
      apply hv
      rw [← hxv]
      funext i
      rcases Finset.mem_union.1 i.2 with h | h
      · exact congrFun hxH ⟨i.1, h⟩
      · exact congrFun hxC ⟨i.1, h⟩
  set Sig := padBlock W (principalBlock N W)⁻¹
  have hSigW : principalBlock Sig W = (principalBlock N W)⁻¹ := principalBlock_padBlock _ _
  have hSig : (principalBlock Sig W).PosDef := hSigW ▸ hNW.inv
  have hE : ∀ y, qf W Sig y = qf H P y + qf C Q y - qf S Q y := fun y ↦ by
    rw [qf, hSigW, nonsing_inv_nonsing_inv _ hNW.det_pos.ne'.isUnit, hformW]
  refine ⟨hNW, ?_, ?_⟩
  · refine principalBlock_eq_of_qf_eq_add hSig hHW hP (fun y ↦ qf C Q y - qf S Q y)
      (fun y ↦ by rw [hE]; ring) (fun y ↦ by linarith [hCS y]) fun x ↦ ?_
    obtain ⟨y, hy, heq⟩ := exists_qf_eq_of_subset hQ hSC hSH
      (fun i hi hiH ↦ Finset.mem_inter.2 ⟨hi, hiH⟩) x
    exact ⟨y, hy, by rw [heq, sub_self]⟩
  · refine principalBlock_eq_of_qf_eq_add hSig hCW hQ (fun y ↦ qf H P y - qf S P y)
      (fun y ↦ by rw [hE, hqfS]; ring) (fun y ↦ by linarith [(qf_le_qf hP hSH y).1])
      fun x ↦ ?_
    obtain ⟨y, hy, heq⟩ := exists_qf_eq_of_subset hP hSH hSC
      (fun i hi hiC ↦ Finset.mem_inter.2 ⟨hiC, hi⟩) x
    exact ⟨y, hy, by rw [heq, sub_self]⟩


omit [Fintype ι] [DecidableEq ι] in
/-- Entries of a principal block. -/
private theorem principalBlock_apply (X : Matrix ι ι ℝ) (D : Finset ι) (a b : ι) (ha : a ∈ D)
    (hb : b ∈ D) : principalBlock X D ⟨a, ha⟩ ⟨b, hb⟩ = X a b := rfl

omit [Fintype ι] in
/-- `[(X_D)⁻¹]^V` vanishes outside `D × D`. -/
private theorem padInv_apply_eq_zero {D : Finset ι} (X : Matrix ι ι ℝ) {a b : ι}
    (h : ¬ (a ∈ D ∧ b ∈ D)) : padInv D X a b = 0 := by
  simp [padInv, padBlock, h]

omit [Fintype ι] in
/-- A matrix vanishing outside `D × D` is the padding of its `D`-block. -/
private theorem padBlock_principalBlock {D : Finset ι} {X : Matrix ι ι ℝ}
    (h : ∀ a b, ¬ (a ∈ D ∧ b ∈ D) → X a b = 0) : padBlock D (principalBlock X D) = X := by
  ext a b
  by_cases hab : a ∈ D ∧ b ∈ D
  · simp [padBlock, principalBlock, hab]
  · simp [padBlock, hab, h a b hab]

omit [Fintype ι] [DecidableEq ι] in
/-- The empty block is positive definite. -/
private theorem posDef_principalBlock_empty (X : Matrix ι ι ℝ) :
    (principalBlock X ∅).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv ↦
    (hv (funext fun i ↦ (Finset.notMem_empty _ i.2).elim)).elim
  ext i
  exact (Finset.notMem_empty _ i.2).elim

/-- Induction over a perfect sequence: the partial estimate on the first `m` cliques is the
inverse of a positive definite block on `C₀ ∪ ⋯ ∪ C_{m-1}` that agrees with `ssd` on each of these
cliques. -/
private theorem exists_padInv_cliqueHistory_eq (G : SimpleGraph ι) {k : ℕ}
    (C : Fin k → Finset ι) (hC : IsPerfectCliqueSequence G C) (ssd : Matrix ι ι ℝ)
    (hblock : ∀ j, (principalBlock ssd (C j)).PosDef) :
    ∀ m ≤ k, ∃ Sig : Matrix ι ι ℝ, (principalBlock Sig (cliqueHistory C m)).PosDef ∧
      padInv (cliqueHistory C m) Sig = ∑ j ∈ Finset.univ.filter (fun j : Fin k ↦ (j : ℕ) < m),
        (padInv (C j) ssd - padInv (cliqueSeparator C j) ssd) ∧
      ∀ j : Fin k, (j : ℕ) < m → ∀ a ∈ C j, ∀ b ∈ C j, Sig a b = ssd a b := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : cliqueHistory C 0 = ∅ := by simp [cliqueHistory]
    refine ⟨0, h0 ▸ posDef_principalBlock_empty 0, ?_, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
    rw [h0]
    ext a b
    simp [padInv, padBlock]
  | succ m ih =>
    intro hm
    obtain ⟨Sig, hSig, hK, hag⟩ := ih (by omega)
    set j : Fin k := ⟨m, by omega⟩ with hjdef
    have hfil : Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < m + 1) =
        insert j (Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < m) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hjdef,
        Fin.ext_iff]
      omega
    have hjn : j ∉ Finset.univ.filter fun i : Fin k ↦ (i : ℕ) < m := by simp [hjdef]
    have hH : cliqueHistory C (m + 1) = cliqueHistory C m ∪ C j := by
      ext v
      simp only [cliqueHistory, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, hv⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact Or.inl ⟨i, h, hv⟩
        · exact Or.inr (by rwa [show i = j from Fin.ext h] at hv)
      · rintro (⟨i, hi, hv⟩ | hv)
        · exact ⟨i, by omega, hv⟩
        · exact ⟨j, by simp [hjdef], hv⟩
    have hsepj : cliqueSeparator C j = C j ∩ cliqueHistory C m := by
      ext v
      simp [cliqueSeparator, cliqueHistory, Fin.lt_def, hjdef]
    have hsub : ∀ i : Fin k, (i : ℕ) < m → C i ⊆ cliqueHistory C m := fun i hi v hv ↦ by
      simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, hv⟩
    have hPQ : ∀ a ∈ C j ∩ cliqueHistory C m, ∀ b ∈ C j ∩ cliqueHistory C m,
        Sig a b = ssd a b := by
      intro a ha b hb
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · have : cliqueHistory C m = ∅ := by subst h0; simp [cliqueHistory]
        simp [this] at ha
      · obtain ⟨i, hij, hi⟩ := hC.2.2.2 j hpos
        rw [← hsepj] at ha hb
        exact hag i (Fin.lt_def.1 hij) a (hi ha) b (hi hb)
    obtain ⟨hNW, h1, h2⟩ := glue hSig (hblock j) hPQ rfl
    set N := padInv (cliqueHistory C m) Sig + padInv (C j) ssd -
      padInv (C j ∩ cliqueHistory C m) ssd with hNdef
    set W := cliqueHistory C m ∪ C j
    have hNsupp : ∀ a b, ¬ (a ∈ W ∧ b ∈ W) → N a b = 0 := by
      intro a b hab
      have h3 : ∀ E : Finset ι, E ⊆ W → ∀ X : Matrix ι ι ℝ, padInv E X a b = 0 :=
        fun E hE X ↦ padInv_apply_eq_zero X fun h ↦ hab ⟨hE h.1, hE h.2⟩
      simp only [hNdef, Matrix.sub_apply, Matrix.add_apply]
      rw [h3 _ Finset.subset_union_left, h3 _ Finset.subset_union_right,
        h3 _ (Finset.inter_subset_left.trans Finset.subset_union_right)]
      ring
    refine ⟨padBlock W (principalBlock N W)⁻¹, ?_, ?_, ?_⟩
    · rw [hH, principalBlock_padBlock]
      exact hNW.inv
    · rw [hH, padInv, principalBlock_padBlock, nonsing_inv_nonsing_inv _ hNW.det_pos.ne'.isUnit,
        padBlock_principalBlock hNsupp, hfil, Finset.sum_insert hjn, ← hK, hNdef, ← hsepj]
      abel
    · intro i hi a ha b hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · have := congrFun (congrFun h1 ⟨a, hsub i hi ha⟩) ⟨b, hsub i hi hb⟩
        rw [principalBlock_apply, principalBlock_apply] at this
        rw [this, hag i hi a ha b hb]
      · have hij : i = j := Fin.ext hi
        subst hij
        have := congrFun (congrFun h2 ⟨a, ha⟩) ⟨b, hb⟩
        rwa [principalBlock_apply, principalBlock_apply] at this


/-- GAPS 105.36, Gaussian decomposable model: for a perfect sequence `C` of the maximal cliques
of `G` (so that `G` is decomposable) and `n > 0` observations, if every clique block of the
sum-of-squares matrix `ssd` is positive definite (which holds almost surely when
`n > max_C |C|` for a Gaussian sample), the maximum likelihood estimate of the concentration
matrix exists, is unique, and equals `n (∑_C [(ssd_C)⁻¹]^V - ∑_S ν(S) [(ssd_S)⁻¹]^V)`.
The likelihood involves `ssd` only through its clique blocks, so no condition on `ssd` outside
them is needed. The almost-sure existence criterion `n > max_C |C|` as a necessary condition
is not stated. -/
theorem isConcentrationMLE_decomposableConcentrationMLE (G : SimpleGraph ι) {k : ℕ}
    (C : Fin k → Finset ι) (hC : IsPerfectCliqueSequence G C) (n : ℕ) (hn : 0 < n)
    (ssd : Matrix ι ι ℝ) (hblock : ∀ j, (principalBlock ssd (C j)).PosDef) :
    IsConcentrationMLE G n ssd (decomposableConcentrationMLE C n ssd) := by
  obtain ⟨Sig, hSig, hK, hag⟩ := exists_padInv_cliqueHistory_eq G C hC ssd hblock k le_rfl
  have hall : cliqueHistory C k = Finset.univ := by
    refine Finset.eq_univ_of_forall fun v ↦ ?_
    obtain ⟨D, hD, hDmax⟩ := exists_maximal_isClique_superset G (T := {v}) (by simp)
    obtain ⟨m, rfl⟩ := hC.2.2.1 D hDmax
    simp only [cliqueHistory, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, m.isLt, hD (by simp)⟩
  have hfk : Finset.univ.filter (fun j : Fin k ↦ (j : ℕ) < k) = Finset.univ := by
    ext j
    simp
  rw [hall, hfk] at hK
  rw [hall] at hSig
  have hag' : ∀ j : Fin k, ∀ a ∈ C j, ∀ b ∈ C j, Sig a b = ssd a b := fun j ↦ hag j j.isLt
  -- `Sig` is positive definite with inverse `∑_j ([(ssd_{C_j})⁻¹]^V - [(ssd_{S_j})⁻¹]^V)`
  have hSigPD : Sig.PosDef := by
    have := hSig.submatrix (e := fun i : ι ↦ (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset ι)))
      fun a b h ↦ congrArg Subtype.val h
    exact this
  have hinv : padInv Finset.univ Sig = Sig⁻¹ := by
    have e := inv_submatrix_equiv Sig (Equiv.subtypeUnivEquiv (p := (· ∈ (Finset.univ : Finset ι)))
      Finset.mem_univ) (Equiv.subtypeUnivEquiv Finset.mem_univ)
    ext a b
    simp only [padInv, padBlock, Finset.mem_univ, and_self, dite_true]
    exact congrFun (congrFun e ⟨a, Finset.mem_univ a⟩) ⟨b, Finset.mem_univ b⟩
  have hS0 : ∀ j : Fin k, (j : ℕ) = 0 → cliqueSeparator C j = ∅ := fun j hj ↦ by
    ext v
    simp [cliqueSeparator, Fin.lt_def, hj]
  have hMLE : decomposableConcentrationMLE C n ssd = (n : ℝ) • Sig⁻¹ := by
    rw [← hinv, hK, decomposableConcentrationMLE, Finset.sum_sub_distrib]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with hj
    · rw [hS0 j hj]
      ext a b
      simp [padInv, padBlock]
    · rfl
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hu : IsUnit Sig.det := hSigPD.det_pos.ne'.isUnit
  have hSinv : ((n : ℝ)⁻¹ • Sig)⁻¹ = (n : ℝ) • Sig⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_inv_cancel₀ hn', one_smul, nonsing_inv_mul _ hu]
  rw [hMLE, ← hSinv]
  refine isConcentrationMLE_inv_of_apply_eq G ssd _ (hSigPD.smul (inv_pos.2 (by positivity)))
    (fun a b hab ↦ ?_) (fun a b hab hadj ↦ ?_)
  · have hpair : G.IsClique (({a, b} : Finset ι) : Set ι) := by
      rw [Finset.coe_pair]
      exact SimpleGraph.isClique_pair.2 fun hne ↦ hab.resolve_left hne
    obtain ⟨D, hD, hDmax⟩ := exists_maximal_isClique_superset G hpair
    obtain ⟨m, rfl⟩ := hC.2.2.1 D hDmax
    rw [Matrix.smul_apply, hag' m a (hD (by simp)) b (hD (by simp)), smul_eq_mul, div_eq_inv_mul]
  · rw [hSinv, ← hinv, hK, Matrix.smul_apply, Matrix.sum_apply]
    rw [Finset.sum_eq_zero, smul_zero]
    intro j _
    have hnot : ¬ (a ∈ C j ∧ b ∈ C j) := fun h ↦ hadj ((hC.2.1 j).prop h.1 h.2 hab)
    have hsep : ∀ v ∈ cliqueSeparator C j, v ∈ C j := fun v hv ↦ by
      simp only [cliqueSeparator, Finset.mem_inter] at hv
      exact hv.1
    rw [Matrix.sub_apply, padInv_apply_eq_zero _ hnot,
      padInv_apply_eq_zero (D := cliqueSeparator C j) _ fun h ↦ hnot ⟨hsep a h.1, hsep b h.2⟩,
      sub_zero]

end Gaussian

end CKSD
