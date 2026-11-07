module

public import CKSD.Geometry.SimplicialPersistence
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Interval decompositions and the isometry theorem

An interval basis of a persistence module `V` indexed by a preorder `P` is a family of nonempty
order-convex supports `I_j ⊆ P` together with bases of every `V_t` indexed by the `j` with
`t ∈ I_j`, such that each structure map `V_s → V_t` sends the basis vector `j` to the basis vector
`j` when `t ∈ I_j` and to zero otherwise. Such a basis is exactly an isomorphism of `V` with the
direct sum of the interval modules `𝕜_{I_j}`; the multiset of supports is the barcode.

Sources: GAPS 108.18 and 108.20.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set
open scoped ENNReal

namespace CKSD

attribute [local instance] Classical.propDecidable

/-- An interval basis of a persistence module over a preorder: a decomposition of `V` as a direct
sum of interval modules, with supports `support j`. -/
structure IntervalBasis {P : Type*} [Preorder P] {K : Type*} [Field K] (V : P ⥤ ModuleCat K)
    (ι : Type*) where
  /-- Support interval of the `j`th summand. -/
  support : ι → Set P
  /-- Supports are nonempty. -/
  support_nonempty : ∀ j, (support j).Nonempty
  /-- Supports are intervals of the index order. -/
  support_ordConnected : ∀ j, (support j).OrdConnected
  /-- A basis of `V_t` indexed by the summands alive at `t`. -/
  basis : ∀ t, Module.Basis {j // t ∈ support j} K (V.obj t)
  /-- Structure maps send each basis vector to its continuation, or to zero after its death. -/
  map_basis : ∀ s t (h : s ≤ t) (j : {j // s ∈ support j}),
    (V.map (homOfLE h)).hom (basis s j) =
      if ht : t ∈ support j.1 then basis t ⟨j.1, ht⟩ else 0

/-- GAPS 108.18, existence (Crawley-Boevey's theorem): every pointwise finite-dimensional
persistence module over `ℝ` with coefficients in a field is a direct sum of interval modules.
The finite totally ordered case is Gabriel's theorem in type `A_n`. -/
theorem exists_intervalBasis_of_isPointwiseFiniteDimensional {K : Type*} [Field K]
    (V : PersistenceModule K) (hV : IsPointwiseFiniteDimensional V) :
    ∃ ι : Type, Nonempty (IntervalBasis V ι) := by
  sorry

/-- GAPS 108.18, uniqueness: the multiset of intervals of an interval decomposition of a
pointwise finite-dimensional persistence module over `ℝ` is unique, that is, any two interval
bases are related by a support-preserving bijection of their index sets. -/
theorem IntervalBasis.exists_equiv_support_eq {K : Type*} [Field K] {V : PersistenceModule K}
    (hV : IsPointwiseFiniteDimensional V) {ι ι' : Type*} (B : IntervalBasis V ι)
    (B' : IntervalBasis V ι') : ∃ e : ι ≃ ι', ∀ j, B'.support (e j) = B.support j := by
  sorry

/-- GAPS 108.20, the isometry theorem, for persistence modules of finite type with closed-open
bars: if `U` and `V` decompose into finitely many interval modules over `[b, d)` and `[b, ∞)`,
their interleaving distance equals the bottleneck distance of their diagrams (both are `∞`
exactly when the numbers of essential bars differ). The general `q`-tame case, with diagrams
defined from rank functions and intervals with arbitrary endpoint types, is not formalized. -/
theorem interleavingEDist_eq_fullBottleneckEDist {K : Type*} [Field K]
    (U V : PersistenceModule K) {α β κ κ' : Type*} [Fintype α] [Fintype β] [Fintype κ]
    [Fintype κ'] (D : FiniteDeathDiagram α) (e : κ → ℝ) (E : FiniteDeathDiagram β) (e' : κ' → ℝ)
    (BU : IntervalBasis U (α ⊕ κ)) (BV : IntervalBasis V (β ⊕ κ'))
    (hBU : ∀ i, BU.support (.inl i) = Ico (D.birth i) (D.death i))
    (hBU' : ∀ k, BU.support (.inr k) = Ici (e k))
    (hBV : ∀ i, BV.support (.inl i) = Ico (E.birth i) (E.death i))
    (hBV' : ∀ k, BV.support (.inr k) = Ici (e' k)) :
    interleavingEDist U V = fullBottleneckEDist D e E e' := by
  sorry

end CKSD
