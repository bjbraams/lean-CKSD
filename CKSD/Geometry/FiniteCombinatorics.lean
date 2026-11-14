module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

/-!
# Finite counting identities

Disjoint-filter cardinality identities used by finite persistence rank formulas and diagram
multiplicity reconstruction. The statements are independent of the simplicial-chain model.

## Main results

* `CKSD.card_filter_eq_add_of_iff`: the cardinality of a filter split into two disjoint filters.
-/

@[expose] public section

namespace CKSD

/-- Counting a disjoint union of two filters: if `P` is the disjoint union of `Q` and `S`, the
filter of `P` has the sum of the two cardinalities. -/
theorem card_filter_eq_add_of_iff {α : Type*} [Fintype α] {P Q S : α → Prop}
    [DecidablePred P] [DecidablePred Q] [DecidablePred S] (hiff : ∀ x, P x ↔ Q x ∨ S x)
    (hdisj : ∀ x, Q x → ¬ S x) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card + (Finset.univ.filter S).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp [hiff]
  · rw [Finset.disjoint_filter]
    exact fun x _ ↦ hdisj x

end CKSD
