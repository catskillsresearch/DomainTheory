/-ai
For an indexed family and a set of indices, the set of finite-basis suprema is directed.

The supremum of the family on the empty finite set belongs to the set. Given two finite-basis suprema, indexed by finite sets contained in the index set, the supremum indexed by their union is a common upper bound still in the set. The union remains contained in the index set because each summand is, and each of the two suprema lies below the union supremum because the image of each finite set is contained in the image of the union.
ai-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem finiteBasisSups_directed {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) :
    IsDirectedSet (finiteBasisSups d x) := by
  constructor
  · exact ⟨sSup (d '' ((∅ : Finset ℕ) : Set ℕ)), ∅, by simp, rfl⟩
  · rintro y ⟨t, htx, rfl⟩ z ⟨u, hux, rfl⟩
    refine ⟨sSup (d '' ((t ∪ u : Finset ℕ) : Set ℕ)),
      ⟨t ∪ u, ?_, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp only [Finset.coe_union, Set.mem_union] at hn
      exact hn.elim (fun h => htx h) (fun h => hux h)
    · apply sSup_le
      intro q hq
      apply le_sSup
      exact Set.image_mono (by
        intro n hn
        exact by simp [hn]) hq
    · apply sSup_le
      intro q hq
      apply le_sSup
      exact Set.image_mono (by
        intro n hn
        exact by simp [hn]) hq

end DomainTheory.DataTypesAsLattices
