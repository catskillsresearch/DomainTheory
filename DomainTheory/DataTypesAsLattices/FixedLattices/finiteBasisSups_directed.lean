module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.ContinuousBasis
public import DomainTheory.DataTypesAsLattices.FixedLattices.finiteBasisSups

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem finiteBasisSups_directed {α : Type u} [CompleteLattice α]
    (d : ℕ → α) (x : Set ℕ) :
    DirectedSet (finiteBasisSups d x) := by
  constructor
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
