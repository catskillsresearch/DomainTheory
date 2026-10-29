module

public import DomainTheory.ContinuousLattice.ContinuousLattices.IdempotentFixedPoint

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {L : Type*} [CompleteLattice L] {e : L → L}

namespace IdempotentFixedPoint

/-- Supremum in the fixed-point set: `e` applied to the ambient supremum. -/
@[reducible] noncomputable def supremumSet (hidem : ∀ x, e (e x) = e x) :
    SupSet (IdempotentFixedPoint e) :=
  ⟨fun S => ⟨e (sSup (Subtype.val '' S)), hidem _⟩⟩

namespace supremumSet

theorem isLUB (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    letI := IdempotentFixedPoint.supremumSet hidem
    ∀ S : Set (IdempotentFixedPoint e), IsLUB S (sSup S) := by
  let := IdempotentFixedPoint.supremumSet hidem
  intro S
  constructor
  · intro k hk
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show (k : L) ≤ e (sSup (Subtype.val '' S))
    calc (k : L) = e k := k.2.symm
      _ ≤ e (sSup (Subtype.val '' S)) :=
          hmono (le_sSup (Set.mem_image_of_mem _ hk))
  · intro w hw
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show e (sSup (Subtype.val '' S)) ≤ (w : L)
    calc e (sSup (Subtype.val '' S)) ≤ e (w : L) := by
          refine hmono (sSup_le ?_)
          rintro _ ⟨k, hk, rfl⟩
          exact hw hk
      _ = (w : L) := w.2

end supremumSet

end IdempotentFixedPoint

end DomainTheory.ContinuousLattice
