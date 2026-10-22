module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem representClosure_mono {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) {x y : Pomega} (hxy : x ⊆ y) :
    representClosure D x ⊆ representClosure D y := by
  intro m hm
  exact hm.trans (by
    apply sSup_le
    intro q hq
    exact le_sSup (Set.image_mono hxy hq))

end DomainTheory.DataTypesAsLattices
