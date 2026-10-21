/-ai
The representing closure is monotone.

If one set of indices is contained in another and a compact element lies below the supremum of the compact elements indexed by the smaller set, each of those compact elements lies below the supremum indexed by the larger set, so the index lies in the representing closure of the larger set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure

@[expose] public section

set_option linter.unusedSectionVars false

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
