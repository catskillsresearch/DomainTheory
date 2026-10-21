/-ai
The representing closure of a countably algebraic lattice is idempotent.

If an index lies in the representing closure of the representing closure, its compact element lies below the supremum of the compact elements indexed by the representing closure. Each of those compact elements already lies below the supremum of the compact elements indexed by the original set, so the outer supremum does as well, and the index lies in the original representing closure. The reverse inclusion is expansiveness of the representing closure.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem representClosure_idem {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    representClosure D (representClosure D x) = representClosure D x := by
  apply subset_antisymm
  · intro m hm
    exact hm.trans (by
      apply sSup_le
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hq
      exact hn)
  · exact representClosure_expansive D (representClosure D x)

end DomainTheory.DataTypesAsLattices
