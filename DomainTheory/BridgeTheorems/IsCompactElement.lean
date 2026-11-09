module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Directed

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

def IsCompactElement (k : D) : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → k ≤ sSup S → ∃ s ∈ S, k ≤ s

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
