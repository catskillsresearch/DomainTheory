module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Order-theoretic compactness: inaccessible by nonempty directed suprema. -/
def IsCompactElement (k : D) : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → k ≤ sSup S → ∃ s ∈ S, k ≤ s

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
