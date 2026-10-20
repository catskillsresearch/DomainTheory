module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.BridgeTheorems.IsCompactElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Algebraicity: every element is the directed lub of compact elements below it. -/
def IsAlgebraicLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
