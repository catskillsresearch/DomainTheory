/-ai
A complete lattice is algebraic when every element is the supremum of the set of compact elements lying under it, and that set is nonempty and directed.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.BridgeTheorems.IsCompactElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Algebraicity: every element is the directed lub of compact elements below it. -/
class AlgebraicLattice (D : Type*) [CompleteLattice D] : Prop where
  out : ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
