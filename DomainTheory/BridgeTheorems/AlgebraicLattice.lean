module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.BridgeTheorems.IsCompactElement
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.UpperLower.Basic
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

class AlgebraicLattice (D : Type*) [CompleteLattice D] : Prop where
  out : ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
