/-ai
The union of the empty set with a set x is x.

This is the empty-union identity.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem botElem_union (x : Pomega) : botElem ∪ x = x := Set.empty_union x

end DomainTheory.DataTypesAsLattices
