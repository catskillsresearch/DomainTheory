/-ai
The union of a set with the empty set on the right is the set itself.

This is the empty-union law.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem union_botElem (x : Pomega) : x ∪ botElem = x := Set.union_empty x

end DomainTheory.DataTypesAsLattices
