module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem union_botElem (x : Pomega) : x ∪ botElem = x := Set.union_empty x

end DomainTheory.DataTypesAsLattices
