module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem botElem_union (x : Pomega) : botElem ∪ x = x := Set.empty_union x

end DomainTheory.DataTypesAsLattices
