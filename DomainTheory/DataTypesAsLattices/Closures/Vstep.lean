
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** `V(a)(x) = Y(λy. x ∪ a(y))`. -/
def Vstep (a x : Pomega) (y : Pomega) : Pomega := x ∪ funOf a y

end DomainTheory.DataTypesAsLattices
