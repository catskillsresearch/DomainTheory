/-ai
The fixed-point approximant of the universe operation at a and x is the least fixed point of the step sending y to the union of x with a(y).
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Vstep

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def VapplyY (a x : Pomega) : Pomega := fix (Vstep a x)

end DomainTheory.DataTypesAsLattices
