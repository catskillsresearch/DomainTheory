
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Vstep

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def VapplyY (a x : Pomega) : Pomega := fix (Vstep a x)

end DomainTheory.DataTypesAsLattices
