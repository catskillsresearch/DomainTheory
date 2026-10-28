module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def dEq : Pomega := fix selfArrowStep

end DomainTheory.DataTypesAsLattices
