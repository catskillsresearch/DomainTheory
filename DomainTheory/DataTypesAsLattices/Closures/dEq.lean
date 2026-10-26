module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.25).** Least solution of `d = I ∪ (d ∘→ d)`. -/
def dEq : Pomega := fix selfArrowStep

end DomainTheory.DataTypesAsLattices
