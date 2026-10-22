module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** Continuous operator whose least fixed point is
the syntax-directed interpreter. -/
def HF (H : Pomega) : Pomega :=
  graph (fun e => graph (fun t => Hstep H e t))

end DomainTheory.DataTypesAsLattices
