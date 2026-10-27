module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.fstC

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def whichC : Pomega := fstC

namespace whichC

theorem app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC.app u

end whichC

end DomainTheory.DataTypesAsLattices
