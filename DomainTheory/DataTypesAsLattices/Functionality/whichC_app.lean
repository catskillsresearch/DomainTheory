
module

public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.whichC

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem whichC_app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC.app u

end DomainTheory.DataTypesAsLattices
