
module

public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.outC

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outC_app (u : Pomega) : funOf outC u = funOf u (ofNat 1) :=
  sndC.app u

end DomainTheory.DataTypesAsLattices
