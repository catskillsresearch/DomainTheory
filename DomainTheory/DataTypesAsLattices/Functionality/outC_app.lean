
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem outC_app (u : Pomega) : funOf outC u = funOf u (ofNat 1) :=
  sndC_app u

end DomainTheory.DataTypesAsLattices
