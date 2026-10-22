
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem whichC_app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC_app u

end DomainTheory.DataTypesAsLattices
