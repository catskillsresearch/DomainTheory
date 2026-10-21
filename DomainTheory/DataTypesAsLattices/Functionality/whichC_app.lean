/-ai
Application of the summand tag to u is the application of u at the numeral 0.

This is the application law for the first projection.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem whichC_app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC_app u

end DomainTheory.DataTypesAsLattices
