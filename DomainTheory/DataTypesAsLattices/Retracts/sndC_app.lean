/-ai
The second-component combinator sends a set to the value of that set at the singleton one.

This is the beta law for the Scott-continuous map that evaluates at the singleton one.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











theorem sndC_app (u : Pomega) : funOf sndC u = funOf u (ofNat 1) :=
  beta (funOf_isScottContinuous_left (ofNat 1)) u

end DomainTheory.DataTypesAsLattices
