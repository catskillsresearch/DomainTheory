/-ai
For a fixed expression e, the map sending an environment t to the variable clause hVar e t is Scott continuous.

It is application in the function argument at the constant payload of e.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hVar_isScottContinuous_t (e : Pomega) :
    IsScottContinuous (fun t => hVar e t) :=
  funOf_isScottContinuous_left (expPayload e)

end DomainTheory.DataTypesAsLattices
