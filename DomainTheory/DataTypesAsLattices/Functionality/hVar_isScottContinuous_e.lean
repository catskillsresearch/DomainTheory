/-ai
For a fixed environment t, the map sending e to the variable clause hVar e t is Scott continuous.

It is the composite of application of the constant t with the payload projection, and both factors are Scott continuous.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hVar_isScottContinuous_e (t : Pomega) :
    IsScottContinuous (fun e => hVar e t) :=
  theorem_1_3 (f := funOf t) (g := expPayload)
    (funOf_isScottContinuous t) (funOf_isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
