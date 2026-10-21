/-ai
Applying the Boolean retract to u returns the doubly strict conditional of u on the numerals zero and one.

This is β-conversion, from Scott continuity of the conditional in its test argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boolR_app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet_isScottContinuous_left (ofNat 0) (ofNat 1)) u

end DomainTheory.DataTypesAsLattices
