/-ai
Applying the integer functional at f to u returns the doubly strict conditional of u on the numeral zero and the conditional of the application of f to the predecessor of u on u and u.

This is β-conversion, from Scott continuity of that conditional map in the input.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intF_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intF_app (f u : Pomega) :
    funOf (intF f) u =
      dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u) :=
  beta (intF_map_isScottContinuous f) u

end DomainTheory.DataTypesAsLattices
