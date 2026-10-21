/-ai
The product a ⊗ b, applied to u, equals the sequence pair of the application of a to the application of u at the numeral 0 and the application of b to the application of u at the numeral 1.

This is the beta law for the graph of that body, using Scott continuity of the body.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem tensorR_app (a b u : Pomega) :
    funOf (tensorR a b) u =
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))) :=
  beta (tensorR_map_isScottContinuous a b) u

end DomainTheory.DataTypesAsLattices
