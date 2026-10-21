/-ai
The coproduct mediator of f and g, applied to u, equals the conditional of the application of u at the numeral 0, returning the application of f or of g to the application of u at the numeral 1.

This is the beta law for the graph of that body, using Scott continuity of the body.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_app (f g u : Pomega) :
    funOf (sumMed f g) u =
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1))) :=
  beta (sumMed_body_isScottContinuous f g) u

end DomainTheory.DataTypesAsLattices
