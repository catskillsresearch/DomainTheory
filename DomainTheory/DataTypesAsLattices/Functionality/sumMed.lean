/-ai
The coproduct mediator of f and g is the graph of the map that reads the application of u at the numeral 0 and, by the conditional, applies f or g to the application of u at the numeral 1.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Coproduct mediator in the category of restricted equivalences. -/
def sumMed (f g : Pomega) : Pomega :=
  graph (fun u =>
    condSet (funOf u (ofNat 0))
      (funOf f (funOf u (ofNat 1)))
      (funOf g (funOf u (ofNat 1))))

end DomainTheory.DataTypesAsLattices
