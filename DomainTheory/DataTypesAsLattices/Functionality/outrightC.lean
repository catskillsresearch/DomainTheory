/-ai
Scott 1976, (4.29). The right projection of a tagged sum is the graph of the conditional set of the first component of u, with bottom as the zero branch and the second component as the positive branch.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.29).** Right projection of a tagged sum. -/
def outrightC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)))

end DomainTheory.DataTypesAsLattices
