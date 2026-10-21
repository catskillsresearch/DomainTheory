/-ai
Scott 1976, (4.28). The left projection of a tagged sum is the graph of the conditional set of the first component of u, with the second component as the zero branch and bottom as the positive branch.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.28).** Left projection of a tagged sum. -/
def outleftC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem)

end DomainTheory.DataTypesAsLattices
