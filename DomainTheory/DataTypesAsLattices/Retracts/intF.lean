/-ai
The integer functional sends f to the graph of the map which, by the doubly strict conditional, returns the numeral zero, or else the conditional of the application of f to the predecessor against the input itself. Scott's clause (4.7) is int(u) = u ⊒ 0, (int(u − 1) ⊒ u, u).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.7).** The integer functional
`int(u) = u ⊒ 0, (int(u−1) ⊒ u, u)`. -/
def intF (f : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))

end DomainTheory.DataTypesAsLattices
