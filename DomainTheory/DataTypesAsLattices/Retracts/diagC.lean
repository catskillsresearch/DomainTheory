/-ai
The diagonal combinator is the graph of the map sending an element to the sequential pair of that element with itself. Scott records it as (4.16).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.16).** Diagonal combinator. -/
def diagC : Pomega := graph (fun u => pairSeq u u)

end DomainTheory.DataTypesAsLattices
