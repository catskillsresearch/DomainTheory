/-ai
The first projection is the graph of the map sending u to the application of u to the numeral zero. Scott records the pair projections as (4.14) and (4.15).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.14)–(4.15).** Projections of a pair-as-function. -/
def fstC : Pomega := graph (fun u => funOf u (ofNat 0))

end DomainTheory.DataTypesAsLattices
