/-ai
The second-component combinator is the graph of the map sending a set to its value at the singleton one.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def sndC : Pomega := graph (fun u => funOf u (ofNat 1))

end DomainTheory.DataTypesAsLattices
