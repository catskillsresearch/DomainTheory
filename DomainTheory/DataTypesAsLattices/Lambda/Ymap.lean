/-ai
The parameterized fixed-point map of a binary operation g is the graph of the map sending x to the fixed point of g at x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Ymap (g : Pomega → Pomega → Pomega) : Pomega :=
  graph (fun x => fix (g x))

end DomainTheory.DataTypesAsLattices
