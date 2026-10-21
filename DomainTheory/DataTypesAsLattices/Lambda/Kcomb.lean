/-ai
The combinator K is the graph of the map sending x to the graph of the constant map with value x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Kcomb : Pomega := graph (fun x => graph (fun _ => x))

end DomainTheory.DataTypesAsLattices
