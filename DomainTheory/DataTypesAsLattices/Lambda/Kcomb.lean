
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Kcomb : Pomega := graph (fun x => graph (fun _ => x))

end DomainTheory.DataTypesAsLattices
