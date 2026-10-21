/-ai
The combinator S is the graph of the curried map sending u, v, and x to the application of u at x applied to v at x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))

end DomainTheory.DataTypesAsLattices
