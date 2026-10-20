module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))

end DomainTheory.DataTypesAsLattices
