
module
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

end DomainTheory.DataTypesAsLattices
