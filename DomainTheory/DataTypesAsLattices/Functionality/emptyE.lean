module

public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.mem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def emptyE : RestrictedEquiv where
  rel := fun _ _ => False
  symm := fun h => False.elim h
  trans := fun h _ => False.elim h

end DomainTheory.DataTypesAsLattices
