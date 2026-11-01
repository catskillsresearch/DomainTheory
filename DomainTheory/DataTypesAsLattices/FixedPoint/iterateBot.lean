module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

end DomainTheory.DataTypesAsLattices
