/-ai
The iterates of an endomap f of Pω, starting from the bottom element, send zero to the bottom element and send the successor of n to f applied to the n-th iterate.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Iterate `f` starting from `⊥`. -/
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

end DomainTheory.DataTypesAsLattices
