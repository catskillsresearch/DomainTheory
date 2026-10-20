module

public import DomainTheory.DataTypesAsLattices.Graph

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Iterate `f` starting from `⊥`. -/
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

end DomainTheory.DataTypesAsLattices
