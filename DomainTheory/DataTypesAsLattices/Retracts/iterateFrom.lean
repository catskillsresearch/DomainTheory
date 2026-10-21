/-ai
The directed iterates of a map f starting from a set x, in Scott's supremum construction, are x at stage zero and the value of f on the preceding iterate at each successor stage.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Directed iterates of `f` starting from `x` (Scott's sup construction). -/
def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)

end DomainTheory.DataTypesAsLattices
