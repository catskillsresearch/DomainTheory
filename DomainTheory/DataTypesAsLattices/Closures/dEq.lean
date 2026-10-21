/-ai
Scott 1976, (5.25). The set dEq is the least fixed point of the self-arrow step, the least solution of the equation d = I ∪ (d ∘→ d).
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.25).** Least solution of `d = I ∪ (d ∘→ d)`. -/
def dEq : Pomega := fix selfArrowStep

end DomainTheory.DataTypesAsLattices
