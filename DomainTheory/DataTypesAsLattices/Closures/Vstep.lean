/-ai
Scott's equation (5.14) presents the universe value V(a)(x) as the least fixed point of the step sending y to the union of x with a(y). This step is that map.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** `V(a)(x) = Y(λy. x ∪ a(y))`. -/
def Vstep (a x : Pomega) (y : Pomega) : Pomega := x ∪ funOf a y

end DomainTheory.DataTypesAsLattices
