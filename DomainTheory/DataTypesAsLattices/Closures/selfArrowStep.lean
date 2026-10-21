/-ai
The step of the fixed-point construction Y(λa. I ∪ (a ∘→ a)) sends a set to the union of the identity combinator with the function-space retract of the set with itself.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.25).** Step of `Y(λa. I ∪ (a ∘→ a))`. -/
def selfArrowStep (a : Pomega) : Pomega := Icomb ∪ arrowR a a

end DomainTheory.DataTypesAsLattices
