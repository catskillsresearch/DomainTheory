module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §5, Definition.** `a` is a closure operation iff `I ⊆ a = a ∘ a`. -/
def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a

end DomainTheory.DataTypesAsLattices
