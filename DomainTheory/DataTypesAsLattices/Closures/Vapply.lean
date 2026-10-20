module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14)–(5.15).** The universe combinator
`V(a)(x) = ⋂ { y | x ⊆ y ∧ a(y) ⊆ y }`. -/
def Vapply (a x : Pomega) : Pomega :=
  ⋂₀ {y | x ⊆ y ∧ funOf a y ⊆ y}

end DomainTheory.DataTypesAsLattices
