/-ai
An element x of Pω is isolated, or compact, when it equals the finite set en for some natural number n in the standard enumeration of finite sets.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Isolated (compact) elements of `Pω` are the finite sets `e n`. -/
def IsIsolated (x : Pomega) : Prop :=
  ∃ n, x = e n

end DomainTheory.DataTypesAsLattices
