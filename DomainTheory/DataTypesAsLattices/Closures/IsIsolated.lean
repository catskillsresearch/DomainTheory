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
