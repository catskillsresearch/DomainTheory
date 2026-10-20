module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** Shift used in the sum of closures. -/
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))

end DomainTheory.DataTypesAsLattices
