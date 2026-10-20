module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Vapply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** The universe combinator. -/
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

end DomainTheory.DataTypesAsLattices
