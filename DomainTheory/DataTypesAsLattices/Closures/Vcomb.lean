
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Vapply

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** The universe combinator. -/
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

end DomainTheory.DataTypesAsLattices
