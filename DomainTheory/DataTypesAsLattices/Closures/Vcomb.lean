/-ai
Scott's universe combinator, equation (5.14), is the graph of the map sending a to the graph of x ↦ V(a)(x).
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Vapply

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** The universe combinator. -/
def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

end DomainTheory.DataTypesAsLattices
