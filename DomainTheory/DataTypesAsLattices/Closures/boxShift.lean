/-ai
Scott 1976, (5.13). The shift of a set a, used in the sum of closures, is the graph of the map sending x to the union of the singleton zero with the successor set of a applied to the predecessor set of x.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** Shift used in the sum of closures. -/
def boxShift (a : Pomega) : Pomega :=
  graph (fun x => ofNat 0 ∪ succSet (funOf a (predSet x)))

end DomainTheory.DataTypesAsLattices
