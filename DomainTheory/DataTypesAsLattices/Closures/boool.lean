/-ai
Scott's modified boolean closure, equation (5.3), is the graph of the map sending u to the conditional of u on the singleton {0} and on ⊤ + 1.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.3).** The modified boolean closure. -/
def boool : Pomega :=
  graph (fun u => condSet u (ofNat 0) (succSet topElem))

end DomainTheory.DataTypesAsLattices
