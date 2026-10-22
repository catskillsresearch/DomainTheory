/-ai
In the sense of Scott 1976, (3.3), the combinator G is the graph of the conditional that returns the packed combinators of successor, predecessor, conditional, K, and S on zero and returns zero otherwise.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.3).** `G = cond(⟨suc, pred, cond, K, S⟩)(0)`. -/
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)

end DomainTheory.DataTypesAsLattices
