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
