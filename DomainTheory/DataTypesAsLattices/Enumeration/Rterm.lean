module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- Closed terms for the two elementary semigroup generators. -/
def Rterm : Term := .lam 0 (seq2Term .zero (.var 0))

end DomainTheory.DataTypesAsLattices
