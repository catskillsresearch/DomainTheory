module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

class IsRE (u : Pomega) : Prop where
  out : REPred fun n : ℕ => n ∈ u

end DomainTheory.DataTypesAsLattices
