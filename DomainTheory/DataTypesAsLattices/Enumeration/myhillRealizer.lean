/-ai
The Myhill realizer of a function p is application of the Myhill set of the natural valuation and p.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def myhillRealizer (p : ℕ → ℕ) : Pomega → Pomega :=
  funOf (myhillQ valNat p)

end DomainTheory.DataTypesAsLattices
